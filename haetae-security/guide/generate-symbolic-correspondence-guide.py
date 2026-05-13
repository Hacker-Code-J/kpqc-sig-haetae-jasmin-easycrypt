#!/usr/bin/env python3
"""Generate a symbolic correspondence guide for the HAETAE EasyCrypt surface."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
from typing import Iterable


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "provable-security" / "proof-files.txt"
EC_DIR = ROOT / "provable-security" / "easycrypt"
OUT = ROOT / "guide" / "haetae-symbolic-correspondence-guide.tex"


DECL_RE = re.compile(r"^\s*(type|op|pred|lemma|equiv)\b")
NAME_RE = {
    "type": re.compile(r"^\s*type\s+([A-Za-z_][A-Za-z0-9_']*)"),
    "op": re.compile(r"^\s*op\s+(?:\[[^\]]+\]\s+)?([A-Za-z_][A-Za-z0-9_']*)"),
    "pred": re.compile(r"^\s*pred\s+([A-Za-z_][A-Za-z0-9_']*)"),
    "lemma": re.compile(r"^\s*lemma\s+([A-Za-z_][A-Za-z0-9_']*)"),
    "equiv": re.compile(r"^\s*equiv\s+([A-Za-z_][A-Za-z0-9_']*)"),
}


FILE_ROLES = {
    "HAETAE_Security.ec": "top-level theorem composition and concrete EUF-CMA bound",
    "Sig_ROM.ec": "generic signature security games over a random oracle",
    "HAETAE_HopGames.ec": "hybrid games, invariants, equivalences, and game-hop losses",
    "HAETAE_Reductions.ec": "arithmetic assembly of concrete loss terms",
    "HAETAE_ROM.ec": "typed random-oracle query and response model",
    "HAETAE_ROM_Programming.ec": "random-oracle programming events and counted bad-event bounds",
    "HAETAE_Scheme.ec": "HAETAE instance of the generic signature interface",
    "HAETAE_Transcript.ec": "transcripts, forking relations, and extraction obligations",
    "HAETAE_Events.ec": "named rejection-failure events",
    "HAETAE_Assumptions.ec": "abstract MLWE, Module-SIS, and bimodal self-target games",
    "HAETAE_Distributions.ec": "sampling distributions and support/cardinality facts",
    "HAETAE_Rejection.ec": "rejection predicates and rejection-sampling probability bounds",
    "HAETAE_Algebra.ec": "deterministic polynomial/vector/matrix algebra used by the model",
    "HAETAE_Params.ec": "mode-dependent parameter constants",
    "HAETAE_FIPS202.ec": "abstracted FIPS202/SHAKE support",
    "HAETAE_Keccak1600.ec": "Keccak state-level support used by the hash model",
}


@dataclass
class Item:
    file: str
    line: int
    kind: str
    name: str
    source: str
    symbol: str
    purpose: str


def manifest_files() -> list[str]:
    files: list[str] = []
    for raw in MANIFEST.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if line and not line.startswith("#"):
            files.append(line)
    return files


def latex_escape(text: str) -> str:
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    return "".join(replacements.get(ch, ch) for ch in text)


def math_name(name: str) -> str:
    return r"\mathsf{" + latex_escape(name) + "}"


def compact(lines: Iterable[str], limit: int = 360) -> str:
    text = " ".join(line.strip() for line in lines)
    text = re.sub(r"\s+", " ", text).strip()
    if len(text) <= limit:
        return text
    return text[: limit - 3].rstrip() + "..."


def kind_name(kind: str) -> str:
    return {
        "op": "operation",
        "pred": "predicate",
        "type": "type",
        "lemma": "lemma",
        "equiv": "equivalence",
        "hoare-step": "hoare proof step",
    }[kind]


def math_type(expr: str) -> str:
    expr = expr.strip().rstrip(".")
    expr = re.sub(r"\s+", " ", expr)
    if not expr:
        return r"\mathsf{Unknown}"
    if expr.endswith(" distr"):
        return r"\mathsf{Distr}(" + math_type(expr[:-6]) + ")"
    if expr.endswith(" list"):
        return r"\mathsf{List}(" + math_type(expr[:-5]) + ")"
    if "*" in expr:
        return r" \times ".join(math_type(part) for part in expr.split("*"))
    aliases = {
        "bool": r"\mathsf{Bool}",
        "int": r"\mathbb{Z}",
        "real": r"\mathbb{R}",
        "unit": r"\mathbf{1}",
    }
    return aliases.get(expr, math_name(expr))


def parse_params(signature_prefix: str) -> list[str]:
    params: list[str] = []
    for group in re.findall(r"\(([^()]*)\)", signature_prefix):
        if ":" not in group:
            continue
        names, ty = group.split(":", 1)
        names = names.strip()
        ty = ty.strip()
        if not names or not ty:
            continue
        for _ in names.split():
            params.append(ty)
    return params


def parse_return_type(kind: str, source: str, name: str) -> str | None:
    if kind == "pred":
        return "bool"
    head = source.split("=", 1)[0]
    head = head.rsplit(".", 1)[0]
    after_name = head.split(name, 1)[1] if name in head else head
    colon = after_name.rfind(":")
    if colon < 0:
        return None
    return after_name[colon + 1 :].strip()


def domain_symbol(params: list[str]) -> str:
    if not params:
        return r"\mathbf{1}"
    return r" \times ".join(math_type(param) for param in params)


def symbolic_for(kind: str, name: str, source: str, parent: str | None = None) -> str:
    if kind == "type":
        m = re.search(r"^\s*type\s+[A-Za-z_][A-Za-z0-9_']*\s*=\s*(.*)\.\s*$", source)
        if m:
            return r"\(" + math_name(name) + r" \equiv " + math_type(m.group(1)) + r"\)"
        return r"\(" + math_name(name) + r"\)" + " is an abstract carrier set."

    if kind in {"op", "pred"}:
        ret = parse_return_type(kind, source, name)
        prefix = source.split(name, 1)[1] if name in source else source
        params = parse_params(prefix)
        codomain = math_type(ret or "bool")
        if ret and ret.endswith("distr"):
            codomain = math_type(ret)
        if "[lossless]" in source and ret and ret.endswith("distr"):
            return (
                r"\("
                + math_name(name)
                + r" : "
                + domain_symbol(params)
                + r" \to "
                + codomain
                + r"\), with total probability mass \(1\)."
            )
        if kind == "pred" or ret == "bool":
            return (
                r"\("
                + math_name(name)
                + r" \subseteq "
                + domain_symbol(params)
                + r"\)"
                + " is a Boolean-valued predicate."
            )
        return (
            r"\("
            + math_name(name)
            + r" : "
            + domain_symbol(params)
            + r" \to "
            + codomain
            + r"\)"
        )

    if kind == "equiv":
        return (
            r"\("
            + math_name(name)
            + r" : \mathcal{C}_1 \sim \mathcal{C}_2 \;[\;R \Rightarrow S\;]\)"
            + " is a relational program equivalence."
        )

    if kind == "hoare-step":
        lemma = math_name(parent or "current lemma")
        return (
            r"Within \("
            + lemma
            + r"\), the proof reduces the probabilistic goal to a Hoare triple "
            + r"\(\{P\}\;c\;\{Q\}\)."
        )

    if "hoare [" in source:
        return (
            r"\("
            + math_name(name)
            + r" : \{P\}\;c\;\{Q\}\)"
            + " states partial correctness of the program command."
        )
    if "equiv [" in source:
        return (
            r"\("
            + math_name(name)
            + r" : c_1 \sim c_2 \;[\;R \Rightarrow S\;]\)"
            + " states relational preservation from precondition to postcondition."
        )
    if "Pr[" in source:
        relation = r"\bowtie"
        if "<=" in source:
            relation = r"\le"
        elif "=" in source:
            relation = r"="
        return (
            r"\("
            + math_name(name)
            + r" : \Pr[c : E] "
            + relation
            + r" B\)"
            + " is a probability bound or exact game probability."
        )
    if "<=" in source or "<=" in source.replace(r"\le", "<="):
        return r"\(" + math_name(name) + r" : X \le Y\)" + " is an arithmetic or probability upper bound."
    if "=>" in source:
        return r"\(" + math_name(name) + r" : P \Rightarrow Q\)" + " is an implication used as a proof obligation."
    if "=" in source:
        return r"\(" + math_name(name) + r" : L = R\)" + " is an equality/rewriting fact."
    return r"\(" + math_name(name) + r" : \forall \vec{x}.\, P(\vec{x})\)" + " is a universally quantified fact."


def purpose_for(kind: str, name: str, source: str, file: str, parent: str | None = None) -> str:
    lname = name.lower()
    if kind == "type":
        return "Fixes the mathematical carrier used by later declarations without committing to an implementation representation."
    if kind == "hoare-step":
        return "Introduces a program-logic proof obligation for the surrounding probabilistic lemma."
    if kind == "equiv" or "equiv [" in source:
        return "Shows that two games expose the same observable behavior under the stated relation."
    if kind == "pred" or parse_return_type(kind, source, name) == "bool":
        if any(word in lname for word in ["valid", "wf", "well", "support", "range"]):
            return "Names a well-formedness or support condition so it can be reused in lemmas."
        if any(word in lname for word in ["bad", "failure", "rejection"]):
            return "Names a bad event whose probability is later shown to be zero or bounded."
        return "Names a Boolean mathematical condition used in statements and invariants."
    if kind == "op":
        ret = parse_return_type(kind, source, name) or ""
        if ret.endswith("distr") or lname.startswith("d"):
            return "Defines a sampler/distribution used by game procedures and probability bounds."
        if any(word in lname for word in ["loss", "bound", "adv", "epsilon", "delta"]):
            return "Defines a concrete numeric loss term used in the final security inequality."
        if any(word in lname for word in ["query", "oracle", "rom", "hash"]):
            return "Defines the random-oracle/hash interface data used by the games."
        if any(word in lname for word in ["transcript", "fork", "extract"]):
            return "Defines transcript or extraction data used in the forking/special-soundness argument."
        return "Defines a total mathematical function used by the EasyCrypt model."
    if any(word in lname for word in ["lossless", "mu", "weight", "support"]):
        return "Proves a distribution fact needed for sampling or probability mass reasoning."
    if any(word in lname for word in ["bound", "loss", "le", "subunit", "security"]):
        return "Proves a bound that contributes to a game-hop or final security inequality."
    if any(word in lname for word in ["exact", "equiv", "erasure", "simulator"]):
        return "Proves an exact game equivalence or simulator transition."
    if any(word in lname for word in ["preserves", "state", "invariant", "discipline"]):
        return "Proves an invariant preservation fact for an oracle, adversary call, or game main procedure."
    if any(word in lname for word in ["valid", "wf", "sound", "correct"]):
        return "Proves a structural correctness fact used to justify later reductions."
    if file == "HAETAE_Security.ec":
        return "Assembles previously checked lemmas into the top-level HAETAE security theorem."
    return "Records a reusable theorem so later proof scripts can rewrite, apply, or compose it."


def collect_declaration(lines: list[str], start: int) -> tuple[str, int]:
    collected = [lines[start].rstrip("\n")]
    idx = start
    while idx + 1 < len(lines) and not lines[idx].strip().endswith("."):
        idx += 1
        collected.append(lines[idx].rstrip("\n"))
    return compact(collected), idx


def scan_file(filename: str) -> list[Item]:
    path = EC_DIR / filename
    lines = path.read_text(encoding="utf-8").splitlines()
    items: list[Item] = []
    active_lemma: str | None = None
    i = 0
    while i < len(lines):
        stripped = lines[i].strip()
        match = DECL_RE.match(lines[i])
        if match:
            kind = match.group(1)
            source, end = collect_declaration(lines, i)
            name_match = NAME_RE[kind].match(source)
            name = name_match.group(1) if name_match else f"{kind}_line_{i + 1}"
            if kind == "lemma":
                active_lemma = name
            items.append(
                Item(
                    file=filename,
                    line=i + 1,
                    kind=kind,
                    name=name,
                    source=source,
                    symbol=symbolic_for(kind, name, source),
                    purpose=purpose_for(kind, name, source, filename),
                )
            )
            i = end + 1
            continue
        if stripped == "hoare.":
            name = f"hoare_step_for_{active_lemma or 'unknown'}"
            items.append(
                Item(
                    file=filename,
                    line=i + 1,
                    kind="hoare-step",
                    name=name,
                    source="hoare.",
                    symbol=symbolic_for("hoare-step", name, "hoare.", active_lemma),
                    purpose=purpose_for("hoare-step", name, "hoare.", filename, active_lemma),
                )
            )
        if stripped == "qed.":
            active_lemma = None
        i += 1
    return items


def write_header(out: list[str], files: list[str], all_items: list[Item]) -> None:
    counts: dict[str, int] = {}
    for item in all_items:
        counts[item.kind] = counts.get(item.kind, 0) + 1
    summary = ", ".join(f"{kind_name(kind)}s: {count}" for kind, count in sorted(counts.items()))
    out.extend(
        [
            r"\documentclass[10pt]{article}",
            r"\usepackage[T1]{fontenc}",
            r"\usepackage[utf8]{inputenc}",
            r"\usepackage{lmodern}",
            r"\usepackage[margin=0.65in,landscape]{geometry}",
            r"\usepackage{amsmath,amssymb}",
            r"\usepackage{xcolor}",
            r"\usepackage{array,booktabs,longtable}",
            r"\usepackage[bookmarks=false]{hyperref}",
            r"\setlength{\emergencystretch}{8em}",
            r"\sloppy",
            r"\newcolumntype{L}[1]{>{\raggedright\arraybackslash}p{#1}}",
            r"\newcommand{\file}[1]{\nolinkurl{#1}}",
            r"\newcommand{\ec}[1]{\begingroup\ttfamily\scriptsize #1\endgroup}",
            r"\hypersetup{colorlinks=true,linkcolor=blue!55!black,urlcolor=blue!55!black}",
            r"\title{HAETAE EasyCrypt Symbolic Correspondence Guide}",
            r"\author{Generated from the provable-security EasyCrypt manifest}",
            r"\date{May 2026}",
            r"\begin{document}",
            r"\maketitle",
            "",
            "This guide indexes the mathematical objects written in the checked HAETAE EasyCrypt proof surface.",
            "It covers each manifest file and records every top-level \\texttt{type}, \\texttt{op}, \\texttt{pred},",
            "\\texttt{lemma}, and \\texttt{equiv} declaration, plus explicit \\texttt{hoare.} proof steps.",
            "The line-by-line companion guides preserve every source line; this document instead gives the symbolic",
            "mathematical reading of each named declaration and why it appears in the proof.",
            "",
            r"\medskip",
            r"\noindent Source manifest: \file{provable-security/proof-files.txt}.",
            r"\noindent Declaration count: "
            + latex_escape(str(len(all_items)))
            + ". "
            + latex_escape(summary)
            + ".",
            "",
            r"\tableofcontents",
            "",
            r"\section{Symbolic Reading Rules}",
            r"\begin{longtable}{L{0.22\textwidth}L{0.70\textwidth}}",
            r"\toprule",
            r"\textbf{EasyCrypt construct} & \textbf{Mathematical correspondence} \\",
            r"\midrule",
            r"\endfirsthead",
            r"\toprule",
            r"\textbf{EasyCrypt construct} & \textbf{Mathematical correspondence} \\",
            r"\midrule",
            r"\endhead",
            r"\texttt{type T.} & An abstract carrier set \(T\).  The proof may quantify over \(T\), but it does not expose an implementation representation. \\",
            r"\texttt{type T = A * B.} & A definitional product \(T \equiv A \times B\).  Tuple projections in later code are projections from this product. \\",
            r"\texttt{op f (x:A) : B = e.} & A total mathematical function \(f : A \to B\) with defining equation \(f(x)=\operatorname{eval}(e)\). \\",
            r"\texttt{op [lossless] d : A distr.} & A probability distribution \(d \in \mathsf{Distr}(A)\) whose mass is \(1\). \\",
            r"\texttt{pred P (x:A).} or Boolean \texttt{op} & A predicate \(P \subseteq A\), equivalently \(P:A\to\mathsf{Bool}\). \\",
            r"\texttt{lemma L xs : P.} & A theorem \(\vdash \forall xs.\,P\).  The proof script after it is the machine-checked derivation. \\",
            r"\texttt{Pr[G.main() @ \&m : E] <= B} & A game probability bound \(\Pr[G:E]\le B\).  These are the numeric game-hop and final security claims. \\",
            r"\texttt{equiv ... : R ==> S.} & A relational judgment \(c_1\sim c_2\,[R\Rightarrow S]\) showing that two games preserve relation \(S\) from relation \(R\). \\",
            r"\texttt{hoare.} & A proof step that changes the active goal to a Hoare triple \(\{P\}\,c\,\{Q\}\). \\",
            r"\bottomrule",
            r"\end{longtable}",
            "",
            r"\section{Manifest Order}",
            r"\begin{enumerate}",
        ]
    )
    for filename in files:
        out.append(
            r"\item \file{"
            + latex_escape(filename)
            + "} -- "
            + latex_escape(FILE_ROLES.get(filename, "checked proof file"))
            + "."
        )
    out.extend([r"\end{enumerate}", ""])


def write_item_table(out: list[str], filename: str, items: list[Item]) -> None:
    title_tex = latex_escape(filename)
    title_pdf = latex_escape(filename.replace("_", " "))
    out.extend(
        [
            r"\clearpage",
            r"\section{\texorpdfstring{\texttt{" + title_tex + r"}}{" + title_pdf + r"}}",
            latex_escape(FILE_ROLES.get(filename, "Checked proof file.")),
            "",
            r"\begin{longtable}{r L{0.17\textwidth} L{0.26\textwidth} L{0.27\textwidth} L{0.20\textwidth}}",
            r"\toprule",
            r"\textbf{Line} & \textbf{Construct} & \textbf{What was written} & \textbf{Symbolic correspondence} & \textbf{Why it is written this way} \\",
            r"\midrule",
            r"\endfirsthead",
            r"\toprule",
            r"\textbf{Line} & \textbf{Construct} & \textbf{What was written} & \textbf{Symbolic correspondence} & \textbf{Why it is written this way} \\",
            r"\midrule",
            r"\endhead",
        ]
    )
    for item in items:
        construct = (
            r"\textbf{"
            + latex_escape(kind_name(item.kind))
            + r"}\\"
            + r"\ec{"
            + latex_escape(item.name)
            + r"}"
        )
        source = r"\ec{" + latex_escape(item.source) + r"}"
        out.append(
            f"{item.line} & {construct} & {source} & {item.symbol} & {latex_escape(item.purpose)} \\\\"
        )
    out.extend([r"\bottomrule", r"\end{longtable}", ""])


def main() -> None:
    files = manifest_files()
    by_file = {filename: scan_file(filename) for filename in files}
    all_items = [item for filename in files for item in by_file[filename]]

    out: list[str] = []
    write_header(out, files, all_items)
    for filename in files:
        write_item_table(out, filename, by_file[filename])

    out.extend(
        [
            r"\section{Regenerating This Guide}",
            r"From \file{haetae-security}, run:",
            r"\begin{verbatim}",
            r"python3 guide/generate-symbolic-correspondence-guide.py",
            r"pdflatex -interaction=nonstopmode -halt-on-error guide/haetae-symbolic-correspondence-guide.tex",
            r"pdflatex -interaction=nonstopmode -halt-on-error guide/haetae-symbolic-correspondence-guide.tex",
            r"\end{verbatim}",
            r"\end{document}",
        ]
    )
    OUT.write_text("\n".join(out) + "\n", encoding="utf-8")
    print(f"wrote {OUT} with {len(all_items)} declarations")


if __name__ == "__main__":
    main()
