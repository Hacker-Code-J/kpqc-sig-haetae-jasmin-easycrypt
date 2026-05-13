#!/usr/bin/env python3
"""Generate textbook-style chapter details for the HAETAE mathematical guide."""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "provable-security" / "proof-files.txt"
EC_DIR = ROOT / "provable-security" / "easycrypt"
OUT_DIR = ROOT / "guide" / "mathematical-chapter-details"


ROLE = {
    "HAETAE_Security.ec": "top-level correctness and EUF-CMA theorem composition",
    "Sig_ROM.ec": "generic signature, random-oracle, EUF-CMA, SUF-CMA, and UF-NMA games",
    "HAETAE_HopGames.ec": "HAETAE-specific hybrid games, simulator transitions, and hop bounds",
    "HAETAE_Reductions.ec": "real-valued security-loss ledger and final arithmetic normal forms",
    "HAETAE_ROM.ec": "typed random-oracle query/output domains",
    "HAETAE_ROM_Programming.ec": "lazy ROM programming, counted bad events, and programming bounds",
    "HAETAE_Scheme.ec": "HAETAE instantiation of the generic signature scheme interface",
    "HAETAE_Transcript.ec": "transcripts, forking predicates, and extraction obligations",
    "HAETAE_Events.ec": "named rejection-failure event predicates",
    "HAETAE_Assumptions.ec": "formal MLWE, Module-SIS, and bimodal self-target MSIS games",
    "HAETAE_Distributions.ec": "sampling distributions, support predicates, point bounds, and losslessness facts",
    "HAETAE_Rejection.ec": "rejection-sampling predicates, accepted-attempt structure, and loss obligations",
    "HAETAE_Algebra.ec": "deterministic polynomial, vector, matrix, key, signature, and verification algebra",
    "HAETAE_Params.ec": "mode-dependent numerical parameters and parameter inequalities",
    "HAETAE_FIPS202.ec": "deterministic FIPS202/SHAKE support for the formal model",
    "HAETAE_Keccak1600.ec": "Keccak-f1600 state and bit-level round equations",
}


DECL_RE = re.compile(
    r"^\s*(?:(local)\s+)?"
    r"(require\s+import|clone\s+import|import|theory|section|declare\s+module|"
    r"module\s+type|module|proc|abbrev\s+type|type|op|pred|lemma|equiv)\b"
)

NAME_PATTERNS = {
    "abbrev type": re.compile(r"^\s*abbrev\s+type\s+([A-Za-z_][A-Za-z0-9_']*)"),
    "type": re.compile(r"^\s*type\s+([A-Za-z_][A-Za-z0-9_']*)"),
    "op": re.compile(r"^\s*op\s+(?:\[[^\]]+\]\s+)?([A-Za-z_][A-Za-z0-9_']*)"),
    "pred": re.compile(r"^\s*pred\s+([A-Za-z_][A-Za-z0-9_']*)"),
    "lemma": re.compile(r"^\s*(?:local\s+)?lemma\s+([A-Za-z_][A-Za-z0-9_']*)"),
    "equiv": re.compile(r"^\s*(?:local\s+)?equiv\s+([A-Za-z_][A-Za-z0-9_']*)"),
    "module type": re.compile(r"^\s*module\s+type\s+([A-Za-z_][A-Za-z0-9_']*)"),
    "module": re.compile(r"^\s*module\s+([A-Za-z_][A-Za-z0-9_']*)"),
    "proc": re.compile(r"^\s*proc\s+([A-Za-z_][A-Za-z0-9_']*)"),
    "theory": re.compile(r"^\s*theory\s+([A-Za-z_][A-Za-z0-9_']*)"),
    "section": re.compile(r"^\s*section\s+([A-Za-z_][A-Za-z0-9_']*)"),
    "declare module": re.compile(r"^\s*declare\s+module\s+([A-Za-z_][A-Za-z0-9_']*)"),
}

RESERVED = {
    "abort",
    "abs",
    "admit",
    "algebra",
    "and",
    "apply",
    "as",
    "auto",
    "beta",
    "bool",
    "by",
    "byequiv",
    "byphoare",
    "call",
    "case",
    "ceil",
    "change",
    "clear",
    "clone",
    "congr",
    "conseq",
    "cut",
    "declare",
    "do",
    "done",
    "elim",
    "else",
    "end",
    "equiv",
    "exfalso",
    "exists",
    "expect",
    "first",
    "for",
    "forall",
    "from",
    "fun",
    "have",
    "hoare",
    "if",
    "import",
    "in",
    "inline",
    "int",
    "is",
    "last",
    "left",
    "lemma",
    "let",
    "local",
    "lossless",
    "module",
    "move",
    "moveeq",
    "nolog",
    "not",
    "of",
    "op",
    "or",
    "pose",
    "pred",
    "print",
    "proc",
    "proof",
    "progress",
    "qed",
    "real",
    "reflexivity",
    "require",
    "res",
    "return",
    "rewrite",
    "right",
    "rcondf",
    "rcondt",
    "rnd",
    "rwnormal",
    "seq",
    "sim",
    "skip",
    "smt",
    "split",
    "sp",
    "suff",
    "swap",
    "then",
    "theory",
    "true",
    "false",
    "type",
    "unit",
    "while",
    "wp",
    "wpa",
}


@dataclass
class Item:
    kind: str
    name: str
    line: int
    source: str
    proof_lines: list[str] = field(default_factory=list)


@dataclass
class FileDetails:
    filename: str
    context: list[Item]
    definitions: list[Item]
    theorems: list[Item]
    program_judgments: list[Item]


def manifest_files() -> list[str]:
    files: list[str] = []
    for raw in MANIFEST.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if line and not line.startswith("#"):
            files.append(line)
    return files


def tex_escape(text: str) -> str:
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


def verb_arg(text: str) -> str:
    """Escape only characters that would break a LaTeX verbatim-like argument."""
    replacements = {
        "\\": r"\textbackslash{}",
        "{": r"\{",
        "}": r"\}",
        "%": r"\%",
        "#": r"\#",
    }
    return "".join(replacements.get(ch, ch) for ch in text)


def compact_source(lines: list[str]) -> str:
    text = "\n".join(line.rstrip() for line in lines).strip()
    return text


def normalized_kind(raw_kind: str) -> str:
    raw_kind = raw_kind.strip()
    if raw_kind == "abbrev type":
        return "type"
    return raw_kind


def extract_name(kind: str, source: str, line: int) -> str:
    pattern = NAME_PATTERNS.get(kind)
    if pattern:
        match = pattern.match(source)
        if match:
            return match.group(1)
    if kind == "require import":
        return "imported theories"
    if kind == "clone import":
        return "cloned theory"
    if kind == "import":
        return "opened namespace"
    return f"{kind.replace(' ', '_')}_line_{line}"


def collect_until(lines: list[str], start: int, kind: str) -> tuple[str, int]:
    collected = [lines[start].rstrip("\n")]
    idx = start
    if kind in {"module", "module type", "proc"}:
        while idx + 1 < len(lines):
            stripped = lines[idx].strip()
            if "{" in stripped or stripped.endswith(".") or (
                kind == "proc" and (stripped.endswith("=") or ":=" in stripped)
            ):
                break
            idx += 1
            collected.append(lines[idx].rstrip("\n"))
        return compact_source(collected), idx

    while idx + 1 < len(lines) and not lines[idx].strip().endswith("."):
        idx += 1
        collected.append(lines[idx].rstrip("\n"))
    return compact_source(collected), idx


def collect_program_judgment(lines: list[str], start: int) -> tuple[str, int]:
    collected = [lines[start].rstrip("\n")]
    idx = start
    while idx + 1 < len(lines) and not lines[idx].strip().endswith("."):
        idx += 1
        collected.append(lines[idx].rstrip("\n"))
    return compact_source(collected), idx


def parse_params(source: str, name: str) -> list[str]:
    if name in source:
        tail = source.split(name, 1)[1]
    else:
        tail = source
    params: list[str] = []
    for group in re.findall(r"\(([^()]*)\)", tail):
        if ":" not in group:
            continue
        names, ty = group.split(":", 1)
        ty = ty.strip().strip(",")
        for _ in names.split():
            if ty:
                params.append(ty)
    return params


def return_type(kind: str, source: str, name: str) -> str | None:
    if kind == "pred":
        return "bool"
    head = source.split("=", 1)[0].rsplit(".", 1)[0]
    if name in head:
        tail = head.split(name, 1)[1]
    else:
        tail = head
    colon = tail.rfind(":")
    if colon < 0:
        return None
    return tail[colon + 1 :].strip()


def math_type(ty: str | None) -> str:
    if ty is None:
        return r"\mathsf{Unknown}"
    ty = re.sub(r"\s+", " ", ty.strip().rstrip("."))
    if not ty:
        return r"\mathsf{Unknown}"
    if "->" in ty:
        parts = [part.strip() for part in ty.split("->")]
        return r" \to ".join(math_type(part) for part in parts)
    if ty.endswith(" distr"):
        return r"\mathsf{Distr}(" + math_type(ty[:-6]) + ")"
    if ty.endswith(" list"):
        return r"\mathsf{List}(" + math_type(ty[:-5]) + ")"
    if "*" in ty:
        return r" \times ".join(math_type(part) for part in ty.split("*"))
    aliases = {
        "bool": r"\mathsf{Bool}",
        "int": r"\mathbb{Z}",
        "real": r"\mathbb{R}",
        "unit": r"\mathbf{1}",
    }
    return aliases.get(ty, r"\mathsf{" + tex_escape(ty) + "}")


def item_title(kind: str, idx: int, item: Item) -> str:
    label = {
        "require import": "Context",
        "clone import": "Context",
        "import": "Context",
        "theory": "Context",
        "section": "Context",
        "declare module": "Context",
        "type": "Definition",
        "op": "Definition",
        "pred": "Definition",
        "module type": "Definition",
        "module": "Definition",
        "proc": "Definition",
        "lemma": "Theorem",
        "equiv": "Relational Theorem",
        "hoare": "Program-Logic Judgment",
        "phoare": "Program-Logic Judgment",
    }.get(kind, "Item")
    return f"{label} {idx} (line {item.line})"


def definition_reading(item: Item) -> str:
    kind = item.kind
    source = item.source
    name = item.name
    if kind == "type":
        if "=" in source:
            return (
                "Mathematical definition. This is a definitional type abbreviation.  "
                "The exact displayed EasyCrypt statement gives the right-hand side; "
                "later proof steps may unfold it without adding an assumption."
            )
        return (
            "Mathematical definition. "
            + r"\("
            + r"\mathsf{"
            + tex_escape(name)
            + r"}\)"
            + " is an abstract carrier set.  The proof may quantify over this domain, but it does not expose a representation."
        )
    if kind in {"op", "pred"}:
        ret = return_type(kind, source, name)
        if kind == "pred" or ret == "bool":
            return "Mathematical definition. This is a Boolean predicate.  The exact displayed EasyCrypt statement gives its arguments; mathematically it is an event, invariant, support condition, or well-formedness predicate over those arguments."
        lossless = "  The EasyCrypt [lossless] annotation states that this distribution has total mass 1." if "[lossless]" in source else ""
        return "Mathematical definition. This is a total EasyCrypt operation.  The exact displayed statement gives the domain, codomain, and defining equation when present." + lossless
    if kind == "module type":
        return "Mathematical definition. This is an interface for an oracle, adversary, scheme, sampler, solver, or reduction.  A later theorem quantified over this interface is universally quantified over all modules implementing these procedures."
    if kind == "module":
        return "Mathematical definition. This is a probabilistic program/game or a module adapter.  Its procedures induce the probability space used by the game-based proof."
    if kind == "proc":
        return "Mathematical definition. This procedure is a command in the probabilistic program.  Its return value, state updates, and oracle calls are the operational content of the game."
    if kind in {"require import", "import", "clone import"}:
        return "Mathematical context. This line imports or specializes earlier theories, making their carrier sets, functions, modules, and theorems available to the current file."
    if kind == "theory":
        return "Mathematical context. This begins a namespace for the formal development in this file."
    if kind == "section":
        return "Mathematical context. This opens a scoped block of hypotheses, module parameters, and lemmas."
    if kind == "declare module":
        return "Mathematical context. This is universal quantification over an adversary, oracle, scheme, sampler, or reduction module satisfying the stated interface and memory restrictions."
    return "Mathematical definition. This source item contributes to the formal vocabulary of the chapter."


def theorem_reading(item: Item) -> str:
    source = item.source
    name = item.name
    if item.kind == "equiv" or "==>" in source or "equiv" in source:
        return (
            "Mathematical theorem. This is a relational program theorem: two games or procedures are coupled so that a precondition on their initial states implies the stated postcondition on final states and return values."
        )
    if "Pr[" in source:
        relation = r"\le" if "<=" in source else "=" if "=" in source else r"\bowtie"
        return (
            "Mathematical theorem. This theorem has the form "
            + r"\(\Pr[G:E] "
            + relation
            + r" B\)"
            + " is a game-probability statement.  It is one of the exact hops, bad-event bounds, or final advantage inequalities used in the reduction."
        )
    if "hoare [" in source or "hoare[" in source:
        return "Mathematical theorem. This statement is a Hoare triple: every terminating run from the precondition establishes the postcondition."
    if "phoare [" in source or "phoare[" in source:
        return "Mathematical theorem. This statement is a probabilistic Hoare judgment with an explicit probability bound."
    if "<=" in source:
        return "Mathematical theorem. This is an inequality, usually an arithmetic loss bound, event inclusion bound, or monotonicity fact used to compose probabilities."
    if "=>" in source:
        return "Mathematical theorem. This is an implication, normally turning one invariant, validity predicate, or proof obligation into another."
    if "=" in source:
        return "Mathematical theorem. This is an equality or definitional expansion used for rewriting and normalization."
    return "Mathematical theorem. This lemma is a universally quantified proposition over the variables shown in the EasyCrypt statement."


def role_for(item: Item, filename: str) -> str:
    name = item.name.lower()
    if item.kind in {"require import", "clone import", "import", "theory", "section", "declare module"}:
        return "Use in this chapter. It fixes the proof context, imported mathematical language, or quantified module parameters for the following statements."
    if item.kind in {"module", "module type", "proc"}:
        if any(word in name for word in ["euf", "cma", "nma", "game"]):
            return "Use in this chapter. It defines the game or game interface whose success event is bounded by later theorems."
        if any(word in name for word in ["oracle", "rom", "hash"]):
            return "Use in this chapter. It defines the oracle boundary through which adversaries and simulations interact."
        if any(word in name for word in ["sampler", "sample"]):
            return "Use in this chapter. It defines the sampling procedure whose distributional behavior is justified by the later loss lemmas."
        return "Use in this chapter. It supplies an executable component of the formal probabilistic model."
    if item.kind in {"type", "op", "pred"}:
        if any(word in name for word in ["loss", "bound", "adv", "term", "epsilon", "delta"]):
            return "Use in this chapter. It names a numerical term that appears in a game-hop or final security inequality."
        if any(word in name for word in ["bad", "failure", "rejection", "collision", "prequery"]):
            return "Use in this chapter. It names a bad event or rejection condition whose probability must be zero or explicitly bounded."
        if any(word in name for word in ["valid", "wf", "ok", "support", "range"]):
            return "Use in this chapter. It names a well-formedness, support, or validity predicate needed by later preservation lemmas."
        if any(word in name for word in ["transcript", "fork", "extract"]):
            return "Use in this chapter. It defines transcript/extraction data for the Fiat-Shamir forking and special-soundness argument."
        if name.startswith("d") or any(word in name for word in ["sample", "coins"]):
            return "Use in this chapter. It contributes a sampler or sampler-derived object to the distributional model."
        return "Use in this chapter. It is part of the exact formal vocabulary used by subsequent lemmas and games."
    if item.kind in {"lemma", "equiv"}:
        if any(word in name for word in ["security", "bound", "loss", "le", "subunit"]):
            return "Use in this chapter. It contributes directly to an advantage bound, bad-event bound, or real-arithmetic composition step."
        if any(word in name for word in ["exact", "equiv", "erasure", "sim"]):
            return "Use in this chapter. It proves an exact game replacement or simulator equivalence."
        if any(word in name for word in ["preserve", "invariant", "discipline", "state"]):
            return "Use in this chapter. It preserves an invariant across an oracle call, adversary call, or game procedure."
        if any(word in name for word in ["valid", "sound", "correct", "wf"]):
            return "Use in this chapter. It proves a structural correctness fact needed by later extraction or verification arguments."
        if filename == "HAETAE_Security.ec":
            return "Use in this chapter. It is a top-level composition theorem or an arithmetic step feeding the final HAETAE theorem."
        return "Use in this chapter. It is a reusable checked theorem cited by later proof scripts."
    return "Use in this chapter. It records a checked formal step."


def proof_summary(lines: list[str]) -> tuple[str, list[str], list[str]]:
    if not lines:
        return "No proof block was collected for this item.", [], []
    tactic_words: list[str] = []
    citations: set[str] = set()
    for raw in lines:
        line = raw.split("//", 1)[0]
        for word in re.findall(r"\b[A-Za-z_][A-Za-z0-9_']*\b", line):
            lower = word.lower()
            if lower in RESERVED:
                if lower not in tactic_words and lower in {
                    "apply",
                    "rewrite",
                    "smt",
                    "hoare",
                    "phoare",
                    "byequiv",
                    "byphoare",
                    "wp",
                    "rnd",
                    "call",
                    "conseq",
                    "proc",
                    "inline",
                    "case",
                    "split",
                    "have",
                    "suff",
                    "pose",
                    "elim",
                }:
                    tactic_words.append(lower)
                continue
            if len(word) == 1:
                continue
            if word[0].isdigit():
                continue
            citations.add(word)
    citation_list = sorted(citations)
    return (
        "Proof-script reading. The machine proof decomposes the theorem into rewrites, program-logic obligations, relational equivalences, and arithmetic side conditions.",
        tactic_words,
        citation_list,
    )


def write_listing(out: list[str], source: str) -> None:
    out.append(r"\begin{lstlisting}[language=EasyCrypt,basicstyle=\ttfamily\scriptsize]")
    out.extend(source.splitlines())
    out.append(r"\end{lstlisting}")


def write_item_body(out: list[str], item: Item, filename: str) -> None:
    out.append(r"\noindent\textbf{EasyCrypt name.}")
    write_listing(out, item.name)
    out.append(r"\noindent\textbf{Checked EasyCrypt statement.}")
    write_listing(out, item.source)
    if item.kind in {"lemma", "equiv"}:
        out.append(r"\noindent\textbf{Formal mathematical reading.}")
        out.append(theorem_reading(item))
    else:
        out.append(r"\noindent\textbf{Formal mathematical reading.}")
        out.append(definition_reading(item))
    out.append("")
    out.append(r"\noindent\textbf{Role in the proof.}")
    out.append(role_for(item, filename))
    out.append("")
    if item.kind in {"lemma", "equiv"}:
        summary, tactics, citations = proof_summary(item.proof_lines)
        out.append(r"\noindent\textbf{Proof-script interpretation.}")
        out.append(summary)
        if tactics:
            out.append(r"\emph{Main tactics visible in the proof script:} " + ", ".join(r"\ec{" + verb_arg(t) + "}" for t in tactics) + ".")
        if citations:
            out.append(r"\emph{Named identifiers syntactically cited in the proof block:}")
            write_listing(out, "\n".join(citations))
        out.append("")


def write_entry(out: list[str], idx: int, item: Item, filename: str) -> None:
    if item.kind in {"type", "op", "pred", "module type", "module", "proc"}:
        out.append(r"\begin{formaldefinition}[EasyCrypt line " + str(item.line) + r"]")
        write_item_body(out, item, filename)
        out.append(r"\end{formaldefinition}")
        out.append("")
        return
    if item.kind in {"lemma", "equiv"}:
        out.append(r"\begin{formaltheorem}[EasyCrypt line " + str(item.line) + r"]")
        write_item_body(out, item, filename)
        out.append(r"\end{formaltheorem}")
        out.append("")
        return

    out.append(r"\paragraph{" + tex_escape(item_title(item.kind, idx, item)) + "}")
    write_item_body(out, item, filename)


def scan_file(filename: str) -> FileDetails:
    path = EC_DIR / filename
    lines = path.read_text(encoding="utf-8").splitlines()
    context: list[Item] = []
    definitions: list[Item] = []
    theorems: list[Item] = []
    judgments: list[Item] = []
    last_theorem: Item | None = None
    in_proof = False
    current_theorem: Item | None = None
    i = 0
    while i < len(lines):
        stripped = lines[i].strip()
        if in_proof:
            assert current_theorem is not None
            current_theorem.proof_lines.append(lines[i])
            if stripped == "qed.":
                in_proof = False
                current_theorem = None
                last_theorem = None
            else:
                if stripped.startswith("hoare") or stripped.startswith("phoare"):
                    source, end = collect_program_judgment(lines, i)
                    kind = "phoare" if stripped.startswith("phoare") else "hoare"
                    judgments.append(Item(kind, f"{kind}_judgment", i + 1, source))
                    i = end
            i += 1
            continue

        if stripped == "proof." and last_theorem is not None:
            in_proof = True
            current_theorem = last_theorem
            current_theorem.proof_lines.append(lines[i])
            i += 1
            continue

        match = DECL_RE.match(lines[i])
        if match:
            raw_kind = match.group(2)
            kind = normalized_kind(raw_kind)
            source, end = collect_until(lines, i, kind)
            name = extract_name(raw_kind, source, i + 1)
            item = Item(kind, name, i + 1, source)
            if kind in {"require import", "clone import", "import", "theory", "section", "declare module"}:
                context.append(item)
                last_theorem = None
            elif kind in {"lemma", "equiv"}:
                theorems.append(item)
                last_theorem = item
            else:
                definitions.append(item)
                last_theorem = None
            i = end + 1
            continue

        if stripped.startswith("hoare") or stripped.startswith("phoare"):
            source, end = collect_program_judgment(lines, i)
            kind = "phoare" if stripped.startswith("phoare") else "hoare"
            judgments.append(Item(kind, f"{kind}_judgment", i + 1, source))
            i = end + 1
            continue

        i += 1
    return FileDetails(filename, context, definitions, theorems, judgments)


def write_file(details: FileDetails) -> None:
    out: list[str] = []
    filename = details.filename
    total = len(details.context) + len(details.definitions) + len(details.theorems) + len(details.program_judgments)
    out.append(r"\subsection*{Textbook Formal Inventory}")
    out.append(
        "This subsection records the exact formal material in "
        + r"\file{"
        + verb_arg(filename)
        + r"}"
        + ".  It is generated from the proof-surface EasyCrypt file, so the line numbers and statements are meant to be read next to the checked source."
    )
    out.append("")
    out.append(
        r"\noindent\textbf{Chapter role.} "
        + tex_escape(ROLE.get(filename, "checked HAETAE proof file"))
        + "."
    )
    out.append("")
    out.append(
        r"\noindent\textbf{Inventory size.} "
        + f"{len(details.context)} context declarations, {len(details.definitions)} definitions/game objects, "
        + f"{len(details.theorems)} lemmas or relational theorems, and {len(details.program_judgments)} explicit Hoare/Phoare judgments were found."
    )
    out.append("")

    if details.context:
        out.append(r"\subsubsection*{Theory Context, Imports, and Quantified Modules}")
        for idx, item in enumerate(details.context, 1):
            write_entry(out, idx, item, filename)
    if details.definitions:
        out.append(r"\subsubsection*{Definitions, Carrier Sets, Operations, Games, and Procedures}")
        for idx, item in enumerate(details.definitions, 1):
            write_entry(out, idx, item, filename)
    if details.theorems:
        out.append(r"\subsubsection*{Lemmas, Theorems, Relational Equivalences, and Their Proof Dependencies}")
        for idx, item in enumerate(details.theorems, 1):
            write_entry(out, idx, item, filename)
    if details.program_judgments:
        out.append(r"\subsubsection*{Explicit Program-Logic Judgments Used Inside Proof Scripts}")
        for idx, item in enumerate(details.program_judgments, 1):
            out.append(r"\begin{formaljudgment}[EasyCrypt line " + str(item.line) + r"]")
            out.append(r"\noindent\textbf{Checked EasyCrypt judgment.}")
            write_listing(out, item.source)
            if item.kind == "phoare":
                out.append(r"\noindent\textbf{Formal mathematical reading.} This is a probabilistic Hoare judgment.  It states that the command satisfies the postcondition with the displayed probability bound.")
            else:
                out.append(r"\noindent\textbf{Formal mathematical reading.} This is a Hoare judgment.  It states partial correctness of the displayed procedure from the displayed precondition to the displayed postcondition.")
            out.append(r"\end{formaljudgment}")
            out.append("")

    out.append(r"\medskip")
    out.append(
        r"\noindent\emph{End of generated formal inventory for \file{"
        + verb_arg(filename)
        + r"}.}"
    )
    (OUT_DIR / f"{filename[:-3]}-textbook-details.tex").write_text("\n".join(out) + "\n", encoding="utf-8")


def main() -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    totals = {"context": 0, "definitions": 0, "theorems": 0, "judgments": 0}
    for filename in manifest_files():
        details = scan_file(filename)
        write_file(details)
        totals["context"] += len(details.context)
        totals["definitions"] += len(details.definitions)
        totals["theorems"] += len(details.theorems)
        totals["judgments"] += len(details.program_judgments)
    print(
        "wrote textbook chapter details: "
        + ", ".join(f"{key}={value}" for key, value in totals.items())
    )


if __name__ == "__main__":
    main()
