#!/usr/bin/env python3
"""Generate line-by-line mathematical LaTeX guides for manifest EasyCrypt files."""

from __future__ import annotations

import datetime as _dt
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "provable-security" / "proof-files.txt"
PROOF_DIR = ROOT / "provable-security" / "easycrypt"
OUT_DIR = ROOT / "guide" / "line-by-line"


ROLE = {
    "HAETAE_Security.ec": (
        "Top-level correctness and EUF-CMA theorem composition.",
        "Read this file as an inequality-composition script.  The local proof "
        "steps mostly apply previously checked game-hop and hardness bounds, "
        "then normalize the final real-valued bound."
    ),
    "Sig_ROM.ec": (
        "Generic signature games and random-oracle interfaces.",
        "Read this file as the reusable game framework.  Its scripts define "
        "abstract experiments and prove the exact NMA-to-CMA adapter fact used "
        "by the HAETAE-specific proof."
    ),
    "HAETAE_HopGames.ec": (
        "Detailed HAETAE hybrid games, invariants, and game-hop bounds.",
        "Read this file as the mechanized replacement for the informal hybrid "
        "sequence: equivalence proofs justify exact game replacements, Hoare "
        "proofs preserve state invariants, and inequalities account for bad "
        "events and sampler losses."
    ),
    "HAETAE_Reductions.ec": (
        "Concrete loss terms and arithmetic normalization.",
        "Read this file as the real-arithmetic ledger.  It collects the bound "
        "expressions and proves they can be grouped in the form consumed by the "
        "top-level security theorem."
    ),
    "HAETAE_ROM.ec": (
        "Typed random-oracle query and output model.",
        "Read this file as the hash-domain interface.  It separates the query "
        "forms so later freshness and programming proofs can refer to precise "
        "events."
    ),
    "HAETAE_ROM_Programming.ec": (
        "Counted random-oracle programming events and bounds.",
        "Read this file as the fundamental-lemma infrastructure for the ROM: "
        "define clear/bad states, prove preservation, then bound the bad-event "
        "probability."
    ),
    "HAETAE_Scheme.ec": (
        "HAETAE instantiation of the generic signature interface.",
        "Read this file as an adapter.  It aligns HAETAE key generation, "
        "signing, and verification with the generic games without doing the "
        "security proof locally."
    ),
    "HAETAE_Transcript.ec": (
        "Transcript records and validity/extraction facts.",
        "Read this file as the bridge from accepted signatures to structured "
        "mathematical objects used by the reductions."
    ),
    "HAETAE_Events.ec": (
        "Named rejection and acceptance events.",
        "Read this file as event vocabulary.  It gives stable names to "
        "predicates that later game hops should cite without unfolding."
    ),
    "HAETAE_Assumptions.ec": (
        "Abstract hardness games and reduction interfaces.",
        "Read this file as the formal trust boundary.  It represents MLWE, "
        "Module-SIS, and bimodal assumptions as explicit game probabilities."
    ),
    "HAETAE_Distributions.ec": (
        "Sampling distributions, support facts, and point bounds.",
        "Read this file as the probability-law library for the proof.  Its "
        "scripts justify losslessness, support membership, and sampler bounds."
    ),
    "HAETAE_Rejection.ec": (
        "Rejection predicates and rejection-sampling loss accounting.",
        "Read this file as the link between accepted HAETAE samples, transcript "
        "validity, and the rejection loss terms used in the final theorem."
    ),
    "HAETAE_Algebra.ec": (
        "Deterministic algebraic model and algebra lemmas.",
        "Read this file as the pure mathematical foundation over finite lists, "
        "polynomials, vectors, matrices, keys, and signatures."
    ),
    "HAETAE_Params.ec": (
        "Parameter modes and constants.",
        "Read this file as the shared numerical vocabulary used by algebra, "
        "distributions, rejection sampling, and reductions."
    ),
    "HAETAE_FIPS202.ec": (
        "Modeled FIPS202/SHAKE support.",
        "Read this file as deterministic hash-interface support for the model, "
        "not as a standard-model security proof for SHAKE."
    ),
    "HAETAE_Keccak1600.ec": (
        "Keccak state and low-level hash support.",
        "Read this file as finite-state deterministic support for the modeled "
        "hash layer."
    ),
}


def manifest_files() -> list[str]:
    files: list[str] = []
    for raw in MANIFEST.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        files.append(line)
    return files


def tex_escape(text: str) -> str:
    repl = {
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
    return "".join(repl.get(ch, ch) for ch in text)


def first_name_after(keyword: str, s: str) -> str:
    tail = s[len(keyword):].strip()
    tail = re.sub(r"^\[[^\]]+\]\s*", "", tail)
    m = re.match(r"([A-Za-z0-9_'.]+)", tail)
    return m.group(1) if m else "this declaration"


def explain(line: str) -> str:
    s = line.strip()
    if not s:
        return "Blank separator.  It marks a boundary between declarations, proof blocks, or tactic phases."
    if s.startswith("//") or s.startswith("(*") or s.startswith("*"):
        return "Commentary for the human reader; it does not add a checked mathematical assumption."
    if s.startswith("require import"):
        deps = s.replace("require import", "", 1).strip().rstrip(".")
        return (
            "Imports " + deps + ".  Mathematically, this exposes earlier carrier sets, "
            "operations, games, and lemmas that the current file may cite."
        )
    if s.startswith("clone import"):
        return "Clones and opens a parameterized EasyCrypt theory, producing a specialized instance used below."
    if s.startswith("import "):
        names = s.replace("import", "", 1).strip().rstrip(".")
        return "Opens " + names + " so its names can be used without qualification in the following proof."
    if s.startswith("theory "):
        name = first_name_after("theory", s).rstrip(".")
        return "Begins the namespace " + name + ", grouping the declarations as one checked theory."
    if s == "end section." or s.startswith("end section"):
        return "Closes the current section, discharging local module and variable scope."
    if s.startswith("end "):
        return "Closes the current theory or module block."
    if s.startswith("section "):
        name = first_name_after("section", s).rstrip(".")
        return "Starts section " + name + ", a scoped region for related declarations and hypotheses."
    if s.startswith("declare module"):
        return "Declares an abstract module parameter.  Mathematically this quantifies over an oracle, adversary, or reduction satisfying the stated interface."
    if s.startswith("module type"):
        name = first_name_after("module type", s)
        return "Defines module interface " + name + ".  It specifies the procedures that later games or adversaries may call."
    if s.startswith("module "):
        name = first_name_after("module", s)
        return "Defines module " + name + ", a probabilistic program or game used to create events and success probabilities."
    if s.startswith("proc "):
        name = first_name_after("proc", s)
        return "Defines procedure " + name + ".  Its body is a probabilistic program whose result becomes part of a game event."
    if s.startswith("type ") or s.startswith("abbrev type"):
        name = first_name_after("abbrev type" if s.startswith("abbrev") else "type", s).rstrip(".")
        return "Declares carrier set " + name + ".  EasyCrypt will type-check all later functions and games over this mathematical domain."
    if s.startswith("op ") or s.startswith("pred "):
        keyword = "pred" if s.startswith("pred ") else "op"
        name = first_name_after(keyword, s)
        if " distr" in s:
            return "Defines " + name + " as a distribution-valued object; later probability proofs rely on its losslessness, support, or point bounds."
        if ": bool" in s or keyword == "pred":
            return "Defines predicate " + name + ", an event or well-formedness condition used in later implications and game proofs."
        if ": real" in s:
            return "Defines real-valued term " + name + ", usually a loss, probability bound, or advantage expression."
        if ": int" in s:
            return "Defines integer-valued parameter " + name + ", used for dimensions, budgets, support sizes, or bounds."
        return "Defines operation " + name + ", a total mathematical function or abbreviation used by later declarations."
    if s.startswith("lemma "):
        name = first_name_after("lemma", s)
        return "States checked lemma " + name + ".  The following proof script must derive this proposition from prior definitions and lemmas."
    if s.startswith("equiv "):
        name = first_name_after("equiv", s)
        return "States relational equivalence " + name + ".  Mathematically it couples two programs and proves their final states or results are related."
    if s.startswith("hoare"):
        return "Starts or states a Hoare proof: every terminating run from a precondition must satisfy the postcondition."
    if s.startswith("phoare"):
        return "Starts or states a probabilistic Hoare proof with an explicit probability bound."
    if s == "proof.":
        return "Begins the proof script for the preceding proposition."
    if s == "qed.":
        return "Ends the proof; EasyCrypt has accepted all remaining obligations."
    if s.startswith("move=>"):
        return "Introduces universally quantified variables or hypotheses into the proof context."
    if s.startswith("rewrite"):
        return "Rewrites the goal using definitions or previously proved equalities, exposing the intended mathematical normal form."
    if s.startswith("apply"):
        return "Applies an existing theorem, lemma, or proof rule to reduce the current goal to its premises."
    if s.startswith("have "):
        return "Creates an intermediate claim.  This mirrors a mathematical proof that first proves a sub-inequality or invariant."
    if s.startswith("suff "):
        return "Replaces the current goal by a sufficient intermediate statement."
    if s.startswith("pose "):
        return "Introduces a local abbreviation to keep the mathematical expression manageable."
    if s.startswith("case") or s.startswith("elim"):
        return "Performs case analysis or induction, splitting the mathematical proof by constructors or list structure."
    if s.startswith("split"):
        return "Splits a conjunction or structured goal into independent proof obligations."
    if s.startswith("left") or s.startswith("right"):
        return "Chooses one side of a disjunction or sum-type proof obligation."
    if s.startswith("by "):
        return "Discharges the current goal in one step using the cited simplification, lemma, or automation."
    if s.startswith("+") or s.startswith("-"):
        return "Solves a proof branch produced by a previous split, transitivity, or case analysis."
    if s.startswith("auto"):
        return "Uses EasyCrypt automation for routine logical, arithmetic, or definitional obligations."
    if s.startswith("smt"):
        return "Calls SMT automation for first-order arithmetic, list, or algebraic side conditions."
    if s.startswith("progress"):
        return "Breaks the goal into simpler subgoals and introduces available hypotheses."
    if s.startswith("wp"):
        return "Applies weakest-precondition reasoning to a program fragment."
    if s.startswith("call"):
        return "Uses a procedure specification or adversary call rule inside a program logic proof."
    if s.startswith("inline"):
        return "Unfolds a procedure body so the proof can reason about its concrete commands."
    if s.startswith("seq"):
        return "Splits a program proof at a command sequence boundary."
    if s.startswith("if"):
        return "Splits proof obligations according to a conditional branch in the program or formula."
    if s.startswith("while"):
        return "Starts loop-invariant reasoning for a while loop."
    if s.startswith("skip"):
        return "Discharges a program-logic step where no state-changing command remains."
    if s.startswith("proc"):
        return "Enters procedure-body proof mode for a module procedure."
    if s.startswith("sp"):
        return "Performs symbolic program simplification, exposing assignments and state updates."
    if "<$" in s:
        return "Samples from a distribution.  Mathematically this introduces a random variable with the named law."
    if "Pr[" in s:
        return "Refers to a probability of an event in an EasyCrypt game; this is the central object of the security bound."
    if "<=" in s:
        return "Part of an inequality, usually comparing probabilities or bounding a concrete loss term."
    if "forall" in s:
        return "Part of a universal mathematical condition that must hold for all listed values."
    if "=>" in s:
        return "Introduces implication structure: later proof steps may assume the antecedent to prove the conclusion."
    if "=" in s:
        return "Part of an equality or definition, identifying two mathematical expressions or assigning a program value."
    return "Continuation line in the current declaration or proof.  Read it with surrounding lines as part of the same mathematical object."


def document_for(file_name: str, lines: list[str], today: str) -> str:
    role, strategy = ROLE.get(file_name, ("Manifest EasyCrypt file.", "Read with the manifest dependency order."))
    title = "Line-by-Line Mathematical Guide for " + file_name
    rows = []
    for idx, line in enumerate(lines, 1):
        source = tex_escape(line) if line else r"\emph{blank}"
        explanation = tex_escape(explain(line))
        rows.append(f"{idx} & {{\\ttfamily\\scriptsize {source}}} & {explanation} \\\\")
    body = "\n".join(rows)
    return rf"""\documentclass[10pt]{{article}}
\usepackage[T1]{{fontenc}}
\usepackage[utf8]{{inputenc}}
\usepackage{{lmodern}}
\usepackage[landscape,margin=0.45in]{{geometry}}
\usepackage{{array,booktabs,longtable,hyperref,xcolor}}
\setlength{{\emergencystretch}}{{3em}}
\newcolumntype{{L}}[1]{{>{{\raggedright\arraybackslash}}p{{#1}}}}
\newcommand{{\file}}[1]{{\nolinkurl{{#1}}}}
\hypersetup{{colorlinks=true,linkcolor=blue!55!black,urlcolor=blue!55!black}}
\title{{{tex_escape(title)}}}
\author{{Generated HAETAE EasyCrypt proof guide}}
\date{{{today}}}
\begin{{document}}
\maketitle

\section*{{File Role}}
{tex_escape(role)}

\section*{{How To Read This Script}}
{tex_escape(strategy)}

\section*{{Line-by-Line Mathematical Reading}}
Each row preserves one EasyCrypt source line and gives the intended mathematical
or proof-script reading.  Blank rows are kept because they mark proof structure
in long EasyCrypt developments.

\scriptsize
\setlength{{\tabcolsep}}{{3pt}}
\begin{{longtable}}{{r L{{0.53\textwidth}} L{{0.37\textwidth}}}}
\toprule
\textbf{{Line}} & \textbf{{EasyCrypt source}} & \textbf{{Mathematical reading}} \\
\midrule
\endfirsthead
\toprule
\textbf{{Line}} & \textbf{{EasyCrypt source}} & \textbf{{Mathematical reading}} \\
\midrule
\endhead
{body}
\bottomrule
\end{{longtable}}

\end{{document}}
"""


def index_document(files: list[str], today: str) -> str:
    rows = []
    for file_name in files:
        path = PROOF_DIR / file_name
        line_count = len(path.read_text(encoding="utf-8").splitlines())
        guide_name = file_name.replace(".ec", "-line-by-line-guide.tex")
        role = ROLE.get(file_name, ("Manifest EasyCrypt file.", ""))[0]
        rows.append(
            f"\\file{{{tex_escape(file_name)}}} & {line_count} & "
            f"\\file{{{tex_escape(guide_name)}}} & {tex_escape(role)} \\\\"
        )
    return rf"""\documentclass[11pt]{{article}}
\usepackage[T1]{{fontenc}}
\usepackage[utf8]{{inputenc}}
\usepackage{{lmodern}}
\usepackage[margin=1in]{{geometry}}
\usepackage{{array,booktabs,longtable,hyperref}}
\newcolumntype{{L}}[1]{{>{{\raggedright\arraybackslash}}p{{#1}}}}
\newcommand{{\file}}[1]{{\nolinkurl{{#1}}}}
\hypersetup{{colorlinks=true,linkcolor=blue!55!black,urlcolor=blue!55!black}}
\title{{HAETAE Line-by-Line EasyCrypt Mathematical Guides}}
\author{{Generated from provable-security/proof-files.txt}}
\date{{{today}}}
\begin{{document}}
\maketitle

This folder contains one LaTeX guide for each EasyCrypt file in the
provable-security manifest.  Each guide preserves every source line and gives a
mathematical or proof-script reading of that line.  The guides are explanatory
documents; the checked artifact remains the EasyCrypt files compiled by
\file{{provable-security/verify-provable-security.sh}}.

\begin{{longtable}}{{L{{0.24\textwidth}} r L{{0.28\textwidth}} L{{0.34\textwidth}}}}
\toprule
\textbf{{EasyCrypt file}} & \textbf{{Lines}} & \textbf{{Guide}} & \textbf{{Role}} \\
\midrule
\endfirsthead
\toprule
\textbf{{EasyCrypt file}} & \textbf{{Lines}} & \textbf{{Guide}} & \textbf{{Role}} \\
\midrule
\endhead
{chr(10).join(rows)}
\bottomrule
\end{{longtable}}

\section*{{Regenerating}}
From \file{{haetae-security}}, run:
\begin{{verbatim}}
python3 guide/generate-line-by-line-guides.py
\end{{verbatim}}

\section*{{Building PDFs}}
From \file{{guide/line-by-line}}, run:
\begin{{verbatim}}
make all
# or build one companion:
make HAETAE_Security-line-by-line-guide.pdf
\end{{verbatim}}

\end{{document}}
"""


def makefile() -> str:
    return """TEXS := $(wildcard *-line-by-line-guide.tex)
PDFS := $(TEXS:.tex=.pdf)

.PHONY: all index clean

index: index.pdf

all: index.pdf $(PDFS)

%.pdf: %.tex
\tpdflatex -interaction=nonstopmode -halt-on-error $<
\tpdflatex -interaction=nonstopmode -halt-on-error $<

clean:
\trm -f *.aux *.log *.out *.toc *.pdf
"""


def main() -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    files = manifest_files()
    today = _dt.date.today().isoformat()
    for file_name in files:
        lines = (PROOF_DIR / file_name).read_text(encoding="utf-8").splitlines()
        guide_name = file_name.replace(".ec", "-line-by-line-guide.tex")
        (OUT_DIR / guide_name).write_text(document_for(file_name, lines, today), encoding="utf-8")
    (OUT_DIR / "index.tex").write_text(index_document(files, today), encoding="utf-8")
    (OUT_DIR / "Makefile").write_text(makefile(), encoding="utf-8")
    print(f"generated {len(files)} line-by-line guides in {OUT_DIR}")


if __name__ == "__main__":
    main()
