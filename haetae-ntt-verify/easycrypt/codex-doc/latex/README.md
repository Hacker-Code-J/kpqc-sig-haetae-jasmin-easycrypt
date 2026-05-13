# LaTeX Notes

This folder collects the mathematically written LaTeX notes for the EasyCrypt
NTT verification effort.

Files:

- `proof-state-report.tex`: status memorandum on the proofs completed and the current blockers.
- `task-formulas-note.tex`: formula dictionary mapping each proof task to its governing identities, invariants, and target theorems.
- `ref-jasmin-ntt-proof-report.tex`: detailed report on the checked `RefJasminNTT.ec` extraction-to-imperative-spec proof.
- `ref-jasmin-ntt-lemma-notes.tex`: mathematician-style proof notes for each lemma and equivalence in `RefJasminNTT.ec`.
- `Makefile`: convenience targets for compiling the notes with `pdflatex`.

Usage:

```sh
cd codex-doc/latex
make
```

This produces:

- `proof-state-report.pdf`
- `task-formulas-note.pdf`
- `ref-jasmin-ntt-proof-report.pdf`
- `ref-jasmin-ntt-lemma-notes.pdf`
