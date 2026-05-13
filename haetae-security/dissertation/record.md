File Structure

  dissertation/
  ├── main.tex                         # Master document + preamble
  ├── Makefile                         # Build: make / make clean / make distclean
  ├── bibliography/
  │   └── refs.bib                     # EasyCrypt, ROM, game-hopping references
  ├── chapters/
  │   ├── titlepage.tex
  │   ├── abstract.tex
  │   ├── acknowledgements.tex
  │   ├── ch01_introduction.tex        # Motivation, problem statement, contributions
  │   ├── ch02_background.tex          # Signatures, ROM, Fiat-Shamir, EasyCrypt
  │   ├── ch03_proof_scope.tex         # provable-security folder and manifest scope
  │   ├── ch04_easycrypt_framework.tex # Modules, judgments, proof style
  │   ├── ch05_security_games.tex      # Sig_ROM and HAETAE_Security theorem chain
  │   ├── ch06_rom_programming.tex     # Lazy ROM, programming sites, bad events
  │   ├── ch07_sampler_freshness.tex   # sampler_bad_prequery and exact hyperball lifting
  │   ├── ch08_transcript_hops.tex     # Transcript games and erasure
  │   ├── ch09_budgeted_lifting.tex    # Query budgets and O.sign lifting
  │   ├── ch10_reductions_bounds.tex   # Concrete reduction terms and arithmetic bounds
  │   ├── ch11_reproducibility.tex     # Verification command and evaluation criteria
  │   ├── ch12_conclusion.tex
  │   └── app_manifest.tex             # Manifest appendix
  └── figures/
      └── README.txt

Proof gate described by the dissertation:

  ../provable-security/proof-files.txt
  ../provable-security/verify-provable-security.sh
  ../provable-security/easycrypt/

Explicitly excluded from the provable-security gate:

  HAETAE_FIPS202_KAT_Empty_Generated.ec
