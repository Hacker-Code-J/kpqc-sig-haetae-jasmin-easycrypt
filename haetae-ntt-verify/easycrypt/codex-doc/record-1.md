• Based on the current EasyCrypt workspace, the remaining work splits into two groups: explicit unfinished lemmas already in the code, and proof obligations that are not written yet but are
  necessary to finish a full Jasmin-correctness proof.

  Explicit Open Items

  - Prove ntt_spec_ll in NTT_Fq.ec:108. This is the losslessness of the imperative forward NTT spec.
  - Prove invntt_spec_ll in NTT_Fq.ec:113. This is the losslessness of the imperative inverse NTT spec.
  - Prove exp_zroot_256 in NTT_Fq.ec:217. This is the HAETAE-specific root-of-unity fact needed to justify the inverse final scaling.

  Still Needed For A Full Jasmin-Correctness Proof

  - Define the state relation between Jasmin arrays BArray1024.t / W32.t and mathematical coefficient arrays coeff Array256.t. Without this bridge, the Jasmin code in extract/Hpoly_extract.ec:210
    cannot be connected to the EasyCrypt specs in NTT_Fq.ec:46.
  - Prove that the extracted Jasmin tables jzetas and jzetas_inv match the mathematical HAETAE twiddle tables zetas_vals and zetas_inv_vals; the constants exist on both sides, but the cross-
    representation proof is still missing. Relevant files: extract/Hpoly_extract.ec:9, NTT_Fq.ec:224, NTT_Fq.ec:328.
  - Prove a single-butterfly correctness lemma for forward NTT, using fqmul_corr, add_corr, and sub_corr from Fq.ec:317, Fq.ec:494, and Fq.ec:515.
  - Prove a single-butterfly correctness lemma for inverse NTT, including the final multiply by jzetas_inv[255] in extract/Hpoly_extract.ec:296.
  - Prove the nested loop invariants for _poly_ntt in extract/Hpoly_extract.ec:210, showing it refines NTT.ntt from NTT_Fq.ec:46.
  - Prove the nested loop invariants for _poly_invntt in extract/Hpoly_extract.ec:254, showing it refines NTT.invntt from NTT_Fq.ec:71.
  - Prove wrapper correctness for poly_ntt_jazz and poly_invntt_jazz in extract/Hpoly_extract.ec:322 and extract/Hpoly_extract.ec:327.
  - Prove that the imperative specs NTT.ntt and NTT.invntt implement the abstract HAETAE NTT operators Rq.ntt and Rq.invntt from Rq.ec:89 and Rq.ec:95. The comments in Rq.ec explicitly say this
    proof is intended, but it has not been written.
  - State and prove the final end-to-end theorems: Jasmin forward NTT equals the HAETAE mathematical NTT, and Jasmin inverse NTT equals the HAETAE mathematical inverse NTT, under the chosen
    representation relation.

  So the short version is: there are only 3 explicit admits, but the main missing work is the full refinement chain Jasmin code -> imperative NTT spec -> abstract HAETAE NTT spec.


  ---

1. Prove ntt_spec_ll in NTT_Fq.ec:108.
2. Prove invntt_spec_ll in NTT_Fq.ec:113.
3. Prove exp_zroot_256 in NTT_Fq.ec:217.
   Relevant files: extract/Hpoly_extract.ec:98, NTT_Fq.ec:274, NTT_Fq.ec:328.
4. Prove that jzetas_inv matches the mathematical inverse twiddle table zetas_inv / zetas_inv_vals.
   Relevant files: extract/Hpoly_extract.ec:9, NTT_Fq.ec:150, NTT_Fq.ec:224.
5. Prove a forward-butterfly correctness lemma using fqmul_corr, add_corr, and sub_corr from Fq.ec:317.
6. Prove an inverse-butterfly correctness lemma, including the final scaling multiply by jzetas_inv[255].
7. Prove loop invariants for _poly_ntt and show it refines NTT.ntt.
   Relevant files: extract/Hpoly_extract.ec:210, NTT_Fq.ec:46.
8.  Prove loop invariants for _poly_invntt and show it refines NTT.invntt.
   Relevant files: extract/Hpoly_extract.ec:254, NTT_Fq.ec:71.
9.  Prove wrapper correctness for poly_ntt_jazz and poly_invntt_jazz.
   Relevant file: extract/Hpoly_extract.ec:322.
10. Prove that the imperative specs NTT.ntt and NTT.invntt implement the abstract HAETAE specs Rq.ntt and Rq.invntt.
   Relevant file: Rq.ec:89.
11. State and prove the final end-to-end theorems:
   Jasmin forward NTT = HAETAE mathematical Rq.ntt.
   Jasmin inverse NTT = HAETAE mathematical Rq.invntt.

---

• Dependency-Ordered Checklist

  1. Prove the easy prerequisites in NTT_Fq.ec:108:
     ntt_spec_ll and invntt_spec_ll.
  2. Prove the remaining algebra fact in NTT_Fq.ec:217:
     exp_zroot_256.
  3. Define the representation relation from Jasmin state to EasyCrypt math objects:
     BArray1024.t / W32.t -> coeff Array256.t.
  4. Prove the twiddle-table bridge for the forward NTT:
     jzetas in extract/Hpoly_extract.ec:98
     matches zetas / zetas_vals in NTT_Fq.ec:274.
  5. Prove the twiddle-table bridge for the inverse NTT:
     jzetas_inv in extract/Hpoly_extract.ec:9
     matches zetas_inv / zetas_inv_vals in NTT_Fq.ec:150.
  6. Prove a forward butterfly correctness lemma using the arithmetic results already in Fq.ec:317.
  7. Prove an inverse butterfly correctness lemma, including the final scaling by jzetas_inv[255].
  8. Prove _poly_ntt refines the imperative spec NTT.ntt by establishing the nested loop invariants.
     Files: extract/Hpoly_extract.ec:210, NTT_Fq.ec:46.
  9. Prove _poly_invntt refines the imperative spec NTT.invntt by establishing the nested loop invariants.
     Files: extract/Hpoly_extract.ec:254, NTT_Fq.ec:71.
  10. Prove the trivial wrapper correctness for poly_ntt_jazz and poly_invntt_jazz in extract/Hpoly_extract.ec:322.
  11. Prove the imperative specs NTT.ntt and NTT.invntt implement the abstract HAETAE specs Rq.ntt and Rq.invntt in Rq.ec:89.
  12. Finish with the end-to-end theorems:
     Jasmin forward NTT = Rq.ntt.
     Jasmin inverse NTT = Rq.invntt.

  Suggested phase split

  - Phase 1: admits and root/twiddle facts.
  - Phase 2: representation lemmas.
  - Phase 3: Jasmin-to-imperative refinement.
  - Phase 4: imperative-to-abstract refinement.
  - Phase 5: final end-to-end theorems.

  If useful, I can turn this into a proof plan with candidate lemma names and what each invariant should state.

---

• The final goal is:

  Prove, in Hoare logic, that the Jasmin routines poly_ntt_jazz and poly_invntt_jazz are equivalent to the EasyCrypt NTT specification, under a suitable relation between concrete machine state and
  mathematical polynomial state.

  With that goal in mind, each step exists for a specific reason:

  1. Prove ntt_spec_ll and invntt_spec_ll.
     Purpose: Hoare-style refinement proofs are easier when the specification procedures are known to terminate and be lossless. These lemmas remove proof obligations about abnormal control flow and
     let the later simulation proofs focus on state transformation only.
  2. Prove exp_zroot_256.
     Purpose: The inverse NTT proof needs the algebraic fact that the chosen HAETAE root has the right order. Without this, the final scaling step in the inverse transform cannot be justified as the
     mathematically correct normalization factor.
  3. Define the representation relation between Jasmin arrays and EasyCrypt coefficient arrays.
     Purpose: Hoare logic compares program states. The Jasmin code works over BArray1024.t and W32.t, while the EasyCrypt spec works over coeff Array256.t. A representation predicate is the bridge
     that says when a concrete memory state denotes a given mathematical polynomial.
  4. Prove that jzetas matches the EasyCrypt forward twiddle table.
     Purpose: In the forward Hoare proof, every concrete read from jzetas must be rewritten as the mathematical twiddle factor used by the EasyCrypt spec. This is how constant loads in Jasmin become
     abstract root-of-unity multiplications in the proof.
  5. Prove that jzetas_inv matches the EasyCrypt inverse twiddle table.
     Purpose: Same reason as Step 4, but for inverse NTT. This step is especially important because jzetas_inv[255] also implements the final normalization/scaling constant.
  6. Prove a forward butterfly correctness lemma.
     Purpose: The core Hoare proof for _poly_ntt is a loop proof. Its atomic state update is one butterfly. You need a local lemma showing that one concrete Jasmin butterfly step implements one
     abstract NTT butterfly step.
  7. Prove an inverse butterfly correctness lemma.
     Purpose: This is the inverse analogue of Step 6. It justifies the local transition used in the loop invariant for _poly_invntt, including the multiply by the inverse twiddle and the final
     scaling phase.
  8. Prove loop invariants for _poly_ntt and refine it to NTT.ntt.
     Purpose: Hoare logic proves whole loops by invariants. This step lifts the one-butterfly result from Step 6 to the full forward Jasmin routine, showing the entire concrete program matches the
     imperative EasyCrypt forward spec.
  9. Prove loop invariants for _poly_invntt and refine it to NTT.invntt.
     Purpose: Same as Step 8, but for inverse NTT. This is the full Hoare refinement proof for the inverse Jasmin core routine.
  10. Prove wrapper correctness for poly_ntt_jazz and poly_invntt_jazz.
     Purpose: The exported Jasmin entry points are wrappers around the core routines. These proofs are usually simple, but they are needed so the final equivalence theorem talks about the actual
     public Jasmin procedures, not only internal helpers.
  11. Prove that NTT.ntt and NTT.invntt implement Rq.ntt and Rq.invntt.
     Purpose: The Jasmin proof will first land on the imperative EasyCrypt procedures because they mirror the program structure. This step connects those imperative specs to the abstract
     mathematical NTT definitions. Without it, you only get “Jasmin = imperative model,” not “Jasmin = mathematical specification.”
  12. Compose everything into the final end-to-end equivalence theorem.
     Purpose: This is the final Hoare-logic conclusion:
     concrete Jasmin state
     -> via representation relation
     -> Jasmin routine
     -> imperative EasyCrypt NTT model
     -> abstract EasyCrypt NTT specification.
     This step is where all earlier lemmas are assembled into the statement you ultimately want: the Jasmin implementation is correct with respect to the EasyCrypt NTT specification.

  In short, the proof pipeline is:

  1. establish algebraic facts and losslessness,
  2. define the concrete-to-abstract state relation,
  3. prove single-step butterfly correctness,
  4. lift that to full-loop Hoare proofs for Jasmin,
  5. connect the imperative EasyCrypt model to the mathematical NTT spec,
  6. compose the chain into the final equivalence theorem.

---

| Step | Task | Why It Is Needed | Role In Final Hoare-Logic Equivalence Proof |
  |---|---|---|---|
  | 1 | Prove ntt_spec_ll and invntt_spec_ll | The EasyCrypt imperative specs must be known to terminate cleanly and behave losslessly. | Lets the later refinement proofs treat NTT.ntt and
  NTT.invntt as well-formed target procedures in Hoare reasoning. |
  | 2 | Prove exp_zroot_256 | The inverse NTT uses a specific HAETAE root-of-unity fact. The final normalization depends on this algebraic identity. | Justifies that the inverse routine’s final
  scaling is mathematically correct. |
  | 3 | Define the representation relation between Jasmin state and EasyCrypt polynomial state | Jasmin manipulates machine words and byte arrays, while the spec uses field elements in coeff
  Array256.t. A relation is needed to compare them. | This is the central abstraction bridge in the Hoare statement: when does a concrete memory state represent a mathematical polynomial? |
  | 4 | Prove jzetas matches the mathematical forward twiddle table | The Jasmin program reads concrete constants; the spec uses abstract roots of unity. These must be identified as the same values.
  | Allows concrete table reads in Jasmin to be rewritten as spec-level twiddle multiplications in the forward proof. |
  | 5 | Prove jzetas_inv matches the mathematical inverse twiddle table | Same issue as Step 4, but for inverse NTT, including the last scaling constant. | Allows the inverse Jasmin proof to connect
  table reads and final scaling to the abstract inverse NTT constants. |
  | 6 | Prove a forward butterfly correctness lemma | The forward NTT loop is built from repeated butterfly updates. The local step must be proved correct first. | Supplies the atomic Hoare step
  used inside the loop invariant proof for forward NTT. |
  | 7 | Prove an inverse butterfly correctness lemma | The inverse NTT loop also reduces to repeated local butterfly transitions plus scaling behavior. | Supplies the atomic Hoare step used inside
  the loop invariant proof for inverse NTT. |
  | 8 | Prove loop invariants for _poly_ntt and show refinement to NTT.ntt | Local butterfly correctness is not enough; the whole nested-loop schedule must be shown to preserve the right partial-
  transform meaning. | Produces the main forward refinement theorem: Jasmin core forward NTT matches the imperative EasyCrypt forward spec. |
  | 9 | Prove loop invariants for _poly_invntt and show refinement to NTT.invntt | Same as Step 8, but for inverse NTT, where the loop order and final scaling differ. | Produces the main inverse
  refinement theorem: Jasmin core inverse NTT matches the imperative EasyCrypt inverse spec. |
  | 10 | Prove wrapper correctness for poly_ntt_jazz and poly_invntt_jazz | The exported procedures are wrappers around internal cores. The final theorem should talk about the public Jasmin entry
  points. | Lifts core-routine correctness to the actual Jasmin procedures that are meant to implement NTT. |
  | 11 | Prove NTT.ntt and NTT.invntt implement Rq.ntt and Rq.invntt | The imperative EasyCrypt model mirrors code structure, but the real specification lives in the abstract ring-level operators in
  Rq.ec. | Connects “Jasmin = imperative model” to “Jasmin = mathematical EasyCrypt specification.” |
  | 12 | Compose the final end-to-end theorem | All previous lemmas establish links in a chain, but they must be composed into one correctness statement. | Yields the final result: under the
  representation relation, Jasmin NTT is equivalent to the EasyCrypt NTT specification in Hoare logic. |

  Overall proof flow

  | Phase | Purpose |
  |---|---|
  | Foundations | Steps 1-2 establish proof-side prerequisites: losslessness and root-of-unity facts. |
  | Abstraction bridge | Steps 3-5 connect concrete Jasmin data to abstract EasyCrypt mathematical objects. |
  | Local program correctness | Steps 6-7 prove one butterfly step is implemented correctly. |
  | Whole-program refinement | Steps 8-10 lift local correctness to the full Jasmin procedures. |
  | Spec connection | Step 11 links the imperative EasyCrypt model to the abstract NTT specification. |
  | Final composition | Step 12 combines all pieces into the final equivalence theorem. |

  ---

  | Step | Lemma / Theorem Name | Precondition | Postcondition | Depends On |
  |---|---|---|---|---|
  | 1 | ntt_spec_ll | None | islossless NTT.ntt | Structure of NTT.ntt |
  | 2 | invntt_spec_ll | None | islossless NTT.invntt | Structure of NTT.invntt |
  | 3 | exp_zroot_256 | None | Zq.exp zroot 256 = incoeff (-1) | HAETAE parameters, zroot, field arithmetic |
  | 4 | rep_poly256 or repr_poly | Concrete array rp : BArray1024.t | Defines when rp represents an abstract polynomial p : coeff Array256.t | Word-to-field conversion conventions |
  | 5 | jzetas_repr | Forward table jzetas in Jasmin memory | Each read from jzetas[k] corresponds to zetas_vals.[k] or the intended zetas.[k] value | rep_poly256, zetasE, zetas_vals |
  | 6 | jzetas_inv_repr | Inverse table jzetas_inv in Jasmin memory | Each read from jzetas_inv[k] corresponds to zetas_inv_vals.[k], including index 255 for scaling | rep_poly256, zetas_invE,
  zetas_inv_vals, scale255E, exp_zroot_256 |
  | 7 | forward_butterfly_corr | Concrete operands represent abstract coeffs; current twiddle read matches abstract twiddle | One Jasmin forward butterfly step produces the same abstract state
  update as one spec butterfly | fqmul_corr, add_corr, sub_corr, jzetas_repr |
  | 8 | inverse_butterfly_corr | Concrete operands represent abstract coeffs; current inverse twiddle read matches abstract twiddle | One Jasmin inverse butterfly step produces the same abstract
  state update as one inverse-spec butterfly | fqmul_corr, add_corr, sub_corr, jzetas_inv_repr |
  | 9 | _poly_ntt_corr or poly_ntt_core_corr | repr_poly rp p at entry | After _poly_ntt, resulting concrete array represents NTT.ntt p zetas | ntt_spec_ll, forward_butterfly_corr, loop invariants,
  jzetas_repr |
  | 10 | _poly_invntt_corr or poly_invntt_core_corr | repr_poly rp p at entry | After _poly_invntt, resulting concrete array represents NTT.invntt p zetas_inv | invntt_spec_ll,
  inverse_butterfly_corr, loop invariants, jzetas_inv_repr, exp_zroot_256 |
  | 11 | poly_ntt_jazz_corr and poly_invntt_jazz_corr | Entry-state representation relation | Public wrappers preserve the same postcondition as the core routines | _poly_ntt_corr, _poly_invntt_corr
  |
  | 12 | ntt_imperative_spec_corr | Abstract input polynomial p | NTT.ntt p zetas = Rq.ntt p | Structure of imperative NTT, zetas facts, algebraic NTT arguments |
  | 13 | invntt_imperative_spec_corr | Abstract input polynomial p | NTT.invntt p zetas_inv = Rq.invntt p | Structure of imperative inverse NTT, zetas_inv facts, scaling proof |
  | 14 | poly_ntt_jazz_eq_easycrypt | repr_poly rp p at entry | Running poly_ntt_jazz yields a concrete state representing Rq.ntt p | poly_ntt_jazz_corr, ntt_imperative_spec_corr |
  | 15 | poly_invntt_jazz_eq_easycrypt | repr_poly rp p at entry | Running poly_invntt_jazz yields a concrete state representing Rq.invntt p | poly_invntt_jazz_corr, invntt_imperative_spec_corr |

  How to read the dependency chain

  | Layer | Main Goal |
  |---|---|
  | Foundational lemmas | Make the spec procedures usable in Hoare proofs and discharge the root/scaling arithmetic facts. |
  | Representation lemmas | Relate machine arrays and constants to mathematical arrays and twiddle factors. |
  | Local correctness lemmas | Show one concrete butterfly matches one abstract butterfly. |
  | Loop refinement lemmas | Lift local correctness to the full Jasmin core routines. |
  | Spec-connection lemmas | Show the imperative EasyCrypt routines equal the abstract Rq specification. |
  | Final theorems | Compose both halves into “Jasmin implementation = EasyCrypt spec”. |

  A compact Hoare-style final target is:

  { repr_poly rp p }
  poly_ntt_jazz(rp)
  { repr_poly res (Rq.ntt p) }

  { repr_poly rp p }
  poly_invntt_jazz(rp)
  { repr_poly res (Rq.invntt p) }

---

Proof Script Roadmap

  This is the order I would implement the missing proof pieces so the Hoare-logic equivalence proof builds monotonically instead of forcing backtracking.

  | Order | File | Lemma / Item | Why First / What It Unlocks |
  |---|---|---|---|
  | 1 | NTT_Fq.ec:108 | ntt_spec_ll | Trivial structural lemma. Clears one proof-side prerequisite immediately. |
  | 2 | NTT_Fq.ec:113 | invntt_spec_ll | Same reason as above; useful later for phoare/equiv consequences. |
  | 3 | NTT_Fq.ec:217 | exp_zroot_256 | This is the last explicit arithmetic gap. Needed before inverse normalization/scaling arguments. |
  | 4 | NTT_Fq.ec:119 | Define representation operators: concrete W32/BArray1024 to abstract coeff / Array256 | Everything after this needs a state relation. Do this before any Jasmin proof. |
  | 5 | NTT_Fq.ec:119 | Prove basic representation lemmas: get32/set32 preserve the relation pointwise | These are the workhorse rewrites inside every loop proof. |
  | 6 | NTT_Fq.ec:224 | Forward twiddle bridge: Jasmin jzetas corresponds to zetas_vals | Lets a concrete table read become a spec twiddle. |
  | 7 | NTT_Fq.ec:224 | Inverse twiddle bridge: Jasmin jzetas_inv corresponds to zetas_inv_vals | Same for inverse NTT, including the final scale constant at index 255. |
  | 8 | NTT_Fq.ec:224 | Conversion lemmas connecting Jasmin signed W32.to_sint values to coeff operations | Needed to apply fqmul_corr, add_corr, and sub_corr in a clean way. |
  | 9 | NTT_Fq.ec:224 | Forward single-butterfly lemma | First real local correctness result. Should use the rep relation and forward twiddle bridge. |
  | 10 | NTT_Fq.ec:224 | Inverse single-butterfly lemma | Same as Step 9, but for inverse update order and multiplication site. |
  | 11 | NTT_Fq.ec:224 | Final inverse scaling lemma | Isolate the proof that the final multiply by jzetas_inv[255] equals multiplication by inv(256). Keeps _poly_invntt proof cleaner. |
  | 12 | NTT_Fq.ec:224 | Inner-loop invariant for forward NTT | Proves one block of butterflies is simulated correctly. |
  | 13 | NTT_Fq.ec:224 | Middle/outer-loop invariants for forward NTT | Lifts the butterfly lemma to the whole _poly_ntt. |
  | 14 | NTT_Fq.ec:224 | Theorem _poly_ntt_corr | First full Hoare refinement: Jasmin forward core matches NTT.ntt. |
  | 15 | NTT_Fq.ec:224 | Inner-loop invariant for inverse NTT | Same structure as forward, but with different dataflow. |
  | 16 | NTT_Fq.ec:224 | Middle/outer-loop invariants for inverse NTT | Lifts local inverse correctness to the whole _poly_invntt. |
  | 17 | NTT_Fq.ec:224 | Theorem _poly_invntt_corr | Full Hoare refinement for the inverse core. |
  | 18 | NTT_Fq.ec:224 | Wrapper lemmas poly_ntt_jazz_corr, poly_invntt_jazz_corr | Simple consequence lemmas; leave them until the core proofs are done. |
  | 19 | NTT_Fq.ec:224 | Imperative-to-abstract theorem NTT.ntt = Rq.ntt | This is separate from Jasmin simulation. Do it after the imperative layer is stable. |
  | 20 | NTT_Fq.ec:224 | Imperative-to-abstract theorem NTT.invntt = Rq.invntt | Same for inverse NTT. |
  | 21 | NTT_Fq.ec:224 | Final end-to-end theorems | Compose Steps 14/17/18 with 19/20 to get Jasmin = EasyCrypt spec. |

  Suggested lemma blocks inside NTT_Fq.ec

  1. Losslessness
  2. Representation
  3. Twiddle Table Correspondence
  4. Local Butterfly Correctness
  5. Forward NTT Loop Refinement
  6. Inverse NTT Loop Refinement
  7. Wrapper Correctness
  8. Imperative Spec = Abstract Spec
  9. End-to-End Jasmin Correctness

  What each invariant should track

  | Invariant | Should State |
  |---|---|
  | Forward inner loop | Processed indices in the current (start,len) block already match the imperative butterfly effect; unprocessed indices still match the pre-state for that stage. |
  | Forward outer loop | After each len, the concrete array represents the polynomial after that forward stage of NTT.ntt. |
  | Inverse inner loop | Processed indices in the current block already match one inverse butterfly step with the current inverse twiddle. |
  | Inverse outer loop | After each len, the concrete array represents the polynomial after that inverse stage of NTT.invntt, before final normalization. |
  | Final scaling loop | After processing prefix 0..j-1, those coefficients are already scaled by inv(256), the suffix is unchanged. |

  Most practical implementation order

  1. Finish the 3 explicit gaps.
  2. Write the representation layer.
  3. Prove the twiddle bridges.
  4. Prove one butterfly lemma.
  5. Prove forward full refinement.
  6. Prove inverse full refinement.
  7. Prove wrapper lemmas.
  8. Prove imperative-to-abstract equivalence.
  9. Compose the final theorems.

