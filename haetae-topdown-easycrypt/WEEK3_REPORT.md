# Week 3 report

Evidence date: 2026-08-05.

## Sprint goal and outcome

Week 3 targeted one obligation:

```text
OBL-MU-TOPLEVEL-CONTROL
```

The required closure was not a wrapper-level theorem. The actual generated
procedures had to appear directly on the two sides of the final equivalence:

- `SignMuHashTarget.M._sf_mu_rawpre`
- `VerifyMuHashTarget.M.__verify_hash_mu` raw branch

This goal is now closed for the raw/internal path. The resulting raw seam also
closes the actual generated mu32 challenge-suffix composition, so the local
loss statement

```text
delta_mu_raw_top = 0
```

is now justified for the generated raw/internal mu path followed by the
generated position-64 mu32 absorb helpers.

## Newly compiled generated-procedure theorems

### 1. Exact Sign top adapter

Theory:
`easycrypt/refinement/composition/ExactMuTopControl.ec`

Theorem:
`sf_mu_rawpre_refines_raw_top`

Meaning:

```easycrypt
equiv [Sign._sf_mu_rawpre ~ SignWrap.run :
  ={Glob.mem, mup, skp, preaddr, prelen, maddr, mlen} /\
  vkbytes{1} = W64.of_int 992
  ==> ={res, Glob.mem}]
```

This theorem proves that the actual generated `_sf_mu_rawpre` has the same
observable result as the Week 2 raw top wrapper under equal inputs and memory.
The proof explicitly follows generated control:

- local state/stack initialization;
- `_keccak_init_state`;
- `_sf_shake256_absorb_sk`;
- two `_sf_shake256_absorb_addr` calls for pre and message;
- `_sf_shake256_finalize`;
- `_keccakf1600`;
- `protect_ptr`;
- `_sf_shake256_squeeze64`.

The erased scheduling instructions are handled as semantics-preserving parts of
the generated procedure, not by axiom.

### 2. Exact Verify raw-branch adapter

Theory:
`easycrypt/refinement/composition/ExactMuTopControl.ec`

Theorems:

- `raw_prelen_shr63_zero`
- `raw_prelen_branch_guard`
- `verify_hash_mu_raw_refines_raw_top`

Meaning:

```easycrypt
equiv [Verify.__verify_hash_mu ~ VerifyWrap.run :
  ={Glob.mem, mup, vkp, prep, prelen, mp, mlen} /\
  vklen{1} = W64.of_int 992 /\
  raw_prelen prelen{1}
  ==> res{1} = res{2}]
```

`raw_prelen` is the explicit branch predicate:

```easycrypt
raw_prelen prelen :=
  0 <= W64.to_uint prelen /\ W64.to_uint prelen < 2 ^ 63.
```

The proof does not assume `ctxflag = 0`. Instead it proves that the actual
generated shift by 63 yields zero from `raw_prelen`, so the generated Verify
procedure truly takes the raw branch.

### 3. Actual generated Sign/Verify mu-prefix theorem

Theory:
`easycrypt/refinement/composition/ExactMuTopControl.ec`

Theorem:
`sign_verify_generated_raw_mu_prefix`

Meaning:

```easycrypt
equiv [Sign._sf_mu_rawpre ~ Verify.__verify_hash_mu :
  ={Glob.mem} /\
  skp{1} = sk0 /\
  Glob.mem{2} = mem0 /\
  vkp{2} = base /\
  vkbytes{1} = W64.of_int 992 /\
  vklen{2} = W64.of_int 992 /\
  preaddr{1} = prep{2} /\
  prelen{1} = prelen{2} /\
  maddr{1} = mp{2} /\
  mlen{1} = mlen{2} /\
  raw_prelen prelen{2} /\
  valid_region prep{2} prelen{2} /\
  valid_region mp{2} mlen{2} /\
  sk_memory_prefix sk0 mem0 base
  ==> mu32_prefix res{1} res{2}]
```

This is the Week 3 closing theorem for `OBL-MU-TOPLEVEL-CONTROL`. The wrapper
boundary remains an internal proof device only. It is not the conclusion
surface of the theorem.

### 4. Actual generated raw mu to challenge-suffix composition

Theory:
`easycrypt/refinement/composition/ExactMode2RawMuComposition.ec`

Theorems:

- `generated_raw_mu_preconditions_from_keygen_prefix`
- `keypair_internal_return_reaches_generated_raw_mu_preconditions`
- `generated_raw_mu_to_challenge_suffix_zero_loss`

The second theorem compares two composed actual executions:

1. actual `_sf_mu_rawpre` then actual Sign mu32 absorb;
2. actual `__verify_hash_mu` raw branch then actual Verify mu32 absorb.

Its postcondition is exact equality of returned challenge state and position.
The theorem requires:

- equal initial challenge state and position;
- challenge position 64;
- equal raw pre/message pointers and lengths;
- `raw_prelen`;
- the local `sk_memory_prefix`;
- the explicit VK, pre, and message no-wrap premises.

Theorem `generated_raw_mu_preconditions_from_keygen_prefix` packages a
concrete non-vacuity witness from a KeyGen-return prefix relation:

- `base = W64.zero`;
- `prelen = W64.zero`;
- Verify memory obtained by storing the 992-byte VK prefix.

The Hoare theorem
`keypair_internal_return_reaches_generated_raw_mu_preconditions` then consumes
`keypair_internal_mode2_return_prefix` for the actual generated
`crypto_sign_keypair_internal_mode2_jazz` procedure. Thus every terminating
internal mode-2 KeyGen execution supplies the constructed local-array/raw
premises; termination itself is not assumed or concluded.

## Proof decomposition that worked

The direct `inline; sim` approach at the generated top level was rejected after
it repeatedly stalled on generated local-variable scheduling and tail-call
alignment. The successful decomposition was:

1. prove exact generated Sign to wrapper refinement;
2. prove exact generated Verify raw-branch to wrapper refinement;
3. reuse the Week 2 wrapper-level mu-prefix theorem as the middle leg;
4. compose by transitivity;
5. reuse the Week 1 mu32 absorb theorem only after the actual generated mu
   theorem has established the mu-prefix premise.

This keeps all implementation semantics in generated procedures or locally
authored wrappers with proved equivalence. No SHAKE-prefix axiom or other
implementation axiom was introduced.

## Raw/internal path versus public-context path

Week 3 closes only the raw/internal path.

Closed:

- `_sf_mu_rawpre`
- `__verify_hash_mu` raw branch
- actual generated position-64 mu32 absorb composition

Still separate:

- Sign `_sf_prepare_pre_raw` plus `_sf_mu_preptr`
- Verify high-bit/context branch
- requirement `ctxlen <= 255`
- exact encoded-pre equality `ctxlen byte || ctx`

Therefore `MU32-HASH` is now **PROVED** only for the raw/internal path. The
public-context variant remains **SPECIFIED**.

## API memory bridge status

The strong secondary goal made procedure-level progress in
`ApiKeyMemoryBridge.ec`. Focused extraction now contains these actual generated
procedures:

- KeyGen `__kp_api_copy_2080_to_addr` and
  `__kp_api_copy_2752_to_addr`;
- Sign `_api_copy_raw_to_2752_prefix`; and
- Verify `_api_copy_raw_to_2752_prefix`.

The focused generated targets are pinned at SHA-256
`7cf8d251...ffd83` (KeyGen), `6192ebc6...062f` (Sign), and
`c74b5a2c...b09` (Verify); the full values are recorded in
`manifests/generated-extractions.sha256`.

The following fresh-compiled Hoare/equivalence theorems open those procedures
directly:

- `keygen_export_vk_mode2_prefix`: a valid 992-byte KeyGen VK export yields
  `mem2080_prefix` in external memory;
- `keygen_export_sk_mode2_prefix`: a valid 1408-byte KeyGen SK export yields
  `mem2752_prefix` in external memory;
- `keygen_export_sk_mode2_prefix_frames_vk`: the same actual SK exporter also
  preserves an already established VK prefix under the minimal
  `disjoint_regions` premise;
- `sign_import_mode2_sk_prefix`: the generated Sign importer at length 1408
  returns a local array whose first 992 bytes equal external memory;
- `verify_import_mode2_vk_prefix`: the generated Verify importer at length
  992 returns the same kind of prefix relation;
- `sign_verify_api_importer_same_inputs`: the two actual importer procedures
  are equivalent on identical memory, address, and length inputs;
- `exported_mode2_regions_agree`, `imported_prefixes_agree`, and
  `imported_sign_sk_reaches_mu_memory`: the exported/imported byte relations
  imply the exact `sk_memory_prefix` premise of the generated mu theorem.

The address premises are explicit. KeyGen exporters use `W64.t` and
`valid_region_w64`; the Sign/Verify importer roots originate as Jasmin `ui64`
but `jasmin2ec` exposes their address and length parameters as mathematical
`int`, so their theorems use `valid_region_int`. No axiom identifies those two
models.

The whole obligation remains:

```text
OBL-API-KEY-MEMORY-RAW: PARTIAL
```

Two composition steps are still missing:

1. an actual caller theorem that composes the VK export and the framed SK
   export and binds each exporter `W64.to_uint` address to the
   importer `int` address; and
2. public KeyGen/Sign/Verify call-site orchestration and time-sensitive alias
   conditions.

Separation is correctness-critical only for writes that must preserve the
other exported region. The isolated importers are read-only, so mutual
separation of those later calls is not added as a proof-convenience premise.
Aliasing across the unextracted public callers remains explicitly unanalyzed.

## Verification commands and results

Week 3 baseline before edits:

```sh
./haetae-topdown-easycrypt/scripts/verify-all.sh
```

Recorded in:

- `logs/week3-baseline-summary.txt`

Direct Week 3 theorem checks:

```sh
easycrypt compile -script -no-eco -timeout 5 \
  haetae-topdown-easycrypt/easycrypt/refinement/composition/ExactMuTopControl.ec \
  -I /tmp/haetae-week3-mu/sign \
  -I /tmp/haetae-week3-mu/verify \
  -I haetae-ref-easycrypt/easycrypt/extract/keygen-mode2-parent \
  -I haetae-ref-easycrypt/easycrypt/spec \
  -I haetae-security \
  -I haetae-topdown-easycrypt/easycrypt/refinement/composition

easycrypt compile -script -no-eco -timeout 5 \
  haetae-topdown-easycrypt/easycrypt/refinement/composition/ExactMode2RawMuComposition.ec \
  -I /tmp/haetae-week3-tx/sign \
  -I /tmp/haetae-week3-tx/verify \
  -I /tmp/haetae-week3-mu/sign \
  -I /tmp/haetae-week3-mu/verify \
  -I haetae-ref-easycrypt/easycrypt/extract/keygen-mode2-parent \
  -I haetae-ref-easycrypt/easycrypt/spec \
  -I haetae-security \
  -I haetae-topdown-easycrypt/easycrypt/refinement/composition \
  -I haetae-topdown-easycrypt/easycrypt/refinement/keygen \
  -I haetae-topdown-easycrypt/easycrypt/support
```

Both fresh-compilations completed successfully.

The secondary API extraction and theory were checked with:

```sh
TOPDOWN_EXTRACT_DIR=/tmp/week3-api \
  ./haetae-topdown-easycrypt/scripts/extract-api-key-memory.sh

./haetae-topdown-easycrypt/scripts/verify-all.sh
```

The focused extraction, generated targets, and authored theory all passed.
The final integrated run was:

```text
PASS focused extraction regeneration drift
PASS actual API copy-helper reachability source checks
PASS baseline verification
PASS LaTeX research notes build
PASS read-only roots unchanged after verification
RESULT PASS authored-targets=14 cache=-no-eco
RESULT PASS selected-baselines=20 read-only=true
```

No proof hole, authored axiom, debug declaration, undefined LaTeX reference,
or undefined citation was found.

## Final Week 3 status

- `OBL-MU-TOPLEVEL-CONTROL`: **PROVED** for the raw/internal path.
- `MU32-HASH`: **PROVED** for actual generated raw/internal calls.
- `MU-CHAL-COMPOSITION`: **PROVED** for actual generated raw/internal mu plus
  actual position-64 mu32 absorb.
- `delta_mu_raw_top = 0`: **justified locally**.
- public-context path: **SPECIFIED**.
- `API-KEY-COPY-HELPERS`: **PROVED as procedure-level partial correctness**
  for the four selected actual generated export/import helpers, including the
  disjoint SK-write frame over a prior VK region.
- `OBL-API-KEY-MEMORY-RAW`: **PARTIAL**; actual-caller export composition,
  `W64`/`int` binding, and public-call alias orchestration remain open.

## Week 4 go/no-go

Current evidence supports the following gate:

- the selected copy helpers are individually closed, but the public chain is
  still partial, so Week 4 should stay focused on caller composition,
  pointer-binding, and alias reachability;
- highbits/LSB packing and full challenge-call equivalence begin only after
  that composed public chain closes;
- there is no justification to widen the public-context or paper-security
  claim before that bridge is procedure-level.
