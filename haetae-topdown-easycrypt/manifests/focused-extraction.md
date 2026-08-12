# Focused mode-2 extraction manifest

Generated files are temporary. The scripts under `scripts/` regenerate them
from pinned read-only Jasmin sources, fresh-compile them, and
`verify-all.sh` checks their exact SHA-256 values against
`generated-extractions.sha256`.

## Packer closure

Source:

- `haetae-ref-jasmin/jasmin/keypair.jazz`
- source SHA-256:
  `8b2ddac2862122d1c9d58767cbc5caa2caad39c8f41fa8096d66ffa77b783e01`

Focused roots:

- `_pack_vk_m23`
- `_pack_sk_m23`

Reachable generated helpers include:

- `_pack_vec_eta_to`
- `_pack_vec2_eta_to`
- the packing helpers called by `_pack_vk_m23`

Output:

- `packer-extract/packers/FocusedPackersTarget.ec`
- generated SHA-256:
  `7062715ca8fe449f15632c315cafdb316bddad6c39d01fe1f2da51104db6931c`

Authored proof:

- `ExtractedPackedKeyPrefix.pack_sk_m23_mode2_vk_prefix`
- `pack_vec_eta_to_prefix_frame`
- `pack_vec2_eta_to_prefix_frame`

The call-to-KeyGen lift imports the broader pinned generated parent theory
`KeygenMode2ParentTarget.ec`, SHA-256
`248f8157e348e3f294665d12573a58ee58e860884356bfe82324fda64de5d0b4`,
because a packer-only focused closure cannot contain `_keypair_full_m23`.
That lift proves `keypair_full_m23_mode2_return_prefix` and
`keypair_internal_mode2_return_prefix`. Both generated theories originate from
the same pinned `keypair.jazz`; no copied source is modified.

Status:

- generated packer procedure prefix: **PROVED**
- generated KeyGen-return lift: **PROVED as partial correctness**
- retry termination/distribution: outside this extraction and still open

Script: `scripts/extract-packers.sh`

## Raw/internal mu hash closure

Sources:

- `haetae-ref-jasmin/jasmin/sign.jazz`
  - SHA-256
    `fd58271f3ada888dfcef4bcf89027c986cc91464a7cb8446b6de11e40037ac31`
- `haetae-ref-jasmin/jasmin/verification_transcript.jazz`
  - SHA-256
    `c2a9865274c5bf2ecbc2ccf6d53065e326df1cb848a329b2c378459b762e0cc8`
- included `verification_transcript.jinc`
  - SHA-256
    `a21679636ba3f3b438baee4b0c4def7e67b235d594a27c244d5a2c28a7b07969`

Focused roots:

- Sign: `_sf_mu_rawpre`
- Verify: `__verify_hash_mu`

Reachable helpers used by the authored proof include:

- Sign `_keccak_init_state`, `_keccakf1600`,
  `_sf_shake256_absorb_sk`, `_sf_shake256_absorb_addr`,
  `_sf_shake256_finalize`, `_sf_shake256_squeeze64`
- Verify `_keccak_init_state`, `_keccakf1600`,
  `__verify_shake256_absorb_raw`,
  `__poly_challenge_shake256_finalize`,
  `__poly_challenge_squeeze256_32`

Outputs:

- `mu-hash-extract/sign/SignMuHashTarget.ec`
  - SHA-256
    `c2232e64adf71ee54763f51e11862938c8caa5ca278af30e4c83756091e83aa7`
- `mu-hash-extract/verify/VerifyMuHashTarget.ec`
  - SHA-256
    `fcee969af0b567447c6c9b9c53e29245375ec2bfd54ae11afecdf0a6ebc0ebb7`

Authored proof:

- `ExtractedMuHashPrefix.sign_sk_verify_vk_absorb_mode2`
- `sign_verify_absorb_addr_from_same_state`
- `sign_verify_finalize_from_same_state`
- `sign_verify_keccakf1600_from_same_state`
- `sign_verify_final_squeeze_mu32_prefix`
- `sign_verify_raw_mu_core_prefix`
- `sign_verify_raw_mu_top_wrappers_prefix`
- `ExactMuTopControl.sf_mu_rawpre_refines_raw_top`
- `ExactMuTopControl.verify_hash_mu_raw_refines_raw_top`
- `ExactMuTopControl.sign_verify_generated_raw_mu_prefix`
- `ExactMode2RawMuComposition.keypair_internal_return_reaches_generated_raw_mu_preconditions`

Status:

- actual generated helper chain and raw local wrappers: **PROVED**
- exact generated `_sf_mu_rawpre` / `__verify_hash_mu` raw-branch control
  adapter: **PROVED** as `OBL-MU-TOPLEVEL-CONTROL`
- public-context high-bit branch: **SPECIFIED**

Script: `scripts/extract-mu-hash.sh`

## Challenge transcript closure

Sources are the same pinned Sign and Verify transcript roots.

Selected procedures:

- Sign `_sf_mu_rawpre`, `_sf_mu_preptr`,
  `__sign_challenge_absorb`
- Verify `__verify_hash_mu`, `__verify_challenge_absorb`

Reachability includes the actual Sign/Verify mu32 challenge-absorb procedures.

Outputs:

- `extract/sign/SignTranscriptTarget.ec`
  - SHA-256
    `774bee231f3bf741413cf047a2fde545c1c8036cc6917e693bf5fa477efeabb6`
- `extract/verify/VerifyTranscriptTarget.ec`
  - SHA-256
    `1d2c8b31636584b790592dbf14bf24d0e477fae818440cdc5c81007f4c1c7d40`

Authored proof:

- `ExtractedChallengeAbsorb.sign_verify_mu32_absorb_from_pos64`
- `Mode2MuChallengeComposition.raw_mu_to_challenge_suffix_zero_loss`
- `ExactMode2RawMuComposition.generated_raw_mu_to_challenge_suffix_zero_loss`

The last theorem invokes the actual generated mu hash procedures before the
actual generated challenge-absorb helpers. It establishes only the raw seam
bound `delta_mu_raw_top = 0`; highbits/LSB and the surrounding public APIs are
outside the theorem.

Script: `scripts/extract-transcripts.sh`

## Public API key-memory copy closure

Sources:

- `haetae-ref-jasmin/jasmin/keypair.jazz`, SHA-256
  `8b2ddac2862122d1c9d58767cbc5caa2caad39c8f41fa8096d66ffa77b783e01`
- `haetae-ref-jasmin/jasmin/sign.jazz`, SHA-256
  `fd58271f3ada888dfcef4bcf89027c986cc91464a7cb8446b6de11e40037ac31`
- `haetae-ref-jasmin/jasmin/verify.jazz`, SHA-256
  `789f36e71ab7784cc37de50ceb04f8d59276f3d1a721acdc64a0be0299f18b06`
- shared `haetae-ref-jasmin/jasmin/api.jinc`, SHA-256
  `4d04b8e74c51ff17236460f93103d43d2f9dcbc78b510191aa2c1a6283aba8a0`

Focused roots:

- KeyGen `__kp_api_copy_2080_to_addr`
- KeyGen `__kp_api_copy_2752_to_addr`
- Sign `_api_copy_raw_to_2752_prefix`
- Verify `_api_copy_raw_to_2752_prefix`

Outputs:

- `api-key-extract/keygen/KeygenApiCopyTarget.ec`, SHA-256
  `7cf8d25136d05d51ffc573b5358723bd36557d1c0c3de02a623a4502ab6ffd83`
- `api-key-extract/sign/SignApiCopyTarget.ec`, SHA-256
  `6192ebc6dd3460d838ef196a98c67f57a27008b553ea231a48093945f467062f`
- `api-key-extract/verify/VerifyApiCopyTarget.ec`, SHA-256
  `c74b5a2cdf7c2ae7f47e0313bf275574653274f53eca34d9d5d81a6295719b09`

Authored procedure-level proofs in `ApiKeyMemoryBridge.ec`:

- `keygen_export_vk_mode2_prefix`
- `keygen_export_sk_mode2_prefix`
- `keygen_export_sk_mode2_prefix_frames_vk`
- `sign_import_mode2_sk_prefix`
- `verify_import_mode2_vk_prefix`
- `sign_verify_api_importer_same_inputs`
- `exported_mode2_regions_agree`
- `imported_prefixes_agree`
- `imported_sign_sk_reaches_mu_memory`
- `mode2_api_region_contract_satisfiable`

The generated KeyGen exporters retain `W64.t` pointers. The generated
Sign/Verify importer formal parameters originate as Jasmin `ui64` but are
translated to mathematical `int`; consequently the authored theory exposes
both `valid_region_w64` and `valid_region_int`. The missing whole-public-call
theorem must prove the concrete `W64.to_uint` binding at the caller boundary;
it is not silently identified by an axiom.

Status:

- each actual generated export/import helper theorem: **PROVED**
- SK-export frame preserving a disjoint prior VK region: **PROVED**
- local exported/imported prefix adapters: **PROVED**
- actual-caller export composition, caller pointer binding, and public-call
  orchestration: **PARTIAL** as `OBL-API-KEY-MEMORY-RAW`

Script: `scripts/extract-api-key-memory.sh`

## Week 4 raw/internal ABI caller closure

Pinned source roots and SHA-256 values:

- KeyGen `haetae-ref-jasmin/jasmin/keypair.jazz`:
  `8b2ddac2862122d1c9d58767cbc5caa2caad39c8f41fa8096d66ffa77b783e01`
- Sign `haetae-ref-jasmin/jasmin/sign.jazz`:
  `fd58271f3ada888dfcef4bcf89027c986cc91464a7cb8446b6de11e40037ac31`
- Verify `haetae-ref-jasmin/jasmin/verify.jazz`:
  `789f36e71ab7784cc37de50ceb04f8d59276f3d1a721acdc64a0be0299f18b06`

Focused roots:

- `cryptolab_haetae_mode2_keypair_internal`
- `cryptolab_haetae_mode2_signature_internal`
- `cryptolab_haetae_mode2_verify_internal`

The generated reachable closures contain the requested internal procedures,
including the KeyGen exporters, Sign SK importer and `_sf_mu_rawpre`, and the
Verify raw wrapper, internal verifier, `_sign_verify_tail_m23`, and
`__verify_hash_mu`.

Outputs and generated hashes:

- `raw-api-extract/keygen/RawKeygenApiTarget.ec`:
  `70716a5cf03d343b958e90ed070940739391c88c93e29bb687b2b64636df4565`
- `raw-api-extract/sign/RawSignApiTarget.ec`:
  `5f632a19c7db616ca75f4f2f0b319b1a8ba821f0bd552613f0c77290b19ef02f`
- `raw-api-extract/verify/RawVerifyApiTarget.ec`:
  `b745f8919f2ce8c2ff80e63a2330da6cdcc6cad414f341fe90081b886825142b`

Week 4 authored evidence proves exact extraction identity for the raw Sign and
Verify hash procedures and exact actual-to-trace control for KeyGen and Sign.
The Verify trace is exact through `sign_verify_internal_mode2_jazz`, but its
raw/public caller lift remains named because unpack/norm checks may return
before `_sign_verify_tail_m23`. The KeyGen exporter procedures and their
disjoint frame theorem compile, but the final single-caller sequential Hoare
composition remains a named residual after the direct proof's final
postcondition normalization stalled. These limitations are not extraction
hash mismatches.

Script: `scripts/extract-raw-api-callers.sh`

## Week 5 reuse of the pinned raw-ABI closure

Week 5 does not widen the extraction roots.  Regeneration produces the same
three generated hashes listed above, and `verify-all.sh` compares them with
`manifests/generated-extractions.sha256` before compiling authored targets.
The existing closure is sufficient for the newly compiled procedure-level
results:

## Week 16 transparent direct-keygen harness

Source:

- `haetae-ref-jasmin/jasmin/keypair.jazz`
- source SHA-256:
  `8b2ddac2862122d1c9d58767cbc5caa2caad39c8f41fa8096d66ffa77b783e01`

Generated parent theory boundary:

- `haetae-ref-easycrypt/easycrypt/extract/keygen-mode2-parent/KeygenMode2ParentTarget.ec`
- generated SHA-256:
  `248f8157e348e3f294665d12573a58ee58e860884356bfe82324fda64de5d0b4`

Selected generated procedures:

- `_kp_m23_matrix`
- `_keypair_finalize_m23`

Authored targets:

- `Mode2KeygenCoreEquation.ec`
- `Mode2KeygenNttMulBridge.ec`
- `Mode2KeygenSnapshotAlgebra.ec`

Authored proof boundary:

- `Mode2KeygenCoreEquation.ActualM23MatrixFinalizeSnapshot.run` is a
  transparent two-call harness over the exact generated parent procedures.
- `actual_m23_matrix_finalize_snapshot` proves only the direct matrix output,
  retained transformed-secret scratch, exact finalizer output, and the returned
  tail frames.
- `Mode2KeygenSnapshotAlgebra` is a local arithmetic decomposition hook for the
  returned snapshot. The core theory defines `actual_snapshot_mod2q_zero` and
  proves it through `finalize_semantic_output_snapshot_mod2q_zero`; it does not
  claim the paper key equations.
- `Mode2KeygenNttMulBridge` adds no extraction root or wrapper. It only exposes
  the existing checked `output_row` as the Montgomery `full_invntt` of the
  actual pointwise row words and transports that representation to both rows
  of the direct snapshot harness. It does not identify those words with
  `Agen*sgen`.

Status:

- transparent direct helper composition: **PROVED**
- `output_row`/full-NTT to security-model `Agen * sgen` bridge:
  **STOPPED (`STOP-KG-NTT`)** at the absent odd-root orthogonality/convolution
  theorem and absent `Rq.poly`-to-security-list adapter
- retry, acceptance, packing, and public-API lift: **DEFERRED**

- actual KeyGen caller:
  `RawApiKeygenSequentialExport.keypair_raw_api_exports_matching_prefixes`;
- actual/raw Verify exact mirrors:
  `RawApiVerifyMuTrace.verify_raw_api_exact_mu_trace` and
  `verify_cryptolab_exact_mu_trace`;
- accepted-path control:
  `RawApiVerifyAcceptTrace.verify_full_m23_trace_accept_implies_tail_reached`,
  `verify_raw_api_actual_accept_implies_trace_tail_reached`, and
  `verify_cryptolab_actual_accept_implies_trace_tail_reached`;
- accepted-path descriptor binding:
  `verify_raw_api_actual_accept_binds_hash_inputs` and
  `verify_cryptolab_actual_accept_binds_hash_inputs`;
- generated hash/suffix adapters under caller-trace facts:
  `RawApiAcceptedMuComposition.raw_api_accepting_execution_hash_mu_zero_loss`
  and
  `raw_api_accepting_execution_generated_challenge_suffix_zero_loss`.

The trace observations are ghost state added only inside the authored Week 5
theories.  They do not alter the generated targets, and each exact equivalence
preserves the actual result and `Glob.mem`.  Tail observations are used only
under `tail_reached` or actual success.

Status after Week 5:

- actual KeyGen sequential external prefix: **PROVED as partial correctness**;
- actual raw/cryptolab Verify exact trace: **PROVED**;
- actual Verify accept implies tail and binds hash inputs: **PROVED**;
- accepted trace-bound generated hash/suffix adapters: **PROVED**;
- direct Sign/Verify trace `observed_mu` equality and Sign-output key-region
  frame: **PARTIAL** as `OBL-API-KEY-MEMORY-RAW-ACCEPT`;
- legitimate Sign output tail reach: **SPECIFIED** separately.

No `stores mem 0 ...` witness appears in the Week 5 API composition targets.
Translator soundness remains in the TCB; deterministic extraction hashes are
drift evidence, not a semantic proof of `jasmin2ec`.

## Week 6 reuse of the pinned closures

Week 6 adds no extraction root and regenerates the same focused/raw targets
and hashes above. The new authored results open those generated procedures:

- `RawApiSignOutputFrame.sign_output_copy_exact_and_frames_reused` opens
  `_api_copy_2948_to_raw` from `RawSignApiTarget.ec`;
- `sign_raw_api_frames_reused_regions` transfers the frame through the exact
  raw Sign trace to the actual
  `cryptolab_haetae_mode2_signature_internal` caller;
- `RegionLocalMuTop.sign_verify_generated_raw_mu_prefix_regionwise` targets
  `_sf_mu_rawpre` from `SignMuHashTarget.ec` and `__verify_hash_mu` from
  `VerifyMuHashTarget.ec` directly, under separate global memories;
- `RawApiDirectObservedMu.raw_sign_then_verify_actual_exact_trace` calls the
  actual raw Sign and Verify procedures and relates them to the existing exact
  trace procedures.

Status after Week 6:

- actual Sign output frame: **PROVED as partial correctness**;
- region-local actual generated mu relation: **PROVED**;
- actual sequential Sign/Verify trace control/results/memory: **PROVED**;
- direct post-state relation between the two stored `observed_mu` values:
  **PARTIAL**.

Extraction identity remains justified by the already compiled exact
equivalences and pinned hashes, not by equal procedure names.

## Week 7 mode-2 signature codec closure

Pinned sources and SHA-256 values:

- `haetae-ref-jasmin/jasmin/signature_pack.jazz`:
  `5be7cf26f2dcef07fc3518747315ad02922978199ed06cf0aabe5925af15e9b1`
- `haetae-ref-jasmin/jasmin/signature_unpack.jazz`:
  `384e6899f794663b48e1fcf9af8296655f39dd8e62d8629b5b76bfb03e0f41d0`
- `signature_pack.jinc`:
  `21f3913b471926490ec95a5ee4e3e59a83c071444928748496c7bb25b617730f`
- `signature_unpack.jinc`:
  `b60f042d3e55b1edbb97d9245c84827d470d5be6279bc2d6304dec28351281fd`
- shared `pack.jinc`:
  `a095a458f43d132b7f8032b3a76dc70b3ad00c910b02f0d9c4fdf0f08303074f`
- shared `sparse_encoding.jinc`:
  `818bb2543a3c37740bf42ee8827a297efbd4e38f786feae075ecfceff8127b49`

Focused roots:

- `pack_sig_mode2_full_jazz`
- `unpack_sig_mode2_full_jazz`

The reachable generated closures contain `_pack_sig_full`,
`_unpack_sig_full`, `_pack_sig_prefix`, `_unpack_sig_prefix`,
`_encode_hb_z1_full`, `_decode_hb_z1_full`, `_encode_h_full`, and
`_decode_h_full`.

Outputs and generated hashes:

- `pack/SignaturePackMode2Target.ec`:
  `cec608044cf12611e5fddce4764bf9b582aa03c3ce69caaeb8d453ed4028f8a9`
- `unpack/SignatureUnpackMode2Target.ec`:
  `8780917ae0788d151cd6ccac6713c80da3b0e75018f22b883bfd58a8064d8adf`

The actual wrapper calls fix the common mode-2 parameters to
`1474, 4, 1024, 13, 6, 512, 13, 239, 132, 7, 416`. Authored fresh-compiled
evidence is:

- `Mode2SignaturePrefixPack.pack_sig_prefix_mode2_layout` for the actual
  `_pack_sig_prefix` loops;
- `Mode2SignaturePrefixUnpack.unpack_sig_prefix_mode2_layout` for the actual
  `_unpack_sig_prefix` loops, including the non-target low-array frame; and
- `Mode2SignaturePrefixRoundTrip.pack_unpack_sig_prefix_mode2_roundtrip`, a
  sequential Hoare theorem whose harness calls both generated procedures.

The round trip is partial correctness under `canonical_challenge` and
`canonical_signed_low`. `prefix_codec_preconditions_satisfiable` supplies a
concrete all-zero witness. The pack result's `[1474,2948)` array-frame theorem
is not yet compiled; metadata, padding, and both rANS inverses remain separate
obligations.

Script: `scripts/extract-signature-codec.sh`

## Week 8 HBZ/rANS closure

Pinned read-only sources and SHA-256 values:

- `encoding.jinc`:
  `dff14e57533e50567d24081a3d1107ab184918792334d6836b260cbca23516cd`
- `sparse_encoding.jinc`:
  `818bb2543a3c37740bf42ee8827a297efbd4e38f786feae075ecfceff8127b49`
- `encoding_tables.jinc`:
  `b1d4b2dd07f405769b4ce8448dd71f6b6fd7e7e51bf413c42d2cfa4c0228429a`
- `encoding.jazz`:
  `e800d1d9c59a2470edbb1240e24d8dfb14458b5fb93e5e68d222e08b75eb5cbd`
- `hpoly.jazz`:
  `c2caff5bd9fc61dc96e917ed95dcf8ba5bc001665de63cbf1f73e82ed4e1f4e9`

Focused exported roots:

- `encode_hb_z1_prepare_jazz`
- `decode_hb_z1_apply_jazz`
- `rans_encode_jazz`
- `rans_decode_jazz`
- `encode_hb_z1_mode2_full_jazz`
- `decode_hb_z1_mode2_full_jazz`

Outputs and generated hashes:

- `hbz-codec/HbzPrepareTarget.ec`:
  `b323a373f1370795166d03a1416125b6fae7ef3491af3336cc9bd6895b83a483`
- `hbz-codec/HbzApplyTarget.ec`:
  `f894584a899bbdd1c91493024ae9d627dfb8e50d8fa460d1b37996323d4e9ab2`
- `hbz-codec/RansEncodeTarget.ec`:
  `3184367f5d41196b54e43524a2b04ea709387f30d72e1a3f699a9e33e22cebc5`
- `hbz-codec/RansDecodeTarget.ec`:
  `2659860ffe3dff9dd5d5bb6fd123a6498cf0ad38784088b0c7ab6e62377a3f75`
- `hbz-codec/HbzFullEncodeTarget.ec`:
  `6c085864d31a3cb406b4b0e4be0d87842e8fc2d574b161e1a0dc89953f0882e0`
- `hbz-codec/HbzFullDecodeTarget.ec`:
  `e70c63bee33aeecbda8f5aa46c52ecdd7b1a62e0368ef6e26173c9c49fcd7994`

The full wrappers fix `count=1024`, `m=13`, and `offset=6`.  The focused
closures contain the actual `_encode_hb_z1_full`, `_decode_hb_z1_full`,
`_rans_encode`, `_rans_decode`, prepare/apply leaves, and encoded-suffix copy.
They are compared against the Week 7 signature pack/unpack closures by exact
source and generated procedure bodies, not by procedure names alone.

Script: `scripts/extract-hbz-codec.sh`

## Exact extraction forms

```sh
jasmin2ec --array-model=barray --output-array=PACK_DIR \
  -o PACK_DIR/FocusedPackersTarget.ec \
  -f _pack_vk_m23 -f _pack_sk_m23 \
  haetae-ref-jasmin/jasmin/keypair.jazz

jasmin2ec --array-model=barray --output-array=MU_SIGN_DIR \
  -o MU_SIGN_DIR/SignMuHashTarget.ec \
  -f _sf_mu_rawpre \
  haetae-ref-jasmin/jasmin/sign.jazz

jasmin2ec --array-model=barray --output-array=MU_VERIFY_DIR \
  -o MU_VERIFY_DIR/VerifyMuHashTarget.ec \
  -f __verify_hash_mu \
  haetae-ref-jasmin/jasmin/verification_transcript.jazz

jasmin2ec --array-model=barray --output-array=SIGN_DIR \
  -o SIGN_DIR/SignTranscriptTarget.ec \
  -f _sf_mu_rawpre -f _sf_mu_preptr -f __sign_challenge_absorb \
  haetae-ref-jasmin/jasmin/sign.jazz

jasmin2ec --array-model=barray --output-array=VERIFY_DIR \
  -o VERIFY_DIR/VerifyTranscriptTarget.ec \
  -f __verify_hash_mu -f __verify_challenge_absorb \
  haetae-ref-jasmin/jasmin/verification_transcript.jazz

jasmin2ec --array-model=barray --output-array=API_KEYGEN_DIR \
  -o API_KEYGEN_DIR/KeygenApiCopyTarget.ec \
  -f __kp_api_copy_2080_to_addr -f __kp_api_copy_2752_to_addr \
  haetae-ref-jasmin/jasmin/keypair.jazz

jasmin2ec --array-model=barray --output-array=API_SIGN_DIR \
  -o API_SIGN_DIR/SignApiCopyTarget.ec \
  -f _api_copy_raw_to_2752_prefix \
  haetae-ref-jasmin/jasmin/sign.jazz

jasmin2ec --array-model=barray --output-array=API_VERIFY_DIR \
  -o API_VERIFY_DIR/VerifyApiCopyTarget.ec \
  -f _api_copy_raw_to_2752_prefix \
  haetae-ref-jasmin/jasmin/verify.jazz

jasmin2ec --array-model=barray --output-array=RAW_KEYGEN_DIR \
  -o RAW_KEYGEN_DIR/RawKeygenApiTarget.ec \
  -f cryptolab_haetae_mode2_keypair_internal \
  haetae-ref-jasmin/jasmin/keypair.jazz

jasmin2ec --array-model=barray --output-array=RAW_SIGN_DIR \
  -o RAW_SIGN_DIR/RawSignApiTarget.ec \
  -f cryptolab_haetae_mode2_signature_internal \
  haetae-ref-jasmin/jasmin/sign.jazz

jasmin2ec --array-model=barray --output-array=RAW_VERIFY_DIR \
  -o RAW_VERIFY_DIR/RawVerifyApiTarget.ec \
  -f cryptolab_haetae_mode2_verify_internal \
  haetae-ref-jasmin/jasmin/verify.jazz

jasmin2ec --array-model=barray --output-array=SIG_PACK_DIR \
  -o SIG_PACK_DIR/SignaturePackMode2Target.ec \
  -f pack_sig_mode2_full_jazz \
  haetae-ref-jasmin/jasmin/signature_pack.jazz

jasmin2ec --array-model=barray --output-array=SIG_UNPACK_DIR \
  -o SIG_UNPACK_DIR/SignatureUnpackMode2Target.ec \
  -f unpack_sig_mode2_full_jazz \
  haetae-ref-jasmin/jasmin/signature_unpack.jazz

jasmin2ec --array-model=barray --output-array=HBZ_DIR \
  -o HBZ_DIR/HbzPrepareTarget.ec \
  -f encode_hb_z1_prepare_jazz \
  haetae-ref-jasmin/jasmin/hpoly.jazz

jasmin2ec --array-model=barray --output-array=HBZ_DIR \
  -o HBZ_DIR/HbzApplyTarget.ec \
  -f decode_hb_z1_apply_jazz \
  haetae-ref-jasmin/jasmin/hpoly.jazz

jasmin2ec --array-model=barray --output-array=HBZ_DIR \
  -o HBZ_DIR/RansEncodeTarget.ec \
  -f rans_encode_jazz \
  haetae-ref-jasmin/jasmin/hpoly.jazz

jasmin2ec --array-model=barray --output-array=HBZ_DIR \
  -o HBZ_DIR/RansDecodeTarget.ec \
  -f rans_decode_jazz \
  haetae-ref-jasmin/jasmin/hpoly.jazz

jasmin2ec --array-model=barray --output-array=HBZ_DIR \
  -o HBZ_DIR/HbzFullEncodeTarget.ec \
  -f encode_hb_z1_mode2_full_jazz \
  haetae-ref-jasmin/jasmin/encoding.jazz

jasmin2ec --array-model=barray --output-array=HBZ_DIR \
  -o HBZ_DIR/HbzFullDecodeTarget.ec \
  -f decode_hb_z1_mode2_full_jazz \
  haetae-ref-jasmin/jasmin/encoding.jazz
```

## Week 8 generated table certificate

`scripts/generate-hbz-symbol-certificate.sh` deterministically reads the
literal mode-2 packed symbol table from the focused signature extraction and
emits `Mode2HbzSymbolWordsGenerated.ec`.  The generator is not a trusted
decision procedure: the emitted 512 packed-word leaf lemmas and the final
`actual_mode2_hbz_tables_certified` corollary are fresh-compiled by EasyCrypt.

Pinned hashes are stored in `manifests/generated-certificates.sha256`:

- generator: `b88e96fd445136d5082f6a8033573de0e1d35fe2725066b715114dc34204efbd`
- generated theory: `3f664576f56de9243355413fc9149217484817309accacf72c0865e3d3d6ba90`

`verify-all.sh` regenerates into its temporary work directory, performs a
byte-for-byte comparison, checks both hashes, and only then compiles the
generated theory.

## Trust and drift boundary

The generated hashes ensure deterministic extraction drift is visible, but do
not prove `jasmin2ec` soundness. Translator correctness remains in the trusted
computing base. The broader KeyGen parent target is separately source-hashed
and imported only because its call graph is needed for the return-value lift.

## Week 9 actual rANS reuse

Week 9 does not create a second extraction surface.  It directly reuses the
Week 8 focused generated targets and their pinned hashes:

- `RansEncodeTarget.ec` (`3184367f5d41196b54e43524a2b04ea709387f30d72e1a3f699a9e33e22cebc5`),
- `RansDecodeTarget.ec` (`2659860ffe3dff9dd5d5bb6fd123a6498cf0ad38784088b0c7ab6e62377a3f75`),
- `HbzFullEncodeTarget.ec` (`6c085864d31a3cb406b4b0e4be0d87842e8fc2d574b161e1a0dc89953f0882e0`).

The Week 9 actual harness calls, in order,
`RansEncodeTarget.M._rans_encode`,
`HbzFullEncodeTarget.M.__copy_encoded_suffix` on the actual returned
`off/size`, and `RansDecodeTarget.M._rans_decode`.  Deterministic regeneration,
the generated-target hash check, and the Week 8 procedure-identity comparison
remain part of `scripts/verify-all.sh`.

This extraction reuse establishes procedure identity and drift control only.
It does not fill the still-open encoder/decoder trace-refinement edge.

## Week 10 encoder extraction reuse

Week 10 creates no new extraction boundary and copies no upstream source. It
uses the same pinned `RansEncodeTarget.ec` generated by
`scripts/extract-hbz-codec.sh` from `rans_encode_jazz`; its SHA-256 remains:

```text
3184367f5d41196b54e43524a2b04ea709387f30d72e1a3f699a9e33e22cebc5
```

The direct Hoare theorems in `Mode2RansEncoderTrace.ec` target
`RansEncodeTarget.M._rans_encode`.  The concrete table equality and source
closure are therefore inherited from the Week 8/9 deterministic regeneration
and generated-procedure identity checks.  Week 10 adds authored adapter
theories only; it does not change `generated-extractions.sha256`,
`generated-certificates.sha256`, or `sources.sha256`.

## Week 11 encoder extraction reuse

Week 11 creates no wrapper and no additional extraction. The final direct
Hoare theorem opens the same pinned generated procedure:

```text
RansEncodeTarget.M._rans_encode
generated target SHA-256:
3184367f5d41196b54e43524a2b04ea709387f30d72e1a3f699a9e33e22cebc5
```

`scripts/extract-hbz-codec.sh` still regenerates this target from the exported
`rans_encode_jazz` closure in `haetae-ref-jasmin/jasmin/hpoly.jazz`, and
`verify-all.sh` checks the generated hash and procedure identity against the
signature full-pack extraction. Week 11 changes authored proof theories only;
all source/extraction/certificate hash manifests remain unchanged.

## Week 12 decoder extraction reuse

Week 12 adds no wrapper, copied upstream source, or extraction root. The direct
Hoare theorem opens the pinned focused target:

```text
RansDecodeTarget.M._rans_decode
generated target SHA-256:
2659860ffe3dff9dd5d5bb6fd123a6498cf0ad38784088b0c7ab6e62377a3f75
```

`scripts/extract-hbz-codec.sh` regenerates this target from
`rans_decode_jazz` in the pinned `haetae-ref-jasmin/jasmin/hpoly.jazz` closure.
`verify-all.sh` checks regeneration, generated hash, the existing full-wrapper
procedure-identity boundary, and fresh-compiles
`actual_rans_decode_trace_refinement`. The source and generated manifests are
unchanged because no extraction input or command changed.

## Week 13 composition reuse

Week 13 creates no new extraction target, wrapper, or copied upstream source.
The final harness reuses the same three pinned generated procedures:

```text
RansEncodeTarget.M._rans_encode
  3184367f5d41196b54e43524a2b04ea709387f30d72e1a3f699a9e33e22cebc5
HbzFullEncodeTarget.M.__copy_encoded_suffix
  HbzFullEncodeTarget hash:
  6c085864d31a3cb406b4b0e4be0d87842e8fc2d574b161e1a0dc89953f0882e0
RansDecodeTarget.M._rans_decode
  2659860ffe3dff9dd5d5bb6fd123a6498cf0ad38784088b0c7ab6e62377a3f75
```

`Mode2RansActualHarness.run` contains these calls directly and Week 13 adds
only authored composition lemmas. `verify-all.sh` regenerates the same focused
targets, checks `generated-extractions.sha256`, and checks the generated
procedure identity against the full signature pack/unpack extractions. No
entry in `sources.sha256` or `generated-extractions.sha256` changes.

## Week 14 full-wrapper and signature-boundary reuse

Week 14 adds no extraction root, generated wrapper, or copied upstream source.
It opens the already pinned full focused targets directly:

```text
HbzFullEncodeTarget.M._encode_hb_z1_full
  HbzFullEncodeTarget hash:
  6c085864d31a3cb406b4b0e4be0d87842e8fc2d574b161e1a0dc89953f0882e0
HbzFullDecodeTarget.M._decode_hb_z1_full
  HbzFullDecodeTarget hash:
  e70c63bee33aeecbda8f5aa46c52ecdd7b1a62e0368ef6e26173c9c49fcd7994
```

The production lift opens the existing signature targets directly:

```text
SignaturePackMode2Target.M._encode_hb_z1_full
  SignaturePackMode2Target hash:
  cec608044cf12611e5fddce4764bf9b582aa03c3ce69caaeb8d453ed4028f8a9
SignatureUnpackMode2Target.M._decode_hb_z1_full
  SignatureUnpackMode2Target hash:
  8780917ae0788d151cd6ccac6713c80da3b0e75018f22b883bfd58a8064d8adf
```

`Mode2HbzInternalBoundaries.ec` proves `proc; sim` exact equivalences for the
full-wrapper internal prepare/rANS/apply procedures. The existing
`Mode2HbzActualBoundary.ec` equivalences and the Week 14 production-harness
equivalence connect the focused full-wrapper theorem to the signature
extraction boundary. `verify-all.sh` regenerates both target pairs, checks
`generated-extractions.sha256`, and byte-compares all six relevant procedure
bodies, including both full wrappers. No generated/source hash manifest entry
changes.

## Week 15 fixed-input success-witness reuse

Week 15 adds no extraction root, generated wrapper, table data, or copied
upstream source. The core witness targets the same pinned generated procedure
directly:

```text
RansEncodeTarget.M._rans_encode
  3184367f5d41196b54e43524a2b04ea709387f30d72e1a3f699a9e33e22cebc5
```

The zero-HBZ corollary opens the existing focused full wrapper, and the
production corollary uses the compiled exact focused/production equivalence:

```text
HbzFullEncodeTarget.M._encode_hb_z1_full
  6c085864d31a3cb406b4b0e4be0d87842e8fc2d574b161e1a0dc89953f0882e0
SignaturePackMode2Target.M._encode_hb_z1_full
  cec608044cf12611e5fddce4764bf9b582aa03c3ce69caaeb8d453ed4028f8a9
```

The all-six capacity proof and failure-cause transport are authored EasyCrypt
lemmas over these bodies and the existing deterministic literal table
certificate. `verify-all.sh` regenerates the focused and production targets,
checks their stored hashes and internal procedure identity, regenerates the
table certificate, and fresh-compiles the new Hoare theorems. No source,
generated-extraction, or generated-certificate hash entry changes. This reuse
does not assert fixed-input termination or general encoder losslessness.

## Week 16 Sign accepted-core boundary

Source:

- `haetae-ref-jasmin/jasmin/sign.jazz`
- source hash remains pinned by `sources.sha256`

Focused roots, in the order used by the authored harness:

- `_sf_round_challenge_mode2`
- `_sf_z_check`
- `_sf_hint_mode2`

Output:

- `sign-accepted-core/SignAcceptedCoreTarget.ec`
- generated SHA-256:
  `ebfe228473760f2f0978ef262c6a5d1f5ef5d01307b2cc0f7f76623fb4ab4b1d`

The extraction deliberately selects no hyperball sampler, retry loop,
signature packer, or public API root. `Mode2SignAcceptedCore` directly calls
the three generated helpers and proves only that its accepted-branch flag is
equivalent to the actual `_sf_z_check` return being zero. The paper equations
(S-1)--(S-7) are not claimed: the exact missing semantic leaf is recorded in
`WEEK16_SIGN_REPORT.md`.
