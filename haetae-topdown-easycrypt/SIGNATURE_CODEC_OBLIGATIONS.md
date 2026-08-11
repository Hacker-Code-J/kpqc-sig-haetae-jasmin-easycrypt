# Week 7 signature codec obligations

Date: 2026-08-07

## Pinned mode-2 codec targets

- pack wrapper: `pack_sig_mode2_full_jazz`
- unpack wrapper: `unpack_sig_mode2_full_jazz`
- generated roots:
  `_pack_sig_full`, `_unpack_sig_full`,
  `_pack_sig_prefix`, `_unpack_sig_prefix`

Generated extraction hashes:

- `pack/SignaturePackMode2Target.ec`
  `cec608044cf12611e5fddce4764bf9b582aa03c3ce69caaeb8d453ed4028f8a9`
- `unpack/SignatureUnpackMode2Target.ec`
  `8780917ae0788d151cd6ccac6713c80da3b0e75018f22b883bfd58a8064d8adf`

Pinned source hashes:

- `haetae-ref-jasmin/jasmin/signature_pack.jazz`
  `5be7cf26f2dcef07fc3518747315ad02922978199ed06cf0aabe5925af15e9b1`
- `haetae-ref-jasmin/jasmin/signature_unpack.jazz`
  `384e6899f794663b48e1fcf9af8296655f39dd8e62d8629b5b76bfb03e0f41d0`
- `haetae-ref-jasmin/jasmin/signature_pack.jinc`
  `21f3913b471926490ec95a5ee4e3e59a83c071444928748496c7bb25b617730f`
- `haetae-ref-jasmin/jasmin/signature_unpack.jinc`
  `b60f042d3e55b1edbb97d9245c84827d470d5be6279bc2d6304dec28351281fd`
- shared `pack.jinc`
  `a095a458f43d132b7f8032b3a76dc70b3ad00c910b02f0d9c4fdf0f08303074f`
- shared `sparse_encoding.jinc`
  `818bb2543a3c37740bf42ee8827a297efbd4e38f786feae075ecfceff8127b49`

## Verified mode-2 parameters from actual extracted wrappers

- `sigbytes = 1474`
- `lcount = 4`
- `hb_count = 1024`
- `hb_m = 13`
- `hb_offset = 6`
- `h_count = 512`
- `h_m = 13`
- `h_offset = 239`
- `base_hb = 132`
- `base_h = 7`
- `payload_limit = 416`

## Actual 1474-byte layout confirmed from extracted code

- bytes `[0,32)`: challenge prefix
- bytes `[32,1056)`: 1024 low-coefficient bytes
- bytes `[1056,1058)`: suffix metadata bytes storing hb/h size deltas
- bytes `[1058,1058+hbsize)`: hbz payload
- remaining payload bytes up to the derived total: `h` payload
- trailing bytes through `1474`: zero padding required by unpack

## Compiled prefix theorem

The following three authored theories fresh-compile against the extracted
targets:

- `Mode2SignaturePrefixPack.pack_sig_prefix_mode2_layout` opens actual
  `_pack_sig_prefix` and proves the packed challenge-bit and 1024-byte low
  layout.
- `Mode2SignaturePrefixUnpack.unpack_sig_prefix_mode2_layout` opens actual
  `_unpack_sig_prefix` and proves the decoded bit words, exact signed-byte
  extension, and preservation of low-array words `[1024,2048)`.
- `Mode2SignaturePrefixRoundTrip.pack_unpack_sig_prefix_mode2_roundtrip`
  runs those two actual generated procedures sequentially and proves
  challenge/low equality on canonical inputs.

The exact input invariants are:

```text
canonical_challenge(cp) :=
  each of cp[0..256) is exactly bitword(cp[i].[0]), hence 0 or 1

canonical_signed_low(low) :=
  each low[0..1024) has signed value in [-128,128) and equals
  sign_extend_byte(truncateu8(low[i]))
```

The all-zero arrays prove that these premises are satisfiable. The theorem is
partial correctness and has no global-memory premise: the standalone
procedures transform bounded-array values. The unpack low tail frame is
proved; the pack signature-array tail and challenge-output tail are explicit
residual frame obligations.

## Obligation graph

| ID | Status | Exact procedure pair | Input/frame invariant | Output relation and reuse | Security relevance / residual |
| --- | --- | --- | --- | --- | --- |
| `OBL-SIG-PREFIX-CODEC` | `PROVED` | `_pack_sig_prefix` then `_unpack_sig_prefix` | canonical bit words; canonical signed bytes; `lcount=4`; `sigbytes=1474` | `challenge_prefix_eq` and `low_mode2_eq`; composes the two new actual-procedure Hoare lemmas | removes prefix serialization ambiguity only |
| `OBL-SIG-PREFIX-FRAME` | `PARTIAL` | same pair | bounded arrays, no global memory | unpack low `[1024,2048)` frame proved | pack `[1474,2948)` and challenge-array tail remain open |
| `OBL-SIG-SUFFIX-METADATA` | `SPECIFIED` | `_pack_sig_full` / `_unpack_sig_full` metadata code | valid hb/h sizes and total payload `<=416` | unpack reconstructs the two packer size deltas | needed to rule out size-header ambiguity; actual theorem open |
| `OBL-SIG-SUFFIX-PADDING` | `SPECIFIED` | `_pack_sig_full` / `_unpack_sig_full` trailing scan | encoded payload ends by byte 1474 | pack zero-fill implies unpack's remaining bytes are zero | canonical-parsing gate; actual theorem open |
| `OBL-SIG-HBZ-ENCODE-DECODE` | `SPECIFIED` | `_encode_hb_z1_full` / `_decode_hb_z1_full` | hb count/range and rANS table invariants | decoded hbz equals input | Week 8 first obligation; no inverse reused |
| `OBL-SIG-H-ENCODE-DECODE` | `SPECIFIED` | `_encode_h_full` / `_decode_h_full` | h count/range and rANS table invariants | decoded hint equals input | follows hbz proof pattern; no inverse reused |
| `OBL-SIG-FULL-CODEC-MODE2` | `BLOCKED` | `pack_sig_mode2_full_jazz` / `unpack_sig_mode2_full_jazz` | all preceding invariants and bad-flag success | full value equality and `bad=0` | blocked by both rANS inverses, metadata, padding, and residual frames |
| `OBL-SIG-CANONICAL-PARSE` | `PARTIAL` | full unpack gates | canonical 1474-byte encoding | accepted parse is unique | prefix canonicality proved; suffix/reject direction open |
| `OBL-SIGN-OUTPUT-TAIL-REACH` | `PARTIAL` | actual Sign output to Verify `_verify_full_m23` | complete codec plus Sign bounds | Sign-produced signature passes unpack/norm gates | full codec, norm, hint, arithmetic still missing |
| `OBL-SIGN-VERIFY-CORRECTNESS` | `BLOCKED` | full Sign/Verify | all functional dependencies | legitimate output accepts | not a Week 7 claim |

## Security relevance

- prefix codec correctness is a prerequisite for canonical parsing
- canonical parsing is needed to prevent ambiguity/malleability in the Verify
  accept event
- suffix metadata and padding affect whether implementation reject events add a
  nonzero encoding delta
- none of the Week 7 codec evidence proves a zero encoding loss

## Week 8 gate

Week 7 reaches `GO-B`: the actual prefix inverse compiles. Week 8 starts with
the single obligation `OBL-SIG-HBZ-ENCODE-DECODE`; it may reuse the resulting
rANS invariant pattern for `h` only after the hbz procedure pair is closed.
