(* HAETAE 1.2.0: checked against the fresh generated/ntt/HpolyTarget.ec.
   Mathematical support is copied locally; see manifests/ntt-assumptions.md. *)

require import AllCore.

from Jasmin require import JModel_x86.

require import HpolyTarget Hpoly_extract Hpoly_loop
               Fq NTT_Fq NTTFullSpec NTTFullAlgebra RefJasminNTTLoop.

theory NTTCorrectness.

module Target = HpolyTarget.M.
module Loop = Hpoly_loop.M.

(* The current target extraction uses the same scalar Montgomery routines and
   the same direct-loop NTT schedule as the checked loop adapter.  Keeping the
   bridge relational makes the source boundary explicit: the theorem below is
   about [HpolyTarget], not merely the historical [Hpoly_extract] module. *)

lemma montgomery_reduce_loop_equiv :
  equiv [Target.__montgomery_reduce ~ Loop.__montgomery_reduce :
    ={a} ==> ={res}].
proof.
proc.
inline {2} Hpoly_loop.M.__montgomery_reduce.
inline {2} Hpoly_extract.M.__montgomery_reduce.
sim.
qed.

lemma fqmul_loop_equiv :
  equiv [Target.__fqmul ~ Loop.__fqmul :
    ={a, b} ==> ={res}].
proof.
proc.
inline {2} Hpoly_loop.M.__fqmul.
inline {2} Hpoly_extract.M.__fqmul.
sim.
qed.

lemma target_fqmul_correct aa bb :
  hoare [Target.__fqmul :
    W32.to_sint a = aa /\ W32.to_sint b = bb ==>
    W32.to_sint res = Fq.SignedReductions.SREDC (aa * bb)].
proof.
by conseq fqmul_loop_equiv
  (RefJasminNTT.loop_fqmul_corr_h aa bb) => /#.
qed.

lemma target_fqmul_ll :
  islossless Target.__fqmul.
proof.
proc.
islossless.
qed.

lemma poly_ntt_loop_equiv :
  equiv [Target._poly_ntt ~ Loop._poly_ntt :
    ={rp} ==> ={res}].
proof.
proc.
inline {1} HpolyTarget.M.__fqmul.
inline {1} HpolyTarget.M.__montgomery_reduce.
inline {2} Hpoly_loop.M.__fqmul.
inline {2} Hpoly_extract.M.__fqmul.
inline {2} Hpoly_extract.M.__montgomery_reduce.
sim.
qed.

lemma poly_invntt_loop_equiv :
  equiv [Target._poly_invntt ~ Loop._poly_invntt :
    ={rp} ==> ={res}].
proof.
proc.
inline {1} HpolyTarget.M.__fqmul.
inline {1} HpolyTarget.M.__montgomery_reduce.
inline {2} Hpoly_loop.M.__fqmul.
inline {2} Hpoly_extract.M.__fqmul.
inline {2} Hpoly_extract.M.__montgomery_reduce.
sim.
qed.

lemma poly_ntt_jazz_loop_equiv :
  equiv [Target.poly_ntt_jazz ~ Loop.poly_ntt_jazz :
    ={rp} ==> ={res}].
proof.
proc.
wp.
call poly_ntt_loop_equiv.
wp.
skip => />.
qed.

lemma poly_invntt_jazz_loop_equiv :
  equiv [Target.poly_invntt_jazz ~ Loop.poly_invntt_jazz :
    ={rp} ==> ={res}].
proof.
proc.
wp.
call poly_invntt_loop_equiv.
wp.
skip => />.
qed.

lemma target_poly_ntt_correct p :
  hoare [Target._poly_ntt :
    NTT_Fq.poly_repr_bound rp p 16 ==>
    NTT_Fq.poly_repr_bound res (NTTFullSpec.full_ntt p) 24].
proof.
have hloop_core :
  hoare [Loop._poly_ntt :
    NTT_Fq.poly_repr_bound rp p 16 ==>
    NTT_Fq.poly_repr_bound res (NTTFullSpec.full_ntt p) 24].
+ by conseq RefJasminNTT.poly_ntt_core_ref
    (NTTFullAlgebra.ntt_full_ntt p) => /#.
by conseq poly_ntt_loop_equiv hloop_core => /#.
qed.

lemma target_poly_ntt_jazz_correct p :
  hoare [Target.poly_ntt_jazz :
    NTT_Fq.poly_repr_bound rp p 16 ==>
    NTT_Fq.poly_repr_bound res (NTTFullSpec.full_ntt p) 24].
proof.
have hloop_core :
  hoare [Loop._poly_ntt :
    NTT_Fq.poly_repr_bound rp p 16 ==>
    NTT_Fq.poly_repr_bound res (NTTFullSpec.full_ntt p) 24].
+ by conseq RefJasminNTT.poly_ntt_core_ref
    (NTTFullAlgebra.ntt_full_ntt p) => /#.
have hloop_jazz :
  hoare [Loop.poly_ntt_jazz :
    NTT_Fq.poly_repr_bound rp p 16 ==>
    NTT_Fq.poly_repr_bound res (NTTFullSpec.full_ntt p) 24].
+ by conseq RefJasminNTT.poly_ntt_jazz_ref hloop_core => /#.
by conseq poly_ntt_jazz_loop_equiv hloop_jazz => /#.
qed.

lemma target_poly_invntt_correct p :
  hoare [Target._poly_invntt :
    NTT_Fq.poly_repr_bound rp p 16 ==>
    NTT_Fq.poly_repr_bound res
      (NTT_Fq.array256_mont (NTTFullSpec.full_invntt p)) 16].
proof.
have hloop_core :
  hoare [Loop._poly_invntt :
    NTT_Fq.poly_repr_bound rp p 16 ==>
    NTT_Fq.poly_repr_bound res
      (NTT_Fq.array256_mont (NTTFullSpec.full_invntt p)) 16].
+ by conseq RefJasminNTT.poly_invntt_core_ref
    (NTTFullAlgebra.invntt_full_invntt p) => /#.
by conseq poly_invntt_loop_equiv hloop_core => /#.
qed.

lemma target_poly_invntt_correct18 p :
  hoare [Target._poly_invntt :
    NTT_Fq.poly_repr_bound rp p 18 ==>
    NTT_Fq.poly_repr_bound res
      (NTT_Fq.array256_mont (NTTFullSpec.full_invntt p)) 16].
proof.
have hloop_core :
  hoare [Loop._poly_invntt :
    NTT_Fq.poly_repr_bound rp p 18 ==>
    NTT_Fq.poly_repr_bound res
      (NTT_Fq.array256_mont (NTTFullSpec.full_invntt p)) 16].
+ by conseq RefJasminNTT.poly_invntt_core_ref18
    (NTTFullAlgebra.invntt_full_invntt p) => /#.
by conseq poly_invntt_loop_equiv hloop_core => /#.
qed.

lemma target_poly_invntt_jazz_correct p :
  hoare [Target.poly_invntt_jazz :
    NTT_Fq.poly_repr_bound rp p 16 ==>
    NTT_Fq.poly_repr_bound res
      (NTT_Fq.array256_mont (NTTFullSpec.full_invntt p)) 16].
proof.
have hloop_core :
  hoare [Loop._poly_invntt :
    NTT_Fq.poly_repr_bound rp p 16 ==>
    NTT_Fq.poly_repr_bound res
      (NTT_Fq.array256_mont (NTTFullSpec.full_invntt p)) 16].
+ by conseq RefJasminNTT.poly_invntt_core_ref
    (NTTFullAlgebra.invntt_full_invntt p) => /#.
have hloop_jazz :
  hoare [Loop.poly_invntt_jazz :
    NTT_Fq.poly_repr_bound rp p 16 ==>
    NTT_Fq.poly_repr_bound res
      (NTT_Fq.array256_mont (NTTFullSpec.full_invntt p)) 16].
+ by conseq RefJasminNTT.poly_invntt_jazz_ref hloop_core => /#.
by conseq poly_invntt_jazz_loop_equiv hloop_jazz => /#.
qed.

lemma target_poly_invntt_jazz_correct18 p :
  hoare [Target.poly_invntt_jazz :
    NTT_Fq.poly_repr_bound rp p 18 ==>
    NTT_Fq.poly_repr_bound res
      (NTT_Fq.array256_mont (NTTFullSpec.full_invntt p)) 16].
proof.
have hloop_core :
  hoare [Loop._poly_invntt :
    NTT_Fq.poly_repr_bound rp p 18 ==>
    NTT_Fq.poly_repr_bound res
      (NTT_Fq.array256_mont (NTTFullSpec.full_invntt p)) 16].
+ by conseq RefJasminNTT.poly_invntt_core_ref18
    (NTTFullAlgebra.invntt_full_invntt p) => /#.
have hloop_jazz :
  hoare [Loop.poly_invntt_jazz :
    NTT_Fq.poly_repr_bound rp p 18 ==>
    NTT_Fq.poly_repr_bound res
      (NTT_Fq.array256_mont (NTTFullSpec.full_invntt p)) 16].
+ by conseq RefJasminNTT.poly_invntt_jazz_ref hloop_core => /#.
by conseq poly_invntt_jazz_loop_equiv hloop_jazz => /#.
qed.

(* Total correctness follows from the lossless mathematical procedures and
   the checked relational refinements. The coefficient bounds are explicit. *)

lemma ntt_spec_total p :
  phoare [NTT_Fq.NTT.ntt :
    arg = (p, NTT_Fq.zetas) ==>
    res = NTTFullSpec.full_ntt p] = 1%r.
proof.
by conseq NTT_Fq.ntt_spec_ll (NTTFullAlgebra.ntt_full_ntt p).
qed.

lemma target_poly_ntt_total p :
  phoare [Target._poly_ntt :
    NTT_Fq.poly_repr_bound rp p 16 ==>
    NTT_Fq.poly_repr_bound res (NTTFullSpec.full_ntt p) 24] = 1%r.
proof.
have hloop_core :
  phoare [Loop._poly_ntt :
    NTT_Fq.poly_repr_bound rp p 16 ==>
    NTT_Fq.poly_repr_bound res (NTTFullSpec.full_ntt p) 24] = 1%r.
+ by conseq RefJasminNTT.poly_ntt_core_ref (ntt_spec_total p) => /#.
by conseq poly_ntt_loop_equiv hloop_core => /#.
qed.

lemma invntt_spec_total p :
  phoare [NTT_Fq.NTT.invntt :
    arg = (p, NTT_Fq.zetas_inv) ==>
    res = NTTFullSpec.full_invntt p] = 1%r.
proof.
by conseq NTT_Fq.invntt_spec_ll (NTTFullAlgebra.invntt_full_invntt p).
qed.

lemma target_poly_invntt_total18 p :
  phoare [Target._poly_invntt :
    NTT_Fq.poly_repr_bound rp p 18 ==>
    NTT_Fq.poly_repr_bound res
      (NTT_Fq.array256_mont (NTTFullSpec.full_invntt p)) 16] = 1%r.
proof.
have hloop_core :
  phoare [Loop._poly_invntt :
    NTT_Fq.poly_repr_bound rp p 18 ==>
    NTT_Fq.poly_repr_bound res
      (NTT_Fq.array256_mont (NTTFullSpec.full_invntt p)) 16] = 1%r.
+ by conseq RefJasminNTT.poly_invntt_core_ref18 (invntt_spec_total p) => /#.
by conseq poly_invntt_loop_equiv hloop_core => /#.
qed.

lemma target_poly_invntt_total p :
  phoare [Target._poly_invntt :
    NTT_Fq.poly_repr_bound rp p 16 ==>
    NTT_Fq.poly_repr_bound res
      (NTT_Fq.array256_mont (NTTFullSpec.full_invntt p)) 16] = 1%r.
proof.
have hloop_core :
  phoare [Loop._poly_invntt :
    NTT_Fq.poly_repr_bound rp p 16 ==>
    NTT_Fq.poly_repr_bound res
      (NTT_Fq.array256_mont (NTTFullSpec.full_invntt p)) 16] = 1%r.
+ by conseq RefJasminNTT.poly_invntt_core_ref (invntt_spec_total p) => /#.
by conseq poly_invntt_loop_equiv hloop_core => /#.
qed.

lemma target_poly_ntt_jazz_total p :
  phoare [Target.poly_ntt_jazz :
    NTT_Fq.poly_repr_bound rp p 16 ==>
    NTT_Fq.poly_repr_bound res (NTTFullSpec.full_ntt p) 24] = 1%r.
proof.
proc.
wp.
call (target_poly_ntt_total p).
wp.
skip => />.
qed.

lemma target_poly_invntt_jazz_total18 p :
  phoare [Target.poly_invntt_jazz :
    NTT_Fq.poly_repr_bound rp p 18 ==>
    NTT_Fq.poly_repr_bound res
      (NTT_Fq.array256_mont (NTTFullSpec.full_invntt p)) 16] = 1%r.
proof.
proc.
wp.
call (target_poly_invntt_total18 p).
wp.
skip => />.
qed.

lemma target_poly_invntt_jazz_total p :
  phoare [Target.poly_invntt_jazz :
    NTT_Fq.poly_repr_bound rp p 16 ==>
    NTT_Fq.poly_repr_bound res
      (NTT_Fq.array256_mont (NTTFullSpec.full_invntt p)) 16] = 1%r.
proof.
proc.
wp.
call (target_poly_invntt_total p).
wp.
skip => />.
qed.

end NTTCorrectness.
