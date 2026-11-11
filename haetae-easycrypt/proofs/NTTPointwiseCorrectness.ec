require import AllCore IntDiv List StdOrder.
from Jasmin require import JModel_x86.
require import BArray1024 BArray8192 BArray32768 ApiTarget HpolyTarget
               Fq NTT_Fq NTTCorrectness NTTMontgomeryBounds NTTVectorSpec GFq Rq Array256.
import IntOrder NTTVectorSpec Zq.

theory NTTPointwiseCorrectness.

module Target = ApiTarget.M(ApiTarget.Syscall).

lemma api_fqmul_equiv :
  equiv [Target.__fqmul ~ HpolyTarget.M.__fqmul :
    ={a,b} ==> ={res}].
proof.
proc.
inline Target.__montgomery_reduce HpolyTarget.M.__montgomery_reduce.
sim.
qed.

lemma api_fqmul_correct aa bb :
  hoare [Target.__fqmul :
    W32.to_sint a = aa /\ W32.to_sint b = bb ==>
    W32.to_sint res = Fq.SignedReductions.SREDC (aa * bb)].
proof.
by conseq api_fqmul_equiv (NTTCorrectness.target_fqmul_correct aa bb) => /#.
qed.

lemma api_fqmul_ll : islossless Target.__fqmul.
proof. proc; inline Target.__montgomery_reduce; islossless. qed.

op pointwise_value (up:BArray8192.t) (vp:BArray1024.t) (i:int) : int =
  Fq.SignedReductions.SREDC
    (W32.to_sint (BArray8192.get32 up i) *
     W32.to_sint (BArray1024.get32 vp (i %% 256))).

op pointwise_prefix (initial up:BArray8192.t) (vp:BArray1024.t)
    (current:BArray8192.t) (n:int) : bool =
  (forall i, 0 <= i < n =>
    W32.to_sint (BArray8192.get32 current i) = pointwise_value up vp i) /\
  (forall j, 4*n <= j < 8192 =>
    BArray8192.get8 current j = BArray8192.get8 initial j).

lemma pointwise_prefix_zero initial up vp :
  pointwise_prefix initial up vp initial 0.
proof. rewrite /pointwise_prefix; smt(). qed.

lemma pointwise_prefix_step initial up vp current n (w:W32.t) :
  0 <= n < 2048 =>
  pointwise_prefix initial up vp current n =>
  W32.to_sint w = pointwise_value up vp n =>
  pointwise_prefix initial up vp
    (BArray8192.set32 current n w) (n+1).
proof.
move=> hn [hp hf] hw; split.
+ move=> i hi.
  rewrite BArray8192.get_set32E 1:/# 1:/#.
  case (i=n) => [-> // | hne].
  smt().
move=> j hj.
rewrite BArray8192.get8_set32dE.
have -> : !(4*n <= j < 4*n+4 /\ 0 <= j < 8192) by smt().
smt().
qed.


lemma pointwise_prefix_step_block initial up vp current k j (w:W32.t) :
  0 <= k < 8 => 0 <= j < 256 =>
  pointwise_prefix initial up vp current (256*k+j) =>
  W32.to_sint w = Fq.SignedReductions.SREDC
    (W32.to_sint (BArray8192.get32 up (256*k+j)) *
     W32.to_sint (BArray1024.get32 vp j)) =>
  pointwise_prefix initial up vp (BArray8192.set32 current (256*k+j) w)
    (256*k+(j+1)).
proof.
move=> hk hj hp hw.
have he : (256*k+j) %% 256 = j by rewrite mulzC modzMDl modz_small /#.
have hs := pointwise_prefix_step initial up vp current (256*k+j) w _ hp _.
+ smt().
+ by rewrite /pointwise_value he.
by have -> : 256*k+(j+1) = 256*k+j+1 by ring.
qed.

lemma pointwise_prefix_outer_step initial up vp current k :
  pointwise_prefix initial up vp current (256*k+256) =>
  pointwise_prefix initial up vp current (256*(k+1)).
proof. smt(). qed.

lemma polyvec_pointwise_correct (initial up0:BArray8192.t)
    (vp0:BArray1024.t) (n:int) :
  0 <= n <= 8 =>
  hoare [Target._polyvec_poly_pointwise :
    rp=initial /\ up=up0 /\ vp=vp0 /\ count=W64.of_int n ==>
    pointwise_prefix initial up0 vp0 res (256*n)].
proof.
move=> hn.
proc.
while (up=up0 /\ vp=vp0 /\ count=W64.of_int n /\
       0 <= W64.to_uint k <= n /\
       W64.to_uint off=256*W64.to_uint k /\
       pointwise_prefix initial up0 vp0 rp (256*W64.to_uint k)).
+ wp.
  while (up=up0 /\ vp=vp0 /\ count=W64.of_int n /\
         0 <= W64.to_uint k < n /\
         W64.to_uint off=256*W64.to_uint k /\
         0 <= W64.to_uint j <= 256 /\
         pointwise_prefix initial up0 vp0 rp (256*W64.to_uint k+W64.to_uint j)).
  + wp.
    ecall (api_fqmul_correct
      (W32.to_sint (BArray8192.get32 up0 (256*W64.to_uint k+W64.to_uint j)))
      (W32.to_sint (BArray1024.get32 vp0 (W64.to_uint j)))).
    auto => /> &hr hk0 hkn hoff hj0 hj256 hp hf hguard.
    rewrite W64.ultE W64.of_uintK /= in hguard.
    have hidx : W64.to_uint (off{hr}+j{hr})=256*W64.to_uint k{hr}+W64.to_uint j{hr}.
    + rewrite W64.to_uintD_small 1:/# hoff; trivial.
    have hnext : W64.to_uint (j{hr}+W64.one)=W64.to_uint j{hr}+1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1; trivial.
    rewrite hidx hnext.
    split; first trivial.
    move=> _ result hresult.
    have hpre : pointwise_prefix initial up0 vp0 rp{hr} (256*W64.to_uint k{hr}+W64.to_uint j{hr}) by split.
    have hpost := pointwise_prefix_step_block initial up0 vp0 rp{hr}
      (W64.to_uint k{hr}) (W64.to_uint j{hr}) result _ _ hpre hresult.
    + smt().
    + smt().
    move: hpost; rewrite /pointwise_prefix; smt().
  auto => /> &hr hk0 hkn hoff hp hf hguard.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  have hks : W64.to_uint k{hr}<n by smt(modz_small).
  split; first exact hks.
  move=> j after hjguard _ hj0 hj256 hpafter hfafter.
  rewrite W64.ultE W64.of_uintK /= in hjguard.
  have hj : W64.to_uint j=256 by smt().
  have hknew : W64.to_uint (k{hr}+W64.one)=W64.to_uint k{hr}+1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1; trivial.
  have hoffnew : W64.to_uint (off{hr}+W64.of_int 256)=256*W64.to_uint k{hr}+256.
  + rewrite W64.to_uintD_small 1:/# W64.of_uintK /= hoff; trivial.
  rewrite hknew hoffnew.
  move: hpafter hfafter; rewrite hj; smt().
auto => />.
split; first smt().
move=> k off after hdone hk0 hkn hoff hp hf.
rewrite W64.ultE W64.of_uintK /= in hdone.
have he : W64.to_uint k=n by smt(modz_small).
move: hp hf; rewrite he; smt().
qed.

lemma polyvec_pointwise_ll : islossless Target._polyvec_poly_pointwise.
proof.
proc.
while (W64.to_uint k <= W64.to_uint count)
      (W64.to_uint count-W64.to_uint k).
+ move=> z; wp.
  while (W64.to_uint j <= 256) (256-W64.to_uint j).
  + move=> zj; wp; call api_fqmul_ll; auto => /> &hr hj hguard.
    rewrite W64.ultE W64.of_uintK /= in hguard.
    rewrite W64.to_uintD_small 1:/# W64.to_uint1; smt().
  auto => /> &hr hk hguard.
  rewrite W64.ultE in hguard.
  have /= hc := W64.to_uint_cmp count{hr}.
  move=> j; split.
  + rewrite W64.ultE W64.of_uintK /=; smt().
  move=> _ _.
  rewrite W64.to_uintD_small 1:W64.to_uint1 1:/# W64.to_uint1; smt().

auto => /> &hr.
split; first smt(W64.to_uint_cmp).
move=> k hk hvariant; rewrite W64.ultE; smt().
qed.

lemma polyvec_pointwise_total initial up0 vp0 n :
  0<=n<=8 =>
  phoare[Target._polyvec_poly_pointwise :
    rp=initial /\ up=up0 /\ vp=vp0 /\ count=W64.of_int n ==>
    pointwise_prefix initial up0 vp0 res (256*n)] = 1%r.
proof.
move=> hn.
by conseq polyvec_pointwise_ll (polyvec_pointwise_correct initial up0 vp0 n hn).
qed.

op montgomery_pointwise (p q : Rq.poly) : Rq.poly =
  Array256.map2 (fun x y => x*y*inv NTT_Fq.R) p q.

lemma montgomery_pointwiseE p q i : 0<=i<256 =>
  (montgomery_pointwise p q).[i]=p.[i]*q.[i]*inv NTT_Fq.R.
proof. by move=> hi; rewrite /montgomery_pointwise Array256.map2iE. qed.

lemma pointwise_scalar_field (a b w:W32.t) :
  Fq.bw32 a 24 => Fq.bw32 b 24 =>
  W32.to_sint w=Fq.SignedReductions.SREDC (W32.to_sint a*W32.to_sint b) =>
  Fq.bw32 w 17 /\
  NTT_Fq.word_to_coeff w = NTT_Fq.word_to_coeff a * NTT_Fq.word_to_coeff b * inv NTT_Fq.R.
proof.
rewrite /Fq.bw32 /= => ha hb hw.
have [hbound hmod] := NTTMontgomeryBounds.fqmul_24_bounds_congr
  (W32.to_sint a) (W32.to_sint b) _ _; first 2 smt().
split; first smt().
rewrite /NTT_Fq.word_to_coeff NTT_Fq.inv_R -!incoeffM -eq_incoeff /GFq.q hw.
rewrite !incoeffK /GFq.q.
smt(modzMml modzMmr).
qed.

lemma pointwise_prefix_repr initial up vp output ps q n :
  vector_repr up ps n 24 => NTT_Fq.poly_repr_bound vp q 24 =>
  pointwise_prefix initial up vp output (256*n) =>
  vector_repr output (List.map (fun p => montgomery_pointwise p q) ps) n 17 /\
  inactive_unchanged initial output n.
proof.
move=> [hn [hsize hu]] hv [hp hf].
split.
+ rewrite /vector_repr size_map hsize; split; first exact hn.
  split; first trivial.
  move=> k hk.
  rewrite (nth_map Rq.zero) 1:/#.
  rewrite /NTT_Fq.poly_repr_bound /NTT_Fq.poly_repr.
  have hcoeff : forall i, 0<=i<256 =>
    NTT_Fq.word_to_coeff (BArray1024.get32 (block8192 output k) i)=
      (montgomery_pointwise (nth Rq.zero ps k) q).[i] /\
    Fq.bw32 (BArray1024.get32 (block8192 output k) i) 17.
  + move=> i hi.
    have hir : i \in range 0 256 by rewrite mem_range.
    have [hup hub] := NTT_Fq.poly_repr_bound_get _ _ _ i (hu k hk) hir.
    have [hvp hvb] := NTT_Fq.poly_repr_bound_get _ _ _ i hv hir.
    have hout := hp (256*k+i) _; first smt().
    rewrite /pointwise_value in hout.
    have hmod : (256*k+i)%%256=i by rewrite mulzC modzMDl modz_small /#.
    move: hout; rewrite hmod; move=> hout.
    move: hub hup; rewrite block8192_get32 1:hi; move=> hub hup.
    have [hb he] := pointwise_scalar_field
      (BArray8192.get32 up (256*k+i)) (BArray1024.get32 vp i)
      (BArray8192.get32 output (256*k+i)) hub hvb hout.
    rewrite block8192_get32 1:hi montgomery_pointwiseE 1:hi hup hvp.
    by split.
  split.
  + apply Array256.ext_eq => i hi.
    rewrite NTT_Fq.barray256_to_polyE 1:mem_range 1:hi.
    have [he hb] := hcoeff i hi; exact he.
  rewrite /NTT_Fq.barray256_bound => i /mem_range hi.
  have [he hb] := hcoeff i hi; exact hb.
rewrite /inactive_unchanged => j hj.
apply hf; smt().
qed.

lemma polyvec_pointwise_field_total initial up0 vp0 ps q n :
  vector_repr up0 ps n 24 => NTT_Fq.poly_repr_bound vp0 q 24 =>
  phoare[Target._polyvec_poly_pointwise :
    rp=initial /\ up=up0 /\ vp=vp0 /\ count=W64.of_int n ==>
    vector_repr res (List.map (fun p => montgomery_pointwise p q) ps) n 17 /\
    inactive_unchanged initial res n] = 1%r.
proof.
move=> hu hv.
have hn : 0<=n<=8 by move: hu; rewrite /vector_repr; smt().
have hh : hoare[Target._polyvec_poly_pointwise :
    rp=initial /\ up=up0 /\ vp=vp0 /\ count=W64.of_int n ==>
    vector_repr res (List.map (fun p => montgomery_pointwise p q) ps) n 17 /\
    inactive_unchanged initial res n].
+ conseq (polyvec_pointwise_correct initial up0 vp0 n hn).
  move=> &hr _ result hp.
  exact (pointwise_prefix_repr initial up0 vp0 result ps q n hu hv hp).
by conseq polyvec_pointwise_ll hh.
qed.

end NTTPointwiseCorrectness.

