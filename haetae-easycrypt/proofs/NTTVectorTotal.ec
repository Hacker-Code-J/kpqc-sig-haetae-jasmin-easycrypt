require import AllCore IntDiv List StdOrder.
from Jasmin require import JModel_x86.
require import ApiTarget HpolyTarget NTTCorrectness NTTVectorSpec NTTVectorCorrectness NTTFullSpec NTT_Fq Rq.

import NTTVectorSpec NTTVectorCorrectness IntOrder.

theory NTTVectorTotal.

op vector_prefix (initial current:BArray8192.t) (ps:Rq.poly list)
    (f:Rq.poly -> Rq.poly) (n i input_bits output_bits:int) : bool =
  0 <= i <= n <= 8 /\ size ps = n /\
  (forall k, 0 <= k < i =>
    NTT_Fq.poly_repr_bound (block8192 current k) (f (nth Rq.zero ps k)) output_bits) /\
  (forall k, i <= k < n =>
    NTT_Fq.poly_repr_bound (block8192 current k) (nth Rq.zero ps k) input_bits) /\
  inactive_unchanged initial current n.

lemma vector_prefix_init initial ps f n input_bits output_bits :
  vector_repr initial ps n input_bits =>
  vector_prefix initial initial ps f n 0 input_bits output_bits.
proof.
rewrite /vector_repr /vector_prefix /inactive_unchanged; smt().
qed.

lemma vector_prefix_next initial current ps f n i input_bits output_bits block :
  vector_prefix initial current ps f n i input_bits output_bits => i < n =>
  NTT_Fq.poly_repr_bound block (f (nth Rq.zero ps i)) output_bits =>
  vector_prefix initial (put_block8192 current i block) ps f n (i+1) input_bits output_bits.
proof.
move=> [hi [hs [hd [ht hf]]]] hin hb.
rewrite /vector_prefix.
split; first smt().
split; first exact hs.
split.
+ move=> k hk.
  case (k=i) => [->|hne].
  + by rewrite block8192_put_same 1:/#.
  rewrite block8192_put_other 1:/# 1:/# 1:/#.
  apply hd; smt().
split.
+ move=> k hk.
  rewrite block8192_put_other 1:/# 1:/# 1:/#.
  apply ht; smt().
apply (inactive_unchanged_trans initial current _ n hf).
apply put_block8192_preserves_tail; smt().
qed.

lemma vector_prefix_done initial current ps f n input_bits output_bits :
  vector_prefix initial current ps f n n input_bits output_bits =>
  vector_repr current (map f ps) n output_bits /\ inactive_unchanged initial current n.
proof.
move=> [hn [hs [hd [ht hf]]]].
split; last exact hf.
rewrite /vector_repr size_map hs.
split; first smt().
split; first trivial.
move=> k hk.
rewrite (nth_map Rq.zero Rq.zero f) 1:/#.
by apply hd.
qed.

op inverse_value p = NTT_Fq.array256_mont (NTTFullSpec.full_invntt p).

lemma vector_ref_invntt_total initial ps n :
  vector_repr initial ps n 18 =>
  phoare[VectorRef.invntt : xp=initial /\ count=n ==>
    vector_repr res (map inverse_value ps) n 16 /\ inactive_unchanged initial res n] = 1%r.
proof.
move=> hpre.
proc.
while (count=n /\ vector_prefix initial xp ps inverse_value n i 18 16) (n-i).
+ move=> z; wp.
  ecall (NTTCorrectness.target_poly_invntt_total18 (nth Rq.zero ps i)).
  wp; skip.
  move=> &hr [[[hc hp] hg] hz].
  have hpin : NTT_Fq.poly_repr_bound (block8192 xp{hr} i{hr}) (nth Rq.zero ps i{hr}) 18.
  + move: hp; rewrite /vector_prefix; smt().
  split; first exact hpin.
  move=> _ block hb.
  have hn : i{hr}<n by smt().
  have hs := vector_prefix_next initial xp{hr} ps inverse_value n i{hr} 18 16 block hp hn hb.
  by rewrite /=; smt().
wp; skip.
move=> &hr [hx hc].
split.
+ rewrite hx hc; split; first trivial.
  by apply vector_prefix_init.
move=> i current; split.
+ by smt().
move=> hdone [hc' hp].
have hi : i=n by move: hp; rewrite /vector_prefix; smt().
apply (vector_prefix_done initial current ps inverse_value n 18 16).
by move: hp; rewrite hi.
qed.

lemma vector_ref_ntt_total initial ps n :
  vector_repr initial ps n 16 =>
  phoare[VectorRef.ntt : xp=initial /\ count=n ==>
    vector_repr res (map NTTFullSpec.full_ntt ps) n 24 /\ inactive_unchanged initial res n] = 1%r.
proof.
move=> hpre.
proc.
while (count=n /\ vector_prefix initial xp ps NTTFullSpec.full_ntt n i 16 24) (n-i).
+ move=> z; wp.
  ecall (NTTCorrectness.target_poly_ntt_total (nth Rq.zero ps i)).
  wp; skip.
  move=> &hr [[[hc hp] hg] hz].
  have hpin : NTT_Fq.poly_repr_bound (block8192 xp{hr} i{hr}) (nth Rq.zero ps i{hr}) 16.
  + move: hp; rewrite /vector_prefix; smt().
  split; first exact hpin.
  move=> _ block hb.
  have hn : i{hr}<n by smt().
  have hs := vector_prefix_next initial xp{hr} ps NTTFullSpec.full_ntt n i{hr} 16 24 block hp hn hb.
  by rewrite /=; smt().
wp; skip.
move=> &hr [hx hc].
split.
+ rewrite hx hc; split; first trivial.
  by apply vector_prefix_init.
move=> i current; split.
+ by smt().
move=> hdone [hc' hp].
have hi : i=n by move: hp; rewrite /vector_prefix; smt().
apply (vector_prefix_done initial current ps NTTFullSpec.full_ntt n 16 24).
by move: hp; rewrite hi.
qed.

lemma api_vector_invntt_total18 initial ps n :
  vector_repr initial ps n 18 =>
  phoare[Actual._polyvec_invntt : xp=initial /\ count=W64.of_int n ==>
    vector_repr res (map inverse_value ps) n 16 /\ inactive_unchanged initial res n] = 1%r.
proof.
move=> hpre.
have hn : 0 <= n <= 8 by move: hpre; rewrite /vector_repr; smt().
have hc : W64.to_uint (W64.of_int n) = n by rewrite W64.to_uint_small; smt().
conseq vector_invntt_equiv (vector_ref_invntt_total initial ps n hpre).
+ move=> &m [hx hcount]; exists (initial,n); smt().
+ by smt().
qed.

lemma api_vector_ntt_total initial ps n :
  vector_repr initial ps n 16 =>
  phoare[Actual._polyvec_ntt : xp=initial /\ count=W64.of_int n ==>
    vector_repr res (map NTTFullSpec.full_ntt ps) n 24 /\ inactive_unchanged initial res n] = 1%r.
proof.
move=> hpre.
have hn : 0 <= n <= 8 by move: hpre; rewrite /vector_repr; smt().
have hc : W64.to_uint (W64.of_int n) = n by rewrite W64.to_uint_small; smt().
conseq vector_ntt_equiv (vector_ref_ntt_total initial ps n hpre).
+ move=> &m [hx hcount]; exists (initial,n); smt().
+ by smt().
qed.

lemma api_vector_invntt_total18_pre initial ps n :
  phoare[Actual._polyvec_invntt :
    xp=initial /\ count=W64.of_int n /\ vector_repr initial ps n 18 ==>
    vector_repr res (map inverse_value ps) n 16 /\ inactive_unchanged initial res n] = 1%r.
proof.
case (vector_repr initial ps n 18) => hpre.
+ by conseq (api_vector_invntt_total18 initial ps n hpre) => /#.
+ by exfalso => /#.
qed.

lemma api_vector_ntt_total_pre initial ps n :
  phoare[Actual._polyvec_ntt :
    xp=initial /\ count=W64.of_int n /\ vector_repr initial ps n 16 ==>
    vector_repr res (map NTTFullSpec.full_ntt ps) n 24 /\ inactive_unchanged initial res n] = 1%r.
proof.
case (vector_repr initial ps n 16) => hpre.
+ by conseq (api_vector_ntt_total initial ps n hpre) => /#.
+ by exfalso => /#.
qed.

end NTTVectorTotal.
