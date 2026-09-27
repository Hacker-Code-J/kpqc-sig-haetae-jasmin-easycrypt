require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import HyperballNormSpec HyperballNormCorrectness HardenedHyperballTarget.
import HyperballNormCorrectness.

(* A machine-word mask records whether ANY earlier addition overflowed.
   Its representation is zero/all-ones, not a live processor flag. *)
op cn_overflow_mask (n : int) : W64.t =
  W64.of_int (-b2i (W64.modulus <= n)).

op cn_step (low mask term : W64.t) : W64.t * W64.t =
  let added = W64.addc low term false in
  (added.`2,mask `|` (W64.subc term term added.`1).`2).

lemma cn_carry_mask (x : W64.t) (carry : bool) :
  (W64.subc x x carry).`2=W64.of_int (-b2i carry).
proof.
  rewrite W64.subcE /= W64.of_intN; ring.
qed.

lemma cn_mask_or (a b : bool) :
  W64.of_int (-b2i a) `|` W64.of_int (-b2i b)=W64.of_int (-b2i (a \/ b)).
proof.
  case a; case b; by rewrite /b2i /= ?W64.of_intN ?W64.minus_one /=.
qed.

lemma cn_addc_low n (term : W64.t) :
  (W64.addc (W64.of_int n) term false).`2=W64.of_int (n+W64.to_uint term).
proof.
  by rewrite W64.addcE /= -{1}(W64.to_uintK term) -W64.of_intD.
qed.

lemma cn_overflow_step n (term : W64.t) : 0 <= n =>
  ((W64.modulus<=n) \/ (W64.addc (W64.of_int n) term false).`1) =
    (W64.modulus<=n+W64.to_uint term).
proof.
  move=> hn; have ht := W64.to_uint_cmp term.
  case (W64.modulus<=n) => hover /=; first smt().
  have hsmall : 0<=n<W64.modulus by smt().
  by rewrite W64.addcE /W64.carry_add /= (W64.to_uint_small n hsmall).
qed.

lemma cn_step_correct n (term : W64.t) : 0 <= n =>
  cn_step (W64.of_int n) (cn_overflow_mask n) term =
    (W64.of_int (n+W64.to_uint term),cn_overflow_mask (n+W64.to_uint term)).
proof.
  move=> hn.
  rewrite /cn_step /= cn_carry_mask cn_addc_low /cn_overflow_mask cn_mask_or.
  by rewrite (cn_overflow_step n term hn).
qed.

lemma cn_square_step n (x : W32.t) : 0 <= n =>
  cn_step (W64.of_int n) (cn_overflow_mask n) (sigextu64 x*sigextu64 x) =
    (W64.of_int (n+W32.to_sint x*W32.to_sint x),
      cn_overflow_mask (n+W32.to_sint x*W32.to_sint x)).
proof.
  move=> hn; by rewrite (cn_step_correct n _ hn) signed32_square_uint.
qed.

lemma cn_overflow_zero_iff n : (cn_overflow_mask n=W64.zero) = (n<W64.modulus).
proof.
  rewrite /cn_overflow_mask /b2i.
  case (W64.modulus<=n) => hn;
    rewrite /= ?W64.to_uint_eq ?W64.of_uintK /=; smt().
qed.

lemma cn_overflow_initial : cn_overflow_mask 0=W64.zero.
proof. by rewrite /cn_overflow_mask /b2i /=. qed.

module CN = HardenedHyperballTarget.M.

lemma checked_sqnorm2_correct
    (ap0 : BArray8192.t) (na : int) (bp0 : BArray8192.t) (nb : int) :
  hoare [CN._hb_checked_sqnorm2_2048 :
    ap=ap0 /\ acount=W64.of_int na /\ bp=bp0 /\ bcount=W64.of_int nb /\
    0<=na<=2048 /\ 0<=nb<=2048 ==>
    res.`1=W64.of_int (hyperball_sqnorm ap0 na bp0 nb) /\
    res.`2=cn_overflow_mask (hyperball_sqnorm ap0 na bp0 nb)].
proof.
  proc.
  while (ap=ap0 /\ acount=W64.of_int na /\ bp=bp0 /\ bcount=W64.of_int nb /\
    0<=na<=2048 /\ 0<=nb<=2048 /\ 0<=W64.to_uint i<=nb /\
    total=W64.of_int (hyperball_prefix_sqnorm ap0 na+
      hyperball_prefix_sqnorm bp0 (W64.to_uint i)) /\
    overflow=cn_overflow_mask (hyperball_prefix_sqnorm ap0 na+
      hyperball_prefix_sqnorm bp0 (W64.to_uint i))).
  + auto => /> &hr hna0 hnamax hnb0 hnbmax hi0 hin hguard.
    have hi : W64.to_uint i{hr}<nb by
      move: hguard; rewrite W64.ultE W64.to_uint_small 1:/#.
    have hpa := hyperball_prefix_sqnorm_nonnegative ap0 na hna0.
    have hpb := hyperball_prefix_sqnorm_nonnegative bp0 (W64.to_uint i{hr}) hi0.
    have hn : 0<=hyperball_prefix_sqnorm ap0 na+
        hyperball_prefix_sqnorm bp0 (W64.to_uint i{hr}) by smt().
    have hstep := cn_square_step (hyperball_prefix_sqnorm ap0 na+
      hyperball_prefix_sqnorm bp0 (W64.to_uint i{hr}))
      (BArray8192.get32 bp0 (W64.to_uint i{hr})) hn.
    rewrite /cn_step /= in hstep.
    have [hlo hmask] := hstep.
    have hnext : hyperball_prefix_sqnorm ap0 na+
        hyperball_prefix_sqnorm bp0 (W64.to_uint i{hr}+1) =
      hyperball_prefix_sqnorm ap0 na+hyperball_prefix_sqnorm bp0 (W64.to_uint i{hr})+
        W32.to_sint (BArray8192.get32 bp0 (W64.to_uint i{hr}))*
        W32.to_sint (BArray8192.get32 bp0 (W64.to_uint i{hr})).
    + rewrite hyperball_prefix_sqnormS 1:hi0 /hyperball_coeff_square; ring.
    rewrite norm_counter_next 1:/# hnext.
    split; first smt().
    split; [exact hlo | exact hmask].
  wp.
  while (ap=ap0 /\ acount=W64.of_int na /\ bp=bp0 /\ bcount=W64.of_int nb /\
    0<=na<=2048 /\ 0<=nb<=2048 /\ 0<=W64.to_uint i<=na /\
    total=W64.of_int (hyperball_prefix_sqnorm ap0 (W64.to_uint i)) /\
    overflow=cn_overflow_mask (hyperball_prefix_sqnorm ap0 (W64.to_uint i))).
  + auto => /> &hr hna0 hnamax hnb0 hnbmax hi0 hin hguard.
    have hi : W64.to_uint i{hr}<na by
      move: hguard; rewrite W64.ultE W64.to_uint_small 1:/#.
    have hn := hyperball_prefix_sqnorm_nonnegative ap0 (W64.to_uint i{hr}) hi0.
    have hstep := cn_square_step (hyperball_prefix_sqnorm ap0 (W64.to_uint i{hr}))
      (BArray8192.get32 ap0 (W64.to_uint i{hr})) hn.
    rewrite /cn_step /= in hstep.
    have [hlo hmask] := hstep.
    rewrite norm_counter_next 1:/# hyperball_prefix_sqnormS 1:hi0 /hyperball_coeff_square.
    split; first smt().
    split; [exact hlo | exact hmask].
  auto => /> hna0 hnamax hnb0 hnbmax.
  rewrite /protect_ptr /protect_64 !hyperball_prefix_sqnorm0 cn_overflow_initial /=.
  move=> i hdone hi0 hin.
  have hi : W64.to_uint i=na by
    move: hdone; rewrite W64.ultE W64.to_uint_small 1:/#; smt().
  rewrite hi /=.
  move=> j hdonej hj0 hjn.
  have hj : W64.to_uint j=nb by
    move: hdonej; rewrite W64.ultE W64.to_uint_small 1:/#; smt().
  by rewrite hj /hyperball_sqnorm.
qed.

lemma checked_sqnorm2_ll : islossless CN._hb_checked_sqnorm2_2048.
proof.
  proc.
  while (W64.to_uint i<=W64.to_uint bcount) (W64.to_uint bcount-W64.to_uint i).
  + move=> z; auto => /> &hr hi hguard.
    have hb := W64.to_uint_cmp bcount{hr}.
    rewrite W64.ultE in hguard.
    rewrite W64.to_uintD_small 1:/# W64.to_uint1; smt().
  wp.
  while (W64.to_uint i<=W64.to_uint acount) (W64.to_uint acount-W64.to_uint i).
  + move=> z; auto => /> &hr hi hguard.
    have ha := W64.to_uint_cmp acount{hr}.
    rewrite W64.ultE in hguard.
    rewrite W64.to_uintD_small 1:/# W64.to_uint1; smt().
  auto => />; rewrite /protect_64; smt(W64.to_uint_cmp W64.ultE).
qed.

lemma checked_sqnorm2_total
    (ap0 : BArray8192.t) (na : int) (bp0 : BArray8192.t) (nb : int) :
  phoare [CN._hb_checked_sqnorm2_2048 :
    ap=ap0 /\ acount=W64.of_int na /\ bp=bp0 /\ bcount=W64.of_int nb /\
    0<=na<=2048 /\ 0<=nb<=2048 ==>
    res.`1=W64.of_int (hyperball_sqnorm ap0 na bp0 nb) /\
    res.`2=cn_overflow_mask (hyperball_sqnorm ap0 na bp0 nb)] = 1%r.
proof. by conseq checked_sqnorm2_ll (checked_sqnorm2_correct ap0 na bp0 nb). qed.

lemma checked_sqnorm2_zero_iff_total
    (ap0 : BArray8192.t) (na : int) (bp0 : BArray8192.t) (nb : int) :
  phoare [CN._hb_checked_sqnorm2_2048 :
    ap=ap0 /\ acount=W64.of_int na /\ bp=bp0 /\ bcount=W64.of_int nb /\
    0<=na<=2048 /\ 0<=nb<=2048 ==>
    W64.to_uint res.`1=hyperball_sqnorm ap0 na bp0 nb %% W64.modulus /\
    (res.`2=W64.zero)=(hyperball_sqnorm ap0 na bp0 nb<W64.modulus)] = 1%r.
proof.
  conseq checked_sqnorm2_ll (checked_sqnorm2_correct ap0 na bp0 nb) => //.
  move=> &hr hpre result.
  have hu := W64.of_uintK (hyperball_sqnorm ap0 na bp0 nb).
  have hz := cn_overflow_zero_iff (hyperball_sqnorm ap0 na bp0 nb).
  smt().
qed.

(* Native word-count interface: array sizes are the only input bounds. *)
lemma checked_sqnorm2_words_total
    (ap0 : BArray8192.t) (acount0 : W64.t) (bp0 : BArray8192.t) (bcount0 : W64.t) :
  phoare [CN._hb_checked_sqnorm2_2048 :
    ap=ap0 /\ acount=acount0 /\ bp=bp0 /\ bcount=bcount0 /\
    0<=W64.to_uint acount0<=2048 /\ 0<=W64.to_uint bcount0<=2048 ==>
    res.`1=W64.of_int (hyperball_sqnorm ap0 (W64.to_uint acount0) bp0 (W64.to_uint bcount0)) /\
    res.`2=cn_overflow_mask (hyperball_sqnorm ap0 (W64.to_uint acount0) bp0 (W64.to_uint bcount0))] = 1%r.
proof.
  by conseq (checked_sqnorm2_total ap0 (W64.to_uint acount0) bp0 (W64.to_uint bcount0)) => />;
    smt(W64.to_uintK).
qed.
