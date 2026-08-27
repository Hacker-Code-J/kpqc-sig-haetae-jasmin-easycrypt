require import
  AllCore Dexcepted DInterval Distr FSet IntDiv List Mu_mem Real StdOrder.

from Jasmin require import JModel_x86.

require import KeygenEtaSamplerSpec.

import RealOrder.

theory Mode2FaithfulSecurityIdealEtaByteLawPostFreeze.

(* This theory isolates the ideal-randomness law of one byte consumed by
   [rej_eta].  It does not identify deterministic SHAKE output with iid
   uniform bytes.  That real-to-ideal step remains an explicit XOF boundary. *)

op ideal_eta_uniform_byte : int distr = dinter 0 255.

op ideal_eta_byte_rejected (byte : int) : bool =
  !(0 <= byte < KeygenEtaSamplerSpec.eta_accept_bound_i).

op ideal_eta_accepted_byte : int distr =
  ideal_eta_uniform_byte \ ideal_eta_byte_rejected.

op eta_center_residue (residue : int) : int =
  if residue = 2 then -1 else residue.

op eta_residue_digit (byte digit : int) : int =
  (byte %/ (3 ^ digit)) %% 3.

op ideal_eta_centered_trit_distribution : int distr =
  dmap (dinter 0 2) eta_center_residue.

op ideal_eta_digit_block_distribution : int list distr =
  dmap ideal_eta_accepted_byte KeygenEtaSamplerSpec.eta_decode_byte.

lemma ideal_eta_uniform_byte_lossless :
  is_lossless ideal_eta_uniform_byte.
proof. by rewrite /ideal_eta_uniform_byte; apply dinter_ll. qed.

lemma ideal_eta_uniform_byte_uniform :
  is_uniform ideal_eta_uniform_byte.
proof. by rewrite /ideal_eta_uniform_byte; apply dinter_uni. qed.

lemma ideal_eta_uniform_byte_point byte :
  mu1 ideal_eta_uniform_byte byte =
  if 0 <= byte <= 255 then 1%r / 256%r else 0%r.
proof.
rewrite /ideal_eta_uniform_byte dinter1E.
case (0 <= byte <= 255) => hbyte; first by rewrite /#.
by rewrite /#.
qed.

lemma ideal_eta_accepted_byte_support byte :
  byte \in ideal_eta_accepted_byte <=>
  0 <= byte < KeygenEtaSamplerSpec.eta_accept_bound_i.
proof.
rewrite /ideal_eta_accepted_byte supp_dexcepted
        /ideal_eta_uniform_byte supp_dinter
        /ideal_eta_byte_rejected.
rewrite /KeygenEtaSamplerSpec.eta_accept_bound_i.
smt().
qed.

lemma ideal_eta_accepted_byte_lossless :
  is_lossless ideal_eta_accepted_byte.
proof.
rewrite /ideal_eta_accepted_byte.
apply dexcepted_ll.
+ exact ideal_eta_uniform_byte_lossless.
have hpos :
    0%r < mu ideal_eta_uniform_byte (predC ideal_eta_byte_rejected).
+ rewrite witness_support.
  exists 0.
  split.
  + rewrite /predC /ideal_eta_byte_rejected
            /KeygenEtaSamplerSpec.eta_accept_bound_i.
    smt().
  + rewrite /ideal_eta_uniform_byte supp_dinter.
    smt().
move: hpos.
rewrite mu_not ideal_eta_uniform_byte_lossless.
smt().
qed.

lemma ideal_eta_accepted_byte_uniform :
  is_uniform ideal_eta_accepted_byte.
proof.
rewrite /ideal_eta_accepted_byte.
apply dexcepted_uni.
exact ideal_eta_uniform_byte_uniform.
qed.

lemma ideal_eta_accepted_byte_eq_dinter :
  ideal_eta_accepted_byte = dinter 0 242.
proof.
have hll1 := ideal_eta_accepted_byte_lossless.
have hll2 : is_lossless (dinter 0 242) by apply dinter_ll.
have huni1 := ideal_eta_accepted_byte_uniform.
have huni2 : is_uniform (dinter 0 242) by apply dinter_uni.
have hsupp :
    support ideal_eta_accepted_byte = support (dinter 0 242).
+ apply fun_ext => byte.
  rewrite ideal_eta_accepted_byte_support supp_dinter
          /KeygenEtaSamplerSpec.eta_accept_bound_i.
  smt().
apply/eq_distr => byte.
rewrite (mu1_uni ideal_eta_accepted_byte byte huni1)
        (mu1_uni (dinter 0 242) byte huni2).
rewrite hll1 hll2 hsupp.
trivial.
qed.

lemma ideal_eta_accepted_byte_point byte :
  0 <= byte < KeygenEtaSamplerSpec.eta_accept_bound_i =>
  mu1 ideal_eta_accepted_byte byte = 1%r / 243%r.
proof.
move=> hbyte.
rewrite ideal_eta_accepted_byte_eq_dinter dinter1E.
rewrite /KeygenEtaSamplerSpec.eta_accept_bound_i in hbyte.
have hclosed : 0 <= byte <= 242 by smt().
rewrite hclosed.
rewrite (_ : 242 - 0 + 1 = 243) 1:/#.
trivial.
qed.

lemma ideal_eta_uniform_byte_accept_mass :
  mu ideal_eta_uniform_byte
    (fun byte =>
      0 <= byte < KeygenEtaSamplerSpec.eta_accept_bound_i) =
  243%r / 256%r.
proof.
pose s := rangeset 0 KeygenEtaSamplerSpec.eta_accept_bound_i.
have hevent :
  mu ideal_eta_uniform_byte
    (fun byte =>
      0 <= byte < KeygenEtaSamplerSpec.eta_accept_bound_i) =
  mu ideal_eta_uniform_byte (mem s).
+ apply mu_eq => byte.
  rewrite /s mem_rangeset.
  trivial.
rewrite hevent.
have hpoint : forall byte, byte \in s =>
  mu1 ideal_eta_uniform_byte byte = 1%r / 256%r.
+ move=> byte hbyte.
  rewrite /s mem_rangeset
          /KeygenEtaSamplerSpec.eta_accept_bound_i in hbyte.
  rewrite ideal_eta_uniform_byte_point.
  have hsupport : 0 <= byte <= 255 by smt().
  rewrite hsupport.
  trivial.
rewrite (mu_mem s ideal_eta_uniform_byte (1%r / 256%r) hpoint).
rewrite /s card_rangeset /KeygenEtaSamplerSpec.eta_accept_bound_i.
rewrite (_ : max 0 (243 - 0) = 243) 1:/#.
ring.
qed.

lemma ideal_eta_uniform_byte_reject_mass :
  mu ideal_eta_uniform_byte ideal_eta_byte_rejected =
  13%r / 256%r.
proof.
have hnot :
  predC ideal_eta_byte_rejected =
  (fun byte =>
    0 <= byte < KeygenEtaSamplerSpec.eta_accept_bound_i).
+ apply fun_ext => byte.
  rewrite /predC /ideal_eta_byte_rejected.
  trivial.
have hmass := ideal_eta_uniform_byte_accept_mass.
rewrite -hnot mu_not ideal_eta_uniform_byte_lossless in hmass.
have hcalc : 1%r - 243%r / 256%r = 13%r / 256%r.
+ field; trivial.
smt().
qed.

clone import WhileSamplingFixedTest as IdealEtaByteSampling with
  type input <- int,
  type t <- int,
  op dt <- (fun _ : int => ideal_eta_uniform_byte),
  op test <- (fun _ : int => ideal_eta_byte_rejected).

lemma ideal_eta_byte_rejection_loop_pr &m P :
  Pr[IdealEtaByteSampling.SampleW.sample(0) @ &m : P res] =
  mu ideal_eta_accepted_byte P.
proof.
rewrite
  (IdealEtaByteSampling.pr_sampleW
    &m 0 P ideal_eta_uniform_byte_lossless).
trivial.
qed.

lemma ideal_eta_byte_rejection_loop_lossless :
  phoare [IdealEtaByteSampling.SampleW.sample : true ==> true] = 1%r.
proof.
bypr=> &m _.
rewrite
  (IdealEtaByteSampling.pr_sampleW
    &m i{m} predT ideal_eta_uniform_byte_lossless) /=.
change (mu ideal_eta_accepted_byte predT = 1%r).
exact ideal_eta_accepted_byte_lossless.
qed.

lemma ideal_eta_byte_rejection_loop_point &m byte :
  0 <= byte < KeygenEtaSamplerSpec.eta_accept_bound_i =>
  Pr[IdealEtaByteSampling.SampleW.sample(0) @ &m : res = byte] =
  1%r / 243%r.
proof.
move=> hbyte.
rewrite (ideal_eta_byte_rejection_loop_pr &m (pred1 byte)).
exact (ideal_eta_accepted_byte_point byte hbyte).
qed.

lemma base3_digits_injective x y :
  0 <= x < 243 =>
  0 <= y < 243 =>
  x %% 3 = y %% 3 =>
  (x %/ 3) %% 3 = (y %/ 3) %% 3 =>
  ((x %/ 3) %/ 3) %% 3 = ((y %/ 3) %/ 3) %% 3 =>
  (((x %/ 3) %/ 3) %/ 3) %% 3 =
    (((y %/ 3) %/ 3) %/ 3) %% 3 =>
  ((((x %/ 3) %/ 3) %/ 3) %/ 3) %% 3 =
    ((((y %/ 3) %/ 3) %/ 3) %/ 3) %% 3 =>
  x = y.
proof.
move=> hx hy h0 h1 h2 h3 h4.
have hx0 := divz_eq x 3.
have hx1 := divz_eq (x %/ 3) 3.
have hx2 := divz_eq ((x %/ 3) %/ 3) 3.
have hx3 := divz_eq (((x %/ 3) %/ 3) %/ 3) 3.
have hx4 := divz_eq ((((x %/ 3) %/ 3) %/ 3) %/ 3) 3.
have hy0 := divz_eq y 3.
have hy1 := divz_eq (y %/ 3) 3.
have hy2 := divz_eq ((y %/ 3) %/ 3) 3.
have hy3 := divz_eq (((y %/ 3) %/ 3) %/ 3) 3.
have hy4 := divz_eq ((((y %/ 3) %/ 3) %/ 3) %/ 3) 3.
have hxq1 : 0 <= x %/ 3 < 81.
+ rewrite divz_ge0 1:// ltz_divLR 1://; smt().
have hxq2 : 0 <= (x %/ 3) %/ 3 < 27.
+ rewrite divz_ge0 1:// ltz_divLR 1://; smt().
have hxq3 : 0 <= ((x %/ 3) %/ 3) %/ 3 < 9.
+ rewrite divz_ge0 1:// ltz_divLR 1://; smt().
have hxq4 : 0 <= (((x %/ 3) %/ 3) %/ 3) %/ 3 < 3.
+ rewrite divz_ge0 1:// ltz_divLR 1://; smt().
have hyq1 : 0 <= y %/ 3 < 81.
+ rewrite divz_ge0 1:// ltz_divLR 1://; smt().
have hyq2 : 0 <= (y %/ 3) %/ 3 < 27.
+ rewrite divz_ge0 1:// ltz_divLR 1://; smt().
have hyq3 : 0 <= ((y %/ 3) %/ 3) %/ 3 < 9.
+ rewrite divz_ge0 1:// ltz_divLR 1://; smt().
have hyq4 : 0 <= (((y %/ 3) %/ 3) %/ 3) %/ 3 < 3.
+ rewrite divz_ge0 1:// ltz_divLR 1://; smt().
have hx5 : ((((x %/ 3) %/ 3) %/ 3) %/ 3) %/ 3 = 0.
+ apply pdiv_small; exact hxq4.
have hy5 : ((((y %/ 3) %/ 3) %/ 3) %/ 3) %/ 3 = 0.
+ apply pdiv_small; exact hyq4.
smt().
qed.

lemma dinter_quotient_point p q i :
  0 < p =>
  0 < q =>
  q %| p =>
  mu (dinter 0 (p - 1)) (fun x => x %/ q = i) =
    if 0 <= i < p %/ q then (q%r / p%r) else 0%r.
proof.
move=> hp hq hqp.
case (0 <= i < p %/ q) => hi.
+ have hpeq : (p %/ q) * q = p by exact (divzK q p hqp).
  pose s := rangeset (i * q) ((i + 1) * q).
  have hevent :
    mu (dinter 0 (p - 1)) (fun x => x %/ q = i) =
    mu (dinter 0 (p - 1)) (mem s).
  + apply mu_eq_support => x hx.
    rewrite supp_dinter in hx.
    rewrite /s mem_rangeset.
    apply/eq_iff.
    exact (divz_eqP x q i hq).
  rewrite hevent.
  have hpoint : forall x, x \in s =>
      mu (dinter 0 (p - 1)) (pred1 x) = 1%r / p%r.
  + move=> x hx.
    rewrite /s mem_rangeset in hx.
    rewrite /pred1 dinter1E /=.
    have hi1 : i + 1 <= p %/ q by smt().
    have hmul : (i + 1) * q <= (p %/ q) * q.
    + apply IntOrder.ler_wpmul2r.
      + smt().
      exact hi1.
    rewrite hpeq in hmul.
    have hiq0 : 0 <= i * q.
    + apply IntOrder.mulr_ge0; smt().
    have hx0 : 0 <= x by smt().
    have hxp1 : x <= p - 1 by smt().
    have hxp : 0 <= x <= p - 1 by smt().
    rewrite hxp.
    ring.
  rewrite (mu_mem s (dinter 0 (p - 1)) (1%r / p%r) hpoint).
  rewrite /s card_rangeset.
  have hwidth : max 0 ((i + 1) * q - i * q) = q by smt().
  rewrite hwidth.
  ring.
have hzero :
  mu (dinter 0 (p - 1)) (fun x => x %/ q = i) = 0%r.
+ apply mu0_false => x hx.
  rewrite supp_dinter in hx.
  case (x %/ q = i) => hxi; last trivial.
  have hxi0 : 0 <= x %/ q by rewrite divz_ge0 1:hq; smt().
  have hxiu : x %/ q < p %/ q.
  + have hxlt : x < p by smt().
    have hpdiv : p %/ q * q = p by exact (divzK q p hqp).
    rewrite ltz_divLR 1:hq.
    smt().
  smt().
rewrite hzero.
trivial.
qed.

lemma dmap_dinter_quotient p q :
  0 < p =>
  0 < q =>
  q %| p =>
  dmap (dinter 0 (p - 1)) (fun x => x %/ q) =
  dinter 0 (p %/ q - 1).
proof.
move=> hp hq hqp.
apply/eq_distr => i.
rewrite dmap1E.
have hpoint := dinter_quotient_point p q i hp hq hqp.
change
  (mu (dinter 0 (p - 1)) (fun x => x %/ q = i) =
   mu1 (dinter 0 (p %/ q - 1)) i).
rewrite hpoint dinter1E.
rewrite -(ltzS i (p %/ q - 1)).
rewrite (_ : p %/ q - 1 + 1 = p %/ q) 1:/#.
case (0 <= i < p %/ q) => hi.
+ have hdivpos : 0 < p %/ q.
  + rewrite ltz_divRL 1:hq 1:hqp.
    smt().
  have hpq : (p %/ q) * q = p by exact (divzK q p hqp).
  have hpq0 : (p %/ q)%r <> 0%r by rewrite eq_fromint; smt().
  have hq0 : q%r <> 0%r by rewrite eq_fromint; smt().
  rewrite (_ : (p %/ q - 1 - 0 + 1) = p %/ q) 1:/#.
  have hpqR : p%r = (p %/ q)%r * q%r.
  + rewrite -fromintM hpq.
    trivial.
  rewrite hpqR.
  rewrite RField.invfM.
  rewrite RField.mulrCA (RField.divff q%r hq0).
  ring.
trivial.
qed.

lemma eta_residue_digit_distribution digit :
  0 <= digit < KeygenEtaSamplerSpec.eta_digits_per_byte_i =>
  dmap (dinter 0 242) (fun byte => eta_residue_digit byte digit) =
  dinter 0 2.
proof.
move=> hdigit.
rewrite /KeygenEtaSamplerSpec.eta_digits_per_byte_i in hdigit.
have hpowpos : 0 < 3 ^ digit.
+ apply IntOrder.expr_gt0; smt().
have hpowdvd : 3 ^ digit %| 243.
+ have h243 : 243 = 3 ^ 5 by ring.
  rewrite h243.
  apply dvdz_exp2l.
  smt().
have hquotE : 243 %/ (3 ^ digit) = 3 ^ (5 - digit).
+ have h243E : 243 = 3 ^ 5 by ring.
  rewrite h243E -exprD_subz 1:/# 1:/#.
  trivial.
have h3dvd : 3 %| 243 %/ (3 ^ digit).
+ rewrite hquotE.
  have hpow : 3 ^ 1 %| 3 ^ (5 - digit).
  + apply dvdz_exp2l.
    smt().
  move: hpow.
  rewrite expr1.
  done.
rewrite /eta_residue_digit.
have hfun :
  (fun byte => (byte %/ (3 ^ digit)) %% 3) =
  ((fun x => x %% 3) \o (fun byte => byte %/ (3 ^ digit))).
+ apply fun_ext => byte.
  rewrite /(\o).
  trivial.
rewrite hfun -dmap_comp.
rewrite (dmap_dinter_quotient 243 (3 ^ digit)) 1:// 1:hpowpos
        1:hpowdvd.
apply duni_range_dvd.
+ rewrite hquotE.
  apply IntOrder.expr_gt0; smt().
+ trivial.
exact h3dvd.
qed.

lemma eta_centered_digit_as_centered_residue byte digit :
  0 <= byte < KeygenEtaSamplerSpec.eta_accept_bound_i =>
  0 <= digit < KeygenEtaSamplerSpec.eta_digits_per_byte_i =>
  KeygenEtaSamplerSpec.eta_centered_digit byte digit =
  eta_center_residue (eta_residue_digit byte digit).
proof.
move=> hbyte hdigit.
rewrite /KeygenEtaSamplerSpec.eta_centered_digit
        /KeygenEtaSamplerSpec.centered_trit_value
        /KeygenEtaSamplerSpec.base3_residue
        /eta_center_residue /eta_residue_digit.
rewrite
  (KeygenEtaSamplerSpec.eta_accepted_quotient_word
    byte digit hbyte _) 1:/#.
trivial.
qed.

lemma eta_residue_digit_range byte digit :
  0 <= eta_residue_digit byte digit < 3.
proof.
rewrite /eta_residue_digit.
by smt(modz_cmp).
qed.

lemma eta_center_residue_injective residue1 residue2 :
  0 <= residue1 < 3 =>
  0 <= residue2 < 3 =>
  eta_center_residue residue1 = eta_center_residue residue2 =>
  residue1 = residue2.
proof.
rewrite /eta_center_residue.
smt().
qed.

lemma eta_centered_digit_residue_injective byte1 byte2 digit :
  0 <= byte1 < KeygenEtaSamplerSpec.eta_accept_bound_i =>
  0 <= byte2 < KeygenEtaSamplerSpec.eta_accept_bound_i =>
  0 <= digit < KeygenEtaSamplerSpec.eta_digits_per_byte_i =>
  KeygenEtaSamplerSpec.eta_centered_digit byte1 digit =
    KeygenEtaSamplerSpec.eta_centered_digit byte2 digit =>
  eta_residue_digit byte1 digit = eta_residue_digit byte2 digit.
proof.
move=> hbyte1 hbyte2 hdigit heq.
rewrite
  (eta_centered_digit_as_centered_residue byte1 digit hbyte1 hdigit)
  (eta_centered_digit_as_centered_residue byte2 digit hbyte2 hdigit)
  in heq.
exact
  (eta_center_residue_injective
    (eta_residue_digit byte1 digit)
    (eta_residue_digit byte2 digit)
    (eta_residue_digit_range byte1 digit)
    (eta_residue_digit_range byte2 digit)
    heq).
qed.

lemma eta_div_pow2 value :
  value %/ (3 ^ 2) = (value %/ 3) %/ 3.
proof.
have h := KeygenEtaSamplerSpec.eta_div3_digit_succ value 1 _.
+ trivial.
move: h.
rewrite (_ : 1 + 1 = 2) 1:/# expr1.
done.
qed.

lemma eta_div_pow3 value :
  value %/ (3 ^ 3) = ((value %/ 3) %/ 3) %/ 3.
proof.
have h := KeygenEtaSamplerSpec.eta_div3_digit_succ value 2 _.
+ trivial.
move: h.
rewrite (_ : 2 + 1 = 3) 1:/# eta_div_pow2.
done.
qed.

lemma eta_div_pow4 value :
  value %/ (3 ^ 4) = (((value %/ 3) %/ 3) %/ 3) %/ 3.
proof.
have h := KeygenEtaSamplerSpec.eta_div3_digit_succ value 3 _.
+ trivial.
move: h.
rewrite (_ : 3 + 1 = 4) 1:/# eta_div_pow3.
done.
qed.

lemma eta_decode_byte_digit_eq byte1 byte2 digit :
  0 <= byte1 < KeygenEtaSamplerSpec.eta_accept_bound_i =>
  0 <= byte2 < KeygenEtaSamplerSpec.eta_accept_bound_i =>
  0 <= digit < KeygenEtaSamplerSpec.eta_digits_per_byte_i =>
  KeygenEtaSamplerSpec.eta_decode_byte byte1 =
    KeygenEtaSamplerSpec.eta_decode_byte byte2 =>
  KeygenEtaSamplerSpec.eta_centered_digit byte1 digit =
    KeygenEtaSamplerSpec.eta_centered_digit byte2 digit.
proof.
move=> hbyte1 hbyte2 hdigit hdecode.
have hnth :
  nth 0 (KeygenEtaSamplerSpec.eta_decode_byte byte1) digit =
  nth 0 (KeygenEtaSamplerSpec.eta_decode_byte byte2) digit.
+ rewrite hdecode.
  trivial.
rewrite
  (KeygenEtaSamplerSpec.eta_decode_byte_nth
    byte1 digit hbyte1 hdigit)
  (KeygenEtaSamplerSpec.eta_decode_byte_nth
    byte2 digit hbyte2 hdigit)
  in hnth.
exact hnth.
qed.

lemma eta_decode_byte_injective byte1 byte2 :
  0 <= byte1 < KeygenEtaSamplerSpec.eta_accept_bound_i =>
  0 <= byte2 < KeygenEtaSamplerSpec.eta_accept_bound_i =>
  KeygenEtaSamplerSpec.eta_decode_byte byte1 =
    KeygenEtaSamplerSpec.eta_decode_byte byte2 =>
  byte1 = byte2.
proof.
move=> hbyte1 hbyte2 hdecode.
have hd0 : 0 <= 0 < KeygenEtaSamplerSpec.eta_digits_per_byte_i by trivial.
have hd1 : 0 <= 1 < KeygenEtaSamplerSpec.eta_digits_per_byte_i by trivial.
have hd2 : 0 <= 2 < KeygenEtaSamplerSpec.eta_digits_per_byte_i by trivial.
have hd3 : 0 <= 3 < KeygenEtaSamplerSpec.eta_digits_per_byte_i by trivial.
have hd4 : 0 <= 4 < KeygenEtaSamplerSpec.eta_digits_per_byte_i by trivial.
have h0 :=
  eta_centered_digit_residue_injective byte1 byte2 0
    hbyte1 hbyte2 hd0
    (eta_decode_byte_digit_eq byte1 byte2 0
      hbyte1 hbyte2 hd0 hdecode).
have h1 :=
  eta_centered_digit_residue_injective byte1 byte2 1
    hbyte1 hbyte2 hd1
    (eta_decode_byte_digit_eq byte1 byte2 1
      hbyte1 hbyte2 hd1 hdecode).
have h2 :=
  eta_centered_digit_residue_injective byte1 byte2 2
    hbyte1 hbyte2 hd2
    (eta_decode_byte_digit_eq byte1 byte2 2
      hbyte1 hbyte2 hd2 hdecode).
have h3 :=
  eta_centered_digit_residue_injective byte1 byte2 3
    hbyte1 hbyte2 hd3
    (eta_decode_byte_digit_eq byte1 byte2 3
      hbyte1 hbyte2 hd3 hdecode).
have h4 :=
  eta_centered_digit_residue_injective byte1 byte2 4
    hbyte1 hbyte2 hd4
    (eta_decode_byte_digit_eq byte1 byte2 4
      hbyte1 hbyte2 hd4 hdecode).
rewrite /eta_residue_digit expr0 !divz1 in h0.
rewrite /eta_residue_digit expr1 in h1.
rewrite /eta_residue_digit !eta_div_pow2 in h2.
rewrite /eta_residue_digit !eta_div_pow3 in h3.
rewrite /eta_residue_digit !eta_div_pow4 in h4.
rewrite /KeygenEtaSamplerSpec.eta_accept_bound_i in hbyte1.
rewrite /KeygenEtaSamplerSpec.eta_accept_bound_i in hbyte2.
exact
  (base3_digits_injective
    byte1 byte2 hbyte1 hbyte2 h0 h1 h2 h3 h4).
qed.

lemma ideal_eta_digit_block_lossless :
  is_lossless ideal_eta_digit_block_distribution.
proof.
rewrite /ideal_eta_digit_block_distribution.
apply dmap_ll.
exact ideal_eta_accepted_byte_lossless.
qed.

lemma ideal_eta_digit_block_point byte :
  0 <= byte < KeygenEtaSamplerSpec.eta_accept_bound_i =>
  mu1 ideal_eta_digit_block_distribution
    (KeygenEtaSamplerSpec.eta_decode_byte byte) =
  1%r / 243%r.
proof.
move=> hbyte.
rewrite /ideal_eta_digit_block_distribution dmap1E.
have hevent :
  mu ideal_eta_accepted_byte
    (pred1 (KeygenEtaSamplerSpec.eta_decode_byte byte) \o
      KeygenEtaSamplerSpec.eta_decode_byte) =
  mu ideal_eta_accepted_byte (pred1 byte).
+ apply mu_eq_support => candidate hcandidate.
  rewrite ideal_eta_accepted_byte_support in hcandidate.
  rewrite /pred1 /(\o) /=.
  apply/eq_iff.
  split.
  + move=> hsame.
    exact
      (eta_decode_byte_injective
        candidate byte hcandidate hbyte hsame).
  move=> ->.
  trivial.
rewrite hevent.
exact (ideal_eta_accepted_byte_point byte hbyte).
qed.

lemma ideal_eta_centered_digit_distribution digit :
  0 <= digit < KeygenEtaSamplerSpec.eta_digits_per_byte_i =>
  dmap ideal_eta_accepted_byte
    (fun byte => KeygenEtaSamplerSpec.eta_centered_digit byte digit) =
  ideal_eta_centered_trit_distribution.
proof.
move=> hdigit.
rewrite ideal_eta_accepted_byte_eq_dinter
        /ideal_eta_centered_trit_distribution.
have hmap :
  dmap (dinter 0 242)
    (fun byte => KeygenEtaSamplerSpec.eta_centered_digit byte digit) =
  dmap (dinter 0 242)
    (fun byte => eta_center_residue (eta_residue_digit byte digit)).
+ apply eq_dmap_in => byte hbyte.
  rewrite supp_dinter in hbyte.
  apply eta_centered_digit_as_centered_residue.
  + rewrite /KeygenEtaSamplerSpec.eta_accept_bound_i.
    smt().
  exact hdigit.
rewrite hmap.
have hfun :
  (fun byte => eta_center_residue (eta_residue_digit byte digit)) =
  (eta_center_residue \o (fun byte => eta_residue_digit byte digit)).
+ apply fun_ext => byte.
  rewrite /(\o).
  trivial.
rewrite hfun -dmap_comp.
rewrite (eta_residue_digit_distribution digit hdigit).
trivial.
qed.

lemma ideal_eta_centered_trit_point_neg1 :
  mu1 ideal_eta_centered_trit_distribution (-1) = 1%r / 3%r.
proof.
rewrite /ideal_eta_centered_trit_distribution dmap1E.
have hevent :
  mu (dinter 0 2) (pred1 (-1) \o eta_center_residue) =
  mu (dinter 0 2) (pred1 2).
+ apply mu_eq_support => residue hresidue.
  rewrite supp_dinter in hresidue.
  rewrite /pred1 /(\o) /eta_center_residue.
  smt().
rewrite hevent dinter1E /pred1 /=.
trivial.
qed.

lemma ideal_eta_centered_trit_point_zero :
  mu1 ideal_eta_centered_trit_distribution 0 = 1%r / 3%r.
proof.
rewrite /ideal_eta_centered_trit_distribution dmap1E.
have hevent :
  mu (dinter 0 2) (pred1 0 \o eta_center_residue) =
  mu (dinter 0 2) (pred1 0).
+ apply mu_eq_support => residue hresidue.
  rewrite supp_dinter in hresidue.
  rewrite /pred1 /(\o) /eta_center_residue.
  smt().
rewrite hevent dinter1E /pred1 /=.
trivial.
qed.

lemma ideal_eta_centered_trit_point_one :
  mu1 ideal_eta_centered_trit_distribution 1 = 1%r / 3%r.
proof.
rewrite /ideal_eta_centered_trit_distribution dmap1E.
have hevent :
  mu (dinter 0 2) (pred1 1 \o eta_center_residue) =
  mu (dinter 0 2) (pred1 1).
+ apply mu_eq_support => residue hresidue.
  rewrite supp_dinter in hresidue.
  rewrite /pred1 /(\o) /eta_center_residue.
  smt().
rewrite hevent dinter1E /pred1 /=.
trivial.
qed.

lemma ideal_eta_centered_digit_point &m digit value :
  0 <= digit < KeygenEtaSamplerSpec.eta_digits_per_byte_i =>
  (value = -1 \/ value = 0 \/ value = 1) =>
  Pr[IdealEtaByteSampling.SampleW.sample(0) @ &m :
       KeygenEtaSamplerSpec.eta_centered_digit res digit = value] =
  1%r / 3%r.
proof.
move=> hdigit hvalue.
rewrite (ideal_eta_byte_rejection_loop_pr &m
  (fun byte => KeygenEtaSamplerSpec.eta_centered_digit byte digit = value)).
have hmass :
  mu ideal_eta_accepted_byte
    (fun byte => KeygenEtaSamplerSpec.eta_centered_digit byte digit = value) =
  mu ideal_eta_centered_trit_distribution (pred1 value).
+ have hleft :
    mu ideal_eta_accepted_byte
      (fun byte => KeygenEtaSamplerSpec.eta_centered_digit byte digit = value) =
    mu1
      (dmap ideal_eta_accepted_byte
        (fun byte => KeygenEtaSamplerSpec.eta_centered_digit byte digit))
      value.
  + rewrite dmap1E /pred1 /(\o) /=.
    trivial.
  rewrite hleft.
  rewrite (ideal_eta_centered_digit_distribution digit hdigit).
  trivial.
rewrite hmass.
move: hvalue => [-> | [-> | ->]].
+ exact ideal_eta_centered_trit_point_neg1.
+ exact ideal_eta_centered_trit_point_zero.
exact ideal_eta_centered_trit_point_one.
qed.

end Mode2FaithfulSecurityIdealEtaByteLawPostFreeze.
