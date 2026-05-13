require import AllCore IntDiv List.

theory HAETAE_Keccak1600.

type keccak_byte = int.
type keccak_lane = bool list.
type keccak_state = keccak_lane list.

op keccak_lane_bits : int = 64.
op keccak_state_lanes : int = 25.
op keccak_state_bytes : int = 200.

op keccak_byte_norm (b : keccak_byte) : keccak_byte = b %% 256.
op keccak_byte_bit (b : keccak_byte) (i : int) : bool =
  ((keccak_byte_norm b) %/ (2 ^ i)) %% 2 <> 0.
op keccak_word_norm (w : int) : int = w %% (2 ^ keccak_lane_bits).
op keccak_word_bit (w : int) (i : int) : bool =
  ((keccak_word_norm w) %/ (2 ^ i)) %% 2 <> 0.

op keccak_lane_zero : keccak_lane = nseq keccak_lane_bits false.
op keccak_lane_bit (lane : keccak_lane) (i : int) : bool =
  nth false lane i.
op keccak_lane_wf (lane : keccak_lane) : bool =
  size lane = keccak_lane_bits.

op keccak_lane_xor (a b : keccak_lane) : keccak_lane =
  mkseq
    (fun i => keccak_lane_bit a i <> keccak_lane_bit b i)
    keccak_lane_bits.
op keccak_lane_and (a b : keccak_lane) : keccak_lane =
  mkseq
    (fun i => keccak_lane_bit a i /\ keccak_lane_bit b i)
    keccak_lane_bits.
op keccak_lane_not (a : keccak_lane) : keccak_lane =
  mkseq
    (fun i => if keccak_lane_bit a i then false else true)
    keccak_lane_bits.
op keccak_lane_rotl (a : keccak_lane) (offset : int) : keccak_lane =
  mkseq
    (fun i => keccak_lane_bit a ((i - offset) %% keccak_lane_bits))
    keccak_lane_bits.

op keccak_lane_of_int (x : int) : keccak_lane =
  mkseq (fun i => keccak_word_bit x i) keccak_lane_bits.

op keccak_lane_to_byte (lane : keccak_lane) (byte_index : int) : keccak_byte =
  sumz
    (map
      (fun j =>
         if keccak_lane_bit lane (8 * byte_index + j)
         then 2 ^ j
         else 0)
      (range 0 8)).

op keccak_bytes_to_lane (bs : keccak_byte list) (lane_index : int) :
  keccak_lane =
  mkseq
    (fun bit =>
       keccak_byte_bit
         (nth 0 bs (8 * lane_index + bit %/ 8))
         (bit %% 8))
    keccak_lane_bits.

op keccak_lanes_of_bytes (bs : keccak_byte list) : keccak_state =
  mkseq (fun lane => keccak_bytes_to_lane bs lane) keccak_state_lanes.

op keccak_bytes_of_lanes (st : keccak_state) : keccak_byte list =
  mkseq
    (fun i =>
       keccak_lane_to_byte
         (nth keccak_lane_zero st (i %/ 8))
         (i %% 8))
    keccak_state_bytes.

op keccak_lane_index (x y : int) : int =
  (x %% 5) + 5 * (y %% 5).
op keccak_state_lane (st : keccak_state) (x y : int) : keccak_lane =
  nth keccak_lane_zero st (keccak_lane_index x y).

op keccak_rho_offsets : int list =
  0 :: 1 :: 62 :: 28 :: 27 ::
  36 :: 44 :: 6 :: 55 :: 20 ::
  3 :: 10 :: 43 :: 25 :: 39 ::
  41 :: 45 :: 15 :: 21 :: 8 ::
  18 :: 2 :: 61 :: 56 :: 14 :: [].

op keccak_round_constants : int list =
  1 ::
  32898 ::
  9223372036854808714 ::
  9223372039002292224 ::
  32907 ::
  2147483649 ::
  9223372039002292353 ::
  9223372036854808585 ::
  138 ::
  136 ::
  2147516425 ::
  2147483658 ::
  2147516555 ::
  9223372036854775947 ::
  9223372036854808713 ::
  9223372036854808579 ::
  9223372036854808578 ::
  9223372036854775936 ::
  32778 ::
  9223372039002259466 ::
  9223372039002292353 ::
  9223372036854808704 ::
  2147483649 ::
  9223372039002292232 :: [].

op keccak_theta_c (st : keccak_state) (x : int) : keccak_lane =
  keccak_lane_xor
    (keccak_lane_xor
      (keccak_lane_xor
        (keccak_lane_xor
          (keccak_state_lane st x 0)
          (keccak_state_lane st x 1))
        (keccak_state_lane st x 2))
      (keccak_state_lane st x 3))
    (keccak_state_lane st x 4).

op keccak_theta_d (st : keccak_state) (x : int) : keccak_lane =
  keccak_lane_xor
    (keccak_theta_c st (x + 4))
    (keccak_lane_rotl (keccak_theta_c st (x + 1)) 1).

op keccak_theta (st : keccak_state) : keccak_state =
  mkseq
    (fun i =>
       let x = i %% 5 in
       let y = i %/ 5 in
       keccak_lane_xor
         (keccak_state_lane st x y)
         (keccak_theta_d st x))
    keccak_state_lanes.

op keccak_rho_pi (st : keccak_state) : keccak_state =
  mkseq
    (fun i =>
       let x = i %% 5 in
       let y = i %/ 5 in
       let sx = (x + 3 * y) %% 5 in
       let sy = x in
       keccak_lane_rotl
         (keccak_state_lane st sx sy)
         (nth 0 keccak_rho_offsets (keccak_lane_index sx sy)))
    keccak_state_lanes.

op keccak_chi (st : keccak_state) : keccak_state =
  mkseq
    (fun i =>
       let x = i %% 5 in
       let y = i %/ 5 in
       keccak_lane_xor
         (keccak_state_lane st x y)
         (keccak_lane_and
           (keccak_lane_not (keccak_state_lane st (x + 1) y))
           (keccak_state_lane st (x + 2) y)))
    keccak_state_lanes.

op keccak_iota (st : keccak_state) (rc : keccak_lane) : keccak_state =
  mkseq
    (fun i =>
       if i = 0
       then keccak_lane_xor (nth keccak_lane_zero st 0) rc
       else nth keccak_lane_zero st i)
    keccak_state_lanes.

op keccak_round (st : keccak_state) (rc : keccak_lane) : keccak_state =
  keccak_iota (keccak_chi (keccak_rho_pi (keccak_theta st))) rc.

op keccak_f1600_lanes (st : keccak_state) : keccak_state =
  foldl
    (fun acc rc => keccak_round acc (keccak_lane_of_int rc))
    st
    keccak_round_constants.

op keccak_f1600_bytes (st : keccak_byte list) : keccak_byte list =
  keccak_bytes_of_lanes (keccak_f1600_lanes (keccak_lanes_of_bytes st)).

lemma keccak_lane_bitsE :
  keccak_lane_bits = 64.
proof. by rewrite /keccak_lane_bits. qed.

lemma keccak_state_lanesE :
  keccak_state_lanes = 25.
proof. by rewrite /keccak_state_lanes. qed.

lemma keccak_state_bytesE :
  keccak_state_bytes = 200.
proof. by rewrite /keccak_state_bytes. qed.

lemma keccak_lane_zero_wf :
  keccak_lane_wf keccak_lane_zero.
proof. by rewrite /keccak_lane_wf /keccak_lane_zero size_nseq. qed.

lemma keccak_lane_xor_wf a b :
  keccak_lane_wf (keccak_lane_xor a b).
proof. by rewrite /keccak_lane_wf /keccak_lane_xor size_mkseq. qed.

lemma keccak_lane_and_wf a b :
  keccak_lane_wf (keccak_lane_and a b).
proof. by rewrite /keccak_lane_wf /keccak_lane_and size_mkseq. qed.

lemma keccak_lane_not_wf a :
  keccak_lane_wf (keccak_lane_not a).
proof. by rewrite /keccak_lane_wf /keccak_lane_not size_mkseq. qed.

lemma keccak_lane_rotl_wf a offset :
  keccak_lane_wf (keccak_lane_rotl a offset).
proof. by rewrite /keccak_lane_wf /keccak_lane_rotl size_mkseq. qed.

lemma keccak_lane_of_int_wf x :
  keccak_lane_wf (keccak_lane_of_int x).
proof. by rewrite /keccak_lane_wf /keccak_lane_of_int size_mkseq. qed.

lemma keccak_lane_mod_range x :
  0 <= x %% keccak_lane_bits < keccak_lane_bits.
proof. by rewrite /keccak_lane_bits; smt(). qed.

lemma keccak_word_modulus_pos :
  0 < 2 ^ keccak_lane_bits.
proof. by rewrite /keccak_lane_bits; smt(). qed.

lemma keccak_word_norm_small w :
  0 <= w < 2 ^ keccak_lane_bits =>
  keccak_word_norm w = w.
proof.
move=> w_range.
by rewrite /keccak_word_norm pmod_small.
qed.

lemma keccak_pow2_0E :
  2 ^ 0 = 1.
proof. by rewrite expr0. qed.

lemma keccak_pow2_1E :
  2 ^ 1 = 2.
proof. by rewrite expr1. qed.

lemma keccak_pow2_2E :
  2 ^ 2 = 4.
proof. by rewrite expr2. qed.

lemma keccak_pow2_3E :
  2 ^ 3 = 8.
proof.
rewrite (_ : 3 = 2 + 1) 1:/# exprS //.
by rewrite keccak_pow2_2E.
qed.

lemma keccak_pow2_4E :
  2 ^ 4 = 16.
proof.
rewrite (_ : 4 = 3 + 1) 1:/# exprS //.
by rewrite keccak_pow2_3E.
qed.

lemma keccak_pow2_5E :
  2 ^ 5 = 32.
proof.
rewrite (_ : 5 = 4 + 1) 1:/# exprS //.
by rewrite keccak_pow2_4E.
qed.

lemma keccak_pow2_6E :
  2 ^ 6 = 64.
proof.
rewrite (_ : 6 = 5 + 1) 1:/# exprS //.
by rewrite keccak_pow2_5E.
qed.

lemma keccak_pow2_7E :
  2 ^ 7 = 128.
proof.
rewrite (_ : 7 = 6 + 1) 1:/# exprS //.
by rewrite keccak_pow2_6E.
qed.

lemma keccak_bytes_to_lane_wf bs lane_index :
  keccak_lane_wf (keccak_bytes_to_lane bs lane_index).
proof. by rewrite /keccak_lane_wf /keccak_bytes_to_lane size_mkseq. qed.

lemma keccak_rho_offsets_size :
  size keccak_rho_offsets = keccak_state_lanes.
proof. by rewrite /keccak_rho_offsets /keccak_state_lanes. qed.

lemma keccak_round_constants_size :
  size keccak_round_constants = 24.
proof. by rewrite /keccak_round_constants. qed.

lemma keccak_lanes_of_bytes_size bs :
  size (keccak_lanes_of_bytes bs) = keccak_state_lanes.
proof. by rewrite /keccak_lanes_of_bytes size_mkseq. qed.

lemma keccak_lanes_of_bytes_lane_wf bs lane :
  0 <= lane < keccak_state_lanes =>
  keccak_lane_wf
    (nth keccak_lane_zero (keccak_lanes_of_bytes bs) lane).
proof.
move=> lane_range.
rewrite /keccak_lanes_of_bytes nth_mkseq; first by smt().
by apply keccak_bytes_to_lane_wf.
qed.

lemma keccak_lanes_of_bytes_bitE bs lane bit :
  0 <= lane < keccak_state_lanes =>
  0 <= bit < keccak_lane_bits =>
  keccak_lane_bit
    (nth keccak_lane_zero (keccak_lanes_of_bytes bs) lane)
    bit =
  keccak_byte_bit
    (nth 0 bs (8 * lane + bit %/ 8))
    (bit %% 8).
proof.
move=> lane_range bit_range.
rewrite /keccak_lane_bit /keccak_lanes_of_bytes nth_mkseq;
  first by smt().
by rewrite /keccak_bytes_to_lane nth_mkseq.
qed.

lemma keccak_lane_xor_bitE a b bit :
  0 <= bit < keccak_lane_bits =>
  keccak_lane_bit (keccak_lane_xor a b) bit =
  (keccak_lane_bit a bit <> keccak_lane_bit b bit).
proof.
move=> bit_range.
rewrite /keccak_lane_bit /keccak_lane_xor nth_mkseq; first by smt().
by [].
qed.

lemma keccak_lane_and_bitE a b bit :
  0 <= bit < keccak_lane_bits =>
  keccak_lane_bit (keccak_lane_and a b) bit =
  (keccak_lane_bit a bit /\ keccak_lane_bit b bit).
proof.
move=> bit_range.
rewrite /keccak_lane_bit /keccak_lane_and nth_mkseq; first by smt().
by [].
qed.

lemma keccak_lane_not_bitE a bit :
  0 <= bit < keccak_lane_bits =>
  keccak_lane_bit (keccak_lane_not a) bit =
  (if keccak_lane_bit a bit then false else true).
proof.
move=> bit_range.
rewrite /keccak_lane_bit /keccak_lane_not nth_mkseq; first by smt().
by [].
qed.

lemma keccak_lane_rotl_bitE a offset bit :
  0 <= bit < keccak_lane_bits =>
  keccak_lane_bit (keccak_lane_rotl a offset) bit =
  keccak_lane_bit a ((bit - offset) %% keccak_lane_bits).
proof.
move=> bit_range.
rewrite /keccak_lane_bit /keccak_lane_rotl nth_mkseq; first by smt().
by [].
qed.

lemma keccak_lane_of_int_bitE x bit :
  0 <= bit < keccak_lane_bits =>
  keccak_lane_bit (keccak_lane_of_int x) bit =
  keccak_word_bit x bit.
proof.
move=> bit_range.
rewrite /keccak_lane_bit /keccak_lane_of_int nth_mkseq; first by smt().
by [].
qed.

lemma keccak_state_lane_bitE st x y bit :
  keccak_lane_bit (keccak_state_lane st x y) bit =
  keccak_lane_bit
    (nth keccak_lane_zero st (keccak_lane_index x y))
    bit.
proof. by rewrite /keccak_state_lane. qed.

op keccak_theta_c_bit_index_value
   (st : keccak_state) (x bit : int) : bool =
  ((((keccak_lane_bit
        (nth keccak_lane_zero st (keccak_lane_index x 0)) bit <>
      keccak_lane_bit
        (nth keccak_lane_zero st (keccak_lane_index x 1)) bit) <>
     keccak_lane_bit
       (nth keccak_lane_zero st (keccak_lane_index x 2)) bit) <>
    keccak_lane_bit
      (nth keccak_lane_zero st (keccak_lane_index x 3)) bit) <>
   keccak_lane_bit
     (nth keccak_lane_zero st (keccak_lane_index x 4)) bit).

op keccak_theta_d_bit_index_value
   (st : keccak_state) (x bit : int) : bool =
  keccak_theta_c_bit_index_value st (x + 4) bit <>
  keccak_theta_c_bit_index_value
    st
    (x + 1)
    ((bit - 1) %% keccak_lane_bits).

lemma keccak_theta_c_bitE st x bit :
  0 <= bit < keccak_lane_bits =>
  keccak_lane_bit (keccak_theta_c st x) bit =
  ((((keccak_lane_bit (keccak_state_lane st x 0) bit <>
      keccak_lane_bit (keccak_state_lane st x 1) bit) <>
     keccak_lane_bit (keccak_state_lane st x 2) bit) <>
    keccak_lane_bit (keccak_state_lane st x 3) bit) <>
   keccak_lane_bit (keccak_state_lane st x 4) bit).
proof.
move=> bit_range.
by rewrite /keccak_theta_c !keccak_lane_xor_bitE.
qed.

lemma keccak_theta_c_bit_indexE st x bit :
  0 <= bit < keccak_lane_bits =>
  keccak_lane_bit (keccak_theta_c st x) bit =
  keccak_theta_c_bit_index_value st x bit.
proof.
move=> bit_range.
by rewrite /keccak_theta_c_bit_index_value
           keccak_theta_c_bitE // !keccak_state_lane_bitE.
qed.

lemma keccak_theta_d_bitE st x bit :
  0 <= bit < keccak_lane_bits =>
  keccak_lane_bit (keccak_theta_d st x) bit =
  (keccak_lane_bit (keccak_theta_c st (x + 4)) bit <>
   keccak_lane_bit
     (keccak_theta_c st (x + 1))
     ((bit - 1) %% keccak_lane_bits)).
proof.
move=> bit_range.
rewrite /keccak_theta_d.
rewrite keccak_lane_xor_bitE; first by smt().
by rewrite keccak_lane_rotl_bitE.
qed.

lemma keccak_theta_d_bit_indexE st x bit :
  0 <= bit < keccak_lane_bits =>
  keccak_lane_bit (keccak_theta_d st x) bit =
  keccak_theta_d_bit_index_value st x bit.
proof.
move=> bit_range.
rewrite keccak_theta_d_bitE //.
rewrite /keccak_theta_d_bit_index_value.
rewrite keccak_theta_c_bit_indexE; first by smt().
rewrite keccak_theta_c_bit_indexE; first by rewrite /keccak_lane_bits; smt().
by [].
qed.

lemma keccak_theta_bitE st lane bit :
  0 <= lane < keccak_state_lanes =>
  0 <= bit < keccak_lane_bits =>
  keccak_lane_bit
    (nth keccak_lane_zero (keccak_theta st) lane)
    bit =
  (let x = lane %% 5 in
   let y = lane %/ 5 in
   keccak_lane_bit (keccak_state_lane st x y) bit <>
   keccak_lane_bit (keccak_theta_d st x) bit).
proof.
move=> lane_range bit_range.
rewrite /keccak_theta nth_mkseq; first by smt().
rewrite /= keccak_lane_xor_bitE; first by smt().
by [].
qed.

lemma keccak_theta_bit_indexE st lane bit :
  0 <= lane < keccak_state_lanes =>
  0 <= bit < keccak_lane_bits =>
  keccak_lane_bit
    (nth keccak_lane_zero (keccak_theta st) lane)
    bit =
  (let x = lane %% 5 in
   let y = lane %/ 5 in
   keccak_lane_bit (nth keccak_lane_zero st (keccak_lane_index x y)) bit <>
   keccak_lane_bit (keccak_theta_d st x) bit).
proof.
move=> lane_range bit_range.
by rewrite keccak_theta_bitE // keccak_state_lane_bitE.
qed.

lemma keccak_rho_pi_bitE st lane bit :
  0 <= lane < keccak_state_lanes =>
  0 <= bit < keccak_lane_bits =>
  keccak_lane_bit
    (nth keccak_lane_zero (keccak_rho_pi st) lane)
    bit =
  (let x = lane %% 5 in
   let y = lane %/ 5 in
   let sx = (x + 3 * y) %% 5 in
   let sy = x in
   keccak_lane_bit
     (keccak_state_lane st sx sy)
     ((bit - nth 0 keccak_rho_offsets (keccak_lane_index sx sy)) %%
      keccak_lane_bits)).
proof.
move=> lane_range bit_range.
rewrite /keccak_rho_pi nth_mkseq; first by smt().
rewrite /= keccak_lane_rotl_bitE; first by smt().
by [].
qed.

lemma keccak_rho_pi_bit_indexE st lane bit :
  0 <= lane < keccak_state_lanes =>
  0 <= bit < keccak_lane_bits =>
  keccak_lane_bit
    (nth keccak_lane_zero (keccak_rho_pi st) lane)
    bit =
  (let x = lane %% 5 in
   let y = lane %/ 5 in
   let sx = (x + 3 * y) %% 5 in
   let sy = x in
   keccak_lane_bit
     (nth keccak_lane_zero st (keccak_lane_index sx sy))
     ((bit - nth 0 keccak_rho_offsets (keccak_lane_index sx sy)) %%
      keccak_lane_bits)).
proof.
move=> lane_range bit_range.
by rewrite keccak_rho_pi_bitE // keccak_state_lane_bitE.
qed.

lemma keccak_chi_bitE st lane bit :
  0 <= lane < keccak_state_lanes =>
  0 <= bit < keccak_lane_bits =>
  keccak_lane_bit
    (nth keccak_lane_zero (keccak_chi st) lane)
    bit =
  (let x = lane %% 5 in
   let y = lane %/ 5 in
   keccak_lane_bit (keccak_state_lane st x y) bit <>
   ((if keccak_lane_bit (keccak_state_lane st (x + 1) y) bit
     then false else true) /\
    keccak_lane_bit (keccak_state_lane st (x + 2) y) bit)).
proof.
move=> lane_range bit_range.
rewrite /keccak_chi nth_mkseq; first by smt().
rewrite /= keccak_lane_xor_bitE; first by smt().
rewrite keccak_lane_and_bitE; first by smt().
rewrite keccak_lane_not_bitE; first by smt().
by [].
qed.

lemma keccak_chi_bit_indexE st lane bit :
  0 <= lane < keccak_state_lanes =>
  0 <= bit < keccak_lane_bits =>
  keccak_lane_bit
    (nth keccak_lane_zero (keccak_chi st) lane)
    bit =
  (let x = lane %% 5 in
   let y = lane %/ 5 in
   keccak_lane_bit (nth keccak_lane_zero st (keccak_lane_index x y)) bit <>
   ((if keccak_lane_bit
          (nth keccak_lane_zero st (keccak_lane_index (x + 1) y))
          bit
     then false else true) /\
    keccak_lane_bit
      (nth keccak_lane_zero st (keccak_lane_index (x + 2) y))
      bit)).
proof.
move=> lane_range bit_range.
by rewrite keccak_chi_bitE // !keccak_state_lane_bitE.
qed.

lemma keccak_iota_bitE st rc lane bit :
  0 <= lane < keccak_state_lanes =>
  0 <= bit < keccak_lane_bits =>
  keccak_lane_bit
    (nth keccak_lane_zero (keccak_iota st rc) lane)
    bit =
  if lane = 0
  then keccak_lane_bit (nth keccak_lane_zero st 0) bit <>
       keccak_lane_bit rc bit
  else keccak_lane_bit (nth keccak_lane_zero st lane) bit.
proof.
move=> lane_range bit_range.
rewrite /keccak_iota nth_mkseq; first by smt().
case (lane = 0) => lane0.
+ rewrite lane0 /= keccak_lane_xor_bitE; first by smt().
  by [].
by rewrite lane0.
qed.

lemma keccak_round_bitE st rc lane bit :
  0 <= lane < keccak_state_lanes =>
  0 <= bit < keccak_lane_bits =>
  keccak_lane_bit
    (nth keccak_lane_zero (keccak_round st rc) lane)
    bit =
  if lane = 0
  then
    keccak_lane_bit
      (nth keccak_lane_zero
        (keccak_chi (keccak_rho_pi (keccak_theta st)))
        0)
      bit <>
    keccak_lane_bit rc bit
  else
    keccak_lane_bit
      (nth keccak_lane_zero
        (keccak_chi (keccak_rho_pi (keccak_theta st)))
        lane)
      bit.
proof.
move=> lane_range bit_range.
rewrite /keccak_round.
by rewrite keccak_iota_bitE.
qed.

lemma keccak_bytes_of_lanes_size st :
  size (keccak_bytes_of_lanes st) = keccak_state_bytes.
proof. by rewrite /keccak_bytes_of_lanes size_mkseq. qed.

lemma keccak_bytes_of_lanes_byteE st i :
  0 <= i < keccak_state_bytes =>
  nth 0 (keccak_bytes_of_lanes st) i =
  keccak_lane_to_byte
    (nth keccak_lane_zero st (i %/ 8))
    (i %% 8).
proof.
move=> i_range.
by rewrite /keccak_bytes_of_lanes nth_mkseq.
qed.

lemma keccak_lane_to_byte_bitsE lane byte_index :
  keccak_lane_to_byte lane byte_index =
  (if keccak_lane_bit lane (8 * byte_index) then 2 ^ 0 else 0) +
  ((if keccak_lane_bit lane (8 * byte_index + 1) then 2 ^ 1 else 0) +
  ((if keccak_lane_bit lane (8 * byte_index + 2) then 2 ^ 2 else 0) +
  ((if keccak_lane_bit lane (8 * byte_index + 3) then 2 ^ 3 else 0) +
  ((if keccak_lane_bit lane (8 * byte_index + 4) then 2 ^ 4 else 0) +
  ((if keccak_lane_bit lane (8 * byte_index + 5) then 2 ^ 5 else 0) +
  ((if keccak_lane_bit lane (8 * byte_index + 6) then 2 ^ 6 else 0) +
   (if keccak_lane_bit lane (8 * byte_index + 7) then 2 ^ 7 else 0))))))).
proof.
rewrite /keccak_lane_to_byte /range /sumz /=.
rewrite (@iotaS 0 7) 1:/# /=
        (@iotaS 1 6) 1:/# /=
        (@iotaS 2 5) 1:/# /=
        (@iotaS 3 4) 1:/# /=
        (@iotaS 4 3) 1:/# /=
        (@iotaS 5 2) 1:/# /=
        (@iotaS 6 1) 1:/# /=
        (@iotaS 7 0) 1:/# /=
        iota0 1:/# /=.
by [].
qed.

lemma keccak_lane_to_byte_from_bitsE
  lane byte_index b0 b1 b2 b3 b4 b5 b6 b7 :
  keccak_lane_bit lane (8 * byte_index) = b0 =>
  keccak_lane_bit lane (8 * byte_index + 1) = b1 =>
  keccak_lane_bit lane (8 * byte_index + 2) = b2 =>
  keccak_lane_bit lane (8 * byte_index + 3) = b3 =>
  keccak_lane_bit lane (8 * byte_index + 4) = b4 =>
  keccak_lane_bit lane (8 * byte_index + 5) = b5 =>
  keccak_lane_bit lane (8 * byte_index + 6) = b6 =>
  keccak_lane_bit lane (8 * byte_index + 7) = b7 =>
  keccak_lane_to_byte lane byte_index =
  (if b0 then 1 else 0) +
  ((if b1 then 2 else 0) +
  ((if b2 then 4 else 0) +
  ((if b3 then 8 else 0) +
  ((if b4 then 16 else 0) +
  ((if b5 then 32 else 0) +
  ((if b6 then 64 else 0) +
   (if b7 then 128 else 0))))))).
proof.
move=> h0 h1 h2 h3 h4 h5 h6 h7.
rewrite keccak_lane_to_byte_bitsE h0 h1 h2 h3 h4 h5 h6 h7 /=.
by rewrite keccak_pow2_0E keccak_pow2_1E keccak_pow2_2E keccak_pow2_3E
           keccak_pow2_4E keccak_pow2_5E keccak_pow2_6E keccak_pow2_7E.
qed.

lemma keccak_lane_to_byte_70E lane byte_index :
  keccak_lane_bit lane (8 * byte_index) = false =>
  keccak_lane_bit lane (8 * byte_index + 1) = true =>
  keccak_lane_bit lane (8 * byte_index + 2) = true =>
  keccak_lane_bit lane (8 * byte_index + 3) = false =>
  keccak_lane_bit lane (8 * byte_index + 4) = false =>
  keccak_lane_bit lane (8 * byte_index + 5) = false =>
  keccak_lane_bit lane (8 * byte_index + 6) = true =>
  keccak_lane_bit lane (8 * byte_index + 7) = false =>
  keccak_lane_to_byte lane byte_index = 70.
proof.
move=> b0 b1 b2 b3 b4 b5 b6 b7.
rewrite keccak_lane_to_byte_bitsE b0 b1 b2 b3 b4 b5 b6 b7 /=.
rewrite keccak_pow2_1E keccak_pow2_2E keccak_pow2_6E.
by smt().
qed.

lemma keccak_f1600_bytes_size st :
  size (keccak_f1600_bytes st) = keccak_state_bytes.
proof. by rewrite /keccak_f1600_bytes keccak_bytes_of_lanes_size. qed.

end HAETAE_Keccak1600.
