require import AllCore IntDiv List Ring BitEncoding.

from Jasmin require import JModel_x86.

import SLH64 BitReverse.

require import KeygenMode2ParentTarget.

theory KeygenM23FFTTableCertificate.

op brv8_bit (n : int) : int =
  b2i (! 2 %| n).

op brv8_half (n : int) : int =
  n %/ 2.

op brv8_eval (n : int) : int =
    128 * brv8_bit n
  +  64 * brv8_bit (brv8_half n)
  +  32 * brv8_bit (brv8_half (brv8_half n))
  +  16 * brv8_bit (brv8_half (brv8_half (brv8_half n)))
  +   8 * brv8_bit
            (brv8_half (brv8_half (brv8_half (brv8_half n))))
  +   4 * brv8_bit
            (brv8_half
              (brv8_half (brv8_half (brv8_half (brv8_half n)))))
  +   2 * brv8_bit
            (brv8_half
              (brv8_half
                (brv8_half
                  (brv8_half (brv8_half (brv8_half n))))))
  +       brv8_bit
            (brv8_half
              (brv8_half
                (brv8_half
                  (brv8_half
                    (brv8_half (brv8_half (brv8_half n))))))).

lemma bsrev8_eval (n : int) :
  bsrev 8 n = brv8_eval n.
proof.
rewrite /brv8_eval /brv8_bit /brv8_half.
do 8!(rewrite bsrev_cons 1:// /=).
rewrite bsrev_neg 1://.
ring.
qed.

op brv8_pair_ok (p : W16.t * int) : bool =
  W16.to_uint p.`1 = bsrev 8 p.`2.

lemma all256_zip_brv8_nth (s : W16.t list) (i : int) :
  size s = 256 =>
  all brv8_pair_ok (zip s (range 0 256)) =>
  0 <= i < 256 =>
  W16.to_uint (nth W16.zero s i) = bsrev 8 i.
proof.
move=> hs hall hi.
have hsrange : size s = size (range 0 256).
+ by rewrite hs size_range /=.
have halln :
  forall j,
    0 <= j < size (zip s (range 0 256)) =>
    brv8_pair_ok
      (nth (W16.zero, 0) (zip s (range 0 256)) j).
+ rewrite
    (all_nthP brv8_pair_ok
      (zip s (range 0 256)) (W16.zero, 0)).
  exact hall.
have h :
  brv8_pair_ok
    (nth (W16.zero, 0) (zip s (range 0 256)) i).
+ apply halln.
  by rewrite size_zip hs size_range /=.
rewrite
  (nth_zip W16.zero 0 s (range 0 256) i hsrange) in h.
rewrite /brv8_pair_ok nth_range 1:/# /= in h.
exact h.
qed.

lemma jfft_brv8_exact (i : int) :
  0 <= i < 256 =>
  W16.to_uint
    (BArray512.get16 KeygenMode2ParentTarget.jfft_brv8 i) =
  bsrev 8 i.
proof.
move=> hi.
rewrite /KeygenMode2ParentTarget.jfft_brv8
        BArray512.get16_of_list16 1://.
apply (all256_zip_brv8_nth _ i).
+ trivial.
+ do 256!(rewrite range_ltn 1:// /=).
  rewrite range_geq 1:// /=.
  rewrite /brv8_pair_ok.
  rewrite !bsrev8_eval
          /brv8_eval /brv8_bit /brv8_half /b2i !dvdzE /=.
  trivial.
+ exact hi.
qed.

lemma all512_nth_signed_bound (s : W32.t list) (i : int) :
  size s = 512 =>
  all (fun (w : W32.t) => -65536 <= W32.to_sint w <= 65536) s =>
  0 <= i < 512 =>
  -65536 <= W32.to_sint (nth W32.zero s i) <= 65536.
proof.
move=> hs hall hi.
have halln :
  forall j,
    0 <= j < size s =>
    -65536 <= W32.to_sint (nth W32.zero s j) <= 65536.
+ rewrite
    (all_nthP
      (fun (w : W32.t) => -65536 <= W32.to_sint w <= 65536)
      s W32.zero).
  exact hall.
apply halln.
by rewrite hs.
qed.

lemma jfft_roots_signed_bound (i : int) :
  0 <= i < 512 =>
  -65536 <=
    W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots i)
  <= 65536.
proof.
move=> hi.
rewrite /KeygenMode2ParentTarget.jfft_roots
        BArray2048.get32_of_list32 1://.
apply (all512_nth_signed_bound _ i).
+ trivial.
+ rewrite /= !W32.of_sintK /W32.smod /=; trivial.
+ exact hi.
qed.

end KeygenM23FFTTableCertificate.
