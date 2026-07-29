require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23RootTableRounding
  KeygenMode2ParentTarget.

import
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23RootTableRounding.

theory KeygenM23RootTableTargetBridge.

lemma root_pair_0 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 0),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 1)) =
  nth (0, 0) root_q16_pairs 0.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_1 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 2),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 3)) =
  nth (0, 0) root_q16_pairs 1.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_2 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 4),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 5)) =
  nth (0, 0) root_q16_pairs 2.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_3 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 6),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 7)) =
  nth (0, 0) root_q16_pairs 3.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_4 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 8),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 9)) =
  nth (0, 0) root_q16_pairs 4.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_5 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 10),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 11)) =
  nth (0, 0) root_q16_pairs 5.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_6 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 12),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 13)) =
  nth (0, 0) root_q16_pairs 6.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_7 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 14),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 15)) =
  nth (0, 0) root_q16_pairs 7.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_8 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 16),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 17)) =
  nth (0, 0) root_q16_pairs 8.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_9 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 18),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 19)) =
  nth (0, 0) root_q16_pairs 9.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_10 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 20),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 21)) =
  nth (0, 0) root_q16_pairs 10.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_11 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 22),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 23)) =
  nth (0, 0) root_q16_pairs 11.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_12 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 24),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 25)) =
  nth (0, 0) root_q16_pairs 12.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_13 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 26),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 27)) =
  nth (0, 0) root_q16_pairs 13.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_14 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 28),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 29)) =
  nth (0, 0) root_q16_pairs 14.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_15 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 30),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 31)) =
  nth (0, 0) root_q16_pairs 15.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_16 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 32),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 33)) =
  nth (0, 0) root_q16_pairs 16.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_17 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 34),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 35)) =
  nth (0, 0) root_q16_pairs 17.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_18 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 36),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 37)) =
  nth (0, 0) root_q16_pairs 18.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_19 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 38),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 39)) =
  nth (0, 0) root_q16_pairs 19.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_20 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 40),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 41)) =
  nth (0, 0) root_q16_pairs 20.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_21 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 42),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 43)) =
  nth (0, 0) root_q16_pairs 21.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_22 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 44),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 45)) =
  nth (0, 0) root_q16_pairs 22.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_23 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 46),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 47)) =
  nth (0, 0) root_q16_pairs 23.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_24 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 48),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 49)) =
  nth (0, 0) root_q16_pairs 24.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_25 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 50),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 51)) =
  nth (0, 0) root_q16_pairs 25.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_26 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 52),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 53)) =
  nth (0, 0) root_q16_pairs 26.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_27 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 54),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 55)) =
  nth (0, 0) root_q16_pairs 27.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_28 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 56),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 57)) =
  nth (0, 0) root_q16_pairs 28.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_29 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 58),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 59)) =
  nth (0, 0) root_q16_pairs 29.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_30 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 60),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 61)) =
  nth (0, 0) root_q16_pairs 30.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_31 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 62),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 63)) =
  nth (0, 0) root_q16_pairs 31.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_32 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 64),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 65)) =
  nth (0, 0) root_q16_pairs 32.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_33 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 66),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 67)) =
  nth (0, 0) root_q16_pairs 33.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_34 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 68),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 69)) =
  nth (0, 0) root_q16_pairs 34.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_35 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 70),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 71)) =
  nth (0, 0) root_q16_pairs 35.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_36 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 72),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 73)) =
  nth (0, 0) root_q16_pairs 36.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_37 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 74),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 75)) =
  nth (0, 0) root_q16_pairs 37.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_38 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 76),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 77)) =
  nth (0, 0) root_q16_pairs 38.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_39 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 78),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 79)) =
  nth (0, 0) root_q16_pairs 39.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_40 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 80),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 81)) =
  nth (0, 0) root_q16_pairs 40.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_41 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 82),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 83)) =
  nth (0, 0) root_q16_pairs 41.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_42 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 84),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 85)) =
  nth (0, 0) root_q16_pairs 42.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_43 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 86),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 87)) =
  nth (0, 0) root_q16_pairs 43.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_44 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 88),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 89)) =
  nth (0, 0) root_q16_pairs 44.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_45 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 90),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 91)) =
  nth (0, 0) root_q16_pairs 45.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_46 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 92),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 93)) =
  nth (0, 0) root_q16_pairs 46.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_47 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 94),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 95)) =
  nth (0, 0) root_q16_pairs 47.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_48 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 96),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 97)) =
  nth (0, 0) root_q16_pairs 48.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_49 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 98),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 99)) =
  nth (0, 0) root_q16_pairs 49.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_50 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 100),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 101)) =
  nth (0, 0) root_q16_pairs 50.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_51 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 102),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 103)) =
  nth (0, 0) root_q16_pairs 51.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_52 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 104),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 105)) =
  nth (0, 0) root_q16_pairs 52.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_53 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 106),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 107)) =
  nth (0, 0) root_q16_pairs 53.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_54 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 108),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 109)) =
  nth (0, 0) root_q16_pairs 54.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_55 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 110),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 111)) =
  nth (0, 0) root_q16_pairs 55.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_56 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 112),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 113)) =
  nth (0, 0) root_q16_pairs 56.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_57 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 114),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 115)) =
  nth (0, 0) root_q16_pairs 57.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_58 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 116),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 117)) =
  nth (0, 0) root_q16_pairs 58.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_59 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 118),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 119)) =
  nth (0, 0) root_q16_pairs 59.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_60 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 120),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 121)) =
  nth (0, 0) root_q16_pairs 60.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_61 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 122),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 123)) =
  nth (0, 0) root_q16_pairs 61.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_62 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 124),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 125)) =
  nth (0, 0) root_q16_pairs 62.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_63 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 126),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 127)) =
  nth (0, 0) root_q16_pairs 63.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_64 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 128),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 129)) =
  nth (0, 0) root_q16_pairs 64.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_65 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 130),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 131)) =
  nth (0, 0) root_q16_pairs 65.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_66 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 132),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 133)) =
  nth (0, 0) root_q16_pairs 66.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_67 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 134),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 135)) =
  nth (0, 0) root_q16_pairs 67.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_68 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 136),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 137)) =
  nth (0, 0) root_q16_pairs 68.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_69 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 138),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 139)) =
  nth (0, 0) root_q16_pairs 69.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_70 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 140),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 141)) =
  nth (0, 0) root_q16_pairs 70.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_71 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 142),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 143)) =
  nth (0, 0) root_q16_pairs 71.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_72 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 144),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 145)) =
  nth (0, 0) root_q16_pairs 72.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_73 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 146),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 147)) =
  nth (0, 0) root_q16_pairs 73.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_74 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 148),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 149)) =
  nth (0, 0) root_q16_pairs 74.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_75 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 150),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 151)) =
  nth (0, 0) root_q16_pairs 75.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_76 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 152),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 153)) =
  nth (0, 0) root_q16_pairs 76.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_77 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 154),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 155)) =
  nth (0, 0) root_q16_pairs 77.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_78 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 156),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 157)) =
  nth (0, 0) root_q16_pairs 78.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_79 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 158),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 159)) =
  nth (0, 0) root_q16_pairs 79.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_80 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 160),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 161)) =
  nth (0, 0) root_q16_pairs 80.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_81 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 162),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 163)) =
  nth (0, 0) root_q16_pairs 81.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_82 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 164),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 165)) =
  nth (0, 0) root_q16_pairs 82.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_83 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 166),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 167)) =
  nth (0, 0) root_q16_pairs 83.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_84 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 168),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 169)) =
  nth (0, 0) root_q16_pairs 84.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_85 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 170),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 171)) =
  nth (0, 0) root_q16_pairs 85.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_86 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 172),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 173)) =
  nth (0, 0) root_q16_pairs 86.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_87 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 174),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 175)) =
  nth (0, 0) root_q16_pairs 87.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_88 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 176),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 177)) =
  nth (0, 0) root_q16_pairs 88.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_89 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 178),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 179)) =
  nth (0, 0) root_q16_pairs 89.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_90 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 180),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 181)) =
  nth (0, 0) root_q16_pairs 90.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_91 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 182),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 183)) =
  nth (0, 0) root_q16_pairs 91.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_92 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 184),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 185)) =
  nth (0, 0) root_q16_pairs 92.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_93 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 186),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 187)) =
  nth (0, 0) root_q16_pairs 93.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_94 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 188),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 189)) =
  nth (0, 0) root_q16_pairs 94.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_95 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 190),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 191)) =
  nth (0, 0) root_q16_pairs 95.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_96 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 192),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 193)) =
  nth (0, 0) root_q16_pairs 96.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_97 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 194),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 195)) =
  nth (0, 0) root_q16_pairs 97.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_98 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 196),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 197)) =
  nth (0, 0) root_q16_pairs 98.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_99 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 198),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 199)) =
  nth (0, 0) root_q16_pairs 99.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_100 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 200),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 201)) =
  nth (0, 0) root_q16_pairs 100.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_101 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 202),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 203)) =
  nth (0, 0) root_q16_pairs 101.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_102 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 204),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 205)) =
  nth (0, 0) root_q16_pairs 102.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_103 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 206),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 207)) =
  nth (0, 0) root_q16_pairs 103.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_104 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 208),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 209)) =
  nth (0, 0) root_q16_pairs 104.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_105 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 210),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 211)) =
  nth (0, 0) root_q16_pairs 105.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_106 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 212),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 213)) =
  nth (0, 0) root_q16_pairs 106.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_107 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 214),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 215)) =
  nth (0, 0) root_q16_pairs 107.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_108 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 216),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 217)) =
  nth (0, 0) root_q16_pairs 108.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_109 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 218),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 219)) =
  nth (0, 0) root_q16_pairs 109.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_110 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 220),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 221)) =
  nth (0, 0) root_q16_pairs 110.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_111 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 222),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 223)) =
  nth (0, 0) root_q16_pairs 111.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_112 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 224),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 225)) =
  nth (0, 0) root_q16_pairs 112.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_113 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 226),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 227)) =
  nth (0, 0) root_q16_pairs 113.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_114 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 228),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 229)) =
  nth (0, 0) root_q16_pairs 114.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_115 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 230),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 231)) =
  nth (0, 0) root_q16_pairs 115.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_116 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 232),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 233)) =
  nth (0, 0) root_q16_pairs 116.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_117 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 234),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 235)) =
  nth (0, 0) root_q16_pairs 117.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_118 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 236),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 237)) =
  nth (0, 0) root_q16_pairs 118.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_119 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 238),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 239)) =
  nth (0, 0) root_q16_pairs 119.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_120 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 240),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 241)) =
  nth (0, 0) root_q16_pairs 120.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_121 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 242),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 243)) =
  nth (0, 0) root_q16_pairs 121.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_122 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 244),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 245)) =
  nth (0, 0) root_q16_pairs 122.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_123 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 246),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 247)) =
  nth (0, 0) root_q16_pairs 123.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_124 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 248),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 249)) =
  nth (0, 0) root_q16_pairs 124.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_125 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 250),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 251)) =
  nth (0, 0) root_q16_pairs 125.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_126 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 252),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 253)) =
  nth (0, 0) root_q16_pairs 126.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_127 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 254),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 255)) =
  nth (0, 0) root_q16_pairs 127.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_128 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 256),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 257)) =
  nth (0, 0) root_q16_pairs 128.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_129 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 258),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 259)) =
  nth (0, 0) root_q16_pairs 129.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_130 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 260),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 261)) =
  nth (0, 0) root_q16_pairs 130.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_131 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 262),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 263)) =
  nth (0, 0) root_q16_pairs 131.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_132 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 264),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 265)) =
  nth (0, 0) root_q16_pairs 132.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_133 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 266),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 267)) =
  nth (0, 0) root_q16_pairs 133.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_134 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 268),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 269)) =
  nth (0, 0) root_q16_pairs 134.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_135 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 270),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 271)) =
  nth (0, 0) root_q16_pairs 135.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_136 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 272),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 273)) =
  nth (0, 0) root_q16_pairs 136.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_137 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 274),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 275)) =
  nth (0, 0) root_q16_pairs 137.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_138 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 276),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 277)) =
  nth (0, 0) root_q16_pairs 138.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_139 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 278),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 279)) =
  nth (0, 0) root_q16_pairs 139.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_140 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 280),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 281)) =
  nth (0, 0) root_q16_pairs 140.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_141 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 282),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 283)) =
  nth (0, 0) root_q16_pairs 141.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_142 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 284),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 285)) =
  nth (0, 0) root_q16_pairs 142.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_143 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 286),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 287)) =
  nth (0, 0) root_q16_pairs 143.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_144 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 288),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 289)) =
  nth (0, 0) root_q16_pairs 144.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_145 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 290),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 291)) =
  nth (0, 0) root_q16_pairs 145.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_146 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 292),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 293)) =
  nth (0, 0) root_q16_pairs 146.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_147 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 294),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 295)) =
  nth (0, 0) root_q16_pairs 147.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_148 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 296),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 297)) =
  nth (0, 0) root_q16_pairs 148.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_149 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 298),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 299)) =
  nth (0, 0) root_q16_pairs 149.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_150 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 300),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 301)) =
  nth (0, 0) root_q16_pairs 150.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_151 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 302),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 303)) =
  nth (0, 0) root_q16_pairs 151.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_152 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 304),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 305)) =
  nth (0, 0) root_q16_pairs 152.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_153 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 306),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 307)) =
  nth (0, 0) root_q16_pairs 153.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_154 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 308),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 309)) =
  nth (0, 0) root_q16_pairs 154.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_155 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 310),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 311)) =
  nth (0, 0) root_q16_pairs 155.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_156 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 312),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 313)) =
  nth (0, 0) root_q16_pairs 156.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_157 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 314),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 315)) =
  nth (0, 0) root_q16_pairs 157.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_158 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 316),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 317)) =
  nth (0, 0) root_q16_pairs 158.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_159 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 318),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 319)) =
  nth (0, 0) root_q16_pairs 159.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_160 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 320),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 321)) =
  nth (0, 0) root_q16_pairs 160.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_161 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 322),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 323)) =
  nth (0, 0) root_q16_pairs 161.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_162 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 324),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 325)) =
  nth (0, 0) root_q16_pairs 162.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_163 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 326),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 327)) =
  nth (0, 0) root_q16_pairs 163.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_164 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 328),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 329)) =
  nth (0, 0) root_q16_pairs 164.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_165 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 330),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 331)) =
  nth (0, 0) root_q16_pairs 165.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_166 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 332),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 333)) =
  nth (0, 0) root_q16_pairs 166.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_167 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 334),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 335)) =
  nth (0, 0) root_q16_pairs 167.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_168 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 336),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 337)) =
  nth (0, 0) root_q16_pairs 168.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_169 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 338),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 339)) =
  nth (0, 0) root_q16_pairs 169.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_170 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 340),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 341)) =
  nth (0, 0) root_q16_pairs 170.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_171 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 342),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 343)) =
  nth (0, 0) root_q16_pairs 171.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_172 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 344),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 345)) =
  nth (0, 0) root_q16_pairs 172.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_173 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 346),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 347)) =
  nth (0, 0) root_q16_pairs 173.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_174 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 348),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 349)) =
  nth (0, 0) root_q16_pairs 174.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_175 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 350),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 351)) =
  nth (0, 0) root_q16_pairs 175.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_176 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 352),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 353)) =
  nth (0, 0) root_q16_pairs 176.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_177 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 354),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 355)) =
  nth (0, 0) root_q16_pairs 177.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_178 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 356),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 357)) =
  nth (0, 0) root_q16_pairs 178.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_179 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 358),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 359)) =
  nth (0, 0) root_q16_pairs 179.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_180 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 360),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 361)) =
  nth (0, 0) root_q16_pairs 180.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_181 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 362),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 363)) =
  nth (0, 0) root_q16_pairs 181.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_182 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 364),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 365)) =
  nth (0, 0) root_q16_pairs 182.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_183 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 366),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 367)) =
  nth (0, 0) root_q16_pairs 183.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_184 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 368),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 369)) =
  nth (0, 0) root_q16_pairs 184.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_185 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 370),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 371)) =
  nth (0, 0) root_q16_pairs 185.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_186 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 372),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 373)) =
  nth (0, 0) root_q16_pairs 186.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_187 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 374),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 375)) =
  nth (0, 0) root_q16_pairs 187.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_188 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 376),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 377)) =
  nth (0, 0) root_q16_pairs 188.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_189 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 378),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 379)) =
  nth (0, 0) root_q16_pairs 189.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_190 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 380),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 381)) =
  nth (0, 0) root_q16_pairs 190.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_191 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 382),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 383)) =
  nth (0, 0) root_q16_pairs 191.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_192 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 384),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 385)) =
  nth (0, 0) root_q16_pairs 192.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_193 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 386),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 387)) =
  nth (0, 0) root_q16_pairs 193.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_194 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 388),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 389)) =
  nth (0, 0) root_q16_pairs 194.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_195 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 390),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 391)) =
  nth (0, 0) root_q16_pairs 195.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_196 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 392),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 393)) =
  nth (0, 0) root_q16_pairs 196.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_197 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 394),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 395)) =
  nth (0, 0) root_q16_pairs 197.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_198 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 396),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 397)) =
  nth (0, 0) root_q16_pairs 198.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_199 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 398),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 399)) =
  nth (0, 0) root_q16_pairs 199.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_200 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 400),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 401)) =
  nth (0, 0) root_q16_pairs 200.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_201 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 402),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 403)) =
  nth (0, 0) root_q16_pairs 201.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_202 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 404),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 405)) =
  nth (0, 0) root_q16_pairs 202.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_203 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 406),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 407)) =
  nth (0, 0) root_q16_pairs 203.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_204 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 408),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 409)) =
  nth (0, 0) root_q16_pairs 204.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_205 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 410),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 411)) =
  nth (0, 0) root_q16_pairs 205.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_206 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 412),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 413)) =
  nth (0, 0) root_q16_pairs 206.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_207 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 414),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 415)) =
  nth (0, 0) root_q16_pairs 207.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_208 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 416),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 417)) =
  nth (0, 0) root_q16_pairs 208.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_209 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 418),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 419)) =
  nth (0, 0) root_q16_pairs 209.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_210 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 420),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 421)) =
  nth (0, 0) root_q16_pairs 210.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_211 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 422),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 423)) =
  nth (0, 0) root_q16_pairs 211.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_212 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 424),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 425)) =
  nth (0, 0) root_q16_pairs 212.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_213 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 426),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 427)) =
  nth (0, 0) root_q16_pairs 213.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_214 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 428),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 429)) =
  nth (0, 0) root_q16_pairs 214.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_215 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 430),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 431)) =
  nth (0, 0) root_q16_pairs 215.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_216 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 432),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 433)) =
  nth (0, 0) root_q16_pairs 216.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_217 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 434),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 435)) =
  nth (0, 0) root_q16_pairs 217.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_218 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 436),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 437)) =
  nth (0, 0) root_q16_pairs 218.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_219 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 438),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 439)) =
  nth (0, 0) root_q16_pairs 219.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_220 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 440),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 441)) =
  nth (0, 0) root_q16_pairs 220.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_221 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 442),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 443)) =
  nth (0, 0) root_q16_pairs 221.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_222 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 444),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 445)) =
  nth (0, 0) root_q16_pairs 222.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_223 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 446),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 447)) =
  nth (0, 0) root_q16_pairs 223.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_224 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 448),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 449)) =
  nth (0, 0) root_q16_pairs 224.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_225 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 450),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 451)) =
  nth (0, 0) root_q16_pairs 225.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_226 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 452),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 453)) =
  nth (0, 0) root_q16_pairs 226.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_227 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 454),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 455)) =
  nth (0, 0) root_q16_pairs 227.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_228 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 456),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 457)) =
  nth (0, 0) root_q16_pairs 228.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_229 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 458),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 459)) =
  nth (0, 0) root_q16_pairs 229.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_230 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 460),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 461)) =
  nth (0, 0) root_q16_pairs 230.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_231 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 462),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 463)) =
  nth (0, 0) root_q16_pairs 231.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_232 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 464),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 465)) =
  nth (0, 0) root_q16_pairs 232.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_233 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 466),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 467)) =
  nth (0, 0) root_q16_pairs 233.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_234 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 468),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 469)) =
  nth (0, 0) root_q16_pairs 234.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_235 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 470),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 471)) =
  nth (0, 0) root_q16_pairs 235.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_236 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 472),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 473)) =
  nth (0, 0) root_q16_pairs 236.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_237 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 474),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 475)) =
  nth (0, 0) root_q16_pairs 237.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_238 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 476),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 477)) =
  nth (0, 0) root_q16_pairs 238.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_239 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 478),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 479)) =
  nth (0, 0) root_q16_pairs 239.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_240 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 480),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 481)) =
  nth (0, 0) root_q16_pairs 240.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_241 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 482),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 483)) =
  nth (0, 0) root_q16_pairs 241.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_242 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 484),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 485)) =
  nth (0, 0) root_q16_pairs 242.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_243 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 486),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 487)) =
  nth (0, 0) root_q16_pairs 243.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_244 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 488),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 489)) =
  nth (0, 0) root_q16_pairs 244.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_245 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 490),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 491)) =
  nth (0, 0) root_q16_pairs 245.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_246 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 492),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 493)) =
  nth (0, 0) root_q16_pairs 246.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_247 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 494),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 495)) =
  nth (0, 0) root_q16_pairs 247.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_248 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 496),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 497)) =
  nth (0, 0) root_q16_pairs 248.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_249 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 498),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 499)) =
  nth (0, 0) root_q16_pairs 249.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_250 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 500),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 501)) =
  nth (0, 0) root_q16_pairs 250.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_251 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 502),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 503)) =
  nth (0, 0) root_q16_pairs 251.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_252 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 504),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 505)) =
  nth (0, 0) root_q16_pairs 252.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_253 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 506),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 507)) =
  nth (0, 0) root_q16_pairs 253.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_254 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 508),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 509)) =
  nth (0, 0) root_q16_pairs 254.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_255 :
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 510),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots 511)) =
  nth (0, 0) root_q16_pairs 255.
proof.
rewrite /KeygenMode2ParentTarget.jfft_roots
        !BArray2048.get32_of_list32 1:// 1://
        /root_q16_pairs.
rewrite /= !W32.of_sintK /W32.smod /=.
trivial.
qed.

lemma root_pair_chunk_0 (j : int) :
  0 <= j < 16 =>
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j)),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j + 1))) =
  nth (0, 0) root_q16_pairs j.
proof.
move=> hj.
case (j = 0) => hj0.
+ rewrite hj0 /=; exact root_pair_0.
case (j = 1) => hj1.
+ rewrite hj1 /=; exact root_pair_1.
case (j = 2) => hj2.
+ rewrite hj2 /=; exact root_pair_2.
case (j = 3) => hj3.
+ rewrite hj3 /=; exact root_pair_3.
case (j = 4) => hj4.
+ rewrite hj4 /=; exact root_pair_4.
case (j = 5) => hj5.
+ rewrite hj5 /=; exact root_pair_5.
case (j = 6) => hj6.
+ rewrite hj6 /=; exact root_pair_6.
case (j = 7) => hj7.
+ rewrite hj7 /=; exact root_pair_7.
case (j = 8) => hj8.
+ rewrite hj8 /=; exact root_pair_8.
case (j = 9) => hj9.
+ rewrite hj9 /=; exact root_pair_9.
case (j = 10) => hj10.
+ rewrite hj10 /=; exact root_pair_10.
case (j = 11) => hj11.
+ rewrite hj11 /=; exact root_pair_11.
case (j = 12) => hj12.
+ rewrite hj12 /=; exact root_pair_12.
case (j = 13) => hj13.
+ rewrite hj13 /=; exact root_pair_13.
case (j = 14) => hj14.
+ rewrite hj14 /=; exact root_pair_14.
have -> : j = 15 by smt().
exact root_pair_15.
qed.

lemma root_pair_chunk_1 (j : int) :
  16 <= j < 32 =>
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j)),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j + 1))) =
  nth (0, 0) root_q16_pairs j.
proof.
move=> hj.
case (j = 16) => hj16.
+ rewrite hj16 /=; exact root_pair_16.
case (j = 17) => hj17.
+ rewrite hj17 /=; exact root_pair_17.
case (j = 18) => hj18.
+ rewrite hj18 /=; exact root_pair_18.
case (j = 19) => hj19.
+ rewrite hj19 /=; exact root_pair_19.
case (j = 20) => hj20.
+ rewrite hj20 /=; exact root_pair_20.
case (j = 21) => hj21.
+ rewrite hj21 /=; exact root_pair_21.
case (j = 22) => hj22.
+ rewrite hj22 /=; exact root_pair_22.
case (j = 23) => hj23.
+ rewrite hj23 /=; exact root_pair_23.
case (j = 24) => hj24.
+ rewrite hj24 /=; exact root_pair_24.
case (j = 25) => hj25.
+ rewrite hj25 /=; exact root_pair_25.
case (j = 26) => hj26.
+ rewrite hj26 /=; exact root_pair_26.
case (j = 27) => hj27.
+ rewrite hj27 /=; exact root_pair_27.
case (j = 28) => hj28.
+ rewrite hj28 /=; exact root_pair_28.
case (j = 29) => hj29.
+ rewrite hj29 /=; exact root_pair_29.
case (j = 30) => hj30.
+ rewrite hj30 /=; exact root_pair_30.
have -> : j = 31 by smt().
exact root_pair_31.
qed.

lemma root_pair_chunk_2 (j : int) :
  32 <= j < 48 =>
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j)),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j + 1))) =
  nth (0, 0) root_q16_pairs j.
proof.
move=> hj.
case (j = 32) => hj32.
+ rewrite hj32 /=; exact root_pair_32.
case (j = 33) => hj33.
+ rewrite hj33 /=; exact root_pair_33.
case (j = 34) => hj34.
+ rewrite hj34 /=; exact root_pair_34.
case (j = 35) => hj35.
+ rewrite hj35 /=; exact root_pair_35.
case (j = 36) => hj36.
+ rewrite hj36 /=; exact root_pair_36.
case (j = 37) => hj37.
+ rewrite hj37 /=; exact root_pair_37.
case (j = 38) => hj38.
+ rewrite hj38 /=; exact root_pair_38.
case (j = 39) => hj39.
+ rewrite hj39 /=; exact root_pair_39.
case (j = 40) => hj40.
+ rewrite hj40 /=; exact root_pair_40.
case (j = 41) => hj41.
+ rewrite hj41 /=; exact root_pair_41.
case (j = 42) => hj42.
+ rewrite hj42 /=; exact root_pair_42.
case (j = 43) => hj43.
+ rewrite hj43 /=; exact root_pair_43.
case (j = 44) => hj44.
+ rewrite hj44 /=; exact root_pair_44.
case (j = 45) => hj45.
+ rewrite hj45 /=; exact root_pair_45.
case (j = 46) => hj46.
+ rewrite hj46 /=; exact root_pair_46.
have -> : j = 47 by smt().
exact root_pair_47.
qed.

lemma root_pair_chunk_3 (j : int) :
  48 <= j < 64 =>
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j)),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j + 1))) =
  nth (0, 0) root_q16_pairs j.
proof.
move=> hj.
case (j = 48) => hj48.
+ rewrite hj48 /=; exact root_pair_48.
case (j = 49) => hj49.
+ rewrite hj49 /=; exact root_pair_49.
case (j = 50) => hj50.
+ rewrite hj50 /=; exact root_pair_50.
case (j = 51) => hj51.
+ rewrite hj51 /=; exact root_pair_51.
case (j = 52) => hj52.
+ rewrite hj52 /=; exact root_pair_52.
case (j = 53) => hj53.
+ rewrite hj53 /=; exact root_pair_53.
case (j = 54) => hj54.
+ rewrite hj54 /=; exact root_pair_54.
case (j = 55) => hj55.
+ rewrite hj55 /=; exact root_pair_55.
case (j = 56) => hj56.
+ rewrite hj56 /=; exact root_pair_56.
case (j = 57) => hj57.
+ rewrite hj57 /=; exact root_pair_57.
case (j = 58) => hj58.
+ rewrite hj58 /=; exact root_pair_58.
case (j = 59) => hj59.
+ rewrite hj59 /=; exact root_pair_59.
case (j = 60) => hj60.
+ rewrite hj60 /=; exact root_pair_60.
case (j = 61) => hj61.
+ rewrite hj61 /=; exact root_pair_61.
case (j = 62) => hj62.
+ rewrite hj62 /=; exact root_pair_62.
have -> : j = 63 by smt().
exact root_pair_63.
qed.

lemma root_pair_chunk_4 (j : int) :
  64 <= j < 80 =>
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j)),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j + 1))) =
  nth (0, 0) root_q16_pairs j.
proof.
move=> hj.
case (j = 64) => hj64.
+ rewrite hj64 /=; exact root_pair_64.
case (j = 65) => hj65.
+ rewrite hj65 /=; exact root_pair_65.
case (j = 66) => hj66.
+ rewrite hj66 /=; exact root_pair_66.
case (j = 67) => hj67.
+ rewrite hj67 /=; exact root_pair_67.
case (j = 68) => hj68.
+ rewrite hj68 /=; exact root_pair_68.
case (j = 69) => hj69.
+ rewrite hj69 /=; exact root_pair_69.
case (j = 70) => hj70.
+ rewrite hj70 /=; exact root_pair_70.
case (j = 71) => hj71.
+ rewrite hj71 /=; exact root_pair_71.
case (j = 72) => hj72.
+ rewrite hj72 /=; exact root_pair_72.
case (j = 73) => hj73.
+ rewrite hj73 /=; exact root_pair_73.
case (j = 74) => hj74.
+ rewrite hj74 /=; exact root_pair_74.
case (j = 75) => hj75.
+ rewrite hj75 /=; exact root_pair_75.
case (j = 76) => hj76.
+ rewrite hj76 /=; exact root_pair_76.
case (j = 77) => hj77.
+ rewrite hj77 /=; exact root_pair_77.
case (j = 78) => hj78.
+ rewrite hj78 /=; exact root_pair_78.
have -> : j = 79 by smt().
exact root_pair_79.
qed.

lemma root_pair_chunk_5 (j : int) :
  80 <= j < 96 =>
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j)),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j + 1))) =
  nth (0, 0) root_q16_pairs j.
proof.
move=> hj.
case (j = 80) => hj80.
+ rewrite hj80 /=; exact root_pair_80.
case (j = 81) => hj81.
+ rewrite hj81 /=; exact root_pair_81.
case (j = 82) => hj82.
+ rewrite hj82 /=; exact root_pair_82.
case (j = 83) => hj83.
+ rewrite hj83 /=; exact root_pair_83.
case (j = 84) => hj84.
+ rewrite hj84 /=; exact root_pair_84.
case (j = 85) => hj85.
+ rewrite hj85 /=; exact root_pair_85.
case (j = 86) => hj86.
+ rewrite hj86 /=; exact root_pair_86.
case (j = 87) => hj87.
+ rewrite hj87 /=; exact root_pair_87.
case (j = 88) => hj88.
+ rewrite hj88 /=; exact root_pair_88.
case (j = 89) => hj89.
+ rewrite hj89 /=; exact root_pair_89.
case (j = 90) => hj90.
+ rewrite hj90 /=; exact root_pair_90.
case (j = 91) => hj91.
+ rewrite hj91 /=; exact root_pair_91.
case (j = 92) => hj92.
+ rewrite hj92 /=; exact root_pair_92.
case (j = 93) => hj93.
+ rewrite hj93 /=; exact root_pair_93.
case (j = 94) => hj94.
+ rewrite hj94 /=; exact root_pair_94.
have -> : j = 95 by smt().
exact root_pair_95.
qed.

lemma root_pair_chunk_6 (j : int) :
  96 <= j < 112 =>
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j)),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j + 1))) =
  nth (0, 0) root_q16_pairs j.
proof.
move=> hj.
case (j = 96) => hj96.
+ rewrite hj96 /=; exact root_pair_96.
case (j = 97) => hj97.
+ rewrite hj97 /=; exact root_pair_97.
case (j = 98) => hj98.
+ rewrite hj98 /=; exact root_pair_98.
case (j = 99) => hj99.
+ rewrite hj99 /=; exact root_pair_99.
case (j = 100) => hj100.
+ rewrite hj100 /=; exact root_pair_100.
case (j = 101) => hj101.
+ rewrite hj101 /=; exact root_pair_101.
case (j = 102) => hj102.
+ rewrite hj102 /=; exact root_pair_102.
case (j = 103) => hj103.
+ rewrite hj103 /=; exact root_pair_103.
case (j = 104) => hj104.
+ rewrite hj104 /=; exact root_pair_104.
case (j = 105) => hj105.
+ rewrite hj105 /=; exact root_pair_105.
case (j = 106) => hj106.
+ rewrite hj106 /=; exact root_pair_106.
case (j = 107) => hj107.
+ rewrite hj107 /=; exact root_pair_107.
case (j = 108) => hj108.
+ rewrite hj108 /=; exact root_pair_108.
case (j = 109) => hj109.
+ rewrite hj109 /=; exact root_pair_109.
case (j = 110) => hj110.
+ rewrite hj110 /=; exact root_pair_110.
have -> : j = 111 by smt().
exact root_pair_111.
qed.

lemma root_pair_chunk_7 (j : int) :
  112 <= j < 128 =>
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j)),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j + 1))) =
  nth (0, 0) root_q16_pairs j.
proof.
move=> hj.
case (j = 112) => hj112.
+ rewrite hj112 /=; exact root_pair_112.
case (j = 113) => hj113.
+ rewrite hj113 /=; exact root_pair_113.
case (j = 114) => hj114.
+ rewrite hj114 /=; exact root_pair_114.
case (j = 115) => hj115.
+ rewrite hj115 /=; exact root_pair_115.
case (j = 116) => hj116.
+ rewrite hj116 /=; exact root_pair_116.
case (j = 117) => hj117.
+ rewrite hj117 /=; exact root_pair_117.
case (j = 118) => hj118.
+ rewrite hj118 /=; exact root_pair_118.
case (j = 119) => hj119.
+ rewrite hj119 /=; exact root_pair_119.
case (j = 120) => hj120.
+ rewrite hj120 /=; exact root_pair_120.
case (j = 121) => hj121.
+ rewrite hj121 /=; exact root_pair_121.
case (j = 122) => hj122.
+ rewrite hj122 /=; exact root_pair_122.
case (j = 123) => hj123.
+ rewrite hj123 /=; exact root_pair_123.
case (j = 124) => hj124.
+ rewrite hj124 /=; exact root_pair_124.
case (j = 125) => hj125.
+ rewrite hj125 /=; exact root_pair_125.
case (j = 126) => hj126.
+ rewrite hj126 /=; exact root_pair_126.
have -> : j = 127 by smt().
exact root_pair_127.
qed.

lemma root_pair_chunk_8 (j : int) :
  128 <= j < 144 =>
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j)),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j + 1))) =
  nth (0, 0) root_q16_pairs j.
proof.
move=> hj.
case (j = 128) => hj128.
+ rewrite hj128 /=; exact root_pair_128.
case (j = 129) => hj129.
+ rewrite hj129 /=; exact root_pair_129.
case (j = 130) => hj130.
+ rewrite hj130 /=; exact root_pair_130.
case (j = 131) => hj131.
+ rewrite hj131 /=; exact root_pair_131.
case (j = 132) => hj132.
+ rewrite hj132 /=; exact root_pair_132.
case (j = 133) => hj133.
+ rewrite hj133 /=; exact root_pair_133.
case (j = 134) => hj134.
+ rewrite hj134 /=; exact root_pair_134.
case (j = 135) => hj135.
+ rewrite hj135 /=; exact root_pair_135.
case (j = 136) => hj136.
+ rewrite hj136 /=; exact root_pair_136.
case (j = 137) => hj137.
+ rewrite hj137 /=; exact root_pair_137.
case (j = 138) => hj138.
+ rewrite hj138 /=; exact root_pair_138.
case (j = 139) => hj139.
+ rewrite hj139 /=; exact root_pair_139.
case (j = 140) => hj140.
+ rewrite hj140 /=; exact root_pair_140.
case (j = 141) => hj141.
+ rewrite hj141 /=; exact root_pair_141.
case (j = 142) => hj142.
+ rewrite hj142 /=; exact root_pair_142.
have -> : j = 143 by smt().
exact root_pair_143.
qed.

lemma root_pair_chunk_9 (j : int) :
  144 <= j < 160 =>
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j)),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j + 1))) =
  nth (0, 0) root_q16_pairs j.
proof.
move=> hj.
case (j = 144) => hj144.
+ rewrite hj144 /=; exact root_pair_144.
case (j = 145) => hj145.
+ rewrite hj145 /=; exact root_pair_145.
case (j = 146) => hj146.
+ rewrite hj146 /=; exact root_pair_146.
case (j = 147) => hj147.
+ rewrite hj147 /=; exact root_pair_147.
case (j = 148) => hj148.
+ rewrite hj148 /=; exact root_pair_148.
case (j = 149) => hj149.
+ rewrite hj149 /=; exact root_pair_149.
case (j = 150) => hj150.
+ rewrite hj150 /=; exact root_pair_150.
case (j = 151) => hj151.
+ rewrite hj151 /=; exact root_pair_151.
case (j = 152) => hj152.
+ rewrite hj152 /=; exact root_pair_152.
case (j = 153) => hj153.
+ rewrite hj153 /=; exact root_pair_153.
case (j = 154) => hj154.
+ rewrite hj154 /=; exact root_pair_154.
case (j = 155) => hj155.
+ rewrite hj155 /=; exact root_pair_155.
case (j = 156) => hj156.
+ rewrite hj156 /=; exact root_pair_156.
case (j = 157) => hj157.
+ rewrite hj157 /=; exact root_pair_157.
case (j = 158) => hj158.
+ rewrite hj158 /=; exact root_pair_158.
have -> : j = 159 by smt().
exact root_pair_159.
qed.

lemma root_pair_chunk_10 (j : int) :
  160 <= j < 176 =>
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j)),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j + 1))) =
  nth (0, 0) root_q16_pairs j.
proof.
move=> hj.
case (j = 160) => hj160.
+ rewrite hj160 /=; exact root_pair_160.
case (j = 161) => hj161.
+ rewrite hj161 /=; exact root_pair_161.
case (j = 162) => hj162.
+ rewrite hj162 /=; exact root_pair_162.
case (j = 163) => hj163.
+ rewrite hj163 /=; exact root_pair_163.
case (j = 164) => hj164.
+ rewrite hj164 /=; exact root_pair_164.
case (j = 165) => hj165.
+ rewrite hj165 /=; exact root_pair_165.
case (j = 166) => hj166.
+ rewrite hj166 /=; exact root_pair_166.
case (j = 167) => hj167.
+ rewrite hj167 /=; exact root_pair_167.
case (j = 168) => hj168.
+ rewrite hj168 /=; exact root_pair_168.
case (j = 169) => hj169.
+ rewrite hj169 /=; exact root_pair_169.
case (j = 170) => hj170.
+ rewrite hj170 /=; exact root_pair_170.
case (j = 171) => hj171.
+ rewrite hj171 /=; exact root_pair_171.
case (j = 172) => hj172.
+ rewrite hj172 /=; exact root_pair_172.
case (j = 173) => hj173.
+ rewrite hj173 /=; exact root_pair_173.
case (j = 174) => hj174.
+ rewrite hj174 /=; exact root_pair_174.
have -> : j = 175 by smt().
exact root_pair_175.
qed.

lemma root_pair_chunk_11 (j : int) :
  176 <= j < 192 =>
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j)),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j + 1))) =
  nth (0, 0) root_q16_pairs j.
proof.
move=> hj.
case (j = 176) => hj176.
+ rewrite hj176 /=; exact root_pair_176.
case (j = 177) => hj177.
+ rewrite hj177 /=; exact root_pair_177.
case (j = 178) => hj178.
+ rewrite hj178 /=; exact root_pair_178.
case (j = 179) => hj179.
+ rewrite hj179 /=; exact root_pair_179.
case (j = 180) => hj180.
+ rewrite hj180 /=; exact root_pair_180.
case (j = 181) => hj181.
+ rewrite hj181 /=; exact root_pair_181.
case (j = 182) => hj182.
+ rewrite hj182 /=; exact root_pair_182.
case (j = 183) => hj183.
+ rewrite hj183 /=; exact root_pair_183.
case (j = 184) => hj184.
+ rewrite hj184 /=; exact root_pair_184.
case (j = 185) => hj185.
+ rewrite hj185 /=; exact root_pair_185.
case (j = 186) => hj186.
+ rewrite hj186 /=; exact root_pair_186.
case (j = 187) => hj187.
+ rewrite hj187 /=; exact root_pair_187.
case (j = 188) => hj188.
+ rewrite hj188 /=; exact root_pair_188.
case (j = 189) => hj189.
+ rewrite hj189 /=; exact root_pair_189.
case (j = 190) => hj190.
+ rewrite hj190 /=; exact root_pair_190.
have -> : j = 191 by smt().
exact root_pair_191.
qed.

lemma root_pair_chunk_12 (j : int) :
  192 <= j < 208 =>
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j)),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j + 1))) =
  nth (0, 0) root_q16_pairs j.
proof.
move=> hj.
case (j = 192) => hj192.
+ rewrite hj192 /=; exact root_pair_192.
case (j = 193) => hj193.
+ rewrite hj193 /=; exact root_pair_193.
case (j = 194) => hj194.
+ rewrite hj194 /=; exact root_pair_194.
case (j = 195) => hj195.
+ rewrite hj195 /=; exact root_pair_195.
case (j = 196) => hj196.
+ rewrite hj196 /=; exact root_pair_196.
case (j = 197) => hj197.
+ rewrite hj197 /=; exact root_pair_197.
case (j = 198) => hj198.
+ rewrite hj198 /=; exact root_pair_198.
case (j = 199) => hj199.
+ rewrite hj199 /=; exact root_pair_199.
case (j = 200) => hj200.
+ rewrite hj200 /=; exact root_pair_200.
case (j = 201) => hj201.
+ rewrite hj201 /=; exact root_pair_201.
case (j = 202) => hj202.
+ rewrite hj202 /=; exact root_pair_202.
case (j = 203) => hj203.
+ rewrite hj203 /=; exact root_pair_203.
case (j = 204) => hj204.
+ rewrite hj204 /=; exact root_pair_204.
case (j = 205) => hj205.
+ rewrite hj205 /=; exact root_pair_205.
case (j = 206) => hj206.
+ rewrite hj206 /=; exact root_pair_206.
have -> : j = 207 by smt().
exact root_pair_207.
qed.

lemma root_pair_chunk_13 (j : int) :
  208 <= j < 224 =>
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j)),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j + 1))) =
  nth (0, 0) root_q16_pairs j.
proof.
move=> hj.
case (j = 208) => hj208.
+ rewrite hj208 /=; exact root_pair_208.
case (j = 209) => hj209.
+ rewrite hj209 /=; exact root_pair_209.
case (j = 210) => hj210.
+ rewrite hj210 /=; exact root_pair_210.
case (j = 211) => hj211.
+ rewrite hj211 /=; exact root_pair_211.
case (j = 212) => hj212.
+ rewrite hj212 /=; exact root_pair_212.
case (j = 213) => hj213.
+ rewrite hj213 /=; exact root_pair_213.
case (j = 214) => hj214.
+ rewrite hj214 /=; exact root_pair_214.
case (j = 215) => hj215.
+ rewrite hj215 /=; exact root_pair_215.
case (j = 216) => hj216.
+ rewrite hj216 /=; exact root_pair_216.
case (j = 217) => hj217.
+ rewrite hj217 /=; exact root_pair_217.
case (j = 218) => hj218.
+ rewrite hj218 /=; exact root_pair_218.
case (j = 219) => hj219.
+ rewrite hj219 /=; exact root_pair_219.
case (j = 220) => hj220.
+ rewrite hj220 /=; exact root_pair_220.
case (j = 221) => hj221.
+ rewrite hj221 /=; exact root_pair_221.
case (j = 222) => hj222.
+ rewrite hj222 /=; exact root_pair_222.
have -> : j = 223 by smt().
exact root_pair_223.
qed.

lemma root_pair_chunk_14 (j : int) :
  224 <= j < 240 =>
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j)),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j + 1))) =
  nth (0, 0) root_q16_pairs j.
proof.
move=> hj.
case (j = 224) => hj224.
+ rewrite hj224 /=; exact root_pair_224.
case (j = 225) => hj225.
+ rewrite hj225 /=; exact root_pair_225.
case (j = 226) => hj226.
+ rewrite hj226 /=; exact root_pair_226.
case (j = 227) => hj227.
+ rewrite hj227 /=; exact root_pair_227.
case (j = 228) => hj228.
+ rewrite hj228 /=; exact root_pair_228.
case (j = 229) => hj229.
+ rewrite hj229 /=; exact root_pair_229.
case (j = 230) => hj230.
+ rewrite hj230 /=; exact root_pair_230.
case (j = 231) => hj231.
+ rewrite hj231 /=; exact root_pair_231.
case (j = 232) => hj232.
+ rewrite hj232 /=; exact root_pair_232.
case (j = 233) => hj233.
+ rewrite hj233 /=; exact root_pair_233.
case (j = 234) => hj234.
+ rewrite hj234 /=; exact root_pair_234.
case (j = 235) => hj235.
+ rewrite hj235 /=; exact root_pair_235.
case (j = 236) => hj236.
+ rewrite hj236 /=; exact root_pair_236.
case (j = 237) => hj237.
+ rewrite hj237 /=; exact root_pair_237.
case (j = 238) => hj238.
+ rewrite hj238 /=; exact root_pair_238.
have -> : j = 239 by smt().
exact root_pair_239.
qed.

lemma root_pair_chunk_15 (j : int) :
  240 <= j < 256 =>
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j)),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j + 1))) =
  nth (0, 0) root_q16_pairs j.
proof.
move=> hj.
case (j = 240) => hj240.
+ rewrite hj240 /=; exact root_pair_240.
case (j = 241) => hj241.
+ rewrite hj241 /=; exact root_pair_241.
case (j = 242) => hj242.
+ rewrite hj242 /=; exact root_pair_242.
case (j = 243) => hj243.
+ rewrite hj243 /=; exact root_pair_243.
case (j = 244) => hj244.
+ rewrite hj244 /=; exact root_pair_244.
case (j = 245) => hj245.
+ rewrite hj245 /=; exact root_pair_245.
case (j = 246) => hj246.
+ rewrite hj246 /=; exact root_pair_246.
case (j = 247) => hj247.
+ rewrite hj247 /=; exact root_pair_247.
case (j = 248) => hj248.
+ rewrite hj248 /=; exact root_pair_248.
case (j = 249) => hj249.
+ rewrite hj249 /=; exact root_pair_249.
case (j = 250) => hj250.
+ rewrite hj250 /=; exact root_pair_250.
case (j = 251) => hj251.
+ rewrite hj251 /=; exact root_pair_251.
case (j = 252) => hj252.
+ rewrite hj252 /=; exact root_pair_252.
case (j = 253) => hj253.
+ rewrite hj253 /=; exact root_pair_253.
case (j = 254) => hj254.
+ rewrite hj254 /=; exact root_pair_254.
have -> : j = 255 by smt().
exact root_pair_255.
qed.

lemma jfft_root_pair_exact (j : int) :
  0 <= j < 256 =>
  (W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j)),
   W32.to_sint
      (BArray2048.get32 KeygenMode2ParentTarget.jfft_roots (2 * j + 1))) =
  nth (0, 0) root_q16_pairs j.
proof.
move=> hj.
case (j < 16) => hj16.
+ apply (root_pair_chunk_0 j); smt().
case (j < 32) => hj32.
+ apply (root_pair_chunk_1 j); smt().
case (j < 48) => hj48.
+ apply (root_pair_chunk_2 j); smt().
case (j < 64) => hj64.
+ apply (root_pair_chunk_3 j); smt().
case (j < 80) => hj80.
+ apply (root_pair_chunk_4 j); smt().
case (j < 96) => hj96.
+ apply (root_pair_chunk_5 j); smt().
case (j < 112) => hj112.
+ apply (root_pair_chunk_6 j); smt().
case (j < 128) => hj128.
+ apply (root_pair_chunk_7 j); smt().
case (j < 144) => hj144.
+ apply (root_pair_chunk_8 j); smt().
case (j < 160) => hj160.
+ apply (root_pair_chunk_9 j); smt().
case (j < 176) => hj176.
+ apply (root_pair_chunk_10 j); smt().
case (j < 192) => hj192.
+ apply (root_pair_chunk_11 j); smt().
case (j < 208) => hj208.
+ apply (root_pair_chunk_12 j); smt().
case (j < 224) => hj224.
+ apply (root_pair_chunk_13 j); smt().
case (j < 240) => hj240.
+ apply (root_pair_chunk_14 j); smt().
apply (root_pair_chunk_15 j); smt().
qed.

lemma jfft_roots_q16_coordinate_error (j : int) :
  0 <= j < 256 =>
  `|creal (ideal_root j) -
      (W32.to_sint
        (BArray2048.get32
          KeygenMode2ParentTarget.jfft_roots (2 * j)))%r / 65536%r|
    < 1%r / 131072%r /\
  `|cimag (ideal_root j) -
      (W32.to_sint
        (BArray2048.get32
          KeygenMode2ParentTarget.jfft_roots (2 * j + 1)))%r / 65536%r|
    < 1%r / 131072%r.
proof.
move=> hj.
have hpair := jfft_root_pair_exact j hj.
have herr := ideal_root_q16_error j hj.
have hre := congr1 fst _ _ hpair.
have him := congr1 snd _ _ hpair.
by rewrite hre him.
qed.

lemma jfft_roots_q16_rounds (j : int) :
  0 <= j < 256 =>
  floor (65536%r * creal (ideal_root j) + 1%r / 2%r) =
    W32.to_sint
      (BArray2048.get32
        KeygenMode2ParentTarget.jfft_roots (2 * j)) /\
  floor (65536%r * cimag (ideal_root j) + 1%r / 2%r) =
    W32.to_sint
      (BArray2048.get32
        KeygenMode2ParentTarget.jfft_roots (2 * j + 1)).
proof.
move=> hj.
have hpair := jfft_root_pair_exact j hj.
have hround := ideal_root_q16_rounds j hj.
have hre := congr1 fst _ _ hpair.
have him := congr1 snd _ _ hpair.
by rewrite hre him.
qed.

lemma jfft_roots_q16_unique (j qre qim : int) :
  0 <= j < 256 =>
  `|creal (ideal_root j) - qre%r / 65536%r|
    < 1%r / 131072%r =>
  `|cimag (ideal_root j) - qim%r / 65536%r|
    < 1%r / 131072%r =>
  qre =
    W32.to_sint
      (BArray2048.get32
        KeygenMode2ParentTarget.jfft_roots (2 * j)) /\
  qim =
    W32.to_sint
      (BArray2048.get32
        KeygenMode2ParentTarget.jfft_roots (2 * j + 1)).
proof.
move=> hj hqre hqim.
have hactual := jfft_roots_q16_coordinate_error j hj.
move: hactual => [hre him].
split.
+ exact (q16_strict_cell_unique qre
    (W32.to_sint
      (BArray2048.get32
        KeygenMode2ParentTarget.jfft_roots (2 * j)))
    (creal (ideal_root j)) hqre hre).
+ exact (q16_strict_cell_unique qim
    (W32.to_sint
      (BArray2048.get32
        KeygenMode2ParentTarget.jfft_roots (2 * j + 1)))
    (cimag (ideal_root j)) hqim him).
qed.

end KeygenM23RootTableTargetBridge.
