require import AllCore IntDiv List.
require import HAETAE_Params HAETAE_FIPS202 HAETAE_FIPS202_CRef.

theory HAETAE_FIPS202_TestVectors.

import HAETAE_Params.
import HAETAE_FIPS202.
import HAETAE_FIPS202_CRef.

op shake256_empty_input : fips_byte list = [].
op shake256_zero_byte_input : fips_byte list = [0].
op shake256_keygen32_input : fips_byte list = mkseq (fun i => i) seedbytes.

op shake256_empty_64_expected : fips_byte list = [
  70; 185; 221; 43; 11; 168; 141; 19; 35; 59; 63; 235; 116; 62; 235; 36;
  63; 205; 82; 234; 98; 184; 27; 130; 181; 12; 39; 100; 110; 213; 118; 47;
  215; 93; 196; 221; 216; 192; 242; 0; 203; 5; 1; 157; 103; 181; 146; 246;
  252; 130; 28; 73; 71; 154; 180; 134; 64; 41; 46; 172; 179; 183; 196; 190
].

op shake256_zero_byte_64_expected : fips_byte list = [
  184; 208; 29; 248; 85; 247; 7; 88; 130; 198; 54; 246; 221; 234; 207; 65;
  229; 222; 11; 191; 48; 4; 46; 240; 168; 110; 54; 244; 184; 96; 13; 84;
  108; 81; 101; 1; 166; 163; 200; 33; 103; 141; 61; 153; 67; 250; 158; 116;
  185; 185; 159; 204; 212; 122; 236; 201; 29; 209; 244; 148; 107; 131; 85; 179
].

op shake256_keygen32_128_expected : fips_byte list = [
  105; 240; 124; 136; 64; 206; 128; 2; 77; 179; 9; 57; 136; 44; 61; 91;
  188; 156; 152; 179; 227; 30; 69; 19; 235; 210; 202; 155; 69; 3; 205; 211;
  201; 201; 7; 66; 69; 44; 113; 115; 212; 167; 90; 196; 145; 99; 225; 78;
  224; 204; 36; 239; 112; 53; 178; 114; 209; 154; 122; 241; 9; 155; 51; 63;
  97; 116; 101; 214; 155; 95; 91; 120; 174; 145; 78; 74; 27; 28; 236; 201;
  33; 246; 213; 121; 24; 48; 174; 63; 145; 75; 238; 155; 2; 146; 178; 136;
  51; 124; 236; 171; 196; 190; 145; 95; 20; 83; 96; 123; 255; 111; 6; 50;
  202; 127; 62; 142; 171; 83; 69; 110; 186; 71; 48; 10; 214; 31; 224; 220
].

op shake256_empty_64_actual : fips_byte list =
  shake256 shake256_empty_input 0 64.
op shake256_zero_byte_64_actual : fips_byte list =
  shake256 shake256_zero_byte_input 1 64.
op shake256_keygen32_128_actual : fips_byte list =
  shake256 shake256_keygen32_input seedbytes (2 * seedbytes + crhbytes).

op shake256_empty_64_known_answer : bool =
  shake256_empty_64_actual = shake256_empty_64_expected.
op shake256_zero_byte_64_known_answer : bool =
  shake256_zero_byte_64_actual = shake256_zero_byte_64_expected.
op shake256_keygen32_128_known_answer : bool =
  shake256_keygen32_128_actual = shake256_keygen32_128_expected.

op shake256_known_answer_obligations : bool =
  shake256_empty_64_known_answer /\
  shake256_zero_byte_64_known_answer /\
  shake256_keygen32_128_known_answer.

op shake256_empty_64_c_api_actual : fips_byte list =
  cref_shake256_c_api_short shake256_empty_input 0 64.
op shake256_zero_byte_64_c_api_actual : fips_byte list =
  cref_shake256_c_api_short shake256_zero_byte_input 1 64.
op shake256_keygen32_128_c_api_actual : fips_byte list =
  cref_shake256_c_api_short
    shake256_keygen32_input
    seedbytes
    (2 * seedbytes + crhbytes).

op shake256_empty_64_c_api_known_answer : bool =
  shake256_empty_64_c_api_actual = shake256_empty_64_expected.
op shake256_zero_byte_64_c_api_known_answer : bool =
  shake256_zero_byte_64_c_api_actual = shake256_zero_byte_64_expected.
op shake256_keygen32_128_c_api_known_answer : bool =
  shake256_keygen32_128_c_api_actual = shake256_keygen32_128_expected.

op shake256_c_api_known_answer_obligations : bool =
  shake256_empty_64_c_api_known_answer /\
  shake256_zero_byte_64_c_api_known_answer /\
  shake256_keygen32_128_c_api_known_answer.

lemma shake256_empty_input_size :
  size shake256_empty_input = 0.
proof. by rewrite /shake256_empty_input. qed.

lemma shake256_zero_byte_input_size :
  size shake256_zero_byte_input = 1.
proof. by rewrite /shake256_zero_byte_input. qed.

lemma shake256_keygen32_input_size :
  size shake256_keygen32_input = seedbytes.
proof. by rewrite /shake256_keygen32_input size_mkseq /seedbytes. qed.

lemma shake256_empty_64_expected_size :
  size shake256_empty_64_expected = 64.
proof. by rewrite /shake256_empty_64_expected. qed.

lemma shake256_zero_byte_64_expected_size :
  size shake256_zero_byte_64_expected = 64.
proof. by rewrite /shake256_zero_byte_64_expected. qed.

lemma shake256_keygen32_128_expected_size :
  size shake256_keygen32_128_expected = 2 * seedbytes + crhbytes.
proof.
by rewrite /shake256_keygen32_128_expected /seedbytes /crhbytes.
qed.

lemma shake256_empty_64_actual_size :
  size shake256_empty_64_actual = 64.
proof. by rewrite /shake256_empty_64_actual shake256_size. qed.

lemma shake256_zero_byte_64_actual_size :
  size shake256_zero_byte_64_actual = 64.
proof. by rewrite /shake256_zero_byte_64_actual shake256_size. qed.

lemma shake256_keygen32_128_actual_size :
  size shake256_keygen32_128_actual = 2 * seedbytes + crhbytes.
proof.
by rewrite /shake256_keygen32_128_actual shake256_size
           /seedbytes /crhbytes.
qed.

lemma shake256_empty_64_c_api_actualE :
  shake256_empty_64_c_api_actual = shake256_empty_64_actual.
proof.
by rewrite /shake256_empty_64_c_api_actual
           /shake256_empty_64_actual
           cref_shake256_c_api_shortE.
qed.

lemma shake256_zero_byte_64_c_api_actualE :
  shake256_zero_byte_64_c_api_actual = shake256_zero_byte_64_actual.
proof.
by rewrite /shake256_zero_byte_64_c_api_actual
           /shake256_zero_byte_64_actual
           cref_shake256_c_api_shortE.
qed.

lemma shake256_keygen32_128_c_api_actualE :
  shake256_keygen32_128_c_api_actual = shake256_keygen32_128_actual.
proof.
by rewrite /shake256_keygen32_128_c_api_actual
           /shake256_keygen32_128_actual
           cref_shake256_c_api_shortE.
qed.

lemma shake256_empty_64_c_api_actual_size :
  size shake256_empty_64_c_api_actual = 64.
proof. by rewrite shake256_empty_64_c_api_actualE shake256_empty_64_actual_size. qed.

lemma shake256_zero_byte_64_c_api_actual_size :
  size shake256_zero_byte_64_c_api_actual = 64.
proof. by rewrite shake256_zero_byte_64_c_api_actualE shake256_zero_byte_64_actual_size. qed.

lemma shake256_keygen32_128_c_api_actual_size :
  size shake256_keygen32_128_c_api_actual = 2 * seedbytes + crhbytes.
proof. by rewrite shake256_keygen32_128_c_api_actualE
                  shake256_keygen32_128_actual_size. qed.

lemma shake256_known_answer_obligations_c_apiE :
  shake256_known_answer_obligations =
  shake256_c_api_known_answer_obligations.
proof.
by rewrite /shake256_known_answer_obligations
           /shake256_c_api_known_answer_obligations
           /shake256_empty_64_known_answer
           /shake256_zero_byte_64_known_answer
           /shake256_keygen32_128_known_answer
           /shake256_empty_64_c_api_known_answer
           /shake256_zero_byte_64_c_api_known_answer
           /shake256_keygen32_128_c_api_known_answer
           shake256_empty_64_c_api_actualE
           shake256_zero_byte_64_c_api_actualE
           shake256_keygen32_128_c_api_actualE.
qed.

lemma cref_shake256_empty_64_actualE :
  shake256_empty_64_actual =
  cref_shake256 shake256_empty_input 0 64.
proof. by rewrite /shake256_empty_64_actual cref_shake256E. qed.

lemma cref_shake256_zero_byte_64_actualE :
  shake256_zero_byte_64_actual =
  cref_shake256 shake256_zero_byte_input 1 64.
proof. by rewrite /shake256_zero_byte_64_actual cref_shake256E. qed.

lemma cref_shake256_keygen32_128_actualE :
  shake256_keygen32_128_actual =
  cref_shake256
    shake256_keygen32_input
    seedbytes
    (2 * seedbytes + crhbytes).
proof. by rewrite /shake256_keygen32_128_actual cref_shake256E. qed.

end HAETAE_FIPS202_TestVectors.
