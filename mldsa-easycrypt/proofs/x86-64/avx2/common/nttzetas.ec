(**
  This theory establishes the formal link between the arrays of roots of unity
  used in the AVX2 implementation and their corresponding mathematical
  definitions.

  In particular, it connects the concrete SIMD-level representation—where
  roots are stored with repetitions to match AVX2 vector lanes—to their
  abstract counterparts in the underlying algebraic specification.

  The repetitions induced by SIMD packing are explicitly accounted for,
  ensuring that each duplicated entry in the implementation arrays is proven
  to correspond to the same mathematical root of unity.
*)

(* -------------------------------------------------------------------- *)
require import AllCore List Ring IntDiv BitEncoding.
require import StdRing StdOrder QFABV.
(*---*) import BitEncoding.BS2Int BitEncoding.BitChunking.

from Jasmin require import JWord JModel_x86.
from JazzEC require import Ml_dsa_65_avx2.

require import Nttlogspec.

(* -------------------------------------------------------------------- *)
require import Array4 Array8 Array16.

(* -------------------------------------------------------------------- *)
op topair ['a] (s : 'a list) =
  (nth witness s 0, nth witness s 1).

(* -------------------------------------------------------------------- *)
op [opaque] LAYER_0_ZETAS = lAYER_0_ZETAS.
op [opaque] LAYER_1_ZETAS = lAYER_1_ZETAS.
op [opaque] LAYER_2_ZETAS = lAYER_2_ZETAS.
op [opaque] LAYER_3_ZETAS = lAYER_3_ZETAS.
op [opaque] LAYER_4_ZETAS = lAYER_4_ZETAS.
op [opaque] LAYER_5_ZETAS = lAYER_5_ZETAS.

lemma LAYER_0_ZETASE : lAYER_0_ZETAS = LAYER_0_ZETAS.
proof. by rewrite /LAYER_0_ZETAS. qed.

lemma LAYER_1_ZETASE : lAYER_1_ZETAS = LAYER_1_ZETAS.
proof. by rewrite /LAYER_1_ZETAS. qed.

lemma LAYER_2_ZETASE : lAYER_2_ZETAS = LAYER_2_ZETAS.
proof. by rewrite /LAYER_2_ZETAS. qed.

lemma LAYER_3_ZETASE : lAYER_3_ZETAS = LAYER_3_ZETAS.
proof. by rewrite /LAYER_3_ZETAS. qed.

lemma LAYER_4_ZETASE : lAYER_4_ZETAS = LAYER_4_ZETAS.
proof. by rewrite /LAYER_4_ZETAS. qed.

lemma LAYER_5_ZETASE : lAYER_5_ZETAS = LAYER_5_ZETAS.
proof. by rewrite /LAYER_5_ZETAS. qed.

(* -------------------------------------------------------------------- *)
section.
hint simplify bs2int_nil, bs2int_cons.
hint simplify rev_nil, rev_cons.
hint simplify int2bs0, int2bs_cons.
hint simplify nseq0, nseqS_minus.
hint simplify b2i1, b2i0.
hint simplify dvdzE.
hint simplify mkseqSr_minus, mkseq0.

op zeta7 : int = 25847.

lemma zeta_L7E : zetaL 7 = [zeta7].
proof. by rewrite /zetaL; cbv delta. qed.

op zeta6L : int = -2608894.
op zeta6R : int = - 518909.

lemma zeta_L6E : zetaL 6 = [zeta6L; zeta6R].
proof. by rewrite /zetaL; cbv delta. qed.

lemma zeta_L5E : zetaL 5 = [237124; -777960; -876248; 466468].
proof. by rewrite /zetaL; cbv delta. qed.

lemma zeta_L4E : zetaL 4 = [
  1826347;  2353451; -359251; -2091905;
  3119733; -2884855;  3111497; 2680103
].
proof. by rewrite /zetaL; cbv delta. qed.

lemma zeta_L3E : zetaL 3 = [
   2725464;  1024112; -1079900;  3585928;
  - 549488; -1119584;  2619752; -2108549;
  -2118186; -3859737; -1399561; -3277672;
   1757237; -  19422;  4010497;   280005
].
proof. by rewrite /zetaL; cbv delta. qed.

lemma zeta_L2E : zetaL 2 = [
   2706023;    95776; 3077325;  3530437; -1661693; -3592148; -2537516;  3915439;
  -3861115; -3043716; 3574422; -2867647;  3539968; - 300467;  2348700; - 539299;
  -1699267; -1643818; 3505694; -3821735;  3507263; -2140649; -1600420;  3699596;
    811944;   531354;  954230;  3881043;  3900724; -2556880;  2071892; -2797779
].
proof. by rewrite /zetaL; cbv delta. qed.

lemma zeta_L1E : zetaL 1 = [
  -3930395; -1528703; -3677745; -3041255; -1452451;  3475950;  2176455; -1585221;
  -1257611;  1939314; -4083598; -1000202; -3190144; -3157330; -3632928;   126922;
   3412210; - 983419;  2147896;  2715295; -2967645; -3693493; - 411027; -2477047;
  - 671102; -1228525; -  22981; -1308169; - 381987;  1349076;  1852771; -1430430;
  -3343383;   264944;   508951;  3097992;    44288; -1100098;   904516;  3958618;
  -3724342; -   8578;  1653064; -3249728;  2389356; - 210977;   759969; -1316856;
    189548; -3553272;  3159746; -1851402; -2409325; - 177440;  1315589;  1341330;
   1285669; -1584928; - 812732; -1439742; -3019102; -3881060; -3628969;  3839961
].
proof. by rewrite /zetaL; cbv delta. qed.

lemma zeta_L0E : zetaL 0 = [
   2091667;  3407706;  2316500;  3817976; -3342478;  2244091; -2446433; -3562462;
    266997;  2434439; -1235728;  3513181; -3520352; -3759364; -1197226; -3193378;
    900702;  1859098;   909542;   819034;   495491; -1613174; -  43260; - 522500;
   -655327; -3122442;  2031748;  3207046; -3556995; - 525098; - 768622; -3595838;
    342297;   286988; -2437823;  4108315;  3437287; -3342277;  1735879;   203044;
   2842341;  2691481; -2590150;  1265009;  4055324;  1247620;  2486353;  1595974;
  -3767016;  1250494;  2635921; -3548272; -2994039;  1869119;  1903435; -1050970;
  -1333058;  1237275; -3318210; -1430225; - 451100;  1312455;  3306115; -1962642;
  -1279661;  1917081; -2546312; -1374803;  1500165;   777191;  2235880;  3406031;
  - 542412; -2831860; -1671176; -1846953; -2584293; -3724270;   594136; -3776993;
  -2013608;  2432395;  2454455; - 164721;  1957272;  3369112;   185531; -1207385;
  -3183426;   162844;  1616392;  3014001;   810149;  1652634; -3694233; -1799107;
  -3038916;  3523897;  3866901;   269760;  2213111; - 975884;  1717735;   472078;
  - 426683;  1723600; -1803090;  1910376; -1667432; -1104333; - 260646; -3833893;
  -2939036; -2235985; - 420899; -2286327;   183443; - 976891;  1612842; -3545687;
  - 554416;  3919660; -  48306; -1362209;  3937738;  1400424; - 846154;  1976782
].
proof. by rewrite /zetaL; cbv delta. qed.

lemma zeta_L5_AVX2 : lAYER_5_ZETAS =
  Array4.of_list
    witness
    (List.map (fun wi => (W8u32.pack8 (nseq 8 (W32.of_int wi)))) (zetaL 5)).
proof.                 (* FIXME: should be done by pure computation *)
rewrite zeta_L5E /=; do! congr;
  apply: W8u32.wordP => i /(mem_range 0 8) @/range;
  rewrite -iotaredE /= => [#|] -> /=;
  by rewrite of_int_bits32_div.
qed.

lemma zeta_L4_AVX2 : lAYER_4_ZETAS =
  Array8.of_list
    witness
    (List.map (fun wi => (W8u32.pack8 (nseq 8 (W32.of_int wi)))) (zetaL 4)).
proof.                 (* FIXME: should be done by pure computation *)
rewrite zeta_L4E /=; do! congr;
  apply: W8u32.wordP => i /(mem_range 0 8) @/range;
  rewrite -iotaredE /= => [#|] -> /=;
  by rewrite of_int_bits32_div.
qed.

lemma zeta_L3_AVX2 : lAYER_3_ZETAS =
  Array16.of_list
    witness
    (List.map (fun wi => (W8u32.pack8 (nseq 8 (W32.of_int wi)))) (zetaL 3)).
proof.                 (* FIXME: should be done by pure computation *)
rewrite zeta_L3E /=; do! congr;
  apply: W8u32.wordP => i /(mem_range 0 8) @/range;
  rewrite -iotaredE /= => [#|] -> /=;
  by rewrite of_int_bits32_div.
qed.

lemma zeta_L2_AVX2 : lAYER_2_ZETAS =
  Array16.of_list
    witness
    (List.map (fun (w : _ * _) =>
       W2u128.pack2 [
         W4u32.pack4 (nseq 4 (W32.of_int w.`1));
         W4u32.pack4 (nseq 4 (W32.of_int w.`2))
       ])
       (map topair (chunk 2 (zetaL 2)))).
proof.
rewrite zeta_L2E /=; cbv delta; do! congr;
  apply: W8u32.wordP => i /(mem_range 0 8) @/range;
  rewrite -iotaredE /= => [#|] -> /=;
  by rewrite of_int_bits32_div.
qed.

op perm1L = [0; 2; 1; 3].

lemma zeta_L1_AVX2 : lAYER_1_ZETAS =
  Array16.of_list
    witness
    (List.map
      (fun ws =>
        W4u64.pack4
          (List.map (fun w => W2u32.pack2 (nseq 2 (W32.of_int w))) ws))
       (map
         (fun ws => map (fun i => nth witness ws i) perm1L)
         (chunk 4 (zetaL 1)))).
proof.
rewrite zeta_L1E /=; cbv delta; do !congr;
  apply: W8u32.wordP => i /(mem_range 0 8) @/range;
  rewrite -iotaredE /= => [#|] -> /=;
  by rewrite of_int_bits32_div /=.
qed.

op perm0L = [0; 1; 4; 5; 2; 3; 6; 7].

lemma zeta_L0_AVX2 : lAYER_0_ZETAS =
  Array16.of_list
    witness
    (List.map
      (fun ws => W8u32.pack8 (map W32.of_int ws))
      (map
        (fun ws => map (fun i => nth witness ws i) perm0L)
        (chunk 8 (zetaL 0)))).
proof.
rewrite zeta_L0E /=; cbv delta; do !congr;
  apply: W8u32.wordP => i /(mem_range 0 8) @/range;
  rewrite -iotaredE /= => [#|] -> /=;
  by rewrite of_int_bits32_div.
qed.

end section.

lemma size_zeta_L0 : size (zetaL 0) = 128.
proof. by rewrite zeta_L0E. qed.

lemma size_zeta_L1 : size (zetaL 1) = 64.
proof. by rewrite zeta_L1E. qed.

lemma size_zeta_L2 : size (zetaL 2) = 32.
proof. by rewrite zeta_L2E. qed.

lemma size_zeta_L3 : size (zetaL 3) = 16.
proof. by rewrite zeta_L3E. qed.

lemma size_zeta_L4 : size (zetaL 4) = 8.
proof. by rewrite zeta_L4E. qed.

lemma size_zeta_L5 : size (zetaL 5) = 4.
proof. by rewrite zeta_L5E. qed.

hint simplify size_zeta_L0.
hint simplify size_zeta_L1.
hint simplify size_zeta_L2.
hint simplify size_zeta_L3.
hint simplify size_zeta_L4.
hint simplify size_zeta_L5.
