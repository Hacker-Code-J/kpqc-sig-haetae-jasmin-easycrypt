require import AllCore IntDiv List Ring StdOrder BitEncoding.

require import Array256.
require import GFq Rq.

import Zq IntOrder BitReverse.

theory NTTFullSpec.

lemma pow2_8 :
  2 ^ 8 = 256.
proof. by []. qed.

lemma bsrev8_range_256 n :
  bsrev 8 n \in range 0 256.
proof.
move: (bsrev_range 8 n).
by rewrite pow2_8.
qed.

lemma bsrev8_involutive_256 n :
  n \in range 0 256 =>
  bsrev 8 (bsrev 8 n) = n.
proof.
move=> hn.
rewrite bsrev_involutive.
+ by smt().
+ by rewrite pow2_8.
by [].
qed.

op partial_ntt (p : poly, len start bsj : int) =
  Rq.BigDom.BAdd.bigi predT
    (fun s =>
      ZqRing.exp zroot ((2 * start + 1) * bsrev 8 s) *
      p.[bsrev 8 (bsj * len + s)])
    0 len.

op full_ntt_spec (r p : poly) =
  forall start,
    start \in range 0 256 =>
    r.[bsrev 8 start] = partial_ntt p 256 start 0.

op full_ntt (p : poly) : poly =
  Array256.init (fun i =>
    Rq.BigDom.BAdd.bigi predT
      (fun j => p.[j] * ZqRing.exp zroot ((2 * br i + 1) * j))
      0 256).

op full_invntt (p : poly) : poly =
  Array256.init (fun i =>
    Rq.BigDom.BAdd.bigi predT
      (fun j =>
        inv (incoeff 256) * p.[j] *
        ZqRing.exp zroot (- ((2 * br j + 1) * i)))
      0 256).

op full_invntt_spec (r p : poly) =
  forall i,
    i \in range 0 256 =>
    r.[bsrev 8 i] =
      Rq.BigDom.BAdd.bigi predT
        (fun j =>
          inv (incoeff 256) * p.[j] *
          ZqRing.exp zroot (- ((2 * br j + 1) * bsrev 8 i)))
        0 256.

lemma full_ntt_spec_imp p r :
  full_ntt_spec r p =>
  r = full_ntt p.
proof.
move=> hspec.
apply Array256.ext_eq => i hi.
rewrite /full_ntt Array256.initiE 1:/#.
have hbr_range : bsrev 8 i \in range 0 256 by apply bsrev8_range_256.
have hspeci : r.[i] = partial_ntt p 256 (bsrev 8 i) 0.
+ have hbri : bsrev 8 (bsrev 8 i) = i by apply bsrev8_involutive_256; rewrite mem_range.
  move: (hspec (bsrev 8 i) hbr_range).
  by rewrite hbri.
rewrite hspeci.
rewrite /partial_ntt /=.
have hperm : perm_eq (range 0 256) (map (bsrev 8) (range 0 256)).
+ rewrite perm_eq_sym.
  have h := bsrev_range_pow2_perm_eq 8 8 _.
  + by [].
  move: h; rewrite !pow2_8 /=.
  have -> : map (( * ) 1) (range 0 256) = range 0 256.
  + by apply/id_map => x; ring.
  by [].
rewrite (Rq.BigDom.BAdd.eq_big_perm _ _ _ (map (bsrev 8) (range 0 256))) 1:hperm.
rewrite Rq.BigDom.BAdd.big_mapT.
apply Rq.BigDom.BAdd.eq_big_int => j hj /=.
rewrite /(\o) /=.
rewrite ZqRing.mulrC.
have -> : bsrev 8 (bsrev 8 j) = j.
+ apply bsrev8_involutive_256.
  by rewrite mem_range; smt().
by [].
qed.

lemma full_invntt_spec_imp p r :
  full_invntt_spec r p =>
  r = full_invntt p.
proof.
move=> hspec.
apply Array256.ext_eq => i hi.
rewrite /full_invntt Array256.initiE 1:/#.
have hbr_range : bsrev 8 i \in range 0 256 by apply bsrev8_range_256.
have hbri : bsrev 8 (bsrev 8 i) = i.
+ by apply bsrev8_involutive_256; rewrite mem_range.
move: (hspec (bsrev 8 i) hbr_range).
by rewrite hbri.
qed.

lemma one_get0 :
  Rq.one.[0] = Zq.one.
proof. by rewrite /Rq.one Array256.get_set_if /=. qed.

lemma one_get_neq0 i :
  0 <= i < 256 =>
  i <> 0 =>
  Rq.one.[i] = Zq.zero.
proof.
move=> hirange hi.
rewrite /Rq.one Array256.get_set_if /= hi.
by rewrite /Rq.zero Array256.createiE.
qed.

lemma rq_ntt_one_odd1 :
  (ntt Rq.one).[1] = Zq.zero.
proof.
rewrite nttE Array256.initiE 1:/# /=.
rewrite Rq.BigDom.BAdd.big_seq_cond Rq.BigDom.BAdd.big1 //= => j [hj _].
have hget : Rq.one.[2 * j + 1] = Zq.zero by apply one_get_neq0; smt().
by rewrite hget ZqRing.mul0r.
qed.

lemma full_ntt_one_odd1 :
  (full_ntt Rq.one).[1] = Zq.one.
proof.
rewrite /full_ntt Array256.initiE 1:/# /=.
rewrite (Rq.BigDom.BAdd.bigD1 _ _ 0) 1:/# 1:/# /=.
rewrite one_get0 ZqRing.expr0 ZqRing.mulr1.
rewrite Rq.BigDom.BAdd.big_seq_cond Rq.BigDom.BAdd.big1 ?ZqRing.addr0 //= => j [hj hj0].
rewrite /Rq.one Array256.get_set_if /=.
have -> : (j = 0) = false by smt().
rewrite /Rq.zero Array256.createiE 1:/#.
by rewrite ZqRing.mul0r.
qed.

lemma rq_ntt_is_not_full_ntt_on_one :
  ntt Rq.one <> full_ntt Rq.one.
proof.
apply/negP => heq.
have h : (ntt Rq.one).[1] = (full_ntt Rq.one).[1] by rewrite heq.
rewrite rq_ntt_one_odd1 full_ntt_one_odd1 in h.
by smt(ZqRing.oner_neq0).
qed.

end NTTFullSpec.
