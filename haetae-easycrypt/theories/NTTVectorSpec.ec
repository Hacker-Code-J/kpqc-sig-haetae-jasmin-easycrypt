require import AllCore IntDiv List StdOrder.
from Jasmin require import JWord.
require import BArray1024 BArray8192 Array256 Rq NTT_Fq.

theory NTTVectorSpec.

op block8192 (a : BArray8192.t) (k : int) : BArray1024.t =
  BArray1024.init (fun j => BArray8192.get8 a (1024 * k + j)).

op put_block8192 (a : BArray8192.t) (k : int) (b : BArray1024.t) : BArray8192.t =
  BArray8192.init (fun j =>
    if 1024 * k <= j < 1024 * (k + 1)
    then BArray1024.get8 b (j - 1024 * k)
    else BArray8192.get8 a j).

op vector_repr (a : BArray8192.t) (ps : Rq.poly list) (count sz : int) : bool =
  0 <= count <= 8 /\ size ps = count /\
  forall k, 0 <= k < count =>
    NTT_Fq.poly_repr_bound (block8192 a k) (nth Rq.zero ps k) sz.

op inactive_unchanged (before after : BArray8192.t) (count : int) : bool =
  forall j, 1024 * count <= j < 8192 =>
    BArray8192.get8 after j = BArray8192.get8 before j.

lemma block8192_get8 a k j :
  0 <= j < 1024 =>
  BArray1024.get8 (block8192 a k) j = BArray8192.get8 a (1024*k+j).
proof. by move=> hj; rewrite /block8192 BArray1024.initiE. qed.

lemma block8192_get32 a k i :
  0 <= i < 256 =>
  BArray1024.get32 (block8192 a k) i = BArray8192.get32 a (256*k+i).
proof.
move=> hi; apply W4u8.wordP => b hb.
rewrite BArray1024.get32d_byte 1:hb BArray8192.get32d_byte 1:hb.
rewrite block8192_get8 1:/#.
have -> : 1024*k+(4*i+b)=4*(256*k+i)+b by ring.
trivial.
qed.

lemma put_block8192_get8 a k b j :
  0 <= j < 8192 =>
  BArray8192.get8 (put_block8192 a k b) j =
    if 1024*k <= j < 1024*(k+1) then BArray1024.get8 b (j-1024*k)
    else BArray8192.get8 a j.
proof. by move=> hj; rewrite /put_block8192 BArray8192.initiE. qed.

lemma block8192_put_same a k b :
  0 <= k < 8 => block8192 (put_block8192 a k b) k = b.
proof.
move=> hk; apply BArray1024.ext_eq => j hj.
rewrite block8192_get8 1:hj put_block8192_get8 1:/#.
smt().
qed.

lemma block8192_put_other a k b l :
  0 <= k < 8 => 0 <= l < 8 => k<>l =>
  block8192 (put_block8192 a k b) l = block8192 a l.
proof.
move=> hk hl hneq; apply BArray1024.ext_eq => j hj.
rewrite !block8192_get8 1:hj 1:hj put_block8192_get8 1:/#.
smt().
qed.

lemma put_block8192_self a k :
  0 <= k < 8 => put_block8192 a k (block8192 a k) = a.
proof.
move=> hk; apply BArray8192.ext_eq => j hj.
rewrite put_block8192_get8 1:hj.
case (1024*k <= j < 1024*(k+1)) => hmem //=.
rewrite block8192_get8 1:/#.
smt().
qed.

lemma inactive_unchanged_refl a n : inactive_unchanged a a n.
proof. by rewrite /inactive_unchanged. qed.

lemma inactive_unchanged_trans a b c n :
  inactive_unchanged a b n => inactive_unchanged b c n => inactive_unchanged a c n.
proof. by rewrite /inactive_unchanged; smt(). qed.

lemma put_block8192_get32 a k b i :
  0 <= k < 8 => 0 <= i < 2048 =>
  BArray8192.get32 (put_block8192 a k b) i =
    if 256*k <= i < 256*(k+1) then BArray1024.get32 b (i-256*k)
    else BArray8192.get32 a i.
proof.
move=> hk hi; apply W4u8.wordP => byte hb.
rewrite BArray8192.get32d_byte 1:hb.
rewrite put_block8192_get8 1:/#.
case (256*k <= i < 256*(k+1)) => hm.
+ have -> : 1024*k <= 4*i+byte < 1024*(k+1) by smt().
  rewrite /= BArray1024.get32d_byte 1:hb.
  have -> : 4*i+byte-1024*k=4*(i-256*k)+byte by ring.
  trivial.
+ have -> : !(1024*k <= 4*i+byte < 1024*(k+1)) by smt().
  by rewrite /= BArray8192.get32d_byte.
qed.

lemma put_block8192_set32 a k b i w :
  0 <= k < 8 => 0 <= i < 256 =>
  BArray8192.set32 (put_block8192 a k b) (256*k+i) w =
    put_block8192 a k (BArray1024.set32 b i w).
proof.
move=> hk hi; apply BArray8192.ext_eq32 => j hj.
have hjj : 0<=j<2048 by smt().
rewrite BArray8192.get_set32E 1:/# 1:/#.
rewrite !put_block8192_get32 1:hk 1:hjj 1:hk 1:hjj.
case (256*k <= j < 256*(k+1)) => hm.
+ rewrite BArray1024.get_set32E 1:/# 1:/#.
  smt().
+ smt().
qed.

lemma block8192_set32 a k i w :
  0 <= k < 8 => 0 <= i < 2048 =>
  block8192 (BArray8192.set32 a i w) k =
    if 256*k <= i < 256*(k+1)
    then BArray1024.set32 (block8192 a k) (i-256*k) w
    else block8192 a k.
proof.
move=> hk hi; apply BArray1024.ext_eq32 => j hj.
have hjj : 0<=j<256 by smt().
rewrite block8192_get32 1:hjj BArray8192.get_set32E 1:/# 1:/#.
case (256*k <= i < 256*(k+1)) => hm.
+ rewrite BArray1024.get_set32E 1:/# 1:/# block8192_get32 1:hjj.
  smt().
+ rewrite block8192_get32 1:hjj; smt().
qed.

lemma put_block8192_preserves_tail a k b n :
  0<=k<n => n<=8 => inactive_unchanged a (put_block8192 a k b) n.
proof.
move=> hkn hn; rewrite /inactive_unchanged => j hj.
rewrite put_block8192_get8 1:/#; smt().
qed.

end NTTVectorSpec.
