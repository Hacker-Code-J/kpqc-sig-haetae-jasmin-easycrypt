require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

require import KeygenMode2ParentTarget HpolyTarget
               SBArray8192_1024 Array256 KeygenM23MatrixSpec
               KeygenM23ArithmeticSpec NTT_Fq.

theory TargetKeygenM23WideSupport.

module Parent = KeygenMode2ParentTarget.M.
module Single = HpolyTarget.M.

op poly_slice (a : BArray8192.t) (base : int) : BArray1024.t =
  SBArray8192_1024.get_sub32 a base.

op put_poly_slice
    (a : BArray8192.t) (base : int) (p : BArray1024.t) :
    BArray8192.t =
  SBArray8192_1024.set_sub32 a base p.

op poly_slice_frame
    (before after : BArray8192.t) (base : int) : bool =
  forall i,
    0 <= i < KeygenM23MatrixSpec.array_words_i =>
    (i < base \/
     base + KeygenM23MatrixSpec.poly_words_i <= i) =>
    BArray8192.get32 after i = BArray8192.get32 before i.

lemma int_shr1_div2 x :
  0 <= x =>
  x `|>>` 1 = x %/ 2.
proof.
move=> hx.
by rewrite /(`|>>`) /(`<<`) /=.
qed.

lemma poly_slice_get32 (a : BArray8192.t) base i :
  0 <= base /\
  base + KeygenM23MatrixSpec.poly_words_i <=
    KeygenM23MatrixSpec.array_words_i =>
  0 <= i < KeygenM23MatrixSpec.poly_words_i =>
  BArray1024.get32 (poly_slice a base) i =
    BArray8192.get32 a (base + i).
proof.
move=> hbase hi.
rewrite /poly_slice.
rewrite SBArray8192_1024.get32d_get_sub 1:/#.
congr.
ring.
qed.

lemma poly_slice_set32
    (a : BArray8192.t) base i w :
  0 <= base /\
  base + KeygenM23MatrixSpec.poly_words_i <=
    KeygenM23MatrixSpec.array_words_i =>
  0 <= i < KeygenM23MatrixSpec.poly_words_i =>
  poly_slice
    (BArray8192.set32 a (base + i) w) base =
  BArray1024.set32 (poly_slice a base) i w.
proof.
move=> hbase hi.
apply BArray1024.ext_eq32 => x hx.
rewrite !BArray1024.get_set32E 1:/# 1:/#.
rewrite poly_slice_get32 1:hbase 1:/#.
rewrite BArray8192.get_set32E 1:/# 1:/#.
rewrite poly_slice_get32 1:hbase 1:/#.
have -> : (base + i = base + x) = (i = x) by smt().
trivial.
qed.

lemma wide_slice_poly_repr_bound
    (a : BArray8192.t) base (p : Rq.poly) sz :
  0 <= base /\
  base + KeygenM23MatrixSpec.poly_words_i <=
    KeygenM23MatrixSpec.array_words_i =>
  (KeygenM23ArithmeticSpec.wide_slice_repr_bound a base p sz <=>
   NTT_Fq.poly_repr_bound (poly_slice a base) p sz).
proof.
move=> hbase.
split.
+ move=> [hp hbound].
  split.
  + rewrite /NTT_Fq.poly_repr.
    apply/Array256.ext_eq => j hj.
    have hj' :
        0 <= j < KeygenM23MatrixSpec.poly_words_i.
    * rewrite /KeygenM23MatrixSpec.poly_words_i.
      exact hj.
    rewrite hp.
    rewrite KeygenM23ArithmeticSpec.wide_poly_get 1:hj'.
    rewrite /NTT_Fq.barray256_to_poly Array256.initiE 1:/# /=.
    rewrite poly_slice_get32 1:hbase 1:hj'.
    trivial.
  + rewrite /NTT_Fq.barray256_bound.
    move=> j /mem_range hj.
    have hj' :
        0 <= j < KeygenM23MatrixSpec.poly_words_i.
    * rewrite /KeygenM23MatrixSpec.poly_words_i.
      exact hj.
    rewrite poly_slice_get32 1:hbase 1:hj'.
    exact (hbound j hj').
+ move=> [hrepr hbound].
  split.
  + apply/Array256.ext_eq => j hj.
    have hj' :
        0 <= j < KeygenM23MatrixSpec.poly_words_i.
    * rewrite /KeygenM23MatrixSpec.poly_words_i.
      exact hj.
    have hjrange : j \in range 0 256.
    * by rewrite mem_range.
    have hget :=
      NTT_Fq.poly_repr_get
        (poly_slice a base) p j hrepr hjrange.
    rewrite KeygenM23ArithmeticSpec.wide_poly_get 1:hj'.
    rewrite poly_slice_get32 1:hbase 1:hj' in hget.
    exact hget.
  + rewrite /KeygenM23ArithmeticSpec.wide_slice_bound.
    move=> j hj.
    have hjrange : j \in range 0 256.
    * rewrite mem_range.
      rewrite /KeygenM23MatrixSpec.poly_words_i in hj.
      exact hj.
    have hget := hbound j hjrange.
    rewrite poly_slice_get32 1:hbase 1:hj in hget.
    exact hget.
qed.

lemma put_poly_slice_get32_in
    (a : BArray8192.t) base (p : BArray1024.t) i :
  0 <= base /\
  base + KeygenM23MatrixSpec.poly_words_i <=
    KeygenM23MatrixSpec.array_words_i =>
  0 <= i < KeygenM23MatrixSpec.poly_words_i =>
  BArray8192.get32 (put_poly_slice a base p) (base + i) =
    BArray1024.get32 p i.
proof.
move=> hbase hi.
rewrite /put_poly_slice.
rewrite SBArray8192_1024.get32d_set_sub_in 1:/#.
congr.
ring.
qed.

lemma put_poly_slice_get32_out
    (a : BArray8192.t) base (p : BArray1024.t) i :
  0 <= base /\
  base + KeygenM23MatrixSpec.poly_words_i <=
    KeygenM23MatrixSpec.array_words_i =>
  0 <= i < KeygenM23MatrixSpec.array_words_i =>
  (i < base \/
   base + KeygenM23MatrixSpec.poly_words_i <= i) =>
  BArray8192.get32 (put_poly_slice a base p) i =
    BArray8192.get32 a i.
proof.
move=> hbase hi hout.
rewrite /put_poly_slice.
rewrite SBArray8192_1024.get32d_set_sub_out 1:/#.
trivial.
qed.

lemma poly_slice_put_same
    (a : BArray8192.t) base (p : BArray1024.t) :
  0 <= base /\
  base + KeygenM23MatrixSpec.poly_words_i <=
    KeygenM23MatrixSpec.array_words_i =>
  poly_slice (put_poly_slice a base p) base = p.
proof.
move=> hbase.
apply BArray1024.ext_eq32 => i hi.
rewrite poly_slice_get32 1:hbase 1:/#.
rewrite put_poly_slice_get32_in 1:hbase 1:/#.
trivial.
qed.

lemma poly_slice_put_other
    (a : BArray8192.t) base other (p : BArray1024.t) :
  0 <= base /\
  base + KeygenM23MatrixSpec.poly_words_i <=
    KeygenM23MatrixSpec.array_words_i =>
  0 <= other /\
  other + KeygenM23MatrixSpec.poly_words_i <=
    KeygenM23MatrixSpec.array_words_i =>
  (other + KeygenM23MatrixSpec.poly_words_i <= base \/
   base + KeygenM23MatrixSpec.poly_words_i <= other) =>
  poly_slice (put_poly_slice a base p) other =
    poly_slice a other.
proof.
move=> hbase hother hdisjoint.
apply BArray1024.ext_eq32 => i hi.
rewrite !poly_slice_get32 1:hother 1:/# 1:hother 1:/#.
rewrite put_poly_slice_get32_out 1:hbase 1:/# 1:/#.
trivial.
qed.

lemma poly_slice_frame_refl a base :
  poly_slice_frame a a base.
proof.
by rewrite /poly_slice_frame.
qed.

lemma poly_slice_frame_set32
    before current base i w :
  0 <= base /\
  base + KeygenM23MatrixSpec.poly_words_i <=
    KeygenM23MatrixSpec.array_words_i =>
  0 <= i < KeygenM23MatrixSpec.poly_words_i =>
  poly_slice_frame before current base =>
  poly_slice_frame
    before (BArray8192.set32 current (base + i) w) base.
proof.
rewrite /poly_slice_frame.
move=> hbase hi hframe x hx hout.
rewrite BArray8192.get_set32E 1:/# 1:/#.
have hne : base + i <> x by smt().
rewrite ifF 1:/#.
exact (hframe x hx hout).
qed.

lemma poly_slice_frame_put
    before base (p : BArray1024.t) :
  0 <= base /\
  base + KeygenM23MatrixSpec.poly_words_i <=
    KeygenM23MatrixSpec.array_words_i =>
  poly_slice_frame before (put_poly_slice before base p) base.
proof.
rewrite /poly_slice_frame.
move=> hbase i hi hout.
exact (put_poly_slice_get32_out before base p i hbase hi hout).
qed.

lemma poly_slice_reassemble
    before current base (p : BArray1024.t) :
  0 <= base /\
  base + KeygenM23MatrixSpec.poly_words_i <=
    KeygenM23MatrixSpec.array_words_i =>
  poly_slice current base = p =>
  poly_slice_frame before current base =>
  current = put_poly_slice before base p.
proof.
move=> hbase hslice hframe.
apply BArray8192.ext_eq32 => i hi.
have hiword :
    0 <= i < KeygenM23MatrixSpec.array_words_i.
+ rewrite /KeygenM23MatrixSpec.array_words_i.
  smt().
case (base <= i <
      base + KeygenM23MatrixSpec.poly_words_i) => hin.
+ have hs :
      BArray1024.get32 (poly_slice current base) (i - base) =
      BArray1024.get32 p (i - base).
  + by rewrite hslice.
  rewrite poly_slice_get32 1:hbase 1:/# in hs.
  have hilocal :
      0 <= i - base < KeygenM23MatrixSpec.poly_words_i by smt().
  have hput :=
    put_poly_slice_get32_in before base p (i - base)
      hbase hilocal.
  smt().
+ have hout :
      i < base \/
      base + KeygenM23MatrixSpec.poly_words_i <= i by smt().
  have hput :=
    put_poly_slice_get32_out before base p i
      hbase hiword hout.
  have hcur := hframe i hiword hout.
  by rewrite hcur hput.
qed.

lemma word_tail_frame_put_before
    before current base words (p : BArray1024.t) :
  0 <= base /\
  base + KeygenM23MatrixSpec.poly_words_i <= words =>
  words <= KeygenM23MatrixSpec.array_words_i =>
  KeygenM23MatrixSpec.word_tail_frame before current words =>
  KeygenM23MatrixSpec.word_tail_frame
    before (put_poly_slice current base p) words.
proof.
rewrite /KeygenM23MatrixSpec.word_tail_frame.
move=> hbase hwords hframe i hi.
rewrite put_poly_slice_get32_out 1:/# 1:/# 1:/#.
exact (hframe i hi).
qed.

lemma parent_single_fqmul_equiv :
  equiv [Parent.__fqmul ~ Single.__fqmul :
    ={a, b} ==> ={res}].
proof.
proc.
inline Parent.__montgomery_reduce Single.__montgomery_reduce.
sim.
qed.

end TargetKeygenM23WideSupport.
