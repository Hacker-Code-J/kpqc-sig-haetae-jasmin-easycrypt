require import AllCore IntDiv List StdOrder.
from Jasmin require import JModel_x86.
require import NTTMatrixTarget ApiTarget BArray8192 BArray1024 NTTVectorSpec NTT_Fq Rq GFq Array256 Fq NTTVectorTotal NTTFullSpec NTTMatrixCorrectness.
import IntOrder NTTVectorSpec Zq.

theory NTTMatrixProductCorrectness.

module Matrix = NTTMatrixTarget.M.
module Api = ApiTarget.M(ApiTarget.Syscall).

lemma matrix_ntt_equiv :
  equiv[Matrix._polyvec_ntt ~ Api._polyvec_ntt : ={xp,count} ==> ={res}].
proof.
proc; inline Matrix.__fqmul Api.__fqmul Matrix.__montgomery_reduce Api.__montgomery_reduce; sim.
qed.

lemma matrix_invntt_equiv :
  equiv[Matrix._polyvec_invntt ~ Api._polyvec_invntt : ={xp,count} ==> ={res}].
proof.
proc; inline Matrix.__fqmul Api.__fqmul Matrix.__montgomery_reduce Api.__montgomery_reduce; sim.
qed.

lemma matrix_acc_equiv :
  equiv[Matrix._polymat_pointwise_acc ~ Api._polymat_pointwise_acc :
    ={tp,mp,vp,rows,cols} ==> ={res}].
proof.
proc; inline Matrix.__fqmul Api.__fqmul Matrix.__montgomery_reduce Api.__montgomery_reduce; sim.
qed.

op copied_prefix (before source current:BArray8192.t) (n:int) =
  (forall i, 0<=i<n => BArray8192.get32 current i=BArray8192.get32 source i) /\
  (forall j, 4*n<=j<8192 => BArray8192.get8 current j=BArray8192.get8 before j).

lemma copied_prefix_step before source current n :
  0<=n<2048 => copied_prefix before source current n =>
  copied_prefix before source
    (BArray8192.set32 current n (BArray8192.get32 source n)) (n+1).
proof.
move=> hn [hp hf]; split.
+ move=> i hi; rewrite BArray8192.get_set32E 1:/# 1:/#.
  case (i=n) => [-> // | hne]; smt().
move=> j hj; rewrite BArray8192.get8_set32dE.
have -> : !(4*n<=j<4*n+4 /\ 0<=j<8192) by smt().
smt().
qed.

lemma matrix_copy_correct before source n :
  0<=n<=2048 =>
  hoare[Matrix._keypair_copy_vec :
    rp=before /\ ap=source /\ count=W64.of_int n ==>
    copied_prefix before source res n].
proof.
move=> hn; proc.
while (ap=source /\ count=W64.of_int n /\ 0<=W64.to_uint i<=n /\
       copied_prefix before source rp (W64.to_uint i)).
+ auto => /> &hr hi0 hin hp hf hguard.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  have hi : W64.to_uint i{hr}<n by smt(modz_small).
  rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  have hc : copied_prefix before source rp{hr} (W64.to_uint i{hr}) by split.
  have hs := copied_prefix_step before source rp{hr} (W64.to_uint i{hr}) _ hc.
  + smt().
  move: hs; rewrite /copied_prefix; smt().
auto => />.
split; first smt().
move=> i current hdone hi0 hin hp hf.
rewrite W64.ultE W64.of_uintK /= in hdone.
have he : W64.to_uint i=n by smt(modz_small).
move: hp hf; rewrite he; smt().
qed.

lemma matrix_copy_ll : islossless Matrix._keypair_copy_vec.
proof.
proc.
while (W64.to_uint i<=W64.to_uint count) (W64.to_uint count-W64.to_uint i).
+ move=> z; auto => /> &hr hi hguard.
  have /= hn := W64.to_uint_cmp count{hr}.
  rewrite W64.ultE in hguard.
  rewrite W64.to_uintD_small 1:W64.to_uint1 1:/# W64.to_uint1; smt().
auto => /> &hr; split; first smt(W64.to_uint_cmp).
move=> i hi hvariant; rewrite W64.ultE; smt().
qed.

lemma matrix_copy_total before source n :
  0<=n<=2048 =>
  phoare[Matrix._keypair_copy_vec :
    rp=before /\ ap=source /\ count=W64.of_int n ==>
    copied_prefix before source res n] = 1%r.
proof.
move=> hn.
by conseq matrix_copy_ll (matrix_copy_correct before source n hn).
qed.

lemma copied_vector_repr before source current ps count sz :
  vector_repr source ps count sz => copied_prefix before source current (256*count) =>
  vector_repr current ps count sz /\ inactive_unchanged before current count.
proof.
move=> [hn [hsize hs]] [hp hf]; split.
+ rewrite /vector_repr; split; first exact hn.
  split; first exact hsize.
  move=> k hk.
  have he : block8192 current k=block8192 source k.
  + apply BArray1024.ext_eq32 => i hi.
    rewrite !block8192_get32 1,2:/#; apply hp; smt().
  rewrite he; exact (hs k hk).
rewrite /inactive_unchanged => j hj; apply hf; smt().
qed.

module Composition = {
  proc copy_ntt(dstp:BArray8192.t, srcp:BArray8192.t, count:W64.t) : BArray8192.t = {
    dstp <@ Matrix._keypair_copy_vec(dstp,srcp,count*W64.of_int 256);
    dstp <@ Api._polyvec_ntt(dstp,count);
    return dstp;
  }
  proc m5(bp:BArray8192.t, s1hatp:BArray8192.t, ap:BArray32768.t,
          s1p:BArray8192.t, rows:W64.t, cols:W64.t) : BArray8192.t*BArray8192.t = {
    s1hatp <@ copy_ntt(s1hatp,s1p,cols);
    bp <@ Api._polymat_pointwise_acc(bp,ap,s1hatp,rows,cols);
    return (bp,s1hatp);
  }
  proc m23(bp:BArray8192.t, s1hatp:BArray8192.t, ap:BArray32768.t,
           s1p:BArray8192.t, rows:W64.t, cols:W64.t) : BArray8192.t*BArray8192.t = {
    var pair:BArray8192.t*BArray8192.t;
    pair <@ m5(bp,s1hatp,ap,s1p,rows,cols);
    bp <- pair.`1;
    s1hatp <- pair.`2;
    bp <@ Api._polyvec_invntt(bp,rows);
    return (bp,s1hatp);
  }
}.

lemma copy_ntt_export_equiv :
  equiv[Matrix.keypair_copy_ntt_jazz ~ Composition.copy_ntt :
    ={dstp,srcp,count} ==> ={res}].
proof.
proc; call matrix_ntt_equiv; wp.
call (_ : ={rp,ap,count} ==> ={res}); first by sim.
auto => />.
qed.

lemma matrix_m23_export_equiv :
  equiv[Matrix.keypair_m23_matrix_jazz ~ Composition.m23 :
    ={bp,s1hatp,ap,s1p,rows,cols} ==> ={res}].
proof.
proc; inline {2} Composition.m5 Composition.copy_ntt; wp; call matrix_invntt_equiv; wp.
call matrix_acc_equiv; wp.
call matrix_ntt_equiv; wp.
call (_ : ={rp,ap,count} ==> ={res}); first by sim.
auto => />.
qed.

lemma matrix_m5_export_equiv :
  equiv[Matrix.keypair_m5_matrix_jazz ~ Composition.m5 :
    ={bp,s1hatp,ap,s1p,rows,cols} ==> ={res}].
proof.
proc; inline {2} Composition.copy_ntt; wp; call matrix_acc_equiv; wp.
call matrix_ntt_equiv; wp.
call (_ : ={rp,ap,count} ==> ={res}); first by sim.
auto => />.
qed.

op canonical_matrix (ap:BArray32768.t) (rows cols:int) =
  0<=rows<=8 /\ 0<=cols<=8 /\ rows*cols<=32 /\
  forall i, 0<=i<256*rows*cols => 0<=W32.to_sint (BArray32768.get32 ap i)<64513.

op matrix_dot (ap:BArray32768.t) (ps:Rq.poly list) (cols row:int) : Rq.poly =
  Array256.init (fun j => Rq.BigDom.BAdd.bigi predT
    (fun c => NTT_Fq.word_to_coeff (BArray32768.get32 ap (256*(row*cols+c)+j)) *
      (nth Rq.zero ps c).[j] * inv NTT_Fq.R) 0 cols).

op matrix_image (ap:BArray32768.t) (ps:Rq.poly list) (rows cols:int) : Rq.poly list =
  mkseq (fun row => matrix_dot ap ps cols row) rows.

lemma matrix_image_size ap ps rows cols : 0<=rows => size (matrix_image ap ps rows cols)=rows.
proof. by move=> hr; rewrite /matrix_image size_mkseq /#. qed.

lemma matrix_image_get ap ps rows cols row : 0<=row<rows =>
  nth Rq.zero (matrix_image ap ps rows cols) row=matrix_dot ap ps cols row.
proof. by move=> hr; rewrite /matrix_image nth_mkseq. qed.

lemma matrix_dotE ap ps cols row j : 0<=j<256 =>
  (matrix_dot ap ps cols row).[j]=Rq.BigDom.BAdd.bigi predT
    (fun c => NTT_Fq.word_to_coeff (BArray32768.get32 ap (256*(row*cols+c)+j)) *
      (nth Rq.zero ps c).[j] * inv NTT_Fq.R) 0 cols.
proof. by move=> hj; rewrite /matrix_dot Array256.initiE. qed.

lemma vector_repr_coeff vp ps count sz c j :
  vector_repr vp ps count sz => 0<=c<count => 0<=j<256 =>
  (nth Rq.zero ps c).[j]=NTT_Fq.word_to_coeff (BArray8192.get32 vp (256*c+j)) /\
  Fq.bw32 (BArray8192.get32 vp (256*c+j)) sz.
proof.
move=> [hn [hs hv]] hc hj.
have h := NTT_Fq.poly_repr_bound_get _ _ _ j (hv c hc) _.
+ by rewrite mem_range.
move: h; rewrite block8192_get32 1:hj; trivial.
qed.

lemma vector_repr_flat_bound vp ps count sz i :
  vector_repr vp ps count sz => 0<=i<256*count =>
  Fq.bw32 (BArray8192.get32 vp i) sz.
proof.
move=> hv hi.
have hc : 0<=i%/256<count by rewrite divz_ge0 1:/# ltz_divLR 1:/#; smt().
have hj : 0<=i%%256<256 by smt(modz_ge0 ltz_pmod).
have [he hb] := vector_repr_coeff vp ps count sz (i%/256) (i%%256) hv hc hj.
have hid : 256*(i%/256)+i%%256=i by smt(divz_eq).
by move: hb; rewrite hid.
qed.

lemma matrix_copy_vector_total_pre before source ps n sz :
  0<=n<=8 =>
  phoare[Matrix._keypair_copy_vec :
    rp=before /\ ap=source /\ count=W64.of_int (256*n) /\
    vector_repr source ps n sz ==>
    vector_repr res ps n sz /\ inactive_unchanged before res n] = 1%r.
proof.
move=> hn.
have hcoeffs : 0<=256*n<=2048 by smt().
have hh : hoare[Matrix._keypair_copy_vec :
    rp=before /\ ap=source /\ count=W64.of_int (256*n) /\
    vector_repr source ps n sz ==>
    vector_repr res ps n sz /\ inactive_unchanged before res n].
+ conseq (matrix_copy_correct before source (256*n) hcoeffs).
  + smt().
  move=> &hr [hr [ha [hc hv]]] result hp.
  exact (copied_vector_repr before source result ps n sz hv hp).
by conseq matrix_copy_ll hh.
qed.

lemma copy_ntt_composition_total before source ps n :
  vector_repr source ps n 16 =>
  phoare[Composition.copy_ntt :
    dstp=before /\ srcp=source /\ count=W64.of_int n ==>
    vector_repr res (List.map NTTFullSpec.full_ntt ps) n 24 /\
    inactive_unchanged before res n] = 1%r.
proof.
move=> hv.
have hn : 0<=n<=8 by move: hv; rewrite /vector_repr; smt().
proc.
ecall (NTTVectorTotal.api_vector_ntt_total_pre dstp ps n).
ecall (matrix_copy_vector_total_pre before source ps n 16 hn).
wp; skip.
move=> &hr /= [hd [hs hc]].
rewrite hd hs hc W64.of_intM.
have hcount : n*256=256*n by ring.
rewrite hcount.
split; first smt().
move=> _ copied [hcop hframe].
split; first smt().
move=> _ transformed [htrans hframe2].
split; first exact htrans.
exact (inactive_unchanged_trans before copied transformed n hframe hframe2).
call matrix_copy_ll; auto.
qed.

lemma copy_ntt_export_total before source ps n :
  vector_repr source ps n 16 =>
  phoare[Matrix.keypair_copy_ntt_jazz :
    dstp=before /\ srcp=source /\ count=W64.of_int n ==>
    vector_repr res (List.map NTTFullSpec.full_ntt ps) n 24 /\
    inactive_unchanged before res n] = 1%r.
proof.
move=> hv.
conseq copy_ntt_export_equiv (copy_ntt_composition_total before source ps n hv).
+ move=> &m [hd [hs hc]]; exists (before,source,W64.of_int n); smt().
+ smt().
qed.

lemma matrix_dot_from_words ap vp ps cols row j sz :
  vector_repr vp ps cols sz => 0<=j<256 =>
  (matrix_dot ap ps cols row).[j]=Rq.BigDom.BAdd.bigi predT
    (fun c => NTT_Fq.word_to_coeff (BArray32768.get32 ap (256*(row*cols+c)+j)) *
      NTT_Fq.word_to_coeff (BArray8192.get32 vp (256*c+j)) * inv NTT_Fq.R) 0 cols.
proof.
move=> hv hj; rewrite matrix_dotE 1:hj.
apply Rq.BigDom.BAdd.eq_big_int => c hc /=.
have [he hb] := vector_repr_coeff vp ps cols sz c j hv hc hj.
by rewrite he.
qed.

lemma matrix_output_from_coefficients current ap ps rows cols :
  0<=rows<=8 =>
  (forall r j, 0<=r<rows => 0<=j<256 =>
    Fq.bw32 (BArray8192.get32 current (256*r+j)) 18 /\
    NTT_Fq.word_to_coeff (BArray8192.get32 current (256*r+j)) =
      (matrix_dot ap ps cols r).[j]) =>
  vector_repr current (matrix_image ap ps rows cols) rows 18.
proof.
move=> hr hcoef; rewrite /vector_repr.
split; first exact hr.
split; first by rewrite matrix_image_size /#.
move=> r hrow; rewrite matrix_image_get 1:hrow.
rewrite /NTT_Fq.poly_repr_bound /NTT_Fq.poly_repr; split.
+ apply Array256.ext_eq => j hj.
  rewrite NTT_Fq.barray256_to_polyE 1:mem_range 1:hj block8192_get32 1:hj.
  have [hb he] := hcoef r j hrow hj; exact he.
rewrite /NTT_Fq.barray256_bound => j /mem_range hj.
rewrite block8192_get32 1:hj.
have [hb he] := hcoef r j hrow hj; exact hb.
qed.

lemma matrix_inputs_from_repr ap vp ps rows cols :
  canonical_matrix ap rows cols => vector_repr vp ps cols 24 =>
  NTTMatrixCorrectness.matrix_inputs ap vp rows cols.
proof.
move=> [hr [hc [hsize ha]]] hv.
rewrite /NTTMatrixCorrectness.matrix_inputs.
split; first exact hr.
split; first exact hc.
split; first exact hsize.
split; first exact ha.
move=> i hi.
have h:=vector_repr_flat_bound vp ps cols 24 i hv hi.
by move: h; rewrite /Fq.bw32 /=; smt().
qed.

lemma matrix_acc_vector_total_pre before ap0 vp0 ps nr nc :
  canonical_matrix ap0 nr nc =>
  phoare[Api._polymat_pointwise_acc :
    tp=before /\ mp=ap0 /\ vp=vp0 /\ rows=W64.of_int nr /\ cols=W64.of_int nc /\
    vector_repr vp0 ps nc 24 ==>
    vector_repr res (matrix_image ap0 ps nr nc) nr 18 /\
    inactive_unchanged before res nr] = 1%r.
proof.
move=> hm; case (vector_repr vp0 ps nc 24) => hv.
+ have hi:=matrix_inputs_from_repr ap0 vp0 ps nr nc hm hv.
  have hh : hoare[Api._polymat_pointwise_acc :
    tp=before /\ mp=ap0 /\ vp=vp0 /\ rows=W64.of_int nr /\ cols=W64.of_int nc /\
    vector_repr vp0 ps nc 24 ==>
    vector_repr res (matrix_image ap0 ps nr nc) nr 18 /\
    inactive_unchanged before res nr].
  + conseq (NTTMatrixCorrectness.polymat_pointwise_correct before ap0 vp0 nr nc hi).
    + smt().
    move=> &hr _ result hp.
    have [hcoef hf] := NTTMatrixCorrectness.completed_rows_field before result ap0 vp0 nr nc hi hp.
    split; last exact hf.
    apply (matrix_output_from_coefficients result ap0 ps nr nc).
    + by move: hm; rewrite /canonical_matrix; smt().
    move=> r j hr hj.
    have [hb he] := hcoef r j hr hj; split; first exact hb.
    rewrite he (matrix_dot_from_words ap0 vp0 ps nc r j 24 hv hj).
    by rewrite /NTTMatrixCorrectness.matrix_field_dot.
  by conseq NTTMatrixCorrectness.polymat_pointwise_ll hh.
+ by exfalso => /#.
qed.

lemma matrix_m5_composition_total before beforehat ap0 source ps nr nc :
  canonical_matrix ap0 nr nc => vector_repr source ps nc 16 =>
  phoare[Composition.m5 :
    bp=before /\ s1hatp=beforehat /\ ap=ap0 /\ s1p=source /\
    rows=W64.of_int nr /\ cols=W64.of_int nc ==>
    vector_repr res.`1 (matrix_image ap0 (List.map NTTFullSpec.full_ntt ps) nr nc) nr 18 /\
    vector_repr res.`2 (List.map NTTFullSpec.full_ntt ps) nc 24 /\
    inactive_unchanged before res.`1 nr /\ inactive_unchanged beforehat res.`2 nc] = 1%r.
proof.
move=> hm hv.
conseq (_ : _ ==> _ : >=1%r) => //.
proc.
seq 1 : (bp=before /\ ap=ap0 /\ rows=W64.of_int nr /\ cols=W64.of_int nc /\
  vector_repr s1hatp (List.map NTTFullSpec.full_ntt ps) nc 24 /\
  inactive_unchanged beforehat s1hatp nc) => //.
+ conseq (_ : _ ==> _ : =1%r) => //.
  call (copy_ntt_composition_total beforehat source ps nc hv).
  wp; skip; smt().
conseq (_ : _ ==> _ : =1%r) => //.
ecall (matrix_acc_vector_total_pre before ap0 s1hatp (List.map NTTFullSpec.full_ntt ps) nr nc hm).
wp; skip.
move=> &hr [hb [ha [hr [hc [hhat hf]]]]].
rewrite hb ha hr hc /=.
split; first smt().
move=> _ result [hout hframe].
by split; [exact hout|split; [exact hhat|split]].
qed.

lemma matrix_m23_composition_total before beforehat ap0 source ps nr nc :
  canonical_matrix ap0 nr nc => vector_repr source ps nc 16 =>
  phoare[Composition.m23 :
    bp=before /\ s1hatp=beforehat /\ ap=ap0 /\ s1p=source /\
    rows=W64.of_int nr /\ cols=W64.of_int nc ==>
    vector_repr res.`1
      (List.map NTTVectorTotal.inverse_value
        (matrix_image ap0 (List.map NTTFullSpec.full_ntt ps) nr nc)) nr 16 /\
    vector_repr res.`2 (List.map NTTFullSpec.full_ntt ps) nc 24 /\
    inactive_unchanged before res.`1 nr /\ inactive_unchanged beforehat res.`2 nc] = 1%r.
proof.
move=> hm hv.
conseq (_ : _ ==> _ : >=1%r) => //.
proc.
seq 1 : (rows=W64.of_int nr /\
    vector_repr pair.`1 (matrix_image ap0 (List.map NTTFullSpec.full_ntt ps) nr nc) nr 18 /\
    vector_repr pair.`2 (List.map NTTFullSpec.full_ntt ps) nc 24 /\
    inactive_unchanged before pair.`1 nr /\ inactive_unchanged beforehat pair.`2 nc) => //.
+ conseq (_ : _ ==> _ : =1%r) => //.
  call (matrix_m5_composition_total before beforehat ap0 source ps nr nc hm hv).
  wp; skip; smt().
conseq (_ : _ ==> _ : =1%r) => //.
ecall (NTTVectorTotal.api_vector_invntt_total18_pre pair.`1
  (matrix_image ap0 (List.map NTTFullSpec.full_ntt ps) nr nc) nr).
wp; skip.
move=> &hr [hr [hinput [hhat [hf hfhat]]]].
rewrite hr /=.
split; first smt().
move=> _ result [hout hframe].
split; first exact hout.
split; first exact hhat.
split; last exact hfhat.
exact (inactive_unchanged_trans before pair{hr}.`1 result nr hf hframe).
qed.

lemma matrix_m5_export_total before beforehat ap0 source ps nr nc :
  canonical_matrix ap0 nr nc => vector_repr source ps nc 16 =>
  phoare[Matrix.keypair_m5_matrix_jazz :
    bp=before /\ s1hatp=beforehat /\ ap=ap0 /\ s1p=source /\
    rows=W64.of_int nr /\ cols=W64.of_int nc ==>
    vector_repr res.`1 (matrix_image ap0 (List.map NTTFullSpec.full_ntt ps) nr nc) nr 18 /\
    vector_repr res.`2 (List.map NTTFullSpec.full_ntt ps) nc 24 /\
    inactive_unchanged before res.`1 nr /\ inactive_unchanged beforehat res.`2 nc] = 1%r.
proof.
move=> hm hv.
conseq matrix_m5_export_equiv (matrix_m5_composition_total before beforehat ap0 source ps nr nc hm hv).
+ move=> &m [hb [hh [ha [hs [hr hc]]]]].
  exists (before,beforehat,ap0,source,W64.of_int nr,W64.of_int nc); smt().
+ smt().
qed.

lemma matrix_m23_export_total before beforehat ap0 source ps nr nc :
  canonical_matrix ap0 nr nc => vector_repr source ps nc 16 =>
  phoare[Matrix.keypair_m23_matrix_jazz :
    bp=before /\ s1hatp=beforehat /\ ap=ap0 /\ s1p=source /\
    rows=W64.of_int nr /\ cols=W64.of_int nc ==>
    vector_repr res.`1
      (List.map NTTVectorTotal.inverse_value
        (matrix_image ap0 (List.map NTTFullSpec.full_ntt ps) nr nc)) nr 16 /\
    vector_repr res.`2 (List.map NTTFullSpec.full_ntt ps) nc 24 /\
    inactive_unchanged before res.`1 nr /\ inactive_unchanged beforehat res.`2 nc] = 1%r.
proof.
move=> hm hv.
conseq matrix_m23_export_equiv (matrix_m23_composition_total before beforehat ap0 source ps nr nc hm hv).
+ move=> &m [hb [hh [ha [hs [hr hc]]]]].
  exists (before,beforehat,ap0,source,W64.of_int nr,W64.of_int nc); smt().
+ smt().
qed.

end NTTMatrixProductCorrectness.
