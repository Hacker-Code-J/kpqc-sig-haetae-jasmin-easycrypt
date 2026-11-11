require import AllCore IntDiv List StdOrder StdBigop.
from Jasmin require import JModel_x86.
require import BArray1024 BArray8192 BArray32768 Array256 ApiTarget HpolyTarget
               Fq GFq Rq NTT_Fq NTTCorrectness NTTMontgomeryBounds NTTVectorSpec.
import Ring.IntID IntOrder Bigint.

theory NTTMatrixCorrectness.

module Target = ApiTarget.M(ApiTarget.Syscall).

lemma api_fqmul_equiv :
  equiv [Target.__fqmul ~ HpolyTarget.M.__fqmul : ={a,b} ==> ={res}].
proof.
proc; inline Target.__montgomery_reduce HpolyTarget.M.__montgomery_reduce; sim.
qed.

lemma api_fqmul_correct aa bb :
  hoare [Target.__fqmul :
    W32.to_sint a = aa /\ W32.to_sint b = bb ==>
    W32.to_sint res = Fq.SignedReductions.SREDC (aa*bb)].
proof.
by conseq api_fqmul_equiv (NTTCorrectness.target_fqmul_correct aa bb) => /#.
qed.

lemma api_fqmul_ll : islossless Target.__fqmul.
proof. proc; inline Target.__montgomery_reduce; islossless. qed.

op matrix_inputs (mp:BArray32768.t) (vp:BArray8192.t) (rows cols:int) =
  0<=rows<=8 /\ 0<=cols<=8 /\ rows*cols<=32 /\
  (forall i, 0<=i<256*rows*cols => 0<=W32.to_sint (BArray32768.get32 mp i)<64513) /\
  (forall i, 0<=i<256*cols => -16777216<=W32.to_sint (BArray8192.get32 vp i)<16777216).

op matrix_term (mp:BArray32768.t) (vp:BArray8192.t) (cols row col j:int) =
  Fq.SignedReductions.SREDC
    (W32.to_sint (BArray32768.get32 mp (256*(row*cols+col)+j)) *
     W32.to_sint (BArray8192.get32 vp (256*col+j))).

op matrix_sum (mp:BArray32768.t) (vp:BArray8192.t) (cols row j n:int) =
  BIA.bigi predT (fun c => matrix_term mp vp cols row c j) 0 n.

op completed_rows (initial current:BArray8192.t)
    (mp:BArray32768.t) (vp:BArray8192.t) (cols rows:int) =
  (forall r j, 0<=r<rows => 0<=j<256 =>
    W32.to_sint (BArray8192.get32 current (256*r+j)) = matrix_sum mp vp cols r j cols) /\
  NTTVectorSpec.inactive_unchanged initial current rows.

op initialized_row (initial current:BArray8192.t)
    (mp:BArray32768.t) (vp:BArray8192.t) (cols row n:int) =
  (forall r j, 0<=r<row => 0<=j<256 =>
    W32.to_sint (BArray8192.get32 current (256*r+j)) = matrix_sum mp vp cols r j cols) /\
  (forall j, 0<=j<n => W32.to_sint (BArray8192.get32 current (256*row+j))=0) /\
  (forall j, 4*(256*row+n)<=j<8192 => BArray8192.get8 current j=BArray8192.get8 initial j).

op accumulated_row (initial current:BArray8192.t)
    (mp:BArray32768.t) (vp:BArray8192.t) (cols row col n:int) =
  (forall r j, 0<=r<row => 0<=j<256 =>
    W32.to_sint (BArray8192.get32 current (256*r+j)) = matrix_sum mp vp cols r j cols) /\
  (forall j, 0<=j<256 => W32.to_sint (BArray8192.get32 current (256*row+j)) =
    matrix_sum mp vp cols row j (col + b2i (j<n))) /\
  NTTVectorSpec.inactive_unchanged initial current (row+1).

lemma matrix_sum_zero mp vp cols row j : matrix_sum mp vp cols row j 0=0.
proof. by rewrite /matrix_sum BIA.big_geq. qed.

lemma matrix_sum_step mp vp cols row j n : 0<=n =>
  matrix_sum mp vp cols row j (n+1) =
  matrix_sum mp vp cols row j n + matrix_term mp vp cols row n j.
proof. by move=> hn; rewrite /matrix_sum BIA.big_int_recr //=. qed.

lemma matrix_term_bound mp vp rows cols row col j :
  matrix_inputs mp vp rows cols => 0<=row<rows => 0<=col<cols => 0<=j<256 =>
  -32768<=matrix_term mp vp cols row col j<32768.
proof.
move=> [hrows [hcols [hsize [hm hv]]]] hr hc hj.
have hm' := hm (256*(row*cols+col)+j) _; first by smt().
have hv' := hv (256*col+j) _; first by smt().
have h := NTTMontgomeryBounds.fqmul_canonical24_bounds_congr
 (W32.to_sint (BArray32768.get32 mp (256*(row*cols+col)+j)))
 (W32.to_sint (BArray8192.get32 vp (256*col+j))) hm' hv'.
by rewrite /matrix_term; smt().
qed.

lemma matrix_sum_bound mp vp rows cols row j n :
  matrix_inputs mp vp rows cols => 0<=row<rows => 0<=j<256 => 0<=n<=cols =>
  -32768*n<=matrix_sum mp vp cols row j n<=32767*n.
proof.
move=> inputs hr hj hn.
have hall : forall c, 0<=c<n => -32768<=matrix_term mp vp cols row c j<=32767.
+ move=> c hc; have h:=matrix_term_bound mp vp rows cols row c j inputs hr _ hj; smt().
move: hn hall; elim/natind: n => [n hn hn' hall|n hn ih hn' hall].
+ have hn0 : n=0 by smt().
  by rewrite hn0 matrix_sum_zero; smt().
rewrite matrix_sum_step 1:hn.
have hp:=ih _ _; first 2 by smt().
have ht:=hall n _; smt().
qed.

lemma completed_rows_zero initial mp vp cols :
  completed_rows initial initial mp vp cols 0.
proof. rewrite /completed_rows /NTTVectorSpec.inactive_unchanged; smt(). qed.

lemma initialize_start initial current mp vp cols row :
  completed_rows initial current mp vp cols row =>
  initialized_row initial current mp vp cols row 0.
proof.
rewrite /completed_rows /initialized_row /NTTVectorSpec.inactive_unchanged; smt().
qed.

lemma initialize_step initial current mp vp cols row n :
  0<=row<8 => 0<=n<256 =>
  initialized_row initial current mp vp cols row n =>
  initialized_row initial (BArray8192.set32 current (256*row+n) W32.zero)
    mp vp cols row (n+1).
proof.
move=> hr hn [hold [hzero hframe]]; split.
+ move=> r j hrr hj.
  rewrite BArray8192.get_set32E 1:/# 1:/#.
  have -> : !(256*row+n=256*r+j) by smt().
  exact (hold r j hrr hj).
split.
+ move=> j hj.
  rewrite BArray8192.get_set32E 1:/# 1:/#.
  case (256*row+n=256*row+j) => he.
  + by rewrite /W32.to_sint W32.to_uint0.
  apply hzero; smt().
move=> j hj.
rewrite BArray8192.get8_set32dE.
have -> : !(4*(256*row+n)<=j<4*(256*row+n)+4 /\ 0<=j<8192) by smt().
smt().
qed.

lemma initialize_done initial current mp vp cols row :
  initialized_row initial current mp vp cols row 256 =>
  accumulated_row initial current mp vp cols row 0 0.
proof.
move=> [hold [hzero hframe]]; split; first exact hold.
split.
+ move=> j hj.
  have -> : b2i (j<0)=0 by smt().
  rewrite /= matrix_sum_zero; exact (hzero j hj).
rewrite /NTTVectorSpec.inactive_unchanged; smt().
qed.

lemma accumulate_step initial current mp vp rows cols row col n (w:W32.t) :
  matrix_inputs mp vp rows cols =>
  0<=row<rows => 0<=col<cols => 0<=n<256 =>
  accumulated_row initial current mp vp cols row col n =>
  W32.to_sint w=matrix_term mp vp cols row col n =>
  accumulated_row initial
    (BArray8192.set32 current (256*row+n)
      (BArray8192.get32 current (256*row+n)+w))
    mp vp cols row col (n+1).
proof.
move=> inputs hr hc hn [hold [hcur hframe]] hw.
have hdim : 0<=rows<=8 /\ 0<=cols<=8.
+ by move: inputs; rewrite /matrix_inputs; smt().
have hacc := hcur n hn.
have hnn : b2i (n<n)=0 by smt().
move: hacc; rewrite hnn /=; move=> hacc.
have hb := matrix_sum_bound mp vp rows cols row n col inputs hr hn _; first smt().
have ht := matrix_term_bound mp vp rows cols row col n inputs hr hc hn.
have hadd : W32.to_sint (BArray8192.get32 current (256*row+n)+w)=
 matrix_sum mp vp cols row n (col+1).
+ rewrite W32.to_sintD_small 1:/# hacc /= hw matrix_sum_step 1:/#; ring.
split.
+ move=> r j hrr hj.
  rewrite BArray8192.get_set32E 1:/# 1:/#.
  have -> : !(256*row+n=256*r+j) by smt().
  exact (hold r j hrr hj).
split.
+ move=> j hj.
  rewrite BArray8192.get_set32E 1:/# 1:/#.
  case (256*row+n=256*row+j) => he.
  + have -> : j=n by smt().
    have -> : b2i (n<n+1)=1 by smt().
    exact hadd.
  have hb2 : b2i (j<n+1)=b2i (j<n) by smt().
  rewrite hb2; exact (hcur j hj).
rewrite /NTTVectorSpec.inactive_unchanged => j hj.
rewrite BArray8192.get8_set32dE.
have -> : !(4*(256*row+n)<=j<4*(256*row+n)+4 /\ 0<=j<8192) by smt().
smt().
qed.

lemma accumulate_next_col initial current mp vp cols row col :
  accumulated_row initial current mp vp cols row col 256 =>
  accumulated_row initial current mp vp cols row (col+1) 0.
proof.
move=> [hold [hcur hframe]]; split; first exact hold.
split; last exact hframe.
move=> j hj.
have h:=hcur j hj.
smt().
qed.

lemma accumulate_done initial current mp vp cols row :
  accumulated_row initial current mp vp cols row cols 0 =>
  completed_rows initial current mp vp cols (row+1).
proof.
move=> [hold [hcur hframe]]; split; last exact hframe.
move=> r j hr hj.
case (r=row) => [-> | hne].
+ have h:=hcur j hj.
  smt().
apply hold; smt().
qed.

lemma matrix_index_bound r c n j :
  0<=r<8 => 0<=c<=8 => 0<=n<=8 => 0<=j<256 =>
  0<=256*r*n+256*c+j<18446744073709551616.
proof. smt(). qed.

lemma polymat_pointwise_correct (initial:BArray8192.t) mp0 vp0 nr nc :
  matrix_inputs mp0 vp0 nr nc =>
  hoare [Target._polymat_pointwise_acc :
    tp=initial /\ mp=mp0 /\ vp=vp0 /\ rows=W64.of_int nr /\ cols=W64.of_int nc ==>
    completed_rows initial res mp0 vp0 nc nr].
proof.
move=> inputs.
have hd : 0<=nr<=8 /\ 0<=nc<=8.
+ by move: inputs; rewrite /matrix_inputs; smt().
proc.
while (mp=mp0 /\ vp=vp0 /\ rows=W64.of_int nr /\ cols=W64.of_int nc /\
  0<=W64.to_uint row<=nr /\
  W64.to_uint row_out=256*W64.to_uint row /\
  W64.to_uint row_mat=256*W64.to_uint row*nc /\
  completed_rows initial tp mp0 vp0 nc (W64.to_uint row)).
+ wp.
  while (mp=mp0 /\ vp=vp0 /\ rows=W64.of_int nr /\ cols=W64.of_int nc /\
    0<=W64.to_uint row<nr /\
    W64.to_uint row_out=256*W64.to_uint row /\
    W64.to_uint row_mat=256*W64.to_uint row*nc /\
    0<=W64.to_uint col<=nc /\ W64.to_uint col_off=256*W64.to_uint col /\
    accumulated_row initial tp mp0 vp0 nc (W64.to_uint row) (W64.to_uint col) 0).
  + wp.
    while (mp=mp0 /\ vp=vp0 /\ rows=W64.of_int nr /\ cols=W64.of_int nc /\
      0<=W64.to_uint row<nr /\
      W64.to_uint row_out=256*W64.to_uint row /\
      W64.to_uint row_mat=256*W64.to_uint row*nc /\
      0<=W64.to_uint col<nc /\ W64.to_uint col_off=256*W64.to_uint col /\
      0<=W64.to_uint j<=256 /\
      accumulated_row initial tp mp0 vp0 nc (W64.to_uint row) (W64.to_uint col) (W64.to_uint j)).
    + wp.
      ecall (api_fqmul_correct
        (W32.to_sint (BArray32768.get32 mp0 (256*(W64.to_uint row*nc+W64.to_uint col)+W64.to_uint j)))
        (W32.to_sint (BArray8192.get32 vp0 (256*W64.to_uint col+W64.to_uint j)))).
      auto => /> &hr hr0 hrn hout hmat hc0 hcn hoff hj0 hjn hp hcur hf hg.
      rewrite W64.ultE W64.of_uintK /= in hg.
      have hmo : W64.to_uint (row_mat{hr}+col_off{hr})=256*W64.to_uint row{hr}*nc+256*W64.to_uint col{hr}.
      + rewrite W64.to_uintD_small 1:/# hmat hoff; trivial.
      have hmi : W64.to_uint (row_mat{hr}+col_off{hr}+j{hr})=256*(W64.to_uint row{hr}*nc+W64.to_uint col{hr})+W64.to_uint j{hr}.
      + have hb := matrix_index_bound (W64.to_uint row{hr}) (W64.to_uint col{hr}) nc (W64.to_uint j{hr}) _ _ _ _; first 4 by smt().
        by rewrite !W64.to_uintD hmat hoff modzDml modz_small 1:/= 1:hb; ring.
      have hvi : W64.to_uint (col_off{hr}+j{hr})=256*W64.to_uint col{hr}+W64.to_uint j{hr}.
      + rewrite W64.to_uintD_small 1:/# hoff; trivial.
      have hoi : W64.to_uint (row_out{hr}+j{hr})=256*W64.to_uint row{hr}+W64.to_uint j{hr}.
      + rewrite W64.to_uintD_small 1:/# hout; trivial.
      have hnext : W64.to_uint (j{hr}+W64.one)=W64.to_uint j{hr}+1.
      + rewrite W64.to_uintD_small 1:/# W64.to_uint1; trivial.
      rewrite hmi hvi hoi hnext.
      split; first trivial.
      move=> _ _ result hresult.
      have hpre : accumulated_row initial tp{hr} mp0 vp0 nc
        (W64.to_uint row{hr}) (W64.to_uint col{hr}) (W64.to_uint j{hr}) by split.
      have hs := accumulate_step initial tp{hr} mp0 vp0 nr nc
        (W64.to_uint row{hr}) (W64.to_uint col{hr}) (W64.to_uint j{hr}) result
        inputs _ _ _ hpre _; first 3 by smt().
      + by rewrite /matrix_term.
      move: hs; rewrite /accumulated_row.
      move=> [h1 [h2 h3]].
      split; first smt().
      split.
      + move=> r jj hr1 hr2 hj1 hj2; apply h1; smt().
      split; last exact h3.
      move=> jj hj1 hj2; apply h2; smt().
    auto => /> &hr hr0 hrn hout hmat hc0 hcn hoff hp hcur hf hg.
    rewrite W64.ultE W64.of_uintK /= in hg.
    have hclt : W64.to_uint col{hr}<nc by smt(modz_small).
    split; first exact hclt.
    move=> j after hjg _ hj0 hjn hp' hcur' hf'.
    rewrite W64.ultE W64.of_uintK /= in hjg.
    have hj : W64.to_uint j=256 by smt().
    have hcnext : W64.to_uint (col{hr}+W64.one)=W64.to_uint col{hr}+1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1; trivial.
    have hoffnext : W64.to_uint (col_off{hr}+W64.of_int 256)=256*(W64.to_uint col{hr}+1).
    + rewrite W64.to_uintD_small 1:/# W64.of_uintK /= hoff; ring.
    rewrite hcnext hoffnext.
    have hpre : accumulated_row initial after mp0 vp0 nc
      (W64.to_uint row{hr}) (W64.to_uint col{hr}) 256 by smt().
    have hs:=accumulate_next_col initial after mp0 vp0 nc
      (W64.to_uint row{hr}) (W64.to_uint col{hr}) hpre.
    move: hs; rewrite /accumulated_row; smt().
  wp.
  while (mp=mp0 /\ vp=vp0 /\ rows=W64.of_int nr /\ cols=W64.of_int nc /\
    0<=W64.to_uint row<nr /\
    W64.to_uint row_out=256*W64.to_uint row /\
    W64.to_uint row_mat=256*W64.to_uint row*nc /\
    0<=W64.to_uint j<=256 /\
    initialized_row initial tp mp0 vp0 nc (W64.to_uint row) (W64.to_uint j)).
  + auto => /> &hr hr0 hrn hout hmat hj0 hjn hp hz hf hg.
    rewrite W64.ultE W64.of_uintK /= in hg.
    have hi : W64.to_uint (row_out{hr}+j{hr})=256*W64.to_uint row{hr}+W64.to_uint j{hr}.
    + rewrite W64.to_uintD_small 1:/# hout; trivial.
    have hnext : W64.to_uint (j{hr}+W64.one)=W64.to_uint j{hr}+1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1; trivial.
    rewrite hi hnext.
    have hpre : initialized_row initial tp{hr} mp0 vp0 nc (W64.to_uint row{hr}) (W64.to_uint j{hr}) by split.
    have hs:=initialize_step initial tp{hr} mp0 vp0 nc (W64.to_uint row{hr}) (W64.to_uint j{hr}) _ _ hpre; first 2 by smt().
    move: hs; rewrite /initialized_row; smt().
  auto => /> &hr hr0 hrn hout hmat hp hf hg.
  rewrite W64.ultE W64.of_uintK /= in hg.
  have hrlt : W64.to_uint row{hr}<nr by smt(modz_small).
  split; first smt().
  move=> j initialized hjg _ hj0 hjn hp' hz' hf'.
  rewrite W64.ultE W64.of_uintK /= in hjg.
  have hj : W64.to_uint j=256 by smt().
  have hi : initialized_row initial initialized mp0 vp0 nc (W64.to_uint row{hr}) 256 by smt().
  have ha:=initialize_done initial initialized mp0 vp0 nc (W64.to_uint row{hr}) hi.
  split.
  + move: ha; rewrite /accumulated_row; smt().
  move=> col0 off0 after hdone hc0 hcn hoff hp2 hcur2 hf2.
  rewrite W64.ultE W64.of_uintK /= in hdone.
  have hc : W64.to_uint col0=nc by smt(modz_small).
  have hpre : accumulated_row initial after mp0 vp0 nc (W64.to_uint row{hr}) nc 0 by smt().
  have hs:=accumulate_done initial after mp0 vp0 nc (W64.to_uint row{hr}) hpre.
  have hnext : W64.to_uint (row{hr}+W64.one)=W64.to_uint row{hr}+1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1; trivial.
  have houtnext : W64.to_uint (row_out{hr}+W64.of_int 256)=256*(W64.to_uint row{hr}+1).
  + rewrite W64.to_uintD_small 1:/# W64.of_uintK /= hout; ring.
  have hmatnext : W64.to_uint (row_mat{hr}+off0)=256*(W64.to_uint row{hr}+1)*nc.
  + have hb:=matrix_index_bound (W64.to_uint row{hr}) nc nc 0 _ _ _ _; first 4 by smt().
    by rewrite W64.to_uintD hmat hoff hc modz_small 1:/= 1:/#; ring.
  rewrite hnext houtnext hmatnext.
  move: hs; rewrite /completed_rows; smt().
auto => />.
split.
+ have hzero:=completed_rows_zero initial mp0 vp0 nc.
  move: hzero; rewrite /completed_rows; smt().
move=> row out mat after hdone hr0 hrn hout hmat hp hf.
rewrite W64.ultE W64.of_uintK /= in hdone.
have hr : W64.to_uint row=nr by smt(modz_small).
rewrite /completed_rows; smt().
qed.

lemma polymat_pointwise_ll : islossless Target._polymat_pointwise_acc.
proof.
proc.
while (W64.to_uint row<=W64.to_uint rows) (W64.to_uint rows-W64.to_uint row).
+ move=> z; wp.
  while (W64.to_uint col<=W64.to_uint cols) (W64.to_uint cols-W64.to_uint col).
  + move=> zc; wp.
    while (W64.to_uint j<=256) (256-W64.to_uint j).
    + move=> zj; wp; call api_fqmul_ll; auto => /> &hr hj hg.
      rewrite W64.ultE W64.of_uintK /= in hg.
      rewrite W64.to_uintD_small 1:/# W64.to_uint1; smt().
    auto => /> &hr hc hg.
    rewrite W64.ultE in hg.
    have /= hcols:=W64.to_uint_cmp cols{hr}.
    move=> j; split.
    + rewrite W64.ultE W64.of_uintK /=; smt().
    move=> _ _.
    rewrite W64.to_uintD_small 1:W64.to_uint1 1:/# W64.to_uint1; smt().
  wp.
  while (W64.to_uint j<=256) (256-W64.to_uint j).
  + move=> zj; auto => /> &hr hj hg.
    rewrite W64.ultE W64.of_uintK /= in hg.
    rewrite W64.to_uintD_small 1:/# W64.to_uint1; smt().
  auto => /> &hr hr hg.
  rewrite W64.ultE in hg.
  have /= hrows:=W64.to_uint_cmp rows{hr}.
  have /= hcols:=W64.to_uint_cmp cols{hr}.
  move=> j; split.
  + rewrite W64.ultE W64.of_uintK /=; smt().
  move=> _ _; split; first smt().
  move=> col; split.
  + rewrite W64.ultE; smt().
  move=> _ _.
  rewrite W64.to_uintD_small 1:W64.to_uint1 1:/# W64.to_uint1; smt().
auto => /> &hr.
split; first smt(W64.to_uint_cmp).
move=> row hr hv; rewrite W64.ultE; smt().
qed.

lemma polymat_pointwise_total initial mp0 vp0 nr nc :
 matrix_inputs mp0 vp0 nr nc =>
 phoare [Target._polymat_pointwise_acc :
    tp=initial /\ mp=mp0 /\ vp=vp0 /\ rows=W64.of_int nr /\ cols=W64.of_int nc ==>
    completed_rows initial res mp0 vp0 nc nr] = 1%r.
proof.
move=> hi.
by conseq polymat_pointwise_ll (polymat_pointwise_correct initial mp0 vp0 nr nc hi).
qed.

import Zq.

op matrix_field_dot (mp:BArray32768.t) (vp:BArray8192.t) (cols row j:int) : Zq.coeff =
 Rq.BigDom.BAdd.bigi predT
   (fun c => NTT_Fq.word_to_coeff (BArray32768.get32 mp (256*(row*cols+c)+j)) *
             NTT_Fq.word_to_coeff (BArray8192.get32 vp (256*c+j)) * inv NTT_Fq.R) 0 cols.

lemma matrix_term_field mp vp rows cols row col j :
 matrix_inputs mp vp rows cols => 0<=row<rows => 0<=col<cols => 0<=j<256 =>
 incoeff (matrix_term mp vp cols row col j) =
 NTT_Fq.word_to_coeff (BArray32768.get32 mp (256*(row*cols+col)+j)) *
 NTT_Fq.word_to_coeff (BArray8192.get32 vp (256*col+j)) * inv NTT_Fq.R.
proof.
move=> [hrows [hcols [hsize [hm hv]]]] hr hc hj.
have hm' := hm (256*(row*cols+col)+j) _; first by smt().
have hv' := hv (256*col+j) _; first by smt().
have [hb hcgr] := NTTMontgomeryBounds.fqmul_canonical24_bounds_congr
 (W32.to_sint (BArray32768.get32 mp (256*(row*cols+col)+j)))
 (W32.to_sint (BArray8192.get32 vp (256*col+j))) hm' hv'.
rewrite /matrix_term /NTT_Fq.word_to_coeff NTT_Fq.inv_R -!incoeffM -eq_incoeff /GFq.q.
rewrite !incoeffK /GFq.q.
smt(modzMml modzMmr).
qed.

lemma matrix_sum_field mp vp rows cols row j n :
 matrix_inputs mp vp rows cols => 0<=row<rows => 0<=j<256 => 0<=n<=cols =>
 incoeff (matrix_sum mp vp cols row j n) =
 Rq.BigDom.BAdd.bigi predT
   (fun c => NTT_Fq.word_to_coeff (BArray32768.get32 mp (256*(row*cols+c)+j)) *
             NTT_Fq.word_to_coeff (BArray8192.get32 vp (256*c+j)) * inv NTT_Fq.R) 0 n.
proof.
move=> inputs hr hj hn.
move: hn; elim/natind: n => [n hn hn'|n hn ih hn'].
+ have hn0:n=0 by smt().
  by rewrite hn0 matrix_sum_zero Rq.BigDom.BAdd.big_geq // incoeff0.
rewrite matrix_sum_step 1:hn incoeffD Rq.BigDom.BAdd.big_int_recr 1:hn /=.
have hp:=ih _; first smt().
rewrite hp.
rewrite (matrix_term_field mp vp rows cols row n j inputs hr _ hj) 1:/#.
trivial.
qed.

lemma completed_rows_field initial output mp vp nr nc :
 matrix_inputs mp vp nr nc => completed_rows initial output mp vp nc nr =>
 (forall r j, 0<=r<nr => 0<=j<256 =>
   Fq.bw32 (BArray8192.get32 output (256*r+j)) 18 /\
   NTT_Fq.word_to_coeff (BArray8192.get32 output (256*r+j))=matrix_field_dot mp vp nc r j) /\
 NTTVectorSpec.inactive_unchanged initial output nr.
proof.
move=> inputs [hcoeff hframe]; split; last exact hframe.
move=> r j hr hj.
have hout:=hcoeff r j hr hj.
have hd : 0<=nc<=8.
+ by move: inputs; rewrite /matrix_inputs; smt().
have hb:=matrix_sum_bound mp vp nr nc r j nc inputs hr hj _; first smt().
have he:=matrix_sum_field mp vp nr nc r j nc inputs hr hj _; first smt().
split.
+ rewrite /Fq.bw32 /= hout; smt().
rewrite /NTT_Fq.word_to_coeff hout /matrix_field_dot.
exact he.
qed.

lemma polymat_pointwise_field_total initial mp0 vp0 nr nc :
 matrix_inputs mp0 vp0 nr nc =>
 phoare [Target._polymat_pointwise_acc :
    tp=initial /\ mp=mp0 /\ vp=vp0 /\ rows=W64.of_int nr /\ cols=W64.of_int nc ==>
    (forall r j, 0<=r<nr => 0<=j<256 =>
      Fq.bw32 (BArray8192.get32 res (256*r+j)) 18 /\
      NTT_Fq.word_to_coeff (BArray8192.get32 res (256*r+j))=matrix_field_dot mp0 vp0 nc r j) /\
    NTTVectorSpec.inactive_unchanged initial res nr] = 1%r.
proof.
move=> hi.
have hh : hoare [Target._polymat_pointwise_acc :
    tp=initial /\ mp=mp0 /\ vp=vp0 /\ rows=W64.of_int nr /\ cols=W64.of_int nc ==>
    (forall r j, 0<=r<nr => 0<=j<256 =>
      Fq.bw32 (BArray8192.get32 res (256*r+j)) 18 /\
      NTT_Fq.word_to_coeff (BArray8192.get32 res (256*r+j))=matrix_field_dot mp0 vp0 nc r j) /\
    NTTVectorSpec.inactive_unchanged initial res nr].
+ conseq (polymat_pointwise_correct initial mp0 vp0 nr nc hi).
  move=> &hr _ result hpost.
  exact (completed_rows_field initial result mp0 vp0 nr nc hi hpost).
by conseq polymat_pointwise_ll hh.
qed.

lemma polymat_pointwise_field_total_pre initial mp0 vp0 nr nc :
 phoare [Target._polymat_pointwise_acc :
    tp=initial /\ mp=mp0 /\ vp=vp0 /\ rows=W64.of_int nr /\ cols=W64.of_int nc /\ matrix_inputs mp0 vp0 nr nc ==>
    (forall r j, 0<=r<nr => 0<=j<256 =>
      Fq.bw32 (BArray8192.get32 res (256*r+j)) 18 /\
      NTT_Fq.word_to_coeff (BArray8192.get32 res (256*r+j))=matrix_field_dot mp0 vp0 nc r j) /\
    NTTVectorSpec.inactive_unchanged initial res nr] = 1%r.
proof.
case (matrix_inputs mp0 vp0 nr nc) => hi.
+ by conseq (polymat_pointwise_field_total initial mp0 vp0 nr nc hi) => /#.
+ by exfalso => /#.
qed.

end NTTMatrixCorrectness.

