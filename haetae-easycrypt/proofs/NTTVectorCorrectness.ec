require import AllCore IntDiv List StdOrder.
from Jasmin require import JModel_x86.
require import ApiTarget HpolyTarget NTTCorrectness NTTVectorSpec NTTFullSpec NTT_Fq RefJasminNTTLoop.

import NTTVectorSpec IntOrder RefJasminNTT.

theory NTTVectorCorrectness.

module Actual = ApiTarget.M(ApiTarget.Syscall).
module Single = HpolyTarget.M.

module VectorRef = {
  proc ntt(xp:BArray8192.t, count:int) : BArray8192.t = {
    var i:int;
    var rp:BArray1024.t;
    i <- 0;
    while (i < count) {
      rp <- block8192 xp i;
      rp <@ Single._poly_ntt(rp);
      xp <- put_block8192 xp i rp;
      i <- i+1;
    }
    return xp;
  }
  proc invntt(xp:BArray8192.t, count:int) : BArray8192.t = {
    var i:int;
    var rp:BArray1024.t;
    i <- 0;
    while (i < count) {
      rp <- block8192 xp i;
      rp <@ Single._poly_invntt(rp);
      xp <- put_block8192 xp i rp;
      i <- i+1;
    }
    return xp;
  }
}.

lemma api_zetas_equal : ApiTarget.jzetas = HpolyTarget.jzetas.
proof. by []. qed.
lemma api_zetas_inv_equal : ApiTarget.jzetas_inv = HpolyTarget.jzetas_inv.
proof. by []. qed.

lemma vector_fqmul_equiv :
  equiv[Actual.__fqmul ~ Single.__fqmul : ={a,b} ==> ={res}].
proof.
proc.
inline Actual.__montgomery_reduce Single.__montgomery_reduce.
sim.
qed.

lemma put_block8192_get32_active a k b j :
  0<=k<8 => 0<=j<256 =>
  BArray8192.get32 (put_block8192 a k b) (256*k+j) =
  BArray1024.get32 b j.
proof.
move=> hk hj.
rewrite put_block8192_get32 1:/# 1:/#.
have hm : 256*k<=256*k+j<256*(k+1) by smt().
by rewrite hm /=; congr; ring.
qed.

lemma vector_invntt_equiv :
  equiv[Actual._polyvec_invntt ~ VectorRef.invntt :
    xp{1}=xp{2} /\ W64.to_uint count{1}=count{2} /\ 0<=count{2}<=8
    ==> res{1}=res{2}].
proof.
proc.
wp.
while (xp{1}=xp{2} /\ W64.to_uint count{1}=count{2} /\
       0<=i{2}<=count{2}<=8 /\ W64.to_uint poly{1}=i{2} /\
       W64.to_uint base{1}=256*i{2} /\ zetasp{1}=ApiTarget.jzetas_inv).
+ inline {2} Single._poly_invntt.
  wp.
  while (xp{1}=put_block8192 xp{2} i{2} rp0{2} /\
         W64.to_uint count{1}=count{2} /\ 0<=i{2}<count{2}<=8 /\
         W64.to_uint poly{1}=i{2} /\ W64.to_uint base{1}=256*i{2} /\
         zetasp{1}=ApiTarget.jzetas_inv /\ ={zeta_0} /\
         W64.to_uint j{1}=j{2} /\ 0<=j{2}<=256).
  + wp; call vector_fqmul_equiv; wp; skip.
    move=> &1 &2 [hinv [hg1 hg2]].
    move: hinv => [hxp [hcount [hirng [hpoly [hbase [hzetasp [hzeta [hj hjb]]]]]]]].
    have hadd : W64.to_uint (base{1}+j{1}) = 256*i{2}+j{2}.
    + by rewrite W64.to_uintD_small 1:/# hbase hj.
    rewrite /= hadd hxp put_block8192_get32 1:/# 1:/#.
    have hmem : 256*i{2} <= 256*i{2}+j{2} < 256*(i{2}+1) by smt().
    rewrite hmem /=.
    have -> : 256*i{2}+j{2}-256*i{2}=j{2} by ring.
    split; first by smt().
    move=> _ r1 r2 heq; rewrite heq put_block8192_set32 1:/# 1:/#.
    have hinc : W64.to_uint (j{1}+W64.one)=j{2}+1.
    + by rewrite W64.to_uintD_small 1:/# W64.to_uint1 hj.
    rewrite W64.ultE hinc W64.to_uint_small 1:/#.
    rewrite hzetasp hcount hpoly hbase hzeta /=.
    smt().
  wp.
  while (xp{1}=put_block8192 xp{2} i{2} rp0{2} /\
    W64.to_uint count{1}=count{2} /\ 0<=i{2}<count{2}<=8 /\
    W64.to_uint poly{1}=i{2} /\ W64.to_uint base{1}=256*i{2} /\
    zetasp{1}=ApiTarget.jzetas_inv /\ ={zetasp} /\
    W64.to_uint len{1}=len{2} /\ inv_len_ok len{2} /\
    W64.to_uint zetasctr{1}=zetasctr{2} /\ zetasctr{2}=inv_zbase len{2}).
  + wp.
    while (xp{1}=put_block8192 xp{2} i{2} rp0{2} /\
    W64.to_uint count{1}=count{2} /\ 0<=i{2}<count{2}<=8 /\
    W64.to_uint poly{1}=i{2} /\ W64.to_uint base{1}=256*i{2} /\
    zetasp{1}=ApiTarget.jzetas_inv /\ ={zetasp} /\
    W64.to_uint len{1}=len{2} /\ inv_len_ok len{2} /\ 0<len{2}<256 /\
    W64.to_uint zetasctr{1}=zetasctr{2} /\
    W64.to_uint start{1}=start{2} /\ 0<=start{2}<=256 /\
    start{2}=2*len{2}*(zetasctr{2}-inv_zbase len{2})).
    + wp.
      while (xp{1}=put_block8192 xp{2} i{2} rp0{2} /\
    W64.to_uint count{1}=count{2} /\ 0<=i{2}<count{2}<=8 /\
    W64.to_uint poly{1}=i{2} /\ W64.to_uint base{1}=256*i{2} /\
    zetasp{1}=ApiTarget.jzetas_inv /\ ={zetasp,zeta_0} /\
    W64.to_uint len{1}=len{2} /\ inv_len_ok len{2} /\ 0<len{2}<256 /\
    W64.to_uint zetasctr{1}=zetasctr{2} /\
    W64.to_uint start{1}=start{2} /\ 0<=start{2}<256 /\
    start{2}+2*len{2}<=256 /\
    start{2}=2*len{2}*(zetasctr{2}-1-inv_zbase len{2}) /\
    1<=zetasctr{2}<=255 /\
    W64.to_uint j{1}=j{2} /\ W64.to_uint cmp{1}=cmp{2} /\
    cmp{2}=start{2}+len{2} /\ start{2}<=j{2}<=cmp{2}).
      + wp; call vector_fqmul_equiv; wp; skip.
        move=> &1 &2 [hinv [hg1 hg2]].
        move: hinv => [hxp hinv].
        move: hinv => [hcount hinv].
        move: hinv => [hirng hinv].
        move: hinv => [hpoly hinv].
        move: hinv => [hbase hinv].
        move: hinv => [hzetasp hinv].
        move: hinv => [heqs hinv].
        move: hinv => [hlen hinv].
        move: hinv => [hlenok hinv].
        move: hinv => [hlenrng hinv].
        move: hinv => [hzc hinv].
        move: hinv => [hst hinv].
        move: hinv => [hstrng hinv].
        move: hinv => [hend hinv].
        move: hinv => [hstart hinv].
        move: hinv => [hzcrng hinv].
        move: hinv => [hj hinv].
        move: hinv => [hcmp hinv].
        move: hinv => [hc hinv].
        have hjb : 0<=j{2}<256 by smt().
        have hkb : 0<=i{2}<8 by smt().
        have hob : 0<=j{2}+len{2}<256 by smt().
        have ho : W64.to_uint (j{1}+len{1})=j{2}+len{2}.
        + by rewrite W64.to_uintD_small 1:/# hj hlen.
        have hidx : W64.to_uint (base{1}+j{1})=256*i{2}+j{2}.
        + by rewrite W64.to_uintD_small 1:/# hbase hj.
        have hidx2 : W64.to_uint (base{1}+(j{1}+len{1}))=256*i{2}+(j{2}+len{2}).
        + by rewrite W64.to_uintD_small 1:/# hbase ho.
        have hinc : W64.to_uint (j{1}+W64.one)=j{2}+1.
        + by rewrite W64.to_uintD_small 1:/# W64.to_uint1 hj.
        rewrite /= hidx hidx2 hxp.
        rewrite (put_block8192_get32_active _ _ _ _ hkb hjb).
        rewrite (put_block8192_get32_active _ _ _ _ hkb hob).
        split; first by smt().
        move=> _ r1 r2 heq; rewrite heq.
        rewrite put_block8192_set32 1:/# 1:/#.
        rewrite put_block8192_set32 1:/# 1:/#.
        rewrite W64.ultE hinc hcmp.
        move: heqs => [hzt hzeta].
        rewrite hcount hpoly hbase -hzt hzetasp hzeta hlen hzc hst /=.
        smt().
      wp; skip.
      move=> &1 &2 [hinv [hg1 hg2]].
      move: hinv => [hxp hinv].
      move: hinv => [hcount hinv].
      move: hinv => [hirng hinv].
      move: hinv => [hpoly hinv].
      move: hinv => [hbase hinv].
      move: hinv => [hzetasp hinv].
      move: hinv => [hzt hinv].
      move: hinv => [hlen hinv].
      move: hinv => [hlenok hinv].
      move: hinv => [hlenrng hinv].
      move: hinv => [hzc hinv].
      move: hinv => [hst hinv].
      move: hinv => [hstrng hinv].
      have hzcbd : 0<=zetasctr{2}<255.
      + have := inv_read_range len{2} start{2} zetasctr{2} hlenok _ _ hinv.
        - by smt().
        - by smt().
        by rewrite mem_range.
      have hend := inv_block_end_bound len{2} start{2} zetasctr{2} hlenok _ _ hinv.
      + by smt().
      + by smt().
      have hci : W64.to_uint (zetasctr{1}+W64.one)=zetasctr{2}+1.
      + by rewrite W64.to_uintD_small 1:/# hzc W64.to_uint1.
      have hcmp : W64.to_uint (start{1}+len{1})=start{2}+len{2}.
      + by rewrite W64.to_uintD_small 1:/# hst hlen.
      rewrite /= !W64.ultE hci hcmp hst hzc.
      split.
      + rewrite hxp hcount hpoly hbase -hzt hzetasp hlen /=.
        smt().
      + move=> jL xpL jR rpR hn1 hn2 hi.
        have huj : W64.to_uint jL=jR by smt().
        have hjend : jR=start{2}+len{2} by smt().
        have hnext : W64.to_uint (jL+len{1})=jR+len{2}.
        + by rewrite W64.to_uintD_small 1:/# huj hlen.
        rewrite W64.ultE hnext W64.to_uint_small 1:/#.
        rewrite hcount hpoly hbase -hzt hzetasp hlen /=.
        have hshift : 2*len{2}*(zetasctr{2}+1-inv_zbase len{2}) =
          2*len{2}*(zetasctr{2}-inv_zbase len{2})+2*len{2} by ring.
        have hrel : jR+len{2}=2*len{2}*(zetasctr{2}+1-inv_zbase len{2}).
        + by rewrite hshift -hinv hjend; ring.
        rewrite -hrel.
        move: hi => [hx _].
        split; first exact hx.
        smt().
    wp; skip.
    move=> &1 &2 [hinv [hg1 hg2]].
    move: hinv => [hxp hinv].
    move: hinv => [hcount hinv].
    move: hinv => [hirng hinv].
    move: hinv => [hpoly hinv].
    move: hinv => [hbase hinv].
    move: hinv => [hzetasp hinv].
    move: hinv => [hzt hinv].
    move: hinv => [hlen hinv].
    move: hinv => [hlenok hinv].
    move: hinv => [hzc hinv].
    have hlenpos : 0<len{2} by move: hlenok; rewrite /inv_len_ok; smt().
    have hshift : W64.to_uint (len{1} `<<` W8.one)=len{2}*2.
    + rewrite (W64.shl_shlw 1) 1:/# W64.to_uint_shl 1:/# hlen /=.
      by rewrite modz_small 1:/#.
    rewrite /= !W64.ultE W64.to_uint_small 1:/#.
    split.
    + rewrite hxp hcount hpoly hbase -hzt hzetasp hlen hzc hinv /=.
      smt().
    + move=> stL xpL zcL rpR stR zcR hn1 hn2 hi.
      have hstR : stR=256 by smt().
      have hzcR : zcR=inv_zbase (len{2}*2).
      + apply (inv_stage_zbase_exit len{2} zcR hlenok hg2).
        by smt().
      have hnextok := inv_len_next_ok len{2} hlenok hg2.
      rewrite int_shl1_mul2 hshift.
      rewrite hcount hpoly hbase -hzt hzetasp /=.
      have hx : xpL=put_block8192 xp{2} i{2} rpR by smt().
      have hz : W64.to_uint zcL=zcR by smt().
      clear hi.
      smt().
  wp; skip.
  move=> &1 &2 [[hxp [hcount [hirng [hpoly [hbase hzetasp]]]]] [hg1 hg2]].
  have hpi : W64.to_uint (poly{1}+W64.one)=i{2}+1.
  + by rewrite W64.to_uintD_small 1:/# W64.to_uint1 hpoly.
  have hbi : W64.to_uint (base{1}+W64.of_int 256)=256*(i{2}+1).
  + rewrite W64.to_uintD_small 1:/# hbase; ring.
  rewrite /= put_block8192_self 1:/# hxp hcount hpoly hbase hzetasp /=.
  rewrite !W64.ultE hpi hbi hcount /=.
  split; first by rewrite /inv_len_ok /inv_zbase /=; smt().
  move=> lenL xpL zcL lenR rpR zcR hn1 hn2 hi.
  split; first by smt().
  move=> jL xpL0 jR rpR0 hn3 hn4 hi2.
  smt().
wp; skip.
move=> &1 &2 [hx [hc hr]].
rewrite /= !W64.ultE /=.
smt().
qed.

lemma vector_ntt_equiv :
  equiv[Actual._polyvec_ntt ~ VectorRef.ntt :
    xp{1}=xp{2} /\ W64.to_uint count{1}=count{2} /\ 0<=count{2}<=8
    ==> res{1}=res{2}].
proof.
proc.
wp.
while (xp{1}=xp{2} /\ W64.to_uint count{1}=count{2} /\
       0<=i{2}<=count{2}<=8 /\ W64.to_uint poly{1}=i{2} /\
       W64.to_uint base{1}=256*i{2} /\ zetasp{1}=ApiTarget.jzetas).
+ inline {2} Single._poly_ntt.
  wp.
  while (xp{1}=put_block8192 xp{2} i{2} rp0{2} /\
    W64.to_uint count{1}=count{2} /\ 0<=i{2}<count{2}<=8 /\
    W64.to_uint poly{1}=i{2} /\ W64.to_uint base{1}=256*i{2} /\
    zetasp{1}=ApiTarget.jzetas /\ ={zetasp} /\
    W64.to_uint len{1}=len{2} /\ fwd_len_ok len{2} /\
    W64.to_uint zetasctr{1}=zetasctr{2} /\ zetasctr{2}=fwd_zbase len{2}).
  + wp.
    while (xp{1}=put_block8192 xp{2} i{2} rp0{2} /\
    W64.to_uint count{1}=count{2} /\ 0<=i{2}<count{2}<=8 /\
    W64.to_uint poly{1}=i{2} /\ W64.to_uint base{1}=256*i{2} /\
    zetasp{1}=ApiTarget.jzetas /\ ={zetasp} /\
    W64.to_uint len{1}=len{2} /\ fwd_len_ok len{2} /\ 0<len{2}<=128 /\
    W64.to_uint zetasctr{1}=zetasctr{2} /\
    W64.to_uint start{1}=start{2} /\ 0<=start{2}<=256 /\
    start{2}=2*len{2}*(zetasctr{2}-fwd_zbase len{2})).
    + wp.
      while (xp{1}=put_block8192 xp{2} i{2} rp0{2} /\
    W64.to_uint count{1}=count{2} /\ 0<=i{2}<count{2}<=8 /\
    W64.to_uint poly{1}=i{2} /\ W64.to_uint base{1}=256*i{2} /\
    zetasp{1}=ApiTarget.jzetas /\ ={zetasp,zeta_0} /\
    W64.to_uint len{1}=len{2} /\ fwd_len_ok len{2} /\ 0<len{2}<=128 /\
    W64.to_uint zetasctr{1}=zetasctr{2} /\
    W64.to_uint start{1}=start{2} /\ 0<=start{2}<256 /\
    start{2}+2*len{2}<=256 /\
    start{2}=2*len{2}*(zetasctr{2}-1-fwd_zbase len{2}) /\
    1<=zetasctr{2}<=255 /\
    W64.to_uint j{1}=j{2} /\ W64.to_uint cmp{1}=cmp{2} /\
    cmp{2}=start{2}+len{2} /\ start{2}<=j{2}<=cmp{2}).
      + wp; call vector_fqmul_equiv; wp; skip.
        move=> &1 &2 [hinv [hg1 hg2]].
        move: hinv => [hxp hinv].
        move: hinv => [hcount hinv].
        move: hinv => [hirng hinv].
        move: hinv => [hpoly hinv].
        move: hinv => [hbase hinv].
        move: hinv => [hzetasp hinv].
        move: hinv => [heqs hinv].
        move: hinv => [hlen hinv].
        move: hinv => [hlenok hinv].
        move: hinv => [hlenrng hinv].
        move: hinv => [hzc hinv].
        move: hinv => [hst hinv].
        move: hinv => [hstrng hinv].
        move: hinv => [hend hinv].
        move: hinv => [hstart hinv].
        move: hinv => [hzcrng hinv].
        move: hinv => [hj hinv].
        move: hinv => [hcmp hinv].
        move: hinv => [hc hinv].
        have hjb : 0<=j{2}<256 by smt().
        have hkb : 0<=i{2}<8 by smt().
        have hob : 0<=j{2}+len{2}<256 by smt().
        have ho : W64.to_uint (j{1}+len{1})=j{2}+len{2}.
        + by rewrite W64.to_uintD_small 1:/# hj hlen.
        have hidx : W64.to_uint (base{1}+j{1})=256*i{2}+j{2}.
        + by rewrite W64.to_uintD_small 1:/# hbase hj.
        have hidx2 : W64.to_uint (base{1}+(j{1}+len{1}))=256*i{2}+(j{2}+len{2}).
        + by rewrite W64.to_uintD_small 1:/# hbase ho.
        have hinc : W64.to_uint (j{1}+W64.one)=j{2}+1.
        + by rewrite W64.to_uintD_small 1:/# W64.to_uint1 hj.
        rewrite /= hidx hidx2 hxp.
        rewrite (put_block8192_get32_active _ _ _ _ hkb hjb).
        rewrite (put_block8192_get32_active _ _ _ _ hkb hob).
        split; first by smt().
        move=> _ r1 r2 heq; rewrite heq.
        rewrite put_block8192_set32 1:/# 1:/#.
        rewrite put_block8192_set32 1:/# 1:/#.
        rewrite W64.ultE hinc hcmp.
        move: heqs => [hzt hzeta].
        rewrite hcount hpoly hbase -hzt hzetasp hzeta hlen hzc hst /=.
        smt().
      wp; skip.
      move=> &1 &2 [hinv [hg1 hg2]].
      move: hinv => [hxp hinv].
      move: hinv => [hcount hinv].
      move: hinv => [hirng hinv].
      move: hinv => [hpoly hinv].
      move: hinv => [hbase hinv].
      move: hinv => [hzetasp hinv].
      move: hinv => [hzt hinv].
      move: hinv => [hlen hinv].
      move: hinv => [hlenok hinv].
      move: hinv => [hlenrng hinv].
      move: hinv => [hzc hinv].
      move: hinv => [hst hinv].
      move: hinv => [hstrng hinv].
      have hzcbd : 0<=zetasctr{2}<255.
      + have := fwd_read_range len{2} start{2} zetasctr{2} hlenok _ _ hinv.
        - by smt().
        - by smt().
        by smt().
      have hend := fwd_block_end_bound len{2} start{2} zetasctr{2} hlenok _ _ hinv.
      + by smt().
      + by smt().
      have hci : W64.to_uint (zetasctr{1}+W64.one)=zetasctr{2}+1.
      + by rewrite W64.to_uintD_small 1:/# hzc W64.to_uint1.
      have hcmp : W64.to_uint (start{1}+len{1})=start{2}+len{2}.
      + by rewrite W64.to_uintD_small 1:/# hst hlen.
      rewrite /= !W64.ultE hci hcmp hst.
      split.
      + rewrite hxp hcount hpoly hbase -hzt hzetasp hlen /=.
        smt().
      + move=> jL xpL jR rpR hn1 hn2 hi.
        have huj : W64.to_uint jL=jR by smt().
        have hjend : jR=start{2}+len{2} by smt().
        have hnext : W64.to_uint (jL+len{1})=jR+len{2}.
        + by rewrite W64.to_uintD_small 1:/# huj hlen.
        rewrite W64.ultE hnext W64.to_uint_small 1:/#.
        rewrite hcount hpoly hbase -hzt hzetasp hlen /=.
        have hshift : 2*len{2}*(zetasctr{2}+1-fwd_zbase len{2}) =
          2*len{2}*(zetasctr{2}-fwd_zbase len{2})+2*len{2} by ring.
        have hrel : jR+len{2}=2*len{2}*(zetasctr{2}+1-fwd_zbase len{2}).
        + by rewrite hshift -hinv hjend; ring.
        rewrite -hrel.
        move: hi => [hx _].
        split; first exact hx.
        smt().
    wp; skip.
    move=> &1 &2 [hinv [hg1 hg2]].
    move: hinv => [hxp hinv].
    move: hinv => [hcount hinv].
    move: hinv => [hirng hinv].
    move: hinv => [hpoly hinv].
    move: hinv => [hbase hinv].
    move: hinv => [hzetasp hinv].
    move: hinv => [hzt hinv].
    move: hinv => [hlen hinv].
    move: hinv => [hlenok hinv].
    move: hinv => [hzc hinv].
    have hlenbd : len{2}<=128 by move: hlenok; rewrite /fwd_len_ok; smt().
    have hshift : W64.to_uint (len{1} `>>` W8.one)=len{2} %/ 2.
    + by rewrite W64.shr_div W8.to_uint1 /= hlen.
    rewrite /= !W64.ultE W64.to_uint_small 1:/#.
    split.
    + rewrite hxp hcount hpoly hbase -hzt hzetasp hlen hzc hinv /=.
      smt().
    + move=> stL xpL zcL rpR stR zcR hn1 hn2 hi.
      have hstR : stR=256 by smt().
      have hzcR : zcR=fwd_zbase (len{2}%/2).
      + apply (fwd_stage_zbase_exit len{2} zcR hlenok hg2).
        by smt().
      have hnextok := fwd_len_next_ok len{2} hlenok hg2.
      rewrite int_shr1_div2 1:/# hshift.
      rewrite hcount hpoly hbase -hzt hzetasp /=.
      have hx : xpL=put_block8192 xp{2} i{2} rpR by smt().
      have hz : W64.to_uint zcL=zcR by smt().
      clear hi.
      smt().
  wp; skip.
  move=> &1 &2 [[hxp [hcount [hirng [hpoly [hbase hzetasp]]]]] [hg1 hg2]].
  have hpi : W64.to_uint (poly{1}+W64.one)=i{2}+1.
  + by rewrite W64.to_uintD_small 1:/# W64.to_uint1 hpoly.
  have hbi : W64.to_uint (base{1}+W64.of_int 256)=256*(i{2}+1).
  + rewrite W64.to_uintD_small 1:/# hbase; ring.
  rewrite /= put_block8192_self 1:/# hxp hcount hpoly hbase hzetasp /=.
  rewrite !W64.ultE hpi hbi hcount /=.
  split; first by rewrite /fwd_len_ok /fwd_zbase /=; smt().
  move=> lenL xpL zcL lenR rpR zcR hn1 hn2 hi.
  smt().
wp; skip.
move=> &1 &2 [hx [hc hr]].
rewrite /= !W64.ultE /=.
smt().
qed.

end NTTVectorCorrectness.
