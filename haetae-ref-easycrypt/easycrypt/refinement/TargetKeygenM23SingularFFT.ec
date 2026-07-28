require import AllCore IntDiv List Ring.

from Jasmin require import JModel_x86.

import SLH64.

require import
  KeygenMode2ParentTarget
  KeygenM23SingularSpec
  KeygenM23SingularFFTSpec
  TargetKeygenM23SingularTotality.

theory TargetKeygenM23SingularFFT.

module Parent = KeygenMode2ParentTarget.M.

lemma fft_mulrnd16_correct (x0 y0 : W32.t) :
  hoare [Parent.__fft_mulrnd16 :
    x = x0 /\ y = y0
    ==>
    res = KeygenM23SingularSpec.mulrnd16_word x0 y0].
proof.
proc.
auto => />.
qed.

lemma fft_init_and_bitrev_correct
    (data0 : BArray2048.t) (xp0 : BArray1024.t)
    (roots0 : BArray2048.t) (brv0 : BArray512.t) :
  hoare [Parent._fft_init_and_bitrev :
    rp = data0 /\ xp = xp0 /\ rootsp = roots0 /\ brvp = brv0
    ==>
    res =
      KeygenM23SingularFFTSpec.fft_init_and_bitrev
        data0 xp0 roots0 brv0].
proof.
proc.
while
  (xp = xp0 /\ rootsp = roots0 /\ brvp = brv0 /\
   0 <= W64.to_uint i <= KeygenM23SingularFFTSpec.fft_words_i /\
   rp =
     KeygenM23SingularFFTSpec.fft_init_prefix
       data0 xp0 roots0 brv0 (W64.to_uint i)).
+ auto => /> &hr hile hdata hguard.
  have hilt :
      W64.to_uint i{hr} < KeygenM23SingularFFTSpec.fft_words_i.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23SingularFFTSpec.fft_words_i /=.
    trivial.
  have hsucc :
      W64.to_uint (i{hr} + W64.one) =
        W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/#.
    trivial.
  rewrite /SLH64.protect_64 hsucc.
  split; first smt().
  rewrite KeygenM23SingularFFTSpec.fft_init_prefixS 1:/#.
  rewrite /KeygenM23SingularFFTSpec.fft_init_step.
  trivial.
auto => />.
split.
+ by rewrite KeygenM23SingularFFTSpec.fft_init_prefix0.
move=> i0 data1 hdone hile.
have hieq :
    W64.to_uint i0 = KeygenM23SingularFFTSpec.fft_words_i.
+ move: hdone hile.
  rewrite /KeygenM23SingularFFTSpec.fft_words_i /=.
  smt(W64.to_uint_cmp).
by rewrite /KeygenM23SingularFFTSpec.fft_init_and_bitrev -hieq.
qed.

lemma fft_butterfly_correct
    (data0 roots0 : BArray2048.t) (even0 odd0 twid0 : W64.t) :
  hoare [Parent._fft_butterfly :
    datap = data0 /\ rootsp = roots0 /\
    even = even0 /\ odd = odd0 /\ twid = twid0
    ==>
    res =
      KeygenM23SingularFFTSpec.fft_butterfly
        data0 roots0 even0 odd0 twid0].
proof.
proc.
wp.
ecall (fft_mulrnd16_correct rimag oreal).
wp.
ecall (fft_mulrnd16_correct rreal oimag).
wp.
ecall (fft_mulrnd16_correct rimag oimag).
wp.
ecall (fft_mulrnd16_correct rreal oreal).
auto => />.
qed.

lemma fft_block_word
    (n m : W64.t) (block : int) :
  0 <= block =>
  W64.to_uint n = block * W64.to_uint m =>
  W64.of_int block * m = n.
proof.
move=> hblock hn.
rewrite -(W64.to_uintK' m) -(W64.to_uintK' n) hn.
by rewrite W64.of_intM.
qed.

op fft_stage_start
    (data roots : BArray2048.t) (r : W64.t) : BArray2048.t =
  (KeygenM23SingularFFTSpec.fft_schedule_prefix
     data roots (W64.to_uint r - 1)).`1.

op fft_params_at
    (data roots : BArray2048.t)
    (r m md2 stride : W64.t) : bool =
  let st =
    KeygenM23SingularFFTSpec.fft_schedule_prefix
      data roots (W64.to_uint r - 1) in
  TargetKeygenM23SingularTotality.m23sing_total_fft_outer_state
    r m md2 stride /\
  m = st.`2 /\ md2 = st.`3 /\ stride = st.`4.

lemma fft_full_correct (data0 roots0 : BArray2048.t) :
  hoare [Parent._fft_full :
    datap = data0 /\ rootsp = roots0
    ==>
    res = KeygenM23SingularFFTSpec.fft_full data0 roots0].
proof.
proc.
while
  (rootsp = roots0 /\
   fft_params_at data0 roots0 r m md2 stride /\
   datap = fft_stage_start data0 roots0 r).
+ wp.
  while
    (rootsp = roots0 /\
     fft_params_at data0 roots0 r m md2 stride /\
     r \ule W64.of_int 8 /\
     W64.to_uint n <= KeygenM23SingularFFTSpec.fft_words_i /\
     W64.to_uint n %% W64.to_uint m = 0 /\
     datap =
       KeygenM23SingularFFTSpec.fft_blocks_prefix
         (fft_stage_start data0 roots0 r) roots0
         m md2 stride (W64.to_uint n %/ W64.to_uint m)).
  + wp.
    while
      (rootsp = roots0 /\
       fft_params_at data0 roots0 r m md2 stride /\
       r \ule W64.of_int 8 /\
       W64.to_uint n %% W64.to_uint m = 0 /\
       W64.to_uint n < KeygenM23SingularFFTSpec.fft_words_i /\
       W64.to_uint k <= W64.to_uint md2 /\
       datap =
         KeygenM23SingularFFTSpec.fft_k_prefix
           (KeygenM23SingularFFTSpec.fft_blocks_prefix
              (fft_stage_start data0 roots0 r) roots0
              m md2 stride (W64.to_uint n %/ W64.to_uint m))
           roots0 n md2 stride (W64.to_uint k)).
    + wp.
      ecall (fft_butterfly_correct datap rootsp even odd twid).
      auto => /> &hr hparams hrbody hnmod hnlt hk hguard.
      have hmd2 :
          W64.to_uint
            (KeygenM23SingularFFTSpec.fft_schedule_prefix
               data0 roots0 (W64.to_uint r{hr} - 1)).`3 <= 256.
      + apply
          (TargetKeygenM23SingularTotality.m23sing_total_fft_state_md2_bound
             r{hr}
             (KeygenM23SingularFFTSpec.fft_schedule_prefix
                data0 roots0 (W64.to_uint r{hr} - 1)).`2
             (KeygenM23SingularFFTSpec.fft_schedule_prefix
                data0 roots0 (W64.to_uint r{hr} - 1)).`3
             (KeygenM23SingularFFTSpec.fft_schedule_prefix
                data0 roots0 (W64.to_uint r{hr} - 1)).`4).
        exact hparams.
      have hksucc :
          W64.to_uint (k{hr} + W64.one) =
            W64.to_uint k{hr} + 1.
      + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
        trivial.
      rewrite /SLH64.protect_ptr /SLH64.protect_64.
      move: hguard.
      rewrite W64.ultE.
      move=> hlt.
      split.
      + rewrite hksucc
                (addzC (W64.to_uint k{hr}) 1)
                lez_add1r.
        exact hlt.
      rewrite hksucc.
      have hk0 : 0 <= W64.to_uint k{hr} by
        smt(W64.to_uint_cmp).
      rewrite KeygenM23SingularFFTSpec.fft_k_prefixS 1:hk0.
      rewrite /KeygenM23SingularFFTSpec.fft_k_step W64.to_uintK'.
      trivial.
    auto => /> &hr2.
    + auto.
    move=> hparams2 hrbody2 hnbound2 hnmod2 hguard2.
    split.
    + split.
      + move: hguard2.
        rewrite W64.ultE W64.of_uintK
                /KeygenM23SingularFFTSpec.fft_words_i /=.
        trivial.
      split; first smt(W64.to_uint_cmp).
      by rewrite KeygenM23SingularFFTSpec.fft_k_prefix0.
    move=> k0 n0 r0
            hkend0 hparams30 hrbody30 hnmod30 hnlt30 hk30.
    have hkend :
        ! (k0 \ult
           (KeygenM23SingularFFTSpec.fft_schedule_prefix
              data0 roots0 (W64.to_uint r0 - 1)).`3) by
      assumption.
    have hparams3 :
        TargetKeygenM23SingularTotality.m23sing_total_fft_outer_state
          r0
          (KeygenM23SingularFFTSpec.fft_schedule_prefix
             data0 roots0 (W64.to_uint r0 - 1)).`2
          (KeygenM23SingularFFTSpec.fft_schedule_prefix
             data0 roots0 (W64.to_uint r0 - 1)).`3
          (KeygenM23SingularFFTSpec.fft_schedule_prefix
             data0 roots0 (W64.to_uint r0 - 1)).`4 by
      assumption.
    have hrbody3 : r0 \ule W64.of_int 8 by assumption.
    have hnmod3 :
        W64.to_uint n0 %%
          W64.to_uint
            (KeygenM23SingularFFTSpec.fft_schedule_prefix
               data0 roots0 (W64.to_uint r0 - 1)).`2 = 0 by
      assumption.
    have hnlt3 :
        W64.to_uint n0 <
          KeygenM23SingularFFTSpec.fft_words_i by
      assumption.
    have hk3 :
        W64.to_uint k0 <=
          W64.to_uint
            (KeygenM23SingularFFTSpec.fft_schedule_prefix
               data0 roots0 (W64.to_uint r0 - 1)).`3 by
      assumption.
    have hm3 :
        1 <=
          W64.to_uint
            (KeygenM23SingularFFTSpec.fft_schedule_prefix
               data0 roots0 (W64.to_uint r0 - 1)).`2 <= 256.
    + apply
        (TargetKeygenM23SingularTotality.m23sing_total_fft_state_body_m_bound
           r0
           (KeygenM23SingularFFTSpec.fft_schedule_prefix
              data0 roots0 (W64.to_uint r0 - 1)).`2
           (KeygenM23SingularFFTSpec.fft_schedule_prefix
              data0 roots0 (W64.to_uint r0 - 1)).`3
           (KeygenM23SingularFFTSpec.fft_schedule_prefix
              data0 roots0 (W64.to_uint r0 - 1)).`4).
      + exact hparams3.
      + exact hrbody3.
    have hkmd2 :
        W64.to_uint k0 =
          W64.to_uint
            (KeygenM23SingularFFTSpec.fft_schedule_prefix
               data0 roots0 (W64.to_uint r0 - 1)).`3.
    + move: hkend hk3.
      rewrite W64.ultE.
      smt().
    have hblock0 :
        0 <=
          W64.to_uint n0 %/
            W64.to_uint
              (KeygenM23SingularFFTSpec.fft_schedule_prefix
                 data0 roots0 (W64.to_uint r0 - 1)).`2 by
      smt(@IntDiv).
    have hn3 :
        W64.to_uint n0 =
          (W64.to_uint n0 %/
             W64.to_uint
               (KeygenM23SingularFFTSpec.fft_schedule_prefix
                  data0 roots0 (W64.to_uint r0 - 1)).`2) *
          W64.to_uint
            (KeygenM23SingularFFTSpec.fft_schedule_prefix
               data0 roots0 (W64.to_uint r0 - 1)).`2 by
      smt(@IntDiv).
    have hnsmall :
        W64.to_uint n0 +
          W64.to_uint
            (KeygenM23SingularFFTSpec.fft_schedule_prefix
               data0 roots0 (W64.to_uint r0 - 1)).`2 <
        W64.modulus by
      smt(W64.to_uint_cmp).
    have hquot :
        W64.to_uint
          (n0 +
           (KeygenM23SingularFFTSpec.fft_schedule_prefix
              data0 roots0 (W64.to_uint r0 - 1)).`2) %/
          W64.to_uint
            (KeygenM23SingularFFTSpec.fft_schedule_prefix
               data0 roots0 (W64.to_uint r0 - 1)).`2 =
        W64.to_uint n0 %/
          W64.to_uint
            (KeygenM23SingularFFTSpec.fft_schedule_prefix
               data0 roots0 (W64.to_uint r0 - 1)).`2 + 1.
    + rewrite W64.to_uintD_small 1:hnsmall.
      smt(@IntDiv).
    have hstepbound :
        (W64.to_uint n0 %/
           W64.to_uint
             (KeygenM23SingularFFTSpec.fft_schedule_prefix
                data0 roots0 (W64.to_uint r0 - 1)).`2 + 1) *
        W64.to_uint
          (KeygenM23SingularFFTSpec.fft_schedule_prefix
             data0 roots0 (W64.to_uint r0 - 1)).`2 <= 256.
    + apply
        (TargetKeygenM23SingularTotality.m23sing_total_fft_state_block_step_bound
           r0
           (KeygenM23SingularFFTSpec.fft_schedule_prefix
              data0 roots0 (W64.to_uint r0 - 1)).`2
           (KeygenM23SingularFFTSpec.fft_schedule_prefix
              data0 roots0 (W64.to_uint r0 - 1)).`3
           (KeygenM23SingularFFTSpec.fft_schedule_prefix
              data0 roots0 (W64.to_uint r0 - 1)).`4
           (W64.to_uint n0 %/
            W64.to_uint
              (KeygenM23SingularFFTSpec.fft_schedule_prefix
                 data0 roots0 (W64.to_uint r0 - 1)).`2)).
      + exact hparams3.
      + exact hrbody3.
      + exact hblock0.
      + smt().
    split.
    + rewrite W64.to_uintD_small 1:hnsmall
              /KeygenM23SingularFFTSpec.fft_words_i.
      smt().
    split.
    + rewrite W64.to_uintD_small 1:hnsmall.
      smt(@IntDiv).
    rewrite hquot
            KeygenM23SingularFFTSpec.fft_blocks_prefixS 1:hblock0.
    rewrite /KeygenM23SingularFFTSpec.fft_block_step.
    rewrite
      (fft_block_word n0
         (KeygenM23SingularFFTSpec.fft_schedule_prefix
            data0 roots0 (W64.to_uint r0 - 1)).`2
         (W64.to_uint n0 %/
          W64.to_uint
            (KeygenM23SingularFFTSpec.fft_schedule_prefix
               data0 roots0 (W64.to_uint r0 - 1)).`2)
         hblock0 hn3).
    by rewrite hkmd2.
  auto => &hr [[hroot [hparams hdata]] hrbody].
  split.
  + split; first exact hroot.
    split; first exact hparams.
    split; first exact hrbody.
    rewrite W64.to_uint0
            /KeygenM23SingularFFTSpec.fft_words_i
            KeygenM23SingularFFTSpec.fft_blocks_prefix0 /=.
    exact hdata.
  move=> data1 m0 md20 n0 r0 rootsp1 stride0 hdone
          [hroot1 [hparams1 [hrbody1 [hnbound [hnmod hdata1]]]]].
  have hn256 :
      W64.to_uint n0 =
        KeygenM23SingularFFTSpec.fft_words_i.
  + move: hdone hnbound.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23SingularFFTSpec.fft_words_i /=.
    smt().
  have hm :
      1 <= W64.to_uint m0 <= 256.
  + apply
      (TargetKeygenM23SingularTotality.m23sing_total_fft_state_body_m_bound
         r0 m0 md20 stride0).
    + move: hparams1.
      rewrite /fft_params_at.
      trivial.
    + exact hrbody1.
  have hblockcount :
      W64.to_uint n0 %/ W64.to_uint m0 =
        KeygenM23SingularFFTSpec.fft_block_count m0.
  + by rewrite hn256 /KeygenM23SingularFFTSpec.fft_block_count.
  have hrpos : 1 <= W64.to_uint r0.
  + move: hparams1.
    rewrite /fft_params_at
            /TargetKeygenM23SingularTotality.m23sing_total_fft_outer_state.
    move=> /= [hstate _].
    move: hstate.
    by do 8! (case=> />); trivial.
  have hrpred0 : 0 <= W64.to_uint r0 - 1 by smt().
  have hrsucc :
      W64.to_uint (r0 + W64.one) - 1 =
        (W64.to_uint r0 - 1) + 1.
  + have hrle : W64.to_uint r0 <= 8.
    + move: hrbody1.
      rewrite W64.uleE W64.of_uintK /=.
      trivial.
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    smt().
  rewrite /SLH64.protect_ptr /SLH64.protect_64.
  split; first exact hroot1.
  split.
  + rewrite /fft_params_at hrsucc
            KeygenM23SingularFFTSpec.fft_schedule_prefixS 1:hrpred0.
    rewrite /KeygenM23SingularFFTSpec.fft_round_step.
    split.
    + apply
        (TargetKeygenM23SingularTotality.m23sing_total_fft_state_step
           r0 m0 md20 stride0).
      + move: hparams1.
        rewrite /fft_params_at.
        trivial.
      + exact hrbody1.
    move: hparams1.
    rewrite /fft_params_at.
    smt().
  have hparamrels :
      m0 =
        (KeygenM23SingularFFTSpec.fft_schedule_prefix
           data0 roots0 (W64.to_uint r0 - 1)).`2 /\
      md20 =
        (KeygenM23SingularFFTSpec.fft_schedule_prefix
           data0 roots0 (W64.to_uint r0 - 1)).`3 /\
      stride0 =
        (KeygenM23SingularFFTSpec.fft_schedule_prefix
           data0 roots0 (W64.to_uint r0 - 1)).`4.
  + move: hparams1.
    rewrite /fft_params_at.
    trivial.
  move: hparamrels =>
    [hmparam [hmdparam hstrideparam]].
  rewrite /fft_stage_start hrsucc
          KeygenM23SingularFFTSpec.fft_schedule_prefixS 1:hrpred0.
  rewrite /KeygenM23SingularFFTSpec.fft_round_step
          /KeygenM23SingularFFTSpec.fft_stage.
  rewrite /= -hmparam -hmdparam -hstrideparam -hblockcount.
  exact hdata1.
auto => />.
split.
+ split.
  + rewrite KeygenM23SingularFFTSpec.fft_schedule_prefix0.
    trivial.
  rewrite /fft_stage_start W64.to_uint1
          KeygenM23SingularFFTSpec.fft_schedule_prefix0.
  trivial.
move=> r0 hdone hstate.
have hr9 : W64.to_uint r0 = 9.
+ move: hstate hdone.
  rewrite /TargetKeygenM23SingularTotality.m23sing_total_fft_outer_state
          W64.uleE W64.of_uintK /=.
  by do 8! (case=> />); smt().
rewrite /KeygenM23SingularFFTSpec.fft_full
        /KeygenM23SingularFFTSpec.fft_stages_i
        /fft_stage_start hr9 /=.
trivial.
qed.

end TargetKeygenM23SingularFFT.
