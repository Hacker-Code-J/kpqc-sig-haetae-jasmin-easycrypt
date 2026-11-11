require import AllCore IntDiv List Distr DList.
from Jasmin require import JModel_x86.
require import GaussianPayloadSpec GaussianPayloadBufferSpec GaussianPayloadBufferPath
  GaussianPayloadTrace GaussianIidBufferSpec GaussianIidBufferPath GaussianUniformBytes
  HyperballGaussianBounds.

lemma gpt_state_count previous initial_values initial_squares n offset history values squares :
  gpt_state previous initial_values initial_squares n offset history values squares =>
  size history <= n.
proof. by rewrite /gpt_state; smt(). qed.

lemma gpt_buffer_correct previous initial_values initial_signs initial_squares n0 offset0 signoff0 :
  gib_bounds n0 offset0 signoff0 =>
  hb_cumulative_square_bound previous initial_squares => previous+n0 <= 2818 =>
  hoare [GaussianPayloadBuffer.sample :
    rp=initial_values /\ signsp=initial_signs /\ sqsump=initial_squares /\
    n=n0 /\ sample_offset=offset0 /\ sign_offset=signoff0 ==>
    size res.`2=n0 /\
    gpt_state previous initial_values initial_squares n0 offset0 res.`2 res.`1.`1 res.`1.`3].
proof.
  move=> hb hc hbudget.
  have hn : n0=256 \/ n0=257 by move: hb; rewrite /gib_bounds; smt().
  have hoff : 0 <= offset0 by move: hb; rewrite /gib_bounds; smt().
  have hcap : offset0+n0 <= 4096 by move: hb; rewrite /gib_bounds; smt().
  proc.
  while (n=n0 /\ sample_offset=offset0 /\ accepted=size history /\ size pending<=8192 /\
    gpt_state previous initial_values initial_squares n0 offset0 history rp sqsump).
  + wp; rnd; wp; skip; auto => />.
    move=> &hr hbytes hstate hactive bytes hdraw.
    have hp : size (gib_remainder pending{hr}++bytes) <= 8192 by
      have h := gpb_refill_size pending{hr} bytes hdraw; smt().
    have [hq [hcount hnext]] := gpt_consume previous initial_values initial_squares
      rp{hr} sqsump{hr} count{hr} (gib_remainder pending{hr}++bytes) n0 offset0 history{hr}
      hn hoff hcap hp hbudget hactive hstate.
    smt().
  wp; rnd; wp; skip; auto => />.
  move=> bytes hdraw.
  have hp : size (drop 32 bytes)<=8192 by
    have h := gpb_initial_size bytes hdraw; smt().
  have hinit := gpt_initial previous initial_values initial_squares n0 offset0 _ hc; first smt().
  have hactive : 0<n0 by smt().
  have [hq [hcount hnext]] := gpt_consume previous initial_values initial_squares
    initial_values initial_squares witness (drop 32 bytes) n0 offset0 []
    hn hoff hcap hp hbudget hactive hinit.
  smt(gpt_state_count).
qed.

lemma gpt_buffer_total previous initial_values initial_signs initial_squares n0 offset0 signoff0 :
  gib_bounds n0 offset0 signoff0 =>
  hb_cumulative_square_bound previous initial_squares => previous+n0 <= 2818 =>
  phoare [GaussianPayloadBuffer.sample :
    rp=initial_values /\ signsp=initial_signs /\ sqsump=initial_squares /\
    n=n0 /\ sample_offset=offset0 /\ sign_offset=signoff0 ==>
    size res.`2=n0 /\
    gpt_state previous initial_values initial_squares n0 offset0 res.`2 res.`1.`1 res.`1.`3] = 1%r.
proof.
  move=> hb hc hbudget.
  conseq gpb_buffer_lossless
    (gpt_buffer_correct previous initial_values initial_signs initial_squares n0 offset0 signoff0
      hb hc hbudget) => />.
  move: hb; rewrite /gib_bounds; smt().
qed.
