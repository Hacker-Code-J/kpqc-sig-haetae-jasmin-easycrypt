require import AllCore IntDiv List Distr DList StdRing StdOrder.
from Jasmin require import JModel_x86.
require import GaussianIidBufferSpec GaussianIidBufferPath GaussianIidProgress.
import RField RealOrder.

lemma git_consume_advance (values : BArray32768.t) (squares : BArray16.t)
    (count : BArray8.t) (pending : W8.t list) (n accepted : int)
    (dummy : bool) (offset : int) :
  0 <= accepted <= n => n <= 512 =>
  accepted <= accepted + W64.to_uint (BArray8.get64
    (gib_consume values squares count pending (n-accepted) dummy offset).`3 0) <= n.
proof.
  move=> ha hn.
  rewrite gib_consume_count 1:/#.
  have hs := size_ge0 (gib_accepted pending).
  rewrite /min; smt().
qed.

lemma git_consume_strict (values : BArray32768.t) (squares : BArray16.t)
    (count : BArray8.t) (pending : W8.t list) (n accepted : int)
    (dummy : bool) (offset : int) :
  0 <= accepted < n => n <= 512 => gib_accepted pending <> [] =>
  accepted < accepted + W64.to_uint (BArray8.get64
    (gib_consume values squares count pending (n-accepted) dummy offset).`3 0).
proof.
  move=> ha hn hp.
  rewrite gib_consume_count 1:/#.
  have hs : 0 < size (gib_accepted pending) by smt(size_eq0 size_ge0).
  rewrite /min; smt().
qed.

lemma git_refill_progress_probability (values : BArray32768.t) (squares : BArray16.t)
    (count : BArray8.t) (pending : W8.t list) (n accepted : int)
    (dummy : bool) (offset : int) &m :
  0 <= accepted < n => n <= 512 =>
  1%r/7%r <= mu gib_block (fun bytes =>
    n - (accepted + W64.to_uint (BArray8.get64
      (gib_consume values squares count (gib_remainder pending ++ bytes)
        (n-accepted) dummy offset).`3 0)) < n-accepted).
proof.
  move=> ha hn.
  have [_ ht] := gib_remainder_size pending.
  have hp := gip_refill_progress (gib_remainder pending) &m _; first smt().
  have hl := mu_le gib_block
    (fun bytes => gib_accepted (gib_remainder pending ++ bytes) <> [])
    (fun bytes => n - (accepted + W64.to_uint (BArray8.get64
      (gib_consume values squares count (gib_remainder pending ++ bytes)
        (n-accepted) dummy offset).`3 0)) < n-accepted) _.
  + move=> bytes hb haccepted.
    have h := git_consume_strict values squares count (gib_remainder pending ++ bytes)
      n accepted dummy offset ha hn haccepted; smt().
  exact (ler_trans _ _ _ hp hl).
qed.

(* The functional array operations are total. Only the bounded requested
   count is needed for termination; input arrays are completely arbitrary. *)
lemma git_functional_range_total (n0 : int) : 0 <= n0 <= 512 =>
  phoare [GaussianIidBufferFunctional.sample : n = n0 ==> true] = 1%r.
proof.
  move=> hn.
  conseq (_ : _ ==> _ : >= 1%r) => //.
  proc.
  seq 4 : (n = n0) => //.
  + while (n = n0 /\ 0 <= block <= 49) (49-block).
    - move=> z; conseq (_ : _ ==> _ : = 1%r) => //.
      wp; rnd; skip; auto => />.
      move=> &hr hb0 hb49 hguard.
      smt(gib_block_ll).
    auto => />; smt().
  seq 4 : (n = n0 /\ 0 <= accepted <= n0) => //.
  + conseq (_ : _ ==> _ : = 1%r) => //.
    auto => />.
    move=> &hr.
    have h := gib_consume_count rp{hr} sqsump{hr} count{hr} (drop 32 pending{hr})
      n0 (n0=257) sample_offset{hr} hn.
    have hs := size_ge0 (gib_accepted (drop 32 pending{hr})).
    rewrite h /min; smt().
  conseq (_ : _ ==> _ : = 1%r) => //.
  while (n = n0 /\ 0 <= accepted <= n0)
    (n0-accepted) n0 (1%r/7%r) => //=.
  + smt().
  + move=> ih.
    seq 5 : (n = n0 /\ 0 <= accepted <= n0) => //.
    + wp; rnd; wp; skip; auto => />.
      move=> &hr ha0 han hguard.
      apply eq1_mu; first exact gib_block_ll.
      move=> bytes hb /=.
      have h := git_consume_advance rp{hr} sqsump{hr} count{hr}
        (gib_remainder pending{hr} ++ bytes) n0 accepted{hr}
        (n0 = 257) (sample_offset{hr}+accepted{hr}) _ _; smt().
    + wp; rnd; wp; skip; auto => />.
      move=> &hr ha0 han hguard.
      apply mu0_false => bytes hb /=.
      have h := git_consume_advance rp{hr} sqsump{hr} count{hr}
        (gib_remainder pending{hr} ++ bytes) n0 accepted{hr}
        (n0 = 257) (sample_offset{hr}+accepted{hr}) _ _; smt().
  + wp; rnd; wp; skip; auto => />.
    move=> &hr ha0 han hguard.
    apply eq1_mu; first exact gib_block_ll.
    move=> bytes hb /=.
    have h := git_consume_advance rp{hr} sqsump{hr} count{hr}
      (gib_remainder pending{hr} ++ bytes) n0 accepted{hr}
      (n0 = 257) (sample_offset{hr}+accepted{hr}) _ _; smt().
  split; first smt().
  move=> z; wp; rnd; wp; skip; auto => />.
  move=> &hr ha0 han hguard.
  apply (git_refill_progress_probability rp{hr} sqsump{hr} count{hr} pending{hr}
    n0 accepted{hr} (n0=257) (sample_offset{hr}+accepted{hr}) &hr); smt().
qed.

lemma git_functional_total
    (initial : BArray32768.t) (initial_signs : BArray512.t) (initial_squares : BArray16.t)
    (n0 sample_offset0 sign_offset0 : int) :
  phoare [GaussianIidBufferFunctional.sample :
    rp = initial /\ signsp = initial_signs /\ sqsump = initial_squares /\
    n = n0 /\ sample_offset = sample_offset0 /\ sign_offset = sign_offset0 /\
    gib_bounds n0 sample_offset0 sign_offset0 ==> true] = 1%r.
proof.
  bypr => &m hpre.
  have hb : gib_bounds n0 sample_offset0 sign_offset0 by smt().
  have hn : 0 <= n0 <= 512 by move: hb; rewrite /gib_bounds; smt().
  by byphoare (git_functional_range_total n0 hn) => //; smt().
qed.

lemma git_functional_lossless :
  phoare [GaussianIidBufferFunctional.sample :
    gib_bounds n sample_offset sign_offset ==> true] = 1%r.
proof.
  exists* rp, signsp, sqsump, n, sample_offset, sign_offset;
    elim* => initial initial_signs initial_squares n0 sample_offset0 sign_offset0.
  by conseq (git_functional_total initial initial_signs initial_squares
    n0 sample_offset0 sign_offset0) => />.
qed.
