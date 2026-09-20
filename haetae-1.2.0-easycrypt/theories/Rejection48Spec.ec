require import AllCore IntDiv List Distr DInterval StdOrder.
from Jasmin require import JModel_x86.
import IntOrder RealOrder RField.

(* The zero guard is the actual rounded W64 output, not the raw candidate. *)
op rejection48_word (rej threshold rounded : W64.t) : W64.t =
  (((rej `^` (rej `&` W64.one)) - threshold) `|>>>` 63) `&`
    (((rounded `|` (W64.zero - rounded)) `>>>` 63) `|` rej) `&` W64.one.

op rejection48_accept (u threshold : int) (rounded : W64.t) : bool =
  2 * (u %/ 2) < threshold /\ (rounded <> W64.zero \/ odd u).

op rejection48_ceil2 (threshold : int) : int = (threshold + 1) %/ 2.
op rejection48_cutoff (threshold : int) : int =
  min 140737488355328 (max 0 (rejection48_ceil2 threshold)).

op rejection48_factor (rounded : W64.t) : real =
  if rounded = W64.zero then 1%r / 2%r else 1%r.

op rejection48_base_probability (threshold : int) : real =
  (rejection48_cutoff threshold)%r / 140737488355328%r.

op rejection48_probability (threshold : int) (rounded : W64.t) : real =
  rejection48_factor rounded * rejection48_base_probability threshold.

(* Explicit ideal rejection input only; no SHAKE law is assumed. *)
op rejection48_uniform : int distr = DInterval.dinter 0 281474976710655.

lemma rejection48_ceil2_bounds threshold :
  threshold <= 2 * rejection48_ceil2 threshold <= threshold + 1.
proof.
have hd := divz_eq (threshold + 1) 2.
have hr := modz_cmp (threshold + 1) 2.
rewrite /rejection48_ceil2; smt().
qed.

lemma rejection48_cutoff_bounds threshold :
  0 <= rejection48_cutoff threshold <= 140737488355328.
proof. rewrite /rejection48_cutoff /min /max; smt(). qed.

lemma rejection48_threshold_test u threshold :
  (2 * (u %/ 2) < threshold) = (u < 2 * rejection48_ceil2 threshold).
proof.
have hu := divz_eq u 2.
have hr := modz_cmp u 2.
have he := rejection48_ceil2_bounds threshold.
smt().
qed.

lemma rejection48_cutoff_test u threshold :
  0 <= u < 281474976710656 =>
  (2 * (u %/ 2) < threshold) = (u < 2 * rejection48_cutoff threshold).
proof.
move=> hu; rewrite rejection48_threshold_test /rejection48_cutoff /min /max.
smt().
qed.

lemma rejection48_accept_cutoff u threshold rounded :
  0 <= u < 281474976710656 =>
  rejection48_accept u threshold rounded =
    (u < 2 * rejection48_cutoff threshold /\ (rounded <> W64.zero \/ odd u)).
proof. move=> hu; by rewrite /rejection48_accept rejection48_cutoff_test. qed.

lemma rejection48_base_bounds threshold :
  0%r <= rejection48_base_probability threshold <= 1%r.
proof.
have hc := rejection48_cutoff_bounds threshold.
rewrite /rejection48_base_probability; smt().
qed.

lemma rejection48_saturates threshold : 281474976710656 <= threshold =>
  rejection48_base_probability threshold = 1%r.
proof.
move=> he; have hc := rejection48_ceil2_bounds threshold.
have hcut : rejection48_cutoff threshold = 140737488355328 by
  rewrite /rejection48_cutoff /min /max; smt().
by rewrite /rejection48_base_probability hcut.
qed.

lemma rejection48_nonpositive threshold : threshold <= 0 =>
  rejection48_base_probability threshold = 0%r.
proof.
move=> he; have hc := rejection48_ceil2_bounds threshold.
have hcut : rejection48_cutoff threshold = 0 by
  rewrite /rejection48_cutoff /min /max; smt().
by rewrite /rejection48_base_probability hcut.
qed.

(* Clipping at either endpoint cannot worsen the stated target error.  The
   upward rounding of an odd threshold contributes at most one unit / 2^48. *)
lemma rejection48_quantization threshold (p epsilon : real) :
  0%r <= p <= 1%r =>
  `|threshold%r / 281474976710656%r - p| <= epsilon =>
  `|rejection48_base_probability threshold - p| <=
    epsilon + 1%r / 281474976710656%r.
proof.
move=> hp he.
have hc := rejection48_ceil2_bounds threshold.
rewrite ler_norml in he.
rewrite ler_norml /rejection48_base_probability /rejection48_cutoff /min /max.
smt().
qed.

lemma rejection48_probability_error threshold rounded (p epsilon : real) :
  0%r <= p <= 1%r =>
  `|threshold%r / 281474976710656%r - p| <= epsilon =>
  `|rejection48_probability threshold rounded - rejection48_factor rounded * p| <=
    rejection48_factor rounded * (epsilon + 1%r / 281474976710656%r).
proof.
move=> hp he.
have h := rejection48_quantization threshold p epsilon hp he.
rewrite ler_norml in h.
rewrite ler_norml /rejection48_probability /rejection48_factor.
case (rounded = W64.zero); smt().
qed.
