require import AllCore IntDiv Ring StdOrder Real.

from Jasmin require import JModel_x86.

import RField RealOrder.

require import BArray2048.
require import
  KeygenM23ComplexReal
  KeygenM23SingularFFTSpec
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTButterflyBridge.

import KeygenM23SingularFFTButterflyBridge.
import KeygenM23ComplexReal.
import KeygenM23SingularFFTInitBridge.

theory KeygenM23SingularFFTKPrefixBridge.

op fft_k_even_index (n : W64.t) (k : int) : int =
  W64.to_uint n + k.

op fft_k_odd_index (n md2 : W64.t) (k : int) : int =
  fft_k_even_index n k + W64.to_uint md2.

op fft_k_twid_index (stride : W64.t) (k : int) : int =
  k * W64.to_uint stride.

op fft_k_schedule_wf (n md2 stride : W64.t) (processed : int) : bool =
  0 <= processed /\
  processed <= W64.to_uint md2 /\
  W64.to_uint n + W64.to_uint md2 + processed <= 256 /\
  (forall k, 0 <= k < processed =>
    k * W64.to_uint stride < 256).

op fft_k_prefix_safe
    (data roots : BArray2048.t) (n md2 stride : W64.t)
    (processed : int) : bool =
  forall k, 0 <= k < processed =>
    fft_butterfly_safe_at
      (KeygenM23SingularFFTSpec.fft_k_prefix
        data roots n md2 stride k)
      roots
      (fft_k_even_index n k)
      (fft_k_odd_index n md2 k)
      (fft_k_twid_index stride k).

op fft_k_prefix_decode_at
    (data roots : BArray2048.t) (n md2 stride : W64.t)
    (processed j : int) : complex =
  if W64.to_uint n <= j < W64.to_uint n + processed
  then
    let k = j - W64.to_uint n in
    fft_butterfly_even_decode_at
      (KeygenM23SingularFFTSpec.fft_k_prefix
        data roots n md2 stride k)
      roots j (j + W64.to_uint md2) (fft_k_twid_index stride k)
  else if W64.to_uint n + W64.to_uint md2 <= j /\
          j < W64.to_uint n + W64.to_uint md2 + processed
  then
    let k = j - (W64.to_uint n + W64.to_uint md2) in
    fft_butterfly_odd_decode_at
      (KeygenM23SingularFFTSpec.fft_k_prefix
        data roots n md2 stride k)
      roots (j - W64.to_uint md2) j (fft_k_twid_index stride k)
  else fft_decode_at data j.

lemma fft_k_schedule_wf_prev
    (n md2 stride : W64.t) (processed : int) :
  0 <= processed =>
  fft_k_schedule_wf n md2 stride (processed + 1) =>
  fft_k_schedule_wf n md2 stride processed.
proof.
rewrite /fft_k_schedule_wf.
move=> hp0 [_ [hpmd2 [hpdata htwid]]].
split.
+ exact hp0.
split.
+ smt().
split.
+ smt().
move=> k hk.
apply htwid.
smt().
qed.

lemma fft_k_prefix_safe_prev
    (data roots : BArray2048.t) (n md2 stride : W64.t)
    (processed : int) :
  0 <= processed =>
  fft_k_prefix_safe data roots n md2 stride (processed + 1) =>
  fft_k_prefix_safe data roots n md2 stride processed.
proof.
move=> hprocessed hsafe.
rewrite /fft_k_prefix_safe.
move=> k [hk0 hkprocessed].
have hsucc : processed < processed + 1.
+ clear hsafe hprocessed hk0 hkprocessed.
  smt().
have hkS : 0 <= k < processed + 1.
+ clear hsafe hprocessed.
  smt().
exact (hsafe k hkS).
qed.

lemma fft_k_even_index_bounds
    (n md2 stride : W64.t) (processed k : int) :
  fft_k_schedule_wf n md2 stride processed =>
  0 <= k < processed =>
  0 <= fft_k_even_index n k < 256.
proof.
rewrite /fft_k_schedule_wf /fft_k_even_index.
smt(W64.to_uint_cmp).
qed.

lemma fft_k_odd_index_bounds
    (n md2 stride : W64.t) (processed k : int) :
  fft_k_schedule_wf n md2 stride processed =>
  0 <= k < processed =>
  0 <= fft_k_odd_index n md2 k < 256.
proof.
rewrite /fft_k_schedule_wf /fft_k_odd_index /fft_k_even_index.
smt(W64.to_uint_cmp).
qed.

lemma fft_k_twid_index_bounds
    (n md2 stride : W64.t) (processed k : int) :
  fft_k_schedule_wf n md2 stride processed =>
  0 <= k < processed =>
  0 <= fft_k_twid_index stride k < 256.
proof.
rewrite /fft_k_schedule_wf /fft_k_twid_index.
move=> [_ [_ [_ htwid]]] [hk0 hkprocessed].
have hk : 0 <= k < processed by smt().
have htwidk := htwid k hk.
have hstride : 0 <= W64.to_uint stride by smt(W64.to_uint_cmp).
have hproduct0 : 0 <= k * W64.to_uint stride by
  exact (IntOrder.mulr_ge0 k (W64.to_uint stride) hk0 hstride).
clear htwid hstride.
smt().
qed.

lemma fft_k_even_odd_neq
    (n md2 stride : W64.t) (processed k : int) :
  fft_k_schedule_wf n md2 stride processed =>
  0 <= k < processed =>
  fft_k_even_index n k <> fft_k_odd_index n md2 k.
proof.
rewrite /fft_k_schedule_wf /fft_k_even_index /fft_k_odd_index.
smt(W64.to_uint_cmp).
qed.

lemma fft_k_even_wordE (n : W64.t) (k : int) :
  n + W64.of_int k = W64.of_int (fft_k_even_index n k).
proof.
by rewrite /fft_k_even_index -(W64.to_uintK' n) W64.of_intD'.
qed.

lemma fft_k_odd_wordE (n md2 : W64.t) (k : int) :
  n + W64.of_int k + md2 = W64.of_int (fft_k_odd_index n md2 k).
proof.
rewrite /fft_k_odd_index /fft_k_even_index.
by rewrite -(W64.to_uintK' n) -(W64.to_uintK' md2)
           !W64.of_intD'.
qed.

lemma fft_k_twid_wordE (stride : W64.t) (k : int) :
  W64.of_int k * stride = W64.of_int (fft_k_twid_index stride k).
proof.
rewrite /fft_k_twid_index.
by rewrite -(W64.to_uintK' stride) W64.of_intM'.
qed.

lemma fft_k_step_decode_written
    (data roots : BArray2048.t) (n md2 stride : W64.t) (k : int) :
  0 <= k =>
  fft_k_schedule_wf n md2 stride (k + 1) =>
  fft_butterfly_safe_at
    data roots
    (fft_k_even_index n k)
    (fft_k_odd_index n md2 k)
    (fft_k_twid_index stride k) =>
  let output =
    KeygenM23SingularFFTSpec.fft_k_step roots n md2 stride data k in
  fft_decode_at output (fft_k_even_index n k) =
    fft_butterfly_even_decode_at
      data roots
      (fft_k_even_index n k)
      (fft_k_odd_index n md2 k)
      (fft_k_twid_index stride k) /\
  fft_decode_at output (fft_k_odd_index n md2 k) =
    fft_butterfly_odd_decode_at
      data roots
      (fft_k_even_index n k)
      (fft_k_odd_index n md2 k)
      (fft_k_twid_index stride k).
proof.
move=> hk0 hwf hsafe /=.
have heven :
  0 <= fft_k_even_index n k < 256.
+ apply (fft_k_even_index_bounds n md2 stride (k + 1) k hwf).
  smt().
have hodd :
  0 <= fft_k_odd_index n md2 k < 256.
+ apply (fft_k_odd_index_bounds n md2 stride (k + 1) k hwf).
  smt().
have htwid :
  0 <= fft_k_twid_index stride k < 256.
+ apply (fft_k_twid_index_bounds n md2 stride (k + 1) k hwf).
  smt().
have hneq :
  fft_k_even_index n k <> fft_k_odd_index n md2 k.
+ apply (fft_k_even_odd_neq n md2 stride (k + 1) k hwf).
  smt().
rewrite /KeygenM23SingularFFTSpec.fft_k_step /=.
rewrite fft_k_odd_wordE fft_k_even_wordE fft_k_twid_wordE.
exact
  (fft_butterfly_decode_written
    data roots
    (fft_k_even_index n k)
    (fft_k_odd_index n md2 k)
    (fft_k_twid_index stride k)
    heven hodd htwid hneq hsafe).
qed.

lemma fft_k_step_decode_frame
    (data roots : BArray2048.t) (n md2 stride : W64.t)
    (k j : int) :
  0 <= k =>
  fft_k_schedule_wf n md2 stride (k + 1) =>
  0 <= j < 256 =>
  j <> fft_k_even_index n k =>
  j <> fft_k_odd_index n md2 k =>
  fft_decode_at
    (KeygenM23SingularFFTSpec.fft_k_step
      roots n md2 stride data k)
    j =
  fft_decode_at data j.
proof.
move=> hk0 hwf hj hje hjo.
have heven :
  0 <= fft_k_even_index n k < 256.
+ apply (fft_k_even_index_bounds n md2 stride (k + 1) k hwf).
  smt().
have hodd :
  0 <= fft_k_odd_index n md2 k < 256.
+ apply (fft_k_odd_index_bounds n md2 stride (k + 1) k hwf).
  smt().
have htwid :
  0 <= fft_k_twid_index stride k < 256.
+ apply (fft_k_twid_index_bounds n md2 stride (k + 1) k hwf).
  smt().
rewrite /KeygenM23SingularFFTSpec.fft_k_step /=.
rewrite fft_k_odd_wordE fft_k_even_wordE fft_k_twid_wordE.
exact
  (fft_butterfly_decode_frame
    data roots
    (fft_k_even_index n k)
    (fft_k_odd_index n md2 k)
    (fft_k_twid_index stride k)
    j
    heven hodd htwid hj hje hjo).
qed.

lemma fft_k_prefix_decode_at_evenS
    (data roots : BArray2048.t) (n md2 stride : W64.t)
    (processed : int) :
  0 <= processed =>
  fft_k_schedule_wf n md2 stride (processed + 1) =>
  fft_k_prefix_decode_at
    data roots n md2 stride
    (processed + 1) (fft_k_even_index n processed) =
  fft_butterfly_even_decode_at
    (KeygenM23SingularFFTSpec.fft_k_prefix
      data roots n md2 stride processed)
    roots
    (fft_k_even_index n processed)
    (fft_k_odd_index n md2 processed)
    (fft_k_twid_index stride processed).
proof.
move=> hproc hwf.
rewrite /fft_k_prefix_decode_at /fft_k_even_index /fft_k_odd_index.
have hmd2 : processed < W64.to_uint md2 by
  move: hwf; rewrite /fft_k_schedule_wf; smt().
rewrite ifT 1:/#.
rewrite /fft_k_twid_index /fft_k_even_index /=.
have hk : W64.to_uint n + processed - W64.to_uint n = processed by
  ring.
by rewrite hk.
qed.

lemma fft_k_prefix_decode_at_oddS
    (data roots : BArray2048.t) (n md2 stride : W64.t)
    (processed : int) :
  0 <= processed =>
  fft_k_schedule_wf n md2 stride (processed + 1) =>
  fft_k_prefix_decode_at
    data roots n md2 stride
    (processed + 1) (fft_k_odd_index n md2 processed) =
  fft_butterfly_odd_decode_at
    (KeygenM23SingularFFTSpec.fft_k_prefix
      data roots n md2 stride processed)
    roots
    (fft_k_even_index n processed)
    (fft_k_odd_index n md2 processed)
    (fft_k_twid_index stride processed).
proof.
move=> hproc hwf.
rewrite /fft_k_prefix_decode_at /fft_k_even_index /fft_k_odd_index.
have hmd2 : processed < W64.to_uint md2 by
  move: hwf; rewrite /fft_k_schedule_wf; smt().
rewrite ifF 1:/# ifT 1:/#.
rewrite /fft_k_twid_index /fft_k_odd_index /fft_k_even_index /=.
have hk :
  W64.to_uint n + processed + W64.to_uint md2 -
    (W64.to_uint n + W64.to_uint md2) = processed by
  ring.
have heven :
  W64.to_uint n + processed + W64.to_uint md2 -
    W64.to_uint md2 = W64.to_uint n + processed by
  ring.
by rewrite hk heven.
qed.

lemma fft_k_prefix_decode_at_pending_even
    (data roots : BArray2048.t) (n md2 stride : W64.t)
    (processed : int) :
  0 <= processed =>
  fft_k_schedule_wf n md2 stride (processed + 1) =>
  fft_k_prefix_decode_at
    data roots n md2 stride processed
    (fft_k_even_index n processed) =
  fft_decode_at data (fft_k_even_index n processed).
proof.
move=> hproc hwf.
rewrite /fft_k_prefix_decode_at /fft_k_even_index /fft_k_odd_index.
have hmd2 : processed < W64.to_uint md2 by
  move: hwf; rewrite /fft_k_schedule_wf; smt().
by rewrite ifF 1:/# ifF 1:/#.
qed.

lemma fft_k_prefix_decode_at_pending_odd
    (data roots : BArray2048.t) (n md2 stride : W64.t)
    (processed : int) :
  0 <= processed =>
  fft_k_schedule_wf n md2 stride (processed + 1) =>
  fft_k_prefix_decode_at
    data roots n md2 stride processed
    (fft_k_odd_index n md2 processed) =
  fft_decode_at data (fft_k_odd_index n md2 processed).
proof.
move=> hproc hwf.
rewrite /fft_k_prefix_decode_at /fft_k_even_index /fft_k_odd_index.
have hmd2 : processed < W64.to_uint md2 by
  move: hwf; rewrite /fft_k_schedule_wf; smt().
by rewrite ifF 1:/# ifF 1:/#.
qed.

lemma fft_k_prefix_decode_at_frameS
    (data roots : BArray2048.t) (n md2 stride : W64.t)
    (processed j : int) :
  0 <= processed =>
  fft_k_schedule_wf n md2 stride (processed + 1) =>
  0 <= j < 256 =>
  j <> fft_k_even_index n processed =>
  j <> fft_k_odd_index n md2 processed =>
  fft_k_prefix_decode_at
    data roots n md2 stride (processed + 1) j =
  fft_k_prefix_decode_at
    data roots n md2 stride processed j.
proof.
move=> hproc hwf hj hje hjo.
rewrite /fft_k_prefix_decode_at /fft_k_even_index /fft_k_odd_index.
have heven :
  (W64.to_uint n <= j < W64.to_uint n + (processed + 1)) =
  (W64.to_uint n <= j < W64.to_uint n + processed).
+ smt().
have hodd :
  (W64.to_uint n + W64.to_uint md2 <= j /\
   j < W64.to_uint n + W64.to_uint md2 + (processed + 1)) =
  (W64.to_uint n + W64.to_uint md2 <= j /\
   j < W64.to_uint n + W64.to_uint md2 + processed).
+ smt().
by rewrite heven hodd.
qed.

lemma fft_k_prefix_decode
    (data roots : BArray2048.t) (n md2 stride : W64.t)
    (processed j : int) :
  fft_k_schedule_wf n md2 stride processed =>
  0 <= j < 256 =>
  fft_k_prefix_safe data roots n md2 stride processed =>
  fft_decode_at
    (KeygenM23SingularFFTSpec.fft_k_prefix
      data roots n md2 stride processed)
    j =
  fft_k_prefix_decode_at data roots n md2 stride processed j.
proof.
move=> hwf hj.
have hgeneral :
  forall p,
    0 <= p =>
    fft_k_schedule_wf n md2 stride p =>
    fft_k_prefix_safe data roots n md2 stride p =>
    forall i, 0 <= i < 256 =>
      fft_decode_at
        (KeygenM23SingularFFTSpec.fft_k_prefix
          data roots n md2 stride p)
        i =
      fft_k_prefix_decode_at data roots n md2 stride p i.
+ apply intind.
  + move=> hwf0 _ i hi.
    by rewrite KeygenM23SingularFFTSpec.fft_k_prefix0
               /fft_k_prefix_decode_at ifF 1:/# ifF 1:/#.
  + move=> p hp0 ih hwfS hsafeS i hi.
    have hwfP := fft_k_schedule_wf_prev n md2 stride p hp0 hwfS.
    have hsafeP :=
      fft_k_prefix_safe_prev
        data roots n md2 stride p hp0 hsafeS.
    have hstep :
      fft_butterfly_safe_at
        (KeygenM23SingularFFTSpec.fft_k_prefix
          data roots n md2 stride p)
        roots
        (fft_k_even_index n p)
        (fft_k_odd_index n md2 p)
        (fft_k_twid_index stride p).
    + have hp_range : 0 <= p < p + 1 by smt().
      exact (hsafeS p hp_range).
    rewrite KeygenM23SingularFFTSpec.fft_k_prefixS 1:hp0.
    case (i = fft_k_even_index n p) => hie.
    + have hwrite :=
        fft_k_step_decode_written
          (KeygenM23SingularFFTSpec.fft_k_prefix
            data roots n md2 stride p)
          roots n md2 stride p hp0 hwfS hstep.
      move: hwrite => [hwrite _].
      rewrite hie.
      rewrite hwrite
              (fft_k_prefix_decode_at_evenS
                data roots n md2 stride p hp0 hwfS).
      done.
    case (i = fft_k_odd_index n md2 p) => hio.
    + have hwrite :=
        fft_k_step_decode_written
          (KeygenM23SingularFFTSpec.fft_k_prefix
            data roots n md2 stride p)
          roots n md2 stride p hp0 hwfS hstep.
      move: hwrite => [_ hwrite].
      rewrite hio.
      rewrite hwrite
              (fft_k_prefix_decode_at_oddS
                data roots n md2 stride p hp0 hwfS).
      done.
    have hframe :=
      fft_k_step_decode_frame
        (KeygenM23SingularFFTSpec.fft_k_prefix
          data roots n md2 stride p)
        roots n md2 stride p i
        hp0 hwfS hi hie hio.
    rewrite hframe.
    rewrite
      (fft_k_prefix_decode_at_frameS
        data roots n md2 stride p i hp0 hwfS hi hie hio).
    exact (ih hwfP hsafeP i hi).
have hprocessed : 0 <= processed by
  move: hwf; rewrite /fft_k_schedule_wf; smt().
move=> hsafe.
exact (hgeneral processed hprocessed hwf hsafe j hj).
qed.

end KeygenM23SingularFFTKPrefixBridge.
