require import AllCore List Distr DList.
from Jasmin require import JModel_x86.
require import GaussianPayloadSpec GaussianPayloadEncoding GaussianPayloadBufferSpec
  GaussianPayloadBufferPath GaussianPayloadEventLaw.

(* A proof-only draw of the complete accepted payload list. The equivalence
   below observes the history of the actual buffered controller and places
   no restriction on its input arrays. *)
module GaussianPayloadDraw = {
  proc sample(n : int) : int list = {
    var history : int list;
    history <$ dlist gpd_accepted n;
    return history;
  }
}.

lemma gpd_draw_law n0 (event : int list -> bool) &m :
  Pr[GaussianPayloadDraw.sample(n0) @ &m : event res] =
    mu (dlist gpd_accepted n0) event.
proof. by byphoare (_ : n=n0 ==> event res) => //; proc; rnd; skip; auto. qed.

lemma gpd_draw_lossless : islossless GaussianPayloadDraw.sample.
proof.
  bypr => &m _; rewrite (gpd_draw_law n{m} (fun _ => true) &m).
  exact (dlist_ll gpd_accepted n{m} gpd_accepted_ll).
qed.

lemma gpd_history_draw :
  equiv [GaussianPayloadHistory.sample ~ GaussianPayloadDraw.sample :
    ={n} /\ 0 <= n{1} <= 512 ==> ={res}].
proof.
  bypr (res{1}) (res{2}) => //= &1 &2 history [hn hb].
  by rewrite (gpe_history_law n{1} (pred1 history) &1 hb)
    (gpd_draw_law n{2} (pred1 history) &2) hn.
qed.

lemma gpd_buffer_draw :
  equiv [GaussianPayloadBuffer.sample ~ GaussianPayloadDraw.sample :
    n{1}=n{2} /\ 0 <= n{1} <= 512 ==> res{1}.`2=res{2}].
proof.
  transitivity GaussianPayloadHistory.sample
    (n{1}=n{2} /\ 0 <= n{1} <= 512 ==> res{1}.`2=res{2})
    (={n} /\ 0 <= n{1} <= 512 ==> ={res}).
  + move=> &1 &2 [hn hb]; exists n{2}; smt().
  + smt().
  + exact gpb_history_projection.
  exact gpd_history_draw.
qed.
