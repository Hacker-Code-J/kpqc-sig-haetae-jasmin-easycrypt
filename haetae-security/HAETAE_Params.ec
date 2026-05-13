require import AllCore.

theory HAETAE_Params.

op seedbytes : int = 32.
op crhbytes : int = 64.
op n : int = 256.
op q : int = 64513.
op dq : int = 2 * q.

type mode = [ Mode2 | Mode3 | Mode5 ].

op mode_k (md : mode) : int =
  with md = Mode2 => 2
  with md = Mode3 => 3
  with md = Mode5 => 4.

op mode_l (md : mode) : int =
  with md = Mode2 => 4
  with md = Mode3 => 6
  with md = Mode5 => 7.

op mode_tau (md : mode) : int =
  with md = Mode2 => 58
  with md = Mode3 => 80
  with md = Mode5 => 128.

op mode_b0sq (md : mode) : int =
  with md = Mode2 => 96944109
  with md = Mode3 => 335438492
  with md = Mode5 => 499239142.

op mode_b1sq (md : mode) : int =
  with md = Mode2 => 96805527
  with md = Mode3 => 335171879
  with md = Mode5 => 498849991.

op mode_b2sq (md : mode) : int =
  with md = Mode2 => 163265017
  with md = Mode3 => 479901314
  with md = Mode5 => 597386433.

op mode_ln (_ : mode) : int = 8192.

op mode_alpha_hint (md : mode) : int =
  with md = Mode2 => 512
  with md = Mode3 => 512
  with md = Mode5 => 256.

op mode_m (md : mode) : int = mode_l md - 1.

op mode_crypto_bytes (md : mode) : int =
  with md = Mode2 => 1474
  with md = Mode3 => 2349
  with md = Mode5 => 2948.

op mode_polyq_packedbytes (md : mode) : int =
  with md = Mode2 => 480
  with md = Mode3 => 480
  with md = Mode5 => 512.

op mode_publickeybytes (md : mode) : int =
  seedbytes + mode_k md * mode_polyq_packedbytes md.

lemma seedbytes_gt0 : 0 < seedbytes by rewrite /seedbytes.
lemma crhbytes_gt0 : 0 < crhbytes by rewrite /crhbytes.
lemma n_gt0 : 0 < n by rewrite /n.
lemma q_gt0 : 0 < q by rewrite /q.
lemma dqE : dq = 129026 by rewrite /dq /q.

lemma mode_k_gt0 md : 0 < mode_k md.
proof. by case md. qed.

lemma mode_l_gt0 md : 0 < mode_l md.
proof. by case md. qed.

lemma mode_tau_gt0 md : 0 < mode_tau md.
proof. by case md. qed.

lemma mode_tau_le_n md : mode_tau md <= n.
proof. by case md. qed.

lemma mode_b0sq_gt0 md : 0 < mode_b0sq md.
proof. by case md. qed.

lemma mode_b1sq_gt0 md : 0 < mode_b1sq md.
proof. by case md. qed.

lemma mode_b2sq_gt0 md : 0 < mode_b2sq md.
proof. by case md. qed.

lemma mode_ln_gt0 md : 0 < mode_ln md.
proof. by case md. qed.

lemma mode_alpha_hint_gt0 md : 0 < mode_alpha_hint md.
proof. by case md. qed.

lemma mode_m_gt0 md : 0 < mode_m md.
proof. by case md. qed.

lemma mode_crypto_bytes_gt0 md : 0 < mode_crypto_bytes md.
proof. by case md. qed.

lemma mode_polyq_packedbytes_gt0 md : 0 < mode_polyq_packedbytes md.
proof. by case md. qed.

lemma n_le_mode_polyq_packedbytes md : n <= mode_polyq_packedbytes md.
proof. by case md. qed.

lemma mode_publickeybytes_gt0 md : 0 < mode_publickeybytes md.
proof. by case md. qed.

end HAETAE_Params.
