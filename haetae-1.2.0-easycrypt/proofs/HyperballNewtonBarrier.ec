require import AllCore IntDiv StdRing StdOrder.
import Ring.IntID IntOrder.

op hnb_Q : int = 2^76.
op hnb_cubic (h y : int) : int = ((3*hnb_Q^3) %/ 2)*y - h*y*y*y.

lemma hnb_Q_value : hnb_Q = 75557863725914323419136.
proof. rewrite /hnb_Q; ring. qed.

lemma hnb_Q_cube : hnb_Q^3 = 431359146674410236714672241392314090778194310760649159697657763987456.
proof. rewrite /hnb_Q; ring. qed.

lemma hnb_pow70 : 2^70 = 1180591620717411303424.
proof. ring. qed.

lemma hnb_pow71 : 2^71 = 2361183241434822606848.
proof. ring. qed.

lemma hnb_pow88 : 2^88 = 309485009821345068724781056.
proof. ring. qed.

lemma hnb_cubic_fraction h y :
  hnb_cubic h y = (3*hnb_Q^3*y) %/ 2 - h*y*y*y.
proof.
  pose C := (3*hnb_Q^3) %/ 2.
  have hC : 3*hnb_Q^3 = C*2 by rewrite /C hnb_Q_cube.
  rewrite /hnb_cubic -/C.
  have he : 3*hnb_Q^3*y = (C*y)*2 by rewrite hC; ring.
  by rewrite he mulzK.
qed.

lemma hnb_scaled_error a e : 0 <= a => `|e| <= hnb_Q =>
  -(a*hnb_Q) <= a*e <= a*hnb_Q.
proof.
  move=> ha; rewrite ler_norml => he.
  have hl := ler_wpmul2l a ha (-hnb_Q) e _; first smt().
  have hu := ler_wpmul2l a ha e hnb_Q _; first smt().
  smt().
qed.

lemma hnb_u_bound h H y s u :
  2^70 <= H <= 2^71 => 0 <= y <= H => 0 <= h <= 2^88 =>
  8*h*H*H <= 9*hnb_Q^3 =>
  `|hnb_Q*s-y*y| <= hnb_Q => `|hnb_Q*u-h*s| <= hnb_Q =>
  u <= (5*hnb_Q) %/ 4.
proof.
  move=> hH hy hh hupper hs hu.
  have hQ : 0 < hnb_Q by rewrite hnb_Q_value.
  have hQ0 : 0 <= hnb_Q by smt().
  have hh0 : 0 <= h by smt().
  have hy2 : y*y <= H*H by smt().
  have hprod := ler_wpmul2l h hh0 (y*y) (H*H) hy2.
  have hs1 : hnb_Q*s <= y*y+hnb_Q by move: hs; rewrite ler_norml; smt().
  have hhs := ler_wpmul2l h hh0 (hnb_Q*s) (y*y+hnb_Q) hs1.
  have hu1 : hnb_Q*u <= h*s+hnb_Q by move: hu; rewrite ler_norml; smt().
  have hqu := ler_wpmul2l hnb_Q hQ0 (hnb_Q*u) (h*s+hnb_Q) hu1.
  have hscaled : 8*hnb_Q*hnb_Q*u <= 9*hnb_Q^3+8*h*hnb_Q+8*hnb_Q*hnb_Q.
  + move: hupper hprod hhs hqu; rewrite hnb_Q_cube hnb_Q_value /=; smt().
  have hbudget : 8*h*hnb_Q+8*hnb_Q*hnb_Q <= hnb_Q^3.
  + move: hh; rewrite hnb_Q_cube hnb_Q_value hnb_pow88 /=; smt().
  move: hscaled hbudget; rewrite hnb_Q_cube hnb_Q_value /=; smt().
qed.

lemma hnb_t_bounds u t : 0 <= u => u <= (5*hnb_Q) %/ 4 =>
  t = (3*hnb_Q) %/ 2-u => hnb_Q %/ 4 <= t <= (3*hnb_Q) %/ 2.
proof. rewrite hnb_Q_value /=; smt(). qed.

lemma hnb_hy_bound h H y :
  2^70 <= H <= 2^71 => 0 <= y <= H => 0 <= h <= 2^88 =>
  0 <= h*y <= 128*hnb_Q*hnb_Q /\ y <= hnb_Q.
proof.
  move=> hH hy hh.
  have hy0 : 0 <= y by smt().
  have hh0 : 0 <= h by smt().
  have hp0 := mulr_ge0 h y hh0 hy0.
  have hp := ler_wpmul2r y hy0 h (2^88) _; first smt().
  move: hp hH hy; rewrite hnb_Q_value hnb_pow70 hnb_pow71 hnb_pow88 /=; smt().
qed.

lemma hnb_error_identity h y s u t z : t = (3*hnb_Q) %/ 2-u =>
  hnb_Q^3*z-hnb_cubic h y =
    hnb_Q*hnb_Q*(hnb_Q*z-t*y) - hnb_Q*y*(hnb_Q*u-h*s) - h*y*(hnb_Q*s-y*y).
proof. move=> ->; rewrite /hnb_cubic hnb_Q_cube hnb_Q_value /=; ring. qed.

lemma hnb_error_bound h H y s u t z :
  2^70 <= H <= 2^71 => 0 <= y <= H => 0 <= h <= 2^88 =>
  `|hnb_Q*s-y*y| <= hnb_Q => `|hnb_Q*u-h*s| <= hnb_Q =>
  t = (3*hnb_Q) %/ 2-u => `|hnb_Q*z-t*y| <= hnb_Q =>
  `|hnb_Q^3*z-hnb_cubic h y| <= 256*hnb_Q^3.
proof.
  move=> hH hy hh hs hu ht hz.
  have [hhy hyQ] := hnb_hy_bound h H y hH hy hh.
  have hQ : 0 <= hnb_Q by rewrite hnb_Q_value.
  have hy0 : 0 <= y by smt().
  have hQy := mulr_ge0 hnb_Q y hQ hy0.
  have hQQ := mulr_ge0 hnb_Q hnb_Q hQ hQ.
  have ez := hnb_scaled_error (hnb_Q*hnb_Q) (hnb_Q*z-t*y) hQQ hz.
  have eu := hnb_scaled_error (hnb_Q*y) (hnb_Q*u-h*s) hQy hu.
  have es := hnb_scaled_error (h*y) (hnb_Q*s-y*y) _ hs; first smt().
  have hbudget : hnb_Q*hnb_Q*hnb_Q + hnb_Q*y*hnb_Q + h*y*hnb_Q <= 256*hnb_Q^3.
  + move: hhy hyQ; rewrite hnb_Q_cube hnb_Q_value /=; smt().
  rewrite (hnb_error_identity h y s u t z ht) ler_norml.
  smt().
qed.

(* This identity is an integer certificate for the upper-half margin. *)
lemma hnb_barrier_identity h H y :
  H*H*(255*H*hnb_Q^3-256*hnb_cubic h y) =
    128*hnb_Q^3*(H-y)*(H-y)*(y+2*H) +
    8*(32*h*H*H-17*hnb_Q^3)*y*y*y +
    hnb_Q^3*(2*y-H)*(4*y*y+2*H*y+H*H).
proof. rewrite /hnb_cubic hnb_Q_cube /=; ring. qed.

lemma hnb_cubic_upper_half h H y :
  2^70 <= H <= 2^71 => 0 <= y <= H =>
  17*hnb_Q^3 <= 32*h*H*H => H <= 2*y =>
  256*hnb_cubic h y <= 255*H*hnb_Q^3.
proof.
  move=> hH hy hslack hhalf.
  have hH0 : 0 <= H by smt().
  have hHp : 0 < H by move: hH; rewrite hnb_pow70 hnb_pow71; smt().
  have hy0 : 0 <= y by smt().
  have hgap : 0 <= H-y by smt().
  have hQ3 : 0 <= hnb_Q^3 by rewrite hnb_Q_cube.
  have hgap2 := mulr_ge0 (H-y) (H-y) hgap hgap.
  have hy2 := mulr_ge0 y y hy0 hy0.
  have hy3 := mulr_ge0 (y*y) y hy2 hy0.
  have hHy := mulr_ge0 H y hH0 hy0.
  have hH2 := mulr_ge0 H H hH0 hH0.
  have hpoly : 0 <= 4*y*y+2*H*y+H*H by smt().
  have hfirst : 0 <= 128*hnb_Q^3*(H-y)*(H-y)*(y+2*H).
  + have h1 := mulr_ge0 (128*hnb_Q^3) ((H-y)*(H-y)) _ hgap2; first smt().
    have h2 := mulr_ge0 (128*hnb_Q^3*((H-y)*(H-y))) (y+2*H) h1 _; first smt().
    smt().
  have hsecond : 0 <= 8*(32*h*H*H-17*hnb_Q^3)*y*y*y.
  + have h1 := mulr_ge0 (8*(32*h*H*H-17*hnb_Q^3)) (y*y*y) _ hy3; first smt().
    smt().
  have hthird : 0 <= hnb_Q^3*(2*y-H)*(4*y*y+2*H*y+H*H).
  + have h1 := mulr_ge0 (hnb_Q^3) (2*y-H) hQ3 _; first smt().
    exact (mulr_ge0 (hnb_Q^3*(2*y-H)) _ h1 hpoly).
  have hH2p := mulr_gt0 H H hHp hHp.
  have hc : 0 <= H*H*(255*H*hnb_Q^3-256*hnb_cubic h y) by
    rewrite hnb_barrier_identity; smt().
  rewrite pmulr_rge0 1:hH2p in hc.
  smt().
qed.

lemma hnb_low_half H y t z :
  2^70 <= H <= 2^71 => 0 <= y => 2*y <= H =>
  t <= (3*hnb_Q) %/ 2 => `|hnb_Q*z-t*y| <= hnb_Q => z <= H.
proof.
  move=> hH hy hhalf ht hz.
  have hmul := ler_wpmul2r y hy t ((3*hnb_Q) %/ 2) ht.
  move: hmul hz hhalf hH; rewrite ler_norml hnb_Q_value hnb_pow70 hnb_pow71 /=; smt().
qed.

lemma hnb_high_half H h y z :
  2^70 <= H => 256*hnb_cubic h y <= 255*H*hnb_Q^3 =>
  `|hnb_Q^3*z-hnb_cubic h y| <= 256*hnb_Q^3 => z <= H.
proof. rewrite ler_norml hnb_Q_cube hnb_pow70 /=; smt(). qed.

lemma hnb_z_bound h H y s u t z :
  2^70 <= H <= 2^71 => 0 <= y <= H => 0 <= h <= 2^88 =>
  17*hnb_Q^3 <= 32*h*H*H => 8*h*H*H <= 9*hnb_Q^3 =>
  `|hnb_Q*s-y*y| <= hnb_Q => 0 <= s =>
  `|hnb_Q*u-h*s| <= hnb_Q => 0 <= u =>
  t = (3*hnb_Q) %/ 2-u => `|hnb_Q*z-t*y| <= hnb_Q => 0 <= z =>
  z <= H.
proof.
  move=> hH hy hh hlo hhi hs hs0 hu hu0 ht hz hz0.
  have hub := hnb_u_bound h H y s u hH hy hh hhi hs hu.
  have htb := hnb_t_bounds u t hu0 hub ht.
  case (2*y <= H) => hhalf.
  + apply (hnb_low_half H y t z hH _ hhalf _ hz); smt().
  have hupper := hnb_cubic_upper_half h H y hH hy hlo _; first smt().
  have he := hnb_error_bound h H y s u t z hH hy hh hs hu ht hz.
  apply (hnb_high_half H h y z _ hupper he); smt().
qed.
