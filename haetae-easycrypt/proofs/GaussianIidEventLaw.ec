require import AllCore IntDiv List Distr DList Xreal StdOrder.
from Jasmin require import JModel_x86.
require import GaussianIidBufferSpec GaussianIidBufferPath GaussianIidNormalization
  GaussianIidKernel GaussianIidVisible GaussianIidStep GaussianUniformBytes
  GaussianByteCarryDistribution.
import RealOrder.

(* The carried byte tail is retained in the potential as a fixed prefix.
   Only the fresh initial block or refill block is averaged. *)
lemma gie_uniform_event_hoare (offset0 : int) (event : int list -> bool) :
  ehoare [GaussianIidBufferUniform.sample :
    (sample_offset=offset0 /\ gib_bounds n sample_offset sign_offset)
      `|` (mu gid_target event)%xr
    ==> (event (gib_magnitudes res offset0))%xr].
proof.
  proc.
  while ((sample_offset=offset0 /\ gib_bounds n sample_offset sign_offset /\
      0 <= accepted <= n /\ size pending <= 6632)
    `|` (mu (gik_kernel (gib_visible rp offset0 accepted) (gib_remainder pending)) event)%xr).
  + move=> &hr; apply xle_cxr_r => hstop; apply xle_cxr_r => hinv.
    have [hoff [hb [ha hp]]] := hinv.
    have haccept : 256 <= accepted{hr} by move: hb; rewrite /gib_bounds; smt().
    have hsize : size (gib_visible rp{hr} offset0 accepted{hr}) = 256.
    + rewrite giv_size 1:/#; smt().
    rewrite (gik_kernel_full _ _ hsize) dunitE.
    have he := giv_terminal (rp{hr},signsp{hr},sqsump{hr}) offset0 accepted{hr} haccept.
    by move: he; rewrite /= => ->.
  + wp; skip => &hr.
    apply xle_cxr_r => hloop; apply xle_cxr_r => hinv.
    have [hoff [hb [ha hp]]] := hinv.
    have hb0 : gib_bounds n{hr} offset0 sign_offset{hr} by move: hb; rewrite hoff.
    have haccept : 0 <= accepted{hr} < n{hr} by smt().
    have [_ hrem] := gib_remainder_size pending{hr}.
    have ht : size (gib_remainder pending{hr}) < 26 by smt().
    have hv : size (gib_visible rp{hr} offset0 accepted{hr}) <= 256.
    + rewrite giv_size 1:/#; smt().
    rewrite hoff hb0 /gib_block -/(gbc_bytes 136) /= Ep_cxr.
    apply xle_cxr_l.
    + move=> bytes hbytes /=.
      have hsize := supp_dlist_size W8.dword 136 bytes _ hbytes; first trivial.
      have [hc [hlen hrest]] := gis_refill rp{hr} sqsump{hr} count{hr}
        (gib_remainder pending{hr}) bytes n{hr} accepted{hr} offset0 sign_offset{hr}
        hb0 haccept ht hsize.
      smt().
    rewrite -(gik_refill_event (gib_visible rp{hr} offset0 accepted{hr})
      (gib_remainder pending{hr}) event hv ht).
    apply le_Ep => bytes hbytes /=.
    have hsize := supp_dlist_size W8.dword 136 bytes _ hbytes; first trivial.
    have [_ [_ [_ [hvisible htail]]]] := gis_refill rp{hr} sqsump{hr} count{hr}
      (gib_remainder pending{hr}) bytes n{hr} accepted{hr} offset0 sign_offset{hr}
      hb0 haccept ht hsize.
    by rewrite hvisible htail.
  wp; skip => &hr; apply xle_cxr_r => -[hoff hb].
  have hb0 : gib_bounds n{hr} offset0 sign_offset{hr} by move: hb; rewrite hoff.
  rewrite hoff hb0 /= Ep_cxr.
  apply xle_cxr_l.
  + move=> bytes hbytes /=.
    have hsize := supp_dlist_size W8.dword 6664 bytes _ hbytes; first trivial.
    have [hc [hlen hrest]] := gis_initial rp{hr} sqsump{hr} (witness<:BArray8.t>)
      bytes n{hr} offset0 sign_offset{hr} hb0 hsize.
    smt().
  rewrite /gid_target -(gik_initial_event event).
  apply le_Ep => bytes hbytes /=.
  have hsize := supp_dlist_size W8.dword 6664 bytes _ hbytes; first trivial.
  have [_ [_ [_ [hvisible htail]]]] := gis_initial rp{hr} sqsump{hr} (witness<:BArray8.t>)
    bytes n{hr} offset0 sign_offset{hr} hb0 hsize.
  by rewrite hvisible htail.
qed.

lemma gie_uniform_event_upper (initial : BArray32768.t) (initial_signs : BArray512.t)
    (initial_squares : BArray16.t) (n offset0 signoff : int)
    (event : int list -> bool) &m :
  gib_bounds n offset0 signoff =>
  Pr[GaussianIidBufferUniform.sample(initial,initial_signs,initial_squares,n,offset0,signoff)
    @ &m : event (gib_magnitudes res offset0)] <= mu gid_target event.
proof.
  move=> hb.
  byehoare (gie_uniform_event_hoare offset0 event) => //.
  by rewrite /= hb.
qed.
