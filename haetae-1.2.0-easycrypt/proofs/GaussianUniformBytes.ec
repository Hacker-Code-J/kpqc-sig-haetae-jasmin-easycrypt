require import AllCore IntDiv List Distr DInterval DList StdRing StdOrder.
from Jasmin require import JModel_x86.
require import BArray26 GaussianRetryInputs MixedRadixUniform SigmaRawSpec
  SigmaNoise72Bridge SigmaRejection48Bridge SigmaCDT83Patch.
require import GaussianUnusedBits.
require import SigmaSpec SigmaCorrectness SigmaConditionalSpec SigmaAcceptanceLowerBound
  SigmaConditionalActual SigmaRawNoiseSpec Rejection48Spec CDTDistributionBridge.
import RField RealOrder.

(* Genuine independent uniform octets. BArray26.darray is the installed
   dmap of 26 W8.dword samples through BArray26.of_list. *)
op gbc_bytes (n : int) : W8.t list distr = dlist W8.dword n.
op gbc_candidate : BArray26.t distr = BArray26.darray.
op gbc_chunks (n : int) (bytes : W8.t list) : BArray26.t list =
  map (fun i => BArray26.of_list (take 26 (drop (26*i) bytes))) (iota_ 0 n).

lemma gbc_bytes_ll n : is_lossless (gbc_bytes n).
proof. rewrite /gbc_bytes; apply dlist_ll; exact W8.dword_ll. qed.

lemma gbc_candidate_ll : is_lossless gbc_candidate.
proof.
  rewrite /gbc_candidate /BArray26.darray; apply dmap_ll.
  apply dlist_ll; exact W8.dword_ll.
qed.

lemma gbc_bytes_split (m n : int) : 0 <= m => 0 <= n =>
  dmap (gbc_bytes (m+n)) (fun bytes => (take m bytes, drop m bytes)) =
    gbc_bytes m `*` gbc_bytes n.
proof.
  move=> hm hn; rewrite /gbc_bytes (dlist_add W8.dword m n hm hn) dmap_comp.
  apply dmap_id_eq_in => -[ls rs] /=.
  rewrite supp_dprod => -[hl hr].
  have hs := supp_dlist_size W8.dword m ls hm hl.
  by rewrite /(\o) /= (take_size_cat m ls rs hs) (drop_size_cat m ls rs hs).
qed.

lemma gbc_chunks0 bytes : gbc_chunks 0 bytes = [].
proof. by rewrite /gbc_chunks iota0. qed.

lemma gbc_chunks_cons (n : int) (head tail : W8.t list) :
  0 <= n => size head = 26 =>
  gbc_chunks (n+1) (head++tail) = BArray26.of_list head :: gbc_chunks n tail.
proof.
  move=> hn hs; rewrite /gbc_chunks (iotaS 0 n hn) /= drop0
    (take_size_cat 26 head tail hs).
  have hi := iota_addl 1 0 n.
  rewrite /= in hi; rewrite hi -map_comp.
  rewrite /=; apply eq_in_map => i; rewrite mem_iota /= => hir.
  rewrite /(\o) /=.
  rewrite drop_catr 1:/# hs.
  have he : 26*(1+i)-26 = 26*i by ring.
  by rewrite he.
qed.

lemma gbc_chunks_iid (n : int) : 0 <= n =>
  dmap (gbc_bytes (26*n)) (gbc_chunks n) = dlist gbc_candidate n.
proof.
  elim: n => [|n hn ih].
  + by rewrite /gbc_bytes dlist0 1:// dmap_dunit gbc_chunks0 dlist0.
  have hlen : 26*(n+1) = 26+26*n by ring.
  rewrite hlen /gbc_bytes (dlist_add W8.dword 26 (26*n)) 1:// 1:/# dmap_comp.
  rewrite dlistS 1:hn /= -ih /gbc_candidate /BArray26.darray /gbc_bytes.
  rewrite dmap_dprod dmap_comp; apply eq_dmap_in => -[head tail] /=.
  rewrite supp_dprod => -[hh ht].
  have hs := supp_dlist_size W8.dword 26 head _ hh; first trivial.
  exact (gbc_chunks_cons n head tail hn hs).
qed.

(* Little-endian octet encoding used only to prove distribution transport
   between independent bytes and bounded integer inputs. *)
op gbc_encode_bytes (n z : int) : W8.t list =
  map (fun i => W8.of_int (z %/ (256^i))) (iota_ 0 n).

lemma gbc_power_positive n : 0 <= n => 0 < 256^n.
proof.
  elim: n => [|n hn ih]; first by rewrite Ring.IntID.expr0.
  rewrite Ring.IntID.exprS 1:hn; smt().
qed.

lemma gbc_word_interval : dmap (dinter 0 255) W8.of_int = W8.dword.
proof.
  have hinj : forall x y, x \in range 0 256 => y \in range 0 256 =>
      W8.of_int x = W8.of_int y => x=y.
  + move=> x y; rewrite !mem_range W8.to_uint_eq !W8.of_uintK /=.
    smt(modz_small).
  by rewrite /dinter /W8.dword W8.all_wordsE /=
    (dmap_duniform W8.of_int (range 0 256) hinj).
qed.

lemma gbc_encode_bytes0 z : gbc_encode_bytes 0 z = [].
proof. by rewrite /gbc_encode_bytes iota0. qed.

lemma gbc_encode_bytes_size n z : 0 <= n => size (gbc_encode_bytes n z) = n.
proof. move=> hn; rewrite /gbc_encode_bytes size_map size_iota; smt(). qed.

lemma gbc_encode_bytesS n z : 0 <= n =>
  gbc_encode_bytes (n+1) z = W8.of_int z :: gbc_encode_bytes n (z %/ 256).
proof.
  move=> hn; rewrite /gbc_encode_bytes (iotaS 0 n hn) /=.
  have hi := iota_addl 1 0 n; rewrite /= in hi.
  rewrite hi -map_comp /=; apply eq_in_map => i.
  rewrite mem_iota /= => hir; rewrite /(\o) /=.
  have he : 256^(1+i) = 256 * (256^i) by
    rewrite (addzC 1 i) Ring.IntID.exprS 1:/#; ring.
  by rewrite he divz_mul.
qed.

lemma gbc_encode_uniform n : 0 <= n =>
  dmap (dinter 0 (256^n-1)) (gbc_encode_bytes n) = gbc_bytes n.
proof.
  elim: n => [|n hn ih].
  + rewrite /gbc_encode_bytes iota0 1:// /= /gbc_bytes dlist0 1://.
    apply dmap_cst; apply dinter_ll; trivial.
  have hp := gbc_power_positive n hn.
  have he : 256^(n+1) = 256*(256^n) by
    rewrite Ring.IntID.exprS 1:hn; ring.
  have hjoin := mru_join_uniform 256 (256^n) _ hp; first trivial.
  rewrite he -hjoin dmap_comp.
  have ih' := ih; rewrite /gbc_bytes in ih'.
  rewrite /gbc_bytes (dlistS W8.dword n hn) /= -ih' -gbc_word_interval.
  rewrite dmap_dprod dmap_comp.
  apply eq_dmap_in => -[a b] /=.
  rewrite supp_dprod !supp_dinter /= => -[ha hb].
  rewrite /(\o) /mru_join /= (gbc_encode_bytesS n (a+256*b) hn).
  have hd : (a+256*b) %/ 256 = b by
    rewrite (mulzC 256 b) divzMDr 1:// pdiv_small; smt().
  have hw : W8.of_int (a+256*b) = W8.of_int a by
    apply W8.to_uint_eq; rewrite !W8.of_uintK (mulzC 256 b) modzMDr.
  by rewrite hd hw.
qed.

lemma gbc_power256 n : 0 <= n => 256^n = 2^(8*n).
proof. by move=> hn; rewrite Ring.IntID.exprM /=. qed.

lemma gbc_encode_bytes_nth n z i : 0 <= i < n =>
  nth W8.zero (gbc_encode_bytes n z) i = W8.of_int (z %/ (256^i)).
proof.
  move=> hi; rewrite /gbc_encode_bytes (nth_map 0) 1:size_iota 1:/#.
  by rewrite nth_iota 1:hi /=.
qed.

lemma gbc_word64_byte z i : 0 <= i < 8 =>
  W64.of_int z \bits8 i = W8.of_int (z %/ (256^i)).
proof.
  move=> hi; rewrite (W8u8.of_int_bits8_div z i hi) /=.
  by rewrite (gbc_power256 i _) 1:/#.
qed.

lemma gbc_divide_digits z a b : 0 <= a => 0 <= b =>
  (z %/ (256^a)) %/ (256^b) = z %/ (256^(a+b)).
proof.
  move=> ha hb; have hp := gbc_power_positive a ha.
  by rewrite (Ring.IntID.exprD_nneg 256 a b ha hb) divz_mul 1:/#.
qed.

lemma gbc_candidate_patch_byte p u y v i : 0 <= i < 26 =>
  BArray26.get8 (gr_candidate_patch p u y v) i =
    if i < 11 then W8.of_int (u %/ (256^i))
    else if i < 17 then W8.of_int (v %/ (256^(i-11)))
    else W8.of_int (y %/ (256^(i-17))).
proof.
  move=> hi.
  rewrite /gr_candidate_patch (sigma_rejection48_patch_byte _ v i hi)
    (sigma_noise72_patch_byte _ y i hi) (sj_cdt83_patch_byte p u i hi).
  case (i<8) => h8.
  + have h := gbc_word64_byte u i _; first smt().
    smt().
  case (i<11) => h11.
  + have h := gbc_word64_byte (u %/ 18446744073709551616) (i-8) _; first smt().
    have hd := gbc_divide_digits u 8 (i-8) _ _; first 2 smt().
    rewrite /= in hd; smt().
  case (i<17) => h17.
  + have h := gbc_word64_byte v (i-11) _; first smt().
    smt().
  case (i<23) => h23.
  + have h := gbc_word64_byte y (i-17) _; first smt().
    smt().
  have h := gbc_word64_byte (y %/ sr_scale) (i-23) _; first smt().
  have hd := gbc_divide_digits y 6 (i-23) _ _; first 2 smt().
  rewrite /= in hd; rewrite /sr_scale in h; smt().
qed.

lemma gbc_candidate_patch_bytes p u y v :
  gr_candidate_patch p u y v = BArray26.of_list
    (gbc_encode_bytes 11 u ++ (gbc_encode_bytes 6 v ++ gbc_encode_bytes 9 y)).
proof.
  apply BArray26.ext_eq => i hi.
  rewrite (gbc_candidate_patch_byte p u y v i hi) (BArray26.get_of_list _ i hi).
  rewrite nth_cat (gbc_encode_bytes_size 11 u _) 1://.
  case (i<11) => h11 /=.
  + by rewrite gbc_encode_bytes_nth 1:/#.
  rewrite nth_cat (gbc_encode_bytes_size 6 v _) 1://.
  case (i<17) => h17 /=.
  + have -> : i-11<6 by smt().
    by rewrite /= gbc_encode_bytes_nth 1:/#.
  have -> : !(i-11<6) by smt().
  have he : i-11-6=i-17 by ring.
  by rewrite /= he gbc_encode_bytes_nth 1:/#.
qed.

lemma gbc_word_mod_power z n : 8 <= n =>
  W8.of_int (z %% (2^n)) = W8.of_int z.
proof.
  move=> hn.
  have ha : `|n| = n by apply IntOrder.ger0_norm; smt().
  have hm : min `|n| `|8| = 8 by rewrite ha /= /min; smt().
  have h := JUtils.modz_mod_pow2 z n 8.
  rewrite hm /= in h.
  by rewrite W8.to_uint_eq !W8.of_uintK h.
qed.

lemma gbc_low83_digit z i : 0 <= i < 11 =>
  W8.of_int ((z %% (2^83)) %/ (256^i)) =
    if i=10 then W8.of_int (z %/ (256^i)) `&` W8.of_int 7
    else W8.of_int (z %/ (256^i)).
proof.
  move=> hi; case (i=10) => he.
  + subst i.
    have hd := IntDiv.modz_pow2_div 83 80 z _; first trivial.
    rewrite /= in hd.
    rewrite /= hd.
    have hm : W8.of_int 7 = W8.of_int (2^3-1) by trivial.
    rewrite hm W8.and_mod 1:// W8.of_uintK /=.
    by rewrite (modz_dvd (z %/ 1208925819614629174706176) 256 8) 1://.
  rewrite /= (gbc_power256 i _) 1:/#.
  rewrite (IntDiv.modz_pow2_div 83 (8*i) z _) 1:/#.
  by apply gbc_word_mod_power; smt().
qed.

lemma gbc_canonical_encoded_first z (tail : W8.t list) :
  gub_canonical (BArray26.of_list (gbc_encode_bytes 11 z ++ tail)) =
    BArray26.of_list (gbc_encode_bytes 11 (z %% (2^83)) ++ tail).
proof.
  apply BArray26.ext_eq => i hi.
  case (i=10) => h10.
  + subst i; rewrite gub_canonical_byte10 !BArray26.get_of_list 1..2://.
    rewrite !nth_cat !gbc_encode_bytes_size //= !gbc_encode_bytes_nth //=.
    have h := gbc_low83_digit z 10 _; first trivial.
    by move: h; rewrite /= => ->.
  rewrite (gub_canonical_outside _ i hi h10) !BArray26.get_of_list 1..2:hi.
  rewrite !nth_cat !gbc_encode_bytes_size //=.
  case (i<11) => h11 /=; last trivial.
  rewrite !gbc_encode_bytes_nth 1..2:/#.
  have h := gbc_low83_digit z i _; first smt().
  by move: h; rewrite h10 /= => ->.
qed.

lemma gbc_candidate_blocks :
  gbc_candidate = dlet (gbc_bytes 11) (fun cdt =>
    dlet (gbc_bytes 6) (fun rej =>
      dmap (gbc_bytes 9) (fun noise => BArray26.of_list (cdt ++ (rej ++ noise))))).
proof.
  rewrite /gbc_candidate /BArray26.darray /gbc_bytes
    (dlist_add W8.dword 11 15) 1,2:// dmap_comp dmap_dprodE.
  apply eq_dlet => // cdt /=.
  rewrite (dlist_add W8.dword 6 9) 1,2:// dmap_comp dmap_dprodE.
  apply eq_dlet => // rej /=; apply eq_dmap => noise.
  by rewrite /(\o) /=.
qed.

lemma gbc_candidate_integers :
  gbc_candidate = dlet (dinter 0 (256^11-1)) (fun u =>
    dlet (dinter 0 (256^6-1)) (fun v =>
      dmap (dinter 0 (256^9-1)) (fun y => BArray26.of_list
        (gbc_encode_bytes 11 u ++ (gbc_encode_bytes 6 v ++ gbc_encode_bytes 9 y))))).
proof.
  have h11 := gbc_encode_uniform 11 _; first trivial.
  have h6 := gbc_encode_uniform 6 _; first trivial.
  have h9 := gbc_encode_uniform 9 _; first trivial.
  rewrite gbc_candidate_blocks -h11 -h6 -h9 dlet_dmap.
  apply eq_dlet => // u /=; rewrite dlet_dmap.
  apply eq_dlet => // v /=; rewrite dmap_comp.
  apply eq_dmap => y; by rewrite /(\o) /=.
qed.

(* Projecting a uniform 88-bit first block to its low 83 bits is exact.
   The high five bits are discarded; the other byte fields stay independent. *)
lemma gbc_canonical_law p :
  dmap gbc_candidate gub_canonical = gr_candidate_distribution p.
proof.
  have hcanonical : dmap gbc_candidate gub_canonical =
    dlet (dinter 0 (256^11-1)) (fun u =>
      dlet (dinter 0 (256^6-1)) (fun v =>
        dmap (dinter 0 (256^9-1)) (fun y =>
          gr_candidate_patch p (u %% cdt83_modulus) y v))).
  + rewrite gbc_candidate_integers dmap_dlet; apply eq_dlet => // u /=.
    rewrite dmap_dlet; apply eq_dlet => // v /=.
    rewrite dmap_comp; apply eq_dmap => y.
    by rewrite /(\o) /= gbc_canonical_encoded_first
      /cdt83_modulus -(gbc_candidate_patch_bytes p (u %% (2^83)) y v).
  have hmod : dmap (dinter 0 (256^11-1)) (fun u => u %% cdt83_modulus) =
      dinter 0 (cdt83_modulus-1).
  + apply duni_range_dvd; by rewrite /cdt83_modulus.
  rewrite hcanonical /gr_candidate_distribution -hmod dlet_dmap.
  apply eq_dlet => // u /=.
  rewrite /sr_noise_uniform /rejection48_uniform /= /dmap dlet_swap.
  trivial.
qed.

lemma gbc_candidate_sigma_law p :
  dmap gbc_candidate sigma76_spec = dmap (gr_candidate_distribution p) sigma76_spec.
proof.
  rewrite -(gbc_canonical_law p) (dmap_comp gub_canonical sigma76_spec gbc_candidate).
  apply eq_dmap => bytes.
  by rewrite /(\o) gub_sigma76_spec.
qed.

lemma gbc_candidate_observer_law p :
  dmap gbc_candidate gr_candidate_observer = sc_actual_pair p.
proof.
  rewrite -(gr_candidate_distribution_pair p) -(gbc_canonical_law p)
    (dmap_comp gub_canonical gr_candidate_observer gbc_candidate).
  apply eq_dmap => bytes.
  by rewrite /(\o) /gr_candidate_observer gub_sigma76_spec.
qed.

lemma gbc_candidate_acceptance_lower &m :
  1%r/7%r <= mu gbc_candidate (fun bytes => (sigma76_spec bytes).`4 = W64.one).
proof.
  have h := sc_actual_acceptance_lower (witness<:BArray26.t>) &m.
  by move: h; rewrite -(sc_actual_acceptance_law (witness<:BArray26.t>) &m)
    -(gbc_candidate_observer_law (witness<:BArray26.t>))
    dmapE /(\o) /sc_accepted /gr_candidate_observer /=.
qed.

lemma gbc_chunks_observer_iid p n : 0 <= n =>
  dmap (gbc_bytes (26*n)) (fun bytes => map gr_candidate_observer (gbc_chunks n bytes)) =
    dlist (sc_actual_pair p) n.
proof.
  move=> hn; rewrite -(gbc_candidate_observer_law p) dlist_dmap
    -(gbc_chunks_iid n hn) dmap_comp.
  apply eq_dmap => bytes; by rewrite /(\o).
qed.
