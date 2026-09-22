require import AllCore IntDiv List Distr DList DBool StdRing StdOrder.
from Jasmin require import JModel_x86.
require import GaussianUniformBytes GaussianIidBufferSpec HyperballScaleSpec.
import HyperballScaleSpec.

(* w2bits lists bits from least to most significant, byte by byte. *)
op gsb_bits (bytes : W8.t list) : bool list = flatten (map W8.w2bits bytes).

op gsb_result_bits (result : gib_result) (signoff : int) : bool list =
  map (fun i => (BArray512.get8 result.`2 (signoff+i %/ 8)).[i %% 8]) (iota_ 0 256).

lemma gsb_word_from_bits : dmap (dlist DBool.dbool 8) W8.bits2w = W8.dword.
proof.
  have huni : is_uniform (dmap (dlist DBool.dbool 8) W8.bits2w).
  + apply dmap_uni_in_inj.
    - move=> xs ys hx hy he.
      have hsx := supp_dlist_size DBool.dbool 8 xs _ hx; first trivial.
      have hsy := supp_dlist_size DBool.dbool 8 ys _ hy; first trivial.
      have /= h := congr1 W8.w2bits _ _ he.
      by move: h; rewrite !W8.bits2wK.
    apply dlist_uni; exact DBool.dbool_uni.
  have hfull : is_full (dmap (dlist DBool.dbool 8) W8.bits2w).
  + move=> w; rewrite supp_dmap; exists (W8.w2bits w); split.
    - rewrite supp_dlist 1:// W8.size_w2bits /=.
      apply/List.allP => b hb; exact (DBool.dbool_fu b).
    by rewrite W8.w2bitsK.
  have hll : is_lossless (dmap (dlist DBool.dbool 8) W8.bits2w).
  + apply dmap_ll; apply dlist_ll; exact DBool.dbool_ll.
  exact (eq_funi_ll _ _ (is_full_funiform _ hfull huni) hll W8.dword_funi W8.dword_ll).
qed.

lemma gsb_word_bits_law : dmap W8.dword W8.w2bits = dlist DBool.dbool 8.
proof.
  rewrite -gsb_word_from_bits dmap_comp.
  apply dmap_id_eq_in => bits hbits.
  have hs := supp_dlist_size DBool.dbool 8 bits _ hbits; first trivial.
  by rewrite /(\o) W8.bits2wK.
qed.

lemma gsb_uniform_bits n : 0 <= n =>
  dmap (gbc_bytes n) gsb_bits = dlist DBool.dbool (8*n).
proof.
  move=> hn.
  rewrite -(dlist_dlist DBool.dbool 8 n _ hn) 1:// -gsb_word_bits_law
    dlist_dmap dmap_comp /gbc_bytes /gsb_bits /(\o).
  trivial.
qed.

lemma gsb_uniform256 : dmap (gbc_bytes 32) gsb_bits = dlist DBool.dbool 256.
proof. exact (gsb_uniform_bits 32 _); trivial. qed.

lemma gsb_bits_nil : gsb_bits [] = [].
proof. by rewrite /gsb_bits /= flatten_nil. qed.

lemma gsb_bits_cons byte bytes : gsb_bits (byte::bytes) = W8.w2bits byte ++ gsb_bits bytes.
proof. by rewrite /gsb_bits /= flatten_cons. qed.

lemma gsb_bits_size bytes : size (gsb_bits bytes) = 8 * size bytes.
proof.
  elim: bytes => [|byte bytes ih]; first by rewrite gsb_bits_nil.
  rewrite gsb_bits_cons size_cat W8.size_w2bits ih /=; ring.
qed.

lemma gsb_bits_nth bytes i : 0 <= i < 8*size bytes =>
  nth false (gsb_bits bytes) i = (nth W8.zero bytes (i %/ 8)).[i %% 8].
proof.
  move=> hi.
  have hd := divz_eq i 8.
  have hr := modz_cmp i 8.
  have hq : 0 <= i %/ 8 < size bytes by smt().
  have hmap : nth [] (map W8.w2bits bytes) (i %/ 8) =
      W8.w2bits (nth W8.zero bytes (i %/ 8)) by
    rewrite (nth_map W8.zero) 1:hq.
  have hprefix : sumz (map size (take (i %/ 8) (map W8.w2bits bytes))) = 8*(i %/ 8).
  + rewrite -size_flatten -map_take -/(gsb_bits (take (i %/ 8) bytes))
      gsb_bits_size size_take 1:/#; smt().
  have h := nth_flatten [] false (map W8.w2bits bytes) (i %/ 8) (i %% 8) _ _.
  + by rewrite size_map.
  + by rewrite hmap W8.size_w2bits.
  have he : 8*(i %/ 8)+i %% 8 = i by smt().
  by move: h; rewrite hprefix he hmap W8.get_w2bits -/(gsb_bits bytes).
qed.

lemma gsb_result_bits_size result signoff : size (gsb_result_bits result signoff) = 256.
proof. by rewrite /gsb_result_bits size_map size_iota. qed.

lemma gsb_result_bits_nth result signoff i : 0 <= i < 256 =>
  nth false (gsb_result_bits result signoff) i =
    (BArray512.get8 result.`2 (signoff+i %/ 8)).[i %% 8].
proof.
  move=> hi; rewrite /gsb_result_bits (nth_map 0) 1:size_iota 1:hi nth_iota 1:hi /=.
  trivial.
qed.

lemma gsb_hb_sign_bit (result : gib_result) signoff i : 0 <= i < 256 =>
  hb_sign_bit result.`2 (8*signoff+i) =
    W8.of_int (b2i (nth false (gsb_result_bits result signoff) i)).
proof.
  move=> hi; rewrite (gsb_result_bits_nth result signoff i hi) /hb_sign_bit
    (mulzC 8 signoff) divzMDl 1:// modzMDl.
  trivial.
qed.

lemma gsb_signs_decode values before squares signoff pending :
  0 <= signoff => signoff+32 <= 512 => 32 <= size pending =>
  gsb_result_bits (values,gib_signs before signoff pending,squares) signoff =
    gsb_bits (take 32 pending).
proof.
  move=> ho hcap hp.
  have htake : size (take 32 pending) = 32 by rewrite size_take 1://; smt().
  apply (List.eq_from_nth false).
  + by rewrite gsb_result_bits_size gsb_bits_size htake.
  move=> i; rewrite gsb_result_bits_size => hi.
  have hd := divz_eq i 8.
  have hr := modz_cmp i 8.
  have hq : 0 <= i %/ 8 < 32 by smt().
  rewrite gsb_result_bits_nth 1:hi /= /gib_signs BArray512.initiE 1:/# /=.
  have hin : signoff <= signoff+i %/ 8 < signoff+32 by smt().
  rewrite hin /= gsb_bits_nth 1:/# nth_take 1:/# 1:/#.
  have he : signoff+i %/ 8-signoff = i %/ 8 by ring.
  by rewrite he.
qed.

lemma gsb_signs_decode32 values before squares signoff signbytes :
  0 <= signoff => signoff+32 <= 512 => size signbytes = 32 =>
  gsb_result_bits (values,gib_signs before signoff signbytes,squares) signoff = gsb_bits signbytes.
proof.
  move=> ho hcap hs.
  have h := gsb_signs_decode values before squares signoff signbytes ho hcap _; first smt().
  by move: h; rewrite take_oversize 1:/#.
qed.
