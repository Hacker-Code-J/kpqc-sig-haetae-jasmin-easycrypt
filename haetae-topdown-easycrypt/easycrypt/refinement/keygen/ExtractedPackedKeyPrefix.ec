require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import PackedKeyPrefix KeygenMode2ParentTarget.

theory ExtractedPackedKeyPrefix.

module Parent = KeygenMode2ParentTarget.M.

op mode2_vkbytes : int = PackedKeyPrefix.mode2_vkbytes.
op vk_prefix_eq = PackedKeyPrefix.vk_prefix_eq.
op copied_prefix = PackedKeyPrefix.copied_prefix.

op mode2_mcount : int = 3.
op mode2_kcount : int = 2.
op mode2_eta_poly_bytes : int = 64.
op mode2_eta2_poly_bytes : int = 96.
op mode2_key_bytes : int = 32.
op mode2_eta_off : int = mode2_vkbytes.
op mode2_eta2_off : int =
  mode2_eta_off + mode2_mcount * mode2_eta_poly_bytes.
op mode2_key_off : int =
  mode2_eta2_off +
  mode2_kcount * mode2_eta2_poly_bytes.

lemma mode2_mcount_word_bytes :
  W64.of_int mode2_mcount * W64.of_int mode2_eta_poly_bytes =
  W64.of_int (mode2_mcount * mode2_eta_poly_bytes).
proof.
by rewrite /mode2_mcount /mode2_eta_poly_bytes /=.
qed.

lemma mode2_key_offset_word :
  W64.of_int mode2_eta2_off +
    W64.of_int (mode2_kcount * mode2_eta2_poly_bytes) =
  W64.of_int mode2_key_off.
proof.
by rewrite /mode2_key_off /mode2_eta2_off /mode2_eta_off
           /mode2_vkbytes /mode2_mcount /mode2_kcount
           /mode2_eta_poly_bytes /mode2_eta2_poly_bytes /=.
qed.

lemma mode2_key_index_after_prefix (i : W64.t) :
  W64.to_uint i <= mode2_key_bytes =>
  mode2_vkbytes <= W64.to_uint (W64.of_int mode2_key_off + i).
proof.
move=> hi.
rewrite /mode2_key_off /mode2_eta2_off /mode2_eta_off
        /mode2_vkbytes /mode2_mcount /mode2_kcount
        /mode2_eta_poly_bytes /mode2_eta2_poly_bytes /mode2_key_bytes.
rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
smt(W64.to_uint_cmp).
qed.

lemma pack_vec_eta_to_prefix_frame
    (vk : BArray2080.t) :
  hoare [Parent._pack_vec_eta_to :
    vk_prefix_eq outp vk mode2_vkbytes /\
    out_off = W64.of_int mode2_eta_off /\
    count = W64.of_int mode2_mcount
    ==>
    vk_prefix_eq res vk mode2_vkbytes].
proof.
proc.
while (vk_prefix_eq outp vk mode2_vkbytes /\
       count = W64.of_int mode2_mcount /\
       0 <= W64.to_uint poly <= mode2_mcount /\
       W64.to_uint pos =
         mode2_eta_off +
         W64.to_uint poly * mode2_eta_poly_bytes).
+ wp.
  while (vk_prefix_eq outp vk mode2_vkbytes /\
         count = W64.of_int mode2_mcount /\
         0 <= W64.to_uint poly < mode2_mcount /\
         0 <= W64.to_uint i <= 64 /\
         W64.to_uint pos =
           mode2_eta_off +
           W64.to_uint poly * mode2_eta_poly_bytes +
           W64.to_uint i).
  + auto => /> &hr hprefix hpoly0 hpolylt hi0 hile hpos_eq hguard.
    have hpos : mode2_vkbytes <= W64.to_uint pos{hr}.
    + rewrite hpos_eq /mode2_eta_off.
      smt().
    have hpos_next :
        W64.to_uint (pos{hr} + W64.one) =
        W64.to_uint pos{hr} + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hi_lt : W64.to_uint i{hr} < 64.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK /=.
      smt(W64.to_uint_cmp).
    have hi_next :
        W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    split.
    + apply PackedKeyPrefix.vk_prefix_eq_set_after.
      * exact hprefix.
      * exact hpos.
    split.
    + split.
      * smt(W64.to_uint_cmp).
      * smt().
    + rewrite hpos_next hi_next.
      smt().
  auto => /> &hr hprefix0 hpoly0 hpolyle hpos0 hguard0.
  rewrite W64.ultE W64.of_uintK /= in hguard0.
  have hpolylt0 : W64.to_uint poly{hr} < mode2_mcount.
  + rewrite /mode2_mcount in hguard0.
    exact hguard0.
  split; first exact hpolylt0.
  move=> i0 outp0 pos0 hdone hprefix1 hpolylt1 hi0 hi64 hpos1.
  have hi_eq : W64.to_uint i0 = 64.
  + rewrite W64.ultE W64.of_uintK /= in hdone.
    smt(W64.to_uint_cmp).
  have hpoly_next :
      W64.to_uint (poly{hr} + W64.one) = W64.to_uint poly{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  split.
  + split.
    + smt(W64.to_uint_cmp).
    + move=> _.
      rewrite hpoly_next.
      smt().
  + rewrite hpoly_next hpos1 hi_eq.
    smt().
auto => />.
qed.

lemma pack_vec2_eta_to_prefix_frame
    (vk : BArray2080.t) :
  hoare [Parent._pack_vec2_eta_to :
    vk_prefix_eq outp vk mode2_vkbytes /\
    out_off = W64.of_int mode2_eta2_off /\
    count = W64.of_int mode2_kcount
    ==>
    vk_prefix_eq res vk mode2_vkbytes].
proof.
proc.
while (vk_prefix_eq outp vk mode2_vkbytes /\
       count = W64.of_int mode2_kcount /\
       0 <= W64.to_uint poly <= mode2_kcount /\
       W64.to_uint pos =
         mode2_eta2_off +
         W64.to_uint poly * mode2_eta2_poly_bytes).
+ wp.
  while (vk_prefix_eq outp vk mode2_vkbytes /\
         count = W64.of_int mode2_kcount /\
         0 <= W64.to_uint poly < mode2_kcount /\
         0 <= W64.to_uint i <= 32 /\
         W64.to_uint pos =
           mode2_eta2_off +
           W64.to_uint poly * mode2_eta2_poly_bytes +
           3 * W64.to_uint i).
  + auto => /> &hr hprefix hpoly0 hpolylt hi0 hi32 hpos_eq hguard.
    have hpos : mode2_vkbytes <= W64.to_uint pos{hr}.
    + rewrite hpos_eq /mode2_eta2_off /mode2_eta_off.
      smt().
    have hpos1 :
        mode2_vkbytes <= W64.to_uint (pos{hr} + W64.of_int 1).
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      smt().
    have hpos2 :
        mode2_vkbytes <= W64.to_uint (pos{hr} + W64.of_int 2).
    + rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
      smt().
    have hpos_next :
        W64.to_uint (pos{hr} + W64.of_int 3) =
        W64.to_uint pos{hr} + 3.
    + rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
      trivial.
    have hi_lt : W64.to_uint i{hr} < 32.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK /=.
      smt(W64.to_uint_cmp).
    have hi_next :
        W64.to_uint (i{hr} + W64.one) =
        W64.to_uint i{hr} + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    split.
    + apply PackedKeyPrefix.vk_prefix_eq_set_after.
      * apply PackedKeyPrefix.vk_prefix_eq_set_after.
        + apply PackedKeyPrefix.vk_prefix_eq_set_after.
          * exact hprefix.
          * exact hpos.
        + exact hpos1.
      * exact hpos2.
    split.
    + split.
      * smt(W64.to_uint_cmp).
      * smt().
    + rewrite hpos_next hi_next.
      smt().
  auto => /> &hr hprefix0 hpoly0 hpolyle hpos0 hguard0.
  rewrite W64.ultE W64.of_uintK /= in hguard0.
  have hpolylt0 : W64.to_uint poly{hr} < mode2_kcount.
  + rewrite /mode2_kcount in hguard0.
    exact hguard0.
  split; first exact hpolylt0.
  move=> i0 outp0 pos0 hdone hprefix1 hpolylt1 hi0 hi32 hpos1.
  have hi_eq : W64.to_uint i0 = 32.
  + rewrite W64.ultE W64.of_uintK /= in hdone.
    smt(W64.to_uint_cmp).
  have hpoly_next :
      W64.to_uint (poly{hr} + W64.one) = W64.to_uint poly{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  split.
  + split.
    + smt(W64.to_uint_cmp).
    + move=> _.
      rewrite hpoly_next.
      smt().
  + rewrite hpoly_next hpos1 hi_eq.
    smt().
auto => />.
qed.

lemma pack_sk_m23_mode2_vk_prefix
    (vk0 : BArray2080.t) :
  hoare [Parent._pack_sk_m23 :
    vkp = vk0 /\
    vkbytes = W64.of_int mode2_vkbytes /\
    mcount = W64.of_int mode2_mcount /\
    kcount = W64.of_int mode2_kcount
    ==>
    vk_prefix_eq res vk0 mode2_vkbytes].
proof.
proc.
wp.
while (vk_prefix_eq skp vk0 mode2_vkbytes /\
       off = W64.of_int mode2_key_off /\
       0 <= W64.to_uint i <= mode2_key_bytes).
+ auto.
  move=> &hr [[hprefix [hoff [hi0 hi_le]]] hguard].
  have hstep :
      mode2_vkbytes <= W64.to_uint (off{hr} + i{hr}).
  + rewrite hoff.
    exact (mode2_key_index_after_prefix i{hr} hi_le).
  have hi_lt : W64.to_uint i{hr} < mode2_key_bytes.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  have hi_next :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  split.
  + apply PackedKeyPrefix.vk_prefix_eq_set_after.
    * exact hprefix.
    * exact hstep.
  + split.
    * smt(W64.to_uint_cmp).
    * rewrite hi_next.
      smt().
auto => />.
call (pack_vec2_eta_to_prefix_frame vk0).
auto => />.
move=> &hr [hvkp [hvkbytes [hm hk]]] off0 skp0 [[hp hoff] hpost] /=.
rewrite hvkp in hp.
rewrite hvkp hm hk.
split.
+ do split.
  + exact hp.
  + rewrite mode2_mcount_word_bytes.
    exact hoff.
  + trivial.
+ move=> hleft out1 hres.
  split; first exact hres.
  rewrite mode2_mcount_word_bytes hoff.
  have hkey := mode2_key_offset_word.
  rewrite /mode2_eta2_poly_bytes in hkey.
  exact hkey.
call (pack_vec_eta_to_prefix_frame vk0).
auto => />.
while (vkp = vk0 /\
       vkbytes = W64.of_int mode2_vkbytes /\
       mcount = W64.of_int mode2_mcount /\
       kcount = W64.of_int mode2_kcount /\
       copied_prefix skp vk0 (W64.to_uint i) /\
       0 <= W64.to_uint i <= mode2_vkbytes).
+ auto.
  move=> &hr
    [[hvkp [hvkbytes [hm [hk [hcopy [hi0 hi_le]]]]]] hguard].
  have hi_lt : W64.to_uint i{hr} < mode2_vkbytes.
  + rewrite W64.ultE hvkbytes in hguard.
    move: hguard.
    rewrite /mode2_vkbytes /PackedKeyPrefix.mode2_vkbytes /=.
  have hi_next :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  trivial.
  have hi_next_body :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  split; first exact hvkp.
  split; first exact hvkbytes.
  split; first exact hm.
  split; first exact hk.
  split.
  + rewrite hi_next_body.
    have -> : vkp{hr} = vk0 by exact hvkp.
    apply PackedKeyPrefix.copied_prefix_step.
    * exact hcopy.
    * exact hi_lt.
  + rewrite hi_next_body.
    smt(W64.to_uint_cmp).
auto => />.
move=> &hr.
split.
+ smt().
+ move=> i0 skp0 hdone hi0 hi_le hcopy hi_le'.
  have hi_ge : mode2_vkbytes <= W64.to_uint i0.
  + move: hdone.
    rewrite W64.ultE /mode2_vkbytes
            /PackedKeyPrefix.mode2_vkbytes /=.
    smt(W64.to_uint_cmp).
  rewrite /vk_prefix_eq /PackedKeyPrefix.vk_prefix_eq.
  move=> j hj.
  apply hcopy.
  smt().
qed.

lemma keypair_full_m23_mode2_return_prefix :
  hoare [Parent._keypair_full_m23 :
    k = 2 /\
    m = 3 /\
    vkbytes = mode2_vkbytes
    ==>
    vk_prefix_eq res.`2 res.`1 mode2_vkbytes].
proof.
proc.
seq 35 :
  (vkbr = W64.of_int mode2_vkbytes /\
   mr = W64.of_int mode2_mcount /\
   kr = W64.of_int mode2_kcount).
+ wp.
  call (_ : true); first by auto.
  wp.
  while (vkbr = W64.of_int mode2_vkbytes /\
         mr = W64.of_int mode2_mcount /\
         kr = W64.of_int mode2_kcount).
  + wp.
    call (_ : true); first by auto.
    wp.
    call (_ : true); first by auto.
    wp.
    call (_ : true); first by auto.
    wp.
    call (_ : true); first by auto.
    wp.
    call (_ : true); first by auto.
    auto.
  wp.
  call (_ : true); first by auto.
  wp.
  call (_ : true); first by auto.
  wp.
  call (_ : true); first by auto.
  auto => />.
wp.
exists* vkp{hr}; elim* => vk0.
call (pack_sk_m23_mode2_vk_prefix vk0).
auto => />.
qed.

lemma keypair_internal_mode2_return_prefix :
  hoare [Parent.crypto_sign_keypair_internal_mode2_jazz :
    true
    ==>
    vk_prefix_eq res.`2 res.`1 mode2_vkbytes].
proof.
proc.
call keypair_full_m23_mode2_return_prefix.
auto.
qed.

end ExtractedPackedKeyPrefix.
