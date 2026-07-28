require import AllCore IntDiv.

from Jasmin require import JModel_x86.

require import BArray8192 KeygenM23MatrixSpec
               KeygenM23FinalizeSpec KeygenM23FinalizeSemantics
               KeygenM23FinalizeArraySemantics HAETAE_Algebra.

theory KeygenM23FinalizeHAETAEBridge.

lemma vk_low_int_eq_haetae (x : int) :
  KeygenM23FinalizeSemantics.vk_low_int x =
    HAETAE_Algebra.coeff_decompose_vk_low x.
proof.
by rewrite /KeygenM23FinalizeSemantics.vk_low_int
           /HAETAE_Algebra.coeff_decompose_vk_low.
qed.

lemma vk_high_int_eq_haetae (x : int) :
  KeygenM23FinalizeSemantics.vk_high_int x =
    HAETAE_Algebra.coeff_decompose_vk_high x.
proof.
by rewrite /KeygenM23FinalizeSemantics.vk_high_int
           /HAETAE_Algebra.coeff_decompose_vk_high
           vk_low_int_eq_haetae.
qed.

lemma egen_low_word_haetae (b : W32.t) :
  W32.to_uint b < KeygenM23FinalizeSemantics.q =>
  KeygenM23FinalizeSpec.egen_low_word b =
    W32.of_int
      (HAETAE_Algebra.coeff_decompose_vk_low (W32.to_uint b)).
proof.
move=> hb.
rewrite KeygenM23FinalizeSemantics.egen_low_word_semantics 1:hb.
by rewrite vk_low_int_eq_haetae.
qed.

lemma egen_high_word_haetae (b : W32.t) :
  W32.to_uint b < KeygenM23FinalizeSemantics.q =>
  KeygenM23FinalizeSpec.egen_high_word b =
    W32.of_int
      (HAETAE_Algebra.coeff_decompose_vk_high (W32.to_uint b)).
proof.
move=> hb.
rewrite KeygenM23FinalizeSemantics.egen_high_word_semantics 1:hb.
by rewrite vk_high_int_eq_haetae.
qed.

lemma egen_low_word_to_sint_haetae (b : W32.t) :
  W32.to_uint b < KeygenM23FinalizeSemantics.q =>
  W32.to_sint (KeygenM23FinalizeSpec.egen_low_word b) =
    HAETAE_Algebra.coeff_decompose_vk_low (W32.to_uint b).
proof.
move=> hb.
rewrite KeygenM23FinalizeSemantics.egen_low_word_to_sint 1:hb.
by rewrite vk_low_int_eq_haetae.
qed.

lemma egen_high_word_to_sint_haetae (b : W32.t) :
  W32.to_uint b < KeygenM23FinalizeSemantics.q =>
  W32.to_sint (KeygenM23FinalizeSpec.egen_high_word b) =
    HAETAE_Algebra.coeff_decompose_vk_high (W32.to_uint b).
proof.
move=> hb.
rewrite KeygenM23FinalizeSemantics.egen_high_word_to_sint 1:hb.
by rewrite vk_high_int_eq_haetae.
qed.

(* This is the pointwise paper-level view justified for the 512 active
   finalizer words.  It deliberately stops at coefficient decomposition:
   no equality with the security model's complete key-generation procedure
   or polynomial-multiplication path is asserted here. *)
op finalize_haetae_semantic_output
    (bp0 s2p0 ap0 bp s2p : BArray8192.t) : bool =
  (forall i,
    0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
    W32.to_uint (BArray8192.get32 bp i) =
      HAETAE_Algebra.coeff_decompose_vk_high
        (KeygenM23FinalizeArraySemantics.raw_residue
          (BArray8192.get32 bp0 i)
          (BArray8192.get32 s2p0 i)
          (BArray8192.get32 ap0 i)) /\
    W32.to_sint (BArray8192.get32 s2p i) =
      W32.to_sint (BArray8192.get32 s2p0 i) -
        HAETAE_Algebra.coeff_decompose_vk_low
          (KeygenM23FinalizeArraySemantics.raw_residue
            (BArray8192.get32 bp0 i)
            (BArray8192.get32 s2p0 i)
            (BArray8192.get32 ap0 i))) /\
  KeygenM23MatrixSpec.word_tail_frame
    bp0 bp KeygenM23MatrixSpec.mode2_b_words_i /\
  KeygenM23MatrixSpec.word_tail_frame
    s2p0 s2p KeygenM23MatrixSpec.mode2_b_words_i.

lemma finalize_semantic_output_haetae
    (bp0 s2p0 ap0 bp s2p : BArray8192.t) :
  KeygenM23FinalizeArraySemantics.finalize_semantic_output
    bp0 s2p0 ap0 bp s2p =>
  finalize_haetae_semantic_output bp0 s2p0 ap0 bp s2p.
proof.
rewrite /KeygenM23FinalizeArraySemantics.finalize_semantic_output
        /finalize_haetae_semantic_output.
move=> [hwords [hbptail hs2tail]].
split.
+ move=> i hi.
  have h := hwords i hi.
  move: h.
  by rewrite vk_high_int_eq_haetae vk_low_int_eq_haetae.
+ split.
  + exact hbptail.
  + exact hs2tail.
qed.

end KeygenM23FinalizeHAETAEBridge.
