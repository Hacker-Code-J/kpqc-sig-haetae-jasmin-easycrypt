require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray8192 BArray32768 VerifyUnpackMode2Target
  VerifyUnpackV3AssemblyPostFreeze VerifyUnpackV3NttPostFreeze
  VerifyUnpackV3NttBound17PostFreeze.
require import Rq NTTRowProductSpec KeygenM23ArithmeticSpec
  KeygenM23MatrixSpec.

import VerifyUnpackV3AssemblyPostFreeze.

theory VerifyUnpackV3NttInstallPostFreeze.

module Verify = VerifyUnpackMode2Target.M.

module InstallFirstColumnMode2 = {
  proc run (matp : BArray32768.t, bp : BArray8192.t) : BArray32768.t = {
    matp <@ Verify._polymat_set_first_column
      (matp, bp, W64.of_int mode2_rows, W64.of_int mode2_cols);
    return matp;
  }
}.

lemma install_first_column_mode2_word_exact
    (mat0 : BArray32768.t) (bp0 : BArray8192.t) :
  hoare [InstallFirstColumnMode2.run :
    matp = mat0 /\ bp = bp0
    ==>
    mat_firstcol_install_prefix bp0 res mode2_vec_words /\
    mat_firstcol_install_frame mat0 res mode2_vec_words].
proof.
proc.
call (polymat_set_first_column_mode2_word_exact mat0 bp0).
auto => />.
qed.

(* This wrapper is the exact generated suffix after the pre-NTT arithmetic.
   It exposes the transformed vector alongside the returned matrix so the
   NTT semantics and the first-column installation can be composed without
   hiding either intermediate value. *)
module ActualVerifyUnpackNttInstallMode2 = {
  proc run (bp : BArray8192.t, matp : BArray32768.t)
      : BArray8192.t * BArray32768.t = {
    bp <@ Verify._polyvec_ntt
      (bp, W64.of_int mode2_rows);
    matp <@ InstallFirstColumnMode2.run (matp, bp);
    return (bp, matp);
  }
}.

lemma actual_verify_unpack_ntt_install_mode2_full_correct
    (bp0 : BArray8192.t) (mat0 : BArray32768.t)
    (p0 p1 : Rq.poly) :
  hoare [ActualVerifyUnpackNttInstallMode2.run :
    bp = bp0 /\ matp = mat0 /\
    VerifyUnpackV3NttPostFreeze.verify_unpack_ntt_input_repr_bound16
      bp0 p0 p1
    ==>
    VerifyUnpackV3NttPostFreeze.verify_unpack_ntt_repr_bound24
      res.`1 p0 p1 /\
    NTTRowProductSpec.vector_forward_repr
      VerifyUnpackV3NttPostFreeze.verify_unpack_ntt_polys
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          res.`1 (col * KeygenM23MatrixSpec.poly_words_i))
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          bp0 (col * KeygenM23MatrixSpec.poly_words_i)) /\
    KeygenM23MatrixSpec.word_tail_frame
      bp0 res.`1 VerifyUnpackV3NttPostFreeze.verify_unpack_ntt_words /\
    mat_firstcol_install_prefix res.`1 res.`2 mode2_vec_words /\
    mat_firstcol_install_frame mat0 res.`2 mode2_vec_words].
proof.
proc.
seq 1 :
  (exists ntt,
     bp = ntt /\ matp = mat0 /\
     VerifyUnpackV3NttPostFreeze.verify_unpack_ntt_repr_bound24
       ntt p0 p1 /\
     NTTRowProductSpec.vector_forward_repr
       VerifyUnpackV3NttPostFreeze.verify_unpack_ntt_polys
       (fun col =>
         KeygenM23ArithmeticSpec.wide_poly
           ntt (col * KeygenM23MatrixSpec.poly_words_i))
       (fun col =>
         KeygenM23ArithmeticSpec.wide_poly
           bp0 (col * KeygenM23MatrixSpec.poly_words_i)) /\
     KeygenM23MatrixSpec.word_tail_frame
       bp0 ntt VerifyUnpackV3NttPostFreeze.verify_unpack_ntt_words).
+ call
    (VerifyUnpackV3NttPostFreeze.verify_unpack_polyvec_ntt_count2_full_correct
       bp0 p0 p1).
  auto => /> result hbound hrepr htail.
  smt().
exlim bp => ntt0.
call (install_first_column_mode2_word_exact mat0 ntt0).
auto => />.
qed.

lemma actual_verify_unpack_ntt_install_mode2_full_correct17
    (bp0 : BArray8192.t) (mat0 : BArray32768.t)
    (p0 p1 : Rq.poly) :
  hoare [ActualVerifyUnpackNttInstallMode2.run :
    bp = bp0 /\ matp = mat0 /\
    VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_input_repr_bound17
      bp0 p0 p1
    ==>
    VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_repr_bound25
      res.`1 p0 p1 /\
    NTTRowProductSpec.vector_forward_repr
      VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_polys
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          res.`1 (col * KeygenM23MatrixSpec.poly_words_i))
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          bp0 (col * KeygenM23MatrixSpec.poly_words_i)) /\
    KeygenM23MatrixSpec.word_tail_frame
      bp0 res.`1
        VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_words /\
    mat_firstcol_install_prefix res.`1 res.`2 mode2_vec_words /\
    mat_firstcol_install_frame mat0 res.`2 mode2_vec_words].
proof.
proc.
seq 1 :
  (exists ntt,
     bp = ntt /\ matp = mat0 /\
     VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_repr_bound25
       ntt p0 p1 /\
     NTTRowProductSpec.vector_forward_repr
       VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_polys
       (fun col =>
         KeygenM23ArithmeticSpec.wide_poly
           ntt (col * KeygenM23MatrixSpec.poly_words_i))
       (fun col =>
         KeygenM23ArithmeticSpec.wide_poly
           bp0 (col * KeygenM23MatrixSpec.poly_words_i)) /\
     KeygenM23MatrixSpec.word_tail_frame
       bp0 ntt
         VerifyUnpackV3NttBound17PostFreeze.verify_unpack_ntt_words).
+ call
    (VerifyUnpackV3NttBound17PostFreeze.verify_unpack_polyvec_ntt_count2_full_correct
       bp0 p0 p1).
  auto => /> result hbound hrepr htail.
  smt().
exlim bp => ntt0.
call (install_first_column_mode2_word_exact mat0 ntt0).
auto => />.
qed.

end VerifyUnpackV3NttInstallPostFreeze.
