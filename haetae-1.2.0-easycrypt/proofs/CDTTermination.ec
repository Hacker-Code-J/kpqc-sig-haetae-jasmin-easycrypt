require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import SamplerTarget.
import SLH64.

lemma cdt_counter_increment (i : W64.t) :
  W64.to_uint i < 166 =>
  W64.to_uint (i + W64.one) = W64.to_uint i + 1.
proof.
  move=> hi.
  rewrite W64.to_uintD W64.to_uint1 modz_small //.
  have /= hr := W64.to_uint_cmp i; smt().
qed.

lemma sample_gauss83_ll : islossless SamplerTarget.M._sample_gauss83.
proof.
  proc.
  while (true) (166 - W64.to_uint i).
  + move=> z; auto => />.
    move=> &hr; rewrite W64.ultE /=; move=> hi.
    rewrite cdt_counter_increment //; smt().
  while (true) (76 - W64.to_uint i).
  + move=> z; auto => />.
    move=> &hr; rewrite W64.ultE /=; move=> hi.
    rewrite cdt_counter_increment 1:/#; smt().
  auto => />.
  move=> i; split.
  + rewrite W64.ultE /=; smt().
  move=> _ j; rewrite W64.ultE /=; smt().
qed.

lemma sample_gauss83_jazz_ll : islossless SamplerTarget.M.sample_gauss83_jazz.
proof. proc; call sample_gauss83_ll; wp; skip; auto. qed.
