require import AllCore List.

from Jasmin require import JModel_x86.

import SLH64.

theory TranscriptBytes.

op mu32 (mu64 : W8.t list) : W8.t list = take 32 mu64.

op sign_challenge_input
    (highbits lsb mu64 : W8.t list) : W8.t list =
  highbits ++ lsb ++ mu32 mu64.

op verify_challenge_input
    (highbits lsb mu : W8.t list) : W8.t list =
  highbits ++ lsb ++ mu.

lemma challenge_input_eq_from_mu_prefix highbits lsb mu64 mu :
  mu32 mu64 = mu =>
  sign_challenge_input highbits lsb mu64 =
  verify_challenge_input highbits lsb mu.
proof.
move=> hmu.
by rewrite /sign_challenge_input /verify_challenge_input hmu.
qed.

lemma challenge_input_eq_components
    highbits_s highbits_v lsb_s lsb_v mu64 mu :
  highbits_s = highbits_v =>
  lsb_s = lsb_v =>
  mu32 mu64 = mu =>
  sign_challenge_input highbits_s lsb_s mu64 =
  verify_challenge_input highbits_v lsb_v mu.
proof.
by move=> -> -> hmu; apply challenge_input_eq_from_mu_prefix.
qed.

end TranscriptBytes.
