require import AllCore.
require import Sig_ROM HAETAE_Params HAETAE_Algebra HAETAE_Distributions.
require import HAETAE_ROM.

theory HAETAE_Scheme.

import HAETAE_Params.
import HAETAE_Algebra.
import HAETAE_Distributions.
import HAETAE_ROM.

clone import Sig_ROM as SIG with
  type pkey <- pkey,
  type skey <- skey,
  type message <- message,
  type context <- context,
  type signature <- signature,
  type ro_query <- ro_query,
  type ro_output <- ro_output,
  op dro_output <- dro_output.

op haetae_mode : mode.

module HAETAE(H : SIG.POracle) = {
  proc kg() : pkey * skey = {
    var sd : seed;
    var rhoprime : seed;
    var kp : pkey * skey;
    var ro_y : ro_output;

    sd <$ dseed;
    rhoprime <- haetae_keygen_rhoprime sd;
    ro_y <@ H.get(matrix_expand_query haetae_mode rhoprime);
    kp <- keygen_internal haetae_mode rhoprime;
    return kp;
  }

  proc sign(sk : skey, m : message, ctx : context) : signature = {
    var coins : random_coins;
    var pk : pkey;
    var highbits : polyveck;
    var lowbits : poly;
    var mu : crh;
    var ro_y : ro_output;
    var sig : signature;

    coins <$ drandom_coins;
    ro_y <@ H.get(sampler_expand_query coins);
    coins <- ro_signing_coins ro_y;
    pk <- public_key_of_secret haetae_mode sk;
    ro_y <@ H.get(message_hash_query pk ctx m);
    mu <- ro_message_hash ro_y;
    highbits <- commitment_highbits haetae_mode sk m ctx coins;
    lowbits <- commitment_lowbits haetae_mode sk m ctx coins;
    ro_y <@ H.get(challenge_hash_query haetae_mode highbits lowbits mu);
    sig <- sign_internal haetae_mode sk m ctx coins;
    return sig;
  }

  proc verify(pk : pkey, m : message, ctx : context,
              sig : signature) : bool = {
    return verify_internal haetae_mode pk m ctx sig;
  }
}.

end HAETAE_Scheme.
