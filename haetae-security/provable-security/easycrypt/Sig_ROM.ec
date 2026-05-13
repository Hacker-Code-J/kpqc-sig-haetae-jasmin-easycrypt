require import AllCore List PROM.

abstract theory Sig_ROM.

type pkey.
type skey.
type message.
type context.
type signature.
type ro_query.
type ro_output.

op [lossless] dro_output : ro_query -> ro_output distr.

type query = message * context.
type signed_query = query * signature.

op fresh_msg (qs : query list) (m : message) (ctx : context) : bool =
  ! ((m, ctx) \in qs).

op fresh_sig (qs : signed_query list) (m : message) (ctx : context)
             (sig : signature) : bool =
  ! (((m, ctx), sig) \in qs).

lemma fresh_msg_nil m ctx : fresh_msg [] m ctx.
proof. by rewrite /fresh_msg. qed.

lemma fresh_sig_nil m ctx sig : fresh_sig [] m ctx sig.
proof. by rewrite /fresh_sig. qed.

clone import FullRO as RO with
  type in_t <- ro_query,
  type out_t <- ro_output,
  op dout <- dro_output.

module type Oracle = {
  include FRO [init, get]
}.

module type POracle = {
  include FRO [get]
}.

module type Scheme(O : POracle) = {
  proc kg() : pkey * skey
  proc sign(sk : skey, m : message, ctx : context) : signature
  proc verify(pk : pkey, m : message, ctx : context,
              sig : signature) : bool
}.

module type CORR_ADV(O : POracle) = {
  proc find(pk : pkey, sk : skey) : message * context
}.

module Correctness(H : Oracle, S : Scheme, A : CORR_ADV) = {
  proc main() : bool = {
    var pk : pkey;
    var sk : skey;
    var m : message;
    var ctx : context;
    var sig : signature;
    var ok : bool;

    H.init();
    (pk, sk) <@ S(H).kg();
    (m, ctx) <@ A(H).find(pk, sk);
    sig <@ S(H).sign(sk, m, ctx);
    ok <@ S(H).verify(pk, m, ctx, sig);
    return !ok;
  }
}.

module type SignOracle = {
  proc sign(m : message, ctx : context) : signature
}.

module type Adversary(H : POracle, O : SignOracle) = {
  proc forge(pk : pkey) : message * context * signature {H.get, O.sign}
}.

module type NMA_Adversary(H : POracle) = {
  proc forge(pk : pkey) : message * context * signature {H.get}
}.

module NMA_As_CMA(A : NMA_Adversary) (H : POracle, O : SignOracle) = {
  proc forge(pk : pkey) : message * context * signature = {
    var r : message * context * signature;

    r <@ A(H).forge(pk);
    return r;
  }
}.

module EUF_CMA(H : Oracle, S : Scheme, A : Adversary) = {
  var sk : skey
  var queries : query list

  module O = {
    proc sign(m : message, ctx : context) : signature = {
      var sig : signature;

      sig <@ S(H).sign(sk, m, ctx);
      queries <- (m, ctx) :: queries;
      return sig;
    }
  }

  module A = A(H, O)

  proc main() : bool = {
    var pk : pkey;
    var m : message;
    var ctx : context;
    var sig : signature;
    var ok : bool;

    H.init();
    queries <- [];
    (pk, sk) <@ S(H).kg();
    (m, ctx, sig) <@ A.forge(pk);
    ok <@ S(H).verify(pk, m, ctx, sig);
    return ok /\ fresh_msg queries m ctx;
  }
}.

module UF_NMA(H : Oracle, S : Scheme, A : NMA_Adversary) = {
  proc main() : bool = {
    var pk : pkey;
    var sk : skey;
    var m : message;
    var ctx : context;
    var sig : signature;
    var ok : bool;

    H.init();
    (pk, sk) <@ S(H).kg();
    (m, ctx, sig) <@ A(H).forge(pk);
    ok <@ S(H).verify(pk, m, ctx, sig);
    return ok;
  }
}.

section NMA_Embedding.

declare module H <: Oracle {-EUF_CMA}.
declare module S <: Scheme {-H, -EUF_CMA}.
declare module A <: NMA_Adversary {-H, -S, -EUF_CMA}.

lemma nma_as_cma_exact &m :
  Pr[EUF_CMA(H, S, NMA_As_CMA(A)).main() @ &m : res] =
  Pr[UF_NMA(H, S, A).main() @ &m : res].
proof.
byequiv (: ={glob H, glob S, glob A} ==> ={res}) => //.
proc.
inline EUF_CMA(H, S, NMA_As_CMA(A)).A.forge
       NMA_As_CMA(A, H, EUF_CMA(H, S, NMA_As_CMA(A)).O).forge.
wp.
call (: ={glob H, glob S, glob A, arg} ==> ={glob H, glob S, glob A, res}).
+ by sim.
wp.
call (: ={glob H, glob S, glob A, arg} ==> ={glob H, glob S, glob A, res}).
+ by sim.
wp.
call (: ={glob H, glob S} ==> ={glob H, glob S, res}).
+ by sim.
wp.
call (: ={glob H} ==> ={glob H}).
+ by sim.
by auto => />.
qed.

end section NMA_Embedding.

module SUF_CMA(H : Oracle, S : Scheme, A : Adversary) = {
  var sk : skey
  var queries : signed_query list

  module O = {
    proc sign(m : message, ctx : context) : signature = {
      var sig : signature;

      sig <@ S(H).sign(sk, m, ctx);
      queries <- ((m, ctx), sig) :: queries;
      return sig;
    }
  }

  module A = A(H, O)

  proc main() : bool = {
    var pk : pkey;
    var m : message;
    var ctx : context;
    var sig : signature;
    var ok : bool;

    H.init();
    queries <- [];
    (pk, sk) <@ S(H).kg();
    (m, ctx, sig) <@ A.forge(pk);
    ok <@ S(H).verify(pk, m, ctx, sig);
    return ok /\ fresh_sig queries m ctx sig;
  }
}.

end Sig_ROM.
