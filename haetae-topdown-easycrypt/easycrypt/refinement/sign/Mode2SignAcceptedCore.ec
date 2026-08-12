require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import SignAcceptedCoreTarget.

theory Mode2SignAcceptedCore.

module Sign = SignAcceptedCoreTarget.M.

module ActualSignAcceptedCore = {
  var round_cp : BArray1024.t
  var round_high : BArray8192.t
  var round_ay : BArray8192.t
  var round_z1rnd : BArray8192.t
  var round_z2rnd : BArray8192.t
  var round_z10 : BArray1024.t

  var zcheck_z1 : BArray8192.t
  var zcheck_z2 : BArray8192.t
  var zcheck_z1tmp : BArray8192.t
  var zcheck_z2tmp : BArray8192.t
  var zcheck_reject : W64.t

  var hint_hp : BArray8192.t
  var hint_z1rnd : BArray8192.t
  var hint_z2rnd : BArray8192.t
  var accepted : bool

  proc run (cp : BArray1024.t, highp : BArray8192.t, ayp : BArray8192.t,
            z1rndp : BArray8192.t, z2rndp : BArray8192.t,
            z10p : BArray1024.t, hp : BArray8192.t,
            z1p : BArray8192.t, z2p : BArray8192.t,
            z1tmpp : BArray8192.t, z2tmpp : BArray8192.t,
            y1p : BArray8192.t, y2p : BArray8192.t,
            a1p : BArray32768.t, mup : BArray64.t,
            s1p : BArray8192.t, s2p : BArray8192.t,
            b : W8.t, lcount : W64.t, kcount : W64.t,
            b1bound : W64.t, b0bound : W64.t) :
            BArray1024.t * BArray8192.t * BArray8192.t *
            BArray8192.t * BArray8192.t * BArray1024.t *
            BArray8192.t * BArray8192.t * BArray8192.t *
            BArray8192.t * BArray8192.t * W64.t = {
    round_cp <- witness;
    round_high <- witness;
    round_ay <- witness;
    round_z1rnd <- witness;
    round_z2rnd <- witness;
    round_z10 <- witness;
    zcheck_z1 <- witness;
    zcheck_z2 <- witness;
    zcheck_z1tmp <- witness;
    zcheck_z2tmp <- witness;
    zcheck_reject <- witness;
    hint_hp <- witness;
    hint_z1rnd <- witness;
    hint_z2rnd <- witness;
    accepted <- false;

    (cp, highp, ayp, z1rndp, z2rndp, z10p) <@
      Sign._sf_round_challenge_mode2
        (cp, highp, ayp, z1rndp, z2rndp, z10p, y1p, y2p, a1p, mup);
    round_cp <- cp;
    round_high <- highp;
    round_ay <- ayp;
    round_z1rnd <- z1rndp;
    round_z2rnd <- z2rndp;
    round_z10 <- z10p;

    (z1p, z2p, z1tmpp, z2tmpp, zcheck_reject) <@
      Sign._sf_z_check
        (z1p, z2p, z1tmpp, z2tmpp, y1p, y2p, cp, s1p, s2p, b,
         lcount, kcount, b1bound, b0bound);
    zcheck_z1 <- z1p;
    zcheck_z2 <- z2p;
    zcheck_z1tmp <- z1tmpp;
    zcheck_z2tmp <- z2tmpp;
    accepted <- false;

    if (zcheck_reject = W64.zero) {
      (hp, z1rndp, z2rndp) <@
        Sign._sf_hint_mode2
          (hp, z1rndp, z2rndp, highp, ayp, z1p, z2p);
      hint_hp <- hp;
      hint_z1rnd <- z1rndp;
      hint_z2rnd <- z2rndp;
      accepted <- true;
    } else {
      hint_hp <- hp;
      hint_z1rnd <- z1rndp;
      hint_z2rnd <- z2rndp;
    }
    return (cp, highp, ayp, z1rndp, z2rndp, z10p,
            hp, z1p, z2p, z1tmpp, z2tmpp, zcheck_reject);
  }
}.

(* This is intentionally a control theorem, not the missing S-1--S-7
   semantics theorem.  In particular its precondition contains neither
   acceptance nor any equation about the returned arrays. *)
lemma actual_sign_accepted_core_branch_control_mode2 :
  hoare [ActualSignAcceptedCore.run :
    true
    ==>
    ActualSignAcceptedCore.accepted = (res.`12 = W64.zero)].
proof.
proc.
sp 15.
seq 1 : true.
+ call (_ : true ==> true); first by auto.
  auto.
+ sp 6.
  seq 1 : true.
  + call (_ : true ==> true); first by auto.
    auto.
  + sp 5.
    if.
    + wp.
      call (_ : true); first by auto.
      auto => />.
    + auto => />.
qed.

end Mode2SignAcceptedCore.
