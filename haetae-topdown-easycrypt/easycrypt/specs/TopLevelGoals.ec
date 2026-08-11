require import AllCore Distr List Real.

theory TopLevelGoals.

(* These are specification symbols, not implementation assumptions.  The
   Boolean operations below are the exact claims that later refinement
   theories must establish. *)
type pkey.
type skey.
type message.
type signature.

op JKeyGen_mode2 : (pkey * skey) distr.
op PaperKeyGen_mode2 : (pkey * skey) distr.

op JSign_mode2 : skey -> message -> signature distr.
op PaperSign_mode2 : skey -> message -> signature distr.

op JVerify_mode2 : pkey -> message -> signature -> bool.
op PaperVerify_mode2 : pkey -> message -> signature -> bool.

op epsilon_correctness : real.
op end_to_end_failure : real.

op FC_KeyGen : bool =
  JKeyGen_mode2 = PaperKeyGen_mode2.

op FC_Sign : bool =
  forall sk m, JSign_mode2 sk m = PaperSign_mode2 sk m.

op FC_Verify : bool =
  forall pk m sig,
    JVerify_mode2 pk m sig = PaperVerify_mode2 pk m sig.

op EndToEnd_Correctness : bool =
  0%r <= epsilon_correctness /\
  end_to_end_failure <= epsilon_correctness.

(* Implementation-to-paper security composition. *)
op adv_euf_cma_jasmin : real.
op adv_euf_cma_paper : real.
op delta_KeyGen : real.
op delta_Sign : real.
op delta_Verify : real.
op delta_Encoding : real.
op qSign : int.

op ImplementationSecurityComposition : bool =
  0 <= qSign /\
  adv_euf_cma_jasmin <=
    adv_euf_cma_paper + delta_KeyGen +
    (qSign%r * delta_Sign) + delta_Verify + delta_Encoding.

(* Paper-level reduction boundary. *)
op adv_MLWE : real.
op adv_BST_MSIS : real.
op epsilon_ROM : real.
op epsilon_Rejection : real.
op epsilon_Fork : real.

op PaperSecurityReduction : bool =
  adv_euf_cma_paper <=
    adv_MLWE + adv_BST_MSIS + epsilon_ROM +
    epsilon_Rejection + epsilon_Fork.

end TopLevelGoals.
