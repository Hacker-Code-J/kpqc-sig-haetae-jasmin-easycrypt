require import AllCore Real.

theory SecurityAssumptions.

(* Only these cryptographic interfaces may remain assumptions in the final
   theorem.  Their concrete games and parameter instances remain explicit. *)
type mlwe_instance.
type bst_msis_instance.
type rom_instance.

op haetae2_mlwe : mlwe_instance.
op haetae2_bst_msis : bst_msis_instance.
op haetae2_rom : rom_instance.

op mlwe_advantage : mlwe_instance -> real.
op bst_msis_advantage : bst_msis_instance -> real.
op rom_failure_probability : rom_instance -> real.

op cryptographic_bounds_well_formed : bool =
  0%r <= mlwe_advantage haetae2_mlwe /\
  0%r <= bst_msis_advantage haetae2_bst_msis /\
  0%r <= rom_failure_probability haetae2_rom.

end SecurityAssumptions.
