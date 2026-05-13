Proof Process: Jasmin → EasyCrypt Equivalence via Hoare Logic                                                                                                                                 
                                                                                                                                                                                                
  The proof establishes a refinement chain across four layers:                                                                                                                                  
                                                                                                                                                                                                
  Jasmin source (poly.jinc)                                                                                                                                                                     
          ↓  [Jasmin compiler extraction]                                                                                                                                                       
  EasyCrypt extraction (Hpoly_extract.ec :: module M)                                                                                                                                           
          ↓  [pRHL equiv, Loop invariants]                                                                                                                                                      
  Imperative EC spec (NTT_Fq.ec :: module NTT)                                                                                                                                                  
          ↓  [phoare / functional reasoning]                                                                                                                                                    
  Abstract math spec (Rq.ec :: op ntt / invntt)                                                                                                                                                 
                                                                                                                                                                                                
  ---                                                                                                                                                                                           
  Phase 1 — Prerequisites: Arithmetic & Root-of-Unity Facts                                                                                                                                     
                                                                                                                                                                                                
  Before any Hoare reasoning, the algebraic foundation must be solid.                                                                                                                           
                                                                                                                                                                                                
  1a. Losslessness (NTT_Fq.ec:110-114)                                                                                                                                                          
  lemma ntt_spec_ll   : islossless NTT.ntt.                                                                                                                                                     
  lemma invntt_spec_ll: islossless NTT.invntt.                                                                                                                                                  
  All loops terminate because len halves each iteration (forward) or doubles with a < 256 bound (inverse). Prove by providing a termination measure and showing each loop body decreases it.    
                                                                                                                                                                                                
  1b. Root-of-unity fact (NTT_Fq.ec:479)                                                                                                                                                        
  lemma exp_zroot_256 : Zq.exp zroot 256 = incoeff (-1).                                                                                                                                        
  Already proved using zroot = 426, zroot^128 = 28837, and field arithmetic mod q = 64513. This justifies that zroot is a primitive 512th root.                                                 
                                                                                                                                                                                                
  ---                                                                                                                                                                                           
  Phase 2 — Representation Bridge (Twiddle-Table Lemmas)                                                                                                                                        
                                                                                                                                                                                                
  The Jasmin code works with BArray1024.t (flat byte arrays of 32-bit words). The spec uses coeff Array256.t. The bridge is:                                                                    
                                                                                                                                                                                                
  poly_repr rp p  ≡  barray256_to_poly rp = p                                                                                                                                                   
                                                                                                                                                                                                
  where barray256_to_poly rp = Array256.init (fun i => word_to_coeff (BArray1024.get32 rp i)).                                                                                                  
                                                                                                                                                                                                
  The two admitted lemmas that must be proved:                                                                                                                                                  
                                                                                                                                                                                                
  (* NTT_Fq.ec:295 *)                                                                                                                                                                           
  lemma jzetas_inv_poly_vals :                                                                                                                                                                  
    barray256_to_poly Hpoly_extract.jzetas_inv = array256_mont_inv zetas_inv.                                                                                                                   
                                                                                                                                                                                                
  (* NTT_Fq.ec:439 *)                                                                                                                                                                           
  lemma jzetas_poly_vals :                                                                                                                                                                      
    barray256_to_poly Hpoly_extract.jzetas = array256_mont zetas.                                                                                                                               
                                                                                                                                                                                                
  Proof strategy: Both jzetas and jzetas_inv (in Hpoly_extract.ec) are concrete BArray1024.of_list32 [...] with explicit W32.of_int values. The right-hand sides array256_mont zetas and        
  array256_mont_inv zetas_inv are also reduced to Array256.of_list witness [incoeff ...; ...] via zetas_vals / zetas_inv_vals. The proof is a pointwise equality check:                         
                                                                                                                                                                                                
  proof.                                                                                                                                                                                        
    rewrite zetas_vals /barray256_to_poly /array256_mont /=.                                                                                                                                    
    apply Array256.ext_eq => i /mem_range hi.                                                                                                                                                   
    rewrite initiE // /word_to_coeff.                                                                                                                                                           
    (* BArray1024.get32 (of_list32 [...]) i unfolds to W32.of_int v_i *)                                                                                                                        
    (* W32.to_sint (W32.of_int v_i) = v_i  (by bounds) *)                                                                                                                                       
    (* incoeff v_i = (array256_mont zetas).[i]  (by zetas_vals) *)                                                                                                                              
    by rewrite BArray1024.get32_of_list32 // W32.to_sintK_small /=;                                                                                                                             
       rewrite get_of_list //=.                                                                                                                                                                 
  qed.                                                                                                                                                                                          
                                                                                                                                                                                                
  The key lemma needed is W32.to_sintK_small (which holds because all twiddle values are in [-32768, 32767] ⊂ W32.sint range) and BArray1024.get32_of_list32 (indexing into a concrete list).   
                                                                                                                                                                                                
  ---                                                                                                                                                                                           
  Phase 3 — __fqmul Correctness                                                                                                                                                                 
                                                                                                                                                                                                
  The Jasmin butterfly uses __fqmul(a, b) which computes Montgomery multiplication:                                                                                                             
                                                                                                                                                                                                
  __fqmul(a, b)  =  montgomery_reduce(to_sint(a) * to_sint(b))                                                                                                                                  
                 ≡  to_sint(a) * to_sint(b) * R⁻¹  (mod q)                                                                                                                                      
                                                                                                                                                                                                
  This is captured by SREDCp_corr from Montgomery.ec:163. The lemma to establish:                                                                                                               
                                                                                                                                                                                                
  lemma fqmul_corr (a b : W32.t) :                                                                                                                                                              
    let r = Hpoly_extract.M.__fqmul a b in   (* Jasmin extracted *)                                                                                                                             
    word_to_coeff r =                                                                                                                                                                           
      (word_to_coeff a) * (word_to_coeff b) * R  (* coeff multiplication, scaled by R *)                                                                                                        
                                                                                                                                                                                                
  This comes from SREDCp_corr instantiated with SignedReductions from Fq.ec:22, where R = 2^32, q = 64513, qinv = 940508161.                                                                    
                                                                                                                                                                                                
  ---                                                                                                                                                                                           
  Phase 4 — pRHL Equivalence: _poly_ntt ↔ NTT.ntt                                                                                                                                               
                                                                                                                                                                                                
  This is the core Hoare logic step. The goal is an equiv (probabilistic Relational Hoare Logic) statement:                                                                                     
                                                                                                                                                                                                
  lemma poly_ntt_equiv (rp : BArray1024.t) (p : coeff Array256.t) :                                                                                                                             
    equiv [                                                                                                                                                                                     
      Hpoly_extract.M._poly_ntt ~ NTT.ntt :                                                                                                                                                     
      (* Precondition: input arrays represent the same polynomial *)                                                                                                                            
      poly_repr rp{1} p{2}  /\                                                                                                                                                                  
      (array256_mont zetas)  (* zetas loaded correctly *)                                                                                                                                       
      ==>                                                                                                                                                                                       
      (* Postcondition: output arrays represent the same polynomial *)                                                                                                                          
      poly_repr res{1} res{2}                                                                                                                                                                   
    ].                                                                                                                                                                                          
                                                                                                                                                                                                
  Proof structure — nested loop synchronization:                                                                                                                                                
                                                                                                                                                                                                
  The Jasmin code and the EC spec both have the same 3-level nested loop structure:                                                                                                             
  - Outer: len from 128 down to 1 (halved each iteration)                                                                                                                                       
  - Middle: start from 0 to 255                                                                                                                                                                 
  - Inner: j from start to start + len - 1                                                                                                                                                      
                                                                                                                                                                                                
  The equiv proof proceeds by synchronizing the two programs step-by-step, maintaining a loop invariant that the Jasmin state and EC state represent the same array at each point.              
                                                                                                                                                                                                
  Outer loop invariant (forward NTT):                                                                                                                                                           
  I_outer(len, zetasctr, rp, r) :=                                                                                                                                                              
    0 < len <= 128  /\  len is a power of 2  /\                                                                                                                                                 
    zetasctr = 256 / len - 1  /\                                                                                                                                                                
    poly_repr rp r  /\                                                                                                                                                                          
    (* after all completed butterfly layers, both arrays agree *)                                                                                                                               
    ∀ i ∈ [0,255]. rp_coeff(rp, i) = r.[i]                                                                                                                                                      
                                                                                                                                                                                                
  Inner loop invariant (butterfly step):                                                                                                                                                        
  I_inner(j, start, len, rp, r) :=                                                                                                                                                              
    start <= j <= start + len  /\                                                                                                                                                               
    poly_repr rp r  /\                                                                                                                                                                          
    (* coefficients outside the current window are unchanged *)                                                                                                                                 
    ∀ i ∉ [start, start+len) ∪ [start+len, start+2*len).                                                                                                                                        
      rp_coeff(rp, i) = r.[i]                                                                                                                                                                   
                                                                                                                                                                                                
  Butterfly step correctness (the key per-iteration lemma):                                                                                                                                     
  (* For Jasmin: *)                                                                                                                                                                             
  t   = __fqmul(zeta, rp[j+len])     (* = zeta * rp[j+len] * R⁻¹ in Zq *)                                                                                                                       
  rp[j+len] = rp[j] - t                                                                                                                                                                         
  rp[j]     = rp[j] + t                                                                                                                                                                         
                                                                                                                                                                                                
  (* For spec: *)                                                                                                                                                                               
  t_spec   = zeta_ * r.[j + len]                                                                                                                                                                
  r[j+len] = r.[j] + (-t_spec)                                                                                                                                                                  
  r[j]     = r.[j] + t_spec                                                                                                                                                                     
                                                                                                                                                                                                
  These are equal when word_to_coeff(zeta) = zeta_ * R (Montgomery form), which is exactly what jzetas_poly_vals provides.                                                                      
                                                                                                                                                                                                
  ---                                                                                                                                                                                           
  Phase 5 — _poly_invntt ↔ NTT.invntt                                                                                                                                                           
                                                                                                                                                                                                
  Structurally identical to Phase 4, with the roles of len/zetasctr reversed and an additional final scaling loop:                                                                              
                                                                                                                                                                                                
  (* Jasmin: *)                                                                                                                                                                                 
  zeta_0 <- BArray1024.get32 zetasp 255   (* = jzetas_inv[255] *)                                                                                                                               
  j <- 0;                                                                                                                                                                                       
  while (j < 256) {                                                                                                                                                                             
    rp[j] = __fqmul(zeta_0, rp[j]);                                                                                                                                                             
    j += 1;                                                                                                                                                                                     
  }                                                                                                                                                                                             
                                                                                                                                                                                                
  (* Spec: *)                                                                                                                                                                                   
  j <- 0;                                                                                                                                                                                    
  while (j < 256) {
    r.[j] <- r.[j] * zetas_inv.[255];                                                                                                                                                           
    j <- j + 1;                                                                                                                                                                                 
  }                                                                                                                                                                                             
                                                                                                                                                                                                
  The connection is jzetas_inv_255_scaleE (NTT_Fq.ec:328):                                                                                                                                      
  lemma jzetas_inv_255_scaleE :                                                                                                                                                                 
    word_to_coeff (BArray1024.get32 jzetas_inv 255) = scale255 * R.                                                                                                                             
  Already proved. The __fqmul(zeta_0, coeff) call computes word_to_coeff(coeff) * scale255 * R * R⁻¹ = coeff * scale255 = coeff * inv(256) in Zq, matching the spec.                            
                                                                                                                                                                                                
  ---                                                                                                                                                                                           
  Phase 6 — Imperative Spec → Abstract Spec (Rq.ntt)                                                                                                                                            
                                                                                                                                                                                                
  Once NTT.ntt is proved correct via the loop invariants, we connect it to the abstract Rq.ntt operator (defined in Rq.ec:89):                                                                  
                                                                                                                                                                                                
  (* Rq.ec *)                                                                                                                                                                                   
  op ntt(p : poly) = Array256.init (fun i =>                                                                                                                                                    
    BAdd.bigi predT (fun j => p.[2*j] * ZqRing.exp zroot ((2*br(i/2)+1)*j)) 0 128 ...)                                                                                                          
                                                                                                                                                                                                
  This is a phoare (single-program Hoare) proof showing the imperative loop computes the correct DFT sum. The key mathematical fact used is the butterfly decomposition of the DFT: the         
  Cooley-Tukey identity relating the length-N DFT to two length-N/2 DFTs via twiddle factors.                                                                                                   
                                                                                                                                                                                                
  ---                                                                                                                                                                                           
  Summary: Full Dependency Graph                                                                                                                                                                
                                                                                                                                                                                                
  exp_zroot_256           ← field arithmetic (done)                                                                                                                                             
        ↓                                                                                                                                                                                       
  zetas_invE              ← concrete table computation (done)                                                                                                                                   
  zetas_inv_vals          ← Montgomery form (done)                                                                                                                                              
        ↓                                                                                                                                                                                       
  jzetas_inv_poly_vals    ← ADMITTED (twiddle bridge, inv)                                                                                                                                      
  jzetas_poly_vals        ← ADMITTED (twiddle bridge, fwd)                                                                                                                                      
        ↓                                                                                                                                                                                       
  fqmul_corr              ← Montgomery reduction correctness (via SREDCp_corr)                                                                                                                  
        ↓                                                                                                                                                                                       
  butterfly_fwd_corr      ← single forward butterfly step                                                                                                                                       
  butterfly_inv_corr      ← single inverse butterfly step (+ final scale)                                                                                                                       
        ↓                                                                                                                                                                                       
  ntt_spec_ll             ← ADMITTED (losslessness)                                                                                                                                             
  invntt_spec_ll          ← ADMITTED (losslessness)                                                                                                                                             
        ↓                                                                                                                                                                                       
  poly_ntt_equiv          ← equiv [M._poly_ntt ~ NTT.ntt : ...]                                                                                                                                 
  poly_invntt_equiv       ← equiv [M._poly_invntt ~ NTT.invntt : ...]                                                                                                                           
        ↓                                                                                                                                                                                       
  poly_ntt_jazz_equiv     ← trivial wrapper (calls _poly_ntt)                                                                                                                                   
        ↓                                                                                                                                                                                       
  ntt_correct             ← NTT.ntt implements Rq.ntt                                                                                                                                           
  invntt_correct          ← NTT.invntt implements Rq.invntt                                                                                                                                     
        ↓                                                                                                                                                                                       
  END-TO-END THEOREM:                                                                                                                                                                           
  poly_ntt_jazz_correct : M.poly_ntt_jazz computes Rq.ntt                                                                                                                                       
  poly_invntt_jazz_correct : M.poly_invntt_jazz computes Rq.invntt                                                                                                                              
                                                                                                                                                                                                
  ---                                                                                                                                                                                           
  The Two Remaining Critical admits                                                                                                                                                             
                                                                                                                                                                                                
  ┌──────────────────────┬───────────────┬─────────────────────────────────────────────────────────────────────────────────────────────────────────────┐                                        
  │        Lemma         │   File:Line   │                                                How to prove                                                 │                                        
  ├──────────────────────┼───────────────┼─────────────────────────────────────────────────────────────────────────────────────────────────────────────┤                                        
  │ jzetas_poly_vals     │ NTT_Fq.ec:439 │ Reduce both sides to of_list via zetas_vals + BArray1024.get32_of_list32 + W32.to_sintK_small, then by norm │                                     
  ├──────────────────────┼───────────────┼─────────────────────────────────────────────────────────────────────────────────────────────────────────────┤                                        
  │ jzetas_inv_poly_vals │ NTT_Fq.ec:295 │ Same strategy using zetas_inv_vals                                                                          │                                        
  └──────────────────────┴───────────────┴─────────────────────────────────────────────────────────────────────────────────────────────────────────────┘                                        
                                                                                                                                                                                                
  Both are essentially concrete numeric equality checks — the values are all in range, so W32.to_sint (W32.of_int v) = v holds, and the Montgomery-scaled concrete values already match between 
  jzetas_inv and zetas_inv_vals.         