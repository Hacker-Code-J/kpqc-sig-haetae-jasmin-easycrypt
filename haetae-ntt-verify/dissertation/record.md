  File Structure                                                                                                                                                      
                                                            
  dissertation/
  ├── main.tex                        # Master document + preamble
  ├── Makefile                        # Build: make / make clean / make distclean                                                                                     
  ├── bibliography/
  │   └── refs.bib                    # 20+ references (Shor, Montgomery, EasyCrypt,                                                                                  
  │                                   #   Jasmin, HAETAE, ML-KEM, Dilithium, FALCON…)                                                                                 
  ├── chapters/                                                                                                                                                       
  │   ├── titlepage.tex                                                                                                                                               
  │   ├── abstract.tex                                                                                                                                                
  │   ├── acknowledgements.tex                                                                                                                                        
  │   ├── ch01_introduction.tex       # Motivation, problem statement, contributions
  │   ├── ch02_background.tex         # Lattices, NTT, Montgomery, EasyCrypt, Jasmin,                                                                                 
  │   │                               #   related work                                                                                                                
  │   ├── ch03_haetae_ntt.tex         # HAETAE parameters, reference C impl, HAETAE vs MLKEM                                                                          
  │   ├── ch04_formal_framework.tex   # 4-layer arch (TikZ figures), proof methodology                                                                                
  │   ├── ch05_field_ring.tex         # Fq.ec, GFq.ec, Rq.ec, array infrastructure                                                                                    
  │   ├── ch06_montgomery.tex         # Signed REDC proof, bound tracking through stages                                                                              
  │   ├── ch07_ntt_spec.tex           # NTT_Fq.ec: loop invariants, termination, twiddle sync                                                                         
  │   ├── ch08_algebra.tex            # NTTFullAlgebra.ec: primitive root, bit-reversal,                                                                              
  │   │                               #   butterfly stage decomposition, MLKEM comparison                                                                             
  │   ├── ch09_jasmin_impl.tex        # Jasmin source walkthrough (reduce, poly, hpoly)                                                                               
  │   ├── ch10_refinement.tex         # RefJasminNTT.ec: pRHL equivalence proofs                                                                                      
  │   ├── ch11_end_to_end.tex         # NTTEndToEnd.ec: main theorems, proof metrics table                                                                            
  │   └── ch12_conclusion.tex         # Contributions, limitations, future work                                                                                       
  └── figures/                                                                                                                                                        
      └── README.txt                                                                                                                                                  
                                                                                                                                                                      
  PhD-level content highlights
                                                                                                                                                                      
  - Full mathematical treatment of the negacyclic NTT evaluation formula with bit-reversal exponent $\brev_8(k)$                                                      
  - Formal statements of all 5 main theorems and 15+ lemmas with proof sketches matching the EasyCrypt source
  - The critical HAETAE vs. MLKEM structural difference (full 256-point vs. incomplete 128-point transform) is identified and motivated as a key technical            
  contribution                                                                                                                                                        
  - Verification metrics table covering all 9 EasyCrypt source files (~4,200 lines, 203 lemmas)      