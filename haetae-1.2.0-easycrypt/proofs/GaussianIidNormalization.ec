require import AllCore IntDiv List Distr DList Xreal StdOrder.
from Jasmin require import JModel_x86.
require import GaussianIidBufferSpec GaussianIidBufferPath GaussianIidInitial
  GaussianIidKernel GaussianIidVisible GaussianIidProgress GaussianUniformBytes
  GaussianByteCarryDistribution GaussianRetryCore.
import RealOrder.

(* Only the finite initial block draws are combined here. The refill loop
   and exact word consumer are unchanged from the functional controller. *)
module GaussianIidBufferUniform = {
  proc sample(rp : BArray32768.t, signsp : BArray512.t, sqsump : BArray16.t,
      n : int, sample_offset : int, sign_offset : int) : gib_result = {
    var count : BArray8.t;
    var bytes, pending : W8.t list;
    var accepted : int;
    count <- witness;
    pending <$ gbc_bytes 6664;
    signsp <- gib_signs signsp sign_offset pending;
    pending <- drop 32 pending;
    (rp, sqsump, count) <- gib_consume rp sqsump count pending n (n = 257) sample_offset;
    accepted <- W64.to_uint (BArray8.get64 count 0);
    while (accepted < n) {
      pending <- gib_remainder pending;
      bytes <$ gib_block;
      pending <- pending ++ bytes;
      (rp, sqsump, count) <- gib_consume rp sqsump count pending (n - accepted)
        (n = 257) (sample_offset + accepted);
      accepted <- accepted + W64.to_uint (BArray8.get64 count 0);
    }
    return (rp, signsp, sqsump);
  }
}.

lemma gid_functional_uniform :
  equiv [GaussianIidBufferFunctional.sample ~ GaussianIidBufferUniform.sample :
    ={rp,signsp,sqsump,n,sample_offset,sign_offset} ==> ={res}].
proof.
  proc.
  outline {1} [2 .. 4] ~ GaussianIidInitial.draw.
  outline {2} 2 ~ GaussianIidInitialUniform.draw.
  seq 2 2 : (={rp,signsp,sqsump,n,sample_offset,sign_offset,count,pending}).
  + call gib_initial_uniform_equiv; by auto.
  by sim.
qed.

op gid_target : int list distr = dlist (gr_output gik_pairs) 256.

lemma gid_functional_uniform_law initial initial_signs initial_squares n offset signoff
    (event : int list -> bool) &m :
  Pr[GaussianIidBufferFunctional.sample(initial,initial_signs,initial_squares,n,offset,signoff)
    @ &m : event (gib_magnitudes res offset)] =
  Pr[GaussianIidBufferUniform.sample(initial,initial_signs,initial_squares,n,offset,signoff)
    @ &m : event (gib_magnitudes res offset)].
proof. by byequiv gid_functional_uniform. qed.
