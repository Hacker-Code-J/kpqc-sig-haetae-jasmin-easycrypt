require import AllCore List Distr DList.
from Jasmin require import JModel_x86.
require import GaussianIidBufferSpec GaussianUniformBytes.

module GaussianIidInitial = {
  proc draw() : W8.t list = {
    var pending, bytes : W8.t list;
    var block : int;
    pending <- [];
    block <- 0;
    while (block < 49) {
      bytes <$ gib_block;
      pending <- pending ++ bytes;
      block <- block + 1;
    }
    return pending;
  }
}.

module GaussianIidInitialUniform = {
  proc draw() : W8.t list = {
    var pending : W8.t list;
    pending <$ gbc_bytes 6664;
    return pending;
  }
}.

clone DList.Program as GIBInitialList with
  type t <- W8.t list,
  op d <- gib_block.

lemma gib_initial_blocks_equiv :
  equiv [GaussianIidInitial.draw ~ GIBInitialList.LoopSnoc.sample :
    n{2}=49 ==> res{1}=flatten res{2}].
proof.
  proc; while (block{1}=i{2} /\ n{2}=49 /\ pending{1}=flatten l{2}).
  + wp; rnd; skip; auto => />.
    move=> &2 hblock bytes hb.
    by rewrite flatten_cat flatten_cons flatten_nil cats0.
  by auto.
qed.

lemma gib_initial_law (event : W8.t list -> bool) &m :
  Pr[GaussianIidInitial.draw() @ &m : event res] = mu (gbc_bytes 6664) event.
proof.
  have he : Pr[GaussianIidInitial.draw() @ &m : event res] =
    Pr[GIBInitialList.LoopSnoc.sample(49) @ &m : event (flatten res)] by
    byequiv gib_initial_blocks_equiv.
  have hs : Pr[GIBInitialList.Sample.sample(49) @ &m : event (flatten res)] =
    Pr[GIBInitialList.LoopSnoc.sample(49) @ &m : event (flatten res)] by
    byequiv GIBInitialList.Sample_LoopSnoc_eq.
  rewrite he -hs.
  have hd : mu (dlist gib_block 49) (fun blocks => event (flatten blocks)) =
    mu (gbc_bytes 6664) event.
  + rewrite -(dmapE _ flatten event) /gib_block dlist_dlist 1:// 1:// /= /gbc_bytes.
    trivial.
  rewrite -hd.
  byphoare (_ : n=49 ==> event (flatten res)) => //.
  proc; rnd; skip; auto.
qed.

lemma gib_initial_ll : islossless GaussianIidInitial.draw.
proof.
  bypr => &m _; rewrite (gib_initial_law (fun _ => true) &m).
  exact (gbc_bytes_ll 6664).
qed.

lemma gib_initial_uniform_law (event : W8.t list -> bool) &m :
  Pr[GaussianIidInitialUniform.draw() @ &m : event res] = mu (gbc_bytes 6664) event.
proof. by byphoare (_ : true ==> event res) => //; proc; rnd; skip; auto. qed.

lemma gib_initial_uniform_equiv :
  equiv [GaussianIidInitial.draw ~ GaussianIidInitialUniform.draw : true ==> ={res}].
proof.
  bypr (res{1}) (res{2}) => //= &1 &2 xs.
  by rewrite (gib_initial_law (pred1 xs) &1) (gib_initial_uniform_law (pred1 xs) &2).
qed.
