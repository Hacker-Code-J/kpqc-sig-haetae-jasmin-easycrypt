require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import GaussianIidBufferSpec GaussianIidBufferPath GaussianIidVisible
  GaussianIidKernel GaussianByteCarryDistribution GaussianUniformBytes
  GaussianBlockSampling GaussianRetryInputs.

lemma gis_count_bounds values squares count pending requested dummy offset :
  0 <= requested <= 512 =>
  0 <= W64.to_uint (BArray8.get64
    (gib_consume values squares count pending requested dummy offset).`3 0) <= requested.
proof.
  move=> hn; rewrite (gib_consume_count values squares count pending requested dummy offset hn).
  have h := size_ge0 (gib_accepted pending); smt().
qed.

lemma gis_refill values squares count tail block n accepted offset signoff :
  gib_bounds n offset signoff => 0 <= accepted < n =>
  size tail < 26 => size block = 136 =>
  let pending = tail ++ block in
  let result = gib_consume values squares count pending (n-accepted) (n=257) (offset+accepted) in
  let q = W64.to_uint (BArray8.get64 result.`3 0) in
  0 <= accepted+q <= n /\
  size pending <= 6632 /\
  0 <= size (gib_remainder pending) < 26 /\
  gib_visible result.`1 offset (accepted+q) =
    gik_scan (gib_visible values offset accepted)
      (gbc_chunks (gbc_refill_count (size tail)) pending) /\
  gib_remainder pending = drop (26*gbc_refill_count (size tail)) pending.
proof.
  move=> hbounds ha ht hb /=; rewrite /gib_bounds in hbounds.
  have [hn [ho [hcap _]]] := hbounds.
  pose pending := tail ++ block.
  pose result := gib_consume values squares count pending (n-accepted) (n=257) (offset+accepted).
  pose q := W64.to_uint (BArray8.get64 result.`3 0).
  have hlen : size pending = size tail+136 by rewrite /pending size_cat hb.
  have hbound : size pending <= 6632 by smt().
  have hbytes : size pending <= 8192 by smt().
  have hreq : 0 <= n-accepted <= 512 by smt().
  have hq : 0 <= q <= n-accepted by
    exact (gis_count_bounds values squares count pending (n-accepted) (n=257) (offset+accepted) hreq).
  have htotal : 0 <= accepted+q <= n by smt().
  have [_ hrem] := gib_remainder_size pending.
  have hchunks : size pending %/ 26 = gbc_refill_count (size tail) by
    rewrite hlen /gbc_refill_count.
  have hvisible : gib_visible result.`1 offset (accepted+q) =
      gik_scan (gib_visible values offset accepted)
        (gbc_chunks (gbc_refill_count (size tail)) pending).
  + rewrite /gik_scan /gik_step -hchunks.
    exact (giv_consume_fold values squares count pending n accepted offset hn ha ho hcap hbytes).
  have hremainder : gib_remainder pending =
      drop (26*gbc_refill_count (size tail)) pending by rewrite /gib_remainder hchunks.
  smt().
qed.

lemma gis_initial values squares count bytes n offset signoff :
  gib_bounds n offset signoff => size bytes = 6664 =>
  let pending = drop 32 bytes in
  let result = gib_consume values squares count pending n (n=257) offset in
  let q = W64.to_uint (BArray8.get64 result.`3 0) in
  0 <= q <= n /\
  size pending = 6632 /\
  0 <= size (gib_remainder pending) < 26 /\
  gib_visible result.`1 offset q = gik_scan [] (gbc_chunks 255 pending) /\
  gib_remainder pending = drop 6630 pending.
proof.
  move=> hbounds hb /=; rewrite /gib_bounds in hbounds.
  have [hn [ho [hcap _]]] := hbounds.
  pose pending := drop 32 bytes.
  pose result := gib_consume values squares count pending n (n=257) offset.
  pose q := W64.to_uint (BArray8.get64 result.`3 0).
  have hlen : size pending = 6632 by rewrite /pending size_drop 1:// hb.
  have hbytes : size pending <= 8192 by smt().
  have hreq : 0 <= n <= 512 by smt().
  have hq : 0 <= q <= n by
    exact (gis_count_bounds values squares count pending n (n=257) offset hreq).
  have [_ hrem] := gib_remainder_size pending.
  have hchunks : size pending %/ 26 = 255 by rewrite hlen.
  have hvisible : gib_visible result.`1 offset q = gik_scan [] (gbc_chunks 255 pending).
  + rewrite /gik_scan /gik_step -hchunks.
    have h := giv_consume_fold values squares count pending n 0 offset hn _ ho hcap hbytes;
      first smt().
    by move: h; rewrite /= giv_empty.
  have hremainder : gib_remainder pending = drop 6630 pending by
    rewrite /gib_remainder hlen.
  smt().
qed.
