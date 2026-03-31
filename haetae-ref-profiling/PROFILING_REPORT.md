# HAETAE Reference Implementation — Professional Profiling Report

| Item | Value |
|------|-------|
| **Date** | 2026-03-30 |
| **CPU** | AMD Ryzen 7 5800X3D (Zen 3, 3D V-Cache, 8C/16T) |
| **Kernel** | Linux 5.15.0-164-generic |
| **perf** | perf version 5.15.193 |
| **valgrind** | valgrind-3.18.1 |
| **Compiler** | GCC 11.4.0 |
| **Build flags** | `-O2 -g` |
| **Core pinned** | CPU 2 (`taskset -c 2`) |
| **perf_event_paranoid** | -1 (full hardware counter access) |

---

## 1. Binary Sizes

```
build/bin/haetae-mode2-benchmark   136K
build/bin/haetae-mode2-main         88K
build/bin/haetae-mode3-benchmark   136K
build/bin/haetae-mode3-main         88K
build/bin/haetae-mode5-benchmark   136K
build/bin/haetae-mode5-main         88K
build/lib/libhaetae-mode2.so       272K
build/lib/libhaetae-mode3.so       272K
build/lib/libhaetae-mode5.so       272K
```

---

## 2. Native Cycle-Count Benchmarks (RDTSC, 1 000 iterations, core pinned)

### 2.1 Mode 2  (K=2, L=4, signature = 1 474 B)

| Operation | Median (cycles) | Average (cycles) | Wall time |
|-----------|----------------:|----------------:|----------:|
| `polymatkm_expand_matA` | 30,191 | 30,594 | — |
| `polyfixveclk_sample_hyperball` | 462,467 | 464,993 | — |
| `polyvecmk_expand_S` | 11,491 | 11,526 | — |
| `fft_bitrev + fft` | 9,689 | 9,684 | — |
| `ntt` | 7,581 | 7,574 | — |
| `invntt_tomont` | 8,737 | 8,759 | — |
| `polymatkm_pointwise_montgomery` | 12,035 | 12,325 | — |
| `polyfixvecl_round + polyfixveck_round` | 9,689 | 9,729 | — |
| `polyveck_poly_fromcrt` | 883 | 883 | — |
| `polyveck_highbits_hint` | 3,399 | 3,412 | — |
| **`crypto_sign_keypair`** | **985,217** | **1,442,651** | **0.424 ms** |
| **`crypto_sign_signature`** | **2,682,599** | **3,953,473** | **1.162 ms** |
| **`crypto_sign_verify`** | **183,089** | **183,523** | **0.054 ms** |

### 2.2 Mode 3  (K=3, L=6, signature = 2 349 B)

| Operation | Median (cycles) | Average (cycles) | Wall time |
|-----------|----------------:|----------------:|----------:|
| `polymatkm_expand_matA` | 76,567 | 76,638 | — |
| `polyfixveclk_sample_hyperball` | 786,011 | 789,422 | — |
| `polyvecmk_expand_S` | 18,325 | 18,364 | — |
| `fft_bitrev + fft` | 9,859 | 9,906 | — |
| `ntt` | 6,799 | 6,844 | — |
| `invntt_tomont` | 7,819 | 8,477 | — |
| `polymatkm_pointwise_montgomery` | 29,375 | 29,546 | — |
| `polyfixvecl_round + polyfixveck_round` | 12,783 | 12,884 | — |
| `polyveck_poly_fromcrt` | 1,291 | 1,280 | — |
| `polyveck_highbits_hint` | 4,827 | 4,835 | — |
| **`crypto_sign_keypair`** | **1,539,587** | **2,158,956** | **0.634 ms** |
| **`crypto_sign_signature`** | **4,269,549** | **5,184,190** | **1.523 ms** |
| **`crypto_sign_verify`** | **296,479** | **297,495** | **0.087 ms** |

### 2.3 Mode 5  (K=4, L=7, signature = 2 948 B)

| Operation | Median (cycles) | Average (cycles) | Wall time |
|-----------|----------------:|----------------:|----------:|
| `polymatkm_expand_matA` | 122,535 | 123,648 | — |
| `polyfixveclk_sample_hyperball` | 966,109 | 991,205 | — |
| `polyvecmk_expand_S` | 22,983 | 23,024 | — |
| `fft_bitrev + fft` | 9,621 | 9,610 | — |
| `ntt` | 6,833 | 6,853 | — |
| `invntt_tomont` | 8,397 | 8,399 | — |
| `polymatkm_pointwise_montgomery` | 47,293 | 47,459 | — |
| `polyfixvecl_round + polyfixveck_round` | 17,849 | 17,874 | — |
| `polyveck_poly_fromcrt` | 1,699 | 1,704 | — |
| `polyveck_highbits_hint` | 5,677 | 5,674 | — |
| **`crypto_sign_keypair`** | **1,199,791** | **1,593,702** | **0.468 ms** |
| **`crypto_sign_signature`** | **5,326,881** | **7,873,974** | **2.315 ms** |
| **`crypto_sign_verify`** | **363,187** | **363,676** | **0.107 ms** |

### 2.4 Cross-Mode Comparison

| Operation | Mode 2 | Mode 3 | Mode 5 | M3/M2 | M5/M2 |
|-----------|-------:|-------:|-------:|------:|------:|
| Keypair (median cycles) | 985,217 | 1,539,587 | 1,199,791 | 1.56x | 1.22x |
| Sign (median cycles) | 2,682,599 | 4,269,549 | 5,326,881 | 1.59x | 1.99x |
| Verify (median cycles) | 183,089 | 296,479 | 363,187 | 1.62x | 1.98x |
| Hyperball sample | 462,467 | 786,011 | 966,109 | 1.70x | 2.09x |
| Matrix expand | 30,191 | 76,567 | 122,535 | 2.54x | 4.06x |

> Sign median vs average divergence (e.g. mode2: 2.68M vs 3.95M; mode5: 5.33M vs
> 7.87M) is inherent to rejection-based lattice sampling — the algorithm retries
> until the sampled vector satisfies a norm bound, producing a heavy-tailed
> distribution.

---

## 3. Hardware Performance Counters (`perf stat`, 5 repetitions)

### 3.1 Core Events

| Metric | Mode 2 | Mode 3 | Mode 5 |
|--------|-------:|-------:|-------:|
| Total cycles | 7,937,731,329 | 11,572,220,584 | 14,697,727,452 |
| Total instructions | 31,914,563,128 | 43,393,222,750 | 56,864,096,237 |
| **IPC** | **4.07** | **3.82** | **3.96** |
| Branch instructions | 2,641,622,317 | 3,668,980,467 | 4,435,983,102 |
| Branch misses | 5,564,748 | 19,352,242 | 26,747,756 |
| **Branch miss rate** | **0.21%** | **0.53%** | **0.62%** |
| Wall time (avg 5 runs) | 1.81 s | 2.64 s | 3.33 s |

> IPC of 3.8-4.1 on a 4-wide Zen 3 indicates near-peak pipeline utilization.
> Branch miss rates are all under 1% -- the branch predictor handles the
> rejection-sampling loops very well.

### 3.2 Cache Events

| Metric | Mode 2 | Mode 3 | Mode 5 |
|--------|-------:|-------:|-------:|
| L1-dcache loads | 6,185,365,748 | 8,829,990,454 | 11,001,078,298 |
| L1-dcache misses | 11,526,654 | 20,842,094 | 27,672,781 |
| **L1-dcache miss rate** | **0.19%** | **0.23%** | **0.25%** |
| LLC-loads | not supported by hw PMU | — | — |

> L1 miss rate below 0.25% across all modes -- excellent cache utilization.
> The AMD Ryzen 5800X3D's 96 MB 3D V-Cache absorbs all working sets.
> LLC hardware counters are not exposed via PMU on this platform/kernel.

### 3.3 TLB Events

| Metric | Mode 2 | Mode 3 | Mode 5 |
|--------|-------:|-------:|-------:|
| dTLB loads | 188,926 | 56,813 | 434,054 |
| dTLB load misses | 8,017 | 3,330 | 23,027 |
| dTLB miss rate | 5.92% | 2.84% | 11.47% |
| iTLB loads | 5,057 | 4,014 | 17,232 |
| iTLB load misses | 22,800 | 12,008 | 27,909 |

> Absolute TLB miss counts are tiny (thousands over the full benchmark run).
> TLB pressure is negligible. High relative variance (+-15%) is measurement noise
> at these small absolute values.

---

## 4. `perf record --call-graph dwarf` -- Hotspot Analysis

### 4.1 Mode 2

| Symbol | % Cycles | Notes |
|--------|--------:|-------|
| `polyfixveclk_sample_hyperball` | **54.9%** | Dominant signing cost |
| -- `sample_gauss_N` | 50.9% | Main loop inside hyperball |
| -- -- `sample_gauss_sigma76` | 25.9% | Gaussian rejection core |
| -- -- -- `approx_exp` / `smulh48` (inlined) | 10.9% | Exp approximation |
| -- -- -- `sample_gauss16` (inlined) | 8.7% | Discrete Gaussian draw |
| -- -- `KeccakF1600_StatePermute` via SHAKE256 | 24.7% | Entropy generation |
| `keypair_internal` | **22.6%** | Full keypair path |
| -- `polyvecmk_sk_singular_value` | 10.4% | Singular value check |
| -- -- `fft` / `_complex_mul` / `_mulrnd16` | 7.2% | Spectral norm computation |

### 4.2 Mode 3

| Symbol | % Cycles |
|--------|--------:|
| `polyfixveclk_sample_hyperball` | **54.7%** |
| -- `sample_gauss_sigma76` | 29.8% |
| -- -- `sample_gauss16` | 12.9% |
| -- -- `approx_exp` / `smulh48` | 9.9% |
| -- `KeccakF1600_StatePermute` | 18.2% |
| `keypair_internal` | **24.7%** |
| -- `fft` / NTT operations | 11.0% |

### 4.3 Mode 5

| Symbol | % Cycles |
|--------|--------:|
| `polyfixveclk_sample_hyperball` | **61.6%** |
| -- `sample_gauss_sigma76` | 33.4% |
| -- -- `sample_gauss16` | 15.1% |
| -- -- `approx_exp` / `smulh48` | 10.6% |
| -- `KeccakF1600_StatePermute` | 20.6% |
| `signature_internal` (NTT/invNTT/pointwise) | **18.6%** |
| -- `invntt_tomont` | 3.3% |
| -- `polymatkl_pointwise_montgomery` | 2.7% |

---

## 5. Valgrind Callgrind -- Instruction-Level Profile (100 iterations)

### 5.1 Global Totals

| Metric | Mode 2 | Mode 3 | Mode 5 |
|--------|-------:|-------:|-------:|
| **Instructions retired (Ir)** | **2,788,634,992** | **3,862,406,070** | **4,628,444,453** |
| Data reads (Dr) | 427,644,892 | 600,609,774 | 703,265,365 |
| Data writes (Dw) | 240,265,942 | 345,951,768 | 396,035,462 |
| D1 miss rate (rd+wr) | 0.1% | 0.2% | 0.2% |
| LLd miss rate | **0.0%** | **0.0%** | **0.0%** |
| Branch conditionals (Bc) | 153,189,468 | 208,793,123 | 250,090,841 |
| Branch mispredictions (Bcm) | 4,976,345 | 6,695,312 | 8,308,112 |
| Branch miss rate (simulated) | 3.2% | 3.2% | 3.3% |
| Indirect branches (Bi) | 25,388,502 | 40,941,857 | 35,051,164 |

> Callgrind branch miss rates are simulated (not hardware); the perf stat
> hardware rates (0.2-0.6%) are more accurate.

### 5.2 Top Functions by Instructions Retired (Ir)

#### Mode 2

| Rank | Function | File | Ir % | D1mr % |
|------|----------|------|------:|-------:|
| 1 | `KeccakF1600_StatePermute` | fips202.c | **30.1%** | 2.3% |
| 2 | `sample_gauss_sigma76` | sampler.c | **19.7%** | 1.1% |
| 3 | `montgomery_reduce` | reduce.c | **8.2%** | 0.0% |
| 4 | `fft` | fft.c | **6.3%** | 0.0% |
| 5 | `invntt_tomont` | ntt.c | **5.1%** | 0.0% |
| 6 | `shake256_squeezeblocks` | fips202.c | **5.0%** | 0.0% |
| 7 | `ntt` | ntt.c | **4.1%** | 5.5% |
| 8 | `fixpoint_mul_rnd13` | fixpoint.c | **1.1%** | 0.0% |
| 9 | `poly_pointwise_montgomery` | poly.c | **1.0%** | **50.0%** (*) |
| 10 | `fixpoint_square` | fixpoint.c | **1.0%** | 0.0% |

#### Mode 3

| Rank | Function | Ir % | D1mr % |
|------|----------|------:|-------:|
| 1 | `KeccakF1600_StatePermute` | **26.9%** | 1.0% |
| 2 | `sample_gauss_sigma76` | **16.0%** | 0.2% |
| 3 | `fft` | **9.9%** | 0.0% |
| 4 | `montgomery_reduce` | **9.7%** | 0.0% |
| 5 | `invntt_tomont` | **5.2%** | 0.0% |
| 6 | `ntt` | **4.7%** | 1.6% |
| 7 | `shake256_squeezeblocks` | **4.2%** | 0.0% |
| 8 | `poly_pointwise_montgomery` | **1.7%** | **51.8%** (*) |
| 9 | `rej_eta` | **1.6%** | 0.0% |
| 10 | `poly_add` | **1.3%** | 10.1% |

#### Mode 5

| Rank | Function | Ir % | D1mr % |
|------|----------|------:|-------:|
| 1 | `KeccakF1600_StatePermute` | **31.6%** | 0.9% |
| 2 | `sample_gauss_sigma76` | **19.3%** | 0.3% |
| 3 | `fft` | **9.2%** | 0.0% |
| 4 | `montgomery_reduce` | **6.4%** | 0.0% |
| 5 | `shake256_squeezeblocks` | **5.0%** | 0.0% |
| 6 | `invntt_tomont` | **4.0%** | 1.7% |
| 7 | `ntt` | **2.5%** | 1.7% |
| 8 | `rej_eta` | **1.4%** | 0.0% |
| 9 | `poly_pointwise_montgomery` | **1.2%** | **46.4%** (*) |
| 10 | `fixpoint_mul_rnd13` | **1.1%** | 0.0% |

> (*) `poly_pointwise_montgomery` shows ~50% simulated D1 miss rate because it
> accesses large NTT-domain arrays (poly = 256 x int32 = 1 KB) in strided order.
> On real hardware the 3D V-Cache absorbs this; measured L1 miss rate remains <0.25%.

---

## 6. Key Findings

### F1 -- Gaussian hyperball sampling dominates signing (55-62%)

`polyfixveclk_sample_hyperball` is the dominant bottleneck, growing from
54.9% (mode 2) to 61.6% (mode 5). Within it:

- Gaussian arithmetic (`sample_gauss_sigma76`, `approx_exp`, `smulh48`,
  `fixpoint_square`): fixed-point rejection sampling. Highly pipelined (IPC 4.0+)
  but very instruction-intensive.
- SHAKE256 entropy (`KeccakF1600_StatePermute`): provides the uniform randomness
  for sampling -- the single most instruction-heavy function at 27-32% of all Ir.

### F2 -- KeccakF1600 is the #1 instruction consumer (27-32%)

Called from both the sampler and signing/keypair hash paths. The high rejection
rate means many fresh SHAKE256 bytes are consumed per accepted sample.

### F3 -- IPC 3.8-4.1 = near-optimal scalar pipeline utilization

The Zen 3 core is 4-wide issue. Achieving IPC 3.82-4.07 means scalar execution
units are nearly saturated. SIMD vectorization is the primary remaining axis.

### F4 -- Excellent cache behavior; 3D V-Cache absorbs all working sets

L1-dcache miss rate <= 0.25% across all modes. LLd miss rate (callgrind) = 0.0%.
The 5800X3D's 96 MB 3D V-Cache holds the entire working set on-die.
Results on a server CPU (e.g., Xeon, 32-64 MB LLC) would differ.

### F5 -- Sign average/median gap reflects rejection sampling tail

| Mode | Median sign | Average sign | Avg/Median |
|------|------------:|-------------:|:----------:|
| 2 | 2,682,599 | 3,953,473 | 1.47x |
| 3 | 4,269,549 | 5,184,190 | 1.21x |
| 5 | 5,326,881 | 7,873,974 | 1.48x |

The tighter mode-3 ratio suggests its acceptance probability is more favorable.

### F6 -- poly_pointwise_montgomery has latent cache sensitivity

Simulated D1 miss rate ~50% due to strided NTT-domain array accesses. Masked by
3D V-Cache here, but a risk on cache-limited deployment platforms.

---

## 7. Optimization Recommendations

| Priority | Target | Technique | Expected Gain |
|----------|--------|-----------|---------------|
| HIGH | `KeccakF1600_StatePermute` | AVX2/AVX-512 Keccak (XKCP) | 3-5x Keccak throughput |
| HIGH | `sample_gauss_sigma76` + `approx_exp` | SIMD batch Gaussian; vectorized exp approx | 2-4x sampler throughput |
| MEDIUM | NTT / `invntt_tomont` | AVX2 NTT (Barrett/Montgomery SIMD, as in Kyber/Dilithium) | 2-3x NTT throughput |
| MEDIUM | `fft` / `_complex_mul` | AVX2 complex multiply with FMA | 2x FFT throughput |
| LOW | `montgomery_reduce` | Already inline-friendly; batch via SIMD in callers | 10-20% |
| LOW | `poly_pointwise_montgomery` | AVX2 batch pointwise + prefetch for cache-limited targets | 1.5x |

> `benchmark/speed.c` already contains JAZZ assembly stubs (`poly_ntt_jazz`,
> `poly_invntt_jazz`, `poly_basemul_jazz`). Enabling them is the most direct
> NTT optimization path.

---

## 8. Interactive Analysis

```bash
# Live perf TUI (call-graph browser)
perf report --input=profiling_results/perf_record/mode2.perf.data
perf report --input=profiling_results/perf_record/mode3.perf.data
perf report --input=profiling_results/perf_record/mode5.perf.data

# Annotated assembly for hottest functions
perf annotate --input=profiling_results/perf_record/mode2.perf.data \
    --symbol=cryptolab_haetae_mode2_polyfixveclk_sample_hyperball
perf annotate --input=profiling_results/perf_record/mode2.perf.data \
    --symbol=KeccakF1600_StatePermute

# Instruction-level GUI (kcachegrind)
kcachegrind profiling_results/callgrind/callgrind.out.mode2
kcachegrind profiling_results/callgrind/callgrind.out.mode3
kcachegrind profiling_results/callgrind/callgrind.out.mode5
```

---

## 9. Artifact Index

| Path | Tool | Content |
|------|------|---------|
| `profiling_results/benchmarks/mode*_benchmark.txt` | native cpucycles | Median/average cycles, 1 000 iters |
| `profiling_results/perf_stat/mode*_core.txt` | perf stat | Cycles/instructions/IPC/branches |
| `profiling_results/perf_stat/mode*_cache.txt` | perf stat | L1-dcache loads/misses |
| `profiling_results/perf_stat/mode*_tlb.txt` | perf stat | dTLB/iTLB loads/misses |
| `profiling_results/perf_record/mode*.perf.data` | perf record | Raw sampling data (DWARF call graph) |
| `profiling_results/perf_record/mode*_flat.txt` | perf report | Flat profile (% self time per symbol) |
| `profiling_results/perf_record/mode*_callgraph.txt` | perf report | Call-graph text |
| `profiling_results/callgrind/callgrind.out.mode*` | valgrind callgrind | Instruction profile (open with kcachegrind) |
| `profiling_results/callgrind/mode*_annotate.txt` | callgrind_annotate | Per-function Ir/Dr/Dw/branch table |

---
*Generated by `profile.sh` -- HAETAE Reference Profiling Pipeline*
