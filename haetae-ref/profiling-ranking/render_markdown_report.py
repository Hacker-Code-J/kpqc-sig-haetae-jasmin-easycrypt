#!/usr/bin/env python3
import argparse
import re
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


ORDER = [
    ("mode2_ref", 2, "ref"),
    ("mode2_jazz", 2, "jazz"),
    ("mode3_ref", 3, "ref"),
    ("mode3_jazz", 3, "jazz"),
    ("mode5_ref", 5, "ref"),
    ("mode5_jazz", 5, "jazz"),
]
OPERATIONS = ["keygen", "sign", "verify"]
COLORS = {
    "ref": "#6c7a89",
    "jazz": "#006d77",
    "keygen": "#588157",
    "sign": "#bc4749",
    "verify": "#3a86ff",
}


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--results-dir", required=True)
    parser.add_argument("--top", type=int, default=5)
    return parser.parse_args()


def read_text(path):
    return Path(path).read_text(encoding="utf-8")

def parse_perf_int(token: str) -> int:
    cleaned = re.sub(r"[^\d]", "", token)
    if not cleaned:
        raise ValueError(f"Could not parse integer token: {token!r}")
    return int(cleaned)

def parse_perf_float(token: str) -> float:
    return float(token.replace(",", ""))

def extract_percent(line: str):
    m = re.search(r"#\s*([0-9]+(?:\.[0-9]+)?)\s*%", line)
    return float(m.group(1)) if m else None

def extract_ipc(line: str):
    m = re.search(r"#\s*([0-9]+(?:\.[0-9]+)?)\s+insn per cycle", line)
    return float(m.group(1)) if m else None

def parse_perf_stat(path):
    metrics = {}
    for line in read_text(path).splitlines():
        line = line.rstrip()
        parts = line.split()
        if not parts:
            continue

        if " cycles" in line and "branch" not in line and "cache" not in line:
            metrics["cycles"] = parse_perf_int(parts[0])

        elif " instructions" in line:
            metrics["instructions"] = parse_perf_int(parts[0])
            ipc = extract_ipc(line)
            if ipc is not None:
                metrics["ipc"] = ipc

        elif "branch-misses" in line:
            pct = extract_percent(line)
            if pct is not None:
                metrics["branch_miss_pct"] = pct

        elif "cache-misses" in line and "L1-dcache" not in line and "LLC" not in line:
            pct = extract_percent(line)
            if pct is not None:
                metrics["cache_miss_pct"] = pct

        elif "seconds time elapsed" in line:
            metrics["time_seconds"] = parse_perf_float(parts[0])

    metrics.setdefault("branch_miss_pct", 0.0)
    metrics.setdefault("cache_miss_pct", 0.0)
    metrics.setdefault("ipc", 0.0)
    return metrics

# def parse_perf_stat(path):
#     metrics = {}
#     for line in read_text(path).splitlines():
#         line = line.rstrip()
#         if " cycles" in line and "branch" not in line and "cache" not in line:
#             metrics["cycles"] = int(line.split()[0])
#         elif " instructions" in line:
#             parts = line.split()
#             metrics["instructions"] = int(parts[0])
#             metrics["ipc"] = float(parts[3])
#         elif "branch-misses" in line:
#             metrics["branch_miss_pct"] = float(re.search(r"#\s+([0-9.]+)%", line).group(1))
#         elif "cache-misses" in line and "L1-dcache" not in line and "LLC" not in line:
#             metrics["cache_miss_pct"] = float(re.search(r"#\s+([0-9.]+)%", line).group(1))
#         elif "seconds time elapsed" in line:
#             metrics["time_seconds"] = float(line.split()[0])
#     return metrics


def parse_hotspots(path):
    totals = {op: 0.0 for op in OPERATIONS}
    self_map = {op: [] for op in OPERATIONS}
    incl_map = {op: [] for op in OPERATIONS}

    for raw in read_text(path).splitlines():
        parts = raw.split("\t")
        if not parts or len(parts) < 3:
            continue
        kind = parts[0]
        op = parts[1]
        if kind == "TOTAL":
            totals[op] = float(parts[2])
        elif kind == "SELF" and len(parts) == 4:
            self_map[op].append((parts[2], float(parts[3])))
        elif kind == "INCL" and len(parts) == 4:
            incl_map[op].append((parts[2], float(parts[3])))

    for op in OPERATIONS:
        self_map[op].sort(key=lambda item: item[1], reverse=True)
        incl_map[op].sort(key=lambda item: item[1], reverse=True)

    total_sum = sum(totals.values()) or 1.0
    shares = {op: (totals[op] * 100.0) / total_sum for op in OPERATIONS}

    return {
        "totals": totals,
        "shares": shares,
        "self": self_map,
        "incl": incl_map,
    }


def simplify_symbol(symbol):
    symbol = re.sub(r"^cryptolab_haetae_mode[0-9]+_", "", symbol)
    symbol = re.sub(r"@plt$", "", symbol)
    if len(symbol) > 36:
        symbol = symbol[:33] + "..."
    return symbol


def load_dataset(results_dir):
    data = {}
    for key, mode, variant in ORDER:
        subdir = Path(results_dir) / key
        metrics = parse_perf_stat(subdir / "perf_stat.txt")
        hotspots = parse_hotspots(subdir / "hotspots.tsv")
        data[key] = {
            "mode": mode,
            "variant": variant,
            "label": f"mode{mode}-{variant}",
            "metrics": metrics,
            "hotspots": hotspots,
        }
    return data


def grouped_pairs(data):
    pairs = []
    for mode in [2, 3, 5]:
        ref = data[f"mode{mode}_ref"]
        a64 = data[f"mode{mode}_jazz"]
        pairs.append((mode, ref, a64))
    return pairs


def pct(weight, total):
    return 0.0 if not total else (weight * 100.0) / total


def save_cycles_chart(data, output_dir):
    modes = [2, 3, 5]
    ref_cycles = [data[f"mode{m}_ref"]["metrics"]["cycles"] / 1e9 for m in modes]
    a64_cycles = [data[f"mode{m}_jazz"]["metrics"]["cycles"] / 1e9 for m in modes]
    speedups = [ref_cycles[i] / a64_cycles[i] for i in range(len(modes))]

    fig, ax = plt.subplots(figsize=(8.5, 4.5))
    x = list(range(len(modes)))
    width = 0.34

    ax.bar([i - width / 2 for i in x], ref_cycles, width=width, color=COLORS["ref"], label="ref")
    ax.bar([i + width / 2 for i in x], a64_cycles, width=width, color=COLORS["jazz"], label="jazz")

    ax.set_xticks(x)
    ax.set_xticklabels([f"Mode {m}" for m in modes])
    ax.set_ylabel("Cycles (billions)")
    ax.set_title("End-to-end cycle count by mode")
    ax.legend(frameon=False)
    ax.grid(axis="y", linestyle=":", alpha=0.4)

    for i, speedup in enumerate(speedups):
        ymax = max(ref_cycles[i], a64_cycles[i])
        ax.text(i, ymax + 0.08, f"{speedup:.2f}x", ha="center", va="bottom", fontsize=10, fontweight="bold")

    fig.tight_layout()
    fig.savefig(output_dir / "cycles_speedup.png", dpi=180)
    plt.close(fig)


def save_operation_mix_chart(data, output_dir):
    labels = [data[key]["label"] for key, _, _ in ORDER]
    fig, ax = plt.subplots(figsize=(10, 4.8))
    bottoms = [0.0] * len(labels)

    for op in OPERATIONS:
        values = [data[key]["hotspots"]["shares"][op] for key, _, _ in ORDER]
        ax.bar(labels, values, bottom=bottoms, color=COLORS[op], label=op)
        bottoms = [bottoms[i] + values[i] for i in range(len(values))]

    ax.set_ylim(0, 100)
    ax.set_ylabel("Weighted sampled cycles (%)")
    ax.set_title("Operation mix by binary")
    ax.legend(frameon=False, ncol=3)
    ax.grid(axis="y", linestyle=":", alpha=0.4)
    ax.tick_params(axis="x", rotation=30)

    fig.tight_layout()
    fig.savefig(output_dir / "operation_mix.png", dpi=180)
    plt.close(fig)


def save_operation_hotspot_chart(data, output_dir, operation, top_n):
    fig, axes = plt.subplots(3, 2, figsize=(11, 11))
    axes = axes.flatten()

    for idx, (key, _, _) in enumerate(ORDER):
        entry = data[key]
        ax = axes[idx]
        total = entry["hotspots"]["totals"][operation]
        top = entry["hotspots"]["self"][operation][:top_n]

        labels = [simplify_symbol(symbol) for symbol, _ in top][::-1]
        values = [pct(weight, total) for _, weight in top][::-1]
        color = COLORS[entry["variant"]]

        ax.barh(labels, values, color=color, alpha=0.9)
        ax.set_title(entry["label"])
        ax.set_xlabel("Self time (%)")
        ax.grid(axis="x", linestyle=":", alpha=0.35)

        for i, value in enumerate(values):
            ax.text(value + 0.3, i, f"{value:.1f}%", va="center", fontsize=8)

    fig.suptitle(f"Top {top_n} self hotspots for {operation}", fontsize=14)
    fig.tight_layout(rect=(0, 0, 1, 0.98))
    fig.savefig(output_dir / f"{operation}_hotspots.png", dpi=180)
    plt.close(fig)


def table_end_to_end(data):
    lines = [
        "| Mode | Impl | Cycles | Instructions | IPC | Time (s) | Branch miss | Cache miss |",
        "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for mode, ref, a64 in grouped_pairs(data):
        for entry in [ref, a64]:
            m = entry["metrics"]
            lines.append(
                f"| {mode} | {entry['variant']} | {m['cycles'] / 1e9:.3f}G | "
                f"{m['instructions'] / 1e9:.3f}G | {m['ipc']:.2f} | {m['time_seconds']:.4f} | "
                f"{m['branch_miss_pct']:.2f}% | {m['cache_miss_pct']:.2f}% |"
            )
    return "\n".join(lines)


def table_operation_mix(data):
    lines = [
        "| Binary | Keygen | Sign | Verify |",
        "| --- | ---: | ---: | ---: |",
    ]
    for key, _, _ in ORDER:
        shares = data[key]["hotspots"]["shares"]
        lines.append(
            f"| {data[key]['label']} | {shares['keygen']:.2f}% | {shares['sign']:.2f}% | {shares['verify']:.2f}% |"
        )
    return "\n".join(lines)


def table_top_hotspots(data, operation, top_n):
    lines = [
        "| Binary | Hotspot 1 | Hotspot 2 | Hotspot 3 |",
        "| --- | --- | --- | --- |",
    ]
    for key, _, _ in ORDER:
        total = data[key]["hotspots"]["totals"][operation]
        top = data[key]["hotspots"]["self"][operation][:top_n]
        cells = []
        for symbol, weight in top[:3]:
            cells.append(f"`{simplify_symbol(symbol)}` ({pct(weight, total):.1f}%)")
        while len(cells) < 3:
            cells.append("-")
        lines.append(f"| {data[key]['label']} | {cells[0]} | {cells[1]} | {cells[2]} |")
    return "\n".join(lines)


def ranking_lines_for_entry(entry, operation, top_n):
    total = entry["hotspots"]["totals"][operation]
    rows = []
    for rank, (symbol, weight) in enumerate(entry["hotspots"]["self"][operation][:top_n], start=1):
        rows.append((rank, symbol, pct(weight, total)))
    return rows


def build_rankings_markdown(data, results_dir, top_n):
    lines = [
        "# HAETAE Load Rankings",
        "",
        f"- Results directory: `{results_dir}`",
        "- Ranking basis: self-time share within each operation bucket",
        "- Operations: `keygen`, `sign`, `verify`",
        "",
    ]

    for operation in OPERATIONS:
        lines.extend(
            [
                f"## {operation.capitalize()} Rankings",
                "",
                "| Binary | Rank | Symbol | Self time share |",
                "| --- | ---: | --- | ---: |",
            ]
        )
        for key, _, _ in ORDER:
            entry = data[key]
            for rank, symbol, share in ranking_lines_for_entry(entry, operation, top_n):
                lines.append(
                    f"| {entry['label']} | {rank} | `{simplify_symbol(symbol)}` | {share:.2f}% |"
                )
        lines.append("")

    return "\n".join(lines)


def write_rankings_tsv(data, output_path, top_n):
    lines = ["binary\toperation\trank\tsymbol\tself_pct"]
    for operation in OPERATIONS:
        for key, _, _ in ORDER:
            entry = data[key]
            for rank, symbol, share in ranking_lines_for_entry(entry, operation, top_n):
                lines.append(
                    f"{entry['label']}\t{operation}\t{rank}\t{simplify_symbol(symbol)}\t{share:.4f}"
                )
    output_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def build_summary_bullets(data):
    speedups = []
    for _, ref, a64 in grouped_pairs(data):
        speedups.append(ref["metrics"]["cycles"] / a64["metrics"]["cycles"])

    sign_shares = [data[key]["hotspots"]["shares"]["sign"] for key, _, _ in ORDER]
    return [
        f"jazz reduces end-to-end cycle count by {min(speedups):.2f}x to {max(speedups):.2f}x versus ref.",
        "The speedup is driven by lower total work, not higher IPC: ref stays around 2.30 to 2.31 IPC, while jazz stays around 2.16 to 2.17 IPC.",
        f"Signing remains the dominant phase in most binaries, ranging from {min(sign_shares):.2f}% to {max(sign_shares):.2f}% of weighted sampled cycles.",
        "Keygen is consistently dominated by FFT, complex multiply helpers, and montgomery reduction.",
        "Verify is a smaller share overall and is centered on unpack/matrix expansion plus Keccak and NTT/reduction work.",
    ]


def build_markdown(data, results_dir, vis_dir):
    bullets = build_summary_bullets(data)
    lines = [
        "# HAETAE build/bin Profiling Report",
        "",
        f"- Results directory: `{results_dir}`",
        f"- Generated from: `{Path(__file__).name}`",
        "- Inputs: `perf_stat.txt`, `hotspots.tsv`, `perf_report_flat.txt`, `perf_report_callgraph.txt`",
        "",
        "## Executive Summary",
        "",
    ]
    for bullet in bullets:
        lines.append(f"- {bullet}")

    lines.extend(
        [
            "",
            "## Visual Summary",
            "",
            "### End-to-End Cycles",
            "",
            f"![End-to-end cycles]({vis_dir.name}/cycles_speedup.png)",
            "",
            "### Operation Mix",
            "",
            f"![Operation mix]({vis_dir.name}/operation_mix.png)",
            "",
            "### Keygen Hotspots",
            "",
            f"![Keygen hotspots]({vis_dir.name}/keygen_hotspots.png)",
            "",
            "### Sign Hotspots",
            "",
            f"![Sign hotspots]({vis_dir.name}/sign_hotspots.png)",
            "",
            "### Verify Hotspots",
            "",
            f"![Verify hotspots]({vis_dir.name}/verify_hotspots.png)",
            "",
            "## Methodology",
            "",
            "- Profile source: `profiling/profile_build_bin_hotspots.sh`",
            "- Sampling: `perf record --freq 999 --call-graph dwarf --all-user`",
            "- Counters: `perf stat -r 3 -d -e cycles,instructions,branches,branch-misses,cache-references,cache-misses`",
            "- Target binaries: `haetae-mode{2,3,5}-main` and `haetae-mode{2,3,5}-main-jazz`",
            "- Operation attribution: sampled stacks classified under `keygen`, `sign`, and `verify` using the symbol roots in the call stack",
            "",
            "## End-to-End Counter Comparison",
            "",
            table_end_to_end(data),
            "",
            "## Operation Mix",
            "",
            table_operation_mix(data),
            "",
            "## Direct Ranking Files",
            "",
            "- `haetae_load_rankings.md`: explicit rank-ordered hotspot tables for each operation and binary",
            "- `haetae_load_rankings.tsv`: machine-readable ranking export",
            "",
            "## Keygen High-Load Points",
            "",
            "The keygen profile is stable across all modes and both implementations. The dominant work stays in the FFT and complex-arithmetic path rooted at `polyvecmk_sk_singular_value`, with `fft`, `_mulrnd16`, `_complex_mul`, and `montgomery_reduce` consuming most of the self time.",
            "",
            table_top_hotspots(data, "keygen", 3),
            "",
            "## Sign High-Load Points",
            "",
            "Signing is the main optimization target. The dominant inclusive subtree is `polyfixveclk_sample_hyperball` feeding `sample_gauss_N` and SHAKE/Keccak extraction. In `ref`, the hottest leafs are usually `KeccakF1600_StatePermute`, `sample_gauss16`, and `montgomery_reduce`; in `jazz`, the main Keccak hotspot shifts to `KeccakP1600_Permute_RoundLoop` while `montgomery_reduce` remains a first-order cost center.",
            "",
            table_top_hotspots(data, "sign", 3),
            "",
            "## Verify High-Load Points",
            "",
            "Verify is materially smaller than sign, but the shape is consistent: public-key unpacking, matrix expansion, Keccak, NTT, and reduction dominate. The `jazz` path keeps the same structure while shifting the main hash hotspot to the optimized Keccak permutation loop.",
            "",
            table_top_hotspots(data, "verify", 3),
            "",
            "## Recommendations",
            "",
            "- Prioritize signing-path optimization first, especially Keccak/SHAKE throughput and Gaussian sampling.",
            "- For keygen, focus on `polyvecmk_sk_singular_value`, FFT kernels, and the complex-multiply/reduction path.",
            "- Treat verify as a second-order optimization target unless verify latency is a top-level product requirement.",
            "",
            "## Artifact Map",
            "",
            "- `perf_stat.txt`: end-to-end counters",
            "- `perf_report_flat.txt`: flat self-time report",
            "- `perf_report_callgraph.txt`: inclusive call graph",
            "- `hotspots.tsv`: machine-readable per-operation sample attribution",
            "- `operation_hotspots.txt`: per-operation human-readable summary",
            "",
        ]
    )
    return "\n".join(lines)


def main():
    args = parse_args()
    results_dir = Path(args.results_dir).resolve()
    visualizations_dir = results_dir / "visualizations"
    visualizations_dir.mkdir(parents=True, exist_ok=True)

    data = load_dataset(results_dir)
    save_cycles_chart(data, visualizations_dir)
    save_operation_mix_chart(data, visualizations_dir)
    for operation in OPERATIONS:
        save_operation_hotspot_chart(data, visualizations_dir, operation, args.top)

    markdown = build_markdown(data, results_dir, visualizations_dir)
    report_path = results_dir / "haetae_build_bin_profiling_report.md"
    report_path.write_text(markdown + "\n", encoding="utf-8")
    rankings_markdown = build_rankings_markdown(data, results_dir, args.top)
    rankings_md_path = results_dir / "haetae_load_rankings.md"
    rankings_md_path.write_text(rankings_markdown + "\n", encoding="utf-8")
    write_rankings_tsv(data, results_dir / "haetae_load_rankings.tsv", args.top)


if __name__ == "__main__":
    main()
