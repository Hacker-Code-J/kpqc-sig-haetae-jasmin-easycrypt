#!/usr/bin/env python3
"""Emit one-step EasyCrypt Keccak bit lemmas for the empty SHAKE256 KAT."""

from __future__ import annotations

import argparse


KECCAK_ROUND_CONSTANTS = [
    1,
    32898,
    9223372036854808714,
    9223372039002292224,
    32907,
    2147483649,
    9223372039002292353,
    9223372036854808585,
    138,
    136,
    2147516425,
    2147483658,
    2147516555,
    9223372036854775947,
    9223372036854808713,
    9223372036854808579,
    9223372036854808578,
    9223372036854775936,
    32778,
    9223372039002259466,
    9223372039002292353,
    9223372036854808704,
    2147483649,
    9223372039002292232,
]

KECCAK_RHO_OFFSETS = [
    0,
    1,
    62,
    28,
    27,
    36,
    44,
    6,
    55,
    20,
    3,
    10,
    43,
    25,
    39,
    41,
    45,
    15,
    21,
    8,
    18,
    2,
    61,
    56,
    14,
]

LANE_BITS = 64
STATE_LANES = 25
WORD_MASK = (1 << LANE_BITS) - 1


def lane_index(x: int, y: int) -> int:
    return (x % 5) + 5 * (y % 5)


def rotl64(word: int, offset: int) -> int:
    offset %= LANE_BITS
    if offset == 0:
        return word & WORD_MASK
    return ((word << offset) | (word >> (LANE_BITS - offset))) & WORD_MASK


def keccak_round(state: list[int], round_constant: int) -> list[int]:
    c = [
        state[lane_index(x, 0)]
        ^ state[lane_index(x, 1)]
        ^ state[lane_index(x, 2)]
        ^ state[lane_index(x, 3)]
        ^ state[lane_index(x, 4)]
        for x in range(5)
    ]
    d = [c[(x - 1) % 5] ^ rotl64(c[(x + 1) % 5], 1) for x in range(5)]

    theta = [0] * STATE_LANES
    for x in range(5):
        for y in range(5):
            theta[lane_index(x, y)] = state[lane_index(x, y)] ^ d[x]

    rho_pi = [0] * STATE_LANES
    for x in range(5):
        for y in range(5):
            src = lane_index(x, y)
            dst = lane_index(y, 2 * x + 3 * y)
            rho_pi[dst] = rotl64(theta[src], KECCAK_RHO_OFFSETS[src])

    chi = [0] * STATE_LANES
    for x in range(5):
        for y in range(5):
            chi[lane_index(x, y)] = (
                rho_pi[lane_index(x, y)]
                ^ ((~rho_pi[lane_index(x + 1, y)])
                   & rho_pi[lane_index(x + 2, y)]
                   & WORD_MASK)
            )

    chi[0] ^= round_constant
    return [word & WORD_MASK for word in chi]


def empty_shake256_round_states() -> list[list[int]]:
    state_bytes = [0] * 200
    state_bytes[0] ^= 0x1F
    state_bytes[135] ^= 0x80

    state = []
    for lane in range(STATE_LANES):
        word = 0
        for byte in range(8):
            word |= state_bytes[8 * lane + byte] << (8 * byte)
        state.append(word)

    states = [state]
    for round_constant in KECCAK_ROUND_CONSTANTS:
        states.append(keccak_round(states[-1], round_constant))
    return states


def bit_value(state: list[int], lane: int, bit: int) -> bool:
    return ((state[lane] >> bit) & 1) != 0


def bit_dependencies(lane: int, bit: int) -> list[tuple[int, int]]:
    x = lane % 5
    y = lane // 5
    dependencies: list[tuple[int, int]] = []

    for rho_pi_lane in [
        lane_index(x, y),
        lane_index(x + 1, y),
        lane_index(x + 2, y),
    ]:
        bx = rho_pi_lane % 5
        by = rho_pi_lane // 5
        sx = (bx + 3 * by) % 5
        sy = bx
        source_lane = lane_index(sx, sy)
        source_bit = (bit - KECCAK_RHO_OFFSETS[source_lane]) % LANE_BITS

        ordered = [(source_lane, source_bit)]
        ordered.extend((lane_index(sx + 4, yy), source_bit) for yy in range(5))
        ordered.extend(
            (lane_index(sx + 1, yy), (source_bit - 1) % LANE_BITS)
            for yy in range(5)
        )

        for dependency in ordered:
            if dependency not in dependencies:
                dependencies.append(dependency)

    return dependencies


def ec_bool(value: bool) -> str:
    return "true" if value else "false"


def hypothesis_name(lane: int, bit: int) -> str:
    return f"h{lane}{bit}"


def emit_rewrite_lines(names: list[str]) -> list[str]:
    chunks = [names[i : i + 11] for i in range(0, len(names), 11)]
    return ["rewrite " + " ".join(chunk) + "." for chunk in chunks]


def emit_pow2_proof_lines(exponent: int) -> list[str]:
    lines = []
    for current in range(exponent, 0, -1):
        lines.append(
            f"  rewrite (_ : {current} = {current - 1} + 1) 1:/# exprS //."
        )
    lines.append("  by rewrite expr0.")
    return lines


def emit_move_lines(names: list[str]) -> list[str]:
    chunks = [names[i : i + 11] for i in range(0, len(names), 11)]
    if len(chunks) == 1:
        return ["move=> " + " ".join(chunks[0]) + "."]

    lines = ["move=> " + " ".join(chunks[0])]
    for chunk in chunks[1:-1]:
        lines.append("       " + " ".join(chunk))
    lines.append("       " + " ".join(chunks[-1]) + ".")
    return lines


def emit_lemma(dst_round: int, lane: int, bit: int) -> str:
    if not 1 <= dst_round <= 24:
        raise ValueError("dst_round must be in 1..24")
    if not 0 <= lane < STATE_LANES:
        raise ValueError("lane must be in 0..24")
    if not 0 <= bit < LANE_BITS:
        raise ValueError("bit must be in 0..63")

    src_round = dst_round - 1
    states = empty_shake256_round_states()
    dependencies = bit_dependencies(lane, bit)
    names = [hypothesis_name(dep_lane, dep_bit) for dep_lane, dep_bit in dependencies]
    conclusion = bit_value(states[dst_round], lane, bit)

    src_state = f"shake256_empty_round{src_round:02d}_lanes_cert"
    dst_state = f"shake256_empty_round{dst_round:02d}_lanes_cert"
    name = (
        f"empty_round{dst_round:02d}_lane{lane:02d}_bit{bit:02d}"
        f"_from_round{src_round:02d}_bits"
    )

    lines = [f"lemma {name} :"]
    for dep_lane, dep_bit in dependencies:
        lines.extend(
            [
                "  keccak_lane_bit",
                f"    (nth keccak_lane_zero {src_state} {dep_lane})",
                f"    {dep_bit} = {ec_bool(bit_value(states[src_round], dep_lane, dep_bit))} =>",
            ]
        )
    lines.extend(
        [
            "  keccak_lane_bit",
            f"    (nth keccak_lane_zero {dst_state} {lane})",
            f"    {bit} = {ec_bool(conclusion)}.",
            "proof.",
        ]
    )
    lines.extend(emit_move_lines(names))
    lines.extend(
        [
            f"rewrite /{dst_state}.",
            "rewrite keccak_round_bitE; 1,2: by smt().",
            "rewrite /= keccak_chi_bit_indexE; 1,2: by smt().",
            "rewrite /= !keccak_rho_pi_bit_indexE; 1..6: by smt().",
            "rewrite /= !keccak_theta_bit_indexE; 1..6: by smt().",
            "rewrite /= !keccak_theta_d_bit_indexE;",
            "  1..3: by rewrite /keccak_lane_bits /keccak_rho_offsets",
            "                   /keccak_lane_index; smt().",
            "rewrite /keccak_theta_d_bit_index_value /keccak_theta_c_bit_index_value.",
            "rewrite /kat_round_constant /keccak_round_constants /=.",
            "rewrite /keccak_lane_index /keccak_rho_offsets /=.",
        ]
    )
    lines.extend(emit_rewrite_lines(names))
    lines.extend(
        [
            "rewrite /keccak_lane_of_int /keccak_lane_bit /keccak_word_bit",
            "        /keccak_word_norm /keccak_lane_bits /=.",
        ]
    )
    if lane == 0 and bit == 0:
        lines.append("by rewrite !nth_mkseq; 1..2: by smt().")
    elif lane == 0:
        round_constant = KECCAK_ROUND_CONSTANTS[dst_round - 1]
        pow2 = 1 << bit
        lines.append("rewrite nth_mkseq; first by smt().")
        lines.append("rewrite /=.")
        lines.append(f"have -> : 2 ^ {bit} = {pow2}.")
        lines.extend(emit_pow2_proof_lines(bit))
        lines.append(
            f"rewrite (: {round_constant} %% 2 ^ 64 = {round_constant});"
        )
        lines.append("  first by rewrite empty_generated_pow2_64E pmod_small; smt().")
        lines.append("by smt().")
    else:
        lines.append("by [].")
    lines.append("qed.")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dst-round", type=int, required=True)
    parser.add_argument("--lane", type=int, required=True)
    parser.add_argument("--bit", type=int, required=True)
    args = parser.parse_args()
    print(emit_lemma(args.dst_round, args.lane, args.bit))


if __name__ == "__main__":
    main()
