#!/usr/bin/env python3
"""Finite independent checks for the order-six manuscript supplement.

No third-party Python packages.

Checks:
1. Enumerate all 6! perfect matchings of the Benjamin-Converse-Krieger DS_3
   instance and keep exactly the stable ones.
2. Recover the finite stable-matching lattice in men's weak-worsening order.
3. Recover its join-irreducible poset.
4. Verify its antichain counts and CI2.
5. Verify an explicit isomorphism from that 15-element join-irreducible poset
   to the manuscript poset P_*.
6. Verify the direct combinatorics of P_* independently.

This checks one extremal example. It is not used for the universal upper bound.
"""
from itertools import permutations, combinations
import json
from pathlib import Path

N = 6
HALF = 3

def ds3_rank_matrix():
    return tuple(
        tuple(
            (
                2 * (i + j)
                if (i < HALF) == (j < HALF)
                else 2 * (j - i) + 1
            ) % N + 1
            for j in range(N)
        )
        for i in range(N)
    )

R = ds3_rank_matrix()
assert all(sorted(row) == list(range(1, N + 1)) for row in R)
assert all(sorted(R[i][j] for i in range(N)) == list(range(1, N + 1))
           for j in range(N))

def stable(p):
    inv = [0] * N
    for i, j in enumerate(p):
        inv[j] = i
    for i in range(N):
        for j in range(N):
            man_prefers = R[i][j] < R[i][p[i]]
            woman_prefers = (N + 1 - R[i][j]) < (N + 1 - R[inv[j]][j])
            if man_prefers and woman_prefers:
                return False
    return True

stable_matchings = [p for p in permutations(range(N)) if stable(p)]
stable_matchings.sort(key=lambda p: (sum(R[i][p[i]] for i in range(N)), p))
s = len(stable_matchings)

# Men's weak-worsening lattice order.
le = [
    [
        all(R[i][p[i]] <= R[i][q[i]] for i in range(N))
        for q in stable_matchings
    ]
    for p in stable_matchings
]

def lower_covers(b):
    ans = []
    for a in range(s):
        if a == b or not le[a][b]:
            continue
        if not any(
            c not in (a, b) and le[a][c] and le[c][b]
            for c in range(s)
        ):
            ans.append(a)
    return ans

lower = [lower_covers(b) for b in range(s)]
join_irreducibles = [i for i in range(s) if len(lower[i]) == 1]
r = len(join_irreducibles)

jle = [
    [le[join_irreducibles[a]][join_irreducibles[b]] for b in range(r)]
    for a in range(r)
]

j_covers = []
for a in range(r):
    for b in range(r):
        if a == b or not jle[a][b]:
            continue
        if not any(
            c not in (a, b) and jle[a][c] and jle[c][b]
            for c in range(r)
        ):
            j_covers.append((a + 1, b + 1))

# Antichain counts of J.
incomp = [[not jle[a][b] and not jle[b][a] for b in range(r)] for a in range(r)]
antichain_counts = [0] * (r + 1)
for mask in range(1 << r):
    chosen = [i for i in range(r) if (mask >> i) & 1]
    if all(incomp[a][b] for a, b in combinations(chosen, 2)):
        antichain_counts[len(chosen)] += 1

# CI2 for J.
ci2 = True
max_common_inc = 0
for a, b in combinations(range(r), 2):
    if jle[a][b] or jle[b][a]:
        common = [z for z in range(r) if incomp[a][z] and incomp[b][z]]
        max_common_inc = max(max_common_inc, len(common))
        ci2 &= len(common) <= 2
        ci2 &= all(not incomp[x][y] for x, y in combinations(common, 2))

# P_*.
def pstar_lt(x, y):
    i, a = x
    j, b = y
    return j >= i + 2 or (j == i + 1 and a != b)

pstar = [(i, a) for i in range(1, 6) for a in range(1, 4)]

# Explicit isomorphism. Join-irreducibles are indexed 1..15 in the
# deterministic order above. At odd levels use coordinates 1,2,3; at even
# levels reverse them.
phi = {}
for i in range(1, 6):
    for k in range(1, 4):
        node = 3 * (i - 1) + k
        a = k if i % 2 == 1 else 4 - k
        phi[node] = (i, a)

isomorphism_ok = True
isomorphism_mismatches = []
for u in range(1, r + 1):
    for v in range(1, r + 1):
        actual = jle[u - 1][v - 1]
        expected = (u == v) or pstar_lt(phi[u], phi[v])
        if actual != expected:
            isomorphism_ok = False
            isomorphism_mismatches.append([u, v, actual, expected])

# Direct P_* verification.
pstar_le = [[x == y or pstar_lt(x, y) for y in pstar] for x in pstar]
pstar_incomp = [
    [not pstar_le[a][b] and not pstar_le[b][a] for b in range(15)]
    for a in range(15)
]
pstar_counts = [0] * 16
for mask in range(1 << 15):
    chosen = [i for i in range(15) if (mask >> i) & 1]
    if all(pstar_incomp[a][b] for a, b in combinations(chosen, 2)):
        pstar_counts[len(chosen)] += 1

pstar_ci2 = True
pstar_max_common = 0
for a, b in combinations(range(15), 2):
    if pstar_le[a][b] or pstar_le[b][a]:
        common = [z for z in range(15)
                  if pstar_incomp[a][z] and pstar_incomp[b][z]]
        pstar_max_common = max(pstar_max_common, len(common))
        pstar_ci2 &= len(common) <= 2
        pstar_ci2 &= all(not pstar_incomp[x][y]
                         for x, y in combinations(common, 2))

# Stable pairs, join-irreducible cover supports.
all_pairs = all(
    any(p[i] == j for p in stable_matchings)
    for i in range(N) for j in range(N)
)
rotation_support_sizes = []
rotations_per_man = [0] * N
for b in join_irreducibles:
    a = lower[b][0]
    support = [i for i in range(N)
               if stable_matchings[a][i] != stable_matchings[b][i]]
    rotation_support_sizes.append(len(support))
    for i in support:
        rotations_per_man[i] += 1

result = {
    "ds3": {
        "male_rank_matrix": R,
        "perfect_matchings_enumerated": 720,
        "stable_matchings": s,
        "all_36_pairs_are_stable_pairs": all_pairs,
        "join_irreducible_poset_size": r,
        "antichains_by_size": antichain_counts[:4],
        "larger_antichains": sum(antichain_counts[4:]),
        "CI2": ci2,
        "max_common_incomparability_size": max_common_inc,
        "rotation_support_sizes": rotation_support_sizes,
        "rotations_per_man": rotations_per_man,
        "join_irreducible_cover_relations_1_based": j_covers,
    },
    "pstar": {
        "antichains_by_size": pstar_counts[:4],
        "larger_antichains": sum(pstar_counts[4:]),
        "CI2": pstar_ci2,
        "max_common_incomparability_size": pstar_max_common,
    },
    "isomorphism": {
        "verified": isomorphism_ok,
        "map_join_irreducible_to_pstar": {str(k): list(v) for k, v in phi.items()},
        "mismatches": isomorphism_mismatches,
    },
}

assert s == 48
assert r == 15
assert antichain_counts[:4] == [1, 15, 27, 5]
assert sum(antichain_counts[4:]) == 0
assert ci2
assert all_pairs
assert rotation_support_sizes == [2] * 15
assert rotations_per_man == [5] * 6
assert pstar_counts[:4] == [1, 15, 27, 5]
assert sum(pstar_counts[4:]) == 0
assert pstar_ci2
assert isomorphism_ok

out = Path(__file__).with_name("DS3_PSTAR_CHECK.json")
out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
print(json.dumps({
    "stable_matchings": s,
    "join_irreducibles": r,
    "antichains": antichain_counts[:4],
    "all_36_pairs": all_pairs,
    "pstar_antichains": pstar_counts[:4],
    "isomorphism_verified": isomorphism_ok,
    "output": str(out),
}, indent=2))
