# Frozen theorem map

Status: **PASS_FULL** for task `F6_CONVEX_WINDOW_DILWORTH_BRIDGE_02`.

The ambient assumptions are exactly `{V : Type*} [Fintype V] [PartialOrder V]`.
The definitions are inherited unchanged from the frozen parent:
`n = Fintype.card V`, `A2 = F6ConvexWindow.Ak 2`,
`A3 = F6ConvexWindow.Ak 3`, and total antichains is
`F6ConvexWindow.totalAntichains`. W3 is `F6ConvexWindow.WidthLE 3`;
width ≤ 2 is `F6ConvexWindow.WidthLE 2`.

All four targets are in [F6ConvexWindowFull.lean](F6ConvexWindowFull.lean).
Their exact Lean signatures are printed in [COMPILE_FULL.log](COMPILE_FULL.log).

| Target | Exact hypotheses | Conclusion | Declaration | Line |
|---|---|---|---|---|
| T1 | W3 + CI2 + A3 > 0 | 2*A3 + 1 ≤ n | `F6ConvexWindowFull.T1` | 77 |
| T2 | W3 + CI2 + A3 > 0 | A2 + 3 ≤ 2*n | `F6ConvexWindowFull.T2` | 82 |
| T3 | W3 + CI2 + A3 > 0 + n ≤ 14 | total antichains ≤ 46 | `F6ConvexWindowFull.T3` | 88 |
| T4 | width ≤ 2 + CI2 + n ≤ 15 | total antichains ≤ 36 | `F6ConvexWindowFull.T4` | 95 |

There are no explicit chain-decomposition hypotheses in these signatures.
The A2/A3 counts are actual antichain counts from the parent definitions;
no bound on either count is an input hypothesis.

## Dilworth bridge

| Step | Proved declaration |
|---|---|
| Equivalent parent/reference antichain predicates | `F6ConvexWindow.antichain_iff_dilworth` |
| W3 supplies cardinality at most 3 | `F6ConvexWindow.w3_antichain_card_le` |
| Width ≤ 2 supplies cardinality at most 2 | `F6ConvexWindow.width2_antichain_card_le` |
| Generic finite Dilworth theorem, with proof compiled locally | `DilworthTheorem.dilworth_theorem` |
| Chain cover supplies the explicit color-fiber interface | `F6ConvexWindow.chain_cover_to_decomposition` |
| Three-chain decomposition from W3 | `F6ConvexWindow.w3_chain_decomposition` |
| Two-chain decomposition from width ≤ 2 | `F6ConvexWindow.width2_chain_decomposition` |

The generic theorem takes a finset S and the condition that each antichain
contained in S has cardinality at most k, and returns a disjoint k-chain cover.
The project applies it to `Finset.univ` only at k = 3 and k = 2.
Selecting a covering chain for each vertex gives the parent's `color : V → Fin k`;
each fiber is a subset of a chain. Empty fibers and the empty vertex type are allowed.

T1 directly reuses `F6ConvexWindow.target1_triples` with the same assumptions.
T2, T3, and T4 respectively reuse `target2_pairs_three_chains`,
`target3_antichains46_three_chains`, and `target4_antichains36_two_chains`,
with the decomposition proved internally by the bridge.

## Verification and scope

The original reference, the local support source, the unchanged parent copy,
and the final source were each compiled directly using `lake env lean`.
All four commands exited 0. The reference needed no API adaptation.

[AXIOMS.txt](AXIOMS.txt) contains the five requested `#print axioms` outputs.
Each lists exactly `propext`, `Classical.choice`, and `Quot.sound`.
The Dilworth source is a locally checked proof, not an assumed axiom.

PASS_FULL applies to these four finite-poset statements. CI2 remains the frozen
input assumption; rotation semantics and the stable-marriage application are
outside this implementation task.
