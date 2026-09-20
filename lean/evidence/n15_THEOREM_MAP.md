# F6_CI2_N15_PURE_POSET_LEAN_03 theorem map

Authoritative mathematics: `research/milestones/F6_CI2_N15_PURE_BOUND_02/HUMAN_PROOF_N15.md`.

Canonical implementation: `lean/StableMarriageF6/F6ConvexWindowN15.lean`.
All new declarations are in namespace `F6ConvexWindow`. The exact final source
is also saved as [F6ConvexWindowN15.lean](F6ConvexWindowN15.lean) in this directory.

| Frozen proof obligation | Lean declarations | Implementation |
| --- | --- | --- |
| Actual triple antichains and their number | `tripleFamily`, `mem_tripleFamily`, `card_tripleFamily` | The family is the existing antichain finset filtered by cardinality three; its cardinality is definitionally `Ak 3`. |
| §1: strict ideal order on all triples | `lastTriple`, `triplesDescending_toFinset`, `triplesDescending_strict`, `ordered_actual_triples` | Repeatedly remove the triple of maximum ideal cardinality. Reverse the resulting list to obtain the ascending ideal order. Nesting and ideal injectivity prove strictness. |
| §1: no re-entry at the last transition | `prefix_overlap_eq_last` | Proves `T ∩ tripleUnion G = T ∩ S` for the preceding triple `S`, using the parent's `no_reentry`. |
| §1: two or three new vertices | `prefix_intersection_le_one`, `successive_new_vertices`, `union_card_step` | Reuses the parent's intersection bound, then counts the difference and union exactly. |
| §1: number `m` of empty transitions | `emptyTransitions`, `emptyTransitions_step` | The recursive counter adds one precisely for an empty prefix overlap; the step theorem identifies that test with disjointness of consecutive triples. The first triple adds zero to the counter. |
| Equation (1): `|U| = 2t + 1 + m` | `triple_union_counts`, first conjunct | Strong induction on the family follows the same successive prefixes as the ideal order. |
| §2: relative position | `earlier_exclusive_below`, `later_exclusive_above` | Implements the frozen ideal-membership arguments and the parent's triple split. |
| §3: one-vertex-overlap case | `below_lt_other_of_inc`, `overlapping_triples_comparable`, `overlapping_prefix_crossPairs_empty` | The shared incomparable vertex forces an earlier-exclusive point below each later-exclusive point. The cross-pair finset is empty. |
| §3: disjoint case is a matching | `disjoint_triples_matching`, `disjoint_triples_cross_le_three` | Each row and each column has at most one neighbor, by `triple_incomparables_le_one`; at most three cross pairs result. |
| §3: no contribution from still-earlier vertices | `earlier_prefix_lt_new`, `prefix_crossPairs_subset` | Uses the preceding triple and the parent's `below_lt_above`. |
| §3: induced-pair recurrence | `inducedPairs_union_subset`, `pairCount_union_le`, `pairCount_triple`, `prefix_pairCount_step` | The new triple contributes its three internal pairs, with at most three further pairs only at an empty transition. |
| Equation (2): `e(U) ≤ 3t + 3m` | `triple_union_counts`, second conjunct | Proved in the same prefix induction as equation (1). |
| §4: Above prefix and Below suffix | `split_monotone`, `above_prefix_neighbors_le_one`, `below_suffix_neighbors_le_one` | Choose the last Above triple and the first Below triple when the corresponding family is nonempty. Each family contributes at most one neighbor. Empty families contribute zero. |
| Equation (4): outsider has at most two neighbors in `U` | `outsider_neighbors_le_two` | Covers the neighbors by the Above-prefix and Below-suffix neighbor sets and adds their bounds. |
| Equation (5): union, cross, and outsider pair counts | `all_pairs_le_union_outsiders`, `pairCount_le_choose` | For `Q = univ \ U`, bounds all pairs by `pairCount U + 2*Q.card + Q.card.choose 2`. |
| Equations (6)–(7): `n = 15`, `t ≥ 6` | `n15_large_triple_arithmetic`, `totalAntichains_le_46_of_six_triples` | Reuses T1 to restrict `t` to six or seven. Uses the three `q` cases for `t = 6`, and `m = q = 0` for `t = 7`. Proves the stronger total bound 46. |
| Equation (8): `1 ≤ t ≤ 5` | `totalAntichains_le_48` | Reuses `F6ConvexWindowFull.T2` and `antichain_count_width3`. |
| No triples | `width2_of_A3_zero`, `totalAntichains_le_48` | Derives the original `WidthLE 2` definition and reuses `F6ConvexWindowFull.T4`. |
| `n ≤ 14` | `totalAntichains_le_48` | Reuses `F6ConvexWindowFull.T3` when triples exist. |
| Final target | `totalAntichains_le_48` | Combines the preceding cases under exactly width three, CI2, and cardinality at most fifteen. |

The final theorem has the signature:

```lean
theorem F6ConvexWindow.totalAntichains_le_48
    {V : Type*} [Fintype V] [PartialOrder V]
    (hw : F6ConvexWindow.WidthLE (V := V) 3)
    (hci : F6ConvexWindow.CI2 (V := V))
    (hn : Fintype.card V ≤ 15) :
    F6ConvexWindow.totalAntichains (V := V) ≤ 48
```

The existing `WidthLE`, `CI2`, `Ak`, and `totalAntichains` definitions are imported
unchanged. Dilworth is reused through `F6ConvexWindowFull.T2`, `T3`, and `T4`.
