# F6_ROTATION_SUPPORT_TO_CI2_LEAN_04 theorem map

Status: PASS_FULL.

Canonical source: `lean/StableMarriageF6/F6RotationSupportCI2.lean`.
The file beside this map is an exact copy. All new declarations are in
namespace `F6RotationSupport`.

The implementation follows only Lemmas 3–4 of
`research/milestones/F6_ROTATION_CI2_BRIDGE_04/HUMAN_PROOF_ROTATION_CI2_V2.md`.
It imports `StableMarriageF6.F6ConvexWindow` and uses that module's exact
`Antichain`, `Chain`, `WidthLE`, `IncRel`, `Inc`, and `CI2` definitions.

| Required item | Lean declarations (source line) | Hypotheses and proof |
| --- | --- | --- |
| Definitions | `supportUnion` (23), `OrderConvex` (27), `interval` (30), `commonInc` (33) | Actual finite union of supports; finset convexity; closed interval; exact intersection of parent `Inc` finsets. Membership is characterized by `mem_supportUnion`, `mem_interval`, and `mem_commonInc`. |
| 1. Width at most three | `widthLE3_of_rotation_support` (94) | H6, HMIN, HSHARE. `antichain_supports_pairwiseDisjoint` (65) proves disjointness of actual fibers of any antichain. `card_supportUnion_antichain` (75) identifies union cardinality with the sum of fiber cardinalities. `two_mul_card_antichain_le_supportUnion` (82) gives `2 * A.card ≤ (supportUnion supp A).card`. The latter is at most six. |
| 2. Interval convexity | `interval_orderConvex` (106) | Transitivity of the partial order. |
| 3. CommonInc convexity | `commonInc_orderConvex` (112) | Applies the parent's `incomparability_interval` to each endpoint's incomparability predicate. |
| 4. Cross-incomparability and disjoint support unions | `interval_commonInc_incomparable` (121), `interval_commonInc_supportUnion_disjoint` (129) | Endpoint comparisons contradict common incomparability. HSHARE then excludes a shared man, using `supports_disjoint_of_incomparable` (55). These helper proofs do not need endpoint strictness and apply in particular when `alpha < beta`. |
| 5. Endpoints and at least two interval elements | `left_mem_interval` (143), `right_mem_interval` (146), `two_le_card_interval` (150) | For `alpha < beta`, the two-element finset `{alpha, beta}` is contained in the interval. |
| 6. At least three men in the interval union | `three_le_card_interval_supportUnion` (163) | HCAP2, interval convexity, and the two distinct endpoints. At most two men would imply at most one interval element. |
| 7. At most three men in commonInc | `card_commonInc_supportUnion_le_three` (175) | H6, HSHARE, HCAP2. The disjoint support unions have total cardinality at most six, and the interval union has cardinality at least three. |
| 8. At most two commonInc elements | `card_commonInc_le_two` (191) | H6, HSHARE, HCAP2, HCAP3. Apply HCAP3 to the convex commonInc finset using item 7. |
| 9. CommonInc is a chain | `commonInc_chain` (205) | H6, HMIN, HSHARE, HCAP2. An incomparable pair has disjoint supports, each of cardinality at least two. Their union is contained in the commonInc support union, contradicting item 7. |
| 10. Exact parent CI2 | `ci2_of_rotation_support` (230) | H6, HMIN, HSHARE, HCAP2, HCAP3. Packages items 8–9 as `F6ConvexWindow.CI2 (V := R)`. |
| 11. Combined theorem | `widthLE3_and_ci2_of_rotation_support` (245) | Exactly H6, HMIN, HSHARE, HCAP2, HCAP3, with `[Fintype R] [PartialOrder R] [Fintype M]` and `supp : R → Finset M`. Conclusion: `F6ConvexWindow.WidthLE (V := R) 3 ∧ F6ConvexWindow.CI2 (V := R)`. |

`support_subset_supportUnion` (40) supplies the fiber inclusions used in the
chain proof. All 22 theorems, including every helper, have explicit
`#print axioms` commands in the compiled source. `AXIOMS.txt` contains their
verbatim output. `COMPILE.log` also prints the fully quantified signatures of
the width, CI2, and combined theorems.

HCAP2 and HCAP3 remain displayed theorem arguments. This result does not prove
stable-marriage rotation semantics, the small-block parity argument, or `f(6)=48`.
