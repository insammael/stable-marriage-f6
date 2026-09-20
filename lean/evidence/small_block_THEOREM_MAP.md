# F6_SMALL_BLOCK_TOKEN_CAPACITY_LEAN_05 — theorem map

All names below are in `F6SmallBlockTokenCapacity.TokenRun`.
The exact final source is [F6SmallBlockTokenCapacity.lean](F6SmallBlockTokenCapacity.lean).

| Item | Lean theorem | Statement and frozen-proof implementation |
| --- | --- | --- |
| 1 | `participation_count` | For every `b`, the cardinality of `participationSteps R b` is at most `Fintype.card B - 1`. `rank_monotone` uses HOUT and HWORSE. Post-participation tokens inject into `W` with the initial token erased; `state 0` gives equal cardinalities of B and W. No participation bound is assumed. |
| 2 | `TWO_SITE_CAPACITY` | `Fintype.card B ≤ 2 → q ≤ 1`. If two steps existed, their supports would both be all of B, contradicting item 1 on the first two steps. |
| 3 | `THREE_SITE_INCIDENCE_EQUALITY` | Given `Fintype.card B ≤ 3` and `3 ≤ q`, returns `card B = 3`, all first-three support cards equal to 2, and every man's first-three participation count equal to 2. `three_incidence_equality` proves the six-incidence squeeze and equality of every summand. |
| 4 | `TWO_SUPPORT_FORCES_SWAP` | A support of cardinality 2 has distinct members x,y whose tokens are exchanged. `previous_holder_mem` uses the equivalences and HOUT; `pair_swap` and `named_pair_swap` use the change forced by HWORSE. |
| 5 | `THREE_STEP_RETURN` | For a three-step run with item 3's equality structure, some x belongs to supports 0 and 2, is outside support 1, and satisfies `state 3 x = state 0 x`. `triangle_supports` constructs the ordered supports `{x,a}`, `{a,b}`, `{x,b}`. The proof composes the three named-pair swaps. |
| 6 | `THREE_SITE_CAPACITY` | `Fintype.card B ≤ 3 → q ≤ 2`. Applies items 3 and 5 to the first three steps, then contradicts HWORSE at steps 0 and 2 with HOUT at step 1. |
| 7 | `SMALL_BLOCK_TOKEN_CAPACITIES` | Packages `(card B ≤ 2 → q ≤ 1) ∧ (card B ≤ 3 → q ≤ 2)`. |
| 8 — OPTIONAL, completed | `SIX_SITE_INCIDENCE_OPTIONAL` | `card B ≤ 6 → (2*q ≤ 6*5 ∧ q ≤ 15)`, from `incidence_bounds` and item 1. |

`TokenRun` has precisely the support, equivalence-state, rank, HMIN, HOUT,
and HWORSE fields requested by the task. `participationSteps` filters all
step indices by support membership. `firstSteps R n h` restricts the original
run to its first n steps using `Fin.castLE`; it preserves ranks and the fixed
token type. Thus the three-step formulation of item 5 applies directly to
item 3's first-three-step data.

Additional engineering lemmas: `mem_participationSteps`, `rank_after_lt`,
`initial_rank_lt_after`, `incidence_sum`, `selected_participation_le`,
`pair_of_card_two_mem`, and `three_membership_sum`.
All 22 theorems have explicit `#print axioms` commands in the delivered source.
