import StableMarriageF6.F6ConvexWindow
import StableMarriageF6.DilworthTheorem

/-!
The frozen finite-poset targets, with the explicit chain-decomposition hypotheses
discharged by the locally compiled proof of classical Dilworth.
The parent source and the external Dilworth proof are copied without changes.
-/

noncomputable section

namespace F6ConvexWindow

open Finset
variable {V : Type*} [Fintype V] [PartialOrder V]

/-- The parent and the reference express the same antichain predicate. -/
theorem antichain_iff_dilworth (A : Finset V) :
    Antichain A ↔ DilworthTheorem.IsAntichain (A : Set V) := by
  constructor
  · intro h x y hx hy hne
    exact antichain_inc h hx hy hne
  · intro h x hx y hy hxy
    by_contra hne
    exact (h x y hx hy hne).1 hxy

/-- W3 in the frozen parent is exactly `WidthLE 3`. -/
theorem w3_antichain_card_le (hw : WidthLE (V := V) 3) (A : Finset V)
    (hA : DilworthTheorem.IsAntichain (A : Set V)) : A.card ≤ 3 :=
  hw A ((antichain_iff_dilworth A).mpr hA)

/-- The width-two hypothesis supplies the reference's antichain bound. -/
theorem width2_antichain_card_le (hw : WidthLE (V := V) 2) (A : Finset V)
    (hA : DilworthTheorem.IsAntichain (A : Set V)) : A.card ≤ 2 :=
  hw A ((antichain_iff_dilworth A).mpr hA)

/-- Choose a covering chain for each vertex; each resulting color fiber is a chain.
Empty chains and the empty vertex type need no additional assumptions. -/
theorem chain_cover_to_decomposition {k : ℕ} (C : Fin k → Finset V)
    (hC : DilworthTheorem.IsChainCover (univ : Finset V) C) :
    Nonempty (ChainDecomposition (V := V) k) := by
  classical
  have hcover (x : V) : ∃ i, x ∈ C i := by
    have hx : x ∈ univ.biUnion C := hC.2.1.symm ▸ mem_univ x
    simpa only [mem_biUnion, mem_univ, true_and] using hx
  choose color hcolor using hcover
  refine ⟨⟨color, ?_⟩⟩
  intro i x hx y hy
  have hxi : color x = i := (mem_filter.mp hx).2
  have hyi : color y = i := (mem_filter.mp hy).2
  exact hC.1 i x y (hxi ▸ hcolor x) (hyi ▸ hcolor y)

/-- The only width-three instance of the generic Dilworth theorem. -/
theorem w3_chain_decomposition (hw : WidthLE (V := V) 3) :
    Nonempty (ChainDecomposition (V := V) 3) := by
  classical
  obtain ⟨C, hC⟩ := DilworthTheorem.dilworth_theorem (univ : Finset V) 3
    (fun A _ hA => w3_antichain_card_le hw A hA)
  exact chain_cover_to_decomposition C hC

/-- The only width-two instance of the generic Dilworth theorem. -/
theorem width2_chain_decomposition (hw : WidthLE (V := V) 2) :
    Nonempty (ChainDecomposition (V := V) 2) := by
  classical
  obtain ⟨C, hC⟩ := DilworthTheorem.dilworth_theorem (univ : Finset V) 2
    (fun A _ hA => width2_antichain_card_le hw A hA)
  exact chain_cover_to_decomposition C hC

end F6ConvexWindow

namespace F6ConvexWindowFull

open F6ConvexWindow
variable {V : Type*} [Fintype V] [PartialOrder V]

/-- T1: the unchanged parent result under exactly W3, CI2, and A3 > 0. -/
theorem T1 (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (hpos : 0 < Ak (V := V) 3) : 2 * Ak (V := V) 3 + 1 ≤ Fintype.card V :=
  target1_triples hw hci hpos

/-- T2: no explicit three-chain decomposition is an input. -/
theorem T2 (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (hpos : 0 < Ak (V := V) 3) : Ak (V := V) 2 + 3 ≤ 2 * Fintype.card V := by
  obtain ⟨d⟩ := w3_chain_decomposition hw
  exact target2_pairs_three_chains hw hci hpos d

/-- T3: the frozen bound for at most fourteen vertices. -/
theorem T3 (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (hpos : 0 < Ak (V := V) 3) (hn : Fintype.card V ≤ 14) :
    totalAntichains (V := V) ≤ 46 := by
  obtain ⟨d⟩ := w3_chain_decomposition hw
  exact target3_antichains46_three_chains hw hci hpos hn d

/-- T4: width at most two, including empty posets and empty chain fibers. -/
theorem T4 (hw : WidthLE (V := V) 2) (hci : CI2 (V := V))
    (hn : Fintype.card V ≤ 15) : totalAntichains (V := V) ≤ 36 := by
  obtain ⟨d⟩ := width2_chain_decomposition hw
  exact target4_antichains36_two_chains hw hci hn d

end F6ConvexWindowFull

-- Exact signatures and transitive kernel dependencies of the load-bearing results.
#check @DilworthTheorem.dilworth_theorem
#check @F6ConvexWindowFull.T1
#check @F6ConvexWindowFull.T2
#check @F6ConvexWindowFull.T3
#check @F6ConvexWindowFull.T4
#print axioms DilworthTheorem.dilworth_theorem
#print axioms F6ConvexWindowFull.T1
#print axioms F6ConvexWindowFull.T2
#print axioms F6ConvexWindowFull.T3
#print axioms F6ConvexWindowFull.T4
