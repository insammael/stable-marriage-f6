import Mathlib

/-!
# Advertised finite-poset statement

This is the complete statement surface advertised to Palomar. It concerns
only a finite poset. It does not claim that the stable-marriage semantic
bridge, or the full theorem `f(6) = 48`, is formalized end to end in Lean.
-/

noncomputable section
namespace StableMarriageF6Public
open Finset
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [PartialOrder V]

/-- Two elements of a poset are incomparable. -/
def incomparability (x z : V) : Prop := ¬ x ≤ z ∧ ¬ z ≤ x

/-- Every two comparable members of `s` are equal. -/
def antichain (s : Finset V) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≤ y → x = y

/-- Every two members of `s` are comparable. -/
def chain (s : Finset V) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≤ y ∨ y ≤ x

/-- Every finite antichain has cardinality at most `k`. -/
def widthLE (k : ℕ) : Prop :=
  ∀ s : Finset V, antichain s → s.card ≤ k

/-- The finite set of elements incomparable with `x`. -/
def inc (x : V) : Finset V := by
  classical
  exact univ.filter (incomparability x)

/--
For every strict comparison `x < y`, the elements incomparable with both
form a chain of cardinality at most two.
-/
def ci2 : Prop :=
  ∀ x y : V, x < y → chain (inc x ∩ inc y) ∧ (inc x ∩ inc y).card ≤ 2

/-- The finite family of all antichains. -/
def antichains : Finset (Finset V) := by
  classical
  exact univ.filter (antichain (V := V))

/-- The total number of antichains. -/
def totalNumberOfAntichains : ℕ := (antichains (V := V)).card

/--
If `P` is a finite poset with at most 15 elements, width at most 3, and CI2,
then `P` has at most 48 antichains.
-/
theorem totalAntichains_le_48
    (hw : widthLE (V := V) 3)
    (hci : ci2 (V := V))
    (hn : Fintype.card V ≤ 15) :
    totalNumberOfAntichains (V := V) ≤ 48 := by
  sorry

end StableMarriageF6Public
