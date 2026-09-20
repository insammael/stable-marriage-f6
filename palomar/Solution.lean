import StableMarriageF6.F6ConvexWindowN15

/-!
# Proved solution

The definitions and theorem statement match `palomar.Challenge`. The proof
reuses the audited theorem `F6ConvexWindow.totalAntichains_le_48`.
-/

noncomputable section
namespace StableMarriageF6Public
open Finset
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [PartialOrder V]

def incomparability (x z : V) : Prop := ¬ x ≤ z ∧ ¬ z ≤ x

def antichain (s : Finset V) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≤ y → x = y

def chain (s : Finset V) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≤ y ∨ y ≤ x

def widthLE (k : ℕ) : Prop :=
  ∀ s : Finset V, antichain s → s.card ≤ k

def inc (x : V) : Finset V := by
  classical
  exact univ.filter (incomparability x)

def ci2 : Prop :=
  ∀ x y : V, x < y → chain (inc x ∩ inc y) ∧ (inc x ∩ inc y).card ≤ 2

def antichains : Finset (Finset V) := by
  classical
  exact univ.filter (antichain (V := V))

def totalNumberOfAntichains : ℕ := (antichains (V := V)).card

theorem totalAntichains_le_48
    (hw : widthLE (V := V) 3)
    (hci : ci2 (V := V))
    (hn : Fintype.card V ≤ 15) :
    totalNumberOfAntichains (V := V) ≤ 48 := by
  change F6ConvexWindow.WidthLE (V := V) 3 at hw
  change F6ConvexWindow.CI2 (V := V) at hci
  change F6ConvexWindow.totalAntichains (V := V) ≤ 48
  exact F6ConvexWindow.totalAntichains_le_48 hw hci hn

end StableMarriageF6Public
