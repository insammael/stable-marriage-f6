import StableMarriageF6.F6ConvexWindow

/-!
The pure support/poset part of frozen human Lemmas 3–4 in
`research/milestones/F6_ROTATION_CI2_BRIDGE_04/HUMAN_PROOF_ROTATION_CI2_V2.md`.

`R` and `M` are abstract finite types. HCAP2 and HCAP3 are explicit hypotheses
supplied by the human stable-marriage Lemmas 1–2. This file does not formalize
preference lists, rotation execution, or the small-block parity argument.
-/

noncomputable section

namespace F6RotationSupport

open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]

/-- The actual men appearing in at least one support indexed by `Q`. -/
def supportUnion (supp : R → Finset M) (Q : Finset R) : Finset M :=
  Q.biUnion supp

/-- Finset order-convexity, including empty and singleton finsets. -/
def OrderConvex (Q : Finset R) : Prop :=
  ∀ x ∈ Q, ∀ z ∈ Q, ∀ y, x ≤ y → y ≤ z → y ∈ Q

def interval (alpha beta : R) : Finset R :=
  univ.filter (fun rho => alpha ≤ rho ∧ rho ≤ beta)

def commonInc (alpha beta : R) : Finset R :=
  F6ConvexWindow.Inc alpha ∩ F6ConvexWindow.Inc beta

@[simp] theorem mem_supportUnion {supp : R → Finset M} {Q : Finset R} {m : M} :
    m ∈ supportUnion supp Q ↔ ∃ rho ∈ Q, m ∈ supp rho := by
  simp [supportUnion]

theorem support_subset_supportUnion (supp : R → Finset M) {Q : Finset R}
    {rho : R} (hrho : rho ∈ Q) : supp rho ⊆ supportUnion supp Q := by
  intro m hm
  exact mem_supportUnion.mpr ⟨rho, hrho, hm⟩

@[simp] theorem mem_interval {alpha beta rho : R} :
    rho ∈ interval alpha beta ↔ alpha ≤ rho ∧ rho ≤ beta := by
  simp [interval]

@[simp] theorem mem_commonInc {alpha beta rho : R} :
    rho ∈ commonInc alpha beta ↔
      F6ConvexWindow.IncRel alpha rho ∧ F6ConvexWindow.IncRel beta rho := by
  simp [commonInc]

/-- HSHARE forces the actual supports of incomparable rotations to be disjoint. -/
theorem supports_disjoint_of_incomparable (supp : R → Finset M)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    {rho sigma : R} (hinc : F6ConvexWindow.IncRel rho sigma) :
    Disjoint (supp rho) (supp sigma) := by
  apply Finset.disjoint_left.mpr
  intro m hrho hsigma
  exact (HSHARE rho sigma ⟨m, mem_inter.mpr ⟨hrho, hsigma⟩⟩).elim hinc.1 hinc.2

/-- Distinct elements of any antichain index pairwise-disjoint support fibers. -/
theorem antichain_supports_pairwiseDisjoint (supp : R → Finset M)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    {A : Finset R} (hA : F6ConvexWindow.Antichain A) :
    (A : Set R).PairwiseDisjoint supp := by
  intro rho hrho sigma hsigma hne
  exact supports_disjoint_of_incomparable supp HSHARE
    (F6ConvexWindow.antichain_inc hA hrho hsigma hne)

/-- Count all actual support fibers; disjointness makes the union count exact. -/
theorem card_supportUnion_antichain (supp : R → Finset M)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    {A : Finset R} (hA : F6ConvexWindow.Antichain A) :
    (supportUnion supp A).card = ∑ rho ∈ A, (supp rho).card := by
  exact Finset.card_biUnion (antichain_supports_pairwiseDisjoint supp HSHARE hA)

theorem two_mul_card_antichain_le_supportUnion (supp : R → Finset M)
    (HMIN : ∀ rho : R, 2 ≤ (supp rho).card)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    {A : Finset R} (hA : F6ConvexWindow.Antichain A) :
    2 * A.card ≤ (supportUnion supp A).card := by
  rw [card_supportUnion_antichain supp HSHARE hA]
  calc
    2 * A.card = ∑ _rho ∈ A, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ rho ∈ A, (supp rho).card := Finset.sum_le_sum (fun rho _ => HMIN rho)

/-- Human Lemma 3: six men bound every antichain by counting its support fibers. -/
theorem widthLE3_of_rotation_support (supp : R → Finset M)
    (H6 : Fintype.card M ≤ 6)
    (HMIN : ∀ rho : R, 2 ≤ (supp rho).card)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho) :
    F6ConvexWindow.WidthLE (V := R) 3 := by
  intro A hA
  have hcount := two_mul_card_antichain_le_supportUnion supp HMIN HSHARE hA
  have hmen := (supportUnion supp A).card_le_univ
  omega

/-- Human Lemma 4a: the closed interval is order-convex. -/
theorem interval_orderConvex (alpha beta : R) : OrderConvex (interval alpha beta) := by
  intro x hx z hz y hxy hyz
  exact mem_interval.mpr ⟨(mem_interval.mp hx).1.trans hxy,
    hyz.trans (mem_interval.mp hz).2⟩

/-- Human Lemma 4a: common incomparability is order-convex. -/
theorem commonInc_orderConvex (alpha beta : R) : OrderConvex (commonInc alpha beta) := by
  intro x hx z hz y hxy hyz
  obtain ⟨hax, hbx⟩ := mem_commonInc.mp hx
  obtain ⟨haz, hbz⟩ := mem_commonInc.mp hz
  exact mem_commonInc.mpr
    ⟨F6ConvexWindow.incomparability_interval hxy hyz hax haz,
      F6ConvexWindow.incomparability_interval hxy hyz hbx hbz⟩

/-- Human Lemma 4b: each interval rotation is incomparable with each commonInc rotation. -/
theorem interval_commonInc_incomparable {alpha beta a z : R}
    (ha : a ∈ interval alpha beta) (hz : z ∈ commonInc alpha beta) :
    F6ConvexWindow.IncRel a z := by
  obtain ⟨hal, hau⟩ := mem_interval.mp ha
  obtain ⟨hza, hzb⟩ := mem_commonInc.mp hz
  exact ⟨fun haz => hza.1 (hal.trans haz), fun hza' => hzb.2 (hza'.trans hau)⟩

/-- Human Lemma 4b: HSHARE makes the two support unions disjoint. -/
theorem interval_commonInc_supportUnion_disjoint (supp : R → Finset M)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    (alpha beta : R) :
    Disjoint (supportUnion supp (interval alpha beta))
      (supportUnion supp (commonInc alpha beta)) := by
  apply Finset.disjoint_left.mpr
  intro m hmA hmZ
  obtain ⟨a, ha, hma⟩ := mem_supportUnion.mp hmA
  obtain ⟨z, hz, hmz⟩ := mem_supportUnion.mp hmZ
  exact Finset.disjoint_left.mp
    (supports_disjoint_of_incomparable supp HSHARE
      (interval_commonInc_incomparable ha hz)) hma hmz

theorem left_mem_interval {alpha beta : R} (hab : alpha ≤ beta) :
    alpha ∈ interval alpha beta := mem_interval.mpr ⟨le_rfl, hab⟩

theorem right_mem_interval {alpha beta : R} (hab : alpha ≤ beta) :
    beta ∈ interval alpha beta := mem_interval.mpr ⟨hab, le_rfl⟩

/-- Human Lemma 4c: the two distinct endpoints give at least two interval rotations. -/
theorem two_le_card_interval {alpha beta : R} (hab : alpha < beta) :
    2 ≤ (interval alpha beta).card := by
  have hsub : ({alpha, beta} : Finset R) ⊆ interval alpha beta := by
    intro rho hrho
    rcases mem_insert.mp hrho with rfl | hrho
    · exact left_mem_interval hab.le
    · have heq := mem_singleton.mp hrho
      subst rho
      exact right_mem_interval hab.le
  have hcard := card_le_card hsub
  simpa [hab.ne] using hcard

/-- Human Lemma 4c: apply the explicit two-man capacity interface to the interval. -/
theorem three_le_card_interval_supportUnion (supp : R → Finset M)
    (HCAP2 : ∀ Q : Finset R, OrderConvex Q →
      (supportUnion supp Q).card ≤ 2 → Q.card ≤ 1)
    {alpha beta : R} (hab : alpha < beta) :
    3 ≤ (supportUnion supp (interval alpha beta)).card := by
  have htwo := two_le_card_interval hab
  by_contra h
  have hsmall : (supportUnion supp (interval alpha beta)).card ≤ 2 := by omega
  have hone := HCAP2 (interval alpha beta) (interval_orderConvex alpha beta) hsmall
  omega

/-- Human Lemma 4d: disjointness and the six-man bound leave at most three men. -/
theorem card_commonInc_supportUnion_le_three (supp : R → Finset M)
    (H6 : Fintype.card M ≤ 6)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    (HCAP2 : ∀ Q : Finset R, OrderConvex Q →
      (supportUnion supp Q).card ≤ 2 → Q.card ≤ 1)
    {alpha beta : R} (hab : alpha < beta) :
    (supportUnion supp (commonInc alpha beta)).card ≤ 3 := by
  have hthree := three_le_card_interval_supportUnion supp HCAP2 hab
  have hdisj := interval_commonInc_supportUnion_disjoint supp HSHARE alpha beta
  have hsum := card_union_of_disjoint hdisj
  have hmen := (supportUnion supp (interval alpha beta) ∪
    supportUnion supp (commonInc alpha beta)).card_le_univ
  omega

/-- Human Lemma 4d: apply the explicit three-man capacity interface to commonInc. -/
theorem card_commonInc_le_two (supp : R → Finset M)
    (H6 : Fintype.card M ≤ 6)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    (HCAP2 : ∀ Q : Finset R, OrderConvex Q →
      (supportUnion supp Q).card ≤ 2 → Q.card ≤ 1)
    (HCAP3 : ∀ Q : Finset R, OrderConvex Q →
      (supportUnion supp Q).card ≤ 3 → Q.card ≤ 2)
    {alpha beta : R} (hab : alpha < beta) :
    (commonInc alpha beta).card ≤ 2 := by
  exact HCAP3 (commonInc alpha beta) (commonInc_orderConvex alpha beta)
    (card_commonInc_supportUnion_le_three supp H6 HSHARE HCAP2 hab)

/-- Human Lemma 4e: an incomparable pair would use four distinct men among at most three. -/
theorem commonInc_chain (supp : R → Finset M)
    (H6 : Fintype.card M ≤ 6)
    (HMIN : ∀ rho : R, 2 ≤ (supp rho).card)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    (HCAP2 : ∀ Q : Finset R, OrderConvex Q →
      (supportUnion supp Q).card ≤ 2 → Q.card ≤ 1)
    {alpha beta : R} (hab : alpha < beta) :
    F6ConvexWindow.Chain (commonInc alpha beta) := by
  intro gamma hgamma delta hdelta
  by_contra hcomp
  have hinc : F6ConvexWindow.IncRel gamma delta :=
    ⟨fun h => hcomp (Or.inl h), fun h => hcomp (Or.inr h)⟩
  have hdisj := supports_disjoint_of_incomparable supp HSHARE hinc
  have hsum := card_union_of_disjoint hdisj
  have hsub : supp gamma ∪ supp delta ⊆ supportUnion supp (commonInc alpha beta) :=
    union_subset (support_subset_supportUnion supp hgamma)
      (support_subset_supportUnion supp hdelta)
  have hcount := card_le_card hsub
  have hgamma_min := HMIN gamma
  have hdelta_min := HMIN delta
  have hthree := card_commonInc_supportUnion_le_three supp H6 HSHARE HCAP2 hab
  omega

/-- Human Lemma 4, packaged as exactly the parent's CI2 predicate. -/
theorem ci2_of_rotation_support (supp : R → Finset M)
    (H6 : Fintype.card M ≤ 6)
    (HMIN : ∀ rho : R, 2 ≤ (supp rho).card)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    (HCAP2 : ∀ Q : Finset R, OrderConvex Q →
      (supportUnion supp Q).card ≤ 2 → Q.card ≤ 1)
    (HCAP3 : ∀ Q : Finset R, OrderConvex Q →
      (supportUnion supp Q).card ≤ 3 → Q.card ≤ 2) :
    F6ConvexWindow.CI2 (V := R) := by
  intro alpha beta hab
  exact ⟨commonInc_chain supp H6 HMIN HSHARE HCAP2 hab,
    card_commonInc_le_two supp H6 HSHARE HCAP2 HCAP3 hab⟩

/-- The complete support/poset bridge under exactly the five specified hypotheses. -/
theorem widthLE3_and_ci2_of_rotation_support (supp : R → Finset M)
    (H6 : Fintype.card M ≤ 6)
    (HMIN : ∀ rho : R, 2 ≤ (supp rho).card)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    (HCAP2 : ∀ Q : Finset R, OrderConvex Q →
      (supportUnion supp Q).card ≤ 2 → Q.card ≤ 1)
    (HCAP3 : ∀ Q : Finset R, OrderConvex Q →
      (supportUnion supp Q).card ≤ 3 → Q.card ≤ 2) :
    F6ConvexWindow.WidthLE (V := R) 3 ∧ F6ConvexWindow.CI2 (V := R) :=
  ⟨widthLE3_of_rotation_support supp H6 HMIN HSHARE,
    ci2_of_rotation_support supp H6 HMIN HSHARE HCAP2 HCAP3⟩

end F6RotationSupport

-- Exact interfaces, including all capacity assumptions and typeclass arguments.
#check @F6RotationSupport.widthLE3_of_rotation_support
#check @F6RotationSupport.ci2_of_rotation_support
#check @F6RotationSupport.widthLE3_and_ci2_of_rotation_support

-- Transitive kernel trust dependencies of every theorem in this source.
#print axioms F6RotationSupport.mem_supportUnion
#print axioms F6RotationSupport.support_subset_supportUnion
#print axioms F6RotationSupport.mem_interval
#print axioms F6RotationSupport.mem_commonInc
#print axioms F6RotationSupport.supports_disjoint_of_incomparable
#print axioms F6RotationSupport.antichain_supports_pairwiseDisjoint
#print axioms F6RotationSupport.card_supportUnion_antichain
#print axioms F6RotationSupport.two_mul_card_antichain_le_supportUnion
#print axioms F6RotationSupport.widthLE3_of_rotation_support
#print axioms F6RotationSupport.interval_orderConvex
#print axioms F6RotationSupport.commonInc_orderConvex
#print axioms F6RotationSupport.interval_commonInc_incomparable
#print axioms F6RotationSupport.interval_commonInc_supportUnion_disjoint
#print axioms F6RotationSupport.left_mem_interval
#print axioms F6RotationSupport.right_mem_interval
#print axioms F6RotationSupport.two_le_card_interval
#print axioms F6RotationSupport.three_le_card_interval_supportUnion
#print axioms F6RotationSupport.card_commonInc_supportUnion_le_three
#print axioms F6RotationSupport.card_commonInc_le_two
#print axioms F6RotationSupport.commonInc_chain
#print axioms F6RotationSupport.ci2_of_rotation_support
#print axioms F6RotationSupport.widthLE3_and_ci2_of_rotation_support
