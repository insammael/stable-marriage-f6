import Mathlib

/-!
Finite-poset implementation of HUMAN_PROOF.md §§6–§9.
The order is an arbitrary finite partial order. No rotation semantics is assumed.
-/

noncomputable section
namespace F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

def IncRel (x z : V) : Prop := ¬ x ≤ z ∧ ¬ z ≤ x

def Antichain (s : Finset V) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≤ y → x = y

def Chain (s : Finset V) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≤ y ∨ y ≤ x

def WidthLE (k : ℕ) : Prop := ∀ s : Finset V, Antichain s → s.card ≤ k

def Inc (x : V) : Finset V := by classical exact univ.filter (IncRel x)

def CI2 : Prop := ∀ x y : V, x < y →
  Chain (Inc x ∩ Inc y) ∧ (Inc x ∩ Inc y).card ≤ 2

def antichains : Finset (Finset V) := by classical exact univ.filter Antichain

def Ak (k : ℕ) : ℕ := by classical exact ((antichains (V := V)).filter (fun s => s.card = k)).card

def totalAntichains : ℕ := (antichains (V := V)).card

def ideal (s : Finset V) : Finset V := by
  classical
  exact univ.filter (fun x => ∃ y ∈ s, x ≤ y)

@[simp] theorem mem_Inc {x z : V} : z ∈ Inc x ↔ IncRel x z := by
  classical
  simp [Inc]

@[simp] theorem mem_ideal {s : Finset V} {x : V} :
    x ∈ ideal s ↔ ∃ y ∈ s, x ≤ y := by
  classical
  simp [ideal]

@[simp] theorem mem_antichains {s : Finset V} :
    s ∈ antichains ↔ Antichain s := by
  classical
  simp [antichains]

theorem inc_symm {x y : V} (h : IncRel x y) : IncRel y x := ⟨h.2, h.1⟩

theorem antichain_inc {s : Finset V} (h : Antichain s)
    {x y : V} (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) : IncRel x y :=
  ⟨fun hxy => hne (h x hx y hy hxy), fun hyx => hne (h y hy x hx hyx).symm⟩

theorem subset_ideal (s : Finset V) : s ⊆ ideal s := by
  intro x hx
  exact mem_ideal.mpr ⟨x, hx, le_rfl⟩

theorem ideal_mono {s t : Finset V} (h : s ⊆ ideal t) : ideal s ⊆ ideal t := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_ideal.mp hx
  obtain ⟨z, hz, hyz⟩ := mem_ideal.mp (h hy)
  exact mem_ideal.mpr ⟨z, hz, hxy.trans hyz⟩

theorem ideal_injective {s t : Finset V} (hs : Antichain s) (ht : Antichain t)
    (h : ideal s = ideal t) : s = t := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_ideal.mp (h ▸ subset_ideal s hx)
    obtain ⟨z, hz, hyz⟩ := mem_ideal.mp (h.symm ▸ subset_ideal t hy)
    have hxz := hs x hx z hz (hxy.trans hyz)
    have hxy' : x = y := le_antisymm hxy (hxz ▸ hyz)
    exact hxy' ▸ hy
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_ideal.mp (h.symm ▸ subset_ideal t hx)
    obtain ⟨z, hz, hyz⟩ := mem_ideal.mp (h ▸ subset_ideal s hy)
    have hxz := ht x hx z hz (hxy.trans hyz)
    have hxy' : x = y := le_antisymm hxy (hxz ▸ hyz)
    exact hxy' ▸ hy

/-- §7d: an element cannot leave and later reenter nested generated ideals. -/
theorem no_reentry {s t u : Finset V} (hu : Antichain u)
    (hst : ideal s ⊆ ideal t) (htu : ideal t ⊆ ideal u)
    {x : V} (hxs : x ∈ s) (hxu : x ∈ u) : x ∈ t := by
  obtain ⟨y, hy, hxy⟩ := mem_ideal.mp (hst (subset_ideal s hxs))
  obtain ⟨z, hz, hyz⟩ := mem_ideal.mp (htu (subset_ideal t hy))
  have hxz := hu x hxu z hz (hxy.trans hyz)
  have hxy' : x = y := le_antisymm hxy (hxz ▸ hyz)
  exact hxy' ▸ hy

/-- §8: incomparability is order-convex along a chain. -/
theorem incomparability_interval {x a b c : V} (hab : a ≤ b) (hbc : b ≤ c)
    (ha : IncRel x a) (hc : IncRel x c) : IncRel x b := by
  exact ⟨fun h => hc.1 (h.trans hbc), fun h => ha.2 (hab.trans h)⟩

/-- The adjacent common-incomparability bound is an immediate CI2 projection. -/
theorem adjacent_common_bound (hci : CI2 (V := V)) {x y : V} (hxy : x < y) :
    (Inc x ∩ Inc y).card ≤ 2 := (hci x y hxy).2

/-- CI2 excludes the induced 2+1+1 configuration used in §7a. -/
theorem nf211 (hci : CI2 (V := V)) {x y a b : V} (hxy : x < y)
    (hxa : IncRel x a) (hya : IncRel y a)
    (hxb : IncRel x b) (hyb : IncRel y b) (hab : IncRel a b) : False := by
  classical
  have ha : a ∈ Inc x ∩ Inc y := by simp [hxa, hya]
  have hb : b ∈ Inc x ∩ Inc y := by simp [hxb, hyb]
  exact ((hci x y hxy).1 a ha b hb).elim hab.1 hab.2


/-- A maximum-size triple meets every outside point by a comparison (§7a). -/
theorem triple_comparison (hw : WidthLE (V := V) 3) {T : Finset V}
    (ht : Antichain T) (hc : T.card = 3) {x : V} (hx : x ∉ T) :
    ∃ y ∈ T, x ≤ y ∨ y ≤ x := by
  classical
  by_contra hn
  have hi : ∀ y ∈ T, IncRel x y := by
    intro y hy
    exact ⟨fun h => hn ⟨y, hy, Or.inl h⟩, fun h => hn ⟨y, hy, Or.inr h⟩⟩
  have ht' : Antichain (insert x T) := by
    intro a ha b hb hab
    rcases mem_insert.mp ha with rfl | haT
    · rcases mem_insert.mp hb with rfl | hbT
      · rfl
      · exact False.elim ((hi b hbT).1 hab)
    · rcases mem_insert.mp hb with rfl | hbT
      · exact False.elim ((hi a haT).2 hab)
      · exact ht a haT b hbT hab
  have := hw (insert x T) ht'
  rw [card_insert_of_notMem hx, hc] at this
  omega

/-- At most one element of a triple can be incomparable with an outside point. -/
theorem triple_incomparables_le_one (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {T : Finset V} (ht : Antichain T) (hc : T.card = 3) {x : V} (hx : x ∉ T) :
    (T.filter (IncRel x)).card ≤ 1 := by
  classical
  obtain ⟨y, hy, hxy⟩ := triple_comparison hw ht hc hx
  have hne : x ≠ y := fun h => hx (h.symm ▸ hy)
  have hchain : Chain (Inc x ∩ Inc y) := by
    rcases hxy with hxy | hyx
    · exact (hci x y (hxy.lt_of_ne hne)).1
    · simpa [inter_comm] using (hci y x (hyx.lt_of_ne hne.symm)).1
  apply card_le_one.mpr
  intro a ha b hb
  obtain ⟨haT, hxa⟩ := mem_filter.mp ha
  obtain ⟨hbT, hxb⟩ := mem_filter.mp hb
  have hay : a ≠ y := by
    intro h
    subst a
    exact hxy.elim hxa.1 hxa.2
  have hby : b ≠ y := by
    intro h
    subst b
    exact hxy.elim hxb.1 hxb.2
  have ha' : a ∈ Inc x ∩ Inc y := by
    simp [hxa, antichain_inc ht hy haT hay.symm]
  have hb' : b ∈ Inc x ∩ Inc y := by
    simp [hxb, antichain_inc ht hy hbT hby.symm]
  exact (hchain a ha' b hb').elim (ht a haT b hbT) (fun h => (ht b hbT a haT h).symm)

def Below (T : Finset V) (x : V) : Prop := 2 ≤ (T.filter (fun t => x < t)).card
def Above (T : Finset V) (x : V) : Prop := 2 ≤ (T.filter (fun t => t < x)).card

/-- §7a: an outside point is below at least two or above at least two triple members. -/
theorem triple_split (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {T : Finset V} (ht : Antichain T) (hc : T.card = 3) {x : V} (hx : x ∉ T) :
    Below T x ∨ Above T x := by
  classical
  have hi := triple_incomparables_le_one hw hci ht hc hx
  have hsum := card_filter_add_card_filter_not (s := T) (p := IncRel x)
  have hcomp : 2 ≤ (T.filter (fun a => ¬ IncRel x a)).card := by omega
  obtain ⟨y, hy, hxy⟩ := triple_comparison hw ht hc hx
  have hne : ∀ a ∈ T, x ≠ a := fun a ha h => hx (h.symm ▸ ha)
  rcases hxy with hxy | hyx
  · left
    apply hcomp.trans
    apply card_le_card
    intro a ha
    obtain ⟨ha, hia⟩ := mem_filter.mp ha
    refine mem_filter.mpr ⟨ha, ?_⟩
    have hax : ¬ a ≤ x := by
      intro h
      have hay := ht a ha y hy (h.trans hxy)
      have heq : x = a := le_antisymm (hay.symm ▸ hxy) h
      exact hne a ha heq
    have hxa : x ≤ a := by
      by_contra h
      exact hia ⟨h, hax⟩
    exact hxa.lt_of_ne (hne a ha)
  · right
    apply hcomp.trans
    apply card_le_card
    intro a ha
    obtain ⟨ha, hia⟩ := mem_filter.mp ha
    refine mem_filter.mpr ⟨ha, ?_⟩
    have hxa : ¬ x ≤ a := by
      intro h
      have hya := ht y hy a ha (hyx.trans h)
      have heq : x = a := le_antisymm h (hya ▸ hyx)
      exact hne a ha heq
    have hax : a ≤ x := by
      by_contra h
      exact hia ⟨hxa, h⟩
    exact hax.lt_of_ne (hne a ha).symm

/-- The two two-element subsets of a triple overlap (§7a). -/
theorem below_lt_above {T : Finset V} (hc : T.card = 3) {l u : V}
    (hl : Below T l) (hu : Above T u) : l < u := by
  classical
  let A := T.filter (fun t => l < t)
  let B := T.filter (fun t => t < u)
  have hun : A ∪ B ⊆ T := union_subset (filter_subset _ _) (filter_subset _ _)
  have hcard := card_le_card hun
  have hsum := card_union_add_card_inter A B
  have hpos : 0 < (A ∩ B).card := by
    change 2 ≤ A.card at hl
    change 2 ≤ B.card at hu
    omega
  obtain ⟨t, ht⟩ := card_pos.mp hpos
  obtain ⟨htA, htB⟩ := mem_inter.mp ht
  exact (mem_filter.mp htA).2.trans (mem_filter.mp htB).2

theorem below_mem_ideal {T : Finset V} {x : V} (h : Below T x) : x ∈ ideal T := by
  classical
  obtain ⟨t, ht⟩ := card_pos.mp (show 0 < (T.filter (fun t => x < t)).card by
    unfold Below at h
    omega)
  obtain ⟨ht, hxt⟩ := mem_filter.mp ht
  exact mem_ideal.mpr ⟨t, ht, hxt.le⟩

theorem above_not_le {T : Finset V} (ht : Antichain T) {x t : V}
    (hx : Above T x) (htT : t ∈ T) : ¬ x ≤ t := by
  classical
  obtain ⟨a, ha⟩ := card_pos.mp (show 0 < (T.filter (fun a => a < x)).card by
    unfold Above at hx
    omega)
  obtain ⟨ha, hax⟩ := mem_filter.mp ha
  intro hxt
  have hat := ht a ha t htT (hax.le.trans hxt)
  exact hax.not_ge (hat.symm ▸ hxt)

/-- §7b: all generated ideals of triple antichains are nested. -/
theorem triple_ideals_nested (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {S T : Finset V} (hs : Antichain S) (ht : Antichain T)
    (hsc : S.card = 3) (htc : T.card = 3) :
    ideal S ⊆ ideal T ∨ ideal T ⊆ ideal S := by
  classical
  by_cases hu : ∃ u ∈ S, Above T u
  · right
    obtain ⟨u, huS, huT⟩ := hu
    have hnlow : ∀ l ∈ S, ¬ Below T l := by
      intro l hlS hlT
      have hlu := below_lt_above htc hlT huT
      exact hlu.ne (hs l hlS u huS hlu.le)
    apply ideal_mono
    intro t htT
    by_cases htS : t ∈ S
    · exact subset_ideal S htS
    obtain ⟨s, hsS, hts | hst⟩ := triple_comparison hw hs hsc htS
    · exact mem_ideal.mpr ⟨s, hsS, hts⟩
    · by_cases hsT : s ∈ T
      · have hst' := ht s hsT t htT hst
        exact False.elim (htS (hst' ▸ hsS))
      · rcases triple_split hw hci ht htc hsT with hlow | hhigh
        · exact False.elim (hnlow s hsS hlow)
        · exact False.elim (above_not_le ht hhigh htT hst)
  · left
    apply ideal_mono
    intro s hsS
    by_cases hsT : s ∈ T
    · exact subset_ideal T hsT
    rcases triple_split hw hci ht htc hsT with hlow | hhigh
    · exact below_mem_ideal hlow
    · exact False.elim (hu ⟨s, hsS, hhigh⟩)

/-- §7c: distinct triple antichains share at most one element. -/
theorem triple_intersection_le_one (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {S T : Finset V} (hs : Antichain S) (ht : Antichain T)
    (hsc : S.card = 3) (htc : T.card = 3) (hne : S ≠ T) : (S ∩ T).card ≤ 1 := by
  classical
  have hnsub : ¬ S ⊆ T := fun h => hne (eq_of_subset_of_card_le h (by omega))
  obtain ⟨x, hxS, hxT⟩ := not_subset.mp hnsub
  have hbound := triple_incomparables_le_one hw hci ht htc hxT
  apply (card_le_card (show S ∩ T ⊆ T.filter (IncRel x) from ?_)).trans hbound
  intro a ha
  obtain ⟨haS, haT⟩ := mem_inter.mp ha
  refine mem_filter.mpr ⟨haT, antichain_inc hs hxS haS ?_⟩
  intro h
  exact hxT (h.symm ▸ haT)


/-- Ordering the generated ideals by cardinality realizes their nesting order. -/
theorem ideal_subset_of_card_le (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {S T : Finset V} (hs : Antichain S) (ht : Antichain T)
    (hsc : S.card = 3) (htc : T.card = 3) (hc : (ideal S).card ≤ (ideal T).card) :
    ideal S ⊆ ideal T := by
  rcases triple_ideals_nested hw hci hs ht hsc htc with h | h
  · exact h
  · exact le_of_eq (eq_of_subset_of_card_le h hc).symm

/-- §7d counting: the first triple contributes three, each later triple at least two. -/
theorem triple_union_lower_bound (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (F : Finset (Finset V)) (hf : ∀ T ∈ F, Antichain T ∧ T.card = 3)
    (hn : F.Nonempty) : 2 * F.card + 1 ≤ (F.biUnion id).card := by
  classical
  induction F using Finset.strongInductionOn with
  | _ F ih =>
    obtain ⟨T, hTF, hTmax⟩ := exists_max_image F (fun T => (ideal T).card) hn
    have ht := hf T hTF
    let G := F.erase T
    have hsub : G ⊆ F := erase_subset _ _
    have hg : ∀ S ∈ G, Antichain S ∧ S.card = 3 := fun S hS => hf S (hsub hS)
    have hF : F = insert T G := (insert_erase hTF).symm
    have hTc : F.card = G.card + 1 := by
      rw [hF, card_insert_of_notMem (notMem_erase _ _)]
    have hU : F.biUnion id = T ∪ G.biUnion id := by rw [hF, biUnion_insert]; rfl
    by_cases hGn : G.Nonempty
    · have ihG := ih G (erase_ssubset hTF) hg hGn
      obtain ⟨S, hSG, hSmax⟩ := exists_max_image G (fun S => (ideal S).card) hGn
      have hs := hg S hSG
      have hST : ideal S ⊆ ideal T :=
        ideal_subset_of_card_le hw hci hs.1 ht.1 hs.2 ht.2 (hTmax S (hsub hSG))
      have hi : (T ∩ G.biUnion id) ⊆ T ∩ S := by
        intro x hx
        obtain ⟨hxT, hxU⟩ := mem_inter.mp hx
        obtain ⟨R, hRG, hxR⟩ := mem_biUnion.mp hxU
        have hr := hg R hRG
        have hRS : ideal R ⊆ ideal S :=
          ideal_subset_of_card_le hw hci hr.1 hs.1 hr.2 hs.2 (hSmax R hRG)
        exact mem_inter.mpr ⟨hxT, no_reentry ht.1 hRS hST hxR hxT⟩
      have hne : T ≠ S := (mem_erase.mp hSG).1.symm
      have hI := (card_le_card hi).trans
        (triple_intersection_le_one hw hci ht.1 hs.1 ht.2 hs.2 hne)
      have hcount := card_union_add_card_inter T (G.biUnion id)
      rw [hU]
      omega
    · have hGe : G = ∅ := not_nonempty_iff_eq_empty.mp hGn
      rw [hU, hGe]
      simp only [biUnion_empty, union_empty]
      simp only [hGe, card_empty] at hTc
      omega

/-- Frozen target 1, with the actual number of three-element antichains. -/
theorem target1_triples (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (hpos : 0 < Ak (V := V) 3) : 2 * Ak (V := V) 3 + 1 ≤ Fintype.card V := by
  classical
  let F := (antichains (V := V)).filter (fun T => T.card = 3)
  have hf : ∀ T ∈ F, Antichain T ∧ T.card = 3 := by
    intro T hT
    exact ⟨mem_antichains.mp (mem_filter.mp hT).1, (mem_filter.mp hT).2⟩
  have hn : F.Nonempty := card_pos.mp hpos
  exact (triple_union_lower_bound hw hci F hf hn).trans (card_le_univ _)


/-- Every nonempty finite chain has a greatest element. -/
theorem chain_greatest {C : Finset V} (hc : Chain C) (hn : C.Nonempty) :
    ∃ y ∈ C, ∀ x ∈ C, x ≤ y := by
  obtain ⟨y, hy, hmax⟩ := exists_maximal hn
  refine ⟨y, hy, ?_⟩
  intro x hx
  exact (hc x hx y hy).elim id (hmax hx)

/-- Exact adjacent-overlap identity underlying the interval double count (§8). -/
theorem chain_adjacent_overlap {C : Finset V} {x y : V}
    (hx : x ∈ C) (hmax : ∀ z ∈ C, z ≤ x) (hxy : x ≤ y) :
    (C.biUnion Inc) ∩ Inc y = Inc x ∩ Inc y := by
  classical
  apply Finset.ext
  intro z
  simp only [mem_inter, mem_biUnion, mem_Inc]
  constructor
  · rintro ⟨⟨a, ha, haz⟩, hyz⟩
    exact ⟨inc_symm (incomparability_interval (hmax a ha) hxy (inc_symm haz) (inc_symm hyz)), hyz⟩
  · rintro ⟨hxz, hyz⟩
    exact ⟨⟨x, hx, hxz⟩, hyz⟩

/-- The exact union recurrence plus CI2 bounds every adjacent overlap by two. -/
theorem chain_degree_union_bound (hci : CI2 (V := V)) (C : Finset V)
    (hc : Chain C) (hn : C.Nonempty) :
    (∑ x ∈ C, (Inc x).card) + 2 ≤ (C.biUnion Inc).card + 2 * C.card := by
  classical
  induction C using Finset.strongInductionOn with
  | _ C ih =>
    obtain ⟨y, hyC, hymax⟩ := chain_greatest hc hn
    let D := C.erase y
    have hsub : D ⊆ C := erase_subset _ _
    have hd : Chain D := fun a ha b hb => hc a (hsub ha) b (hsub hb)
    have hC : C = insert y D := (insert_erase hyC).symm
    have hyD : y ∉ D := notMem_erase _ _
    have hcard : C.card = D.card + 1 := by rw [hC, card_insert_of_notMem hyD]
    have hsum : (∑ x ∈ C, (Inc x).card) = (Inc y).card + ∑ x ∈ D, (Inc x).card := by
      rw [hC, sum_insert hyD]
    have hunion : C.biUnion Inc = D.biUnion Inc ∪ Inc y := by
      rw [hC, biUnion_insert, union_comm]
    by_cases hnD : D.Nonempty
    · obtain ⟨x, hxD, hxmax⟩ := chain_greatest hd hnD
      have hxy : x < y := (hymax x (hsub hxD)).lt_of_ne (mem_erase.mp hxD).1
      have hover := chain_adjacent_overlap hxD hxmax hxy.le
      have hbound : ((D.biUnion Inc) ∩ Inc y).card ≤ 2 := by
        rw [hover]
        exact adjacent_common_bound hci hxy
      have hrec := ih D (erase_ssubset hyC) hd hnD
      have hcount := card_union_add_card_inter (D.biUnion Inc) (Inc y)
      rw [hsum, hunion, hcard]
      omega
    · have hDe : D = ∅ := not_nonempty_iff_eq_empty.mp hnD
      rw [hsum, hunion, hcard, hDe]
      simp

/-- A chain contains no member of any of its own incomparability sets. -/
theorem chain_inc_union_disjoint {C : Finset V} (hc : Chain C) :
    Disjoint C (C.biUnion Inc) := by
  classical
  apply disjoint_left.mpr
  intro x hx hxu
  obtain ⟨y, hy, hxy⟩ := mem_biUnion.mp hxu
  have hi := mem_Inc.mp hxy
  exact (hc y hy x hx).elim hi.1 hi.2

/-- §8 chain row bound, written without natural-number subtraction. -/
theorem chain_degree_bound (hci : CI2 (V := V)) {C : Finset V}
    (hc : Chain C) (hn : C.Nonempty) :
    (∑ x ∈ C, (Inc x).card) + 2 ≤ Fintype.card V + C.card := by
  have h := chain_degree_union_bound hci C hc hn
  have hdis := chain_inc_union_disjoint hc
  have hcard := card_le_univ (C ∪ C.biUnion Inc)
  rw [card_union_of_disjoint hdis] at hcard
  omega

/-- §6: the unique zero-element antichain. -/
theorem Ak_zero : Ak (V := V) 0 = 1 := by
  classical
  have he : (antichains (V := V)).filter (fun s => s.card = 0) = {∅} := by
    ext s
    simp only [mem_filter, mem_antichains, card_eq_zero, mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl
      exact ⟨by intro x hx; simp at hx, rfl⟩
  unfold Ak
  rw [he]
  simp

/-- §6: singleton antichains are counted exactly once per vertex. -/
theorem Ak_one : Ak (V := V) 1 = Fintype.card V := by
  classical
  have he : (antichains (V := V)).filter (fun s => s.card = 1) =
      (univ : Finset V).image (fun x => {x}) := by
    ext s
    simp only [mem_filter, mem_antichains, mem_image, mem_univ, true_and]
    constructor
    · intro h
      obtain ⟨x, hx⟩ := card_eq_one.mp h.2
      exact ⟨x, hx.symm⟩
    · rintro ⟨x, rfl⟩
      refine ⟨?_, by simp⟩
      intro a ha b hb hab
      simpa only [mem_singleton] using (mem_singleton.mp ha).trans (mem_singleton.mp hb).symm
  unfold Ak
  rw [he, card_image_of_injective]
  · exact card_univ
  · intro a b hab
    simpa using hab

/-- Exhaustive decomposition into antichain sizes; no counts are supplied as assumptions. -/
theorem antichain_count_decomposition (k : ℕ) (hw : WidthLE (V := V) k) :
    totalAntichains (V := V) = ∑ j ∈ range (k + 1), Ak (V := V) j := by
  classical
  exact card_eq_sum_card_fiberwise (f := Finset.card) (s := antichains)
    (t := range (k + 1)) (fun s hs => mem_range.mpr (Nat.lt_succ_of_le (hw s (mem_antichains.mp hs))))

theorem antichain_count_width3 (hw : WidthLE (V := V) 3) :
    totalAntichains (V := V) = 1 + Fintype.card V + Ak (V := V) 2 + Ak (V := V) 3 := by
  rw [antichain_count_decomposition 3 hw]
  simp [sum_range_succ, Ak_zero, Ak_one]

theorem antichain_count_width2 (hw : WidthLE (V := V) 2) :
    totalAntichains (V := V) = 1 + Fintype.card V + Ak (V := V) 2 := by
  rw [antichain_count_decomposition 2 hw]
  simp [sum_range_succ, Ak_zero, Ak_one]


/-- Two distinct incomparable vertices give the corresponding two-element antichain. -/
theorem pair_antichain {x y : V} (hi : IncRel x y) : Antichain {x, y} := by
  classical
  intro a ha b hb hab
  simp only [mem_insert, mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exact False.elim (hi.1 hab)
  · exact False.elim (hi.2 hab)
  · rfl

/-- Bijection between neighbors of a vertex and two-element antichains containing it. -/
theorem degree_pair_fiber (x : V) : (Inc x).card =
    (((antichains (V := V)).filter (fun T => T.card = 2)).filter (fun T => x ∈ T)).card := by
  classical
  apply card_bij (fun y _ => ({x, y} : Finset V))
  · intro y hy
    have hi := mem_Inc.mp hy
    have hne : x ≠ y := fun h => hi.1 (le_of_eq h)
    simp only [mem_filter, mem_antichains]
    exact ⟨⟨pair_antichain hi, by simp [hne]⟩, by simp⟩
  · intro a ha b hb he
    have hax : a ≠ x := fun h => (mem_Inc.mp ha).2 (le_of_eq h)
    have ham : a ∈ ({x, b} : Finset V) := he ▸ (by simp : a ∈ ({x, a} : Finset V))
    simpa [hax] using ham
  · intro T hT
    obtain ⟨⟨hTa, hTc⟩, hxT⟩ := mem_filter.mp hT |>.imp_left mem_filter.mp
    have hTa := mem_antichains.mp hTa
    obtain ⟨a, b, hab, hTab⟩ := card_eq_two.mp hTc
    subst T
    rcases (show x = a ∨ x = b by simpa using hxT) with rfl | rfl
    · have hi := antichain_inc hTa (by simp) (by simp) hab
      exact ⟨b, mem_Inc.mpr hi, rfl⟩
    · have hi := antichain_inc hTa (by simp) (by simp) hab.symm
      exact ⟨a, mem_Inc.mpr hi, by simp [pair_comm]⟩

/-- §8 double count: each actual two-element antichain contributes exactly two incidences. -/
theorem degree_sum_eq_twice_A2 : (∑ x : V, (Inc x).card) = 2 * Ak (V := V) 2 := by
  classical
  let F := (antichains (V := V)).filter (fun T => T.card = 2)
  calc
    (∑ x : V, (Inc x).card) = ∑ x : V, (F.filter (fun T => x ∈ T)).card := by
      apply sum_congr rfl
      intro x hx
      exact degree_pair_fiber x
    _ = ∑ T ∈ F, ∑ x : V, if x ∈ T then 1 else 0 := by
      simp only [card_filter]
      rw [sum_comm]
    _ = ∑ T ∈ F, T.card := by simp
    _ = ∑ T ∈ F, 2 := by
      apply sum_congr rfl
      intro T hT
      exact (mem_filter.mp hT).2
    _ = 2 * Ak (V := V) 2 := by simp [Ak, F, Nat.mul_comm]

/-- Explicit Dilworth interface: a partition into k chain fibers (empty fibers allowed). -/
structure ChainDecomposition (k : ℕ) where
  color : V → Fin k
  chain_fiber : ∀ i, Chain (univ.filter (fun x => color x = i))

namespace ChainDecomposition
variable {k : ℕ} (d : ChainDecomposition (V := V) k)

def part (i : Fin k) : Finset V := univ.filter (fun x => d.color x = i)

@[simp] theorem mem_part {i : Fin k} {x : V} : x ∈ d.part i ↔ d.color x = i := by
  simp [part]

theorem parts_card : (∑ i, (d.part i).card) = Fintype.card V := by
  simpa [part] using
    (card_eq_sum_card_fiberwise (s := (univ : Finset V)) (t := (univ : Finset (Fin k)))
      (f := d.color) (fun x hx => mem_univ (d.color x))).symm

theorem parts_sum (f : V → ℕ) : (∑ i, ∑ x ∈ d.part i, f x) = ∑ x, f x := by
  exact sum_fiberwise univ d.color f

theorem color_injective_on_antichain {T : Finset V} (ht : Antichain T) :
    Set.InjOn d.color T := by
  intro x hx y hy he
  have hxP : x ∈ d.part (d.color x) := (mem_part d).mpr rfl
  have hyP : y ∈ d.part (d.color x) := (mem_part d).mpr he.symm
  exact ((d.chain_fiber (d.color x)) x hxP y hyP).elim
    (ht x hx y hy) (fun h => (ht y hy x hx h).symm)

theorem part_nonempty_of_full_antichain {T : Finset V}
    (ht : Antichain T) (hc : T.card = k) (i : Fin k) : (d.part i).Nonempty := by
  classical
  have hcard : (T.image d.color).card = k := (card_image_of_injOn (d.color_injective_on_antichain ht)).trans hc
  have hfull : T.image d.color = univ := eq_of_subset_of_card_le (subset_univ _) (by simp [hcard])
  have hi : i ∈ T.image d.color := hfull.symm ▸ mem_univ i
  obtain ⟨x, hx, hxi⟩ := mem_image.mp hi
  exact ⟨x, (mem_part d).mpr hxi⟩

end ChainDecomposition

/-- Frozen target 2 conditional only on the explicitly displayed Dilworth decomposition. -/
theorem target2_pairs_three_chains (_hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (hpos : 0 < Ak (V := V) 3) (d : ChainDecomposition (V := V) 3) :
    Ak (V := V) 2 + 3 ≤ 2 * Fintype.card V := by
  classical
  obtain ⟨T, hT⟩ := card_pos.mp hpos
  have ht : Antichain T := mem_antichains.mp (mem_filter.mp hT).1
  have htc : T.card = 3 := (mem_filter.mp hT).2
  have hb (i : Fin 3) : (∑ x ∈ d.part i, (Inc x).card) + 2 ≤
      Fintype.card V + (d.part i).card := chain_degree_bound hci (d.chain_fiber i)
    (d.part_nonempty_of_full_antichain ht htc i)
  have hsum := sum_le_sum (s := (univ : Finset (Fin 3))) (fun i _ => hb i)
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  rw [d.parts_sum, degree_sum_eq_twice_A2, d.parts_card] at hsum
  omega

/-- Frozen target 3 conditional only on the explicitly displayed Dilworth decomposition. -/
theorem target3_antichains46_three_chains (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (hpos : 0 < Ak (V := V) 3) (hn : Fintype.card V ≤ 14)
    (d : ChainDecomposition (V := V) 3) : totalAntichains (V := V) ≤ 46 := by
  have h3 := target1_triples hw hci hpos
  have h2 := target2_pairs_three_chains hw hci hpos d
  have he := antichain_count_width3 hw
  omega


/-- A size-k antichain meets every fiber of a k-chain decomposition exactly once. -/
theorem ChainDecomposition.full_antichain_fiber_card {k : ℕ}
    (d : ChainDecomposition (V := V) k) {T : Finset V}
    (ht : Antichain T) (hc : T.card = k) (i : Fin k) :
    (T.filter (fun x => d.color x = i)).card = 1 := by
  classical
  have hinj := d.color_injective_on_antichain ht
  have hcard : (T.image d.color).card = k := (card_image_of_injOn hinj).trans hc
  have hfull : T.image d.color = univ := eq_of_subset_of_card_le (subset_univ _) (by simp [hcard])
  have hi : i ∈ T.image d.color := hfull.symm ▸ mem_univ i
  obtain ⟨x, hx, hxi⟩ := mem_image.mp hi
  apply card_eq_one.mpr
  refine ⟨x, ?_⟩
  ext y
  simp only [mem_filter, mem_singleton]
  constructor
  · rintro ⟨hy, hyi⟩
    exact hinj hy hx (hyi.trans hxi.symm)
  · rintro rfl
    exact ⟨hx, hxi⟩

/-- For two chains, each row counts every two-element antichain exactly once. -/
theorem two_chain_degree_eq_A2 (d : ChainDecomposition (V := V) 2) (i : Fin 2) :
    (∑ x ∈ d.part i, (Inc x).card) = Ak (V := V) 2 := by
  classical
  let F := (antichains (V := V)).filter (fun T => T.card = 2)
  calc
    (∑ x ∈ d.part i, (Inc x).card) = ∑ x ∈ d.part i, (F.filter (fun T => x ∈ T)).card := by
      apply sum_congr rfl
      intro x hx
      exact degree_pair_fiber x
    _ = ∑ T ∈ F, ∑ x ∈ d.part i, if x ∈ T then 1 else 0 := by
      simp only [card_filter]
      rw [sum_comm]
    _ = ∑ T ∈ F, (T.filter (fun x => d.color x = i)).card := by
      apply sum_congr rfl
      intro T hT
      have hsets : (d.part i).filter (fun x => x ∈ T) =
          T.filter (fun x => d.color x = i) := by
        ext x
        simp only [mem_filter, ChainDecomposition.mem_part]
        exact and_comm
      have hcard :
          ((d.part i).filter (fun x => x ∈ T)).card =
            (T.filter (fun x => d.color x = i)).card :=
        congrArg Finset.card hsets
      simpa only [sum_boole, Nat.cast_id] using hcard
    _ = ∑ T ∈ F, 1 := by
      apply sum_congr rfl
      intro T hT
      exact d.full_antichain_fiber_card (mem_antichains.mp (mem_filter.mp hT).1)
        (mem_filter.mp hT).2 i
    _ = Ak (V := V) 2 := by simp [Ak, F]

/-- Frozen target 4 conditional only on the explicit two-chain instance of Dilworth.
Empty fibers cover width zero and one without a nonemptiness assumption. -/
theorem target4_antichains36_two_chains (hw : WidthLE (V := V) 2) (hci : CI2 (V := V))
    (hn : Fintype.card V ≤ 15) (d : ChainDecomposition (V := V) 2) :
    totalAntichains (V := V) ≤ 36 := by
  classical
  have he := antichain_count_width2 hw
  have hrow0 := two_chain_degree_eq_A2 d 0
  have hrow1 := two_chain_degree_eq_A2 d 1
  by_cases h0 : (d.part 0).Nonempty
  · by_cases h1 : (d.part 1).Nonempty
    · have hb0 := chain_degree_bound hci (d.chain_fiber 0) h0
      have hb1 := chain_degree_bound hci (d.chain_fiber 1) h1
      change (∑ x ∈ d.part 0, (Inc x).card) + 2 ≤ Fintype.card V + (d.part 0).card at hb0
      change (∑ x ∈ d.part 1, (Inc x).card) + 2 ≤ Fintype.card V + (d.part 1).card at hb1
      rw [hrow0] at hb0
      rw [hrow1] at hb1
      have hp := d.parts_card
      simp only [Fin.sum_univ_two] at hp
      omega
    · have hempty := not_nonempty_iff_eq_empty.mp h1
      rw [hempty, sum_empty] at hrow1
      omega
  · have hempty := not_nonempty_iff_eq_empty.mp h0
    rw [hempty, sum_empty] at hrow0
    omega

end F6ConvexWindow

-- Print the exact target signatures and the transitive kernel trust dependencies.
#check @F6ConvexWindow.target1_triples
#check @F6ConvexWindow.target2_pairs_three_chains
#check @F6ConvexWindow.target3_antichains46_three_chains
#check @F6ConvexWindow.target4_antichains36_two_chains
#print axioms F6ConvexWindow.target1_triples
#print axioms F6ConvexWindow.target2_pairs_three_chains
#print axioms F6ConvexWindow.target3_antichains46_three_chains
#print axioms F6ConvexWindow.target4_antichains36_two_chains
#print axioms F6ConvexWindow.triple_ideals_nested
#print axioms F6ConvexWindow.triple_intersection_le_one
#print axioms F6ConvexWindow.no_reentry
#print axioms F6ConvexWindow.chain_adjacent_overlap
#print axioms F6ConvexWindow.degree_sum_eq_twice_A2
#print axioms F6ConvexWindow.antichain_count_width3
#print axioms F6ConvexWindow.antichain_count_width2
