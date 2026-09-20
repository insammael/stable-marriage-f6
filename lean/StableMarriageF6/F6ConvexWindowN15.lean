import StableMarriageF6.F6ConvexWindowFull

/-!
Implementation of the frozen HUMAN_PROOF_N15.md, §§1–5.
The finite family of actual triples is ordered by generated-ideal cardinality.
Maximal-element removal represents the successive prefixes of that order.
-/

noncomputable section
namespace F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

def IsTriple (T : Finset V) : Prop := Antichain T ∧ T.card = 3

def tripleFamily : Finset (Finset V) :=
  (antichains (V := V)).filter (fun T => T.card = 3)

@[simp] theorem mem_tripleFamily {T : Finset V} :
    T ∈ tripleFamily ↔ IsTriple T := by simp [tripleFamily, IsTriple]

@[simp] theorem card_tripleFamily : (tripleFamily (V := V)).card = Ak (V := V) 3 := rfl

def tripleUnion (F : Finset (Finset V)) : Finset V := F.biUnion id

@[simp] theorem mem_tripleUnion {F : Finset (Finset V)} {x : V} :
    x ∈ tripleUnion F ↔ ∃ T ∈ F, x ∈ T := by simp [tripleUnion]

/-- §2: an earlier-exclusive point is Below the later triple. -/
theorem earlier_exclusive_below (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {S T : Finset V} (ht : IsTriple T) (hST : ideal S ⊆ ideal T)
    {x : V} (hxS : x ∈ S) (hxT : x ∉ T) : Below T x := by
  rcases triple_split hw hci ht.1 ht.2 hxT with h | h
  · exact h
  · obtain ⟨t, htT, hxt⟩ := mem_ideal.mp (hST (subset_ideal S hxS))
    exact False.elim (above_not_le ht.1 h htT hxt)

/-- §2: a later-exclusive point is Above the earlier triple. -/
theorem later_exclusive_above (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {S T : Finset V} (hs : IsTriple S) (ht : IsTriple T)
    (hST : ideal S ⊆ ideal T) {y : V} (hyT : y ∈ T) (hyS : y ∉ S) : Above S y := by
  have hyI : y ∉ ideal S := by
    intro h
    obtain ⟨s, hsS, hys⟩ := mem_ideal.mp h
    obtain ⟨z, hzT, hsz⟩ := mem_ideal.mp (hST (subset_ideal S hsS))
    have hyz := ht.1 y hyT z hzT (hys.trans hsz)
    have hsy : s = y := le_antisymm (hyz.symm ▸ hsz) hys
    exact hyS (hsy ▸ hsS)
  exact (triple_split hw hci hs.1 hs.2 hyS).resolve_left
    (fun h => hyI (below_mem_ideal h))

/-- A Below point incomparable with one triple member is below the other two. -/
theorem below_lt_other_of_inc {T : Finset V} (ht : T.card = 3)
    {x s y : V} (hx : Below T x) (hs : s ∈ T) (hy : y ∈ T)
    (hsy : s ≠ y) (hxs : IncRel x s) : x < y := by
  classical
  by_contra hxy
  have hsub : T.filter (fun t => x < t) ⊆ (T.erase s).erase y := by
    intro t ht'
    obtain ⟨htT, hxt⟩ := mem_filter.mp ht'
    refine mem_erase.mpr ⟨?_, mem_erase.mpr ⟨?_, htT⟩⟩
    · intro h; exact hxy (h ▸ hxt)
    · intro h; exact hxs.1 (h ▸ hxt.le)
  have hc := card_le_card hsub
  rw [card_erase_of_mem (mem_erase.mpr ⟨hsy.symm, hy⟩), card_erase_of_mem hs, ht] at hc
  unfold Below at hx
  omega

/-- §3, nonempty transition: every old-only/new-only pair is comparable. -/
theorem overlapping_triples_comparable (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {S T : Finset V} (hs : IsTriple S) (ht : IsTriple T)
    (hST : ideal S ⊆ ideal T) (hover : (S ∩ T).Nonempty)
    {x y : V} (hxS : x ∈ S) (hxT : x ∉ T) (hyT : y ∈ T) (hyS : y ∉ S) : x < y := by
  obtain ⟨s, hsm⟩ := hover
  obtain ⟨hsS, hsT⟩ := mem_inter.mp hsm
  have hxs : x ≠ s := fun h => hxT (h.symm ▸ hsT)
  have hsy : s ≠ y := fun h => hyS (h ▸ hsS)
  exact below_lt_other_of_inc ht.2 (earlier_exclusive_below hw hci ht hST hxS hxT)
    hsT hyT hsy (antichain_inc hs.1 hxS hsS hxs)

/-- A no-triple case under width three has width at most two. -/
theorem width2_of_A3_zero (hw : WidthLE (V := V) 3) (hzero : Ak (V := V) 3 = 0) :
    WidthLE (V := V) 2 := by
  intro T ht
  have hc := hw T ht
  by_contra h
  have h3 : T.card = 3 := by omega
  have hm : T ∈ tripleFamily := mem_tripleFamily.mpr ⟨ht, h3⟩
  have hp := card_pos.mpr ⟨T, hm⟩
  rw [card_tripleFamily, hzero] at hp
  omega

/-- Actual two-element antichains induced on a vertex set. -/
def inducedPairs (U : Finset V) : Finset (Finset V) :=
  (U.powersetCard 2).filter Antichain

@[simp] theorem mem_inducedPairs {U P : Finset V} :
    P ∈ inducedPairs U ↔ P ⊆ U ∧ P.card = 2 ∧ Antichain P := by
  simp [inducedPairs, and_assoc]

def pairCount (U : Finset V) : ℕ := (inducedPairs U).card

theorem pairCount_univ : pairCount (univ : Finset V) = Ak (V := V) 2 := by
  classical
  unfold pairCount Ak
  congr 1
  ext P
  simp [inducedPairs, and_comm]

theorem pairCount_le_choose (U : Finset V) : pairCount U ≤ U.card.choose 2 := by
  exact (card_filter_le _ _).trans_eq (card_powersetCard 2 U)

theorem pairCount_triple {T : Finset V} (ht : IsTriple T) : pairCount T = 3 := by
  have he : inducedPairs T = T.powersetCard 2 := by
    apply filter_eq_self.mpr
    intro P hP
    have hsub := (mem_powersetCard.mp hP).1
    exact fun x hx y hy hxy => ht.1 x (hsub hx) y (hsub hy) hxy
  rw [pairCount, he, card_powersetCard, ht.2]
  decide

/-- Oriented cross pairs are represented by their actual unordered two-element sets. -/
def crossPairs (U W : Finset V) : Finset (Finset V) :=
  U.biUnion (fun x => (W.filter (IncRel x)).image (fun y => {x, y}))

def crossCount (U W : Finset V) : ℕ := ∑ x ∈ U, (W.filter (IncRel x)).card

theorem card_crossPairs_le (U W : Finset V) : (crossPairs U W).card ≤ crossCount U W := by
  classical
  apply (card_biUnion_le).trans
  exact sum_le_sum (fun x _ => card_image_le)

theorem crossPairs_mono {U U' W W' : Finset V} (hU : U ⊆ U') (hW : W ⊆ W') :
    crossPairs U W ⊆ crossPairs U' W' := by
  classical
  intro P hP
  obtain ⟨x, hx, hPx⟩ := mem_biUnion.mp hP
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hPx
  exact mem_biUnion.mpr ⟨x, hU hx, mem_image.mpr
    ⟨y, mem_filter.mpr ⟨hW (mem_filter.mp hy).1, (mem_filter.mp hy).2⟩, rfl⟩⟩

/-- Finite-set adapter for the three classes of pairs when a set is appended. -/
theorem inducedPairs_union_subset (U W : Finset V) :
    inducedPairs (U ∪ W) ⊆ inducedPairs U ∪ inducedPairs W ∪ crossPairs (U \ W) (W \ U) := by
  classical
  intro P hP
  obtain ⟨hsub, hc, ha⟩ := mem_inducedPairs.mp hP
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hc
  have haUW := hsub (mem_insert_self a {b})
  have hbUW := hsub (mem_insert_of_mem (mem_singleton_self b))
  have hi : IncRel a b := antichain_inc ha (by simp) (by simp) hab
  have addU (haU : a ∈ U) (hbU : b ∈ U) :
      {a, b} ∈ inducedPairs U ∪ inducedPairs W ∪ crossPairs (U \ W) (W \ U) :=
    mem_union_left _ (mem_union_left _ (mem_inducedPairs.mpr
      ⟨by simp only [insert_subset_iff, singleton_subset_iff]; exact ⟨haU, hbU⟩,
        by simp [hab], ha⟩))
  have addW (haW : a ∈ W) (hbW : b ∈ W) :
      {a, b} ∈ inducedPairs U ∪ inducedPairs W ∪ crossPairs (U \ W) (W \ U) :=
    mem_union_left _ (mem_union_right _ (mem_inducedPairs.mpr
      ⟨by simp only [insert_subset_iff, singleton_subset_iff]; exact ⟨haW, hbW⟩,
        by simp [hab], ha⟩))
  by_cases haU : a ∈ U
  · by_cases hbU : b ∈ U
    · exact addU haU hbU
    · have hbW := (mem_union.mp hbUW).resolve_left hbU
      by_cases haW : a ∈ W
      · exact addW haW hbW
      · exact mem_union_right _ (mem_biUnion.mpr ⟨a, mem_sdiff.mpr ⟨haU, haW⟩,
          mem_image.mpr ⟨b, mem_filter.mpr ⟨mem_sdiff.mpr ⟨hbW, hbU⟩, hi⟩, rfl⟩⟩)
  · have haW := (mem_union.mp haUW).resolve_left haU
    by_cases hbW : b ∈ W
    · exact addW haW hbW
    · have hbU := (mem_union.mp hbUW).resolve_right hbW
      exact mem_union_right _ (mem_biUnion.mpr ⟨b, mem_sdiff.mpr ⟨hbU, hbW⟩,
        mem_image.mpr ⟨a, mem_filter.mpr ⟨mem_sdiff.mpr ⟨haW, haU⟩, inc_symm hi⟩,
          pair_comm b a⟩⟩)

theorem pairCount_union_le (U W : Finset V) :
    pairCount (U ∪ W) ≤ pairCount U + pairCount W + (crossPairs (U \ W) (W \ U)).card := by
  have h := (card_le_card (inducedPairs_union_subset U W)).trans (card_union_le _ _)
  have h' := card_union_le (inducedPairs U) (inducedPairs W)
  unfold pairCount
  omega

/-- §3, empty transition: each row and each column has at most one cross neighbor. -/
theorem disjoint_triples_matching (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {S T : Finset V} (hs : IsTriple S) (ht : IsTriple T) (hd : Disjoint S T) :
    (∀ x ∈ S, (T.filter (IncRel x)).card ≤ 1) ∧
    (∀ y ∈ T, (S.filter (IncRel y)).card ≤ 1) := by
  constructor
  · intro x hx
    exact triple_incomparables_le_one hw hci ht.1 ht.2
      (fun h => disjoint_left.mp hd hx h)
  · intro y hy
    exact triple_incomparables_le_one hw hci hs.1 hs.2
      (fun h => disjoint_left.mp hd h hy)

theorem disjoint_triples_cross_le_three (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {S T : Finset V} (hs : IsTriple S) (ht : IsTriple T) (hd : Disjoint S T) :
    (crossPairs S T).card ≤ 3 := by
  have h := sum_le_sum (disjoint_triples_matching hw hci hs ht hd).1
  have hc : crossCount S T ≤ 3 := by simpa [crossCount, hs.2] using h
  exact (card_crossPairs_le S T).trans hc

/-- Last triple in the ideal-cardinality order; only finite maximization is used. -/
def lastTriple (F : Finset (Finset V)) (hn : F.Nonempty) : Finset V :=
  Classical.choose (exists_max_image F (fun T => (ideal T).card) hn)

theorem lastTriple_mem (F : Finset (Finset V)) (hn : F.Nonempty) : lastTriple F hn ∈ F :=
  (Classical.choose_spec (exists_max_image F (fun T => (ideal T).card) hn)).1

theorem lastTriple_max (F : Finset (Finset V)) (hn : F.Nonempty) :
    ∀ S ∈ F, (ideal S).card ≤ (ideal (lastTriple F hn)).card :=
  (Classical.choose_spec (exists_max_image F (fun T => (ideal T).card) hn)).2

/-- The actual finite ideal order, stored last-to-first for prefix recursion. -/
def triplesDescending (F : Finset (Finset V)) : List (Finset V) :=
  if hn : F.Nonempty then
    lastTriple F hn :: triplesDescending (F.erase (lastTriple F hn))
  else []
termination_by F.card
decreasing_by exact card_lt_card (erase_ssubset (lastTriple_mem F hn))

theorem triplesDescending_toFinset (F : Finset (Finset V)) :
    (triplesDescending F).toFinset = F := by
  classical
  induction F using Finset.strongInductionOn with
  | _ F ih =>
    by_cases hn : F.Nonempty
    · rw [triplesDescending, dif_pos hn, List.toFinset_cons,
        ih _ (erase_ssubset (lastTriple_mem F hn)), insert_erase (lastTriple_mem F hn)]
    · rw [triplesDescending, dif_neg hn]
      exact (not_nonempty_iff_eq_empty.mp hn).symm

theorem triplesDescending_strict (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (F : Finset (Finset V)) (hf : ∀ T ∈ F, IsTriple T) :
    (triplesDescending F).Pairwise (fun T S => ideal S ⊂ ideal T) := by
  classical
  induction F using Finset.strongInductionOn with
  | _ F ih =>
    by_cases hn : F.Nonempty
    · rw [triplesDescending, dif_pos hn, List.pairwise_cons]
      have hT := hf _ (lastTriple_mem F hn)
      constructor
      · intro S hS
        have hm : S ∈ F.erase (lastTriple F hn) := by
          rw [← triplesDescending_toFinset (F.erase (lastTriple F hn))]
          exact List.mem_toFinset.mpr hS
        have hs := hf S (mem_of_mem_erase hm)
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · exact ideal_subset_of_card_le hw hci hs.1 hT.1 hs.2 hT.2
            (lastTriple_max F hn S (mem_of_mem_erase hm))
        · intro he
          exact (mem_erase.mp hm).1 (ideal_injective hs.1 hT.1 he)
      · exact ih _ (erase_ssubset (lastTriple_mem F hn))
          (fun S hS => hf S (mem_of_mem_erase hS))
    · rw [triplesDescending, dif_neg hn]
      simp

/-- §1: all actual triple antichains, strictly ordered by their generated ideals. -/
theorem ordered_actual_triples (hw : WidthLE (V := V) 3) (hci : CI2 (V := V)) :
    ∃ L : List (Finset V), L.toFinset = tripleFamily ∧
      L.Pairwise (fun S T => ideal S ⊂ ideal T) := by
  refine ⟨(triplesDescending (tripleFamily (V := V))).reverse, ?_, ?_⟩
  · rw [List.toFinset_reverse, triplesDescending_toFinset]
  · exact (triplesDescending_strict hw hci tripleFamily
      (fun T hT => mem_tripleFamily.mp hT)).reverse

/-- Counts empty-overlap transitions while removing successive last triples.
The first triple has no transition.  No-reentry identifies each prefix overlap
with the overlap with its immediately preceding triple. -/
def emptyTransitions (F : Finset (Finset V)) : ℕ :=
  if hn : F.Nonempty then
    emptyTransitions (F.erase (lastTriple F hn)) +
      if (F.erase (lastTriple F hn)).Nonempty ∧
        Disjoint (tripleUnion (F.erase (lastTriple F hn))) (lastTriple F hn) then 1 else 0
  else 0
termination_by F.card
decreasing_by exact card_lt_card (erase_ssubset (lastTriple_mem F hn))

/-- The previous triple contains every vertex of the new triple already in the prefix. -/
theorem prefix_overlap_eq_last (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {G : Finset (Finset V)} (hg : ∀ R ∈ G, IsTriple R) {S T : Finset V}
    (hSG : S ∈ G) (hSmax : ∀ R ∈ G, (ideal R).card ≤ (ideal S).card)
    (ht : IsTriple T) (hST : ideal S ⊆ ideal T) :
    T ∩ tripleUnion G = T ∩ S := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨hxT, hxU⟩ := mem_inter.mp hx
    obtain ⟨R, hRG, hxR⟩ := mem_tripleUnion.mp hxU
    have hr := hg R hRG
    have hs := hg S hSG
    have hRS := ideal_subset_of_card_le hw hci hr.1 hs.1 hr.2 hs.2 (hSmax R hRG)
    exact mem_inter.mpr ⟨hxT, no_reentry ht.1 hRS hST hxR hxT⟩
  · intro x hx
    obtain ⟨hxT, hxS⟩ := mem_inter.mp hx
    exact mem_inter.mpr ⟨hxT, mem_tripleUnion.mpr ⟨S, hSG, hxS⟩⟩

/-- A vertex in a still-earlier triple cannot create an extra new cross edge. -/
theorem earlier_prefix_lt_new (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {G : Finset (Finset V)} (hg : ∀ R ∈ G, IsTriple R) {S T : Finset V}
    (hSG : S ∈ G) (hSmax : ∀ R ∈ G, (ideal R).card ≤ (ideal S).card)
    (ht : IsTriple T) (hST : ideal S ⊆ ideal T) {x y : V}
    (hx : x ∈ tripleUnion G) (hxS : x ∉ S) (hyT : y ∈ T) (hyS : y ∉ S) : x < y := by
  obtain ⟨R, hRG, hxR⟩ := mem_tripleUnion.mp hx
  have hr := hg R hRG
  have hs := hg S hSG
  have hRS := ideal_subset_of_card_le hw hci hr.1 hs.1 hr.2 hs.2 (hSmax R hRG)
  exact below_lt_above hs.2 (earlier_exclusive_below hw hci hs hRS hxR hxS)
    (later_exclusive_above hw hci hs ht hST hyT hyS)

/-- §4: the Above triples form an initial segment and Below triples a final segment. -/
theorem split_monotone (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {S T : Finset V} (hs : IsTriple S) (ht : IsTriple T)
    (hST : ideal S ⊆ ideal T) {x : V} (hxS : x ∉ S) (hxT : x ∉ T) :
    (Above T x → Above S x) ∧ (Below S x → Below T x) := by
  have hincompat : Below S x → Above T x → False := by
    intro hl hu
    obtain ⟨t, htT, hxt⟩ := mem_ideal.mp (hST (below_mem_ideal hl))
    exact above_not_le ht.1 hu htT hxt
  constructor
  · intro hu
    exact (triple_split hw hci hs.1 hs.2 hxS).resolve_left (fun hl => hincompat hl hu)
  · intro hl
    exact (triple_split hw hci ht.1 ht.2 hxT).resolve_right (hincompat hl)

/-- All incomparable neighbors in an Above prefix belong to its last triple. -/
theorem above_prefix_neighbors_le_one (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (F : Finset (Finset V)) (hf : ∀ T ∈ F, IsTriple T) {x : V}
    (hx : x ∉ tripleUnion F) (ha : ∀ T ∈ F, Above T x) :
    ((tripleUnion F).filter (IncRel x)).card ≤ 1 := by
  classical
  by_cases hn : F.Nonempty
  · obtain ⟨S, hSF, hSmax⟩ := exists_max_image F (fun T => (ideal T).card) hn
    have hs := hf S hSF
    have hxs : x ∉ S := fun h => hx (mem_tripleUnion.mpr ⟨S, hSF, h⟩)
    apply (card_le_card (show (tripleUnion F).filter (IncRel x) ⊆ S.filter (IncRel x) from ?_)).trans
      (triple_incomparables_le_one hw hci hs.1 hs.2 hxs)
    intro y hy
    obtain ⟨hyU, hxy⟩ := mem_filter.mp hy
    refine mem_filter.mpr ⟨?_, hxy⟩
    by_contra hyS
    obtain ⟨R, hRF, hyR⟩ := mem_tripleUnion.mp hyU
    have hr := hf R hRF
    have hRS := ideal_subset_of_card_le hw hci hr.1 hs.1 hr.2 hs.2 (hSmax R hRF)
    exact hxy.2 (below_lt_above hs.2
      (earlier_exclusive_below hw hci hs hRS hyR hyS) (ha S hSF)).le
  · rw [not_nonempty_iff_eq_empty.mp hn]
    simp [tripleUnion]

/-- All incomparable neighbors in a Below suffix belong to its first triple. -/
theorem below_suffix_neighbors_le_one (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (F : Finset (Finset V)) (hf : ∀ T ∈ F, IsTriple T) {x : V}
    (hx : x ∉ tripleUnion F) (hb : ∀ T ∈ F, Below T x) :
    ((tripleUnion F).filter (IncRel x)).card ≤ 1 := by
  classical
  by_cases hn : F.Nonempty
  · obtain ⟨S, hSF, hSmin⟩ := exists_min_image F (fun T => (ideal T).card) hn
    have hs := hf S hSF
    have hxs : x ∉ S := fun h => hx (mem_tripleUnion.mpr ⟨S, hSF, h⟩)
    apply (card_le_card (show (tripleUnion F).filter (IncRel x) ⊆ S.filter (IncRel x) from ?_)).trans
      (triple_incomparables_le_one hw hci hs.1 hs.2 hxs)
    intro y hy
    obtain ⟨hyU, hxy⟩ := mem_filter.mp hy
    refine mem_filter.mpr ⟨?_, hxy⟩
    by_contra hyS
    obtain ⟨R, hRF, hyR⟩ := mem_tripleUnion.mp hyU
    have hr := hf R hRF
    have hSR := ideal_subset_of_card_le hw hci hs.1 hr.1 hs.2 hr.2 (hSmin R hRF)
    exact hxy.1 (below_lt_above hs.2 (hb S hSF)
      (later_exclusive_above hw hci hs hr hSR hyR hyS)).le
  · rw [not_nonempty_iff_eq_empty.mp hn]
    simp [tripleUnion]

/-- §4, equation (4): any vertex outside the triple union has at most two neighbors in it. -/
theorem outsider_neighbors_le_two (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (F : Finset (Finset V)) (hf : ∀ T ∈ F, IsTriple T) {x : V}
    (hx : x ∉ tripleUnion F) : ((tripleUnion F).filter (IncRel x)).card ≤ 2 := by
  classical
  let A := F.filter (fun T => Above T x)
  let B := F.filter (fun T => Below T x)
  have hxF (G : Finset (Finset V)) (hG : G ⊆ F) : x ∉ tripleUnion G := by
    intro h
    obtain ⟨T, hTG, hxT⟩ := mem_tripleUnion.mp h
    exact hx (mem_tripleUnion.mpr ⟨T, hG hTG, hxT⟩)
  have hA := above_prefix_neighbors_le_one hw hci A
    (fun T hT => hf T (mem_filter.mp hT).1) (hxF A (filter_subset _ _))
    (fun T hT => (mem_filter.mp hT).2)
  have hB := below_suffix_neighbors_le_one hw hci B
    (fun T hT => hf T (mem_filter.mp hT).1) (hxF B (filter_subset _ _))
    (fun T hT => (mem_filter.mp hT).2)
  have hcover : (tripleUnion F).filter (IncRel x) ⊆
      (tripleUnion A).filter (IncRel x) ∪ (tripleUnion B).filter (IncRel x) := by
    intro y hy
    obtain ⟨hyU, hxy⟩ := mem_filter.mp hy
    obtain ⟨T, hTF, hyT⟩ := mem_tripleUnion.mp hyU
    have ht := hf T hTF
    have hxT : x ∉ T := fun h => hx (mem_tripleUnion.mpr ⟨T, hTF, h⟩)
    rcases triple_split hw hci ht.1 ht.2 hxT with hl | hu
    · exact mem_union_right _ (mem_filter.mpr
        ⟨mem_tripleUnion.mpr ⟨T, mem_filter.mpr ⟨hTF, hl⟩, hyT⟩, hxy⟩)
    · exact mem_union_left _ (mem_filter.mpr
        ⟨mem_tripleUnion.mpr ⟨T, mem_filter.mpr ⟨hTF, hu⟩, hyT⟩, hxy⟩)
  have hc := (card_le_card hcover).trans (card_union_le _ _)
  omega

/-- Localization of every new cross pair to the immediately preceding triple. -/
theorem prefix_crossPairs_subset (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {G : Finset (Finset V)} (hg : ∀ R ∈ G, IsTriple R) {S T : Finset V}
    (hSG : S ∈ G) (hSmax : ∀ R ∈ G, (ideal R).card ≤ (ideal S).card)
    (ht : IsTriple T) (hST : ideal S ⊆ ideal T) :
    crossPairs (tripleUnion G \ T) (T \ tripleUnion G) ⊆ crossPairs S T := by
  classical
  intro P hP
  obtain ⟨x, hx, hPx⟩ := mem_biUnion.mp hP
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hPx
  obtain ⟨hy, hxy⟩ := mem_filter.mp hy
  have hyS : y ∉ S := fun h => (mem_sdiff.mp hy).2 (mem_tripleUnion.mpr ⟨S, hSG, h⟩)
  have hxS : x ∈ S := by
    by_contra h
    exact hxy.1 (earlier_prefix_lt_new hw hci hg hSG hSmax ht hST
      (mem_sdiff.mp hx).1 h (mem_sdiff.mp hy).1 hyS).le
  exact mem_biUnion.mpr ⟨x, hxS,
    mem_image.mpr ⟨y, mem_filter.mpr ⟨(mem_sdiff.mp hy).1, hxy⟩, rfl⟩⟩

/-- §3, one-vertex overlap: there are no old-only/new-only incomparable pairs. -/
theorem overlapping_prefix_crossPairs_empty (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {G : Finset (Finset V)} (hg : ∀ R ∈ G, IsTriple R) {S T : Finset V}
    (hSG : S ∈ G) (hSmax : ∀ R ∈ G, (ideal R).card ≤ (ideal S).card)
    (ht : IsTriple T) (hST : ideal S ⊆ ideal T) (hover : (S ∩ T).Nonempty) :
    crossPairs (tripleUnion G \ T) (T \ tripleUnion G) = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro P hP
  obtain ⟨x, hx, hPx⟩ := mem_biUnion.mp hP
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hPx
  obtain ⟨hy, hxy⟩ := mem_filter.mp hy
  have hyS : y ∉ S := fun h => (mem_sdiff.mp hy).2 (mem_tripleUnion.mpr ⟨S, hSG, h⟩)
  by_cases hxS : x ∈ S
  · exact hxy.1 (overlapping_triples_comparable hw hci (hg S hSG) ht hST hover
      hxS (mem_sdiff.mp hx).2 (mem_sdiff.mp hy).1 hyS).le
  · exact hxy.1 (earlier_prefix_lt_new hw hci hg hSG hSmax ht hST
      (mem_sdiff.mp hx).1 hxS (mem_sdiff.mp hy).1 hyS).le

/-- §3: a new triple adds at most three internal pairs and, only for an empty
transition, at most three cross pairs. -/
theorem prefix_pairCount_step (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {G : Finset (Finset V)} (hg : ∀ R ∈ G, IsTriple R) {S T : Finset V}
    (hSG : S ∈ G) (hSmax : ∀ R ∈ G, (ideal R).card ≤ (ideal S).card)
    (ht : IsTriple T) (hST : ideal S ⊆ ideal T) :
    pairCount (tripleUnion G ∪ T) ≤ pairCount (tripleUnion G) + 3 +
      if Disjoint (tripleUnion G) T then 3 else 0 := by
  have hs := hg S hSG
  have hbase := pairCount_union_le (tripleUnion G) T
  rw [pairCount_triple ht] at hbase
  by_cases hd : Disjoint (tripleUnion G) T
  · rw [if_pos hd]
    have hSTd : Disjoint S T := disjoint_left.mpr
      (fun x hxS hxT => disjoint_left.mp hd (mem_tripleUnion.mpr ⟨S, hSG, hxS⟩) hxT)
    have hc := (card_le_card (prefix_crossPairs_subset hw hci hg hSG hSmax ht hST)).trans
      (disjoint_triples_cross_le_three hw hci hs ht hSTd)
    omega
  · rw [if_neg hd]
    have hover : (S ∩ T).Nonempty := by
      by_contra hn
      apply hd
      apply disjoint_iff_inter_eq_empty.mpr
      rw [inter_comm, prefix_overlap_eq_last hw hci hg hSG hSmax ht hST, inter_comm]
      exact not_nonempty_iff_eq_empty.mp hn
    rw [overlapping_prefix_crossPairs_empty hw hci hg hSG hSmax ht hST hover, card_empty] at hbase
    omega

/-- No-reentry and intersection at most one control the new vertices at each step. -/
theorem prefix_intersection_le_one (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {G : Finset (Finset V)} (hg : ∀ R ∈ G, IsTriple R) {S T : Finset V}
    (hSG : S ∈ G) (hSmax : ∀ R ∈ G, (ideal R).card ≤ (ideal S).card)
    (ht : IsTriple T) (hST : ideal S ⊆ ideal T) (hTG : T ∉ G) :
    (tripleUnion G ∩ T).card ≤ 1 := by
  rw [inter_comm, prefix_overlap_eq_last hw hci hg hSG hSmax ht hST]
  exact triple_intersection_le_one hw hci ht.1 (hg S hSG).1 ht.2 (hg S hSG).2
    (fun h => hTG (h.symm ▸ hSG))

/-- §1: every successive triple introduces exactly two or three new vertices. -/
theorem successive_new_vertices (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {G : Finset (Finset V)} (hg : ∀ R ∈ G, IsTriple R) {S T : Finset V}
    (hSG : S ∈ G) (hSmax : ∀ R ∈ G, (ideal R).card ≤ (ideal S).card)
    (ht : IsTriple T) (hST : ideal S ⊆ ideal T) (hTG : T ∉ G) :
    (T \ tripleUnion G).card = 2 ∨ (T \ tripleUnion G).card = 3 := by
  have hi := prefix_intersection_le_one hw hci hg hSG hSmax ht hST hTG
  have hc := card_sdiff_add_card_inter T (tripleUnion G)
  rw [inter_comm T, ht.2] at hc
  omega

/-- Exact union growth, with the empty-transition indicator displayed. -/
theorem union_card_step {U T : Finset V} (ht : T.card = 3) (hi : (U ∩ T).card ≤ 1) :
    (U ∪ T).card = U.card + 2 + if Disjoint U T then 1 else 0 := by
  have hc := card_union_add_card_inter U T
  by_cases hd : Disjoint U T
  · rw [if_pos hd]
    rw [disjoint_iff_inter_eq_empty.mp hd, card_empty, ht] at hc
    omega
  · rw [if_neg hd]
    have hp : 0 < (U ∩ T).card := by
      apply Nat.pos_of_ne_zero
      intro hz
      exact hd (disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp hz))
    omega

/-- §1–§3, equations (1) and (2), by induction over the ideal-ordered prefixes. -/
theorem triple_union_counts (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (F : Finset (Finset V)) (hf : ∀ T ∈ F, IsTriple T) (hn : F.Nonempty) :
    (tripleUnion F).card = 2 * F.card + 1 + emptyTransitions F ∧
    pairCount (tripleUnion F) ≤ 3 * F.card + 3 * emptyTransitions F := by
  classical
  induction F using Finset.strongInductionOn with
  | _ F ih =>
    let T := lastTriple F hn
    have hTF : T ∈ F := lastTriple_mem F hn
    have hTmax : ∀ R ∈ F, (ideal R).card ≤ (ideal T).card := lastTriple_max F hn
    have ht := hf T hTF
    let G := F.erase T
    have hsub : G ⊆ F := erase_subset _ _
    have hg : ∀ R ∈ G, IsTriple R := fun R hR => hf R (hsub hR)
    have hTG : T ∉ G := notMem_erase _ _
    have hF : F = insert T G := (insert_erase hTF).symm
    have hFc : F.card = G.card + 1 := by rw [hF, card_insert_of_notMem hTG]
    have hU : tripleUnion F = tripleUnion G ∪ T := by
      rw [hF]
      simp [tripleUnion, union_comm]
    have hm : emptyTransitions F = emptyTransitions G +
        if G.Nonempty ∧ Disjoint (tripleUnion G) T then 1 else 0 := by
      rw [emptyTransitions, dif_pos hn]
    by_cases hGn : G.Nonempty
    · have ihG := ih G (erase_ssubset hTF) hg hGn
      let S := lastTriple G hGn
      have hSG : S ∈ G := lastTriple_mem G hGn
      have hSmax : ∀ R ∈ G, (ideal R).card ≤ (ideal S).card := lastTriple_max G hGn
      have hs := hg S hSG
      have hST := ideal_subset_of_card_le hw hci hs.1 ht.1 hs.2 ht.2 (hTmax S (hsub hSG))
      have hi := prefix_intersection_le_one hw hci hg hSG hSmax ht hST hTG
      have huc := union_card_step ht.2 hi
      have hec := prefix_pairCount_step hw hci hg hSG hSmax ht hST
      simp only [hGn, true_and] at hm
      rw [hU]
      by_cases hd : Disjoint (tripleUnion G) T
      · simp only [if_pos hd] at hm huc hec
        constructor <;> omega
      · simp only [if_neg hd] at hm huc hec
        constructor <;> omega
    · have hGe : G = ∅ := not_nonempty_iff_eq_empty.mp hGn
      have hmG : emptyTransitions G = 0 := by
        rw [hGe, emptyTransitions]
        simp
      have hmF : emptyTransitions F = 0 := by simp [hGn, hmG] at hm; exact hm
      have hFc' : F.card = 1 := by simpa [hGe] using hFc
      have hU' : tripleUnion F = T := by simpa [hGe, tripleUnion] using hU
      rw [hU', hFc', hmF, ht.2, pairCount_triple ht]
      omega

/-- The recursive counter is the count of disjoint consecutive triples in the
same ideal order: at a noninitial step its test is exactly the predecessor test. -/
theorem emptyTransitions_step (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (F : Finset (Finset V)) (hf : ∀ T ∈ F, IsTriple T) (hn : F.Nonempty)
    (hGn : (F.erase (lastTriple F hn)).Nonempty) :
    emptyTransitions F = emptyTransitions (F.erase (lastTriple F hn)) +
      if Disjoint (lastTriple (F.erase (lastTriple F hn)) hGn) (lastTriple F hn) then 1 else 0 := by
  let T := lastTriple F hn
  let G := F.erase T
  let S := lastTriple G hGn
  have hTF : T ∈ F := lastTriple_mem F hn
  have hSG : S ∈ G := lastTriple_mem G hGn
  have hg : ∀ R ∈ G, IsTriple R := fun R hR => hf R (mem_of_mem_erase hR)
  have hs := hg S hSG
  have ht := hf T hTF
  have hST := ideal_subset_of_card_le hw hci hs.1 ht.1 hs.2 ht.2
    (lastTriple_max F hn S (mem_of_mem_erase hSG))
  have he := prefix_overlap_eq_last hw hci hg hSG (lastTriple_max G hGn) ht hST
  have hd : Disjoint (tripleUnion G) T ↔ Disjoint S T := by
    simp only [disjoint_iff_inter_eq_empty]
    rw [inter_comm (tripleUnion G), he, inter_comm T]
  rw [emptyTransitions, dif_pos hn]
  change emptyTransitions G + (if G.Nonempty ∧ Disjoint (tripleUnion G) T then 1 else 0) =
    emptyTransitions G + (if Disjoint S T then 1 else 0)
  have hGn' : G.Nonempty := hGn
  simp only [hGn', true_and, hd]

/-- §5: partition the actual incomparable pairs into union, cross, and outsider pairs. -/
theorem all_pairs_le_union_outsiders (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (F : Finset (Finset V)) (hf : ∀ T ∈ F, IsTriple T) :
    Ak (V := V) 2 ≤ pairCount (tripleUnion F) +
      2 * (univ \ tripleUnion F).card + (univ \ tripleUnion F).card.choose 2 := by
  classical
  let U := tripleUnion F
  let Q := (univ : Finset V) \ U
  have hcover : Q ∪ U = univ := by
    ext x
    by_cases hx : x ∈ U <;> simp [Q, hx]
  have hb := pairCount_union_le Q U
  rw [hcover, pairCount_univ] at hb
  have hQ := pairCount_le_choose Q
  have hcross := (card_le_card (crossPairs_mono (sdiff_subset : Q \ U ⊆ Q)
    (sdiff_subset : U \ Q ⊆ U))).trans (card_crossPairs_le Q U)
  have hrows := sum_le_sum (s := Q) (fun x hx => outsider_neighbors_le_two hw hci F hf
    (show x ∉ tripleUnion F from (mem_sdiff.mp hx).2))
  have hc : crossCount Q U ≤ 2 * Q.card := by
    simpa [crossCount, U, Nat.mul_comm] using hrows
  change Ak (V := V) 2 ≤ pairCount U + 2 * Q.card + Q.card.choose 2
  omega

/-- The three numerical outsider cases in §5; this is only bounded arithmetic. -/
theorem n15_large_triple_arithmetic (t m q e : ℕ) (ht : 6 ≤ t) (htop : 2 * t + 1 ≤ 15)
    (hn : 2 * t + 1 + m + q = 15)
    (he : e ≤ 3 * t + 3 * m + 2 * q + q.choose 2) : e + t ≤ 30 := by
  have hcases : t = 6 ∨ t = 7 := by omega
  rcases hcases with rfl | rfl
  · have hq : q = 0 ∨ q = 1 ∨ q = 2 := by omega
    rcases hq with rfl | rfl | rfl <;> norm_num at he <;> omega
  · have hm : m = 0 := by omega
    have hq : q = 0 := by omega
    simp only [hm, hq] at he
    norm_num at he
    omega

/-- §5, equation (7): the stronger bound when n=15 and there are at least six triples. -/
theorem totalAntichains_le_46_of_six_triples (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (hn : Fintype.card V = 15) (ht : 6 ≤ Ak (V := V) 3) : totalAntichains (V := V) ≤ 46 := by
  classical
  let F := tripleFamily (V := V)
  let U := tripleUnion F
  let Q := (univ : Finset V) \ U
  have hf : ∀ T ∈ F, IsTriple T := fun T hT => mem_tripleFamily.mp hT
  have hFc : F.card = Ak (V := V) 3 := card_tripleFamily
  have hFn : F.Nonempty := card_pos.mp (by omega)
  have htop := F6ConvexWindowFull.T1 hw hci (show 0 < Ak (V := V) 3 by omega)
  rw [hn] at htop
  obtain ⟨huc, hec⟩ := triple_union_counts hw hci F hf hFn
  have hpart : U.card + Q.card = Fintype.card V := by
    have h := card_sdiff_add_card_eq_card (subset_univ U)
    simpa [Q, Nat.add_comm] using h
  have hsize : 2 * Ak (V := V) 3 + 1 + emptyTransitions F + Q.card = 15 := by
    change U.card = 2 * F.card + 1 + emptyTransitions F at huc
    omega
  have he := all_pairs_le_union_outsiders hw hci F hf
  have he' : Ak (V := V) 2 ≤ 3 * Ak (V := V) 3 + 3 * emptyTransitions F +
      2 * Q.card + Q.card.choose 2 := by
    change Ak (V := V) 2 ≤ pairCount U + 2 * Q.card + Q.card.choose 2 at he
    change pairCount U ≤ 3 * F.card + 3 * emptyTransitions F at hec
    omega
  have htrade := n15_large_triple_arithmetic _ _ _ _ ht htop hsize he'
  have hcount := antichain_count_width3 hw
  omega

/-- The frozen N15 theorem, under the unchanged finite-poset definitions. -/
theorem totalAntichains_le_48 (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (hn : Fintype.card V ≤ 15) : totalAntichains (V := V) ≤ 48 := by
  by_cases hz : Ak (V := V) 3 = 0
  · exact (F6ConvexWindowFull.T4 (width2_of_A3_zero hw hz) hci hn).trans (by omega)
  · have hpos : 0 < Ak (V := V) 3 := Nat.pos_of_ne_zero hz
    by_cases hn14 : Fintype.card V ≤ 14
    · exact (F6ConvexWindowFull.T3 hw hci hpos hn14).trans (by omega)
    · have hn15 : Fintype.card V = 15 := by omega
      by_cases ht : 6 ≤ Ak (V := V) 3
      · exact (totalAntichains_le_46_of_six_triples hw hci hn15 ht).trans (by omega)
      · have hpairs := F6ConvexWindowFull.T2 hw hci hpos
        have hcount := antichain_count_width3 hw
        omega

end F6ConvexWindow

#check @F6ConvexWindow.totalAntichains_le_48
#print axioms F6ConvexWindow.ordered_actual_triples
#print axioms F6ConvexWindow.earlier_exclusive_below
#print axioms F6ConvexWindow.later_exclusive_above
#print axioms F6ConvexWindow.successive_new_vertices
#print axioms F6ConvexWindow.emptyTransitions_step
#print axioms F6ConvexWindow.overlapping_prefix_crossPairs_empty
#print axioms F6ConvexWindow.disjoint_triples_matching
#print axioms F6ConvexWindow.disjoint_triples_cross_le_three
#print axioms F6ConvexWindow.prefix_pairCount_step
#print axioms F6ConvexWindow.triple_union_counts
#print axioms F6ConvexWindow.outsider_neighbors_le_two
#print axioms F6ConvexWindow.all_pairs_le_union_outsiders
#print axioms F6ConvexWindow.n15_large_triple_arithmetic
#print axioms F6ConvexWindow.totalAntichains_le_46_of_six_triples
#print axioms F6ConvexWindow.width2_of_A3_zero
#print axioms F6ConvexWindow.totalAntichains_le_48
