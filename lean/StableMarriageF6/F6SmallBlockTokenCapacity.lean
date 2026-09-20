import Mathlib

/-!
Abstract token-run capacities. Implements only the frozen proof in
research/milestones/F6_SMALL_BLOCK_TOKEN_CAPACITY_05/HUMAN_PROOF_SMALL_BLOCK.md.
-/

open scoped BigOperators
open Classical
noncomputable section

namespace F6SmallBlockTokenCapacity

variable {B W : Type*} [Fintype B] [Fintype W] {q : ℕ}

/-- The fixed token pool is encoded by equivalences onto the same type `W`. -/
structure TokenRun (B W : Type*) [Fintype B] [Fintype W] (q : ℕ) where
  support : Fin q → Finset B
  state : Fin (q + 1) → (B ≃ W)
  rank : B → W → ℕ
  HMIN : ∀ i, 2 ≤ (support i).card
  HOUT : ∀ i b, b ∉ support i → state i.castSucc b = state i.succ b
  HWORSE : ∀ i b, b ∈ support i →
    rank b (state i.castSucc b) < rank b (state i.succ b)

namespace TokenRun

variable (R : TokenRun B W q)

noncomputable def participationSteps (b : B) : Finset (Fin q) := by
  classical
  exact Finset.univ.filter (fun i => b ∈ R.support i)

@[simp] theorem mem_participationSteps (b : B) (i : Fin q) :
    i ∈ R.participationSteps b ↔ b ∈ R.support i := by
  classical
  simp [participationSteps]

/-- Ranks never decrease, including the transitions outside the support. -/
theorem rank_monotone (b : B) : Monotone (fun t => R.rank b (R.state t b)) := by
  classical
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  by_cases h : b ∈ R.support i
  · exact (R.HWORSE i b h).le
  · rw [R.HOUT i b h]

theorem rank_after_lt (b : B) {i j : Fin q} (hij : i < j)
    (hj : b ∈ R.support j) :
    R.rank b (R.state i.succ b) < R.rank b (R.state j.succ b) := by
  apply lt_of_le_of_lt (R.rank_monotone b (show i.succ ≤ j.castSucc from ?_))
    (R.HWORSE j b hj)
  change i.val + 1 ≤ j.val
  exact hij

theorem initial_rank_lt_after (b : B) {i : Fin q} (hi : b ∈ R.support i) :
    R.rank b (R.state 0 b) < R.rank b (R.state i.succ b) :=
  lt_of_le_of_lt (R.rank_monotone b (Fin.zero_le _)) (R.HWORSE i b hi)

/-- Lemma A: post-participation tokens inject into `W` minus the initial token. -/
theorem participation_count (b : B) :
    (R.participationSteps b).card ≤ Fintype.card B - 1 := by
  classical
  have hinj : Set.InjOn (fun i : Fin q => R.state i.succ b)
      (R.participationSteps b : Set (Fin q)) := by
    intro i hi j hj heq
    change R.state i.succ b = R.state j.succ b at heq
    have hi' : b ∈ R.support i := (R.mem_participationSteps b i).mp hi
    have hj' : b ∈ R.support j := (R.mem_participationSteps b j).mp hj
    rcases lt_trichotomy i j with hij | hij | hij
    · have h := R.rank_after_lt b hij hj'
      rw [heq] at h
      exact (lt_irrefl _ h).elim
    · exact hij
    · have h := R.rank_after_lt b hij hi'
      rw [heq] at h
      exact (lt_irrefl _ h).elim
  have hmap : Set.MapsTo (fun i : Fin q => R.state i.succ b)
      (R.participationSteps b : Set (Fin q))
      ((Finset.univ.erase (R.state 0 b) : Finset W) : Set W) := by
    intro i hi
    have h := R.initial_rank_lt_after b ((R.mem_participationSteps b i).mp hi)
    have hne : R.state i.succ b ≠ R.state 0 b := by
      intro heq
      rw [heq] at h
      exact lt_irrefl _ h
    simpa using hne
  have hc := Finset.card_le_card_of_injOn (fun i : Fin q => R.state i.succ b) hmap hinj
  have hBW : Fintype.card B = Fintype.card W := Fintype.card_congr (R.state 0)
  simpa [Finset.card_erase_of_mem, hBW] using hc

/-- Double counting incidences, for any selected set of steps. -/
theorem incidence_sum (T : Finset (Fin q)) :
    (∑ i ∈ T, (R.support i).card) =
      ∑ b : B, (T.filter (fun i => b ∈ R.support i)).card := by
  classical
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem selected_participation_le (T : Finset (Fin q)) (b : B) :
    (T.filter (fun i => b ∈ R.support i)).card ≤ Fintype.card B - 1 := by
  classical
  apply le_trans (Finset.card_le_card ?_) (R.participation_count b)
  intro i hi
  exact (R.mem_participationSteps b i).mpr (Finset.mem_filter.mp hi).2

/-- Restriction to the first `n` transitions, with no change of tokens or ranks. -/
def firstSteps (n : ℕ) (h : n ≤ q) : TokenRun B W n where
  support i := R.support (i.castLE h)
  state t := R.state (t.castLE (Nat.add_le_add_right h 1))
  rank := R.rank
  HMIN i := R.HMIN (i.castLE h)
  HOUT i b hb := R.HOUT (i.castLE h) b hb
  HWORSE i b hb := R.HWORSE (i.castLE h) b hb

/-- The two sides of the incidence squeeze used in the frozen proof. -/
theorem incidence_bounds :
    2 * q ≤ (∑ i : Fin q, (R.support i).card) ∧
    (∑ i : Fin q, (R.support i).card) ≤ Fintype.card B * (Fintype.card B - 1) := by
  classical
  constructor
  · have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin q)))
      (fun i _ => R.HMIN i)
    simpa [Nat.mul_comm] using h
  · rw [R.incidence_sum]
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset B))
      (fun b _ => R.participation_count b)
    simpa [participationSteps] using h

/-- Two supports in a two-site run would both be the entire site type. -/
theorem TWO_SITE_CAPACITY (R : TokenRun B W q) (hB : Fintype.card B ≤ 2) : q ≤ 1 := by
  classical
  by_contra hq
  have htwo : 2 ≤ q := by omega
  let P := R.firstSteps 2 htwo
  have hfull (i : Fin 2) : P.support i = Finset.univ := by
    apply Finset.eq_univ_of_card
    have hlo := P.HMIN i
    have hhi := (P.support i).card_le_univ
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < 2) (P.HMIN 0))
  have hc := P.participation_count b
  have heq : (P.participationSteps b).card = 2 := by
    simp [participationSteps, hfull]
  omega

/-- Incidence equality for a run consisting of exactly three transitions. -/
theorem three_incidence_equality (P : TokenRun B W 3) (hB : Fintype.card B ≤ 3) :
    Fintype.card B = 3 ∧
    (∀ i : Fin 3, (P.support i).card = 2) ∧
    (∀ b : B, (P.participationSteps b).card = 2) := by
  classical
  have hcount (b : B) : (P.participationSteps b).card ≤ 2 := by
    have h := P.participation_count b
    omega
  have hlo : 6 ≤ ∑ i : Fin 3, (P.support i).card := P.incidence_bounds.1
  have hhi : (∑ i : Fin 3, (P.support i).card) ≤ Fintype.card B * 2 := by
    rw [P.incidence_sum]
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset B)) (fun b _ => hcount b)
    simpa [participationSteps] using h
  have hcard : Fintype.card B = 3 := by omega
  have htotal : (∑ i : Fin 3, (P.support i).card) = 6 := by omega
  refine ⟨hcard, ?_, ?_⟩
  · have heq : (∑ _i : Fin 3, (2 : ℕ)) = ∑ i : Fin 3, (P.support i).card := by
      simpa using htotal.symm
    have h := (Finset.sum_eq_sum_iff_of_le (fun i _ => P.HMIN i)).mp heq
    exact fun i => (h i (Finset.mem_univ i)).symm
  · have heq : (∑ b : B, (P.participationSteps b).card) = ∑ _b : B, (2 : ℕ) := by
      simpa [participationSteps, hcard, P.incidence_sum] using htotal
    have h := (Finset.sum_eq_sum_iff_of_le (fun b _ => hcount b)).mp heq
    exact fun b => h b (Finset.mem_univ b)

/-- Item 3, stated for the first three steps of an arbitrary-length run. -/
theorem THREE_SITE_INCIDENCE_EQUALITY (hB : Fintype.card B ≤ 3) (hq : 3 ≤ q) :
    Fintype.card B = 3 ∧
    (∀ i : Fin 3, ((R.firstSteps 3 hq).support i).card = 2) ∧
    (∀ b : B, ((R.firstSteps 3 hq).participationSteps b).card = 2) :=
  three_incidence_equality (R.firstSteps 3 hq) hB

omit [Fintype B] [Fintype W] in
/-- Fixing the complement of a support preserves its pool of previous tokens. -/
theorem previous_holder_mem (s : Finset B) (before after : B ≃ W)
    (hout : ∀ b, b ∉ s → before b = after b) {x : B} (hx : x ∈ s) :
    before.symm (after x) ∈ s := by
  classical
  by_contra hn
  have hfix := hout (before.symm (after x)) hn
  have heq : after (before.symm (after x)) = after x := by
    rw [← hfix, before.apply_symm_apply]
  have hsame := after.injective heq
  exact hn (hsame.symm ▸ hx)

omit [Fintype B] [Fintype W] in
/-- A nontrivial transition on a named pair exchanges its two tokens.
`hmove` is supplied by HWORSE in a TokenRun; fixing the complement alone
would also permit the identity transition. -/
theorem pair_swap (s : Finset B) (before after : B ≃ W)
    (hout : ∀ b, b ∉ s → before b = after b)
    (hmove : ∀ b, b ∈ s → before b ≠ after b)
    (x y : B) (_hxy : x ≠ y) (hs : s = {x, y}) :
    after x = before y ∧ after y = before x := by
  classical
  have hone (a c : B) (ha : a ∈ s) (hac : s = {a, c}) : after a = before c := by
    have hmem := previous_holder_mem s before after hout ha
    rw [hac, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with heq | heq
    · have hsame : before a = after a := by
        calc
          before a = before (before.symm (after a)) := congrArg before heq.symm
          _ = after a := before.apply_symm_apply _
      exact (hmove a ha hsame).elim
    · rw [← heq, before.apply_symm_apply]
  constructor
  · exact hone x y (by simp [hs]) hs
  · exact hone y x (by simp [hs]) (by simpa [Finset.pair_comm] using hs)

theorem named_pair_swap (i : Fin q) (x y : B) (hxy : x ≠ y)
    (hs : R.support i = {x, y}) :
    R.state i.succ x = R.state i.castSucc y ∧
    R.state i.succ y = R.state i.castSucc x := by
  apply pair_swap (R.support i) (R.state i.castSucc) (R.state i.succ)
    (R.HOUT i) ?_ x y hxy hs
  intro b hb heq
  have h := R.HWORSE i b hb
  rw [heq] at h
  exact lt_irrefl _ h

/-- Item 4: the two members of a two-element support exchange their tokens. -/
theorem TWO_SUPPORT_FORCES_SWAP (i : Fin q) (hcard : (R.support i).card = 2) :
    ∃ x y : B, x ≠ y ∧ R.support i = {x, y} ∧
      R.state i.succ x = R.state i.castSucc y ∧
      R.state i.succ y = R.state i.castSucc x := by
  classical
  obtain ⟨x, y, hxy, hs⟩ := Finset.card_eq_two.mp hcard
  exact ⟨x, y, hxy, hs, R.named_pair_swap i x y hxy hs⟩

omit [Fintype B] in
/-- A representation lemma naming the other member of a pair. -/
theorem pair_of_card_two_mem (s : Finset B) (hs : s.card = 2) (x : B) (hx : x ∈ s) :
    ∃ a : B, x ≠ a ∧ s = {x, a} := by
  classical
  obtain ⟨u, v, huv, hs⟩ := Finset.card_eq_two.mp hs
  have h : x = u ∨ x = v := by simpa [hs] using hx
  rcases h with rfl | rfl
  · exact ⟨v, huv, hs⟩
  · exact ⟨u, huv.symm, by simpa [Finset.pair_comm] using hs⟩

omit [Fintype B] in
/-- Expanding the three index positions is just a representation lemma. -/
theorem three_membership_sum (S : Fin 3 → Finset B) (b : B) :
    ((Finset.univ : Finset (Fin 3)).filter (fun i => b ∈ S i)).card =
      (if b ∈ S 0 then 1 else 0) + (if b ∈ S 1 then 1 else 0) +
        (if b ∈ S 2 then 1 else 0) := by
  classical
  rw [Finset.card_filter, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [add_assoc]

/-- The equality structure forces the frozen triangle of supports.
This is a set-cardinality argument, without enumerating states or permutations. -/
theorem triangle_supports (S : Fin 3 → Finset B) (hB : Fintype.card B = 3)
    (hs : ∀ i, (S i).card = 2)
    (hc : ∀ b : B,
      ((Finset.univ : Finset (Fin 3)).filter (fun i => b ∈ S i)).card = 2) :
    ∃ x a b : B, x ≠ a ∧ x ≠ b ∧ a ≠ b ∧
      S 0 = {x, a} ∧ S 1 = {a, b} ∧ S 2 = {x, b} := by
  classical
  have hsum (b : B) :
      (if b ∈ S 0 then 1 else 0) + (if b ∈ S 1 then 1 else 0) +
        (if b ∈ S 2 then 1 else 0) = 2 := by
    rw [← three_membership_sum]
    exact hc b
  have hinter : 0 < (S 0 ∩ S 2).card := by
    have hu := (S 0 ∪ S 2).card_le_univ
    have hi := Finset.card_union_add_card_inter (S 0) (S 2)
    rw [hs 0, hs 2] at hi
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hinter
  obtain ⟨hx0, hx2⟩ := Finset.mem_inter.mp hx
  have hx1 : x ∉ S 1 := by
    intro h
    have hh := hsum x
    simp [hx0, h, hx2] at hh
  obtain ⟨a, hxa, h0⟩ := pair_of_card_two_mem (S 0) (hs 0) x hx0
  obtain ⟨b, hxb, h2⟩ := pair_of_card_two_mem (S 2) (hs 2) x hx2
  have h1compl : S 1 = Finset.univ.erase x := by
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro hcx
      exact hx1 (hcx ▸ hc)
    · simp [hB, hs 1]
  have ha1 : a ∈ S 1 := by simp [h1compl, hxa.symm]
  have hb1 : b ∈ S 1 := by simp [h1compl, hxb.symm]
  have hab : a ≠ b := by
    intro heq
    have ha0 : a ∈ S 0 := by simp [h0]
    have ha2 : a ∈ S 2 := by simp [h2, heq]
    have hh := hsum a
    simp [ha0, ha1, ha2] at hh
  have h1 : S 1 = {a, b} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact ha1
      · exact hb1
    · simp [hs 1, hab]
  exact ⟨x, a, b, hxa, hxb, hab, h0, h1, h2⟩

/-- Item 5: the three swaps along the triangle return `x` to its initial token. -/
theorem THREE_STEP_RETURN (P : TokenRun B W 3)
    (hB : Fintype.card B = 3)
    (hs : ∀ i, (P.support i).card = 2)
    (hc : ∀ b : B, (P.participationSteps b).card = 2) :
    ∃ x : B, x ∈ P.support 0 ∧ x ∉ P.support 1 ∧ x ∈ P.support 2 ∧
      P.state 3 x = P.state 0 x := by
  classical
  obtain ⟨x, a, b, hxa, hxb, hab, h0, h1, h2⟩ :=
    triangle_supports P.support hB hs (by simpa [participationSteps] using hc)
  have hswap0 := P.named_pair_swap 0 x a hxa h0
  have hswap1 := P.named_pair_swap 1 a b hab h1
  have hswap2 := P.named_pair_swap 2 x b hxb h2
  refine ⟨x, by simp [h0], by simp [h1, hxa, hxb], by simp [h2], ?_⟩
  calc
    P.state 3 x = P.state 2 b := hswap2.1
    _ = P.state 1 a := hswap1.2
    _ = P.state 0 x := hswap0.2

/-- Item 6: the forced return contradicts worsening at steps 0 and 2,
with the unchanged token at step 1 between them. -/
theorem THREE_SITE_CAPACITY (R : TokenRun B W q) (hB : Fintype.card B ≤ 3) :
    q ≤ 2 := by
  classical
  by_contra hq
  have hthree : 3 ≤ q := by omega
  let P := R.firstSteps 3 hthree
  obtain ⟨hcard, hs, hc⟩ := R.THREE_SITE_INCIDENCE_EQUALITY hB hthree
  obtain ⟨x, hx0, hx1, hx2, hreturn⟩ := THREE_STEP_RETURN P hcard hs hc
  have hw0 : P.rank x (P.state 0 x) < P.rank x (P.state 1 x) := P.HWORSE 0 x hx0
  have hout1 : P.state 1 x = P.state 2 x := P.HOUT 1 x hx1
  have hw2 : P.rank x (P.state 2 x) < P.rank x (P.state 3 x) := P.HWORSE 2 x hx2
  rw [← hout1, hreturn] at hw2
  exact lt_asymm hw0 hw2

/-- Item 7: both abstract small-block capacities in one theorem. -/
theorem SMALL_BLOCK_TOKEN_CAPACITIES (R : TokenRun B W q) :
    (Fintype.card B ≤ 2 → q ≤ 1) ∧ (Fintype.card B ≤ 3 → q ≤ 2) :=
  ⟨R.TWO_SITE_CAPACITY, R.THREE_SITE_CAPACITY⟩

/-- OPTIONAL item 8: the generic six-site incidence consequence. -/
theorem SIX_SITE_INCIDENCE_OPTIONAL (R : TokenRun B W q) (hB : Fintype.card B ≤ 6) :
    2 * q ≤ 6 * 5 ∧ q ≤ 15 := by
  have hcap : Fintype.card B * (Fintype.card B - 1) ≤ 6 * 5 :=
    Nat.mul_le_mul hB (by omega)
  have hinc : 2 * q ≤ 6 * 5 := R.incidence_bounds.1.trans (R.incidence_bounds.2.trans hcap)
  exact ⟨hinc, by omega⟩

end TokenRun

end F6SmallBlockTokenCapacity

-- Kernel axiom reports for every theorem in this implementation.
#print axioms F6SmallBlockTokenCapacity.TokenRun.mem_participationSteps
#print axioms F6SmallBlockTokenCapacity.TokenRun.rank_monotone
#print axioms F6SmallBlockTokenCapacity.TokenRun.rank_after_lt
#print axioms F6SmallBlockTokenCapacity.TokenRun.initial_rank_lt_after
#print axioms F6SmallBlockTokenCapacity.TokenRun.participation_count
#print axioms F6SmallBlockTokenCapacity.TokenRun.incidence_sum
#print axioms F6SmallBlockTokenCapacity.TokenRun.selected_participation_le
#print axioms F6SmallBlockTokenCapacity.TokenRun.incidence_bounds
#print axioms F6SmallBlockTokenCapacity.TokenRun.TWO_SITE_CAPACITY
#print axioms F6SmallBlockTokenCapacity.TokenRun.three_incidence_equality
#print axioms F6SmallBlockTokenCapacity.TokenRun.THREE_SITE_INCIDENCE_EQUALITY
#print axioms F6SmallBlockTokenCapacity.TokenRun.previous_holder_mem
#print axioms F6SmallBlockTokenCapacity.TokenRun.pair_swap
#print axioms F6SmallBlockTokenCapacity.TokenRun.named_pair_swap
#print axioms F6SmallBlockTokenCapacity.TokenRun.TWO_SUPPORT_FORCES_SWAP
#print axioms F6SmallBlockTokenCapacity.TokenRun.pair_of_card_two_mem
#print axioms F6SmallBlockTokenCapacity.TokenRun.three_membership_sum
#print axioms F6SmallBlockTokenCapacity.TokenRun.triangle_supports
#print axioms F6SmallBlockTokenCapacity.TokenRun.THREE_STEP_RETURN
#print axioms F6SmallBlockTokenCapacity.TokenRun.THREE_SITE_CAPACITY
#print axioms F6SmallBlockTokenCapacity.TokenRun.SMALL_BLOCK_TOKEN_CAPACITIES
#print axioms F6SmallBlockTokenCapacity.TokenRun.SIX_SITE_INCIDENCE_OPTIONAL
