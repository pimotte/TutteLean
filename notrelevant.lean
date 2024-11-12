import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card


theorem chainInSubtypeGivesChainInSupertype {α : Type} {p : α → Prop} [LE α] {c : Set (Subtype p)} (hc : IsChain (. ≤ .) c) :
   IsChain (. ≤ .) (Subtype.val '' c ) := by
    intro x hx y hy hxy
    obtain ⟨x' , hx'⟩ := hx
    obtain ⟨y' , hy'⟩ := hy

    rw [← hx'.2, ← hy'.2] at hxy
    let h := hc hx'.1 hy'.1 (fun a => hxy (congrArg Subtype.val a))
    dsimp at *
    dsimp at h
    cases h with
    | inl ha =>
      left
      rw [← hx'.2, ← hy'.2]
      exact ha
    | inr hb =>
      right
      rw [← hx'.2, ← hy'.2]
      exact hb

theorem chainFinsetInFintypeHasMax {α : Type*} [PartialOrder α] [DecidableEq α] {c : Finset α} [hnc : Nonempty c] (hic : IsChain (. ≤ .) c.toSet) :
  ∃ m ∈ c, ∀ a ∈ c, a ≤ m := by
    by_contra! hc
    obtain ⟨ g , hg ⟩ := hnc
    obtain ⟨ g' , hg' ⟩ := hc g hg
    obtain hcemp | hcnemp := (c \ {g}).eq_empty_or_nonempty
    · rw [Finset.sdiff_eq_empty_iff_subset] at hcemp
      rw [Finset.subset_singleton_iff'] at hcemp
      apply hg'.2
      rw [hcemp g' hg'.1]


    · have cGch : IsChain (. ≤ .) (c \ {g}).toSet := by
        rw [Finset.coe_sdiff]
        rw [Finset.coe_singleton]
        apply IsChain.mono (@Set.diff_subset _ c {g})
        exact hic
      haveI instNonEmp : Nonempty ↑(c \ {g}) := Set.Nonempty.to_subtype hcnemp
      obtain ⟨ m , hm ⟩ := chainFinsetInFintypeHasMax cGch
      obtain ⟨ n , hn ⟩ := hc m (Finset.mem_sdiff.mp hm.1).1

      have : n = g := by
        by_contra! hc'
        apply hn.2
        apply hm.2 n
        rw [Finset.sdiff_singleton_eq_erase]
        rw [Finset.mem_erase]
        exact  ⟨ hc', hn.1 ⟩
      have h'' : ¬g' ≤ n := by
        rw [← this] at hg'
        exact hg'.2
      apply h''
      have h''' := hm.2 g'

      have h'''' : g' ∈ c \ {g} := by
        rw [Finset.sdiff_singleton_eq_erase]
        rw [Finset.mem_erase]
        exact ⟨ ne_of_not_le hg'.2 , hg'.1 ⟩
      apply le_of_lt
      apply lt_of_le_of_lt (h''' h'''')
      have h''''' := hic (Finset.mem_sdiff.mp hm.1).1 (hn.1) (ne_of_not_le hn.2).symm
      dsimp at h'''''
      cases h''''' with
      | inl ha => exact lt_iff_le_and_ne.mpr ⟨ ha , (ne_of_not_le hn.2).symm ⟩
      | inr hb =>
         exfalso
         exact hn.2 hb
termination_by c.card
decreasing_by
· simp_wf
  rw [← Finset.erase_eq]
  rw [← Finset.card_erase_add_one hg]
  simp only [lt_add_iff_pos_right, zero_lt_one]
--   haveI : Fintype c := setFintype c
--   rw [Set.ncard_eq_toFinset_card]



theorem chainInFintypeHasMax {α : Type*} [Fintype α] [PartialOrder α] [DecidableEq α] (c : Set α) [hnc : Nonempty c] (hic : IsChain (. ≤ .) c) :
  ∃ m ∈ c, ∀ a ∈ c, a ≤ m := by
  let c' := c.toFinset
  have fChain : IsChain (. ≤ .) c'.toSet := by
    intro x hx y hy hxy
    cases hic (Set.mem_toFinset.mp hx) (Set.mem_toFinset.mp hy) hxy with
    | inl ha =>
      left
      assumption
    | inr hb =>
      right
      assumption
  haveI : Nonempty c' := by
    obtain ⟨ e , he ⟩ := hnc
    use e
    exact Set.mem_toFinset.mpr he
  have ⟨ m , hm ⟩ := chainFinsetInFintypeHasMax fChain
  use m
  constructor
  · exact Set.mem_toFinset.mp hm.1
  · intro a ha
    exact hm.2 a (Set.mem_toFinset.mpr ha)

lemma subdivide [Fintype V] [Inhabited V] [DecidableEq V] {G G' : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (h : G ≤ G') (c : ConnectedComponent G') : ∃ (cs : Finset (ConnectedComponent G)), (ConnectedComponent.supp '' cs.toSet).sUnion = c.supp := by
      use (connectedComponentMk G '' c.supp).toFinset
      ext v
      constructor
      · intro hv
        rw [Set.sUnion_image] at hv
        rw [Set.mem_iUnion] at hv
        obtain ⟨ i , hi ⟩ := hv
        rw [Set.mem_iUnion] at hi
        obtain ⟨ j , hj ⟩ := hi
        rw [@Finset.mem_coe] at j
        rw [@Set.mem_toFinset] at j
        rw [Set.mem_image] at j
        obtain ⟨ k , hk ⟩ := j
        rw [ConnectedComponent.mem_supp_iff] at *
        rw [← hk.1]
        rw [← hk.2] at hj
        rw [@ConnectedComponent.eq] at *
        apply SimpleGraph.Reachable.mono h
        exact hj
      · intro hv
        rw [Set.mem_sUnion]

        use (connectedComponentMk G v).supp
        constructor
        · rw [Function.Injective.mem_set_image SimpleGraph.ConnectedComponent.supp_injective, Finset.mem_coe, Set.mem_toFinset, Set.mem_image]
          use v
        · exact rfl


lemma exclUnion [Fintype V] [Inhabited V] [DecidableEq V] [DecidableRel G.Adj] (s : Finset (ConnectedComponent G))
  : Fintype.card ↑(⋃ x ∈ s, @ConnectedComponent.supp V G x) = Finset.sum s (fun x => Nat.card (@ConnectedComponent.supp V G x)) := by

    rw [← Set.toFinset_card ]
    have hp : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      Disjoint (Set.toFinset (@ConnectedComponent.supp _ G x)) (Set.toFinset (ConnectedComponent.supp y)) := by
      intro xs _ ys _ hxy s' hx hy
      simp only [Finset.bot_eq_empty, Finset.le_eq_subset]
      rw [Finset.subset_empty]
      rw [Finset.eq_empty_iff_forall_not_mem]
      by_contra! hc
      obtain ⟨ v , hv ⟩ := hc
      obtain ha := hx hv
      obtain hb := hy hv
      simp only [ne_eq, Finset.le_eq_subset, Set.subset_toFinset, Set.mem_toFinset,
        ConnectedComponent.mem_supp_iff] at *
      exact hxy (ha.symm ▸ hb)
      done

    have : Set.toFinset (⋃ x ∈ s, ConnectedComponent.supp x) = Finset.biUnion s (fun x => (ConnectedComponent.supp x).toFinset) := by
      ext v
      simp only [Set.mem_toFinset, Set.mem_iUnion, ConnectedComponent.mem_supp_iff, exists_prop,
        exists_eq_right', Finset.mem_biUnion]

    rw [this]
    rw [Finset.card_biUnion hp]
    congr
    dsimp
    ext c
    rw [@Set.toFinset_card]
    rw [Nat.card_eq_fintype_card]


lemma evenFinsetSum {a : Finset α} (f : α → ℕ) (h : ∀ (c : a), Even (f c)) : Even (Finset.sum a f) := by
  rw [@Nat.even_iff]
  rw [Finset.sum_nat_mod]
  have : (Finset.sum a fun i => f i % 2) = Finset.sum a fun i => 0 := by
    exact Finset.sum_congr (rfl : a = a) (by
      intro x hx
      have h' := h ⟨ x , hx ⟩
      dsimp at h'
      rw [@Nat.even_iff] at h'
      exact h'
      )
  rw [this]
  simp only [Finset.sum_const_zero, Nat.zero_mod]

lemma disjoint_pair (v w : V) (u : Set V) : Disjoint u {v , w} ↔ v ∉ u ∧ w ∉ u := by
  constructor
  · intro h
    exact ⟨ (Set.disjoint_right.mp h) (Set.mem_insert v {w}), (Set.disjoint_right.mp h) (Set.mem_insert_of_mem v rfl) ⟩
  · intro h
    intro s hsu hsvw
    simp only [Set.le_eq_subset, Set.bot_eq_empty] at *
    rw [@Set.subset_def] at hsvw
    rw [@Set.subset_empty_iff, @Set.eq_empty_iff_forall_not_mem]
    intro x hxs
    have := hsvw _ hxs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    cases this with
    | inl hl => exact h.1 (hsu (hl ▸ hxs))
    | inr hr => exact h.2 (hsu (hr ▸ hxs))
