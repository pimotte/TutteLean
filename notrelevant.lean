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
