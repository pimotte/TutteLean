import TutteLean.Defs

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

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

lemma Set.triple_ncard_two {x y z : V} (h : ({x, y, z} : Set V).ncard ≤ 2) : x = y ∨ x = z ∨ y = z := by
  by_contra! hc
  have := Set.ncard_eq_three.mpr ⟨x, y, z, hc.1, hc.2.1, hc.2.2, rfl⟩
  omega


lemma pair_subset_pair {v w x y : V} (h : v ≠ w) (h3 : ({v , w} : Set V) ⊆ {x, y}) : ({v, w} : Set V) = {x, y} := by
  rw [@Set.Subset.antisymm_iff]
  refine ⟨h3, ?_⟩
  have h4 := Set.nontrivial_pair h
  have : ({v, w} : Set V).Nonempty := by
    simp only [Set.insert_nonempty]
  rw [Set.Nonempty.subset_pair_iff_eq this] at h3
  simp [@Set.Nontrivial.ne_singleton _ _ x h4, @Set.Nontrivial.ne_singleton _ _ y h4] at h3
  exact Eq.subset (Eq.symm h3)
