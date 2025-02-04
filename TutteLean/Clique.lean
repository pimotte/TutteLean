import Mathlib.Combinatorics.SimpleGraph.Clique

import TutteLean.Defs

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

-- In #18878
theorem exists_union_disjoint_ncard_eq_of_even (he : Even s.ncard) : ∃ (t u : Set α),
    t ∪ u = s ∧ Disjoint t u ∧ t.ncard = u.ncard := by
  sorry

lemma isClique_even_iff_matches [DecidableEq V]
    (u : Set V) (hu : Set.Finite u) (hc : G.IsClique u) : Even u.ncard ↔ ∃ (M : Subgraph G), M.verts = u ∧ M.IsMatching := by
  refine ⟨?_ , by
    rintro ⟨M, ⟨rfl, hMr⟩⟩
    simpa [Set.ncard_eq_toFinset_card _ hu, Set.toFinite_toFinset,
      ← Set.toFinset_card] using @hMr.even_card _  _ _ hu.fintype⟩
  intro h
  obtain ⟨t, u, rfl, hd, hcard⟩ := exists_union_disjoint_ncard_eq_of_even h
  obtain ⟨f⟩ : Nonempty (t ≃ u) := by
    rw [← Cardinal.eq, ← t.cast_ncard (Set.finite_union.mp hu).1, ← u.cast_ncard (Set.finite_union.mp hu).2]
    exact congrArg Nat.cast hcard
  exact SimpleGraph.Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv hd f (by
    intro v
    apply hc (by simp) (by simp)
    exact hd.ne_of_mem (by simp) (by simp))

lemma isNotClique_iff (G : SimpleGraph V) (u : Set V) : ¬G.IsClique u ↔ ∃ (v w : u), v ≠ w ∧ ¬ G.Adj v w := by
  constructor
  · rw [@isClique_iff_induce_eq]
    intro h
    by_contra! hc
    apply h
    ext v w
    rw [@top_adj]
    exact ⟨fun h' ↦ Adj.ne' (adj_symm (induce u G) h'), fun h' ↦ hc v w h' ⟩
  · rintro ⟨ v , ⟨ w , h ⟩ ⟩
    rw [SimpleGraph.isClique_iff]
    by_contra! hc
    exact h.2 (hc (Subtype.coe_prop v) (w.coe_prop) (Subtype.coe_ne_coe.mpr h.1))
