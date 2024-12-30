import TutteLean.Defs
-- import TutteLean.Part2

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}


lemma Subgraph.alternating_edge (C : Subgraph G) (M : Subgraph G) (h : C.IsAlternating M)
    (hic : C.IsCycle) (hM : ¬ M.Adj v w) (hc : C.Adj v w)
    : ∃ w', M.Adj v w' ∧ C.Adj v w' ∧ w ≠ w' := by
    -- have hv : v ∈ p.support := Walk.toSubgraph_Adj_mem_support p hp
    have hn := hic.1 v (by rw [SimpleGraph.Subgraph.mem_support]; use w)
    rw [@Set.ncard_eq_two] at hn
    obtain ⟨x, y, hxy⟩ := hn
    by_cases hxw : x = w
    · use y
      have hpvy : C.Adj v y := by
        have : y ∈ ({x, y} : Set V) := by
          exact Set.mem_insert_of_mem x rfl
        rw [← hxy.2] at this
        exact this
      have := h _ _ _ (hxw ▸ hxy.1) hc hpvy
      rw [@iff_not_comm] at this
      have hMAdj : M.Adj v y := this.mpr hM
      exact ⟨hMAdj, hpvy, hxw ▸ hxy.1⟩
    · use x
      have hpvx : C.Adj v x := by
        have : x ∈ ({x, y} : Set V) := by
          exact Set.mem_insert x {y}
        rw [← hxy.2] at this
        exact this

      push_neg at hxw
      have := h _ _ _ hxw hpvx hc
      exact ⟨this.mpr hM, hpvx, hxw.symm⟩

lemma Subgraph.alternating_edge' (C : Subgraph G) (M : Subgraph G) (h : C.IsAlternating M)
    (hic : C.IsCycle) (hM : M.Adj v w) (hc : C.Adj v w)
    : ∃ w', ¬ M.Adj v w' ∧ C.Adj v w' ∧ w ≠ w' := by
    have hn := hic.1 v (by rw [SimpleGraph.Subgraph.mem_support]; use w)
    rw [@Set.ncard_eq_two] at hn
    obtain ⟨x, y, hxy⟩ := hn
    by_cases hxw : x = w
    · use y
      have hpvy : C.Adj v y := by
        have : y ∈ ({x, y} : Set V) := by
          exact Set.mem_insert_of_mem x rfl
        rw [← hxy.2] at this
        exact this
      have := (h _ _ _ (hxw ▸ hxy.1) hc hpvy).mp hM
      exact ⟨this, hpvy, hxw ▸ hxy.1⟩
    · use x
      have hpvx : C.Adj v x := by
        have : x ∈ ({x, y} : Set V) := by
          exact Set.mem_insert x {y}
        rw [← hxy.2] at this
        exact this
      push_neg at hxw
      have := h _ _ _ hxw hpvx hc
      rw [@iff_not_comm] at this
      exact ⟨this.mp hM, hpvx, hxw.symm⟩
