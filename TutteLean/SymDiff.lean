import TutteLean.Defs
import TutteLean.Walk

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

-- In #14976 (Should be using symmdiff in the top graph not on subgraphs)
def Subgraph.symDiff (M : Subgraph G) (C : Subgraph G) : Subgraph G := {
  verts := M.verts ∪ C.verts,
  Adj := fun v w ↦ (¬ M.Adj v w ∧ C.Adj v w) ∨ (M.Adj v w ∧ ¬ C.Adj v w),
  adj_sub := by
    intro v w hvw
    cases hvw
    next h1 => simp only [h1.2, C.adj_sub]
    next h2 => simp only [h2.1, M.adj_sub]
  edge_vert := by
    intro v w hvw
    cases hvw
    next h1 =>
      right
      apply SimpleGraph.Subgraph.support_subset_verts
      exact C.mem_support.mpr ⟨w, h1.2⟩
    next h2 =>
      left
      apply SimpleGraph.Subgraph.support_subset_verts
      exact M.mem_support.mpr ⟨w, h2.1⟩
  symm := by
    intro v w hvw
    cases hvw
    next h1 =>
      left
      exact ⟨fun h ↦ h1.1 h.symm, h1.2.symm⟩
    next h2 =>
      right
      exact ⟨h2.1.symm, fun h ↦ h2.2 h.symm⟩
  }

-- In #14976
@[simp]
lemma Subgraph.symDiff_verts (M : Subgraph G) (C : Subgraph G) : (M.symDiff C).verts = M.verts ∪ C.verts := by rfl
-- In #14976
@[simp]
lemma Subgraph.symDiff_adj (M : Subgraph G) (C : Subgraph G) : (M.symDiff C).Adj v w = ((¬ M.Adj v w ∧ C.Adj v w) ∨ (M.Adj v w ∧ ¬ C.Adj v w)) := rfl
-- In #14976
lemma Subgraph.symDiff_adj_comm (M : Subgraph G) (C : Subgraph G) : (M.symDiff C).Adj v w = (C.symDiff M).Adj v w := by
  unfold symDiff
  simp
  tauto

-- In #14976
lemma Subgraph.symDiffSingletonAdj {M : Subgraph G} : (M.symDiff (G.singletonSubgraph u)).Adj v w = M.Adj v w := by
  unfold symDiff
  simp [singletonSubgraph_adj, Pi.bot_apply, eq_iff_iff, Prop.bot_eq_false]

lemma alternatingCycleSymDiffMatch {M : Subgraph G} {p : G.Walk u u} (hM : M.IsPerfectMatching)
    (hpc : p.IsCycle) (hpalt : p.IsAlternating M) : (M.symDiff p.toSubgraph).IsMatching := by
    intro v _
    --unused?
    have hv : v ∈ M.verts := hM.2 v
    obtain ⟨w, hw⟩ := hM.1 (hM.2 v)
    by_cases hc : p.toSubgraph.Adj v w
    · unfold Subgraph.symDiff
      dsimp at *
      obtain ⟨w', hw'⟩ := alternating_edge' p M hpalt hpc hw.1 hc
      use w'
      constructor
      · left
        exact ⟨hw'.1, hw'.2.1⟩
      · dsimp at *
        intro y hy
        cases hy with
        | inl hl => {
          -- obtain ⟨w'', hw''⟩ := alternating_edge p M hpalt hpc hw'.1 hw'.2.1
          push_neg at hw'
          have hc2 := cycle_two_neighbors p hpc (p.toSubgraph_Adj_mem_support hc)
          by_contra! hc'
          have hc3 : ({y, w, w'} : Set V).ncard = 3 := by
            rw [Set.ncard_eq_three]
            use y
            use w
            use w'
            simp only [ne_eq, and_true]
            push_neg
            refine ⟨?_, hc', hw'.2.2⟩
            intro hyw
            exact hl.1 (hyw ▸ hw.1)

          have : ({y, w, w'} : Set V) ⊆ p.toSubgraph.neighborSet v := by
            intro v' hv'
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv'
            unfold Subgraph.neighborSet
            rw [@Set.mem_setOf]
            cases hv' with
            | inl h1 => {
              rw [h1]
              exact hl.2
            }
            | inr h2 => {
              cases h2 with
              | inl h3 => {
                rw [h3]
                exact hc
              }
              | inr h4 => {
                rw [h4]
                exact hw'.2.1
              }
            }
          rw [@Set.ncard_eq_two] at hc2
          obtain ⟨x', y', hxy'⟩ := hc2
          have : ({y, w, w'} : Set V).ncard ≤ ({x', y'} : Set V).ncard := by
            refine Set.ncard_le_ncard ?_ (by
              simp only [Set.finite_singleton, Set.Finite.insert]
              )
            rw [← hxy'.2]
            exact this
          rw [hc3] at this
          rw [Set.ncard_pair hxy'.1] at this
          omega
        }
        | inr hr => {
          exfalso
          have := hw.2 _ hr.1
          rw [this] at hr
          exact hr.2 hc
        }
    · use w
      unfold Subgraph.symDiff at *
      dsimp at *
      constructor
      · right
        exact ⟨hw.1, hc⟩
      · intro y hy

        cases hy with
        | inl h1 => {
          obtain ⟨w', hw'⟩ := alternating_edge p M hpalt hpc h1.1 h1.2
          have := hw.2 _ hw'.1
          exact (hc (this ▸ hw'.2.1)).elim
        }
        | inr h2 => {
          apply hw.2
          exact h2.1
        }


lemma Subgraph.symDiffPerfectMatchingsAlternating {M1 : Subgraph G} {M2 : Subgraph G}
    (hM1 : M1.IsPerfectMatching) (hM2 : M2.IsPerfectMatching) : (M1.symDiff M2).IsAlternating M2 := by
  unfold Subgraph.IsAlternating
  intro v w w' hww' havw havw'
  unfold Subgraph.symDiff at *
  simp only [ne_eq] at *
  by_cases h : M2.Adj v w
  · simp only [h, true_iff]
    intro h'
    obtain ⟨w'', hw''⟩ := hM2.1 (hM2.2 v)
    have heq1 := hw''.2 w h
    have heq2 := hw''.2 w' h'
    apply hww'
    exact heq2.symm ▸ heq1
  · simp only [h, false_iff, not_not]
    cases havw with
    | inl hl => exact (h hl.2).elim
    | inr hr =>
      have hM1' : ¬M1.Adj v w' := by
        intro h1vw
        obtain ⟨w'', hw''⟩ := hM1.1 (hM1.2 v)
        have heq1 := hw''.2 w hr.1
        have heq2 := hw''.2 w' h1vw
        apply hww'
        exact heq2.symm ▸ heq1
      cases havw' with
      | inl h1 => exact h1.2
      | inr h2 => exact (hM1' h2.1).elim


lemma Subgraph.symDiffPerfectMatchingsCard {M1 : Subgraph G} {M2 : Subgraph G}
    (hM1 : M1.IsPerfectMatching) (hM2 : M2.IsPerfectMatching) (v : V) : ((M1.symDiff M2).neighborSet v) = ∅ ∨ ((M1.symDiff M2).neighborSet v).ncard = 2 := by
  obtain ⟨w1, hw1⟩ := hM1.1 (hM1.2 v)
  obtain ⟨w2, hw2⟩ := hM2.1 (hM2.2 v)
  unfold Subgraph.symDiff
  unfold Subgraph.neighborSet
  by_cases h : w1 = w2
  · left
    simp only
    rw [@Set.eq_empty_iff_forall_not_mem]
    intro v'
    simp only [Set.mem_setOf_eq, not_or, not_and, not_not]
    constructor
    · intro h1nvv' h2vv'
      have := hw2.2 _ h2vv'
      rw [this, ← h] at h1nvv'
      exact h1nvv' hw1.1
    · intro h1vv'
      have := hw1.2 _ h1vv'
      exact this ▸ h ▸ hw2.1
  · right
    simp only
    rw [@Set.ncard_eq_two]
    use w1
    use w2
    refine ⟨h, ?_⟩
    ext w'
    constructor
    · intro hw'
      simp only [Set.mem_setOf_eq] at hw'
      cases hw' with
      | inl hl =>
        have := hw2.2 _ hl.2
        rw [this]
        exact Set.mem_insert_of_mem w1 rfl
      | inr hr =>
        have := hw1.2 _ hr.1
        rw [this]
        exact Set.mem_insert w1 {w2}
    · intro hw'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw'
      simp only [Set.mem_setOf_eq]
      cases hw' with
      | inl hl =>
        right
        refine ⟨hl.symm ▸ hw1.1 , ?_⟩
        intro h2vw
        have := hw2.2 _ h2vw
        exact h (hl.symm ▸ this)
      | inr hr =>
        left
        refine ⟨?_, hr.symm ▸ hw2.1⟩
        intro h1vw
        exact h (hr ▸ (hw1.2 _ h1vw).symm)

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

lemma alternatingCycleSymDiffMatch' {M : Subgraph G} {C : Subgraph G} (hM : M.IsPerfectMatching)
    (hic : C.IsCycle) (halt : C.IsAlternating M) : (M.symDiff C).IsMatching := by
    intro v _

    --unused?
    have hv : v ∈ M.verts := hM.2 v
    obtain ⟨w, hw⟩ := hM.1 (hM.2 v)
    by_cases hc : C.Adj v w
    · --unfold Subgraph.symDiff
      dsimp at *
      obtain ⟨w', hw'⟩ := Subgraph.alternating_edge' C M halt hic hw.1 hc
      use w'
      constructor
      · left
        exact ⟨hw'.1, hw'.2.1⟩
      · dsimp at *
        intro y hy
        cases hy with
        | inl hl => {
          -- obtain ⟨w'', hw''⟩ := alternating_edge p M hpalt hpc hw'.1 hw'.2.1
          push_neg at hw'
          have hc2 := hic.1 v ((by rw [SimpleGraph.Subgraph.mem_support]; use w))
          by_contra! hc'
          have hc3 : ({y, w, w'} : Set V).ncard = 3 := by
            rw [Set.ncard_eq_three]
            use y
            use w
            use w'
            simp only [ne_eq, and_true]
            push_neg
            refine ⟨?_, hc', hw'.2.2⟩
            intro hyw
            exact hl.1 (hyw ▸ hw.1)

          have : ({y, w, w'} : Set V) ⊆ C.neighborSet v := by
            intro v' hv'
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv'
            unfold Subgraph.neighborSet
            rw [@Set.mem_setOf]
            cases hv' with
            | inl h1 => {
              rw [h1]
              exact hl.2
            }
            | inr h2 => {
              cases h2 with
              | inl h3 => {
                rw [h3]
                exact hc
              }
              | inr h4 => {
                rw [h4]
                exact hw'.2.1
              }
            }
          rw [@Set.ncard_eq_two] at hc2
          obtain ⟨x', y', hxy'⟩ := hc2
          have : ({y, w, w'} : Set V).ncard ≤ ({x', y'} : Set V).ncard := by
            refine Set.ncard_le_ncard ?_ (by
              simp only [Set.finite_singleton, Set.Finite.insert]
              )
            rw [← hxy'.2]
            exact this
          rw [hc3] at this
          rw [Set.ncard_pair hxy'.1] at this
          omega
        }
        | inr hr => {
          exfalso
          have := hw.2 _ hr.1
          rw [this] at hr
          exact hr.2 hc
        }
    · use w
      unfold Subgraph.symDiff at *
      dsimp at *
      constructor
      · right
        exact ⟨hw.1, hc⟩
      · intro y hy

        cases hy with
        | inl h1 => {
          obtain ⟨w', hw'⟩ := Subgraph.alternating_edge C M halt hic h1.1 h1.2
          have := hw.2 _ hw'.1
          exact (hc (this ▸ hw'.2.1)).elim
        }
        | inr h2 => {
          apply hw.2
          exact h2.1
        }
