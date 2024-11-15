import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Operations

namespace SimpleGraph
-- universe u
variable {V : Type*} {G : SimpleGraph V}

theorem IsPerfectMatching.toSubgraph_spanningCoe {M : Subgraph G} (hM : M.IsPerfectMatching)
    (h : M.spanningCoe ≤ G') : (G'.toSubgraph M.spanningCoe h).IsPerfectMatching := by
  refine ⟨?_, fun v ↦ by simp⟩
  intro v _
  apply hM.1
  simp only [Subgraph.IsSpanning.verts_eq_univ hM.2, Set.mem_univ]

theorem adj_of_sym2_eq (h : G.Adj v w) (h2 : s(v, w) = s(u, t)) : G.Adj u t := by
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h2
  cases' h2 with hl hr
  · rw [hl.1, hl.2] at h
    exact h
  · rw [hr.1, hr.2] at h
    exact h.symm

theorem Subgraph.adj_of_sym2_eq {H : Subgraph G} (h : H.Adj v w) (h2 : s(v, w) = s(u, t)) : H.Adj u t := by
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h2
  cases' h2 with hl hr
  · rw [hl.1, hl.2] at h
    exact h
  · rw [hr.1, hr.2] at h
    exact h.symm

theorem tutte_part2 {x a b c : V} (hxa : G.Adj x a) (hab : G.Adj a b) (hnxb : ¬ G.Adj x b) (hnac : ¬ G.Adj a c)
    (hnxb : x ≠ b) (hnxc : x ≠ c) (hnac : a ≠ c) (hnbc : b ≠ c)
    (hm1 : ∃ (M : Subgraph (G ⊔ edge x b)), M.IsPerfectMatching)
    (hm2 : ∃ (M : Subgraph (G ⊔ edge a c)), M.IsPerfectMatching)
    : ∃ (M : Subgraph G), M.IsPerfectMatching := by
  obtain ⟨M1, hM1⟩ := hm1
  obtain ⟨M2, hM2⟩ := hm2
  -- have {v w : V} (M' : Subgraph (G ⊔ edge v w)) (hM' : M.)
  by_cases hM1xb : ¬ M1.Adj x b

  · have : M1.spanningCoe ≤ G := by
      intro v w hvw
      simp only [Subgraph.spanningCoe_adj] at *
      by_cases h : s(v, w) = s(x, b)
      · exact (hM1xb (Subgraph.adj_of_sym2_eq hvw h)).elim
      · have := hvw.adj_sub
        simp only [sup_adj, edge_adj] at this
        cases' this with hl hr
        · exact hl
        · rw [Sym2.eq_iff] at h
          exact (h hr.1).elim
    use G.toSubgraph M1.spanningCoe this
    exact IsPerfectMatching.toSubgraph_spanningCoe hM1 this



  -- let cycles := symmDiff M1.spanningCoe M2.spanningCoe
  simp only [not_not] at hM1xb


  sorry
