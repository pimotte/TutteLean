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

theorem adj_of_sym2_eq (h2 : s(v, w) = s(u, t)) : G.Adj v w ↔ G.Adj u t := by
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h2
  cases' h2 with hl hr
  · rw [hl.1, hl.2]
  · rw [hr.1, hr.2, adj_comm]

theorem Subgraph.adj_of_sym2_eq {H : Subgraph G} (h2 : s(v, w) = s(u, t)) : H.Adj v w ↔ H.Adj u t := by
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h2
  cases' h2 with hl hr
  · rw [hl.1, hl.2]
  · rw [hr.1, hr.2, Subgraph.adj_comm]


theorem Subgraph.sup_edge_spanningCoe_le {v w : V} {H : Subgraph (G ⊔ edge v w)} (h : ¬ H.Adj v w) :
    H.spanningCoe ≤ G := by
  intro v' w' hvw'
  simp only [Subgraph.spanningCoe_adj] at *
  by_cases hs : s(v', w') = s(v, w)
  · exact (h ((Subgraph.adj_of_sym2_eq hs).mp hvw')).elim
  · have := hvw'.adj_sub
    simp only [SimpleGraph.sup_adj, SimpleGraph.edge_adj] at this
    cases' this with hl hr
    · exact hl
    · rw [Sym2.eq_iff] at hs
      exact (hs hr.1).elim

def IsCycles := (∀ v : V, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 2)

def IsAlternating (G : SimpleGraph V) (G' : SimpleGraph V) :=
  ∀ (v w w': V), w ≠ w' → G.Adj v w → G.Adj v w' → (G'.Adj v w ↔ ¬ G'.Adj v w')

lemma symmDiff_spanningCoe_IsPerfectMatching_IsCycles
    {M : Subgraph G} {M' : Subgraph G'} (hM : M.IsPerfectMatching)
    (hM' : M'.IsPerfectMatching) : (symmDiff M.spanningCoe M'.spanningCoe).IsCycles := by
  sorry

lemma IsPerfectMatching.symmDiff_spanningCoe_of_IsAlternating {M : Subgraph G''} (hM : M.IsPerfectMatching)
    (hG' : G'.IsAlternating M.spanningCoe) (hle : symmDiff M.spanningCoe G' ≤ G) :
    (G.toSubgraph (symmDiff M.spanningCoe G') hle).IsPerfectMatching := by
  sorry

lemma IsAlternating.induce_supp (c : G.ConnectedComponent) (h : G.IsAlternating G') : (G.induce c.supp).spanningCoe.IsAlternating G' := by
  sorry

lemma symmDiff_spanningCoe_IsPerfectMatching_IsAlternating_left
    {M : Subgraph G} {M' : Subgraph G'} (hM : M.IsPerfectMatching)
    (hM' : M'.IsPerfectMatching) : (symmDiff M.spanningCoe M'.spanningCoe).IsAlternating M.spanningCoe := by
  sorry

lemma symmDiff_spanningCoe_IsPerfectMatching_IsAlternating_right
    {M : Subgraph G} {M' : Subgraph G'} (hM : M.IsPerfectMatching)
    (hM' : M'.IsPerfectMatching) : (symmDiff M.spanningCoe M'.spanningCoe).IsAlternating M'.spanningCoe := by
  sorry

lemma symmDiff_le (h : G ≤ H) (h' : G' ≤ H') : (symmDiff G G') ≤ H ⊔ H' := by
  sorry

lemma induce_component_spanningCoe_Adj (c : G.ConnectedComponent) :
  (G.induce c.supp).spanningCoe.Adj v w ↔ v ∈ c.supp ∧ G.Adj v w := by
  sorry

theorem tutte_part2 {x a b c : V} (hxa : G.Adj x a) (hab : G.Adj a b) (hnGxb : ¬G.Adj x b) (hnGac : ¬ G.Adj a c)
    (hnxb : x ≠ b) (hnxc : x ≠ c) (hnac : a ≠ c) (hnbc : b ≠ c)
    (hm1 : ∃ (M : Subgraph (G ⊔ edge x b)), M.IsPerfectMatching)
    (hm2 : ∃ (M : Subgraph (G ⊔ edge a c)), M.IsPerfectMatching)
    : ∃ (M : Subgraph G), M.IsPerfectMatching := by
  obtain ⟨M1, hM1⟩ := hm1
  obtain ⟨M2, hM2⟩ := hm2

  have hM2nxb : ¬M2.Adj x b := by
    intro h
    simpa [hnGxb, edge_adj, hnxb, hxa.ne, hnxc] using h.adj_sub


  by_cases hM1xb : ¬M1.Adj x b
  · use G.toSubgraph M1.spanningCoe (M1.sup_edge_spanningCoe_le hM1xb)
    exact IsPerfectMatching.toSubgraph_spanningCoe hM1 (M1.sup_edge_spanningCoe_le hM1xb)
  by_cases hM2ac : ¬M2.Adj a c
  · use G.toSubgraph M2.spanningCoe (M2.sup_edge_spanningCoe_le hM2ac)
    exact IsPerfectMatching.toSubgraph_spanningCoe hM2 (M2.sup_edge_spanningCoe_le hM2ac)
  simp only [not_not] at hM1xb hM2ac

  suffices ∃ (G' : SimpleGraph V), G'.IsAlternating M2.spanningCoe ∧ symmDiff M2.spanningCoe G' ≤ G by
    obtain ⟨G', hg⟩ := this
    use (G.toSubgraph (symmDiff M2.spanningCoe G') hg.2)
    apply IsPerfectMatching.symmDiff_spanningCoe_of_IsAlternating hM2 hg.1

  suffices ∃ (G' : SimpleGraph V), G'.IsAlternating M2.spanningCoe ∧ ¬G'.Adj x b ∧ G'.Adj a c
      ∧ G' ≤ G ⊔ edge a c by
    obtain ⟨G', ⟨hG', hG'xb, hnG'ac, hle⟩⟩ := this
    use G'
    refine ⟨hG', ?_⟩
    intro v w hv
    by_cases hsym : s(v, w) = s(a, c)
    · simp [adj_of_sym2_eq hsym, symmDiff_def, hM2ac, hnG'ac] at hv
    · simp only [symmDiff_def, sup_adj, sdiff_adj, Subgraph.spanningCoe_adj] at hv
      rw [@Sym2.eq_iff] at hsym
      cases' hv with hl hr
      · have := hl.1.adj_sub
        simp only [sup_adj] at this
        cases' this with h1 h2
        · exact h1
        · simp [edge_adj] at h2
          exact (hsym h2.1).elim
      · simpa [edge_adj, hsym] using hle hr.1
  let cycles := symmDiff M1.spanningCoe M2.spanningCoe
  have hcalt : cycles.IsAlternating M2.spanningCoe := symmDiff_spanningCoe_IsPerfectMatching_IsAlternating_right hM1 hM2

  have hcxb : cycles.Adj x b := by sorry
  have hcac : cycles.Adj a c := by sorry


  by_cases hxc : x ∉ (cycles.connectedComponentMk c).supp
  · use (cycles.induce (cycles.connectedComponentMk c).supp).spanningCoe
    refine ⟨hcalt.induce_supp (cycles.connectedComponentMk c), ?_⟩


    simp only [induce_component_spanningCoe_Adj, hxc, hcac]
    simp only [false_and, not_false_eq_true, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq,
      and_true, true_and, hcac.reachable]
    
    intro v w hvw
    rw [@induce_component_spanningCoe_Adj] at hvw
    unfold cycles at hvw
    rw [@symmDiff_def] at hvw
    simp? at hvw


    sorry
  push_neg at hxc
  -- let cycles := symmDiff M1.spanningCoe M2.spanningCoe

  sorry
