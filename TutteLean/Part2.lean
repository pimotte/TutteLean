import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Path


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

def IsCycles (G : SimpleGraph V) := ∀ ⦃v⦄, (G.neighborSet v).Nonempty → (G.neighborSet v).ncard = 2

-- In #19250
lemma IsCycles.exists_other (h : G.IsCycles) (hadj : G.Adj v w) : ∃ w', w ≠ w' ∧ G.Adj v w' := by
  sorry

def IsAlternating (G : SimpleGraph V) (G' : SimpleGraph V) :=
  ∀ {v w w': V}, w ≠ w' → G.Adj v w → G.Adj v w' → (G'.Adj v w ↔ ¬ G'.Adj v w')

-- In #19250
lemma symmDiff_spanningCoe_IsPerfectMatching_IsCycles
    {M : Subgraph G} {M' : Subgraph G'} (hM : M.IsPerfectMatching)
    (hM' : M'.IsPerfectMatching) : (symmDiff M.spanningCoe M'.spanningCoe).IsCycles := by
  sorry

-- In #19250
lemma IsPerfectMatching.symmDiff_spanningCoe_of_IsAlternating {M : Subgraph G} (hM : M.IsPerfectMatching)
    (hG' : G'.IsAlternating M.spanningCoe) (hG'cyc : G'.IsCycles)  :
    ((symmDiff M.spanningCoe G').toSubgraph (symmDiff M.spanningCoe G') (by rfl)).IsPerfectMatching := by
  sorry

lemma spanningCoe_adj {v w : V} {s : Set V} (G : SimpleGraph s) (hv : v ∈ s) (hw : w ∈ s) : (SimpleGraph.spanningCoe G).Adj v w ↔ G.Adj ⟨v, hv⟩ ⟨w, hw⟩ := by
  simp_all only [map_adj, Function.Embedding.coe_subtype, Subtype.exists, exists_and_right, exists_eq_right_right,
    exists_true_left, exists_eq_right]


lemma mem_spanningCoe_of_adj {v w : V} {s : Set V} (G : SimpleGraph s) (hadj : G.spanningCoe.Adj v w) : v ∈ s := by
  aesop


@[simp]
lemma induce_adj {s : Set V} {G : SimpleGraph V} {v w : V}  (hv : v ∈ s) (hw : w ∈ s) : (G.induce s).spanningCoe.Adj v w ↔ G.Adj v w := by
  aesop


lemma IsAlternating.induce_supp (c : G.ConnectedComponent) (h : G.IsAlternating G') : (G.induce c.supp).spanningCoe.IsAlternating G' := by
  intro v w w' hww' hvw hvw'
  have h1 := mem_spanningCoe_of_adj (induce c.supp G) hvw
  have h2 : w ∈ c.supp := mem_spanningCoe_of_adj (induce c.supp G) (id (adj_symm (induce c.supp G).spanningCoe hvw))
  have h3 : w' ∈ c.supp := mem_spanningCoe_of_adj (induce c.supp G) (id (adj_symm (induce c.supp G).spanningCoe hvw'))
  rw [induce_adj h1 h2] at hvw
  rw [induce_adj h1 h3] at hvw'
  exact h hww' hvw hvw'

open scoped symmDiff

lemma symmDiff_spanningCoe_IsPerfectMatching_IsAlternating_left
    {M : Subgraph G} {M' : Subgraph G'} (hM : M.IsPerfectMatching)
    (hM' : M'.IsPerfectMatching) : (M.spanningCoe ∆ M'.spanningCoe).IsAlternating M.spanningCoe := by
  intro v w w' hww' hvw hvw'
  obtain ⟨v1, ⟨hm1, hv1⟩⟩ := hM.1 (hM.2 v)
  obtain ⟨v2, ⟨hm2, hv2⟩⟩ := hM'.1 (hM'.2 v)
  simp only [ne_eq, symmDiff_def, sup_adj, sdiff_adj, Subgraph.spanningCoe_adj] at *
  aesop


lemma symmDiff_spanningCoe_IsPerfectMatching_IsAlternating_right
    {M : Subgraph G} {M' : Subgraph G'} (hM : M.IsPerfectMatching)
    (hM' : M'.IsPerfectMatching) : (symmDiff M.spanningCoe M'.spanningCoe).IsAlternating M'.spanningCoe := by
  rw [symmDiff_comm]
  apply symmDiff_spanningCoe_IsPerfectMatching_IsAlternating_left

lemma symmDiff_le (h : G ≤ H) (h' : G' ≤ H') : (symmDiff G G') ≤ H ⊔ H' := by
  intro v w hvw
  simp [symmDiff_def] at *
  aesop

lemma mem_supp_of_adj {c : G.ConnectedComponent} (h : v ∈ c.supp) (h' : G.Adj v w) : w ∈ c.supp := by
  simp only [ConnectedComponent.mem_supp_iff] at *
  rw [← h]
  exact ConnectedComponent.connectedComponentMk_eq_of_adj h'.symm


lemma induce_component_spanningCoe_Adj (c : G.ConnectedComponent) :
  (G.induce c.supp).spanningCoe.Adj v w ↔ v ∈ c.supp ∧ G.Adj v w := by
  by_cases h : v ∈ c.supp
  · simp only [h, true_and]
    constructor
    · aesop
    · intro h'
      have : w ∈ c.supp := by
        exact mem_supp_of_adj h h'
      aesop
  · aesop

lemma induce_component_IsCycles (c : G.ConnectedComponent) (h : G.IsCycles)
  : (G.induce c.supp).spanningCoe.IsCycles := by
  intro v ⟨w, hw⟩
  rw [mem_neighborSet, induce_component_spanningCoe_Adj] at hw
  rw [← h ⟨w, hw.2⟩]
  congr
  ext w'
  simp only [mem_neighborSet, induce_component_spanningCoe_Adj, hw, true_and]


lemma Path.of_IsCycles [DecidableEq V] {c : G.ConnectedComponent} (h : G.IsCycles) (hv : v ∈ c.supp)
  (hn : (G.neighborSet v).Nonempty) (hcs : c.supp.Finite):
    ∃ (p : G.Walk v v), p.IsCycle ∧ p.toSubgraph.support = c.supp := by
  obtain ⟨w, hw⟩ := hn
  let p : G.Walk v w := Adj.toWalk hw
  let rec f {u : V} (p : G.Walk u v) (hs : p.toSubgraph.support ⊆ c.supp) : G.Walk v v :=
    if huv : u = v then
      huv ▸ p
    else
      (f (Walk.cons (h.exists_other (by sorry : G.Adj u (p.getVert 1))).choose_spec.2.symm p) (by sorry))
  termination_by c.supp.ncard + 1 - p.length
  decreasing_by {
    simp_wf
    have : p.toSubgraph.support.ncard ≤ c.supp.ncard := by sorry

    done
  }

  sorry

lemma IsCycle.first_two {p : G.Walk v v} (h : p.IsCycle) (hadj : p.toSubgraph.Adj v w) :
    ∃ (p' : G.Walk v v), p'.IsCycle ∧ p'.getVert 1 = w ∧ p'.toSubgraph.support = p.toSubgraph.support := by
  sorry

lemma IsCycle_takeUntil [DecidableEq V] {p : G.Walk v v} (h : p.IsCycle) (h : w ∈ p.support) (hvw : v ≠ w) :
    (p.takeUntil w h).IsPath := by

  sorry

lemma takeUntil_getVert_one [DecidableEq V] {p : G.Walk u v} (hsu : w ≠ u) (h : w ∈ p.support)
  : (p.takeUntil w h).getVert 1 = p.getVert 1 := by
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

  suffices ∃ (G' : SimpleGraph V), G'.IsAlternating M2.spanningCoe ∧ G'.IsCycles ∧ symmDiff M2.spanningCoe G' ≤ G by
    obtain ⟨G', hg⟩ := this
    use (G.toSubgraph (symmDiff M2.spanningCoe G') hg.2.2)
    apply IsPerfectMatching.symmDiff_spanningCoe_of_IsAlternating hM2 hg.1 hg.2.1

  suffices ∃ (G' : SimpleGraph V), G'.IsAlternating M2.spanningCoe ∧ G'.IsCycles  ∧ ¬G'.Adj x b ∧ G'.Adj a c
      ∧ G' ≤ G ⊔ edge a c by
    obtain ⟨G', ⟨hG', hG'cyc, hG'xb, hnG'ac, hle⟩⟩ := this
    use G'
    refine ⟨hG', hG'cyc, ?_⟩
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
  have hcycles := symmDiff_spanningCoe_IsPerfectMatching_IsCycles hM1 hM2
  have hcxb : cycles.Adj x b := by sorry
  have hcac : cycles.Adj a c := by sorry

  have hM1sub : M1.spanningCoe ≤ G ⊔ edge x b := Subgraph.spanningCoe_le M1
  have hM2sub := Subgraph.spanningCoe_le M2

  by_cases hxc : x ∉ (cycles.connectedComponentMk c).supp
  · use (cycles.induce (cycles.connectedComponentMk c).supp).spanningCoe
    refine ⟨hcalt.induce_supp (cycles.connectedComponentMk c), ?_⟩

    simp only [induce_component_spanningCoe_Adj, hxc, hcac]
    simp only [false_and, not_false_eq_true, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq,
      and_true, true_and, hcac.reachable]
    refine ⟨induce_component_IsCycles (cycles.connectedComponentMk c) hcycles, ?_⟩
    intro v w hvw
    rw [@induce_component_spanningCoe_Adj] at hvw
    have hs := symmDiff_le hM1sub hM2sub hvw.2
    have : G ⊔ edge x b ⊔ (G ⊔ edge a c) = (G ⊔ edge a c) ⊔ edge x b := by sorry
    rw [this, sup_adj] at hs
    cases' hs with h1 h2
    · exact h1
    · simp only [edge_adj, ne_eq] at h2
      cases' h2.1 with hl hr
      · rw [hl.1] at hvw
        exact (hxc hvw.1).elim
      · rw [hr.2] at hvw
        have : x ∈ (cycles.connectedComponentMk c) := by
          exact mem_supp_of_adj hvw.1 hvw.2
        exact (hxc this).elim
  push_neg at hxc

  have hacc : a ∈ (cycles.connectedComponentMk c).supp := by
    exact mem_supp_of_adj rfl hcac.symm


  have : ∃ x' ∈ ({x, b} : Set V), ∃ (p : cycles.Walk a x'), p.IsPath ∧
    p.toSubgraph.Adj a c ∧ ¬ p.toSubgraph.Adj x b := by
      obtain ⟨p, hp⟩ := Path.of_IsCycles hcycles hacc (Set.nonempty_of_mem hcac)
      obtain ⟨p', hp'⟩ := IsCycle.first_two hp.1 (by sorry : p.toSubgraph.Adj a c)
      have hxp' : x ∈ p'.support := by sorry
      have : DecidableEq V := by exact Classical.typeDecidableEq V
      by_cases hc : b ∈ (p'.takeUntil x hxp').support
      · use b, (by simp), ((p'.takeUntil x hxp').takeUntil b hc)

        refine ⟨(IsCycle_takeUntil hp'.1 hxp' hxa.ne').takeUntil hc, ?_⟩
        constructor
        · have : 0 < ((p'.takeUntil x hxp').takeUntil b hc).length := by sorry
          have := ((p'.takeUntil x hxp').takeUntil b hc).toSubgraph_adj_getVert this
          rw [takeUntil_getVert_one (by sorry) (by sorry)] at this
          rw [takeUntil_getVert_one (by sorry) (by sorry)] at this
          simp at this
          rw [hp'.2.1] at this
          exact this
        ·
          sorry
      · use x, (by simp), (p'.takeUntil x hxp')
        sorry

  obtain ⟨x', hx', p, hp, hpac, hnpxb⟩ := this

  use p.toSubgraph.spanningCoe ⊔ edge x' a

  sorry
