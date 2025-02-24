import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Card


-- import TutteLean.Walk

namespace SimpleGraph
-- universe u
variable {V : Type*} {G : SimpleGraph V}


@[simp]
lemma induce_adj {s : Set V} {G : SimpleGraph V} {v w : V}  (hv : v ∈ s) (hw : w ∈ s) : (G.induce s).spanningCoe.Adj v w ↔ G.Adj v w := by
  aesop

open scoped symmDiff

lemma symmDiff_le (h : G ≤ H) (h' : G' ≤ H') : (G ∆ G') ≤ H ⊔ H' := by
  intro v w hvw
  simp [symmDiff_def] at *
  aesop

-- In as snd_of_toSubgraph_adj
theorem toSubgraph_adj_sndOfNotNil {u v} (p : G.Walk u v) (hpp : p.IsPath)
    (h : v' ∈ p.toSubgraph.neighborSet u) : p.getVert 1 = v' := by
  exact hpp.snd_of_toSubgraph_adj h

lemma not_mem_support_takeUntil_takeUntil [DecidableEq V] {p : G.Walk u v} (w x : V) (h : x ≠ w) (hw : w ∈ p.support) (hx : x ∈ (p.takeUntil w hw).support) :
  w ∉ ((p.takeUntil w hw).takeUntil x hx).support := by
  intro hw'
  have h1 : (((p.takeUntil w hw).takeUntil x hx).takeUntil w hw').length < ((p.takeUntil w hw).takeUntil x hx).length := by
    exact Walk.length_takeUntil_lt _ h.symm
  have h2 : ((p.takeUntil w hw).takeUntil x hx).length < (p.takeUntil w hw).length := by
    exact Walk.length_takeUntil_lt _ h
  simp only [Walk.takeUntil_takeUntil] at h1 h2
  omega

lemma Walk.takeUntilSet {u v} [DecidableEq V] (p : G.Walk u v) (s : Set V) (hs : s.Finite) (h : (s ∩ p.support.toFinset).Nonempty) :
    ∃ x ∈ s, ∃ (hx : x ∈ p.support), (∀ t ∈ s, ∀ w ∈ s, ¬ (p.takeUntil x hx).toSubgraph.Adj t w) := by
  classical
  obtain ⟨x, hx⟩ := h
  simp only [List.coe_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq] at hx
  by_cases hxe : ((s \ {x}) ∩ (p.takeUntil x hx.2).support.toFinset).Nonempty
  · obtain ⟨x', hx', hx'p, h⟩ := (p.takeUntil x hx.2).takeUntilSet (s \ {x}) (Set.Finite.diff hs) hxe
    use x', hx'.1, (p.support_takeUntil_subset _ hx'p)
    rw [takeUntil_takeUntil] at h
    simp only [Set.mem_diff] at h
    intro t ht r hr
    have hx'x : x' ≠ x := hx'.2
    by_cases htrx : t = x ∨ r = x
    · have : x ∉ (p.takeUntil x' (p.support_takeUntil_subset _ hx'p)).support := by
        rw [← takeUntil_takeUntil]
        exact Walk.not_mem_support_takeUntil_takeUntil hx'x hx.2 hx'p
      intro htr
      have := mem_support_of_adj_toSubgraph htr
      have := mem_support_of_adj_toSubgraph htr.symm
      aesop
    push_neg at htrx
    exact h t ⟨ht, by simp [htrx.1]⟩ r ⟨hr, by simp [htrx.2]⟩
  use x, hx.1, hx.2
  intro t ht r hr
  by_cases htrx : t = x ∧ r = x
  · rw [htrx.1, htrx.2]
    exact fun hadj ↦ hadj.ne rfl
  rw [not_and] at htrx
  by_cases htx : t = x
  · subst htx
    have : r ∈ s \ {t} := by simp [htrx rfl, hr]
    simp only [List.coe_toFinset,Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] at hxe
    exact fun hadj ↦ Set.disjoint_left.mp hxe this (mem_support_of_adj_toSubgraph hadj.symm)
  have : t ∈ s \ {x} := by simp [htrx, htx, ht]
  simp only [List.coe_toFinset,Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] at hxe
  exact fun hadj ↦ Set.disjoint_left.mp hxe this (by exact mem_support_of_adj_toSubgraph hadj)
termination_by p.length + s.ncard
decreasing_by
  simp_wf
  simp only [List.coe_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq] at hx
  have := p.length_takeUntil_le hx.2
  rw [Set.ncard_diff (by simp_all)]
  have : 0 < s.ncard := by
    rw [Set.ncard_pos hs]
    use x, hx.1
  simp only [Set.ncard_singleton, gt_iff_lt]
  omega


lemma Walk.takeUntil_snd [DecidableEq V] {u v} {p : G.Walk u v} (hx : x ∈ p.support) (hux : u ≠ x) : (p.takeUntil x hx).snd = p.snd := by
  induction p with
  | nil =>
    simp only [support_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
    exact (hux hx.symm).elim
  | cons h q =>
    simp only [support_cons, List.mem_cons, hux.symm, false_or] at hx
    simp [Walk.takeUntil_cons hx hux]

lemma tutte_part2b [Fintype V] [DecidableEq V] {x b a c : V} {cycles : SimpleGraph V} {M2 : Subgraph (G ⊔ edge a c)} (hM2 : M2.IsPerfectMatching)
    (p : cycles.Walk a x) (hp : p.IsPath) (hcalt : cycles.IsAlternating M2.spanningCoe)
    (hM2nadj : ¬ M2.Adj x a) (hpac : p.toSubgraph.Adj a c) (hnpxb : ¬p.toSubgraph.Adj x b) (hM2ac :  M2.Adj a c) (hgadj : G.Adj x a) (hnxc : x ≠ c)
    (hnab : a ≠ b) (hle : p.toSubgraph.spanningCoe ≤ G ⊔ edge a c) (aux : (c' : V) → c' ≠ a → p.toSubgraph.Adj c' x → M2.Adj c' x):
    ∃ G', G'.IsAlternating M2.spanningCoe ∧ G'.IsCycles ∧ ¬G'.Adj x b ∧ G'.Adj a c ∧ G' ≤ G ⊔ edge a c := by
  use p.toSubgraph.spanningCoe ⊔ edge x a
  refine ⟨IsAlternating.sup_edge (hcalt.spanningCoe p.toSubgraph) (by simp_all) (fun u' hu'x hadj ↦ by
    simpa [← toSubgraph_adj_sndOfNotNil p hp hadj, toSubgraph_adj_sndOfNotNil p hp hpac]) (fun c' hc'a hadj ↦ aux _ hc'a hadj), ?_⟩

  have hfincycle : (p.toSubgraph.spanningCoe ⊔ edge x a).IsCycles := by
    refine fun v hv ↦ hp.isCycles_spanningCoe_toSubgraph_sup_edge hgadj.ne.symm (fun hadj ↦ ?_) hv
    rw [← Walk.mem_edges_toSubgraph, Subgraph.mem_edgeSet] at hadj
    simp [← toSubgraph_adj_sndOfNotNil p hp hadj.symm, toSubgraph_adj_sndOfNotNil p hp hpac] at hnxc

  have hfin3 : ¬(p.toSubgraph.spanningCoe ⊔ edge x a).Adj x b := by
    simp only [sup_adj, Subgraph.spanningCoe_adj, hnpxb, edge_adj]
    aesop

  exact ⟨hfincycle, hfin3, by aesop,
    sup_le_iff.mpr ⟨hle, fun v w hvw ↦ by simpa [sup_adj, edge_adj, adj_congr_of_sym2 _ ((adj_edge _ _).mp hvw).1.symm] using .inl hgadj⟩⟩


theorem tutte_part2 [Fintype V] [DecidableEq V] {x a b c : V} (hxa : G.Adj x a) (hab : G.Adj a b) (hnGxb : ¬G.Adj x b) (hnGac : ¬ G.Adj a c)
    (hnxb : x ≠ b) (hnxc : x ≠ c) (hnac : a ≠ c) (hnbc : b ≠ c)
    (hm1 : ∃ (M : Subgraph (G ⊔ edge x b)), M.IsPerfectMatching)
    (hm2 : ∃ (M : Subgraph (G ⊔ edge a c)), M.IsPerfectMatching)
    : ∃ (M : Subgraph G), M.IsPerfectMatching := by
  classical
  obtain ⟨M1, hM1⟩ := hm1
  obtain ⟨M2, hM2⟩ := hm2

  have hM1nac : ¬M1.Adj a c := fun h ↦ by simpa [hnGac, edge_adj, hnac, hxa.ne, hnbc.symm, hab.ne] using h.adj_sub
  have hM2nxb : ¬M2.Adj x b := fun h ↦ by simpa [hnGxb, edge_adj, hnxb, hxa.ne, hnxc] using h.adj_sub

  by_cases hM1xb : ¬M1.Adj x b
  · use G.toSubgraph M1.spanningCoe (M1.spanningCoe_sup_edge_le _ hM1xb)
    exact (Subgraph.IsPerfectMatching.toSubgraph_iff (M1.spanningCoe_sup_edge_le _ hM1xb)).mpr hM1
  by_cases hM2ac : ¬M2.Adj a c
  · use G.toSubgraph M2.spanningCoe (M2.spanningCoe_sup_edge_le _ hM2ac)
    exact (Subgraph.IsPerfectMatching.toSubgraph_iff (M2.spanningCoe_sup_edge_le _ hM2ac)).mpr hM2
  simp only [not_not] at hM1xb hM2ac

  have hsupG : G ⊔ edge x b ⊔ (G ⊔ edge a c) = (G ⊔ edge a c) ⊔ edge x b := by aesop

  suffices ∃ (G' : SimpleGraph V), G'.IsAlternating M2.spanningCoe ∧ G'.IsCycles ∧ symmDiff M2.spanningCoe G' ≤ G by
    obtain ⟨G', hg⟩ := this
    use (G.toSubgraph (symmDiff M2.spanningCoe G') hg.2.2)
    apply IsPerfectMatching.symmDiff_of_isAlternating hM2 hg.1 hg.2.1

  suffices ∃ (G' : SimpleGraph V), G'.IsAlternating M2.spanningCoe ∧ G'.IsCycles ∧ ¬G'.Adj x b ∧ G'.Adj a c
      ∧ G' ≤ G ⊔ edge a c by
    obtain ⟨G', ⟨hG', hG'cyc, hG'xb, hnG'ac, hle⟩⟩ := this
    use G'
    refine ⟨hG', hG'cyc, ?_⟩
    apply Disjoint.left_le_of_le_sup_right (_root_.symmDiff_le (le_sup_of_le_right M2.spanningCoe_le) (le_sup_of_le_right hle))
    simp [disjoint_edge, symmDiff_def, hM2ac, hnG'ac]

  let cycles := symmDiff M1.spanningCoe M2.spanningCoe
  have hcalt : cycles.IsAlternating M2.spanningCoe := IsPerfectMatching.isAlternating_symmDiff_right hM1 hM2
  have hcycles := Subgraph.IsPerfectMatching.symmDiff_isCycles hM1 hM2

  have hcxb : cycles.Adj x b := by simp [cycles, symmDiff_def, hM2nxb, hM1xb]
  have hcac : cycles.Adj a c := by simp [cycles, symmDiff_def, hM2ac, hM1nac]
  have hM1sub : M1.spanningCoe ≤ G ⊔ edge x b := Subgraph.spanningCoe_le M1
  have hM2sub := Subgraph.spanningCoe_le M2

  have cycles_le : cycles ≤ (G ⊔ edge a c) ⊔ (edge x b) := by
    simp only [← hsupG, cycles]
    exact symmDiff_le hM1sub hM2sub

  have induce_le : (induce (cycles.connectedComponentMk c).supp cycles).spanningCoe ≤ (G ⊔ edge a c) ⊔ edge x b := by
    refine le_trans ?_ cycles_le
    exact spanningCoe_induce_le cycles (cycles.connectedComponentMk c).supp

  by_cases hxc : x ∉ (cycles.connectedComponentMk c).supp
  · use (cycles.induce (cycles.connectedComponentMk c).supp).spanningCoe
    refine ⟨hcalt.mono (spanningCoe_induce_le cycles (cycles.connectedComponentMk c).supp), ?_⟩
    simp only [ConnectedComponent.adj_spanningCoe_induce_supp, hxc, hcac, false_and, not_false_eq_true, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq,
      and_true, true_and, hcac.reachable]
    refine ⟨hcycles.induce_supp (cycles.connectedComponentMk c), Disjoint.left_le_of_le_sup_right induce_le ?_⟩
    rw [disjoint_edge]
    aesop
  push_neg at hxc

  have hacc : a ∈ (cycles.connectedComponentMk c).supp := (ConnectedComponent.mem_supp_congr_adj (cycles.connectedComponentMk c) hcac.symm).mp rfl

  have (G : SimpleGraph V) : LocallyFinite G := fun _ ↦ Fintype.ofFinite _

  have hnM2 (x' : V) (h : x' ≠ c) : ¬ M2.Adj x' a := by
    rw [M2.adj_comm]
    exact hM2.1.not_adj_left_of_ne h.symm hM2ac

  have : ∃ x' ∈ ({x, b} : Set V), ∃ (p : cycles.Walk a x'), p.IsPath ∧
    p.toSubgraph.Adj a c ∧ ¬ p.toSubgraph.Adj x b := by
      obtain ⟨p, hp⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hacc (Set.nonempty_of_mem hcac)
      obtain ⟨p', hp'⟩ := hp.1.exists_isCycle_snd_verts_eq (by
        rwa [hp.1.adj_toSubgraph_iff_of_isCycles hcycles (hp.2 ▸ hacc)])
      obtain ⟨x', hx', hx'p, htw⟩ := Walk.takeUntilSet p' {x, b} (Set.toFinite _) (by
        use x
        simp only [List.coe_toFinset, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          true_or, Set.mem_setOf_eq, true_and, cycles]
        rwa [← @Walk.mem_verts_toSubgraph, hp'.2.2, hp.2])
      use x', hx', p'.takeUntil x' hx'p
      refine ⟨hp'.1.isPath_takeUntil hx'p, ?_, htw _ (by simp : x ∈ {x, b}) _ (by simp : b ∈ {x, b})⟩
      have : (p'.takeUntil x' hx'p).toSubgraph.Adj a (p'.takeUntil x' hx'p).snd := by
        apply SimpleGraph.Walk.toSubgraph_adj_snd
        rw [Walk.nil_takeUntil]
        aesop
      rwa [Walk.takeUntil_snd _ (by aesop), hp'.2.1] at this

  obtain ⟨x', hx', p, hp, hpac, hnpxb⟩ := this

  have hle4 : p.toSubgraph.spanningCoe ≤ G ⊔ edge a c := by
    rw [← sdiff_edge _ (by simpa : ¬ p.toSubgraph.spanningCoe.Adj x b), sdiff_le_iff']
    intro v w hvw
    exact (hsupG ▸ sup_le_sup hM1sub hM2sub) ((symmDiff_le (fun ⦃v w⦄ a => a) fun ⦃v w⦄ a => a) (p.toSubgraph.spanningCoe_le hvw))

  have aux {x' : V} (hx' : x' ∈ ({x, b} : Set V)) (c' : V) : c' ≠ a → p.toSubgraph.Adj c' x' → M2.Adj c' x' := by
    intro hc hadj
    have := hadj.adj_sub
    simp only [cycles, symmDiff_def] at this

    cases' this with hl hr
    · exfalso
      obtain ⟨w, hw⟩ := hM1.1 (hM1.2 x')
      apply hnpxb
      cases' hx' with h1 h2
      · subst h1
        rw [hw.2 _ hM1xb, ← hw.2 _ hl.1.symm]
        exact hadj.symm
      · subst h2
        rw [hw.2 _ hM1xb.symm, ← hw.2 _ hl.1.symm]
        exact hadj
    · exact hr.1

  cases' hx' with hl hl <;> subst hl
  · exact tutte_part2b hM2 p hp hcalt (hnM2 x' hnxc) hpac hnpxb hM2ac hxa hnxc hab.ne hle4 (aux (by simp))
  · conv =>
      enter [1, G', 2, 2, 1, 1]
      rw [adj_comm]
    rw [Subgraph.adj_comm] at hnpxb
    apply tutte_part2b hM2 p hp hcalt (hnM2 _ hnbc) hpac hnpxb hM2ac (hab.symm) hnbc hxa.ne.symm hle4 (aux (by simp))
