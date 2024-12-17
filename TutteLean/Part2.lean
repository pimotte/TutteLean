import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Set.Operations


import TutteLean.Walk

namespace SimpleGraph
-- universe u
variable {V : Type*} {G : SimpleGraph V}

-- Already in: IsPerfectMatching.toSubgraph_spanningCoe_iff
theorem IsPerfectMatching.toSubgraph_spanningCoe {M : Subgraph G} (hM : M.IsPerfectMatching)
    (h : M.spanningCoe ≤ G') : (G'.toSubgraph M.spanningCoe h).IsPerfectMatching := by
  refine ⟨?_, fun v ↦ by simp⟩
  intro v _
  apply hM.1
  simp only [Subgraph.IsSpanning.verts_eq_univ hM.2, Set.mem_univ]

-- In #19377
theorem adj_iff_of_sym2_eq (h : s(v, w) = s(u, t)) : G.Adj v w ↔ G.Adj u t := by
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h
  cases' h with hl hr
  · rw [hl.1, hl.2]
  · rw [hr.1, hr.2, adj_comm]

-- In #19377
theorem Subgraph.adj_iff_of_sym2_eq {H : Subgraph G} (h2 : s(v, w) = s(u, t)) : H.Adj v w ↔ H.Adj u t := by
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h2
  cases' h2 with hl hr
  · rw [hl.1, hl.2]
  · rw [hr.1, hr.2, Subgraph.adj_comm]

-- In #19377
theorem Subgraph.sup_edge_spanningCoe_le {v w : V} {H : Subgraph (G ⊔ edge v w)} (h : ¬ H.Adj v w) :
    H.spanningCoe ≤ G := by
  intro v' w' hvw'
  simp only [Subgraph.spanningCoe_adj] at *
  by_cases hs : s(v', w') = s(v, w)
  · exact (h ((Subgraph.adj_iff_of_sym2_eq hs).mp hvw')).elim
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

-- In #19377
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
  exact @symmDiff_spanningCoe_IsPerfectMatching_IsAlternating_left V G' G M' M hM' hM

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

@[simp]
lemma sup_spanningCoe (H H' : Subgraph G) : (H ⊔ H').spanningCoe = H.spanningCoe ⊔ H'.spanningCoe := by rfl

lemma induce_component_IsCycles (c : G.ConnectedComponent) (h : G.IsCycles)
  : (G.induce c.supp).spanningCoe.IsCycles := by
  intro v ⟨w, hw⟩
  rw [mem_neighborSet, induce_component_spanningCoe_Adj] at hw
  rw [← h ⟨w, hw.2⟩]
  congr
  ext w'
  simp only [mem_neighborSet, induce_component_spanningCoe_Adj, hw, true_and]

-- In #19373
lemma IsPath.getVert_injective {p : G.Walk v w} (hp : p.IsPath) : Set.InjOn p.getVert {i | i ≤ p.length} := by
  intro n hn m hm hnm
  simp at *
  induction p generalizing n m with
  | nil => aesop
  | @cons v w u h p ihp =>
    simp at hn hm hnm
    by_cases hn0 : n = 0 <;> by_cases hm0 : m = 0
    · aesop
    · simp [hn0, Walk.getVert_cons p h hm0] at hnm
      have hvp : v ∉ p.support := by
        aesop
      exact (hvp (Walk.mem_support_iff_exists_getVert.mpr ⟨(m - 1), ⟨hnm.symm, by omega⟩⟩)).elim
    · simp [hm0, Walk.getVert_cons p h hn0] at hnm
      have hvp : v ∉ p.support := by
        aesop
      exact (hvp (Walk.mem_support_iff_exists_getVert.mpr ⟨(n - 1), ⟨hnm, by omega⟩⟩)).elim
    · simp [Walk.getVert_cons _ _ hn0, Walk.getVert_cons _ _ hm0] at hnm
      have hnl : (n - 1) ≤ p.length := by omega
      have hml : (m - 1) ≤ p.length := by omega
      have := ihp (Walk.IsPath.of_cons hp) hnl hml hnm
      omega



lemma IsCycles_Path_mem_support_is_second (p : G.Walk v w) (hw : w ≠ w') (hw' : w' ∈ p.support) (hp : p.IsPath)
    (hadj : G.Adj v w') (hcyc : G.IsCycles) : p.getVert 1 = w' := by
  rw [@Walk.mem_support_iff_exists_getVert] at hw'
  obtain ⟨n, ⟨rfl, hnl⟩⟩ := hw'
  have hnz : n ≠ 0 := by
    intro h
    simp_all only [h, zero_le, Walk.getVert_zero, ne_eq, SimpleGraph.irrefl]
  by_cases hn : n = 1
  · rw [hn]
  have hnp1 : G.Adj (p.getVert n) (p.getVert (n + 1)) := by
    exact (Walk.toSubgraph_adj_getVert p (by
      by_contra! hc
      exact hw (Walk.getVert_of_length_le p hc).symm)).adj_sub
  rw [adj_comm] at hadj
  have hns1 : G.Adj (p.getVert n) (p.getVert (n - 1)) := by
    simpa [show n - 1 + 1 = n from by omega] using (@Walk.toSubgraph_adj_getVert _  _  _ _ p (n - 1) (by omega)).adj_sub.symm
  have := hcyc (Set.nonempty_of_mem hnp1)
  rw [@Set.ncard_eq_two] at this
  obtain ⟨x, y, hxy⟩ := this
  have hvgv : v ∈ G.neighborSet (p.getVert n) := hadj
  have hsgv : p.getVert (n - 1) ∈ G.neighborSet (p.getVert n) := hns1
  have hpgv : p.getVert (n + 1) ∈ G.neighborSet (p.getVert n) := hnp1
  rw [hxy.2] at hvgv hsgv hpgv

  have : p.getVert (n - 1) ≠ p.getVert (n + 1) := by
    by_cases h : n = p.length
    · subst h
      simp_all only [ne_eq, and_true, Set.mem_insert_iff, Set.mem_singleton_iff, le_refl, Walk.getVert_length,
        not_true_eq_false]
    intro h
    apply IsPath.getVert_injective hp (by rw [@Set.mem_setOf]; omega) (by rw [@Set.mem_setOf]; omega) at h

    omega

  have hsnv : p.getVert (n - 1) ≠ v := by
    intro h
    have : p.getVert (n - 1) = p.getVert 0 := by aesop
    apply IsPath.getVert_injective hp (by rw [Set.mem_setOf]; omega) (by rw [Set.mem_setOf]; omega) at this
    omega

  have hpnv : p.getVert (n + 1) ≠ v := by
    have : p.getVert (n + 1) = p.getVert 0 := by aesop
    by_cases h : n = p.length
    · subst h
      simp_all only [ne_eq, and_true, Set.mem_insert_iff, Set.mem_singleton_iff, le_refl, Walk.getVert_length,
        not_true_eq_false]
    apply IsPath.getVert_injective hp (by rw [Set.mem_setOf]; omega) (by rw [Set.mem_setOf]; omega) at this
    omega

  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsgv hpgv
  aesop

lemma subgraphOfAdj_spanningCoe (hadj : G.Adj v w) : (G.subgraphOfAdj hadj).spanningCoe = fromEdgeSet {s(v, w)} := by
  ext v w
  aesop

lemma IsCycles_Reachable_Path [Fintype V] (hcyc : G.IsCycles)
  (p : G.Walk v w) (hp : p.IsPath) :
    (G \ p.toSubgraph.spanningCoe).Reachable w v := by
  by_cases hvw : v = w
  · subst hvw
    use .nil
  have hpn : ¬p.Nil := Walk.not_nil_of_ne hvw
  have : p.toSubgraph.Adj v (p.getVert 1) := by
    simpa [Walk.getVert_zero p] using
      SimpleGraph.Walk.toSubgraph_adj_getVert p (Walk.not_nil_iff_lt_length.mp hpn)
  obtain ⟨w', ⟨hw'1, hw'2⟩⟩ := hcyc.exists_other (this.adj_sub)
  have hnpvw' : ¬ p.toSubgraph.Adj v w' := by
    intro h
    rw [@Walk.toSubgraph_adj_iff] at h
    obtain ⟨i, hi⟩ := h
    by_cases h0 : i = 0
    · aesop
    by_cases h1 : i = 1
    · subst h1
      have : p.getVert 1 ≠ v := by
        intro h
        rw [h] at this
        exact this.ne rfl
      aesop
    by_cases hpi : p.getVert i = v
    · have : p.getVert i = p.getVert 0 := by aesop
      apply IsPath.getVert_injective hp (by rw [Set.mem_setOf]; omega) (by rw [Set.mem_setOf]; omega) at this
      omega
    have : p.getVert (i + 1) = p.getVert 0 := by aesop
    apply IsPath.getVert_injective hp (by rw [Set.mem_setOf]; omega) (by rw [Set.mem_setOf]; omega) at this
    omega
  by_cases hww' : w = w'
  · subst hww'
    have : (G \ p.toSubgraph.spanningCoe).Adj w v := by
      simp only [sdiff_adj, Subgraph.spanningCoe_adj]
      exact ⟨hw'2.symm, fun h ↦ hnpvw' h.symm⟩
    exact this.reachable
  let p' := Walk.cons hw'2.symm p
  have hle : (G \ p'.toSubgraph.spanningCoe) ≤ (G \ p.toSubgraph.spanningCoe) := by
    apply sdiff_le_sdiff (by rfl) ?hcd
    aesop

  have hp'p : p'.IsPath := by
    unfold p'
    rw [@Walk.cons_isPath_iff]
    refine ⟨hp, ?_⟩
    intro hw'
    have := IsCycles_Path_mem_support_is_second _  hww'  hw' hp hw'2 hcyc
    exact hw'1 this

  have p'' := (IsCycles_Reachable_Path hcyc p' hp'p).some


  let pMap := Walk.mapLe hle p''
  have : (G \ p.toSubgraph.spanningCoe).Adj w' v := by
    simp only [sdiff_adj, Subgraph.spanningCoe_adj]
    refine ⟨hw'2.symm, ?_⟩
    intro h
    exact hnpvw' h.symm

  use Walk.append pMap (this.toWalk)
termination_by Fintype.card V + 1 - p.length
decreasing_by
  simp_wf
  have : p.length < Fintype.card V := by exact Walk.IsPath.length_lt hp
  omega

lemma IsCycles_Reachable [Fintype V] (hadj : G.Adj v w) (hcyc : G.IsCycles) :
    (G \ SimpleGraph.fromEdgeSet {s(v, w)}).Reachable v w := by
  -- have := hcyc (Set.nonempty_of_mem hadj)
  have hr := IsCycles_Reachable_Path hcyc hadj.toWalk (by aesop)
  have : fromEdgeSet {s(v, w)} = hadj.toWalk.toSubgraph.spanningCoe := by
    simp only [Walk.toSubgraph, singletonSubgraph_le_iff, subgraphOfAdj_verts, Set.mem_insert_iff,
      Set.mem_singleton_iff, or_true, sup_of_le_left]
    exact Eq.symm (subgraphOfAdj_spanningCoe hadj)
  rw [this]
  exact hr.symm

lemma Walk.toSubgraph_Adj_mem_support_new (p : G.Walk u v) (hp : p.toSubgraph.Adj u' v') : u' ∈ p.support := by
  unfold Walk.toSubgraph at hp
  match p with
  | nil =>
    simp only [singletonSubgraph_adj, Pi.bot_apply] at hp
    exact hp.elim
  | .cons h q =>
    simp only [Subgraph.sup_adj, subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk] at hp
    rw [@support_cons]
    rw [@List.mem_cons_eq]
    cases hp with
    | inl hl =>
      cases hl with
      | inl h1 => left; exact h1.1.symm
      | inr h2 =>
        right
        rw [← h2.2]
        exact start_mem_support q
    | inr hr =>
      right
      exact q.toSubgraph_Adj_mem_support_new hr

lemma Walk.toSubgraph_Adj_mem_support_new' (p : G.Walk u v) (hp : p.toSubgraph.Adj u' v') : v' ∈ p.support := p.toSubgraph_Adj_mem_support_new hp.symm


@[simp]
lemma mem_rotate_support [DecidableEq V] {p : G.Walk u u} (h : v ∈ p.support) : w ∈ (p.rotate h).support ↔ w ∈ p.support := by
  simp only [Walk.rotate.eq_1, Walk.mem_support_append_iff]
  rw [or_comm]
  simp [← Walk.mem_support_append_iff, Walk.take_spec]

lemma cycle_cons_is_not_nil (p : G.Walk u v) (h : G.Adj v u) (hc : (Walk.cons h p).IsCycle) : ¬ p.Nil := by
  have hl := Walk.IsCycle.three_le_length hc
  rw [@Walk.not_nil_iff_lt_length]
  rw [@Walk.length_cons] at hl
  omega


lemma cycle_getVert_injOn (p : G.Walk u u) (hpc : p.IsCycle) : Set.InjOn p.getVert {i | 1 ≤ i ∧ i ≤ p.length} := by
  have hnp : ¬ p.Nil := hpc.not_nil
  rw [← p.cons_tail_eq hpc.not_nil] at hpc
  have hnpt : ¬ p.tail.Nil := cycle_cons_is_not_nil _ _ hpc
  rw [@Walk.cons_isCycle_iff] at hpc
  intro n hn m hm hnm
  rw [← SimpleGraph.Walk.length_tail_add_one hnp, Set.mem_setOf] at hn hm
  have := IsPath.getVert_injective hpc.1 (by omega : n - 1 ≤ p.tail.length) (by omega : m - 1 ≤ p.tail.length)
      (by
        simp [SimpleGraph.Walk.getVert_tail _ hnp, show n - 1 + 1 = n from by omega,
          show m - 1 + 1 = m from by omega]
        exact hnm
        )
  omega

-- In #19611
lemma List.drop_length_sub_one (h : l ≠ []) : List.drop (l.length - 1) l = [l.getLast h] := by
  induction l with
  | nil => aesop
  | cons a l ih =>
    simp
    by_cases hl : l = []
    · aesop
    rw [List.drop_length_cons hl a]
    aesop

-- In #19611
lemma List.nodup_tail_reverse (l : List α) (h : l.get? 0 = l.get? (l.length - 1)) : l.reverse.tail.Nodup ↔ l.tail.Nodup := by
  simp_all only [List.get?_eq_getElem?, List.tail_reverse, List.nodup_reverse]
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hl : l = []
    · aesop
    · rw [List.dropLast_cons_of_ne_nil hl]
      simp only [List.length_cons, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true,
        List.getElem?_eq_getElem, List.getElem_cons_zero, add_tsub_cancel_right,
        lt_add_iff_pos_right, Option.some.injEq] at h
      rw [@List.getElem_cons] at h
      have hln0 :  l.length ≠ 0 := by aesop
      simp [hln0] at h
      simp only [List.tail_cons]
      rw [h]
      have := List.take_append_drop (l.length - 1) l

      have : l.Nodup = (l.dropLast ++ [l.getLast hl]).Nodup := by
        rw [List.dropLast_eq_take]
        rw [← List.drop_length_sub_one]
        aesop
      rw [this]
      rw [List.nodup_append_comm]
      simp_all only [List.take_append_drop, eq_iff_iff, List.nodup_cons, List.singleton_append]
      rw [List.getLast_eq_getElem]
-- In #19611 (variant)
lemma getVert_support_get_new (p : G.Walk u v) (h2 : n ≤ p.length) : p.getVert n = (p.support.get? n) := by
  match p with
  | .nil =>
    simp_all only [Walk.length_nil, nonpos_iff_eq_zero, h2, Walk.getVert_zero, Walk.support_nil,
      List.get?_cons_zero]
  | .cons h q =>
    simp only [Walk.support_cons]
    by_cases hn : n = 0
    · simp only [hn, Walk.getVert_zero, List.get?_cons_zero]
    · push_neg at hn
      nth_rewrite 2 [show n = (n - 1) + 1 from by omega]
      rw [Walk.getVert_cons q h hn, List.get?_cons_succ]
      exact getVert_support_get q (by
        rw [Walk.length_cons] at h2
        exact Nat.sub_le_of_le_add h2
        )
-- In #19611
lemma nodup_eq_endpoints {p : G.Walk u u} : p.reverse.support.tail.Nodup ↔  p.support.tail.Nodup := by
  rw [@Walk.support_reverse]
  refine List.nodup_tail_reverse p.support ?h
  have hp0 := SimpleGraph.Walk.getVert_zero p
  have hpl := SimpleGraph.Walk.getVert_length p
  rw [← getVert_support_get_new _ (by omega)]
  rw [← getVert_support_get_new _ (by
    rw [Walk.length_support]
    omega
    )]
  aesop
-- In #19611
lemma Subgraph.IsCycle.reverse {p : G.Walk u u} (h : p.IsCycle) : p.reverse.IsCycle := by
  have hnp := h.not_nil
  rw [@Walk.isCycle_def] at h ⊢
  refine ⟨h.1.reverse, by
    intro h'
    apply h.2.1
    simp_all [← @Walk.length_eq_zero_iff, Walk.length_reverse]
    , ?_⟩
  rw [nodup_eq_endpoints]
  exact h.2.2


lemma cycle_getVert_injOn' (p : G.Walk u u) (hpc : p.IsCycle) : Set.InjOn p.getVert {i |  i ≤ p.length - 1} := by
  intro n hn m hm hnm
  simp only [Set.mem_setOf_eq] at hn hm
  have hl := hpc.three_le_length
  have h1 : 1 ≤ (p.length - n) ∧ (p.length - n) ≤ p.reverse.length := by
    rw [Walk.length_reverse]
    omega
  have h2 : 1 ≤ (p.length - m) ∧ (p.length - m) ≤ p.reverse.length := by
    rw [Walk.length_reverse]
    omega
  have := cycle_getVert_injOn _ (Subgraph.IsCycle.reverse hpc) h1 h2
  simp only [Walk.getVert_reverse, show p.length - (p.length - n) = n from by omega, hnm,
    show p.length - (p.length - m) = m from by omega, forall_const] at this
  omega


lemma cycle_getVert_endpoint {p : G.Walk u u} (hpc : p.IsCycle) (hl : i ≤ p.length) : p.getVert i = u ↔ i = 0 ∨ i = p.length := by
  refine ⟨?_, by aesop⟩
  intro h
  by_cases hi : i = 0
  · left; exact hi
  right
  apply cycle_getVert_injOn _ hpc (by
    simp only [Set.mem_setOf_eq]; omega) (by
      simp only [Set.mem_setOf_eq, le_refl, and_true]; omega
      )
  rw [h]
  exact (Walk.getVert_length p).symm

lemma cycle_startPoint_neighborSet (p : G.Walk u u) (hpc : p.IsCycle) : p.toSubgraph.neighborSet u = {p.getVert 1, p.getVert (p.length - 1)} := by
  have hl := hpc.three_le_length
  have hadj1 : p.toSubgraph.Adj (p.getVert 0) (p.getVert 1) := SimpleGraph.Walk.toSubgraph_adj_getVert _ (by omega)
  have hadj2 : p.toSubgraph.Adj (p.getVert p.length) (p.getVert (p.length - 1)) :=
    ((show p.length - 1 + 1 = p.length from by omega) ▸ SimpleGraph.Walk.toSubgraph_adj_getVert _ (by omega)).symm
  simp at *
  ext v
  simp_all only [Subgraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hadj
    have hne := hadj.ne
    rw [SimpleGraph.Walk.toSubgraph_adj_iff] at hadj
    obtain ⟨i, hi⟩ := hadj
    by_cases hp : p.getVert i = u
    · rw [cycle_getVert_endpoint hpc (by omega)] at hp
      aesop
    · have hp' : p.getVert (i + 1) = u := by aesop
      rw [cycle_getVert_endpoint hpc (by omega)] at hp'
      cases' hp' with hl hr
      · contradiction
      · rw [← hr]
        right
        simp only [add_tsub_cancel_right]
        aesop
  · aesop

lemma cycle_internal_neighborSet (p : G.Walk u u) (hpc : p.IsCycle) (h : i ≠ 0) (h' : i < p.length): p.toSubgraph.neighborSet (p.getVert i) = {p.getVert (i - 1), p.getVert (i + 1)} := by
  sorry

lemma cycle_getVert_sub_one_neq_getVert_add_one {p : G.Walk u u} (hpc : p.IsCycle) (h : i ≤ p.length) : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
  have hl := hpc.three_le_length
  by_cases hi' : i ≥ p.length - 1
  · rw [SimpleGraph.Walk.getVert_of_length_le _ (by omega : p.length ≤ i + 1)]
    intro h'
    rw [cycle_getVert_endpoint hpc (by omega)] at h'
    omega
  intro h'
  have := cycle_getVert_injOn' _ hpc (by simp; omega) (by simp; omega) h'
  omega

lemma cycle_two_neighbors'' (p : G.Walk u u) (hpc : p.IsCycle) (h : v ∈ p.support): (p.toSubgraph.neighborSet v).ncard = 2 := by
  rw [Set.ncard_eq_two]
  have hpcl :=  Walk.IsCycle.three_le_length hpc
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at h
  obtain ⟨i, hi⟩ := h
  by_cases he : i = 0 ∨ i = p.length
  · have huv : u = v := by aesop
    use p.getVert 1, p.getVert (p.length - 1)
    refine ⟨by
      intro h'
      have := cycle_getVert_injOn' _ hpc (by simp; omega) (by simp) h'
      omega, ?_⟩
    rw [← huv]
    apply cycle_startPoint_neighborSet _ hpc
  push_neg at he
  use p.getVert (i - 1), p.getVert (i + 1)
  rw [← hi.1]
  refine ⟨?_, cycle_internal_neighborSet _ hpc he.1 (by omega)⟩
  exact cycle_getVert_sub_one_neq_getVert_add_one hpc (by omega)



-- lemma Cycle_trip [DecidableEq V] (p : G.Walk u v) (c : G.Walk u u) (hp: p.IsPath) (hc : c.IsCycle) : v ∈ c.support ∨
--     ∃ x, x ∈ c.support ∧ (G.neighborSet x).ncard > 2 := by
--   by_cases hnp : p.Nil
--   · left
--     rw [← hnp.eq]
--     exact Walk.start_mem_support c
--   by_cases h : p.getVert 1 ∈ c.support
--   · cases Cycle_trip p.tail (c.rotate h) (hp.tail hnp) (hc.rotate h) <;> aesop
--   · right
--     use u
--     simp_all only [Walk.start_mem_support, gt_iff_lt, true_and]

--     sorry
-- termination_by p.length
-- decreasing_by
--   simp_wf
--   rw [← SimpleGraph.Walk.length_tail_add_one hnp]
--   omega

lemma Walks_split (p : G.Walk u v) (p' : G.Walk u w) : v ∈ p'.support ∨ (∃ i, i < p.length ∧ i ≤ p'.length ∧ ∀ j ≤ i, p.getVert j = p'.getVert j ∧ p.getVert (i + 1) ≠ p'.getVert (i + 1))  :=
  match p, p' with
  | Walk.nil, p' => by left; aesop

  | Walk.cons h q, .nil => by
      right
      use 0
      aesop
  | Walk.cons h q, Walk.cons h' q' => by
      by_cases heq : q.getVert 0 = q'.getVert 0
      · simp only [Walk.getVert_zero] at heq
        cases' Walks_split q (q'.copy heq.symm (rfl)) with hl hr
        · left
          aesop
        · right
          obtain ⟨i, hi⟩ := hr
          use (i + 1)
          simp only [Walk.length_cons, add_lt_add_iff_right, hi.1, add_le_add_iff_right,
            SimpleGraph.Walk.length_copy _ _ _ ▸ hi.2.1, Walk.getVert_cons_succ, ne_eq, true_and]
          intro j hj
          have := hi.2.2 _ (by omega : j - 1 ≤ i)
          by_cases hj0 : j = 0
          · aesop
          rw [← Walk.getVert_cons _ h hj0, ← Walk.getVert_cons (q'.copy heq.symm (rfl)) (heq ▸ h') hj0] at this
          aesop
      · right
        use 0
        aesop

lemma card_subgraph_argument {H : Subgraph G} (h : G.neighborSet v ≃ H.neighborSet v) : H.Adj v w ↔ G.Adj v w := by
  refine ⟨fun a => a.adj_sub, ?_⟩
  intro hadj
  
  sorry

lemma Path.of_IsCycles [Fintype V] [DecidableEq V] {c : G.ConnectedComponent} (h : G.IsCycles) (hv : v ∈ c.supp)
  (hn : (G.neighborSet v).Nonempty) (hcs : c.supp.Finite):
    ∃ (p : G.Walk v v), p.IsCycle ∧ p.toSubgraph.verts = c.supp := by
  obtain ⟨w, hw⟩ := hn
  simp only [mem_neighborSet] at hw
  have := IsCycles_Reachable hw h
  obtain ⟨u, p, hp⟩ := SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle.mp ⟨hw, this⟩

  have hvp : v ∈ p.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges _ hp.2


  have : p.toSubgraph.verts = c.supp := by
    ext v'
    constructor <;> intro hm
    · have hv'p := (Walk.mem_verts_toSubgraph p).mp hm
      let p' := p.takeUntil _ hv'p
      let p'' : G.Walk u v := p.takeUntil _ (Walk.fst_mem_support_of_mem_edges p hp.2)
      rw [@ConnectedComponent.mem_supp_iff] at hv ⊢
      rw [← hv, @ConnectedComponent.eq]
      use p'.reverse.append p''
    · rw [@ConnectedComponent.mem_supp_iff] at hm hv
      rw [← hv] at hm
      rw [@ConnectedComponent.eq] at hm
      let p' := hm.some
      rw [← SimpleGraph.Walk.toSubgraph_rotate _ hvp]
      simp only [Walk.toSubgraph_rotate, Walk.verts_toSubgraph, Set.mem_setOf_eq]
      cases' Walks_split p'.reverse (p.rotate hvp) with hl hr
      · aesop
      ·
        exfalso
        obtain ⟨i, hi⟩ := hr
        have hadj1 : G.Adj (p'.reverse.getVert i) (p'.reverse.getVert (i + 1)) :=
          (SimpleGraph.Walk.toSubgraph_adj_getVert _ hi.1).adj_sub
        have hnadj : ¬ (p.rotate hvp).toSubgraph.Adj (p'.reverse.getVert i) (p'.reverse.getVert (i + 1)) := by
          sorry
        rw [(hi.2.2 _ (by rfl)).1] at hadj1
        -- have := cycle_internal_neighborSet _ (hp.1.rotate hvp) (by omega) (by omega)
        have := h (Set.nonempty_of_mem hadj1)
        rw [@Set.ncard_eq_two] at this
        obtain ⟨v, w, hvw⟩ := this
        have : v = p'.reverse.getVert (i + 1) ∨ w = p'.reverse.getVert (i + 1) := by

          sorry
        -- have hadj2 : G.Adj ((p.rotate hvp).reverse.getVert (i - 1)) ((p.rotate hvp).reverse.getVert i) :=
        --   (SimpleGraph.Walk.toSubgraph_adj_getVert _ (by

        --     omega)).adj_sub



        sorry

  use p.rotate hvp
  rw [← this]
  refine ⟨?_, by simp_all only [ConnectedComponent.mem_supp_iff, Walk.verts_toSubgraph, Walk.toSubgraph_rotate]⟩
  exact hp.1.rotate _

lemma IsCycle.first_two {p : G.Walk v v} (h : p.IsCycle) (hadj : p.toSubgraph.Adj v w) :
    ∃ (p' : G.Walk v v), p'.IsCycle ∧ p'.getVert 1 = w ∧ p'.toSubgraph.support = p.toSubgraph.support := by
  sorry

lemma IsCycle_takeUntil [DecidableEq V] {p : G.Walk v v} (h : p.IsCycle) (h : w ∈ p.support) (hvw : v ≠ w) :
    (p.takeUntil w h).IsPath := by

  sorry

lemma takeUntil_getVert_one [DecidableEq V] {p : G.Walk u v} (hsu : w ≠ u) (h : w ∈ p.support)
  : (p.takeUntil w h).getVert 1 = p.getVert 1 := by
  sorry

theorem tutte_part2 [Fintype V] [DecidableEq V] {x a b c : V} (hxa : G.Adj x a) (hab : G.Adj a b) (hnGxb : ¬G.Adj x b) (hnGac : ¬ G.Adj a c)
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
    · simp [adj_iff_of_sym2_eq hsym, symmDiff_def, hM2ac, hnG'ac] at hv
    · simp only [symmDiff_def, sup_adj, sdiff_adj] at hv
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
    have : G ⊔ edge x b ⊔ (G ⊔ edge a c) = (G ⊔ edge a c) ⊔ edge x b := by
      -- is aesop
      simp_all only [ne_eq, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq, sup_adj, cycles]
      obtain ⟨left, right⟩ := hvw
      cases hs with
      | inl h =>
        cases h with
        | inl h_1 =>
          ext x_1 x_2 : 4
          simp_all only [sup_adj]
          apply Iff.intro
          · intro a_1
            cases a_1 with
            | inl h =>
              cases h with
              | inl h_2 => simp_all only [true_or]
              | inr h_3 => simp_all only [or_true]
            | inr h_2 =>
              cases h_2 with
              | inl h => simp_all only [true_or]
              | inr h_3 => simp_all only [or_true, true_or]
          · intro a_1
            cases a_1 with
            | inl h =>
              cases h with
              | inl h_2 => simp_all only [true_or, or_self]
              | inr h_3 => simp_all only [or_true]
            | inr h_2 => simp_all only [or_true, true_or]
        | inr h_2 =>
          ext x_1 x_2 : 4
          simp_all only [sup_adj]
          apply Iff.intro
          · intro a_1
            cases a_1 with
            | inl h =>
              cases h with
              | inl h_1 => simp_all only [true_or]
              | inr h_3 => simp_all only [or_true]
            | inr h_1 =>
              cases h_1 with
              | inl h => simp_all only [true_or]
              | inr h_3 => simp_all only [or_true, true_or]
          · intro a_1
            cases a_1 with
            | inl h =>
              cases h with
              | inl h_1 => simp_all only [true_or, or_self]
              | inr h_3 => simp_all only [or_true]
            | inr h_1 => simp_all only [or_true, true_or]
      | inr h_1 =>
        cases h_1 with
        | inl h =>
          ext x_1 x_2 : 4
          simp_all only [sup_adj]
          apply Iff.intro
          · intro a_1
            cases a_1 with
            | inl h_1 =>
              cases h_1 with
              | inl h_2 => simp_all only [true_or]
              | inr h_3 => simp_all only [or_true]
            | inr h_2 =>
              cases h_2 with
              | inl h_1 => simp_all only [true_or]
              | inr h_3 => simp_all only [or_true, true_or]
          · intro a_1
            cases a_1 with
            | inl h_1 =>
              cases h_1 with
              | inl h_2 => simp_all only [true_or, or_self]
              | inr h_3 => simp_all only [or_true]
            | inr h_2 => simp_all only [or_true, true_or]
        | inr h_2 =>
          ext x_1 x_2 : 4
          simp_all only [sup_adj]
          apply Iff.intro
          · intro a_1
            cases a_1 with
            | inl h =>
              cases h with
              | inl h_1 => simp_all only [true_or]
              | inr h_3 => simp_all only [or_true]
            | inr h_1 =>
              cases h_1 with
              | inl h => simp_all only [true_or]
              | inr h_3 => simp_all only [or_true, true_or]
          · intro a_1
            cases a_1 with
            | inl h =>
              cases h with
              | inl h_1 => simp_all only [true_or, or_self]
              | inr h_3 => simp_all only [or_true]
            | inr h_1 => simp_all only [or_true, true_or]

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
      obtain ⟨p, hp⟩ := Path.of_IsCycles hcycles hacc (Set.nonempty_of_mem hcac) (Set.toFinite _)
      obtain ⟨p', hp'⟩ := IsCycle.first_two hp.1 (by

        sorry : p.toSubgraph.Adj a c)
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
