import TutteLean.Defs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Metric

import TutteLean.Set

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

lemma walk_length_one_adj : (∃ (p : G.Walk u v), p.length = 1) ↔ G.Adj u v := by
  constructor
  · rintro ⟨p , hp⟩
    match p with
    | Walk.nil' u => simp only [Walk.length_nil, zero_ne_one] at hp
    | Walk.cons' u v w h p' =>
      simp only [Walk.length_cons, add_left_eq_self] at hp
      exact ((SimpleGraph.Walk.eq_of_length_eq_zero hp) ▸ h)
  · intro h
    use Walk.cons h Walk.nil
    simp only [Walk.length_cons, Walk.length_nil, zero_add]

lemma dist_gt_one_of_ne_and_nadj (h : G.Reachable u v) (hne : u ≠ v) (hnadj : ¬G.Adj u v) : 1 < G.dist u v := by
  have : 1 ≠ G.dist u v := by
    by_contra! hc
    obtain ⟨p, hp⟩ := Reachable.exists_path_of_dist h
    rw [← hc] at hp
    exact hnadj (walk_length_one_adj.mp ⟨p, hp.2⟩)
  exact Nat.lt_of_le_of_ne (h.pos_dist_of_ne hne) this


noncomputable def lift_walk {c : ConnectedComponent G} {v w : c.supp}  (p : G.Walk v w) : (G.induce c.supp).Walk v w :=
  if hp : p.Nil
  then
    Subtype.val_injective (SimpleGraph.Walk.Nil.eq hp) ▸ Walk.nil
  else
    let u := (SimpleGraph.Walk.not_nil_iff.mp hp).choose
    let h := (SimpleGraph.Walk.not_nil_iff.mp hp).choose_spec.choose
    let q := (SimpleGraph.Walk.not_nil_iff.mp hp).choose_spec.choose_spec.choose
    let h' := (SimpleGraph.Walk.not_nil_iff.mp hp).choose_spec.choose_spec.choose_spec
    have hu : u ∈ c.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff,
        ← (c.mem_supp_iff w).mp w.coe_prop,
        ConnectedComponent.eq]
      exact Walk.reachable q
    let u' : c.supp := ⟨u , hu⟩
    Walk.cons (by simp only [comap_adj, Function.Embedding.coe_subtype, h] : (G.induce c.supp).Adj v u') (lift_walk q)
termination_by p.length
decreasing_by
  simp_wf
  rw [@Nat.lt_iff_add_one_le]
  rw [← SimpleGraph.Walk.length_cons]
  exact Nat.le_of_eq (congrArg Walk.length (id h'.symm))

noncomputable def lift_walk' {H : Subgraph G} {c : ConnectedComponent H.coe} (v w : (H.induce (Subtype.val '' c.supp)).verts) (hH : H.IsSpanning)
    (p : H.coe.Walk ⟨v, hH v⟩ ⟨w, hH w⟩) : (H.induce c.supp).coe.Walk v w :=
  if hp : p.Nil
  then
    (Set.inclusion_inj fun ⦃a⦄ a_1 => hH a).mp hp.eq ▸ Walk.nil
  else
    let u := (SimpleGraph.Walk.not_nil_iff.mp hp).choose
    let h := (SimpleGraph.Walk.not_nil_iff.mp hp).choose_spec.choose
    let q := (SimpleGraph.Walk.not_nil_iff.mp hp).choose_spec.choose_spec.choose
    let h' := (SimpleGraph.Walk.not_nil_iff.mp hp).choose_spec.choose_spec.choose_spec
    have hu : u.val ∈ (H.induce (Subtype.val '' c.supp)).verts := by
      rw [@Subgraph.induce_verts]
      refine Set.mem_image_val_of_mem (hH ↑u) ?ha'
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff,
        ← (c.mem_supp_iff ⟨w, hH w⟩).mp (by
          have := w.2
          simp only [Subgraph.induce_verts, Set.mem_image, ConnectedComponent.mem_supp_iff,
            Subtype.exists, exists_and_right, exists_eq_right] at this
          simp only [Subgraph.induce_verts, ConnectedComponent.mem_supp_iff]
          obtain ⟨_, hx⟩ := this
          exact hx
          ),
        ConnectedComponent.eq]
      exact Walk.reachable q
    have hadj : (H.induce c.supp).coe.Adj v ⟨u, hu⟩ := by
      simp only [Subgraph.induce_verts, Subgraph.coe_adj, Subgraph.induce_adj, Set.mem_image,
        ConnectedComponent.mem_supp_iff, Subtype.exists, exists_and_right, exists_eq_right,
        Subtype.coe_eta, Subtype.coe_prop, exists_const]
      have := v.2
      simp only [Subgraph.induce_verts, Set.mem_image, ConnectedComponent.mem_supp_iff,
        Subtype.exists, exists_and_right, exists_eq_right] at this
      simp only [true_and]
      refine ⟨?_, ?_⟩
      · rw [← (c.mem_supp_iff ⟨u, hH u⟩).mp (by
          exact Set.mem_of_mem_image_val hu
          )]
      · simp only [Subgraph.induce_verts, Subgraph.coe_adj] at h
        exact h


    Walk.cons hadj (lift_walk' ⟨u, hu⟩ w hH q)
termination_by p.length
decreasing_by
  simp_wf
  rw [@Nat.lt_iff_add_one_le]
  rw [← SimpleGraph.Walk.length_cons]
  exact Nat.le_of_eq (congrArg Walk.length (id h'.symm))

lemma reachable_in_connected_component_induce (c : ConnectedComponent G) (v w : c.supp) : (G.induce c.supp).Reachable v w := by
  have hvc := (c.mem_supp_iff v).mp (Subtype.coe_prop v)
  have hwc := (c.mem_supp_iff w).mp (Subtype.coe_prop w)
  have : G.connectedComponentMk v = G.connectedComponentMk w := by
    rw [hvc, hwc]
  have p := (Classical.inhabited_of_nonempty (ConnectedComponent.exact this)).default
  exact Walk.reachable (lift_walk p)

lemma reachable_in_connected_component_induce_coe {H : Subgraph G} (hH : H.IsSpanning) (c : ConnectedComponent H.coe) (v w : (H.induce (Subtype.val '' c.supp)).verts) : (H.induce c.supp).coe.Reachable v w := by
  have hm (x : (H.induce (Subtype.val '' c.supp)).verts) : ⟨x.val, hH x.val⟩ ∈ c.supp := by
    have := x.2
    simp only [Subgraph.induce_verts, Set.mem_image, ConnectedComponent.mem_supp_iff,
      Subtype.exists, exists_and_right, exists_eq_right] at this
    obtain ⟨_, hv⟩ := this
    rw [@ConnectedComponent.mem_supp_iff]
    exact hv

  have hvc := (c.mem_supp_iff ⟨v.val , hH v.val⟩).mp (hm v)
  have hwc := (c.mem_supp_iff ⟨w.val , hH w.val⟩).mp (hm w)
  have : H.coe.connectedComponentMk ⟨↑v, hH v.val⟩  = H.coe.connectedComponentMk ⟨↑w, hH w.val⟩  := by
    rw [hvc, hwc]
  have p := (Classical.inhabited_of_nonempty (ConnectedComponent.exact this)).default
  apply Walk.reachable
  exact lift_walk' _ _ hH p


lemma verts_of_walk (p : G.Walk v w) (hp : p.length = G.dist v w) (hl : 1 < G.dist v w) : ∃ (x a b : V), G.Adj x a ∧ G.Adj a b ∧ ¬ G.Adj x b ∧ x ≠ b := by

  have hnp : ¬p.Nil := by
    rw [SimpleGraph.Walk.nil_iff_length_eq]
    rw [hp]
    exact Nat.not_eq_zero_of_lt hl


  have hnt : ¬p.tail.Nil := by
    rw [SimpleGraph.Walk.nil_iff_length_eq]
    rw [← hp] at hl
    rw [← (SimpleGraph.Walk.length_tail_add_one hnp)] at hl
    rw [@Nat.lt_add_left_iff_pos] at hl
    exact Nat.not_eq_zero_of_lt hl

  use v
  use p.getVert 1
  use p.tail.getVert 1
  -- simp? [ne_eq, Walk.adj_getVert_one, Walk.adj_getVert_succ]
  refine ⟨Walk.adj_getVert_one hnp, ?_, ?_⟩
  · rw [Walk.getVert_tail p hnp]
    simp [Walk.adj_getVert_succ _ (Nat.lt_of_lt_of_eq hl hp.symm)]
  constructor
  · intro hadj
    let pcon := Walk.cons hadj p.tail.tail
    have hdist : pcon.length < G.dist v w := by
      rw [← hp]
      rw [@Walk.length_cons]
      rw [Walk.length_tail_add_one hnt]
      apply @Nat.lt_of_add_lt_add_right _ _ 1
      rw [Walk.length_tail_add_one hnp]
      exact lt_add_one p.length

    linarith [SimpleGraph.dist_le pcon]
  · intro heq
    let pcon := p.tail.tail
    have hdist : pcon.length < G.dist (p.tail.getVert 1) w := by
      apply @Nat.lt_of_add_lt_add_right _ _ 1
      rw [Walk.length_tail_add_one hnt]
      rw [← heq]
      apply @Nat.lt_of_add_lt_add_right _ _ 1
      rw [Walk.length_tail_add_one hnp]
      rw [hp]
      omega
    linarith [SimpleGraph.dist_le pcon]



lemma union_gt_iff : G < G ⊔ G' ↔ ¬ (G' ≤ G) := by
  constructor
  · intro h h'
    simp only [sup_of_le_left h', lt_self_iff_false] at h
  · intro h
    exact left_lt_sup.mpr h




def Subgraph.coeBig (H : Subgraph G) : SimpleGraph V := {
  Adj := fun v w => H.Adj v w
  symm := fun v w => by
    exact fun a => (adj_symm H a)
  loopless := Subgraph.loopless H
}

structure Walk.IsAlternating (p : G.Walk u v) (M : Subgraph G) where
  halt : ∀ (v w w': V), w ≠ w' → p.toSubgraph.Adj v w → p.toSubgraph.Adj v w' → (M.Adj v w ↔ ¬ M.Adj v w')


lemma reverse_Nil (p : G.Walk u v) : p.reverse.Nil ↔ p.Nil := by
  rw [@Walk.nil_iff_length_eq]
  rw [SimpleGraph.Walk.length_reverse]
  exact Walk.nil_iff_length_eq.symm


def Walk.lastButOneOfNotNil (p : G.Walk u v) := p.getVert (p.length - 1)


lemma mem_reverse_support (p : G.Walk u v) (w : V) : w ∈ p.support ↔ w ∈ p.reverse.support := by
  rw [SimpleGraph.Walk.mem_support_iff_exists_append]
  rw [SimpleGraph.Walk.mem_support_iff_exists_append]
  constructor
  · rintro ⟨q, r, hqr⟩
    use r.reverse
    use q.reverse
    exact hqr ▸ Walk.reverse_append q r
  · rintro ⟨q, r, hqr⟩
    use r.reverse
    use q.reverse
    rw [← Walk.reverse_reverse p]
    exact hqr ▸ Walk.reverse_append q r

lemma lastButOneOfNotNil_mem_support (p : G.Walk u v) : p.lastButOneOfNotNil ∈ p.support := by
  unfold Walk.lastButOneOfNotNil
  rw [@Walk.mem_support_iff_exists_getVert]
  use (p.length - 1)
  simp

lemma cycle_neq_not_nil (p : G.Walk u u) (hpc : p.IsCycle) : ¬p.Nil := by
  intro hp
  apply hpc.1.2
  rw [← @Walk.length_eq_zero_iff]
  exact Walk.nil_iff_length_eq.mp hp


lemma support_tail_length (p : G.Walk v w) : p.support.tail.length = p.length := by
  match p with
  | .nil => simp only [Walk.support_nil, List.tail_cons, List.length_nil, Walk.length_nil]
  | .cons _ _ => simp only [Walk.support_cons, List.tail_cons, Walk.length_support, Walk.length_cons]

lemma support_length (p : G.Walk v w) : p.support.length = p.length + 1 := by
  match p with
  | .nil => simp only [Walk.support_nil, List.length_singleton, Walk.length_nil, zero_add]
  | .cons _ _ => simp only [Walk.support_cons, List.length_cons, Walk.length_support,
    Nat.succ_eq_add_one, Walk.length_cons]

lemma get?_nonZero (a : α) (l : List α) (h : n ≠ 0) : (a :: l).get? n = l.get? (n - 1) := by
    have : ∃ (i : ℕ), i.succ = n := by
      use (n - 1)
      exact Nat.sub_one_add_one_eq_of_pos (Nat.zero_lt_of_ne_zero h)
    obtain ⟨i, hi⟩ := this
    rw [← hi]
    simp only [Nat.succ_eq_add_one, List.get?_cons_succ, add_tsub_cancel_right]

lemma tail_get? (l : List α) : l.tail.get? n = l.get? (n + 1) := by
  match l with
  | [] =>
    simp only [List.tail_nil, List.get?_nil]
  | _ :: _ =>
    simp only [List.tail_cons, List.get?_cons_succ]



lemma getVert_support_get (p : G.Walk u v) (h2 : n ≤ p.length) : p.getVert n = p.support.get? n := by
  match p with
  | .nil =>
    simp only [Walk.length_nil, nonpos_iff_eq_zero] at h2
    simp only [h2, Walk.getVert_zero, Walk.support_nil, List.get?_cons_zero]
  | .cons h q =>
    simp only [Walk.support_cons]
    by_cases hn : n = 0
    · simp only [hn, Walk.getVert_zero, List.get?_cons_zero]
    · push_neg at hn
      rw [Walk.getVert_cons q h hn]
      rw [get?_nonZero _ _ hn]
      exact getVert_support_get q (by
        rw [@Walk.length_cons] at h2
        exact Nat.sub_le_of_le_add h2
        )

lemma cycle_getVert_sub_neq_getVert_add (p : G.Walk u u) (hpc : p.IsCycle) (h1 : 0 < n) (h2 : n < p.length) : ¬p.getVert (n - 1) = p.getVert (n + 1) := by
  have hnodup := hpc.2
  rw [@List.nodup_iff_get?_ne_get?] at hnodup
  by_cases h : n = 1
  · have : p.getVert (n - 1) = u := by
      simp [h]
    rw [this]
    intro h'
    have hgl : p.getVert p.length = u := Walk.getVert_length p
    have hpl := SimpleGraph.Walk.IsCycle.three_le_length hpc
    have := hnodup n (p.length - 1) (by
      rw [h]
      omega)
      (by
        simp [hpl]
        omega
        )
    apply this
    rw [h]
    rw [tail_get?]
    rw [tail_get?]
    rw [← getVert_support_get _ (by omega)]
    rw [← getVert_support_get _ (by omega)]
    simp only [Nat.reduceAdd, Option.some.injEq]
    rw [h] at h'
    simp only [Nat.reduceAdd] at h'
    rw [← h']
    have : p.length - 1 + 1 = p.length := by omega
    rw [this]
    exact hgl.symm
  ·
    have := hnodup (n - 2) n (Nat.sub_lt h1 (by simp : 0 < 2)) (support_tail_length p ▸ h2)
    push_neg
    rw [tail_get?] at this
    rw [tail_get?] at this
    have h' : n - 2 + 1 = n - 1 := by omega
    rw [h'] at this
    rw [← getVert_support_get _ (by
      calc
        n - 1 ≤ n := Nat.sub_le n 1
        _ ≤  p.length := Nat.le_of_succ_le h2
      )] at this
    rw [← getVert_support_get _ h2] at this

    exact fun a => this (congrArg some a)

lemma path_getVert_sub_neq_getVert_add (p : G.Walk u v) (hpp : p.IsPath) (h1 : 0 < n) (h2 : n < p.length) : ¬p.getVert (n - 1) = p.getVert (n + 1) := by
  have hnodup := hpp.2
  rw [@List.nodup_iff_get?_ne_get?] at hnodup
  have := hnodup (n - 1) (n + 1) (by omega) (by
    rw [SimpleGraph.Walk.length_support]
    omega
    )
  rw [← getVert_support_get _ (by omega)] at this
  rw [← getVert_support_get _ (by omega)] at this
  exact fun a => this (congrArg some a)

-- In getVert PR
theorem toSubgraph_adj_exists {u v} (w : G.Walk u v)
    (hadj : (w.toSubgraph).Adj u' v') : ∃ i, (u' = w.getVert i ∧ v' = w.getVert (i + 1) ∨ v' = w.getVert i ∧ u' = w.getVert (i + 1)) ∧ i < w.length := by
  unfold Walk.toSubgraph at hadj
  match w with
  | .nil =>
    simp at hadj
  | .cons h p =>
    simp at hadj
    cases hadj with
    | inl hl =>
      cases hl with
      | inl h1 =>
        use 0
        simp only [Walk.getVert_zero, zero_add, Walk.getVert_cons_succ]
        constructor
        · left
          exact ⟨h1.1.symm, h1.2.symm⟩
        · simp only [Walk.length_cons, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]
      | inr h2 =>
        use 0
        simp only [Walk.getVert_zero, zero_add, Walk.getVert_cons_succ]
        constructor
        · right
          exact ⟨h2.1.symm, h2.2.symm⟩
        · simp only [Walk.length_cons, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]
    | inr hr =>
      obtain ⟨i, hi⟩ := toSubgraph_adj_exists _ hr
      use (i + 1)
      simp only [Walk.getVert_cons_succ]
      constructor
      · exact hi.1
      · simp only [Walk.length_cons, add_lt_add_iff_right, hi.2]



lemma cycle_two_neighbors (p : G.Walk u u) (hpc : p.IsCycle) (h : v ∈ p.support): (p.toSubgraph.neighborSet v).ncard = 2 := by
  unfold Subgraph.neighborSet
  obtain ⟨n, ⟨hn, _⟩⟩ := Walk.mem_support_iff_exists_getVert.mp h
  rw [@Set.ncard_eq_two]
  by_cases hbounds : 0 < n ∧ n < p.length
  · use p.getVert (n - 1)
    use p.getVert (n + 1)
    simp only [ne_eq]
    constructor
    · exact cycle_getVert_sub_neq_getVert_add p hpc hbounds.1 hbounds.2
    · ext w'
      constructor
      · intro hw'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        by_contra! hc
        rw [@Set.mem_setOf] at hw'
        obtain ⟨i, hi⟩ := toSubgraph_adj_exists _ hw'
        cases hi.1 with
        | inl hl =>
          have hnodup := hpc.2
          rw [@List.nodup_iff_get?_ne_get?] at hnodup
          have : n ≠ i := by
            intro h
            apply hc.2
            exact h ▸ hl.2

          cases Nat.lt_or_gt_of_ne this with
          | inl h1 =>
            have := hnodup (n - 1) (i - 1) (by omega) (by
              rw [@support_tail_length]
              calc
                i - 1 < i := by omega
                _ < p.length := hi.2
              )
            apply this
            rw [@tail_get?]
            rw [tail_get?]
            have : (n - 1 + 1) = n := by omega

            rw [this]
            have : (i - 1 + 1) = i := by omega
            rw [this]
            rw [← getVert_support_get _ (by omega)]
            rw [← getVert_support_get _ (by omega)]
            rw [← hl.1]
            rw [hn]
          | inr h2 =>
            have : i > 0 := by
              by_contra! hc
              simp only [nonpos_iff_eq_zero] at hc
              rw [hc] at hl
              rw [hl.1] at hn
              rw [@Walk.getVert_zero] at hn
              have := hnodup (n - 1) (p.support.tail.length - 1) (by
                rw [@support_tail_length]
                omega
                ) (by
                rw [support_tail_length]
                omega
                )
              simp only [tail_get?, List.length_tail, Walk.length_support, add_tsub_cancel_right,
                ne_eq] at this
              apply this
              have : (n - 1 + 1) = n := by omega
              rw [this]
              have : (p.length - 1 + 1) = p.length := by omega
              rw [this]
              rw [← getVert_support_get _ (by omega)]
              rw [← getVert_support_get _ (by rfl)]
              rw [hn]
              rw [@Walk.getVert_length]

            have := hnodup (i - 1) (n - 1) (by omega) (by
              rw [support_tail_length]
              omega
              )
            apply this
            rw [tail_get?]
            rw [tail_get?]
            have : (n - 1 + 1) = n := by omega
            rw [this]
            have : (i - 1 + 1) = i := by omega
            rw [this]
            rw [← getVert_support_get _ (by omega)]
            rw [← getVert_support_get _ (by omega)]
            rw [hn]
            rw [← hl.1]
        | inr hr =>
          -- duplicated from other case
          have hnodup := hpc.2
          rw [@List.nodup_iff_get?_ne_get?] at hnodup
          have : n ≠ (i + 1) := by
            intro h
            apply hc.1
            rw [h]
            simp only [add_tsub_cancel_right]
            exact hr.1

          cases Nat.lt_or_gt_of_ne this with
          | inl h1 =>
            have := hnodup (n - 1) i (by omega) (by
              rw [@support_tail_length]
              exact hi.2
              )
            apply this
            rw [@tail_get?]
            rw [tail_get?]
            have : (n - 1 + 1) = n := by omega
            rw [this]
            rw [← getVert_support_get _ (by omega)]
            rw [← getVert_support_get _ (by omega)]
            rw [hn]
            rw [hr.2]
          | inr h2 =>
            have := hnodup i (n - 1) (by omega) (by
              rw [@support_tail_length]
              omega
              )
            apply this
            rw [tail_get?]
            rw [tail_get?]
            rw [← getVert_support_get _ (by omega)]
            rw [← getVert_support_get _ (by omega)]
            have : (n - 1 + 1) = n := by omega
            rw [this]
            rw [← hr.2]
            rw [hn]

      ·
        intro hw'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw'
        cases hw' with
        | inl hl =>
          simp only [Set.mem_setOf_eq]
          rw [hl, ← hn]
          have := SimpleGraph.Walk.adj_getVert_succ p (by omega : n - 1 < p.length)
          have h' : n - 1 + 1 = n := by omega
          rw [h'] at this
          have := Walk.toSubgraph_adj_getVert p (by omega : n - 1 < p.length)
          rw [h'] at this
          exact this.symm
        | inr hr =>
          simp only [Set.mem_setOf_eq]
          rw [hr, ← hn]
          exact Walk.toSubgraph_adj_getVert _ hbounds.2

  · use p.getVert 1
    use p.getVert (p.length - 1)
    have hnodup := hpc.2
    rw [@List.nodup_iff_get?_ne_get?] at hnodup
    constructor
    · intro h
      have := SimpleGraph.Walk.IsCycle.three_le_length hpc
      have := hnodup 0 (p.length - 2) (by
        omega
        ) (by
          rw [@support_tail_length]
          omega
          )
      apply this
      rw [tail_get?]
      rw [tail_get?]
      have : p.length - 2 + 1 = p.length - 1 := by omega
      rw [this]
      simp only [Nat.reduceAdd]
      rw [← getVert_support_get _ (by omega)]
      rw [← getVert_support_get _ (by omega)]
      simp only [Walk.getVert_length, Option.some.injEq]
      exact h
    · ext w'
      have hp3 := SimpleGraph.Walk.IsCycle.three_le_length hpc
      rw [@Set.mem_setOf]
      push_neg at hbounds
      have huv : u = v := by
        rw [← hn]
        by_cases hz : 0 = n
        · rw [← hz]
          simp only [Walk.getVert_zero]
        · rw [Walk.getVert_of_length_le p (hbounds (by omega))]
      rw [← huv]
      constructor
      · intro h
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        by_contra! hc
        obtain ⟨i, hi⟩ := toSubgraph_adj_exists _ h
        cases hi.1 with
        | inl hl =>
          have : i ≠ 0 := by
            intro hi'
            rw [hi'] at hl
            simp only [Walk.getVert_zero, zero_add, true_and] at hl
            exact hc.1 hl
          have := hnodup (i - 1) (p.length - 1) (by omega) (by
            rw [@support_tail_length]
            omega
            )
          apply this
          rw [tail_get?]
          rw [tail_get?]
          rw [← getVert_support_get _ (by omega)]
          rw [← getVert_support_get _ (by omega)]
          have : i - 1 + 1 = i := by omega
          rw [this]
          have : p.length - 1 + 1 = p.length := by omega
          rw [this]
          rw [← hl.1]
          rw [@Walk.getVert_length]
        | inr hr =>
          have : i ≠ p.length - 1 := by
            intro h
            rw [h] at hr
            exact hc.2 hr.1
          have := hnodup i (p.length - 1) (by omega) (by
            rw [@support_tail_length]
            omega
            )
          apply this
          rw [tail_get?]
          rw [tail_get?]
          rw [← getVert_support_get _ (by omega)]
          rw [← getVert_support_get _ (by omega)]
          have : p.length - 1 + 1 = p.length := by omega
          rw [this]
          rw [← hr.2]
          rw [Walk.getVert_length]
      · intro h
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
        cases h with
        | inl hl =>
          rw [hl]
          have := Walk.toSubgraph_adj_getVert p (by omega : 0 < p.length)
          simpa using this
        | inr hr =>
          rw [hr]
          have hadj := Walk.toSubgraph_adj_getVert p (by omega : p.length - 1 < p.length)
          have : (p.length - 1 + 1) = p.length := by omega
          rw [this] at hadj
          simp at hadj
          exact hadj.symm

lemma Walk.toSubgraph_Adj_mem_support (p : G.Walk u v) (hp : p.toSubgraph.Adj u' v') : u' ∈ p.support := by
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
      exact q.toSubgraph_Adj_mem_support hr

lemma Walk.toSubgraph_Adj_mem_support' (p : G.Walk u v) (hp : p.toSubgraph.Adj u' v') : v' ∈ p.support := p.toSubgraph_Adj_mem_support hp.symm


lemma alternating_edge (p : G.Walk u u) (M : Subgraph G) (h : p.IsAlternating M)
    (hpc : p.IsCycle) (hM : ¬ M.Adj v w) (hp : p.toSubgraph.Adj v w)
    : ∃ w', M.Adj v w' ∧ p.toSubgraph.Adj v w' ∧ w ≠ w' := by
    have hv : v ∈ p.support := Walk.toSubgraph_Adj_mem_support p hp
    have hn := cycle_two_neighbors p hpc hv
    rw [@Set.ncard_eq_two] at hn
    obtain ⟨x, y, hxy⟩ := hn
    by_cases hxw : x = w
    · use y
      have hpvy : p.toSubgraph.Adj v y := by
        have : y ∈ ({x, y} : Set V) := by
          exact Set.mem_insert_of_mem x rfl
        rw [← hxy.2] at this
        exact this
      have := h.halt _ _ _ (hxw ▸ hxy.1) hp hpvy
      rw [@iff_not_comm] at this
      have hMAdj : M.Adj v y := this.mpr hM
      exact ⟨hMAdj, hpvy, hxw ▸ hxy.1⟩
    · use x
      have hpvx : p.toSubgraph.Adj v x := by
        have : x ∈ ({x, y} : Set V) := by
          exact Set.mem_insert x {y}
        rw [← hxy.2] at this
        exact this

      push_neg at hxw
      have := h.halt _ _ _ hxw hpvx hp
      exact ⟨this.mpr hM, hpvx, hxw.symm⟩

lemma alternating_edge' (p : G.Walk u u) (M : Subgraph G) (h : p.IsAlternating M)
    (hpc : p.IsCycle) (hM : M.Adj v w) (hp : p.toSubgraph.Adj v w)
    : ∃ w', ¬ M.Adj v w' ∧ p.toSubgraph.Adj v w' ∧ w ≠ w' := by
    have hv : v ∈ p.support := Walk.toSubgraph_Adj_mem_support p hp
    have hn := cycle_two_neighbors p hpc hv
    rw [@Set.ncard_eq_two] at hn
    obtain ⟨x, y, hxy⟩ := hn
    by_cases hxw : x = w
    · use y
      have hpvy : p.toSubgraph.Adj v y := by
        have : y ∈ ({x, y} : Set V) := by
          exact Set.mem_insert_of_mem x rfl
        rw [← hxy.2] at this
        exact this
      have := (h.halt _ _ _ (hxw ▸ hxy.1) hp hpvy).mp hM
      exact ⟨this, hpvy, hxw ▸ hxy.1⟩
    · use x
      have hpvx : p.toSubgraph.Adj v x := by
        have : x ∈ ({x, y} : Set V) := by
          exact Set.mem_insert x {y}
        rw [← hxy.2] at this
        exact this
      push_neg at hxw
      have := h.halt _ _ _ hxw hpvx hp
      rw [@iff_not_comm] at this
      exact ⟨this.mp hM, hpvx, hxw.symm⟩


@[simp]
lemma Subgraph.support_sup (H H' : Subgraph G) : (H ⊔ H').support = H.support ∪ H'.support := by
  ext v
  simp only [mem_support, sup_adj, Set.mem_union]
  exact exists_or

lemma Walk.mem_toSubgraph_support_mem_support {p : G.Walk u v} (hnp : ¬ p.Nil) (w : V) : w ∈ p.toSubgraph.support ↔ w ∈ p.support := by
  match p with
  | .nil => simp only [nil_nil, not_true_eq_false] at hnp
  | .cons h q =>
    match q with
    | .nil =>
      simp only [Walk.toSubgraph, ge_iff_le, singletonSubgraph_le_iff, subgraphOfAdj_verts,
        Set.mem_insert_iff, Set.mem_singleton_iff, or_true, sup_of_le_left, support_cons,
        support_nil, List.mem_cons, List.mem_singleton]
      rw [support_subgraphOfAdj]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, List.not_mem_nil, or_false]
    | .cons h2 q1 =>
      rw [Walk.support_cons]
      constructor
      · intro hw
        rw [SimpleGraph.Subgraph.mem_support] at hw
        obtain ⟨v', hv'⟩ := hw
        unfold Walk.toSubgraph at hv'
        rw [Subgraph.sup_adj] at hv'
        simp only [subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,] at hv'
        rw [@List.mem_cons_eq]
        cases hv' with
        | inl hl =>
          cases hl with
          | inl h1 =>
            left
            exact h1.1.symm
          | inr h2 =>
            right
            rw [← h2.2]
            exact start_mem_support (cons _ q1)
        | inr hr =>
          right
          have := (SimpleGraph.Subgraph.mem_support _).mpr ⟨v', hr⟩
          exact (Walk.mem_toSubgraph_support_mem_support (by simp only [not_nil_cons, not_false_eq_true]) w).mp this
      · intro hw
        rw [support_cons, List.mem_cons] at hw
        cases hw with
        | inl hl =>
          simp only [Walk.toSubgraph, Subgraph.support_sup, Set.mem_union]
          left
          rw [hl, support_subgraphOfAdj]
          exact Set.mem_insert u _
        | inr hr =>
          rw [Walk.toSubgraph, Subgraph.support_sup]
          right
          exact (Walk.mem_toSubgraph_support_mem_support not_nil_cons _).mpr hr
termination_by p.length

theorem toSubgraph_adj_sndOfNotNil {u v} (p : G.Walk u v) (hpp : p.IsPath)
    (hadj : (p.toSubgraph).Adj u v') : p.getVert 1 = v' := by
  have ⟨i, hi⟩ := toSubgraph_adj_exists _ hadj
  have hnodup := hpp.2
  rw [@List.nodup_iff_get?_ne_get?] at hnodup
  have hi0 : i = 0 := by
    by_contra! hc
    cases hi.1 with
    | inl hl =>
      have := hnodup 0 i (by omega) (by
        rw [support_length]
        have := hi.2
        omega)
      apply this
      rw [← getVert_support_get _ (by omega)]
      rw [← getVert_support_get _ (by omega)]
      simp only [Walk.getVert_zero, Option.some.injEq]
      exact hl.1
    | inr hr =>
      have := hnodup 0 (i + 1) (by omega) (by
        rw [support_length]
        have := hi.2
        omega)
      apply this
      rw [← getVert_support_get _ (by omega)]
      rw [← getVert_support_get _ (by omega)]
      simp only [Walk.getVert_zero, Option.some.injEq]
      exact hr.2
  rw [hi0] at hi
  simp only [Walk.getVert_zero, zero_add, true_and] at hi
  cases hi.1 with
  | inl hl => exact hl.symm
  | inr hr => exact (hadj.ne hr.1.symm).elim


lemma Walk.toSubgraph_Adj_sndOfNotNil {p : G.Walk u v} (hnp : ¬ p.Nil) : p.toSubgraph.Adj u (p.getVert 1) := by
  have := Walk.toSubgraph_adj_getVert p (by
    rw [SimpleGraph.Walk.nil_iff_length_eq] at hnp
    exact Nat.zero_lt_of_ne_zero hnp
    : 0 < p.length)
  simpa using this

lemma exOther {v w : V} {C : Subgraph G} (hc : C.IsCycle) (hadj : C.Adj v w) : ∃ w', w' ≠ w ∧ C.Adj v w' := by
  have h2 := hc.1 v (C.mem_support.mpr ⟨w, hadj⟩)
  rw [Set.ncard_eq_two] at h2
  obtain ⟨x, y, hxy⟩ := h2
  unfold Subgraph.neighborSet at hxy
  cases Set.subset_pair_iff.mp (Eq.subset hxy.2) w (Set.mem_setOf.mpr hadj) with
  | inl hl =>
    use y
    refine ⟨hl ▸ hxy.1.symm , ?_⟩
    have : y ∈ {w | C.Adj v w} := by
      rw [hxy.2]
      exact Set.mem_insert_of_mem x rfl
    exact this
  | inr hr =>
    use x
    refine ⟨hr ▸ hxy.1, ?_⟩
    have : x ∈ {w | C.Adj v w} := by
      rw [hxy.2]
      exact Set.mem_insert x {y}
    exact this

lemma Walk.support_path_subgraph_support {C : Subgraph G} (p : G.Walk u w) (hnp : ¬ p.Nil)
    (hp : p.toSubgraph ≤ C) (hv : v ∈ p.support) : v ∈ C.support := by
  rw [@Subgraph.mem_support]
  rw [← Walk.mem_toSubgraph_support_mem_support hnp] at hv
  rw [@Subgraph.mem_support] at hv
  obtain ⟨w, hw⟩ := hv
  use w
  exact hp.2 hw

lemma Walk.toSubgraph_adj_sndOfNotNil (p : G.Walk u w) (hnp : ¬ p.Nil) : p.toSubgraph.Adj u (p.getVert 1) :=
  p.notNilRec (by simp) hnp

lemma Walk.toSubgraph_append_le (p : G.Walk u v) (q : G.Walk v w) : p.toSubgraph ≤ (p.append q).toSubgraph := by
  rw [@toSubgraph_append]
  exact SemilatticeSup.le_sup_left p.toSubgraph q.toSubgraph

lemma Walk.toSubgraph_append_le' (p : G.Walk u v) (q : G.Walk v w) : q.toSubgraph ≤ (p.append q).toSubgraph := by
  rw [@toSubgraph_append]
  exact le_sup_right

lemma Walk.not_nil_reverse (p : G.Walk u v) : ¬ p.reverse.Nil ↔ ¬ p.Nil := by
  rw [@not_iff_not]
  exact reverse_Nil p



noncomputable def fpath [Fintype V] {u : V} [DecidableEq V] {C : Subgraph G}
  (hc : C.IsCycle) (p : G.Walk u v) (hnp : ¬ p.Nil) (hp : p.toSubgraph ≤ C) (hpp : p.IsPath) : G.Walk v v :=
  -- let b := hp.2
  -- let w' := (exOther hc (hp.2 (p.toSubgraph_Adj_sndOfNotNil hnp))).choose
  have hw' := (exOther hc (hp.2 (p.toSubgraph_Adj_sndOfNotNil hnp))).choose_spec
  if h : (exOther hc (hp.2 (p.toSubgraph_Adj_sndOfNotNil hnp))).choose = v
  then
    Walk.cons (h ▸ hw'.2.symm.adj_sub) p
  else
    have : (Fintype.card V + 1) - (p.length + 1 + 1) < (Fintype.card V + 1) - (p.length + 1) := by
      have h1 := SimpleGraph.Walk.IsPath.length_lt hpp
      omega

    fpath hc (.cons hw'.2.symm.adj_sub p) (Walk.not_nil_cons) (by
      simp only [Walk.toSubgraph, ne_eq, sup_le_iff]
      refine ⟨?_, hp⟩
      apply SimpleGraph.subgraphOfAdj_le_of_adj
      exact hw'.2.symm
    ) (by
      push_neg at h
      rw [@Walk.cons_isPath_iff]
      refine ⟨hpp, ?_⟩
      intro hx

      obtain ⟨n, ⟨hn, _⟩⟩ := Walk.mem_support_iff_exists_getVert.mp hx
      have hnpl : n < p.length := by
        by_contra! hc
        rw [Walk.getVert_of_length_le p hc] at hn
        apply h
        exact hn.symm

      have hn0 : 0 < n := by
        rw [@Nat.pos_iff_ne_zero]
        intro h0
        apply hw'.2.ne
        rw [h0] at hn
        rw [← hn]
        rw [@Walk.getVert_zero]

      have hvn:= path_getVert_sub_neq_getVert_add p hpp hn0 hnpl

      have hc2 := hc.1 _ (p.support_path_subgraph_support hnp hp hx)

      -- rw [@Set.ncard_eq_two] at hc2
      have : {p.getVert (n-1), p.getVert (n + 1), u} ⊆ C.neighborSet ((exOther hc (hp.2 (p.toSubgraph_Adj_sndOfNotNil hnp))).choose) := by
        intro v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        cases hv with
        | inl hl =>
          unfold Subgraph.neighborSet
          rw [@Set.mem_setOf]
          have hadj := Walk.toSubgraph_adj_getVert p (by omega : n - 1 < p.length)
          rw [← hl] at hadj
          have : n - 1 + 1 = n := by omega
          rw [this] at hadj
          rw [hn] at hadj
          exact hp.2 hadj.symm
        | inr hr =>
          cases hr with
          | inl h1 =>
            unfold Subgraph.neighborSet
            rw [@Set.mem_setOf]
            have hadj := Walk.toSubgraph_adj_getVert p (by omega : n < p.length)
            rw [← h1] at hadj
            rw [hn] at hadj
            exact hp.2 hadj
          | inr h2 =>
            rw [h2]
            unfold Subgraph.neighborSet
            rw [@Set.mem_setOf]
            exact hw'.2.symm
      have : ({p.getVert (n-1), p.getVert (n + 1), u}  : Set V).ncard ≤ 2 := by
        rw [← hc2]
        refine Set.ncard_le_ncard ?_ (Set.toFinite _)
        exact this
      cases Set.triple_ncard_two this with
      | inl hl =>
        exact hvn hl
      | inr hr =>
        have hnodup := hpp.2
        rw [@List.nodup_iff_get?_ne_get?] at hnodup
        cases hr with
        | inl h1 =>
          have hn1 : n ≠ 1 := by
            intro h
            rw [h] at hn
            rw [← hn] at hw'
            exact hw'.1 rfl

          have := hnodup 0 (n - 1) (by omega) (by
            rw [SimpleGraph.Walk.length_support]
            omega)
          rw [← getVert_support_get _ (by omega)] at this
          rw [← getVert_support_get _ (by omega)] at this
          rw [h1] at this
          rw [@Walk.getVert_zero] at this
          apply this
          rfl
        | inr h2 =>
          have := hnodup 0 (n + 1) (by omega) (by
            rw [@Walk.length_support]
            omega
            )
          rw [← getVert_support_get _ (by omega)] at this
          rw [← getVert_support_get _ (by omega)] at this
          simp only [Walk.getVert_zero, ne_eq, Option.some.injEq] at this
          exact this h2.symm
      )
termination_by (Fintype.card V + 1) - p.support.length

lemma fpath_IsCycle [Fintype V] {u : V} [DecidableEq V] {C : Subgraph G}
  (hc : C.IsCycle) (p : G.Walk u v) (hnp : ¬ p.Nil) (hp : p.toSubgraph ≤ C) (hpp : p.IsPath) : (fpath hc p hnp hp hpp).IsCycle := by
  unfold fpath
  split_ifs with h
  · simp only
    rw [@Walk.cons_isCycle_iff]
    refine ⟨hpp, ?_⟩
    intro hs
    rw [← SimpleGraph.Walk.mem_edges_toSubgraph] at hs
    rw [@Subgraph.mem_edgeSet] at hs
    obtain ⟨i, hi⟩ := toSubgraph_adj_exists p hs
    cases hi.1 with
    | inl hl =>
      have hi0 : (i + 1) = 0 := by
        by_contra! hc
        rw [@Walk.isPath_def] at hpp
        rw [@List.nodup_iff_get?_ne_get?] at hpp
        have hnodup := hpp 0 (i + 1) (by omega) (by
          rw [support_length]
          omega
          )
        apply hnodup
        rw [← getVert_support_get _ (by omega)]
        rw [← getVert_support_get _ (by omega)]
        rw [← hl.2]
        rw [@Walk.getVert_zero]
      simp only [add_eq_zero, one_ne_zero, and_false] at hi0
    | inr hr =>
      have hi0 : i = 0 := by
        by_contra! hc
        rw [@Walk.isPath_def] at hpp
        rw [@List.nodup_iff_get?_ne_get?] at hpp
        have hnodup := hpp 0 i (by omega) (by
          rw [support_length]
          omega
          )
        apply hnodup
        rw [← getVert_support_get _ (by omega)]
        rw [← getVert_support_get _ (by omega)]
        rw [← hr.1]
        rw [@Walk.getVert_zero]
      rw [hi0] at hr
      simp only [Walk.getVert_zero, zero_add, true_and] at hr
      have := (fpath.proof_1 hc p hnp hp).choose_spec.1
      apply this
      rw [h]
      exact hr
  · have : (Fintype.card V + 1) - (p.length + 1 + 1) < (Fintype.card V + 1) - (p.length + 1) := by
      have h1 := SimpleGraph.Walk.IsPath.length_lt hpp
      omega
    apply fpath_IsCycle
termination_by (Fintype.card V + 1) - p.support.length



lemma cycle_with_path {C : Subgraph G} (hc : C.IsCycle) (p : G.Walk v v) (hic : p.IsCycle) (hp : p.toSubgraph ≤ C)
    (v' w' : C.verts) (hv : v'.val ∈ p.support) (p' : C.coe.Walk v' w') : w'.val ∈ p.support := by
  match p' with
  | .nil => exact hv
  | .cons' u v w h q =>
    refine cycle_with_path hc p hic hp _ _ ?_ q
    rw [@Subgraph.coe_adj] at h
    have hc2 := hc.1 _ (Walk.support_path_subgraph_support p (cycle_neq_not_nil p hic) hp hv)
    have hp2 := cycle_two_neighbors p hic hv
    rw [@Set.ncard_eq_two] at hc2 hp2
    obtain ⟨x, y, hxy⟩ := hc2
    obtain ⟨x2, y2, hxy2⟩ := hp2
    have hpsc : p.toSubgraph.neighborSet u.val ⊆ C.neighborSet u.val := by
      exact Subgraph.neighborSet_subset_of_subgraph hp ↑u
    rw [hxy.2, hxy2.2] at hpsc
    have hpsceq := pair_subset_pair hxy2.1 hpsc
    rw [← hxy.2, ← hxy2.2] at hpsceq
    have : v.val ∈ C.neighborSet u.val := h
    rw [← hpsceq] at this
    exact Walk.toSubgraph_Adj_mem_support' p this

lemma fpath_toSubgraph [Fintype V] {u : V} [DecidableEq V] {C : Subgraph G}
  (hc : C.IsCycle) (p : G.Walk u v) (hnp : ¬ p.Nil) (hp : p.toSubgraph ≤ C) (hpp : p.IsPath)  : (fpath hc p hnp hp hpp).toSubgraph = C := by
  have hpc := fpath_IsCycle hc p hnp hp hpp
  unfold fpath at hpc ⊢
  split_ifs with h
  · simp only [Walk.toSubgraph]
    -- rw [@Subgraph.ext_iff]
    have : G.subgraphOfAdj (fpath.proof_3 hc p hnp hp (fpath.proof_2 hc p hnp hp) h) ⊔ p.toSubgraph ≤ C := by
      rw [@sup_le_iff]
      refine ⟨?_, hp⟩
      apply SimpleGraph.subgraphOfAdj_le_of_adj
      have := (fpath.proof_1 hc p hnp hp).choose_spec.2
      rw [h] at this
      exact this.symm
    rw [le_antisymm_iff]
    refine ⟨this, ?_⟩
    simp [h] at hpc

    have hsupp {w : V} (hw : w ∈ C.verts) : w ∈ p.support := by
      have hv : v ∈ C.verts := by
        apply hp.1
        exact Walk.end_mem_verts_toSubgraph p
      have ⟨p', hp'⟩ := SimpleGraph.Reachable.exists_path_of_dist (hc.2 ⟨v,
        hv⟩ ⟨w, hw⟩)
      have : (Walk.cons (fpath.proof_3 hc p hnp hp (fpath.proof_2 hc p hnp hp) h) p).toSubgraph ≤ C := by
        simp only [Walk.toSubgraph]
        exact this
      have := cycle_with_path hc _ hpc this ⟨v, hv⟩ ⟨w, hw⟩ (Walk.start_mem_support _) p'
      simp only [Walk.support_cons, List.mem_cons] at this
      cases this with
      | inl hl =>
        exact hl ▸ p.end_mem_support
      | inr hr => exact hr
    constructor
    · simp only [Subgraph.verts_sup, subgraphOfAdj_verts, Walk.verts_toSubgraph]
      intro w hw
      exact Set.mem_union_right {v, u} (hsupp hw)
    · intro v' w hv'w
      have hv' : v' ∈ p.support := by
        apply hsupp
        exact C.edge_vert hv'w
      have hw : w ∈ p.support := by
        apply hsupp
        exact C.edge_vert hv'w.symm

      have hp2 := cycle_two_neighbors _ hpc (by simp [hv']: v' ∈ _)
      have hc2 := hc.1 v' (Walk.support_path_subgraph_support p hnp hp hv')
      rw [@Set.ncard_eq_two] at hc2 hp2
      obtain ⟨x, y, hxy⟩ := hc2
      obtain ⟨x2, y2, hxy2⟩ := hp2
      have hpsc : (Walk.cons (fpath.proof_3 hc p hnp hp (fpath.proof_2 hc p hnp hp) (of_eq_true (Eq.trans (congrArg (fun x => x = v) h) (eq_self v))) : G.Adj v u) p).toSubgraph.neighborSet v' ⊆ C.neighborSet v' := by
        exact Subgraph.neighborSet_subset_of_subgraph this v'
      rw [hxy.2, hxy2.2] at hpsc
      have hpsceq := pair_subset_pair hxy2.1 hpsc
      rw [← hxy.2, ← hxy2.2] at hpsceq
      have : w ∈ C.neighborSet v' := hv'w
      rw [← hpsceq] at this
      exact this
  · have : (Fintype.card V + 1) - (p.length + 1 + 1) < (Fintype.card V + 1) - (p.length + 1) := by
      have h1 := SimpleGraph.Walk.IsPath.length_lt hpp
      omega
    apply fpath_toSubgraph
termination_by (Fintype.card V + 1) - p.support.length

lemma Subgraph.IsCycle_iff [Fintype V] [DecidableEq V] {C : Subgraph G} (h : v ∈ C.support) : C.IsCycle ↔ ∃ (p : G.Walk v v), p.IsCycle ∧ p.toSubgraph = C := by
  constructor
  · intro hc
    rw [@mem_support] at h
    obtain ⟨w, hvw⟩ := h
    have hsub : (Walk.cons (hvw.adj_sub.symm) .nil).toSubgraph ≤ C := by
      simp only [Walk.toSubgraph, ge_iff_le, singletonSubgraph_le_iff, subgraphOfAdj_verts,
        Set.mem_insert_iff, Set.mem_singleton_iff, or_true, sup_of_le_left]
      exact SimpleGraph.subgraphOfAdj_le_of_adj C hvw.symm
    have hpath : (Walk.cons (hvw.adj_sub.symm) .nil).IsPath := by
      simp only [Walk.cons_isPath_iff, Walk.isPath_iff_eq_nil, Walk.support_nil,
      List.mem_singleton, hvw.ne.symm, not_false_eq_true, and_self]
    let p := fpath hc (Walk.cons (hvw.adj_sub.symm) .nil) Walk.not_nil_cons hsub hpath
    use p
    have hpc : p.IsCycle := by
      unfold fpath
      simp only [ne_eq, Walk.toSubgraph, subgraphOfAdj_verts, id_eq,
        eq_mpr_eq_cast]

      split_ifs with h
      · exfalso
        have := (fpath.proof_1 hc (Walk.cons (hvw.adj_sub.symm) .nil) Walk.not_nil_cons hsub).choose_spec
        simp only [ne_eq] at this
        exact this.1 h
      · apply fpath_IsCycle
    refine ⟨hpc, ?_⟩
    have hpsc : p.toSubgraph = C := by
      unfold fpath
      simp only [ne_eq]
      split_ifs with h
      · exfalso
        have := (fpath.proof_1 hc (Walk.cons (hvw.adj_sub.symm) .nil) Walk.not_nil_cons hsub).choose_spec
        simp only [ne_eq] at this
        exact this.1 h
      · apply fpath_toSubgraph

    exact hpsc


  · rintro ⟨p, hp⟩
    rw [← hp.2] at h

    constructor
    ·
      intro v' hv'
      have := cycle_two_neighbors p hp.1 (by
        rw [← Walk.mem_toSubgraph_support_mem_support (Walk.IsCycle.not_nil hp.1)]
        rw [hp.2]
        exact hv')
      exact hp.2 ▸ this
    · exact hp.2 ▸ p.toSubgraph_connected



lemma matching_union_left (M : (G ⊔ G').Subgraph) (hM : M.IsPerfectMatching) (hd : M.coeBig ⊓ G' = ⊥)
  : ∃ (M' : Subgraph G), M'.IsPerfectMatching := by
  let M' : Subgraph G := {
    verts := Set.univ,
    Adj := fun v w => M.Adj v w,
    adj_sub := by
      intro v w hvw
      have := M.adj_sub hvw
      rw [@sup_adj] at this
      cases this
      next h1 =>
        exact h1
      next h2 =>
        have : (M.coeBig ⊓ G').Adj v w := by
          rw [inf_adj]
          exact ⟨hvw, h2⟩
        rw [hd] at this
        exact this.elim
    edge_vert := fun {v w} a => trivial
    symm := fun ⦃x y⦄ a => Subgraph.adj_symm M a
  }
  use M'
  rw [@Subgraph.isPerfectMatching_iff]
  intro v
  obtain ⟨w, hw⟩ := Subgraph.isPerfectMatching_iff.mp hM v
  use w

lemma Walk.IsCycle.of_append_left {p : G.Walk u v} {q : G.Walk v u} (h : u ≠ v) (hcyc : (p.append q).IsCycle) : p.IsPath := by
  have := hcyc.2
  rw [SimpleGraph.Walk.tail_support_append, List.nodup_append] at this
  rw [@isPath_def, @support_eq_cons, @List.nodup_cons]
  refine ⟨?_, this.1⟩
  intro h'
  apply this.2.2 h'
  exact q.end_mem_tail_support_of_ne h.symm

lemma Walk.IsCycle.of_append_right {p : G.Walk u v} {q : G.Walk v u} (h : u ≠ v) (hcyc : (p.append q).IsCycle) : q.IsPath := by
  have := hcyc.2
  rw [SimpleGraph.Walk.tail_support_append, List.nodup_append] at this
  rw [@isPath_def, @support_eq_cons, @List.nodup_cons]
  exact ⟨this.2.2 (p.end_mem_tail_support_of_ne h), this.2.1⟩

lemma Walk.IsCycle.mem_endpoint {p : G.Walk u u} (h : p.IsCycle) : u ∈ p.toSubgraph.support := by
  rw [@Subgraph.mem_support]
  use p.getVert 1
  exact toSubgraph_adj_sndOfNotNil p (cycle_neq_not_nil p h)

lemma Walk.cons_to_Subgraph_first_adj (h : G.Adj u v) (p : G.Walk v w) : (Walk.cons h p).toSubgraph.Adj u v := by
  unfold Walk.toSubgraph
  rw [@Subgraph.sup_adj]
  left
  exact rfl

lemma perfectMapLe {M : Subgraph G} (h : G ≤ G') (hM : M.IsPerfectMatching) : (M.map (Hom.ofLE h)).IsPerfectMatching := by
  simp only [Subgraph.IsPerfectMatching, Subgraph.IsMatching, Subgraph.map,
    Subgraph.IsSpanning, Hom.coe_ofLE, id_eq, Set.image_id', Relation.map_id_id]
  exact hM


def Walk.coeWalk {H : Subgraph G} {u v : H.verts} (p : H.coe.Walk u v) : G.Walk u.val v.val :=
  match p with
  | .nil => Walk.nil
  | .cons h q => Walk.cons (H.adj_sub h) (q.coeWalk)

@[simp]
lemma Walk.coeWalkLength {H : Subgraph G} {u v : H.verts} (p : H.coe.Walk u v) : (p.coeWalk).length = p.length := by
  induction p using Walk.coeWalk.induct with
  | case1 =>
    simp only [Walk.length_nil, coeWalk]
  | case2 _ _ _ _ _ ih =>
    simp only [Walk.length_cons, ih, Walk.coeWalk]

@[simp]
lemma Walk.coeWalkNil {H : Subgraph G} {u v : H.verts} (p : H.coe.Walk u v) : (p.coeWalk).Nil ↔ p.Nil := by
  rw [Walk.nil_iff_length_eq]
  rw [Walk.nil_iff_length_eq]
  simp only [coeWalkLength]

@[simp]
lemma Walk.coeWalkNotNil {H : Subgraph G} {u v : H.verts} (p : H.coe.Walk u v) (h : ¬ p.Nil) : ¬ (p.coeWalk).Nil := by
  rw [coeWalkNil]
  exact h


lemma Walk.IsCycle.decompose_mem_support_part {p : G.Walk u u} {q : G.Walk u v} {r : G.Walk v u} (hp : p.IsCycle) (h : p = q.append r)
    (hx : x ∈ q.support) (hxu : x ≠ u) (hxv : x ≠ v) : x ∉ r.support := by
  intro har
  have := hp.2
  rw [@List.nodup_iff_get?_ne_get?] at this
  obtain ⟨n, hn⟩ := Walk.mem_support_iff_exists_getVert.mp har
  obtain ⟨n', hn'⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  have hn'q : n' < q.length := by
    have := hn'.2
    rw [@Nat.le_iff_lt_or_eq] at this
    cases this with
    | inl hl => exact hl
    | inr hr =>
      exfalso
      rw [hr] at hn'
      simp only [Walk.getVert_length, le_refl, and_true] at hn'
      exact hxv hn'.symm
  have hpn' : p.getVert n' = x := by
    rw [h]
    rw [SimpleGraph.Walk.getVert_append ]
    simp only [hn'q, ↓reduceIte]
    exact hn'.1

  have hlsup : q.length + n - 1 < p.support.tail.length := by
    rw [h]
    simp only [List.length_tail, Walk.length_support, Walk.length_append,
      add_tsub_cancel_right, add_lt_add_iff_left]
    have := hn.2
    rw [@Nat.le_iff_lt_or_eq] at this
    cases this with
    | inl hl => omega
    | inr hr =>
      exfalso
      rw [hr] at hn
      simp only [Walk.getVert_length, le_refl, and_true] at hn
      exact hxu hn.symm
  have hn'0 : 0 < n' := by
    rw [@Nat.pos_iff_ne_zero]
    intro hn'
    rw [hn'] at hpn'
    rw [@Walk.getVert_zero] at hpn'
    exact hxu hpn'.symm

  have hn0 : 0 < n := by
    rw [@Nat.pos_iff_ne_zero]
    intro hn'
    rw [hn'] at hn
    rw [@Walk.getVert_zero] at hn
    exact hxv hn.1.symm

  have hqlpl : q.length + n ≤ p.length := by
    rw [h]
    simp only [Walk.length_append, add_le_add_iff_left]
    omega
  have := this (n' - 1) (q.length + n - 1) (by omega) (hlsup)
  apply this
  rw [← Walk.support_tail_of_not_nil _ hp.not_nil]

  rw [← getVert_support_get p.tail (by
    rw [@Nat.sub_le_iff_le_add]
    rw [Walk.length_tail_add_one (hp.not_nil)]
    omega
    ) ]
  rw [← getVert_support_get p.tail (by
    rw [@Nat.sub_le_iff_le_add]
    rw [Walk.length_tail_add_one (hp.not_nil)]
    omega
    ) ]
  simp only [Option.some.injEq]
  rw [getVert_tail _ hp.not_nil]
  rw [getVert_tail _ hp.not_nil]
  have hn'sa : n' - 1 + 1 = n' := by exact Nat.sub_add_cancel hn'0
  have hqln : q.length + n - 1 + 1 = q.length + n := by
    apply Nat.sub_add_cancel
    omega

  rw [hn'sa]
  rw [hqln]
  rw [hpn']
  rw [h]
  rw [SimpleGraph.Walk.getVert_append]
  simp only [add_lt_iff_neg_left, not_lt_zero', ↓reduceIte, add_tsub_cancel_left, hn.1]



lemma Walk.toSubgraph_cons_adj_iff {p : G.Walk u v} {h : G.Adj t u} : (Walk.cons h p).toSubgraph.Adj w x ↔ (s(t, u) = s(w, x) ∨ p.toSubgraph.Adj w x) := by
  simp only [Walk.toSubgraph, Subgraph.sup_adj, subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff',
    Prod.mk.injEq, Prod.swap_prod_mk]

lemma Walk.IsPath.start_neighbourSet_ncard {p : G.Walk u v} (hnp : ¬ p.Nil) (hp : p.IsPath) : (p.toSubgraph.neighborSet u).ncard = 1 := by
  rw [@Set.ncard_eq_one]
  use p.getVert 1
  ext v'
  constructor
  · intro h
    rw [@Subgraph.mem_neighborSet] at h
    rw [@Set.mem_singleton_iff]
    have hnodup := hp.2
    rw [@List.nodup_iff_get?_ne_get?] at hnodup
    obtain ⟨i, hi⟩ := toSubgraph_adj_exists _ h
    by_cases hi0 : i = 0
    · rw [hi0] at hi
      simp only [getVert_zero, zero_add, true_and] at hi
      cases hi.1 with
      | inl hl => exact hl
      | inr hr =>
        exfalso
        exact h.ne hr.1.symm
    · exfalso
      cases hi.1 with
      | inl hl =>
        have := hnodup 0 i (by omega) (by
          rw [length_support]
          omega
          )
        rw [← getVert_support_get _ (by omega)] at this
        rw [← getVert_support_get _ (by omega)] at this
        rw [← hl.1] at this
        rw [@getVert_zero] at this
        exfalso
        exact this rfl
      | inr hr =>
        have := hnodup 0 (i + 1) (by omega) (by
          rw [length_support]
          omega
          )
        rw [← getVert_support_get _ (by omega)] at this
        rw [← getVert_support_get _ (by omega)] at this
        rw [getVert_zero] at this
        rw [← hr.2] at this
        exact this rfl
  · intro h
    rw [@Set.mem_singleton_iff] at h
    rw [h]
    rw [@Subgraph.mem_neighborSet]
    exact toSubgraph_adj_sndOfNotNil p hnp


lemma Walk.toSubgraph_snd {p : G.Walk u v} (hp : p.IsPath) (hnp : ¬ p.Nil) (h : p.toSubgraph.Adj u w) : p.getVert 1 = w := by
  have hset := hp.start_neighbourSet_ncard hnp
  have hwmem : w ∈ p.toSubgraph.neighborSet u := by
    exact h
  have hsmem : p.getVert 1 ∈ p.toSubgraph.neighborSet u  := by
    exact toSubgraph_adj_sndOfNotNil p hnp
  rw [Set.ncard_eq_one] at hset
  obtain ⟨v, hv⟩ := hset
  have := Set.eq_of_mem_singleton (hv ▸ hwmem)
  rw [this]
  exact Set.eq_of_mem_singleton (hv ▸ hsmem)

lemma Walk.IsCycle.IsAlternating_cons {p : G.Walk u v} {h : G.Adj v u} {M : Subgraph G} (hnp : ¬ p.Nil) (hcyc : (Walk.cons h p).IsCycle)
  (halt : p.toSubgraph.IsAlternating M) (ha : M.Adj u v  ↔ ¬ M.Adj u (p.getVert 1)) (hb : M.Adj v u ↔ ¬ M.Adj v (p.lastButOneOfNotNil))
    : (Walk.cons h p).toSubgraph.IsAlternating M := by
  intro v' w w' hww' hadj hadj'
  rw [@cons_isCycle_iff] at hcyc
  rw [Walk.toSubgraph_cons_adj_iff ] at hadj hadj'
  cases hadj with
  | inl hl =>
    cases hadj' with
    | inl hl' =>
      rw [hl'] at hl
      simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, true_and, Prod.swap_prod_mk] at hl
      exfalso
      cases hl with
      | inl h1 =>
        exact hww' h1.symm
      | inr h2 =>
        rw [← h2.1, h2.2] at hww'
        simp only [ne_eq, not_true_eq_false] at hww'
    | inr hr' =>
      simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hl
      cases hl with
      | inl h1 =>
        rw [← h1.1, ← h1.2]
        rw [hb]
        rw [← h1.1] at hr'
        rw [← SimpleGraph.Walk.toSubgraph_reverse ] at hr'
        unfold lastButOneOfNotNil
        have := p.reverse.toSubgraph_snd ((isPath_reverse_iff p).mpr hcyc.1)
          (by rw [@reverse_Nil]; exact hnp) hr'
        rw [← getVert_reverse, this]
      | inr h2 =>
        rw [← h2.1, ← h2.2]
        rw [ha]
        rw [← h2.2] at hr'
        have := p.toSubgraph_snd hcyc.1 hnp hr'
        rw [this]
  | inr hr =>
    cases hadj' with
    | inl hl' =>
      simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hl'
      cases hl' with
      | inl h1 =>
        rw [← h1.1, ← h1.2]
        rw [hb]
        rw [← h1.1] at hr
        rw [← SimpleGraph.Walk.toSubgraph_reverse ] at hr
        have := p.reverse.toSubgraph_snd ((isPath_reverse_iff p).mpr hcyc.1)
          (by rw [@reverse_Nil]; exact hnp) hr
        unfold lastButOneOfNotNil
        rw [← getVert_reverse, this]
        simp only [not_not]
      | inr h2 =>
        rw [← h2.1, ← h2.2]
        rw [ha]
        rw [← h2.2] at hr
        have := p.toSubgraph_snd hcyc.1 hnp hr
        rw [this]
        simp only [not_not]
    | inr hr' =>
      exact halt v' w w' hww' hr hr'

lemma Walk.IsPath.IsAlternating_cons {p : G.Walk u v} {h : G.Adj t u} {M : Subgraph G} (hnp : ¬ p.Nil) (hpath : (Walk.cons h p).IsPath)
  (halt : p.toSubgraph.IsAlternating M) (ha : M.Adj t u  ↔ ¬ M.Adj u (p.getVert 1))
    : (Walk.cons h p).toSubgraph.IsAlternating M := by
  intro v' w w' hww' hadj hadj'
  rw [Walk.toSubgraph_cons_adj_iff ] at hadj hadj'
  rw [@cons_isPath_iff] at hpath
  cases hadj with
  | inl hl =>
    cases hadj' with
    | inl hl' =>
      exfalso
      rw [hl'] at hl
      simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, true_and, Prod.swap_prod_mk] at hl
      cases hl with
      | inl h1 => exact hww' h1.symm
      | inr h2 => exact hww' (h2.1 ▸ h2.2.symm)
    | inr hr' =>
      simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hl
      cases hl with
      | inl h1 =>
        suffices hsuf : t ∈ p.support from (by
          exfalso; exact hpath.2 hsuf
          )
        rw [← h1.1] at hr'
        exact toSubgraph_Adj_mem_support p hr'
      | inr h2 =>
        rw [← h2.1, ← h2.2]
        rw [Subgraph.adj_comm, ha]
        rw [← h2.2] at hr'
        have := p.toSubgraph_snd hpath.1 hnp hr'
        rw [this]
  | inr hr =>
    cases hadj' with
    | inl hl' =>
      simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hl'
      cases hl' with
      | inl h1 =>
        suffices hsuf : t ∈ p.support from (by
          exfalso; exact hpath.2 hsuf
          )
        rw [← h1.1] at hr
        exact toSubgraph_Adj_mem_support p hr
      | inr h2 =>
        rw [← h2.1, ← h2.2]
        rw [Subgraph.adj_comm _ u t, ha]
        rw [← h2.2] at hr
        have := p.toSubgraph_snd hpath.1 hnp hr
        rw [this]
        simp only [not_not]
    | inr hr' =>
      exact halt v' w w' hww' hr hr'

lemma Walk.append_toSubgraph_alternating {p : G.Walk u v} {q : G.Walk v w} {M : Subgraph G} (h : (p.append q).toSubgraph.IsAlternating M) : p.toSubgraph.IsAlternating M ∧ q.toSubgraph.IsAlternating M := by
  constructor
  · intro v w w' hww' hadj hadj'
    exact  h v w w' hww' (by
      rw [SimpleGraph.Walk.toSubgraph_append, @Subgraph.sup_adj]
      left
      exact hadj
      ) (by
      rw [SimpleGraph.Walk.toSubgraph_append, @Subgraph.sup_adj]
      left
      exact hadj'
      )
  · intro v w w' hww' hadj hadj'
    exact  h v w w' hww' (by
      rw [SimpleGraph.Walk.toSubgraph_append, @Subgraph.sup_adj]
      right
      exact hadj
      ) (by
      rw [SimpleGraph.Walk.toSubgraph_append, @Subgraph.sup_adj]
      right
      exact hadj'
      )

lemma Walk.append_sndOfNotNil {u v w : V} {p : G.Walk u v} {q : G.Walk v w} (hpq : ¬ (p.append q).Nil) (hp : ¬ p.Nil) : (p.append q).getVert 1 = p.getVert 1 := by
  cases p with
  | nil =>
    simp only [nil_nil, not_true_eq_false] at hp
  | cons h q' =>
    simp only [cons_append, getVert_cons_succ, getVert_zero]

lemma Walk.append_notNil {u v w : V} {p : G.Walk u v} {q : G.Walk v w} : (p.append q).Nil ↔ p.Nil ∧ q.Nil := by
  constructor
  · intro hpq
    rw [@nil_iff_length_eq] at hpq
    rw [@length_append] at hpq
    rw [@Nat.add_eq_zero] at hpq
    simp [nil_iff_length_eq]
    exact hpq
  · rintro ⟨hp, hq⟩
    rw [@nil_iff_length_eq]
    simp only [length_append, add_eq_zero, nil_iff_length_eq.mp hp, nil_iff_length_eq.mp hq]


lemma Walk.append_subgraph_adj {u v w : V} {p : G.Walk u v} {q : G.Walk v w} (h : p.toSubgraph.Adj x y) : (p.append q).toSubgraph.Adj x y := by
  rw [@toSubgraph_append]
  rw [@Subgraph.sup_adj]
  exact Or.intro_left _ h

lemma Walk.append_subgraph_adj' {u v w : V} {p : G.Walk u v} {q : G.Walk v w} (h : q.toSubgraph.Adj x y) : (p.append q).toSubgraph.Adj x y := by
  rw [@toSubgraph_append]
  rw [@Subgraph.sup_adj]
  exact Or.intro_right _ h

lemma Walk.tail_support_imp_support {u v w : V} {p : G.Walk u v} (hp : ¬ p.Nil) (h : w ∈ p.tail.support) : w ∈ p.support := by
  rw [mem_support_iff_exists_append]
  rw [@mem_support_iff_exists_append] at h
  obtain ⟨q, r, hqr⟩ := h
  use (Walk.cons (adj_getVert_one hp) q)
  use r
  rw [@cons_append]
  rw [← hqr]
  exact (cons_tail_eq p hp).symm

lemma Walk.IsPath.start_non_mem_support_tail {p : G.Walk u v} (hp : p.IsPath) (hnp : ¬ p.Nil) : u ∉ p.tail.support := by
  have := p.cons_tail_eq hnp
  rw [← this] at hp
  rw [@cons_isPath_iff] at hp
  exact hp.2

lemma Walk.IsPath.edge_start_not_mem_tail_edges {p : G.Walk u v} (hp : p.IsPath) (hnp : ¬ p.Nil) : s(u, w) ∉ p.tail.edges := by
  intro hsp
  have := p.tail.fst_mem_support_of_mem_edges hsp
  exact hp.start_non_mem_support_tail hnp this


lemma Walk.tail_toSubgraph {p : G.Walk u v} (hp : ¬ p.Nil) : p.tail.toSubgraph ≤ p.toSubgraph := by
  constructor
  · simp only [verts_toSubgraph, Set.setOf_subset_setOf]
    intro v hv
    rw [@mem_support_iff]
    right
    rw [← support_tail_of_not_nil _ hp]
    exact hv
  · intro v' w hvw
    have := p.cons_tail_eq hp
    rw [← this]
    simp only [Walk.toSubgraph, Subgraph.sup_adj, subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff',
      Prod.mk.injEq, Prod.swap_prod_mk]
    right
    exact hvw

lemma Walk.reverse_tail_toSubgraph {p : G.Walk u v} (hp : ¬ p.reverse.Nil) : p.reverse.tail.toSubgraph ≤ p.toSubgraph := by
  -- have hnp : ¬ p.Nil := (not_nil_reverse p).mp hp
  have := p.reverse.tail_toSubgraph hp
  rw [@toSubgraph_reverse] at this
  exact this


lemma Subgraph.IsAlternatingMono {C C' M: Subgraph G} (h : C ≤ C') (halt : C'.IsAlternating M) : C.IsAlternating M := by
  intro v w w' hww' hadj hadj'
  exact halt v w w' hww' (h.2 hadj) (h.2 hadj')

lemma Walk.getVert_two {p : G.Walk u v} (hnp1 : ¬ p.Nil) (hnp2 : ¬ p.tail.Nil) : p.getVert 2 = p.tail.getVert 1 := by
  cases p with
  | nil =>
    simp only [nil_nil, not_true_eq_false] at hnp1
  | cons h q =>
    simp only [getVert_cons_succ, tail_cons, getVert_copy]

lemma Walk.IsPath.start_ne_snd_snd {p : G.Walk u v} (hp : p.IsPath) (hnp1 : ¬ p.Nil) (hnp2 : ¬ p.tail.Nil) : u ≠ p.tail.getVert 1 := by
  intro h
  have hnodup := hp.2
  rw [@List.nodup_iff_get?_ne_get?] at hnodup
  have help : 2 < p.support.length := by
    rw [SimpleGraph.Walk.length_support]
    rw [← SimpleGraph.Walk.cons_tail_eq _ hnp1]
    rw [← SimpleGraph.Walk.cons_tail_eq _ hnp2]
    have : 2 ≤ (Walk.cons (adj_getVert_one hnp1) (Walk.cons (adj_getVert_one hnp2) p.tail.tail)).length := by
      rw [SimpleGraph.Walk.length_cons]
      rw [SimpleGraph.Walk.length_cons]
      omega
    omega
  have := hnodup 0 2 (by omega) (by omega)
  rw [← getVert_support_get _ (by omega)] at this
  rw [← getVert_support_get _ (by
    rw [length_support] at help
    omega
    )] at this
  apply this
  simp only [getVert_zero, Option.some.injEq, p.getVert_two hnp1 hnp2]
  exact h

lemma Walk.getVert_length_sub_one {p : G.Walk u v} (hnp : ¬ p.Nil)  : p.getVert (p.length - 1) = p.lastButOneOfNotNil := by
  unfold lastButOneOfNotNil
  rw [← SimpleGraph.Walk.getVert_reverse]

lemma Walk.IsPath.start_ne_lastButOne {p : G.Walk u v} (hnp : ¬ p.Nil) (hnp' : ¬ p.tail.Nil) (hadj : G.Adj w (p.getVert 1))
    (hpath : (Walk.cons hadj p.tail).IsPath) : (Walk.cons hadj p.tail).lastButOneOfNotNil ≠ w := by
  intro h
  have hnodup := hpath.2
  rw [@List.nodup_iff_get?_ne_get?] at hnodup
  have h1 : 0 < (cons hadj p.tail).length - 1 := by
    unfold length
    have : p.tail.length > 0 := by
      by_contra! hc
      rw [@Nat.le_zero] at hc
      have := SimpleGraph.Walk.nil_iff_length_eq.mpr hc
      exact hnp' this
    omega
  have := hnodup 0 ((Walk.cons hadj p.tail).length - 1) h1 (by
    rw [length_support]
    omega)
  rw [← getVert_support_get _ (by omega)] at this
  rw [← getVert_support_get _ (by
    omega
    )] at this
  apply this
  simp only [getVert_zero, length_cons, length_tail_add_one, Option.some.injEq]
  have : p.length = (Walk.cons hadj p.tail).length := by
    rw [Walk.length_cons]
    exact (length_tail_add_one hnp).symm
  rw [length_tail_add_one hnp]
  rw [this]
  rw [Walk.getVert_length_sub_one (Walk.not_nil_cons)]
  exact h.symm

lemma Walk.cons_lastButOneOfNotNil {p : G.Walk u v} (hnp : ¬ p.Nil) (hadj : G.Adj w u)
    : (Walk.cons hadj p).lastButOneOfNotNil = p.lastButOneOfNotNil := by
  cases p with
  | nil =>
    simp at hnp
  | cons h q =>
    unfold lastButOneOfNotNil
    simp only [length_cons, add_tsub_cancel_right, getVert_cons_succ]

lemma Walk.IsPath.start_ne_lastButOne' {p : G.Walk u v} (hnp : ¬ p.Nil)  (hadj : G.Adj w u)
    (hpath : (Walk.cons hadj p).IsPath) : (Walk.cons hadj p).lastButOneOfNotNil ≠ w := by
  intro h
  have hnodup := hpath.2
  rw [@List.nodup_iff_get?_ne_get?] at hnodup
  have hpl : 0 < p.length := by
    rw [SimpleGraph.Walk.nil_iff_length_eq] at hnp
    omega
  have := hnodup 0 ((Walk.cons hadj p).length - 1) (by
    unfold length
    omega
    ) (by
    rw [length_support]
    omega)
  rw [← getVert_support_get _ (by omega)] at this
  rw [← getVert_support_get _ (by omega)] at this
  apply this
  simp only [getVert_zero, length_cons, length_tail_add_one, Option.some.injEq]
  have : p.length = (Walk.cons hadj p).length - 1 := by
    rw [Walk.length_cons]
    omega
  rw [this]
  simp only [length_cons, add_tsub_cancel_right]
  rw [getVert_cons p hadj (by omega)]
  rw [getVert_length_sub_one hnp]
  rw [Walk.cons_lastButOneOfNotNil hnp] at h
  exact h.symm

lemma Walk.IsCircuit.reverse {p: G.Walk u u} (hp : p.IsCircuit) : p.reverse.IsCircuit := by
  constructor
  · exact hp.1.reverse
  · intro h
    rw [← @nil_iff_eq_nil] at h
    rw [@reverse_Nil] at h
    apply hp.2
    exact nil_iff_eq_nil.mp h

@[simp]
lemma List.getElem?_tail {l : List α} {n : ℕ} : l.tail[n]? = l[n + 1]? := by
  induction l with
  | nil => simp only [List.tail_nil, List.getElem?_nil]
  | cons h q _ => simp only [List.tail_cons, List.getElem?_cons_succ]

lemma getVert_support_getElem? (p : G.Walk u v) (h2 : n ≤ p.length) : p.getVert n = p.support[n]? := by
  match p, n with
  | .nil, 0 =>
    simp only [Walk.getVert_zero, Walk.support_nil, List.length_singleton, zero_lt_one,
      List.getElem?_eq_getElem, List.getElem_cons_zero]
  | .nil, (n + 1) =>
    simp only [Walk.length_nil, nonpos_iff_eq_zero, add_eq_zero, one_ne_zero, and_false] at h2
  | .cons h q, 0 =>
    simp only [Walk.getVert_zero, Walk.support_cons, List.length_cons, Walk.length_support,
      lt_add_iff_pos_left, add_pos_iff, Nat.ofNat_pos, or_true, List.getElem?_eq_getElem,
      List.getElem_cons_zero]
  | .cons h q, (n + 1) =>
    simp only [Walk.getVert_cons_succ, Walk.support_cons, List.getElem?_cons_succ]
    apply getVert_support_getElem?
    rw [@Walk.length_cons] at h2
    omega

lemma Walk.IsCycle.getVert_internal_neq_endpoint {i : ℕ} {p : G.Walk u u} (hp : p.IsCycle)
    (h : 0 < i) (h' : i < p.length) : p.getVert i ≠ u := by
  have hnodup := hp.2
  rw [List.nodup_iff_getElem?_ne_getElem?] at hnodup
  have := hnodup (i - 1) (p.length - 1) (by omega) (by rw [support_tail_length]; omega)
  simp only [List.getElem?_tail] at this ⊢
  rw [← getVert_support_getElem? _ (by omega), ← getVert_support_getElem? _ (by omega)] at this
  rw [(by omega : i - 1 + 1 = i), (by omega : p.length - 1 + 1 = p.length)] at this
  simpa only [getVert_length, ne_eq, Option.some.injEq] using this

/--
  Private because it's a strict subcase of nodup and nodup'
-/
private lemma Walk.IsCycle.getVert_internal_nodup {i j : ℕ} {p : G.Walk u u} (hp : p.IsCycle) (hi : 0 < i) (hij : i < j)
    (hjl : j < p.length) : p.getVert i ≠ p.getVert j := by
  have hnodup := hp.2
  rw [List.nodup_iff_getElem?_ne_getElem?] at hnodup
  have := hnodup (i - 1) (j - 1) (by omega) (by rw [support_tail_length]; omega)
  simp only [List.getElem?_tail] at this ⊢
  rw [← getVert_support_getElem? _ (by omega), ← getVert_support_getElem? _ (by omega)] at this
  rw [(by omega : i - 1 + 1 = i), (by omega : j - 1 + 1 = j)] at this
  simpa only [getVert_length, ne_eq, Option.some.injEq] using this

lemma Walk.IsCycle.getVert_nodup {i j : ℕ} {p : G.Walk u u} (hp : p.IsCycle) (hij : i < j)
    (hjl : j < p.length - 1) : p.getVert i ≠ p.getVert j := by
  by_cases h : i = 0
  · simp only [h, getVert_zero]
    exact (hp.getVert_internal_neq_endpoint (by omega) (by omega)).symm
  · exact hp.getVert_internal_nodup (by omega) (by omega) (by omega)

lemma Walk.IsCycle.getVert_nodup' {i j : ℕ} {p : G.Walk u u} (hp : p.IsCycle) (hi : 0 < i) (hij : i < j)
    (hjl : j ≤ p.length): p.getVert i ≠ p.getVert j := by
  by_cases h : j = p.length
  · simp only [h, getVert_length, ne_eq]
    exact (hp.getVert_internal_neq_endpoint (by omega) (by omega))
  · exact hp.getVert_internal_nodup (by omega) (by omega) (by omega)

lemma Walk.tail_nodup_reverse {p : G.Walk u u} [DecidableEq V] (hp : p.IsCycle): p.reverse.support.tail.Nodup  := by
  have hp3 : p.length ≥ 3 := IsCycle.three_le_length hp
  rw [support_reverse, List.nodup_iff_get?_ne_get?]
  intro i j hij hj
  simp only [List.length_tail, List.length_reverse, length_support, add_tsub_cancel_right] at hj
  simp [List.length_tail, List.length_reverse, tail_get?]

  rw [List.getElem?_reverse (by
    rw [List.length_dropLast,support_length]; omega),
    List.getElem?_reverse (by rw [List.length_dropLast, support_length]; omega)]
  simp only [@List.getElem?_dropLast]
  rw [← getVert_support_getElem? _ (by rw [List.length_dropLast, support_length]; omega)]
  rw [← getVert_support_getElem? _ (by rw [List.length_dropLast, support_length]; omega)]
  simp only [length_support, add_tsub_cancel_right, Option.some.injEq]
  by_cases hj' : j = p.length
  · simp only [hj', le_add_iff_nonneg_right, zero_le, tsub_eq_zero_of_le, getVert_zero]
    omega
  · by_cases hj'' : j = p.length - 1
    · simp [List.length_dropLast, length_support, add_tsub_cancel_right, hj'', Nat.sub_self,
      getVert_zero, show p.length - 1 - i < p.length from by omega, show 0 < p.length from by omega]
      exact hp.getVert_internal_neq_endpoint (by omega) (by omega)
    · simp [show p.length - 1 - i < p.length from by omega, show p.length - 1 - j < p.length from by omega, show 0 < p.length from by omega]
      exact (hp.getVert_nodup' (by omega) (by omega) (by omega)).symm


lemma Walk.IsCycle.reverse {p : G.Walk u u} [DecidableEq V] (hp : p.IsCycle) : p.reverse.IsCycle := by
  constructor
  · exact hp.1.reverse
  · exact Walk.tail_nodup_reverse hp


lemma Walk.IsCycle.decompose_mem_support_part' {p : G.Walk u u} {q : G.Walk u v} {r : G.Walk v u} (hp : p.IsCycle) (h : p = q.append r)
    (hrpath : r.IsPath)
    (hux : p.toSubgraph.Adj u x) (hx : ¬ q.toSubgraph.Adj u x) (huv : u ≠ v) (hxu : x ≠ u) (hxv : x ≠ v) : x ∉ q.support := by
  have : r.toSubgraph.Adj u x := by
    rw [h] at hux
    simp only [toSubgraph_append, Subgraph.sup_adj] at hux
    cases hux with
    | inl h1 => exact (hx h1).elim
    | inr h2 => exact h2

  have : r.reverse.getVert 1 = x := by
    exact SimpleGraph.toSubgraph_adj_sndOfNotNil r.reverse (
      (isPath_reverse_iff r).mpr hrpath) (by simpa [SimpleGraph.Walk.toSubgraph_reverse] )
  intro hq
  obtain ⟨i, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hq
  have hrl1 : r.getVert (r.length - 1) = x := by
    rw [← this, getVert_length_sub_one (not_nil_of_ne huv.symm)]
    unfold lastButOneOfNotNil
    rw [← @getVert_reverse]

  have hine0 : i ≠ 0 := by
    intro hi'
    rw [hi'] at hi
    rw [@getVert_zero] at hi
    exact hxu hi.1.symm

  have hnodup := hp.2
  rw [@List.nodup_iff_get?_ne_get?] at hnodup
  have hp3 : p.length ≥ 3 := three_le_length hp

  have hiq : i < q.length := by
    have h1 := hi.2
    rw [@Nat.le_iff_lt_or_eq] at h1
    cases h1 with
    | inl hl => exact hl
    | inr hr =>
      rw [hr] at hi
      rw [@getVert_length] at hi
      exact (hxv hi.1.symm).elim
  have hqp : q.length ≤ p.length := by
    rw [h]
    rw [@length_append]
    exact Nat.le_add_right q.length r.length
  have h3 : r.length ≥ 1 := by
    by_contra! hc
    rw [@Nat.lt_one_iff] at hc
    exact (not_nil_of_ne huv.symm) (SimpleGraph.Walk.nil_iff_length_eq.mpr hc)
  have := hnodup (i - 1) (p.length - 2) (by
    have h2 : p.length = q.length + r.length := by
      rw [h]
      exact length_append q r

    rw [h2]
    omega
    ) (by rw [@support_tail_length]; omega)
  apply this
  rw [@tail_get?]
  rw [@tail_get?]
  have : i - 1 + 1 = i := by omega
  rw [this]
  have : p.length - 2 + 1 = p.length - 1 := by omega
  rw [this]
  rw [← getVert_support_get _ (by omega)]
  rw [← getVert_support_get _ (by
    omega
    )]
  simp only [Option.some.injEq]

  rw [h]
  simp only [length_append]
  rw [@getVert_append]
  simp only [hiq, ↓reduceIte, hi.1]
  rw [getVert_append]
  have : ¬ q.length + r.length - 1 < q.length := by omega
  simp only [this, ↓reduceIte]
  have : q.length + r.length - 1 - q.length = r.length - 1 := by omega
  rw [this, hrl1]

lemma Walk.IsCycle.decompose_mem_support_part'' {p : G.Walk u u} {q : G.Walk u v} {r : G.Walk v u} (hp : p.IsCycle) (h : p = q.append r)
    (hqpath : q.IsPath)
    (hux : p.toSubgraph.Adj u x) (hx : ¬ r.toSubgraph.Adj u x) (huv : u ≠ v) (hxu : x ≠ u) (hxv : x ≠ v) : x ∉ r.support := by

  have : q.toSubgraph.Adj u x := by
    rw [h] at hux
    simp only [toSubgraph_append, Subgraph.sup_adj] at hux
    cases hux with
    | inl h1 => exact h1
    | inr h2 => exact (hx h2).elim

  have hqs : q.getVert 1 = x := by
    exact SimpleGraph.toSubgraph_adj_sndOfNotNil q (hqpath) this

  intro hr
  obtain ⟨i, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hr

  have hine0 : i ≠ 0 := by
    intro hi'
    rw [hi'] at hi
    rw [@getVert_zero] at hi
    exact hxv hi.1.symm

  have hnodup := hp.2
  rw [@List.nodup_iff_get?_ne_get?] at hnodup
  have hp3 : p.length ≥ 3 := three_le_length hp

  have hir : i < r.length := by
    have h1 := hi.2
    rw [@Nat.le_iff_lt_or_eq] at h1
    cases h1 with
    | inl hl => exact hl
    | inr hr =>
      rw [hr] at hi
      rw [@getVert_length] at hi
      exact (hxu hi.1.symm).elim

  have hqp : r.length ≤ p.length := by
    rw [h]
    rw [@length_append]
    exact Nat.le_add_left r.length q.length
  have h3 : q.length ≥ 1 := by
    by_contra! hc
    rw [@Nat.lt_one_iff] at hc
    exact (not_nil_of_ne huv) (SimpleGraph.Walk.nil_iff_length_eq.mpr hc)
  have := hnodup 0 (q.length + i - 1) (by
    omega
    ) (by rw [@support_tail_length]
          have h2 : p.length = q.length + r.length := by
            rw [h]
            exact length_append q r
          omega)
  apply this
  rw [@tail_get?]
  rw [@tail_get?]

  have : q.length + i + 1 ≤ p.length := by
    rw [h]
    simp only [length_append]
    omega

  rw [← getVert_support_get _ (by omega)]
  rw [← getVert_support_get _ (by
    omega
    )]
  simp only [Option.some.injEq]

  rw [h]
  have : (q.append r).getVert 1 = q.getVert 1 := by
    rw [getVert_append]
    by_cases hq1 : q.length = 1
    · simp only [ite_eq_left_iff, not_lt]
      intro _
      rw [hq1]
      simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, getVert_zero]
      rw [← hq1]
      simp only [getVert_length]
    · simp only [ite_eq_left_iff, not_lt]
      intro hq
      omega

  rw [this]

  rw [getVert_append]

  have : ¬ q.length + i - 1 + 1 < q.length := by omega
  simp only [this, ↓reduceIte]
  have : q.length + i - 1 + 1 - q.length = i := by omega
  rw [this, hi.1]
  rw [← hqs]

lemma ConnectedComponent.supp_induce_connected {H : Subgraph G} (hH : H.IsSpanning) (c : ConnectedComponent H.coe) (h : v ∈ Subtype.val '' c.supp) : (H.induce (Subtype.val '' c.supp)).Connected := by
  rw [@Subgraph.connected_iff]
  have : (H.induce (Subtype.val '' c.supp)).verts.Nonempty := by
    use v
    rw [@Subgraph.induce_verts]
    exact h
  refine ⟨?_, this⟩
  rw [@Subgraph.preconnected_iff]
  intro u w

  exact reachable_in_connected_component_induce_coe hH _ _ _


lemma ConnectedComponent.supp_eq_of_mem_supp {c c' : ConnectedComponent G} {v} (h : v ∈ c.supp) (h' : v ∈ c'.supp) : c = c' := by
  simp [SimpleGraph.ConnectedComponent.mem_supp_iff] at h h'
  subst h h'
  rfl
