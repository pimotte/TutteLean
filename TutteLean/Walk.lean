import TutteLean.Defs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

lemma sup_support_eq_support_union (H H': Subgraph G) : (H ⊔ H').support = H.support ∪ H'.support := by
  ext v
  constructor
  · intro hv
    rw [SimpleGraph.Subgraph.mem_support ] at hv
    obtain ⟨ w , hw ⟩ := hv
    cases SimpleGraph.Subgraph.sup_adj.mp hw with
    | inl hl =>
      left
      rw [SimpleGraph.Subgraph.mem_support]
      use w
    | inr hr =>
      right
      rw [SimpleGraph.Subgraph.mem_support]
      use w
  · intro hv
    rw [SimpleGraph.Subgraph.mem_support]
    cases hv with
    | inl hl =>
      obtain ⟨ w , hw ⟩ := hl
      exact ⟨ w , SimpleGraph.Subgraph.sup_adj.mpr (.inl hw) ⟩
    | inr hr =>
      obtain ⟨ w , hw ⟩ := hr
      exact ⟨ w , SimpleGraph.Subgraph.sup_adj.mpr (.inr hw) ⟩

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
      refine ⟨this, ?_, ?_⟩
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
