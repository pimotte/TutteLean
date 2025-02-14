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

lemma mem_supp_of_adj_alt {c : G.ConnectedComponent} (h : v ∈ c.supp) (h' : G.Adj v w) : w ∈ c.supp := by
  simp only [ConnectedComponent.mem_supp_iff] at *
  rw [← h]
  exact ConnectedComponent.connectedComponentMk_eq_of_adj h'.symm

-- In #20830
@[simp]
lemma sup_spanningCoe (H H' : Subgraph G) : (H ⊔ H').spanningCoe = H.spanningCoe ⊔ H'.spanningCoe := by rfl

-- In #20830
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
    apply hp.getVert_injOn (by rw [@Set.mem_setOf]; omega) (by rw [@Set.mem_setOf]; omega) at h

    omega

  have hsnv : p.getVert (n - 1) ≠ v := by
    intro h
    have : p.getVert (n - 1) = p.getVert 0 := by aesop
    apply hp.getVert_injOn (by rw [Set.mem_setOf]; omega) (by rw [Set.mem_setOf]; omega) at this
    omega

  have hpnv : p.getVert (n + 1) ≠ v := by
    have : p.getVert (n + 1) = p.getVert 0 := by aesop
    by_cases h : n = p.length
    · subst h
      simp_all only [ne_eq, and_true, Set.mem_insert_iff, Set.mem_singleton_iff, le_refl, Walk.getVert_length,
        not_true_eq_false]
    apply hp.getVert_injOn (by rw [Set.mem_setOf]; omega) (by rw [Set.mem_setOf]; omega) at this
    omega

  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsgv hpgv
  aesop

-- In #20830
lemma subgraphOfAdj_spanningCoe (hadj : G.Adj v w) : (G.subgraphOfAdj hadj).spanningCoe = fromEdgeSet {s(v, w)} := by
  ext v w
  aesop

-- In #20830
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
  obtain ⟨w', ⟨hw'1, hw'2⟩⟩ := hcyc.other_adj_of_adj (this.adj_sub)
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
      apply hp.getVert_injOn (by rw [Set.mem_setOf]; omega) (by rw [Set.mem_setOf]; omega) at this
      omega
    have : p.getVert (i + 1) = p.getVert 0 := by aesop
    apply hp.getVert_injOn (by rw [Set.mem_setOf]; omega) (by rw [Set.mem_setOf]; omega) at this
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

-- In #20830
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
  rw [← p.mem_verts_toSubgraph]
  exact p.toSubgraph.edge_vert hp

-- In #20830 (obsoleted)
lemma get?_nonZero (a : α) (l : List α) (h : n ≠ 0) : (a :: l).get? n = l.get? (n - 1) := by
    have : ∃ (i : ℕ), i.succ = n := by
      use (n - 1)
      exact Nat.sub_one_add_one_eq_of_pos (Nat.zero_lt_of_ne_zero h)
    obtain ⟨i, hi⟩ := this
    rw [← hi]
    simp only [Nat.succ_eq_add_one, List.get?_cons_succ, add_tsub_cancel_right]

-- In #20830 (obsoleted)
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

-- In #20830
lemma card_subgraph_argument [DecidableEq V] {H : Subgraph G} (h : G.neighborSet v ≃ H.neighborSet v) (hfin : (G.neighborSet v).Finite) : ∀ w, H.Adj v w ↔ G.Adj v w := by
  intro w
  refine ⟨fun a => a.adj_sub, ?_⟩
  have : Finite (H.neighborSet v) := by
    rw [Set.finite_coe_iff, ← (Equiv.set_finite_iff h)]
    exact hfin
  have : Fintype (H.neighborSet v) := by
    exact Set.Finite.fintype this
  let f : H.neighborSet v → G.neighborSet v := fun a => ⟨a, a.coe_prop.adj_sub⟩
  have hfinj : f.Injective := by
    intro w w' hww'
    aesop
  have hfsurj : f.Surjective := by
    apply Function.Injective.surjective_of_fintype _ hfinj
    exact h.symm
  have hfbij : f.Bijective := ⟨hfinj, hfsurj⟩
  have g := Fintype.bijInv hfbij
  intro h
  obtain ⟨v', hv'⟩ : ∃ v', f v' = ⟨w, h⟩ := hfsurj ⟨w, h⟩
  have : (f v').1 = (⟨w, h⟩ : G.neighborSet v).1 := by
    exact congrArg Subtype.val hv'
  simp at this
  rw [← this]
  have := (g ⟨w, h⟩).coe_prop
  rw [← hv'] at this
  aesop

-- In #20830
def Walk.coeWalk {H : Subgraph G} {u v : H.verts} (p : H.coe.Walk u v) : G.Walk u.val v.val :=
  match p with
  | .nil => Walk.nil
  | .cons h q => Walk.cons (H.adj_sub h) (q.coeWalk)

-- In #20830 (obsoleted)
theorem Subgraph.verts_bot_iff (H : G.Subgraph) : H.verts = ∅ ↔ H = ⊥ := by
  refine ⟨?_, by aesop⟩
  intro h
  rw [Subgraph.ext_iff]
  refine ⟨h, ?_⟩
  ext v w
  simp only [not_bot_adj, iff_false]
  intro hadj
  have := hadj.fst_mem
  simp_all only [Set.mem_empty_iff_false]

-- In #20830 (obsoleted)
lemma Subgraph_eq_component_supp {H : Subgraph G} (hb : H ≠ ⊥) (h : ∀ v ∈ H.verts, ∀ w, H.Adj v w ↔ G.Adj v w)
    (hc : H.Connected) :
    ∃ c : G.ConnectedComponent, H.verts = c.supp := by
  rw [SimpleGraph.ConnectedComponent.exists]
  simp at hb
  rw [← Subgraph.verts_bot_iff, Set.eq_empty_iff_forall_not_mem] at hb
  push_neg at hb
  obtain ⟨v, hv⟩ := hb
  use v
  ext w
  simp only [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
  by_cases hvw : v = w
  · aesop
  constructor
  · intro hw
    obtain ⟨p⟩ := hc ⟨v, hv⟩ ⟨w, hw⟩
    simpa using p.coeWalk.reachable.symm
  · let rec aux {v' : V} (hv' : v' ∈ H.verts) (p : G.Walk v' w) : w ∈ H.verts := by
      by_cases hnp : p.Nil
      · have : v' = w := hnp.eq
        exact this ▸ hv'
      have : p.getVert 1 ∈ H.verts := H.edge_vert (by
            rw [Subgraph.adj_comm, h _ hv' _]
            exact Walk.adj_snd hnp)
      exact aux this p.tail
    termination_by p.length
    decreasing_by {
      simp_wf
      rw [← Walk.length_tail_add_one hnp]
      omega
    }
    exact fun hr ↦ aux hv hr.some.reverse

-- In #20830
lemma Path.of_IsCycles [Fintype V] [DecidableEq V] {c : G.ConnectedComponent} (h : G.IsCycles) (hv : v ∈ c.supp)
  (hn : (G.neighborSet v).Nonempty) :
    ∃ (p : G.Walk v v), p.IsCycle ∧ p.toSubgraph.verts = c.supp := by
  obtain ⟨w, hw⟩ := hn
  simp only [mem_neighborSet] at hw
  have := IsCycles_Reachable hw h
  obtain ⟨u, p, hp⟩ := SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle.mp ⟨hw, this⟩

  have hvp : v ∈ p.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges _ hp.2
  have : p.toSubgraph.verts = c.supp := by
    obtain ⟨c', hc'⟩ := Subgraph_eq_component_supp (by
      intro hpb
      rw [← @Subgraph.verts_bot_iff, Set.eq_empty_iff_forall_not_mem] at hpb
      rw [← Walk.mem_verts_toSubgraph] at hvp
      exact hpb _ hvp) (by
        intro v hv w
        refine card_subgraph_argument ?_ (Set.toFinite _) w
        exact @Classical.ofNonempty _ (by
          rw [← Cardinal.eq]
          apply Cardinal.toNat_injOn (Set.mem_Iio.mpr (by apply Cardinal.lt_aleph0_of_finite))
                (Set.mem_Iio.mpr (by apply Cardinal.lt_aleph0_of_finite))
          rw [← Set.cast_ncard (Set.toFinite _),← Set.cast_ncard (Set.toFinite _)]
          rw [h (by
            rw [@Walk.mem_verts_toSubgraph] at hv
            exact (Set.nonempty_of_ncard_ne_zero (by rw [hp.1.ncard_neighborSet_toSubgraph_eq_two hv]; omega)).mono (p.toSubgraph.neighborSet_subset v)
            )]
          rw [hp.1.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.mp hv)])
        ) p.toSubgraph_connected
    rw [hc']
    have : v ∈ c'.supp := by
      rw [← hc', Walk.mem_verts_toSubgraph]
      exact hvp
    simp_all
  use p.rotate hvp
  rw [← this]
  refine ⟨?_, by simp_all only [ConnectedComponent.mem_supp_iff, Walk.verts_toSubgraph, Walk.toSubgraph_rotate]⟩
  exact hp.1.rotate _

lemma IsCycle.first_two {p : G.Walk v v} (h : p.IsCycle) (hadj : p.toSubgraph.Adj v w) :
    ∃ (p' : G.Walk v v), p'.IsCycle ∧ p'.getVert 1 = w ∧ p'.toSubgraph.verts = p.toSubgraph.verts := by
  have : w ∈ p.toSubgraph.neighborSet v := hadj
  rw [h.neighborSet_toSubgraph_endpoint] at this
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  cases' this with hl hr
  · use p
    exact ⟨h, hl.symm, rfl⟩
  · use p.reverse
    rw [Walk.penultimate, ← @Walk.getVert_reverse] at hr
    exact ⟨h.reverse, hr.symm, by rw [SimpleGraph.Walk.toSubgraph_reverse _]⟩

-- In takeUntil PR
lemma cons_takeUntil [DecidableEq V] {p : G.Walk v' v} (hwp : w ∈ p.support) (h : u ≠ w) (hadj : G.Adj u v')
  (hwp' : w ∈ (Walk.cons hadj p).support := List.mem_of_mem_tail hwp) :
  (Walk.cons hadj p).takeUntil w hwp' = Walk.cons hadj (p.takeUntil w hwp) := by
  nth_rewrite 1 [Walk.takeUntil]
  simp [h]

-- In takeUntil PR
@[simp]
lemma takeUntil_first [DecidableEq V] (p : G.Walk u v) (hup : u ∈ p.support) : p.takeUntil u hup = Walk.nil := by
  cases p with
  | nil => rfl
  | cons h q => simp [Walk.takeUntil]

-- In takeUntil PR
lemma takeUntil_notNil [DecidableEq V] (p : G.Walk u v) (hwp : w ∈ p.support) (huw : u ≠ w) : ¬ (p.takeUntil w hwp).Nil := by
  intro hnil
  cases p with
  | nil =>
    simp only [Walk.support_nil, List.mem_singleton] at hwp
    exact huw hwp.symm
  | @cons _ v' _ h q =>
    simp only [Walk.support_cons, List.mem_cons, huw.symm, false_or] at hwp
    simp [cons_takeUntil hwp huw] at hnil

lemma support_length (p : G.Walk v w) : p.support.length = p.length + 1 := by
  match p with
  | .nil => simp only [Walk.support_nil, List.length_singleton, Walk.length_nil, zero_add]
  | .cons _ _ => simp only [Walk.support_cons, List.length_cons, Walk.length_support,
    Nat.succ_eq_add_one, Walk.length_cons]

lemma IsPath.getVert_injOn_iff (p : G.Walk u v): Set.InjOn p.getVert {i | i ≤ p.length} ↔ p.IsPath := by
  refine ⟨?_, fun a => a.getVert_injOn⟩
  intro hinj
  rw [@Walk.isPath_def]
  rw [@List.nodup_iff_getElem?_ne_getElem?]
  intro i j hij hjp hsij
  rw [@support_length] at hjp
  have := hinj (by omega : i ≤ p.length) (by omega : j ≤ p.length)
  apply hij.ne
  apply this
  rw [← SimpleGraph.Walk.getVert_eq_support_get? _ (by omega : i ≤ p.length),
      ← SimpleGraph.Walk.getVert_eq_support_get? _ (by omega : j ≤ p.length)] at hsij
  exact Option.some_injective _ hsij

-- In takeUntil PR
lemma Walk.IsCycle.of_append_right {p : G.Walk u v} {q : G.Walk v u} (h : u ≠ v) (hcyc : (p.append q).IsCycle) : q.IsPath := by
  have := hcyc.2
  rw [SimpleGraph.Walk.tail_support_append, List.nodup_append] at this
  rw [@isPath_def, @support_eq_cons, @List.nodup_cons]
  exact ⟨this.2.2 (p.end_mem_tail_support_of_ne h), this.2.1⟩

-- In takeUntil PR
lemma IsCycle_takeUntil [DecidableEq V] {p : G.Walk v v} (h : p.IsCycle) (hwp : w ∈ p.support) :
    (p.takeUntil w hwp).IsPath := by
  by_cases hvw : v = w
  · subst hvw
    rw [takeUntil_first]
    exact Walk.IsPath.nil
  rw [← Walk.isCycle_reverse] at h
  rw [← Walk.take_spec p hwp] at h
  rw [@Walk.reverse_append] at h
  rw [← @Walk.isPath_reverse_iff]
  exact Walk.IsCycle.of_append_right hvw h

-- In takeUntil PR
lemma takeUntil_getVert_one [DecidableEq V] {p : G.Walk u v} (hsu : w ≠ u) (h : w ∈ p.support)
  : (p.takeUntil w h).getVert 1 = p.getVert 1 := by
  have : ¬ p.Nil := by
    intro hnp
    rw [SimpleGraph.Walk.nil_iff_support_eq] at hnp
    rw [hnp] at h
    simp at h
    exact hsu h
  cases p with
  | nil => aesop
  | @cons _ v' _ hadj q =>
    rw [@Walk.mem_support_iff] at h
    cases' h with hl hr
    · aesop
    rw [Walk.support_cons, List.tail_cons] at hr
    rw [cons_takeUntil hr hsu.symm _]
    simp

-- In takeUntil PR
lemma takeUntil_getVert [DecidableEq V] {p : G.Walk u v} (hw : w ∈ p.support) (hn : n ≤ (p.takeUntil w hw).length) :
    (p.takeUntil w hw).getVert n = p.getVert n := by
  cases p with
  | nil =>
    simp only [Walk.support_nil, List.mem_singleton] at hw
    aesop
  | @cons _ v' _ h q =>
    simp at hw
    by_cases huw : w = u
    · subst huw
      simp_all only [takeUntil_first, Walk.length_nil, nonpos_iff_eq_zero, Walk.getVert_zero]
    simp only [huw, false_or] at hw
    push_neg at huw
    rw [cons_takeUntil hw huw.symm] at hn ⊢
    by_cases hn0 : n = 0
    · aesop
    rw [Walk.getVert_cons _ _ hn0]
    rw [Walk.getVert_cons _ _ hn0]
    apply takeUntil_getVert hw
    rw [@Walk.length_cons] at hn
    omega

-- In takeUntil PR
lemma Walk.length_takeUntil_lt [DecidableEq V] {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) (huw : u ≠ w) : (p.takeUntil u h).length < p.length := by
  have := SimpleGraph.Walk.length_takeUntil_le p h
  rw [this.lt_iff_ne]
  intro hl
  have : (p.takeUntil u h).getVert (p.takeUntil u h).length = p.getVert p.length := by
    rw [takeUntil_getVert _ (by omega), hl]
  simp at this
  exact huw this


-- In takeUntil PR
lemma takeUntil_takeUntil [DecidableEq V] {p : G.Walk u v} (w x : V) (hw : w ∈ p.support) (hx : x ∈ (p.takeUntil w hw).support) :
  (p.takeUntil w hw).takeUntil x hx = p.takeUntil x (p.support_takeUntil_subset hw hx) := by
  cases p
  · sorry
  · sorry

-- In takeUntil PR
lemma Walk.IsCycle.takeUntil [DecidableEq V] {p : G.Walk u u} (hp : p.IsCycle) (hw : w ∈ p.support) : (p.takeUntil w hw).IsPath := by
  exact IsCycle_takeUntil hp hw

-- In takeUntil PR
lemma takeUntil_last [DecidableEq V] {p : G.Walk u v} (hp : p.IsPath) (hw : w ∈ p.support) (h : v ≠ w) :
  v ∉ (p.takeUntil w hw).support := by
  intro hv
  rw [@Walk.mem_support_iff_exists_getVert] at hv
  obtain ⟨n, ⟨hn, hnl⟩⟩ := hv
  rw [takeUntil_getVert hw hnl] at hn
  have := Walk.length_takeUntil_lt p hw h.symm
  have : n = p.length := hp.getVert_injOn (by rw [@Set.mem_setOf]; omega) (by rw [@Set.mem_setOf]) (hn.symm ▸ p.getVert_length.symm)
  omega

-- In takeUntil (not really, but easy to inline)
lemma cycle_takeUntil_new [DecidableEq V] (p : G.Walk u u) (hp : p.IsCycle) (hw : w ∈ p.support) (hx : x ∈ (p.takeUntil w hw).support)  (hwx : w ≠ x):
    w ∉ (p.takeUntil x (p.support_takeUntil_subset hw hx)).support :=
  (takeUntil_takeUntil w x hw hx) ▸
    takeUntil_last (IsCycle_takeUntil hp hw) hx hwx


-- In takeUntil PR
lemma cycle_takeUntil_takeUntil_adj [DecidableEq V] (p : G.Walk u u) (hp : p.IsCycle) (hw : w ∈ p.support) (hx : x ∈ (p.takeUntil w hw).support) :
    ¬((p.takeUntil w hw).takeUntil x hx).toSubgraph.Adj w x := by
  rw [Subgraph.adj_comm]
  intro h
  have hww : (p.takeUntil w hw).getVert (p.takeUntil w hw).length = w := Walk.getVert_length _
  have hx := Walk.toSubgraph_Adj_mem_support_new _ h.symm
  rw [@Walk.mem_support_iff_exists_getVert] at hx
  obtain ⟨n, ⟨hn, hnl⟩⟩ := hx
  rw [takeUntil_getVert _ (by omega)] at hn
  have heq : (p.takeUntil w hw).getVert n = (p.takeUntil w hw).getVert (p.takeUntil w hw).length := by simp_all only [Walk.getVert_length]
  have := Walk.length_takeUntil_lt (p.takeUntil w hw) hx h.ne

  apply (hp.takeUntil hw).getVert_injOn (by rw [@Set.mem_setOf]; omega) (by simp) at heq
  omega

lemma cycles_arg [Finite V] [DecidableEq V] {p : G.Walk u u} (hp : p.IsCycle) (hcyc : G.IsCycles) (hv : v ∈ p.toSubgraph.verts) :
    ∀ w, p.toSubgraph.Adj v w ↔ G.Adj v w := by
  intro w
  refine card_subgraph_argument (?_ : Inhabited ((G.neighborSet v) ≃ (p.toSubgraph.neighborSet v))).default (Set.toFinite _) w
  apply Classical.inhabited_of_nonempty

  have h : (G.neighborSet v).Nonempty := Set.Nonempty.mono (p.toSubgraph.neighborSet_subset v) <|
           Set.nonempty_of_ncard_ne_zero <|
          by simp [hp.ncard_neighborSet_toSubgraph_eq_two (by aesop), Set.Nonempty.mono, Set.nonempty_of_ncard_ne_zero]
  rw [← Cardinal.eq, ← Set.cast_ncard (Set.toFinite _), ← Set.cast_ncard (Set.toFinite _),
        hcyc h, hp.ncard_neighborSet_toSubgraph_eq_two (by aesop)]


lemma IsAlternating.spanningCoe (H : Subgraph G) (halt : G.IsAlternating G') : H.spanningCoe.IsAlternating G' := by
  intro v w w' hww' hvw hvv'
  simp only [Subgraph.spanningCoe_adj] at hvw hvv'
  exact halt hww' hvw.adj_sub hvv'.adj_sub

lemma IsAlternating.sup_edge (halt : G.IsAlternating G') (hnadj : ¬G'.Adj u x) (hu' : ∀ u', u' ≠ u → G.Adj x u' → G'.Adj x u')
  (hx' : ∀ x', x' ≠ x → G.Adj x' u → G'.Adj x' u): (G ⊔ edge u x).IsAlternating G' := by
  by_cases hadj : G.Adj u x
  · rwa [sup_edge_of_adj G hadj]
  intro v w w' hww' hvw hvv'
  simp only [sup_adj, edge_adj] at hvw hvv'
  cases' hvw with hl hr <;> cases' hvv' with h1 h2
  · exact halt hww' hl h1
  · rw [G'.adj_congr_of_sym2 (by aesop : s(v, w') = s(u, x))]
    simp only [hnadj, not_false_eq_true, iff_true]
    rcases h2.1 with (⟨h2l1, h2l2⟩| ⟨h2r1, h2r2⟩)
    · subst h2l1 h2l2
      exact (hx' _ hww' hl.symm).symm
    · aesop
  · rw [G'.adj_congr_of_sym2 (by aesop : s(v, w) = s(u, x))]
    simp only [hnadj, false_iff, not_not]
    rcases hr.1 with (⟨hrl1, hrl2⟩| ⟨hrr1, hrr2⟩)
    · subst hrl1 hrl2
      exact (hx' _ hww'.symm h1.symm).symm
    · aesop
  · aesop

lemma spanningCoe_neighborSet (H : Subgraph G) : H.spanningCoe.neighborSet = H.neighborSet := by
  ext v w
  simp

lemma IsCycle.IsCycles_toSubgraph_spanningCoe {p : G.Walk u u} (hpc : p.IsCycle) :
    p.toSubgraph.spanningCoe.IsCycles := by
  intro v hv
  rw [spanningCoe_neighborSet]
  apply hpc.ncard_neighborSet_toSubgraph_eq_two
  obtain ⟨_, hw⟩ := hv
  exact p.toSubgraph_Adj_mem_support_new hw

lemma mapSpanningSubgraph_inj (h : G ≤ G'): Function.Injective (Hom.mapSpanningSubgraphs h) := by
  intro v w hvw
  simpa [Hom.mapSpanningSubgraphs_apply] using hvw

lemma path_map_spanning {w x : V} (p : G.Walk u v) : p.toSubgraph.Adj w x ↔ (p.mapLe (OrderTop.le_top G)).toSubgraph.Adj w x := by
  simp only [Walk.toSubgraph_map, Subgraph.map_adj]
  nth_rewrite 2 [← Hom.mapSpanningSubgraphs_apply (OrderTop.le_top _) w]
  nth_rewrite 2 [← Hom.mapSpanningSubgraphs_apply (OrderTop.le_top _) x]
  rw [Relation.map_apply_apply (mapSpanningSubgraph_inj _) (mapSpanningSubgraph_inj _)]

lemma path_edge_IsCycles (p : G.Walk u v) (hp : p.IsPath) (h : u ≠ v) (hs : s(v, u) ∉ p.edges) : (p.toSubgraph.spanningCoe ⊔ edge v u).IsCycles := by
  let p' := p.mapLe (OrderTop.le_top G)
  let c := Walk.cons (by simp [h.symm] : (⊤ : SimpleGraph V).Adj v u) p'
  simp only [Hom.coe_ofLE, id_eq] at p' c
  have hc : c.IsCycle := by
    simp [Walk.cons_isCycle_iff, c, p', hp, hs]
  have : p.toSubgraph.spanningCoe ⊔ edge v u = c.toSubgraph.spanningCoe := by
    ext w x
    simp
    simp only [edge_adj, c, p', SimpleGraph.Walk.toSubgraph.eq_2, Subgraph.sup_adj, subgraphOfAdj_adj, ← path_map_spanning]
    aesop

  rw [this]
  exact IsCycle.IsCycles_toSubgraph_spanningCoe hc

lemma Walk.IsPath.getVert_start_iff {i : ℕ} {p : G.Walk u w} (hp : p.IsPath) (hi : i ≤ p.length) :
    p.getVert i = u ↔ i = 0 := by
  refine ⟨?_, by aesop⟩
  intro h
  by_cases hi : i = 0
  · exact hi
  · apply hp.getVert_injOn (by rw [Set.mem_setOf]; omega) (by rw [Set.mem_setOf]; omega)
    simp [h]

lemma Walk.IsPath.getVert_end_iff {i : ℕ} {p : G.Walk u w} (hp : p.IsPath) (hi : i ≤ p.length) :
    p.getVert i = w ↔ i = p.length := by
  have := hp.reverse.getVert_start_iff (by omega : p.reverse.length - i ≤ p.reverse.length)
  simp only [length_reverse, getVert_reverse,
    show p.length - (p.length - i) = i from by omega] at this
  rw [this]
  omega

lemma Walk.IsPath.neighborSet_toSubgraph_start {u} {p : G.Walk u v} (hp : p.IsPath) (hnp : ¬p.Nil):
    p.toSubgraph.neighborSet u = {p.snd} := by
  have hadj1 := p.toSubgraph_adj_snd hnp
  ext v
  simp_all only [Subgraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff,
    SimpleGraph.Walk.toSubgraph_adj_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  refine ⟨?_, by aesop⟩
  rintro ⟨i, (hl | hl)⟩ <;> rw [hp.getVert_start_iff (by omega)] at hl <;> aesop

-- In #21250
lemma nil_reverse {p : G.Walk v w} : p.reverse.Nil ↔ p.Nil := by
  sorry

lemma Walk.IsPath.neighborSet_toSubgraph_end {u} {p : G.Walk u v} (hp : p.IsPath) (hnp : ¬p.Nil):
    p.toSubgraph.neighborSet v = {p.penultimate} := by
  simpa [toSubgraph_reverse, Walk.snd_reverse] using hp.reverse.neighborSet_toSubgraph_start (by simpa [nil_reverse])

lemma Walk.not_nil_of_adj_toSubgraph {u v} (p : G.Walk u v) (hadj : p.toSubgraph.Adj w x) : ¬p.Nil := by
  cases p <;> simp_all

theorem toSubgraph_adj_sndOfNotNil {u v} (p : G.Walk u v) (hpp : p.IsPath)
    (h : v' ∈ p.toSubgraph.neighborSet u) : p.getVert 1 = v' := by
  simpa [hpp.neighborSet_toSubgraph_start (p.not_nil_of_adj_toSubgraph h), Eq.comm] using h

lemma Subgraph.IsMatching.not_adj_of_ne {M : Subgraph G} {u v w : V} (hM : M.IsMatching) (huv : v ≠ w) (hadj : M.Adj u v) : ¬ M.Adj u w := by
  intro hadj'
  obtain ⟨x, hx⟩ := hM (M.edge_vert hadj)
  exact huv (hx.2 _ hadj ▸ (hx.2 _ hadj').symm)

lemma disjoint_edge {u v : V} (h : u ≠ v): Disjoint G (edge u v) ↔ ¬ G.Adj u v := by
  simp [← disjoint_edgeSet, edge_edgeSet_of_ne h]

lemma sdiff_edge {u v : V} (h : ¬G.Adj u v): G \ edge u v = G := by
  by_cases huv : u = v
  · subst huv
    simp [edge_self_eq_bot]
  · simp [disjoint_edge huv, h]

lemma adj_edge_iff {u v x w : V} : (edge u v).Adj x w ↔ (s(u, v) = s(x, w) ∧ (x ≠ w)) := by
  simp only [edge_adj, ne_eq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
    and_congr_left_iff]
  tauto


lemma tutte_part2b [Fintype V] [DecidableEq V] {x b a c : V} {cycles : SimpleGraph V} {M2 : Subgraph (G ⊔ edge a c)} (hM2 : M2.IsPerfectMatching)
    (p : cycles.Walk a x) (hp : p.IsPath) (hcalt : cycles.IsAlternating M2.spanningCoe)
    (hM2nadj : ¬ M2.Adj x a) (hpac : p.toSubgraph.Adj a c) (hnpxb : ¬p.toSubgraph.Adj x b) (hM2ac :  M2.Adj a c) (hgadj : G.Adj x a) (hnxc : x ≠ c)
    (hnab : a ≠ b) (hle : p.toSubgraph.spanningCoe ≤ G ⊔ edge a c) (aux : (c' : V) → c' ≠ a → p.toSubgraph.Adj c' x → M2.Adj c' x):
    ∃ G', G'.IsAlternating M2.spanningCoe ∧ G'.IsCycles ∧ ¬G'.Adj x b ∧ G'.Adj a c ∧ G' ≤ G ⊔ edge a c := by
  use p.toSubgraph.spanningCoe ⊔ edge x a
  refine ⟨IsAlternating.sup_edge (hcalt.spanningCoe p.toSubgraph) (by simp_all) (fun u' hu'x hadj ↦ by simpa [← toSubgraph_adj_sndOfNotNil p hp hadj, toSubgraph_adj_sndOfNotNil p hp hpac]) (fun c' hc'a hadj ↦ aux _ hc'a hadj), ?_⟩

  have hfincycle : (p.toSubgraph.spanningCoe ⊔ edge x a).IsCycles := by
    intro v hv
    refine path_edge_IsCycles _ hp hgadj.ne.symm (fun hadj ↦ ?_) hv
    rw [← Walk.mem_edges_toSubgraph, Subgraph.mem_edgeSet] at hadj
    simp [← toSubgraph_adj_sndOfNotNil p hp hadj.symm, toSubgraph_adj_sndOfNotNil p hp hpac] at hnxc

  have hfin3 : ¬(p.toSubgraph.spanningCoe ⊔ edge x a).Adj x b := by
    simp only [sup_adj, Subgraph.spanningCoe_adj, hnpxb, edge_adj]
    aesop

  exact ⟨hfincycle, hfin3, by aesop,
    sup_le_iff.mpr ⟨hle, fun v w hvw ↦ by simpa [sup_adj, edge_adj, adj_congr_of_sym2 _ (adj_edge_iff.mp hvw).1.symm] using .inl hgadj⟩⟩

theorem tutte_part2 [Fintype V] [DecidableEq V] {x a b c : V} (hxa : G.Adj x a) (hab : G.Adj a b) (hnGxb : ¬G.Adj x b) (hnGac : ¬ G.Adj a c)
    (hnxb : x ≠ b) (hnxc : x ≠ c) (hnac : a ≠ c) (hnbc : b ≠ c)
    (hm1 : ∃ (M : Subgraph (G ⊔ edge x b)), M.IsPerfectMatching)
    (hm2 : ∃ (M : Subgraph (G ⊔ edge a c)), M.IsPerfectMatching)
    : ∃ (M : Subgraph G), M.IsPerfectMatching := by
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
    simp [disjoint_edge hnac, symmDiff_def, hM2ac, hnG'ac]

  let cycles := symmDiff M1.spanningCoe M2.spanningCoe
  have hcalt : cycles.IsAlternating M2.spanningCoe := IsPerfectMatching.isAlternating_symmDiff_right hM1 hM2
  have hcycles := Subgraph.IsPerfectMatching.symmDiff_isCycles hM1 hM2

  have hcxb : cycles.Adj x b := by
    simp [cycles, symmDiff_def, hM2nxb, hM1xb]
  have hcac : cycles.Adj a c := by
    simp [cycles, symmDiff_def, hM2ac, hM1nac]


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
    rw [disjoint_edge hnxb]
    aesop
  push_neg at hxc

  have hacc : a ∈ (cycles.connectedComponentMk c).supp := by
    exact mem_supp_of_adj_alt rfl hcac.symm

  have hnM2 (x' : V) (h : x' ≠ c) : ¬ M2.Adj x' a := by
    rw [M2.adj_comm]
    exact hM2.1.not_adj_of_ne h.symm hM2ac

  have : ∃ x' ∈ ({x, b} : Set V), ∃ (p : cycles.Walk a x'), p.IsPath ∧
    p.toSubgraph.Adj a c ∧ ¬ p.toSubgraph.Adj x b := by
      obtain ⟨p, hp⟩ := Path.of_IsCycles hcycles hacc (Set.nonempty_of_mem hcac)
      obtain ⟨p', hp'⟩ := IsCycle.first_two hp.1 (by
        rwa [cycles_arg hp.1 hcycles (hp.2 ▸ hacc)])
      have hxp' : x ∈ p'.support := by
        rwa [← SimpleGraph.Walk.mem_verts_toSubgraph, hp'.2.2, hp.2]
      by_cases hc : b ∈ (p'.takeUntil x hxp').support
      · use b, (by simp), (p'.takeUntil b (p'.support_takeUntil_subset _ hc))
        refine ⟨(IsCycle_takeUntil hp'.1 (p'.support_takeUntil_subset _ hc)), ⟨?_, fun h ↦ cycle_takeUntil_new p' hp'.1 _
            ((p'.takeUntil b (Walk.support_takeUntil_subset p' hxp' hc)).toSubgraph_Adj_mem_support_new
                 h) hnxb.symm hc⟩⟩
        have : 0 < (p'.takeUntil b (p'.support_takeUntil_subset _ hc)).length := by
          rw [Nat.pos_iff_ne_zero, Ne.eq_def, ← Walk.nil_iff_length_eq]
          exact fun h ↦ takeUntil_notNil p' (p'.support_takeUntil_subset _ hc) hab.ne h
        simpa [takeUntil_getVert_one hab.ne.symm, hp'.2.1] using
          ((p'.takeUntil b (p'.support_takeUntil_subset _ hc)).toSubgraph_adj_getVert this)
      · use x, (by simp), (p'.takeUntil x hxp')
        refine ⟨IsCycle_takeUntil hp'.1 hxp', ⟨?_, fun h ↦ hc ((p'.takeUntil x hxp').toSubgraph_Adj_mem_support_new h.symm)⟩⟩
        have : (p'.takeUntil x hxp').toSubgraph.Adj ((p'.takeUntil x hxp').getVert 0) ((p'.takeUntil x hxp').getVert 1) := by
          apply SimpleGraph.Walk.toSubgraph_adj_getVert
          rw [Nat.pos_iff_ne_zero, Ne.eq_def, ← Walk.nil_iff_length_eq]
          exact fun hl ↦ takeUntil_notNil p' hxp' hxa.ne.symm hl
        simpa [Walk.getVert_zero, takeUntil_getVert_one hxa.ne, hp'.2.1] using this

  obtain ⟨x', hx', p, hp, hpac, hnpxb⟩ := this

  have hle4 : p.toSubgraph.spanningCoe ≤ G ⊔ edge a c := by
    rw [← sdiff_edge (by simpa : ¬ p.toSubgraph.spanningCoe.Adj x b), sdiff_le_iff']
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
