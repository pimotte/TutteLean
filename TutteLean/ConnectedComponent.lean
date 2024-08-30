import TutteLean.Defs

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}


-- in #15539
theorem ConnectedComponent.connectedComponentMk_subset {V : Type u_1} {G G' : SimpleGraph V} {v : V} (h : G ≤ G')
  (c' : G'.ConnectedComponent) (hc' : v ∈ c'.supp) : (G.connectedComponentMk v).supp ⊆ c'.supp := by
  intro v' hv'
  simp only [mem_supp_iff, ConnectedComponent.eq] at hv' ⊢
  rw [ConnectedComponent.sound (hv'.mono h)]
  exact hc'

-- in #15539
lemma ConnectedComponent.union_supps_eq_supp {G G' : SimpleGraph V}
    (h : G ≤ G') (c' : ConnectedComponent G') : ⋃ c : {c : ConnectedComponent G | c.supp ⊆ c'.supp}, c.1.supp = c'.supp := by
  ext v
  simp_rw [Set.mem_iUnion]
  refine ⟨fun ⟨i, hi⟩ ↦ i.2 hi, ?_⟩
  intro hv
  use ⟨G.connectedComponentMk v, by
    simp only [Set.le_eq_subset, Set.mem_setOf_eq]
    exact connectedComponentMk_subset h c' hv
    ⟩
  rfl


-- in #15539
lemma oddSubComponent' [Fintype V] [Inhabited V] [DecidableEq V] (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (h : G ≤ G') (c' : ConnectedComponent G') : Odd (Nat.card c'.supp) ↔  Odd (Nat.card ({(c : {c : ConnectedComponent G | c.supp ⊆ c'.supp}) | Odd (Nat.card c.1.supp) })) := by
  rw [Nat.card_eq_fintype_card]
  rw [@Fintype.card_ofFinset]
  rw [@Set.filter_mem_univ_eq_toFinset]
  rw [@Set.toFinset_card]
  haveI : DecidablePred (fun c : ConnectedComponent G ↦ c.supp ⊆ c'.supp) := by
    exact Classical.decPred _
  simp_rw [(c'.union_supps_eq_supp h).symm]
  rw [← @Set.toFinset_card]
  rw [@Set.toFinset_iUnion V {c : ConnectedComponent G | c.supp ⊆ c'.supp} _ _ (fun c => c.1.supp)]
  rw [Finset.card_biUnion
    (fun x _ y _ hxy ↦ Set.disjoint_toFinset.mpr (pairwise_disjoint_supp_connectedComponent _ (Subtype.coe_ne_coe.mpr hxy
      )))]
  simp_rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
  rw [Nat.card_eq_fintype_card, Fintype.card_ofFinset]
  apply Finset.odd_sum_iff_odd_card_odd



lemma deleteAll [Fintype V] [Inhabited V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]  (H : Subgraph G): H.deleteVerts ⊤ = ⊥ := by
  ext v w
  · rw [@Subgraph.deleteVerts_verts]
    rw [@Set.mem_diff]
    constructor
    · intro h
      exfalso
      apply h.2
      exact trivial
    · intro h
      exact h.elim
  · rw [@Subgraph.deleteVerts_adj]
    constructor
    · intro h
      exfalso
      apply h.2.1
      exact trivial
    · intro h
      exact h.elim

lemma commonComponent [Fintype V] [DecidableEq V] {G G' : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel G'.Adj]
     {c : ConnectedComponent G} {c' d' : ConnectedComponent G'} (h : G ≤ G') (hc' : c.supp ⊆ c'.supp) (hd' : c.supp ⊆ d'.supp) : c' = d' := by
    obtain ⟨ v, hv ⟩ := c.exists_rep
    rw [← (SimpleGraph.ConnectedComponent.mem_supp_iff c' v).mp]
    exact hd' hv
    exact hc' hv


lemma oddComponentsIncrease [Fintype V] [Inhabited V] [DecidableEq V] (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (h : G ≤ G') (u : Set V):
    cardOddComponents ((⊤ : Subgraph G').deleteVerts u).coe ≤ cardOddComponents ((⊤ : Subgraph G).deleteVerts u).coe := by
      unfold cardOddComponents
      --haveI : Finite (ConnectedComponent G)
      --haveI : Finite ↑{ (c : ConnectedComponent ((⊤ : Subgraph G').deleteVerts u).coe) | ConnectedComponent.isOdd c} := Subtype.finite
      let compSet (G'' : SimpleGraph V) := ↑{ (c : ConnectedComponent ((⊤ : Subgraph G'').deleteVerts u).coe) | ConnectedComponent.isOdd c}
      -- let type2 := ↑{ (c : ConnectedComponent ((⊤ : Subgraph G).deleteVerts u).coe) | ConnectedComponent.isOdd c}

      haveI : Fintype (compSet G) := Fintype.ofFinite _
      haveI : Fintype (compSet G') := Fintype.ofFinite _
      rw [Set.ncard_eq_toFinset_card']
      rw [Set.ncard_eq_toFinset_card']
      rw [Set.toFinset_card, Set.toFinset_card]

      if h' : u = ⊤
      then
        subst h'

        have ha := deleteAll (⊤ : Subgraph G)
        rw [@Nat.le_iff_lt_or_eq]
        right
        have compEmpty (G'' : SimpleGraph V): compSet G'' ≃ Empty := by
          have : compSet G'' = ∅ := by
            ext v
            have := v.exists_rep.choose
            have I : DecidableRel G''.Adj := Classical.decRel _
            rw [deleteAll] at this
            rw [SimpleGraph.Subgraph.verts_bot] at this
            exact ((Equiv.Set.empty _) this).elim
          rw [this]
          exact Equiv.Set.empty _


        rw [Fintype.cardEqZeroEquivEquivEmpty.invFun (compEmpty G)]
        rw [Fintype.cardEqZeroEquivEquivEmpty.invFun (compEmpty G')]
      else
        haveI : Inhabited ↑((⊤ : Subgraph G).deleteVerts u).verts := by
          simp only [Set.top_eq_univ] at h'
          push_neg at h'
          rw [← Set.ssubset_univ_iff ] at h'
          rw [@Subgraph.deleteVerts_verts]
          rw [@Subgraph.verts_top]
          apply Classical.inhabited_of_nonempty
          exact Set.Nonempty.to_subtype (Set.nonempty_of_ssubset h')
        have fsort (c : ConnectedComponent ((⊤ : Subgraph G').deleteVerts u).coe) (hc : c.isOdd) :
          ∃ c' : ConnectedComponent ((⊤ : Subgraph G).deleteVerts u).coe,
            c'.isOdd ∧ c'.supp ⊆ c.supp := by
            have b : ((⊤ : Subgraph G).deleteVerts u).coe ≤ ((⊤ : Subgraph G').deleteVerts u).coe := by
              intro x y hxy
              simp only [Set.top_eq_univ, Subgraph.induce_verts, Subgraph.verts_top,
                Subgraph.coe_adj, Subgraph.induce_adj, Set.mem_diff, Set.mem_univ, true_and,
                Subgraph.top_adj] at *
              exact ⟨ hxy.1 , ⟨ hxy.2.1 , h hxy.2.2 ⟩ ⟩


            rw [@ConnectedComponent.isOdd_iff] at hc
            rw [@Fintype.card_eq_nat_card] at hc
            have := Odd.pos <| (oddSubComponent' ((⊤ : Subgraph G).deleteVerts u).coe ((⊤ : Subgraph G').deleteVerts u).coe b c).mp hc
            rw [@Finite.card_pos_iff] at this
            obtain ⟨ v , hv ⟩ := Classical.inhabited_of_nonempty this

            use v.1
            constructor
            · rw [@ConnectedComponent.isOdd_iff]
              rw [@Fintype.card_eq_nat_card]
              exact hv
            · exact v.2

        have hb : ((⊤ : Subgraph G).deleteVerts u).coe ≤ ((⊤ : Subgraph G').deleteVerts u).coe := by
              intro x y hxy
              simp only [Set.top_eq_univ, Subgraph.induce_verts, Subgraph.verts_top,
                Subgraph.coe_adj, Subgraph.induce_adj, Set.mem_diff, Set.mem_univ, true_and,
                Subgraph.top_adj] at *
              exact ⟨ hxy.1 , ⟨ hxy.2.1 , h hxy.2.2 ⟩ ⟩
        let f : {(c : ConnectedComponent ((⊤ : Subgraph G').deleteVerts u).coe) | ConnectedComponent.isOdd c} →  {(c : ConnectedComponent ((⊤ : Subgraph G).deleteVerts u).coe) | ConnectedComponent.isOdd c} :=
          (fun (c : Set.Elem {(c : ConnectedComponent ((⊤ : Subgraph G').deleteVerts u).coe) | ConnectedComponent.isOdd c}) =>
          ⟨Exists.choose (fsort _ (by exact c.prop)), (by
            exact (fsort _ (by exact c.prop)).choose_spec.1) ⟩)
        have fInj : Function.Injective f := by
          intro x y hfxy
          simp_rw [f] at hfxy
          rw [Subtype.mk.injEq] at hfxy

          have h1 := (fsort x (by exact x.prop)).choose_spec
          have h2 := (fsort y (by exact y.prop)).choose_spec
          rw [hfxy] at h1
          rw [Subtype.mk.injEq]
          exact commonComponent hb h1.2 h2.2
        exact Fintype.card_le_of_injective f fInj

lemma ConnectedComponentSubsetVerts (H : Subgraph G) (c : ConnectedComponent H.coe) : (c.supp : Set V) ⊆ H.verts := by
  intro v hv
  exact Set.image_val_subset hv
