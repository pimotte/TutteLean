import TutteLean.Defs

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

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
            have := Odd.pos <| (ConnectedComponent.odd_card_supp_iff_odd_subcomponents ((⊤ : Subgraph G).deleteVerts u).coe b c).mp hc
            rw [@Finite.card_pos_iff] at this
            obtain ⟨ v , hv ⟩ := Classical.inhabited_of_nonempty this

            use v
            constructor
            · rw [@ConnectedComponent.isOdd_iff]
              rw [@Fintype.card_eq_nat_card]
              exact hv.2
            · exact hv.1

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


lemma ConnectedComponent.exists_vert (c : ConnectedComponent G) : ∃ v, G.connectedComponentMk v = c := c.exists_rep

lemma ConnectedComponent.exists_vert_mem_supp (c : ConnectedComponent G) : c.exists_vert.choose ∈ c.supp := c.exists_vert.choose_spec
