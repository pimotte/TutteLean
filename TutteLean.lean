import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

import TutteLean.Defs
import TutteLean.Supp
import TutteLean.SingleEdge
import TutteLean.MaxWithoutMatching
import TutteLean.ConnectedComponent
import TutteLean.Clique
import TutteLean.Set
import TutteLean.Walk
import TutteLean.SymDiff
import TutteLean.PartNew
-- import Mathlib.Algebra.BigOperators.Basic



namespace SimpleGraph
-- universe u
variable {V : Type*} {G : SimpleGraph V}













-- lemma ConnectedComponent.exists_vert_unique (c c' : ConnectedComponent G) (h : c.exists_vert.choose ∈ c'.supp) :  :




lemma sndOfNotNil_mem_support (p : G.Walk u v) (hnp : ¬ p.Nil) : p.getVert 1 ∈ p.support := by
  rw [SimpleGraph.Walk.mem_support_iff]
  right
  rw [← Walk.support_tail_of_not_nil _ hnp]
  exact Walk.start_mem_support p.tail


theorem tutte [Fintype V] [Inhabited V] [DecidableEq V] [DecidableRel G.Adj] :
    (∃ (M : Subgraph G) , M.IsPerfectMatching) ↔
      (∀ (u : Set V),
        cardOddComponents ((⊤ : G.Subgraph).deleteVerts u).coe ≤ u.ncard) := by
  constructor
  {
    rintro ⟨M, hM⟩ u
    let f : {c : ConnectedComponent ((⊤ : Subgraph G).deleteVerts u).coe | Odd (Nat.card c.supp)} → u :=
      fun c => ⟨(c.1.odd_matches_node_outside hM c.2).choose,(c.1.odd_matches_node_outside hM c.2).choose_spec.1⟩
    have := Finite.card_le_of_injective f (by
      intro x y hxy
      obtain ⟨v, hv⟩:= (x.1.odd_matches_node_outside hM x.2).choose_spec.2
      obtain ⟨w, hw⟩:= (y.1.odd_matches_node_outside hM y.2).choose_spec.2
      rw [Subtype.mk_eq_mk.mp hxy] at hv
      obtain ⟨v', hv'⟩ := (M.isPerfectMatching_iff).mp hM (f y)
      rw [(Subtype.val_injective (hv'.2 _ hw.1.symm ▸ hv'.2 _ hv.1.symm) : v = w)] at hv
      rw [Subtype.mk_eq_mk]
      exact ConnectedComponent.supp_eq_of_mem_supp hv.2 hw.2
      )
    simp only [Set.Nat.card_coe_set_eq] at this
    unfold cardOddComponents
    simp_rw [ConnectedComponent.isOdd_iff, Fintype.card_eq_nat_card, Set.Nat.card_coe_set_eq]

    exact this
  }
  {
    contrapose!
    intro h
    if hvOdd : Odd (Finset.univ : Finset V).card
    then
      use ∅
      simp only [Set.ncard_empty, Subgraph.induce_verts, Subgraph.verts_top]
      have : Odd (Nat.card ↑((⊤ : Subgraph G).deleteVerts ∅).verts) := by
        simp only [Nat.card_eq_fintype_card,Finset.card_univ, Nat.odd_iff_not_even, Subgraph.deleteVerts_empty,
          Subgraph.verts_top, Fintype.card_congr (Equiv.Set.univ V)] at *
        exact hvOdd

      have := Odd.pos <| (odd_card_iff_odd_components ((⊤ : Subgraph G).deleteVerts ∅).coe).mp this
      rw [@Finite.card_pos_iff] at this
      have ⟨ c , hc ⟩:= Classical.inhabited_of_nonempty this
      unfold cardOddComponents
      rw [Set.ncard_pos]
      use c
      exact hc
    else

      -- let Gmax := maximalWithoutMatching h
      obtain ⟨Gmax, hSubgraph, hMatchingFree, hMaximal⟩ := exists_maximal_isMatchingFree h

      suffices ∃ u, Set.ncard u < cardOddComponents ((⊤ : Subgraph Gmax).deleteVerts u).coe by
        · obtain ⟨u, hu ⟩ := this
          use u
          exact lt_of_lt_of_le hu (by
            haveI : DecidableRel Gmax.Adj := Classical.decRel _
            exact oddComponentsIncrease G Gmax hSubgraph u
            )

      let S : Set V := {v | ∀ w, v ≠ w → Gmax.Adj w v}

      let Gsplit := ((⊤ : Subgraph Gmax).deleteVerts S)


      by_contra! hc

      have h' := hc S
      unfold cardOddComponents at h'
      haveI : DecidableRel Gmax.Adj := Classical.decRel _
      haveI : Fintype ↑{ (c : ConnectedComponent ((⊤ : Subgraph Gmax).deleteVerts S).coe) | ConnectedComponent.isOdd c} := Fintype.ofFinite _
      rw [@Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card'] at h'
      rw [Set.toFinset_card, Set.toFinset_card] at h'
      let h'' := h'

      if h' : ∀ (K : ConnectedComponent Gsplit.coe), Gsplit.coe.IsClique K.supp
      then
        rw [← @Nat.even_iff_not_odd] at hvOdd
        rw [Fintype.card_eq_nat_card] at h''

        simp_rw [ConnectedComponent.isOdd_iff, Fintype.card_eq_nat_card, Set.Nat.card_coe_set_eq] at h''
        obtain ⟨M, hM⟩ := tutte_part' hvOdd h'' h'
        exact hMatchingFree M hM
    else
      push_neg at h'
      obtain ⟨K, hK⟩ := h'
      rw [isNotClique_iff] at hK
      obtain ⟨x, ⟨y, hxy⟩⟩ := hK


      obtain ⟨p , hp⟩ := SimpleGraph.Reachable.exists_path_of_dist (reachable_in_connected_component_induce K x y)


      obtain ⟨x, ⟨a, ⟨b, hxab⟩⟩⟩ := verts_of_walk p hp.2 (dist_gt_one_of_ne_and_nadj (Walk.reachable p) hxy.1 hxy.2)

      have ha : (a : V) ∉ S := by exact deleteVerts_verts_notmem_deleted _
      have hc : ∃ (c : V), ¬ Gmax.Adj a c ∧ (a : V) ≠ c := by

        have : ¬ ∀ (w : V), (a : V) ≠ w → Gmax.Adj (w : V) a := by exact ha
        push_neg at this
        obtain ⟨c, hc⟩ := this
        use c
        constructor
        · intro h
          exact hc.2 (adj_symm Gmax h)
        · exact hc.1
      obtain ⟨c, hc⟩ := hc

      have hbnec : b.val.val ≠ c := by
        intro h
        apply (h ▸ hc.1)
        have := hxab.2.1
        rw [@induce_eq_coe_induce_top] at this
        rw [@Subgraph.coe_adj] at this
        have := this.adj_sub
        exact Subgraph.coe_adj_sub Gsplit (↑a) (↑b) this

      let G1 := Gmax ⊔ (singleEdge <| Subtype.coe_ne_coe.mpr <| Subtype.coe_ne_coe.mpr hxab.2.2.2)
      let G2 := Gmax ⊔ (singleEdge hc.2)

      have hG1nxb : ¬ Gmax.Adj x.val.val b.val.val := by

        intro h
        apply hxab.2.2.1
        rw [@induce_eq_coe_induce_top]
        simp only [Subgraph.coe_adj, Subgraph.induce_verts, Subgraph.induce_adj, Subgraph.top_adj]
        refine ⟨Subtype.coe_prop x, Subtype.coe_prop b, ?_⟩
        rw [@Subgraph.deleteVerts_adj]
        simp only [Subgraph.verts_top, Set.mem_univ, deleteVerts_verts_notmem_deleted,
          not_false_eq_true, Subgraph.top_adj, h, and_self]

      have hG1 : Gmax < G1 := by

        apply union_gt_iff.mpr
        rw [@singleEdge_le_iff]
        exact hG1nxb

      have hG2 : Gmax < G2 := by

        apply union_gt_iff.mpr
        rw [@singleEdge_le_iff]
        intro h
        exact hc.1 h

      obtain ⟨M1, hM1⟩ := hMaximal _ hG1
      obtain ⟨M2, hM2⟩ := hMaximal _ hG2

      have hM1' : M1.Adj x b := by

        by_contra! hc
        obtain ⟨Mcon, hMcon⟩ := matching_union_left M1 hM1 (by
          ext v hv
          simp only [ne_eq, inf_adj, bot_adj, iff_false, not_and]
          intro h hc'
          unfold singleEdge at hc'
          unfold Subgraph.coeBig at h
          apply hc
          simp only at h hc' ⊢
          cases hc'
          next h1 =>
            exact h1.1.symm ▸ h1.2.symm ▸ h
          next h2 =>
            exact h2.1.symm ▸ h2.2.symm ▸ h.symm
          )
        exact hMatchingFree Mcon hMcon

      -- TODO: Dedup with above
      have hM2' : M2.Adj a c := by

        by_contra! hc
        obtain ⟨Mcon, hMcon⟩ := matching_union_left M2 hM2 (by
          ext v hv
          simp only [ne_eq, inf_adj, bot_adj, iff_false, not_and]
          intro h hc'
          unfold singleEdge at hc'
          unfold Subgraph.coeBig at h
          apply hc
          simp only at h hc' ⊢
          cases hc'
          next h1 =>
            exact h1.1.symm ▸ h1.2.symm ▸ h
          next h2 =>
            exact h2.1.symm ▸ h2.2.symm ▸ h.symm
          )
        exact hMatchingFree Mcon hMcon

      let G12 := Gmax ⊔ (singleEdge <| Subtype.coe_ne_coe.mpr <| Subtype.coe_ne_coe.mpr hxab.2.2.2) ⊔ (singleEdge hc.2)

      have hG1leG12 : G1 ≤ G12 := SemilatticeSup.le_sup_left G1 (singleEdge hc.right)
      have hG2leG12 : G2 ≤ G12 := by
        have : G12 = Gmax ⊔ (singleEdge hc.2) ⊔ (singleEdge <| Subtype.coe_ne_coe.mpr <| Subtype.coe_ne_coe.mpr hxab.2.2.2) := by
          exact
            sup_right_comm Gmax
              (singleEdge (Subtype.coe_ne_coe.mpr (Subtype.coe_ne_coe.mpr hxab.right.right.right)))
              (singleEdge hc.right)
        rw [this]
        exact
          SemilatticeSup.le_sup_left G2
            (singleEdge (Subtype.coe_ne_coe.mpr (Subtype.coe_ne_coe.mpr hxab.right.right.right)))


      let M1' := M1.map (Hom.ofLE hG1leG12)
      let M2' := M2.map (Hom.ofLE hG2leG12)

      have hM1'' := perfectMapLe hG1leG12 hM1
      have hM2'' := perfectMapLe hG2leG12 hM2

      have hM2'nxb : ¬M2'.Adj ↑↑x ↑↑b := by
        intro h
        rw [@Subgraph.map_adj] at h
        simp only [Hom.coe_ofLE, Relation.map_id_id] at h
        have := h.adj_sub
        rw [@sup_adj] at this
        cases this with
        | inl hl =>
          exact hG1nxb hl
        | inr hr =>
          simp only [singleEdge_Adj] at hr
          cases hr with
          | inl h1 =>
            exact hbnec h1.2.symm
          | inr h2 =>
            apply hxab.2.1.ne
            exact Subtype.val_injective (Subtype.val_injective h2.1)

      have hM2'nab : ¬M2'.Adj ↑↑a ↑↑b := by
        intro h
        obtain ⟨w, hw⟩ := hM2''.1 (hM2''.2 a.val.val)
        have hb := hw.2 _ h
        have hc := hw.2 _ (by simp only [Subgraph.map_adj, Hom.coe_ofLE, Relation.map_id_id]; exact hM2')
        rw [← hc] at hb
        exact hbnec hb

      let cycles := M1'.symDiff M2'
      have hCycles (v : V) : v ∈ (M1'.symDiff M2').verts := by
        unfold Subgraph.symDiff
        simp only [Set.mem_union]
        left
        exact hM1''.2 v
      let cycleComp := cycles.coe.connectedComponentMk ⟨c, hCycles c⟩
      let cycle := cycles.induce cycleComp.supp

      have supportImpMemSupp {u : V} (h : u ∈ cycle.support) : (u ∈ (cycleComp.supp : Set V)) := by
        have := SimpleGraph.Subgraph.support_subset_verts _ h
        rw [SimpleGraph.Subgraph.induce_verts] at this
        exact this

      have suppImpMemSupp {u : V} (h : u ∈ cycle.support) :  ⟨u, hCycles u⟩ ∈ cycleComp.supp := by
        have := SimpleGraph.Subgraph.support_subset_verts _ h
        rw [SimpleGraph.Subgraph.induce_verts] at this
        exact Set.mem_of_mem_image_val (supportImpMemSupp h)

      have hadjImp {u v : V} (h : cycle.Adj u v) : cycles.Adj u v := by
        rw [SimpleGraph.Subgraph.induce_adj] at h
        exact h.2.2

      have hadjImp' {u v : V} (h : cycles.Adj u v) (hu : u ∈ cycle.support) : cycle.Adj u v := by

        rw [SimpleGraph.Subgraph.induce_adj]
        exact ⟨ (supportImpMemSupp hu), by
          have memSup := mem_supp_of_adj _ _ _ (suppImpMemSupp hu) (SimpleGraph.Subgraph.Adj.coe h)
          exact Set.mem_image_val_of_mem (hCycles v) memSup
          , h⟩

      have hadjImpSupp {u v : V} (h : cycles.Adj u v) (hu : u ∈ cycle.support) : v ∈ cycle.support := by

        rw [@Subgraph.mem_support]
        use u
        exact (hadjImp' h hu).symm


      have cycleAlt : cycle.IsAlternating M2' := by
        intro u v w hvw huv huw
        exact Subgraph.symDiffPerfectMatchingsAlternating hM1'' hM2'' u v w hvw (hadjImp huv) (hadjImp huw)

      have cycleAlt' : cycle.IsAlternating M1' := by

        intro u v w hvw huv huw
        exact Subgraph.symDiffPerfectMatchingsAlternating hM2'' hM1'' u v w hvw
          (Subgraph.symDiff_adj_comm _ _ ▸ hadjImp huv) (Subgraph.symDiff_adj_comm _ _ ▸ hadjImp huw)




      have hM'2ca : M2'.Adj c ↑↑a := by
          rw [@Subgraph.map_adj]
          simp only [Hom.coe_ofLE, Relation.map_id_id]
          exact hM2'.symm

      have hnM'1ca :¬M1'.Adj c ↑↑a := by
        intro h
        rw [@Subgraph.map_adj] at h
        simp only [Hom.coe_ofLE, Relation.map_id_id] at h
        have := h.adj_sub
        rw [sup_adj] at this
        cases this with
        | inl hl => exact hc.1 hl.symm
        | inr hr =>
          rw [@singleEdge_Adj] at hr
          cases hr with
          | inl h1 =>
            apply hxab.2.1.ne
            exact Subtype.val_injective (Subtype.val_injective h1.2.symm)
          | inr h2 =>
            apply hxab.1.ne
            exact Subtype.val_injective (Subtype.val_injective h2.1)

      have hCyclesca : cycles.Adj c ↑↑a := by
        rw [@Subgraph.symDiff_adj]
        left
        exact ⟨hnM'1ca, hM'2ca⟩

      have cycleIsCycle : cycle.IsCycle := by
        constructor
        ·
          intro v hv
          have := Subgraph.symDiffPerfectMatchingsCard hM1'' hM2'' v
          simp only at this
          cases this with
          | inl hl =>
            exfalso
            have hvs := suppImpMemSupp hv
            have hcs : ⟨c, hCycles c⟩ ∈ cycleComp.supp := rfl
            rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hvs hcs
            rw [← hcs] at hvs
            have := SimpleGraph.ConnectedComponent.exact hvs
            rw [Set.eq_empty_iff_forall_not_mem ] at hl
            by_cases hvc : v = c
            · rw [hvc] at hl
              apply hl a.val.val
              rw [SimpleGraph.Subgraph.mem_neighborSet]
              left
              have : (Subgraph.map (Hom.ofLE hG2leG12) M2).Adj c a.val.val := by
                rw [@Subgraph.map_adj]
                simp only [Hom.coe_ofLE, Relation.map_id_id]
                exact hM2'.symm
              refine ⟨?_, this⟩
              intro h
              rw [Subgraph.map_adj] at h
              simp only [Hom.coe_ofLE, Relation.map_id_id] at h
              apply hc.1
              have := M1.adj_sub h
              rw [sup_adj] at this
              cases this with
              | inl h1 =>
                exact h1.symm
              | inr h2 =>
                unfold singleEdge at h2
                simp only at h2
                cases h2 with
                | inl h3 =>
                  exfalso
                  apply SimpleGraph.Adj.ne' hxab.2.1
                  exact Subtype.val_injective (Subtype.val_injective h3.2)
                | inr h4 =>
                  exfalso
                  apply SimpleGraph.Adj.ne' hxab.1
                  exact Subtype.val_injective (Subtype.val_injective h4.1.symm)
            ·
              obtain ⟨p, _⟩ := SimpleGraph.Reachable.exists_path_of_dist this
              push_neg at hvc
              have hnp : ¬ p.Nil:= p.not_nil_of_ne (by
                intro h
                apply hvc
                rwa [Subtype.mk.injEq] at h
                )
              have := hl (p.getVert 1)
              apply this
              rw [SimpleGraph.Subgraph.mem_neighborSet]

              exact SimpleGraph.Walk.adj_getVert_one hnp
          | inr hr =>
            rw [@Set.ncard_eq_two] at hr ⊢
            obtain ⟨x, y, hxy⟩ := hr
            use x
            use y
            refine ⟨hxy.1, ?_⟩
            unfold Subgraph.neighborSet
            unfold Subgraph.neighborSet at hxy
            rw [← hxy.2]
            ext w
            simp only [Set.mem_setOf_eq]
            constructor
            · intro hcvw
              exact hadjImp hcvw
            · intro hcvw
              exact hadjImp' hcvw hv
        ·
          exact ConnectedComponent.supp_induce_connected (by
            intro v
            exact hCycles v
            ) cycleComp (by
            have : ⟨c, hCycles c⟩ ∈ cycleComp.supp := by exact rfl
            exact Set.mem_image_val_of_mem (hCycles c) this)

      by_cases hxcycle : (x : V) ∈ cycle.support
      ·
        have hxsupp := suppImpMemSupp hxcycle
        simp only [ConnectedComponent.mem_supp_iff] at hxsupp
        rw [SimpleGraph.ConnectedComponent.eq] at hxsupp

        obtain ⟨p, hp⟩ := SimpleGraph.Reachable.exists_path_of_dist hxsupp
        have hnp : ¬ p.Nil := by
          refine Walk.not_nil_of_ne ?_
          intro h
          rw [@Subtype.mk_eq_mk] at h
          rw [← h] at hc
          apply hc.1
          have := hxab.1
          simp only [comap_adj, Function.Embedding.coe_subtype, Subgraph.coe_adj] at this
          exact Gsplit.coe_adj_sub (↑a) (↑x) (Gsplit.adj_symm this)


        have hM1'xb : M1'.Adj x.val.val b.val.val := by
          rw [@Subgraph.map_adj]
          simp only [Hom.coe_ofLE, Relation.map_id_id]
          exact hM1'


        have hCyclesxb : cycles.Adj x.val.val b.val.val := by
          rw [@Subgraph.symDiff_adj]
          right
          refine ⟨(by
            rw [@Subgraph.map_adj]
            simp only [Hom.coe_ofLE, Relation.map_id_id]
            exact hM1'
            ), ?_⟩
          exact hM2'nxb

        have hCyclexb : cycle.Adj x.val.val b.val.val := by
          rw [@Subgraph.induce_adj]
          refine ⟨supportImpMemSupp hxcycle, ?_, ?_⟩
          · apply supportImpMemSupp
            refine hadjImpSupp ?_ hxcycle
            exact hCyclesxb
          · exact hCyclesxb

        have hcmemcycsupport : c ∈ cycle.support := by
          rw [@Subgraph.mem_support]
          use a.val.val
          rw [SimpleGraph.Subgraph.induce_adj]
          refine ⟨Set.mem_image_val_of_mem (hCycles c) rfl, ?_, hCyclesca⟩
          refine Set.mem_image_val_of_mem (hCycles ↑↑a) ?h.ha'
          apply mem_supp_of_adj cycleComp ⟨c, hCycles c⟩ ⟨↑↑a, hCycles ↑↑a⟩ rfl
          exact hCyclesca


        rw [Subgraph.IsCycle_iff hcmemcycsupport] at cycleIsCycle
        obtain ⟨p, hp⟩ := cycleIsCycle
        have hxpsupport : x.val.val ∈ p.support := by
          have := hp.2 ▸ hxcycle
          rw [← @Walk.mem_verts_toSubgraph]
          exact p.toSubgraph.support_subset_verts this

        -- use hxcycle to split p into two appended paths, then rearrange from there
        obtain ⟨q, r, hqr⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hxpsupport


        suffices ∃ C : Subgraph G12, C.Adj a.val.val c ∧ ¬ C.Adj b x ∧ C.IsCycle ∧ C.IsAlternating M2' from (by

          -- copy pasted from below
          obtain ⟨C, ⟨hcadjac, hncadjbx, cic, cia⟩⟩ := this
          let Mcon := M2'.symDiff C
          have hMcon := alternatingCycleSymDiffMatch' hM2'' cic cia
          have hMconSpan : Mcon.IsSpanning := by
            intro v
            rw [Subgraph.symDiff_verts]
            left
            exact hM2''.2 v
          let Mrealcon := Mcon.comap (Hom.ofLE (le_of_lt <| lt_of_lt_of_le hG1 hG1leG12))
          apply hMatchingFree Mrealcon
          refine ⟨?_, by
            intro v
            rw [SimpleGraph.Subgraph.comap_verts]
            rw [@Hom.coe_ofLE]
            simp only [Set.preimage_id_eq, id_eq]
            exact hMconSpan v⟩
          intro v hv
          rw [SimpleGraph.Subgraph.comap_verts] at hv
          rw [@Hom.coe_ofLE] at hv
          simp only [Set.preimage_id_eq, id_eq] at hv
          obtain ⟨w, hw⟩ := hMcon (hMconSpan v)
          use w
          constructor
          · dsimp
            rw [SimpleGraph.Subgraph.comap_adj]
            refine ⟨?_, hw.1⟩
            have := hw.1
            unfold Subgraph.symDiff at this
            simp only [Subgraph.map_adj, Hom.coe_ofLE, Relation.map_id_id] at this
            cases this with
            | inl hl =>
              have := hl.2.adj_sub
              rw [sup_adj] at this
              rw [sup_adj] at this
              cases this with
              | inl hl' =>
                cases hl' with
                | inl h1 => exact h1
                | inr h2 =>
                  exfalso
                  rw [@singleEdge_Adj] at h2
                  apply hncadjbx
                  cases h2 with
                  | inl h1' => exact (h1'.1 ▸ h1'.2 ▸ hl.2.symm)
                  | inr h2' => exact (h2'.1 ▸ h2'.2 ▸ hl.2)
              | inr hr' =>
                exfalso
                rw [@singleEdge_Adj] at hr'
                apply hl.1
                cases hr' with
                | inl h1 => exact (h1.1 ▸ h1.2 ▸ hM2')
                | inr h2 => exact (h2.1 ▸ h2.2 ▸ hM2'.symm)
            | inr hr =>
              have := hr.1.adj_sub
              rw [sup_adj] at this
              cases this with
              | inl hl' => exact hl'
              | inr hr' =>
                rw [@singleEdge_Adj] at hr'
                exfalso
                apply hr.2
                cases hr' with
                | inl h1 => exact (h1.1 ▸ h1.2 ▸ hcadjac)
                | inr h2 => exact (h2.1 ▸ h2.2 ▸ hcadjac.symm)
          · intro y hy
            have := hw.2 y
            rw [@Subgraph.comap_adj] at hy
            exact this hy.2
        )
        have hG12adjca : G12.Adj c a := by

          rw [sup_adj, sup_adj]
          right
          simp only [singleEdge_Adj, and_self, or_true]

        have hG12adjba : G12.Adj b.val.val a := by

          rw [sup_adj, sup_adj]
          left ; left
          have := hxab.2.1
          rw [@induce_eq_coe_induce_top] at this
          simp only [Subgraph.coe_adj, Subgraph.induce_verts, Subgraph.induce_adj,
            ConnectedComponent.mem_supp_iff, Subgraph.top_adj] at this
          exact this.2.2.adj_sub.symm

        have hGsplitadjax : Gmax.Adj ↑↑a ↑↑x := by

          have := hxab.1
          rw [@induce_eq_coe_induce_top] at this
          rw [@Subgraph.coe_adj] at this
          rw [@Subgraph.induce_adj] at this
          have := this.2.2.adj_sub
          exact Gsplit.coe_adj_sub _ _ (adj_symm Gsplit.coe this)
        have hG12adjax : G12.Adj a x.val.val := by
          left ; left
          exact hGsplitadjax

        have hcnex : c ≠ x.val.val := by

          intro hxc
          apply hc.1
          rw [hxc]
          exact hGsplitadjax

        have haneb : a.val.val ≠ b.val.val := by

          intro h
          have := hxab.2.1
          rw [@induce_eq_coe_induce_top] at this
          rw [@Subgraph.coe_adj] at this
          apply this.ne
          exact Subtype.val_injective h

        have hscanesbx : s(c, ↑↑a) ≠ s(↑↑b, ↑↑x) := by
          intro h
          simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h
          cases h with
          | inl hl =>
            apply hbnec
            exact hl.1.symm
          | inr hr =>
            exact haneb hr.2

        have hM2'nax : ¬ M2'.Adj a.val.val x.val.val := by

          intro hM2'xa
          obtain ⟨x', hx'⟩ := hM2''.1 (hM2''.2 a.val.val)
          have hxx' := hx'.2 _ hM2'xa
          have hcc' := hx'.2 c (by simp only [Subgraph.map_adj, Hom.coe_ofLE, Relation.map_id_id, hM2'])
          exact hcnex (hxx' ▸ hcc')

        have hrn : ¬ r.Nil := SimpleGraph.Walk.not_nil_of_ne hcnex.symm
        have hqn : ¬ q.Nil := SimpleGraph.Walk.not_nil_of_ne hcnex
        have hqrn : ¬ q.reverse.Nil :=  SimpleGraph.Walk.not_nil_of_ne hcnex.symm

        have hrpath : r.IsPath := Walk.IsCycle.of_append_right hcnex (hqr ▸ hp.1)
        have hqpath : q.IsPath := Walk.IsCycle.of_append_left hcnex (hqr ▸ hp.1)
        have hralt : r.toSubgraph.IsAlternating M2' := (Walk.append_toSubgraph_alternating (hqr ▸ hp.2 ▸ cycleAlt)).2
        have hqalt : q.toSubgraph.IsAlternating M2' := (Walk.append_toSubgraph_alternating (hqr ▸ hp.2 ▸ cycleAlt)).1


        have hqlpl : q.length ≤ p.length := by

          rw [hqr]
          simp only [Walk.length_append, le_add_iff_nonneg_right, zero_le]

        have hnqxbImprxb (h : ¬ q.toSubgraph.Adj x.val.val b) : r.toSubgraph.Adj x.val.val b := by

          have := hCyclexb
          rw [← hp.2, hqr] at this
          rw [@Walk.toSubgraph_append] at this
          simp only [Subgraph.sup_adj] at this
          cases this with
          | inl hl => exfalso; exact h hl
          | inr hr => exact hr

        have hnqxbImprxb' (h : ¬ q.toSubgraph.Adj x.val.val b) : r.getVert 1 = b := by

          obtain ⟨w, hw'⟩ := hM1''.1 (hM1''.2 x)
          have hbw := hw'.2 _ (by simp only [Subgraph.map_adj, Hom.coe_ofLE, Relation.map_id_id]; exact hM1')
          have hrb : r.toSubgraph.Adj x b := by
            exact hnqxbImprxb h
          exact toSubgraph_adj_sndOfNotNil r hrpath hrb

        have hqxbImpqrsb (h : q.toSubgraph.Adj x.val.val b) : (q.reverse.getVert 1) = b := by

          refine toSubgraph_adj_sndOfNotNil q.reverse ?hpp (by rw [SimpleGraph.Walk.toSubgraph_reverse ]; exact h)
          rw [@Walk.isPath_reverse_iff]
          exact (hqr ▸ hp.1).of_append_left hcnex

        have hqadjqrs : q.toSubgraph.Adj (↑↑x) (q.reverse.getVert 1) := by
          rw [← @Walk.toSubgraph_reverse]
          exact Walk.toSubgraph_adj_sndOfNotNil q.reverse hqrn

        have hpadjqrs : p.toSubgraph.Adj (↑↑x) (q.reverse.getVert 1) := by
          rw [hqr]
          simp only [Walk.toSubgraph_append, Subgraph.sup_adj]
          left
          exact hqadjqrs
        by_cases hqca : q.toSubgraph.Adj c a
        · have hnars : a.val.val ∉ r.support := hp.1.decompose_mem_support_part hqr (q.toSubgraph_Adj_mem_support (q.toSubgraph.adj_symm hqca))
              hG12adjca.ne.symm hG12adjax.ne

          by_cases hqxb : q.toSubgraph.Adj x.val.val b
          ·
            let p' := Walk.cons (hG12adjca) (Walk.cons hG12adjax r)
            have hnbrs : b.val.val ∉ r.support := hp.1.decompose_mem_support_part hqr (q.toSubgraph_Adj_mem_support (q.toSubgraph.adj_symm hqxb)) hbnec
              (by intro h; exact hqxb.ne h.symm)

            have hM2'Adjxr2 :  M2'.Adj (↑↑x) (r.getVert 1) := by

              have hr := Walk.toSubgraph_adj_sndOfNotNil r hrn
              have hp' : p.toSubgraph.Adj x.val.val (r.getVert 1) := by
                rw [hqr]
                simp only [Walk.toSubgraph_append, Subgraph.sup_adj]
                exact Or.inr hr
              rw [hp.2] at hp'
              have := hadjImp hp'
              rw [@Subgraph.symDiff_adj] at this
              cases this with
              | inl hl =>
                exact hl.2
              | inr hr' =>
                exfalso
                obtain ⟨w, hw⟩ := (hM1''.1 (hM1''.2 x.val.val))
                have hrw := hw.2 _ hr'.1
                have hbw := hw.2 b.val.val (by
                  simp only [Subgraph.map_adj, Hom.coe_ofLE, Relation.map_id_id]
                  exact hM1'
                  )
                apply hnbrs
                rw [hbw, ← hrw]
                exact r.toSubgraph_Adj_mem_support hr.symm

            have hconsrPath : (Walk.cons hG12adjax r).IsPath := by

              simp only [Walk.cons_isPath_iff]
              exact ⟨(hqr ▸ hp.1).of_append_right hcnex, hnars⟩

            have hp'c : p'.IsCycle := by

              rw [@Walk.cons_isCycle_iff]
              refine ⟨hconsrPath, ?_⟩
              intro h
              simp only [Walk.edges_cons, List.mem_cons, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
                Prod.swap_prod_mk, and_true] at h
              cases h with
              | inl hl =>
                cases hl with
                | inl h1 => exact hG12adjca.ne h1.1
                | inr h2 => exact hcnex h2
              | inr hr =>
                apply hnars
                exact Walk.snd_mem_support_of_mem_edges r hr

            have hcss : c ∈ p'.toSubgraph.support := hp'c.mem_endpoint

            have hsubcyc : p'.toSubgraph.IsCycle := (p'.toSubgraph.IsCycle_iff hcss).mpr ⟨p', ⟨hp'c, rfl⟩⟩

            have hp'tsac : p'.toSubgraph.Adj (↑↑a) c := ((Walk.cons hG12adjax r).cons_to_Subgraph_first_adj hG12adjca).symm
            have hp'nbx : ¬p'.toSubgraph.Adj ↑↑b ↑↑x := by

              intro h
              have : b.val.val ∉ r.support := hp.1.decompose_mem_support_part hqr
                   (Walk.toSubgraph_Adj_mem_support q (Subgraph.adj_symm q.toSubgraph hqxb))
                  hbnec h.ne
              apply this
              rw [@Walk.toSubgraph.eq_def] at h
              simp only [Walk.toSubgraph, Subgraph.sup_adj, subgraphOfAdj_adj, Sym2.eq,
                Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, and_true] at h
              cases h with
              | inl hl =>
                exfalso
                cases hl with
                | inl h1 =>
                  exact hGsplitadjax.ne h1.2
                | inr h2 =>
                  exact hcnex h2.1
              | inr hr =>
                cases hr with
                | inl h1 =>
                  exfalso
                  cases h1 with
                  | inl hl' =>
                    exact haneb hl'
                  | inr hr' => exact hG12adjax.ne hr'.1
                | inr h2 => exact Walk.toSubgraph_Adj_mem_support r h2

            have hp'alt : p'.toSubgraph.IsAlternating M2' := by
              refine hp'c.IsAlternating_cons (Walk.not_nil_cons) ?halt ?ha ?hb
              · refine hconsrPath.IsAlternating_cons hrn hralt ?ha'
                simp only [hM2'nax, false_iff, not_not]
                exact hM2'Adjxr2
              · simp only [hM'2ca.symm, Walk.getVert_cons_succ, Walk.getVert_zero, true_iff]
                intro hM2'a
                obtain ⟨w, hw'⟩ := hM2''.1 (hM2''.2 a)
                have h1 := hw'.2 x hM2'a
                have h2 := hw'.2 _ (hM'2ca.symm)
                exact False.elim (hM2'nax hM2'a)
              · simp only [hM'2ca, true_iff]
                intro h
                unfold Walk.lastButOneOfNotNil at h
                rw [← @Walk.getVert_reverse] at h
                simp only [Walk.reverse_cons] at h
                obtain ⟨w, hw'⟩ := hM2''.1 (hM2''.2 c)
                have h1 := hw'.2 _ h
                have h2 := hw'.2 _ (by simp only [Subgraph.map_adj, Hom.coe_ofLE,
                  Relation.map_id_id] ; exact hM2'.symm)
                have hrn' : ¬ r.reverse.Nil := by

                  rw [@reverse_Nil]
                  exact hrn

                rw [Walk.append_sndOfNotNil (by

                  rw [Walk.append_notNil]
                  push_neg
                  intro hrnn
                  exfalso
                  exact hrn' hrnn
                  ) hrn'] at h1
                have : r.reverse.getVert 1 ∈ r.support := by
                  refine (mem_reverse_support r (r.reverse.getVert 1)).mpr ?_
                  exact sndOfNotNil_mem_support r.reverse hrn'
                rw [h1, ← h2] at this
                exact hnars this

            use p'.toSubgraph

          ·
            have hG12ars : G12.Adj a (r.getVert 1) := by

              rw [hnqxbImprxb' hqxb]
              rw [sup_adj]
              simp only [sup_adj, singleEdge_Adj, and_true, true_and]
              left ; left
              have := hxab.2.1
              simp only [comap_adj, Function.Embedding.coe_subtype, Subgraph.coe_adj] at this
              exact this.adj_sub


            let p' := Walk.cons (hG12adjca) (Walk.cons hG12ars r.tail)
            have hconsrPath : (Walk.cons hG12ars r.tail).IsPath := by

              simp only [Walk.cons_isPath_iff]
              exact ⟨hrpath.tail hrn, by
                intro h
                apply hnars
                exact Walk.tail_support_imp_support hrn h⟩

            have hp'c : p'.IsCycle := by

              rw [@Walk.cons_isCycle_iff]
              refine ⟨hconsrPath, ?_⟩
              intro h
              simp only [Walk.edges_cons, List.mem_cons, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
                Prod.swap_prod_mk, and_true] at h
              cases h with
              | inl hl =>
                cases hl with
                | inl hl' =>
                  exact hqca.ne hl'.1
                | inr hr' =>
                  have := hnqxbImprxb' hqxb
                  apply hbnec
                  rw [hr', ← this]
              | inr hr =>

                rw [@Walk.cons_isPath_iff] at hconsrPath
                apply hconsrPath.2
                exact r.tail.snd_mem_support_of_mem_edges hr
            have hcss : c ∈ p'.toSubgraph.support := by
              exact Walk.IsCycle.mem_endpoint hp'c
            have hsubcyc : p'.toSubgraph.IsCycle := (p'.toSubgraph.IsCycle_iff hcss).mpr ⟨p', ⟨hp'c, rfl⟩⟩

            have hcac : p'.toSubgraph.Adj a.val.val c := ((Walk.cons hG12ars r.tail).cons_to_Subgraph_first_adj hG12adjca ).symm

            have hcnbx : ¬ p'.toSubgraph.Adj b.val.val x.val.val := by

              intro hp'
              rw [@Walk.toSubgraph_cons_adj_iff] at hp'
              cases hp' with
              | inl hl => exact hscanesbx hl
              | inr hr =>
                rw [@Walk.toSubgraph_cons_adj_iff] at hr
                cases hr with
                | inl hl' =>
                  rw [hnqxbImprxb' hqxb] at hl'
                  simp at hl'
                  cases hl' with
                  | inl h1 =>
                    exact haneb h1.1
                  | inr h2 =>
                    exact hG12adjax.ne h2
                | inr hr' =>
                  exact hrpath.start_non_mem_support_tail hrn (r.tail.toSubgraph_Adj_mem_support (hr'.symm))
            have hrrn : ¬ r.tail.Nil := by

              apply SimpleGraph.Walk.not_nil_of_ne
              rw [hnqxbImprxb' hqxb]
              exact hbnec

            have hpAdjbrtt : p.toSubgraph.Adj b.val.val (r.tail.getVert 1) := by

              rw [hqr]
              refine Subgraph.adj_symm (q.append r).toSubgraph (Walk.append_subgraph_adj' ?_)
              rw [← hnqxbImprxb' hqxb]
              rw [@Subgraph.adj_comm]
              have h1 : r.tail.toSubgraph.Adj (r.getVert 1) (r.tail.getVert 1) := by
                exact Walk.toSubgraph_adj_sndOfNotNil r.tail hrrn
              have h2 : r.tail.toSubgraph ≤ r.toSubgraph := by
                exact Walk.tail_toSubgraph hrn
              exact h2.2 h1

            have hp'alt : p'.toSubgraph.IsAlternating M2' := by

              refine hp'c.IsAlternating_cons (Walk.not_nil_cons) ?_ ?_ ?_
              · refine hconsrPath.IsAlternating_cons hrrn ?_ ?_
                · exact r.tail.toSubgraph.IsAlternatingMono (by
                  exact Walk.tail_toSubgraph hrn) hralt
                · constructor
                  · intro h
                    exfalso
                    rw [hnqxbImprxb' hqxb] at h
                    exact hM2'nab h
                  · intro h
                    exfalso

                    rw [hp.2] at hpAdjbrtt
                    have := hadjImp hpAdjbrtt
                    rw [← hnqxbImprxb' hqxb] at this
                    rw [@Subgraph.symDiff_adj] at this
                    cases this with
                    | inl hl =>
                      exact (h (hl.2)).elim
                    | inr hr =>
                      rw [← hnqxbImprxb' hqxb] at hM1'
                      have := hM1'
                      have : M1'.Adj (r.getVert 1) x.val.val := by
                        rw [@Subgraph.map_adj]
                        simp only [Hom.coe_ofLE, Relation.map_id_id]
                        exact this.symm
                      obtain ⟨w, hw⟩ := hM1''.1 (hM1''.2 (r.getVert 1))
                      have h1 := hw.2 _ hr.1
                      have h2 := hw.2 _ this
                      rw [← h2] at h1
                      apply hrpath.start_ne_snd_snd hrn hrrn
                      exact h1.symm
              · simp only [hM'2ca.symm, Walk.getVert_cons_succ, Walk.getVert_zero, true_iff]
                intro h
                rw [hnqxbImprxb' hqxb] at h
                obtain ⟨w, hw⟩ := hM2''.1 (hM2''.2 a.val.val)

                simp only [Relation.map_id_id] at hw

                have h1 := hw.2 _ h
                have h2 := hw.2 _ hM'2ca.symm
                rw [← h2] at h1
                exact hbnec h1
              · simp only [hM'2ca, true_iff]
                intro h
                obtain ⟨w, hw⟩ := hM2''.1 (hM2''.2 c)

                simp only [Relation.map_id_id] at hw
                have h1 := hw.2 _ h
                have h2 := hw.2 _ hM'2ca
                rw [← h2] at h1
                apply (Walk.IsPath.start_ne_lastButOne hrn hrrn hG12ars hconsrPath)
                exact h1

            use p'.toSubgraph

        ·
          have hnars : a.val.val ∉ q.reverse.support := by

            have : p.reverse = r.reverse.append q.reverse := by
              rw [hqr]
              exact Walk.reverse_append q r
            exact Walk.IsCycle.decompose_mem_support_part'' (hp.1.reverse) this (
              (Walk.isPath_reverse_iff r).mpr hrpath) (by
                rw [@Walk.toSubgraph_reverse]
                have := hadjImp' hCyclesca.symm (
                    (hadjImpSupp hCyclesca hcmemcycsupport))
                rw [← hp.2] at this
                exact this.symm
                ) (by rwa [@Walk.toSubgraph_reverse]) (hcnex) hG12adjca.ne.symm hG12adjax.ne



          by_cases hqxb : q.toSubgraph.Adj x.val.val b
          ·
            have G12Adjaqrs : G12.Adj a (q.reverse.getVert 1) := by

              rw [hqxbImpqrsb hqxb]
              exact hG12adjba.symm
            let p' := Walk.cons hG12adjca (Walk.cons G12Adjaqrs q.reverse.tail)
            have hrtPath : q.reverse.tail.IsPath := hqpath.reverse.tail (q.not_nil_reverse.mpr hqn)

            have hconsrPath : (Walk.cons G12Adjaqrs q.reverse.tail).IsPath := by

              simp only [Walk.cons_isPath_iff]
              refine ⟨hrtPath, ?_⟩
              intro h
              apply hnars
              rw [← SimpleGraph.Walk.cons_support_tail _ hqrn]
              exact List.mem_cons_of_mem (↑↑x) h

            have hrnt : ¬ q.reverse.tail.Nil := by

              apply SimpleGraph.Walk.not_nil_of_ne
              rw [hqxbImpqrsb hqxb]
              exact hbnec

            have hp'c : p'.IsCycle := by

              rw [@Walk.cons_isCycle_iff]
              refine ⟨hconsrPath, ?_⟩
              intro h
              simp only [Walk.edges_cons, List.mem_cons, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
                Prod.swap_prod_mk, and_true] at h
              cases h with
              | inl hl =>
                cases hl with
                | inl hl' =>
                  exact (hG12adjca.ne hl'.1).elim
                | inr hr' =>
                  rw [hqxbImpqrsb hqxb] at hr'
                  exact hbnec hr'.symm
              | inr hr =>
                rw [@Walk.cons_isPath_iff] at hconsrPath
                apply hconsrPath.2
                exact q.reverse.tail.snd_mem_support_of_mem_edges hr

            have hcss : c ∈ p'.toSubgraph.support := by
              exact Walk.IsCycle.mem_endpoint hp'c

            have hsubcyc : p'.toSubgraph.IsCycle := (p'.toSubgraph.IsCycle_iff hcss).mpr ⟨p', ⟨hp'c, rfl⟩⟩

            have hp'ac : p'.toSubgraph.Adj (↑↑a) c := ((Walk.cons G12Adjaqrs q.reverse.tail).cons_to_Subgraph_first_adj hG12adjca).symm


            have hp'xb : ¬ p'.toSubgraph.Adj b x.val.val := by

              intro hp'
              rw [@Walk.toSubgraph_cons_adj_iff] at hp'

              cases hp' with
              | inl hl => exact hscanesbx hl
              | inr hr =>
                rw [@Walk.toSubgraph_cons_adj_iff] at hr
                cases hr with
                | inl hl' =>
                  rw [hqxbImpqrsb hqxb] at hl'
                  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, and_true] at hl'
                  cases hl' with
                  | inl h1 => exact hqxb.ne h1.2.symm
                  | inr h2 =>
                    exact hG12adjax.ne h2
                | inr hr' =>
                  have : s(x.val.val, b.val.val) ∉ q.reverse.tail.edges := hqpath.reverse.edge_start_not_mem_tail_edges hqrn
                  rw [← @Subgraph.mem_edgeSet] at hr'
                  rw [@Walk.mem_edges_toSubgraph] at hr'
                  rw [@Sym2.eq_swap] at hr'
                  exact this hr'

            have hpAdjbqts : p.toSubgraph.Adj b.val.val (q.reverse.tail.getVert 1) := by
              rw [hqr]
              refine Subgraph.adj_symm (q.append r).toSubgraph (Walk.append_subgraph_adj ?_)
              rw [← hqxbImpqrsb hqxb]
              rw [@Subgraph.adj_comm]
              have h1 := Walk.toSubgraph_adj_sndOfNotNil q.reverse.tail hrnt
              have h2 : q.reverse.tail.toSubgraph ≤ q.toSubgraph := Walk.reverse_tail_toSubgraph hqrn
              exact h2.2 h1

            have pc'alt : p'.toSubgraph.IsAlternating M2' := by
              refine hp'c.IsAlternating_cons (Walk.not_nil_cons) ?_ ?_ ?_
              · refine hconsrPath.IsAlternating_cons hrnt ?_ ?_
                · refine q.reverse.tail.toSubgraph.IsAlternatingMono ?_ hqalt
                  exact Walk.reverse_tail_toSubgraph hqrn
                · constructor
                  · intro h h'
                    rw [hqxbImpqrsb hqxb] at h

                    exact hM2'nab h
                  · intro h

                    exfalso
                    have := hpAdjbqts
                    rw [hp.2] at hpAdjbqts
                    have := hadjImp hpAdjbqts
                    rw [← hqxbImpqrsb hqxb] at this
                    rw [@Subgraph.symDiff_adj] at this
                    cases this with
                    | inl hl =>
                      exact h hl.2
                    | inr hr =>
                      rw [← hqxbImpqrsb hqxb] at hM1'
                      have := hM1'
                      have : M1'.Adj (q.reverse.getVert 1)  (↑↑x) := by
                        rw [@Subgraph.map_adj]
                        simp only [Hom.coe_ofLE, Relation.map_id_id]
                        exact this.symm
                      obtain ⟨w, hw⟩ := hM1''.1 (hM1''.2 (q.reverse.getVert 1))
                      have h1 := hw.2 _ hr.1
                      have h2 := hw.2 _ this
                      rw [← h2] at h1
                      exact hqpath.reverse.start_ne_snd_snd hqrn
                         hrnt h1.symm
              · simp only [hM'2ca.symm, Walk.getVert_cons_succ, Walk.getVert_zero, true_iff]
                intro h
                rw [hqxbImpqrsb hqxb] at h
                exact hM2'nab h
              · simp only [hM'2ca, true_iff]
                intro h
                obtain ⟨w, hw⟩ := hM2''.1 (hM2''.2 c)

                simp only [Relation.map_id_id] at hw
                have h1 := hw.2 _ h
                have h2 := hw.2 _ hM'2ca
                rw [← h2] at h1
                exact Walk.IsPath.start_ne_lastButOne hqrn hrnt G12Adjaqrs hconsrPath h1

            use p'.toSubgraph

          ·
            let p' := Walk.cons hG12adjca (Walk.cons hG12adjax q.reverse)

            have hconsrPath : (Walk.cons hG12adjax q.reverse).IsPath := by
              simp only [Walk.cons_isPath_iff]
              exact ⟨hqpath.reverse, hnars⟩

            have hp'c : p'.IsCycle := by
              rw [@Walk.cons_isCycle_iff]
              refine ⟨hconsrPath, ?_⟩
              intro h
              simp only [Walk.edges_cons, Walk.edges_reverse, List.mem_cons, Sym2.eq, Sym2.rel_iff',
                Prod.mk.injEq, Prod.swap_prod_mk, and_true, List.mem_reverse] at h
              cases h with
              | inl hl =>
                cases hl with
                | inl hl' =>
                  exact hG12adjca.ne hl'.1
                | inr hr' =>
                  exact hcnex hr'
              | inr hr =>
                apply hqca
                rw [← @Subgraph.mem_edgeSet]
                rw [@Walk.mem_edges_toSubgraph]
                exact hr

            have hcss : c ∈ p'.toSubgraph.support := by
              exact Walk.IsCycle.mem_endpoint hp'c

            have hsubcyc : p'.toSubgraph.IsCycle := (p'.toSubgraph.IsCycle_iff hcss).mpr ⟨p', ⟨hp'c, rfl⟩⟩

            have hp'ac : p'.toSubgraph.Adj (↑↑a) c := ((Walk.cons hG12adjax q.reverse).cons_to_Subgraph_first_adj hG12adjca).symm

            have hp'xb : ¬ p'.toSubgraph.Adj b x.val.val := by
              intro hp'
              rw [@Walk.toSubgraph_cons_adj_iff] at hp'
              cases hp' with
              | inl hl =>
                exact hscanesbx hl
              | inr hr =>
                rw [@Walk.toSubgraph_cons_adj_iff] at hr
                cases hr with
                | inl hl' =>
                  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, and_true, Prod.swap_prod_mk] at hl'
                  cases hl' with
                  | inl h1 =>
                    exact haneb h1
                  | inr h2 =>
                    exact hG12adjax.ne h2.1
                | inr hr' =>
                  rw [@Walk.toSubgraph_reverse] at hr'
                  exact hqxb hr'.symm

            have pc'alt : p'.toSubgraph.IsAlternating M2' := by
              refine hp'c.IsAlternating_cons (Walk.not_nil_cons) ?_ ?_ ?_
              · refine hconsrPath.IsAlternating_cons hqrn ?_ ?_
                · rw [@Walk.toSubgraph_reverse]
                  exact hqalt
                · simp only [hM2'nax, false_iff, not_not]
                  have := hpadjqrs
                  rw [hp.2] at this
                  have := hadjImp this
                  rw [@Subgraph.symDiff_adj] at this
                  cases this with
                  | inl hl =>
                    exact hl.2
                  | inr hr =>
                    exfalso
                    obtain ⟨w, hw'⟩ := hM1''.1 (hM1''.2 x)
                    have h1 := hw'.2 _ hr.1
                    have h2 := hw'.2 _ hM1'xb
                    rw [← h2] at h1
                    have hqxb := hqadjqrs
                    rw [h1] at hqxb
                    apply hp'xb
                    unfold Walk.toSubgraph
                    rw [Subgraph.sup_adj]
                    right
                    unfold Walk.toSubgraph
                    rw [Subgraph.sup_adj]
                    right
                    rw [@Walk.toSubgraph_reverse]
                    exact hqxb.symm
              · simp only [hM'2ca.symm, Walk.getVert_cons_succ, Walk.getVert_zero, true_iff]
                exact hM2'nax
              · simp only [hM'2ca, true_iff]
                intro h
                obtain ⟨w, hw⟩ := hM2''.1 (hM2''.2 c)
                simp only [Relation.map_id_id] at hw
                have h1 := hw.2 _ h
                have h2 := hw.2 _ hM'2ca
                rw [← h2] at h1
                exact Walk.IsPath.start_ne_lastButOne' hqrn hG12adjax hconsrPath h1

            use p'.toSubgraph

      ·
        let Mcon := M2'.symDiff cycle
        have hMcon := alternatingCycleSymDiffMatch' hM2'' cycleIsCycle cycleAlt
        have hMconSpan : Mcon.IsSpanning := by
          intro v
          rw [Subgraph.symDiff_verts]
          left
          exact hM2''.2 v
        let Mrealcon := Mcon.comap (Hom.ofLE (le_of_lt <| lt_of_lt_of_le hG1 hG1leG12))
        apply hMatchingFree Mrealcon
        refine ⟨?_, by
          intro v
          rw [SimpleGraph.Subgraph.comap_verts]
          rw [@Hom.coe_ofLE]
          simp only [Set.preimage_id_eq, id_eq]
          exact hMconSpan v⟩
        intro v hv
        rw [SimpleGraph.Subgraph.comap_verts] at hv
        rw [@Hom.coe_ofLE] at hv
        simp only [Set.preimage_id_eq, id_eq] at hv
        obtain ⟨w, hw⟩ := hMcon (hMconSpan v)
        use w
        constructor
        · dsimp
          rw [SimpleGraph.Subgraph.comap_adj]
          refine ⟨?_, hw.1⟩
          have := hw.1
          unfold Subgraph.symDiff at this
          simp only [Subgraph.map_adj, Hom.coe_ofLE, Relation.map_id_id] at this
          cases this with
          | inl hl =>
            have := cycle.adj_sub hl.2
            rw [sup_adj] at this
            rw [sup_adj] at this
            cases this with
            | inl hl' =>
              cases hl' with
              | inl h1 => exact h1
              | inr h2 =>
                simp only [singleEdge_Adj] at h2
                cases h2 with
                | inl h1' =>
                  rw [← h1'.1] at hl
                  exfalso
                  apply hxcycle
                  exact (Subgraph.mem_support _).mpr (⟨w, hl.2⟩)
                | inr h2' =>
                  rw [← h2'.1] at hl
                  exfalso
                  apply hxcycle
                  exact (Subgraph.mem_support _).mpr (⟨v, hl.2.symm⟩)
            | inr hr' =>
              simp only [singleEdge_Adj] at hr'
              cases hr' with
              | inl h1 =>
                rw [← h1.1, ← h1.2] at hl
                exfalso
                exact hl.1 hM2'
              | inr h2 =>
                rw [← h2.1, ← h2.2] at hl
                exfalso
                exact hl.1 hM2'.symm
          | inr hr =>
            have := M2.adj_sub hr.1
            rw [sup_adj] at this
            cases this with
            | inl hl => exact hl
            | inr hr' =>
              simp only [singleEdge_Adj] at hr'
              exfalso
              have hac : M2.Adj a.val.val c ∧ ¬cycle.Adj a.val.val c := by
                cases hr' with
                | inl h1 => exact h1.1 ▸ h1.2 ▸ hr

                | inr h2 =>
                  exact ⟨h2.1 ▸
                  h2.2 ▸ hr.1.symm, by
                    intro h
                    apply hr.2
                    rw [← h2.1, ← h2.2]
                    exact h.symm
                    ⟩
              apply hac.2
              rw [SimpleGraph.Subgraph.induce_adj]
              have hcca : cycles.Adj c ↑↑a := hCyclesca
              have : a.val.val ∈ (cycleComp.supp : Set V) := by
                -- sorr
                simp only [Set.mem_image]
                use ⟨a.val, hCycles a.val⟩
                simp only [and_true]
                apply mem_supp_of_adj _ _ _ ((cycleComp.mem_supp_iff ⟨c, hCycles c⟩).mpr rfl )
                simp only [Subgraph.coe_adj]
                exact hcca
              refine ⟨this, ?_⟩
              refine ⟨?_, hcca.symm⟩
              rw [@Set.mem_image]
              use ⟨c, hCycles c⟩
              exact ⟨rfl, rfl⟩
        · intro y hy
          refine hw.2 y ?_
          simp only [Subgraph.symDiff_adj, Subgraph.map_adj, Hom.coe_ofLE, Relation.map_id_id]
          rw [SimpleGraph.Subgraph.comap_adj] at hy
          have := hy.2
          simp only [Hom.coe_ofLE, id_eq] at this
          rw [Subgraph.symDiff_adj] at this
          cases this with
          | inl hl =>
            left
            refine ⟨?_, hl.2⟩
            intro hvy
            apply hl.1
            rw [Subgraph.map_adj]
            simp only [Hom.coe_ofLE, Relation.map_id_id, hvy]
          | inr hr =>
            right
            refine ⟨?_, hr.2⟩
            rw [Subgraph.map_adj] at hr
            simp only [Hom.coe_ofLE, Relation.map_id_id] at hr
            exact hr.1
  }
