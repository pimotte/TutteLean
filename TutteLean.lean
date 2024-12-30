import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

import TutteLean.Defs
import TutteLean.Supp
import TutteLean.SingleEdge
import TutteLean.ConnectedComponent
import TutteLean.Clique
import TutteLean.Set
import TutteLean.Walk
import TutteLean.SymDiff
import TutteLean.PartNew
import TutteLean.Part2
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
    if hvOdd : Odd (Fintype.card V)
    then
      use ∅
      simp only [Set.ncard_empty, Subgraph.induce_verts, Subgraph.verts_top]
      have : Odd (Nat.card ↑((⊤ : Subgraph G).deleteVerts ∅).verts) := by
        simp only [Nat.card_eq_fintype_card,Finset.card_univ, Subgraph.deleteVerts_empty,
          Subgraph.verts_top, Fintype.card_congr (Equiv.Set.univ V), hvOdd]

      have ⟨c , hc⟩ := Classical.inhabited_of_nonempty
        (Finite.card_pos_iff.mp <| Odd.pos <|
        (odd_card_iff_odd_components ((⊤ : Subgraph G).deleteVerts ∅).coe).mp this)
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

      let G1 := Gmax ⊔ (edge x.val.val b.val.val)
      let G2 := Gmax ⊔ (edge a.val.val c)

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
        rw [singleEdge_le_iff (Subtype.coe_ne_coe.mpr <| Subtype.coe_ne_coe.mpr hxab.2.2.2)]
        exact hG1nxb

      have hG2 : Gmax < G2 := by

        apply union_gt_iff.mpr
        rw [singleEdge_le_iff hc.2]
        intro h
        exact hc.1 h

      obtain ⟨M1, hM1⟩ := hMaximal _ hG1
      obtain ⟨M2, hM2⟩ := hMaximal _ hG2

      have hGMaxadjax : Gmax.Adj ↑↑a ↑↑x := by
        have := hxab.1
        rw [@induce_eq_coe_induce_top] at this
        rw [@Subgraph.coe_adj] at this
        rw [@Subgraph.induce_adj] at this
        have := this.2.2.adj_sub
        exact Gsplit.coe_adj_sub _ _ (adj_symm Gsplit.coe this)

      have hGMaxadjab : Gmax.Adj ↑↑a ↑↑b := by
        have := hxab.2.1
        rw [@induce_eq_coe_induce_top] at this
        rw [@Subgraph.coe_adj] at this
        rw [@Subgraph.induce_adj] at this
        have := this.2.2.adj_sub
        exact Gsplit.coe_adj_sub _ _ (adj_symm Gsplit.coe this.symm)
      have hcnex : c ≠ x.val.val := by
          intro hxc
          apply hc.1
          rw [hxc]
          exact hGMaxadjax
      obtain ⟨Mcon, hMcon⟩ := tutte_part2 hGMaxadjax.symm hGMaxadjab hG1nxb hc.1 (by
        intro h
        apply hxab.2.2.2
        exact Subtype.val_injective (Subtype.val_injective h)) hcnex.symm hc.2 hbnec (hMaximal _ hG1) (hMaximal _ hG2)
      exact hMatchingFree Mcon hMcon
  }
