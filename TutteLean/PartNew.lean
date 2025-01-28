import TutteLean.Defs
import TutteLean.Clique
import TutteLean.ConnectedComponent

import Mathlib.Combinatorics.SimpleGraph.UniversalVerts

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

-- In #20024/#21097 (refactored)
def oddVerts (G : SimpleGraph V) : Set V := Subtype.val '' ((fun c ↦ c.exists_rep.choose) '' {(c : ConnectedComponent G.deleteUniversalVerts.coe) | Odd (c.supp.ncard)})

-- In #20024/#21097 (refactored)
lemma rep_choose_inj : Function.Injective (fun (c : G.ConnectedComponent) ↦ c.exists_rep.choose) := by
  intro c d hcd
  dsimp at hcd
  rw [← (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp (ConnectedComponent.exists_vert_mem_supp c)]
  rw [← (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp (ConnectedComponent.exists_vert_mem_supp d)]
  exact congrArg G.connectedComponentMk hcd

-- In represents PR/easy
--lemma disjoint_image_val_universalVerts {s : Set (G.deleteUniversalVerts.verts)} :
--   Disjoint (Subtype.val '' s) G.universalVerts := by
--  exact Subgraph.disjoint_deleteVerts_verts_image_val.symm

lemma oddVerts_core_disjoint : Disjoint G.oddVerts G.universalVerts := by
  rw [@Set.disjoint_left]
  intro v hv
  rw [oddVerts, Set.mem_image] at hv
  simp_rw [Set.mem_image] at hv
  obtain ⟨w, hw⟩ := hv
  obtain ⟨c, hc⟩ := hw.1
  rw [← hw.2, ← hc.2]
  exact deleteVerts_verts_notmem_deleted _

lemma subgraph_coe (H : Subgraph G) {x y : H.verts} (h : H.coe.Adj x y) : G.Adj x.val y.val := h.adj_sub

lemma isClique_lifts {K : G.deleteUniversalVerts.coe.ConnectedComponent}
    (h : G.deleteUniversalVerts.coe.IsClique K.supp) : G.IsClique (Subtype.val '' K.supp) := by
  intro x hx y hy hxy
  rw [Set.mem_image] at hx hy
  obtain ⟨x', hx'⟩ := hx
  obtain ⟨y', hy'⟩ := hy
  rw [← hx'.2, ← hy'.2] at hxy ⊢
  have := h hx'.1 hy'.1 (fun a => hxy (congrArg Subtype.val a))
  exact subgraph_coe G.deleteUniversalVerts this

lemma disjoint_supp_universalVerts {K : G.deleteUniversalVerts.coe.ConnectedComponent} :
    Disjoint (Subtype.val '' K.supp) G.universalVerts := by
  rw [Set.disjoint_left]
  intro v hv
  simp only [Set.mem_image, ConnectedComponent.mem_supp_iff, Subtype.exists,
    deleteUniversalVerts_verts, Set.mem_diff, Set.mem_univ, true_and, exists_and_right,
    exists_eq_right] at hv
  exact hv.choose

lemma component_rep (c : G.ConnectedComponent): G.connectedComponentMk c.exists_rep.choose = c := by
  exact c.exists_rep.choose_spec

--lemma disjoint_even_supp_oddVerts {K : G.deleteUniversalVerts.coe.ConnectedComponent}
--    {s : Set (G.deleteUniversalVerts.verts)}
--    (hrep : s.Represents {(c : ConnectedComponent G.deleteUniversalVerts.coe) | Odd (c.supp.ncard)})
--    (h : Even K.supp.ncard) : Disjoint s K.supp := by
--  exact ConnectedComponent.disjoint_supp_of_represents hrep (Nat.not_odd_iff_even.mpr h)

-- In represents PR/easy
lemma disjoint_even_supp_oddVerts {K : G.deleteUniversalVerts.coe.ConnectedComponent}
    (h : Even (Subtype.val '' K.supp).ncard) : Disjoint (Subtype.val '' K.supp) G.oddVerts := by
  by_contra hc
  simp [Subtype.val_injective, Set.ncard_image_of_injective] at h
  rw [@Set.not_disjoint_iff] at hc
  obtain ⟨v, ⟨⟨v', ⟨hv', rfl⟩⟩, ⟨w, ⟨⟨c, hc'⟩, hw'⟩⟩⟩⟩ := hc
  simp only [Set.mem_setOf_eq] at hc'
  rw [@ConnectedComponent.mem_supp_iff] at hv'
  have : K = c := by
    rw [← hv']
    rw [← Subtype.val_injective hw']
    rw [← hc'.2]
    exact component_rep c
  rw [← Nat.not_even_iff_odd] at hc'
  rw [this] at h
  exact hc'.1 h

-- In #20024/#21097 (refactored)
lemma supp_intersection_oddVerts_card {K : G.deleteUniversalVerts.coe.ConnectedComponent}
    (h : Odd (Subtype.val '' K.supp).ncard) : (Subtype.val '' K.supp ∩ G.oddVerts).ncard = 1 := by
  rw [@Set.ncard_eq_one]
  use K.exists_rep.choose
  ext v
  constructor
  · intro hv
    simp only [Set.mem_singleton_iff]
    rw [Set.mem_inter_iff] at hv
    obtain ⟨⟨w, ⟨hw, rfl⟩⟩, ⟨w', ⟨⟨c, ⟨hc, rfl⟩⟩, hw''⟩⟩⟩ := hv
    apply Subtype.val_injective at hw''
    rw [← hw''] at hw ⊢
    congr
    dsimp at hw
    rw [@ConnectedComponent.mem_supp_iff] at hw
    rw [← hw]
    exact Eq.symm (component_rep c)
  · intro hv
    simp only [Set.mem_singleton_iff] at hv
    rw [hv]
    refine ⟨Set.mem_image_of_mem _ K.exists_vert_mem_supp, ?_⟩
    apply Set.mem_image_of_mem
    simp only [Set.mem_image, Set.mem_setOf_eq]
    simp [Subtype.val_injective, Set.ncard_image_of_injective] at h
    exact ⟨K, ⟨h, rfl⟩⟩


lemma IsMatching.exists_of_disjoint_sets_of_equiv {s t : Set V} (h : Disjoint s t)
    (f : s ≃ t) (hadj : ∀ v : s, G.Adj v (f v)) :
    ∃ M : Subgraph G, M.verts = s ∪ t ∧ M.IsMatching := by

  sorry

lemma IsMatching.exists_of_universalVerts [Fintype V] [DecidableEq V] {s : Set V} (h : Disjoint G.universalVerts s) (hc : s.ncard ≤ G.universalVerts.ncard) :
    ∃ t ⊆ G.universalVerts, ∃ (M : Subgraph G), M.IsMatching ∧ M.verts = s ∪ t := by
  obtain ⟨t, ht⟩ := Set.exists_subset_card_eq hc
  use t
  refine ⟨ht.1, ?_⟩
  have f : s ≃ t := by
    simp only [← Set.Nat.card_coe_set_eq, Nat.card.eq_1] at ht
    have : Nonempty (s ≃ t) := by
      rw [← Cardinal.eq]
      exact Cardinal.toNat_injOn (Set.mem_Iio.mpr (Set.Finite.lt_aleph0 (s.toFinite)))
        (Set.mem_Iio.mpr (Set.Finite.lt_aleph0 (Set.toFinite t))) ht.2.symm
    exact (Classical.inhabited_of_nonempty this).default
  have hd := (Set.disjoint_of_subset_left ht.1 h).symm
  obtain ⟨M1, hM1⟩ := IsMatching.exists_of_disjoint_sets_of_equiv
    hd
    f
    (by
      intro v
      have : ((f v) : V) ∈ G.universalVerts := ht.1 (f v).coe_prop
      simp only [universalVerts, Set.mem_setOf_eq] at this
      apply this
      rw [ne_comm]
      exact Disjoint.ne_of_mem hd v.coe_prop (f v).coe_prop
      : ∀ (v : ↑s), G.Adj ↑v ↑(f v))
  aesop

theorem tutte_part' [Fintype V] [Inhabited V] [DecidableEq V] [DecidableRel G.Adj]
  (hveven : Even (Fintype.card V))
  (h : {c : G.deleteUniversalVerts.coe.ConnectedComponent | Odd (c.supp.ncard)}.ncard ≤ G.universalVerts.ncard)
  (h' : ∀ (K : G.deleteUniversalVerts.coe.ConnectedComponent), G.deleteUniversalVerts.coe.IsClique K.supp) :
    ∃ (M : Subgraph G), M.IsPerfectMatching := by
  classical
  simp only [← Set.Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at h

  obtain ⟨t, ht, M1, hM1⟩ := IsMatching.exists_of_universalVerts oddVerts_core_disjoint.symm (by
      unfold oddVerts
      simp only [Subtype.val_injective, Set.ncard_image_of_injective, rep_choose_inj]
      simp only [Fintype.card_eq_nat_card, Set.Nat.card_coe_set_eq] at h
      exact h
      : G.oddVerts.ncard ≤ G.universalVerts.ncard)


  have evenKsubM1 (K : G.deleteUniversalVerts.coe.ConnectedComponent) : Even ((Subtype.val '' K.supp) \ M1.verts).ncard := by
    rw [hM1.2]
    rw [← @Set.diff_inter_diff]
    have : Subtype.val '' K.supp \ t = Subtype.val '' K.supp := by
      simp only [sdiff_eq_left]
      apply Set.disjoint_of_subset_right ht
      exact disjoint_supp_universalVerts
    simp only [this, Set.inter_diff_distrib_right, Set.inter_self, Set.diff_inter_self_eq_diff]

    by_cases h : Even (Subtype.val '' K.supp).ncard
    · have : Subtype.val '' K.supp \ G.oddVerts = Subtype.val '' K.supp := by
        simp only [sdiff_eq_left]
        exact disjoint_even_supp_oddVerts h
      rw [this]
      exact h
    · have hOdd := h
      rw [@Nat.not_even_iff_odd] at hOdd
      rw [← Set.ncard_inter_add_ncard_diff_eq_ncard (Subtype.val '' K.supp) G.oddVerts] at h
      rw [supp_intersection_oddVerts_card hOdd] at h
      simp only [Nat.not_even_iff_odd] at h
      rw [@Nat.odd_add] at h
      simp only [odd_one, true_iff] at h
      exact h

  have compMatching (K : G.deleteUniversalVerts.coe.ConnectedComponent) :
      ∃ M : Subgraph G, M.verts = Subtype.val '' K.supp \ M1.verts ∧ M.IsMatching := by
    have : G.IsClique (Subtype.val '' K.supp \ M1.verts) := (isClique_lifts (h' K)).subset Set.diff_subset
    rw [← isClique_even_iff_matches _ (Set.toFinite _ ) this]
    exact evenKsubM1 K

  let M2 : Subgraph G := (⨆ (K : G.deleteUniversalVerts.coe.ConnectedComponent), (compMatching K).choose)

  have hM2 : M2.IsMatching := by
    apply Subgraph.IsMatching.iSup (fun c => (compMatching c).choose_spec.2)
    intro i j hij
    rw [(compMatching i).choose_spec.2.support_eq_verts, (compMatching j).choose_spec.2.support_eq_verts,
      (compMatching i).choose_spec.1, (compMatching j).choose_spec.1]
    exact Set.disjoint_of_subset (Set.diff_subset) (Set.diff_subset) <| Set.disjoint_image_of_injective Subtype.val_injective (SimpleGraph.pairwise_disjoint_supp_connectedComponent _ hij)

  have disjointM12 : Disjoint M1.verts M2.verts := by
    rw [@Set.disjoint_right]
    intro v hv
    rw [Subgraph.verts_iSup, Set.mem_iUnion] at hv
    obtain ⟨K, hK⟩ := hv
    rw [(compMatching K).choose_spec.1] at hK
    exact hK.2

  have hM12 : (M1 ⊔ M2).IsMatching := by
    apply hM1.1.sup hM2
    rw [hM1.1.support_eq_verts, hM2.support_eq_verts]
    exact disjointM12

  have evensubM1M2 : Even ((Set.univ : Set V) \ (M1.verts ∪ M2.verts)).ncard := by
    rw [Set.ncard_diff (by intro v _; trivial), Nat.even_sub (Set.ncard_le_ncard (by intro v _; trivial))]
    rw [Fintype.card_eq_nat_card, ← Set.ncard_univ] at hveven
    simp only [hveven, true_iff]
    simp only [Set.ncard_union_eq disjointM12, Nat.even_add,
      Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card', iff_true_left hM1.1.even_card, hM2.even_card]

  have sub : ((Set.univ : Set V) \ (M1.verts ∪ M2.verts)) ⊆ G.universalVerts := by
    rw [@Set.diff_subset_iff]
    intro v _
    by_cases h : v ∈ M1.verts ∪ G.universalVerts
    · cases' h with hl hr
      · left; left; exact hl
      · right; exact hr
    · rw [@Set.mem_union] at h
      push_neg at h
      left; right
      rw [@Subgraph.verts_iSup]
      rw [@Set.mem_iUnion]
      let K := G.deleteUniversalVerts.coe.connectedComponentMk ⟨v, by
        rw [deleteUniversalVerts_verts]
        simp only [Set.mem_diff, Set.mem_univ, true_and]
        exact h.2
        ⟩
      use K
      simp only [(compMatching K).choose_spec.1, Set.mem_diff, Set.mem_image, ConnectedComponent.mem_supp_iff, Subtype.exists,
        deleteUniversalVerts_verts, Set.mem_univ, true_and, exists_and_right, exists_eq_right,
        exists_prop, and_true]
      aesop

  have subM1M2Clique : G.IsClique ((Set.univ : Set V) \ (M1.verts ∪ M2.verts)) := by
    exact G.isClique_universalVerts.subset sub

  obtain ⟨M3, hM3⟩ := (isClique_even_iff_matches _ (Set.toFinite _ ) subM1M2Clique).mp evensubM1M2

  let Mcon := M1 ⊔ M2 ⊔ M3
  use Mcon

  have MconSpan : Mcon.IsSpanning := by
    rw [Subgraph.isSpanning_iff, Subgraph.verts_sup, Subgraph.verts_sup, hM3.1]
    exact Set.union_diff_cancel (by
      intro v _
      trivial)
  refine ⟨?_, MconSpan⟩
  unfold Mcon
  exact hM12.sup hM3.2 (by
    simp only [hM12.support_eq_verts, hM3.2.support_eq_verts, hM3.1, Subgraph.verts_sup]
    exact Disjoint.symm Set.disjoint_sdiff_left
    )
