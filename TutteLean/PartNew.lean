import TutteLean.Defs
import TutteLean.Clique

import Mathlib.Combinatorics.SimpleGraph.UniversalVerts
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Represents

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

lemma disjoint_image_val_universalVerts (s : Set G.deleteUniversalVerts.verts) : Disjoint (Subtype.val '' s) G.universalVerts := by
  simpa [deleteUniversalVerts, Subgraph.deleteVerts_verts, ← Set.disjoint_compl_right_iff_subset,
    Set.compl_eq_univ_diff] using Subtype.coe_image_subset _ s


lemma subgraph_coe (H : Subgraph G) {x y : H.verts} (h : H.coe.Adj x y) : G.Adj x.val y.val := h.adj_sub

-- In #20705 (not mine)
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

lemma quot_out_inj (r : V → V → Prop): Function.Injective (@Quot.out _ r) :=
  fun v w h ↦ by simpa [Quot.out_eq] using (congrArg _ h : Quot.mk r v.out = Quot.mk r w.out)

lemma IsMatching.exists_of_universalVerts [Fintype V] [DecidableEq V] {s : Set V} (h : Disjoint G.universalVerts s) (hc : s.ncard ≤ G.universalVerts.ncard) :
    ∃ t ⊆ G.universalVerts, ∃ (M : Subgraph G), M.IsMatching ∧ M.verts = s ∪ t := by
  obtain ⟨t, ⟨ht, hts⟩⟩ := Set.exists_subset_card_eq hc
  use t
  refine ⟨ht, ?_⟩
  obtain ⟨f⟩ : Nonempty (s ≃ t) := by
    rw [← Cardinal.eq, ← t.cast_ncard (Set.toFinite _), ← s.cast_ncard (Set.toFinite _)]
    exact congrArg Nat.cast hts.symm
  have hd := (Set.disjoint_of_subset_left ht h).symm
  obtain ⟨M1, hM1⟩ := Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv hd f
    (fun v ↦ ht (f v).coe_prop (hd.symm.ne_of_mem (f v).coe_prop v.coe_prop) : ∀ (v : ↑s), G.Adj ↑v ↑(f v))
  aesop

lemma even_comp_left [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {t : Set V} (K : G.deleteUniversalVerts.coe.ConnectedComponent)  (h : t ⊆ G.universalVerts) :
  Even ((Subtype.val '' K.supp) \ (Subtype.val '' (Quot.out '' {c : G.deleteUniversalVerts.coe.ConnectedComponent | Odd (c.supp.ncard)}) ∪ t)).ncard := by
  classical
  have hrep := ConnectedComponent.Represents.image_out {c : G.deleteUniversalVerts.coe.ConnectedComponent | Odd (c.supp.ncard)}
  have : Subtype.val '' K.supp \ t = Subtype.val '' K.supp := by
    simp only [sdiff_eq_left]
    apply Set.disjoint_of_subset_right h
    exact disjoint_supp_universalVerts
  simp only [← Set.diff_inter_diff, ← Set.image_diff Subtype.val_injective, this, Set.inter_diff_distrib_right,
    Set.inter_self, Set.diff_inter_self_eq_diff, ← Set.image_inter Subtype.val_injective, Set.ncard_image_of_injective _ Subtype.val_injective]
  by_cases h : Even K.supp.ncard
  · simpa [hrep.ncard_sdiff_of_not_mem (by simpa [Set.ncard_image_of_injective, ← Nat.not_odd_iff_even] using h)] using h
  · rw [hrep.ncard_sdiff_of_mem (Nat.not_even_iff_odd.mp h)]
    rw [Nat.even_sub (by
      have : K.supp.ncard ≠ 0 := Nat.ne_of_odd_add (Nat.not_even_iff_odd.mp h)
      omega)]
    simpa using Nat.not_even_iff_odd.mp h


theorem comp_matching [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
  (h : {c : G.deleteUniversalVerts.coe.ConnectedComponent | Odd (c.supp.ncard)}.ncard ≤ G.universalVerts.ncard)
  (h' : ∀ (K : G.deleteUniversalVerts.coe.ConnectedComponent), G.deleteUniversalVerts.coe.IsClique K.supp) :
    ∃ (M : Subgraph G), M.IsMatching ∧ Set.univ \ M.verts ⊆ G.universalVerts := by
  classical
  simp only [← Set.Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at h

  have hrep := ConnectedComponent.Represents.image_out {c : G.deleteUniversalVerts.coe.ConnectedComponent | Odd (c.supp.ncard)}
  let oddVerts := Quot.out '' {c : G.deleteUniversalVerts.coe.ConnectedComponent | Odd (c.supp.ncard)}
  obtain ⟨t, ht, M1, hM1⟩ := IsMatching.exists_of_universalVerts (disjoint_image_val_universalVerts _).symm (by
      simp only [Fintype.card_eq_nat_card, Set.Nat.card_coe_set_eq] at h
      rwa [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_image_of_injective _ (quot_out_inj _)])

  have compMatching (K : G.deleteUniversalVerts.coe.ConnectedComponent) :
      ∃ M : Subgraph G, M.verts = Subtype.val '' K.supp \ M1.verts ∧ M.IsMatching := by
    have : G.IsClique (Subtype.val '' K.supp \ M1.verts) := (isClique_lifts (h' K)).subset Set.diff_subset
    rw [← isClique_even_iff_matches _ (Set.toFinite _ ) this]
    rw [hM1.2]
    exact even_comp_left _ ht
  let M2 : Subgraph G := (⨆ (K : G.deleteUniversalVerts.coe.ConnectedComponent), (compMatching K).choose)

  have hM2 : M2.IsMatching := by
    apply Subgraph.IsMatching.iSup (fun c => (compMatching c).choose_spec.2)
    intro i j hij
    rw [(compMatching i).choose_spec.2.support_eq_verts, (compMatching j).choose_spec.2.support_eq_verts,
      (compMatching i).choose_spec.1, (compMatching j).choose_spec.1]
    exact Set.disjoint_of_subset (Set.diff_subset) (Set.diff_subset) <| Set.disjoint_image_of_injective Subtype.val_injective (SimpleGraph.pairwise_disjoint_supp_connectedComponent _ hij)

  have disjointM12 : Disjoint M1.verts M2.verts := by
    rw [Subgraph.verts_iSup, Set.disjoint_iUnion_right]
    intro K
    rw [(compMatching K).choose_spec.1]
    exact Set.disjoint_sdiff_right

  have hM12 : (M1 ⊔ M2).IsMatching := by
    apply hM1.1.sup hM2
    rw [hM1.1.support_eq_verts, hM2.support_eq_verts]
    exact disjointM12

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
      exact ⟨⟨h.2, (by simp [K])⟩, h.1⟩
  exact ⟨M1 ⊔ M2, hM12, sub⟩


theorem tutte_part' [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
  (hveven : Even (Fintype.card V))
  (h : {c : G.deleteUniversalVerts.coe.ConnectedComponent | Odd (c.supp.ncard)}.ncard ≤ G.universalVerts.ncard)
  (h' : ∀ (K : G.deleteUniversalVerts.coe.ConnectedComponent), G.deleteUniversalVerts.coe.IsClique K.supp) :
    ∃ (M : Subgraph G), M.IsPerfectMatching := by
  classical
  obtain ⟨M, ⟨hM, sub⟩⟩ := comp_matching h h'

  have subM1M2Clique : G.IsClique ((Set.univ : Set V) \ M.verts) := by
    exact G.isClique_universalVerts.subset sub

  have evensubM1M2 : Even ((Set.univ : Set V) \ M.verts).ncard := by
    rw [Set.ncard_diff (by intro v _; trivial), Nat.even_sub (Set.ncard_le_ncard (by intro v _; trivial))]
    rw [Fintype.card_eq_nat_card, ← Set.ncard_univ] at hveven
    simp [hveven, show Even M.verts.ncard from by
      simpa [-Set.toFinset_card,← Set.toFinset_union, ← Set.ncard_eq_toFinset_card'] using hM.even_card]
  obtain ⟨M3, hM3⟩ := (isClique_even_iff_matches _ (Set.toFinite _ ) subM1M2Clique).mp evensubM1M2

  let Mcon := M ⊔ M3
  use Mcon

  have MconSpan : Mcon.IsSpanning := by
    rw [Subgraph.isSpanning_iff, Subgraph.verts_sup, hM3.1]
    exact Set.union_diff_cancel (by
      intro v _
      trivial)
  refine ⟨?_, MconSpan⟩
  unfold Mcon
  exact hM.sup hM3.2 (by
    simp only [hM.support_eq_verts, hM3.2.support_eq_verts, hM3.1, Subgraph.verts_sup]
    exact Disjoint.symm Set.disjoint_sdiff_left
    )
