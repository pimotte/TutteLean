import TutteLean.Defs
import TutteLean.SingleEdge

namespace SimpleGraph
-- universe u
variable {V : Type*} {G : SimpleGraph V}

theorem cardEdgeSetLessThanSquare (H : SimpleGraph V) [Fintype V] [DecidableRel H.Adj] : (edgeSet H).ncard ≤ Fintype.card V * Fintype.card V := by
  -- rw [← Fintype.card_prod]
  rw [← @coe_edgeFinset]
  rw [@Set.ncard_coe_Finset]
  apply le_trans (Finset.card_le_univ _)
  rw [@Sym2.card]
  rw [Nat.choose_two_right]
  rw [Nat.triangle_succ]
  -- rw [← mul_add_one]
  rw [← mul_le_mul_left (by omega : 0 < 2)]
  rw [Nat.left_distrib]
  rw [← Nat.mul_div_assoc _ (by
    rw [Nat.Prime.dvd_mul (Nat.prime_two)]
    if h : Even (Fintype.card V)
    then
      left
      exact even_iff_two_dvd.mp h
    else
      right
      rw [← @Nat.odd_iff_not_even] at h
      refine even_iff_two_dvd.mp ?h.a
      rw [Nat.odd_iff] at h
      rw [Nat.even_iff]
      rw [Nat.sub_mod_eq_zero_of_mod_eq]
      simpa only [Nat.mod_succ]
    )]
  ring_nf
  rw [Nat.mul_div_left _ (by omega : 0 < 2)]
  rw [← Nat.left_distrib]
  rw [Nat.pow_two]
  rw [Nat.mul_assoc]
  if h' : Fintype.card V = 0
  then
    simp only [h'] ; rfl
  else
    apply Nat.mul_le_mul_left
    have : Fintype.card V > 0 := Nat.zero_lt_of_ne_zero h'
    omega



-- Om #15357
lemma isMatchingFree_mono {G G' : SimpleGraph V} (h : G ≤ G') (hmf : isMatchingFree G') : isMatchingFree G := by
  intro x
  by_contra! hc
  apply hmf (x.map (SimpleGraph.Hom.ofLE h))
  refine ⟨hc.1.map_ofLE h, ?_⟩
  intro v
  simp only [Subgraph.map_verts, Hom.coe_ofLE, id_eq, Set.image_id']
  exact hc.2 v


structure MatchingFreeExtension (G : SimpleGraph V) where
  G' : SimpleGraph V
  hDec : DecidableRel G'.Adj
  hSubgraph : G ≤ G'
  hMatchFree : isMatchingFree G'

structure MaximalMatchingFreeExtension (G : SimpleGraph V) extends MatchingFreeExtension G where
  hMaximal : ∀ (G'' : SimpleGraph V), G'' > G' → ¬ isMatchingFree G''

lemma bigger_gives_edge {G G' : SimpleGraph V} (h : G < G') : ∃ v w, ¬ G.Adj v w ∧ G'.Adj v w := by
  by_contra! hc
  apply h.2
  intro v w hvw
  by_contra! hc'
  exact hc v w hc' hvw

noncomputable def maximalWithoutMatching' [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
   (GExt : MatchingFreeExtension G) : MaximalMatchingFreeExtension G := by
    have inst : DecidableRel G.Adj := by infer_instance
    if h' : ∃ (v : V) (w : V) (h : v ≠ w), ¬ GExt.G'.Adj v w ∧ isMatchingFree (GExt.G' ⊔ SimpleGraph.singleEdge h) then
      let h := h'.choose_spec.choose_spec.choose
      exact maximalWithoutMatching'
        ⟨ GExt.G' ⊔ singleEdge h ,
          Classical.decRel _ ,
          by exact le_trans GExt.hSubgraph (distribLattice.proof_7 GExt.G' (singleEdge h)) ,
          h'.choose_spec.choose_spec.choose_spec.2 ⟩
    else
      exact ⟨⟨ GExt.G' , GExt.hDec, GExt.hSubgraph, GExt.hMatchFree ⟩ , (by
        by_contra! hc
        apply h'
        obtain ⟨ G'' , hG'' ⟩ := hc
        obtain ⟨ v , ⟨ w , hvw ⟩ ⟩ := bigger_gives_edge (hG''.1)
        use v
        use w

        use (by
          by_contra! hc
          exact G''.loopless v (hc ▸ hvw.2)
          )
        constructor
        · by_contra! hc
          exact hvw.1 hc
        ·
          apply isMatchingFree_mono (_ : GExt.G' ⊔ singleEdge _ ≤ G'')
          · exact hG''.2
          · intro v' w' hvw'
            rw [SimpleGraph.sup_adj] at hvw'
            cases hvw' with
            | inl ha =>
              apply hG''.1.1
              exact ha
            | inr hb =>
              unfold singleEdge at hb
              dsimp at hb
              cases hb with
              | inl ha' =>
                exact ha'.1 ▸ ha'.2 ▸ hvw.2
              | inr hb' =>
                exact hb'.1 ▸ hb'.2 ▸ hvw.2.symm
        ) ⟩
termination_by (Fintype.card V * Fintype.card V + 1) - (GExt.G'.edgeSet).ncard
decreasing_by
· simp (config := { unfoldPartialApp := true, zetaDelta := true }) [invImage, Prod.lex, sizeOfWFRel, measure, Nat.lt_wfRel, WellFoundedRelation.rel]
  -- simp [InvImage]

  apply Nat.sub_lt_sub_left
  haveI inst := GExt.hDec
  · exact Nat.lt_succ_of_le (cardEdgeSetLessThanSquare _)

  · apply Set.ncard_lt_ncard
    · dsimp
      simp only [edgeSet_sup]
      rw [singleEdge_edgeset]
      rw [Set.union_singleton]
      apply Set.ssubset_insert
      rw [SimpleGraph.mem_edgeSet]

      exact h'.choose_spec.choose_spec.choose_spec.1
    · simp_wf
      haveI inst := GExt.hDec
      exact ⟨ allEdgeSetFinite GExt.G' , singleEdgeSetFinite _ ⟩

noncomputable def maximalWithoutMatching [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
   (h : G.isMatchingFree) : MaximalMatchingFreeExtension G := by
    exact maximalWithoutMatching' ⟨ G , by infer_instance , by rfl , h ⟩
