import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
-- import Mathlib.Algebra.BigOperators.Basic



namespace SimpleGraph
-- universe u
variable {V : Type*} {G : SimpleGraph V}

/-- A connected component is *odd* if it has an add number of vertices
in its support. -/
-- Note: only connected components with finitely many vertices can be odd.
def ConnectedComponent.isOdd (c : G.ConnectedComponent) : Prop :=
  Odd (Nat.card c.supp)

noncomputable def cardOddComponents (G : SimpleGraph V) : Nat :=
  Set.ncard {c : G.ConnectedComponent | c.isOdd}

lemma ConnectedComponent.isOdd_iff (c : G.ConnectedComponent) [Fintype c.supp] :
    c.isOdd ↔ Odd (Fintype.card c.supp) := by
  rw [isOdd, Nat.card_eq_fintype_card]


lemma deleteVerts_verts_notmem_deleted (a : ((⊤ : G.Subgraph).deleteVerts u).verts) : a.val ∉ u := a.prop.2


instance myInst3 [r : DecidableRel G.Adj] : DecidableRel (((⊤ : G.Subgraph).deleteVerts u).coe).Adj := by
  intro x y
  cases (r x y) with
  | isFalse nh => {
    exact .isFalse (by
      intro w
      exact nh (Subgraph.coe_adj_sub _ _ _ w)
      )
  }
  | isTrue h => {
    exact .isTrue (by
      apply (SimpleGraph.Subgraph.Adj.coe)
      apply Subgraph.deleteVerts_adj.mpr
      constructor
      · trivial
      constructor
      · exact deleteVerts_verts_notmem_deleted x
      constructor
      · trivial
      constructor
      · exact deleteVerts_verts_notmem_deleted y
      exact h
      done

    )
  }

instance [Fintype V] [DecidableEq V] [DecidableRel G.Adj] : DecidableEq (ConnectedComponent G) := by
  intro c c'
  exact c.recOn
    (fun v =>
      c'.recOn (fun w => by
        rw [@ConnectedComponent.eq]
        infer_instance)
        (fun _ _ _ _ => Subsingleton.elim _ _))
    (fun _ _ _ _ => Subsingleton.elim _ _)


-- noncomputable instance myInst5 [Fintype V] [DecidableEq V] (u : Set V) : Fintype u := by
--   exact Fintype.ofFinite ↑u

noncomputable instance myInst4 [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (u : Set V) :
    Fintype ((⊤ : G.Subgraph).deleteVerts u).verts := by
      haveI : Fintype u := by
        exact Fintype.ofFinite u
      simp only [Subgraph.induce_verts, Subgraph.verts_top]
      infer_instance


theorem mem_supp_of_adj (C : G.ConnectedComponent) (v w : V) (hv : v ∈ C.supp) (hadj : G.Adj v w) :
       w ∈ C.supp := by

      rw [ConnectedComponent.mem_supp_iff]
      rw [← (ConnectedComponent.mem_supp_iff _ _).mp hv]
      exact ConnectedComponent.connectedComponentMk_eq_of_adj (adj_symm G hadj)


theorem mem_supp_of_adj' [Fintype V] [DecidableEq V] [DecidableRel G.Adj]  (c : ConnectedComponent ((⊤ : Subgraph G).deleteVerts u).coe)
      (v w : V) (hv : v ∈ Subtype.val '' c.supp) (hw : w ∈ ((⊤ : Subgraph G).deleteVerts  u).verts)
      (hadj : G.Adj v w) :
       w ∈ Subtype.val '' c.supp := by
      rw [Set.mem_image]
      obtain ⟨ v' , hv' ⟩ := hv
      use ⟨ w , ⟨ by trivial , by refine Set.not_mem_of_mem_diff hw ⟩ ⟩
      rw [ConnectedComponent.mem_supp_iff]
      constructor
      · rw [← (ConnectedComponent.mem_supp_iff _ _).mp hv'.1]
        apply ConnectedComponent.connectedComponentMk_eq_of_adj
        apply SimpleGraph.Subgraph.Adj.coe
        rw [Subgraph.deleteVerts_adj]
        constructor
        · exact trivial
        · constructor
          · exact Set.not_mem_of_mem_diff hw
          · constructor
            · exact trivial
            · constructor
              · exact deleteVerts_verts_notmem_deleted v'
              · rw [Subgraph.top_adj]
                rw [hv'.2]
                exact adj_symm G hadj


      · dsimp


def isMatchingFree (G : SimpleGraph V) := ∀ (M : Subgraph G), ¬Subgraph.IsPerfectMatching M


def singleEdge {v w : V} (h : v ≠ w) : SimpleGraph V where
  Adj v' w' := (v = v' ∧ w = w') ∨ (v = w' ∧ w = v')

@[simp]
lemma singleEdge_Adj {v w : V} (h : v ≠ w) : (singleEdge h).Adj v' w' = ((v = v' ∧ w = w') ∨ (v = w' ∧ w = v')) := rfl

lemma singleEdge_edgeset {v w : V} {h : v ≠ w} : (singleEdge h).edgeSet = {Sym2.mk ⟨ v , w ⟩}  := by
  unfold singleEdge
  ext x
  rw [@Set.mem_singleton_iff]
  constructor
  · exact x.ind (fun x y => by
      rw [@mem_edgeSet]
      simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
      intro h
      cases h with
      | inl ha =>
        left
        exact ⟨ ha.1.symm , ha.2.symm ⟩
      | inr hb =>
        right
        exact ⟨ hb.2.symm , hb.1.symm ⟩
      )
  · intro h
    rw [h]
    simp only [mem_edgeSet, and_self, true_or]

def singleEdgeSetFinite {v w : V} (h : v ≠ w) : Finite ((singleEdge h).edgeSet) := by
  rw [singleEdge_edgeset]
  infer_instance

def allEdgeSetFinite (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : Finite (G.edgeSet) := by

  infer_instance

instance singleEdgeDecidableRel [DecidableEq V] {v w : V} (h : v ≠ w) : DecidableRel (singleEdge h).Adj := by
  intro x y
  if h' : (v = x ∧ w = y) ∨ (v = y ∧ w = x)
  then
    exact .isTrue h'
  else
    exact .isFalse h'


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

@[simps]
def Subgraph.empty (G : SimpleGraph V) : Subgraph G where
  verts := ∅
  Adj _ _ := False
  adj_sub := False.elim
  edge_vert := False.elim

lemma Set.Finite.one_lt_ncard_of_nonempty_of_even (hs : Set.Finite s) (hn : Set.Nonempty s)
    (he : Even (s.ncard)) : 1 < s.ncard := by
  have : s.ncard ≠ 0 := by
    intro h
    rw [@Set.nonempty_iff_ne_empty] at hn
    exact hn <| (Set.ncard_eq_zero hs).mp h
  have : s.ncard ≠ 1 := by
    intro h
    simp [h] at he
  omega


@[simp]
lemma Set.Finite.odd_card_insert_iff {x : V} {u : Set V} (hu : Set.Finite u) (hx : x ∉ u) :
    Odd (insert x u).ncard ↔ Even u.ncard := by
  rw [Set.ncard_insert_of_not_mem hx hu, Nat.odd_add]
  simp only [Nat.odd_add, Nat.odd_iff_not_even, Nat.not_even_one, iff_false, Decidable.not_not]

@[simp]
lemma Set.Finite.even_card_insert_iff {x : V} {u : Set V} (hu : Set.Finite u) (hx : x ∉ u) :
    Even (insert x u).ncard ↔ Odd u.ncard := by
  rw [Set.ncard_insert_of_not_mem hx hu, Nat.even_add]
  simp only [Nat.not_even_one, iff_false, Nat.odd_iff_not_even]



lemma isClique_even_iff_matches [DecidableEq V]
    (u : Set V) (hu : Set.Finite u) (hc : G.IsClique u) : Even u.ncard ↔ ∃ (M : Subgraph G), M.verts = u ∧ M.IsMatching := by
  haveI : Fintype u := hu.fintype
  refine ⟨?_ , by
    rintro ⟨M, ⟨hMl, hMr⟩⟩
    haveI : Fintype M.verts := hMl ▸ hu.fintype
    subst hMl
    simpa [Set.ncard_eq_toFinset_card _ hu, Set.toFinite_toFinset,
      Set.toFinset_card] using hMr.even_card
    ⟩
  intro he
  cases' Set.eq_empty_or_nonempty u with h h
  · subst h
    use (Subgraph.empty G)
    simp only [Subgraph.empty_verts, true_and]
    intro _ h
    contradiction
  · obtain ⟨x, y, ⟨hx, hy, hxy⟩⟩ := (Set.one_lt_ncard_iff hu).mp (Set.Finite.one_lt_ncard_of_nonempty_of_even hu h he)
    let u' := u \ {x, y}
    have : insert x (insert y (u \ {x, y})) = u := by
      ext v
      simp only [Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff]
      rw [← or_assoc]
      by_cases h : v = x ∨ v = y
      · cases' h with h' h' <;> subst h' <;> simpa
      · simp only [h, not_false_eq_true, and_true, false_or]
    have hu'e : Even (u \ {x, y}).ncard := by
      rw [← Set.Finite.odd_card_insert_iff (hu.diff {x, y}) (by simp : y ∉ u \ {x, y})]
      rw [← Set.Finite.even_card_insert_iff (insert y (u \ {x, y})).toFinite (by
        simp [hxy] : x ∉ (insert y (u \ {x, y})))]
      rwa [this]
    have hu'c := hc.subset (Set.diff_subset : u' ⊆ u)
    have hu'f := Set.Finite.diff hu {x, y}
    obtain ⟨M, hM⟩ := (isClique_even_iff_matches u' hu'f hu'c).mp hu'e
    use M ⊔ subgraphOfAdj _ (hc hx hy hxy)
    simp only [Subgraph.verts_sup, hM.1, subgraphOfAdj_verts]
    refine ⟨by
      rw [Set.diff_union_self]
      exact Set.union_eq_self_of_subset_right (Set.pair_subset hx hy), ?_⟩
    refine Subgraph.IsMatching.sup hM.2 (Subgraph.IsMatching.subgraphOfAdj (hc hx hy hxy)) ?h.hd
    simp only [support_subgraphOfAdj, hM.2.support_eq_verts, hM.1]
    exact Set.disjoint_sdiff_left
termination_by u.ncard
decreasing_by
· simp_wf
  refine Set.ncard_lt_ncard ?_ hu
  exact ⟨Set.diff_subset, by
    rw [@Set.not_subset_iff_exists_mem_not_mem]
    use x
    exact ⟨hx, by simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, true_or,
      not_true_eq_false, and_false, not_false_eq_true]⟩⟩

lemma completeGraph_isClique (u : Set V) : (completeGraph V).IsClique u := by
  intro x _ y _ a_2 a_3
  simp_all only [Set.mem_univ, ne_eq, not_true_eq_false]

lemma completeGraph_even_iff_matches [Fintype V] [DecidableEq V] :
    Even (Fintype.card V) ↔ ∃ (M : Subgraph (completeGraph V)), M.verts = Set.univ ∧ M.IsMatching := by
  simpa [Set.ncard_univ, Nat.card_eq_fintype_card, (set_fintype_card_eq_univ_iff _).mpr rfl] using
    isClique_even_iff_matches (Set.univ : Set V) Set.finite_univ (completeGraph_isClique _)

lemma existsIsMatching [Fintype V] [DecidableEq V]
  (u : Set V) (hu : Set.Finite u) (h : G.IsClique u) (uEven : Even (u.ncard)) : ((isClique_even_iff_matches u hu h).mp uEven).choose.IsMatching := by
  exact (Exists.choose_spec ((isClique_even_iff_matches u hu h).mp uEven)).2


lemma componentExistsRep (c : ConnectedComponent G) : ∃ v, SimpleGraph.connectedComponentMk G v = c := c.exists_rep

lemma oddSubOneEven (n : Nat) (h : Odd n) : Even (n - 1) := by
  obtain ⟨ k , hk ⟩ := h
  use k
  rw [hk]
  rw [Nat.add_sub_cancel]
  ring


lemma oddCliqueAlmostMatches [Fintype V] [DecidableEq V]
  {u : Set V} {v : V} (hv : v ∈ u) (h : G.IsClique u) (uOdd : Odd (u.ncard)) : ∃ (M : Subgraph G), insert v M.verts = u ∧ M.IsMatching := by
  haveI : Fintype u := Fintype.ofFinite _
  rw [@Set.ncard_eq_toFinset_card'] at uOdd
  rw [@Set.toFinset_card] at uOdd
  have u'Even : Even ((u \ {v} : Set V).ncard) := by
    rw [Set.ncard_eq_toFinset_card']
    rw [Set.toFinset_diff]
    simp only [Set.mem_setOf_eq, Set.toFinset_singleton]
    rw [Finset.sdiff_singleton_eq_erase]
    rw [Finset.card_erase_of_mem (Set.mem_toFinset.mpr hv)]
    rw [Set.toFinset_card]
    exact oddSubOneEven _ uOdd
  have u'Clique : G.IsClique (u \ {v}) := SimpleGraph.IsClique.subset (@Set.diff_subset V u {v}) h
  obtain ⟨ M , hM ⟩ := ((isClique_even_iff_matches (u \ {v}) (Set.toFinite (u \ {v})) u'Clique).mp u'Even)
  use M
  constructor
  · rw [hM.1]
    rw [Set.insert_diff_singleton]
    exact (Set.insert_eq_of_mem hv)
  · exact hM.2

lemma oddCliqueAlmostMatchesDoesNotContainNode [Fintype V] [DecidableEq V]
  {u : Set V} {v : V} (hv : v ∈ u) (h : G.IsClique u) (uOdd : Odd (u.ncard)) : v ∉ (oddCliqueAlmostMatches hv h uOdd).choose.verts := by
  haveI (s : Set V) : Fintype s := Fintype.ofFinite _
  have hM := (oddCliqueAlmostMatches hv h uOdd).choose_spec

  have : Even (Fintype.card (oddCliqueAlmostMatches hv h uOdd).choose.verts) := by
    rw [← @Set.toFinset_card]
    exact SimpleGraph.Subgraph.IsMatching.even_card hM.2
  intro hv
  rw [Set.insert_eq_of_mem hv] at hM

  rw [← hM.1] at uOdd
  rw [@Nat.even_iff_not_odd] at this
  -- rw? at this
  -- rw [← @Set.toFinset_card] at uOdd
  rw [Set.ncard_eq_toFinset_card] at uOdd
  rw [@Set.Finite.card_toFinset] at uOdd
  exact this uOdd


lemma oddCliqueAlmostMatchesSubset [Fintype V] [DecidableEq V]
  {u : Set V} {v : V} (hv : v ∈ u) (h : G.IsClique u) (uOdd : Odd (u.ncard)) : (oddCliqueAlmostMatches hv h uOdd).choose.verts ⊆ u := by
  intro x hx
  rw [← (oddCliqueAlmostMatches hv h uOdd).choose_spec.1]
  exact Set.subset_insert _ _ hx

lemma disjoint_pair (v w : V) (u : Set V) : Disjoint u {v , w} ↔ v ∉ u ∧ w ∉ u := by
  constructor
  · intro h
    exact ⟨ (Set.disjoint_right.mp h) (Set.mem_insert v {w}), (Set.disjoint_right.mp h) (Set.mem_insert_of_mem v rfl) ⟩
  · intro h
    intro s hsu hsvw
    simp only [Set.le_eq_subset, Set.bot_eq_empty] at *
    rw [@Set.subset_def] at hsvw
    rw [@Set.subset_empty_iff, @Set.eq_empty_iff_forall_not_mem]
    intro x hxs
    have := hsvw _ hxs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    cases this with
    | inl hl => exact h.1 (hsu (hl ▸ hxs))
    | inr hr => exact h.2 (hsu (hr ▸ hxs))

lemma ConnectedComponentSubsetVerts (H : Subgraph G) (c : ConnectedComponent H.coe) : (c.supp : Set V) ⊆ H.verts := by
  intro v hv
  exact Set.image_val_subset hv


lemma isNotClique_iff (G : SimpleGraph V) (u : Set V) : ¬G.IsClique u ↔ ∃ (v w : u), v ≠ w ∧ ¬ G.Adj v w := by
  constructor
  · rw [@isClique_iff_induce_eq]
    intro h
    by_contra! hc
    apply h
    ext v w
    rw [@top_adj]
    exact ⟨fun h' ↦ Adj.ne' (adj_symm (induce u G) h'), fun h' ↦ hc v w h' ⟩
  · rintro ⟨ v , ⟨ w , h ⟩ ⟩
    rw [SimpleGraph.isClique_iff]
    by_contra! hc
    exact h.2 (hc (Subtype.coe_prop v) (w.coe_prop) (Subtype.coe_ne_coe.mpr h.1))


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

lemma singleEdge_le_iff (hneq : v ≠ w) : singleEdge hneq ≤ G ↔ G.Adj v w := by
  constructor
  · intro h
    exact h <| .inl ⟨rfl, rfl⟩
  · intro hadj
    intro v' w' hvw'
    cases hvw' with
    | inl h1 =>
      exact (h1.1 ▸ h1.2 ▸ hadj)
    | inr h2 =>
      exact (h2.1 ▸ h2.2 ▸ hadj.symm)


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


-- In #14976
def Subgraph.symDiff (M : Subgraph G) (C : Subgraph G) : Subgraph G := {
  verts := M.verts ∪ C.verts,
  Adj := fun v w ↦ (¬ M.Adj v w ∧ C.Adj v w) ∨ (M.Adj v w ∧ ¬ C.Adj v w),
  adj_sub := by
    intro v w hvw
    cases hvw
    next h1 => simp only [h1.2, C.adj_sub]
    next h2 => simp only [h2.1, M.adj_sub]
  edge_vert := by
    intro v w hvw
    cases hvw
    next h1 =>
      right
      apply SimpleGraph.Subgraph.support_subset_verts
      exact C.mem_support.mpr ⟨w, h1.2⟩
    next h2 =>
      left
      apply SimpleGraph.Subgraph.support_subset_verts
      exact M.mem_support.mpr ⟨w, h2.1⟩
  symm := by
    intro v w hvw
    cases hvw
    next h1 =>
      left
      exact ⟨fun h ↦ h1.1 h.symm, h1.2.symm⟩
    next h2 =>
      right
      exact ⟨h2.1.symm, fun h ↦ h2.2 h.symm⟩
  }

-- In #14976
@[simp]
lemma Subgraph.symDiff_verts (M : Subgraph G) (C : Subgraph G) : (M.symDiff C).verts = M.verts ∪ C.verts := by rfl
-- In #14976
@[simp]
lemma Subgraph.symDiff_adj (M : Subgraph G) (C : Subgraph G) : (M.symDiff C).Adj v w = ((¬ M.Adj v w ∧ C.Adj v w) ∨ (M.Adj v w ∧ ¬ C.Adj v w)) := rfl
-- In #14976
lemma Subgraph.symDiff_adj_comm (M : Subgraph G) (C : Subgraph G) : (M.symDiff C).Adj v w = (C.symDiff M).Adj v w := by
  unfold symDiff
  simp
  tauto

-- In #14976
lemma Subgraph.symDiffSingletonAdj {M : Subgraph G} : (M.symDiff (G.singletonSubgraph u)).Adj v w = M.Adj v w := by
  unfold symDiff
  simp [singletonSubgraph_adj, Pi.bot_apply, eq_iff_iff, Prop.bot_eq_false]

lemma alternatingCycleSymDiffMatch {M : Subgraph G} {p : G.Walk u u} (hM : M.IsPerfectMatching)
    (hpc : p.IsCycle) (hpalt : p.IsAlternating M) : (M.symDiff p.toSubgraph).IsMatching := by
    intro v _
    --unused?
    have hv : v ∈ M.verts := hM.2 v
    obtain ⟨w, hw⟩ := hM.1 (hM.2 v)
    by_cases hc : p.toSubgraph.Adj v w
    · unfold Subgraph.symDiff
      dsimp at *
      obtain ⟨w', hw'⟩ := alternating_edge' p M hpalt hpc hw.1 hc
      use w'
      constructor
      · left
        exact ⟨hw'.1, hw'.2.1⟩
      · dsimp at *
        intro y hy
        cases hy with
        | inl hl => {
          -- obtain ⟨w'', hw''⟩ := alternating_edge p M hpalt hpc hw'.1 hw'.2.1
          push_neg at hw'
          have hc2 := cycle_two_neighbors p hpc (p.toSubgraph_Adj_mem_support hc)
          by_contra! hc'
          have hc3 : ({y, w, w'} : Set V).ncard = 3 := by
            rw [Set.ncard_eq_three]
            use y
            use w
            use w'
            simp only [ne_eq, and_true]
            push_neg
            refine ⟨?_, hc', hw'.2.2⟩
            intro hyw
            exact hl.1 (hyw ▸ hw.1)

          have : ({y, w, w'} : Set V) ⊆ p.toSubgraph.neighborSet v := by
            intro v' hv'
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv'
            unfold Subgraph.neighborSet
            rw [@Set.mem_setOf]
            cases hv' with
            | inl h1 => {
              rw [h1]
              exact hl.2
            }
            | inr h2 => {
              cases h2 with
              | inl h3 => {
                rw [h3]
                exact hc
              }
              | inr h4 => {
                rw [h4]
                exact hw'.2.1
              }
            }
          rw [@Set.ncard_eq_two] at hc2
          obtain ⟨x', y', hxy'⟩ := hc2
          have : ({y, w, w'} : Set V).ncard ≤ ({x', y'} : Set V).ncard := by
            refine Set.ncard_le_ncard ?_ (by
              simp only [Set.finite_singleton, Set.Finite.insert]
              )
            rw [← hxy'.2]
            exact this
          rw [hc3] at this
          rw [Set.ncard_pair hxy'.1] at this
          omega
        }
        | inr hr => {
          exfalso
          have := hw.2 _ hr.1
          rw [this] at hr
          exact hr.2 hc
        }
    · use w
      unfold Subgraph.symDiff at *
      dsimp at *
      constructor
      · right
        exact ⟨hw.1, hc⟩
      · intro y hy

        cases hy with
        | inl h1 => {
          obtain ⟨w', hw'⟩ := alternating_edge p M hpalt hpc h1.1 h1.2
          have := hw.2 _ hw'.1
          exact (hc (this ▸ hw'.2.1)).elim
        }
        | inr h2 => {
          apply hw.2
          exact h2.1
        }

def Subgraph.IsAlternating (B : Subgraph G) (M : Subgraph G) :=
  ∀ (v w w': V), w ≠ w' → B.Adj v w → B.Adj v w' → (M.Adj v w ↔ ¬ M.Adj v w')

lemma Subgraph.symDiffPerfectMatchingsAlternating {M1 : Subgraph G} {M2 : Subgraph G}
    (hM1 : M1.IsPerfectMatching) (hM2 : M2.IsPerfectMatching) : (M1.symDiff M2).IsAlternating M2 := by
  unfold Subgraph.IsAlternating
  intro v w w' hww' havw havw'
  unfold Subgraph.symDiff at *
  simp only [ne_eq] at *
  by_cases h : M2.Adj v w
  · simp only [h, true_iff]
    intro h'
    obtain ⟨w'', hw''⟩ := hM2.1 (hM2.2 v)
    have heq1 := hw''.2 w h
    have heq2 := hw''.2 w' h'
    apply hww'
    exact heq2.symm ▸ heq1
  · simp only [h, false_iff, not_not]
    cases havw with
    | inl hl => exact (h hl.2).elim
    | inr hr =>
      have hM1' : ¬M1.Adj v w' := by
        intro h1vw
        obtain ⟨w'', hw''⟩ := hM1.1 (hM1.2 v)
        have heq1 := hw''.2 w hr.1
        have heq2 := hw''.2 w' h1vw
        apply hww'
        exact heq2.symm ▸ heq1
      cases havw' with
      | inl h1 => exact h1.2
      | inr h2 => exact (hM1' h2.1).elim


lemma Subgraph.symDiffPerfectMatchingsCard {M1 : Subgraph G} {M2 : Subgraph G}
    (hM1 : M1.IsPerfectMatching) (hM2 : M2.IsPerfectMatching) (v : V) : ((M1.symDiff M2).neighborSet v) = ∅ ∨ ((M1.symDiff M2).neighborSet v).ncard = 2 := by
  obtain ⟨w1, hw1⟩ := hM1.1 (hM1.2 v)
  obtain ⟨w2, hw2⟩ := hM2.1 (hM2.2 v)
  unfold Subgraph.symDiff
  unfold Subgraph.neighborSet
  by_cases h : w1 = w2
  · left
    simp only
    rw [@Set.eq_empty_iff_forall_not_mem]
    intro v'
    simp only [Set.mem_setOf_eq, not_or, not_and, not_not]
    constructor
    · intro h1nvv' h2vv'
      have := hw2.2 _ h2vv'
      rw [this, ← h] at h1nvv'
      exact h1nvv' hw1.1
    · intro h1vv'
      have := hw1.2 _ h1vv'
      exact this ▸ h ▸ hw2.1
  · right
    simp only
    rw [@Set.ncard_eq_two]
    use w1
    use w2
    refine ⟨h, ?_⟩
    ext w'
    constructor
    · intro hw'
      simp only [Set.mem_setOf_eq] at hw'
      cases hw' with
      | inl hl =>
        have := hw2.2 _ hl.2
        rw [this]
        exact Set.mem_insert_of_mem w1 rfl
      | inr hr =>
        have := hw1.2 _ hr.1
        rw [this]
        exact Set.mem_insert w1 {w2}
    · intro hw'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw'
      simp only [Set.mem_setOf_eq]
      cases hw' with
      | inl hl =>
        right
        refine ⟨hl.symm ▸ hw1.1 , ?_⟩
        intro h2vw
        have := hw2.2 _ h2vw
        exact h (hl.symm ▸ this)
      | inr hr =>
        left
        refine ⟨?_, hr.symm ▸ hw2.1⟩
        intro h1vw
        exact h (hr ▸ (hw1.2 _ h1vw).symm)

def Subgraph.IsCycle (M : Subgraph G) := (∀ v ∈ M.support, (M.neighborSet v).ncard = 2) ∧ M.Connected

lemma Subgraph.alternating_edge (C : Subgraph G) (M : Subgraph G) (h : C.IsAlternating M)
    (hic : C.IsCycle) (hM : ¬ M.Adj v w) (hc : C.Adj v w)
    : ∃ w', M.Adj v w' ∧ C.Adj v w' ∧ w ≠ w' := by
    -- have hv : v ∈ p.support := Walk.toSubgraph_Adj_mem_support p hp
    have hn := hic.1 v (by rw [SimpleGraph.Subgraph.mem_support]; use w)
    rw [@Set.ncard_eq_two] at hn
    obtain ⟨x, y, hxy⟩ := hn
    by_cases hxw : x = w
    · use y
      have hpvy : C.Adj v y := by
        have : y ∈ ({x, y} : Set V) := by
          exact Set.mem_insert_of_mem x rfl
        rw [← hxy.2] at this
        exact this
      have := h _ _ _ (hxw ▸ hxy.1) hc hpvy
      rw [@iff_not_comm] at this
      have hMAdj : M.Adj v y := this.mpr hM
      exact ⟨hMAdj, hpvy, hxw ▸ hxy.1⟩
    · use x
      have hpvx : C.Adj v x := by
        have : x ∈ ({x, y} : Set V) := by
          exact Set.mem_insert x {y}
        rw [← hxy.2] at this
        exact this

      push_neg at hxw
      have := h _ _ _ hxw hpvx hc
      exact ⟨this.mpr hM, hpvx, hxw.symm⟩

lemma Subgraph.alternating_edge' (C : Subgraph G) (M : Subgraph G) (h : C.IsAlternating M)
    (hic : C.IsCycle) (hM : M.Adj v w) (hc : C.Adj v w)
    : ∃ w', ¬ M.Adj v w' ∧ C.Adj v w' ∧ w ≠ w' := by
    have hn := hic.1 v (by rw [SimpleGraph.Subgraph.mem_support]; use w)
    rw [@Set.ncard_eq_two] at hn
    obtain ⟨x, y, hxy⟩ := hn
    by_cases hxw : x = w
    · use y
      have hpvy : C.Adj v y := by
        have : y ∈ ({x, y} : Set V) := by
          exact Set.mem_insert_of_mem x rfl
        rw [← hxy.2] at this
        exact this
      have := (h _ _ _ (hxw ▸ hxy.1) hc hpvy).mp hM
      exact ⟨this, hpvy, hxw ▸ hxy.1⟩
    · use x
      have hpvx : C.Adj v x := by
        have : x ∈ ({x, y} : Set V) := by
          exact Set.mem_insert x {y}
        rw [← hxy.2] at this
        exact this
      push_neg at hxw
      have := h _ _ _ hxw hpvx hc
      rw [@iff_not_comm] at this
      exact ⟨this.mp hM, hpvx, hxw.symm⟩

lemma alternatingCycleSymDiffMatch' {M : Subgraph G} {C : Subgraph G} (hM : M.IsPerfectMatching)
    (hic : C.IsCycle) (halt : C.IsAlternating M) : (M.symDiff C).IsMatching := by
    intro v _

    --unused?
    have hv : v ∈ M.verts := hM.2 v
    obtain ⟨w, hw⟩ := hM.1 (hM.2 v)
    by_cases hc : C.Adj v w
    · --unfold Subgraph.symDiff
      dsimp at *
      obtain ⟨w', hw'⟩ := Subgraph.alternating_edge' C M halt hic hw.1 hc
      use w'
      constructor
      · left
        exact ⟨hw'.1, hw'.2.1⟩
      · dsimp at *
        intro y hy
        cases hy with
        | inl hl => {
          -- obtain ⟨w'', hw''⟩ := alternating_edge p M hpalt hpc hw'.1 hw'.2.1
          push_neg at hw'
          have hc2 := hic.1 v ((by rw [SimpleGraph.Subgraph.mem_support]; use w))
          by_contra! hc'
          have hc3 : ({y, w, w'} : Set V).ncard = 3 := by
            rw [Set.ncard_eq_three]
            use y
            use w
            use w'
            simp only [ne_eq, and_true]
            push_neg
            refine ⟨?_, hc', hw'.2.2⟩
            intro hyw
            exact hl.1 (hyw ▸ hw.1)

          have : ({y, w, w'} : Set V) ⊆ C.neighborSet v := by
            intro v' hv'
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv'
            unfold Subgraph.neighborSet
            rw [@Set.mem_setOf]
            cases hv' with
            | inl h1 => {
              rw [h1]
              exact hl.2
            }
            | inr h2 => {
              cases h2 with
              | inl h3 => {
                rw [h3]
                exact hc
              }
              | inr h4 => {
                rw [h4]
                exact hw'.2.1
              }
            }
          rw [@Set.ncard_eq_two] at hc2
          obtain ⟨x', y', hxy'⟩ := hc2
          have : ({y, w, w'} : Set V).ncard ≤ ({x', y'} : Set V).ncard := by
            refine Set.ncard_le_ncard ?_ (by
              simp only [Set.finite_singleton, Set.Finite.insert]
              )
            rw [← hxy'.2]
            exact this
          rw [hc3] at this
          rw [Set.ncard_pair hxy'.1] at this
          omega
        }
        | inr hr => {
          exfalso
          have := hw.2 _ hr.1
          rw [this] at hr
          exact hr.2 hc
        }
    · use w
      unfold Subgraph.symDiff at *
      dsimp at *
      constructor
      · right
        exact ⟨hw.1, hc⟩
      · intro y hy

        cases hy with
        | inl h1 => {
          obtain ⟨w', hw'⟩ := Subgraph.alternating_edge C M halt hic h1.1 h1.2
          have := hw.2 _ hw'.1
          exact (hc (this ▸ hw'.2.1)).elim
        }
        | inr h2 => {
          apply hw.2
          exact h2.1
        }

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


lemma Set.triple_ncard_two {x y z : V} (h : ({x, y, z} : Set V).ncard ≤ 2) : x = y ∨ x = z ∨ y = z := by
  by_contra! hc
  have := Set.ncard_eq_three.mpr ⟨x, y, z, hc.1, hc.2.1, hc.2.2, rfl⟩
  omega



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

lemma pair_subset_pair {v w x y : V} (h : v ≠ w) (h3 : ({v , w} : Set V) ⊆ {x, y}) : ({v, w} : Set V) = {x, y} := by
  rw [@Set.Subset.antisymm_iff]
  refine ⟨h3, ?_⟩
  have h4 := Set.nontrivial_pair h
  have : ({v, w} : Set V).Nonempty := by
    simp only [Set.insert_nonempty]
  rw [Set.Nonempty.subset_pair_iff_eq this] at h3
  simp [@Set.Nontrivial.ne_singleton _ _ x h4, @Set.Nontrivial.ne_singleton _ _ y h4] at h3
  exact Eq.subset (Eq.symm h3)


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
  rw [List.getElem?_reverse (by rw [support_length]; omega),
    List.getElem?_reverse (by rw [support_length]; omega)]
  rw [← getVert_support_getElem? _ (by rw [support_length]; omega)]
  rw [← getVert_support_getElem? _ (by rw [support_length]; omega)]
  simp only [length_support, add_tsub_cancel_right, Option.some.injEq]
  by_cases hj' : j = p.length
  · simp only [hj', le_add_iff_nonneg_right, zero_le, tsub_eq_zero_of_le, getVert_zero]
    exact hp.getVert_internal_neq_endpoint (by omega) (by omega)
  · by_cases hj'' : j = p.length - 1
    · simp only [hj'', (by omega : p.length - (p.length - 1 + 1) = 0), getVert_zero]
      exact hp.getVert_internal_neq_endpoint (by omega) (by omega)
    · exact (hp.getVert_nodup' (by omega) (by omega) (by omega)).symm


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


@[simps]
def Subgraph.ofFunction {u : Set V} (f : V → V) (h : ∀ v ∈ u, G.Adj v (f v)) : Subgraph G where
  verts := u ∪ f '' u
  Adj v w := v ∈ u ∧ f v = w ∨ w ∈ u ∧ f w = v
  adj_sub := by
    intro v w' hvw'
    cases' hvw' with hv hw'
    · rw [← hv.2]
      exact h v hv.1
    · rw [← hw'.2]
      exact (h w' hw'.1).symm
  edge_vert := by
    intro v w hvw'
    cases' hvw' with hv hw'
    · left; exact hv.1
    · right; rw [← hw'.2]
      exact Set.mem_image_of_mem f hw'.1

lemma Subgraph.isMatching_ofFunction {u : Set V} (f : V → V) (h : ∀ v ∈ u, G.Adj v (f v))
    (hinj : u.InjOn f) (hd : Disjoint u (f '' u)) : (Subgraph.ofFunction f h).IsMatching := by
  rw [@Set.disjoint_right] at hd
  intro v hv
  simp only [ofFunction_adj]
  cases' hv with hl hr
  · use f v
    simp only [and_true]
    refine ⟨.inl hl, ?_⟩
    intro y hy
    cases' hy with h1 h2
    · exact h1.2.symm
    · exfalso
      exact hd (by rw [Set.mem_image]; use y) hl
  · rw [Set.mem_image] at hr
    obtain ⟨w, hw⟩ := hr
    use w
    dsimp
    refine ⟨.inr hw, ?_⟩
    intro y hy
    cases' hy with h1 h2
    · exfalso
      exact hd (by rw [Set.mem_image]; use w) h1.1
    · exact hinj h2.1 hw.1 (h2.2 ▸ hw.2.symm)

lemma ConnectedComponent.exists_vert (c : ConnectedComponent G) : ∃ v, G.connectedComponentMk v = c := c.exists_rep


theorem tutte_part' [Fintype V] [Inhabited V] [DecidableEq V] [DecidableRel G.Adj]
  (hveven : Even (Fintype.card V))
  (h : {c : ((⊤ : Subgraph G).deleteVerts {v : V | ∀ w, v ≠ w → G.Adj w v}).coe.ConnectedComponent | Odd (c.supp.ncard)}.ncard ≤ {v : V | ∀ w, v ≠ w → G.Adj w v}.ncard)
  (h' : ∀ (K : ((⊤ : Subgraph G).deleteVerts {v : V | ∀ w, v ≠ w → G.Adj w v}).coe.ConnectedComponent),
  (((⊤ : Subgraph G).deleteVerts {v | ∀ w, v ≠ w → G.Adj w v}).coe.IsClique K.supp)) :
    ∃ (M : Subgraph G), M.IsPerfectMatching := by
  classical
  let S := {v : V | ∀ w, v ≠ w → G.Adj w v}
  let Gsplit := ((⊤ : Subgraph G).deleteVerts {v | ∀ w, v ≠ w → G.Adj w v})
  simp only [← Set.Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at h

  have ⟨ f , hf ⟩ := Classical.inhabited_of_nonempty (Function.Embedding.nonempty_of_card_le h)
  let rep := fun (c : ConnectedComponent Gsplit.coe) => c.exists_vert.choose
  let oddVerts := Subtype.val '' (rep '' {(c : ConnectedComponent Gsplit.coe) | Odd (c.supp.ncard)})
  have oddVertMemSplit {v : V} (h : v ∈ oddVerts) : v ∈ Gsplit.verts := by
    rw [Set.mem_image] at h
    obtain ⟨v, heq⟩ := h
    rw [← heq.2]
    exact v.2
  have oddVertOddComp {v : V} (h : v ∈ oddVerts) : Odd (Fintype.card (Gsplit.coe.connectedComponentMk ⟨v, oddVertMemSplit h⟩).supp) := by
    rw [Set.mem_image] at h
    simp_rw [Set.mem_image] at h
    obtain ⟨w, hw⟩ := h
    obtain ⟨c, hc⟩ := hw.1
    rw [@Set.mem_setOf] at hc
    have : Gsplit.coe.connectedComponentMk w = c := by
      rw [← hc.2]
      exact c.exists_vert.choose_spec
    rw [(SetCoe.ext hw.2.symm : ⟨v, oddVertMemSplit h⟩ = w)]
    rw [this]
    simpa [← Set.Nat.card_coe_set_eq, Nat.card_eq_fintype_card] using hc.1

  let g : V → V := fun v ↦ if h : v ∈ oddVerts then f ⟨(Gsplit.coe.connectedComponentMk ⟨v, oddVertMemSplit h⟩), oddVertOddComp h⟩ else Classical.arbitrary V

  have oddVertNotInS {v : V} (h : v ∈ oddVerts) : v ∉ S := by
    rw [Set.mem_image] at h
    simp_rw [Set.mem_image] at h
    obtain ⟨w, hw⟩ := h
    obtain ⟨c, hc⟩ := hw.1
    rw [← hw.2]
    rw [← hc.2]
    exact deleteVerts_verts_notmem_deleted (rep c)

  have gMemS {v : V} (h : v ∈ oddVerts) : (g v) ∈ S := by
    unfold_let g
    dsimp
    split_ifs
    apply Subtype.coe_prop

  have hdg : Disjoint oddVerts (g '' oddVerts) := by
    rw [@Set.disjoint_left]
    intro v hv hgv
    apply oddVertNotInS hv
    rw [Set.mem_image] at hgv
    obtain ⟨v', hv'⟩ := hgv
    rw [← hv'.2]
    exact gMemS hv'.1

  have aux {x : V} {cx : Gsplit.coe.ConnectedComponent} (h : (Subtype.val ∘ rep) cx = x) (hx : x ∈ Gsplit.verts): Gsplit.coe.connectedComponentMk ⟨x, hx⟩ = cx := by
    rw [← @ConnectedComponent.mem_supp_iff]
    simp only [Function.comp_apply] at h
    unfold_let rep at h
    have := cx.exists_vert.choose_spec
    rw [← this]
    simp only at h
    subst h
    simp only [Subtype.coe_eta, ConnectedComponent.mem_supp_iff]

  have compInj : Function.Injective (fun (v : oddVerts) => (Gsplit.coe.connectedComponentMk ⟨v.1, oddVertMemSplit v.2⟩)) := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    dsimp at *
    have hx' := oddVertMemSplit hx
    have hy' := oddVertMemSplit hy
    unfold_let oddVerts at hx hy
    rw [← Set.image_comp, Set.mem_image] at hx hy
    obtain ⟨cx, hcx⟩ := hx
    obtain ⟨cy, hcy⟩ := hy
    rw [@Subtype.mk_eq_mk]
    rw [aux hcx.2 hx'] at hxy
    rw [aux hcy.2 hy'] at hxy
    rw [← hcx.2, ← hcy.2]
    rw [hxy]

  have gInjOn : Set.InjOn g oddVerts := by
    unfold_let g
    dsimp
    rw [@Set.injOn_iff_injective]
    rw [@Set.restrict_dite]
    intro x y hxy
    simp only at hxy
    have := hf <| Subtype.val_injective hxy

    rw [Subtype.mk.injEq] at this
    exact compInj this

  have hadj : ∀ v ∈ oddVerts, G.Adj v (g v) := by
    intro v hv
    have := gMemS hv
    unfold_let S at this
    rw [@Set.mem_setOf] at this
    apply this v
    intro h
    apply oddVertNotInS hv
    exact (h ▸ gMemS hv)

  let M1 : Subgraph G := Subgraph.ofFunction g hadj

  have hM1 : M1.IsMatching := by
    unfold_let M1
    exact Subgraph.isMatching_ofFunction g hadj gInjOn hdg

  have memImKNotS {v : V} (K : ((⊤ : Subgraph G).deleteVerts {v : V | ∀ w, v ≠ w → G.Adj w v}).coe.ConnectedComponent)
    (h : v ∈ Subtype.val '' K.supp) : v ∉ S := by
    unfold_let S
    intro hv
    rw [Set.mem_image] at h
    obtain ⟨v', hv'⟩ := h
    have := v'.2
    simp only [Subgraph.induce_verts, Subgraph.verts_top, Set.mem_diff] at this
    rw [hv'.2] at this
    exact this.2 hv

  have evenKsubM1 (K : ((⊤ : Subgraph G).deleteVerts {v : V | ∀ w, v ≠ w → G.Adj w v}).coe.ConnectedComponent)
    : Even ((Subtype.val '' K.supp) \ M1.verts).ncard := by
    by_cases h : Even (Subtype.val '' K.supp).ncard
    · have : Subtype.val '' K.supp \ M1.verts = Subtype.val '' K.supp := by
        unfold_let M1
        unfold_let oddVerts
        unfold_let rep
        ext v
        refine ⟨fun hv ↦ hv.1, ?_⟩
        intro hv
        apply Set.mem_diff_of_mem hv
        intro hv'
        simp only [Subgraph.ofFunction_verts, Set.mem_union, Set.mem_image,
          Set.mem_setOf_eq, exists_exists_and_eq_and] at hv'
        cases' hv' with hl hr
        · obtain ⟨a, ha⟩ := hl
          have hc1 := a.exists_vert.choose_spec
          rw [← ha.2] at hv
          rw [← hc1] at hv
          rw [Subtype.val_injective.mem_set_image] at hv
          rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hv
          rw [Nat.odd_iff_not_even] at ha
          apply ha.1
          have hc2 := (Gsplit.coe.connectedComponentMk (a.exists_vert).choose).exists_vert.choose_spec
          rw [← hc1]
          rw [← hc2]

          unfold_let Gsplit
          rw [← hv] at h
          rw [Set.ncard_image_of_injective _ Subtype.val_injective] at h
          exact h

        · obtain ⟨a, ha⟩ := hr
          rw [← ha.2] at hv
          have : a.exists_vert.choose.val ∈ oddVerts := by
            unfold_let oddVerts
            rw [Set.mem_image]
            simp_rw [Set.mem_image]
            unfold_let rep
            use a.exists_vert.choose
            refine ⟨?_, rfl⟩
            use a
            exact ⟨ha.1, rfl⟩
          have := gMemS this
          apply memImKNotS _ hv
          exact this
      rw [this]
      exact h
    · 
      sorry

  sorry

theorem tutte_part [Fintype V] [Inhabited V] [DecidableEq V] [DecidableRel G.Adj]
  (hvOdd : Even (Finset.univ : Finset V).card)
  (h : Nat.card ↑{c : ((⊤ : Subgraph G).deleteVerts {v : V | ∀ w, v ≠ w → G.Adj w v}).coe.ConnectedComponent | Odd (c.supp.ncard)} ≤ {v : V | ∀ w, v ≠ w → G.Adj w v}.ncard)
  (h' : ∀ (K : ((⊤ : Subgraph G).deleteVerts {v : V | ∀ w, v ≠ w → G.Adj w v}).coe.ConnectedComponent),
  (((⊤ : Subgraph G).deleteVerts {v | ∀ w, v ≠ w → G.Adj w v}).coe.IsClique K.supp)) :
    ∃ (M : Subgraph G), M.IsPerfectMatching := by
  let S := {v : V | ∀ w, v ≠ w → G.Adj w v}
  haveI : Fintype ↑{ (c : ConnectedComponent ((⊤ : Subgraph G).deleteVerts {v : V | ∀ w, v ≠ w → G.Adj w v}).coe) | ConnectedComponent.isOdd c} := Fintype.ofFinite _
  rw [← Set.Nat.card_coe_set_eq] at h
  rw [Nat.card_eq_fintype_card] at h
  rw [Nat.card_eq_fintype_card] at h

  have ⟨ f , hf ⟩ := Classical.inhabited_of_nonempty (Function.Embedding.nonempty_of_card_le h)
  let Gsplit := ((⊤ : Subgraph G).deleteVerts {v | ∀ w, v ≠ w → G.Adj w v})
  let f' := fun (c : {(c : ConnectedComponent Gsplit.coe) | Odd (c.supp.ncard)}) => (componentExistsRep c.val).choose
  have f'mem  (c : {(c : ConnectedComponent Gsplit.coe) | Odd (c.supp.ncard)}) : f' c ∈ c.val.supp := by
    simp only [Set.mem_setOf_eq, ConnectedComponent.mem_supp_iff]
    rw [← (componentExistsRep c.val).choose_spec]
  haveI hFin (s : Set V) : Fintype s := Fintype.ofFinite _
  let M1 : Subgraph G := (⨆ (c : {c : ConnectedComponent Gsplit.coe | Odd (c.supp.ncard)}),
    let v := f' c
    let M := (oddCliqueAlmostMatches (f'mem c) (h' c) c.2).choose

    SimpleGraph.Subgraph.coeSubgraph M ⊔ G.subgraphOfAdj ((by
      apply (f c).2
      intro hfcv
      apply Set.not_mem_diff_of_mem (f c).2
      rw [hfcv]
      exact Subtype.mem v
      ) : G.Adj v (f c) )
    )
  have hM1 : M1.IsMatching := by

    exact Subgraph.IsMatching.iSup (by
      intro i
      dsimp
      let oddMatches := oddCliqueAlmostMatches (f'mem i) (h' i) i.2

      exact Subgraph.IsMatching.sup (oddMatches.choose_spec).2.coeSubgraph (Subgraph.IsMatching.subgraphOfAdj _)
          (by
            rw [support_subgraphOfAdj, disjoint_pair]
            have := (f' i).2
            constructor
            · intro hf'i
              have := SimpleGraph.Subgraph.support_subset_verts _ hf'i
              rw [Subgraph.verts_coeSubgraph] at this
              obtain ⟨x, hx, hx'⟩ := this
              exact (oddCliqueAlmostMatchesDoesNotContainNode (f'mem i) (h' i) (i.2)) (Subtype.val_injective hx' ▸ hx)
            · intro hfi
              have := SimpleGraph.Subgraph.support_subset_verts _ hfi
              rw [Subgraph.verts_coeSubgraph] at this
              have := Set.image_val_subset this
              rw [SimpleGraph.Subgraph.deleteVerts_verts] at this
              apply ((Set.mem_diff _).mp this).2
              exact Subtype.coe_prop (f i)
            )
      ) (by

        intro i j hij s hs1 hs2
        have hi := oddCliqueAlmostMatchesSubset (f'mem i) (h' i) (i.2)
        have hj := oddCliqueAlmostMatchesSubset (f'mem j) (h' j) (j.2)
        simp only [Subgraph.induce_verts, Subgraph.verts_top, Set.coe_setOf, ne_eq,
          Set.mem_setOf_eq, Set.le_eq_subset, Set.bot_eq_empty] at *
        rw [sup_support_eq_support_union] at *
        rw [Set.subset_empty_iff]
        rw [Set.eq_empty_iff_forall_not_mem]
        intro v hv
        cases hs1 hv with
        | inl hl =>
          have hii := SimpleGraph.Subgraph.support_subset_verts _ hl
          rw [Subgraph.verts_coeSubgraph] at hii
          have hi' := hi (Set.mem_of_mem_image_val hii)
          cases hs2 hv with
          | inl hl' =>
            have := SimpleGraph.Subgraph.support_subset_verts _ hl'
            rw [Subgraph.verts_coeSubgraph] at this
            have hj' := hj (Set.mem_of_mem_image_val this)
            rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at *
            rw [hj'] at hi'
            apply hij
            exact Subtype.eq (id hi'.symm)
          | inr hr' =>
            rw [support_subgraphOfAdj] at hr'
            simp at hr'
            cases hr' with
            | inl h1 =>
              have hf'memj := f'mem j
              apply hij
              apply Subtype.val_injective
              rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at *

              have : ⟨ v , Set.image_val_subset hii ⟩ = f' j := by
                exact SetCoe.ext h1
              rw [this] at hi'
              rw [hf'memj] at hi'
              exact hi'.symm
            | inr h2 =>
              have := Set.image_val_subset hii
              rw [SimpleGraph.Subgraph.deleteVerts_verts] at this
              rw [h2] at this
              apply ((Set.mem_diff _).mp this).2
              exact Subtype.coe_prop (f j)
        | inr hr =>
          have hjj := SimpleGraph.Subgraph.support_subset_verts _ hr
          rw [@subgraphOfAdj_verts] at hjj
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hjj
          cases hs2 hv with
          | inl hl' =>
            have hii := SimpleGraph.Subgraph.support_subset_verts _ hl'
            rw [Subgraph.verts_coeSubgraph] at hii
            have hj' := hj (Set.mem_of_mem_image_val hii)
            cases hjj with
            | inl h1 =>
              have : ⟨ v , Set.image_val_subset hii ⟩ = f' i := by
                exact SetCoe.ext h1
              have hf'memi := f'mem i
              apply hij
              rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at *
              apply Subtype.val_injective
              rw [← hf'memi]
              rw [← hj']
              rw [this]
            | inr h2 =>
              have := Set.image_val_subset hii
              rw [SimpleGraph.Subgraph.deleteVerts_verts] at this
              apply ((Set.mem_diff _).mp this).2
              rw [h2]
              exact Subtype.coe_prop (f i)
          | inr hr' =>
            have hrr := SimpleGraph.Subgraph.support_subset_verts _ hr'
            rw [@subgraphOfAdj_verts] at hrr
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hrr
            cases hjj with
            | inl h1 =>
              cases hrr with
              | inl h1' =>
                have f'memi := f'mem i
                have f'memj := f'mem j
                rw [h1'] at h1
                apply hij
                rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at *
                have : f' j = f' i := by
                  exact SetCoe.ext h1
                rw [this] at f'memj
                rw [f'memj] at f'memi
                exact Subtype.eq (id f'memi.symm)
              | inr h2' =>
                have : (f' i : V) ∈ Gsplit.verts := by
                  exact Subtype.coe_prop (f' i)
                rw [← h1] at this
                rw [SimpleGraph.Subgraph.deleteVerts_verts] at this
                apply ((Set.mem_diff _).mp this).2
                have : (f j : V) ∈ S := by
                  exact Subtype.coe_prop (f j)
                exact Set.mem_of_eq_of_mem h2' this
            | inr h2 =>
              cases hrr with
              | inl h1' =>
                have : (f' j : V) ∈ Gsplit.verts := by
                  exact Subtype.coe_prop (f' j)
                rw [← h1'] at this
                rw [SimpleGraph.Subgraph.deleteVerts_verts] at this
                apply ((Set.mem_diff _).mp this).2
                have : (f i : V) ∈ S := by
                  exact Subtype.coe_prop (f i)
                exact Set.mem_of_eq_of_mem h2 this
              | inr h2' =>
                rw [h2'] at h2
                apply hij
                apply hf
                exact SetCoe.ext (id h2.symm)
        )

  let M2 : Subgraph G := (⨆ (c : {c : ConnectedComponent Gsplit.coe | (Even (c.supp.ncard))}),
    Subgraph.coeSubgraph ((isClique_even_iff_matches c.val.supp (Set.toFinite _) (h' c)).mp c.2).choose )

  have hM2 : M2.IsMatching := by

    exact Subgraph.IsMatching.iSup (by
      intro i
      exact ((isClique_even_iff_matches i.val.supp (Set.toFinite _) (h' i)).mp i.2).choose_spec.2.coeSubgraph
      ) (by
        intro i j hij s hsi hsj
        simp only [Subgraph.induce_verts, Subgraph.verts_top, Set.coe_setOf, ne_eq,
          Set.mem_setOf_eq, ConnectedComponent.mem_supp_iff, Subtype.forall, Set.le_eq_subset,
          Set.bot_eq_empty] at *
        let hispec := ((isClique_even_iff_matches i.val.supp (Set.toFinite _) (h' i)).mp i.2).choose_spec
        have hi := hispec.1

        let hjspec := ((isClique_even_iff_matches j.val.supp (Set.toFinite _) (h' j)).mp j.2).choose_spec
        have hj := hjspec.1

        rw [Set.subset_empty_iff]
        rw [Set.eq_empty_iff_forall_not_mem]
        intro v hv

        have hii := SimpleGraph.Subgraph.support_subset_verts _ (hsi hv)
        rw [Subgraph.verts_coeSubgraph] at hii
        have hi' := (subset_of_eq hi) (Set.mem_of_mem_image_val hii)

        have hjj := SimpleGraph.Subgraph.support_subset_verts _ (hsj hv)
        rw [Subgraph.verts_coeSubgraph] at hjj
        have hj' := (subset_of_eq hj) (Set.mem_of_mem_image_val hjj)
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at *
        rw [hj'] at hi'
        apply hij
        exact SetCoe.ext (id hi'.symm)
        )
  let oddComVerts := (⋃ (c : {c : ConnectedComponent Gsplit.coe | (Odd (Set.ncard (c.supp)))}),
      c.val.supp )
  have hM1sub : M1.verts ⊆ oddComVerts ∪ S := by
    intro v hv
    rw [@Subgraph.verts_iSup] at hv
    obtain ⟨ i , hi ⟩ := Set.mem_iUnion.mp hv
    rw [@Subgraph.verts_sup] at hi

    rw [Set.mem_union] at hi
    cases hi with
    | inl hl =>
      rw [Subgraph.verts_coeSubgraph] at hl
      rw [@Set.mem_union]
      left
      rw [@Set.mem_image] at *
      obtain ⟨ j , hj ⟩ := hl
      have hji := (oddCliqueAlmostMatchesSubset (f'mem i) (h' i) (i.2)) hj.1
      use ⟨ v , Set.image_val_subset ⟨ j , hj ⟩ ⟩
      refine ⟨ ?_ , rfl ⟩
      rw [@Set.mem_iUnion]
      use ⟨ i.1 , (by

        have := i.2
        rw [@Set.mem_setOf] at *
        simp only [Set.mem_setOf_eq] at this
        exact this
        ) ⟩
      simp only [Set.mem_setOf_eq, ConnectedComponent.mem_supp_iff]
      simp only [Set.mem_setOf_eq, ConnectedComponent.mem_supp_iff] at hji
      have : j = ⟨ v , Set.image_val_subset (Exists.intro j hj)⟩ := SetCoe.ext hj.2

      rw [← this]
      exact hji

    | inr hr =>
      simp at hr
      rw [@Set.mem_union]
      cases hr with
      | inl h1 =>
        have := f'mem i
        rw [h1]
        left
        apply Set.mem_image_of_mem
        rw [@Set.mem_iUnion]
        use ⟨ i.1 , (by
          have := i.2
          rw [@Set.mem_setOf] at *
          simp only [Set.mem_setOf_eq] at this
          exact this
          ) ⟩
      | inr h2 =>
        right
        rw [h2]
        exact Subtype.coe_prop (f i)

  let evenComVerts := (⋃ (c : {c : ConnectedComponent Gsplit.coe | (Even (c.supp.ncard))}),
      c.val.supp )
  have hM2sub : M2.verts ⊆ evenComVerts := by
    intro v hv
    rw [@Subgraph.verts_iSup] at hv
    obtain ⟨ i , hi ⟩ := Set.mem_iUnion.mp hv
    have hi' := hi
    rw [Subgraph.verts_coeSubgraph] at hi
    rw [Set.mem_image] at *

    obtain ⟨ x , hx ⟩ := hi
    use ⟨ x , Subtype.coe_prop x ⟩
    constructor
    · rw [Set.mem_iUnion]
      use i
      rw [← ((isClique_even_iff_matches i.val.supp (Set.toFinite _) (h' i)).mp i.2).choose_spec.1]
      rw [Subtype.eta]
      exact hx.1
    · rw [Subtype.eta]
      exact hx.2
  have hM2sub' : (evenComVerts : Set V) ⊆ M2.verts := by
    intro v hv
    rw [@Subgraph.verts_iSup]
    rw [Set.mem_iUnion]
    rw [Set.mem_image] at hv
    obtain ⟨ v' , hv' ⟩ := hv
    rw [Set.mem_iUnion] at hv'
    obtain ⟨ i' , hi' ⟩ := hv'.1
    use i'
    rw [Subgraph.verts_coeSubgraph]

    have := ((isClique_even_iff_matches (i'.1).supp (Set.toFinite _) (h' i'.1)).mp i'.2).choose_spec
    rw [this.1]
    rw [← hv'.2]
    exact Set.mem_image_of_mem Subtype.val hi'

  have hM1sub' : (oddComVerts : Set V) ⊆ M1.verts := by
    intro v hv
    rw [@Subgraph.verts_iSup]
    rw [Set.mem_iUnion]
    rw [Set.mem_image] at hv
    obtain ⟨ v' , hv' ⟩ := hv
    rw [Set.mem_iUnion] at hv'
    obtain ⟨ i' , hi' ⟩ := hv'.1
    let i'' : Set.Elem {c : ConnectedComponent Gsplit.coe | Odd (c.supp.ncard)} := ⟨ i', by
      simp only [Set.mem_setOf_eq]
      -- rw [ConnectedComponent.isOdd_iff]
      have := i'.2
      rw [@Set.mem_setOf] at this
      exact this
      ⟩
    use i''
    rw [Subgraph.verts_sup]
    rw [Set.mem_union]
    rw [Subgraph.verts_coeSubgraph]
    have := (oddCliqueAlmostMatches (f'mem i'') (h' i''.1) (i''.2)).choose_spec
    rw [← hv'.2]
    rw [← this.1] at hi'
    rw [Set.mem_insert_iff ] at hi'
    cases hi' with
    | inl hl =>
      right
      simp only [subgraphOfAdj_verts, Set.mem_insert_iff, Set.mem_singleton_iff]
      left
      exact congrArg Subtype.val hl
    | inr hr =>
      left
      exact Set.mem_image_of_mem Subtype.val hr


  have hM12 : (M1 ⊔ M2).IsMatching := by

    refine Subgraph.IsMatching.sup hM1 hM2 ?hd
    intro s h1 h2
    simp only [Subgraph.induce_verts, Subgraph.verts_top, Set.coe_setOf, ne_eq,
      Set.mem_setOf_eq, ConnectedComponent.mem_supp_iff, Subtype.forall, Set.le_eq_subset,
      Set.bot_eq_empty] at *
    rw [SimpleGraph.Subgraph.IsMatching.support_eq_verts hM1] at h1
    rw [SimpleGraph.Subgraph.IsMatching.support_eq_verts hM2] at h2
    rw [Set.subset_empty_iff]
    rw [Set.eq_empty_iff_forall_not_mem]
    intro x hx
    have hx1 := hM1sub (h1 hx)
    have hx2 := hM2sub (h2 hx)
    rw [Set.mem_image] at hx2
    obtain ⟨ v , hv ⟩ := hx2
    have := hv.1
    rw [Set.mem_iUnion] at this
    obtain ⟨ i , hi ⟩ := this
    rw [Set.mem_union] at hx1
    rw [Set.mem_image] at hx1
    cases hx1 with
    | inl hl =>
      obtain ⟨ w , hw ⟩ := hl
      rw [Set.mem_iUnion] at hw
      obtain ⟨ j , hj ⟩ := hw.1
      rw [← hw.2] at hv
      have := Subtype.val_injective hv.2
      rw [this] at hi
      rw [@ConnectedComponent.mem_supp_iff] at *
      rw [hj] at hi

      have hj' := j.2
      have hi' := i.2
      rw [hi] at hj'
      simp only [Set.mem_setOf_eq, Nat.odd_iff_not_even] at *
      exact hj' hi'
    | inr hr =>
      have memhi := Set.mem_image_of_mem Subtype.val hi
      have := v.2
      rw [hv.2] at this
      rw [SimpleGraph.Subgraph.deleteVerts_verts] at this
      exact ((Set.mem_diff _).mp this).2 hr

  have hM12Even : Even ((M1 ⊔ M2).verts.ncard) := by

    have := SimpleGraph.Subgraph.IsMatching.even_card hM12
    rw [Set.ncard_eq_toFinset_card' ]
    exact this

  have hnM12Even : Even (((Set.univ : Set V) \ (M1 ⊔ M2).verts : Set V).ncard) := by
    rw [Set.ncard_diff (by exact fun ⦃a⦄ a => trivial)]
    exact (Nat.even_sub (by
      apply Set.ncard_le_ncard
      exact fun ⦃a⦄ a => trivial
      exact Set.finite_univ
      )).mpr (by
        constructor
        · intro _
          exact hM12Even
        · intro _
          rw [← Finset.coe_univ]
          rwa [@Set.ncard_coe_Finset]
          )


  obtain ⟨ M' , hM' ⟩ := (isClique_even_iff_matches ((Set.univ : Set V) \ (M1 ⊔ M2).verts) (Set.toFinite _) (by

    intro v hv w hw hvw
    have : v ∈ S := by
      by_contra hc
      let v' : Gsplit.verts := ⟨ v , (by
        rw [SimpleGraph.Subgraph.deleteVerts_verts ]
        rw [Set.mem_diff]
        exact ⟨ by trivial , hc ⟩
        ) ⟩
      if heven : Even ((Gsplit.coe.connectedComponentMk v').supp.ncard)
      then

        have : (v' : V) ∈ M2.verts := by
          apply hM2sub'
          rw [Set.mem_image]
          use ⟨ v' , Subtype.mem v' ⟩
          constructor
          · rw [Set.mem_iUnion]
            use ⟨ Gsplit.coe.connectedComponentMk v', heven ⟩
            simp only [Subtype.coe_eta, ConnectedComponent.mem_supp_iff]
          · simp only
        rw [@Set.mem_diff] at hv
        rw [@Subgraph.verts_sup] at hv
        rw [@Set.mem_union] at hv
        apply hv.2
        right
        exact this
      else
        rw [← @Nat.odd_iff_not_even] at heven
        have : (v' : V) ∈ M1.verts := by

          apply hM1sub'
          rw [Set.mem_image]
          use ⟨ v' , Subtype.mem v' ⟩
          constructor
          · rw [Set.mem_iUnion]
            use ⟨ Gsplit.coe.connectedComponentMk v', heven ⟩
            simp only [Subtype.coe_eta, ConnectedComponent.mem_supp_iff]
          · simp only
        rw [@Set.mem_diff] at hv
        rw [@Subgraph.verts_sup] at hv
        rw [@Set.mem_union] at hv
        apply hv.2
        left
        exact this

    have := Set.mem_setOf.mp this
    exact (this w hvw).symm
      : G.IsClique ((Set.univ : Set V) \ (M1 ⊔ M2).verts) )).mp hnM12Even
  have conMatch : ((M1 ⊔ M2) ⊔ M').IsMatching := Subgraph.IsMatching.sup hM12 hM'.2 (by
      rw [SimpleGraph.Subgraph.IsMatching.support_eq_verts hM'.2]
      rw [hM'.1]
      rw [SimpleGraph.Subgraph.IsMatching.support_eq_verts hM12]
      exact Set.disjoint_sdiff_right
      )

  have conSpanning : ((M1 ⊔ M2) ⊔ M').IsSpanning := by
    intro v
    if h : v ∈ (M1 ⊔ M2).verts then
      rw [@Subgraph.verts_sup]
      rw [Set.mem_union]
      exact .inl h
    else
      rw [@Subgraph.verts_sup]
      rw [Set.mem_union]
      right
      rw [hM'.1]
      exact Set.mem_diff_of_mem (by trivial) h
  use ((M1 ⊔ M2) ⊔ M')
  exact ⟨conMatch, conSpanning⟩


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

      let Gmax := maximalWithoutMatching h


      suffices ∃ u, Set.ncard u < cardOddComponents ((⊤ : Subgraph Gmax.G').deleteVerts u).coe by
        · obtain ⟨u, hu ⟩ := this
          use u
          exact lt_of_lt_of_le hu (by
            haveI : DecidableRel Gmax.G'.Adj := Classical.decRel _
            exact oddComponentsIncrease G Gmax.G' Gmax.hSubgraph u
            )

      let S : Set V := {v | ∀ w, v ≠ w → Gmax.G'.Adj w v}

      let Gsplit := ((⊤ : Subgraph Gmax.G').deleteVerts S)


      by_contra! hc

      have h' := hc S
      unfold cardOddComponents at h'
      haveI := Gmax.hDec
      haveI : Fintype ↑{ (c : ConnectedComponent ((⊤ : Subgraph Gmax.G').deleteVerts S).coe) | ConnectedComponent.isOdd c} := Fintype.ofFinite _
      rw [@Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card'] at h'
      rw [Set.toFinset_card, Set.toFinset_card] at h'
      let h'' := h'

      if h' : ∀ (K : ConnectedComponent Gsplit.coe), Gsplit.coe.IsClique K.supp
      then
        rw [← @Nat.even_iff_not_odd] at hvOdd
        rw [Fintype.card_eq_nat_card] at h''

        simp_rw [ConnectedComponent.isOdd_iff, Fintype.card_eq_nat_card, Set.Nat.card_coe_set_eq] at h''
        rw [← Set.Nat.card_coe_set_eq] at h''
        obtain ⟨M, hM⟩ := tutte_part hvOdd h'' h'
        exact Gmax.hMatchFree M hM
    else
      push_neg at h'
      obtain ⟨K, hK⟩ := h'
      rw [isNotClique_iff] at hK
      obtain ⟨x, ⟨y, hxy⟩⟩ := hK


      obtain ⟨p , hp⟩ := SimpleGraph.Reachable.exists_path_of_dist (reachable_in_connected_component_induce K x y)


      obtain ⟨x, ⟨a, ⟨b, hxab⟩⟩⟩ := verts_of_walk p hp.2 (dist_gt_one_of_ne_and_nadj (Walk.reachable p) hxy.1 hxy.2)

      have ha : (a : V) ∉ S := by exact deleteVerts_verts_notmem_deleted _
      have hc : ∃ (c : V), ¬ Gmax.G'.Adj a c ∧ (a : V) ≠ c := by

        have : ¬ ∀ (w : V), (a : V) ≠ w → Gmax.G'.Adj (w : V) a := by exact ha
        push_neg at this
        obtain ⟨c, hc⟩ := this
        use c
        constructor
        · intro h
          exact hc.2 (adj_symm Gmax.G' h)
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

      let G1 := Gmax.G' ⊔ (singleEdge <| Subtype.coe_ne_coe.mpr <| Subtype.coe_ne_coe.mpr hxab.2.2.2)
      let G2 := Gmax.G' ⊔ (singleEdge hc.2)

      have hG1nxb : ¬ Gmax.G'.Adj x.val.val b.val.val := by

        intro h
        apply hxab.2.2.1
        rw [@induce_eq_coe_induce_top]
        simp only [Subgraph.coe_adj, Subgraph.induce_verts, Subgraph.induce_adj, Subgraph.top_adj]
        refine ⟨Subtype.coe_prop x, Subtype.coe_prop b, ?_⟩
        rw [@Subgraph.deleteVerts_adj]
        simp only [Subgraph.verts_top, Set.mem_univ, deleteVerts_verts_notmem_deleted,
          not_false_eq_true, Subgraph.top_adj, h, and_self]

      have hG1 : Gmax.G' < G1 := by

        apply union_gt_iff.mpr
        rw [@singleEdge_le_iff]
        exact hG1nxb

      have hG2 : Gmax.G' < G2 := by

        apply union_gt_iff.mpr
        rw [@singleEdge_le_iff]
        intro h
        exact hc.1 h

      obtain ⟨M1, hM1⟩ := not_forall_not.mp (Gmax.hMaximal _ hG1)
      obtain ⟨M2, hM2⟩ := not_forall_not.mp (Gmax.hMaximal _ hG2)

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
        exact Gmax.hMatchFree Mcon hMcon

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
        exact Gmax.hMatchFree Mcon hMcon

      let G12 := Gmax.G' ⊔ (singleEdge <| Subtype.coe_ne_coe.mpr <| Subtype.coe_ne_coe.mpr hxab.2.2.2) ⊔ (singleEdge hc.2)

      have hG1leG12 : G1 ≤ G12 := SemilatticeSup.le_sup_left G1 (singleEdge hc.right)
      have hG2leG12 : G2 ≤ G12 := by
        have : G12 = Gmax.G' ⊔ (singleEdge hc.2) ⊔ (singleEdge <| Subtype.coe_ne_coe.mpr <| Subtype.coe_ne_coe.mpr hxab.2.2.2) := by
          exact
            sup_right_comm Gmax.G'
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
          apply Gmax.hMatchFree Mrealcon
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

        have hGsplitadjax : Gmax.G'.Adj ↑↑a ↑↑x := by

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
        apply Gmax.hMatchFree Mrealcon
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
