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

/-- This is `Quot.recOn` specialized to connected components.
For convenience, it strengthens the assumptions in the hypothesis
to provide a path between the vertices. -/
@[elab_as_elim]
def ConnectedComponent.recOn
    {motive : G.ConnectedComponent → Sort*}
    (c : G.ConnectedComponent)
    (f : (v : V) → motive (G.connectedComponentMk v))
    (h : ∀ (u v : V) (p : G.Walk u v) (_ : p.IsPath),
      ConnectedComponent.sound p.reachable ▸ f u = f v) :
    motive c :=
  Quot.recOn c f (fun u v r => r.elim_path fun p => h u v p p.2)

instance [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (c : G.ConnectedComponent) (v : V) : Decidable (v ∈ c.supp) :=
  c.recOn
    (fun w => by simp only [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]; infer_instance)
    (fun _ _ _ _ => Subsingleton.elim _ _)


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

instance myInst2 [r : DecidableRel G.Adj] : DecidableRel (Subgraph.coe (⊤ : Subgraph G)).Adj := by
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
      apply (Subgraph.coe_adj_sub _ _ _ _)
      exact h
    )
  }

instance myInst [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (u : ConnectedComponent G) :
    Fintype u.supp := inferInstance


lemma SimpleGraph.PerfectMatchingInducesMatchingOnComponent [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
  (M : Subgraph G) (hM : Subgraph.IsPerfectMatching M) (c : ConnectedComponent G) : (Subgraph.IsMatching (M.induce c.supp)) := by
    intro v hv
    have vM : v ∈ M.verts := by
      apply hM.2
    have h := hM.1 vM
    obtain ⟨ w, hw ⟩ := h
    use w
    dsimp at *
    constructor
    · constructor
      · assumption
      · constructor
        · rw [ConnectedComponent.mem_supp_iff]
          rw [ConnectedComponent.mem_supp_iff] at hv
          rw [← hv]
          apply ConnectedComponent.connectedComponentMk_eq_of_adj
          apply M.adj_sub
          rw [Subgraph.adj_comm]
          exact hw.1
        · exact hw.1
    · intro y hy
      apply hw.2
      exact hy.2.2
    done


lemma SimpleGraph.PerfectMatchingConnectedComponentEven [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
  (M : Subgraph G) (hM : Subgraph.IsPerfectMatching M) (c : ConnectedComponent G) : Even (Fintype.card ↑(ConnectedComponent.supp c)) := by
    classical
    have h : Even (M.induce c.supp).verts.toFinset.card := by exact Subgraph.IsMatching.even_card (SimpleGraph.PerfectMatchingInducesMatchingOnComponent M hM c)
    obtain ⟨ k , hk ⟩ := h
    use k
    rw [← hk, Subgraph.induce_verts, @Fintype.card_ofFinset]
    congr
    simp only [ConnectedComponent.mem_supp_iff]
    exact Set.filter_mem_univ_eq_toFinset fun x => connectedComponentMk G x = c

    done

instance [Fintype V] [DecidableEq V] [DecidableRel G.Adj] : DecidableEq (ConnectedComponent G) := by
  intro c c'
  exact c.recOn
    (fun v =>
      c'.recOn (fun w => by
        rw [@ConnectedComponent.eq]
        infer_instance)
        (fun _ _ _ _ => Subsingleton.elim _ _))
    (fun _ _ _ _ => Subsingleton.elim _ _)


noncomputable instance myInst5 [Fintype V] [DecidableEq V] (u : Set V) : Fintype u := by
  exact Fintype.ofFinite ↑u

noncomputable instance myInst4 [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (u : Set V) [Fintype u]:
    Fintype ((⊤ : G.Subgraph).deleteVerts u).verts := by
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

lemma OddComponentHasNodeMatchedOutside [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
  (M : Subgraph G) (hM : Subgraph.IsPerfectMatching M) (u : Set V) (c : ConnectedComponent ((⊤ : Subgraph G).deleteVerts u).coe)
  (codd : c.isOdd) : ∃ (w : Set.Elem u) (v : Set.Elem ((⊤ : G.Subgraph).deleteVerts u).verts) ,  M.Adj v w ∧ v ∈ c.supp := by
      rw [ConnectedComponent.isOdd_iff] at codd

      by_contra! h

      have h' : (Subgraph.IsMatching (M.induce c.supp)) := by
        intro v hv
        obtain ⟨ w , hw ⟩ := hM.1 (hM.2 v)
        obtain ⟨ v' , hv' ⟩ := hv
        use w
        dsimp at *
        constructor
        · constructor
          · exact ⟨ v' , hv' ⟩
          · constructor
            · have h'' : w ∉ u := by
                intro hw'
                apply h ⟨ w , hw' ⟩ v' _
                · exact hv'.1
                rw [hv'.2]
                exact hw.1
                done

              apply mem_supp_of_adj' c v' w ⟨ v' , ⟨ hv'.1 , rfl ⟩ ⟩ ⟨ by trivial , h'' ⟩
              rw [hv'.2]
              exact Subgraph.adj_sub _ hw.1
            · exact hw.1
        · intro y hy
          apply hw.2
          exact hy.2.2
        done

      apply Nat.odd_iff_not_even.mp codd
      have h'' := Subgraph.IsMatching.even_card h'
      simp only [Subgraph.induce_verts, Subgraph.verts_top] at h''
      unfold Fintype.card
      rw [Nat.even_iff] at h'' ⊢
      rw [← h'']
      rw [ Set.toFinset_image ]
      rw [Finset.card_image_of_injective _ (Subtype.val_injective)]
      simp only [Subgraph.induce_verts, Subgraph.verts_top, Set.toFinset_card]
      rfl




theorem chainInSubtypeGivesChainInSupertype {α : Type} {p : α → Prop} [LE α] {c : Set (Subtype p)} (hc : IsChain (. ≤ .) c) :
   IsChain (. ≤ .) (Subtype.val '' c ) := by
    intro x hx y hy hxy
    obtain ⟨x' , hx'⟩ := hx
    obtain ⟨y' , hy'⟩ := hy

    rw [← hx'.2, ← hy'.2] at hxy
    let h := hc hx'.1 hy'.1 (fun a => hxy (congrArg Subtype.val a))
    dsimp at *
    dsimp at h
    cases h with
    | inl ha =>
      left
      rw [← hx'.2, ← hy'.2]
      exact ha
    | inr hb =>
      right
      rw [← hx'.2, ← hy'.2]
      exact hb

theorem chainFinsetInFintypeHasMax {α : Type*} [PartialOrder α] [DecidableEq α] {c : Finset α} [hnc : Nonempty c] (hic : IsChain (. ≤ .) c.toSet) :
  ∃ m ∈ c, ∀ a ∈ c, a ≤ m := by
    by_contra! hc
    obtain ⟨ g , hg ⟩ := hnc
    obtain ⟨ g' , hg' ⟩ := hc g hg
    obtain hcemp | hcnemp := (c \ {g}).eq_empty_or_nonempty
    · rw [Finset.sdiff_eq_empty_iff_subset] at hcemp
      rw [Finset.subset_singleton_iff'] at hcemp
      apply hg'.2
      rw [hcemp g' hg'.1]


    · have cGch : IsChain (. ≤ .) (c \ {g}).toSet := by
        rw [Finset.coe_sdiff]
        rw [Finset.coe_singleton]
        apply IsChain.mono (@Set.diff_subset _ c {g})
        exact hic
      haveI instNonEmp : Nonempty ↑(c \ {g}) := Set.Nonempty.to_subtype hcnemp
      obtain ⟨ m , hm ⟩ := chainFinsetInFintypeHasMax cGch
      obtain ⟨ n , hn ⟩ := hc m (Finset.mem_sdiff.mp hm.1).1

      have : n = g := by
        by_contra! hc'
        apply hn.2
        apply hm.2 n
        rw [Finset.sdiff_singleton_eq_erase]
        rw [Finset.mem_erase]
        exact  ⟨ hc', hn.1 ⟩
      have h'' : ¬g' ≤ n := by
        rw [← this] at hg'
        exact hg'.2
      apply h''
      have h''' := hm.2 g'

      have h'''' : g' ∈ c \ {g} := by
        rw [Finset.sdiff_singleton_eq_erase]
        rw [Finset.mem_erase]
        exact ⟨ ne_of_not_le hg'.2 , hg'.1 ⟩
      apply le_of_lt
      apply lt_of_le_of_lt (h''' h'''')
      have h''''' := hic (Finset.mem_sdiff.mp hm.1).1 (hn.1) (ne_of_not_le hn.2).symm
      dsimp at h'''''
      cases h''''' with
      | inl ha => exact lt_iff_le_and_ne.mpr ⟨ ha , (ne_of_not_le hn.2).symm ⟩
      | inr hb =>
         exfalso
         exact hn.2 hb
termination_by c.card
decreasing_by
· simp_wf
  rw [← Finset.erase_eq]
  rw [← Finset.card_erase_add_one hg]
  simp only [lt_add_iff_pos_right, zero_lt_one]
--   haveI : Fintype c := setFintype c
--   rw [Set.ncard_eq_toFinset_card]



theorem chainInFintypeHasMax {α : Type*} [Fintype α] [PartialOrder α] [DecidableEq α] (c : Set α) [hnc : Nonempty c] (hic : IsChain (. ≤ .) c) :
  ∃ m ∈ c, ∀ a ∈ c, a ≤ m := by
  let c' := c.toFinset
  have fChain : IsChain (. ≤ .) c'.toSet := by
    intro x hx y hy hxy
    cases hic (Set.mem_toFinset.mp hx) (Set.mem_toFinset.mp hy) hxy with
    | inl ha =>
      left
      assumption
    | inr hb =>
      right
      assumption
  haveI : Nonempty c' := by
    obtain ⟨ e , he ⟩ := hnc
    use e
    exact Set.mem_toFinset.mpr he
  have ⟨ m , hm ⟩ := chainFinsetInFintypeHasMax fChain
  use m
  constructor
  · exact Set.mem_toFinset.mp hm.1
  · intro a ha
    exact hm.2 a (Set.mem_toFinset.mpr ha)

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

--First (done)
lemma isMatchingHom (G G' : SimpleGraph V) (x : Subgraph G) (h : G ≤ G') (hM : x.IsMatching) : (x.map (SimpleGraph.Hom.ofLE h)).IsMatching := by
  intro v hv
  unfold Subgraph.IsMatching at hM
  dsimp at hv
  obtain ⟨ v' , ⟨ hv' , hv'' ⟩ ⟩ := Set.mem_image_iff_bex.mp hv
  obtain ⟨ w' , hw' ⟩ := hM hv'
  use w'
  dsimp at *
  simpa only [Relation.map_id_id] using hv'' ▸ hw'

lemma isMatchingFree_mono {G G' : SimpleGraph V} (h : G ≤ G') (hmf : isMatchingFree G') : isMatchingFree G := by
  intro x
  by_contra! hc
  apply hmf (Subgraph.map (SimpleGraph.Hom.ofLE h) x)
  constructor
  · exact isMatchingHom _ _ _ _ hc.1
  · intro v
    dsimp
    rw [@Set.image_id]
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
          by infer_instance ,
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


lemma subdivide [Fintype V] [Inhabited V] [DecidableEq V] {G G' : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (h : G ≤ G') (c : ConnectedComponent G') : ∃ (cs : Finset (ConnectedComponent G)), (ConnectedComponent.supp '' cs.toSet).sUnion = c.supp := by
      use (connectedComponentMk G '' c.supp).toFinset
      ext v
      constructor
      · intro hv
        rw [Set.sUnion_image] at hv
        rw [Set.mem_iUnion] at hv
        obtain ⟨ i , hi ⟩ := hv
        rw [Set.mem_iUnion] at hi
        obtain ⟨ j , hj ⟩ := hi
        rw [@Finset.mem_coe] at j
        rw [@Set.mem_toFinset] at j
        rw [Set.mem_image] at j
        obtain ⟨ k , hk ⟩ := j
        rw [ConnectedComponent.mem_supp_iff] at *
        rw [← hk.1]
        rw [← hk.2] at hj
        rw [@ConnectedComponent.eq] at *
        apply SimpleGraph.Reachable.mono h
        exact hj
      · intro hv
        rw [Set.mem_sUnion]

        use (connectedComponentMk G v).supp
        constructor
        · rw [Function.Injective.mem_set_image SimpleGraph.ConnectedComponent.supp_injective, Finset.mem_coe, Set.mem_toFinset, Set.mem_image]
          use v
        · exact rfl





lemma exclUnion [Fintype V] [Inhabited V] [DecidableEq V] [DecidableRel G.Adj] (s : Finset (ConnectedComponent G))
  : Fintype.card ↑(⋃ x ∈ s, @ConnectedComponent.supp V G x) = Finset.sum s (fun x => Nat.card (@ConnectedComponent.supp V G x)) := by

    rw [← Set.toFinset_card ]
    have hp : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      Disjoint (Set.toFinset (@ConnectedComponent.supp _ G x)) (Set.toFinset (ConnectedComponent.supp y)) := by
      intro xs _ ys _ hxy s' hx hy
      simp only [Finset.bot_eq_empty, Finset.le_eq_subset]
      rw [Finset.subset_empty]
      rw [Finset.eq_empty_iff_forall_not_mem]
      by_contra! hc
      obtain ⟨ v , hv ⟩ := hc
      obtain ha := hx hv
      obtain hb := hy hv
      simp only [ne_eq, Finset.le_eq_subset, Set.subset_toFinset, Set.mem_toFinset,
        ConnectedComponent.mem_supp_iff] at *
      exact hxy (ha.symm ▸ hb)
      done

    have : Set.toFinset (⋃ x ∈ s, ConnectedComponent.supp x) = Finset.biUnion s (fun x => (ConnectedComponent.supp x).toFinset) := by
      ext v
      simp only [Set.mem_toFinset, Set.mem_iUnion, ConnectedComponent.mem_supp_iff, exists_prop,
        exists_eq_right', Finset.mem_biUnion]

    rw [this]
    rw [Finset.card_biUnion hp]
    congr
    dsimp
    ext c
    rw [@Set.toFinset_card]
    rw [Nat.card_eq_fintype_card]

lemma cardUnion [Fintype V] [Inhabited V] [DecidableEq V] [DecidableRel G.Adj] (s : Finset (ConnectedComponent G))
      : Fintype.card (⋃₀ (ConnectedComponent.supp '' s.toSet)) = Finset.sum s (Set.ncard ∘ ConnectedComponent.supp) := by
  simp only [Set.sUnion_image, Finset.mem_coe, Function.comp_apply]
  have hp :  Pairwise fun i j => Disjoint (⋃ (_ : i ∈ s), ConnectedComponent.supp i)
    (⋃ (_ : j ∈ s), ConnectedComponent.supp j) := by
    intro x y hxy s' hx hy
    simp only [Set.bot_eq_empty, Set.le_eq_subset]
    rw [@Set.subset_empty_iff]
    by_contra! hc
    obtain ⟨ v , hv ⟩ := hc
    obtain ⟨ a , ha ⟩ := hx hv
    obtain ⟨ b , hb ⟩ := hy hv
    simp only [ne_eq, Set.le_eq_subset, Set.mem_range, exists_prop] at *
    have h1 := ha.1.2.symm ▸ ha.2
    have h2 := hb.1.2.symm ▸ hb.2
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at *
    exact hxy (h1.symm ▸ h2)
    done

  rw [exclUnion]
  congr
  ext x
  exact Set.Nat.card_coe_set_eq (ConnectedComponent.supp x)

lemma evenFinsetSum {a : Finset α} (f : α → ℕ) (h : ∀ (c : a), Even (f c)) : Even (Finset.sum a f) := by
  rw [@Nat.even_iff]
  rw [Finset.sum_nat_mod]
  have : (Finset.sum a fun i => f i % 2) = Finset.sum a fun i => 0 := by
    exact Finset.sum_congr (rfl : a = a) (by
      intro x hx
      have h' := h ⟨ x , hx ⟩
      dsimp at h'
      rw [@Nat.even_iff] at h'
      exact h'
      )
  rw [this]
  simp only [Finset.sum_const_zero, Nat.zero_mod]



lemma oddSubComponent [Fintype V] [Inhabited V] [DecidableEq V] (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (h : G ≤ G') (c : ConnectedComponent G') (ho : c.isOdd) : ∃ v ∈ c.supp, (G.connectedComponentMk v).isOdd := by

      simp_rw [ConnectedComponent.isOdd_iff, Nat.odd_iff_not_even]
      by_contra! hc

      have : Even (Fintype.card c.supp) := by
        obtain ⟨ a , ha ⟩ := subdivide h c

        rw [← ha]
        rw [cardUnion]
        apply evenFinsetSum

        intro c'
        rw [@Function.comp_apply]
        have ⟨ v , hv ⟩:= c'.val.exists_rep
        rw [← SimpleGraph.connectedComponentMk] at hv
        rw [← hv]
        have vMem : v ∈ ConnectedComponent.supp c := by
          rw [← ha]
          simp only [Set.sUnion_image, Finset.mem_coe, Set.mem_iUnion,
            ConnectedComponent.mem_supp_iff, exists_prop, exists_eq_right']
          rw [hv]
          exact Finset.coe_mem c'
        rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
        exact hc v vMem

      rw [@ConnectedComponent.isOdd_iff] at ho
      exact Nat.odd_iff_not_even.mp ho this


lemma oddComponent [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (ho : Odd (Fintype.card V)) : ∃ (c : ConnectedComponent G), c.isOdd := by
      simp_rw [ConnectedComponent.isOdd_iff, Nat.odd_iff_not_even]
      by_contra! hc

      have : (Set.univ : Set V) = ⋃ (c : G.ConnectedComponent), c.supp := by
        ext v
        constructor
        · intro hv
          use G.connectedComponentMk v
          simp only [Set.mem_range, SetLike.mem_coe]
          constructor
          · use G.connectedComponentMk v
            exact rfl
          · exact rfl
        · intro hv
          exact trivial
      rw [← (set_fintype_card_eq_univ_iff _).mpr (this.symm) ] at ho
      rw [← Set.toFinset_card ] at ho
      -- rw [← Nat.card_eq_card_toFinset ] at ho
      rw [@Nat.odd_iff_not_even] at ho
      apply ho
      have : Set.toFinset (⋃ (x : ConnectedComponent G), ConnectedComponent.supp x) = Finset.biUnion (Finset.univ : Finset (ConnectedComponent G)) (fun x => (ConnectedComponent.supp x).toFinset) := by
        ext v
        simp only [Set.mem_toFinset, Set.mem_iUnion, ConnectedComponent.mem_supp_iff, exists_eq',
          Finset.mem_biUnion, Finset.mem_univ, true_and, true_iff]
      rw [this]
      rw [Finset.card_biUnion (by
        intro x hx y hy hxy
        rw [Set.disjoint_toFinset]
        intro s hsx hsy
        simp only [Set.toFinset_card, Finset.mem_univ, ne_eq, Set.le_eq_subset,
          Set.bot_eq_empty] at *
        rw [@Set.subset_empty_iff, Set.eq_empty_iff_forall_not_mem]
        intro v hv
        have hsxv := hsx hv
        have hsyv := hsy hv
        rw [@ConnectedComponent.mem_supp_iff] at *
        rw [hsxv] at hsyv
        apply hxy
        exact hsyv
        )]
      simp only [Set.toFinset_card]
      exact evenFinsetSum _ fun c => hc ↑c



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
            obtain ⟨ v , hv ⟩ := (oddSubComponent ((⊤ : Subgraph G).deleteVerts u).coe ((⊤ : Subgraph G').deleteVerts u).coe b c hc)
            use ((((⊤ : Subgraph G).deleteVerts u).coe ).connectedComponentMk v)
            constructor
            · exact hv.2
            ·
              rw [@Set.subset_def]
              intro x hx
              rw [@ConnectedComponent.mem_supp_iff]
              have h' := hv.1
              rw [@ConnectedComponent.mem_supp_iff] at h'
              rw [← h']
              rw [@ConnectedComponent.mem_supp_iff] at hx
              rw [SimpleGraph.ConnectedComponent.eq] at *
              exact SimpleGraph.Reachable.mono b hx

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

def evenSplit [DecidableEq V] (u : Finset V) (uEven : Even (u.card)) : ∃ u', u' ⊆ u ∧ u'.card = (u \ u').card := by
  by_cases h : u.card = 0
  · use ∅
    simp only [Finset.empty_subset, Finset.card_empty, Finset.sdiff_empty, true_and]
    exact h.symm
  · push_neg at h
    obtain ⟨ v , hv ⟩ := Finset.card_pos.mp (Nat.zero_lt_of_ne_zero h)
    have hno : u.card ≠ 1 := by
      intro h
      exact Nat.not_even_one (h ▸ uEven)
    have : 0 < (u.erase v).card := by
      rw [Finset.card_erase_of_mem hv]
      simp only [tsub_pos_iff_lt]
      exact (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ h , hno ⟩)
    obtain ⟨ w , hw ⟩ := Finset.card_pos.mp this
    obtain ⟨ u' , hu' ⟩ := evenSplit ((u.erase v).erase w) (by
      obtain ⟨ k, hk ⟩ := uEven
      have : 0 < k := by
        rw [hk] at h
        ring_nf at h
        rw [Nat.mul_ne_zero_iff] at h
        exact Nat.zero_lt_of_ne_zero h.1
      use (k - 1)
      rw [Finset.card_erase_of_mem hw]
      rw [Finset.card_erase_of_mem hv]
      rw [Nat.sub_sub]
      rw [← Nat.sub_add_comm (by linarith)]
      rw [← Nat.add_sub_assoc (by linarith)]
      rw [← hk]
      rw [Nat.sub_sub]
      )
    use (insert w u')
    constructor
    · intro x hx
      rw [Finset.mem_insert] at hx
      cases hx with
      | inl h1 => exact h1 ▸ (Finset.mem_erase.mp hw).2
      | inr h2 =>
        apply Finset.erase_subset v u
        apply Finset.erase_subset w (Finset.erase u v)
        exact hu'.1 h2
    · rw [Finset.card_insert_of_not_mem (by
        intro h
        exact (Finset.not_mem_erase _ _) (hu'.1 h))]
      -- rw [hu'.2]
      rw [Finset.sdiff_insert]
      have := hu'.2
      rw [Finset.erase_sdiff_comm] at this
      rw [Finset.erase_sdiff_comm] at this
      rw [Finset.card_erase_of_mem (by
        rw [@Finset.mem_sdiff]
        exact ⟨ (Finset.mem_erase.mp hw).2 , (by
          intro hnw
          exact (Finset.not_mem_erase _ _) (hu'.1 hnw)
          ) ⟩
        )]

      rw [this]
      rw [Finset.card_erase_of_mem (by
        rw [Finset.mem_erase]
        exact ⟨ (Finset.mem_erase.mp hw).1 , (by
          rw [Finset.mem_sdiff]
          exact ⟨ (Finset.mem_erase.mp hw).2 , (by
            intro hwu'
            exact (Finset.not_mem_erase _ _) (hu'.1 hwu')
            ) ⟩
          ) ⟩
        )]

      rw [Finset.card_erase_of_mem (by

        rw [Finset.mem_sdiff]
        exact ⟨ hv , (by
          intro hvu'
          have := hu'.1 hvu'
          exact (Finset.not_mem_erase _ _) (Finset.mem_erase.mp (hu'.1 hvu')).2) ⟩
        )]
      have : u'.card ≤ u.card - 2 := by
        have h' := Finset.card_le_card hu'.1
        rw [Finset.card_erase_of_mem hw] at h'
        rw [Finset.card_erase_of_mem hv] at h'
        rw [Nat.sub_sub] at h'
        exact h'

      have : (u \ u').card > 1 := by
        calc (u \ u').card
          _ ≥ u.card - u'.card := by exact Finset.le_card_sdiff u' u
          _ > 1 := by omega
      rw [@tsub_add_cancel_iff_le]
      omega

termination_by u.card
decreasing_by
  simp_wf
  rw [Finset.card_erase_of_mem hw]
  rw [Finset.card_erase_of_mem hv]
  omega

lemma evenCliqueMatches [Fintype V] [DecidableEq V]
  (u : Set V) (h : G.IsClique u) (uEven : Even (u.ncard)) : ∃ (M : Subgraph G), M.support = u ∧ M.IsMatching := by
  obtain ⟨ u' , hu'⟩ := evenSplit u.toFinset (Set.ncard_eq_toFinset_card' u ▸ uEven)
  have f := Finset.equivOfCardEq hu'.2
  let M : Subgraph G := (⨆ (v : u'), G.subgraphOfAdj ((by
    apply h
    · rw [← Set.mem_toFinset]
      exact hu'.1 v.2
    · rw [← Set.mem_toFinset]
      exact (Finset.mem_sdiff.mp (f v).2).1
    intro heq
    have := (Finset.mem_sdiff.mp (f v).2).2
    apply this
    rw [← heq]
    exact v.2
    ) : G.Adj v (f v)))
  use M
  constructor
  · ext v
    constructor
    · intro hv
      obtain ⟨ w , hw ⟩ := M.mem_support.mp hv
      rw [SimpleGraph.Subgraph.iSup_adj] at hw
      obtain ⟨ i , hi ⟩ := hw
      rw [SimpleGraph.subgraphOfAdj_adj] at hi
      cases Sym2.eq_iff.mp hi with
      | inl h1 =>
        rw [← Set.mem_toFinset]
        exact hu'.1 (h1.1 ▸ i.2)
      | inr h2 =>
        rw [← Set.mem_toFinset]
        rw [← h2.2]
        exact (Finset.mem_sdiff.mp (f i).2).1
    · intro hv
      rw [SimpleGraph.Subgraph.mem_support]
      if hvu' : v ∈ u'
      then
        use f ⟨ v , hvu' ⟩
        rw [SimpleGraph.Subgraph.iSup_adj]
        use ⟨ v , hvu' ⟩
        simp only [subgraphOfAdj_adj]
      else
        have : v ∈ Set.toFinset u \ u' := (by

          rw [@Finset.mem_sdiff]
          exact ⟨ Set.mem_toFinset.mpr hv , hvu' ⟩
          )
        use f.invFun ⟨ v , this ⟩
        rw [SimpleGraph.Subgraph.iSup_adj]
        use f.invFun ⟨ v , this ⟩
        simp only [Equiv.invFun_as_coe, Equiv.apply_symm_apply, subgraphOfAdj_adj, Sym2.eq,
          Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, or_true]
  · intro v hv
    rw [SimpleGraph.Subgraph.verts_iSup] at hv
    rw [Set.mem_iUnion ] at hv
    obtain ⟨ i , hi ⟩ := hv
    simp only [subgraphOfAdj_verts, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    cases hi with
    | inl h1 =>
      use f i
      exact ⟨ by
        dsimp
        rw [SimpleGraph.Subgraph.iSup_adj]
        use i
        simp only [subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, and_true,
          Prod.swap_prod_mk]
        left
        exact h1.symm
        , (by
        intro y hy
        rw [SimpleGraph.Subgraph.iSup_adj] at hy
        obtain ⟨ i' , hi' ⟩ := hy
        simp at hi'
        cases hi' with
        | inl hl =>
          rw [← hl.2]
          rw [@SetCoe.ext_iff]
          rw [← hl.1] at h1
          rw [Subtype.val_injective h1]
        | inr hr =>
          have : (f i').val ∈ Set.toFinset u \ u' := by
            exact (f i').2
          rw [hr.2] at this
          exfalso
          rw [@Finset.mem_sdiff] at this
          apply this.2
          rw [h1]
          exact i.2
        ) ⟩
    | inr h2 =>
      use i
      dsimp
      constructor
      · rw [SimpleGraph.Subgraph.iSup_adj]
        use i
        rw [h2]
        simp only [subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
          or_true]
      · intro y hy
        rw [SimpleGraph.Subgraph.iSup_adj] at hy
        obtain ⟨ i' , hi' ⟩ := hy
        simp only [subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
          at hi'
        cases hi' with
        | inl hl =>
          have : (f i).val ∈ Set.toFinset u \ u' := by
            exact (f i).2
          rw [← h2] at this
          exfalso
          rw [@Finset.mem_sdiff] at this
          apply this.2
          rw [← hl.1]
          exact i'.2
        | inr hr =>
          rw [← hr.1]
          rw [h2] at hr
          rw [@SetCoe.ext_iff]
          apply Equiv.injective f
          apply Subtype.val_injective
          exact hr.2

lemma existsIsMatching [Fintype V] [DecidableEq V]
  (u : Set V) (h : G.IsClique u) (uEven : Even (u.ncard)) : (evenCliqueMatches u h uEven).choose.IsMatching := by
  exact (Exists.choose_spec (evenCliqueMatches u h uEven)).2


--First (done)
lemma sup_IsMatching [Fintype V] [Inhabited V] [DecidableEq V] [DecidableRel G.Adj]
  {M M' : Subgraph G} (hM : M.IsMatching) (hM' : M'.IsMatching) (hd : Disjoint (M.support) (M'.support)) : (M ⊔ M').IsMatching := by
  intro v hv
  rw [SimpleGraph.Subgraph.verts_sup] at hv
  cases Set.mem_or_mem_of_mem_union hv with
  | inl hmM =>
    obtain ⟨ w , hw ⟩ := hM hmM
    use w
    dsimp at *
    constructor
    · exact SimpleGraph.Subgraph.sup_adj.mpr (.inl hw.1)
    · intro y hy
      rw [SimpleGraph.Subgraph.sup_adj] at hy
      cases hy with
      | inl h1 => exact hw.2 y h1
      | inr h2 =>
        have hvM's: v ∈ M'.support := by
          rw [SimpleGraph.Subgraph.mem_support ]
          use y
        have hvMs : v ∈ M.support := by
          rw [SimpleGraph.Subgraph.mem_support ]
          use w
          exact hw.1
        exfalso
        rw [Set.disjoint_left] at hd
        exact hd hvMs hvM's
  | inr hmM' =>
    obtain ⟨ w , hw ⟩ := hM' hmM'
    use w
    dsimp at *
    constructor
    · exact SimpleGraph.Subgraph.sup_adj.mpr (.inr hw.1)
    · intro y hy
      rw [SimpleGraph.Subgraph.sup_adj] at hy
      cases hy with
      | inr h1 => exact hw.2 y h1
      | inl h2 =>
        have hvM's: v ∈ M'.support := by
          rw [SimpleGraph.Subgraph.mem_support ]
          use w
          exact hw.1
        have hvMs : v ∈ M.support := by
          rw [SimpleGraph.Subgraph.mem_support ]
          use y
        exfalso
        rw [Set.disjoint_left] at hd
        exact hd hvMs hvM's

--First (done)
lemma iSup_IsMatching [Fintype V] [Inhabited V] [DecidableEq V] [DecidableRel G.Adj]
  {f : ι → Subgraph G} (hM : (i : ι) → (f i).IsMatching) (hd : (i j : ι) → (i ≠ j) →  Disjoint ((f i).support) ((f j).support)) : (⨆ i , f i).IsMatching := by
  intro v hv
  rw [SimpleGraph.Subgraph.verts_iSup] at hv
  obtain ⟨ i , hi ⟩ := Set.mem_iUnion.mp hv
  obtain ⟨ w , hw ⟩ := hM i hi
  use w
  dsimp at *
  constructor
  · rw [SimpleGraph.Subgraph.iSup_adj]
    use i
    exact hw.1
  · intro y hy
    rw [SimpleGraph.Subgraph.iSup_adj] at hy
    obtain ⟨ i' , hi' ⟩ := hy
    if heq : i = i' then
      exact hw.2 y (heq.symm ▸ hi')
    else
      have hvsi : v ∈ Subgraph.support (f i) := by
        rw [SimpleGraph.Subgraph.mem_support ]
        use w
        exact hw.1
      have hvsi' : v ∈ Subgraph.support (f i') := by
        rw [SimpleGraph.Subgraph.mem_support ]
        use y
      have := hd _ _ heq
      rw [Set.disjoint_left] at this
      exfalso
      exact this hvsi hvsi'

--First (done)
lemma subgraphOfAdj_IsMatching [Fintype V] [Inhabited V] [DecidableEq V] [DecidableRel G.Adj]
  (h : G.Adj v w) : (G.subgraphOfAdj h).IsMatching := by
  intro v' hv'
  rw [@subgraphOfAdj_verts] at hv'
  rw [@Set.mem_insert_iff] at hv'
  rw [@Set.mem_singleton_iff] at hv'
  cases hv' with
  | inl hl =>
    use w
    simp only [subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, and_true,
      Prod.swap_prod_mk]
    constructor
    · exact .inl hl.symm
    · intro y hy
      cases hy with
      | inl h1 =>
        exact h1.2.symm
      | inr h2 =>
        rw [h2.1] at hl
        rw [← h2.2] at hl
        exact hl.symm
  | inr hr =>
    use v
    simp only [subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
      true_and]
    constructor
    · exact .inr hr.symm
    · intro y hy
      cases hy with
      | inl h1 =>
        rw [← h1.1] at hr
        rw [h1.2] at hr
        exact hr.symm
      | inr h2 =>
        exact h2.1.symm

--First
--Alternative proof through IsMatching
lemma subgraphOfAdj_support
  (h : G.Adj v w) : (G.subgraphOfAdj h).support = {v , w} := by
  ext v'
  rw [SimpleGraph.Subgraph.mem_support]
  constructor
  · rintro ⟨ w , hw ⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    simp only [subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hw
    cases hw with
    | inl h1 => exact .inl h1.1.symm
    | inr hr => exact .inr hr.2.symm
  · intro hv'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv'
    cases hv' with
    | inl hl =>
      use w
      simp only [subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, and_true,
        Prod.swap_prod_mk]
      exact .inl hl.symm
    | inr hr =>
      use v
      simp only [subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
        true_and]
      exact .inr hr.symm



lemma componentExistsRep (c : ConnectedComponent G) : ∃ v, SimpleGraph.connectedComponentMk G v = c := c.exists_rep

--First
@[simp]
lemma coe_verts [Fintype V] [Inhabited V] [DecidableEq V] [DecidableRel G.Adj]
  {G' : Subgraph G} (M : Subgraph G'.coe) : M.coeSubgraph.verts = (M.verts : Set V) := rfl

--First
lemma coe_IsMatching [Fintype V] [Inhabited V] [DecidableEq V] [DecidableRel G.Adj]
  {G' : Subgraph G} {M : Subgraph G'.coe} (hM : M.IsMatching) : M.coeSubgraph.IsMatching := by
  intro v hv
  rw [coe_verts] at hv
  obtain ⟨ w , hw ⟩ := hM (Set.mem_of_mem_image_val hv)
  use w

  -- dsimp at *
  constructor
  ·
    conv =>
      enter [0, w]
      rw [Subgraph.coeSubgraph_adj]
    dsimp at *
    have := (Set.mem_of_mem_image_val hv)
    simp only [Subtype.forall] at hw
    simp only [Subtype.coe_eta, Subtype.coe_prop, exists_const] at *
    rw [Set.mem_image] at hv
    obtain ⟨ v' , hv' ⟩ := hv
    use (hv'.2 ▸ v'.2)
    exact hw.1
  · intro y hy
    rw [SimpleGraph.Subgraph.coeSubgraph_adj] at hy
    obtain ⟨ hv' , ⟨ hw' , hvw ⟩ ⟩ := hy
    rw [← hw.2 ⟨ y , hw' ⟩ hvw]


lemma oddSubOneEven (n : Nat) (h : Odd n) : Even (n - 1) := by
  obtain ⟨ k , hk ⟩ := h
  use k
  rw [hk]
  rw [Nat.add_sub_cancel]
  ring


lemma oddCliqueAlmostMatches [Fintype V] [DecidableEq V]
  {u : Set V} {v : V} (hv : v ∈ u) (h : G.IsClique u) (uOdd : Odd (Fintype.card u)) : ∃ (M : Subgraph G), insert v M.verts = u ∧ M.IsMatching := by
  have u'Even : Even ((u \ {v}).ncard) := by
    rw [Set.ncard_eq_toFinset_card']
    rw [Set.toFinset_diff]
    simp only [Set.mem_setOf_eq, Set.toFinset_singleton]
    rw [Finset.sdiff_singleton_eq_erase]
    rw [Finset.card_erase_of_mem (Set.mem_toFinset.mpr hv)]
    rw [Set.toFinset_card]
    exact oddSubOneEven _ uOdd
  have u'Clique : G.IsClique (u \ {v}) := SimpleGraph.IsClique.subset (@Set.diff_subset _ u {v}) h
  obtain ⟨ M , hM ⟩ := (evenCliqueMatches (u \ {v}) u'Clique u'Even)
  use M
  constructor
  · rw [← SimpleGraph.Subgraph.IsMatching.support_eq_verts hM.2]
    rw [hM.1]
    rw [Set.insert_diff_singleton]
    exact (Set.insert_eq_of_mem hv)
  · exact hM.2

lemma oddCliqueAlmostMatchesDoesNotContainNode [Fintype V] [DecidableEq V]
  {u : Set V} {v : V} (hv : v ∈ u) (h : G.IsClique u) (uOdd : Odd (Fintype.card u)) : v ∉ (oddCliqueAlmostMatches hv h uOdd).choose.verts := by
  have hM := (oddCliqueAlmostMatches hv h uOdd).choose_spec

  have : Even (Fintype.card (oddCliqueAlmostMatches hv h uOdd).choose.verts) := by
    rw [← @Set.toFinset_card]
    exact SimpleGraph.Subgraph.IsMatching.even_card hM.2
  intro hv
  rw [Set.insert_eq_of_mem hv] at hM

  rw [← hM.1] at uOdd
  rw [@Nat.even_iff_not_odd] at this
  exact this uOdd


lemma oddCliqueAlmostMatchesSubset [Fintype V] [DecidableEq V]
  {u : Set V} {v : V} (hv : v ∈ u) (h : G.IsClique u) (uOdd : Odd (Fintype.card u)) : (oddCliqueAlmostMatches hv h uOdd).choose.verts ⊆ u := by
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



lemma reachable_in_connected_component_induce (c : ConnectedComponent G) (v w : c.supp) : (G.induce c.supp).Reachable v w := by
  have hvc := (c.mem_supp_iff v).mp (Subtype.coe_prop v)
  have hwc := (c.mem_supp_iff w).mp (Subtype.coe_prop w)
  have : G.connectedComponentMk v = G.connectedComponentMk w := by
    rw [hvc, hwc]
  have p := (Classical.inhabited_of_nonempty (ConnectedComponent.exact this)).default
  exact Walk.reachable (lift_walk p)

lemma verts_of_walk (p : G.Walk v w) (hp : p.length = G.dist v w) (hl : 1 < G.dist v w) : ∃ (x a b : V), G.Adj x a ∧ G.Adj a b ∧ ¬ G.Adj x b ∧ x ≠ b := by

  have hnp : ¬p.Nil := by
    rw [SimpleGraph.Walk.nil_iff_length_eq]
    rw [hp]
    exact Nat.not_eq_zero_of_lt hl

  let t := p.tail hnp

  have hnt : ¬t.Nil := by
    rw [SimpleGraph.Walk.nil_iff_length_eq]
    rw [← hp] at hl
    rw [← (SimpleGraph.Walk.length_tail_add_one hnp)] at hl
    rw [@Nat.lt_add_left_iff_pos] at hl
    exact Nat.not_eq_zero_of_lt hl

  use v
  use p.sndOfNotNil hnp
  use t.sndOfNotNil hnt
  simp only [Walk.adj_sndOfNotNil, true_and]
  constructor
  · intro hadj
    let pcon := Walk.cons hadj (t.tail hnt)
    have hdist : pcon.length < G.dist v w := by
      rw [← hp]
      rw [@Walk.length_cons]
      rw [Walk.length_tail_add_one]
      apply @Nat.lt_of_add_lt_add_right _ _ 1
      rw [Walk.length_tail_add_one]
      exact lt_add_one p.length

    linarith [SimpleGraph.dist_le pcon]
  · intro heq
    let pcon := t.tail hnt
    have hdist : (t.tail hnt).length < G.dist (t.sndOfNotNil hnt) w := by
      apply @Nat.lt_of_add_lt_add_right _ _ 1
      rw [Walk.length_tail_add_one]
      rw [← heq]
      apply @Nat.lt_of_add_lt_add_right _ _ 1
      rw [Walk.length_tail_add_one]
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

-- structure Walk.isAlternating (p : G.Walk u v) (M : Subgraph G) where
--   firstEdge (hnp : ¬ p.Nil) : (p.firstDart hnp).edge ∉ M.edgeSet
--   secondEdge (hnp : ¬ p.Nil) (hnt : ¬ (p.tail hnp).Nil) : ((p.tail hnp).firstDart hnt).edge ∈ M.edgeSet
--   tailAlternating (hnp : ¬ p.Nil) (hnt : ¬ (p.tail hnp).Nil) :

-- inductive Walk.IsAlternating (M : Subgraph G) : {v w : V} → (p : G.Walk v w) → Prop where
--   | nil {u : V} : Walk.IsAlternating M (nil : G.Walk u u)
--   | single (hadj : G.Adj v w) : Walk.IsAlternating M (.cons hadj .nil)
--   | alt (q : G.Walk v w) : (hnq : ¬ q.Nil) → (hnt : ¬ (q.tail hnq).Nil) →
--       (halt: (q.firstDart hnq).edge ∈ M.edgeSet ↔ ¬ ((q.tail hnq).firstDart hnt).edge ∈ M.edgeSet) →
--       (htail: Walk.IsAlternating M (q.tail hnq)) → Walk.IsAlternating M q

-- structure Walk.IsAlternating (p : G.Walk u v) (M : Subgraph G) where
--   halt : ∀ (n : ℕ), 0 < n → n < p.length → (M.Adj (p.getVert (n-1)) (p.getVert n) ↔ ¬ M.Adj (p.getVert n) (p.getVert (n+1)))

structure Walk.IsAlternating (p : G.Walk u v) (M : Subgraph G) where
  halt : ∀ (v w w': V), w ≠ w' → p.toSubgraph.Adj v w → p.toSubgraph.Adj v w' → (M.Adj v w ↔ ¬ M.Adj v w')


lemma reverse_Nil (p : G.Walk u v) : p.reverse.Nil ↔ p.Nil := by
  rw [@Walk.nil_iff_length_eq]
  rw [SimpleGraph.Walk.length_reverse]
  exact Walk.nil_iff_length_eq.symm


def Walk.lastButOneOfNotNil (p : G.Walk u v) (hnp : ¬ p.Nil) := p.reverse.sndOfNotNil (by rwa [reverse_Nil])



@[simp]
lemma notNilRec_cons {motive : {u w : V} → (p : G.Walk u w) → (h : ¬ p.Nil) → Sort*}
    (cons : {u v w : V} → (h : G.Adj u v) → (q : G.Walk v w) → motive (Walk.cons h q) Walk.not_nil_cons)
    (h' : G.Adj u v) (q' : G.Walk v w) : @Walk.notNilRec _ _ _ _ _ cons _ _ = cons h' q' := by
    rfl

lemma cons_tail (p : G.Walk u v) (h : G.Adj t u) : (Walk.cons h p).tail (Walk.not_nil_cons) = p := by
  unfold Walk.tail
  simp only [notNilRec_cons]

lemma tail_support_eq_support_tail (p : G.Walk u v) (hnp : ¬p.Nil) : (p.tail hnp).support = p.support.tail :=
  p.notNilRec (by
    intro u v w huv q
    unfold Walk.tail
    simp only [notNilRec_cons, Walk.support_cons, List.tail_cons]) hnp

lemma sndOfNotNil_mem_support (p : G.Walk u v) (hnp : ¬ p.Nil) : p.sndOfNotNil hnp ∈ p.support := by
  rw [SimpleGraph.Walk.mem_support_iff]
  right
  rw [← tail_support_eq_support_tail _ hnp]
  exact Walk.start_mem_support (p.tail hnp)

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

lemma lastButOneOfNotNil_mem_support (p : G.Walk u v) (hnp : ¬ p.Nil) : p.lastButOneOfNotNil hnp ∈ p.support := by
  unfold Walk.lastButOneOfNotNil
  rw [mem_reverse_support]
  exact sndOfNotNil_mem_support p.reverse (Walk.lastButOneOfNotNil.proof_1 p hnp)

lemma cycle_neq_not_nil (p : G.Walk u u) (hpc : p.IsCycle) : ¬p.Nil := by
  intro hp
  apply hpc.1.2
  rw [← @Walk.length_eq_zero_iff]
  exact Walk.nil_iff_length_eq.mp hp

lemma support_exists_getVert (p : G.Walk v w) (h : u ∈ p.support) : ∃ n, p.getVert n = u := by
  obtain ⟨q, r, hqr⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp h
  use q.length
  rw [hqr]
  rw [@Walk.getVert_append]
  simp only [lt_self_iff_false, ↓reduceIte, ge_iff_le, le_refl, tsub_eq_zero_of_le,
    Walk.getVert_zero]

lemma support_exists_getVert' (p : G.Walk v w) (h : u ∈ p.support) : ∃ n, p.getVert n = u ∧ n ≤ p.length := by
  obtain ⟨q, r, hqr⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp h
  use q.length
  rw [hqr]
  rw [@Walk.getVert_append]
  simp only [lt_self_iff_false, ↓reduceIte, ge_iff_le, le_refl, tsub_eq_zero_of_le,
    Walk.getVert_zero, Walk.length_append, le_add_iff_nonneg_right, zero_le, and_self]

@[simp]
lemma cons_getVert_succ (p : G.Walk v w) (h : G.Adj u v) : (Walk.cons h p).getVert n.succ = p.getVert n := by
  rfl

lemma support_tail_length (p : G.Walk v w) : p.support.tail.length = p.length := by
  match p with
  | .nil => simp only [Walk.support_nil, List.tail_cons, List.length_nil, Walk.length_nil]
  | .cons _ _ => simp only [Walk.support_cons, List.tail_cons, Walk.length_support, Walk.length_cons]

lemma support_length (p : G.Walk v w) : p.support.length = p.length + 1 := by
  match p with
  | .nil => simp only [Walk.support_nil, List.length_singleton, Walk.length_nil, zero_add]
  | .cons _ _ => simp only [Walk.support_cons, List.length_cons, Walk.length_support,
    Nat.succ_eq_add_one, Walk.length_cons]

lemma getVert_nonZero (p : G.Walk v w) (h : G.Adj u v) (hn : 0 < n) : (Walk.cons h p).getVert n = p.getVert (n - 1) := by
  have : ∃ (i : ℕ), i.succ = n := by
    use (n - 1)
    exact Nat.sub_one_add_one_eq_of_pos hn
  obtain ⟨i, hi⟩ := this
  rw [← hi]
  simp only [Nat.succ_eq_add_one, cons_getVert_succ, add_tsub_cancel_right]

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
      rw [getVert_nonZero _ _  (Nat.zero_lt_of_ne_zero hn)]
      rw [get?_nonZero _ _ hn]
      exact getVert_support_get q (by
        rw [@Walk.length_cons] at h2
        exact Nat.sub_le_of_le_add h2
        )
lemma getVert_tail_support_get (p : G.Walk u v) (hnp: ¬ p.Nil) : (p.tail hnp).getVert n = p.getVert (n + 1) :=
  p.notNilRec (by
    intro u v w h q
    simp only [cons_getVert_succ]
    rw [@cons_tail]
    ) hnp

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

theorem toSubgraph_getVert_succ {u v} (w : G.Walk u v) {i : ℕ} (hi : i < w.length) :
    (w.toSubgraph).Adj (w.getVert i) (w.getVert (i + 1)) := by
  induction w generalizing i with
  | nil => cases hi
  | cons hxy i' ih =>
    cases i
    · simp only [Walk.toSubgraph, Walk.getVert_zero, zero_add, cons_getVert_succ, Subgraph.sup_adj,
      subgraphOfAdj_adj, true_or]
    · simp only [Walk.toSubgraph, cons_getVert_succ, Subgraph.sup_adj, subgraphOfAdj_adj, Sym2.eq,
      Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
      right
      exact ih (Nat.succ_lt_succ_iff.mp hi)

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
        simp only [Walk.getVert_zero, zero_add, cons_getVert_succ]
        constructor
        · left
          exact ⟨h1.1.symm, h1.2.symm⟩
        · simp only [Walk.length_cons, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]
      | inr h2 =>
        use 0
        simp only [Walk.getVert_zero, zero_add, cons_getVert_succ]
        constructor
        · right
          exact ⟨h2.1.symm, h2.2.symm⟩
        · simp only [Walk.length_cons, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]
    | inr hr =>
      obtain ⟨i, hi⟩ := toSubgraph_adj_exists _ hr
      use (i + 1)
      simp only [cons_getVert_succ]
      constructor
      · exact hi.1
      · simp only [Walk.length_cons, add_lt_add_iff_right, hi.2]

lemma cycle_two_neighbors (p : G.Walk u u) (hpc : p.IsCycle) (h : v ∈ p.support): (p.toSubgraph.neighborSet v).ncard = 2 := by
  unfold Subgraph.neighborSet
  obtain ⟨n, hn⟩ := support_exists_getVert p h
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
          have := toSubgraph_getVert_succ p (by omega : n - 1 < p.length)
          rw [h'] at this
          exact this.symm
        | inr hr =>
          simp only [Set.mem_setOf_eq]
          rw [hr, ← hn]
          exact toSubgraph_getVert_succ _ hbounds.2

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
          have := toSubgraph_getVert_succ p (by omega : 0 < p.length)
          simpa using this
        | inr hr =>
          rw [hr]
          have hadj := toSubgraph_getVert_succ p (by omega : p.length - 1 < p.length)
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

@[simp]
lemma Subgraph.symDiff_verts (M : Subgraph G) (C : Subgraph G) : (M.symDiff C).verts = M.verts ∪ C.verts := by rfl

@[simp]
lemma Subgraph.symDiff_adj (M : Subgraph G) (C : Subgraph G) : (M.symDiff C).Adj v w = ((¬ M.Adj v w ∧ C.Adj v w) ∨ (M.Adj v w ∧ ¬ C.Adj v w)) := rfl


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

lemma SimpleGraph.subgraphOfAdj_IsMatching (h : G.Adj u v) : (G.subgraphOfAdj h).IsMatching := by
  intro w hw
  by_cases hwu : w = u
  · use v
    simp only [hwu.symm, subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, true_and,
      Prod.swap_prod_mk]
    intro y hy
    cases hy with
    | inl hl => exact hl.symm
    | inr hr => rw [← hr.1, hr.2]
  · have hwv : w = v := by
      simp only [subgraphOfAdj_verts, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      cases hw with
      | inl hl => exact (hwu hl).elim
      | inr hr => assumption
    use u
    simp only [hwv.symm, subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk, or_true, and_true, true_and]
    intro y hy
    cases hy with
    | inl hl => rw [hl.1, hl.2]
    | inr hr => exact hr.symm

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
      rw [subgraphOfAdj_support]
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
          rw [hl, @subgraphOfAdj_support]
          exact Set.mem_insert u _
        | inr hr =>
          rw [Walk.toSubgraph, Subgraph.support_sup]
          right
          exact (Walk.mem_toSubgraph_support_mem_support not_nil_cons _).mpr hr
termination_by p.length

@[simp]
lemma Walk.cons_sndOfNotNil (q : G.Walk v w) (hadj : G.Adj u v) : (Walk.cons hadj q).sndOfNotNil (not_nil_cons) = v := by
  unfold sndOfNotNil
  simp only [notNilRec_cons]


lemma Walk.getVert_one (p : G.Walk u v) (hnp : ¬ p.Nil) : p.getVert 1 = p.sndOfNotNil hnp :=
  p.notNilRec (by
    intro u v w h q
    simp only [cons_getVert_succ, getVert_zero, cons_sndOfNotNil]
    ) hnp


lemma Walk.toSubgraph_Adj_sndOfNotNil {p : G.Walk u v} (hnp : ¬ p.Nil) : p.toSubgraph.Adj u (p.sndOfNotNil hnp) := by
  have := toSubgraph_getVert_succ p (by
    rw [SimpleGraph.Walk.nil_iff_length_eq] at hnp
    exact Nat.zero_lt_of_ne_zero hnp
    : 0 < p.length)
  simp at this
  rw [Walk.getVert_one p hnp] at this
  exact this

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

lemma Walk.toSubgraph_adj_sndOfNotNil (p : G.Walk u w) (hnp : ¬ p.Nil) : p.toSubgraph.Adj u (p.sndOfNotNil hnp) :=
  p.notNilRec (by simp) hnp

lemma Walk.toSubgraph_append_le (p : G.Walk u v) (q : G.Walk v w) : p.toSubgraph ≤ (p.append q).toSubgraph := by
  rw [@toSubgraph_append]
  exact SemilatticeSup.le_sup_left p.toSubgraph q.toSubgraph

lemma Walk.toSubgraph_append_le' (p : G.Walk u v) (q : G.Walk v w) : q.toSubgraph ≤ (p.append q).toSubgraph := by
  rw [@toSubgraph_append]
  exact le_sup_right

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

      obtain ⟨n, hn⟩ := support_exists_getVert p (hx)
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
          have hadj := toSubgraph_getVert_succ p (by omega : n - 1 < p.length)
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
            have hadj := toSubgraph_getVert_succ p (by omega : n < p.length)
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
            apply hw'.1
            exact Walk.getVert_one p hnp
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
      rw [Walk.getVert_one p hnp] at hr
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
      simp only [Walk.cons_sndOfNotNil, ne_eq, Walk.toSubgraph, subgraphOfAdj_verts, id_eq,
        eq_mpr_eq_cast]

      split_ifs with h
      · exfalso
        have := (fpath.proof_1 hc (Walk.cons (hvw.adj_sub.symm) .nil) Walk.not_nil_cons hsub).choose_spec
        simp only [Walk.cons_sndOfNotNil, ne_eq] at this
        exact this.1 h
      · apply fpath_IsCycle
    refine ⟨hpc, ?_⟩
    have hpsc : p.toSubgraph = C := by
      unfold fpath
      simp only [Walk.cons_sndOfNotNil, ne_eq]
      split_ifs with h
      · exfalso
        have := (fpath.proof_1 hc (Walk.cons (hvw.adj_sub.symm) .nil) Walk.not_nil_cons hsub).choose_spec
        simp only [Walk.cons_sndOfNotNil, ne_eq] at this
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
  obtain ⟨w, hw⟩ := M.isPerfectMatching_iff.mp hM v
  use w

-- noncomputable def altWalk {v a b x : V} [Fintype V] [DecidableEq V] {G1 G2 : SimpleGraph V} {M1 : Subgraph G1} {M2 : Subgraph G2}[DecidableRel M1.Adj]
--   [DecidableRel M2.Adj] (hM1 : M1.IsPerfectMatching) (hM2 : M2.IsPerfectMatching) (p : G2.Walk v c) (hp : p.length ≥ 1) : G2.Walk c c :=
--   let w := p.sndOfNotNil (by
--     rw [@Walk.nil_iff_length_eq]
--     omega
--     )
--   if hv : v = a then
--     .cons (by
--       sorry
--         : G2.Adj c v) p
--   else
--     if hv' : v = x ∨ v = b then
--       .cons (by sorry : G2.Adj c a) (.cons (by sorry : G2.Adj a v) p)
--     else
--       have : Fintype.card V - (p.length + 1 + 1) < (Fintype.card V - (p.length + 1)) := by
--         sorry
--       if M1.Adj v w then

--         altWalk (-.cons (by sorry : G2.Adj (hM2.1 (hM2.2 v)).choose v) p) (by sorry)
--       else
--         altWalk (.cons (by sorry : G2.Adj (hM1.1 (hM1.2 v)).choose v) p) (by sorry)
-- termination_by Fintype.card V - p.support.length



lemma Walk.IsCycle.of_append_right {p : G.Walk u v} {q : G.Walk v u} (h : u ≠ v) (hcyc : (p.append q).IsCycle) : q.IsPath := by
  have := hcyc.2
  rw [SimpleGraph.Walk.tail_support_append, List.nodup_append] at this
  rw [@isPath_def, @support_eq_cons, @List.nodup_cons]
  exact ⟨this.2.2 (p.end_mem_tail_support_of_ne h), this.2.1⟩


lemma Walk.IsCycle.mem_endpoint {p : G.Walk u u} (h : p.IsCycle) : u ∈ p.toSubgraph.support := by
  rw [@Subgraph.mem_support]
  use p.sndOfNotNil (cycle_neq_not_nil p h)
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
  stop
  intro har
  have := hp.2
  rw [@List.nodup_iff_get?_ne_get?] at this
  obtain ⟨n, hn⟩ := support_exists_getVert' _ har
  obtain ⟨n', hn'⟩ := support_exists_getVert' _ hx
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
  rw [← tail_support_eq_support_tail _ hp.1.not_nil]

  rw [← getVert_support_get (p.tail hp.1.not_nil) (by
    rw [@Nat.sub_le_iff_le_add]
    rw [@Walk.length_tail_add_one]
    omega
    ) ]
  rw [← getVert_support_get (p.tail hp.1.not_nil) (by
    rw [@Nat.sub_le_iff_le_add]
    rw [@Walk.length_tail_add_one]
    omega
    ) ]
  simp only [Option.some.injEq]
  rw [getVert_tail_support_get]
  rw [getVert_tail_support_get]
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
  use p.sndOfNotNil hnp
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
      simp only [getVert_zero, zero_add, true_and, getVert_one _ hnp] at hi
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


lemma Walk.toSubgraph_snd {p : G.Walk u v} (hp : p.IsPath) (hnp : ¬ p.Nil) (h : p.toSubgraph.Adj u w) : p.sndOfNotNil hnp = w := by
  have hset := hp.start_neighbourSet_ncard hnp
  have hwmem : w ∈ p.toSubgraph.neighborSet u := by
    exact h
  have hsmem : (p.sndOfNotNil hnp) ∈ p.toSubgraph.neighborSet u  := by
    exact toSubgraph_adj_sndOfNotNil p hnp
  rw [Set.ncard_eq_one] at hset
  obtain ⟨v, hv⟩ := hset
  have := Set.eq_of_mem_singleton (hv ▸ hwmem)
  rw [this]
  exact Set.eq_of_mem_singleton (hv ▸ hsmem)

lemma Walk.IsCycle.IsAlternating_cons {p : G.Walk u v} {h : G.Adj v u} {M : Subgraph G} (hnp : ¬ p.Nil) (hcyc : (Walk.cons h p).IsCycle)
  (halt : p.toSubgraph.IsAlternating M) (ha : M.Adj u v  ↔ ¬ M.Adj u (p.sndOfNotNil hnp)) (hb : M.Adj v u ↔ ¬ M.Adj v (p.lastButOneOfNotNil (hnp)))
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
        rw [this]
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
        rw [this]
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
  (halt : p.toSubgraph.IsAlternating M) (ha : M.Adj t u  ↔ ¬ M.Adj u (p.sndOfNotNil hnp))
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
    
    sorry

theorem tutte [Fintype V] [Inhabited V] [DecidableEq V] [DecidableRel G.Adj] :
    (∃ (M : Subgraph G) , M.IsPerfectMatching) ↔
      (∀ (u : Set V),
        cardOddComponents ((⊤ : G.Subgraph).deleteVerts u).coe ≤ u.ncard) := by
  constructor
  {
    rintro ⟨M, hM⟩ u
    unfold cardOddComponents
    let f : {c : ConnectedComponent ((⊤ : Subgraph G).deleteVerts u).coe | ConnectedComponent.isOdd c} → u :=
      fun c => Exists.choose (OddComponentHasNodeMatchedOutside M hM u c c.2)

    let g : ConnectedComponent ((⊤ : Subgraph G).deleteVerts u).coe → V := fun c =>
      if h : Odd (Fintype.card c.supp) then f ⟨ c , (by
            rw [← ConnectedComponent.isOdd_iff] at h
            exact h
      ) ⟩ else default

    exact Set.ncard_le_ncard_of_injOn g (by
      intro a ha
      dsimp at ha
      have h : g a = f ⟨ a , ha ⟩ := by
        rw [dite_eq_iff]
        left
        use (ConnectedComponent.isOdd_iff _).mp ha
        done
      rw [h]
      dsimp
      rw [Set.mem_def]
      -- simp only [ConnectedComponent.mem_supp_iff, Subtype.exists, Set.mem_diff, Set.mem_univ,
      --   true_and, exists_and_left]
      apply Subtype.prop
      ) (by
        intro x hx y hy hxy
        have h : g x = f ⟨ x , hx ⟩ := by
          rw [dite_eq_iff]
          left
          use (ConnectedComponent.isOdd_iff _).mp hx
          done
        have h' : g y = f ⟨ y , hy ⟩ := by
          rw [dite_eq_iff]
          left
          use (ConnectedComponent.isOdd_iff _).mp hy
          done
        rw [h, h'] at hxy

        dsimp at hxy
        obtain ⟨ v , hv ⟩ := (OddComponentHasNodeMatchedOutside M hM u x hx).choose_spec
        obtain ⟨ v' , hv' ⟩ := (OddComponentHasNodeMatchedOutside M hM u y hy).choose_spec


        have ⟨ w , hw ⟩ := (Subgraph.isPerfectMatching_iff M).mp hM (f ⟨ x , hx ⟩)
        have h'' := hw.2 _ hv.1.symm
        rw [hxy] at hw
        have h''' := hw.2 _ hv'.1.symm
        rw [← h'''] at h''
        rw [← ((ConnectedComponent.mem_supp_iff x v).mp hv.2)]
        rw [← ((ConnectedComponent.mem_supp_iff y v').mp hv'.2)]
        rw [Subtype.val_injective h'']
      ) (Set.toFinite u)
  }
  {

    contrapose!
    intro h
    if hvOdd : Odd (Finset.univ : Finset V).card
    then
      use ∅
      simp only [Set.ncard_empty, Subgraph.induce_verts, Subgraph.verts_top]
      have : Odd (Fintype.card ↑((⊤ : Subgraph G).deleteVerts ∅).verts) := by
        simp only [Finset.card_univ, Nat.odd_iff_not_even, Subgraph.deleteVerts_empty,
          Subgraph.verts_top, Fintype.card_congr (Equiv.Set.univ V)] at *
        exact hvOdd
      have ⟨ c , hc ⟩:= oddComponent ((⊤ : Subgraph G).deleteVerts ∅).coe this
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
            haveI := Gmax.hDec
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
      have ⟨ f , hf ⟩ := Classical.inhabited_of_nonempty (Function.Embedding.nonempty_of_card_le h')

      if h' : ∀ (K : ConnectedComponent Gsplit.coe), Gsplit.coe.IsClique K.supp
      then
        stop
        let f' := fun (c : {(c : ConnectedComponent Gsplit.coe) | ConnectedComponent.isOdd c}) => (componentExistsRep c.val).choose
        have f'mem  (c : {(c : ConnectedComponent Gsplit.coe) | ConnectedComponent.isOdd c}) : f' c ∈ c.val.supp := by
          simp only [Set.mem_setOf_eq, ConnectedComponent.mem_supp_iff]
          rw [← (componentExistsRep c.val).choose_spec]


        let M1 : Subgraph Gmax.G' := (⨆ (c : {c : ConnectedComponent Gsplit.coe | ConnectedComponent.isOdd c}),
          let v := f' c


          let M := (oddCliqueAlmostMatches (f'mem c) (h' c) (c.val.isOdd_iff.mp c.2)).choose

          SimpleGraph.Subgraph.coeSubgraph M ⊔ Gmax.G'.subgraphOfAdj ((by
            apply (f c).2
            intro hfcv
            apply Set.not_mem_diff_of_mem (f c).2
            rw [hfcv]
            exact Subtype.mem v
            ) : Gmax.G'.Adj v (f c) )
          )
        have hM1 : M1.IsMatching := by
          stop
          exact iSup_IsMatching (by
            intro i
            dsimp
            let oddMatches := oddCliqueAlmostMatches (f'mem i) (h' i) (i.val.isOdd_iff.mp i.2)
            exact sup_IsMatching (by

              exact coe_IsMatching (oddMatches.choose_spec).2
              ) (by exact subgraphOfAdj_IsMatching _)
                (by
                  rw [subgraphOfAdj_support]
                  rw [disjoint_pair]
                  have := (f' i).2
                  constructor
                  · intro hf'i
                    have := SimpleGraph.Subgraph.support_subset_verts _ hf'i
                    simp at this
                    exact (oddCliqueAlmostMatchesDoesNotContainNode (f'mem i) (h' i) (i.val.isOdd_iff.mp i.2)) this
                  · intro hfi
                    have := SimpleGraph.Subgraph.support_subset_verts _ hfi
                    rw [coe_verts] at this
                    have := Set.image_val_subset this
                    rw [SimpleGraph.Subgraph.deleteVerts_verts] at this
                    apply ((Set.mem_diff _).mp this).2
                    exact Subtype.coe_prop (f i)
                  )
            ) (by

              intro i j hij s hs1 hs2
              have hi := oddCliqueAlmostMatchesSubset (f'mem i) (h' i) (i.val.isOdd_iff.mp i.2)
              have hj := oddCliqueAlmostMatchesSubset (f'mem j) (h' j) (j.val.isOdd_iff.mp j.2)
              simp only [Subgraph.induce_verts, Subgraph.verts_top, Set.coe_setOf, ne_eq,
                Set.mem_setOf_eq, Set.le_eq_subset, Set.bot_eq_empty] at *
              rw [sup_support_eq_support_union] at *
              rw [Set.subset_empty_iff]
              rw [Set.eq_empty_iff_forall_not_mem]
              intro v hv
              cases hs1 hv with
              | inl hl =>
                have hii := SimpleGraph.Subgraph.support_subset_verts _ hl
                rw [coe_verts] at hii
                have hi' := hi (Set.mem_of_mem_image_val hii)
                cases hs2 hv with
                | inl hl' =>
                  have := SimpleGraph.Subgraph.support_subset_verts _ hl'
                  rw [coe_verts] at this
                  have hj' := hj (Set.mem_of_mem_image_val this)
                  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at *
                  rw [hj'] at hi'
                  apply hij
                  exact Subtype.eq (id hi'.symm)
                | inr hr' =>
                  rw [subgraphOfAdj_support] at hr'
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
                    -- have := (ConnectedComponentSubsetVerts _ _) hi'
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
                  rw [coe_verts] at hii
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

        let M2 : Subgraph Gmax.G' := (⨆ (c : {c : ConnectedComponent Gsplit.coe | (Even (Set.ncard (c.supp)))}),
          Subgraph.coeSubgraph (evenCliqueMatches c.val.supp (h' c) c.2).choose )

        have hM2 : M2.IsMatching := by
          stop
          exact iSup_IsMatching (by
            intro i
            exact coe_IsMatching (by
              exact (evenCliqueMatches i.val.supp (h' i) i.2).choose_spec.2
              )
            ) (by
              intro i j hij s hsi hsj
              simp only [Subgraph.induce_verts, Subgraph.verts_top, Set.coe_setOf, ne_eq,
                Set.mem_setOf_eq, ConnectedComponent.mem_supp_iff, Subtype.forall, Set.le_eq_subset,
                Set.bot_eq_empty] at *
              let hispec := (evenCliqueMatches i.val.supp (h' i) i.2).choose_spec
              have hi := hispec.1
              rw [SimpleGraph.Subgraph.IsMatching.support_eq_verts hispec.2] at hi

              let hjspec := (evenCliqueMatches j.val.supp (h' j) j.2).choose_spec
              have hj := hjspec.1
              rw [SimpleGraph.Subgraph.IsMatching.support_eq_verts hjspec.2] at hj

              rw [Set.subset_empty_iff]
              rw [Set.eq_empty_iff_forall_not_mem]
              intro v hv

              have hii := SimpleGraph.Subgraph.support_subset_verts _ (hsi hv)
              rw [coe_verts] at hii
              have hi' := (subset_of_eq hi) (Set.mem_of_mem_image_val hii)

              have hjj := SimpleGraph.Subgraph.support_subset_verts _ (hsj hv)
              rw [coe_verts] at hjj
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
            rw [@coe_verts] at hl
            rw [@Set.mem_union]
            left
            rw [@Set.mem_image] at *
            obtain ⟨ j , hj ⟩ := hl
            have hji := (oddCliqueAlmostMatchesSubset (f'mem i) (h' i) (i.val.isOdd_iff.mp i.2)) hj.1
            use ⟨ v , Set.image_val_subset ⟨ j , hj ⟩ ⟩
            refine ⟨ ?_ , rfl ⟩
            rw [@Set.mem_iUnion]
            use ⟨ i.1 , (by

              have := i.2
              rw [@Set.mem_setOf] at *
              simp only [Set.mem_setOf_eq] at this
              rw [@ConnectedComponent.isOdd_iff] at this
              rw [Set.ncard_eq_toFinset_card']
              rw [@Set.toFinset_card]
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
                rw [@ConnectedComponent.isOdd_iff] at this
                rw [Set.ncard_eq_toFinset_card']
                rw [@Set.toFinset_card]
                exact this
                ) ⟩
            | inr h2 =>
              right
              rw [h2]
              exact Subtype.coe_prop (f i)

        let evenComVerts := (⋃ (c : {c : ConnectedComponent Gsplit.coe | (Even (Set.ncard (c.supp)))}),
            c.val.supp )
        have hM2sub : M2.verts ⊆ evenComVerts := by
          intro v hv
          rw [@Subgraph.verts_iSup] at hv
          obtain ⟨ i , hi ⟩ := Set.mem_iUnion.mp hv
          have hi' := hi
          rw [@coe_verts] at hi
          rw [Set.mem_image] at *

          obtain ⟨ x , hx ⟩ := hi
          use ⟨ x , Subtype.coe_prop x ⟩
          constructor
          · rw [Set.mem_iUnion]
            use i
            rw [← (evenCliqueMatches i.val.supp (h' i) i.2).choose_spec.1]
            rw [SimpleGraph.Subgraph.IsMatching.support_eq_verts (evenCliqueMatches i.val.supp (h' i) i.2).choose_spec.2]
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
          rw [@coe_verts]

          have := (evenCliqueMatches (i'.1).supp (h' i'.1) i'.2).choose_spec
          rw [← (SimpleGraph.Subgraph.IsMatching.support_eq_verts (this.2))]
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
          let i'' : Set.Elem {c : ConnectedComponent Gsplit.coe | ConnectedComponent.isOdd c} := ⟨ i', by
            simp only [Set.mem_setOf_eq]
            rw [ConnectedComponent.isOdd_iff]
            have := i'.2
            rw [@Set.mem_setOf] at this
            rw [← Set.toFinset_card]
            rw [← Nat.card_eq_card_toFinset]
            rwa [@Set.Nat.card_coe_set_eq]
            ⟩
          use i''
          rw [Subgraph.verts_sup]
          rw [Set.mem_union]
          rw [coe_verts]
          have := (oddCliqueAlmostMatches (f'mem i'') (h' i''.1) ((ConnectedComponent.isOdd_iff i''.1).mp i''.2)).choose_spec
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
          stop
          refine sup_IsMatching hM1 hM2 ?hd
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
          stop
          have := SimpleGraph.Subgraph.IsMatching.even_card hM12
          rw [Set.ncard_eq_toFinset_card' ]
          exact this
        rw [← @Nat.even_iff_not_odd] at hvOdd

        have hnM12Even : Even ((Set.univ : Set V) \ (M1 ⊔ M2).verts).ncard := by
          stop
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


        obtain ⟨ M' , hM' ⟩ := evenCliqueMatches ((Set.univ : Set V) \ (M1 ⊔ M2).verts) (by
          stop
          intro v hv w hw hvw
          have : v ∈ S := by
            by_contra hc
            let v' : Gsplit.verts := ⟨ v , (by
              rw [SimpleGraph.Subgraph.deleteVerts_verts ]
              rw [Set.mem_diff]
              exact ⟨ by trivial , hc ⟩
              ) ⟩
            if heven : Even (Gsplit.coe.connectedComponentMk v').supp.ncard
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
           : Gmax.G'.IsClique ((Set.univ : Set V) \ (M1 ⊔ M2).verts) ) hnM12Even
        have conMatch : ((M1 ⊔ M2) ⊔ M').IsMatching := sup_IsMatching hM12 hM'.2 (by
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
            rw [← SimpleGraph.Subgraph.IsMatching.support_eq_verts hM'.2]
            rw [hM'.1]
            exact Set.mem_diff_of_mem (by trivial) h
        exact Gmax.hMatchFree ((M1 ⊔ M2) ⊔ M') ⟨ conMatch, conSpanning ⟩
    else
      push_neg at h'
      obtain ⟨K, hK⟩ := h'
      rw [isNotClique_iff] at hK
      obtain ⟨x, ⟨y, hxy⟩⟩ := hK


      obtain ⟨p , hp⟩ := SimpleGraph.Reachable.exists_path_of_dist (reachable_in_connected_component_induce K x y)


      obtain ⟨x, ⟨a, ⟨b, hxab⟩⟩⟩ := verts_of_walk p hp.2 (dist_gt_one_of_ne_and_nadj (Walk.reachable p) hxy.1 hxy.2)

      have ha : (a : V) ∉ S := by exact deleteVerts_verts_notmem_deleted _
      have hc : ∃ (c : V), ¬ Gmax.G'.Adj a c ∧ (a : V) ≠ c := by
        stop
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

      have hG1 : Gmax.G' < G1 := by
        stop
        apply union_gt_iff.mpr
        rw [@singleEdge_le_iff]
        intro h
        apply hxab.2.2.1
        rw [@induce_eq_coe_induce_top]
        simp only [Subgraph.coe_adj, Subgraph.induce_verts, Subgraph.induce_adj, Subgraph.top_adj]
        refine ⟨Subtype.coe_prop x, Subtype.coe_prop b, ?_⟩
        rw [@Subgraph.deleteVerts_adj]
        simp only [Subgraph.verts_top, Set.mem_univ, deleteVerts_verts_notmem_deleted,
          not_false_eq_true, Subgraph.top_adj, h, and_self]

      have hG2 : Gmax.G' < G2 := by
        apply union_gt_iff.mpr
        rw [@singleEdge_le_iff]
        intro h
        exact hc.1 h

      obtain ⟨M1, hM1⟩ := Decidable.not_forall_not.mp (Gmax.hMaximal _ hG1)
      obtain ⟨M2, hM2⟩ := Decidable.not_forall_not.mp (Gmax.hMaximal _ hG2)

      have hM1' : M1.Adj x b := by
        stop
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
        stop
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
        stop
        rw [SimpleGraph.Subgraph.induce_adj]
        exact ⟨ (supportImpMemSupp hu), by
          have memSup := mem_supp_of_adj _ _ _ (suppImpMemSupp hu) (SimpleGraph.Subgraph.Adj.coe h)
          exact Set.mem_image_val_of_mem (hCycles v) memSup
          , h⟩

      have cycleAlt : cycle.IsAlternating M2' := by
        intro u v w hvw huv huw
        exact Subgraph.symDiffPerfectMatchingsAlternating hM1'' hM2'' u v w hvw (hadjImp huv) (hadjImp huw)

      have cycleIsCycle : cycle.IsCycle := by
        stop
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
          · save
            obtain ⟨p, _⟩ := SimpleGraph.Reachable.exists_walk_of_dist this
            push_neg at hvc
            have hnp : ¬ p.Nil:= p.not_nil_of_ne (by
              intro h
              apply hvc
              rwa [Subtype.mk.injEq] at h
              )
            have := hl (p.sndOfNotNil hnp)
            apply this
            rw [SimpleGraph.Subgraph.mem_neighborSet]
            exact SimpleGraph.Walk.adj_sndOfNotNil hnp
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
          stop
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
          stop
          rw [sup_adj, sup_adj]
          right
          simp only [singleEdge_Adj, and_self, or_true]
        have hGsplitadjax : Gmax.G'.Adj ↑↑a ↑↑x := by
          stop
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
          stop
          intro hxc
          apply hc.1
          rw [hxc]
          exact hGsplitadjax

        have haneb : a.val.val ≠ b.val.val := by
          stop
          intro h
          have := hxab.2.1
          rw [@induce_eq_coe_induce_top] at this
          rw [@Subgraph.coe_adj] at this
          apply this.ne
          exact Subtype.val_injective h


        have hrn : ¬ r.Nil := SimpleGraph.Walk.not_nil_of_ne hcnex.symm
        have hqrn : ¬ q.reverse.Nil :=  SimpleGraph.Walk.not_nil_of_ne hcnex.symm

        have hqlpl : q.length ≤ p.length := by
          stop
          rw [hqr]
          simp only [Walk.length_append, le_add_iff_nonneg_right, zero_le]

        by_cases hqca : q.toSubgraph.Adj c a
        · have hnars : a.val.val ∉ r.support := hp.1.decompose_mem_support_part hqr (q.toSubgraph_Adj_mem_support (q.toSubgraph.adj_symm hqca))
              hG12adjca.ne.symm hG12adjax.ne




          by_cases hqxb : q.toSubgraph.Adj x.val.val b
          · let p' := Walk.cons (hG12adjca) (Walk.cons hG12adjax r)
            have hp'c : p'.IsCycle := by
              rw [@Walk.cons_isCycle_iff]
              simp only [Walk.cons_isPath_iff]
              refine ⟨⟨(hqr ▸ hp.1).of_append_right hcnex, hnars⟩, ?_⟩
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

            have hp'tsac : p'.toSubgraph.Adj (↑↑a) c := by
              exact
                Subgraph.adj_symm p'.toSubgraph
                  (Walk.cons_to_Subgraph_first_adj hG12adjca (Walk.cons hG12adjax r))

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

              sorry

            use p'.toSubgraph


          · let p' := Walk.cons (hG12adjca) (Walk.cons (by sorry : G12.Adj a (r.sndOfNotNil hrn)) (r.tail hrn))
            have hp'c : p'.IsCycle := by sorry
            have hcss : c ∈ p'.toSubgraph.support := by sorry
            have hsubcyc : p'.toSubgraph.IsCycle := (p'.toSubgraph.IsCycle_iff hcss).mpr ⟨p', ⟨hp'c, rfl⟩⟩
            sorry
        · by_cases hqxb : q.toSubgraph.Adj x.val.val b
          · let p' := Walk.cons hG12adjca (Walk.cons (by sorry : G12.Adj a (q.reverse.sndOfNotNil hqrn)) (q.reverse.tail hqrn))
            have hp'c : p'.IsCycle := by sorry
            have hcss : c ∈ p'.toSubgraph.support := by sorry
            have hsubcyc : p'.toSubgraph.IsCycle := (p'.toSubgraph.IsCycle_iff hcss).mpr ⟨p', ⟨hp'c, rfl⟩⟩
            sorry
          · let p' := Walk.cons hG12adjca (Walk.cons hG12adjax q.reverse)
            have hp'c : p'.IsCycle := by sorry
            have hcss : c ∈ p'.toSubgraph.support := by sorry
            have hsubcyc : p'.toSubgraph.IsCycle := (p'.toSubgraph.IsCycle_iff hcss).mpr ⟨p', ⟨hp'c, rfl⟩⟩
            sorry

        -- let p' := p.coeWalk
        -- have hnp' := p.coeWalkNotNil hnp
        -- let x2 := p'.sndOfNotNil hnp'
        -- let c2 := p'.lastButOneOfNotNil hnp'

        -- have G12ab : G12.Adj a b := by
        --   rw [sup_adj]
        --   rw [sup_adj]
        --   left ; left
        --   have := hxab.2.1
        --   simp only [comap_adj, Function.Embedding.coe_subtype, Subgraph.coe_adj] at this
        --   exact Gsplit.coe_adj_sub _ _ this

        -- let p' := p.coeWalk
        -- by_cases hxb : x2 = b
        -- · by_cases hac : c2 = a
        --   · let pC := Walk.cons (hxb ▸ G12ab) (p'.tail hnp')

        --     sorry
        --   · sorry

        -- · sorry


      · stop
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
              have hcca : cycles.Adj c ↑↑a := by sorry
              have : a.val.val ∈ (cycleComp.supp : Set V) := by
                -- sorry
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



      -- have hM1' : M1'.IsPerfectMatching := by exact?

      -- let auxAltWalk (l : List V) (h : l.length > 1) : List V :=
      --   let v := l.head (by
      --     intro hl
      --     rw [List.length_eq_zero.mpr hl] at h
      --     omega
      --     )
      --   let w := l.get ⟨1, h⟩
      --   if hv : v = a then
      --     c :: []
      --   else
      --     if hv' : v = x ∨ v = b then
      --       c :: a :: []
      --     else
      --       if M1.Adj v w then
      --         (hM2.1 (hM2.2 v)).choose :: []
      --       else
      --         (hM1.1 (hM1.2 v)).choose :: []


      -- let C := f ((hM1.1 (hM1.2 c)).choose :: c :: []) (by simp)





      -- let C := altWalk (.cons (by sorry : G2.Adj (hM1.1 (hM1.2 c)).choose c) Walk.nil) (by sorry)




  }


-- lemma cycle_two_neighbors (p : G.Walk u u) (hpc : p.IsCycle) (h : v ∈ p.support): (p.toSubgraph.neighborSet v).ncard = 2 := by
--   unfold Subgraph.neighborSet
--   by_cases hu : v = u
--   · sorry
--   ·
--   --   have hv' : v ∈ p.support.tail := by
--   --     cases (Walk.mem_support_iff _).mp h with
--   --     | inl h1 => exact (hu h1).elim
--   --     | inr h2 => exact h2
--     -- rw [← tail_support_eq_support_tail p (cycle_neq_not_nil p hpc)]

--     obtain ⟨q, r, hqr⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp h
--     rw [hqr]
--     rw [SimpleGraph.Walk.toSubgraph_append]
--     rw [@Set.ncard_eq_two]
--     let firstNode := r.sndOfNotNil (Walk.not_nil_of_ne hu)
--     let secondNode := q.lastButOneOfNotNil (by
--       exact Walk.not_nil_of_ne fun a => hu a.symm
--       )
--     use firstNode
--     use secondNode
--     constructor
--     · intro hrq
--       have hf : firstNode ∈ p.support := by
--         rw [hqr, SimpleGraph.Walk.mem_support_append_iff]
--         right
--         exact sndOfNotNil_mem_support r (Walk.not_nil_of_ne hu)
--       have := hpc.1.1
--       by_cases h2 : secondNode = u
--       ·
--         sorry
--       · sorry
--     · sorry
