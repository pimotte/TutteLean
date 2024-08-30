import TutteLean.Defs
import TutteLean.Clique
import TutteLean.Set
import TutteLean.Walk

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}


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
