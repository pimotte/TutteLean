import TutteLean.Defs
import TutteLean.Clique
import TutteLean.ConnectedComponent
import TutteLean.Subgraph

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

def core (G : SimpleGraph V) : Set V := {v : V | ∀ w, v ≠ w → G.Adj w v}

lemma deleteVerts_core : ((⊤ : Subgraph G).deleteVerts G.core).verts = Set.univ \ G.core := by
  simp only [Subgraph.induce_verts, Subgraph.verts_top]


def slices (G : SimpleGraph V) : Subgraph G := ((⊤ : Subgraph G).deleteVerts (core G))

def oddVerts (G : SimpleGraph V) : Set V := Subtype.val '' ((fun c ↦ c.exists_vert.choose) '' {(c : ConnectedComponent G.slices.coe) | Odd (c.supp.ncard)})

lemma oddVerts_subset_slices : oddVerts G ⊆ G.slices.verts := by
  intro _ hv
  rw [oddVerts, Set.mem_image] at hv
  obtain ⟨v, heq⟩ := hv
  rw [← heq.2]
  exact v.2

lemma odd_connectedComponent_of_oddVert {v : V} (h : v ∈ oddVerts G) :
  Odd ((G.slices.coe.connectedComponentMk ⟨v, oddVerts_subset_slices h⟩).supp.ncard) := by
    simp_rw [oddVerts, Set.mem_image] at h
    obtain ⟨w, hw⟩ := h
    obtain ⟨c, hc⟩ := hw.1
    rw [@Set.mem_setOf] at hc
    have : G.slices.coe.connectedComponentMk w = c := by
      rw [← hc.2]
      exact c.exists_vert.choose_spec
    rw [(SetCoe.ext hw.2.symm : ⟨v, oddVerts_subset_slices h⟩ = w), this]
    exact hc.1

lemma oddVerts_core_disjoint : Disjoint G.oddVerts G.core := by
  rw [@Set.disjoint_left]
  intro v hv
  rw [oddVerts, Set.mem_image] at hv
  simp_rw [Set.mem_image] at hv
  obtain ⟨w, hw⟩ := hv
  obtain ⟨c, hc⟩ := hw.1
  rw [← hw.2, ← hc.2]
  exact deleteVerts_verts_notmem_deleted _


theorem tutte_part' [Fintype V] [Inhabited V] [DecidableEq V] [DecidableRel G.Adj]
  (hveven : Even (Fintype.card V))
  (h : {c : G.slices.coe.ConnectedComponent | Odd (c.supp.ncard)}.ncard ≤ G.core.ncard)
  (h' : ∀ (K : G.slices.coe.ConnectedComponent), G.slices.coe.IsClique K.supp) :
    ∃ (M : Subgraph G), M.IsPerfectMatching := by
  classical
  simp only [← Set.Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at h

  have ⟨ f , hf ⟩ := Classical.inhabited_of_nonempty (Function.Embedding.nonempty_of_card_le h)
  let rep := fun (c : ConnectedComponent G.slices.coe) => c.exists_vert.choose
  let oddVerts := Subtype.val '' (rep '' {(c : G.slices.coe.ConnectedComponent) | Odd (c.supp.ncard)})


  let g : V → V := fun v ↦ if h : v ∈ oddVerts then f ⟨(G.slices.coe.connectedComponentMk ⟨v, oddVerts_subset_slices h⟩), odd_connectedComponent_of_oddVert h⟩ else Classical.arbitrary V

  have gMemS {v : V} (h : v ∈ oddVerts) : (g v) ∈ G.core := by
    unfold_let g
    dsimp
    split_ifs
    apply Subtype.coe_prop

  have hdg : Disjoint oddVerts (g '' oddVerts) := by
    rw [@Set.disjoint_left]
    intro v hv hgv
    apply Set.disjoint_left.mp oddVerts_core_disjoint hv
    rw [Set.mem_image] at hgv
    obtain ⟨v', hv'⟩ := hgv
    rw [← hv'.2]
    exact gMemS hv'.1

  have aux {x : V} {cx : G.slices.coe.ConnectedComponent} (h : (Subtype.val ∘ rep) cx = x) (hx : x ∈ G.slices.verts): G.slices.coe.connectedComponentMk ⟨x, hx⟩ = cx := by
    rw [← @ConnectedComponent.mem_supp_iff]
    simp only [Function.comp_apply] at h
    unfold_let rep at h
    have := cx.exists_vert.choose_spec
    rw [← this]
    simp only at h
    subst h
    simp only [Subtype.coe_eta, ConnectedComponent.mem_supp_iff]

  have compInj : Function.Injective (fun (v : oddVerts) => (G.slices.coe.connectedComponentMk ⟨v.1, oddVerts_subset_slices v.2⟩)) := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    dsimp at *
    have hx' := oddVerts_subset_slices hx
    have hy' := oddVerts_subset_slices hy
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
    rw [core, @Set.mem_setOf] at this
    apply this v
    intro h
    apply Set.disjoint_left.mp oddVerts_core_disjoint hv
    exact (h ▸ gMemS hv)

  let M1 : Subgraph G := Subgraph.ofFunction g hadj

  have hM1 : M1.IsMatching := by
    unfold_let M1
    exact Subgraph.isMatching_ofFunction g hadj gInjOn hdg

  have memImKNotS {v : V} (K : G.slices.coe.ConnectedComponent)
    (h : v ∈ Subtype.val '' K.supp) : v ∉ G.core := by
    intro hv
    rw [Set.mem_image] at h
    obtain ⟨v', hv'⟩ := h
    have := v'.2
    simp only [Subgraph.induce_verts, Subgraph.verts_top, Set.mem_diff] at this
    rw [hv'.2] at this
    exact this.2 hv


  have memSuppOddIsRep {v : V} (K : G.slices.coe.ConnectedComponent)
    (h : v ∈ Subtype.val '' K.supp) (h' : v ∈ oddVerts) : K.exists_vert.choose.val = v := by
    unfold_let oddVerts at h'
    rw [Set.mem_image] at h'
    simp_rw [Set.mem_image] at h'
    obtain ⟨x, ⟨⟨c, hc⟩, hx⟩⟩ := h'
    rw [← hx] at h ⊢
    rw [← hc.2] at h ⊢
    unfold_let rep at h ⊢

    rw [Subtype.val_injective.mem_set_image] at h

    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at h
    have := c.exists_vert_mem_supp
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at this
    rw [this] at h
    rw [h]

  have repMemOdd {K : ((⊤ : Subgraph G).deleteVerts {v : V | ∀ w, v ≠ w → G.Adj w v}).coe.ConnectedComponent}
    (h : Odd K.supp.ncard) : K.exists_vert.choose.val ∈ oddVerts := by
    unfold_let oddVerts
    rw [Set.mem_image]
    simp_rw [Set.mem_image]
    use K.exists_vert.choose
    refine ⟨?_, rfl⟩
    use K
    exact ⟨h, rfl⟩

  have evenKsubM1 (K : G.slices.coe.ConnectedComponent)
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
          have hc2 := (G.slices.coe.connectedComponentMk (a.exists_vert).choose).exists_vert.choose_spec
          rw [← hc1]
          rw [← hc2]

          -- unfold_let Gsplit
          rw [← hv] at h
          rw [Set.ncard_image_of_injective _ Subtype.val_injective] at h
          exact h

        · obtain ⟨a, ha⟩ := hr
          rw [← ha.2] at hv
          have := gMemS (repMemOdd ha.1)
          apply memImKNotS _ hv
          exact this
      rw [this]
      exact h
    · rw [← @Nat.odd_iff_not_even] at h
      have kMem : K.exists_vert.choose.val ∉ (Subtype.val '' K.supp \ M1.verts) := by
        rw [@Set.mem_diff]
        push_neg
        intro h'
        unfold_let M1
        simp only [ne_eq, Subgraph.induce_verts, Subgraph.verts_top, Subgraph.ofFunction_verts,
          Set.mem_union, Set.mem_image]
        left
        exact repMemOdd (Set.ncard_image_of_injective _ Subtype.val_injective ▸ h)
      have : insert K.exists_vert.choose.val (Subtype.val '' K.supp \ M1.verts) = Subtype.val '' K.supp := by
        ext v
        simp only [Subgraph.induce_verts, Subgraph.verts_top, Set.mem_insert_iff,
          Set.mem_diff]
        constructor
        · intro h
          cases' h with hl hr
          · rw [hl]
            rw [Subtype.val_injective.mem_set_image]
            exact ConnectedComponent.exists_vert_mem_supp _
          · exact hr.1
        · intro h
          by_cases hc : v = K.exists_vert.choose.val
          · left; exact hc
          · right
            refine ⟨h, ?_⟩
            unfold_let M1
            simp only [Subgraph.ofFunction_verts, Set.mem_union]
            push_neg
            constructor
            · intro h'
              apply hc
              exact (memSuppOddIsRep _ h h').symm
            · intro hv
              rw [Set.mem_image] at hv
              obtain ⟨v', hv'⟩ := hv
              have : v ∈ G.core := by
                rw [← hv'.2]
                exact gMemS hv'.1
              exact memImKNotS _ h this

      rw [← this] at h

      rw [← Set.Finite.odd_card_insert_iff (Set.toFinite _) kMem]
      exact h
  have compMatching (K : G.slices.coe.ConnectedComponent) :
      ∃ M : Subgraph G, M.verts = Subtype.val '' K.supp \ M1.verts ∧ M.IsMatching := by
    have : G.IsClique (Subtype.val '' K.supp \ M1.verts) := by

      sorry
    rw [← isClique_even_iff_matches _ (Set.toFinite _ ) this]
    exact evenKsubM1 K



  sorry
