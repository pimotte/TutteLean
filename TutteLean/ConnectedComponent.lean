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

-- In #20398
lemma commonComponent [Fintype V] [DecidableEq V] {G G' : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel G'.Adj]
     {c : ConnectedComponent G} {c' d' : ConnectedComponent G'} (hc' : c.supp ⊆ c'.supp) (hd' : c.supp ⊆ d'.supp) : c' = d' := by
    obtain ⟨ v, hv ⟩ := c.exists_rep
    rw [← (SimpleGraph.ConnectedComponent.mem_supp_iff c' v).mp]
    exact hd' hv
    exact hc' hv

-- In #20398
lemma ConnectedComponent.odd_components_mono [Fintype V] [DecidableEq V] (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (h : G ≤ G') : ({c : ConnectedComponent G' | Odd (Nat.card c.supp)}).ncard ≤ ({c : ConnectedComponent G | Odd (Nat.card c.supp)}).ncard := by
  have ex_subcomponent (c : G'.ConnectedComponent) (hc : Odd (Nat.card c.supp)) : ∃ (c' : G.ConnectedComponent), c'.supp ⊆ c.supp ∧ Odd (Nat.card c'.supp) := by
    have := (c.odd_card_supp_iff_odd_subcomponents _ h).mp hc
    have : Set.ncard {c' : G.ConnectedComponent | c'.supp ⊆ c.supp ∧ Odd (Nat.card c'.supp)} ≠ 0 := by
      rw [← Set.Nat.card_coe_set_eq]
      intro h
      rw [h] at this
      contradiction
    exact Set.nonempty_of_ncard_ne_zero this

  let f : {c : ConnectedComponent G' | Odd (Nat.card c.supp)} → {c : ConnectedComponent G | Odd (Nat.card c.supp)} :=
    fun ⟨c, hc⟩ ↦ ⟨(ex_subcomponent c hc).choose, (ex_subcomponent c hc).choose_spec.2⟩
  rw [← Set.Nat.card_coe_set_eq, ← Set.Nat.card_coe_set_eq]
  have finj : Function.Injective f := by
    intro c c' fcc'
    simp only [Subtype.mk.injEq, f] at fcc'
    have hc := (ex_subcomponent c.1 c.2).choose_spec
    have hc' := (ex_subcomponent c'.1 c'.2).choose_spec
    rw [fcc'] at hc
    exact Subtype.val_injective (commonComponent hc.1 hc'.1)
  exact Finite.card_le_of_injective f finj

-- In #20398
lemma oddComponentsIncrease [Fintype V] [DecidableEq V] (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (h : G ≤ G') (u : Set V):
    ({c : ConnectedComponent ((⊤ : Subgraph G').deleteVerts u).coe | Odd (Nat.card c.supp)}).ncard ≤ ({c : ConnectedComponent ((⊤ : Subgraph G).deleteVerts u).coe | Odd (Nat.card c.supp)}).ncard  := by
  -- set_option trace.Meta.synthInstance true in
  apply ConnectedComponent.odd_components_mono
  intro v w hvw
  simp at *
  exact h hvw

lemma ConnectedComponentSubsetVerts (H : Subgraph G) (c : ConnectedComponent H.coe) : (c.supp : Set V) ⊆ H.verts := by
  intro v hv
  exact Set.image_val_subset hv


lemma ConnectedComponent.exists_vert (c : ConnectedComponent G) : ∃ v, G.connectedComponentMk v = c := c.exists_rep

lemma ConnectedComponent.exists_vert_mem_supp (c : ConnectedComponent G) : c.exists_vert.choose ∈ c.supp := c.exists_vert.choose_spec
