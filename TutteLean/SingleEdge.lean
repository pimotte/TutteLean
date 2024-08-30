import TutteLean.Defs

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}




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
