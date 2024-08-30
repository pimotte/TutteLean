import TutteLean.Defs

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}


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
