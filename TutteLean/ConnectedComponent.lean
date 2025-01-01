import TutteLean.Defs

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}


lemma ConnectedComponentSubsetVerts (H : Subgraph G) (c : ConnectedComponent H.coe) : (c.supp : Set V) ⊆ H.verts := by
  intro v hv
  exact Set.image_val_subset hv


lemma ConnectedComponent.exists_vert (c : ConnectedComponent G) : ∃ v, G.connectedComponentMk v = c := c.exists_rep

lemma ConnectedComponent.exists_vert_mem_supp (c : ConnectedComponent G) : c.exists_vert.choose ∈ c.supp := c.exists_vert.choose_spec
