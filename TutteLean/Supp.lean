import TutteLean.Defs

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

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
