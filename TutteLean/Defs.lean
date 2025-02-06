import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace SimpleGraph
-- universe u
variable {V : Type*} {G : SimpleGraph V}


lemma deleteVerts_verts_notmem_deleted (a : ((⊤ : G.Subgraph).deleteVerts u).verts) : a.val ∉ u := a.prop.2

-- In #20398
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


-- Was needed for #20398 but inlined, can be removed when oddComponentsIncrease is removed
noncomputable instance myInst4 [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (u : Set V) :
    Fintype ((⊤ : G.Subgraph).deleteVerts u).verts := by
      haveI : Fintype u := by
        exact Fintype.ofFinite u
      simp only [Subgraph.induce_verts, Subgraph.verts_top]
      infer_instance
