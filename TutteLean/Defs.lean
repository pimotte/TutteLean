import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

def TutteBlocker (G: SimpleGraph V) (u : Set V) : Prop :=
  u.ncard < {c : ((⊤ : G.Subgraph).deleteVerts u).coe.ConnectedComponent | Odd (c.supp.ncard)}.ncard

instance [Fintype V] [DecidableEq V] [DecidableRel G.Adj] : DecidableEq (ConnectedComponent G) := by
  intro c c'
  exact c.recOn
    (fun v =>
      c'.recOn (fun w => by
        rw [@ConnectedComponent.eq]
        infer_instance)
        (fun _ _ _ _ => Subsingleton.elim _ _))
    (fun _ _ _ _ => Subsingleton.elim _ _)
