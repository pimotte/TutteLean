import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

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

instance [Fintype V] [DecidableEq V] [DecidableRel G.Adj] : DecidableEq (ConnectedComponent G) := by
  intro c c'
  exact c.recOn
    (fun v =>
      c'.recOn (fun w => by
        rw [@ConnectedComponent.eq]
        infer_instance)
        (fun _ _ _ _ => Subsingleton.elim _ _))
    (fun _ _ _ _ => Subsingleton.elim _ _)


-- noncomputable instance myInst5 [Fintype V] [DecidableEq V] (u : Set V) : Fintype u := by
--   exact Fintype.ofFinite ↑u

noncomputable instance myInst4 [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (u : Set V) :
    Fintype ((⊤ : G.Subgraph).deleteVerts u).verts := by
      haveI : Fintype u := by
        exact Fintype.ofFinite u
      simp only [Subgraph.induce_verts, Subgraph.verts_top]
      infer_instance

def isMatchingFree (G : SimpleGraph V) := ∀ (M : Subgraph G), ¬Subgraph.IsPerfectMatching M

def singleEdge {v w : V} (h : v ≠ w) : SimpleGraph V where
  Adj v' w' := (v = v' ∧ w = w') ∨ (v = w' ∧ w = v')

def Subgraph.IsCycle (M : Subgraph G) := (∀ v ∈ M.support, (M.neighborSet v).ncard = 2) ∧ M.Connected

def Subgraph.IsAlternating (B : Subgraph G) (M : Subgraph G) :=
  ∀ (v w w': V), w ≠ w' → B.Adj v w → B.Adj v w' → (M.Adj v w ↔ ¬ M.Adj v w')
