import Mathlib.Combinatorics.SimpleGraph.Operations

import TutteLean.Defs

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

lemma singleEdge_le_iff (hneq : v ≠ w) : edge v w ≤ G ↔ G.Adj v w := by
  constructor
  · intro h
    apply h
    simp only [edge_adj, and_self, hneq, false_and, or_false, ne_eq, not_false_eq_true]
  · intro hadj v' w' hvw'
    simp [edge_adj, hneq] at hvw'
    cases hvw'.1 with
    | inl h1 =>
      exact (h1.1 ▸ h1.2 ▸ hadj)
    | inr h2 =>
      exact (h2.1 ▸ h2.2 ▸ hadj.symm)
