import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib
import TutteLean.Defs

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

lemma edge_le_iff (h : v ≠ w) : edge v w ≤ G ↔ G.Adj v w := by
  refine ⟨fun h ↦ h (by simp_all [edge_adj, h]), fun hadj v' w' hvw' ↦ ?_⟩
  simp only [edge_adj, ne_eq] at hvw'
  cases hvw'.1 with
  | inl h1 => exact (h1.1 ▸ h1.2 ▸ hadj)
  | inr h2 => exact (h2.1 ▸ h2.2 ▸ hadj.symm)
