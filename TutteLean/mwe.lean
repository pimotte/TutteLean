import Mathlib.Combinatorics.SimpleGraph.Path

def oddVerts (G : SimpleGraph V) := {(c : SimpleGraph.ConnectedComponent G) | Nonempty c}
