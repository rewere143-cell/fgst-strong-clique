import Std

namespace FGST.Chapter3

/-- Vertices are enumerated exactly once; multiplicity counts edge instances. -/
structure FiniteMultigraph (V : Type u) where
  vertices : List V
  complete : ∀ v, v ∈ vertices
  nodup : vertices.Nodup
  multiplicity : V → V → Nat
  symmetric : ∀ u v, multiplicity u v = multiplicity v u
  loopless : ∀ v, multiplicity v v = 0

def FiniteMultigraph.degree (G : FiniteMultigraph V) (v : V) : Nat :=
  (G.vertices.map (G.multiplicity v)).sum

end FGST.Chapter3
