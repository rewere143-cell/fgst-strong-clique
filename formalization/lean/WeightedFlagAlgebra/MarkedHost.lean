import WeightedFlagAlgebra.FiniteCounting
import WeightedFlagAlgebra.FiniteHost

namespace FGST.Chapter3

inductive EdgeColor where
  | absent
  | blue
  | red
  deriving DecidableEq

structure MarkedGraph (V : Type u) where
  host : FiniteMultigraph V
  marked : V → V → Nat
  marked_le : ∀ u v, marked u v ≤ host.multiplicity u v
  marked_symm : ∀ u v, marked u v = marked v u

namespace MarkedGraph

variable (G : MarkedGraph V)

abbrev Adj (u v : V) : Prop := 0 < G.host.multiplicity u v

def Strong : Prop :=
  ∀ a b c d, 0 < G.marked a b → 0 < G.marked c d →
    a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    G.Adj a c ∨ G.Adj a d ∨ G.Adj b c ∨ G.Adj b d

def color (u v : V) : EdgeColor :=
  if 0 < G.marked u v then .red else if G.Adj u v then .blue else .absent

def base (u v : V) : Nat := if 0 < G.marked u v then 1 else 0

def extra (u v : V) : Nat := G.marked u v - 1

def blue (u v : V) : Nat := if G.color u v = .blue then 1 else 0

def reducedMultiplicity (u v : V) : Nat := G.marked u v + G.blue u v

theorem marked_loopless (v : V) : G.marked v v = 0 :=
  Nat.le_zero.mp (G.host.loopless v ▸ G.marked_le v v)

theorem color_symm (u v : V) : G.color u v = G.color v u := by
  simp only [color, Adj, G.marked_symm u v, G.host.symmetric u v]

@[simp] theorem color_refl (v : V) : G.color v v = .absent := by
  simp [color, Adj, G.host.loopless, G.marked_loopless]

@[simp] theorem color_eq_red (u v : V) : G.color u v = .red ↔ 0 < G.marked u v := by
  by_cases hm : 0 < G.marked u v
  · simp [color, hm]
  · by_cases ha : G.Adj u v <;> simp [color, hm, ha]

@[simp] theorem color_ne_absent (u v : V) : G.color u v ≠ .absent ↔ G.Adj u v := by
  unfold color
  split
  · rename_i h
    exact iff_of_true (by decide) (Nat.lt_of_lt_of_le h (G.marked_le u v))
  · split <;> simp_all

theorem base_add_extra (u v : V) : G.base u v + G.extra u v = G.marked u v := by
  unfold base extra
  split <;> omega

theorem reducedMultiplicity_symm (u v : V) :
    G.reducedMultiplicity u v = G.reducedMultiplicity v u := by
  simp only [reducedMultiplicity, blue, G.marked_symm u v, G.color_symm u v]

theorem reducedMultiplicity_le (u v : V) : G.reducedMultiplicity u v ≤ G.host.multiplicity u v := by
  unfold reducedMultiplicity blue
  split
  · rename_i h
    have h₁ := (G.color_ne_absent u v).mp (by rw [h]; decide)
    have h₂ : ¬ 0 < G.marked u v := by
      intro hc
      have := (G.color_eq_red u v).mpr hc
      rw [h] at this
      contradiction
    unfold Adj at h₁
    omega
  · simpa using G.marked_le u v

theorem reducedMultiplicity_pos (u v : V) : 0 < G.reducedMultiplicity u v ↔ G.Adj u v := by
  constructor
  · intro h
    exact Nat.lt_of_lt_of_le h (G.reducedMultiplicity_le u v)
  · intro h
    by_cases hp : 0 < G.marked u v
    · exact Nat.lt_of_lt_of_le hp (Nat.le_add_right ..)
    · simp [reducedMultiplicity, blue, color, hp, h]

/-- Keep every marked instance and a single edge on each blue pair. -/
def reduceParallel : MarkedGraph V where
  host := { G.host with
    multiplicity := G.reducedMultiplicity
    symmetric := G.reducedMultiplicity_symm
    loopless := fun v => by simp [reducedMultiplicity, blue, G.marked_loopless] }
  marked := G.marked
  marked_le u v := Nat.le_add_right ..
  marked_symm := G.marked_symm

@[simp] theorem reduceParallel_adj (u v : V) : G.reduceParallel.Adj u v ↔ G.Adj u v :=
  G.reducedMultiplicity_pos u v

theorem reduceParallel_strong : G.reduceParallel.Strong ↔ G.Strong := by
  simp only [Strong, reduceParallel_adj]
  rfl

theorem reduceParallel_degree_le (v : V) : G.reduceParallel.host.degree v ≤ G.host.degree v :=
  nsum_le _ _ _ (fun u _ => G.reducedMultiplicity_le v u)

def redDegree (v : V) : Nat := nsum G.host.vertices (G.marked v)

def orientedMarked : Nat := nsum G.host.vertices G.redDegree

def orientedBase : Nat := nsum G.host.vertices (fun v => nsum G.host.vertices (G.base v))

def orientedExtra : Nat := nsum G.host.vertices (fun v => nsum G.host.vertices (G.extra v))

theorem oriented_marked_partition : G.orientedBase + G.orientedExtra = G.orientedMarked := by
  unfold orientedBase orientedExtra orientedMarked redDegree
  rw [← nsum_add]
  apply nsum_congr
  intro v _
  rw [← nsum_add]
  exact nsum_congr _ _ _ (fun u _ => G.base_add_extra v u)

/-- Formula (3.2), including coinciding images of distinct positions. -/
theorem marked_pair_cross (hs : G.Strong) (a b c d : V)
    (hab : 0 < G.marked a b) (hcd : 0 < G.marked c d) :
    G.Adj a c ∨ G.Adj a d ∨ G.Adj b c ∨ G.Adj b d := by
  classical
  have hforward : G.Adj c d := Nat.lt_of_lt_of_le hcd (G.marked_le c d)
  have hback : G.Adj d c := by simpa [Adj, ← G.host.symmetric c d] using hforward
  by_cases hac : a = c
  · exact .inr (.inl (hac.symm ▸ hforward))
  by_cases had : a = d
  · exact .inl (had.symm ▸ hback)
  by_cases hbc : b = c
  · exact .inr (.inr (.inr (hbc.symm ▸ hforward)))
  by_cases hbd : b = d
  · exact .inr (.inr (.inl (hbd.symm ▸ hback)))
  exact hs a b c d hab hcd hac had hbc hbd

end MarkedGraph

end FGST.Chapter3
