import WeightedFlagAlgebra.CliqueTruncation
import WeightedFlagAlgebra.DegreeFourSimple
import WeightedFlagAlgebra.RootCounts

namespace FGST.Chapter3.MarkedGraph

variable (G : MarkedGraph V)

/-- Forget edge multiplicities while keeping a unique representative of
    every marked pair and every support adjacency. -/
def simpleSupport (hs : G.Strong) : DegreeFour.Graph V where
  vertices := G.host.vertices
  verticesNodup := G.host.nodup
  adjacent u v := decide (G.Adj u v)
  symmetric u v := by
    change decide (0 < G.host.multiplicity u v) = decide (0 < G.host.multiplicity v u)
    rw [G.host.symmetric u v]
  loopless v := by
    change decide (0 < G.host.multiplicity v v) = false
    rw [G.host.loopless v]
    decide
  redEdges := G.chosenRedPairs
  redNodup := G.chosenRedPairs_nodup
  redOrientation h := G.chosenRedPairs_noReverse h
  redAdjacent e he := decide_eq_true
    (Nat.lt_of_lt_of_le ((G.mem_chosenRedPairs_iff e.1 e.2).mp he).2
      (G.marked_le e.1 e.2))
  redVertices _e h := G.chosenRedPairs_vertices h
  strong e he f hf := by
    have hr := (G.mem_chosenRedPairs_iff e.1 e.2).mp he
    have hs' := (G.mem_chosenRedPairs_iff f.1 f.2).mp hf
    simpa only [decide_eq_true_eq] using
      G.marked_pair_cross hs e.1 e.2 f.1 f.2 hr.2 hs'.2

theorem simpleSupport_degree_le (hs : G.Strong) (x : V) :
    (G.simpleSupport hs).degree x ≤ G.host.degree x := by
  let p (y : V) := decide (G.Adj x y)
  have hcount := nsum_filter G.host.vertices p (fun _ => 1)
  have hsize : (G.simpleSupport hs).degree x =
      nsum G.host.vertices (fun y => if p y then 1 else 0) := by
    change (G.host.vertices.filter p).length = _
    simpa only [nsum_const, Nat.mul_one] using hcount
  rw [hsize]
  apply nsum_le
  intro y _
  by_cases hy : G.Adj x y
  · rw [if_pos (decide_eq_true hy)]
    exact hy
  · simp [p, hy]

private theorem orientedMarked_eq_base_of_no_repeats (h : ∀ x y, G.marked x y ≤ 1) :
    G.orientedMarked = G.orientedBase := by
  unfold orientedMarked orientedBase
  apply nsum_congr
  intro x _
  unfold redDegree
  apply nsum_congr
  intro y _
  by_cases hxy : 0 < G.marked x y
  · have hmarked := h x y
    simp [base, show G.marked x y = 1 by omega]
  · simp [base, show G.marked x y = 0 by omega]

/-- Degree four has at most 40 ordered marked instances and hence at most
    20 marked edge instances. This strengthens the interval exclusion in
    Theorem 3.9. -/
theorem degreeFour_oriented_bound (hs : G.Strong) (hd : ∀ x, G.host.degree x ≤ 4) :
    G.orientedMarked ≤ 40 := by
  classical
  by_cases h : ∃ x y, 2 ≤ G.marked x y
  · obtain ⟨x, y, hxy⟩ := h
    have hr := G.degreeFour_parallel_bound hs hd x y (by omega)
    omega
  have hsingle : ∀ x y, G.marked x y ≤ 1 := by
    intro x y
    apply Classical.byContradiction
    intro hxy
    exact h ⟨x, y, by omega⟩
  have hg := (G.simpleSupport hs).degree_four_simple_bound
    (fun x => Nat.le_trans (G.simpleSupport_degree_le hs x) (hd x))
  change G.chosenRedPairs.length ≤ 20 at hg
  rw [G.orientedMarked_eq_base_of_no_repeats hsingle, G.orientedBase_eq_twice_chosenRedPairs]
  omega

theorem degreeFour_clique_bound (hs : G.Strong) (hd : ∀ x, G.host.degree x ≤ 4) :
    G.cliqueSize ≤ 20 := by
  have h := G.degreeFour_oriented_bound hs hd
  rw [G.orientedMarked_eq_twice_cliqueSize] at h
  omega

/-- Theorem 3.9: at degree bound four the normalized size M lies outside
    the closed rational interval [21/16, 11/8]. -/
theorem theorem3_9 (hs : G.Strong) (hd : ∀ x, G.host.degree x ≤ 4) :
    ¬ ((21 : Rat) / 16 ≤ (G.cliqueSize : Rat) / 16 ∧
      (G.cliqueSize : Rat) / 16 ≤ (11 : Rat) / 8) := by
  have h := G.degreeFour_clique_bound hs hd
  have hl : G.cliqueSize < 21 := by omega
  have hcast : (G.cliqueSize : Rat) < ((21 : Nat) : Rat) :=
    Rat.natCast_lt_natCast.mpr hl
  have hmass : (G.cliqueSize : Rat) / 16 < (21 : Rat) / 16 :=
    (Rat.div_lt_iff (by decide : (0 : Rat) < 16)).mpr
      (by rw [Rat.div_mul_cancel (by decide : (16 : Rat) ≠ 0)]; exact hcast)
  exact fun hm => Rat.not_le.mpr hmass hm.1

#print axioms degreeFour_oriented_bound
#print axioms theorem3_9

end FGST.Chapter3.MarkedGraph
