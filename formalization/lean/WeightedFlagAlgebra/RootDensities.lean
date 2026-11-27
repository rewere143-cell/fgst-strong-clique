import WeightedFlagAlgebra.Objective
import WeightedFlagAlgebra.RepeatedRootDensity

namespace FGST.Chapter3

local instance : Std.Associative (fun a b : Rat => a * b) := ⟨Rat.mul_assoc⟩
local instance : Std.Commutative (fun a b : Rat => a * b) := ⟨Rat.mul_comm⟩

theorem representative_root_count (G : MarkedGraph V) :
    weightedCount G redEdgePattern [] = G.orientedBase := by
  classical
  unfold weightedCount MarkedGraph.orientedBase
  simp only [induced_edge_iff, List.map_nil, List.prod_nil, enumMaps, nsum_flatMap, nsum_map,
    nsum_cons, nsum_nil, Nat.add_zero]
  change nsum G.host.vertices (fun u => nsum G.host.vertices (fun v =>
    if G.color u v = .red then 1 else 0)) = _
  apply nsum_congr
  intro u _
  apply nsum_congr
  intro v _
  simp [MarkedGraph.base]

private theorem twice_as_ratio (s m : Nat) :
    ((2 * s : Nat) : Rat) / ((2 * m : Nat) : Rat) = (s : Rat) / (m : Rat) := by
  simp only [Rat.natCast_mul]
  change (2 * (s : Rat)) / (2 * (m : Rat)) = (s : Rat) / (m : Rat)
  simp only [Rat.div_def, Rat.inv_mul_rev]
  calc
    _ = ((s : Rat) * (m : Rat)⁻¹) * ((2 : Rat) * (2 : Rat)⁻¹) := by ac_rfl
    _ = _ := by rw [Rat.mul_inv_cancel 2 (by decide), Rat.mul_one]

/-- The two root densities and their sum, as in (3.6). -/
theorem root_density_pair (G : MarkedGraph V) (D : Nat) (hD : 0 < D)
    (hm : 0 < G.cliqueSize) :
    let s := G.chosenRedPairs.length
    let m := G.cliqueSize
    let b := m - s
    weightedDensity G D redEdgePattern [] = (s : Rat) / (m : Rat) ∧
      weightedDensity G D redEdgePattern [(0, 1)] = (b : Rat) / (m : Rat) ∧
      weightedDensity G D redEdgePattern [] + weightedDensity G D redEdgePattern [(0, 1)] = 1 := by
  dsimp
  have he := G.oriented_marked_partition
  rw [G.orientedBase_eq_twice_chosenRedPairs, G.orientedMarked_eq_twice_cliqueSize] at he
  have he' : G.orientedExtra = 2 * (G.cliqueSize - G.chosenRedPairs.length) := by omega
  have hsum : G.chosenRedPairs.length + (G.cliqueSize - G.chosenRedPairs.length) = G.cliqueSize := by
    omega
  have hb : weightedDensity G D redEdgePattern [] = (G.chosenRedPairs.length : Rat) / (G.cliqueSize : Rat) := by
    change normalizeCount G.orientedMarked D 2 (weightedCount G redEdgePattern []) = _
    rw [normalizeCount_two _ _ _ hD, representative_root_count, G.orientedBase_eq_twice_chosenRedPairs,
      G.orientedMarked_eq_twice_cliqueSize, twice_as_ratio]
  have hx : weightedDensity G D redEdgePattern [(0, 1)] =
      ((G.cliqueSize - G.chosenRedPairs.length : Nat) : Rat) / (G.cliqueSize : Rat) := by
    change normalizeCount G.orientedMarked D 2 (weightedCount G redEdgePattern [(0, 1)]) = _
    rw [normalizeCount_two _ _ _ hD, weighted_root_edge_count, he',
      G.orientedMarked_eq_twice_cliqueSize, twice_as_ratio]
  refine ⟨hb, hx, ?_⟩
  rw [hb, hx]
  simp only [Rat.div_def, ← Rat.add_mul, ← Rat.natCast_add, hsum]
  exact Rat.mul_inv_cancel _ (Rat.ne_of_gt (Rat.natCast_pos.mpr hm))

/-- The normalized parameters of (3.1) satisfy S = M (1 - e). -/
theorem density_parameters (G : MarkedGraph V) (D : Nat) (hD : 0 < D)
    (hm : 0 < G.cliqueSize) :
    let m := G.cliqueSize
    let s := G.chosenRedPairs.length
    let b := m - s
    (s : Rat) / ((D ^ 2 : Nat) : Rat) =
      ((m : Rat) / ((D ^ 2 : Nat) : Rat)) * (1 - (b : Rat) / (m : Rat)) := by
  dsimp
  obtain ⟨hb, he, hsum⟩ := root_density_pair G D hD hm
  rw [hb, he] at hsum
  let m : Rat := G.cliqueSize
  let s : Rat := G.chosenRedPairs.length
  let b : Rat := (G.cliqueSize - G.chosenRedPairs.length : Nat)
  let d : Rat := (D ^ 2 : Nat)
  change s / m + b / m = 1 at hsum
  change s / d = (m / d) * (1 - b / m)
  have hcomp : 1 - b / m = s / m := by
    rw [← hsum, Rat.add_sub_cancel]
  rw [hcomp, Rat.div_def (a := m), Rat.div_def (a := s) (b := m)]
  symm
  calc
    _ = (s / d) * (m * m⁻¹) := by rw [Rat.div_def]; ac_rfl
    _ = _ := by rw [Rat.mul_inv_cancel _ (Rat.ne_of_gt (Rat.natCast_pos.mpr hm)), Rat.mul_one]

end FGST.Chapter3
