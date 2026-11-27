import WeightedFlagAlgebra.RootCounts
import WeightedFlagAlgebra.DensityArithmetic

namespace FGST.Chapter3

local instance : Std.Associative (fun a b : Rat => a * b) := ⟨Rat.mul_assoc⟩
local instance : Std.Commutative (fun a b : Rat => a * b) := ⟨Rat.mul_comm⟩

/-- The red edge with both endpoint orders present in the color matrix. -/
def redEdgePattern : Pattern 2 := fun i j => if i = j then .absent else .red

/-- The red path 0-1-2 in (3.15), with ends having color zero. -/
def redPathPattern : Pattern 3 := fun i j =>
  if i ≠ j ∧ (i = 1 ∨ j = 1) then .red else .absent

private theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have h := i.isLt
  have h' : i.val = 0 ∨ i.val = 1 := by omega
  rcases h' with h' | h'
  · exact .inl (Fin.eq_of_val_eq h')
  · exact .inr (Fin.eq_of_val_eq h')

private theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  have h := i.isLt
  have h' : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases h' with h' | h' | h'
  · exact .inl (Fin.eq_of_val_eq h')
  · exact .inr (.inl (Fin.eq_of_val_eq h'))
  · exact .inr (.inr (Fin.eq_of_val_eq h'))

theorem induced_edge_iff (G : MarkedGraph V) (f : Fin 2 → V) :
    redEdgePattern = inducedPattern G f ↔ G.color (f 0) (f 1) = .red := by
  constructor
  · intro h
    exact (congrFun (congrFun h 0) 1).symm
  · intro h
    have hs : G.color (f 1) (f 0) = .red := (G.color_symm _ _).trans h
    funext i j
    rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl <;>
      simp only [redEdgePattern, inducedPattern, G.color_refl, h, hs] <;> decide

private theorem induced_path_iff (G : MarkedGraph V) (f : Fin 3 → V) :
    redPathPattern = inducedPattern G f ↔
      G.color (f 0) (f 1) = .red ∧ G.color (f 1) (f 2) = .red ∧
        G.color (f 0) (f 2) = .absent := by
  constructor
  · intro h
    exact ⟨(congrFun (congrFun h 0) 1).symm, (congrFun (congrFun h 1) 2).symm,
      (congrFun (congrFun h 0) 2).symm⟩
  · rintro ⟨h₁, h₂, h₃⟩
    have h₄ : G.color (f 1) (f 0) = .red := (G.color_symm _ _).trans h₁
    have h₅ : G.color (f 2) (f 1) = .red := (G.color_symm _ _).trans h₂
    have h₆ : G.color (f 2) (f 0) = .absent := (G.color_symm _ _).trans h₃
    funext i j
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl <;>
      simp only [redPathPattern, inducedPattern, G.color_refl, h₁, h₂, h₃, h₄, h₅, h₆] <;> decide

private theorem extra_zero_of_not_red (G : MarkedGraph V) (u v : V)
    (hn : G.color u v ≠ .red) : G.extra u v = 0 := by
  have hz : ¬ 0 < G.marked u v := fun h => hn ((G.color_eq_red u v).mpr h)
  unfold MarkedGraph.extra
  omega

theorem weighted_root_edge_count (G : MarkedGraph V) :
    weightedCount G redEdgePattern [(0, 1)] = G.orientedExtra := by
  unfold weightedCount MarkedGraph.orientedExtra
  simp only [induced_edge_iff, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Nat.mul_one, enumMaps, nsum_flatMap, nsum_map, nsum_cons, nsum_nil, Nat.add_zero]
  change nsum G.host.vertices (fun u => nsum G.host.vertices (fun v =>
    if G.color u v = .red then G.extra u v else 0)) = _
  apply nsum_congr
  intro u _
  apply nsum_congr
  intro v _
  by_cases h : G.color u v = .red
  · exact if_pos h
  · rw [if_neg h, extra_zero_of_not_red G u v h]

theorem weighted_root_path_count [DecidableEq V] (G : MarkedGraph V) (hs : G.Strong)
    (hd : ∀ x, G.host.degree x ≤ 4) (hm : 36 ≤ G.orientedMarked) :
    weightedCount G redPathPattern [(0, 1)] = 3 * weightedCount G redEdgePattern [(0, 1)] := by
  rw [weighted_root_edge_count]
  unfold weightedCount MarkedGraph.orientedExtra
  simp only [induced_path_iff, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Nat.mul_one, enumMaps, nsum_flatMap, nsum_map, nsum_cons, nsum_nil, Nat.add_zero]
  change nsum G.host.vertices (fun u => nsum G.host.vertices (fun v =>
    nsum G.host.vertices (fun x =>
      if G.color u v = .red ∧ G.color v x = .red ∧ G.color u x = .absent
      then G.extra u v else 0))) = _
  simp only [← nsum_mul]
  apply nsum_congr
  intro u _
  apply nsum_congr
  intro v _
  by_cases hx : 0 < G.extra u v
  · have hr : G.color u v = .red := by
      rw [G.color_eq_red]
      unfold MarkedGraph.extra at hx
      omega
    simp only [hr, true_and]
    calc
      _ = G.extra u v * nsum G.host.vertices
          (fun x => if G.color v x = .red ∧ G.color u x = .absent then 1 else 0) := by
        rw [← nsum_mul]
        apply nsum_congr
        intro x _
        split <;> simp
      _ = _ := by rw [G.degreeFour_third_images hs hd hm u v hx, Nat.mul_comm]
  · have hz : G.extra u v = 0 := by omega
    simp [hz, nsum_const]

/-- Theorem 3.8, with the exact normalized densities in (3.15). -/
theorem degreeFour_path_density [DecidableEq V] (G : MarkedGraph V) (hs : G.Strong)
    (hd : ∀ x, G.host.degree x ≤ 4) (hm : 36 ≤ G.orientedMarked) :
    4 * weightedDensity G 4 redPathPattern [(0, 1)] =
      3 * weightedDensity G 4 redEdgePattern [(0, 1)] := by
  change 4 * normalizeCount G.orientedMarked 4 3 (weightedCount G redPathPattern [(0, 1)]) =
    3 * normalizeCount G.orientedMarked 4 2 (weightedCount G redEdgePattern [(0, 1)])
  rw [weighted_root_path_count G hs hd hm]
  let h := weightedCount G redEdgePattern [(0, 1)]
  change 4 * normalizeCount G.orientedMarked 4 3 (3 * h) =
    3 * normalizeCount G.orientedMarked 4 2 h
  have hmul (n c : Nat) : normalizeCount n 4 3 (c * h) =
      (c : Rat) * normalizeCount n 4 3 h := by
    unfold normalizeCount
    simp only [Rat.natCast_mul, Rat.div_def]
    ac_rfl
  calc
    _ = 3 * normalizeCount G.orientedMarked 4 3 (4 * h) := by
      rw [hmul _ 3, hmul _ 4]
      change (4 : Rat) * (3 * _) = (3 : Rat) * (4 * _)
      ac_rfl
    _ = _ := by rw [normalizeCount_step G.orientedMarked 4 2 h (by decide)]

end FGST.Chapter3
