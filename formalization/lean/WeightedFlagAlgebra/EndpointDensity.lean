import WeightedFlagAlgebra.DensityArithmetic
import WeightedFlagAlgebra.EndpointCounting

namespace FGST.Chapter3

def endpointRoots : List (Fin 4 × Fin 4) := [(0, 1), (2, 3)]
def starRoots : List (Fin 3 × Fin 3) := [(0, 1), (0, 2)]

/-- The pattern H_c in Theorem 3.6. -/
def endpointStar (c : EdgeColor) : Pattern 3 := fun i j =>
  if i = j then .absent else if i = 0 ∨ j = 0 then .red else c

def edgeColors : List EdgeColor := [.absent, .blue, .red]

private theorem color_mem (c : EdgeColor) : c ∈ edgeColors := by
  cases c <;> decide

private theorem enumerate4 (vertices : List V) (g : (Fin 4 → V) → Nat) :
    nsum (enumMaps vertices 4) g = nsum vertices (fun a => nsum vertices (fun b =>
      nsum vertices (fun c => nsum vertices (fun d =>
        g (prependMap a (prependMap b (prependMap c (prependMap d Fin.elim0)))))))) := by
  simp only [enumMaps, nsum_flatMap, nsum_map, nsum_cons, nsum_nil, Nat.add_zero]

noncomputable def endpointPatternTotal (G : MarkedGraph V) (keys : List (Pattern 4)) : Nat :=
  nsum keys (fun F => weightedCount G F endpointRoots)

noncomputable def endpointPatternAdjacent (G : MarkedGraph V) (keys : List (Pattern 4)) : Nat :=
  nsum keys (fun F => if F 1 2 ≠ .absent then weightedCount G F endpointRoots else 0)

noncomputable def sharedPatternIncidences (G : MarkedGraph V) : Nat :=
  nsum edgeColors (fun c => weightedCount G (endpointStar c) starRoots)

private theorem rooted_weight4 (G : MarkedGraph V) (f : Fin 4 → V) :
    specifiedWeight G endpointRoots f = G.extra (f 0) (f 1) * G.extra (f 2) (f 3) := by
  simp [specifiedWeight, endpointRoots]

private theorem rooted_weight3 (G : MarkedGraph V) (f : Fin 3 → V) :
    specifiedWeight G starRoots f = G.extra (f 0) (f 1) * G.extra (f 0) (f 2) := by
  simp [specifiedWeight, starRoots]

theorem endpoint_pattern_total (G : MarkedGraph V) (keys : List (Pattern 4))
    (hn : keys.Nodup) (hc : ∀ f : Fin 4 → V, inducedPattern G f ∈ keys) :
    endpointPatternTotal G keys = G.orientedExtra * G.orientedExtra := by
  have hg := group_weightedCount G keys hn hc (fun _ => True) endpointRoots
  simp only [if_true] at hg
  unfold endpointPatternTotal
  rw [hg, enumerate4]
  simp only [rooted_weight4]
  change nsum G.host.vertices (fun a => nsum G.host.vertices (fun b =>
    nsum G.host.vertices (fun c => nsum G.host.vertices (fun d =>
      G.extra a b * G.extra c d)))) = _
  simp only [nsum_mul]
  change nsum G.host.vertices (fun a => nsum G.host.vertices (fun b =>
    G.extra a b * G.orientedExtra)) = _
  simp only [Nat.mul_comm _ G.orientedExtra, nsum_mul]
  rfl

theorem endpoint_pattern_adjacent (G : MarkedGraph V) (keys : List (Pattern 4))
    (hn : keys.Nodup) (hc : ∀ f : Fin 4 → V, inducedPattern G f ∈ keys) :
    endpointPatternAdjacent G keys = G.adjacentOrderCount := by
  unfold endpointPatternAdjacent
  let keep : Pattern 4 → Prop := fun F => F 1 2 ≠ .absent
  let hp : DecidablePred keep := fun F => inferInstanceAs (Decidable (F 1 2 ≠ .absent))
  change nsum keys (fun F => if keep F then _ else _) = _
  rw [@group_weightedCount _ _ G keys hn hc keep hp endpointRoots, enumerate4]
  simp only [rooted_weight4]
  unfold MarkedGraph.adjacentOrderCount MarkedGraph.extraPairSum MarkedGraph.extraEdgeSum
  apply nsum_congr
  intro a _
  apply nsum_congr
  intro b _
  rw [← nsum_mul]
  apply nsum_congr
  intro c _
  rw [← nsum_mul]
  apply nsum_congr
  intro d _
  change (if G.color b c ≠ .absent then G.extra a b * G.extra c d else 0) =
    G.extra a b * (G.extra c d * (if G.Adj b c then 1 else 0))
  by_cases hab : G.Adj b c
  · have hp := (G.color_ne_absent b c).mpr hab
    simp [hab, hp]
  · have hp : ¬ G.color b c ≠ .absent := fun h => hab ((G.color_ne_absent b c).mp h)
    simp [hab, hp]

private theorem star_of_red (G : MarkedGraph V) (f : Fin 3 → V)
    (h₁ : G.color (f 0) (f 1) = .red) (h₂ : G.color (f 0) (f 2) = .red) :
    endpointStar (G.color (f 1) (f 2)) = inducedPattern G f := by
  have hs₁ : G.color (f 1) (f 0) = .red := (G.color_symm _ _).trans h₁
  have hs₂ : G.color (f 2) (f 0) = .red := (G.color_symm _ _).trans h₂
  funext i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
    simp [endpointStar, inducedPattern, h₁, h₂, hs₁, hs₂, G.color_symm (f 2) (f 1)]

private theorem star_weight_positive (G : MarkedGraph V) (f : Fin 3 → V)
    (h : 0 < specifiedWeight G starRoots f) :
    endpointStar (G.color (f 1) (f 2)) = inducedPattern G f := by
  rw [rooted_weight3] at h
  have h₁ := Nat.pos_of_mul_pos_right h
  have h₂ := Nat.pos_of_mul_pos_left h
  apply star_of_red
  · apply (G.color_eq_red _ _).mpr
    unfold MarkedGraph.extra at h₁
    omega
  · apply (G.color_eq_red _ _).mpr
    unfold MarkedGraph.extra at h₂
    omega

private theorem endpointStar_key (c : EdgeColor) : endpointStar c 1 2 = c := by
  simp [endpointStar]

theorem shared_pattern_incidences (G : MarkedGraph V) :
    sharedPatternIncidences G = G.sharedIncidenceCount := by
  classical
  unfold sharedPatternIncidences weightedCount
  rw [nsum_swap]
  have wave (f : Fin 3 → V) :
      nsum edgeColors (fun c =>
        if endpointStar c = inducedPattern G f then specifiedWeight G starRoots f else 0) =
        specifiedWeight G starRoots f := by
    by_cases h : 0 < specifiedWeight G starRoots f
    · have he := star_weight_positive G f h
      rw [nsum_congr edgeColors _ (fun c =>
        if c = G.color (f 1) (f 2) then specifiedWeight G starRoots f else 0)]
      · exact nsum_single _ (by decide) _ (color_mem _) _
      · intro c _
        have hf : endpointStar c = inducedPattern G f ↔ c = G.color (f 1) (f 2) := by
          constructor
          · intro hEq
            have hh := congrFun (congrFun hEq 1) 2
            rwa [endpointStar_key] at hh
          · intro hEq
            rwa [hEq]
        simp only [hf]
    · have hz : specifiedWeight G starRoots f = 0 := by omega
      simp [hz, nsum_const]
  change nsum (enumMaps G.host.vertices 3) (fun f => nsum edgeColors (fun c =>
    if endpointStar c = inducedPattern G f then specifiedWeight G starRoots f else 0)) = _
  rw [nsum_congr _ _ _ (fun f _ => wave f)]
  simp only [rooted_weight3, enumMaps, nsum_flatMap, nsum_map, nsum_cons, nsum_nil, Nat.add_zero]
  change nsum G.host.vertices (fun a => nsum G.host.vertices (fun b =>
    nsum G.host.vertices (fun c => G.extra a b * G.extra a c))) = _
  simp only [nsum_mul]
  change nsum G.host.vertices (fun a => nsum G.host.vertices (fun b =>
    G.extra a b * G.extraDegree a)) = nsum G.host.vertices _
  simp only [Nat.mul_comm _ (G.extraDegree _), nsum_mul]
  exact nsum_congr _ _ _ (fun _ _ => rfl)

local instance : Std.Associative (fun a b : Rat => a * b) := ⟨Rat.mul_assoc⟩
local instance : Std.Commutative (fun a b : Rat => a * b) := ⟨Rat.mul_comm⟩

private theorem normalize_mul (a D n k x : Nat) :
    normalizeCount a D n (k * x) = (k : Rat) * normalizeCount a D n x := by
  simp only [normalizeCount, Rat.natCast_mul, Rat.div_def]
  ac_rfl

private theorem normalize_mono (a D n : Nat) (ha : 0 < a) (hD : 0 < D) {x y : Nat}
    (hxy : x ≤ y) : normalizeCount a D n x ≤ normalizeCount a D n y := by
  simp only [normalizeCount, Rat.div_def]
  apply Rat.mul_le_mul_of_nonneg_right
  · exact Rat.natCast_le_natCast.mpr (Nat.mul_le_mul_left _ hxy)
  · exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.natCast_pos.mpr
      (Nat.mul_pos ha (Nat.pow_pos hD))))

private theorem normalized_star_scale (a D x : Nat) (hD : 0 < D) :
    (2 / (D : Rat)) * normalizeCount a D 3 x = normalizeCount a D 4 (2 * x) := by
  rw [← normalizeCount_step a D 3 x hD, normalize_mul, normalize_mul]
  simp only [Rat.natCast_ofNat]
  let q := normalizeCount a D 4 x
  change (2 / (D : Rat)) * ((D : Rat) * q) = 2 * q
  rw [Rat.div_def]
  calc
    _ = (2 * q) * ((D : Rat) * (D : Rat)⁻¹) := by ac_rfl
    _ = _ := by
      rw [Rat.mul_inv_cancel _ (Rat.ne_of_gt (Rat.natCast_pos.mpr hD)), Rat.mul_one]

/-- Equation (3.14): the sums use common denominators within each arity. -/
theorem endpoint_density_inequality (G : MarkedGraph V) (hs : G.Strong)
    (D : Nat) (hD : 0 < D) (hm : 0 < G.orientedMarked) (keys : List (Pattern 4))
    (hn : keys.Nodup) (hc : ∀ f : Fin 4 → V, inducedPattern G f ∈ keys) :
    normalizeCount G.orientedMarked D 4 (endpointPatternTotal G keys) +
      2 / (D : Rat) * normalizeCount G.orientedMarked D 3 (sharedPatternIncidences G) ≤
      4 * normalizeCount G.orientedMarked D 4 (endpointPatternAdjacent G keys) := by
  have hr : normalizeCount G.orientedMarked D 4 (4 * endpointPatternAdjacent G keys) =
      4 * normalizeCount G.orientedMarked D 4 (endpointPatternAdjacent G keys) :=
    by simpa only [Rat.natCast_ofNat] using
      normalize_mul G.orientedMarked D 4 4 (endpointPatternAdjacent G keys)
  rw [normalized_star_scale _ D _ hD, ← normalizeCount_add, ← hr]
  apply normalize_mono _ D 4 hm hD
  rw [endpoint_pattern_total G keys hn hc, shared_pattern_incidences,
    endpoint_pattern_adjacent G keys hn hc]
  exact G.endpoint_order_inequality hs

#print axioms endpoint_density_inequality
end FGST.Chapter3
