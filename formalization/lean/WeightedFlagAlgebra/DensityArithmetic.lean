import WeightedFlagAlgebra.DegreeExtension

namespace FGST.Chapter3

local instance : Std.Associative (fun a b : Rat => a * b) := ⟨Rat.mul_assoc⟩
local instance : Std.Commutative (fun a b : Rat => a * b) := ⟨Rat.mul_comm⟩

def normalizeCount (orientedMarked D n count : Nat) : Rat :=
  ((D ^ 2 * count : Nat) : Rat) / ((orientedMarked * D ^ n : Nat) : Rat)

theorem normalizeCount_add (a D n x y : Nat) :
    normalizeCount a D n (x + y) = normalizeCount a D n x + normalizeCount a D n y := by
  simp only [normalizeCount, Nat.mul_add, Rat.natCast_add, Rat.div_def, Rat.add_mul]

theorem normalizeCount_nsum (a D n : Nat) (keys : List A) (count : A → Nat) :
    normalizeCount a D n (nsum keys count) =
      (keys.map (fun x => normalizeCount a D n (count x))).sum := by
  induction keys with
  | nil => simp [normalizeCount, Rat.div_def, Rat.zero_mul]
  | cons x xs ih => simp [normalizeCount_add, ih]

private theorem rat_mul_div_common (a b d : Rat) (hd : d ≠ 0) :
    a * d / (b * d) = a / b := by
  simp only [Rat.div_def, Rat.inv_mul_rev]
  calc
    _ = (a * b⁻¹) * (d * d⁻¹) := by ac_rfl
    _ = _ := by rw [Rat.mul_inv_cancel d hd, Rat.mul_one]

private theorem positive_cast_ne_zero {d : Nat} (hd : 0 < d) : (d : Rat) ≠ 0 :=
  Rat.ne_of_gt (Rat.natCast_pos.mpr hd)

theorem normalizeCount_two (a D h : Nat) (hD : 0 < D) :
    normalizeCount a D 2 h = (h : Rat) / (a : Rat) := by
  simp only [normalizeCount, Rat.natCast_mul]
  rw [Rat.mul_comm, rat_mul_div_common _ _ _ (positive_cast_ne_zero (Nat.pow_pos hD))]

theorem normalizeCount_step (a D k h : Nat) (hD : 0 < D) :
    normalizeCount a D (k + 1) (D * h) = normalizeCount a D k h := by
  simp only [normalizeCount, Nat.pow_succ D k, Rat.natCast_mul]
  have h₁ : (↑(D ^ 2) : Rat) * (↑D * ↑h) = ((↑(D ^ 2) : Rat) * ↑h) * ↑D := by ac_rfl
  rw [h₁, ← Rat.mul_assoc, rat_mul_div_common _ _ _ (positive_cast_ne_zero hD)]

/-- The degree extension equation (3.13), including its normalization. -/
theorem degree_extension_density (G : MarkedGraph V) (D : Nat) (hD : 0 < D)
    (regular : ∀ v, nsum G.host.vertices (G.reducedMultiplicity v) = D)
    (keys : List (Pattern (k + 1))) (hn : keys.Nodup)
    (hc : ∀ f : Fin (k + 1) → V, inducedPattern G f ∈ keys)
    (F : Pattern k) (u : Fin k) (J : List (Fin k × Fin k)) :
    let q := normalizeCount G.orientedMarked D (k + 1)
    q (extensionCount G keys F u .blue (shiftPairs J)) +
      q (extensionCount G keys F u .red (shiftPairs J)) +
      q (extensionCount G keys F u .red ((u.succ, 0) :: shiftPairs J)) =
    weightedDensity G D F J := by
  dsimp
  rw [← normalizeCount_add, ← normalizeCount_add,
    degree_extension_raw G D regular keys hn hc F u J,
    normalizeCount_step _ _ _ _ hD]
  rfl

/-- Formula (3.5) after combining the common denominators. -/
theorem normalized_two_root_objective (G : MarkedGraph V) (D : Nat)
    (hM : 0 < G.orientedMarked) (hD : 0 < D)
    (keys : List (Pattern 4)) (hn : keys.Nodup)
    (hc : ∀ f : Fin 4 → V, inducedPattern G f ∈ keys) :
    normalizeCount G.orientedMarked D 4 (nsum keys fun F => nsum rootChoices (twoRootCount G F)) /
      2 = (G.orientedMarked : Rat) / 2 / ((D ^ 2 : Nat) : Rat) := by
  rw [two_root_count_total G keys hn hc]
  let a : Rat := G.orientedMarked
  let d : Rat := (D ^ 2 : Nat)
  have ha : a ≠ 0 := positive_cast_ne_zero hM
  have hd : d ≠ 0 := positive_cast_ne_zero (Nat.pow_pos hD)
  have hpow : D ^ 4 = D ^ 2 * D ^ 2 := Nat.pow_add D 2 2
  simp only [normalizeCount, hpow, Rat.natCast_mul]
  change d * (a * a) / (a * (d * d)) / 2 = a / 2 / d
  have hcancel : d * (a * a) / (a * (d * d)) = a / d := by
    have h₁ : d * (a * a) = (a * a) * d := by ac_rfl
    rw [h₁, ← Rat.mul_assoc, rat_mul_div_common _ _ _ hd,
      Rat.mul_comm a d, rat_mul_div_common _ _ _ ha]
  rw [hcancel]
  simp only [Rat.div_def]
  ac_rfl

end FGST.Chapter3
