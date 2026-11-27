import WeightedFlagAlgebra.Objective

namespace FGST.Chapter3

noncomputable def extensionPatterns (F : Pattern k) (u : Fin k) (c : EdgeColor) :
    List (Pattern (k + 1)) := by
  classical
  exact (patternKeys (k + 1)).filter fun H =>
    decide (KeepExtension F u c H ∧ PatternRedStrong H)

noncomputable def extensionDensitySum (G : MarkedGraph V) (D : Nat)
    (F : Pattern k) (u : Fin k) (c : EdgeColor) (J : List (Fin (k + 1) × Fin (k + 1))) :
    Rat := ((extensionPatterns F u c).map (fun H => weightedDensity G D H J)).sum

private theorem extension_density_eq_sum (G : MarkedGraph V) (hs : G.Strong) (D : Nat)
    (F : Pattern k) (u : Fin k) (c : EdgeColor) (J : List (Fin (k + 1) × Fin (k + 1))) :
    normalizeCount G.orientedMarked D (k + 1) (extensionCount G (patternKeys (k + 1)) F u c J) =
      extensionDensitySum G D F u c J := by
  classical
  unfold extensionDensitySum
  have hf : extensionCount G (patternKeys (k + 1)) F u c J =
      nsum (extensionPatterns F u c) (fun H => weightedCount G H J) := by
    unfold extensionCount extensionPatterns
    rw [nsum_filter]
    simp only [decide_eq_true_eq]
    apply nsum_congr
    intro H _
    by_cases hk : KeepExtension F u c H
    · by_cases hS : PatternRedStrong H
      · simp only [hk, hS, and_self, if_true]
      · have hz (f : Fin (k + 1) → V) : H ≠ inducedPattern G f := fun heq =>
          hS (heq ▸ induced_pattern_redStrong G hs f)
        rw [weightedCount_zero_of_unrealizable G H J hz]
        split <;> split <;> rfl
    · simp only [hk, false_and, if_false]
  rw [hf, normalizeCount_nsum]
  rfl

/-- Theorem 3.5, summing over the two color classes of admissible extensions. -/
theorem theorem3_5 (G : MarkedGraph V) (D : Nat) (hD : 0 < D)
    (hp : Prepared D G) (F : Pattern k) (u : Fin k) (J : List (Fin k × Fin k)) :
    extensionDensitySum G D F u .blue (shiftPairs J) +
      extensionDensitySum G D F u .red (shiftPairs J) +
      extensionDensitySum G D F u .red ((u.succ, 0) :: shiftPairs J) =
    weightedDensity G D F J := by
  simp only [← extension_density_eq_sum G hp.1 D]
  exact degree_extension_density G D hD hp.2.2 (patternKeys (k + 1))
    (patternKeys_nodup (k + 1)) (fun f => patternKeys_complete _ (inducedPattern G f)) F u J

end FGST.Chapter3
