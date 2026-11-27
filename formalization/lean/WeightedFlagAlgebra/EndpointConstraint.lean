import WeightedFlagAlgebra.EndpointDensity
import WeightedFlagAlgebra.Objective

namespace FGST.Chapter3

private theorem product_zero (xs : List Nat) (h : 0 ∈ xs) : xs.prod = 0 := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with h | h
    · simp [← h]
    · simp [ih h]

private theorem weightedCount_zero_nonred (G : MarkedGraph V) (F : Pattern n)
    (J : List (Fin n × Fin n)) (p : Fin n × Fin n) (hJ : p ∈ J)
    (hc : F p.1 p.2 ≠ .red) : weightedCount G F J = 0 := by
  unfold weightedCount
  rw [nsum_congr _ _ (fun _ => 0)]
  · simp [nsum_const]
  · intro f _
    split
    · rename_i hf
      apply product_zero
      apply List.mem_map.mpr
      have hbad : ¬ 0 < G.marked (f p.1) (f p.2) := fun h =>
        hc (by rw [hf]; exact (G.color_eq_red _ _).mpr h)
      have hz : G.extra (f p.1) (f p.2) = 0 := by unfold MarkedGraph.extra; omega
      exact ⟨p, hJ, hz⟩
    · rfl

private theorem endpoint_count_support (G : MarkedGraph V) (hs : G.Strong) (F : Pattern 4)
    (h : ¬ (F 0 1 = .red ∧ F 2 3 = .red ∧ PatternRedStrong F)) :
    weightedCount G F endpointRoots = 0 := by
  by_cases h₁ : F 0 1 = .red
  · by_cases h₂ : F 2 3 = .red
    · apply weightedCount_zero_of_unrealizable
      intro f hf
      exact h ⟨h₁, h₂, hf ▸ induced_pattern_redStrong G hs f⟩
    · exact weightedCount_zero_nonred G F endpointRoots (2, 3) (by simp [endpointRoots]) h₂
  · exact weightedCount_zero_nonred G F endpointRoots (0, 1) (by simp [endpointRoots]) h₁

noncomputable def adjacentObjectivePatterns : List (Pattern 4) :=
  objectivePatterns.filter (fun F => decide (F 1 2 ≠ .absent))

private theorem total_count_eq (G : MarkedGraph V) (hs : G.Strong) :
    endpointPatternTotal G (patternKeys 4) =
      nsum objectivePatterns (fun F => weightedCount G F endpointRoots) := by
  classical
  unfold endpointPatternTotal objectivePatterns
  rw [nsum_filter]
  simp only [decide_eq_true_eq]
  apply nsum_congr
  intro F _
  split
  · rfl
  · exact endpoint_count_support G hs F (by assumption)

private theorem adjacent_count_eq (G : MarkedGraph V) (hs : G.Strong) :
    endpointPatternAdjacent G (patternKeys 4) =
      nsum adjacentObjectivePatterns (fun F => weightedCount G F endpointRoots) := by
  classical
  unfold endpointPatternAdjacent adjacentObjectivePatterns objectivePatterns
  rw [nsum_filter, nsum_filter]
  simp only [decide_eq_true_eq]
  apply nsum_congr
  intro F _
  by_cases hb : F 0 1 = .red ∧ F 2 3 = .red ∧ PatternRedStrong F
  · rw [if_pos hb]
  · rw [if_neg hb, endpoint_count_support G hs F hb]
    split <;> rfl

/-- Theorem 3.6, with the two four-position pattern classes and the three
star patterns as in (3.14). -/
theorem theorem3_6 (G : MarkedGraph V) (hs : G.Strong)
    (D : Nat) (hD : 0 < D) (hm : 0 < G.orientedMarked) :
    (objectivePatterns.map (fun F => weightedDensity G D F endpointRoots)).sum +
      2 / (D : Rat) * (edgeColors.map (fun c => weightedDensity G D (endpointStar c) starRoots)).sum ≤
      4 * (adjacentObjectivePatterns.map (fun F => weightedDensity G D F endpointRoots)).sum := by
  have h := endpoint_density_inequality G hs D hD hm (patternKeys 4)
    (patternKeys_nodup 4) (fun f => patternKeys_complete 4 (inducedPattern G f))
  rw [total_count_eq G hs, adjacent_count_eq G hs] at h
  unfold sharedPatternIncidences at h
  simp only [normalizeCount_nsum] at h
  exact h

end FGST.Chapter3
