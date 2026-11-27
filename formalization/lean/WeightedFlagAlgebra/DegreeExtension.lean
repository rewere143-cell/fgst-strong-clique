import WeightedFlagAlgebra.WeightedCounts

namespace FGST.Chapter3

def specifiedWeight (G : MarkedGraph V) (J : List (Fin n × Fin n)) (f : Fin n → V) : Nat :=
  (J.map (fun p => G.extra (f p.1) (f p.2))).prod

/-- Group the count by the induced pattern, with a restriction on which keys are used. -/
theorem group_weightedCount (G : MarkedGraph V) (keys : List (Pattern n))
    (hn : keys.Nodup) (hc : ∀ f : Fin n → V, inducedPattern G f ∈ keys)
    (keep : Pattern n → Prop) [DecidablePred keep] (J : List (Fin n × Fin n)) :
    nsum keys (fun H => if keep H then weightedCount G H J else 0) =
      nsum (enumMaps G.host.vertices n) (fun f =>
        if keep (inducedPattern G f) then specifiedWeight G J f else 0) := by
  classical
  refine Eq.trans (b := nsum keys (fun H => nsum (enumMaps G.host.vertices n) (fun f =>
    if H = inducedPattern G f then
      (if keep (inducedPattern G f) then specifiedWeight G J f else 0)
    else 0))) ?_ (nsum_partition _ keys (inducedPattern G) hn (fun f _ => hc f) _)
  apply nsum_congr
  intro H _
  by_cases hk : keep H
  · simp only [if_pos hk, weightedCount]
    apply nsum_congr
    intro f _
    by_cases h : H = inducedPattern G f
    · subst H
      simp [hk, specifiedWeight]
    · simp [h]
  · rw [if_neg hk]
    symm
    rw [nsum_congr _ _ (fun _ => 0)]
    · simp [nsum_const]
    · intro f _
      by_cases h : H = inducedPattern G f
      · subst H
        simp [hk]
      · simp [h]

/-- The old positions are shifted once, so the new position is numbered zero.
This is the same extension as adding the last position, with all positions relabeled. -/
def oldPattern (H : Pattern (k + 1)) : Pattern k := fun i j => H i.succ j.succ

def shiftPairs (J : List (Fin k × Fin k)) : List (Fin (k + 1) × Fin (k + 1)) :=
  J.map fun p => (p.1.succ, p.2.succ)

def KeepExtension (F : Pattern k) (u : Fin k) (color : EdgeColor) (H : Pattern (k + 1)) :
    Prop := oldPattern H = F ∧ H u.succ 0 = color

noncomputable def extensionCount (G : MarkedGraph V) (keys : List (Pattern (k + 1)))
    (F : Pattern k) (u : Fin k) (color : EdgeColor) (J : List (Fin (k + 1) × Fin (k + 1))) :
    Nat := by
  classical
  exact nsum keys (fun H => if KeepExtension F u color H then weightedCount G H J else 0)

private theorem extensionCount_as_maps (G : MarkedGraph V) (keys : List (Pattern (k + 1)))
    (hn : keys.Nodup) (hc : ∀ f : Fin (k + 1) → V, inducedPattern G f ∈ keys)
    (F : Pattern k) (u : Fin k) (color : EdgeColor) (J : List (Fin (k + 1) × Fin (k + 1))) :
    extensionCount G keys F u color J = (by
      classical
      exact nsum (enumMaps G.host.vertices (k + 1)) (fun f =>
        if KeepExtension F u color (inducedPattern G f) then specifiedWeight G J f else 0)) := by
  classical
  exact group_weightedCount G keys hn hc (KeepExtension F u color) J

@[simp] theorem old_induced_prepend (G : MarkedGraph V) (v : V) (f : Fin k → V) :
    oldPattern (inducedPattern G (prependMap v f)) = inducedPattern G f := by
  funext i j
  simp [inducedPattern, oldPattern, prependMap]

@[simp] theorem weight_shift_prepend (G : MarkedGraph V) (J : List (Fin k × Fin k))
    (v : V) (f : Fin k → V) :
    specifiedWeight G (shiftPairs J) (prependMap v f) = specifiedWeight G J f := by
  simp [specifiedWeight, shiftPairs, List.map_map, Function.comp_def, prependMap]

private theorem reduced_cases (G : MarkedGraph V) (v w : V) (weight : Nat) :
    (if G.color v w = .blue then weight else 0) +
      (if G.color v w = .red then weight else 0) +
      (if G.color v w = .red then G.extra v w * weight else 0) =
    G.reducedMultiplicity v w * weight := by
  by_cases hm : 0 < G.marked v w
  · have hc := (G.color_eq_red v w).mpr hm
    have hb : G.base v w = 1 := by simp [MarkedGraph.base, hm]
    have hpart := G.base_add_extra v w
    rw [hb] at hpart
    simp [hc, MarkedGraph.reducedMultiplicity, MarkedGraph.blue, ← hpart, Nat.add_mul]
  · have hz : G.marked v w = 0 := by omega
    have hn : G.color v w ≠ .red := fun h => hm ((G.color_eq_red v w).mp h)
    by_cases hb : G.color v w = .blue <;>
      simp [hb, hn, hz, MarkedGraph.reducedMultiplicity, MarkedGraph.blue]

/-- The finite integer count of all three extensions in the proof of (3.13).
The degree assumption is precisely regularity after deleting unmarked parallel copies. -/
theorem degree_extension_raw (G : MarkedGraph V) (D : Nat)
    (regular : ∀ v, nsum G.host.vertices (G.reducedMultiplicity v) = D)
    (keys : List (Pattern (k + 1))) (hn : keys.Nodup)
    (hc : ∀ f : Fin (k + 1) → V, inducedPattern G f ∈ keys)
    (F : Pattern k) (u : Fin k) (J : List (Fin k × Fin k)) :
    extensionCount G keys F u .blue (shiftPairs J) +
      extensionCount G keys F u .red (shiftPairs J) +
      extensionCount G keys F u .red ((u.succ, 0) :: shiftPairs J) =
    D * weightedCount G F J := by
  classical
  simp only [extensionCount_as_maps G keys hn hc, ← nsum_add, sum_enum_succ,
    nsum_swap G.host.vertices (enumMaps G.host.vertices k)]
  unfold weightedCount
  rw [← nsum_mul]
  apply nsum_congr
  intro f _
  by_cases hf : inducedPattern G f = F
  · rw [if_pos hf.symm]
    refine Eq.trans (b := nsum G.host.vertices (fun v =>
      G.reducedMultiplicity (f u) v * specifiedWeight G J f)) ?_ ?_
    · apply nsum_congr
      intro v _
      simpa [KeepExtension, hf, inducedPattern, prependMap, specifiedWeight, shiftPairs,
        List.map_map, Function.comp_def] using
        reduced_cases G (f u) v (specifiedWeight G J f)
    · simp only [Nat.mul_comm _ (specifiedWeight G J f), nsum_mul, regular]
      rw [Nat.mul_comm]
      rfl
  · rw [if_neg (Ne.symm hf), Nat.mul_zero]
    rw [nsum_congr _ _ (fun _ => 0)]
    · simp [nsum_const]
    · intro v _
      simp [KeepExtension, hf]

end FGST.Chapter3
