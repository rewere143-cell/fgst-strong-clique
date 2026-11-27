import WeightedFlagAlgebra.CliqueTruncation
import WeightedFlagAlgebra.DensityArithmetic
import WeightedFlagAlgebra.Preparation

namespace FGST.Chapter3

universe u

private def colorKeys : List EdgeColor := [.absent, .blue, .red]

private theorem colorKeys_nodup : colorKeys.Nodup := by decide

private theorem colorKeys_complete (c : EdgeColor) : c ∈ colorKeys := by
  cases c <;> decide

def patternKeys (k : Nat) : List (Pattern k) := enumMaps (enumMaps colorKeys k) k

theorem patternKeys_nodup (k : Nat) : (patternKeys k).Nodup :=
  enumMaps_nodup _ (enumMaps_nodup _ colorKeys_nodup k) k

theorem patternKeys_complete (k : Nat) (F : Pattern k) : F ∈ patternKeys k :=
  enumMaps_complete _ (enumMaps_complete colorKeys colorKeys_complete k) k F

/-- M(Q) from §3.1. The two red roots and their four choices of extra marks
are enforced by twoRootCount. Unrealizable keys contribute zero. -/
noncomputable def objective (G : MarkedGraph V) (D : Nat) : Rat :=
  normalizeCount G.orientedMarked D 4
    (nsum (patternKeys 4) (fun F => nsum rootChoices (twoRootCount G F))) / 2

noncomputable def objectivePatterns : List (Pattern 4) := by
  classical
  exact (patternKeys 4).filter fun F => decide (F 0 1 = .red ∧ F 2 3 = .red ∧ PatternRedStrong F)

/-- The objective is one half of the density sum over the paper's pattern class
and specified-root subsets. Nonrealizable patterns contribute zero. -/
theorem objective_eq_pattern_sum (G : MarkedGraph V) (D : Nat) (hs : G.Strong) :
    objective G D =
      (objectivePatterns.map (fun F => (rootChoices.map (fun choice =>
        weightedDensity G D F (rootPairs choice))).sum)).sum / 2 := by
  classical
  unfold objective
  have h (F : Pattern 4) : nsum rootChoices (twoRootCount G F) =
      if F 0 1 = .red ∧ F 2 3 = .red ∧ PatternRedStrong F then
        nsum rootChoices (fun choice => weightedCount G F (rootPairs choice)) else 0 := by
    by_cases hp : F 0 1 = .red ∧ F 2 3 = .red
    · by_cases hS : PatternRedStrong F
      · rw [if_pos (show F 0 1 = .red ∧ F 2 3 = .red ∧ PatternRedStrong F from
          ⟨hp.1, hp.2, hS⟩)]
        exact nsum_congr _ _ _ (fun c _ => by unfold twoRootCount; rw [if_pos hp])
      · have hz (f : Fin 4 → V) : F ≠ inducedPattern G f := fun he =>
          hS (he ▸ induced_pattern_redStrong G hs f)
        rw [if_neg (show ¬ (F 0 1 = .red ∧ F 2 3 = .red ∧ PatternRedStrong F) from
          fun z => hS z.2.2)]
        rw [nsum_congr _ _ (fun _ => 0)]
        · simp [nsum_const]
        · intro c _
          unfold twoRootCount
          rw [if_pos hp, weightedCount_zero_of_unrealizable G F _ hz]
    · have hnp : ¬ (F 0 1 = .red ∧ F 2 3 = .red ∧ PatternRedStrong F) :=
        fun z => hp ⟨z.1, z.2.1⟩
      rw [if_neg hnp, nsum_congr _ _ (fun _ => 0)]
      · simp [nsum_const]
      · intro c _
        unfold twoRootCount
        rw [if_neg hp]
  rw [nsum_congr _ _ _ (fun F _ => h F)]
  have hf : nsum objectivePatterns (fun F => nsum rootChoices
      (fun choice => weightedCount G F (rootPairs choice))) =
      nsum (patternKeys 4) (fun F => if F 0 1 = .red ∧ F 2 3 = .red ∧ PatternRedStrong F then
        nsum rootChoices (fun choice => weightedCount G F (rootPairs choice)) else 0) := by
    unfold objectivePatterns
    rw [nsum_filter]
    simp only [decide_eq_true_eq]
  rw [← hf, normalizeCount_nsum]
  apply congrArg (fun (xs : List Rat) => xs.sum / 2)
  apply List.map_congr_left
  intro F _
  rw [normalizeCount_nsum]
  rfl

/-- Equation (3.5), with the clique size counting unordered edge instances. -/
theorem objective_eq_cliqueSize (G : MarkedGraph V) (D : Nat)
    (hD : 0 < D) (hm : 0 < G.cliqueSize) :
    objective G D = (G.cliqueSize : Rat) / ((D ^ 2 : Nat) : Rat) := by
  unfold objective
  have hMarked : 0 < G.orientedMarked := by
    rw [G.orientedMarked_eq_twice_cliqueSize]
    omega
  rw [normalized_two_root_objective G D hMarked hD _ (patternKeys_nodup 4)
    (fun f => patternKeys_complete 4 (inducedPattern G f))]
  rw [G.orientedMarked_eq_twice_cliqueSize, Rat.natCast_mul]
  have hc : ((2 * (G.cliqueSize : Rat)) / 2) = G.cliqueSize := by
    rw [Rat.mul_comm]
    exact Rat.mul_div_cancel (by decide)
  change ((2 * (G.cliqueSize : Rat)) / 2) / ((D ^ 2 : Nat) : Rat) = _
  rw [hc]

private theorem scaledNat_le_iff (D a b : Nat) (hD : 0 < D) :
    (a : Rat) / ((D ^ 2 : Nat) : Rat) ≤ (b : Rat) / ((D ^ 2 : Nat) : Rat) ↔ a ≤ b := by
  have hd : 0 < (((D ^ 2 : Nat) : Rat)) := Rat.natCast_pos.mpr (Nat.pow_pos hD)
  rw [Rat.div_def, Rat.div_def]
  have hi := Rat.inv_pos.mpr hd
  exact ⟨fun h => Rat.natCast_le_natCast.mp (Rat.le_of_mul_le_mul_right h hi),
    fun h => Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.mpr h)
      (Rat.le_of_lt hi)⟩

private theorem scaledNat_eq_iff (D a b : Nat) (hD : 0 < D) :
    (a : Rat) / ((D ^ 2 : Nat) : Rat) = (b : Rat) / ((D ^ 2 : Nat) : Rat) ↔ a = b := by
  constructor
  · intro h
    exact Nat.le_antisymm ((scaledNat_le_iff D a b hD).mp (h ▸ Rat.le_refl))
      ((scaledNat_le_iff D b a hD).mp (h ▸ Rat.le_refl))
  · rintro rfl
    rfl

private theorem prepared_cliqueSize {G : MarkedGraph V} {H : MarkedGraph W}
    (heq : H.orientedMarked = G.orientedMarked) : H.cliqueSize = G.cliqueSize := by
  rw [H.orientedMarked_eq_twice_cliqueSize, G.orientedMarked_eq_twice_cliqueSize] at heq
  omega

def CliqueUpperBound (D bound : Nat) : Prop :=
  ∀ (V : Type u) (G : MarkedGraph V), (∀ x, G.host.degree x ≤ D) → G.Strong →
    G.cliqueSize ≤ bound

def Prepared (D : Nat) (G : MarkedGraph V) : Prop :=
  G.Strong ∧ G.Reduced ∧ (∀ v, nsum G.host.vertices (G.reducedMultiplicity v) = D)

def DensityUpperBound (D bound : Nat) : Prop :=
  ∀ (V : Type u) (G : MarkedGraph V), Prepared D G → 0 < G.cliqueSize →
    objective G D ≤ (bound : Rat) / ((D ^ 2 : Nat) : Rat)

def ExcludesExactDensity (D bound : Nat) : Prop :=
  ¬ ∃ (V : Type u) (G : MarkedGraph V), Prepared D G ∧ 0 < G.cliqueSize ∧
    objective G D = ((bound + 1 : Nat) : Rat) / ((D ^ 2 : Nat) : Rat)

private theorem prepared_degree {G : MarkedGraph V} {D : Nat} (hp : Prepared D G) (v : V) :
    G.host.degree v = D := by
  have hr := hp.2.2 v
  rw [nsum_congr _ _ _ (fun w _ => hp.2.1 v w)] at hr
  exact hr

private theorem bound_iff_density (D bound : Nat) (hD : 0 < D) :
    CliqueUpperBound.{u} D bound ↔ DensityUpperBound.{u} D bound := by
  constructor
  · intro hb V G hp hm
    have hb' := hb V G (fun v => Nat.le_of_eq (prepared_degree hp v)) hp.1
    rw [objective_eq_cliqueSize G D hD hm]
    exact (scaledNat_le_iff D _ _ hD).mpr hb'
  · intro hd V G hb hs
    by_cases hm : 0 < G.cliqueSize
    · obtain ⟨W, H, hS, hE, hR, hDreg⟩ := G.exists_preparedHost D hD hs hb
      have hc := prepared_cliqueSize hE
      have hpos : 0 < H.cliqueSize := hc.symm ▸ hm
      have hHd := hd W H ⟨hS, hR, hDreg⟩ hpos
      rw [objective_eq_cliqueSize H D hD hpos] at hHd
      exact hc ▸ (scaledNat_le_iff D _ _ hD).mp hHd
    · omega

private theorem bound_iff_exact (D bound : Nat) (hD : 0 < D) :
    CliqueUpperBound.{u} D bound ↔ ExcludesExactDensity.{u} D bound := by
  constructor
  · intro hb hx
    obtain ⟨V, G, hp, hpos, heq⟩ := hx
    rw [objective_eq_cliqueSize G D hD hpos] at heq
    have hc := (scaledNat_eq_iff D _ _ hD).mp heq
    have hu := hb V G (fun v => Nat.le_of_eq (prepared_degree hp v)) hp.1
    omega
  · intro hx V G hd hs
    classical
    by_cases hb : G.cliqueSize ≤ bound
    · exact hb
    · exfalso
      obtain ⟨T, hhost, hS, _, hsize⟩ := G.truncateClique hs (bound + 1) (by omega)
      have hT : ∀ v, T.host.degree v ≤ D := by intro v; rw [hhost]; exact hd v
      obtain ⟨W, H, hHS, hE, hR, hReg⟩ := T.exists_preparedHost D hD hS hT
      have hc := prepared_cliqueSize hE
      have hpos : 0 < H.cliqueSize := by omega
      apply hx
      refine ⟨W, H, ⟨hHS, hR, hReg⟩, hpos, ?_⟩
      rw [objective_eq_cliqueSize H D hD hpos, hc, hsize]

def fgstBound (D : Nat) : Nat := D ^ 2 + (D / 2) ^ 2

/-- The three equivalent assertions of Theorem 3.2 for the conjectured bound. -/
theorem theorem3_2 (D : Nat) (hD : 0 < D) :
    (CliqueUpperBound.{u} D (fgstBound D) ↔ DensityUpperBound.{u} D (fgstBound D)) ∧
      (DensityUpperBound.{u} D (fgstBound D) ↔ ExcludesExactDensity.{u} D (fgstBound D)) :=
  ⟨bound_iff_density D _ hD, (bound_iff_density D _ hD).symm.trans (bound_iff_exact D _ hD)⟩

end FGST.Chapter3
