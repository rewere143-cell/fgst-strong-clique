import WeightedFlagAlgebra.MarkedHost

namespace FGST.Chapter3

abbrev Pattern (n : Nat) := Fin n → Fin n → EdgeColor

def inducedPattern (G : MarkedGraph V) (f : Fin n → V) : Pattern n :=
  fun i j => G.color (f i) (f j)

def PatternRedStrong (F : Pattern n) : Prop :=
  ∀ a b c d, F a b = .red → F c d = .red →
    a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    F a c ≠ .absent ∨ F a d ≠ .absent ∨ F b c ≠ .absent ∨ F b d ≠ .absent

theorem induced_pattern_redStrong (G : MarkedGraph V) (hs : G.Strong) (f : Fin n → V) :
    PatternRedStrong (inducedPattern G f) := by
  intro a b c d h₁ h₂ _ _ _ _
  have hw := G.marked_pair_cross hs (f a) (f b) (f c) (f d)
    ((G.color_eq_red _ _).mp h₁) ((G.color_eq_red _ _).mp h₂)
  exact hw.imp (G.color_ne_absent _ _).mpr (fun h => h.imp (G.color_ne_absent _ _).mpr
    (fun h => h.imp (G.color_ne_absent _ _).mpr (G.color_ne_absent _ _).mpr))

/-- The finite count in (3.4), with the positions in a specified pair kept distinct.
The product counts independent choices of extra instances, even for repeated images. -/
noncomputable def weightedCount (G : MarkedGraph V) (F : Pattern n) (J : List (Fin n × Fin n)) :
    Nat := by
  classical
  exact nsum (enumMaps G.host.vertices n) (fun f =>
    if F = inducedPattern G f then (J.map (fun p => G.extra (f p.1) (f p.2))).prod else 0)

theorem weightedCount_zero_of_unrealizable (G : MarkedGraph V) (F : Pattern n)
    (J : List (Fin n × Fin n)) (hn : ∀ f : Fin n → V, F ≠ inducedPattern G f) :
    weightedCount G F J = 0 := by
  unfold weightedCount
  rw [nsum_congr _ _ (fun _ => 0) (fun f _ => if_neg (hn f)), nsum_const, Nat.mul_zero]

/-- This expression also works for patterns with zero or one position. -/
noncomputable def weightedDensity (G : MarkedGraph V) (D : Nat) (F : Pattern n)
    (J : List (Fin n × Fin n)) : Rat :=
  ((D ^ 2 * weightedCount G F J : Nat) : Rat) /
    ((G.orientedMarked * D ^ n : Nat) : Rat)

private def chosenMultiplicity (G : MarkedGraph V) (extra : Bool) (u v : V) : Nat :=
  if extra then G.extra u v else G.base u v

def rootChoices : List (Bool × Bool) :=
  [(false, false), (false, true), (true, false), (true, true)]

def rootPairs (choice : Bool × Bool) : List (Fin 4 × Fin 4) :=
  (if choice.1 then [(0, 1)] else []) ++ (if choice.2 then [(2, 3)] else [])

private def rootWeight (G : MarkedGraph V) (choice : Bool × Bool) (f : Fin 4 → V) : Nat :=
  chosenMultiplicity G choice.1 (f 0) (f 1) *
    chosenMultiplicity G choice.2 (f 2) (f 3)

private theorem rootWeight_sum (G : MarkedGraph V) (f : Fin 4 → V) :
    nsum rootChoices (fun choice => rootWeight G choice f) =
      G.marked (f 0) (f 1) * G.marked (f 2) (f 3) := by
  rw [← G.base_add_extra (f 0) (f 1), ← G.base_add_extra (f 2) (f 3)]
  simp [rootChoices, rootWeight, chosenMultiplicity, Nat.add_mul, Nat.mul_add, Nat.add_assoc,
    Nat.add_left_comm]

/-- Counts only maps where both distinguished pairs are red. -/
noncomputable def twoRootCount (G : MarkedGraph V) (F : Pattern 4) (choice : Bool × Bool) : Nat :=
  if F 0 1 = .red ∧ F 2 3 = .red then weightedCount G F (rootPairs choice) else 0

private theorem twoRootCount_as_sum (G : MarkedGraph V) (F : Pattern 4) (choice : Bool × Bool) :
    twoRootCount G F choice =
      (by
        classical
        exact nsum (enumMaps G.host.vertices 4)
          (fun f => if F = inducedPattern G f then rootWeight G choice f else 0)) := by
  classical
  unfold twoRootCount
  split
  · rename_i h
    unfold weightedCount
    apply nsum_congr
    intro f _
    split
    · rename_i hf
      have h₁ : 0 < G.marked (f 0) (f 1) :=
        (G.color_eq_red _ _).mp (by simpa only [hf, inducedPattern] using h.1)
      have h₂ : 0 < G.marked (f 2) (f 3) :=
        (G.color_eq_red _ _).mp (by simpa only [hf, inducedPattern] using h.2)
      rcases choice with ⟨a, b⟩
      cases a <;> cases b <;>
        simp [rootPairs, rootWeight, chosenMultiplicity, MarkedGraph.base, h₁, h₂]
    · rfl
  · rename_i h
    symm
    rw [nsum_congr _ _ (fun _ => 0)]
    · simp [nsum_const]
    · intro f _
      split
      · rename_i hf
        have hc : ¬ 0 < G.marked (f 0) (f 1) ∨ ¬ 0 < G.marked (f 2) (f 3) := by
          have h' : ¬ (0 < G.marked (f 0) (f 1) ∧ 0 < G.marked (f 2) (f 3)) := by
            simpa only [hf, inducedPattern, MarkedGraph.color_eq_red] using h
          exact Classical.not_and_iff_not_or_not.mp h'
        rcases hc with hn | hn
        · have he : G.marked (f 0) (f 1) = 0 := by omega
          cases choice.1 <;> simp [rootWeight, chosenMultiplicity, MarkedGraph.base,
            MarkedGraph.extra, he]
        · have he : G.marked (f 2) (f 3) = 0 := by omega
          cases choice.2 <;> simp [rootWeight, chosenMultiplicity, MarkedGraph.base,
            MarkedGraph.extra, he]
      · rfl

theorem sum_enum_succ (vertices : List V) (k : Nat) (g : (Fin (k + 1) → V) → Nat) :
    nsum (enumMaps vertices (k + 1)) g =
      nsum vertices (fun v => nsum (enumMaps vertices k) (fun f => g (prependMap v f))) := by
  simp only [enumMaps, nsum_flatMap, nsum_map]

private theorem oriented_root_square (G : MarkedGraph V) :
    nsum (enumMaps G.host.vertices 4)
      (fun f => G.marked (f 0) (f 1) * G.marked (f 2) (f 3)) =
      G.orientedMarked * G.orientedMarked := by
  simp only [enumMaps, nsum_flatMap, nsum_map, nsum_cons, nsum_nil, Nat.add_zero]
  change nsum G.host.vertices (fun a => nsum G.host.vertices (fun b =>
    nsum G.host.vertices (fun c => nsum G.host.vertices (fun d =>
      G.marked a b * G.marked c d)))) = _
  simp only [nsum_mul]
  change nsum G.host.vertices (fun a => nsum G.host.vertices (fun b =>
    G.marked a b * G.orientedMarked)) = _
  simp only [Nat.mul_comm _ G.orientedMarked, nsum_mul]
  rfl

/-- The cardinality identity immediately before (3.5).
Patterns in the key list need only cover patterns realized by maps. All other keys count zero. -/
theorem two_root_count_total (G : MarkedGraph V) (keys : List (Pattern 4))
    (hn : keys.Nodup) (hc : ∀ f : Fin 4 → V, inducedPattern G f ∈ keys) :
    nsum keys (fun F => nsum rootChoices (twoRootCount G F)) =
      G.orientedMarked * G.orientedMarked := by
  classical
  rw [nsum_swap]
  refine Eq.trans (b := nsum rootChoices
    (fun choice => nsum (enumMaps G.host.vertices 4) (rootWeight G choice))) ?_ ?_
  · apply nsum_congr
    intro choice _
    rw [nsum_congr keys _ _
      (fun F _ => twoRootCount_as_sum G F choice)]
    exact nsum_partition _ keys (inducedPattern G) hn (fun f _ => hc f) _
  · rw [nsum_swap]
    refine Eq.trans (b := nsum (enumMaps G.host.vertices 4)
      (fun f => G.marked (f 0) (f 1) * G.marked (f 2) (f 3))) ?_ (oriented_root_square G)
    exact nsum_congr _ _ _ (fun f _ => rootWeight_sum G f)

end FGST.Chapter3
