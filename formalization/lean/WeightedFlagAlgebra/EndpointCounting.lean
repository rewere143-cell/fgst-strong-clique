import WeightedFlagAlgebra.MarkedHost

namespace FGST.Chapter3.MarkedGraph

private def indicator (p : Prop) [Decidable p] : Nat := if p then 1 else 0

private theorem indicator_pos [Decidable p] (h : p) : indicator p = 1 := if_pos h
private theorem indicator_zero [Decidable p] (h : ¬ p) : indicator p = 0 := if_neg h

/-- Number of endpoint orders that put an adjacency at positions 1 and 2. -/
def crossCount (G : MarkedGraph V) (a b c d : V) : Nat :=
  indicator (G.Adj a c) + indicator (G.Adj a d) +
    (indicator (G.Adj b c) + indicator (G.Adj b d))

/-- Shared vertex incidences for this pair of edges, including two on a parallel pair. -/
def commonCount [DecidableEq V] (a b c d : V) : Nat :=
  indicator (a = c) + indicator (a = d) + (indicator (b = c) + indicator (b = d))

private theorem single_choice [DecidableEq V] (v x y : V) (h : x ≠ y) :
    indicator (v = x) + indicator (v = y) ≤ 1 := by
  by_cases h₁ : v = x
  · have h₂ : v ≠ y := fun he => h (h₁.symm.trans he)
    rw [indicator_pos h₁, indicator_zero h₂]
    decide
  · rw [indicator_zero h₁]
    by_cases h₂ : v = y
    · rw [indicator_pos h₂]
      decide
    · rw [indicator_zero h₂]
      decide

/-- The endpoint-order contribution of one pair, including parallel edges. -/
theorem crossCount_lower [DecidableEq V] (G : MarkedGraph V) (hs : G.Strong)
    (a b c d : V) (h₁ : 0 < G.extra a b) (h₂ : 0 < G.extra c d) :
    2 + commonCount a b c d ≤ 2 * G.crossCount a b c d := by
  have hred₁ : 0 < G.marked a b := by unfold extra at h₁; omega
  have hred₂ : 0 < G.marked c d := by unfold extra at h₂; omega
  have hcd : c ≠ d := by
    intro he
    subst d
    simp [G.marked_loopless] at hred₂
  have hlim : commonCount a b c d ≤ 2 := by
    unfold commonCount
    exact Nat.add_le_add (single_choice a c d hcd) (single_choice b c d hcd)
  have hab : G.Adj a b := Nat.lt_of_lt_of_le hred₁ (G.marked_le a b)
  have hba : G.Adj b a := by simpa [← G.host.symmetric a b] using hab
  have hcd' : G.Adj c d := Nat.lt_of_lt_of_le hred₂ (G.marked_le c d)
  have hdc : G.Adj d c := by simpa [← G.host.symmetric c d] using hcd'
  by_cases hac : a = c
  · have ha : G.Adj a d := hac.symm ▸ hcd'
    have hb : G.Adj b c := hac ▸ hba
    unfold crossCount
    rw [indicator_pos ha, indicator_pos hb]
    omega
  by_cases had : a = d
  · have ha : G.Adj a c := had.symm ▸ hdc
    have hb : G.Adj b d := had ▸ hba
    unfold crossCount
    rw [indicator_pos ha, indicator_pos hb]
    omega
  by_cases hbc : b = c
  · have ha : G.Adj a c := hbc ▸ hab
    have hb : G.Adj b d := hbc.symm ▸ hcd'
    unfold crossCount
    rw [indicator_pos ha, indicator_pos hb]
    omega
  by_cases hbd : b = d
  · have ha : G.Adj a d := hbd ▸ hab
    have hb : G.Adj b c := hbd.symm ▸ hdc
    unfold crossCount
    rw [indicator_pos ha, indicator_pos hb]
    omega
  have hn : commonCount a b c d = 0 := by simp [commonCount, indicator, hac, had, hbc, hbd]
  rw [hn]
  have hw := G.marked_pair_cross hs a b c d hred₁ hred₂
  unfold crossCount
  rcases hw with h | h | h | h <;> rw [indicator_pos h] <;> omega

def extraDegree (G : MarkedGraph V) (v : V) : Nat := nsum G.host.vertices (G.extra v)

/-- Sum over oriented extra edge instances, with multiplicity as the weight. -/
def extraEdgeSum (G : MarkedGraph V) (f : V → V → Nat) : Nat :=
  nsum G.host.vertices (fun u => nsum G.host.vertices (fun v => G.extra u v * f u v))

def extraPairSum (G : MarkedGraph V) (f : V → V → V → V → Nat) : Nat :=
  G.extraEdgeSum (fun a b => G.extraEdgeSum (f a b))

private theorem extraEdgeSum_congr (G : MarkedGraph V) (f g : V → V → Nat)
    (h : ∀ a b, f a b = g a b) : G.extraEdgeSum f = G.extraEdgeSum g := by
  unfold extraEdgeSum
  apply nsum_congr
  intro a _
  exact nsum_congr _ _ _ (fun b _ => by rw [h])

private theorem extraEdgeSum_add (G : MarkedGraph V) (f g : V → V → Nat) :
    G.extraEdgeSum (fun a b => f a b + g a b) = G.extraEdgeSum f + G.extraEdgeSum g := by
  unfold extraEdgeSum
  rw [← nsum_add]
  apply nsum_congr
  intro a _
  rw [← nsum_add]
  exact nsum_congr _ _ _ (fun b _ => Nat.mul_add ..)

private theorem extraEdgeSum_scale (G : MarkedGraph V) (f : V → V → Nat) (k : Nat) :
    G.extraEdgeSum (fun a b => k * f a b) = k * G.extraEdgeSum f := by
  unfold extraEdgeSum
  rw [← nsum_mul]
  apply nsum_congr
  intro a _
  rw [← nsum_mul]
  apply nsum_congr
  intro b _
  change G.extra a b * (k * f a b) = k * (G.extra a b * f a b)
  ac_rfl

private theorem extraEdgeSum_flip (G : MarkedGraph V) (f : V → V → Nat) :
    G.extraEdgeSum (fun a b => f b a) = G.extraEdgeSum f := by
  unfold extraEdgeSum
  rw [nsum_swap]
  apply nsum_congr
  intro b _
  exact nsum_congr _ _ _ (fun a _ => by rw [show G.extra a b = G.extra b a by
    simp [MarkedGraph.extra, G.marked_symm a b]])

private theorem extraEdgeSum_left (G : MarkedGraph V) (f : V → Nat) :
    G.extraEdgeSum (fun a _ => f a) =
      nsum G.host.vertices (fun a => G.extraDegree a * f a) := by
  unfold extraEdgeSum extraDegree
  apply nsum_congr
  intro a _
  rw [Nat.mul_comm, ← nsum_mul]
  exact nsum_congr _ _ _ (fun b _ => Nat.mul_comm _ _)

private theorem extraPairSum_add (G : MarkedGraph V) (f g : V → V → V → V → Nat) :
    G.extraPairSum (fun a b c d => f a b c d + g a b c d) =
      G.extraPairSum f + G.extraPairSum g := by
  unfold extraPairSum
  simp only [extraEdgeSum_add]

private theorem extraPairSum_scale (G : MarkedGraph V) (f : V → V → V → V → Nat) (k : Nat) :
    G.extraPairSum (fun a b c d => k * f a b c d) = k * G.extraPairSum f := by
  unfold extraPairSum
  simp only [extraEdgeSum_scale]

private theorem extraPairSum_flip_first (G : MarkedGraph V) (f : V → V → V → V → Nat) :
    G.extraPairSum (fun a b c d => f b a c d) = G.extraPairSum f :=
  extraEdgeSum_flip G (fun a b => G.extraEdgeSum (f a b))

private theorem extraPairSum_flip_second (G : MarkedGraph V) (f : V → V → V → V → Nat) :
    G.extraPairSum (fun a b c d => f a b d c) = G.extraPairSum f :=
  extraEdgeSum_congr _ _ _ (fun a b => extraEdgeSum_flip G (f a b))

private theorem extraPairSum_le (G : MarkedGraph V) (f g : V → V → V → V → Nat)
    (h : ∀ a b c d, 0 < G.extra a b → 0 < G.extra c d → f a b c d ≤ g a b c d) :
    G.extraPairSum f ≤ G.extraPairSum g := by
  unfold extraPairSum extraEdgeSum
  apply nsum_le
  intro a _
  apply nsum_le
  intro b _
  by_cases hab : 0 < G.extra a b
  · apply Nat.mul_le_mul_left
    apply nsum_le
    intro c _
    apply nsum_le
    intro d _
    by_cases hcd : 0 < G.extra c d
    · exact Nat.mul_le_mul_left _ (h a b c d hab hcd)
    · simp [show G.extra c d = 0 by omega]
  · simp [show G.extra a b = 0 by omega]

def adjacentOrderCount (G : MarkedGraph V) : Nat :=
  G.extraPairSum (fun _ b c _ => indicator (G.Adj b c))

def sharedIncidenceCount (G : MarkedGraph V) : Nat :=
  nsum G.host.vertices (fun v => G.extraDegree v * G.extraDegree v)

private theorem extraPairSum_four (G : MarkedGraph V) (f : V → V → Nat) :
    G.extraPairSum (fun a b c d => f a c + f a d + (f b c + f b d)) =
      4 * G.extraPairSum (fun a _ c _ => f a c) := by
  have h₁ := extraPairSum_flip_first G (fun a _ c _ => f a c)
  have h₂ := extraPairSum_flip_second G (fun a _ c _ => f a c)
  have h₃ := extraPairSum_flip_second G (fun _ b c _ => f b c)
  simp only [extraPairSum_add, h₁, h₂, h₃]
  omega

private theorem extraPairSum_eq (G : MarkedGraph V) [DecidableEq V] :
    G.extraPairSum (fun a _ c _ => indicator (a = c)) = G.sharedIncidenceCount := by
  unfold extraPairSum sharedIncidenceCount
  rw [extraEdgeSum_left]
  apply nsum_congr
  intro a _
  rw [extraEdgeSum_left]
  have h : nsum G.host.vertices (fun c => G.extraDegree c * indicator (a = c)) =
      G.extraDegree a := by
    rw [nsum_congr _ _ (fun c => if c = a then G.extraDegree a else 0)]
    · exact nsum_single _ G.host.nodup a (G.host.complete a) _
    · intro c _
      by_cases hc : c = a
      · subst c
        simp [indicator]
      · simp [indicator, hc, Ne.symm hc]
  rw [h]

private theorem totalPairs (G : MarkedGraph V) :
    G.extraPairSum (fun _ _ _ _ => 1) = G.orientedExtra * G.orientedExtra := by
  unfold extraPairSum
  rw [extraEdgeSum_left]
  have h₁ : G.extraEdgeSum (fun _ _ => 1) = G.orientedExtra := by
    simp [extraEdgeSum, orientedExtra]
  have h₂ : nsum G.host.vertices G.extraDegree = G.orientedExtra := rfl
  rw [h₁]
  rw [nsum_congr _ _ (fun a => G.orientedExtra * G.extraDegree a)]
  · rw [nsum_mul, h₂]
  · intro a _
    exact Nat.mul_comm _ _

/-- Exact count form of Theorem 3.6, before partitioning by induced patterns.
The two occurrences of each extra edge are counted independently. -/
theorem endpoint_order_inequality (G : MarkedGraph V) (hs : G.Strong) :
    G.orientedExtra * G.orientedExtra + 2 * G.sharedIncidenceCount ≤
      4 * G.adjacentOrderCount := by
  classical
  have h := extraPairSum_le G (fun a b c d => 2 + commonCount a b c d)
    (fun a b c d => 2 * G.crossCount a b c d)
    (fun a b c d hab hcd => G.crossCount_lower hs a b c d hab hcd)
  have hcross : G.extraPairSum G.crossCount = 4 * G.adjacentOrderCount := by
    unfold crossCount adjacentOrderCount
    rw [extraPairSum_four]
    rw [extraPairSum_flip_first G (fun a _ c _ => indicator (G.Adj a c))]
  have hcommon : G.extraPairSum commonCount = 4 * G.sharedIncidenceCount := by
    unfold commonCount
    rw [extraPairSum_four, extraPairSum_eq]
  have h2 : G.extraPairSum (fun _ _ _ _ => 2) = 2 * (G.orientedExtra * G.orientedExtra) := by
    change G.extraPairSum (fun _ _ _ _ => 2 * 1) = _
    rw [extraPairSum_scale, totalPairs]
  rw [extraPairSum_add, extraPairSum_scale, h2, hcross, hcommon] at h
  omega

#print axioms endpoint_order_inequality

end FGST.Chapter3.MarkedGraph
