import WeightedFlagAlgebra.MarkedHost

namespace FGST.Chapter3.MarkedGraph

variable {V : Type u} [DecidableEq V]

abbrev Outside (u v x : V) : Prop := x ≠ u ∧ x ≠ v

def outsideSum (G : MarkedGraph V) (u v : V) (f : V → Nat) : Nat :=
  nsum G.host.vertices fun x => if Outside u v x then f x else 0

abbrev RootNeighbor (G : MarkedGraph V) (u v x : V) : Prop :=
  Outside u v x ∧ (G.Adj u x ∨ G.Adj v x)

def rootNeighborCount (G : MarkedGraph V) (u v : V) : Nat :=
  nsum G.host.vertices fun x => if G.RootNeighbor u v x then 1 else 0

def outsideMarked (G : MarkedGraph V) (u v : V) : Nat :=
  G.outsideSum u v fun x => G.outsideSum u v (G.marked x)

private theorem outsideSum_add (G : MarkedGraph V) (u v : V) (f g : V → Nat) :
    G.outsideSum u v (fun x => f x + g x) = G.outsideSum u v f + G.outsideSum u v g := by
  unfold outsideSum
  rw [← nsum_add]
  apply nsum_congr
  intro x _
  by_cases hx : Outside u v x
  · simp only [if_pos hx]
  · simp only [if_neg hx, Nat.zero_add]

private theorem outsideSum_mul (G : MarkedGraph V) (u v : V) (c : Nat) (f : V → Nat) :
    G.outsideSum u v (fun x => c * f x) = c * G.outsideSum u v f := by
  unfold outsideSum
  rw [← nsum_mul]
  apply nsum_congr
  intro x _
  by_cases hx : Outside u v x
  · simp only [if_pos hx]
  · simp only [if_neg hx, Nat.mul_zero]

private theorem outsideSum_congr (G : MarkedGraph V) (u v : V) (f g : V → Nat)
    (h : ∀ x, Outside u v x → f x = g x) : G.outsideSum u v f = G.outsideSum u v g := by
  apply nsum_congr
  intro x _
  by_cases hx : Outside u v x
  · simpa only [outsideSum, if_pos hx] using h x hx
  · simp only [if_neg hx]

private theorem outsideSum_split (G : MarkedGraph V) (u v : V) (huv : u ≠ v) (f : V → Nat) :
    nsum G.host.vertices f = f u + f v + G.outsideSum u v f :=
  nsum_split_pair G.host.vertices G.host.nodup u v (G.host.complete u) (G.host.complete v) huv f

private theorem host_degree_split (G : MarkedGraph V) (u v x : V) (huv : u ≠ v) :
    G.host.degree x = G.host.multiplicity x u + G.host.multiplicity x v +
      G.outsideSum u v (G.host.multiplicity x) :=
  G.outsideSum_split u v huv (G.host.multiplicity x)

private theorem red_degree_split (G : MarkedGraph V) (u v x : V) (huv : u ≠ v) :
    G.redDegree x = G.marked x u + G.marked x v + G.outsideSum u v (G.marked x) :=
  G.outsideSum_split u v huv (G.marked x)

private theorem red_outside_le_degree (G : MarkedGraph V) (u v x : V) :
    G.outsideSum u v (G.marked x) ≤ G.outsideSum u v (G.host.multiplicity x) := by
  apply nsum_le
  intro y _
  by_cases hy : Outside u v y
  · simpa only [if_pos hy] using G.marked_le x y
  · simp only [if_neg hy, Nat.le_refl]

/-- Decomposition into the common root pair, root-to-outside edges, and outside edges,
with both orientations counted. -/
theorem oriented_marked_split (G : MarkedGraph V) (u v : V) (huv : u ≠ v) :
    G.orientedMarked =
      2 * (G.marked u v + G.outsideSum u v (G.marked u) + G.outsideSum u v (G.marked v)) +
        G.outsideMarked u v := by
  unfold orientedMarked
  rw [G.outsideSum_split u v huv]
  have ho : G.outsideSum u v G.redDegree =
      G.outsideSum u v (G.marked u) + G.outsideSum u v (G.marked v) + G.outsideMarked u v := by
    calc
      _ = G.outsideSum u v (fun x => G.marked u x + G.marked v x +
          G.outsideSum u v (G.marked x)) := by
        apply G.outsideSum_congr
        intro x _
        rw [G.red_degree_split u v x huv, G.marked_symm x u, G.marked_symm x v]
      _ = _ := by rw [G.outsideSum_add, G.outsideSum_add]; rfl
  rw [ho, G.red_degree_split u v u huv, G.red_degree_split u v v huv,
    G.marked_loopless, G.marked_loopless, G.marked_symm v u]
  omega

private theorem rootCount_le_outside (G : MarkedGraph V) (u v : V) :
    G.rootNeighborCount u v ≤ G.outsideSum u v (G.host.multiplicity u) +
      G.outsideSum u v (G.host.multiplicity v) := by
  unfold rootNeighborCount outsideSum
  rw [← nsum_add]
  apply nsum_le
  intro x _
  by_cases hx : Outside u v x
  · by_cases ha : G.Adj u x ∨ G.Adj v x
    · simp only [if_pos (show G.RootNeighbor u v x from ⟨hx, ha⟩), if_pos hx]
      rcases ha with ha | ha <;> omega
    · rw [if_neg (show ¬ G.RootNeighbor u v x from fun h => ha h.2), if_pos hx, if_pos hx]
      exact Nat.zero_le _
  · simp only [if_neg (show ¬ G.RootNeighbor u v x from fun h => hx h.1), if_neg hx,
      Nat.zero_add, Nat.le_refl]

private theorem outside_neighbor_capacity (G : MarkedGraph V) (u v x : V) (huv : u ≠ v)
    (hdeg : ∀ y, G.host.degree y ≤ 4) (hx : G.RootNeighbor u v x) :
    G.outsideSum u v (G.marked x) ≤ 3 := by
  have hdom := G.red_outside_le_degree u v x
  have hdx := hdeg x
  rw [G.host_degree_split u v x huv] at hdx
  rcases hx.2 with h | h
  · rw [← G.host.symmetric u x] at hdx
    omega
  · rw [← G.host.symmetric v x] at hdx
    omega

private theorem outside_count_le (G : MarkedGraph V) (hs : G.Strong) (u v : V)
    (huv : u ≠ v) (hred : 0 < G.marked u v) (hdeg : ∀ x, G.host.degree x ≤ 4) :
    G.outsideMarked u v ≤ 6 * G.rootNeighborCount u v := by
  let left := nsum G.host.vertices (fun x =>
    if G.RootNeighbor u v x then G.outsideSum u v (G.marked x) else 0)
  have hcap : left ≤ 3 * G.rootNeighborCount u v := by
    unfold left rootNeighborCount
    rw [← nsum_mul]
    apply nsum_le
    intro x _
    by_cases hx : G.RootNeighbor u v x
    · simpa only [if_pos hx, Nat.mul_one] using G.outside_neighbor_capacity u v x huv hdeg hx
    · simp only [if_neg hx, Nat.mul_zero, Nat.le_refl]
  have hcover : G.outsideMarked u v ≤ left + left := by
    let a := fun x y => if G.RootNeighbor u v x ∧ Outside u v y then G.marked x y else 0
    have ha : left = nsum G.host.vertices (fun x => nsum G.host.vertices (a x)) := by
      apply nsum_congr
      intro x _
      by_cases hx : G.RootNeighbor u v x
      · simp only [a, outsideSum, if_pos hx]
        apply nsum_congr
        intro y _
        by_cases hy : Outside u v y
        · simp only [if_pos hy, if_pos (show G.RootNeighbor u v x ∧ Outside u v y from ⟨hx, hy⟩)]
        · simp only [if_neg hy, if_neg (show ¬ (G.RootNeighbor u v x ∧ Outside u v y) from
            fun h => hy h.2)]
      · simp only [a, if_neg hx]
        symm
        rw [nsum_congr _ _ (fun _ => 0)]
        · simp [nsum_const]
        · intro y _
          exact if_neg (fun h => hx h.1)
    have hsides : left + left = nsum G.host.vertices (fun x =>
      nsum G.host.vertices (a x) + nsum G.host.vertices (fun y => a y x)) := by
      calc
        _ = nsum G.host.vertices (fun x => nsum G.host.vertices (a x)) + left :=
          congrArg (fun t => t + left) ha
        _ = _ := by
          rw [nsum_add]
          exact congrArg (nsum G.host.vertices (fun x => nsum G.host.vertices (a x)) + ·)
            (ha.trans (nsum_swap G.host.vertices G.host.vertices a))
    rw [hsides]
    unfold outsideMarked outsideSum
    apply nsum_le
    intro x _
    rw [← nsum_add]
    by_cases hx : Outside u v x
    · simp only [if_pos hx]
      apply nsum_le
      intro y _
      by_cases hy : Outside u v y
      · simp only [if_pos hy]
        by_cases hz : 0 < G.marked x y
        · have h := hs u v x y hred hz (Ne.symm hx.1) (Ne.symm hy.1)
            (Ne.symm hx.2) (Ne.symm hy.2)
          rcases h with h | h | h | h
          · have hx' : G.RootNeighbor u v x := ⟨hx, Or.inl h⟩
            simpa only [a, if_pos (show G.RootNeighbor u v x ∧ Outside u v y from ⟨hx', hy⟩)]
              using Nat.le_add_right (G.marked x y) (a y x)
          · have hy' : G.RootNeighbor u v y := ⟨hy, Or.inl h⟩
            simpa only [a, if_pos (show G.RootNeighbor u v y ∧ Outside u v x from ⟨hy', hx⟩),
              G.marked_symm y x] using Nat.le_add_left (G.marked x y) (a x y)
          · have hx' : G.RootNeighbor u v x := ⟨hx, Or.inr h⟩
            simpa only [a, if_pos (show G.RootNeighbor u v x ∧ Outside u v y from ⟨hx', hy⟩)]
              using Nat.le_add_right (G.marked x y) (a y x)
          · have hy' : G.RootNeighbor u v y := ⟨hy, Or.inr h⟩
            simpa only [a, if_pos (show G.RootNeighbor u v y ∧ Outside u v x from ⟨hy', hx⟩),
              G.marked_symm y x] using Nat.le_add_left (G.marked x y) (a x y)
        · have hzero : G.marked x y = 0 := by omega
          simp [hzero]
      · rw [if_neg hy]
        exact Nat.zero_le _
    · rw [if_neg hx]
      exact Nat.zero_le _
  omega

/-- The repeated-root bound within Theorem 3.7, in oriented counts. -/
theorem degreeFour_parallel_bound (G : MarkedGraph V) (hs : G.Strong)
    (hdeg : ∀ x, G.host.degree x ≤ 4) (u v : V) (hk : 0 < G.marked u v) :
    G.orientedMarked + 14 * G.marked u v ≤ 64 := by
  have huv : u ≠ v := by
    intro h
    subst v
    rw [G.marked_loopless] at hk
    omega
  have hu := hdeg u
  have hv := hdeg v
  rw [G.host_degree_split u v u huv, G.host.loopless] at hu
  rw [G.host_degree_split u v v huv, G.host.loopless, G.host.symmetric v u] at hv
  have hmult := G.marked_le u v
  have hq := G.rootCount_le_outside u v
  have hr₁ := G.red_outside_le_degree u v u
  have hr₂ := G.red_outside_le_degree u v v
  have hw := G.outside_count_le hs u v huv hk hdeg
  have hsplit := G.oriented_marked_split u v huv
  omega

structure ParallelRootStructure (G : MarkedGraph V) (u v : V) : Prop where
  distinct : u ≠ v
  common : G.marked u v = 2
  neighbors : G.rootNeighborCount u v = 4
  left_marked : G.outsideSum u v (G.marked u) = 2
  right_marked : G.outsideSum u v (G.marked v) = 2
  outside : ∀ x, Outside u v x → G.host.multiplicity u x + G.host.multiplicity v x ≤ 1 ∧
    G.marked u x = G.host.multiplicity u x ∧ G.marked v x = G.host.multiplicity v x

/-- Theorem 3.7: in the equality case both roots have two distinct, fully marked
outer incidences, and their outside neighbor sets are disjoint. -/
theorem degreeFour_parallel_structure (G : MarkedGraph V) (hs : G.Strong)
    (hdeg : ∀ x, G.host.degree x ≤ 4) (hm : 36 ≤ G.orientedMarked)
    (u v : V) (hk : 2 ≤ G.marked u v) : G.ParallelRootStructure u v := by
  have hred : 0 < G.marked u v := by omega
  have hmark := G.degreeFour_parallel_bound hs hdeg u v hred
  have htwo : G.marked u v = 2 := by omega
  have huv : u ≠ v := by
    intro h
    subst v
    rw [G.marked_loopless] at htwo
    omega
  have hu := hdeg u
  have hv := hdeg v
  rw [G.host_degree_split u v u huv, G.host.loopless] at hu
  rw [G.host_degree_split u v v huv, G.host.loopless, G.host.symmetric v u] at hv
  have hmult := G.marked_le u v
  have hq := G.rootCount_le_outside u v
  have hr₁ := G.red_outside_le_degree u v u
  have hr₂ := G.red_outside_le_degree u v v
  have hw := G.outside_count_le hs u v huv hred hdeg
  have hsplit := G.oriented_marked_split u v huv
  have hfour : G.rootNeighborCount u v = 4 := by omega
  have hru : G.outsideSum u v (G.marked u) = 2 := by omega
  have hrv : G.outsideSum u v (G.marked v) = 2 := by omega
  have hmu : G.outsideSum u v (G.host.multiplicity u) = 2 := by omega
  have hmv : G.outsideSum u v (G.host.multiplicity v) = 2 := by omega
  refine ⟨huv, htwo, hfour, hru, hrv, ?_⟩
  intro x hx
  let indicator := fun y => if G.RootNeighbor u v y then 1 else 0
  let incidences := fun y =>
    (if Outside u v y then G.host.multiplicity u y else 0) +
    (if Outside u v y then G.host.multiplicity v y else 0)
  have hsum : nsum G.host.vertices indicator = nsum G.host.vertices incidences := by
    have hsum' : G.rootNeighborCount u v = G.outsideSum u v (G.host.multiplicity u) +
        G.outsideSum u v (G.host.multiplicity v) := by omega
    simpa only [rootNeighborCount, outsideSum, indicator, incidences, nsum_add] using hsum'
  have hterm := term_eq_of_sum_eq G.host.vertices indicator incidences (by
    intro y _
    unfold indicator incidences
    by_cases hy : Outside u v y
    · by_cases ha : G.RootNeighbor u v y
      · simp only [if_pos ha, if_pos hy]
        rcases ha.2 with a | a <;> omega
      · simp only [if_neg ha, if_pos hy, Nat.zero_le]
    · simp only [if_neg (show ¬ G.RootNeighbor u v y from fun h => hy h.1),
        if_neg hy, Nat.zero_add, Nat.le_refl]) hsum x (G.host.complete x)
  have hunit : G.host.multiplicity u x + G.host.multiplicity v x ≤ 1 := by
    simp only [incidences, indicator, if_pos hx] at hterm
    by_cases hy : G.RootNeighbor u v x
    · rw [if_pos hy] at hterm
      omega
    · rw [if_neg hy] at hterm
      omega
  have same_marks (w : V) (h : G.outsideSum u v (G.marked w) =
      G.outsideSum u v (G.host.multiplicity w)) : G.marked w x = G.host.multiplicity w x := by
    have ht := term_eq_of_sum_eq G.host.vertices
      (fun y => if Outside u v y then G.marked w y else 0)
      (fun y => if Outside u v y then G.host.multiplicity w y else 0)
      (by
        intro y _
        by_cases hy : Outside u v y
        · simpa only [if_pos hy] using G.marked_le w y
        · simp only [if_neg hy, Nat.le_refl])
      h x (G.host.complete x)
    simpa only [if_pos hx] using ht
  exact ⟨hunit, same_marks u (hru.trans hmu.symm), same_marks v (hrv.trans hmv.symm)⟩

/-- Number of possible images of position 2 in Theorem 3.8.
It includes the repeated image of position 0. -/
theorem degreeFour_third_images (G : MarkedGraph V) (hs : G.Strong)
    (hdeg : ∀ x, G.host.degree x ≤ 4) (hm : 36 ≤ G.orientedMarked)
    (u v : V) (hk : 0 < G.extra u v) :
    nsum G.host.vertices
      (fun x => if G.color v x = .red ∧ G.color u x = .absent then 1 else 0) = 3 := by
  have hk' : 2 ≤ G.marked u v := by
    unfold extra at hk
    omega
  have S := G.degreeFour_parallel_structure hs hdeg hm u v hk'
  let count := fun x => if G.color v x = .red ∧ G.color u x = .absent then 1 else 0
  change nsum G.host.vertices count = 3
  rw [G.outsideSum_split u v S.distinct]
  have hred : G.color v u = .red := by
    rw [G.color_eq_red, G.marked_symm v u, S.common]
    decide
  have h₁ : count u = 1 := if_pos ⟨hred, G.color_refl u⟩
  have h₂ : count v = 0 := if_neg (fun h => by
    have h' := h.1
    rw [G.color_refl] at h'
    contradiction)
  have h₃ : G.outsideSum u v count = G.outsideSum u v (G.marked v) := by
    apply G.outsideSum_congr
    intro x hx
    obtain ⟨hcap, _, hmark⟩ := S.outside x hx
    by_cases hd : 0 < G.marked v x
    · have hm1 : G.marked v x = 1 := by omega
      have hz : G.host.multiplicity u x = 0 := by omega
      have ha : G.color u x = .absent := Classical.not_not.mp
        (fun hk => Nat.ne_of_gt ((G.color_ne_absent u x).mp hk) hz)
      simp [count, ha, hm1]
    · have hz : G.marked v x = 0 := by omega
      simp [count, hz]
  rw [h₁, h₂, h₃, S.right_marked]

end FGST.Chapter3.MarkedGraph
