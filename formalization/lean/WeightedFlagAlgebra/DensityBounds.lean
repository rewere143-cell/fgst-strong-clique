import WeightedFlagAlgebra.DensityArithmetic

namespace FGST.Chapter3

private def appendMap (f : Fin k → V) (v : V) : Fin (k + 1) → V :=
  Fin.lastCases v f

@[simp] private theorem appendMap_old (f : Fin k → V) (v : V) (i : Fin k) :
    appendMap f v i.castSucc = f i := Fin.lastCases_castSucc i

@[simp] private theorem appendMap_last (f : Fin k → V) (v : V) :
    appendMap f v (Fin.last k) = v := Fin.lastCases_last

private theorem perm_nat_sum {xs ys : List Nat} (h : xs.Perm ys) : xs.sum = ys.sum := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap _ _ _ => simp [Nat.add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem sum_enum_last (vertices : List V) (hd : vertices.Nodup)
    (hc : ∀ v, v ∈ vertices) (k : Nat) (f : (Fin (k + 1) → V) → Nat) :
    nsum (enumMaps vertices (k + 1)) f =
      nsum (enumMaps vertices k) (fun g => nsum vertices (fun v => f (appendMap g v))) := by
  let keys := (enumMaps vertices k).flatMap (fun g => vertices.map (appendMap g))
  have hk : keys.Nodup := by
    change ((enumMaps vertices k).flatMap (fun g => vertices.map (appendMap g))).Pairwise
      (fun a b => a ≠ b)
    rw [List.pairwise_flatMap]
    constructor
    · intro g _
      exact List.pairwise_map.mpr (hd.imp (fun hne heq => hne (by
        simpa using congrFun heq (Fin.last k))))
    · exact (enumMaps_nodup vertices hd k).imp (by
        intro a b hab f hf g hg heq
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp hf
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hg
        exact hab (funext fun i => by simpa using congrFun heq i.castSucc))
  have hkc (g : Fin (k + 1) → V) : g ∈ keys := by
    apply List.mem_flatMap.mpr
    refine ⟨fun i => g i.castSucc, enumMaps_complete vertices hc k _, ?_⟩
    refine List.mem_map.mpr ⟨g (Fin.last k), hc _, ?_⟩
    funext i
    cases i using Fin.lastCases <;> simp
  have hp : (enumMaps vertices (k + 1)).Perm keys :=
    (List.perm_ext_iff_of_nodup (enumMaps_nodup vertices hd (k + 1)) hk).mpr
      (fun g => ⟨fun _ => hkc g, fun _ => enumMaps_complete vertices hc (k + 1) g⟩)
  have hs : nsum (enumMaps vertices (k + 1)) f = nsum keys f := perm_nat_sum (hp.map f)
  rw [hs]
  simp only [keys, nsum_flatMap, nsum_map]

/-- A rooted tree traversal with the two root positions first. A specified step
uses an extra edge instance, and an ordinary step uses only support adjacency. -/
inductive GrowthPlan : Nat → Type where
  | root (specified : Bool) : GrowthPlan 0
  | append {k} (previous : GrowthPlan k) (parent : Fin (k + 2)) (specified : Bool) :
      GrowthPlan (k + 1)

def GrowthPlan.rootSpecified : GrowthPlan k → Bool
  | .root s => s
  | .append p _ _ => p.rootSpecified

def GrowthPlan.specifiedPairs : GrowthPlan k → List (Fin (k + 2) × Fin (k + 2))
  | .root s => if s then [(0, 1)] else []
  | .append p i s =>
      (p.specifiedPairs.map (fun e => (e.1.castSucc, e.2.castSucc))) ++
        if s then [(i.castSucc, Fin.last _)] else []

def GrowthPlan.follows : GrowthPlan k → Pattern (k + 2) → Prop
  | .root _, F => F 0 1 = .red
  | .append p i _, F =>
      p.follows (fun a b => F a.castSucc b.castSucc) ∧
        F i.castSucc (Fin.last _) ≠ .absent

private def stepWeight (G : MarkedGraph V) (s : Bool) (x y : V) : Nat :=
  if s then G.extra x y else if G.Adj x y then 1 else 0

private def GrowthPlan.traversalWeight (G : MarkedGraph V) :
    (p : GrowthPlan k) → (Fin (k + 2) → V) → Nat
  | .root s, f => if s then G.extra (f 0) (f 1) else G.base (f 0) (f 1)
  | .append p i s, f =>
      p.traversalWeight G (fun j => f j.castSucc) *
        stepWeight G s (f i.castSucc) (f (Fin.last _))

private def rootTotal (G : MarkedGraph V) (s : Bool) : Nat :=
  if s then G.orientedExtra else G.orientedBase

private theorem branch_weight_at_most_degree (G : MarkedGraph V) (s : Bool) (x : V) :
    nsum G.host.vertices (stepWeight G s x) ≤ G.host.degree x := by
  apply nsum_le
  intro y _
  cases s with
  | false =>
    by_cases h : G.Adj x y
    · simp only [stepWeight, Bool.false_eq_true, if_false, if_pos h]
      exact h
    · simp [stepWeight, h]
  | true =>
    have hm := G.marked_le x y
    simp only [stepWeight, if_true, MarkedGraph.extra]
    omega

private theorem traversal_weight_on_pattern (G : MarkedGraph V) (p : GrowthPlan k)
    (f : Fin (k + 2) → V) (h : p.follows (inducedPattern G f)) :
    p.traversalWeight G f = specifiedWeight G p.specifiedPairs f := by
  induction p with
  | root s =>
    have hred : 0 < G.marked (f 0) (f 1) := (G.color_eq_red _ _).mp h
    cases s <;> simp [GrowthPlan.traversalWeight, GrowthPlan.specifiedPairs, specifiedWeight,
      MarkedGraph.base, hred]
  | @append k p i s ih =>
    have h₁ : p.follows (inducedPattern G (fun j => f j.castSucc)) := h.1
    have ha : G.Adj (f i.castSucc) (f (Fin.last _)) :=
      (G.color_ne_absent _ _).mp h.2
    rw [GrowthPlan.traversalWeight, ih _ h₁]
    cases s <;> simp [stepWeight, ha, GrowthPlan.specifiedPairs, specifiedWeight,
      List.prod_append, List.map_map, Function.comp_def]

private theorem traversal_sum_bound (G : MarkedGraph V) (D : Nat)
    (hd : ∀ x, G.host.degree x ≤ D) (p : GrowthPlan k) :
    nsum (enumMaps G.host.vertices (k + 2)) (p.traversalWeight G) ≤
      D ^ k * rootTotal G p.rootSpecified := by
  induction p with
  | root s =>
    cases s <;> simp only [enumMaps, nsum_flatMap, nsum_map, nsum_cons, nsum_nil, Nat.add_zero,
      GrowthPlan.traversalWeight, GrowthPlan.rootSpecified, rootTotal, Nat.pow_zero, Nat.one_mul,
      Bool.false_eq_true, if_false, if_true]
    · exact Nat.le_refl G.orientedBase
    · exact Nat.le_refl G.orientedExtra
  | @append k p i s ih =>
    rw [sum_enum_last G.host.vertices G.host.nodup G.host.complete]
    have h : nsum (enumMaps G.host.vertices (k + 2)) (fun g =>
          nsum G.host.vertices (fun v => (GrowthPlan.append p i s).traversalWeight G
            (appendMap g v))) ≤
        nsum (enumMaps G.host.vertices (k + 2)) (fun g => D * p.traversalWeight G g) := by
      apply nsum_le
      intro g _
      simp only [GrowthPlan.traversalWeight, appendMap_old, appendMap_last]
      rw [nsum_mul, Nat.mul_comm D]
      exact Nat.mul_le_mul_left _ (Nat.le_trans
        (branch_weight_at_most_degree G s (g i)) (hd (g i)))
    refine Nat.le_trans h ?_
    rw [nsum_mul, GrowthPlan.rootSpecified, Nat.pow_succ]
    calc
      D * nsum (enumMaps G.host.vertices (k + 2)) (p.traversalWeight G)
           ≤ D * (D ^ k * rootTotal G p.rootSpecified) := Nat.mul_le_mul_left _ ih
      _ = _ := by ac_rfl

/-- Quantitative rooted-traversal form of Lemma 3.3 before density normalization. -/
theorem weighted_count_le_root_traversal (G : MarkedGraph V) (D : Nat)
    (hd : ∀ x, G.host.degree x ≤ D) (p : GrowthPlan k) (F : Pattern (k + 2))
    (hF : p.follows F) :
    weightedCount G F p.specifiedPairs ≤ D ^ k * rootTotal G p.rootSpecified := by
  refine Nat.le_trans ?_ (traversal_sum_bound G D hd p)
  unfold weightedCount
  apply nsum_le
  intro f _
  split
  · rename_i hf
    rw [hf] at hF
    exact Nat.le_of_eq (traversal_weight_on_pattern G p f hF).symm
  · exact Nat.zero_le _

local instance : Std.Associative (fun a b : Rat => a * b) := ⟨Rat.mul_assoc⟩
local instance : Std.Commutative (fun a b : Rat => a * b) := ⟨Rat.mul_comm⟩

private theorem cast_inverse_nonneg (a : Nat) : 0 ≤ (a : Rat)⁻¹ := by
  by_cases hz : a = 0
  · subst a
    change 0 ≤ (0 : Rat)⁻¹
    rw [Rat.inv_zero]
    exact Rat.le_refl
  · exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.natCast_pos.mpr (Nat.pos_of_ne_zero hz)))

/-- Nonnegativity assertion of Lemma 3.3 holds for every pattern. -/
theorem weighted_density_nonneg (G : MarkedGraph V) (D : Nat) (F : Pattern n)
    (J : List (Fin n × Fin n)) : 0 ≤ weightedDensity G D F J := by
  simp only [weightedDensity, Rat.div_def]
  exact Rat.mul_nonneg Rat.natCast_nonneg (cast_inverse_nonneg _)

private theorem normalize_mono (a D n : Nat) {x y : Nat}
    (hxy : x ≤ y) : normalizeCount a D n x ≤ normalizeCount a D n y := by
  simp only [normalizeCount, Rat.div_def]
  exact Rat.mul_le_mul_of_nonneg_right
    (Rat.natCast_le_natCast.mpr (Nat.mul_le_mul_left _ hxy)) (cast_inverse_nonneg _)

private theorem normalize_pow (a D b k : Nat) (hD : 0 < D) :
    normalizeCount a D (k + 2) (D ^ k * b) = (b : Rat) / (a : Rat) := by
  induction k with
  | zero =>
    simp only [Nat.pow_zero, Nat.one_mul, Nat.zero_add, normalizeCount, Rat.natCast_mul, Rat.div_def,
      Rat.inv_mul_rev]
    let x : Rat := (D ^ 2 : Nat)
    change x * (b : Rat) * (x⁻¹ * (a : Rat)⁻¹) = (b : Rat) * (a : Rat)⁻¹
    have hx : x ≠ 0 := Rat.ne_of_gt (Rat.natCast_pos.mpr (Nat.pow_pos hD))
    calc
      _ = ((b : Rat) * (a : Rat)⁻¹) * (x * x⁻¹) := by ac_rfl
      _ = _ := by rw [Rat.mul_inv_cancel x hx, Rat.mul_one]
  | succ k ih =>
    have he : D ^ (k + 1) * b = D * (D ^ k * b) := by
      rw [Nat.pow_succ]
      ac_rfl
    rw [he]
    exact (normalizeCount_step a D (k + 2) (D ^ k * b) hD).trans ih

/-- Lemma 3.3 in the labeling of a rooted growth plan. The two cases of its
right side are 1-e for a base root and e for a specified root. -/
theorem weighted_density_le_root_traversal (G : MarkedGraph V) (D : Nat)
    (hD : 0 < D) (hm : 0 < G.orientedMarked)
    (hd : ∀ x, G.host.degree x ≤ D) (p : GrowthPlan k) (F : Pattern (k + 2))
    (hF : p.follows F) :
    weightedDensity G D F p.specifiedPairs ≤
      if p.rootSpecified then (G.orientedExtra : Rat) / (G.orientedMarked : Rat)
      else 1 - (G.orientedExtra : Rat) / (G.orientedMarked : Rat) := by
  change normalizeCount G.orientedMarked D (k + 2) (weightedCount G F p.specifiedPairs) ≤ _
  refine Rat.le_trans (normalize_mono _ _ _ (weighted_count_le_root_traversal G D hd p F hF)) ?_
  rw [normalize_pow _ _ _ _ hD]
  cases hs : p.rootSpecified with
  | true => simp [rootTotal]
  | false =>
    simp only [rootTotal, Bool.false_eq_true, if_false]
    let a : Rat := G.orientedMarked
    let b : Rat := G.orientedBase
    let e : Rat := G.orientedExtra
    change b / a ≤ 1 - e / a
    suffices he : b / a = 1 - e / a by
      rw [he]
      exact Rat.le_refl
    have hp : b + e = a := by
      change (G.orientedBase : Rat) + (G.orientedExtra : Rat) = (G.orientedMarked : Rat)
      rw [← Rat.natCast_add, G.oriented_marked_partition]
    have ha : a ≠ 0 := Rat.ne_of_gt (Rat.natCast_pos.mpr hm)
    have hsum : b / a + e / a = 1 := by
      simp only [Rat.div_def]
      rw [← Rat.add_mul, hp, Rat.mul_inv_cancel a ha]
    calc
      _ = (b / a + e / a) - e / a := Rat.add_sub_cancel.symm
      _ = _ := by rw [hsum]

#print axioms weighted_density_nonneg
#print axioms weighted_density_le_root_traversal

end FGST.Chapter3
