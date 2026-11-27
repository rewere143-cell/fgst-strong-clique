import Std

/-!
Pilot checks for §3 of FGST-Conjecture_none.pdf.
These lemmas cover the positions and adjacency layer and selected counting reductions.
-/

namespace FGST.Chapter3

inductive Color where
  | absent
  | blue
  | red
  deriving DecidableEq

/-- The red/blue support of a loopless graph. -/
structure Support (V : Type) where
  color : V → V → Color
  symmetric : ∀ u v, color u v = color v u
  loopless : ∀ v, color v v = .absent

def Support.Adj (G : Support V) (u v : V) : Prop :=
  G.color u v ≠ .absent

/-- Strong clique property for red pairs with disjoint endpoint sets. -/
def Support.RedStrong (G : Support V) : Prop :=
  ∀ a b c d, G.color a b = .red → G.color c d = .red →
    a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    G.Adj a c ∨ G.Adj a d ∨ G.Adj b c ∨ G.Adj b d

private theorem adj_of_red (G : Support V) (h : G.color u v = .red) :
    G.Adj u v := by
  simp [Support.Adj, h]

/-- Equation (3.2): the two red pairs may share images under a pattern map. -/
theorem red_pairs_have_cross_adjacency (G : Support V) (strong : G.RedStrong)
    (a b c d : V) (first : G.color a b = .red) (second : G.color c d = .red) :
    G.Adj a c ∨ G.Adj a d ∨ G.Adj b c ∨ G.Adj b d := by
  classical
  by_cases hac : a = c
  · exact .inr (.inl (hac.symm ▸ adj_of_red G second))
  by_cases had : a = d
  · exact .inl (had.symm ▸ adj_of_red G ((G.symmetric d c).trans second))
  by_cases hbc : b = c
  · exact .inr (.inr (.inr (hbc.symm ▸ adj_of_red G second)))
  by_cases hbd : b = d
  · exact .inr (.inr (.inl (hbd.symm ▸ adj_of_red G ((G.symmetric d c).trans second))))
  exact strong a b c d first second hac had hbc hbd

/-- Pull back the colored support along an arbitrary map of positions. -/
def pullback (G : Support V) (image : P → V) : Support P where
  color u v := G.color (image u) (image v)
  symmetric u v := G.symmetric (image u) (image v)
  loopless v := G.loopless (image v)

theorem red_strong_pullback (G : Support V) (strong : G.RedStrong) (image : P → V) :
    (pullback G image).RedStrong := by
  intro a b c d first second _ _ _ _
  exact red_pairs_have_cross_adjacency G strong (image a) (image b)
    (image c) (image d) first second

section Gluing

variable {R A B V : Type}

def restrictLeft (g : R ⊕ (A ⊕ B) → V) : R ⊕ A → V
  | .inl r => g (.inl r)
  | .inr a => g (.inr (.inl a))

def restrictRight (g : R ⊕ (A ⊕ B) → V) : R ⊕ B → V
  | .inl r => g (.inl r)
  | .inr b => g (.inr (.inr b))

def glue (left : R ⊕ A → V) (right : R ⊕ B → V) : R ⊕ (A ⊕ B) → V
  | .inl r => left (.inl r)
  | .inr (.inl a) => left (.inr a)
  | .inr (.inr b) => right (.inr b)

/-- The map-bijection step in Theorem 3.4, before imposing colors and summing weights. -/
theorem glue_existsUnique (left : R ⊕ A → V) (right : R ⊕ B → V)
    (agree : ∀ r, left (.inl r) = right (.inl r)) :
    ∃ g, (restrictLeft g = left ∧ restrictRight g = right) ∧
      ∀ g', (restrictLeft g' = left ∧ restrictRight g' = right) → g' = g := by
  refine ⟨glue left right, ⟨?_, ?_⟩, ?_⟩
  · funext x
    cases x <;> rfl
  · funext x
    cases x with
    | inl r => exact agree r
    | inr b => rfl
  · intro g' hg'
    funext x
    cases x with
    | inl r => exact congrFun hg'.1 (.inl r)
    | inr x =>
      cases x with
      | inl a => exact congrFun hg'.1 (.inr a)
      | inr b => exact congrFun hg'.2 (.inr b)

end Gluing

/-- Integer-exponent identity in the proof of (3.10). -/
theorem gluing_exponents (k ni nj : Int) :
    (k - 2) + (ni - k) + (nj - k) = (ni + nj - k) - 2 := by
  omega

private theorem rational_square_nonneg (z : Rat) : 0 ≤ z * z := by
  rcases Rat.le_total (a := 0) (b := z) with hz | hz
  · exact Rat.mul_nonneg hz hz
  · have hneg : 0 ≤ -z := by
      simpa only [Rat.neg_zero] using Rat.neg_le_neg hz
    simpa only [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] using Rat.mul_nonneg hneg hneg

private theorem rat_sum_map_mul_left (xs : List A) (c : Rat) (f : A → Rat) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih, Rat.mul_add]

private theorem rat_sum_map_mul_right (xs : List A) (c : Rat) (f : A → Rat) :
    (xs.map (fun x => f x * c)).sum = (xs.map f).sum * c := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih, Rat.add_mul]

/-- A single root's rank-one quadratic form expands to the square of a dot product. -/
theorem rank_one_quadratic_form (coords : List I) (z : I → Rat) :
    (coords.map (fun i => (coords.map (fun j => z i * z j)).sum)).sum =
      (coords.map z).sum * (coords.map z).sum := by
  simp only [rat_sum_map_mul_left, rat_sum_map_mul_right]

/-- Nonnegativity of the rational weighted square sum on the right of (3.8b). -/
theorem weighted_square_sum_nonnegative (roots : List A) (scale : Rat) (hscale : 0 ≤ scale)
    (weight dotProduct : A → Rat) (hw : ∀ r, 0 ≤ weight r) :
    0 ≤ scale * (roots.map (fun r => weight r * (dotProduct r * dotProduct r))).sum := by
  apply Rat.mul_nonneg hscale
  induction roots with
  | nil => exact Rat.le_refl
  | cons r roots ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Rat.add_nonneg (Rat.mul_nonneg (hw r) (rational_square_nonneg (dotProduct r))) ih

/-- Count saturation in Theorem 3.7, given the graph-theoretic incidence bounds. -/
theorem degreeFour_saturation
    (m k q rootMarked outsideMarked : Nat) (hm : 18 ≤ m) (hk : 2 ≤ k)
    (hq : q + 2 * k ≤ 8) (hroot : rootMarked + k ≤ 8)
    (houtside : outsideMarked ≤ 3 * q) (hpartition : m = rootMarked + outsideMarked) :
    m = 18 ∧ k = 2 ∧ q = 4 ∧ rootMarked = 6 ∧ outsideMarked = 12 := by
  omega

/-- The final coefficient comparison of Theorem 3.6 after clearing denominators. -/
theorem pair_count_coefficients (allOrders adjacentOrders sharedIncidences b : Nat)
    (hall : allOrders = 4 * b)
    (hgood : 2 * b + sharedIncidences ≤ 2 * adjacentOrders) :
    allOrders + 2 * sharedIncidences ≤ 4 * adjacentOrders := by
  omega

#print axioms red_strong_pullback
#print axioms glue_existsUnique
#print axioms gluing_exponents
#print axioms rank_one_quadratic_form
#print axioms weighted_square_sum_nonnegative
#print axioms degreeFour_saturation
#print axioms pair_count_coefficients

end FGST.Chapter3

