/-
The finite weighted flag construction from §3.2.
Position sets are reindexed as a common root and two disjoint groups of new
positions. Host vertices are never required to be distinct across positions.
-/
import Lean

namespace FGST.FlagGluing

noncomputable section
open Classical

section Scalar
open Lean.Grind
variable {R : Type} [CommRing R]

private theorem sumMapMulLeft {A : Type} (xs : List A) (c : R)
    (f : A -> R) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp [Semiring.mul_zero]
  | cons a xs ih => simp [ih, Semiring.left_distrib]

private theorem sumMapMulRight {A : Type} (xs : List A) (c : R)
    (f : A -> R) :
    (xs.map (fun x => f x * c)).sum = (xs.map f).sum * c := by
  induction xs with
  | nil => simp [Semiring.zero_mul]
  | cons a xs ih => simp [ih, Semiring.right_distrib]

theorem rankOneQuadraticForm {A : Type} (coords : List A) (z : A -> R) :
    (coords.map (fun i => (coords.map (fun j => z i * z j)).sum)).sum =
      (coords.map z).sum * (coords.map z).sum := by
  simp only [sumMapMulLeft, sumMapMulRight]


private theorem sumMapAdd {A : Type} (xs : List A) (f g : A -> R) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp [AddCommMonoid.zero_add]
  | cons a xs ih =>
    simp [ih, Semiring.add_assoc, AddCommMonoid.add_left_comm]

def doubleSum {I : Type} (is : List I) (f : I -> I -> R) : R :=
  (is.map (fun i => (is.map (fun j => f i j)).sum)).sum

private theorem doubleSumAdd {I : Type} (is : List I) (f g : I -> I -> R) :
    doubleSum is (fun i j => f i j + g i j) = doubleSum is f + doubleSum is g := by
  unfold doubleSum
  simp only [sumMapAdd]

private theorem doubleSumMulLeft {I : Type} (is : List I) (c : R) (f : I -> I -> R) :
    doubleSum is (fun i j => c * f i j) = c * doubleSum is f := by
  unfold doubleSum
  simp only [sumMapMulLeft]

private theorem doubleSumZero {I : Type} (is : List I) :
    doubleSum is (fun _ _ => (0 : R)) = 0 := by
  simpa only [Semiring.zero_mul] using doubleSumMulLeft is (0 : R) (fun _ _ => 0)

theorem gramExpansion {A I : Type} (roots : List A) (is : List I) (w : A -> R)
    (z : A -> I -> R) :
    doubleSum is (fun i j => (roots.map (fun a => w a * (z a i * z a j))).sum) =
      (roots.map (fun a => w a * ((is.map (z a)).sum * (is.map (z a)).sum))).sum := by
  induction roots with
  | nil => simpa using doubleSumZero is
  | cons a roots ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [doubleSumAdd, doubleSumMulLeft, ih]
    unfold doubleSum
    rw [rankOneQuadraticForm]

def gramMatrix {A I : Type} (roots : List A) (scale : R)
    (w : A -> R) (v : A -> I -> R) (i j : I) : R :=
  scale * (roots.map (fun a => w a * (v a i * v a j))).sum

theorem gramMatrix_expansion {A I : Type} (roots : List A) (is : List I)
    (scale : R) (w : A -> R) (v : A -> I -> R) (x : I -> R) :
    doubleSum is (fun i j => x i * gramMatrix roots scale w v i j * x j) =
      scale * (roots.map (fun a => w a *
        ((is.map (fun i => x i * v a i)).sum * (is.map (fun i => x i * v a i)).sum))).sum := by
  have hentry (i j : I) :
      x i * gramMatrix roots scale w v i j * x j =
        scale * (roots.map (fun a => w a * ((x i * v a i) * (x j * v a j)))).sum := by
    unfold gramMatrix
    have hf (a : A) : ((x i * (scale * (w a * (v a i * v a j)))) * x j) =
        scale * (w a * ((x i * v a i) * (x j * v a j))) := by
      simp [CommSemiring.mul_left_comm, CommSemiring.mul_comm]
    rw [<- sumMapMulLeft, <- sumMapMulLeft, <- sumMapMulRight,
      <- sumMapMulLeft]
    simp only [hf]
  simp only [hentry, doubleSumMulLeft, gramExpansion]

section Ordered
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

private theorem scalarSquareNonneg (z : R) : 0 <= z * z := by
  have hz : z ^ (2 : Nat) = z * z := by
    change z ^ (1 + 1) = z * z
    rw [Semiring.pow_succ]
    change z ^ (0 + 1) * z = z * z
    rw [Semiring.pow_succ, Semiring.pow_zero, Semiring.one_mul]
  rw [<- hz]
  exact OrderedRing.sq_nonneg

omit [Std.LawfulOrderLT R] in
private theorem scalarAddNonneg {a b : R} (ha : 0 <= a) (hb : 0 <= b) : 0 <= a + b := by
  have h := OrderedAdd.add_le_left ha b
  rw [AddCommMonoid.zero_add] at h
  exact Std.le_trans hb h

private theorem weightedGramQuadraticNonneg {A : Type} (roots : List A)
    (scale : R) (hscale : 0 <= scale) (w z : A -> R)
    (hw : forall a, 0 <= w a) :
    0 <= scale * (roots.map (fun a => w a * (z a * z a))).sum := by
  apply OrderedRing.mul_nonneg hscale
  induction roots with
  | nil => exact Std.le_refl _
  | cons a roots ih =>
    simp only [List.map_cons, List.sum_cons]
    exact scalarAddNonneg (OrderedRing.mul_nonneg (hw a) (scalarSquareNonneg (z a))) ih

theorem gramMatrix_nonneg {A I : Type} (roots : List A) (is : List I)
    (scale : R) (hscale : 0 <= scale) (w : A -> R) (v : A -> I -> R)
    (hw : forall a, 0 <= w a) (x : I -> R) :
    0 <= doubleSum is (fun i j => x i * gramMatrix roots scale w v i j * x j) := by
  rw [gramMatrix_expansion]
  exact weightedGramQuadraticNonneg roots scale hscale w
    (fun a => (is.map (fun i => x i * v a i)).sum) hw
end Ordered
end Scalar

abbrev Positions (K A B : Type) := K ⊕ (A ⊕ B)
abbrev MapPieces (K A B V : Type) := (K → V) × (A → V) × (B → V)

def leftPosition {K A B : Type} : K ⊕ A → Positions K A B :=
  Sum.elim Sum.inl (fun a => Sum.inr (Sum.inl a))

def rightPosition {K A B : Type} : K ⊕ B → Positions K A B :=
  Sum.elim Sum.inl (fun b => Sum.inr (Sum.inr b))

def glue {K A B V : Type} (pieces : MapPieces K A B V) : Positions K A B → V :=
  Sum.elim pieces.1 (Sum.elim pieces.2.1 pieces.2.2)

def splitMap {K A B V : Type} (g : Positions K A B → V) : MapPieces K A B V :=
  (fun k => g (Sum.inl k), fun a => g (Sum.inr (Sum.inl a)),
    fun b => g (Sum.inr (Sum.inr b)))

theorem glue_splitMap {K A B V : Type} (g : Positions K A B → V) :
    glue (splitMap g) = g := by
  funext p
  rcases p with k | a | b <;> rfl

theorem splitMap_glue {K A B V : Type} (p : MapPieces K A B V) :
    splitMap (glue p) = p := by
  rcases p with ⟨φ, l, r⟩
  rfl

theorem glue_restriction_unique {K A B V : Type} (g : Positions K A B → V)
    (p : MapPieces K A B V)
    (hl : ∀ i, g (leftPosition i) = Sum.elim p.1 p.2.1 i)
    (hr : ∀ j, g (rightPosition j) = Sum.elim p.1 p.2.2 j) :
    g = glue p := by
  funext i
  rcases i with k | a | b
  · exact hl (Sum.inl k)
  · exact hl (Sum.inr a)
  · exact hr (Sum.inr b)

def inducedColor {P V C : Type} (color : V → V → C) (f : P → V) :
    P → P → C :=
  fun i j => color (f i) (f j)

def Realizes {P V C : Type} (color : V → V → C) (pattern : P → P → C)
    (f : P → V) : Prop :=
  inducedColor color f = pattern

/-- The host assertion for pairs whose endpoint sets are disjoint. -/
def HostStrong {V : Type} (red present : V → V → Prop) : Prop :=
  ∀ u v x y, red u v → red x y →
    u ≠ x → u ≠ y → v ≠ x → v ≠ y →
    present u x ∨ present u y ∨ present v x ∨ present v y

/-- The color-pattern clause for four distinct positions. -/
def PatternStrong {P C : Type} (red present : C → Prop) (pattern : P → P → C) : Prop :=
  ∀ i j k l, red (pattern i j) → red (pattern k l) →
    i ≠ k → i ≠ l → j ≠ k → j ≠ l →
    present (pattern i k) ∨ present (pattern i l) ∨
      present (pattern j k) ∨ present (pattern j l)

/-- Pull back the strong-clique property, including the cases of coincident images. -/
theorem inducedColor_strong {P V C : Type} (color : V → V → C)
    (red present : C → Prop)
    (hred : ∀ c, red c → present c) (hsym : ∀ u v, color u v = color v u)
    (hstrong : HostStrong (fun u v => red (color u v)) (fun u v => present (color u v)))
    (f : P → V) :
    PatternStrong red present (inducedColor color f) := by
  intro i j k l hfirst hsecond _ _ _ _
  simp only [inducedColor] at hfirst hsecond ⊢
  by_cases hik : f i = f k
  · exact Or.inr (Or.inl (hik ▸ hred _ hsecond))
  by_cases hil : f i = f l
  · have h := hred _ hsecond
    rw [hsym (f k) (f l), ← hil] at h
    exact Or.inl h
  by_cases hjk : f j = f k
  · exact Or.inr (Or.inr (Or.inr (hjk ▸ hred _ hsecond)))
  by_cases hjl : f j = f l
  · have h := hred _ hsecond
    rw [hsym (f k) (f l), ← hjl] at h
    exact Or.inr (Or.inr (Or.inl h))
  exact hstrong (f i) (f j) (f k) (f l) hfirst hsecond hik hil hjk hjl

def crossColor {K A B V C : Type} (color : V → V → C) (p : MapPieces K A B V) :
    A → B → C :=
  fun a b => color (p.2.1 a) (p.2.2 b)

/-- The rooted flag restrictions and the left-right colors determine the entire pattern. -/
def gluedColor {K A B C : Type} (left : K ⊕ A → K ⊕ A → C)
    (right : K ⊕ B → K ⊕ B → C) (cross : A → B → C) :
    Positions K A B → Positions K A B → C
  | .inl k, .inl l => left (.inl k) (.inl l)
  | .inl k, .inr (.inl a) => left (.inl k) (.inr a)
  | .inr (.inl a), .inl k => left (.inr a) (.inl k)
  | .inr (.inl a), .inr (.inl a') => left (.inr a) (.inr a')
  | .inl k, .inr (.inr b) => right (.inl k) (.inr b)
  | .inr (.inr b), .inl k => right (.inr b) (.inl k)
  | .inr (.inr b), .inr (.inr b') => right (.inr b) (.inr b')
  | .inr (.inl a), .inr (.inr b) => cross a b
  | .inr (.inr b), .inr (.inl a) => cross a b

theorem realizes_gluedColor_iff {K A B V C : Type} (color : V → V → C)
    (hsym : ∀ u v, color u v = color v u)
    (left : K ⊕ A → K ⊕ A → C) (right : K ⊕ B → K ⊕ B → C)
    (agree : ∀ i j : K, left (.inl i) (.inl j) = right (.inl i) (.inl j))
    (cross : A → B → C) (p : MapPieces K A B V) :
    Realizes color (gluedColor left right cross) (glue p) ↔
      Realizes color left (Sum.elim p.1 p.2.1) ∧
      Realizes color right (Sum.elim p.1 p.2.2) ∧ crossColor color p = cross := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · funext i j
      have point := congrFun (congrFun h (leftPosition i)) (leftPosition j)
      cases i <;> cases j <;> exact point
    · funext i j
      have point := congrFun (congrFun h (rightPosition i)) (rightPosition j)
      rcases i with k | b <;> rcases j with l | b'
      · exact (congrFun (congrFun h (Sum.inl k)) (Sum.inl l)).trans (agree k l)
      all_goals exact point
    · funext a b
      exact congrFun (congrFun h (Sum.inr (Sum.inl a))) (Sum.inr (Sum.inr b))
  · rintro ⟨hl, hr, hc⟩
    funext i j
    rcases i with k | a | b <;> rcases j with l | a' | b'
    · exact congrFun (congrFun hl (Sum.inl k)) (Sum.inl l)
    · exact congrFun (congrFun hl (Sum.inl k)) (Sum.inr a')
    · exact congrFun (congrFun hr (Sum.inl k)) (Sum.inr b')
    · exact congrFun (congrFun hl (Sum.inr a)) (Sum.inl l)
    · exact congrFun (congrFun hl (Sum.inr a)) (Sum.inr a')
    · exact congrFun (congrFun hc a) b'
    · exact congrFun (congrFun hr (Sum.inr b)) (Sum.inl l)
    · exact (hsym _ _).trans (congrFun (congrFun hc a') b)
    · exact congrFun (congrFun hr (Sum.inr b)) (Sum.inr b')

/-- Ordered representatives of unordered specified pairs; products allow repeated host images. -/
def pairProduct {P V : Type} (extra : V → V → Rat) (f : P → V)
    (pairs : List (P × P)) : Rat :=
  (pairs.map (fun p => extra (f p.1) (f p.2))).prod

private theorem pairProduct_map {P Q V : Type} (extra : V → V → Rat)
    (f : Q → V) (p : P → Q) (pairs : List (P × P)) :
    pairProduct extra f (pairs.map (fun e => (p e.1, p e.2))) =
      pairProduct extra (fun i => f (p i)) pairs := by
  simp only [pairProduct, List.map_map]
  rfl

private theorem pairProduct_append {P V : Type} (extra : V → V → Rat) (f : P → V)
    (p q : List (P × P)) :
    pairProduct extra f (p ++ q) = pairProduct extra f p * pairProduct extra f q := by
  induction p with
  | nil => simp [pairProduct]
  | cons e p ih =>
    simp [pairProduct, Rat.mul_assoc] at ih ⊢
    rw [ih]

def gluedPairs {K A B : Type} (root : List (K × K))
    (left : List ((K ⊕ A) × (K ⊕ A))) (right : List ((K ⊕ B) × (K ⊕ B))) :
    List (Positions K A B × Positions K A B) :=
  root.map (fun p => (Sum.inl p.1, Sum.inl p.2)) ++
  (left.map (fun p => (leftPosition p.1, leftPosition p.2)) ++
    right.map (fun p => (rightPosition p.1, rightPosition p.2)))

theorem gluedPairs_product {K A B V : Type} (extra : V → V → Rat)
    (root : List (K × K)) (left : List ((K ⊕ A) × (K ⊕ A)))
    (right : List ((K ⊕ B) × (K ⊕ B))) (p : MapPieces K A B V) :
    pairProduct extra (glue p) (gluedPairs root left right) =
      pairProduct extra p.1 root *
        (pairProduct extra (Sum.elim p.1 p.2.1) left *
         pairProduct extra (Sum.elim p.1 p.2.2) right) := by
  unfold gluedPairs
  rw [pairProduct_append, pairProduct_append, pairProduct_map, pairProduct_map,
    pairProduct_map]
  have hl : (fun v => glue p (leftPosition v)) = Sum.elim p.1 p.2.1 := by
    funext v
    cases v <;> rfl
  have hr : (fun v => glue p (rightPosition v)) = Sum.elim p.1 p.2.2 := by
    funext v
    cases v <;> rfl
  rw [hl, hr]
  rfl

/-- A list that enumerates every member of a finite type exactly once. -/
structure Enumeration (X : Type) where
  values : List X
  nodup : values.Nodup
  complete : ∀ x, x ∈ values

private theorem ratSumMapZero {X : Type} (xs : List X) :
    (xs.map (fun _ => (0 : Rat))).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih, Rat.zero_add]

private theorem ratSumMapAppend {X : Type} (xs ys : List X) (f : X → Rat) :
    ((xs ++ ys).map f).sum = (xs.map f).sum + (ys.map f).sum := by
  induction xs with
  | nil => simp [Rat.zero_add]
  | cons a xs ih => simp [Rat.add_assoc]

private theorem ratSumMapFlatMap {X Y : Type} (xs : List X) (f : X → List Y)
    (g : Y → Rat) :
    ((xs.flatMap f).map g).sum = (xs.map (fun x => ((f x).map g).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih]

private theorem sumByKey_single {C : Type} (keys : List C)
    (hkeys : keys.Nodup) (c : C) (hc : c ∈ keys) (a : Rat) :
    (keys.map (fun k => if c = k then a else 0)).sum = a := by
  induction keys with
  | nil => simp at hc
  | cons k keys ih =>
    have hnodup := List.nodup_cons.mp hkeys
    rcases List.mem_cons.mp hc with rfl | htail
    · have ht (k : C) (hk : k ∈ keys) : (if c = k then a else 0) = 0 := by
        apply if_neg
        intro h
        exact hnodup.1 (h.symm ▸ hk)
      have hd : keys.map (fun k => if c = k then a else 0) = keys.map (fun _ => 0) :=
        List.map_congr_left ht
      simp [hd, ratSumMapZero, Rat.add_zero]
    · have hne : c ≠ k := fun h => hnodup.1 (h ▸ htail)
      simp [hne, ih hnodup.2 htail, Rat.zero_add]

/-- Partition a finite sum by any complete enumeration of its color key. -/
theorem sumByKey {X C : Type} (xs : List X) (keys : Enumeration C)
    (classify : X → C) (w : X → Rat) :
    (keys.values.map (fun k =>
      (xs.map (fun x => if classify x = k then w x else 0)).sum)).sum =
      (xs.map w).sum := by
  induction xs with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact ratSumMapZero keys.values
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [sumMapAdd, sumByKey_single keys.values keys.nodup _ (keys.complete _) _, ih]

def allPieces {K A B V : Type} (roots : List (K → V)) (left : List (A → V))
    (right : List (B → V)) : List (MapPieces K A B V) :=
  roots.flatMap (fun root => left.flatMap (fun l => right.map (fun r => (root, l, r))))

theorem allPieces_mem_iff {K A B V : Type} (roots : List (K → V)) (left : List (A → V))
    (right : List (B → V)) (p : MapPieces K A B V) :
    p ∈ allPieces roots left right ↔ p.1 ∈ roots ∧ p.2.1 ∈ left ∧ p.2.2 ∈ right := by
  rcases p with ⟨root, l, r⟩
  simp only [allPieces, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨root', hmroot, l', hml, r', hmr, rfl, rfl, rfl⟩
    exact ⟨hmroot, hml, hmr⟩
  · rintro ⟨hmroot, hml, hmr⟩
    exact ⟨root, hmroot, l, hml, r, hmr, rfl, rfl, rfl⟩

theorem allGluedMaps_complete {K A B V : Type} (roots : Enumeration (K → V))
    (left : Enumeration (A → V)) (right : Enumeration (B → V)) (g : Positions K A B → V) :
    g ∈ (allPieces roots.values left.values right.values).map glue := by
  apply List.mem_map.mpr
  exact ⟨splitMap g, (allPieces_mem_iff _ _ _ _).mpr
    ⟨roots.complete _, left.complete _, right.complete _⟩, glue_splitMap g⟩

def typeWeight {K V C : Type} (color : V → V → C) (extra : V → V → Rat)
    (typePattern : K → K → C) (rootPairs : List (K × K)) (root : K → V) : Rat :=
  if Realizes color typePattern root then pairProduct extra root rootPairs else 0

def extensionWeight {K A V C : Type} (color : V → V → C) (extra : V → V → Rat)
    (pattern : K ⊕ A → K ⊕ A → C) (newPairs : List ((K ⊕ A) × (K ⊕ A)))
    (root : K → V) (extension : A → V) : Rat :=
  if Realizes color pattern (Sum.elim root extension) then
    pairProduct extra (Sum.elim root extension) newPairs else 0

/-- A fixed cross-color pattern gives the raw count of its glued realizations. -/
def gluedRaw {K A B V C : Type} (color : V → V → C) (extra : V → V → Rat)
    (roots : List (K → V)) (lefts : List (A → V)) (rights : List (B → V))
    (left : K ⊕ A → K ⊕ A → C) (right : K ⊕ B → K ⊕ B → C) (cross : A → B → C)
    (rootPairs : List (K × K)) (leftPairs : List ((K ⊕ A) × (K ⊕ A)))
    (rightPairs : List ((K ⊕ B) × (K ⊕ B))) : Rat :=
  (((allPieces roots lefts rights).map glue).map (fun g =>
      if Realizes color (gluedColor left right cross) g then
        pairProduct extra g (gluedPairs rootPairs leftPairs rightPairs) else 0)).sum

private theorem flags_match_type {K A V C : Type} (color : V → V → C)
    (typePattern : K → K → C) (left : K ⊕ A → K ⊕ A → C)
    (hleft : ∀ i j, left (.inl i) (.inl j) = typePattern i j)
    (root : K → V) (l : A → V)
    (hl : Realizes color left (Sum.elim root l)) : Realizes color typePattern root := by
  funext i j
  exact (congrFun (congrFun hl (.inl i)) (.inl j)).trans (hleft i j)

theorem gluedRaw_eq_group {K A B V C : Type} (color : V → V → C) (extra : V → V → Rat)
    (hsym : ∀ u v, color u v = color v u)
    (roots : List (K → V)) (lefts : List (A → V)) (rights : List (B → V))
    (typePattern : K → K → C)
    (left : K ⊕ A → K ⊕ A → C) (right : K ⊕ B → K ⊕ B → C) (cross : A → B → C)
    (hleft : ∀ i j, left (.inl i) (.inl j) = typePattern i j)
    (hright : ∀ i j, right (.inl i) (.inl j) = typePattern i j)
    (rootPairs : List (K × K)) (leftPairs : List ((K ⊕ A) × (K ⊕ A)))
    (rightPairs : List ((K ⊕ B) × (K ⊕ B))) :
    gluedRaw color extra roots lefts rights left right cross rootPairs leftPairs rightPairs =
      ((allPieces roots lefts rights).map (fun p =>
        if crossColor color p = cross then
          typeWeight color extra typePattern rootPairs p.1 *
            (extensionWeight color extra left leftPairs p.1 p.2.1 *
             extensionWeight color extra right rightPairs p.1 p.2.2)
        else 0)).sum := by
  simp only [gluedRaw, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  have hagree (i j : K) : left (.inl i) (.inl j) = right (.inl i) (.inl j) :=
    (hleft i j).trans (hright i j).symm
  simp only [Function.comp_apply, realizes_gluedColor_iff color hsym left right hagree]
  by_cases hl : Realizes color left (Sum.elim p.1 p.2.1)
  · by_cases hr : Realizes color right (Sum.elim p.1 p.2.2)
    · have hroot := flags_match_type color typePattern left hleft p.1 p.2.1 hl
      simp [hl, hr, typeWeight, extensionWeight, hroot, gluedPairs_product]
    · simp [hl, hr, extensionWeight, Rat.mul_zero]
  · simp [hl, extensionWeight, Rat.zero_mul, Rat.mul_zero]

/-- Rearrange the product of the two extension sums as one sum over all pairs. -/
private theorem entry_unfold {K A B V C : Type} (color : V → V → C)
    (extra : V → V → Rat)
    (roots : List (K → V)) (lefts : List (A → V)) (rights : List (B → V))
    (typePattern : K → K → C)
    (left : K ⊕ A → K ⊕ A → C) (right : K ⊕ B → K ⊕ B → C)
    (rootPairs : List (K × K)) (leftPairs : List ((K ⊕ A) × (K ⊕ A)))
    (rightPairs : List ((K ⊕ B) × (K ⊕ B))) :
    (roots.map (fun root =>
      typeWeight color extra typePattern rootPairs root *
        ((lefts.map (extensionWeight color extra left leftPairs root)).sum *
         (rights.map (extensionWeight color extra right rightPairs root)).sum))).sum =
      ((allPieces roots lefts rights).map (fun p =>
        typeWeight color extra typePattern rootPairs p.1 *
          (extensionWeight color extra left leftPairs p.1 p.2.1 *
           extensionWeight color extra right rightPairs p.1 p.2.2))).sum := by
  simp only [allPieces, ratSumMapFlatMap, List.map_map]
  congr 1
  apply List.map_congr_left
  intro root _
  let w := typeWeight color extra typePattern rootPairs root
  let f := extensionWeight color extra left leftPairs root
  let g := extensionWeight color extra right rightPairs root
  change w * ((lefts.map f).sum * (rights.map g).sum) =
    (lefts.map (fun l => (rights.map (fun r => w * (f l * g r))).sum)).sum
  simp only [sumMapMulLeft, sumMapMulRight]

/-- Raw gluing identity of (3.12), before the common positive normalization. -/
theorem weightedGluing_raw {K A B V C : Type} (color : V → V → C)
    (extra : V → V → Rat) (hsym : ∀ u v, color u v = color v u)
    (roots : List (K → V)) (lefts : List (A → V)) (rights : List (B → V))
    (typePattern : K → K → C)
    (left : K ⊕ A → K ⊕ A → C) (right : K ⊕ B → K ⊕ B → C)
    (hleft : ∀ i j, left (.inl i) (.inl j) = typePattern i j)
    (hright : ∀ i j, right (.inl i) (.inl j) = typePattern i j)
    (rootPairs : List (K × K)) (leftPairs : List ((K ⊕ A) × (K ⊕ A)))
    (rightPairs : List ((K ⊕ B) × (K ⊕ B)))
    (crossColors : Enumeration (A → B → C)) :
    (roots.map (fun root =>
      typeWeight color extra typePattern rootPairs root *
        ((lefts.map (extensionWeight color extra left leftPairs root)).sum *
         (rights.map (extensionWeight color extra right rightPairs root)).sum))).sum =
      (crossColors.values.map (fun cross =>
        gluedRaw color extra roots lefts rights left right cross rootPairs leftPairs rightPairs)).sum := by
  simp only [gluedRaw_eq_group color extra hsym roots lefts rights typePattern left right _
    hleft hright rootPairs leftPairs rightPairs]
  rw [sumByKey, entry_unfold]

/-- No color pattern that actually occurs in the host can fail the admissibility test. -/
theorem gluedRaw_zero_of_not_strong {K A B V C : Type} (color : V → V → C)
    (extra : V → V → Rat) (red present : C → Prop)
    (hred : ∀ c, red c → present c) (hsym : ∀ u v, color u v = color v u)
    (hstrong : HostStrong (fun u v => red (color u v)) (fun u v => present (color u v)))
    (roots : List (K → V)) (lefts : List (A → V)) (rights : List (B → V))
    (left : K ⊕ A → K ⊕ A → C) (right : K ⊕ B → K ⊕ B → C) (cross : A → B → C)
    (rootPairs : List (K × K)) (leftPairs : List ((K ⊕ A) × (K ⊕ A)))
    (rightPairs : List ((K ⊕ B) × (K ⊕ B)))
    (hbad : ¬ PatternStrong red present (gluedColor left right cross)) :
    gluedRaw color extra roots lefts rights left right cross rootPairs leftPairs rightPairs = 0 := by
  unfold gluedRaw
  have hn (g : Positions K A B → V) :
      ¬ Realizes color (gluedColor left right cross) g := by
    intro h
    apply hbad
    rw [← h]
    exact inducedColor_strong color red present hred hsym hstrong g
  have hmap :
      ((allPieces roots lefts rights).map glue).map (fun g =>
        if Realizes color (gluedColor left right cross) g then
          pairProduct extra g (gluedPairs rootPairs leftPairs rightPairs) else 0) =
      ((allPieces roots lefts rights).map (glue (V := V))).map (fun _ => (0 : Rat)) :=
    List.map_congr_left (fun g _ => if_neg (hn g))
  rw [hmap, ratSumMapZero]

private theorem ratSumMapFilter {X : Type} (xs : List X) (keep : X → Prop)
    (f : X → Rat) (hzero : ∀ x, ¬ keep x → f x = 0) :
    ((xs.filter (fun x => decide (keep x))).map f).sum = (xs.map f).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases ha : keep a
    · simp [ha, ih]
    · simp [ha, ih, hzero a ha, Rat.zero_add]

/-- The same denominator convention as the paper, including (n=0,1). -/
def normalization (D m : Rat) (n : Int) : Rat :=
  (2 * m * D ^ (n - 2))⁻¹

theorem normalization_glue (D m : Rat) (hD : D ≠ 0) (k a b : Int) :
    normalization D m (k + a + b) =
      normalization D m k * ((D ^ a)⁻¹ * (D ^ b)⁻¹) := by
  unfold normalization
  rw [show k + a + b - 2 = (k - 2) + a + b by omega,
    Rat.zpow_add hD ((k - 2) + a) b, Rat.zpow_add hD (k - 2) a]
  simp only [Rat.inv_mul_rev]
  have leftComm (x y z : Rat) : x * (y * z) = y * (x * z) := by
    rw [← Rat.mul_assoc, Rat.mul_comm x y, Rat.mul_assoc]
  simp [Rat.mul_assoc, leftComm, Rat.mul_comm]

/-- The data for one entry of the moment matrix. Complete listings are supplied
explicitly, so enumeration never relies on decidable equality of functions. -/
structure FlagEntry (K A B V C : Type) where
  color : V → V → C
  extra : V → V → Rat
  color_symmetric : ∀ u v, color u v = color v u
  typePattern : K → K → C
  leftPattern : K ⊕ A → K ⊕ A → C
  rightPattern : K ⊕ B → K ⊕ B → C
  left_agrees : ∀ i j, leftPattern (.inl i) (.inl j) = typePattern i j
  right_agrees : ∀ i j, rightPattern (.inl i) (.inl j) = typePattern i j
  rootPairs : List (K × K)
  leftPairs : List ((K ⊕ A) × (K ⊕ A))
  rightPairs : List ((K ⊕ B) × (K ⊕ B))
  rootSlots : Enumeration K
  leftSlots : Enumeration A
  rightSlots : Enumeration B
  roots : Enumeration (K → V)
  leftMaps : Enumeration (A → V)
  rightMaps : Enumeration (B → V)
  crossColors : Enumeration (A → B → C)

def FlagEntry.rawDensity {K A B V C : Type} (d : FlagEntry K A B V C)
    (cross : A → B → C) : Rat :=
  gluedRaw d.color d.extra d.roots.values d.leftMaps.values d.rightMaps.values
    d.leftPattern d.rightPattern cross d.rootPairs d.leftPairs d.rightPairs

def FlagEntry.leftCount {K A B V C : Type} (d : FlagEntry K A B V C)
    (root : K → V) : Rat :=
  (d.leftMaps.values.map (extensionWeight d.color d.extra d.leftPattern d.leftPairs root)).sum

def FlagEntry.rightCount {K A B V C : Type} (d : FlagEntry K A B V C)
    (root : K → V) : Rat :=
  (d.rightMaps.values.map (extensionWeight d.color d.extra d.rightPattern d.rightPairs root)).sum

def FlagEntry.momentEntry {K A B V C : Type} (d : FlagEntry K A B V C) (D m : Rat) : Rat :=
  normalization D m d.rootSlots.values.length *
    (d.roots.values.map (fun root =>
      typeWeight d.color d.extra d.typePattern d.rootPairs root *
        ((d.leftCount root * (D ^ (d.leftSlots.values.length : Int))⁻¹) *
         (d.rightCount root * (D ^ (d.rightSlots.values.length : Int))⁻¹)))).sum

def FlagEntry.density {K A B V C : Type} (d : FlagEntry K A B V C) (D m : Rat)
    (cross : A → B → C) : Rat :=
  normalization D m ((d.rootSlots.values.length : Int) + d.leftSlots.values.length +
    d.rightSlots.values.length) * d.rawDensity cross

/-- Equation (3.10) of Theorem 3.4. The root pairs are used once. The lists of
pairs outside the root may be specialized to the paper's forest case; the
finite counting identity in fact holds for every such list. -/
theorem FlagEntry.momentEntry_eq_sum {K A B V C : Type} (d : FlagEntry K A B V C)
    (D m : Rat) (hD : D ≠ 0) (red present : C → Prop)
    (hred : ∀ c, red c → present c)
    (hstrong : HostStrong (fun u v => red (d.color u v)) (fun u v => present (d.color u v))) :
    d.momentEntry D m =
      ((d.crossColors.values.filter (fun cross =>
        decide (PatternStrong red present (gluedColor d.leftPattern d.rightPattern cross)))).map
          (d.density D m)).sum := by
  have hzero (cross : A → B → C)
      (hbad : ¬ PatternStrong red present (gluedColor d.leftPattern d.rightPattern cross)) :
      d.density D m cross = 0 := by
    unfold FlagEntry.density FlagEntry.rawDensity
    rw [gluedRaw_zero_of_not_strong _ _ _ _ hred d.color_symmetric hstrong _ _ _
      _ _ _ _ _ _ hbad, Rat.mul_zero]
  rw [ratSumMapFilter _ _ _ hzero]
  unfold FlagEntry.momentEntry FlagEntry.density
  let k : Int := d.rootSlots.values.length
  let a : Int := d.leftSlots.values.length
  let b : Int := d.rightSlots.values.length
  let s := (D ^ a)⁻¹ * (D ^ b)⁻¹
  let W := typeWeight d.color d.extra d.typePattern d.rootPairs
  have hfactor (root : K → V) :
      W root * (d.leftCount root * (D ^ a)⁻¹ *
        (d.rightCount root * (D ^ b)⁻¹)) =
      s * (W root * (d.leftCount root * d.rightCount root)) := by
    unfold s
    have leftComm (x y z : Rat) : x * (y * z) = y * (x * z) := by
      rw [← Rat.mul_assoc, Rat.mul_comm x y, Rat.mul_assoc]
    simp [Rat.mul_assoc, leftComm, Rat.mul_comm]
  change normalization D m k *
      (d.roots.values.map (fun root =>
        W root * (d.leftCount root * (D ^ a)⁻¹ *
          (d.rightCount root * (D ^ b)⁻¹)))).sum =
    (d.crossColors.values.map (fun cross =>
      normalization D m (k + a + b) * d.rawDensity cross)).sum
  simp only [hfactor, sumMapMulLeft, normalization_glue D m hD k a b]
  rw [← Rat.mul_assoc]
  have hdensity : d.rawDensity = (fun cross =>
      gluedRaw d.color d.extra d.roots.values d.leftMaps.values d.rightMaps.values
        d.leftPattern d.rightPattern cross d.rootPairs d.leftPairs d.rightPairs) := rfl
  rw [hdensity]
  simpa only [W, s, FlagEntry.leftCount, FlagEntry.rightCount, FlagEntry.rawDensity] using
    congrArg (fun r => normalization D m k * s * r)
      (weightedGluing_raw d.color d.extra d.color_symmetric d.roots.values
        d.leftMaps.values d.rightMaps.values d.typePattern d.leftPattern d.rightPattern
        d.left_agrees d.right_agrees d.rootPairs d.leftPairs d.rightPairs d.crossColors)

private theorem nodup_flatMap_projection {X Y : Type} (xs : List X) (block : X → List Y)
    (project : Y → X) (hnodup : xs.Nodup) (hblocks : ∀ x, (block x).Nodup)
    (hproject : ∀ x y, y ∈ block x → project y = x) :
    (xs.flatMap block).Nodup := by
  unfold List.Nodup at *
  refine List.pairwise_flatMap.mpr ⟨fun x _ => hblocks x, ?_⟩
  exact hnodup.imp (fun {x y} hne u hu v hv huv =>
    hne ((hproject x u hu).symm.trans ((congrArg project huv).trans (hproject y v hv))))

theorem allPieces_nodup {K A B V : Type} (roots : List (K → V)) (left : List (A → V))
    (right : List (B → V)) (hroots : roots.Nodup) (hleft : left.Nodup) (hright : right.Nodup) :
    (allPieces roots left right).Nodup := by
  unfold allPieces
  apply nodup_flatMap_projection roots _ Prod.fst hroots
  · intro root
    apply nodup_flatMap_projection left _ (fun p => p.2.1) hleft
    · intro l
      apply List.pairwise_map.mpr
      exact hright.imp (fun hne hp => hne (congrArg (fun p => p.2.2) hp))
    · intro l p hp
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hp
      rfl
  · intro root p hp
    obtain ⟨l, _, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hp
    rfl

/-- The glued list contains each map on the union exactly once. -/
def allGluedMaps {K A B V : Type} (roots : Enumeration (K → V))
    (left : Enumeration (A → V)) (right : Enumeration (B → V)) :
    Enumeration (Positions K A B → V) where
  values := (allPieces roots.values left.values right.values).map glue
  nodup := List.pairwise_map.mpr <|
    (allPieces_nodup roots.values left.values right.values roots.nodup left.nodup
      right.nodup).imp (fun hne h => hne <| by
        simpa only [splitMap_glue] using congrArg splitMap h)
  complete := allGluedMaps_complete roots left right

theorem pairProduct_nonneg {P V : Type} (extra : V → V → Rat)
    (hextra : ∀ u v, 0 ≤ extra u v) (f : P → V) (pairs : List (P × P)) :
    0 ≤ pairProduct extra f pairs := by
  induction pairs with
  | nil =>
    change (0 : Rat) ≤ 1
    decide
  | cons p pairs ih =>
    change 0 ≤ extra (f p.1) (f p.2) * pairProduct extra f pairs
    exact Rat.mul_nonneg (hextra _ _) ih

theorem typeWeight_nonneg {K V C : Type} (color : V → V → C)
    (extra : V → V → Rat) (hextra : ∀ u v, 0 ≤ extra u v)
    (typePattern : K → K → C) (rootPairs : List (K × K)) (root : K → V) :
    0 ≤ typeWeight color extra typePattern rootPairs root := by
  unfold typeWeight
  split
  · exact pairProduct_nonneg extra hextra root rootPairs
  · exact Rat.le_refl

theorem normalization_nonneg (D m : Rat) (hD : 0 < D) (hm : 0 < m) (n : Int) :
    0 ≤ normalization D m n := by
  apply Rat.le_of_lt
  apply Rat.inv_pos.mpr
  exact Rat.mul_pos (Rat.mul_pos (by decide) hm) (Rat.zpow_pos hD)

/-- A list of flags of one weighted type, with possibly different sizes. -/
structure FlagFamily (K V C I : Type) where
  NewPositions : I → Type
  color : V → V → C
  extra : V → V → Rat
  color_symmetric : ∀ u v, color u v = color v u
  typePattern : K → K → C
  flagPattern : (i : I) → K ⊕ NewPositions i → K ⊕ NewPositions i → C
  flag_agrees : ∀ i k l, flagPattern i (.inl k) (.inl l) = typePattern k l
  rootPairs : List (K × K)
  newPairs : (i : I) → List ((K ⊕ NewPositions i) × (K ⊕ NewPositions i))
  rootSlots : Enumeration K
  newSlots : (i : I) → Enumeration (NewPositions i)
  roots : Enumeration (K → V)
  extensions : (i : I) → Enumeration (NewPositions i → V)
  crossColors : (i j : I) → Enumeration (NewPositions i → NewPositions j → C)

def FlagFamily.entry {K V C I : Type} (f : FlagFamily K V C I) (i j : I) :
    FlagEntry K (f.NewPositions i) (f.NewPositions j) V C where
  color := f.color
  extra := f.extra
  color_symmetric := f.color_symmetric
  typePattern := f.typePattern
  leftPattern := f.flagPattern i
  rightPattern := f.flagPattern j
  left_agrees := f.flag_agrees i
  right_agrees := f.flag_agrees j
  rootPairs := f.rootPairs
  leftPairs := f.newPairs i
  rightPairs := f.newPairs j
  rootSlots := f.rootSlots
  leftSlots := f.newSlots i
  rightSlots := f.newSlots j
  roots := f.roots
  leftMaps := f.extensions i
  rightMaps := f.extensions j
  crossColors := f.crossColors i j

def FlagFamily.rootWeight {K V C I : Type} (f : FlagFamily K V C I) (root : K → V) : Rat :=
  typeWeight f.color f.extra f.typePattern f.rootPairs root

def FlagFamily.flagVector {K V C I : Type} (f : FlagFamily K V C I) (D : Rat)
    (root : K → V) (i : I) : Rat :=
  ((f.extensions i).values.map
      (extensionWeight f.color f.extra (f.flagPattern i) (f.newPairs i) root)).sum *
    (D ^ ((f.newSlots i).values.length : Int))⁻¹

def FlagFamily.densityEntry {K V C I : Type} (f : FlagFamily K V C I)
    (D m : Rat) (red present : C → Prop) (i j : I) : Rat :=
  (((f.crossColors i j).values.filter (fun cross =>
      decide (PatternStrong red present
        (gluedColor (f.flagPattern i) (f.flagPattern j) cross)))).map
    ((f.entry i j).density D m)).sum

theorem FlagFamily.gramMatrix_eq_densityEntry {K V C I : Type} (f : FlagFamily K V C I)
    (D m : Rat) (hD : D ≠ 0) (red present : C → Prop) (hred : ∀ c, red c → present c)
    (hstrong : HostStrong (fun u v => red (f.color u v)) (fun u v => present (f.color u v)))
    (i j : I) :
    gramMatrix f.roots.values (normalization D m f.rootSlots.values.length)
      f.rootWeight (f.flagVector D) i j = f.densityEntry D m red present i j := by
  exact (f.entry i j).momentEntry_eq_sum D m hD red present hred hstrong

/-- The weighted flag inequalities obtained after (3.10), for rational
coefficients. The equation and inequality hold also for arbitrary lists of
specified pairs under the extended density definition. -/
theorem FlagFamily.weightedFlagInequality {K V C I : Type} (f : FlagFamily K V C I)
    (D m : Rat) (hD : 0 < D) (hm : 0 < m) (hextra : ∀ u v, 0 ≤ f.extra u v)
    (red present : C → Prop) (hred : ∀ c, red c → present c)
    (hstrong : HostStrong (fun u v => red (f.color u v)) (fun u v => present (f.color u v)))
    (indices : List I) (x : I → Rat) :
    0 ≤ doubleSum indices (fun i j => x i * f.densityEntry D m red present i j * x j) := by
  have hw : ∀ root, 0 ≤ f.rootWeight root :=
    typeWeight_nonneg f.color f.extra hextra f.typePattern f.rootPairs
  have hg := gramMatrix_nonneg f.roots.values indices
    (normalization D m f.rootSlots.values.length)
    (normalization_nonneg D m hD hm _) f.rootWeight (f.flagVector D) hw x
  simpa only [f.gramMatrix_eq_densityEntry D m (Rat.ne_of_gt hD) red present hred hstrong]
    using hg

section ScalarExtension

open Lean.Grind
variable {R : Type} [CommRing R] [LE R]

/-- The arithmetic needed to view the rational flag densities in a larger
ordered scalar field. In particular, this is the usual inclusion into the
reals; no approximation of the rational densities is involved. -/
structure RationalScalarMap (R : Type) [CommRing R] [LE R] where
  toFun : Rat → R
  map_zero : toFun 0 = 0
  map_add : ∀ a b, toFun (a + b) = toFun a + toFun b
  map_mul : ∀ a b, toFun (a * b) = toFun a * toFun b
  map_nonneg : ∀ a, 0 ≤ a → 0 ≤ toFun a

private theorem RationalScalarMap.map_sum {X : Type} (ι : RationalScalarMap R)
    (xs : List X) (f : X → Rat) :
    ι.toFun (xs.map f).sum = (xs.map (fun a => ι.toFun (f a))).sum := by
  induction xs with
  | nil => exact ι.map_zero
  | cons a xs ih => simp only [List.map_cons, List.sum_cons, ι.map_add, ih]

theorem RationalScalarMap.map_gramMatrix {X I : Type} (ι : RationalScalarMap R)
    (roots : List X) (scale : Rat) (w : X → Rat) (v : X → I → Rat) (i j : I) :
    ι.toFun (gramMatrix roots scale w v i j) =
      gramMatrix roots (ι.toFun scale) (fun a => ι.toFun (w a))
        (fun a k => ι.toFun (v a k)) i j := by
  simp only [gramMatrix, ι.map_mul, ι.map_sum]

variable [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- The flag inequality with coefficients in any ordered scalar ring that
contains the rational densities. Specializing the scalar to the reals yields
the real-coefficient version of the inequality after (3.10). -/
theorem FlagFamily.weightedFlagInequality_over {K V C I : Type}
    (f : FlagFamily K V C I) (ι : RationalScalarMap R)
    (D m : Rat) (hD : 0 < D) (hm : 0 < m) (hextra : ∀ u v, 0 ≤ f.extra u v)
    (red present : C → Prop) (hred : ∀ c, red c → present c)
    (hstrong : HostStrong (fun u v => red (f.color u v)) (fun u v => present (f.color u v)))
    (indices : List I) (x : I → R) :
    0 ≤ doubleSum indices (fun i j => x i * ι.toFun (f.densityEntry D m red present i j) * x j) := by
  have hw : ∀ root, 0 ≤ ι.toFun (f.rootWeight root) := fun root =>
    ι.map_nonneg _ (typeWeight_nonneg f.color f.extra hextra f.typePattern f.rootPairs root)
  have hscale := ι.map_nonneg _ (normalization_nonneg D m hD hm f.rootSlots.values.length)
  have hg := gramMatrix_nonneg f.roots.values indices _ hscale
    (fun root => ι.toFun (f.rootWeight root))
    (fun root i => ι.toFun (f.flagVector D root i)) hw x
  simp only [← ι.map_gramMatrix, f.gramMatrix_eq_densityEntry D m (Rat.ne_of_gt hD)
    red present hred hstrong] at hg
  exact hg

end ScalarExtension

/-- The unordered graph of specified position pairs. -/
def specifiedAdjacent {P : Type} (pairs : List (P × P)) (u v : P) : Prop :=
  (u, v) ∈ pairs ∨ (v, u) ∈ pairs

def specifiedWalk {P : Type} (pairs : List (P × P)) : List P → Prop
  | u :: v :: tail => specifiedAdjacent pairs u v ∧ specifiedWalk pairs (v :: tail)
  | _ => True

/-- A forest has no simple cycle of length at least three. Loops and repeated
unordered pairs are ruled out separately by the simple-pair data below. -/
def SpecifiedForest {P : Type} (pairs : List (P × P)) : Prop :=
  ¬ ∃ (u : P) (tail : List P),
    2 ≤ tail.length ∧ (u :: tail).Nodup ∧ specifiedWalk pairs (u :: (tail ++ [u]))

def DistinctUnorderedPairs {P : Type} (pairs : List (P × P)) : Prop :=
  pairs.Pairwise (fun p q => p ≠ q ∧ p ≠ (q.2, q.1))

/-- The paper's domain for a weighted pattern, with unordered position pairs
represented by an orientation for the purpose of finite products. -/
structure PaperWeightedPattern (P C : Type) (red : C → Prop) where
  pattern : P → P → C
  specified : List (P × P)
  withoutDuplicates : DistinctUnorderedPairs specified
  differentPositions : ∀ e ∈ specified, e.1 ≠ e.2
  specifiedRed : ∀ e ∈ specified, red (pattern e.1 e.2)
  forest : SpecifiedForest specified

private theorem gluedColor_onLeft {K A B C : Type} (left : K ⊕ A → K ⊕ A → C)
    (right : K ⊕ B → K ⊕ B → C) (cross : A → B → C) (i j : K ⊕ A) :
    gluedColor left right cross (leftPosition i) (leftPosition j) = left i j := by
  cases i <;> cases j <;> rfl

private theorem gluedColor_onRight {K A B C : Type} (left : K ⊕ A → K ⊕ A → C)
    (right : K ⊕ B → K ⊕ B → C) (cross : A → B → C)
    (agree : ∀ i j : K, left (.inl i) (.inl j) = right (.inl i) (.inl j))
    (i j : K ⊕ B) :
    gluedColor left right cross (rightPosition i) (rightPosition j) = right i j := by
  cases i with
  | inl i =>
    cases j with
    | inl j => exact agree i j
    | inr j => rfl
  | inr i => cases j <;> rfl

/-- The specified pairs of the two flags remain red after gluing. -/
theorem FlagEntry.gluedPairs_red {K A B V C : Type} (d : FlagEntry K A B V C)
    (red : C → Prop) (cross : A → B → C)
    (hroot : ∀ e ∈ d.rootPairs, red (d.typePattern e.1 e.2))
    (hleft : ∀ e ∈ d.leftPairs, red (d.leftPattern e.1 e.2))
    (hright : ∀ e ∈ d.rightPairs, red (d.rightPattern e.1 e.2))
    (e : Positions K A B × Positions K A B)
    (he : e ∈ gluedPairs d.rootPairs d.leftPairs d.rightPairs) :
    red (gluedColor d.leftPattern d.rightPattern cross e.1 e.2) := by
  simp only [gluedPairs, List.mem_append, List.mem_map] at he
  rcases he with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · change red (d.leftPattern (.inl p.1) (.inl p.2))
    rw [d.left_agrees]
    exact hroot p hp
  · rw [gluedColor_onLeft]
    exact hleft p hp
  · rw [gluedColor_onRight]
    · exact hright p hp
    · intro i j
      exact (d.left_agrees i j).trans (d.right_agrees i j).symm

def FlagEntry.paperWeightedPattern {K A B V C : Type} (d : FlagEntry K A B V C)
    (red : C → Prop) (cross : A → B → C)
    (hroot : ∀ e ∈ d.rootPairs, red (d.typePattern e.1 e.2))
    (hleft : ∀ e ∈ d.leftPairs, red (d.leftPattern e.1 e.2))
    (hright : ∀ e ∈ d.rightPairs, red (d.rightPattern e.1 e.2))
    (hnodup : DistinctUnorderedPairs (gluedPairs d.rootPairs d.leftPairs d.rightPairs))
    (hloopless : ∀ e ∈ gluedPairs d.rootPairs d.leftPairs d.rightPairs, e.1 ≠ e.2)
    (hforest : SpecifiedForest (gluedPairs d.rootPairs d.leftPairs d.rightPairs)) :
    PaperWeightedPattern (Positions K A B) C red where
  pattern := gluedColor d.leftPattern d.rightPattern cross
  specified := gluedPairs d.rootPairs d.leftPairs d.rightPairs
  withoutDuplicates := hnodup
  differentPositions := hloopless
  specifiedRed := d.gluedPairs_red red cross hroot hleft hright
  forest := hforest

end

end FGST.FlagGluing
