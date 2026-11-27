import WeightedFlagAlgebra.FlagGluing
import WeightedFlagAlgebra.WeightedCounts

namespace FGST.FlagGluing

open FGST.Chapter3

noncomputable section
open Classical

def enumFin (n : Nat) : Enumeration (Fin n) where
  values := List.finRange n
  nodup := List.nodup_finRange n
  complete := List.mem_finRange

def enumFunctions {V : Type} (values : Enumeration V) (n : Nat) :
    Enumeration (Fin n → V) where
  values := enumMaps values.values n
  nodup := enumMaps_nodup values.values values.nodup n
  complete := enumMaps_complete values.values values.complete n

def hostVertices {V : Type} (G : MarkedGraph V) : Enumeration V where
  values := G.host.vertices
  nodup := G.host.nodup
  complete := G.host.complete

def colors : Enumeration EdgeColor where
  values := [.absent, .blue, .red]
  nodup := by decide
  complete := fun c => by cases c <;> simp

def FlagEntry.onMarkedHost {K A B V : Type} (d : FlagEntry K A B V EdgeColor)
    (G : MarkedGraph V) : FlagEntry K A B V EdgeColor :=
  { d with
    color := G.color
    extra := fun u v => (G.extra u v : Rat)
    color_symmetric := G.color_symm }

def FlagFamily.onMarkedHost {K V I : Type} (f : FlagFamily K V EdgeColor I)
    (G : MarkedGraph V) : FlagFamily K V EdgeColor I :=
  { f with
    color := G.color
    extra := fun u v => (G.extra u v : Rat)
    color_symmetric := G.color_symm }

def isRed (c : EdgeColor) : Prop := c = .red
def isPresent (c : EdgeColor) : Prop := c ≠ .absent

theorem red_implies_present (c : EdgeColor) : isRed c → isPresent c := by
  intro h
  cases c <;> simp_all [isRed, isPresent]

theorem markedHost_strong {V : Type} (G : MarkedGraph V) (hG : G.Strong) :
    HostStrong (fun u v => isRed (G.color u v)) (fun u v => isPresent (G.color u v)) := by
  intro u v x y huv hxy hux huy hvx hvy
  have hh := hG u v x y ((G.color_eq_red u v).mp huv) ((G.color_eq_red x y).mp hxy)
    hux huy hvx hvy
  simpa only [isPresent, MarkedGraph.color_ne_absent] using hh

theorem FlagFamily.weightedFlagInequality_markedHost {K V I : Type}
    (f : FlagFamily K V EdgeColor I) (G : MarkedGraph V) (hG : G.Strong)
    (D m : Rat) (hD : 0 < D) (hm : 0 < m) (indices : List I) (x : I → Rat) :
    0 ≤ doubleSum indices (fun i j =>
      x i * (f.onMarkedHost G).densityEntry D m isRed isPresent i j * x j) := by
  exact (f.onMarkedHost G).weightedFlagInequality D m hD hm
    (fun _ _ => Rat.natCast_nonneg) isRed isPresent red_implies_present
    (markedHost_strong G hG) indices x

theorem FlagEntry.momentEntry_eq_sum_markedHost {K A B V : Type}
    (d : FlagEntry K A B V EdgeColor) (G : MarkedGraph V) (hG : G.Strong)
    (D m : Rat) (hD : D ≠ 0) :
    (d.onMarkedHost G).momentEntry D m =
      ((d.crossColors.values.filter (fun cross =>
        decide (PatternStrong isRed isPresent (gluedColor d.leftPattern d.rightPattern cross)))).map
          ((d.onMarkedHost G).density D m)).sum := by
  exact (d.onMarkedHost G).momentEntry_eq_sum D m hD isRed isPresent red_implies_present
    (markedHost_strong G hG)

/-- Number positions in the order common root, left extensions, right extensions. -/
def finJoin {k l : Nat} : Fin k ⊕ Fin l → Fin (k + l) :=
  Sum.elim (Fin.castAdd l) (Fin.natAdd k)

def finSplit {k l : Nat} : Fin (k + l) → Fin k ⊕ Fin l :=
  Fin.addCases Sum.inl Sum.inr

@[simp] theorem finJoin_split {k l : Nat} (i : Fin (k + l)) :
    finJoin (finSplit i) = i := by
  induction i using Fin.addCases <;> simp [finJoin, finSplit, Fin.addCases_left, Fin.addCases_right]

@[simp] theorem finSplit_join {k l : Nat} (p : Fin k ⊕ Fin l) :
    finSplit (finJoin p) = p := by
  cases p <;> simp [finJoin, finSplit, Fin.addCases_left, Fin.addCases_right]

def positionIndex {k a b : Nat} : Positions (Fin k) (Fin a) (Fin b) → Fin (k + (a + b)) :=
  fun p => finJoin (p.map id finJoin)

def indexedPosition {k a b : Nat} : Fin (k + (a + b)) → Positions (Fin k) (Fin a) (Fin b) :=
  fun i => (finSplit i).map id finSplit

@[simp] theorem positionIndex_indexedPosition {k a b : Nat} (i : Fin (k + (a + b))) :
    positionIndex (indexedPosition i) = i := by
  unfold positionIndex indexedPosition
  have hm (p : Fin k ⊕ Fin (a + b)) : (p.map id finSplit).map id finJoin = p := by
    cases p <;> simp
  rw [hm, finJoin_split]

@[simp] theorem indexedPosition_positionIndex {k a b : Nat}
    (p : Positions (Fin k) (Fin a) (Fin b)) :
    indexedPosition (positionIndex p) = p := by
  cases p <;> simp [positionIndex, indexedPosition]

private theorem ratSumPerm {xs ys : List Rat} (h : xs.Perm ys) : xs.sum = ys.sum := by
  induction h with
  | nil => rfl
  | cons a h ih => simp [ih]
  | swap a b xs => simp only [List.sum_cons, Rat.add_left_comm]
  | trans _ _ i j => exact i.trans j

private theorem nsum_ratCast {A : Type} (xs : List A) (f : A → Nat) :
    (nsum xs f : Rat) = (xs.map (fun a => (f a : Rat))).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [nsum_cons, Rat.natCast_add, List.map_cons, List.sum_cons, ih]

private theorem prod_ratCast (xs : List Nat) :
    (xs.prod : Rat) = (xs.map (fun n : Nat => (n : Rat))).prod := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.prod_cons, Rat.natCast_mul, List.map_cons, ih]

def FlagEntry.indexedPattern {k a b : Nat} {V : Type}
    (d : FlagEntry (Fin k) (Fin a) (Fin b) V EdgeColor) (cross : Fin a → Fin b → EdgeColor) :
    Pattern (k + (a + b)) :=
  fun i j => gluedColor d.leftPattern d.rightPattern cross (indexedPosition i) (indexedPosition j)

def FlagEntry.indexedPairs {k a b : Nat} {V : Type}
    (d : FlagEntry (Fin k) (Fin a) (Fin b) V EdgeColor) :
    List (Fin (k + (a + b)) × Fin (k + (a + b))) :=
  (gluedPairs d.rootPairs d.leftPairs d.rightPairs).map (fun e =>
    (positionIndex e.1, positionIndex e.2))

private theorem indexedMaps_perm {k a b : Nat} {V : Type} (G : MarkedGraph V)
    (maps : Enumeration (Positions (Fin k) (Fin a) (Fin b) → V)) :
    (maps.values.map (fun g i => g (indexedPosition i))).Perm
      (enumMaps G.host.vertices (k + (a + b))) := by
  have hn : (maps.values.map (fun g i => g (indexedPosition i))).Nodup := by
    apply List.pairwise_map.mpr
    exact maps.nodup.imp (fun hne heq => hne <| by
      funext p
      simpa only [indexedPosition_positionIndex] using congrFun heq (positionIndex p))
  apply (List.perm_ext_iff_of_nodup hn (enumMaps_nodup G.host.vertices G.host.nodup _)).mpr
  intro f
  constructor
  · intro _
    exact enumMaps_complete G.host.vertices G.host.complete _ f
  · intro _
    refine List.mem_map.mpr ⟨fun p => f (positionIndex p), maps.complete _, ?_⟩
    funext i
    change f (positionIndex (indexedPosition i)) = f i
    rw [positionIndex_indexedPosition]

private theorem indexedPattern_realizes {k a b : Nat} {V : Type}
    (d : FlagEntry (Fin k) (Fin a) (Fin b) V EdgeColor) (G : MarkedGraph V)
    (cross : Fin a → Fin b → EdgeColor) (g : Positions (Fin k) (Fin a) (Fin b) → V) :
    d.indexedPattern cross = inducedPattern G (fun i => g (indexedPosition i)) ↔
      Realizes G.color (gluedColor d.leftPattern d.rightPattern cross) g := by
  constructor
  · intro h
    funext p q
    have h' := congrFun (congrFun h (positionIndex p)) (positionIndex q)
    simpa only [FlagEntry.indexedPattern, inducedPattern, indexedPosition_positionIndex,
      inducedColor] using h'.symm
  · intro h
    funext i j
    exact (congrFun (congrFun h (indexedPosition i)) (indexedPosition j)).symm

private theorem indexedPairs_product {k a b : Nat} {V : Type}
    (d : FlagEntry (Fin k) (Fin a) (Fin b) V EdgeColor) (G : MarkedGraph V)
    (g : Positions (Fin k) (Fin a) (Fin b) → V) :
    ((d.indexedPairs.map (fun p =>
      G.extra (g (indexedPosition p.1)) (g (indexedPosition p.2)))).prod : Rat) =
      pairProduct (fun u v => (G.extra u v : Rat)) g
        (gluedPairs d.rootPairs d.leftPairs d.rightPairs) := by
  rw [prod_ratCast]
  simp only [FlagEntry.indexedPairs, pairProduct, List.map_map, Function.comp_def,
    indexedPosition_positionIndex]

theorem FlagEntry.rawDensity_eq_weightedCount {k a b : Nat} {V : Type}
    (d : FlagEntry (Fin k) (Fin a) (Fin b) V EdgeColor) (G : MarkedGraph V)
    (cross : Fin a → Fin b → EdgeColor) :
    (d.onMarkedHost G).rawDensity cross =
      (weightedCount G (d.indexedPattern cross) d.indexedPairs : Rat) := by
  let w (f : Fin (k + (a + b)) → V) : Rat :=
    ((if d.indexedPattern cross = inducedPattern G f then
      (d.indexedPairs.map (fun p => G.extra (f p.1) (f p.2))).prod else 0) : Nat)
  let maps := allGluedMaps d.roots d.leftMaps d.rightMaps
  have perm := indexedMaps_perm G maps
  unfold weightedCount
  rw [nsum_ratCast]
  change _ = (List.map w (enumMaps G.host.vertices _)).sum
  rw [← ratSumPerm (perm.map w)]
  unfold FlagEntry.rawDensity gluedRaw
  change (maps.values.map _).sum = _
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro g _
  have h := indexedPattern_realizes d G cross g
  by_cases hr : Realizes G.color (gluedColor d.leftPattern d.rightPattern cross) g
  · have hh := h.mpr hr
    change (if Realizes G.color (gluedColor d.leftPattern d.rightPattern cross) g then
      pairProduct (fun u v => (G.extra u v : Rat)) g
        (gluedPairs d.rootPairs d.leftPairs d.rightPairs) else 0) = w _
    simp only [w, if_pos hr, if_pos hh]
    exact (indexedPairs_product d G g).symm
  · have hh := fun he => hr (h.mp he)
    change (if Realizes G.color (gluedColor d.leftPattern d.rightPattern cross) g then
      pairProduct (fun u v => (G.extra u v : Rat)) g
        (gluedPairs d.rootPairs d.leftPairs d.rightPairs) else 0) = w _
    simp only [w, if_neg hr, if_neg hh]
    rfl

private theorem norm_eq_count_formula (D m n c : Nat) (hD : (D : Rat) ≠ 0) :
    normalization (D : Rat) ((m : Rat) / 2) (n : Int) * (c : Rat) =
      ((D ^ 2 * c : Nat) : Rat) / ((m * D ^ n : Nat) : Rat) := by
  have hm : 2 * ((m : Rat) / 2) = (m : Rat) := by
    rw [Rat.mul_comm]
    exact Rat.div_mul_cancel (by decide)
  have hp : (D : Rat) ^ ((n : Int) - 2) = ((D : Rat) ^ n) * (((D : Rat) ^ (2 : Nat))⁻¹) := by
    rw [show (n : Int) - 2 = (n : Int) + -(2 : Int) by omega, Rat.zpow_add hD,
      Rat.zpow_neg]
    change ((D : Rat) ^ (n : Int)) * (((D : Rat) ^ ((2 : Nat) : Int))⁻¹) = _
    rw [Rat.zpow_natCast, Rat.zpow_natCast]
  rw [normalization, hm, hp, Rat.div_def]
  simp only [Rat.natCast_mul, Rat.natCast_pow, Rat.inv_mul_rev, Rat.inv_inv]
  have leftComm (x y z : Rat) : x * (y * z) = y * (x * z) := by
    rw [← Rat.mul_assoc, Rat.mul_comm x y, Rat.mul_assoc]
  simp [leftComm, Rat.mul_comm]

private theorem finEnumeration_length (n : Nat) (e : Enumeration (Fin n)) :
    e.values.length = n := by
  have hp := (List.perm_ext_iff_of_nodup e.nodup (List.nodup_finRange n)).mpr
    (fun i => iff_of_true (e.complete i) (List.mem_finRange i))
  simpa using hp.length_eq

/-- Section 3.2 uses literally the density from §3.1 after the positional relabeling. -/
theorem FlagEntry.density_eq_weightedDensity {k a b : Nat} {V : Type}
    (d : FlagEntry (Fin k) (Fin a) (Fin b) V EdgeColor) (G : MarkedGraph V)
    (D : Nat) (hD : (D : Rat) ≠ 0) (cross : Fin a → Fin b → EdgeColor) :
    (d.onMarkedHost G).density (D : Rat) ((G.orientedMarked : Rat) / 2) cross =
      weightedDensity G D (d.indexedPattern cross) d.indexedPairs := by
  unfold FlagEntry.density weightedDensity
  rw [FlagEntry.rawDensity_eq_weightedCount]
  change normalization (D : Rat) ((G.orientedMarked : Rat) / 2)
      ((d.rootSlots.values.length : Int) + d.leftSlots.values.length + d.rightSlots.values.length) *
        (weightedCount G (d.indexedPattern cross) d.indexedPairs : Rat) = _
  rw [finEnumeration_length k d.rootSlots, finEnumeration_length a d.leftSlots,
    finEnumeration_length b d.rightSlots]
  rw [show (k : Int) + a + b = ((k + (a + b) : Nat) : Int) by omega]
  exact norm_eq_count_formula _ _ _ _ hD

/-- Theorem 3.4 stated with the chapter's common definition of weighted density. -/
theorem FlagEntry.momentEntry_eq_sum_weightedDensity {k a b : Nat} {V : Type}
    (d : FlagEntry (Fin k) (Fin a) (Fin b) V EdgeColor) (G : MarkedGraph V) (hG : G.Strong)
    (D : Nat) (hD : (D : Rat) ≠ 0) :
    (d.onMarkedHost G).momentEntry (D : Rat) ((G.orientedMarked : Rat) / 2) =
      ((d.crossColors.values.filter (fun cross =>
        decide (PatternStrong isRed isPresent (gluedColor d.leftPattern d.rightPattern cross)))).map
          (fun cross => weightedDensity G D (d.indexedPattern cross) d.indexedPairs)).sum := by
  rw [d.momentEntry_eq_sum_markedHost G hG _ _ hD]
  congr 1
  exact List.map_congr_left (fun cross _ => d.density_eq_weightedDensity G D hD cross)

/-- All flags in §3.2 share the first k numbered positions. The auxiliary
positions of flag i are numbered by Fin (size i). -/
structure NumberedFlagFamily (k : Nat) (I : Type) where
  size : I → Nat
  typePattern : Fin k → Fin k → EdgeColor
  flagPattern : (i : I) → Fin k ⊕ Fin (size i) → Fin k ⊕ Fin (size i) → EdgeColor
  flag_agrees : ∀ i x y, flagPattern i (.inl x) (.inl y) = typePattern x y
  rootPairs : List (Fin k × Fin k)
  newPairs : (i : I) → List ((Fin k ⊕ Fin (size i)) × (Fin k ⊕ Fin (size i)))

def NumberedFlagFamily.onHost {k : Nat} {V I : Type} (f : NumberedFlagFamily k I)
    (G : MarkedGraph V) : FlagFamily (Fin k) V EdgeColor I where
  NewPositions i := Fin (f.size i)
  color := G.color
  extra u v := (G.extra u v : Rat)
  color_symmetric := G.color_symm
  typePattern := f.typePattern
  flagPattern := f.flagPattern
  flag_agrees := f.flag_agrees
  rootPairs := f.rootPairs
  newPairs := f.newPairs
  rootSlots := enumFin k
  newSlots i := enumFin (f.size i)
  roots := enumFunctions (hostVertices G) k
  extensions i := enumFunctions (hostVertices G) (f.size i)
  crossColors i j := enumFunctions (enumFunctions colors (f.size j)) (f.size i)

def NumberedFlagFamily.commonDensityEntry {k : Nat} {V I : Type}
    (f : NumberedFlagFamily k I) (G : MarkedGraph V) (D : Nat) (i j : I) : Rat :=
  let d := (f.onHost G).entry i j
  ((d.crossColors.values.filter (fun cross =>
    decide (PatternStrong isRed isPresent (gluedColor d.leftPattern d.rightPattern cross)))).map
        (fun cross => weightedDensity G D (d.indexedPattern cross) d.indexedPairs)).sum

theorem NumberedFlagFamily.densityEntry_eq_common {k : Nat} {V I : Type}
    (f : NumberedFlagFamily k I) (G : MarkedGraph V) (D : Nat)
    (hD : (D : Rat) ≠ 0) (i j : I) :
    (f.onHost G).densityEntry D ((G.orientedMarked : Rat) / 2) isRed isPresent i j =
      f.commonDensityEntry G D i j := by
  unfold FlagFamily.densityEntry NumberedFlagFamily.commonDensityEntry
  dsimp only
  congr 1
  apply List.map_congr_left
  intro cross _
  exact FlagEntry.density_eq_weightedDensity ((f.onHost G).entry i j) G D hD cross

section

open Lean.Grind

/-- The final inequality of §3.2 using only the common weighted-density
definition and the actual marked multigraph. -/
theorem NumberedFlagFamily.weightedFlagInequality {R : Type} [CommRing R] [LE R] [LT R]
    [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    {k : Nat} {V I : Type} (f : NumberedFlagFamily k I) (G : MarkedGraph V) (hG : G.Strong)
    (D : Nat) (hD : 0 < (D : Rat)) (hm : 0 < (G.orientedMarked : Rat))
    (ι : RationalScalarMap R) (indices : List I) (x : I → R) :
    0 ≤ doubleSum indices (fun i j => x i * ι.toFun (f.commonDensityEntry G D i j) * x j) := by
  have hm' : 0 < (G.orientedMarked : Rat) / 2 := by
    rw [Rat.div_def]
    exact Rat.mul_pos hm (Rat.inv_pos.mpr (by decide))
  have hg := (f.onHost G).weightedFlagInequality_over ι
    (D : Rat) ((G.orientedMarked : Rat) / 2) hD hm'
    (fun _ _ => Rat.natCast_nonneg) isRed isPresent red_implies_present
    (markedHost_strong G hG) indices x
  simpa only [f.densityEntry_eq_common G D (Rat.ne_of_gt hD)] using hg

end

end

end FGST.FlagGluing
