import Std

namespace FGST.Chapter3

/-- A finite sum over a concrete enumeration. -/
def nsum (xs : List A) (f : A → Nat) : Nat := (xs.map f).sum

@[simp] theorem nsum_nil (f : A → Nat) : nsum [] f = 0 := rfl

@[simp] theorem nsum_cons (a : A) (xs : List A) (f : A → Nat) :
    nsum (a :: xs) f = f a + nsum xs f := rfl

theorem nsum_congr (xs : List A) (f g : A → Nat)
    (h : ∀ a ∈ xs, f a = g a) : nsum xs f = nsum xs g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [nsum_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem nsum_le (xs : List A) (f g : A → Nat)
    (h : ∀ a ∈ xs, f a ≤ g a) : nsum xs f ≤ nsum xs g := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons a xs ih =>
    exact Nat.add_le_add (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

theorem nsum_add (xs : List A) (f g : A → Nat) :
    nsum xs (fun a => f a + g a) = nsum xs f + nsum xs g := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih, Nat.add_assoc, Nat.add_left_comm]

theorem nsum_const (xs : List A) (c : Nat) : nsum xs (fun _ => c) = xs.length * c := by
  induction xs with
  | nil => exact (Nat.zero_mul _).symm
  | cons a xs ih => simp [ih, Nat.succ_mul, Nat.add_comm]

theorem nsum_mul (xs : List A) (f : A → Nat) (c : Nat) :
    nsum xs (fun a => c * f a) = c * nsum xs f := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih, Nat.mul_add]

theorem nsum_map (xs : List A) (f : A → B) (g : B → Nat) :
    nsum (xs.map f) g = nsum xs (fun x => g (f x)) := by
  simp [nsum, List.map_map, Function.comp_def]

theorem nsum_filter (xs : List A) (p : A → Bool) (f : A → Nat) :
    nsum (xs.filter p) f = nsum xs (fun a => if p a then f a else 0) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : p a <;> simp [h, ih]

theorem nsum_perm (xs ys : List A) (hp : xs.Perm ys) (f : A → Nat) :
    nsum xs f = nsum ys f := (hp.map f).sum_nat

theorem term_le_nsum (xs : List A) (f : A → Nat) (x : A) (hx : x ∈ xs) :
    f x ≤ nsum xs f := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_add_right ..
    · exact Nat.le_trans (ih hx) (Nat.le_add_left ..)

theorem nsum_flatMap (xs : List A) (ys : A → List B) (f : B → Nat) :
    nsum (xs.flatMap ys) f = nsum xs (fun x => nsum (ys x) f) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [nsum, List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons] at ih ⊢
    rw [ih]

theorem nsum_swap (xs : List A) (ys : List B) (f : A → B → Nat) :
    nsum xs (fun x => nsum ys (f x)) = nsum ys (fun y => nsum xs (fun x => f x y)) := by
  induction xs with
  | nil => simp [nsum_const]
  | cons x xs ih =>
    simp only [nsum_cons]
    rw [nsum_add, ih]

theorem nsum_zero_of_not_mem [DecidableEq A] (xs : List A) (a : A) (ha : a ∉ xs) (c : Nat) :
    nsum xs (fun x => if x = a then c else 0) = 0 := by
  rw [nsum_congr xs (fun x => if x = a then c else 0) (fun _ => 0)
    (fun x hx => if_neg (show x ≠ a from fun h => ha (h ▸ hx)))]
  simp [nsum_const]

theorem nsum_single [DecidableEq A] (xs : List A) (hd : xs.Nodup) (a : A) (ha : a ∈ xs)
    (c : Nat) : nsum xs (fun x => if x = a then c else 0) = c := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    obtain ⟨hnot, hn⟩ := List.nodup_cons.mp hd
    by_cases h : x = a
    · subst x
      simp [nsum_zero_of_not_mem xs a hnot]
    · simp [h, ih hn ((List.mem_cons.mp ha).resolve_left (Ne.symm h))]

/-- Reindex a finite weighted sum by a unique key for each term. -/
theorem nsum_partition [DecidableEq B] (xs : List A) (keys : List B) (key : A → B)
    (hd : keys.Nodup) (hc : ∀ a ∈ xs, key a ∈ keys) (f : A → Nat) :
    nsum keys (fun k => nsum xs (fun a => if k = key a then f a else 0)) = nsum xs f := by
  rw [nsum_swap]
  exact nsum_congr _ _ _ (fun a ha => nsum_single keys hd (key a) (hc a ha) (f a))

theorem nsum_split_pair [DecidableEq A] (xs : List A) (hd : xs.Nodup)
    (a b : A) (ha : a ∈ xs) (hb : b ∈ xs) (hab : a ≠ b) (f : A → Nat) :
    nsum xs f = f a + f b + nsum xs (fun x => if x ≠ a ∧ x ≠ b then f x else 0) := by
  rw [← nsum_single xs hd a ha (f a), ← nsum_single xs hd b hb (f b), ← nsum_add, ← nsum_add]
  apply nsum_congr
  intro x _
  by_cases hxa : x = a
  · subst x
    simp [hab]
  · by_cases hxb : x = b
    · subst x
      simp [hxa]
    · simp [hxa, hxb]

theorem term_eq_of_sum_eq (xs : List A) (f g : A → Nat)
    (hle : ∀ x ∈ xs, f x ≤ g x) (hsum : nsum xs f = nsum xs g) (x : A) (hx : x ∈ xs) :
    f x = g x := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    have ha := hle a (by simp)
    have htail := nsum_le xs f g (fun b hb => hle b (by simp [hb]))
    simp only [nsum_cons] at hsum
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    exact ih (fun b hb => hle b (by simp [hb])) (by omega) hx

def prependMap (v : V) (f : Fin n → V) : Fin (n + 1) → V := Fin.cases v f

/-- Enumerate all maps on numbered positions, with independent choices at each position. -/
def enumMaps (vertices : List V) : (n : Nat) → List (Fin n → V)
  | 0 => [Fin.elim0]
  | n + 1 => vertices.flatMap fun v => (enumMaps vertices n).map (prependMap v)

theorem enumMaps_complete (vertices : List V) (complete : ∀ v, v ∈ vertices) (n : Nat)
    (f : Fin n → V) : f ∈ enumMaps vertices n := by
  induction n with
  | zero =>
    have heq : f = Fin.elim0 := by funext i; exact i.elim0
    simp [enumMaps, heq]
  | succ n ih =>
    apply List.mem_flatMap.mpr
    refine ⟨f 0, complete _, List.mem_map.mpr ⟨fun i => f i.succ, ih _, ?_⟩⟩
    funext i
    cases i using Fin.cases <;> simp [prependMap]

theorem enumMaps_nodup (vertices : List V) (nodup : vertices.Nodup) (n : Nat) :
    (enumMaps vertices n).Nodup := by
  induction n with
  | zero => simp [enumMaps]
  | succ n ih =>
    change ((vertices.flatMap fun v => (enumMaps vertices n).map (prependMap v)).Pairwise
      (fun a b => a ≠ b))
    rw [List.pairwise_flatMap]
    constructor
    · intro v _
      apply List.pairwise_map.mpr
      exact ih.imp (fun hab heq => hab (funext fun i => by simpa [prependMap] using congrFun heq i.succ))
    · exact nodup.imp (by
        intro a b hab f hf g hg heq
        obtain ⟨f₀, _, rfl⟩ := List.mem_map.mp hf
        obtain ⟨g₀, _, rfl⟩ := List.mem_map.mp hg
        exact hab (by simpa [prependMap] using congrFun heq 0))

end FGST.Chapter3
