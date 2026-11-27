import WeightedFlagAlgebra.DensityBounds

namespace FGST.Chapter3
namespace ForestTraversal

/-- Reflexive transitive closure, used for the finite support and the specified forest. -/
inductive Reach {P : Type u} (rel : P → P → Prop) (start : P) : P → Prop
  | refl : Reach rel start start
  | tail {x y : P} : Reach rel start x → rel x y → Reach rel start y

theorem Reach.map {R S : P → P → Prop} (h : ∀ x y, R x y → S x y)
    (r : Reach R x y) : Reach S x y := by
  induction r with
  | refl => exact .refl
  | tail _ e ih => exact .tail ih (h _ _ e)

theorem Reach.trans {R : P → P → Prop} (a : Reach R x y) (b : Reach R y z) :
    Reach R x z := by
  induction b with
  | refl => exact a
  | tail _ e ih => exact .tail ih e

theorem Reach.symm {R : P → P → Prop} (symmetric : ∀ x y, R x y → R y x)
    (r : Reach R x y) : Reach R y x := by
  induction r with
  | refl => exact .refl
  | tail _ e ih => exact (Reach.tail .refl (symmetric _ _ e)).trans ih

def within (J : P → P → Prop) (seen : P → Prop) (x y : P) : Prop :=
  J x y ∧ seen x ∧ seen y

def avoidsPair (a b x y : P) : Prop :=
  ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a))

/-- Forest in the equivalent cut-edge formulation: removing any edge separates its endpoints. -/
def IsForest (J : P → P → Prop) : Prop :=
  ∀ a b, J a b → ¬ Reach (fun x y => J x y ∧ avoidsPair a b x y) a b

/-- A reached set contains a path between its vertices in each forest component it meets. -/
def ComponentConnected (J : P → P → Prop) (seen : P → Prop) : Prop :=
  ∀ x y, seen x → seen y → Reach J x y → Reach (within J seen) x y

def Closed (R : P → P → Prop) (seen : P → Prop) : Prop :=
  ∀ x y, seen x → R x y → seen y

theorem closed_reach {R : P → P → Prop} {seen : P → Prop} (hc : Closed R seen)
    (r : Reach R x y) (hx : seen x) : seen y := by
  induction r with
  | refl => exact hx
  | tail _ e ih => exact hc _ _ ih e

theorem crossing_of_reachable {R : P → P → Prop} {seen : P → Prop}
    (hx : seen x) (hy : ¬ seen y) (h : Reach R x y) :
    ∃ a b, seen a ∧ ¬ seen b ∧ R a b := by
  classical
  induction h with
  | refl => exact False.elim (hy hx)
  | @tail a b _ e ih =>
    by_cases ha : seen a
    · exact ⟨a, b, ha, hy, e⟩
    · exact ih ha

private theorem within_symmetric {J : P → P → Prop} {seen : P → Prop}
    (symm : ∀ x y, J x y → J y x) : ∀ x y, within J seen x y → within J seen y x :=
  fun _ _ h => ⟨symm _ _ h.1, h.2.2, h.2.1⟩

/-- A forest crossing from a reached component has only one possible reached endpoint. -/
theorem unique_crossing_neighbor {J : P → P → Prop} {seen : P → Prop}
    (symm : ∀ x y, J x y → J y x) (forest : IsForest J)
    (withinConnected : ComponentConnected J seen)
    (hx : seen x) (hy : ¬ seen y) (hxy : J x y) (hz : seen z) (hzy : J z y) :
    z = x := by
  classical
  by_cases he : z = x
  · exact he
  · have r : Reach J x z := .tail (.tail .refl hxy) (symm z y hzy)
    have rd := (withinConnected x z hx hz r).map (fun a b h =>
      (show J a b ∧ avoidsPair x y a b from ⟨h.1, fun hx' =>
        hx'.elim (fun hh => hy (hh.2 ▸ h.2.2)) (fun hh => hy (hh.1 ▸ h.2.1))⟩))
    have hAvoid : avoidsPair x y z y := by
      intro h
      rcases h with h | h
      · exact he h.1
      · exact hy (h.1 ▸ hz)
    exact False.elim (forest x y hxy (.tail rd ⟨hzy, hAvoid⟩))

/-- Appending a position along a specified edge preserves the component invariant. -/
theorem connected_after_crossing {J : P → P → Prop} {seen : P → Prop}
    (symm : ∀ x y, J x y → J y x) (old : ComponentConnected J seen)
    (hx : seen x) (hxy : J x y) :
    ComponentConnected J (fun z => seen z ∨ z = y) := by
  have both_old (a b : P) (ha : seen a) (hb : seen b) (r : Reach J a b) :
      Reach (within J (fun z => seen z ∨ z = y)) a b :=
    (old _ _ ha hb r).map (fun _ _ h => ⟨h.1, Or.inl h.2.1, Or.inl h.2.2⟩)
  have last (a : P) (ha : seen a) (r : Reach J a y) :
      Reach (within J (fun z => seen z ∨ z = y)) a y :=
    .tail (both_old a x ha hx (.tail r (symm _ _ hxy))) ⟨hxy, Or.inl hx, Or.inr rfl⟩
  intro a b ha hb r
  rcases ha with ha | rfl <;> rcases hb with hb | rfl
  · exact both_old _ _ ha hb r
  · exact last _ ha r
  · exact (last _ hb (r.symm symm)).symm (within_symmetric symm)
  · exact .refl

/-- If no specified edge crosses, a new position lies in a different forest component. -/
theorem connected_after_bridge {J : P → P → Prop} {seen : P → Prop}
    (symm : ∀ x y, J x y → J y x) (old : ComponentConnected J seen)
    (closed : Closed J seen) (hy : ¬ seen y) :
    ComponentConnected J (fun z => seen z ∨ z = y) := by
  intro a b ha hb r
  rcases ha with ha | rfl <;> rcases hb with hb | rfl
  · exact (old _ _ ha hb r).map (fun _ _ h => ⟨h.1, Or.inl h.2.1, Or.inl h.2.2⟩)
  · exact False.elim (hy (closed_reach closed r ha))
  · exact False.elim (hy (closed_reach closed (r.symm symm) hb))
  · exact .refl

def seen (order : Fin k → P) (x : P) : Prop := ∃ i, order i = x

def pulledPattern (F : Pattern n) (order : Fin k → Fin n) : Pattern k :=
  fun i j => F (order i) (order j)

def used (plan : GrowthPlan k) (order : Fin (k + 2) → P) (a b : P) : Prop :=
  ∃ e ∈ plan.specifiedPairs,
    (order e.1 = a ∧ order e.2 = b) ∨ (order e.1 = b ∧ order e.2 = a)

private def extendOrder (order : Fin k → P) (x : P) : Fin (k + 1) → P :=
  Fin.lastCases x order

@[simp] private theorem extendOrder_old (order : Fin k → P) (x : P) (i : Fin k) :
    extendOrder order x i.castSucc = order i := Fin.lastCases_castSucc i

@[simp] private theorem extendOrder_last (order : Fin k → P) (x : P) :
    extendOrder order x (Fin.last k) = x := Fin.lastCases_last

private theorem seen_extend (order : Fin k → P) (y z : P) :
    seen (extendOrder order y) z ↔ seen order z ∨ z = y := by
  constructor
  · rintro ⟨i, hi⟩
    cases i using Fin.lastCases with
    | last => exact Or.inr (by simpa using hi.symm)
    | cast i => exact Or.inl ⟨i, by simpa using hi⟩
  · rintro (⟨i, hi⟩ | rfl)
    · exact ⟨i.castSucc, by simpa using hi⟩
    · exact ⟨Fin.last k, by simp⟩

private theorem extend_inj (order : Fin k → P) (hi : Function.Injective order)
    (y : P) (hy : ¬ seen order y) : Function.Injective (extendOrder order y) := by
  intro i j he
  cases i using Fin.lastCases with
  | last =>
    cases j using Fin.lastCases with
    | last => rfl
    | cast j => exact False.elim (hy ⟨j, by simpa using he.symm⟩)
  | cast i =>
    cases j using Fin.lastCases with
    | last => exact False.elim (hy ⟨i, by simpa using he⟩)
    | cast j => exact congrArg Fin.castSucc (hi (by simpa using he))

private theorem used_extend (plan : GrowthPlan k) (order : Fin (k + 2) → P)
    (i : Fin (k + 2)) (y a b : P) (s : Bool) :
    used (.append plan i s) (extendOrder order y) a b ↔ used plan order a b ∨
      (s = true ∧ ((order i = a ∧ y = b) ∨ (order i = b ∧ y = a))) := by
  unfold used
  simp only [GrowthPlan.specifiedPairs, List.mem_append]
  constructor
  · rintro ⟨e, he | he, hab⟩
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
      exact Or.inl ⟨f, hf, by simpa using hab⟩
    · cases s
      · simp at he
      · have heq : e = (i.castSucc, Fin.last (k + 2)) := by simpa using he
        subst e
        exact Or.inr ⟨rfl, by simpa using hab⟩
  · rintro (⟨e, he, hab⟩ | ⟨he, hab⟩)
    · exact ⟨(e.1.castSucc, e.2.castSucc), Or.inl (List.mem_map_of_mem he), by simpa using hab⟩
    · subst s
      exact ⟨(i.castSucc, Fin.last (k + 2)), Or.inr (by simp), by simpa using hab⟩

structure Prefix (F : Pattern n) (J : Fin n → Fin n → Prop) (s : Bool) (k : Nat) where
  plan : GrowthPlan k
  order : Fin (k + 2) → Fin n
  injective : Function.Injective order
  follows : plan.follows (pulledPattern F order)
  rootFlag : plan.rootSpecified = s
  components : ComponentConnected J (seen order)
  precise : ∀ a b, used plan order a b ↔ J a b ∧ seen order a ∧ seen order b

private def rootOrder (a b : P) : Fin 2 → P :=
  fun i => if i = 0 then a else b

private theorem seen_root (a b z : P) : seen (rootOrder a b) z ↔ z = a ∨ z = b := by
  constructor
  · rintro ⟨i, hi⟩
    by_cases h0 : i = 0
    · exact Or.inl (by simpa [rootOrder, h0] using hi.symm)
    · exact Or.inr (by simpa [rootOrder, h0] using hi.symm)
  · rintro (rfl | rfl)
    · exact ⟨0, by simp [rootOrder]⟩
    · exact ⟨1, by simp [rootOrder]⟩

private theorem root_inj (a b : P) (hab : a ≠ b) : Function.Injective (rootOrder a b) := by
  intro i j h
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp_all [rootOrder]

private def initialPrefix (F : Pattern n) (J : Fin n → Fin n → Prop) (s : Bool)
    (a b : Fin n) (hab : a ≠ b) (red : F a b = .red)
    (symm : ∀ x y, J x y → J y x) (loopless : ∀ x, ¬ J x x)
    (present : s = true → J a b) (empty : s = false → ∀ x y, ¬ J x y) :
    Prefix F J s 0 where
  plan := .root s
  order := rootOrder a b
  injective := root_inj a b hab
  follows := by simpa [GrowthPlan.follows, pulledPattern, rootOrder] using red
  rootFlag := rfl
  components := by
    intro x y hx hy path
    rcases (seen_root a b x).mp hx with hxe | hxe <;>
      rcases (seen_root a b y).mp hy with hye | hye <;>
      subst x <;> subst y
    · exact .refl
    · cases s
      · exact False.elim (hab (by
          have hca := closed_reach (seen := fun x => x = a)
            (fun x y _ h => (empty rfl x y h).elim) path rfl
          exact hca.symm))
      · exact .tail .refl ⟨present rfl, hx, hy⟩
    · cases s
      · have hca := closed_reach (seen := fun x => x = b)
          (fun x y _ h => (empty rfl x y h).elim) path rfl
        exact False.elim (hab hca)
      · exact .tail .refl ⟨symm a b (present rfl), hx, hy⟩
    · exact .refl
  precise := by
    intro x y
    cases s
    · constructor
      · simp [used, GrowthPlan.specifiedPairs]
      · intro h
        exact (empty rfl x y h.1).elim
    · constructor
      · rintro ⟨e, he, h⟩
        have heq : e = (0, 1) := by simpa [GrowthPlan.specifiedPairs] using he
        subst e
        rcases h with ⟨hx, hy⟩ | ⟨hy, hx⟩
        · exact ⟨by simpa [rootOrder] using
            (show J (rootOrder a b 0) (rootOrder a b 1) by simpa [rootOrder] using present rfl)
              |> (fun hv => hx ▸ hy ▸ hv),
            ⟨0, hx⟩, ⟨1, hy⟩⟩
        · exact ⟨by
            have hz : J (rootOrder a b 1) (rootOrder a b 0) := by
              simpa [rootOrder] using symm a b (present rfl)
            exact hx ▸ hy ▸ hz,
            ⟨1, hx⟩, ⟨0, hy⟩⟩
      · rintro ⟨h, hx, hy⟩
        rcases (seen_root a b x).mp hx with hxe | hxe <;>
          rcases (seen_root a b y).mp hy with hye | hye <;>
          subst x <;> subst y
        · exact (loopless _ h).elim
        · exact ⟨(0, 1), by simp [GrowthPlan.specifiedPairs], Or.inl (by simp [rootOrder])⟩
        · exact ⟨(0, 1), by simp [GrowthPlan.specifiedPairs], Or.inr (by simp [rootOrder])⟩
        · exact (loopless _ h).elim

private def appendPrefix {F : Pattern n} {J : Fin n → Fin n → Prop}
    (cur : Prefix F J s k) (i : Fin (k + 2)) (y : Fin n) (flag : Bool)
    (hy : ¬ seen cur.order y) (step : F (cur.order i) y ≠ .absent)
    (symm : ∀ x y, J x y → J y x) (loopless : ∀ x, ¬ J x x)
    (unique : ∀ z, seen cur.order z → (J z y ↔ flag = true ∧ cur.order i = z))
    (connected : ComponentConnected J (fun z => seen cur.order z ∨ z = y)) :
    Prefix F J s (k + 1) where
  plan := .append cur.plan i flag
  order := extendOrder cur.order y
  injective := extend_inj cur.order cur.injective y hy
  follows := by
    simp only [GrowthPlan.follows, pulledPattern, extendOrder_old, extendOrder_last]
    exact ⟨cur.follows, step⟩
  rootFlag := cur.rootFlag
  components := by
    intro a b ha hb path
    apply (connected a b ((seen_extend ..).mp ha) ((seen_extend ..).mp hb) path).map
    intro x z h
    exact ⟨h.1, (seen_extend ..).mpr h.2.1, (seen_extend ..).mpr h.2.2⟩
  precise := by
    intro a b
    rw [used_extend, cur.precise, seen_extend, seen_extend]
    have hi : seen cur.order (cur.order i) := ⟨i, rfl⟩
    constructor
    · rintro (⟨hab, ha, hb⟩ | ⟨hf, ⟨ha, hb⟩ | ⟨hb, ha⟩⟩)
      · exact ⟨hab, Or.inl ha, Or.inl hb⟩
      · subst a
        subst b
        exact ⟨(unique _ hi).mpr ⟨hf, rfl⟩, Or.inl hi, Or.inr rfl⟩
      · subst a
        subst b
        exact ⟨symm _ _ ((unique _ hi).mpr ⟨hf, rfl⟩), Or.inr rfl, Or.inl hi⟩
    · rintro ⟨hab, ha | ha, hb | hb⟩
      · exact Or.inl ⟨hab, ha, hb⟩
      · subst b
        obtain ⟨hf, he⟩ := (unique _ ha).mp hab
        exact Or.inr ⟨hf, Or.inl ⟨he, rfl⟩⟩
      · subst a
        obtain ⟨hf, he⟩ := (unique _ hb).mp (symm _ _ hab)
        exact Or.inr ⟨hf, Or.inr ⟨he, rfl⟩⟩
      · subst a
        subst b
        exact (loopless _ hab).elim

private theorem oneMore {F : Pattern n} {J : Fin n → Fin n → Prop}
    (cur : Prefix F J s k) (missing : Fin n) (hmissing : ¬ seen cur.order missing)
    (symm : ∀ x y, J x y → J y x) (loopless : ∀ x, ¬ J x x)
    (forest : IsForest J) (red : ∀ x y, J x y → F x y = .red)
    (conn : ∀ x y, Reach (fun x y => F x y ≠ .absent) x y) :
    ∃ (next : Prefix F J s (k + 1)) (y : Fin n), ¬ seen cur.order y ∧
      ∀ z, seen next.order z ↔ seen cur.order z ∨ z = y := by
  classical
  by_cases closed : Closed J (seen cur.order)
  · obtain ⟨x, y, hx, hy, hxy⟩ := crossing_of_reachable
      (seen := seen cur.order) (show seen cur.order (cur.order 0) from ⟨0, rfl⟩)
      hmissing (conn (cur.order 0) missing)
    obtain ⟨i, rfl⟩ := hx
    let next := appendPrefix cur i y false hy hxy symm loopless
      (fun z hz => by
        suffices h : ¬ J z y by simp [h]
        exact fun e => hy (closed z y hz e))
      (connected_after_bridge symm cur.components closed hy)
    exact ⟨next, y, hy, fun z => seen_extend cur.order y z⟩
  · have crossing : ∃ x y, seen cur.order x ∧ ¬ seen cur.order y ∧ J x y := by
      apply Classical.byContradiction
      intro h
      apply closed
      intro x y hx hxy
      by_cases hy : seen cur.order y
      · exact hy
      · exact (h ⟨x, y, hx, hy, hxy⟩).elim
    obtain ⟨x, y, hx, hy, hxy⟩ := crossing
    obtain ⟨i, rfl⟩ := hx
    have hi : seen cur.order (cur.order i) := ⟨i, rfl⟩
    have step : F (cur.order i) y ≠ .absent := by simp [red _ _ hxy]
    let next := appendPrefix cur i y true hy step symm loopless
      (fun z hz => by
        constructor
        · intro h
          exact ⟨rfl, (unique_crossing_neighbor symm forest cur.components hi hy hxy hz h).symm⟩
        · rintro ⟨_, he⟩
          exact he ▸ hxy)
      (connected_after_crossing symm cur.components hi hxy)
    exact ⟨next, y, hy, fun z => seen_extend cur.order y z⟩

private theorem finishPrefix {F : Pattern n} {J : Fin n → Fin n → Prop} (remaining : Nat)
    (symm : ∀ x y, J x y → J y x) (loopless : ∀ x, ¬ J x x)
    (forest : IsForest J) (red : ∀ x y, J x y → F x y = .red)
    (conn : ∀ x y, Reach (fun x y => F x y ≠ .absent) x y) :
    ∀ (k : Nat) (cur : Prefix F J s k) (todo : List (Fin n)),
      todo.length = remaining → todo.Nodup →
      (∀ x, x ∈ todo ↔ ¬ seen cur.order x) →
      ∃ (l : Nat) (endResult : Prefix F J s l), Function.Surjective endResult.order := by
  classical
  induction remaining using Nat.strongRecOn with
  | ind r ih =>
    intro k cur todo ht hd hset
    cases todo with
    | nil =>
      refine ⟨k, cur, fun x => ?_⟩
      by_cases h : seen cur.order x
      · exact h
      · exact False.elim (by simpa using (hset x).mpr h)
    | cons z tail =>
      have hmissing : ¬ seen cur.order z := (hset z).mp (by simp)
      obtain ⟨next, y, hy, hseen⟩ := oneMore cur z hmissing symm loopless forest red conn
      have hymem : y ∈ z :: tail := (hset y).mpr hy
      have hsmall : ((z :: tail).erase y).length < r := by
        rw [List.length_erase_of_mem hymem, ht]
        have hp : 0 < (z :: tail).length := by simp
        omega
      refine ih _ hsmall (k + 1) next ((z :: tail).erase y) rfl (hd.erase y) ?_
      intro x
      rw [hd.mem_erase_iff, hset, hseen]
      exact ⟨fun h hb => hb.elim h.2 h.1, fun h => ⟨fun e => h (.inr e), fun e => h (.inl e)⟩⟩

private theorem completeFromRoot {F : Pattern n} {J : Fin n → Fin n → Prop}
    (a b : Fin n) (hab : a ≠ b) (rootRed : F a b = .red) (s : Bool)
    (present : s = true → J a b) (empty : s = false → ∀ x y, ¬ J x y)
    (symm : ∀ x y, J x y → J y x) (loopless : ∀ x, ¬ J x x)
    (forest : IsForest J) (red : ∀ x y, J x y → F x y = .red)
    (conn : ∀ x y, Reach (fun x y => F x y ≠ .absent) x y) :
    ∃ (l : Nat) (endResult : Prefix F J s l), Function.Surjective endResult.order := by
  classical
  let p := initialPrefix F J s a b hab rootRed symm loopless present empty
  let todo := (List.finRange n).filter (fun x => decide (¬ seen p.order x))
  refine finishPrefix todo.length symm loopless forest red conn 0 p todo rfl
    ((List.nodup_finRange _).filter _) ?_
  intro x
  simp [todo, List.mem_finRange]

/-- A connected pattern extends a specified forest to a rooted growth plan. -/
theorem forest_growth_plan (F : Pattern n) (J : Fin n → Fin n → Prop)
    (someRed : ∃ a b, a ≠ b ∧ F a b = .red)
    (symm : ∀ x y, J x y → J y x) (loopless : ∀ x, ¬ J x x)
    (forest : IsForest J) (red : ∀ x y, J x y → F x y = .red)
    (conn : ∀ x y, Reach (fun x y => F x y ≠ .absent) x y) :
    ∃ (s : Bool) (l : Nat) (endResult : Prefix F J s l), Function.Surjective endResult.order ∧
      (s = true ↔ ∃ x y, J x y) := by
  classical
  by_cases h : ∃ x y, J x y
  · obtain ⟨a, b, hab⟩ := h
    have hne : a ≠ b := fun h => loopless a (h ▸ hab)
    obtain ⟨l, p, hp⟩ := completeFromRoot a b hne (red a b hab) true
      (fun _ => hab) (fun e => Bool.noConfusion e) symm loopless forest red conn
    exact ⟨true, l, p, hp, ⟨fun _ => ⟨a, b, hab⟩, fun _ => rfl⟩⟩
  · obtain ⟨a, b, hab, hred⟩ := someRed
    obtain ⟨l, p, hp⟩ := completeFromRoot a b hab hred false
      (fun e => Bool.noConfusion e) (fun _ x y e => h ⟨x, y, e⟩) symm loopless forest red conn
    exact ⟨false, l, p, hp,
      ⟨fun e => Bool.noConfusion e, fun he => (h he).elim⟩⟩

theorem bijective_fin_size {k n : Nat} (order : Fin k → Fin n)
    (hi : Function.Injective order) (hs : Function.Surjective order) : k = n := by
  let ordered := (List.finRange k).map order
  have hn : ordered.Nodup := List.pairwise_map.mpr
    ((List.nodup_finRange k).imp (fun ne eq => ne (hi eq)))
  have hp : ordered.Perm (List.finRange n) :=
    (List.perm_ext_iff_of_nodup hn (List.nodup_finRange n)).mpr (fun x =>
      ⟨fun _ => List.mem_finRange x, fun _ => by
        obtain ⟨y, hy⟩ := hs x
        exact List.mem_map.mpr ⟨y, List.mem_finRange y, hy⟩⟩)
  simpa [ordered] using hp.length_eq

theorem plan_pairs_increasing (plan : GrowthPlan k) :
    ∀ e ∈ plan.specifiedPairs, e.1 < e.2 := by
  induction plan with
  | root flag =>
    intro e he
    cases flag <;> simp [GrowthPlan.specifiedPairs] at he
    subst e
    decide
  | @append k p i flag ih =>
    intro e he
    rw [GrowthPlan.specifiedPairs, List.mem_append] at he
    rcases he with old | added
    · obtain ⟨orig, ho, rfl⟩ := List.mem_map.mp old
      have h := ih orig ho
      exact h
    · cases flag
      · simp at added
      · have heq : e = (i.castSucc, Fin.last (k + 2)) := by simpa using added
        subst e
        exact Fin.castSucc_lt_last i

theorem plan_pairs_nodup (plan : GrowthPlan k) : plan.specifiedPairs.Nodup := by
  induction plan with
  | root flag => cases flag <;> simp [GrowthPlan.specifiedPairs]
  | @append k p i flag ih =>
    rw [GrowthPlan.specifiedPairs, List.nodup_append]
    refine ⟨List.pairwise_map.mpr (ih.imp ?_), ?_, ?_⟩
    · intro a b hab he
      exact hab (Prod.ext (Fin.castSucc_inj.mp (congrArg Prod.fst he))
        (Fin.castSucc_inj.mp (congrArg Prod.snd he)))
    · cases flag <;> simp
    · intro a ha b hb eq
      cases flag
      · simp at hb
      · obtain ⟨orig, _, rfl⟩ := List.mem_map.mp ha
        have heq : b = (i.castSucc, Fin.last (k + 2)) := by simpa using hb
        rw [heq] at eq
        exact Fin.ne_of_lt (Fin.castSucc_lt_last orig.2) (congrArg Prod.snd eq)

#print axioms forest_growth_plan

end ForestTraversal
end FGST.Chapter3
