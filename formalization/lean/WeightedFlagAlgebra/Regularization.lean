import WeightedFlagAlgebra.FiniteHost

namespace FGST.Chapter3
namespace FiniteMultigraph

open Classical

private noncomputable def unitIf (p : Prop) : Nat := if p then 1 else 0

private noncomputable def occurrences (v : V) (xs : List V) : Nat :=
  (xs.map fun x => unitIf (x = v)).sum

private theorem sum_map_eq (xs : List A) (f g : A → Nat)
    (h : ∀ x ∈ xs, f x = g x) : (xs.map f).sum = (xs.map g).sum :=
  congrArg List.sum (List.map_inj_left.mpr h)

private theorem sum_map_zero (xs : List A) (f : A → Nat) (h : ∀ x ∈ xs, f x = 0) :
    (xs.map f).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have hs := ih (fun y hy => h y (by simp [hy]))
    simp [hx, hs]

private theorem sum_map_add (xs : List A) (f g : A → Nat) :
    (xs.map fun x => f x + g x).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

private theorem occurrences_cons (v x : V) (xs : List V) :
    occurrences v (x :: xs) = unitIf (x = v) + occurrences v xs := rfl

private theorem occurrences_append (v : V) (xs ys : List V) :
    occurrences v (xs ++ ys) = occurrences v xs + occurrences v ys := by
  simp [occurrences]

private theorem occurrences_replicate (v x : V) (n : Nat) :
    occurrences v (List.replicate n x) = if x = v then n else 0 := by
  by_cases h : x = v <;> simp [occurrences, unitIf, h, List.sum_replicate_nat]

private theorem occurrences_zero_of_not_mem (v : V) (xs : List V) (h : v ∉ xs) :
    occurrences v xs = 0 := by
  apply sum_map_zero
  intro x hx
  have hne : x ≠ v := fun hEq => h (hEq ▸ hx)
  simp [unitIf, hne]

private theorem occurrences_one (v : V) (xs : List V) (h : xs.Nodup) (hv : v ∈ xs) :
    occurrences v xs = 1 := by
  induction xs with
  | nil => simp at hv
  | cons x xs ih =>
    obtain ⟨hn, ht⟩ := List.nodup_cons.mp h
    rw [occurrences_cons]
    by_cases he : x = v
    · subst x
      simp [unitIf, occurrences_zero_of_not_mem v xs hn]
    · have hv' : v ∈ xs := by
        rcases List.mem_cons.mp hv with hs | hs
        · exact False.elim (he hs.symm)
        · exact hs
      simp [unitIf, he, ih ht hv']

private theorem occurrences_map_eq (f : V → W) (hf : ∀ x y, f x = f y → x = y)
    (v : V) (xs : List V) : occurrences (f v) (xs.map f) = occurrences v xs := by
  simp only [occurrences, List.map_map]
  apply sum_map_eq
  intro x _
  by_cases he : x = v
  · subst x
    simp [unitIf]
  · have hne : f x ≠ f v := fun e => he (hf x v e)
    simp [unitIf, he, hne]

private theorem occurrences_map_other (f : V → W) (v : W) (xs : List V)
    (h : ∀ x, f x ≠ v) : occurrences v (xs.map f) = 0 := by
  simp only [occurrences, List.map_map]
  exact sum_map_zero _ _ (fun x _ => by simp [unitIf, h x])

private theorem nodup_map (f : A → B) (h : ∀ x y, f x = f y → x = y)
    (xs : List A) (hx : xs.Nodup) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hn, ht⟩ := List.nodup_cons.mp hx
    refine List.nodup_cons.mpr ⟨?_, ih ht⟩
    intro hm
    obtain ⟨y, hy, he⟩ := List.mem_map.mp hm
    exact hn (h y x he ▸ hy)

private inductive Port (D : Nat)
  | first
  | second
  | other (index : Fin (D - 1))

private def portList (D : Nat) : List (Port D) :=
  .first :: .second :: (List.finRange (D - 1)).map Port.other

private theorem port_complete (p : Port D) : p ∈ portList D := by
  cases p with
  | first => simp [portList]
  | second => simp [portList]
  | other i => exact by simp [portList, List.mem_finRange]

private theorem port_nodup (D : Nat) : (portList D).Nodup := by
  rw [portList, List.nodup_cons, List.nodup_cons]
  refine ⟨by simp, by simp, ?_⟩
  exact nodup_map Port.other (fun x y h => Port.other.inj h) _ (List.nodup_finRange _)

private noncomputable def insidePair : Port D → Port D → Nat
  | .first, .other _ | .other _, .first => 1
  | .second, .other _ | .other _, .second => 1
  | .other i, .other j => unitIf (i ≠ j)
  | _, _ => 0

private noncomputable def crossPair (x y v : V) : Port D → Nat
  | .first => unitIf (v = x)
  | .second => unitIf (v = y)
  | .other _ => 0

private noncomputable def attachMult (G : FiniteMultigraph V) (x y : V) :
    V ⊕ Port D → V ⊕ Port D → Nat
  | .inl v, .inl w => G.multiplicity v w
  | .inl v, .inr p | .inr p, .inl v => crossPair x y v p
  | .inr p, .inr q => insidePair p q

/-- Attach a new K_(D+1) missing its port edge, with ports incident to x and y. -/
private noncomputable def attachPair (G : FiniteMultigraph V) (D : Nat) (x y : V) :
    FiniteMultigraph (V ⊕ Port D) where
  vertices := G.vertices.map Sum.inl ++ (portList D).map Sum.inr
  complete v := by
    cases v with
    | inl v => exact List.mem_append_left _ (List.mem_map_of_mem (G.complete v))
    | inr p => exact List.mem_append_right _ (List.mem_map_of_mem (port_complete p))
  nodup := by
    refine List.nodup_append.mpr ⟨?_, ?_, ?_⟩
    · exact nodup_map Sum.inl (fun x y h => Sum.inl.inj h) _ G.nodup
    · exact nodup_map Sum.inr (fun x y h => Sum.inr.inj h) _ (port_nodup D)
    · simp
  multiplicity := attachMult G x y
  symmetric u v := by
    cases u with
    | inl u => cases v with
      | inl v => exact G.symmetric u v
      | inr v => rfl
    | inr u => cases v with
      | inl v => rfl
      | inr v => cases u <;> cases v <;> simp [attachMult, insidePair, ne_comm]
  loopless v := by
    cases v with
    | inl v => exact G.loopless v
    | inr v => cases v <;> simp [attachMult, insidePair, unitIf]

private theorem attach_degree_old (G : FiniteMultigraph V) (D : Nat) (x y v : V) :
    (attachPair G D x y).degree (Sum.inl v) =
      G.degree v + unitIf (v = x) + unitIf (v = y) := by
  simp only [FiniteMultigraph.degree, attachPair, List.map_append, List.sum_append_nat,
    List.map_map, portList, List.map_cons, List.sum_cons, attachMult, Function.comp_def, crossPair]
  have hz := sum_map_zero (List.finRange (D - 1)) (fun _ => 0) (by simp)
  simp [hz, Nat.add_assoc]

private theorem complementary_sum (xs : List A) (x : A) :
    (xs.map fun y => unitIf (x ≠ y)).sum + occurrences x xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons y xs ih =>
    rw [occurrences_cons, List.map_cons, List.sum_cons, List.length_cons]
    by_cases h : x = y
    · subst y
      rw [show unitIf (x ≠ x) = 0 by simp [unitIf], show unitIf (x = x) = 1 by simp [unitIf]]
      omega
    · have hn : y ≠ x := Ne.symm h
      rw [show unitIf (x ≠ y) = 1 by simp [unitIf, h],
        show unitIf (y = x) = 0 by simp [unitIf, hn]]
      omega

private theorem attach_degree_new (G : FiniteMultigraph V) (D : Nat) (hD : 1 ≤ D)
    (x y : V) (p : Port D) : (attachPair G D x y).degree (Sum.inr p) = D := by
  have hx := occurrences_one x G.vertices G.nodup (G.complete x)
  have hy := occurrences_one y G.vertices G.nodup (G.complete y)
  cases p with
  | first =>
    have hlen : ((List.finRange (D - 1)).map (fun _ => 1)).sum = D - 1 := by
      simp [List.map_const', List.sum_replicate_nat]
    simp only [FiniteMultigraph.degree, attachPair, List.map_append, List.sum_append_nat,
      List.map_map, portList, List.map_cons, List.sum_cons, attachMult, Function.comp_def,
      crossPair, insidePair]
    change occurrences x G.vertices + (0 + (0 + _)) = D
    rw [hx, hlen]
    omega
  | second =>
    have hlen : ((List.finRange (D - 1)).map (fun _ => 1)).sum = D - 1 := by
      simp [List.map_const', List.sum_replicate_nat]
    simp only [FiniteMultigraph.degree, attachPair, List.map_append, List.sum_append_nat,
      List.map_map, portList, List.map_cons, List.sum_cons, attachMult, Function.comp_def,
      crossPair, insidePair]
    change occurrences y G.vertices + (0 + (0 + _)) = D
    rw [hy, hlen]
    omega
  | other i =>
    have ht := complementary_sum (List.finRange (D - 1)) i
    have hi := occurrences_one i (List.finRange (D - 1)) (List.nodup_finRange _)
      (List.mem_finRange _)
    rw [hi, List.length_finRange] at ht
    have hz := sum_map_zero G.vertices (fun _ => 0) (by simp)
    have hdeg := i.isLt
    simp only [FiniteMultigraph.degree, attachPair, List.map_append, List.sum_append_nat,
      List.map_map, portList, List.map_cons, List.sum_cons, attachMult, Function.comp_def,
      crossPair, insidePair, hz]
    omega

/-- An induced embedding that preserves every old multiplicity and adds only simple edges. -/
structure SimpleExtension (G : FiniteMultigraph V) (H : FiniteMultigraph W)
    (embed : V → W) : Prop where
  injective : Function.Injective embed
  induced : ∀ v w, H.multiplicity (embed v) (embed w) = G.multiplicity v w
  new_simple : ∀ x y, (¬ (∃ v, embed v = x) ∨ ¬ (∃ v, embed v = y)) →
    H.multiplicity x y ≤ 1

theorem SimpleExtension.refl (G : FiniteMultigraph V) : SimpleExtension G G id where
  injective := by intro _ _ h; exact h
  induced := fun _ _ => rfl
  new_simple x y h := by
    rcases h with h | h
    · exact False.elim (h ⟨x, rfl⟩)
    · exact False.elim (h ⟨y, rfl⟩)

theorem SimpleExtension.comp {G : FiniteMultigraph V} {H : FiniteMultigraph W}
    {K : FiniteMultigraph U} {f : V → W} {g : W → U}
    (first : SimpleExtension G H f) (second : SimpleExtension H K g) :
    SimpleExtension G K (g ∘ f) where
  injective := by intro _ _ h; exact first.injective (second.injective h)
  induced x y := (second.induced (f x) (f y)).trans (first.induced x y)
  new_simple x y h := by
    by_cases hx : ∃ w, g w = x
    · by_cases hy : ∃ w, g w = y
      · obtain ⟨wx, rfl⟩ := hx
        obtain ⟨wy, rfl⟩ := hy
        rw [second.induced]
        apply first.new_simple
        rcases h with h | h
        · exact Or.inl (fun ⟨v, hv⟩ => h ⟨v, congrArg g hv⟩)
        · exact Or.inr (fun ⟨v, hv⟩ => h ⟨v, congrArg g hv⟩)
      · exact second.new_simple _ _ (Or.inr hy)
    · exact second.new_simple _ _ (Or.inl hx)

private theorem attach_simple_extension (G : FiniteMultigraph V) (D : Nat) (v w : V) :
    SimpleExtension G (attachPair G D v w) Sum.inl where
  injective := by intro _ _ h; exact Sum.inl.inj h
  induced _ _ := rfl
  new_simple x y h := by
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        rcases h with h | h
        · exact False.elim (h ⟨x, rfl⟩)
        · exact False.elim (h ⟨y, rfl⟩)
      | inr p => cases p <;> simp [attachPair, attachMult, crossPair, unitIf] <;> split <;> omega
    | inr p =>
      cases y with
      | inl y => cases p <;> simp [attachPair, attachMult, crossPair, unitIf] <;> split <;> omega
      | inr q =>
        cases p <;> cases q <;> simp [attachPair, attachMult, insidePair, unitIf] <;> split <;> omega

private def padMult (G : FiniteMultigraph V) : Option V → Option V → Nat
  | some x, some y => G.multiplicity x y
  | _, _ => 0

private def addIsolate (G : FiniteMultigraph V) : FiniteMultigraph (Option V) where
  vertices := none :: G.vertices.map some
  complete v := by
    cases v with
    | none => simp
    | some v => simp [G.complete v]
  nodup := List.nodup_cons.mpr ⟨by simp, nodup_map some (fun x y h => Option.some.inj h) _ G.nodup⟩
  multiplicity := padMult G
  symmetric u v := by
    cases u <;> cases v <;> simp [padMult, G.symmetric]
  loopless v := by cases v <;> simp [padMult, G.loopless]

private theorem isolate_simple_extension (G : FiniteMultigraph V) :
    SimpleExtension G (addIsolate G) some where
  injective := by intro _ _ h; exact Option.some.inj h
  induced _ _ := rfl
  new_simple x y h := by
    cases x with
    | none => exact Nat.zero_le 1
    | some x =>
      cases y with
      | none => exact Nat.zero_le 1
      | some y =>
        rcases h with h | h
        · exact False.elim (h ⟨x, rfl⟩)
        · exact False.elim (h ⟨y, rfl⟩)

private theorem isolated_degree (G : FiniteMultigraph V) : (addIsolate G).degree none = 0 := by
  apply sum_map_zero
  intro v _
  cases v <;> rfl

private theorem pad_degree_old (G : FiniteMultigraph V) (v : V) :
    (addIsolate G).degree (some v) = G.degree v := by
  simp [addIsolate, FiniteMultigraph.degree, padMult, Function.comp_def]

private def deficitTargets (G : FiniteMultigraph V) (D : Nat) : List V :=
  G.vertices.flatMap (fun x => List.replicate (D - G.degree x) x)

private theorem occurrences_flatten_replicate
    (xs : List V) (c : V → Nat) (v : V) (hnd : xs.Nodup) :
    occurrences v (xs.flatMap fun x => List.replicate (c x) x) =
      if v ∈ xs then c v else 0 := by
  induction xs with
  | nil => simp [occurrences]
  | cons x xs ih =>
    obtain ⟨hn, ht⟩ := List.nodup_cons.mp hnd
    rw [List.flatMap_cons, occurrences_append, occurrences_replicate, ih ht]
    by_cases h : x = v
    · subst x
      simp [hn]
    · simp [h, Ne.symm h]

private theorem occurs_in_deficit_targets (G : FiniteMultigraph V) (D : Nat) (v : V) :
    occurrences v (deficitTargets G D) = D - G.degree v := by
  rw [deficitTargets, occurrences_flatten_replicate _ _ _ G.nodup]
  simp [G.complete v]

private def sumSquare (G : FiniteMultigraph V) (xs : List V) : Nat :=
  (xs.map fun v => (xs.map fun w => G.multiplicity v w).sum).sum

private theorem sumSquare_cons (G : FiniteMultigraph V) (v : V) (xs : List V) :
    sumSquare G (v :: xs) = 2 * (xs.map fun w => G.multiplicity v w).sum + sumSquare G xs := by
  simp only [sumSquare, List.map_cons, List.sum_cons, G.loopless, Nat.zero_add]
  rw [sum_map_add]
  have hs : (xs.map fun w => G.multiplicity w v).sum =
      (xs.map fun w => G.multiplicity v w).sum :=
    sum_map_eq _ _ _ (fun w _ => G.symmetric w v)
  rw [hs]
  omega

private theorem sumSquare_even (G : FiniteMultigraph V) (xs : List V) :
    sumSquare G xs % 2 = 0 := by
  induction xs with
  | nil => rfl
  | cons v xs ih =>
    rw [sumSquare_cons]
    omega

private theorem deficit_length_budget (G : FiniteMultigraph V) (D : Nat)
    (bounded : ∀ v, G.degree v ≤ D) :
    (deficitTargets G D).length + sumSquare G G.vertices = G.vertices.length * D := by
  simp only [deficitTargets, List.length_flatMap, List.length_replicate]
  change (G.vertices.map fun a => D - G.degree a).sum + (G.vertices.map G.degree).sum =
    G.vertices.length * D
  rw [← sum_map_add]
  have h : (G.vertices.map fun a => D - G.degree a + G.degree a).sum =
      (G.vertices.map fun _ => D).sum :=
    sum_map_eq _ _ _ (fun v _ => Nat.sub_add_cancel (bounded v))
  simp [h, List.map_const', List.sum_replicate_nat]

universe u

private theorem unitIf_eq_comm (a b : V) : unitIf (a = b) = unitIf (b = a) :=
  congrArg unitIf (propext eq_comm)

private theorem fillTargets (D : Nat) (hD : 1 ≤ D) (n : Nat) :
    ∀ {V : Type u} (G : FiniteMultigraph V) (targets : List V),
      targets.length = n →
      n % 2 = 0 →
      (∀ v, G.degree v + occurrences v targets = D) →
      ∃ (W : Type u) (H : FiniteMultigraph W) (embed : V → W),
        SimpleExtension G H embed ∧ ∀ w, H.degree w = D := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro V G targets hn hEven needed
    cases targets with
    | nil =>
      refine ⟨V, G, id, SimpleExtension.refl G, ?_⟩
      intro v
      simpa [occurrences] using needed v
    | cons x rest =>
      cases rest with
      | nil => simp at hn; omega
      | cons y xs =>
        have hs : xs.length < n := by simp at hn; omega
        have he : xs.length % 2 = 0 := by simp at hn; omega
        let H := attachPair G D x y
        let embed : V → V ⊕ Port D := Sum.inl
        have hInjective : ∀ a b, embed a = embed b → a = b :=
          fun _ _ eq => Sum.inl.inj eq
        have pending : ∀ v, H.degree v + occurrences v (xs.map embed) = D := by
          intro v
          cases v with
          | inl v =>
            change H.degree (embed v) + occurrences (embed v) (xs.map embed) = D
            rw [occurrences_map_eq embed hInjective]
            change (attachPair G D x y).degree (Sum.inl v) + occurrences v xs = D
            rw [attach_degree_old, unitIf_eq_comm v x, unitIf_eq_comm v y]
            have hOld := needed v
            rw [occurrences_cons, occurrences_cons] at hOld
            omega
          | inr p =>
            change (attachPair G D x y).degree (Sum.inr p) +
              occurrences (Sum.inr p) (xs.map embed) = D
            rw [attach_degree_new G D hD,
              occurrences_map_other embed (Sum.inr p) xs (fun _ h => by cases h)]
            simp
        obtain ⟨W, K, map, ext, reg⟩ :=
          ih xs.length hs H (xs.map embed) (List.length_map _) he pending
        exact ⟨W, K, map ∘ embed, (attach_simple_extension G D x y).comp ext, reg⟩

/-- Lemma 3.1: complete a finite loopless multigraph to degree D, by pairing
its deficit units and attaching fresh copies of K_(D+1) minus one edge. -/
theorem exists_regularization {V : Type u} (G : FiniteMultigraph V) (D : Nat)
    (hD : 1 ≤ D) (bounded : ∀ v, G.degree v ≤ D) :
    ∃ (W : Type u) (H : FiniteMultigraph W) (embed : V → W),
      SimpleExtension G H embed ∧ ∀ w, H.degree w = D := by
  let targets := deficitTargets G D
  by_cases hEven : targets.length % 2 = 0
  · apply fillTargets D hD targets.length G targets rfl hEven
    intro v
    rw [occurs_in_deficit_targets]
    have hb := bounded v
    omega
  · have hDodd : D % 2 = 1 := by
      have hb := deficit_length_budget G D bounded
      have hz := sumSquare_even G G.vertices
      change targets.length + sumSquare G G.vertices = G.vertices.length * D at hb
      by_cases he : D % 2 = 0
      · have hm : (G.vertices.length * D) % 2 = 0 := by
          rw [Nat.mul_mod, he, Nat.mul_zero, Nat.zero_mod]
        omega
      · omega
    let padded := addIsolate G
    let pending : List (Option V) := targets.map some ++ List.replicate D none
    have hPair : pending.length % 2 = 0 := by
      change (targets.map some ++ List.replicate D none).length % 2 = 0
      simp only [List.length_append, List.length_map, List.length_replicate]
      omega
    have hPend : ∀ x, padded.degree x + occurrences x pending = D := by
      intro x
      change (addIsolate G).degree x + occurrences x (targets.map some ++ List.replicate D none) = D
      rw [occurrences_append, occurrences_replicate]
      cases x with
      | none =>
        rw [isolated_degree, occurrences_map_other some none targets (fun _ h => by cases h)]
        simp
      | some v =>
        rw [pad_degree_old,
          occurrences_map_eq some (fun _ _ h => Option.some.inj h) v targets]
        change G.degree v + (occurrences v (deficitTargets G D) + _) = D
        rw [occurs_in_deficit_targets]
        have hNone : (none : Option V) ≠ some v := fun h => by cases h
        simp only [if_neg hNone, Nat.add_zero]
        have hb := bounded v
        omega
    obtain ⟨W, H, embed, ext, reg⟩ :=
      fillTargets D hD pending.length padded pending rfl hPair hPend
    exact ⟨W, H, embed ∘ some, (isolate_simple_extension G).comp ext, reg⟩

theorem exists_regularization_simple {V : Type u} (G : FiniteMultigraph V) (D : Nat)
    (hD : 1 ≤ D) (bounded : ∀ v, G.degree v ≤ D)
    (simple : ∀ v w, G.multiplicity v w ≤ 1) :
    ∃ (W : Type u) (H : FiniteMultigraph W) (embed : V → W),
      SimpleExtension G H embed ∧ (∀ w, H.degree w = D) ∧
      ∀ v w, H.multiplicity v w ≤ 1 := by
  obtain ⟨W, H, embed, ext, reg⟩ := exists_regularization G D hD bounded
  refine ⟨W, H, embed, ext, reg, ?_⟩
  intro x y
  by_cases hx : ∃ v, embed v = x
  · by_cases hy : ∃ v, embed v = y
    · obtain ⟨v, rfl⟩ := hx
      obtain ⟨w, rfl⟩ := hy
      rw [ext.induced v w]
      exact simple v w
    · exact ext.new_simple x y (Or.inr hy)
  · exact ext.new_simple x y (Or.inl hx)

end FiniteMultigraph
end FGST.Chapter3

#print axioms FGST.Chapter3.FiniteMultigraph.exists_regularization
#print axioms FGST.Chapter3.FiniteMultigraph.exists_regularization_simple
