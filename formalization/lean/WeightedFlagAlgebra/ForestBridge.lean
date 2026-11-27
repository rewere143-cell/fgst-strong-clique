import WeightedFlagAlgebra.FlagGluing
import WeightedFlagAlgebra.ForestDensity

namespace FGST.Chapter3.ForestTraversal

open FGST.FlagGluing

private inductive Trail (R : P → P → Prop) : P → List P → P → Prop where
  | nil (a : P) : Trail R a [] a
  | cons {a b c : P} {tail : List P} :
      R a b → Trail R b tail c → Trail R a (b :: tail) c

private theorem Trail.append {R : P → P → Prop} {a b c : P} {tail : List P}
    (h : Trail R a tail b) (e : R b c) : Trail R a (tail ++ [c]) c := by
  induction h with
  | nil a => exact .cons e (.nil c)
  | cons h _ ih => exact .cons h (ih e)

private theorem Trail.trim {R : P → P → Prop} {a b : P} {tail : List P}
    (h : Trail R a tail b) :
    ∀ z ∈ a :: tail, ∃ initial : List P, initial.Sublist tail ∧ Trail R a initial z := by
  induction h with
  | nil a =>
    intro z hz
    have hza : z = a := by simpa using hz
    subst z
    exact ⟨[], .slnil, .nil a⟩
  | @cons a b c tail hab _ ih =>
    intro z hz
    rcases List.mem_cons.mp hz with he | ht
    · subst z
      exact ⟨[], List.nil_sublist _, .nil a⟩
    · obtain ⟨initial, hs, hpre⟩ := ih z ht
      exact ⟨b :: initial, hs.cons_cons b, .cons hab hpre⟩

/-- Any reachability proof has a representative walk without repeated vertices. -/
private theorem Reach.simpleTrail {R : P → P → Prop} {a b : P} (h : Reach R a b) :
    ∃ tail : List P, Trail R a tail b ∧ (a :: tail).Nodup := by
  classical
  induction h with
  | refl => exact ⟨[], .nil a, by simp⟩
  | @tail b c _ hbc ih =>
    obtain ⟨tail, path, nodup⟩ := ih
    by_cases hc : c ∈ a :: tail
    · obtain ⟨pre, hs, ht⟩ := path.trim c hc
      exact ⟨pre, ht, List.Pairwise.sublist (hs.cons_cons a) nodup⟩
    · refine ⟨tail ++ [c], path.append hbc, ?_⟩
      change ((a :: tail) ++ [c]).Nodup
      refine List.nodup_append.mpr ⟨nodup, by simp, ?_⟩
      intro x hx y hy he
      have hcy : y = c := by simpa using hy
      exact hc (hcy ▸ he ▸ hx)

private theorem Trail.walk_close {P : Type} {R : P → P → Prop} {a b last : P}
    {tail : List P} (pairs : List (P × P))
    (h : Trail R a tail b) (inside : ∀ x y, R x y → specifiedAdjacent pairs x y)
    (e : specifiedAdjacent pairs b last) :
    specifiedWalk pairs (a :: (tail ++ [last])) := by
  induction h with
  | nil => exact ⟨e, trivial⟩
  | cons edge _ ih => exact ⟨inside _ _ edge, ih e⟩

/-- The usual cycle-free definition in the paper entails the edge deletion
form of the forest condition used by the growth-order construction. -/
theorem isForest_of_specifiedForest {P : Type} (pairs : List (P × P))
    (forest : SpecifiedForest pairs)
    (loopless : ∀ a, ¬ specifiedAdjacent pairs a a) :
    IsForest (specifiedAdjacent pairs) := by
  intro a b hab hreach
  obtain ⟨tail, path, hn⟩ := hreach.simpleTrail
  have hlength : 2 ≤ tail.length := by
    cases tail with
    | nil =>
      cases path
      exact (loopless a hab).elim
    | cons v rest =>
      cases rest with
      | nil =>
        cases path with
        | cons edge path =>
          cases path
          exact (edge.2 (Or.inl ⟨rfl, rfl⟩)).elim
      | cons w rest =>
        simp
  have hba : specifiedAdjacent pairs b a := hab.symm
  have hwalk := path.walk_close pairs (fun x y e => e.1) hba
  exact forest ⟨a, tail, hlength, hn, hwalk⟩

theorem pairSupport_isForest_of_specifiedForest {n : Nat} (pairs : List (Fin n × Fin n))
    (forest : SpecifiedForest pairs) (loopless : ∀ a, ¬ PairSupport pairs a a) :
    IsForest (PairSupport pairs) :=
  isForest_of_specifiedForest pairs forest loopless

/-- Lemma 3.3 with the usual cycle-free condition on the specified position pairs. -/
theorem connected_density_bound_of_specifiedForest (G : MarkedGraph V) (D : Nat)
    (hD : 0 < D) (hm : 0 < G.orientedMarked) (hd : ∀ x, G.host.degree x ≤ D)
    (F : Pattern n) (J : List (Fin n × Fin n))
    (symmetry : ∀ x y, F x y = F y x)
    (hasRed : ∃ a b, a ≠ b ∧ F a b = .red)
    (pairsUnique : J.Pairwise (fun e f => e ≠ f ∧ e ≠ (f.2, f.1)))
    (noLoops : ∀ e ∈ J, e.1 ≠ e.2)
    (pairsRed : ∀ e ∈ J, F e.1 e.2 = .red)
    (forest : SpecifiedForest J)
    (connected : ∀ x y, Reach (fun x y => F x y ≠ .absent) x y) :
    weightedDensity G D F J ≤
      if J = [] then 1 - (G.orientedExtra : Rat) / (G.orientedMarked : Rat)
      else (G.orientedExtra : Rat) / (G.orientedMarked : Rat) := by
  have hloopless (a : Fin n) : ¬ PairSupport J a a := fun h =>
    noLoops (a, a) (h.elim id id) rfl
  exact connected_forest_density_bound G D hD hm hd F J symmetry hasRed
    pairsUnique noLoops pairsRed (pairSupport_isForest_of_specifiedForest J forest hloopless)
    connected

end FGST.Chapter3.ForestTraversal
