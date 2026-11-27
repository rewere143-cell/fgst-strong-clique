import WeightedFlagAlgebra.ForestTraversal
import WeightedFlagAlgebra.PatternRelabeling

namespace FGST.Chapter3

open ForestTraversal

private theorem plan_support (plan : GrowthPlan k) (q : Fin (k + 2) → Fin n)
    (hi : Function.Injective q) (a b : Fin (k + 2)) :
    PairSupport plan.specifiedPairs a b ↔ used plan q (q a) (q b) := by
  constructor
  · rintro (h | h)
    · exact ⟨(a, b), h, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨(b, a), h, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ⟨e, he, h | h⟩
    · have heq : e = (a, b) := Prod.ext (hi h.1) (hi h.2)
      exact Or.inl (heq ▸ he)
    · have heq : e = (b, a) := Prod.ext (hi h.1) (hi h.2)
      exact Or.inr (heq ▸ he)

private theorem support_exists_iff (J : List (Fin n × Fin n)) :
    (∃ a b, PairSupport J a b) ↔ J ≠ [] := by
  constructor
  · rintro ⟨a, b, ha | ha⟩ h
    · simp [h] at ha
    · simp [h] at ha
  · cases J with
    | nil => intro h; exact (h rfl).elim
    | cons e es => exact fun _ => ⟨e.1, e.2, Or.inl (by simp)⟩

/-- Lemma 3.3's upper bounds for a connected pattern with a red edge.
The forest hypothesis uses the equivalent form that removing a specified edge
disconnects its endpoints. Position pairs are represented by either orientation. -/
theorem connected_forest_density_bound (G : MarkedGraph V) (D : Nat) (hD : 0 < D)
    (hm : 0 < G.orientedMarked) (hd : ∀ x, G.host.degree x ≤ D)
    (F : Pattern n) (J : List (Fin n × Fin n))
    (symmetry : ∀ x y, F x y = F y x)
    (hasRed : ∃ a b, a ≠ b ∧ F a b = .red)
    (pairsUnique : J.Pairwise (fun e f => e ≠ f ∧ e ≠ (f.2, f.1)))
    (noLoops : ∀ e ∈ J, e.1 ≠ e.2)
    (pairsRed : ∀ e ∈ J, F e.1 e.2 = .red)
    (forest : IsForest (PairSupport J))
    (connected : ∀ x y, Reach (fun x y => F x y ≠ .absent) x y) :
    weightedDensity G D F J ≤
      if J = [] then 1 - (G.orientedExtra : Rat) / (G.orientedMarked : Rat)
      else (G.orientedExtra : Rat) / (G.orientedMarked : Rat) := by
  classical
  have hsymm : ∀ a b, PairSupport J a b → PairSupport J b a :=
    fun _ _ h => h.elim Or.inr Or.inl
  have hloop : ∀ a, ¬ PairSupport J a a := by
    intro a h
    rcases h with h | h
    · exact noLoops (a, a) h rfl
    · exact noLoops (a, a) h rfl
  have hred : ∀ a b, PairSupport J a b → F a b = .red := by
    intro a b h
    rcases h with h | h
    · exact pairsRed (a, b) h
    · exact (symmetry a b).trans (pairsRed (b, a) h)
  obtain ⟨s, k, traversal, surj, hflag⟩ :=
    forest_growth_plan F (PairSupport J) hasRed hsymm hloop forest hred connected
  have he : k + 2 = n := bijective_fin_size traversal.order traversal.injective surj
  subst n
  let q := traversal.order
  let p : Fin (k + 2) → Fin (k + 2) := fun i => Classical.choose (surj i)
  have hqp : ∀ i, q (p i) = i := fun i => Classical.choose_spec (surj i)
  have hpq : ∀ i, p (q i) = i := fun i => traversal.injective (hqp (q i))
  have hsp : ∀ a b, PairSupport traversal.plan.specifiedPairs a b ↔
      PairSupport (relabelPairs p J) a b := by
    intro a b
    rw [plan_support traversal.plan q traversal.injective,
      traversal.precise (q a) (q b), pairSupport_relabel_iff J p q hqp hpq]
    exact ⟨fun h => h.1, fun h => ⟨h, ⟨a, rfl⟩, ⟨b, rfl⟩⟩⟩
  have hplan : (traversal.plan.specifiedPairs.map canonicalPair).Nodup := by
    rw [canonicalPair_map_of_increasing _ (plan_pairs_increasing traversal.plan)]
    exact plan_pairs_nodup traversal.plan
  have hperm := canonicalPair_lists_perm_of_support traversal.plan.specifiedPairs
    (relabelPairs p J) hplan
    (canonicalPairs_nodup_relabel J p q hqp (canonicalPairs_nodup J pairsUnique)) hsp
  have hdens :
      weightedDensity G D (relabelPattern q F) traversal.plan.specifiedPairs =
        weightedDensity G D F J :=
    (weightedDensity_canonical G D (relabelPattern q F) _ _ hperm).trans
      (weightedDensity_relabel G D F J p q hqp hpq)
  have bound := weighted_density_le_root_traversal G D hD hm hd traversal.plan
    (relabelPattern q F) traversal.follows
  rw [hdens, traversal.rootFlag] at bound
  by_cases hempty : J = []
  · have hs : s = false := by
      cases s with
      | false => rfl
      | true => exact False.elim (((support_exists_iff J).mp (hflag.mp rfl)) hempty)
    simpa [hempty, hs] using bound
  · have hs : s = true := hflag.mpr ((support_exists_iff J).mpr hempty)
    simpa [hempty, hs] using bound

#print axioms connected_forest_density_bound

end FGST.Chapter3
