import WeightedFlagAlgebra.MarkedHost

namespace FGST.Chapter3
namespace MarkedGraph

noncomputable section
open Classical

/-- Count the marked instances by their unordered endpoint pairs. -/
def markedOnPairs (w : V → V → Nat) : List V → Nat
  | [] => 0
  | u :: vertices => nsum vertices (w u) + markedOnPairs w vertices

def cliqueSize (G : MarkedGraph V) : Nat :=
  markedOnPairs G.marked G.host.vertices

theorem oriented_eq_twice_markedOnPairs (w : V → V → Nat)
    (hsymm : ∀ u v, w u v = w v u) (hloopless : ∀ u, w u u = 0) (xs : List V) :
    nsum xs (fun u => nsum xs (w u)) = 2 * markedOnPairs w xs := by
  induction xs with
  | nil => rfl
  | cons u xs ih =>
    simp only [nsum_cons, markedOnPairs, hloopless, Nat.zero_add]
    rw [nsum_add]
    rw [nsum_congr xs (fun u' => w u' u) (w u) (fun u' _ => hsymm u' u), ih]
    omega

theorem orientedMarked_eq_twice_cliqueSize (G : MarkedGraph V) :
    G.orientedMarked = 2 * G.cliqueSize :=
  oriented_eq_twice_markedOnPairs G.marked G.marked_symm G.marked_loopless G.host.vertices

/-- The marked strong property is preserved when some instances are unmarked. -/
theorem strong_of_marked_le (G H : MarkedGraph V)
    (hhost : H.host = G.host) (hmark : ∀ u v, H.marked u v ≤ G.marked u v)
    (hG : G.Strong) : H.Strong := by
  intro u v x y huv hxy hux huy hvx hvy
  simpa only [Adj, hhost] using
    hG u v x y (Nat.lt_of_lt_of_le huv (hmark u v)) (Nat.lt_of_lt_of_le hxy (hmark x y))
      hux huy hvx hvy

private def isEitherOrientation (u v a b : V) : Prop :=
  (a = u ∧ b = v) ∨ (a = v ∧ b = u)

private theorem orientation_symm (u v a b : V) :
    isEitherOrientation u v a b ↔ isEitherOrientation u v b a := by
  unfold isEitherOrientation
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩

noncomputable def unmarkOne (G : MarkedGraph V) (u v : V) : MarkedGraph V := by
  classical
  exact {
    host := G.host
    marked := fun a b => if isEitherOrientation u v a b then G.marked a b - 1 else G.marked a b
    marked_le := fun a b => by
      have h := G.marked_le a b
      split <;> omega
    marked_symm := fun a b => by
      by_cases h : isEitherOrientation u v a b
      · simp only [if_pos h, if_pos ((orientation_symm u v a b).mp h)]
        exact congrArg (fun n => n - 1) (G.marked_symm a b)
      · have h' : ¬ isEitherOrientation u v b a := fun hh => h ((orientation_symm u v a b).mpr hh)
        simp only [if_neg h, if_neg h']
        exact G.marked_symm a b }

theorem unmarkOne_marked_le (G : MarkedGraph V) (u v a b : V) :
    (G.unmarkOne u v).marked a b ≤ G.marked a b := by
  unfold unmarkOne
  dsimp only
  split <;> omega

private theorem marked_eq_after_unmark (G : MarkedGraph V) (u v : V)
    (huv : 0 < G.marked u v) (a b : V) :
    G.marked a b = (G.unmarkOne u v).marked a b +
      (if a = u ∧ b = v then 1 else 0) + (if a = v ∧ b = u then 1 else 0) := by
  classical
  have hne : u ≠ v := by
    rintro rfl
    rw [G.marked_loopless] at huv
    omega
  unfold unmarkOne
  dsimp only
  by_cases h₁ : a = u ∧ b = v
  · obtain ⟨ha, hb⟩ := h₁
    subst a
    subst b
    simp [isEitherOrientation, hne]
    omega
  by_cases h₂ : a = v ∧ b = u
  · obtain ⟨ha, hb⟩ := h₂
    subst a
    subst b
    simp [isEitherOrientation, hne, Ne.symm hne]
    have he := G.marked_symm v u
    omega
  simp [isEitherOrientation, h₁, h₂]

private theorem orientedIndicator_sum (vertices : List V) (hn : vertices.Nodup)
    (u v : V) (hu : u ∈ vertices) (hv : v ∈ vertices) :
    (by
      classical
      exact nsum vertices (fun a => nsum vertices (fun b => if a = u ∧ b = v then 1 else 0))) = 1 := by
  classical
  refine Eq.trans (b := nsum vertices (fun a => if a = u then 1 else 0)) ?_
    (nsum_single vertices hn u hu 1)
  apply nsum_congr
  intro a _
  by_cases he : a = u
  · simpa only [he, true_and, if_true] using nsum_single vertices hn v hv 1
  · simp [he, nsum_const]

theorem orientedMarked_unmarkOne (G : MarkedGraph V) (u v : V)
    (huv : 0 < G.marked u v) :
    G.orientedMarked = (G.unmarkOne u v).orientedMarked + 2 := by
  classical
  change nsum G.host.vertices (fun a => nsum G.host.vertices (G.marked a)) =
    nsum G.host.vertices (fun a => nsum G.host.vertices ((G.unmarkOne u v).marked a)) + 2
  have he (a : V) :
      nsum G.host.vertices (G.marked a) =
        nsum G.host.vertices (fun b => (G.unmarkOne u v).marked a b +
          (if a = u ∧ b = v then 1 else 0) + (if a = v ∧ b = u then 1 else 0)) :=
    nsum_congr _ _ _ (fun b _ => marked_eq_after_unmark G u v huv a b)
  simp only [he, nsum_add]
  rw [orientedIndicator_sum G.host.vertices G.host.nodup u v (G.host.complete u)
    (G.host.complete v), orientedIndicator_sum G.host.vertices G.host.nodup v u
    (G.host.complete v) (G.host.complete u)]

theorem cliqueSize_unmarkOne (G : MarkedGraph V) (u v : V) (huv : 0 < G.marked u v) :
    G.cliqueSize = (G.unmarkOne u v).cliqueSize + 1 := by
  have h := G.orientedMarked_unmarkOne u v huv
  rw [orientedMarked_eq_twice_cliqueSize, orientedMarked_eq_twice_cliqueSize] at h
  omega

theorem marked_pair_of_positive_size (G : MarkedGraph V) (h : 0 < G.cliqueSize) :
    ∃ u v, 0 < G.marked u v := by
  classical
  by_cases yes : ∃ u v, 0 < G.marked u v
  · exact yes
  exfalso
  have hz (u v : V) : G.marked u v = 0 := by
    by_cases hne : G.marked u v = 0
    · exact hne
    · exact False.elim (yes ⟨u, v, by omega⟩)
  have hn : G.orientedMarked = 0 := by
    unfold orientedMarked
    rw [nsum_congr _ _ (fun _ => 0)]
    · simp [nsum_const]
    · intro u _
      unfold redDegree
      rw [nsum_congr _ _ (fun _ => 0) (fun v _ => hz u v)]
      simp [nsum_const]
  rw [orientedMarked_eq_twice_cliqueSize] at hn
  omega

/-- Every smaller size is realized by a marked subclique in the same host. -/
theorem truncateClique (G : MarkedGraph V) (hG : G.Strong)
    (n : Nat) (hn : n ≤ G.cliqueSize) :
    ∃ H : MarkedGraph V, H.host = G.host ∧ H.Strong ∧
      (∀ u v, H.marked u v ≤ G.marked u v) ∧ H.cliqueSize = n := by
  have run (k : Nat) : ∀ G' : MarkedGraph V, G'.Strong → G'.cliqueSize = n + k →
      ∃ H : MarkedGraph V, H.host = G'.host ∧ H.Strong ∧
        (∀ u v, H.marked u v ≤ G'.marked u v) ∧ H.cliqueSize = n := by
    induction k with
    | zero =>
      intro G' hS hsz
      exact ⟨G', rfl, hS, fun _ _ => Nat.le_refl _, by omega⟩
    | succ k ih =>
      intro G' hS hsz
      obtain ⟨u, v, hp⟩ := G'.marked_pair_of_positive_size (by omega)
      let intermediate := G'.unmarkOne u v
      have hle : ∀ a b, intermediate.marked a b ≤ G'.marked a b :=
        G'.unmarkOne_marked_le u v
      have hcount := G'.cliqueSize_unmarkOne u v hp
      change G'.cliqueSize = intermediate.cliqueSize + 1 at hcount
      obtain ⟨H, hhost, hHS, hHle, hHsize⟩ :=
        ih intermediate (G'.strong_of_marked_le intermediate rfl hle hS) (by omega)
      exact ⟨H, hhost, hHS, fun a b => Nat.le_trans (hHle a b) (hle a b), hHsize⟩
  exact run (G.cliqueSize - n) G hG (by omega)

/-- A degree condition, or any other host-only predicate, is unchanged on truncation. -/
theorem cliqueSize_upper_iff_no_exact {V : Type} (allowed : FiniteMultigraph V → Prop)
    (bound : Nat) :
    (∀ G : MarkedGraph V, allowed G.host → G.Strong → G.cliqueSize ≤ bound) ↔
      ¬ ∃ G : MarkedGraph V, allowed G.host ∧ G.Strong ∧ G.cliqueSize = bound + 1 := by
  constructor
  · intro upper h
    obtain ⟨G, hA, hS, hm⟩ := h
    have hl := upper G hA hS
    omega
  · intro noExact G hA hS
    by_cases h : G.cliqueSize ≤ bound
    · exact h
    exfalso
    obtain ⟨H, hhost, hHS, _, hsize⟩ := G.truncateClique hS (bound + 1) (by omega)
    exact noExact ⟨H, hhost ▸ hA, hHS, hsize⟩

/-- One orientation of every distinct pair, induced by the order of the vertices. -/
def unorientedPairs : List V → List (V × V)
  | [] => []
  | u :: xs => xs.map (fun v => (u, v)) ++ unorientedPairs xs

theorem unorientedPairs_vertices {xs : List V} {u v : V}
    (h : (u, v) ∈ unorientedPairs xs) : u ∈ xs ∧ v ∈ xs := by
  induction xs with
  | nil => simp [unorientedPairs] at h
  | cons a xs ih =>
    simp only [unorientedPairs, List.mem_append, List.mem_map, Prod.mk.injEq] at h
    rcases h with ⟨b, hb, rfl, rfl⟩ | ht
    · exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ hb⟩
    · exact ⟨List.mem_cons_of_mem _ (ih ht).1, List.mem_cons_of_mem _ (ih ht).2⟩

theorem unorientedPairs_complete {xs : List V} {u v : V} (hu : u ∈ xs)
    (hv : v ∈ xs) (huv : u ≠ v) :
    (u, v) ∈ unorientedPairs xs ∨ (v, u) ∈ unorientedPairs xs := by
  induction xs with
  | nil => simp at hu
  | cons a xs ih =>
    rcases List.mem_cons.mp hu with he | hu'
    · subst a
      have hv' := (List.mem_cons.mp hv).resolve_left (Ne.symm huv)
      exact Or.inl (List.mem_append_left _ (List.mem_map.mpr ⟨v, hv', rfl⟩))
    · rcases List.mem_cons.mp hv with he | hv'
      · subst a
        exact Or.inr (List.mem_append_left _ (List.mem_map.mpr ⟨u, hu', rfl⟩))
      · exact (ih hu' hv').imp (List.mem_append_right _) (List.mem_append_right _)

theorem unorientedPairs_noReverse {xs : List V} (hn : xs.Nodup) {u v : V}
    (h : (u, v) ∈ unorientedPairs xs) : (v, u) ∉ unorientedPairs xs := by
  induction xs with
  | nil => simp [unorientedPairs] at h
  | cons a xs ih =>
    obtain ⟨ha, hxs⟩ := List.nodup_cons.mp hn
    intro hr
    simp only [unorientedPairs, List.mem_append, List.mem_map, Prod.mk.injEq] at h hr
    rcases h with ⟨b, hb, e₁, e₂⟩ | ht
    · subst u
      subst v
      rcases hr with ⟨c, hc, e₁, _⟩ | hrt
      · exact ha (e₁ ▸ hb)
      · exact ha (unorientedPairs_vertices hrt).2
    · rcases hr with ⟨b, _, e₁, _⟩ | hrt
      · exact ha (e₁ ▸ (unorientedPairs_vertices ht).2)
      · exact ih hxs ht hrt

theorem unorientedPairs_nodup {xs : List V} (hn : xs.Nodup) :
    (unorientedPairs xs).Nodup := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons a xs ih =>
    obtain ⟨ha, hxs⟩ := List.nodup_cons.mp hn
    apply List.pairwise_append.mpr
    refine ⟨List.pairwise_map.mpr (hxs.imp (fun hn he => hn (congrArg Prod.snd he))),
      ih hxs, ?_⟩
    intro p hp q hq he
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hp
    subst q
    exact ha (unorientedPairs_vertices hq).1

theorem markedOnPairs_eq_sum (w : V → V → Nat) (xs : List V) :
    markedOnPairs w xs = nsum (unorientedPairs xs) (fun e => w e.1 e.2) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [markedOnPairs, unorientedPairs, ih, nsum, List.map_map,
      Function.comp_def]

def chosenRedPairs (G : MarkedGraph V) : List (V × V) :=
  (unorientedPairs G.host.vertices).filter (fun e => decide (0 < G.marked e.1 e.2))

theorem mem_chosenRedPairs_iff (G : MarkedGraph V) (u v : V) :
    (u, v) ∈ G.chosenRedPairs ↔
      (u, v) ∈ unorientedPairs G.host.vertices ∧ 0 < G.marked u v := by
  simp [chosenRedPairs]

theorem chosenRedPairs_vertices (G : MarkedGraph V) {u v : V}
    (h : (u, v) ∈ G.chosenRedPairs) : u ∈ G.host.vertices ∧ v ∈ G.host.vertices :=
  unorientedPairs_vertices ((G.mem_chosenRedPairs_iff u v).mp h).1

theorem chosenRedPairs_nodup (G : MarkedGraph V) : G.chosenRedPairs.Nodup :=
  (unorientedPairs_nodup G.host.nodup).filter _

theorem chosenRedPairs_noReverse (G : MarkedGraph V) {u v : V}
    (h : (u, v) ∈ G.chosenRedPairs) : (v, u) ∉ G.chosenRedPairs := by
  intro hr
  exact unorientedPairs_noReverse G.host.nodup ((G.mem_chosenRedPairs_iff u v).mp h).1
    ((G.mem_chosenRedPairs_iff v u).mp hr).1

theorem chosenRedPairs_distinct (G : MarkedGraph V) {u v : V}
    (h : (u, v) ∈ G.chosenRedPairs) : u ≠ v := by
  rintro rfl
  exact G.chosenRedPairs_noReverse h h

theorem chosenRedPairs_complete (G : MarkedGraph V) {u v : V} (h : 0 < G.marked u v) :
    (u, v) ∈ G.chosenRedPairs ∨ (v, u) ∈ G.chosenRedPairs := by
  have hne : u ≠ v := by
    rintro rfl
    simp [G.marked_loopless] at h
  have hs := (G.marked_symm u v) ▸ h
  exact (unorientedPairs_complete (G.host.complete u) (G.host.complete v) hne).imp
    (fun hp => (G.mem_chosenRedPairs_iff u v).mpr ⟨hp, h⟩)
    (fun hp => (G.mem_chosenRedPairs_iff v u).mpr ⟨hp, hs⟩)

private theorem sum_indicator_eq_filter_length (xs : List A) (p : A → Prop)
    [DecidablePred p] :
    nsum xs (fun a => if p a then 1 else 0) =
      (xs.filter (fun a => decide (p a))).length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => by_cases ha : p a <;> simp [ha, ih, Nat.add_comm]

theorem orientedBase_eq_twice_chosenRedPairs (G : MarkedGraph V) :
    G.orientedBase = 2 * G.chosenRedPairs.length := by
  have hsymm (u v : V) : G.base u v = G.base v u := by
    unfold base
    rw [G.marked_symm u v]
  have hloopless (u : V) : G.base u u = 0 := by simp [base, G.marked_loopless]
  unfold orientedBase
  rw [oriented_eq_twice_markedOnPairs G.base hsymm hloopless, markedOnPairs_eq_sum]
  unfold base chosenRedPairs
  exact congrArg (fun n => 2 * n)
    (sum_indicator_eq_filter_length _ (fun e : V × V => 0 < G.marked e.1 e.2))

end
end MarkedGraph
end FGST.Chapter3
