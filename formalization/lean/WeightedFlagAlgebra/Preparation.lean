import WeightedFlagAlgebra.MarkedHost
import WeightedFlagAlgebra.Regularization

namespace FGST.Chapter3.MarkedGraph

abbrev IsMarkedEndpoint (G : MarkedGraph V) (v : V) : Prop := 0 < G.redDegree v

theorem endpoint_of_mark (G : MarkedGraph V) (u v : V) (h : 0 < G.marked u v) :
    G.IsMarkedEndpoint u := Nat.lt_of_lt_of_le h
  (term_le_nsum _ _ v (G.host.complete v))

def markedEndpointVertices (G : MarkedGraph V) : List {v // G.IsMarkedEndpoint v} :=
  (G.host.vertices.filter (fun v => decide (0 < G.redDegree v))).attachWith
    (fun v => G.IsMarkedEndpoint v) (fun _ h => of_decide_eq_true (List.mem_filter.mp h).2)

/-- The induced host on endpoints of marked edge instances. -/
def restrictToMarkedEndpoints (G : MarkedGraph V) : MarkedGraph {v // G.IsMarkedEndpoint v} where
  host := {
    vertices := G.markedEndpointVertices
    complete := fun x => (List.mem_attachWith _ x).mpr (List.mem_filter.mpr
      ⟨G.host.complete x.val, decide_eq_true x.property⟩)
    nodup := by
      have hd := G.host.nodup.filter (fun v => decide (0 < G.redDegree v))
      have h : G.markedEndpointVertices.unattach.Nodup := by
        simpa only [markedEndpointVertices, List.unattach_attachWith, List.Nodup] using hd
      have hp := List.pairwise_map.mp h
      exact hp.imp (fun h he => h (congrArg Subtype.val he))
    multiplicity := fun x y => G.host.multiplicity x.val y.val
    symmetric := fun x y => G.host.symmetric x.val y.val
    loopless := fun x => G.host.loopless x.val
  }
  marked := fun x y => G.marked x.val y.val
  marked_le := fun x y => G.marked_le x.val y.val
  marked_symm := fun x y => G.marked_symm x.val y.val

theorem restrict_endpoints_strong (G : MarkedGraph V) (hs : G.Strong) :
    G.restrictToMarkedEndpoints.Strong := by
  intro a b c d h₁ h₂ h₃ h₄ h₅ h₆
  exact hs a.val b.val c.val d.val h₁ h₂
    (fun h => h₃ (Subtype.ext h)) (fun h => h₄ (Subtype.ext h))
    (fun h => h₅ (Subtype.ext h)) (fun h => h₆ (Subtype.ext h))

private theorem nsum_marked_endpoints (G : MarkedGraph V) (f : V → Nat) :
    nsum G.markedEndpointVertices (fun a => f a.val) =
      nsum G.host.vertices (fun a => if 0 < G.redDegree a then f a else 0) := by
  unfold nsum
  rw [List.map_subtype (g := f) (by intros; rfl)]
  simp only [markedEndpointVertices, List.unattach_attachWith]
  simpa only [nsum, decide_eq_true_eq] using
    nsum_filter G.host.vertices (fun v => decide (0 < G.redDegree v)) f

theorem restrict_endpoints_degree_le (G : MarkedGraph V) (v : {v // G.IsMarkedEndpoint v}) :
    G.restrictToMarkedEndpoints.host.degree v ≤ G.host.degree v.val := by
  change nsum G.markedEndpointVertices (fun a => G.host.multiplicity v.val a.val) ≤ _
  rw [G.nsum_marked_endpoints]
  apply nsum_le
  intro a _
  split <;> omega

theorem restrict_endpoints_orientedMarked (G : MarkedGraph V) :
    G.restrictToMarkedEndpoints.orientedMarked = G.orientedMarked := by
  have hrow : ∀ v : {v // G.IsMarkedEndpoint v},
      G.restrictToMarkedEndpoints.redDegree v = G.redDegree v.val := by
    intro v
    change nsum G.markedEndpointVertices (fun a => G.marked v.val a.val) = _
    rw [G.nsum_marked_endpoints]
    apply nsum_congr
    intro a _
    by_cases h : 0 < G.redDegree a
    · exact if_pos h
    · have hz : G.marked v.val a = 0 := Nat.eq_zero_of_not_pos (fun hn =>
        h (G.endpoint_of_mark _ _ (by rw [G.marked_symm]; exact hn)))
      simp [hz]
  change nsum G.markedEndpointVertices G.restrictToMarkedEndpoints.redDegree = _
  rw [nsum_congr _ _ _ (fun v _ => hrow v), G.nsum_marked_endpoints]
  apply nsum_congr
  intro x _
  split <;> omega

def Reduced (G : MarkedGraph V) : Prop :=
  ∀ u v, G.reducedMultiplicity u v = G.host.multiplicity u v

theorem reduceParallel_reduced (G : MarkedGraph V) : G.reduceParallel.Reduced := by
  intro u v
  change G.marked u v + G.reduceParallel.blue u v = G.marked u v + G.blue u v
  unfold blue
  have heq : G.reduceParallel.color u v = G.color u v := by
    unfold color
    change (if 0 < G.marked u v then EdgeColor.red else
      if G.reduceParallel.Adj u v then EdgeColor.blue else EdgeColor.absent) = _
    by_cases hg : G.Adj u v
    · simp only [if_pos hg, if_pos ((G.reduceParallel_adj u v).mpr hg)]
    · simp only [if_neg hg, if_neg (fun h => hg ((G.reduceParallel_adj u v).mp h))]
  rw [heq]

private noncomputable def preimage (embed : V → W) (w : W) : Option V := by
  classical
  exact if h : ∃ v, embed v = w then some (Classical.choose h) else none

private theorem preimage_spec (embed : V → W) (w : W) (v : V) :
    preimage embed w = some v → embed v = w := by
  classical
  unfold preimage
  split
  · rename_i h
    intro heq
    rw [← Option.some.inj heq]
    exact Classical.choose_spec h
  · simp

private theorem preimage_embed (embed : V → W) (hei : Function.Injective embed) (v : V) :
    preimage embed (embed v) = some v := by
  classical
  unfold preimage
  rw [dif_pos (show ∃ x, embed x = embed v from ⟨v, rfl⟩)]
  congr 1
  exact hei (Classical.choose_spec (show ∃ x, embed x = embed v from ⟨v, rfl⟩))

private theorem preimage_none (embed : V → W) (w : W) :
    preimage embed w = none ↔ ¬∃ v, embed v = w := by
  classical
  unfold preimage
  split <;> simp_all

/-- Extend the markings on an induced subgraph by giving every new edge no mark. -/
noncomputable def extendMarks (G : MarkedGraph V) (H : FiniteMultigraph W) (embed : V → W)
    (he : G.host.SimpleExtension H embed) : MarkedGraph W where
  host := H
  marked := fun x y =>
    match preimage embed x, preimage embed y with
    | some a, some b => G.marked a b
    | _, _ => 0
  marked_le x y := by
    cases hx : preimage embed x with
    | none => simp
    | some a =>
      cases hy : preimage embed y with
      | none => simp
      | some b =>
        rw [← preimage_spec _ _ _ hx, ← preimage_spec _ _ _ hy, he.induced]
        exact G.marked_le a b
  marked_symm x y := by
    cases preimage embed x <;> cases preimage embed y <;> simp [G.marked_symm]

@[simp] theorem extend_marks_old (G : MarkedGraph V) (H : FiniteMultigraph W) (embed : V → W)
    (he : G.host.SimpleExtension H embed) (u v : V) :
    (G.extendMarks H embed he).marked (embed u) (embed v) = G.marked u v := by
  simp [extendMarks, preimage_embed embed he.injective]

theorem extend_marks_strong (G : MarkedGraph V) (hs : G.Strong)
    (H : FiniteMultigraph W) (embed : V → W) (he : G.host.SimpleExtension H embed) :
    (G.extendMarks H embed he).Strong := by
  intro a b c d h₁ h₂ h₃ h₄ h₅ h₆
  have hasOld (x y : W) (hx : 0 < (G.extendMarks H embed he).marked x y) :
      ∃ u v : V, embed u = x ∧ embed v = y := by
    simp only [extendMarks] at hx
    cases hₓ : preimage embed x with
    | none => simp [hₓ] at hx
    | some u =>
      cases hᵧ : preimage embed y with
      | none => simp [hₓ, hᵧ] at hx
      | some v => exact ⟨u, v, preimage_spec _ _ _ hₓ, preimage_spec _ _ _ hᵧ⟩
  obtain ⟨x, y, rfl, rfl⟩ := hasOld a b h₁
  obtain ⟨z, w, rfl, rfl⟩ := hasOld c d h₂
  simp only [extend_marks_old] at h₁ h₂
  simpa only [Adj, extendMarks, he.induced] using
    hs x y z w h₁ h₂ (fun h => h₃ (congrArg embed h)) (fun h => h₄ (congrArg embed h))
      (fun h => h₅ (congrArg embed h)) (fun h => h₆ (congrArg embed h))

/-- Sum over an induced embedding after all newly added vertices contribute zero. -/
private theorem sum_extend_zero (old : FiniteMultigraph V) (new : FiniteMultigraph W)
    (embed : V → W) (hm : Function.Injective embed) (f : W → Nat)
    (hz : ∀ w, preimage embed w = none → f w = 0) :
    nsum new.vertices f = nsum old.vertices (fun v => f (embed v)) := by
  classical
  let keep : W → Bool := fun w => decide (∃ v, embed v = w)
  have hkeep : (new.vertices.filter keep).Nodup := new.nodup.filter keep
  have hmapped : (old.vertices.map embed).Nodup :=
    List.pairwise_map.mpr (old.nodup.imp (fun h he => h (hm he)))
  have hp : (new.vertices.filter keep).Perm (old.vertices.map embed) := by
    apply (List.perm_ext_iff_of_nodup hkeep hmapped).mpr
    intro w
    simp only [List.mem_filter, List.mem_map, keep, decide_eq_true_eq]
    constructor
    · rintro ⟨_, v, hv⟩
      exact ⟨v, old.complete v, hv⟩
    · rintro ⟨v, _, hv⟩
      exact ⟨new.complete w, v, hv⟩
  rw [← nsum_map old.vertices embed f, ← nsum_perm _ _ hp, nsum_filter]
  apply nsum_congr
  intro w _
  by_cases hw : ∃ v, embed v = w
  · simp [keep, hw]
  · simp [keep, hw, hz w ((preimage_none embed w).mpr hw)]

theorem extend_marks_orientedMarked (G : MarkedGraph V) (H : FiniteMultigraph W)
    (embed : V → W) (he : G.host.SimpleExtension H embed) :
    (G.extendMarks H embed he).orientedMarked = G.orientedMarked := by
  let ext := G.extendMarks H embed he
  change nsum H.vertices ext.redDegree = _
  rw [sum_extend_zero G.host H embed he.injective]
  · apply nsum_congr
    intro v _
    change nsum H.vertices (ext.marked (embed v)) = _
    rw [sum_extend_zero G.host H embed he.injective]
    · exact nsum_congr _ _ _ (fun u _ => G.extend_marks_old H embed he v u)
    · intro u hu
      simp [ext, extendMarks, hu, preimage_embed embed he.injective]
  · intro w hw
    change nsum H.vertices (ext.marked w) = 0
    simp [ext, extendMarks, hw, nsum_const]

theorem extend_marks_reduced (G : MarkedGraph V) (hr : G.Reduced)
    (H : FiniteMultigraph W) (embed : V → W) (he : G.host.SimpleExtension H embed) :
    (G.extendMarks H embed he).Reduced := by
  intro x y
  let ext := G.extendMarks H embed he
  have old (u v : V) : ext.reducedMultiplicity (embed u) (embed v) =
      H.multiplicity (embed u) (embed v) := by
    have hx : ext.marked (embed u) (embed v) = G.marked u v := G.extend_marks_old H embed he u v
    have hy : ext.host.multiplicity (embed u) (embed v) = G.host.multiplicity u v := he.induced u v
    simpa only [reducedMultiplicity, blue, color, Adj, hx, hy, he.induced] using hr u v
  have fresh (hm : ext.marked x y = 0) (hz : H.multiplicity x y ≤ 1) :
      ext.reducedMultiplicity x y = H.multiplicity x y := by
    have hy : ext.host.multiplicity x y = H.multiplicity x y := rfl
    by_cases hg : 0 < H.multiplicity x y
    · simp [reducedMultiplicity, blue, color, hm, hy, show H.multiplicity x y = 1 by omega]
    · simp [reducedMultiplicity, blue, color, hm, hy, show H.multiplicity x y = 0 by omega]
  cases hx : preimage embed x with
  | none =>
    exact fresh (by simp [ext, extendMarks, hx])
      (he.new_simple x y (.inl ((preimage_none embed x).mp hx)))
  | some u =>
    cases hy : preimage embed y with
    | none =>
      exact fresh (by simp [ext, extendMarks, hx, hy])
        (he.new_simple x y (.inr ((preimage_none embed y).mp hy)))
    | some v =>
      rw [← preimage_spec _ _ _ hx, ← preimage_spec _ _ _ hy]
      exact old u v

/-- The full preprocessing in §3.1 preserves the clique size and gives a reduced,
regular host with a single incident instance for every blue pair. -/
theorem exists_preparedHost {V : Type u} (G : MarkedGraph V) (D : Nat) (hD : 0 < D)
    (hs : G.Strong) (hb : ∀ v, G.host.degree v ≤ D) :
    ∃ (W : Type u) (H : MarkedGraph W),
      H.Strong ∧ H.orientedMarked = G.orientedMarked ∧ H.Reduced ∧
        ∀ w, nsum H.host.vertices (H.reducedMultiplicity w) = D := by
  let S := G.restrictToMarkedEndpoints
  let R := S.reduceParallel
  have hbound (x : {v // G.IsMarkedEndpoint v}) : R.host.degree x ≤ D :=
    Nat.le_trans (S.reduceParallel_degree_le x)
      (Nat.le_trans (G.restrict_endpoints_degree_le x) (hb x.val))
  obtain ⟨W, H, embed, he, hregular⟩ := R.host.exists_regularization D hD hbound
  let T := R.extendMarks H embed he
  have hr : T.Reduced := R.extend_marks_reduced S.reduceParallel_reduced H embed he
  have hm : T.orientedMarked = G.orientedMarked := by
    rw [R.extend_marks_orientedMarked H embed he]
    exact G.restrict_endpoints_orientedMarked
  refine ⟨W, T, R.extend_marks_strong
    (S.reduceParallel_strong.mpr (G.restrict_endpoints_strong hs)) H embed he, hm, hr, ?_⟩
  intro w
  rw [nsum_congr _ _ _ (fun v _ => hr w v)]
  exact hregular w

end FGST.Chapter3.MarkedGraph
