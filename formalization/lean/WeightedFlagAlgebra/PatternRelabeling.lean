import WeightedFlagAlgebra.WeightedCounts

namespace FGST.Chapter3

def relabelPattern (q : Fin n → Fin n) (F : Pattern n) : Pattern n :=
  fun i j => F (q i) (q j)

def relabelPairs (p : Fin n → Fin n) (J : List (Fin n × Fin n)) :
    List (Fin n × Fin n) :=
  J.map (fun e => (p e.1, p e.2))

private theorem pullMaps_perm (G : MarkedGraph V) (p q : Fin n → Fin n)
    (hqp : ∀ i, q (p i) = i) (hpq : ∀ i, p (q i) = i) :
    ((enumMaps G.host.vertices n).map (fun f => f ∘ q)).Perm
      (enumMaps G.host.vertices n) := by
  have hn := enumMaps_nodup G.host.vertices G.host.nodup n
  have hmap : ((enumMaps G.host.vertices n).map (fun f => f ∘ q)).Nodup := by
    apply List.pairwise_map.mpr
    exact hn.imp (fun hne he => hne (funext fun i => by
      simpa only [Function.comp_apply, hqp] using congrFun he (p i)))
  apply (List.perm_ext_iff_of_nodup hmap hn).mpr
  intro f
  refine ⟨fun _ => enumMaps_complete G.host.vertices G.host.complete n f, fun _ => ?_⟩
  exact List.mem_map.mpr
    ⟨f ∘ p, enumMaps_complete G.host.vertices G.host.complete n (f ∘ p),
      funext fun i => by simp only [Function.comp_apply, hpq]⟩

private theorem relabelPattern_realizes (G : MarkedGraph V) (F : Pattern n)
    (f : Fin n → V) (p q : Fin n → Fin n) (hqp : ∀ i, q (p i) = i) :
    relabelPattern q F = inducedPattern G (f ∘ q) ↔ F = inducedPattern G f := by
  constructor
  · intro h
    funext i j
    simpa only [relabelPattern, inducedPattern, Function.comp_apply, hqp] using
      congrFun (congrFun h (p i)) (p j)
  · intro h
    funext i j
    exact congrFun (congrFun h (q i)) (q j)

/-- Simultaneous relabeling of positions in the pattern and all specified pairs
preserves the exact count. The bijection moves positions, never host vertices. -/
theorem weightedCount_relabel (G : MarkedGraph V) (F : Pattern n)
    (J : List (Fin n × Fin n)) (p q : Fin n → Fin n)
    (hqp : ∀ i, q (p i) = i) (hpq : ∀ i, p (q i) = i) :
    weightedCount G (relabelPattern q F) (relabelPairs p J) = weightedCount G F J := by
  classical
  let w (f : Fin n → V) : Nat := if relabelPattern q F = inducedPattern G f then
    ((relabelPairs p J).map (fun e => G.extra (f e.1) (f e.2))).prod else 0
  unfold weightedCount
  change nsum (enumMaps G.host.vertices n) w = _
  rw [← nsum_perm _ _ (pullMaps_perm G p q hqp hpq) w, nsum_map]
  exact nsum_congr _ _ _ (fun f _ => by
    simp only [w, relabelPattern_realizes G F f p q hqp]
    simp only [relabelPairs, List.map_map, Function.comp_def, hqp])

theorem weightedDensity_relabel (G : MarkedGraph V) (D : Nat) (F : Pattern n)
    (J : List (Fin n × Fin n)) (p q : Fin n → Fin n)
    (hqp : ∀ i, q (p i) = i) (hpq : ∀ i, p (q i) = i) :
    weightedDensity G D (relabelPattern q F) (relabelPairs p J) = weightedDensity G D F J := by
  unfold weightedDensity
  rw [weightedCount_relabel G F J p q hqp hpq]

private theorem natProd_perm {xs ys : List Nat} (h : xs.Perm ys) : xs.prod = ys.prod := by
  induction h with
  | nil => rfl
  | cons a h ih => simp [ih]
  | swap a b xs => simp only [List.prod_cons, Nat.mul_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem weightedCount_pairs_perm (G : MarkedGraph V) (F : Pattern n)
    (J K : List (Fin n × Fin n)) (h : J.Perm K) :
    weightedCount G F J = weightedCount G F K := by
  unfold weightedCount
  apply nsum_congr
  intro f _
  split
  · exact natProd_perm (h.map (fun e => G.extra (f e.1) (f e.2)))
  · rfl

theorem weightedDensity_pairs_perm (G : MarkedGraph V) (D : Nat) (F : Pattern n)
    (J K : List (Fin n × Fin n)) (h : J.Perm K) :
    weightedDensity G D F J = weightedDensity G D F K := by
  unfold weightedDensity
  rw [weightedCount_pairs_perm G F J K h]

def canonicalPair (e : Fin n × Fin n) : Fin n × Fin n :=
  if e.2 < e.1 then (e.2, e.1) else e

theorem canonicalPair_original_or_swapped (e : Fin n × Fin n) :
    canonicalPair e = e ∨ canonicalPair e = (e.2, e.1) := by
  unfold canonicalPair
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

@[simp] theorem canonicalPair_swap (e : Fin n × Fin n) :
    canonicalPair (e.2, e.1) = canonicalPair e := by
  obtain ⟨u, v⟩ := e
  by_cases hvu : v < u
  · have hn : ¬ u < v := by omega
    simp [canonicalPair, hvu, hn]
  · by_cases huv : u < v
    · simp [canonicalPair, hvu, huv]
    · have he : u = v := by omega
      subst v
      rfl

theorem canonicalPair_eq_iff (e f : Fin n × Fin n) :
    canonicalPair e = canonicalPair f ↔ e = f ∨ e = (f.2, f.1) := by
  constructor
  · intro h
    rcases canonicalPair_original_or_swapped e with he | he <;>
      rcases canonicalPair_original_or_swapped f with hf | hf <;>
      rw [he, hf] at h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr (congrArg (fun a : Fin n × Fin n => (a.2, a.1)) h)
    · exact Or.inl (congrArg (fun a : Fin n × Fin n => (a.2, a.1)) h)
  · rintro (rfl | he)
    · rfl
    · rw [he, canonicalPair_swap]

private theorem extra_swap (G : MarkedGraph V) (u v : V) :
    G.extra u v = G.extra v u := by
  unfold MarkedGraph.extra
  rw [G.marked_symm u v]

theorem weightedCount_pairs_reorient (G : MarkedGraph V) (F : Pattern n)
    (J : List (Fin n × Fin n)) (orient : Fin n × Fin n → Fin n × Fin n)
    (h : ∀ e ∈ J, orient e = e ∨ orient e = (e.2, e.1)) :
    weightedCount G F (J.map orient) = weightedCount G F J := by
  unfold weightedCount
  apply nsum_congr
  intro f _
  split
  · simp only [List.map_map, Function.comp_def]
    congr 1
    exact List.map_congr_left (fun e he => by
      rcases h e he with ho | ho
      · rw [ho]
      · rw [ho]
        exact extra_swap G _ _)
  · rfl

/-- Comparing lists of specified pairs as multisets of unordered pairs. -/
theorem weightedCount_canonical (G : MarkedGraph V) (F : Pattern n)
    (J K : List (Fin n × Fin n)) (h : (J.map canonicalPair).Perm (K.map canonicalPair)) :
    weightedCount G F J = weightedCount G F K :=
  (weightedCount_pairs_reorient G F J canonicalPair
    (fun e _ => canonicalPair_original_or_swapped e)).symm.trans
    ((weightedCount_pairs_perm G F _ _ h).trans
      (weightedCount_pairs_reorient G F K canonicalPair
        (fun e _ => canonicalPair_original_or_swapped e)))

theorem weightedDensity_canonical (G : MarkedGraph V) (D : Nat) (F : Pattern n)
    (J K : List (Fin n × Fin n)) (h : (J.map canonicalPair).Perm (K.map canonicalPair)) :
    weightedDensity G D F J = weightedDensity G D F K := by
  unfold weightedDensity
  rw [weightedCount_canonical G F J K h]

def PairSupport (J : List (Fin n × Fin n)) (u v : Fin n) : Prop :=
  (u, v) ∈ J ∨ (v, u) ∈ J

private theorem mem_relabelPairs_iff (J : List (Fin n × Fin n)) (p q : Fin n → Fin n)
    (hqp : ∀ i, q (p i) = i) (hpq : ∀ i, p (q i) = i) (u v : Fin n) :
    (u, v) ∈ relabelPairs p J ↔ (q u, q v) ∈ J := by
  unfold relabelPairs
  constructor
  · intro h
    obtain ⟨e, he, h⟩ := List.mem_map.mp h
    have hu : e.1 = q u := by
      simpa only [hqp] using congrArg (fun x : Fin n × Fin n => q x.1) h
    have hv : e.2 = q v := by
      simpa only [hqp] using congrArg (fun x : Fin n × Fin n => q x.2) h
    rwa [← hu, ← hv]
  · intro h
    exact List.mem_map.mpr ⟨(q u, q v), h, by simp only [hpq]⟩

theorem pairSupport_relabel_iff (J : List (Fin n × Fin n)) (p q : Fin n → Fin n)
    (hqp : ∀ i, q (p i) = i) (hpq : ∀ i, p (q i) = i) (u v : Fin n) :
    PairSupport (relabelPairs p J) u v ↔ PairSupport J (q u) (q v) := by
  unfold PairSupport
  rw [mem_relabelPairs_iff J p q hqp hpq, mem_relabelPairs_iff J p q hqp hpq]

theorem canonicalPair_map_of_increasing (J : List (Fin n × Fin n))
    (h : ∀ e ∈ J, e.1 < e.2) : J.map canonicalPair = J := by
  refine Eq.trans (b := J.map id) ?_ (by simp)
  apply List.map_congr_left
  intro e he
  have hs := h e he
  have hn : ¬ e.2 < e.1 := by omega
  simp [canonicalPair, hn]

theorem canonicalPairs_nodup_relabel (J : List (Fin n × Fin n)) (p q : Fin n → Fin n)
    (hqp : ∀ i, q (p i) = i) (h : (J.map canonicalPair).Nodup) :
    ((relabelPairs p J).map canonicalPair).Nodup := by
  unfold relabelPairs
  simp only [List.map_map, List.Nodup, List.pairwise_map] at h ⊢
  apply h.imp
  intro e f hne heq
  apply hne
  apply (canonicalPair_eq_iff e f).mpr
  change canonicalPair (p e.1, p e.2) = canonicalPair (p f.1, p f.2) at heq
  rcases (canonicalPair_eq_iff _ _).mp heq with same | reversed
  · exact Or.inl (Prod.ext
      (by simpa only [hqp] using congrArg (fun x : Fin n × Fin n => q x.1) same)
      (by simpa only [hqp] using congrArg (fun x : Fin n × Fin n => q x.2) same))
  · exact Or.inr (Prod.ext
      (by simpa only [hqp] using congrArg (fun x : Fin n × Fin n => q x.1) reversed)
      (by simpa only [hqp] using congrArg (fun x : Fin n × Fin n => q x.2) reversed))

theorem canonicalPair_lists_perm_of_support (J K : List (Fin n × Fin n))
    (hJ : (J.map canonicalPair).Nodup) (hK : (K.map canonicalPair).Nodup)
    (hs : ∀ u v, PairSupport J u v ↔ PairSupport K u v) :
    (J.map canonicalPair).Perm (K.map canonicalPair) := by
  apply (List.perm_ext_iff_of_nodup hJ hK).mpr
  intro e
  constructor
  · intro he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    rcases (hs x.1 x.2).mp (Or.inl (by simpa using hx)) with hy | hy
    · exact List.mem_map.mpr ⟨x, by simpa using hy, rfl⟩
    · exact List.mem_map.mpr ⟨(x.2, x.1), hy, canonicalPair_swap x⟩
  · intro he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    rcases (hs x.1 x.2).mpr (Or.inl (by simpa using hx)) with hy | hy
    · exact List.mem_map.mpr ⟨x, by simpa using hy, rfl⟩
    · exact List.mem_map.mpr ⟨(x.2, x.1), hy, canonicalPair_swap x⟩

theorem canonicalPairs_nodup (J : List (Fin n × Fin n))
    (h : J.Pairwise (fun e f => e ≠ f ∧ e ≠ (f.2, f.1))) :
    (J.map canonicalPair).Nodup :=
  List.pairwise_map.mpr (h.imp (fun ⟨h₁, h₂⟩ he =>
    ((canonicalPair_eq_iff _ _).mp he).elim h₁ h₂))

end FGST.Chapter3
