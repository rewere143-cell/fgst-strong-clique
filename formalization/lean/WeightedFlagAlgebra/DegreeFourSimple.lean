import Std

namespace FGST.Chapter3.DegreeFour

universe u v

/-- A finite simple support with one stored orientation of each red edge. The
    strong-clique condition is stated as cross adjacency. For intersecting red
    edges this follows from the red edges themselves. -/
structure Graph (V : Type u) where
  vertices : List V
  verticesNodup : vertices.Nodup
  adjacent : V → V → Bool
  symmetric : ∀ x y, adjacent x y = adjacent y x
  loopless : ∀ x, adjacent x x = false
  redEdges : List (V × V)
  redNodup : redEdges.Nodup
  redOrientation : ∀ {x y}, (x, y) ∈ redEdges → (y, x) ∉ redEdges
  redAdjacent : ∀ e ∈ redEdges, adjacent e.1 e.2 = true
  redVertices : ∀ e ∈ redEdges, e.1 ∈ vertices ∧ e.2 ∈ vertices
  strong : ∀ e ∈ redEdges, ∀ f ∈ redEdges,
    adjacent e.1 f.1 = true ∨ adjacent e.1 f.2 = true ∨
      adjacent e.2 f.1 = true ∨ adjacent e.2 f.2 = true

section FiniteSums

variable {A : Type u} {B : Type v}

private def total (xs : List A) (f : A → Nat) : Nat :=
  (xs.map f).sum

@[simp] private theorem total_nil (f : A → Nat) : total [] f = 0 := rfl

@[simp] private theorem total_cons (a : A) (xs : List A) (f : A → Nat) :
    total (a :: xs) f = f a + total xs f := rfl

private theorem total_congr (xs : List A) {f g : A → Nat}
    (h : ∀ a ∈ xs, f a = g a) : total xs f = total xs g := by
  unfold total
  rw [List.map_congr_left h]

private theorem total_mono (xs : List A) {f g : A → Nat}
    (h : ∀ a ∈ xs, f a ≤ g a) : total xs f ≤ total xs g := by
  induction xs with
  | nil => simp [total]
  | cons a xs ih =>
    simp only [total, List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

private theorem total_add (xs : List A) (f g : A → Nat) :
    total xs (fun a => f a + g a) = total xs f + total xs g := by
  induction xs with
  | nil => simp [total]
  | cons a xs ih =>
    simp only [total, List.map_cons, List.sum_cons] at *
    omega

private theorem total_const (xs : List A) (c : Nat) :
    total xs (fun _ => c) = xs.length * c := by
  induction xs with
  | nil => simp [total]
  | cons a xs ih =>
    rw [total_cons, ih]
    simp [Nat.add_mul, Nat.add_comm]

private theorem total_mul (xs : List A) (c : Nat) (f : A → Nat) :
    total xs (fun a => c * f a) = c * total xs f := by
  induction xs with
  | nil => simp [total]
  | cons a xs ih =>
    simp [Nat.mul_add, ih]

private theorem total_swap (xs : List A) (ys : List B) (f : A → B → Nat) :
    total xs (fun a => total ys (f a)) =
      total ys (fun b => total xs (fun a => f a b)) := by
  induction xs with
  | nil => simp [total_const]
  | cons a xs ih =>
    change total ys (f a) + total xs (fun a => total ys (f a)) =
      total ys (fun b => f a b + total xs (fun a => f a b))
    rw [total_add, ih]

private theorem total_filter (xs : List A) (p : A → Bool) (f : A → Nat) :
    total (xs.filter p) f = total xs (fun a => if p a then f a else 0) := by
  induction xs with
  | nil => simp [total]
  | cons a xs ih =>
    cases h : p a <;> simp [h, ih]

private theorem card_as_total (xs : List A) (p : A → Bool) :
    (xs.filter p).length = total xs (fun a => if p a then 1 else 0) := by
  have h := total_filter xs p (fun _ => 1)
  simpa only [total_const, Nat.mul_one] using h

private theorem card_of_mono (xs : List A) {p q : A → Bool}
    (h : ∀ a ∈ xs, p a = true → q a = true) :
    (xs.filter p).length ≤ (xs.filter q).length := by
  rw [card_as_total, card_as_total]
  apply total_mono
  intro a ha
  cases hp : p a
  · simp
  · simp [h a ha hp]

private theorem card_of_equiv (xs : List A) {p q : A → Bool}
    (h : ∀ a ∈ xs, p a = true ↔ q a = true) :
    (xs.filter p).length = (xs.filter q).length :=
  Nat.le_antisymm (card_of_mono xs (fun a ha => (h a ha).mp))
    (card_of_mono xs (fun a ha => (h a ha).mpr))

private theorem filter_nodup {xs : List A} (h : xs.Nodup) (p : A → Bool) :
    (xs.filter p).Nodup :=
  h.sublist List.filter_sublist

private theorem map_nodup_on {xs : List A} (h : xs.Nodup) (f : A → B)
    (hi : ∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b) : (xs.map f).Nodup := by
  apply List.pairwise_map.mpr
  exact h.imp_of_mem (fun ha hb hne heq => hne (hi _ ha _ hb heq))

private theorem card_by_membership {xs ys : List A} (hx : xs.Nodup) (hy : ys.Nodup)
    (h : ∀ a, a ∈ xs ↔ a ∈ ys) : xs.length = ys.length :=
  ((List.perm_ext_iff_of_nodup hx hy).mpr h).length_eq

end FiniteSums

section Counts

variable {V : Type u} [DecidableEq V] (G : Graph V)

def Graph.neighbors (x : V) : List V :=
  G.vertices.filter (G.adjacent x)

def Graph.degree (x : V) : Nat :=
  (G.neighbors x).length

def touches (x : V) (e : V × V) : Bool :=
  decide (e.1 = x ∨ e.2 = x)

def opposite (x : V) (e : V × V) : V :=
  if e.1 = x then e.2 else e.1

def Graph.redDegree (x : V) : Nat :=
  (G.redEdges.filter (touches x)).length

omit [DecidableEq V] in
private theorem Graph.red_ne {e : V × V} (he : e ∈ G.redEdges) :
    e.1 ≠ e.2 := by
  intro h
  have hadj := G.redAdjacent e he
  rw [h, G.loopless] at hadj
  cases hadj

omit [DecidableEq V] in
private theorem Graph.edge_symmetric {e : V × V} (he : e ∈ G.redEdges) :
    G.adjacent e.2 e.1 = true := by
  rw [G.symmetric]
  exact G.redAdjacent e he

omit [DecidableEq V] in
private theorem Graph.same_unordered {e f : V × V}
    (he : e ∈ G.redEdges) (hf : f ∈ G.redEdges)
    (h : e = f ∨ (e.2, e.1) = f) : e = f := by
  rcases h with h | h
  · exact h
  · rcases e with ⟨a, b⟩
    exact (G.redOrientation he (h ▸ hf)).elim

private theorem Graph.opposite_adj {x : V} {e : V × V}
    (he : e ∈ G.redEdges) (ht : touches x e = true) :
    opposite x e ∈ G.neighbors x := by
  have hp := G.redVertices e he
  simp only [touches, decide_eq_true_eq] at ht
  simp only [Graph.neighbors, List.mem_filter, opposite]
  by_cases h : e.1 = x
  · rw [if_pos h]
    exact ⟨hp.2, h ▸ G.redAdjacent e he⟩
  · rw [if_neg h]
    have hx := ht.resolve_left h
    exact ⟨hp.1, hx ▸ G.edge_symmetric he⟩

private theorem Graph.opposite_injective {x : V} {e f : V × V}
    (he : e ∈ G.redEdges) (hf : f ∈ G.redEdges)
    (hte : touches x e = true) (htf : touches x f = true)
    (h : opposite x e = opposite x f) : e = f := by
  rcases e with ⟨a, b⟩
  rcases f with ⟨c, d⟩
  simp only [touches, decide_eq_true_eq, opposite] at *
  apply G.same_unordered he hf
  by_cases ha : a = x
  · by_cases hc : c = x
    · simp only [if_pos ha, if_pos hc] at h
      exact .inl (Prod.ext (ha.trans hc.symm) h)
    · simp only [if_pos ha, if_neg hc] at h
      exact .inr (Prod.ext h (ha.trans (htf.resolve_left hc).symm))
  · by_cases hc : c = x
    · simp only [if_neg ha, if_pos hc] at h
      exact .inr (Prod.ext ((hte.resolve_left ha).trans hc.symm) h)
    · simp only [if_neg ha, if_neg hc] at h
      exact .inl (Prod.ext h ((hte.resolve_left ha).trans (htf.resolve_left hc).symm))

theorem Graph.redDegree_le_degree (x : V) : G.redDegree x ≤ G.degree x := by
  let rs := G.redEdges.filter (touches x)
  let ns := rs.map (opposite x)
  have hn : ns.Nodup := map_nodup_on (filter_nodup G.redNodup _) _ (by
    intro e he f hf h
    exact G.opposite_injective (List.mem_filter.mp he).1 (List.mem_filter.mp hf).1
      (List.mem_filter.mp he).2 (List.mem_filter.mp hf).2 h)
  have hs : ns ⊆ G.neighbors x := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
    exact G.opposite_adj (List.mem_filter.mp he).1 (List.mem_filter.mp he).2
  simpa only [ns, rs, List.length_map, Graph.redDegree, Graph.degree] using
    hn.length_le_of_subset hs

/-- The neighbors of the two roots, with both roots omitted. -/
def Graph.rootNeighbors (x y : V) : List V :=
  G.vertices.filter fun z => decide (z ≠ x ∧ z ≠ y) &&
    (G.adjacent x z || G.adjacent y z)

private theorem Graph.rootNeighbors_mem {x y z : V} :
    z ∈ G.rootNeighbors x y ↔
      z ∈ G.vertices ∧ z ≠ x ∧ z ≠ y ∧
        (G.adjacent x z = true ∨ G.adjacent y z = true) := by
  simp only [Graph.rootNeighbors, List.mem_filter, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, and_assoc]

theorem Graph.rootNeighbors_bound {e : V × V} (he : e ∈ G.redEdges) :
    (G.rootNeighbors e.1 e.2).length + 2 ≤ G.degree e.1 + G.degree e.2 := by
  let left := G.neighbors e.1
  let right := G.neighbors e.2
  have hleft : e.2 ∈ left := List.mem_filter.mpr ⟨(G.redVertices e he).2, G.redAdjacent e he⟩
  have hright : e.1 ∈ right := List.mem_filter.mpr ⟨(G.redVertices e he).1, G.edge_symmetric he⟩
  have hsub : G.rootNeighbors e.1 e.2 ⊆ left.erase e.2 ++ right.erase e.1 := by
    intro z hz
    obtain ⟨hv, hne1, hne2, hadj⟩ := G.rootNeighbors_mem.mp hz
    apply List.mem_append.mpr
    rcases hadj with hl | hr
    · exact .inl (List.mem_erase_of_ne hne2 |>.mpr (List.mem_filter.mpr ⟨hv, hl⟩))
    · exact .inr (List.mem_erase_of_ne hne1 |>.mpr (List.mem_filter.mpr ⟨hv, hr⟩))
  have hsize := (filter_nodup G.verticesNodup _).length_le_of_subset hsub
  simp only [List.length_append, List.length_erase_of_mem hleft,
    List.length_erase_of_mem hright] at hsize
  have hleftpos := List.length_pos_iff.mpr (List.ne_nil_of_mem hleft)
  have hrightpos := List.length_pos_iff.mpr (List.ne_nil_of_mem hright)
  change (G.rootNeighbors e.1 e.2).length ≤ left.length - 1 + (right.length - 1) at hsize
  change (G.rootNeighbors e.1 e.2).length + 2 ≤ left.length + right.length
  omega

private theorem Graph.red_edge_meets_rootNeighbors {e f : V × V}
    (he : e ∈ G.redEdges) (hf : f ∈ G.redEdges) (hne : f ≠ e) :
    f.1 ∈ G.rootNeighbors e.1 e.2 ∨ f.2 ∈ G.rootNeighbors e.1 e.2 := by
  rcases e with ⟨a, b⟩
  rcases f with ⟨c, d⟩
  have hcd : c ≠ d := G.red_ne hf
  have hvertices := G.redVertices (c, d) hf
  have hdAdj : G.adjacent d c = true := G.edge_symmetric hf
  have hcAdj : G.adjacent c d = true := G.redAdjacent (c, d) hf
  have hnotBoth : ¬ ((c = a ∨ c = b) ∧ (d = a ∨ d = b)) := by
    intro h
    rcases h with ⟨hc | hc, hd | hd⟩
    · exact hcd (hc.trans hd.symm)
    · exact hne (Prod.ext hc hd)
    · exact hne (G.same_unordered hf he (.inr (Prod.ext hd hc)))
    · exact hcd (hc.trans hd.symm)
  change c ∈ G.rootNeighbors a b ∨ d ∈ G.rootNeighbors a b
  rw [G.rootNeighbors_mem, G.rootNeighbors_mem]
  by_cases hc : c = a ∨ c = b
  · have hdn := fun hd => hnotBoth ⟨hc, hd⟩
    refine .inr ⟨hvertices.2, fun h => hdn (.inl h), fun h => hdn (.inr h), ?_⟩
    rcases hc with h | h
    · exact .inl (h ▸ hcAdj)
    · exact .inr (h ▸ hcAdj)
  by_cases hd : d = a ∨ d = b
  · refine .inl ⟨hvertices.1, fun h => hc (.inl h), fun h => hc (.inr h), ?_⟩
    rcases hd with h | h
    · exact .inl (h ▸ hdAdj)
    · exact .inr (h ▸ hdAdj)
  rcases G.strong (a, b) he (c, d) hf with h | h | h | h
  · exact .inl ⟨hvertices.1, fun h => hc (.inl h), fun h => hc (.inr h), .inl h⟩
  · exact .inr ⟨hvertices.2, fun h => hd (.inl h), fun h => hd (.inr h), .inl h⟩
  · exact .inl ⟨hvertices.1, fun h => hc (.inl h), fun h => hc (.inr h), .inr h⟩
  · exact .inr ⟨hvertices.2, fun h => hd (.inl h), fun h => hd (.inr h), .inr h⟩

private theorem total_at_least_one {xs : List A} {f : A → Nat}
    {a : A} (ha : a ∈ xs) (hf : 1 ≤ f a) :
    1 ≤ total xs f := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    rcases List.mem_cons.mp ha with rfl | ht
    · simp only [total_cons]
      omega
    · have h := ih ht
      simp only [total_cons]
      omega

theorem Graph.redEdges_le_from_root {e : V × V} (he : e ∈ G.redEdges)
    (r : Nat) (hd : ∀ x ∈ G.rootNeighbors e.1 e.2, G.redDegree x ≤ r) :
    G.redEdges.length ≤ 1 + (G.rootNeighbors e.1 e.2).length * r := by
  let roots := G.rootNeighbors e.1 e.2
  let outside := G.redEdges.erase e
  have hl : outside.length + 1 = G.redEdges.length := by
    have hpos := List.length_pos_iff.mpr (List.ne_nil_of_mem he)
    simpa only [outside, List.length_erase_of_mem he] using
      (Nat.sub_add_cancel hpos : G.redEdges.length - 1 + 1 = G.redEdges.length)
  have hm : outside ⊆ G.redEdges := List.erase_sublist.subset
  have hc : outside.length ≤
      total outside (fun f => total roots (fun x => if touches x f then 1 else 0)) := by
    rw [← Nat.mul_one outside.length, ← total_const]
    apply total_mono
    intro f hf
    have hd := (G.redNodup.mem_erase_iff).mp hf
    rcases G.red_edge_meets_rootNeighbors he hd.2 hd.1 with h | h
    · apply total_at_least_one h
      simp [touches]
    · apply total_at_least_one h
      simp [touches]
  have hc' := total_swap outside roots (fun f x => if touches x f then 1 else 0)
  rw [hc'] at hc
  have hbound : total roots
      (fun x => total outside (fun f => if touches x f then 1 else 0)) ≤
      roots.length * r := by
    rw [← total_const]
    apply total_mono
    intro x hx
    rw [← card_as_total]
    have hs : outside.filter (touches x) ⊆ G.redEdges.filter (touches x) := by
      intro e he
      obtain ⟨hm', hfilter⟩ := List.mem_filter.mp he
      exact List.mem_filter.mpr ⟨hm hm', hfilter⟩
    have hn := filter_nodup (G.redNodup.erase e) (touches x)
    exact Nat.le_trans (hn.length_le_of_subset hs : _ ≤ G.redDegree x) (hd x hx)
  change G.redEdges.length ≤ 1 + roots.length * r
  omega

/-- Opening reduction of Theorem 3.9: a counterexample has red degree four
    at some vertex. This statement uses only the graph's actual edge lists. -/
theorem Graph.exists_redDegree_four (hmax : ∀ x, G.degree x ≤ 4)
    (hs : 21 ≤ G.redEdges.length) : ∃ x, G.redDegree x = 4 := by
  apply Classical.byContradiction
  intro hn
  have hall (x : V) : G.redDegree x ≤ 3 := by
    have hdeg := Nat.le_trans (G.redDegree_le_degree x) (hmax x)
    apply Classical.byContradiction
    intro he
    exact hn ⟨x, by omega⟩
  have hpos : 0 < G.redEdges.length := by omega
  obtain ⟨e, he⟩ : ∃ e, e ∈ G.redEdges := by
    cases h : G.redEdges with
    | nil => simp [h] at hpos
    | cons e es => exact ⟨e, by simp⟩
  have hq := G.rootNeighbors_bound he
  have hda := hmax e.1
  have hdb := hmax e.2
  have hbound := G.redEdges_le_from_root he 3 (fun x _ => hall x)
  omega

private theorem card_union_le {A : Type u} (xs : List A) (p q : A → Bool) :
    (xs.filter (fun a => p a || q a)).length ≤
      (xs.filter p).length + (xs.filter q).length := by
  calc
    _ = total xs (fun a => if p a || q a then 1 else 0) := card_as_total xs _
    _ ≤ total xs (fun a => (if p a then 1 else 0) + (if q a then 1 else 0)) :=
      total_mono xs (by intro a _; cases p a <;> cases q a <;> decide)
    _ = _ := by rw [total_add, ← card_as_total xs p, ← card_as_total xs q]

private theorem append_nodup_disjoint {xs ys : List A}
    (hx : xs.Nodup) (hy : ys.Nodup) (hd : ∀ a ∈ xs, a ∉ ys) : (xs ++ ys).Nodup := by
  exact List.nodup_append.mpr ⟨hx, hy, fun a ha b hb h => hd a ha (h ▸ hb)⟩

private theorem full_of_subset_length {xs ys : List V} (hx : xs.Nodup)
    (hsub : xs ⊆ ys) (hsize : ys.length ≤ xs.length) : ys ⊆ xs := by
  intro a ha
  by_cases hx' : a ∈ xs
  · exact hx'
  · have h' : a :: xs ⊆ ys := by
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · exact hsub hb
    have hlo := (List.nodup_cons.mpr ⟨hx', hx⟩).length_le_of_subset h'
    simp only [List.length_cons] at hlo
    omega

private theorem sum_matching (xs : List V) (h : xs.Nodup) (x : V) (c : Nat) :
    total xs (fun y => if y = x then c else 0) = if x ∈ xs then c else 0 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨hna, hnd⟩ := List.nodup_cons.mp h
    by_cases he : a = x
    · subst a
      simp [hna, ih hnd]
    · simp [he, Ne.symm he, ih hnd]

private theorem Graph.tally_red_incidence (xs : List V) (hxs : xs.Nodup) (weight : V → Nat) :
    total xs (fun x => weight x * G.redDegree x) =
      total G.redEdges (fun e => (if e.1 ∈ xs then weight e.1 else 0) +
        (if e.2 ∈ xs then weight e.2 else 0)) := by
  have hrow (x : V) : weight x * G.redDegree x =
      total G.redEdges (fun e => if touches x e then weight x else 0) := by
    unfold Graph.redDegree
    rw [card_as_total, ← total_mul]
    apply total_congr
    intro e _
    cases touches x e <;> simp
  have hmat := total_congr xs (fun x _ => hrow x)
  rw [hmat, total_swap]
  apply total_congr
  intro e he
  have hne := G.red_ne he
  have hpoint (x : V) :
      (if touches x e then weight x else 0) =
        (if x = e.1 then weight e.1 else 0) +
          (if x = e.2 then weight e.2 else 0) := by
    by_cases hx : x = e.1
    · subst x
      simp [touches, hne]
    by_cases hy : x = e.2
    · subst x
      simp [touches, hne, Ne.symm hne]
    simp [touches, hx, hy, Ne.symm hx, Ne.symm hy]
  rw [total_congr xs (fun x _ => hpoint x), total_add, sum_matching xs hxs, sum_matching xs hxs]

/-- Keep the edges and adjacencies induced by a list of distinct vertices. -/
def Graph.inducedOn (xs : List V) (hxs : xs.Nodup) : Graph V where
  vertices := xs
  verticesNodup := hxs
  adjacent := G.adjacent
  symmetric := G.symmetric
  loopless := G.loopless
  redEdges := G.redEdges.filter (fun e => decide (e.1 ∈ xs ∧ e.2 ∈ xs))
  redNodup := filter_nodup G.redNodup _
  redOrientation he hf := G.redOrientation (List.mem_filter.mp he).1 (List.mem_filter.mp hf).1
  redAdjacent e he := G.redAdjacent e (List.mem_filter.mp he).1
  redVertices _e he := of_decide_eq_true (List.mem_filter.mp he).2
  strong e he f hf := G.strong e (List.mem_filter.mp he).1 f (List.mem_filter.mp hf).1

private theorem Graph.induced_red_mem {xs : List V} {hxs : xs.Nodup} {e : V × V} :
    e ∈ (G.inducedOn xs hxs).redEdges ↔ e ∈ G.redEdges ∧ e.1 ∈ xs ∧ e.2 ∈ xs := by
  simp only [Graph.inducedOn, List.mem_filter, decide_eq_true_eq]

private theorem Graph.neighbor_has_red_edge {x a : V} (ha : a ∈ G.neighbors x)
    (hfull : G.redDegree x = G.degree x) :
    ∃ e ∈ G.redEdges, (e.1 = x ∧ e.2 = a) ∨ (e.1 = a ∧ e.2 = x) := by
  let rs := G.redEdges.filter (touches x)
  let ns := rs.map (opposite x)
  have hn : ns.Nodup := map_nodup_on (filter_nodup G.redNodup _) _ (by
    intro e he f hf h
    exact G.opposite_injective (List.mem_filter.mp he).1 (List.mem_filter.mp hf).1
      (List.mem_filter.mp he).2 (List.mem_filter.mp hf).2 h)
  have hs : ns ⊆ G.neighbors x := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
    exact G.opposite_adj (List.mem_filter.mp he).1 (List.mem_filter.mp he).2
  have hsize : (G.neighbors x).length ≤ ns.length := by
    rw [List.length_map]
    change G.degree x ≤ G.redDegree x
    exact Nat.le_of_eq hfull.symm
  obtain ⟨e, he, hval⟩ := List.mem_map.mp (full_of_subset_length hn hs hsize ha)
  obtain ⟨her, het⟩ := List.mem_filter.mp he
  have het' : e.1 = x ∨ e.2 = x := of_decide_eq_true het
  by_cases hx : e.1 = x
  · exact ⟨e, her, .inl ⟨hx, by simpa only [opposite, if_pos hx] using hval⟩⟩
  · exact ⟨e, her, .inr ⟨by simpa only [opposite, if_neg hx] using hval,
      het'.resolve_left hx⟩⟩

omit [DecidableEq V] in
private theorem Graph.partitioned_degree_le (a b : List V)
    (ha : a.Nodup) (hb : b.Nodup) (hd : ∀ x ∈ a, x ∉ b)
    (hsuba : a ⊆ G.vertices) (hsubb : b ⊆ G.vertices) (x : V) :
    (a.filter (G.adjacent x)).length + (b.filter (G.adjacent x)).length ≤ G.degree x := by
  have hn := append_nodup_disjoint (filter_nodup ha (G.adjacent x))
    (filter_nodup hb (G.adjacent x)) (by
      intro y hya hyb
      exact hd y (List.mem_filter.mp hya).1 (List.mem_filter.mp hyb).1)
  have hsub : a.filter (G.adjacent x) ++ b.filter (G.adjacent x) ⊆ G.neighbors x := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact List.mem_filter.mpr ⟨hsuba (List.mem_filter.mp hy).1, (List.mem_filter.mp hy).2⟩
    · exact List.mem_filter.mpr ⟨hsubb (List.mem_filter.mp hy).1, (List.mem_filter.mp hy).2⟩
  simpa only [List.length_append, Graph.degree] using hn.length_le_of_subset hsub

private theorem Graph.covers_root_neighbors {v : V} {f : V × V}
    (hf : f ∈ G.redEdges) (hx : G.adjacent v f.1 = false) (hy : G.adjacent v f.2 = false)
    (hfull : G.redDegree v = G.degree v) {a : V} (ha : a ∈ G.neighbors v) :
    G.adjacent f.1 a = true ∨ G.adjacent f.2 a = true := by
  obtain ⟨e, he, hord⟩ := G.neighbor_has_red_edge ha hfull
  have hstrong := G.strong e he f hf
  have h' : G.adjacent a f.1 = true ∨ G.adjacent a f.2 = true := by
    rcases hord with ⟨he1, he2⟩ | ⟨he1, he2⟩
    · simpa only [he1, he2, hx, hy, Bool.false_eq_true, false_or] using hstrong
    · simpa only [he1, he2, hx, hy, Bool.false_eq_true, or_false] using hstrong
  simpa only [G.symmetric a f.1, G.symmetric a f.2] using h'

def Graph.outside (v : V) : List V :=
  G.vertices.filter fun x => decide (x ≠ v) && !G.adjacent v x

private theorem Graph.outside_mem {v x : V} :
    x ∈ G.outside v ↔ x ∈ G.vertices ∧ x ≠ v ∧ G.adjacent v x = false := by
  simp only [Graph.outside, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true']

private theorem Graph.neighbor_outside_disjoint {v x : V} (ha : x ∈ G.neighbors v) :
    x ∉ G.outside v := by
  intro hw
  have hn := (List.mem_filter.mp ha).2
  rw [(G.outside_mem.mp hw).2.2] at hn
  cases hn

omit [DecidableEq V] in
private theorem Graph.not_root_neighbor (v : V) : v ∉ G.neighbors v := by
  simp [Graph.neighbors, G.loopless]

private theorem Graph.delete_root_region {v x : V} (hx : x ∈ G.vertices) (hne : x ≠ v) :
    x ∈ G.neighbors v ∨ x ∈ G.outside v := by
  cases h : G.adjacent v x
  · exact .inr (G.outside_mem.mpr ⟨hx, hne, h⟩)
  · exact .inl (List.mem_filter.mpr ⟨hx, h⟩)

def Graph.outer (v : V) : Graph V :=
  G.inducedOn (G.outside v) (filter_nodup G.verticesNodup _)

def Graph.inner (v : V) : Graph V :=
  G.inducedOn (G.neighbors v) (filter_nodup G.verticesNodup _)

def Graph.cross (v : V) : List (V × V) :=
  G.redEdges.filter fun e => decide
    ((e.1 ∈ G.outside v ∧ e.2 ∈ G.neighbors v) ∨ (e.2 ∈ G.outside v ∧ e.1 ∈ G.neighbors v))

def Graph.signatureSize (v x : V) : Nat :=
  ((G.neighbors v).filter (G.adjacent x)).length

def Graph.acrossCount (v : V) : Nat :=
  total (G.outside v) (G.signatureSize v)

private theorem Graph.outer_mem {v : V} {e : V × V} :
    e ∈ (G.outer v).redEdges ↔ e ∈ G.redEdges ∧ e.1 ∈ G.outside v ∧ e.2 ∈ G.outside v :=
  G.induced_red_mem

private theorem Graph.inner_mem {v : V} {e : V × V} :
    e ∈ (G.inner v).redEdges ↔
      e ∈ G.redEdges ∧ e.1 ∈ G.neighbors v ∧ e.2 ∈ G.neighbors v :=
  G.induced_red_mem

private theorem Graph.cross_mem {v : V} {e : V × V} :
    e ∈ G.cross v ↔ e ∈ G.redEdges ∧
      ((e.1 ∈ G.outside v ∧ e.2 ∈ G.neighbors v) ∨
        (e.2 ∈ G.outside v ∧ e.1 ∈ G.neighbors v)) := by
  simp only [Graph.cross, List.mem_filter, decide_eq_true_eq]

private theorem Graph.red_root_partition (v : V) :
    G.redEdges.length = G.redDegree v + (G.inner v).redEdges.length +
      (G.cross v).length + (G.outer v).redEdges.length := by
  let a x := x ∈ G.neighbors v
  let w x := x ∈ G.outside v
  let r (e : V × V) := touches v e
  let p (e : V × V) := decide (a e.1 ∧ a e.2)
  let q (e : V × V) := decide ((w e.1 ∧ a e.2) ∨ (w e.2 ∧ a e.1))
  let z (e : V × V) := decide (w e.1 ∧ w e.2)
  change G.redEdges.length = (G.redEdges.filter r).length + (G.redEdges.filter p).length +
      (G.redEdges.filter q).length + (G.redEdges.filter z).length
  rw [← Nat.mul_one G.redEdges.length, ← total_const]
  rw [card_as_total G.redEdges r, card_as_total G.redEdges p, card_as_total G.redEdges q,
    card_as_total G.redEdges z, ← total_add, ← total_add, ← total_add]
  apply total_congr
  intro e he
  obtain ⟨hm1, hm2⟩ := G.redVertices e he
  have hnone (x : V) : ¬ (a x ∧ w x) :=
    fun h => G.neighbor_outside_disjoint h.1 h.2
  have hwa : ¬ w v := fun h => (G.outside_mem.mp h).2.1 rfl
  have hva : ¬a v := G.not_root_neighbor v
  have hclass (x : V) (hx : x ∈ G.vertices) :
      x = v ∨ (a x ∧ ¬w x) ∨ (w x ∧ ¬a x) := by
    by_cases hx' : x = v
    · exact .inl hx'
    · rcases G.delete_root_region hx hx' with ha | hw
      · exact .inr (.inl ⟨ha, fun hw => hnone x ⟨ha, hw⟩⟩)
      · exact .inr (.inr ⟨hw, fun ha => hnone x ⟨ha, hw⟩⟩)
  have hne (x : V) : a x ∨ w x → x ≠ v := by
    intro h hh
    subst x
    exact h.elim hva hwa
  rcases hclass e.1 hm1 with h | ⟨ha, hwa'⟩ | ⟨hw, hva'⟩
  · simp [r, p, q, z, touches, h, hva, hwa]
  · have hn := hne e.1 (.inl ha)
    rcases hclass e.2 hm2 with h | ⟨ha', hw'⟩ | ⟨hw', ha'⟩
    · simp [r, p, q, z, touches, h, hn, hva, hwa]
    · simp [r, p, q, z, touches, hn, hne e.2 (.inl ha'), ha, ha', hwa', hw']
    · simp [r, p, q, z, touches, hn, hne e.2 (.inr hw'), ha, ha', hwa', hw']
  · have hn := hne e.1 (.inr hw)
    rcases hclass e.2 hm2 with h | ⟨ha', hw'⟩ | ⟨hw', ha'⟩
    · simp [r, p, q, z, touches, h, hn, hva, hwa]
    · simp [r, p, q, z, touches, hn, hne e.2 (.inl ha'), hw, hva', ha', hw']
    · simp [r, p, q, z, touches, hn, hne e.2 (.inr hw'), hw, hva', ha', hw']

private theorem Graph.signature_cover {v : V} {e : V × V}
    (hfull : G.redDegree v = G.degree v) (he : e ∈ (G.outer v).redEdges) :
    G.degree v ≤ G.signatureSize v e.1 + G.signatureSize v e.2 := by
  obtain ⟨he', hw1, hw2⟩ := G.outer_mem.mp he
  have hc (a : V) (ha : a ∈ G.neighbors v) :
      (G.adjacent e.1 a || G.adjacent e.2 a) = true :=
    (Bool.or_eq_true _ _).mpr (G.covers_root_neighbors he' (G.outside_mem.mp hw1).2.2
      (G.outside_mem.mp hw2).2.2 hfull ha)
  have hu := card_union_le (G.neighbors v) (G.adjacent e.1) (G.adjacent e.2)
  rw [List.filter_eq_self.mpr hc] at hu
  exact hu

private theorem Graph.signature_and_outer_degree_le (v x : V) :
    G.signatureSize v x + (G.outer v).degree x ≤ G.degree x :=
  G.partitioned_degree_le (G.neighbors v) (G.outside v)
    (filter_nodup G.verticesNodup _) (filter_nodup G.verticesNodup _)
    (fun _ hx => G.neighbor_outside_disjoint hx)
    List.filter_sublist.subset List.filter_sublist.subset x

private def Graph.crossGraph (v : V) : Graph V where
  vertices := G.vertices
  verticesNodup := G.verticesNodup
  adjacent := G.adjacent
  symmetric := G.symmetric
  loopless := G.loopless
  redEdges := G.cross v
  redNodup := filter_nodup G.redNodup _
  redOrientation he hf := G.redOrientation (G.cross_mem.mp he).1 (G.cross_mem.mp hf).1
  redAdjacent e he := G.redAdjacent e (G.cross_mem.mp he).1
  redVertices e he := G.redVertices e (G.cross_mem.mp he).1
  strong e he f hf := G.strong e (G.cross_mem.mp he).1 f (G.cross_mem.mp hf).1

private theorem Graph.cross_degree_le_signature (v x : V) (hx : x ∈ G.outside v) :
    (G.crossGraph v).redDegree x ≤ G.signatureSize v x := by
  let C := G.crossGraph v
  let rs := C.redEdges.filter (touches x)
  let ns := rs.map (opposite x)
  have hn : ns.Nodup := map_nodup_on (filter_nodup C.redNodup _) _ (by
    intro e he f hf h
    exact C.opposite_injective (List.mem_filter.mp he).1 (List.mem_filter.mp hf).1
      (List.mem_filter.mp he).2 (List.mem_filter.mp hf).2 h)
  have hnot : x ∉ G.neighbors v := fun ha => G.neighbor_outside_disjoint ha hx
  have hs : ns ⊆ (G.neighbors v).filter (G.adjacent x) := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
    obtain ⟨her, het⟩ := List.mem_filter.mp he
    have hadj := (List.mem_filter.mp (C.opposite_adj her het)).2
    apply List.mem_filter.mpr
    refine ⟨?_, hadj⟩
    have het' : e.1 = x ∨ e.2 = x := of_decide_eq_true het
    rcases (G.cross_mem.mp her).2 with ⟨hw, ha⟩ | ⟨hw, ha⟩
    · have hne : e.2 ≠ x := fun h => hnot (h ▸ ha)
      simpa only [opposite, if_pos (het'.resolve_right hne)] using ha
    · have hne : e.1 ≠ x := fun h => hnot (h ▸ ha)
      simpa only [opposite, if_neg hne] using ha
  simpa only [ns, rs, List.length_map, Graph.redDegree, Graph.signatureSize] using
    hn.length_le_of_subset hs

private theorem Graph.cross_le_across (v : V) : (G.cross v).length ≤ G.acrossCount v := by
  let C := G.crossGraph v
  have htally := C.tally_red_incidence (G.outside v) (filter_nodup G.verticesNodup _) (fun _ => 1)
  have hrows : total (G.outside v) C.redDegree = (G.cross v).length := by
    have ht : total (G.outside v) C.redDegree =
        total C.redEdges (fun e => (if e.1 ∈ G.outside v then 1 else 0) +
          (if e.2 ∈ G.outside v then 1 else 0)) := by
      simpa only [Nat.one_mul] using htally
    rw [ht, ← Nat.mul_one (G.cross v).length, ← total_const]
    apply total_congr
    intro e he
    rcases (G.cross_mem.mp he).2 with ⟨hw, ha⟩ | ⟨hw, ha⟩
    · simp [hw, G.neighbor_outside_disjoint ha]
    · simp [hw, G.neighbor_outside_disjoint ha]
  rw [← hrows]
  exact total_mono _ (G.cross_degree_le_signature v)

private theorem Graph.inner_tally (v : V) :
    total (G.neighbors v) (G.inner v).redDegree = 2 * (G.inner v).redEdges.length := by
  let I := G.inner v
  have htally := I.tally_red_incidence (G.neighbors v) (filter_nodup G.verticesNodup _) (fun _ => 1)
  have ht : total (G.neighbors v) I.redDegree =
      total I.redEdges (fun e => (if e.1 ∈ G.neighbors v then 1 else 0) +
        (if e.2 ∈ G.neighbors v then 1 else 0)) := by
    simpa only [Nat.one_mul] using htally
  rw [ht, Nat.mul_comm 2, ← total_const]
  apply total_congr
  intro e he
  obtain ⟨_, ha, hb⟩ := G.inner_mem.mp he
  simp [ha, hb]

private theorem Graph.across_swaps (v : V) :
    G.acrossCount v = total (G.neighbors v) (fun a => ((G.outside v).filter (G.adjacent a)).length) := by
  let A := G.neighbors v
  let W := G.outside v
  change total W (fun x => (A.filter (G.adjacent x)).length) =
    total A (fun a => (W.filter (G.adjacent a)).length)
  calc
    _ = total W (fun x => total A (fun a => if G.adjacent x a then 1 else 0)) :=
      total_congr W (fun x _ => card_as_total A (G.adjacent x))
    _ = total A (fun a => total W (fun x => if G.adjacent x a then 1 else 0)) :=
      total_swap W A _
    _ = _ := by
      apply total_congr
      intro a _
      rw [card_as_total]
      apply total_congr
      intro x _
      rw [G.symmetric x a]

private theorem Graph.inner_across_bound (v : V) (hv : v ∈ G.vertices)
    (hv4 : G.degree v = 4) (hmax : ∀ x, G.degree x ≤ 4) :
    2 * (G.inner v).redEdges.length + G.acrossCount v ≤ 12 := by
  let A := G.neighbors v
  let W := G.outside v
  have hnr : (v :: A).Nodup := List.nodup_cons.mpr
    ⟨G.not_root_neighbor v, filter_nodup G.verticesNodup _⟩
  have hsub : v :: A ⊆ G.vertices := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hv
    · exact List.filter_sublist.subset hx
  have hdis : ∀ x ∈ v :: A, x ∉ W := by
    intro x hx hw
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (G.outside_mem.mp hw).2.1 rfl
    · exact G.neighbor_outside_disjoint hx hw
  have hrow (a : V) (ha : a ∈ A) :
      (G.inner v).redDegree a + (W.filter (G.adjacent a)).length ≤ 3 := by
    have h := G.partitioned_degree_le (v :: A) W hnr (filter_nodup G.verticesNodup _)
      hdis hsub List.filter_sublist.subset a
    have hadj : G.adjacent a v = true := by
      rw [G.symmetric a v]
      exact (List.mem_filter.mp ha).2
    simp only [List.filter_cons, hadj, if_true, List.length_cons] at h
    have hred := (G.inner v).redDegree_le_degree a
    change (G.inner v).redDegree a ≤ (A.filter (G.adjacent a)).length at hred
    have hm := hmax a
    omega
  have h := total_mono A hrow
  rw [total_add, total_const] at h
  change total (G.neighbors v) (G.inner v).redDegree +
      total (G.neighbors v) (fun a => ((G.outside v).filter (G.adjacent a)).length) ≤
      G.degree v * 3 at h
  simpa only [G.inner_tally, ← G.across_swaps, hv4] using h

private theorem Graph.redDegree_pos {e : V × V} (he : e ∈ G.redEdges)
    {x : V} (hx : touches x e = true) : 0 < G.redDegree x :=
  List.length_filter_pos_iff.mpr ⟨e, he, hx⟩

private theorem Graph.signature_bounds_of_red {v : V} (hv4 : G.degree v = 4)
    (hfull : G.redDegree v = G.degree v) (hmax : ∀ x, G.degree x ≤ 4)
    {e : V × V} (he : e ∈ (G.outer v).redEdges) :
    1 ≤ G.signatureSize v e.1 ∧ G.signatureSize v e.1 ≤ 3 ∧
      1 ≤ G.signatureSize v e.2 ∧ G.signatureSize v e.2 ≤ 3 ∧
      4 ≤ G.signatureSize v e.1 + G.signatureSize v e.2 := by
  let W := G.outer v
  have h1 := G.signature_and_outer_degree_le v e.1
  have h2 := G.signature_and_outer_degree_le v e.2
  have h1' := W.redDegree_le_degree e.1
  have h2' := W.redDegree_le_degree e.2
  have hr1 := W.redDegree_pos (x := e.1) he (by simp [touches])
  have hr2 := W.redDegree_pos (x := e.2) he (by simp [touches])
  have hd1 := hmax e.1
  have hd2 := hmax e.2
  have hc := G.signature_cover hfull he
  rw [hv4] at hc
  change 0 < (G.outer v).redDegree e.1 at hr1
  change 0 < (G.outer v).redDegree e.2 at hr2
  change (G.outer v).redDegree e.1 ≤ (G.outer v).degree e.1 at h1'
  change (G.outer v).redDegree e.2 ≤ (G.outer v).degree e.2 at h2'
  omega

def signaturePenalty (c : Nat) : Nat :=
  c - (c - 1) * (4 - c)

private theorem signature_capacity_le {c : Nat} (hc : c ≤ 4) :
    signaturePenalty c + (c - 1) * (4 - c) = c := by
  have h : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
  rcases h with h | h | h | h | h <;> simpa only [h] using
    (by decide : signaturePenalty _ + (_ - 1) * (4 - _) = _)

private theorem signature_penalty_odd {c : Nat} (hc : c ≤ 4) :
    c % 2 ≤ signaturePenalty c := by
  have h : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
  rcases h with h | h | h | h | h <;> subst c <;> decide

private theorem signature_penalty_pos {c : Nat} (hc1 : 1 ≤ c) (hc3 : c ≤ 3)
    (hc : signaturePenalty c = 0) : c = 2 := by
  have h : c = 1 ∨ c = 2 ∨ c = 3 := by omega
  rcases h with h | h | h <;> subst c
  · contradiction
  · rfl
  · contradiction

def Graph.outerPenalty (v : V) : Nat :=
  total (G.outside v) (fun x => signaturePenalty (G.signatureSize v x))

def Graph.outerSurplus (v : V) : Nat :=
  total (G.outer v).redEdges (fun e => G.signatureSize v e.1 + G.signatureSize v e.2 - 4)

/-- Degree accounting on W. Each red edge pays two, plus the signature
    surplus above four; vertices of signature 1, 3 or 4 consume extra capacity. -/
theorem Graph.outer_budget {v : V} (hv4 : G.degree v = 4)
    (hfull : G.redDegree v = G.degree v) (hmax : ∀ x, G.degree x ≤ 4) :
    G.outerPenalty v + G.outerSurplus v + 2 * (G.outer v).redEdges.length ≤
      G.acrossCount v := by
  let W := G.outside v
  let H := G.outer v
  let c := G.signatureSize v
  let k x := c x - 1
  have hcap (x : V) :
      signaturePenalty (c x) + k x * H.redDegree x ≤ c x := by
    have hf := G.signature_and_outer_degree_le v x
    have hr := H.redDegree_le_degree x
    have hm := hmax x
    change c x + H.degree x ≤ G.degree x at hf
    have hc : c x ≤ 4 := by omega
    have hrd : H.redDegree x ≤ 4 - c x := by omega
    have hmul := Nat.mul_le_mul_left (k x) hrd
    have heq := signature_capacity_le hc
    change signaturePenalty (c x) + k x * (4 - c x) = c x at heq
    omega
  have hall := total_mono W (fun x _ => hcap x)
  rw [total_add] at hall
  have htally := H.tally_red_incidence W (filter_nodup G.verticesNodup _) k
  rw [htally] at hall
  have hreplace :
      total H.redEdges (fun e => (if e.1 ∈ W then k e.1 else 0) +
        (if e.2 ∈ W then k e.2 else 0)) =
        total H.redEdges (fun e => (c e.1 + c e.2 - 4) + 2) := by
    apply total_congr
    intro e he
    obtain ⟨_, hm1, hm2⟩ := G.outer_mem.mp he
    change e.1 ∈ W at hm1
    change e.2 ∈ W at hm2
    simp only [if_pos hm1, if_pos hm2]
    obtain ⟨hx, _, hy, _, hs⟩ := G.signature_bounds_of_red hv4 hfull hmax he
    change 1 ≤ c e.1 at hx
    change 1 ≤ c e.2 at hy
    change 4 ≤ c e.1 + c e.2 at hs
    change c e.1 - 1 + (c e.2 - 1) = _
    omega
  rw [hreplace, total_add, total_const] at hall
  change total W (fun x => signaturePenalty (c x)) +
    total H.redEdges (fun e => c e.1 + c e.2 - 4) + 2 * H.redEdges.length ≤ total W c
  omega

private theorem total_value_le {A : Type u} (xs : List A) (f : A → Nat) {a : A} (ha : a ∈ xs) :
    f a ≤ total xs f := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    rcases List.mem_cons.mp ha with rfl | ht
    · simp
    · have h := ih ht
      simp only [total_cons]
      omega

private def Graph.outerTwoVertices (v : V) : List V :=
  (G.outside v).filter fun x => decide (G.signatureSize v x = 2)

private theorem Graph.outerTwo_mem {v x : V} :
    x ∈ G.outerTwoVertices v ↔ x ∈ G.outside v ∧ G.signatureSize v x = 2 := by
  simp only [Graph.outerTwoVertices, List.mem_filter, decide_eq_true_eq]

private def Graph.outerTwo (v : V) : Graph V :=
  G.inducedOn (G.outerTwoVertices v) (filter_nodup (filter_nodup G.verticesNodup _) _)

private theorem Graph.outerTwo_degree_le (v : V) (hmax : ∀ x, G.degree x ≤ 4)
    {x : V} (hx : x ∈ G.outerTwoVertices v) : (G.outerTwo v).degree x ≤ 2 := by
  have hc := G.signature_and_outer_degree_le v x
  rw [(G.outerTwo_mem.mp hx).2] at hc
  have hs : (G.outerTwo v).neighbors x ⊆ (G.outer v).neighbors x := by
    intro u hu
    obtain ⟨hmem, hadj⟩ := List.mem_filter.mp hu
    exact List.mem_filter.mpr ⟨(G.outerTwo_mem.mp hmem).1, hadj⟩
  have hnd := filter_nodup (G.outerTwo v).verticesNodup ((G.outerTwo v).adjacent x)
  have hle := hnd.length_le_of_subset hs
  change (G.outerTwo v).degree x ≤ (G.outer v).degree x at hle
  have hh := hmax x
  omega

private theorem Graph.red_max_two_bound (hmax : ∀ x ∈ G.vertices, G.degree x ≤ 2) :
    G.redEdges.length ≤ 5 := by
  cases h : G.redEdges with
  | nil => simp
  | cons e es =>
    have he : e ∈ G.redEdges := by rw [h]; simp
    obtain ⟨hv1, hv2⟩ := G.redVertices e he
    have h1 := hmax e.1 hv1
    have h2 := hmax e.2 hv2
    have hq := G.rootNeighbors_bound he
    have hs := G.redEdges_le_from_root he 2 (fun x hx =>
      Nat.le_trans (G.redDegree_le_degree x) (hmax x (G.rootNeighbors_mem.mp hx).1))
    rw [h] at hs
    omega

theorem Graph.outer_le_five {v : V} (hv4 : G.degree v = 4)
    (hfull : G.redDegree v = G.degree v) (hv : v ∈ G.vertices)
    (hmax : ∀ x, G.degree x ≤ 4) : (G.outer v).redEdges.length ≤ 5 := by
  have hbound := G.inner_across_bound v hv hv4 hmax
  have hbudget := G.outer_budget hv4 hfull hmax
  by_cases hlen : (G.outer v).redEdges.length ≤ 5
  · exact hlen
  · have hzero : G.outerPenalty v = 0 := by omega
    let T := G.outerTwo v
    have hsub : (G.outer v).redEdges ⊆ T.redEdges := by
      intro e he
      obtain ⟨her, hw1, hw2⟩ := G.outer_mem.mp he
      obtain ⟨hmin1, hmax1, hmin2, hmax2, _⟩ := G.signature_bounds_of_red hv4 hfull hmax he
      have hpen1 := total_value_le (G.outside v) (fun x => signaturePenalty (G.signatureSize v x)) hw1
      have hpen2 := total_value_le (G.outside v) (fun x => signaturePenalty (G.signatureSize v x)) hw2
      change signaturePenalty (G.signatureSize v e.1) ≤ G.outerPenalty v at hpen1
      change signaturePenalty (G.signatureSize v e.2) ≤ G.outerPenalty v at hpen2
      have hc1 := signature_penalty_pos hmin1 hmax1 (by omega)
      have hc2 := signature_penalty_pos hmin2 hmax2 (by omega)
      exact G.induced_red_mem.mpr ⟨her, G.outerTwo_mem.mpr ⟨hw1, hc1⟩,
        G.outerTwo_mem.mpr ⟨hw2, hc2⟩⟩
    have hdeg := T.red_max_two_bound (fun x hx => G.outerTwo_degree_le v hmax hx)
    have hsz := (G.outer v).redNodup.length_le_of_subset hsub
    omega

private theorem tally_parity {A : Type u} (xs : List A) (f : A → Nat) :
    total xs (fun x => f x % 2) % 2 = total xs f % 2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [total_cons]
    omega

private theorem Graph.outer_odd_budget (v : V) (hmax : ∀ x, G.degree x ≤ 4) :
    total (G.outside v) (fun x => G.signatureSize v x % 2) ≤ G.outerPenalty v := by
  apply total_mono
  intro x _
  have h := G.signature_and_outer_degree_le v x
  exact signature_penalty_odd (Nat.le_trans (Nat.le_trans
    (Nat.le_add_right (G.signatureSize v x) ((G.outer v).degree x)) h) (hmax x))

/-- Numerical consequences of a hypothetical 21-edge red strong clique. -/
theorem Graph.large_root_profile (hmax : ∀ x, G.degree x ≤ 4)
    (hsize : 21 ≤ G.redEdges.length) :
    ∃ v ∈ G.vertices, G.redDegree v = 4 ∧ G.degree v = 4 ∧
      (G.inner v).redEdges.length = 0 ∧ (G.cross v).length = 12 ∧
      G.acrossCount v = 12 ∧ (G.outer v).redEdges.length = 5 ∧ G.outerPenalty v ≤ 2 := by
  obtain ⟨v, hv⟩ := G.exists_redDegree_four hmax hsize
  have hvd := G.redDegree_le_degree v
  have hvmax := hmax v
  have hv4 : G.degree v = 4 := by omega
  have hvfull : G.redDegree v = G.degree v := by omega
  have hvpos : 0 < G.redDegree v := by omega
  obtain ⟨f, hf, ht⟩ := List.length_filter_pos_iff.mp hvpos
  have hvlist : v ∈ G.vertices := by
    have ht' : f.1 = v ∨ f.2 = v := of_decide_eq_true ht
    obtain ⟨hu, hw⟩ := G.redVertices f hf
    exact ht'.elim (fun he => he ▸ hu) (fun he => he ▸ hw)
  have hb := G.inner_across_bound v hvlist hv4 hmax
  have hp := G.red_root_partition v
  have hc := G.cross_le_across v
  have hw := G.outer_le_five hv4 hvfull hvlist hmax
  have hbud := G.outer_budget hv4 hvfull hmax
  exact ⟨v, hvlist, hv, hv4, by omega⟩

/-- The five-edge boundary case forces each outer red edge's two signatures
    to cover the four root neighbors as a disjoint union. -/
theorem Graph.outer_signatures_complementary {v : V} (hv4 : G.degree v = 4)
    (hfull : G.redDegree v = G.degree v) (hmax : ∀ x, G.degree x ≤ 4)
    (hp : G.acrossCount v = 12) (hw : (G.outer v).redEdges.length = 5)
    {e : V × V} (he : e ∈ (G.outer v).redEdges) :
    G.signatureSize v e.1 + G.signatureSize v e.2 = 4 := by
  have hb := G.outer_budget hv4 hfull hmax
  obtain ⟨_, hm1, hm2⟩ := G.outer_mem.mp he
  obtain ⟨hmn1, hmx1, hmn2, hmx2, hc⟩ := G.signature_bounds_of_red hv4 hfull hmax he
  apply Classical.byContradiction
  intro hne
  have hs := total_value_le (G.outer v).redEdges
    (fun f => G.signatureSize v f.1 + G.signatureSize v f.2 - 4) he
  change G.signatureSize v e.1 + G.signatureSize v e.2 - 4 ≤ G.outerSurplus v at hs
  have hodd := tally_parity (G.outside v) (G.signatureSize v)
  change total (G.outside v) (fun x => G.signatureSize v x % 2) % 2 =
    G.acrossCount v % 2 at hodd
  have hoddle := G.outer_odd_budget v hmax
  have hpos : 1 ≤ total (G.outside v) (fun x => G.signatureSize v x % 2) := by
    have hu : G.signatureSize v e.1 = 3 ∨ G.signatureSize v e.2 = 3 := by omega
    rcases hu with h | h
    · have hh := total_value_le (G.outside v) (fun x => G.signatureSize v x % 2) hm1
      omega
    · have hh := total_value_le (G.outside v) (fun x => G.signatureSize v x % 2) hm2
      omega
  omega

/-- Red adjacency with either orientation in the stored edge list. -/
def Graph.RedLink (x y : V) : Prop :=
  (x, y) ∈ G.redEdges ∨ (y, x) ∈ G.redEdges

private theorem Graph.neighbor_red_link {x y : V} (hy : y ∈ G.neighbors x)
    (hfull : G.redDegree x = G.degree x) : G.RedLink x y := by
  obtain ⟨e, he, h⟩ := G.neighbor_has_red_edge hy hfull
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hh : e = (x, y) := Prod.ext h1 h2
    exact .inl (hh ▸ he)
  · have hh : e = (y, x) := Prod.ext h1 h2
    exact .inr (hh ▸ he)

omit [DecidableEq V] in
private theorem Graph.edge_eq_from_ends {e f : V × V}
    (he : e ∈ G.redEdges) (hf : f ∈ G.redEdges)
    (h1 : f.1 = e.1 ∨ f.1 = e.2) (h2 : f.2 = e.1 ∨ f.2 = e.2) : f = e := by
  have hne := G.red_ne hf
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact (hne (h1.trans h2.symm)).elim
  · exact Prod.ext h1 h2
  · apply G.same_unordered hf he
    exact .inr (Prod.ext h2 h1)
  · exact (hne (h1.trans h2.symm)).elim

private theorem Graph.red_link_fst_snd {v x y : V}
    (hp : G.acrossCount v = 12) (hw : (G.outer v).redEdges.length = 5)
    (hv4 : G.degree v = 4) (hfull : G.redDegree v = G.degree v)
    (hmax : ∀ z, G.degree z ≤ 4) (hxy : (G.outer v).RedLink x y) :
    G.signatureSize v x + G.signatureSize v y = 4 := by
  rcases hxy with h | h
  · exact G.outer_signatures_complementary hv4 hfull hmax hp hw h
  · have h' := G.outer_signatures_complementary hv4 hfull hmax hp hw h
    exact (Nat.add_comm _ _).trans h'

private theorem Graph.outer_all_two {v : V} (hv4 : G.degree v = 4)
    (hfull : G.redDegree v = G.degree v) (hmax : ∀ x, G.degree x ≤ 4)
    (hp : G.acrossCount v = 12) (hw : (G.outer v).redEdges.length = 5)
    {e : V × V} (he : e ∈ (G.outer v).redEdges) :
    G.signatureSize v e.1 = 2 ∧ G.signatureSize v e.2 = 2 := by
  let H := G.outer v
  let W := G.outside v
  let c := G.signatureSize v
  have hsum := G.outer_signatures_complementary hv4 hfull hmax hp hw he
  have hb := G.outer_budget hv4 hfull hmax
  have ⟨he1min, he1max, he2min, he2max, _⟩ := G.signature_bounds_of_red hv4 hfull hmax he
  by_cases ht : c e.1 = 2
  · change c e.1 + c e.2 = 4 at hsum
    change c e.1 = 2 ∧ c e.2 = 2
    exact ⟨ht, by omega⟩
  have hsum' : c e.1 + c e.2 = 4 := hsum
  have he1min' : 1 ≤ c e.1 := he1min
  have he1max' : c e.1 ≤ 3 := he1max
  have he2min' : 1 ≤ c e.2 := he2min
  have he2max' : c e.2 ≤ 3 := he2max
  have he1odd : c e.1 % 2 = 1 := by omega
  have he2odd : c e.2 % 2 = 1 := by omega
  have ⟨_, he1mem, he2mem⟩ := G.outer_mem.mp he
  let odd := W.filter (fun x => decide (c x % 2 = 1))
  have hoddle : odd.length ≤ G.outerPenalty v := by
    rw [card_as_total]
    refine Nat.le_trans (total_mono W ?_) (G.outer_odd_budget v hmax)
    intro x _
    change (if decide (c x % 2 = 1) then 1 else 0) ≤ c x % 2
    by_cases ho : c x % 2 = 1 <;> simp [ho]
  have hoddsize : odd.length ≤ ([e.1, e.2] : List V).length := by
    simp only [List.length_cons, List.length_nil]
    omega
  have hends : [e.1, e.2] ⊆ odd := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact List.mem_filter.mpr ⟨he1mem, decide_eq_true he1odd⟩
    · exact List.mem_filter.mpr ⟨he2mem, decide_eq_true he2odd⟩
  have hnodup : ([e.1, e.2] : List V).Nodup :=
    List.nodup_cons.mpr ⟨by simpa only [List.mem_singleton] using H.red_ne he, by simp⟩
  have hoddcover := full_of_subset_length hnodup hends hoddsize
  have hother (f : V × V) (hf : f ∈ H.redEdges) (hfe : f ≠ e) :
      c f.1 = 2 ∧ c f.2 = 2 := by
    have hs : c f.1 + c f.2 = 4 := G.outer_signatures_complementary hv4 hfull hmax hp hw hf
    have ⟨h1, h2, h3, h4, _⟩ := G.signature_bounds_of_red hv4 hfull hmax hf
    change 1 ≤ c f.1 at h1
    change c f.1 ≤ 3 at h2
    change 1 ≤ c f.2 at h3
    change c f.2 ≤ 3 at h4
    obtain ⟨_, hm1, hm2⟩ := G.outer_mem.mp hf
    by_cases htwo : c f.1 = 2
    · exact ⟨htwo, by omega⟩
    · have ha : f.1 ∈ odd := List.mem_filter.mpr ⟨hm1, decide_eq_true (by omega)⟩
      have hb' : f.2 ∈ odd := List.mem_filter.mpr ⟨hm2, decide_eq_true (by omega)⟩
      have ha' : f.1 = e.1 ∨ f.1 = e.2 := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false] using hoddcover ha
      have hb'' : f.2 = e.1 ∨ f.2 = e.2 := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false] using hoddcover hb'
      exact (hfe (H.edge_eq_from_ends he hf ha' hb'')).elim
  have hdeg (x : V) : c x + H.degree x ≤ 4 :=
    Nat.le_trans (G.signature_and_outer_degree_le v x) (hmax x)
  have hr (x : V) (hx : x ∈ H.rootNeighbors e.1 e.2) : H.redDegree x ≤ 1 := by
    have ⟨hxv, hne1, hne2, hadj⟩ := H.rootNeighbors_mem.mp hx
    by_cases htwo : c x = 2
    · have hd := hdeg x
      have hdr := H.redDegree_le_degree x
      apply Classical.byContradiction
      intro hnot
      have hfullx : H.redDegree x = H.degree x := by omega
      rcases hadj with hadj | hadj
      · have hxe : e.1 ∈ H.neighbors x := List.mem_filter.mpr
          ⟨he1mem, (H.symmetric x e.1).trans hadj⟩
        have link := H.neighbor_red_link hxe hfullx
        have hh : c x + c e.1 = 4 := G.red_link_fst_snd hp hw hv4 hfull hmax link
        omega
      · have hxe : e.2 ∈ H.neighbors x := List.mem_filter.mpr
          ⟨he2mem, (H.symmetric x e.2).trans hadj⟩
        have link := H.neighbor_red_link hxe hfullx
        have hh : c x + c e.2 = 4 := G.red_link_fst_snd hp hw hv4 hfull hmax link
        omega
    · apply Classical.byContradiction
      intro hn
      have hpos : 0 < H.redDegree x := by omega
      obtain ⟨f, hf, hfx⟩ := List.length_filter_pos_iff.mp hpos
      have hfx' : f.1 = x ∨ f.2 = x := of_decide_eq_true hfx
      have hfe : f ≠ e := by
        intro h
        rw [h] at hfx'
        exact hfx'.elim (fun h' => hne1 h'.symm) (fun h' => hne2 h'.symm)
      obtain ⟨h1, h2⟩ := hother f hf hfe
      exact htwo (hfx'.elim (fun h => h ▸ h1) (fun h => h ▸ h2))
  have h1 := hdeg e.1
  have h2 := hdeg e.2
  have hq := H.rootNeighbors_bound he
  have hlen := H.redEdges_le_from_root he 1 hr
  change H.redEdges.length = 5 at hw
  omega

omit [DecidableEq V] in
private theorem Graph.two_red_links_need_cross {x y a b : V}
    (hxy : G.RedLink x y) (hab : G.RedLink a b)
    (hxa : G.adjacent x a = false) (hxb : G.adjacent x b = false)
    (hya : G.adjacent y a = false) (hyb : G.adjacent y b = false) : False := by
  rcases hxy with h1 | h1 <;> rcases hab with h2 | h2
  · simpa [hxa, hxb, hya, hyb] using G.strong _ h1 _ h2
  · simpa [hxa, hxb, hya, hyb] using G.strong _ h1 _ h2
  · simpa [hxa, hxb, hya, hyb] using G.strong _ h1 _ h2
  · simpa [hxa, hxb, hya, hyb] using G.strong _ h1 _ h2

private theorem Graph.root_cover_accounting {e : V × V} (he : e ∈ G.redEdges) :
    total (G.rootNeighbors e.1 e.2) G.redDegree =
      G.redEdges.length - 1 +
        (G.redEdges.filter (fun f => decide
          (f.1 ∈ G.rootNeighbors e.1 e.2 ∧ f.2 ∈ G.rootNeighbors e.1 e.2))).length := by
  let roots := G.rootNeighbors e.1 e.2
  let both (f : V × V) := decide (f.1 ∈ roots ∧ f.2 ∈ roots)
  let other (f : V × V) := decide (f ≠ e)
  have hn := filter_nodup G.verticesNodup
    (fun z => decide (z ≠ e.1 ∧ z ≠ e.2) && (G.adjacent e.1 z || G.adjacent e.2 z))
  have htally := G.tally_red_incidence roots hn (fun _ => 1)
  have hc : (G.redEdges.filter other).length = G.redEdges.length - 1 := by
    rw [← List.length_erase_of_mem he]
    apply card_by_membership (filter_nodup G.redNodup _) (G.redNodup.erase e)
    intro f
    rw [G.redNodup.mem_erase_iff, List.mem_filter]
    simp [other, and_comm]
  change total roots G.redDegree = _ + (G.redEdges.filter both).length
  rw [← hc, card_as_total G.redEdges other, card_as_total G.redEdges both, ← total_add]
  have ht : total roots G.redDegree = total G.redEdges
      (fun f => (if f.1 ∈ roots then 1 else 0) + (if f.2 ∈ roots then 1 else 0)) := by
    simpa only [Nat.one_mul] using htally
  rw [ht]
  apply total_congr
  intro f hf
  by_cases hfe : f = e
  · subst f
    have h1 : e.1 ∉ roots := fun h => (G.rootNeighbors_mem.mp h).2.1 rfl
    have h2 : e.2 ∉ roots := fun h => (G.rootNeighbors_mem.mp h).2.2.1 rfl
    simp [other, both, h1, h2]
  rcases G.red_edge_meets_rootNeighbors he hf hfe with hx | hy
  · change f.1 ∈ roots at hx
    by_cases hy : f.2 ∈ roots <;> simp [other, both, hx, hy, hfe]
  · change f.2 ∈ roots at hy
    by_cases hx : f.1 ∈ roots <;> simp [other, both, hx, hy, hfe]

private theorem Graph.extra_neighbor {x y : V} (hy : y ∈ G.neighbors x)
    (hd : G.degree x = 2) :
    ∃ z, (G.neighbors x).erase y = [z] ∧ z ≠ y ∧ z ≠ x ∧ z ∈ G.neighbors x := by
  have hlen := List.length_erase_of_mem hy
  change ((G.neighbors x).erase y).length = G.degree x - 1 at hlen
  rw [hd] at hlen
  obtain ⟨z, hz⟩ := List.length_eq_one_iff.mp hlen
  have hm : z ∈ (G.neighbors x).erase y := by rw [hz]; simp
  obtain ⟨hzy, hzn⟩ := (filter_nodup G.verticesNodup (G.adjacent x)).mem_erase_iff.mp hm
  have hzx : z ≠ x := fun he => G.not_root_neighbor x (he ▸ hzn)
  exact ⟨z, hz, hzy, hzx, hzn⟩

private theorem Graph.neighbor_erasure_pair {x y z w : V}
    (hz : (G.neighbors x).erase y = [z]) (hw : w ∈ G.neighbors x) :
    w = y ∨ w = z := by
  by_cases hw' : w = y
  · exact .inl hw'
  · have hh := (List.mem_erase_of_ne hw').mpr hw
    rw [hz, List.mem_singleton] at hh
    exact .inr hh

private theorem Graph.two_colors_no_five (color : V → Bool)
    (hcolor : ∀ e ∈ G.redEdges, color e.1 ≠ color e.2)
    (hmax : ∀ x ∈ G.vertices, G.degree x ≤ 2) :
    G.redEdges.length ≤ 4 := by
  by_cases hfin : G.redEdges.length ≤ 4
  · exact hfin
  have hs : G.redEdges.length = 5 := by
    have h := G.red_max_two_bound hmax
    omega
  have hpos : 0 < G.redEdges.length := by omega
  have he0 : ∃ e, e ∈ G.redEdges := by
    cases h : G.redEdges with
    | nil => simp [h] at hpos
    | cons e es => exact ⟨e, by simp⟩
  obtain ⟨⟨x, y⟩, he⟩ := he0
  let R := G.rootNeighbors x y
  have hxv := (G.redVertices _ he).1
  have hyv := (G.redVertices _ he).2
  have hx := hmax x hxv
  have hy := hmax y hyv
  have hq := G.rootNeighbors_bound he
  have hr := G.redEdges_le_from_root he 2 (fun z hz =>
    Nat.le_trans (G.redDegree_le_degree z) (hmax z (G.rootNeighbors_mem.mp hz).1))
  change R.length + 2 ≤ G.degree x + G.degree y at hq
  change G.redEdges.length ≤ 1 + R.length * 2 at hr
  have hx2 : G.degree x = 2 := by omega
  have hy2 : G.degree y = 2 := by omega
  have hr2 : R.length = 2 := by omega
  have hxy : y ∈ G.neighbors x := List.mem_filter.mpr ⟨hyv, G.redAdjacent _ he⟩
  have hyx : x ∈ G.neighbors y := List.mem_filter.mpr ⟨hxv, G.edge_symmetric he⟩
  obtain ⟨a, hea, hay, hax, ha⟩ := G.extra_neighbor hxy hx2
  obtain ⟨b, heb, hbx, hby, hb⟩ := G.extra_neighbor hyx hy2
  have hxa_adj := (List.mem_filter.mp ha).2
  have hyb_adj := (List.mem_filter.mp hb).2
  have hav := (List.mem_filter.mp ha).1
  have hbv := (List.mem_filter.mp hb).1
  have haR : a ∈ R := G.rootNeighbors_mem.mpr ⟨hav, hax, hay, .inl hxa_adj⟩
  have hbR : b ∈ R := G.rootNeighbors_mem.mpr ⟨hbv, hbx, hby, .inr hyb_adj⟩
  have hList : ∀ z ∈ R, z = a ∨ z = b := by
    intro z hz
    obtain ⟨hzv, hzx, hzy, hAdj⟩ := G.rootNeighbors_mem.mp hz
    rcases hAdj with h | h
    · exact .inl ((G.neighbor_erasure_pair hea (List.mem_filter.mpr ⟨hzv, h⟩)).resolve_left hzy)
    · exact .inr ((G.neighbor_erasure_pair heb (List.mem_filter.mpr ⟨hzv, h⟩)).resolve_left hzx)
  have hRnodup := filter_nodup G.verticesNodup
    (fun z => decide (z ≠ x ∧ z ≠ y) && (G.adjacent x z || G.adjacent y z))
  have hab : a ≠ b := by
    intro h
    have hsub : R ⊆ [a] := by
      intro z hz
      exact List.mem_singleton.mpr ((hList z hz).elim id (fun hb' => hb'.trans h.symm))
    have hbound := hRnodup.length_le_of_subset hsub
    simp only [List.length_cons, List.length_nil] at hbound
    change R.length ≤ 1 at hbound
    omega
  have hsum : total R G.redDegree = G.redDegree a + G.redDegree b := by
    have hpoint (z : V) (hz : z ∈ R) :
        G.redDegree z = (if z = a then G.redDegree a else 0) +
          (if z = b then G.redDegree b else 0) := by
      rcases hList z hz with h | h <;> subst z <;> simp [hab, Ne.symm hab]
    rw [total_congr R hpoint, total_add, sum_matching R hRnodup,
      sum_matching R hRnodup, if_pos haR, if_pos hbR]
  have hacc := G.root_cover_accounting he
  let both := G.redEdges.filter (fun f => decide (f.1 ∈ R ∧ f.2 ∈ R))
  change total R G.redDegree = G.redEdges.length - 1 + both.length at hacc
  have hared := G.redDegree_le_degree a
  have hbred := G.redDegree_le_degree b
  have ha2 := hmax a hav
  have hb2 := hmax b hbv
  have hafull : G.redDegree a = G.degree a := by omega
  have hbfull : G.redDegree b = G.degree b := by omega
  have hbdeg : G.degree b = 2 := by omega
  have hboth : both.length = 0 := by omega
  have hba : G.adjacent b a = false := by
    cases hj : G.adjacent b a
    · rfl
    · have hlink := G.neighbor_red_link (List.mem_filter.mpr ⟨hav, hj⟩) hbfull
      have hp : 0 < both.length := List.length_filter_pos_iff.mpr (by
        rcases hlink with h | h
        · exact ⟨(b, a), h, decide_eq_true ⟨hbR, haR⟩⟩
        · exact ⟨(a, b), h, decide_eq_true ⟨haR, hbR⟩⟩)
      omega
  have hay' : y ∈ G.neighbors b := List.mem_filter.mpr
    ⟨hyv, (G.symmetric b y).trans hyb_adj⟩
  have hax' : x ∈ G.neighbors a := List.mem_filter.mpr
    ⟨hxv, (G.symmetric a x).trans hxa_adj⟩
  have haxR := G.neighbor_red_link hax' hafull
  have hbyR := G.neighbor_red_link hay' hbfull
  obtain ⟨d, hed, hdy, hdb, hd⟩ := G.extra_neighbor hay' hbdeg
  have hdv := (List.mem_filter.mp hd).1
  have hbdR := G.neighbor_red_link hd hbfull
  have hda : d ≠ a := by
    intro h
    have h' := (List.mem_filter.mp hd).2
    rw [h, hba] at h'
    cases h'
  have hcol (u v : V) : G.RedLink u v → color u ≠ color v := by
    intro hl
    rcases hl with hl | hl
    · exact hcolor _ hl
    · exact Ne.symm (hcolor _ hl)
  have hcxy : color x ≠ color y := hcolor _ he
  have hcax := hcol a x haxR
  have hcby := hcol b y hbyR
  have hcbd := hcol b d hbdR
  have hdc : color d = color a := by
    cases hx' : color x <;> cases hy' : color y <;> cases ha' : color a <;>
      cases hb' : color b <;> cases hd' : color d <;> simp_all
  have hadj_xb : G.adjacent x b = false := by
    cases h : G.adjacent x b
    · rfl
    · have hp := G.neighbor_erasure_pair hea (List.mem_filter.mpr ⟨hbv, h⟩)
      exact (hp.elim hby (Ne.symm hab)).elim
  have hadj_xd : G.adjacent x d = false := by
    cases h : G.adjacent x d
    · rfl
    · have hp := G.neighbor_erasure_pair hea (List.mem_filter.mpr ⟨hdv, h⟩)
      exact (hp.elim hdy hda).elim
  have hadj_ad : G.adjacent a d = false := by
    cases h : G.adjacent a d
    · rfl
    · have hl := G.neighbor_red_link (List.mem_filter.mpr ⟨hdv, h⟩) hafull
      exact (hcol _ _ hl hdc.symm).elim
  have hxaR : G.RedLink x a := haxR.symm
  exact (G.two_red_links_need_cross hxaR hbdR hadj_xb hadj_xd
    ((G.symmetric a b).trans hba) hadj_ad).elim

private theorem Graph.outer_color {v a : V} (ha : a ∈ G.neighbors v)
    (hv4 : G.degree v = 4) (hfull : G.redDegree v = G.degree v)
    (hmax : ∀ x, G.degree x ≤ 4) (hp : G.acrossCount v = 12)
    (hw : (G.outer v).redEdges.length = 5)
    {e : V × V} (he : e ∈ (G.outer v).redEdges) :
    G.adjacent e.1 a ≠ G.adjacent e.2 a := by
  let A := G.neighbors v
  let p := G.adjacent e.1
  let q := G.adjacent e.2
  have heq := G.outer_signatures_complementary hv4 hfull hmax hp hw he
  have ⟨he', hm1, hm2⟩ := G.outer_mem.mp he
  have hcover (z : V) (hz : z ∈ A) : p z = true ∨ q z = true :=
    G.covers_root_neighbors he' (G.outside_mem.mp hm1).2.2
      (G.outside_mem.mp hm2).2.2 hfull hz
  have hcount :
      A.length + (A.filter (fun z => p z && q z)).length =
        G.signatureSize v e.1 + G.signatureSize v e.2 := by
    calc
      _ = total A (fun _ => 1) + total A (fun z => if p z && q z then 1 else 0) := by
        rw [total_const, Nat.mul_one]
        exact congrArg (fun n => A.length + n) (card_as_total A _)
      _ = total A (fun z => if p z then 1 else 0) +
          total A (fun z => if q z then 1 else 0) := by
        rw [← total_add, ← total_add]
        apply total_congr
        intro z hz
        have h := hcover z hz
        cases hx : p z <;> cases hy : q z <;> simp_all
      _ = _ := by
        rw [← card_as_total A p, ← card_as_total A q]
        rfl
  change G.degree v + (A.filter (fun z => p z && q z)).length = _ at hcount
  intro h
  have hadj : p a = true ∧ q a = true := by
    change p a = q a at h
    exact (hcover a ha).elim (fun h' => ⟨h', h.symm.trans h'⟩)
      (fun h' => ⟨h.trans h', h'⟩)
  have hpos : 0 < (A.filter (fun z => p z && q z)).length :=
    List.length_filter_pos_iff.mpr ⟨a, ha, (Bool.and_eq_true _ _).mpr hadj⟩
  omega

/-- Degree-four support bound in the proof of Theorem 3.9. -/
theorem Graph.degree_four_simple_bound (hmax : ∀ x, G.degree x ≤ 4) :
    G.redEdges.length ≤ 20 := by
  apply Classical.byContradiction
  intro hc
  have hs : 21 ≤ G.redEdges.length := by omega
  obtain ⟨v, _, hvred, hv4, _, _, hp, hw, _⟩ := G.large_root_profile hmax hs
  have hfull : G.redDegree v = G.degree v := hvred.trans hv4.symm
  let A := G.neighbors v
  have hpos : 0 < A.length := by change 0 < G.degree v; omega
  have ha' : ∃ a, a ∈ A := by
    cases h : A with
    | nil => simp [h] at hpos
    | cons a as => exact ⟨a, by simp⟩
  obtain ⟨a, ha⟩ := ha'
  let T := G.outerTwo v
  have hsub : (G.outer v).redEdges ⊆ T.redEdges := by
    intro e he
    obtain ⟨hc1, hc2⟩ := G.outer_all_two hv4 hfull hmax hp hw he
    obtain ⟨her, hm1, hm2⟩ := G.outer_mem.mp he
    exact G.induced_red_mem.mpr ⟨her, G.outerTwo_mem.mpr ⟨hm1, hc1⟩,
      G.outerTwo_mem.mpr ⟨hm2, hc2⟩⟩
  have hcolor (e : V × V) (he : e ∈ T.redEdges) :
      G.adjacent e.1 a ≠ G.adjacent e.2 a := by
    obtain ⟨her, h1, h2⟩ := G.induced_red_mem.mp he
    have hmem := G.outer_mem.mpr ⟨her, (G.outerTwo_mem.mp h1).1, (G.outerTwo_mem.mp h2).1⟩
    exact G.outer_color ha hv4 hfull hmax hp hw hmem
  have ht := T.two_colors_no_five (fun x => G.adjacent x a) hcolor
    (fun x hx => G.outerTwo_degree_le v hmax hx)
  have hlen := (G.outer v).redNodup.length_le_of_subset hsub
  omega

#print axioms Graph.degree_four_simple_bound

end Counts

end FGST.Chapter3.DegreeFour
