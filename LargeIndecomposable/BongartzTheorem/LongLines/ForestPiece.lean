module

public import LargeIndecomposable.BongartzTheorem.ContourExclusion.ContourFree

/-!
# Without contours, convex pieces are forests

If a ray category has no contours, parallel paths of the universal cover with the same nonzero
value are equal, so every weight on the arrows is a cocycle. Local simple connectivity then shows
that every arrow of a finite convex piece is a bridge (`gr_isAcyclic`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver Module Classical Statement SimpleGraph

universe u

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P}

/-- The label of an arrow of the cover. -/
def arrLabel {x y : RayVert (Cover x₀)} (e : x ⟶ y) : (quiver P).A :=
  ⟨x.out.y, y.out.y, Cover.val e.1, isIrreducible_val e.2⟩

/-- The labels of a path of the cover. -/
def labels {x : RayVert (Cover x₀)} : ∀ {y : RayVert (Cover x₀)}, Quiver.Path x y →
    List (quiver P).A
  | _, .nil => []
  | _, .cons p e => labels p ++ [arrLabel e]

lemma labels_path {x : RayVert (Cover x₀)} : ∀ {y : RayVert (Cover x₀)} (p : Quiver.Path x y),
    PathFrom (D := quiver P) x.out.y (labels p) y.out.y
  | _, .nil => rfl
  | _, .cons p e => RayQuiver.pathFrom_append _ _ _ _ _ (labels_path p) ⟨rfl, rfl⟩

lemma pathMor_labels {x : RayVert (Cover x₀)} : ∀ {y : RayVert (Cover x₀)} (p : Quiver.Path x y),
    pathMor (labels p) x.out.y y.out.y (labels_path p) = Cover.val (pathVal p)
  | _, .nil => rfl
  | _, .cons p e => by
    have h1 := RayQuiver.pathMor_append (labels p) [arrLabel e] _ _ _ (labels_path p) ⟨rfl, rfl⟩
    refine h1.trans ?_
    rw [pathMor_labels p]
    change Cover.val (pathVal p) ≫ (eqToHom rfl ≫ Cover.val e.1 ≫ eqToHom rfl) =
      Cover.val (pathVal p ≫ e.1)
    rw [val_comp]
    simp

/-- An arrow is determined by its target and its label. -/
lemma arrow_eq_of_label {a a' y : RayVert (Cover x₀)} (e : a ⟶ y) (e' : a' ⟶ y)
    (h : arrLabel e = arrLabel e') : a = a' ∧ HEq e e' := by
  have hy : a.out.y = a'.out.y := (Sigma.mk.inj h).1
  obtain ⟨ya, ua⟩ := a
  obtain ⟨ya', ua'⟩ := a'
  change ya = ya' at hy
  subst hy
  have h3 := eq_of_heq (Sigma.mk.inj h).2
  have hv0 := congrArg Subtype.val (eq_of_heq (Sigma.mk.inj h3).2)
  obtain ⟨o, ho⟩ := e
  obtain ⟨o', ho'⟩ := e'
  rcases o with _ | f
  · exact absurd rfl ho.1
  rcases o' with _ | f'
  · exact absurd rfl ho'.1
  have hv : f.1 = f'.1 := hv0
  have haa : (⟨ya, ua⟩ : Cover x₀) = ⟨ya, ua'⟩ := source_eq f f' rfl (heq_of_eq hv)
  cases haa
  refine ⟨rfl, heq_of_eq (Subtype.ext ?_)⟩
  exact Cover.val_injective hv0

/-- A path of the cover is determined by its labels. -/
theorem path_eq_of_labels {x : RayVert (Cover x₀)} : ∀ {y : RayVert (Cover x₀)}
    (p q : Quiver.Path x y), labels p = labels q → p = q := by
  intro y p
  induction p with
  | nil =>
    intro q h
    cases q with
    | nil => rfl
    | cons q e =>
      have : labels q ++ [arrLabel e] = [] := h.symm
      simp at this
  | cons p e ih =>
    intro q h
    cases q with
    | nil =>
      have : labels p ++ [arrLabel e] = [] := h
      simp at this
    | cons q e' =>
      have h1 : labels p ++ [arrLabel e] = labels q ++ [arrLabel e'] := h
      obtain ⟨h2, h3⟩ := List.append_inj' h1 rfl
      have h4 : arrLabel e = arrLabel e' := by simpa using h3
      obtain ⟨rfl, h5⟩ := arrow_eq_of_label e e' h4
      obtain rfl := eq_of_heq h5
      rw [ih q h2]


/-- **Without contours, parallel nonzero paths are equal.** -/
theorem path_eq_of_noContour (hnc : NoContour P) {x y : RayVert (Cover x₀)}
    (p q : Quiver.Path x y) (he : pathVal p = pathVal q) (h0 : pathVal p ≠ 0) : p = q := by
  apply path_eq_of_labels
  have hv : Cover.val (pathVal p) ≠ 0 := fun h ↦ h0 ((val_eq_zero_iff _).1 h)
  refine hnc _ _ _ _ (labels_path p) (labels_path q) ?_ ?_
  · rw [pathMor_labels, pathMor_labels, he]
  · rw [pathMor_labels]
    exact hv

section Forest

variable {S : Finset (Cover x₀)} {k : Type u} [Field k]
  (hacyc : ∀ (i : (pieceQuiver S).V) (l : List (pieceQuiver S).A), l ≠ [] → ¬PathFrom i l i)

/-- The weight of a single arrow. -/
def edgeWeight (a b : Cover x₀) : ArrowWeight (Cover x₀) := fun {x y} _ ↦ if x = a ∧ y = b then 1 else 0

include hacyc in
/-- **An arrow of a convex piece is a bridge.** -/
lemma not_reachable_arrow (hnc : NoContour P) (hS : Convex (S : Set (Cover x₀)))
    (hlsc : CoverLocalSC x₀) {a b : (pieceQuiver S).V}
    (hab : (pieceDirData (k := k) hacyc).Arr a b) :
    ¬((pieceDirData (k := k) hacyc).gr.deleteEdges {s(a, b)}).Reachable a b := by
  intro hreach
  let D := pieceDirData (k := k) hacyc
  let H : Set (Cover x₀) := (S : Set (Cover x₀))
  let c : ArrowWeight (Cover x₀) := @fun _ _ e ↦ edgeWeight (pt S a) (pt S b) e
  have hcoc : IsCocycleOn H c := fun p q _ _ he h0 ↦ by
    rw [path_eq_of_noContour hnc p q he h0]
  have hconv : ConvexR H := fun x hx y hy z ⟨p⟩ ⟨q⟩ ↦
    hS x z y hx hy (reach_of_path p) (reach_of_path q)
  obtain ⟨φ, hφ⟩ := hlsc H S.finite_toSet hconv c hcoc
  have hmem : ∀ i : (pieceQuiver S).V, (pt S i) ∈ H := fun i ↦ (show S from i).2
  have hgen : ∀ {x y : (pieceQuiver S).V}, D.Arr x y →
      φ (pt S y) - φ (pt S x) = if pt S x = pt S a ∧ pt S y = pt S b then 1 else 0 := by
    intro x y h
    obtain ⟨α, rfl, rfl, -⟩ := h
    let f : RayVert.mk (pt S ((pieceQuiver S).src α)) ⟶ RayVert.mk (pt S ((pieceQuiver S).tgt α)) :=
      ⟨α.2.2.1, α.2.2.2⟩
    exact (hφ f (hmem _) (hmem _)).symm
  have h1 := hgen hab
  rw [if_pos ⟨rfl, rfl⟩] at h1
  let Z : Set (pieceQuiver S).V := {z | φ (pt S z) = φ (pt S a)}
  have hcl : ∀ z ∈ Z, ∀ z', (D.gr.deleteEdges {s(a, b)}).Adj z z' → z' ∈ Z := by
    intro z hz z' hzz
    obtain ⟨hadj, hne⟩ := deleteEdges_adj.1 hzz
    have hne' : s(z, z') ≠ s(a, b) := fun h ↦ hne (Set.mem_singleton_iff.2 h)
    have hz' : φ (pt S z) = φ (pt S a) := hz
    change φ (pt S z') = φ (pt S a)
    rcases (AR.DirData.gr_adj.1 hadj).2 with h | h
    · have h2 := hgen h
      rw [if_neg] at h2
      · omega
      · rintro ⟨h3, h4⟩
        exact hne' (by rw [show z = a from Subtype.ext h3, show z' = b from Subtype.ext h4])
    · have h2 := hgen h
      rw [if_neg] at h2
      · omega
      · rintro ⟨h3, h4⟩
        apply hne'
        rw [show z' = a from Subtype.ext h3, show z = b from Subtype.ext h4, Sym2.eq_swap]
  have h2 : φ (pt S b) = φ (pt S a) := AR.DirData.mem_of_reachable (S := Z) hcl rfl hreach
  omega

/-- **Without contours, convex pieces are forests.** -/
theorem gr_isAcyclic (hnc : NoContour P) (hS : Convex (S : Set (Cover x₀)))
    (hlsc : CoverLocalSC x₀) : (pieceDirData (k := k) hacyc).gr.IsAcyclic := by
  refine isAcyclic_iff_forall_adj_isBridge.2 fun v w hadj ↦ ?_
  rw [isBridge_iff]
  rcases (AR.DirData.gr_adj.1 hadj).2 with h | h
  · exact not_reachable_arrow hacyc hnc hS hlsc h
  · intro hr
    have h1 := not_reachable_arrow hacyc hnc hS hlsc h
    have e1 : s(w, v) = s(v, w) := Sym2.eq_swap
    apply h1
    change ((pieceDirData (k := k) hacyc).gr.deleteEdges {s(w, v)}).Reachable w v
    rw [e1]
    exact hr.symm

end Forest

end LargeIndecomposable.RayCat
