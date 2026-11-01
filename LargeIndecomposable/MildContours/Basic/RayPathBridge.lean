module

public import LargeIndecomposable.MildContours.Basic.Assembly
public import LargeIndecomposable.RayCategories.Basic.ResidueQuiver
public import LargeIndecomposable.RayCategories.Contours.ProperPathInterlacement

/-!
# From the reversed ray paths to paths of `Q_P`

the reversed ray quiver on `RayVertex C` is reversed: an arrow `i ⟶ j` is an
irreducible morphism `j.obj ⟶ i.obj`, and `rayPathMap (p.comp q) =
rayPathMap q ≫ rayPathMap p`. A reversed ray path `p : i ⟶ j` therefore becomes a path
`toP p` of the quiver of `P = RaySmall C` from `⟨j.obj⟩` to `⟨i.obj⟩` with
value `sh (rayPathMap p)`; the reverse translation `fromP` sends interlacing
steps of nonzero paths to proper-whisker steps, so non-interlaced reversed
contours give non-interlaced contours of `P`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable

universe v u

namespace RayCat

variable {C : Type} [Category.{v} C] [HasZeroMorphisms C] [LocallySmall.{0} C]

omit [LocallySmall.{0} C] in
lemma rayPathMap_comp' {i j l : RayVertex C} (p : Quiver.Path i j) (q : Quiver.Path j l) :
    rayPathMap (p.comp q) = rayPathMap q ≫ rayPathMap p :=
  LinearPathCategory.pathMap_comp _ _ p q

omit [LocallySmall.{0} C] in
lemma rayPathMap_nil' (i : RayVertex C) : rayPathMap (Quiver.Path.nil : Quiver.Path i i) = 𝟙 i.obj :=
  LinearPathCategory.pathMap_nil _ _ i

omit [LocallySmall.{0} C] in
lemma rayPathMap_cons' {i j l : RayVertex C} (p : Quiver.Path i j) (a : j ⟶ l) :
    rayPathMap (p.cons a) = a.1 ≫ rayPathMap p :=
  LinearPathCategory.pathMap_cons _ _ p a

/-- An arrow of the reversed ray quiver as an arrow of the quiver of `RaySmall C`. -/
def reversedArr {i j : RayVertex C} (a : i ⟶ j) :
    (RayVert.mk (⟨j.obj⟩ : RaySmall.{0} C) : RayVert (RaySmall.{0} C)) ⟶ RayVert.mk ⟨i.obj⟩ :=
  ⟨RaySmall.sh a.1, (RaySmall.isIrreducible_sh_iff _).2 ((isIrreducible_iff_isIrreducibleRayMorphism _).2 a.2)⟩

/-- A reversed ray path, reversed into a path of the quiver of `RaySmall C`. -/
def toP {i : RayVertex C} : ∀ {j : RayVertex C}, Quiver.Path i j →
    Quiver.Path (RayVert.mk (⟨j.obj⟩ : RaySmall.{0} C) : RayVert (RaySmall.{0} C))
      (RayVert.mk ⟨i.obj⟩)
  | _, .nil => .nil
  | _, .cons p a => (Quiver.Path.nil.cons (reversedArr a)).comp (toP p)

lemma pathVal_toP {i : RayVertex C} : ∀ {j : RayVertex C} (p : Quiver.Path i j),
    pathVal (toP p) = RaySmall.sh (rayPathMap p)
  | _, .nil => by
      rw [rayPathMap_nil']; exact (RaySmall.sh_id (⟨i.obj⟩ : RaySmall.{0} C)).symm
  | _, .cons p a => by
      change pathVal ((Quiver.Path.nil.cons (reversedArr a)).comp (toP p)) = _
      rw [pathVal_comp, pathVal_toP p, rayPathMap_cons']
      refine Eq.trans ?_ (RaySmall.sh_comp (X := (⟨_⟩ : RaySmall.{0} C)) (Y := ⟨_⟩)
        (Z := ⟨_⟩) _ _).symm
      rw [show pathVal (Quiver.Path.nil.cons (reversedArr a)) = (reversedArr a).1 from Category.id_comp _]
      rfl

/-- An arrow of the quiver of `RaySmall C` as an arrow of the reversed ray quiver. -/
def fromArr {X Y : RayVert (RaySmall.{0} C)} (e : X ⟶ Y) :
    (⟨Y.out.as⟩ : RayVertex C) ⟶ ⟨X.out.as⟩ :=
  ⟨(RaySmall.sh).symm e.1, (isIrreducible_iff_isIrreducibleRayMorphism _).1 ((RaySmall.isIrreducible_sh_iff _).1 (by
    rw [Equiv.apply_symm_apply]; exact e.2))⟩

/-- A path of the quiver of `RaySmall C`, reversed into a reversed ray path. -/
def fromP {X : RayVert (RaySmall.{0} C)} : ∀ {Y : RayVert (RaySmall.{0} C)}, Quiver.Path X Y →
    Quiver.Path (⟨Y.out.as⟩ : RayVertex C) ⟨X.out.as⟩
  | _, .nil => .nil
  | _, .cons p e => (Quiver.Path.nil.cons (fromArr e)).comp (fromP p)

lemma fromP_comp {X Y : RayVert (RaySmall.{0} C)} (p : Quiver.Path X Y) :
    ∀ {Z : RayVert (RaySmall.{0} C)} (q : Quiver.Path Y Z), fromP (p.comp q) = (fromP q).comp (fromP p)
  | _, .nil => (Quiver.Path.nil_comp _).symm
  | _, .cons q e => by
      change (Quiver.Path.nil.cons (fromArr e)).comp (fromP (p.comp q)) =
        ((Quiver.Path.nil.cons (fromArr e)).comp (fromP q)).comp _
      rw [fromP_comp p q, Quiver.Path.comp_assoc]

lemma rayPathMap_fromP {X : RayVert (RaySmall.{0} C)} : ∀ {Y : RayVert (RaySmall.{0} C)}
    (p : Quiver.Path X Y), rayPathMap (fromP p) = (RaySmall.sh).symm (pathVal p)
  | _, .nil => by
      change rayPathMap (Quiver.Path.nil : Quiver.Path (⟨X.out.as⟩ : RayVertex C) _) = _
      rw [rayPathMap_nil']
      change 𝟙 X.out.as = (RaySmall.sh).symm (𝟙 X.out)
      rw [← RaySmall.sh_id, Equiv.symm_apply_apply]
  | _, .cons p e => by
      change rayPathMap ((Quiver.Path.nil.cons (fromArr e)).comp (fromP p)) = _
      rw [rayPathMap_comp', rayPathMap_fromP p, rayPathMap_cons', rayPathMap_nil',
        Category.comp_id]
      change _ = (RaySmall.sh).symm (pathVal p ≫ e.1)
      rw [RaySmall.sh_symm_comp]; rfl

lemma fromP_toP {i : RayVertex C} : ∀ {j : RayVertex C} (p : Quiver.Path i j), fromP (toP p) = p
  | _, .nil => rfl
  | _, .cons p a => by
      change fromP ((Quiver.Path.nil.cons (reversedArr a)).comp (toP p)) = p.cons a
      rw [fromP_comp, fromP_toP p]
      change p.comp ((Quiver.Path.nil.cons (fromArr (reversedArr a))).comp .nil) = p.cons a
      have : fromArr (reversedArr a) = a := Subtype.ext (Equiv.symm_apply_apply _ _)
      rw [this]; rfl

lemma length_fromP {X : RayVert (RaySmall.{0} C)} : ∀ {Y : RayVert (RaySmall.{0} C)}
    (p : Quiver.Path X Y), (fromP p).length = p.length
  | _, .nil => rfl
  | _, .cons p e => by
      change ((Quiver.Path.nil.cons (fromArr e)).comp (fromP p)).length = _
      rw [Quiver.Path.length_comp, length_fromP p]; simp; omega

lemma symm_sh_ne_zero {X Y : RaySmall.{0} C} {f : X ⟶ Y} (hf : f ≠ 0) : (RaySmall.sh).symm f ≠ 0 := by
  intro h
  apply hf
  have := congrArg RaySmall.sh h
  rw [Equiv.apply_symm_apply] at this
  rw [this, RaySmall.sh_zero]

/-- An interlacing step of nonzero paths is a proper-whisker step. -/
lemma reversedStep_of_interStep {X Y : RayVert (RaySmall.{0} C)} {u w : Quiver.Path X Y}
    (h : InterStep u w) (h0 : pathVal u ≠ 0) :
    ProperWhiskerInterlacementStep (rayPathContourRelation (C := C)) (fromP u) (fromP w) := by
  have hval := interStep_val h
  obtain ⟨a, b, s, v', w', t, rfl, rfl, hv, hv0, hlen⟩ := h
  refine ⟨⟨b.out.as⟩, ⟨a.out.as⟩, fromP t, fromP v', fromP w', fromP s, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_,
    ?_, ?_⟩
  · rw [rayPathMap_fromP]; exact symm_sh_ne_zero hv0
  · rw [rayPathMap_fromP, rayPathMap_fromP, hv]
  · rw [Quiver.Path.comp_assoc, ← fromP_comp, ← fromP_comp, rayPathMap_fromP]
    exact symm_sh_ne_zero h0
  · rw [Quiver.Path.comp_assoc, ← fromP_comp, ← fromP_comp, Quiver.Path.comp_assoc,
      ← fromP_comp, ← fromP_comp, rayPathMap_fromP, rayPathMap_fromP,
      ← Quiver.Path.comp_assoc, ← Quiver.Path.comp_assoc, hval]
  · rw [length_fromP, length_fromP]; omega
  · rw [fromP_comp, fromP_comp, Quiver.Path.comp_assoc]
  · rw [fromP_comp, fromP_comp, Quiver.Path.comp_assoc]

/-- Interlaced nonzero paths of `RaySmall C` reverse to interlaced ray paths. -/
lemma reversedInterlaced_of_interlaced {X Y : RayVert (RaySmall.{0} C)} {u w : Quiver.Path X Y}
    (h : Interlaced u w) (h0 : pathVal u ≠ 0) :
    (properWhiskerInterlacementRelation (rayPathContourRelation (C := C))).interlaced
      (fromP u) (fromP w) := by
  induction h with
  | rel u w h => exact Relation.EqvGen.rel _ _ (reversedStep_of_interStep h h0)
  | refl => exact Relation.EqvGen.refl _
  | symm u w h ih =>
      have : pathVal u ≠ 0 := by rw [interlaced_val h]; exact h0
      exact Relation.EqvGen.symm _ _ (ih this)
  | trans u w z h₁ h₂ ih₁ ih₂ =>
      have : pathVal w ≠ 0 := by rw [← interlaced_val h₁]; exact h0
      exact Relation.EqvGen.trans _ _ _ (ih₁ h0) (ih₂ this)

/-- **Non-interlaced reversed contours give non-interlaced contours of `RaySmall C`.** -/
lemma not_interlaced_toP {i j : RayVertex C} {p q : Quiver.Path i j}
    (h0 : rayPathMap p ≠ 0)
    (hni : ¬(properWhiskerInterlacementRelation (rayPathContourRelation (C := C))).interlaced p q) :
    ¬Interlaced (toP p) (toP q) := by
  intro h
  apply hni
  have := reversedInterlaced_of_interlaced h (by
    rw [pathVal_toP]; exact fun h ↦ h0 ((RaySmall.sh_eq_zero_iff _).1 h))
  rwa [fromP_toP, fromP_toP] at this

end RayCat

end LargeIndecomposable
