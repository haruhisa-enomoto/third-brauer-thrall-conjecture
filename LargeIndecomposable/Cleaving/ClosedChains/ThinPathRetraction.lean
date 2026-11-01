module

public import LargeIndecomposable.Foundations.PathCategories.LinearPathLift
public import LargeIndecomposable.Cleaving.ClosedChains.CleavingTransfer

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable.ClosedZigzagTransfer

universe u v w x

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]
variable {C : Type x} [Category.{max (max u v) w} C]
  [Preadditive C] [Linear k C]

abbrev FreeLinearCategory := LinearPathCategory.Category k Q

/-- Evaluate the unique member of a family of linear functionals when its
index type is inhabited, and return zero when it is empty. -/
def coefficientOrZero {P V : Type*} [AddCommMonoid V] [Module k V]
    (c : P → V →ₗ[k] k) (g : V) : k := by
  classical
  exact if h : Nonempty P then c (Classical.choice h) g else 0

@[simp]
theorem coefficientOrZero_of_nonempty {P V : Type*}
    [AddCommMonoid V] [Module k V] (c : P → V →ₗ[k] k)
    (g : V) (h : Nonempty P) :
    coefficientOrZero c g = c (Classical.choice h) g := by
  classical
  simp [coefficientOrZero, h]

@[simp]
theorem coefficientOrZero_of_isEmpty {P V : Type*}
    [AddCommMonoid V] [Module k V] (c : P → V →ₗ[k] k)
    (g : V) (h : IsEmpty P) : coefficientOrZero c g = 0 := by
  classical
  simp [coefficientOrZero, not_nonempty_iff.mpr h]

/-- Scalar coefficient data for a linear functor out of a thin free path
category.  The last field is the scalar form of the two-variable naturality
required by BGRS Proposition 3.2.  In a radical-square-zero quiver its paths
are only identities and arrows, so this is precisely the finite family of
stable-supplement inclusions used in BGRS 3.4 and 3.7. -/
structure ThinPathCoefficientData
    (D : FreeLinearCategory (k := k) (Q := Q) ⥤ C)
    [D.Additive] [D.Linear k] where
  path_subsingleton : ∀ a b : Q, Subsingleton (Quiver.Path a b)
  coefficient : ∀ {X Y : FreeLinearCategory (k := k) (Q := Q)},
    Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X) →
      (D.obj X ⟶ D.obj Y) →ₗ[k] k
  normalized : ∀ {X Y : FreeLinearCategory (k := k) (Q := Q)}
      (p : Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X)),
    coefficient p (D.map (LinearPathCategory.pathHom p)) = 1
  whisker_coefficient : ∀
      {X' X Y Y' : FreeLinearCategory (k := k) (Q := Q)}
      (p : Quiver.Path (LinearPathCategory.vertex X)
        (LinearPathCategory.vertex X'))
      (g : D.obj X ⟶ D.obj Y)
      (q : Quiver.Path (LinearPathCategory.vertex Y')
        (LinearPathCategory.vertex Y))
      (r : Quiver.Path (LinearPathCategory.vertex Y')
        (LinearPathCategory.vertex X')),
    coefficient r
        (D.map (LinearPathCategory.pathHom p) ≫ g ≫
          D.map (LinearPathCategory.pathHom q)) =
      coefficientOrZero
        (fun s : Quiver.Path (LinearPathCategory.vertex Y)
            (LinearPathCategory.vertex X) ↦ coefficient s) g

namespace ThinPathCoefficientData

variable {D : FreeLinearCategory (k := k) (Q := Q) ⥤ C}
variable [D.Additive] [D.Linear k]

/-- The path-coefficient projection.  Thinness makes a nonempty path set a
singleton, so one scalar reconstructs the entire source Hom element. -/
def retraction (h : ThinPathCoefficientData (k := k) D)
    (X Y : FreeLinearCategory (k := k) (Q := Q)) :
    (D.obj X ⟶ D.obj Y) →ₗ[k] (X ⟶ Y) := by
  classical
  by_cases hp : Nonempty (Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X))
  · exact (h.coefficient (Classical.choice hp)).smulRight
      (LinearPathCategory.pathHom (Classical.choice hp))
  · exact 0

@[simp]
theorem retraction_apply_of_nonempty
    (h : ThinPathCoefficientData (k := k) D)
    (X Y : FreeLinearCategory (k := k) (Q := Q))
    (hp : Nonempty (Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)))
    (g : D.obj X ⟶ D.obj Y) :
    h.retraction X Y g =
      h.coefficient (Classical.choice hp) g •
        LinearPathCategory.pathHom (Classical.choice hp) := by
  classical
  simp [retraction, hp]

@[simp]
theorem retraction_apply_of_isEmpty
    (h : ThinPathCoefficientData (k := k) D)
    (X Y : FreeLinearCategory (k := k) (Q := Q))
    (hp : IsEmpty (Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)))
    (g : D.obj X ⟶ D.obj Y) :
    h.retraction X Y g = 0 := by
  classical
  simp [retraction, not_nonempty_iff.mpr hp]

private theorem hom_eq_zero_of_path_isEmpty
    (X Y : FreeLinearCategory (k := k) (Q := Q))
    (hp : IsEmpty (Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X))) (f : X ⟶ Y) :
    f = 0 := by
  apply (LinearPathCategory.homPathLinearEquiv X Y).injective
  ext p
  exact (hp.false p).elim

@[simp]
theorem retraction_map
    (h : ThinPathCoefficientData (k := k) D)
    {X Y : FreeLinearCategory (k := k) (Q := Q)} (f : X ⟶ Y) :
    h.retraction X Y (D.map f) = f := by
  classical
  letI : Subsingleton (Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) :=
    h.path_subsingleton _ _
  have hlinear :
      (h.retraction X Y).comp (D.mapLinearMap k) = LinearMap.id := by
    apply (LinearPathCategory.homPathBasis X Y).ext
    intro p
    simp only [LinearMap.comp_apply, LinearMap.id_apply,
      LinearPathCategory.homPathBasis_apply]
    rw [h.retraction_apply_of_nonempty X Y ⟨p⟩]
    rw [Subsingleton.elim (Classical.choice ⟨p⟩) p]
    change h.coefficient p (D.map (LinearPathCategory.pathHom p)) •
      LinearPathCategory.pathHom p = LinearPathCategory.pathHom p
    rw [h.normalized, one_smul]
  exact DFunLike.congr_fun hlinear f

/-- Naturality for path-basis whiskers. -/
private theorem naturality_path
    (h : ThinPathCoefficientData (k := k) D)
    {X' X Y Y' : FreeLinearCategory (k := k) (Q := Q)}
    (p : Quiver.Path (LinearPathCategory.vertex X)
      (LinearPathCategory.vertex X'))
    (g : D.obj X ⟶ D.obj Y)
    (q : Quiver.Path (LinearPathCategory.vertex Y')
      (LinearPathCategory.vertex Y)) :
    h.retraction X' Y'
        (D.map (LinearPathCategory.pathHom p) ≫ g ≫
          D.map (LinearPathCategory.pathHom q)) =
      LinearPathCategory.pathHom p ≫ h.retraction X Y g ≫
        LinearPathCategory.pathHom q := by
  classical
  letI : Subsingleton (Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) := h.path_subsingleton _ _
  letI : Subsingleton (Quiver.Path (LinearPathCategory.vertex Y')
      (LinearPathCategory.vertex X')) := h.path_subsingleton _ _
  by_cases hmiddle : Nonempty
      (Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X))
  · let middle := Classical.choice hmiddle
    let composite : Quiver.Path (LinearPathCategory.vertex Y')
        (LinearPathCategory.vertex X') := q.comp (middle.comp p)
    have hcoeff := h.whisker_coefficient p g q composite
    rw [coefficientOrZero_of_nonempty _ _ hmiddle] at hcoeff
    rw [h.retraction_apply_of_nonempty X' Y' ⟨composite⟩,
      h.retraction_apply_of_nonempty X Y hmiddle]
    rw [Subsingleton.elim (Classical.choice ⟨composite⟩) composite,
      hcoeff, Subsingleton.elim (Classical.choice hmiddle) middle]
    dsimp only [composite]
    simp only [Linear.comp_smul, Linear.smul_comp,
      LinearPathCategory.pathHom_comp, Quiver.Path.comp_assoc]
  · have hmiddle' : IsEmpty
        (Quiver.Path (LinearPathCategory.vertex Y)
          (LinearPathCategory.vertex X)) :=
      not_nonempty_iff.mp hmiddle
    rw [h.retraction_apply_of_isEmpty X Y hmiddle']
    simp only [comp_zero, zero_comp]
    by_cases hlanding : Nonempty
        (Quiver.Path (LinearPathCategory.vertex Y')
          (LinearPathCategory.vertex X'))
    · let r := Classical.choice hlanding
      have hcoeff := h.whisker_coefficient p g q r
      rw [coefficientOrZero_of_isEmpty _ _ hmiddle'] at hcoeff
      rw [h.retraction_apply_of_nonempty X' Y' hlanding,
        Subsingleton.elim (Classical.choice hlanding) r, hcoeff,
        zero_smul]
    · have hlanding' : IsEmpty
          (Quiver.Path (LinearPathCategory.vertex Y')
            (LinearPathCategory.vertex X')) :=
        not_nonempty_iff.mp hlanding
      exact h.retraction_apply_of_isEmpty X' Y' hlanding' _

/-- Pathwise coefficient equations extend by linearity to the full
two-variable Hom-bifunctor retraction. -/
def homBifunctorRetraction
    (h : ThinPathCoefficientData (k := k) D) :
    HomBifunctorRetraction (k := k) D where
  retraction := h.retraction
  map_retraction := h.retraction_map
  naturality := by
    intro X' X Y Y' a g b
    let leftA : (X' ⟶ X) →ₗ[k] ((Y ⟶ Y') →ₗ[k] (X' ⟶ Y')) :=
      { toFun := fun a ↦
          { toFun := fun b ↦ h.retraction X' Y'
              (D.map a ≫ g ≫ D.map b)
            map_add' := by
              intro b c
              simp only [D.map_add, Preadditive.comp_add,
                LinearMap.map_add]
            map_smul' := by
              intro r b
              simp only [D.map_smul, Linear.comp_smul,
                LinearMap.map_smul, RingHom.id_apply] }
        map_add' := by
          intro a c
          apply LinearMap.ext
          intro b
          simp only [D.map_add, Preadditive.add_comp,
            LinearMap.map_add]
          rfl
        map_smul' := by
          intro r a
          apply LinearMap.ext
          intro b
          simp only [D.map_smul, Linear.smul_comp, LinearMap.map_smul,
            RingHom.id_apply]
          rfl }
    let rightA : (X' ⟶ X) →ₗ[k] ((Y ⟶ Y') →ₗ[k] (X' ⟶ Y')) :=
      { toFun := fun a ↦
          { toFun := fun b ↦ a ≫ h.retraction X Y g ≫ b
            map_add' := by
              intro b c
              simp only [Preadditive.comp_add]
            map_smul' := by
              intro r b
              simp only [Linear.comp_smul, RingHom.id_apply] }
        map_add' := by
          intro a c
          apply LinearMap.ext
          intro b
          simp only [Preadditive.add_comp]
          rfl
        map_smul' := by
          intro r a
          apply LinearMap.ext
          intro b
          simp only [Linear.smul_comp, RingHom.id_apply]
          rfl }
    have hA : leftA = rightA := by
      apply (LinearPathCategory.homPathBasis X' X).ext
      intro p
      apply (LinearPathCategory.homPathBasis Y Y').ext
      intro q
      simp only [leftA, rightA, LinearPathCategory.homPathBasis_apply]
      exact h.naturality_path p g q
    exact DFunLike.congr_fun (DFunLike.congr_fun hA a) b

end ThinPathCoefficientData

end LargeIndecomposable.ClosedZigzagTransfer
