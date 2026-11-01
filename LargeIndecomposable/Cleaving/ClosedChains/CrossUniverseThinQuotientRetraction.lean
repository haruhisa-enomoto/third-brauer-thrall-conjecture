module

public import LargeIndecomposable.Foundations.CategoryTheory.LinearIdealQuotient
public import LargeIndecomposable.Cleaving.ClosedChains.CrossUniverseAssembly
public import LargeIndecomposable.Cleaving.ClosedChains.ThinPathRetraction

@[expose] public section

/-!
# Cross-universe thin-path retractions for bound sources

This file is the quotient analogue of `CrossUniverseThinPathRetraction`.
The free quiver is thin, but some of its paths may vanish in a linear
Hom-ideal quotient.  Normalization is therefore stated after multiplying the
quotient path itself.  A killed path imposes no impossible equation such as
`0 = 1`, while the same coefficient table still proves a Hom-bifunctor
retraction of the bound source.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable.ClosedZigzagCrossUniverse

open LargeIndecomposable.PreadditiveHomIdeal

universe u v w x z

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]
variable {C : Type x} [Category.{z} C] [Preadditive C] [Linear k C]

abbrev ThinQuotientFreeCategory := LinearPathCategory.Category k Q

/-- The path-coefficient projection on a pair of chosen free
representatives. -/
def thinQuotientPathProjection
    (I : HomIdeal (ThinQuotientFreeCategory (k := k) (Q := Q)))
    [Preadditive (CategoryTheory.Quotient I.rel)]
    [Linear k (CategoryTheory.Quotient I.rel)]
    [(CategoryTheory.Quotient.functor I.rel).Additive]
    [(CategoryTheory.Quotient.functor I.rel).Linear k]
    (D : CategoryTheory.Quotient I.rel ⥤ C)
    [D.Additive] [D.Linear k]
    (coefficient : ∀
      {X Y : ThinQuotientFreeCategory (k := k) (Q := Q)},
      Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X) →
        (D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
          D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y)) →ₗ[k] k)
    (X Y : ThinQuotientFreeCategory (k := k) (Q := Q)) :
    (D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
      D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y)) →ₗ[k]
      (((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
        ((CategoryTheory.Quotient.functor I.rel).obj Y)) := by
  classical
  by_cases hp : Nonempty (Quiver.Path
      (LinearPathCategory.vertex Y) (LinearPathCategory.vertex X))
  · exact (coefficient (Classical.choice hp)).smulRight
      ((CategoryTheory.Quotient.functor I.rel).map
        (LinearPathCategory.pathHom (Classical.choice hp)))
  · exact 0

@[simp] theorem thinQuotientPathProjection_apply_of_nonempty
    (I : HomIdeal (ThinQuotientFreeCategory (k := k) (Q := Q)))
    [Preadditive (CategoryTheory.Quotient I.rel)]
    [Linear k (CategoryTheory.Quotient I.rel)]
    [(CategoryTheory.Quotient.functor I.rel).Additive]
    [(CategoryTheory.Quotient.functor I.rel).Linear k]
    (D : CategoryTheory.Quotient I.rel ⥤ C)
    [D.Additive] [D.Linear k]
    (coefficient : ∀
      {X Y : ThinQuotientFreeCategory (k := k) (Q := Q)},
      Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X) →
        (D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
          D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y)) →ₗ[k] k)
    (X Y : ThinQuotientFreeCategory (k := k) (Q := Q))
    (hp : Nonempty (Quiver.Path
      (LinearPathCategory.vertex Y) (LinearPathCategory.vertex X)))
    (g : D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
      D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y)) :
    thinQuotientPathProjection I D coefficient X Y g =
      coefficient (Classical.choice hp) g •
        (CategoryTheory.Quotient.functor I.rel).map
          (LinearPathCategory.pathHom (Classical.choice hp)) := by
  classical
  simp only [thinQuotientPathProjection, hp]
  rfl

@[simp] theorem thinQuotientPathProjection_apply_of_isEmpty
    (I : HomIdeal (ThinQuotientFreeCategory (k := k) (Q := Q)))
    [Preadditive (CategoryTheory.Quotient I.rel)]
    [Linear k (CategoryTheory.Quotient I.rel)]
    [(CategoryTheory.Quotient.functor I.rel).Additive]
    [(CategoryTheory.Quotient.functor I.rel).Linear k]
    (D : CategoryTheory.Quotient I.rel ⥤ C)
    [D.Additive] [D.Linear k]
    (coefficient : ∀
      {X Y : ThinQuotientFreeCategory (k := k) (Q := Q)},
      Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X) →
        (D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
          D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y)) →ₗ[k] k)
    (X Y : ThinQuotientFreeCategory (k := k) (Q := Q))
    (hp : IsEmpty (Quiver.Path
      (LinearPathCategory.vertex Y) (LinearPathCategory.vertex X)))
    (g : D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
      D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y)) :
    thinQuotientPathProjection I D coefficient X Y g = 0 := by
  classical
  simp [thinQuotientPathProjection, not_nonempty_iff.mpr hp]

/-- Scalar coefficient data for a thin free quiver after quotienting by a
linear Hom ideal.  The coefficient table is evaluated in the ambient target,
whereas normalization is an equality in the bound source. -/
structure ThinQuotientPathCoefficientData
    (I : HomIdeal (ThinQuotientFreeCategory (k := k) (Q := Q)))
    [Preadditive (CategoryTheory.Quotient I.rel)]
    [Linear k (CategoryTheory.Quotient I.rel)]
    [(CategoryTheory.Quotient.functor I.rel).Additive]
    [(CategoryTheory.Quotient.functor I.rel).Linear k]
    (D : CategoryTheory.Quotient I.rel ⥤ C)
    [D.Additive] [D.Linear k] where
  path_subsingleton : ∀ a b : Q, Subsingleton (Quiver.Path a b)
  coefficient : ∀ {X Y : ThinQuotientFreeCategory (k := k) (Q := Q)},
    Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X) →
      (D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
        D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y)) →ₗ[k] k
  normalized_scaled : ∀
      {X Y : ThinQuotientFreeCategory (k := k) (Q := Q)}
      (p : Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X)),
    coefficient p
        (D.map ((CategoryTheory.Quotient.functor I.rel).map
          (LinearPathCategory.pathHom p))) •
      (CategoryTheory.Quotient.functor I.rel).map
        (LinearPathCategory.pathHom p) =
      (CategoryTheory.Quotient.functor I.rel).map
        (LinearPathCategory.pathHom p)
  whisker_scaled : ∀
      {X' X Y Y' : ThinQuotientFreeCategory (k := k) (Q := Q)}
      (p : Quiver.Path (LinearPathCategory.vertex X)
        (LinearPathCategory.vertex X'))
      (g : D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
        D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y))
      (q : Quiver.Path (LinearPathCategory.vertex Y')
        (LinearPathCategory.vertex Y))
      (r : Quiver.Path (LinearPathCategory.vertex Y')
        (LinearPathCategory.vertex X')),
    coefficient r
        (D.map ((CategoryTheory.Quotient.functor I.rel).map
            (LinearPathCategory.pathHom p)) ≫ g ≫
          D.map ((CategoryTheory.Quotient.functor I.rel).map
            (LinearPathCategory.pathHom q))) •
        (CategoryTheory.Quotient.functor I.rel).map
          (LinearPathCategory.pathHom r) =
      (CategoryTheory.Quotient.functor I.rel).map
          (LinearPathCategory.pathHom p) ≫
        thinQuotientPathProjection I D coefficient X Y g ≫
          (CategoryTheory.Quotient.functor I.rel).map
            (LinearPathCategory.pathHom q)

namespace ThinQuotientPathCoefficientData

variable {I : HomIdeal (ThinQuotientFreeCategory (k := k) (Q := Q))}
variable [Preadditive (CategoryTheory.Quotient I.rel)]
variable [Linear k (CategoryTheory.Quotient I.rel)]
variable [(CategoryTheory.Quotient.functor I.rel).Additive]
variable [(CategoryTheory.Quotient.functor I.rel).Linear k]
variable {D : CategoryTheory.Quotient I.rel ⥤ C}
variable [D.Additive] [D.Linear k]

/-- The quotient path-coefficient projection. -/
def retraction (h : ThinQuotientPathCoefficientData (k := k) I D)
    (X Y : CategoryTheory.Quotient I.rel) :
    (D.obj X ⟶ D.obj Y) →ₗ[k] (X ⟶ Y) := by
  classical
  by_cases hp : Nonempty (Quiver.Path
      (LinearPathCategory.vertex Y.as) (LinearPathCategory.vertex X.as))
  · exact (h.coefficient (Classical.choice hp)).smulRight
      ((CategoryTheory.Quotient.functor I.rel).map
        (LinearPathCategory.pathHom (Classical.choice hp)))
  · exact 0

@[simp] theorem retraction_apply_of_nonempty
    (h : ThinQuotientPathCoefficientData (k := k) I D)
    (X Y : CategoryTheory.Quotient I.rel)
    (hp : Nonempty (Quiver.Path
      (LinearPathCategory.vertex Y.as) (LinearPathCategory.vertex X.as)))
    (g : D.obj X ⟶ D.obj Y) :
    h.retraction X Y g =
      h.coefficient (Classical.choice hp) g •
        (CategoryTheory.Quotient.functor I.rel).map
          (LinearPathCategory.pathHom (Classical.choice hp)) := by
  classical
  simp only [retraction, hp]
  rfl

@[simp] theorem retraction_apply_of_isEmpty
    (h : ThinQuotientPathCoefficientData (k := k) I D)
    (X Y : CategoryTheory.Quotient I.rel)
    (hp : IsEmpty (Quiver.Path
      (LinearPathCategory.vertex Y.as) (LinearPathCategory.vertex X.as)))
    (g : D.obj X ⟶ D.obj Y) :
    h.retraction X Y g = 0 := by
  classical
  simp [retraction, not_nonempty_iff.mpr hp]

@[simp] theorem retraction_apply_of_nonempty_obj
    (h : ThinQuotientPathCoefficientData (k := k) I D)
    (X Y : ThinQuotientFreeCategory (k := k) (Q := Q))
    (hp : Nonempty (Quiver.Path
      (LinearPathCategory.vertex Y) (LinearPathCategory.vertex X)))
    (g : D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
      D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y)) :
    h.retraction
        ((CategoryTheory.Quotient.functor I.rel).obj X)
        ((CategoryTheory.Quotient.functor I.rel).obj Y) g =
      h.coefficient (Classical.choice hp) g •
        (CategoryTheory.Quotient.functor I.rel).map
          (LinearPathCategory.pathHom (Classical.choice hp)) := by
  classical
  simpa only [CategoryTheory.Quotient.functor] using
    h.retraction_apply_of_nonempty
      ((CategoryTheory.Quotient.functor I.rel).obj X)
      ((CategoryTheory.Quotient.functor I.rel).obj Y) hp g

@[simp] theorem retraction_apply_of_isEmpty_obj
    (h : ThinQuotientPathCoefficientData (k := k) I D)
    (X Y : ThinQuotientFreeCategory (k := k) (Q := Q))
    (hp : IsEmpty (Quiver.Path
      (LinearPathCategory.vertex Y) (LinearPathCategory.vertex X)))
    (g : D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
      D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y)) :
    h.retraction
        ((CategoryTheory.Quotient.functor I.rel).obj X)
        ((CategoryTheory.Quotient.functor I.rel).obj Y) g = 0 := by
  classical
  simpa only [CategoryTheory.Quotient.functor] using
    h.retraction_apply_of_isEmpty
      ((CategoryTheory.Quotient.functor I.rel).obj X)
      ((CategoryTheory.Quotient.functor I.rel).obj Y) hp g

@[simp] theorem retraction_map
    (h : ThinQuotientPathCoefficientData (k := k) I D)
    {X Y : CategoryTheory.Quotient I.rel} (f : X ⟶ Y) :
    h.retraction X Y (D.map f) = f := by
  classical
  obtain ⟨f, rfl⟩ :=
    (CategoryTheory.Quotient.functor I.rel).map_surjective f
  letI : Subsingleton (Quiver.Path (LinearPathCategory.vertex Y.as)
      (LinearPathCategory.vertex X.as)) := h.path_subsingleton _ _
  have hlinear :
      (h.retraction X Y).comp
        ((CategoryTheory.Quotient.functor I.rel ⋙ D).mapLinearMap k) =
      (CategoryTheory.Quotient.functor I.rel).mapLinearMap k := by
    apply (LinearPathCategory.homPathBasis X.as Y.as).ext
    intro p
    simp only [LinearMap.comp_apply, LinearPathCategory.homPathBasis_apply]
    rw [h.retraction_apply_of_nonempty X Y ⟨p⟩]
    rw [Subsingleton.elim (Classical.choice ⟨p⟩) p]
    exact h.normalized_scaled p
  exact DFunLike.congr_fun hlinear f

private theorem retraction_obj_eq_projection
    (h : ThinQuotientPathCoefficientData (k := k) I D)
    (X Y : ThinQuotientFreeCategory (k := k) (Q := Q))
    (g : D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
      D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y)) :
    h.retraction
        ((CategoryTheory.Quotient.functor I.rel).obj X)
        ((CategoryTheory.Quotient.functor I.rel).obj Y) g =
      thinQuotientPathProjection I D h.coefficient X Y g := by
  classical
  by_cases hp : Nonempty (Quiver.Path
      (LinearPathCategory.vertex Y) (LinearPathCategory.vertex X))
  · rw [h.retraction_apply_of_nonempty_obj X Y hp,
      thinQuotientPathProjection_apply_of_nonempty I D h.coefficient X Y hp]
  · have hp' : IsEmpty (Quiver.Path
        (LinearPathCategory.vertex Y) (LinearPathCategory.vertex X)) :=
      not_nonempty_iff.mp hp
    rw [h.retraction_apply_of_isEmpty_obj X Y hp',
      thinQuotientPathProjection_apply_of_isEmpty I D h.coefficient X Y hp']

/-- Naturality for quotient images of path-basis whiskers. -/
private theorem naturality_path
    (h : ThinQuotientPathCoefficientData (k := k) I D)
    {X' X Y Y' : ThinQuotientFreeCategory (k := k) (Q := Q)}
    (p : Quiver.Path (LinearPathCategory.vertex X)
      (LinearPathCategory.vertex X'))
    (g : D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
      D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y))
    (q : Quiver.Path (LinearPathCategory.vertex Y')
      (LinearPathCategory.vertex Y)) :
    h.retraction
        ((CategoryTheory.Quotient.functor I.rel).obj X')
        ((CategoryTheory.Quotient.functor I.rel).obj Y')
        (D.map ((CategoryTheory.Quotient.functor I.rel).map
            (LinearPathCategory.pathHom p)) ≫ g ≫
          D.map ((CategoryTheory.Quotient.functor I.rel).map
            (LinearPathCategory.pathHom q))) =
      (CategoryTheory.Quotient.functor I.rel).map
          (LinearPathCategory.pathHom p) ≫
        h.retraction
          ((CategoryTheory.Quotient.functor I.rel).obj X)
          ((CategoryTheory.Quotient.functor I.rel).obj Y) g ≫
        (CategoryTheory.Quotient.functor I.rel).map
          (LinearPathCategory.pathHom q) := by
  classical
  letI : Subsingleton (Quiver.Path (LinearPathCategory.vertex Y')
      (LinearPathCategory.vertex X')) := h.path_subsingleton _ _
  by_cases hlanding : Nonempty
      (Quiver.Path (LinearPathCategory.vertex Y')
        (LinearPathCategory.vertex X'))
  · let r := Classical.choice hlanding
    rw [h.retraction_apply_of_nonempty_obj X' Y' hlanding,
      Subsingleton.elim (Classical.choice hlanding) r,
      h.retraction_obj_eq_projection X Y g]
    exact h.whisker_scaled p g q r
  · have hlanding' : IsEmpty
        (Quiver.Path (LinearPathCategory.vertex Y')
          (LinearPathCategory.vertex X')) := not_nonempty_iff.mp hlanding
    have hmiddle' : IsEmpty
        (Quiver.Path (LinearPathCategory.vertex Y)
          (LinearPathCategory.vertex X)) := by
      constructor
      intro s
      exact hlanding'.false (q.comp (s.comp p))
    rw [h.retraction_apply_of_isEmpty_obj X' Y' hlanding',
      h.retraction_apply_of_isEmpty_obj X Y hmiddle']
    simp

set_option maxHeartbeats 800000 in
/-- Pathwise coefficient equations extend to a cross-universe Hom-bifunctor
retraction of the bound quotient source. -/
def homBifunctorRetraction
    (h : ThinQuotientPathCoefficientData (k := k) I D) :
    HomBifunctorRetraction (k := k) D where
  retraction := h.retraction
  map_retraction := h.retraction_map
  naturality := by
    rintro ⟨X0⟩ ⟨X1⟩ ⟨Y0⟩ ⟨Y1⟩ a g b
    change D.obj ((CategoryTheory.Quotient.functor I.rel).obj X1) ⟶
      D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y0) at g
    obtain ⟨a, rfl⟩ :=
      (CategoryTheory.Quotient.functor I.rel).map_surjective a
    obtain ⟨b, rfl⟩ :=
      (CategoryTheory.Quotient.functor I.rel).map_surjective b
    let leftA : (X0 ⟶ X1) →ₗ[k]
        ((Y0 ⟶ Y1) →ₗ[k]
          ((CategoryTheory.Quotient.functor I.rel).obj X0 ⟶
            (CategoryTheory.Quotient.functor I.rel).obj Y1)) :=
      { toFun := fun a ↦
          { toFun := fun b ↦ h.retraction
              ((CategoryTheory.Quotient.functor I.rel).obj X0)
              ((CategoryTheory.Quotient.functor I.rel).obj Y1)
              (D.map ((CategoryTheory.Quotient.functor I.rel).map a) ≫ g ≫
                D.map ((CategoryTheory.Quotient.functor I.rel).map b))
            map_add' := by
              intro b c
              rw [(CategoryTheory.Quotient.functor I.rel).map_add,
                D.map_add, Preadditive.comp_add, Preadditive.comp_add,
                LinearMap.map_add]
            map_smul' := by
              intro r b
              rw [(CategoryTheory.Quotient.functor I.rel).map_smul,
                D.map_smul, Linear.comp_smul, Linear.comp_smul,
                LinearMap.map_smul]
              rfl }
        map_add' := by
          intro a c
          apply LinearMap.ext
          intro b
          change h.retraction
              ((CategoryTheory.Quotient.functor I.rel).obj X0)
              ((CategoryTheory.Quotient.functor I.rel).obj Y1)
                (D.map ((CategoryTheory.Quotient.functor I.rel).map (a + c)) ≫
                  g ≫ D.map ((CategoryTheory.Quotient.functor I.rel).map b)) =
            h.retraction
                ((CategoryTheory.Quotient.functor I.rel).obj X0)
                ((CategoryTheory.Quotient.functor I.rel).obj Y1)
                  (D.map ((CategoryTheory.Quotient.functor I.rel).map a) ≫
                    g ≫ D.map ((CategoryTheory.Quotient.functor I.rel).map b)) +
              h.retraction
                ((CategoryTheory.Quotient.functor I.rel).obj X0)
                ((CategoryTheory.Quotient.functor I.rel).obj Y1)
                  (D.map ((CategoryTheory.Quotient.functor I.rel).map c) ≫
                    g ≫ D.map ((CategoryTheory.Quotient.functor I.rel).map b))
          rw [(CategoryTheory.Quotient.functor I.rel).map_add,
            D.map_add, Preadditive.add_comp,
            LinearMap.map_add]
        map_smul' := by
          intro r a
          apply LinearMap.ext
          intro b
          change h.retraction
              ((CategoryTheory.Quotient.functor I.rel).obj X0)
              ((CategoryTheory.Quotient.functor I.rel).obj Y1)
                (D.map ((CategoryTheory.Quotient.functor I.rel).map (r • a)) ≫
                  g ≫ D.map ((CategoryTheory.Quotient.functor I.rel).map b)) =
            r • h.retraction
              ((CategoryTheory.Quotient.functor I.rel).obj X0)
              ((CategoryTheory.Quotient.functor I.rel).obj Y1)
                (D.map ((CategoryTheory.Quotient.functor I.rel).map a) ≫
                  g ≫ D.map ((CategoryTheory.Quotient.functor I.rel).map b))
          rw [(CategoryTheory.Quotient.functor I.rel).map_smul,
            D.map_smul, Linear.smul_comp,
            LinearMap.map_smul] }
    let rightA : (X0 ⟶ X1) →ₗ[k]
        ((Y0 ⟶ Y1) →ₗ[k]
          ((CategoryTheory.Quotient.functor I.rel).obj X0 ⟶
            (CategoryTheory.Quotient.functor I.rel).obj Y1)) :=
      { toFun := fun a ↦
          { toFun := fun b ↦
              (CategoryTheory.Quotient.functor I.rel).map a ≫
                h.retraction
                  ((CategoryTheory.Quotient.functor I.rel).obj X1)
                  ((CategoryTheory.Quotient.functor I.rel).obj Y0) g ≫
                  (CategoryTheory.Quotient.functor I.rel).map b
            map_add' := by
              intro b c
              rw [(CategoryTheory.Quotient.functor I.rel).map_add,
                Preadditive.comp_add, Preadditive.comp_add]
            map_smul' := by
              intro r b
              rw [(CategoryTheory.Quotient.functor I.rel).map_smul,
                Linear.comp_smul, Linear.comp_smul]
              rfl }
        map_add' := by
          intro a c
          apply LinearMap.ext
          intro b
          change (CategoryTheory.Quotient.functor I.rel).map (a + c) ≫
                h.retraction
                  ((CategoryTheory.Quotient.functor I.rel).obj X1)
                  ((CategoryTheory.Quotient.functor I.rel).obj Y0) g ≫
                  (CategoryTheory.Quotient.functor I.rel).map b =
            ((CategoryTheory.Quotient.functor I.rel).map a ≫
                h.retraction
                  ((CategoryTheory.Quotient.functor I.rel).obj X1)
                  ((CategoryTheory.Quotient.functor I.rel).obj Y0) g ≫
                  (CategoryTheory.Quotient.functor I.rel).map b) +
              ((CategoryTheory.Quotient.functor I.rel).map c ≫
                h.retraction
                  ((CategoryTheory.Quotient.functor I.rel).obj X1)
                  ((CategoryTheory.Quotient.functor I.rel).obj Y0) g ≫
                  (CategoryTheory.Quotient.functor I.rel).map b)
          rw [(CategoryTheory.Quotient.functor I.rel).map_add,
            Preadditive.add_comp]
        map_smul' := by
          intro r a
          apply LinearMap.ext
          intro b
          change (CategoryTheory.Quotient.functor I.rel).map (r • a) ≫
                h.retraction
                  ((CategoryTheory.Quotient.functor I.rel).obj X1)
                  ((CategoryTheory.Quotient.functor I.rel).obj Y0) g ≫
                  (CategoryTheory.Quotient.functor I.rel).map b =
            r • ((CategoryTheory.Quotient.functor I.rel).map a ≫
              h.retraction
                ((CategoryTheory.Quotient.functor I.rel).obj X1)
                ((CategoryTheory.Quotient.functor I.rel).obj Y0) g ≫
                (CategoryTheory.Quotient.functor I.rel).map b)
          rw [(CategoryTheory.Quotient.functor I.rel).map_smul,
            Linear.smul_comp] }
    have hA : leftA = rightA := by
      apply (LinearPathCategory.homPathBasis X0 X1).ext
      intro p
      apply (LinearPathCategory.homPathBasis Y0 Y1).ext
      intro q
      simp only [leftA, rightA, LinearPathCategory.homPathBasis_apply]
      exact h.naturality_path p g q
    exact DFunLike.congr_fun (DFunLike.congr_fun hA a) b

end ThinQuotientPathCoefficientData

/-! ## Quotients which identify parallel paths

The free quiver need not itself be thin.  For a commutative diamond, for
example, there are two parallel free paths although their images in the bound
quotient agree.  The following variant records exactly that weaker condition.
The rest of the path-basis argument is unchanged: freeness is used upstairs
to extend from paths by linearity, while uniqueness is needed only after
passing to the quotient.
-/

/-- Scalar coefficient data for a quotient in which all parallel free paths
have the same image. -/
structure IdentifiedQuotientPathCoefficientData
    (I : HomIdeal (ThinQuotientFreeCategory (k := k) (Q := Q)))
    [Preadditive (CategoryTheory.Quotient I.rel)]
    [Linear k (CategoryTheory.Quotient I.rel)]
    [(CategoryTheory.Quotient.functor I.rel).Additive]
    [(CategoryTheory.Quotient.functor I.rel).Linear k]
    (D : CategoryTheory.Quotient I.rel ⥤ C)
    [D.Additive] [D.Linear k] where
  path_images_eq : ∀ {a b : Q} (p q : Quiver.Path a b),
    (CategoryTheory.Quotient.functor I.rel).map
        (LinearPathCategory.pathHom p) =
      (CategoryTheory.Quotient.functor I.rel).map
        (LinearPathCategory.pathHom q)
  coefficient : ∀ {X Y : ThinQuotientFreeCategory (k := k) (Q := Q)},
    Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X) →
      (D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
        D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y)) →ₗ[k] k
  normalized_scaled : ∀
      {X Y : ThinQuotientFreeCategory (k := k) (Q := Q)}
      (p : Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X)),
    coefficient p
        (D.map ((CategoryTheory.Quotient.functor I.rel).map
          (LinearPathCategory.pathHom p))) •
      (CategoryTheory.Quotient.functor I.rel).map
        (LinearPathCategory.pathHom p) =
      (CategoryTheory.Quotient.functor I.rel).map
        (LinearPathCategory.pathHom p)
  whisker_scaled : ∀
      {X' X Y Y' : ThinQuotientFreeCategory (k := k) (Q := Q)}
      (p : Quiver.Path (LinearPathCategory.vertex X)
        (LinearPathCategory.vertex X'))
      (g : D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
        D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y))
      (q : Quiver.Path (LinearPathCategory.vertex Y')
        (LinearPathCategory.vertex Y))
      (r : Quiver.Path (LinearPathCategory.vertex Y')
        (LinearPathCategory.vertex X')),
    coefficient r
        (D.map ((CategoryTheory.Quotient.functor I.rel).map
            (LinearPathCategory.pathHom p)) ≫ g ≫
          D.map ((CategoryTheory.Quotient.functor I.rel).map
            (LinearPathCategory.pathHom q))) •
        (CategoryTheory.Quotient.functor I.rel).map
          (LinearPathCategory.pathHom r) =
      (CategoryTheory.Quotient.functor I.rel).map
          (LinearPathCategory.pathHom p) ≫
        thinQuotientPathProjection I D coefficient X Y g ≫
          (CategoryTheory.Quotient.functor I.rel).map
            (LinearPathCategory.pathHom q)

namespace IdentifiedQuotientPathCoefficientData

variable {I : HomIdeal (ThinQuotientFreeCategory (k := k) (Q := Q))}
variable [Preadditive (CategoryTheory.Quotient I.rel)]
variable [Linear k (CategoryTheory.Quotient I.rel)]
variable [(CategoryTheory.Quotient.functor I.rel).Additive]
variable [(CategoryTheory.Quotient.functor I.rel).Linear k]
variable {D : CategoryTheory.Quotient I.rel ⥤ C}
variable [D.Additive] [D.Linear k]

/-- The quotient path-coefficient projection. -/
def retraction (h : IdentifiedQuotientPathCoefficientData (k := k) I D)
    (X Y : CategoryTheory.Quotient I.rel) :
    (D.obj X ⟶ D.obj Y) →ₗ[k] (X ⟶ Y) := by
  classical
  by_cases hp : Nonempty (Quiver.Path
      (LinearPathCategory.vertex Y.as) (LinearPathCategory.vertex X.as))
  · exact (h.coefficient (Classical.choice hp)).smulRight
      ((CategoryTheory.Quotient.functor I.rel).map
        (LinearPathCategory.pathHom (Classical.choice hp)))
  · exact 0

@[simp] theorem retraction_apply_of_nonempty
    (h : IdentifiedQuotientPathCoefficientData (k := k) I D)
    (X Y : CategoryTheory.Quotient I.rel)
    (hp : Nonempty (Quiver.Path
      (LinearPathCategory.vertex Y.as) (LinearPathCategory.vertex X.as)))
    (g : D.obj X ⟶ D.obj Y) :
    h.retraction X Y g =
      h.coefficient (Classical.choice hp) g •
        (CategoryTheory.Quotient.functor I.rel).map
          (LinearPathCategory.pathHom (Classical.choice hp)) := by
  classical
  simp only [retraction, hp]
  rfl

@[simp] theorem retraction_apply_of_isEmpty
    (h : IdentifiedQuotientPathCoefficientData (k := k) I D)
    (X Y : CategoryTheory.Quotient I.rel)
    (hp : IsEmpty (Quiver.Path
      (LinearPathCategory.vertex Y.as) (LinearPathCategory.vertex X.as)))
    (g : D.obj X ⟶ D.obj Y) :
    h.retraction X Y g = 0 := by
  classical
  simp [retraction, not_nonempty_iff.mpr hp]

@[simp] theorem retraction_apply_of_nonempty_obj
    (h : IdentifiedQuotientPathCoefficientData (k := k) I D)
    (X Y : ThinQuotientFreeCategory (k := k) (Q := Q))
    (hp : Nonempty (Quiver.Path
      (LinearPathCategory.vertex Y) (LinearPathCategory.vertex X)))
    (g : D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
      D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y)) :
    h.retraction
        ((CategoryTheory.Quotient.functor I.rel).obj X)
        ((CategoryTheory.Quotient.functor I.rel).obj Y) g =
      h.coefficient (Classical.choice hp) g •
        (CategoryTheory.Quotient.functor I.rel).map
          (LinearPathCategory.pathHom (Classical.choice hp)) := by
  classical
  simpa only [CategoryTheory.Quotient.functor] using
    h.retraction_apply_of_nonempty
      ((CategoryTheory.Quotient.functor I.rel).obj X)
      ((CategoryTheory.Quotient.functor I.rel).obj Y) hp g

@[simp] theorem retraction_apply_of_isEmpty_obj
    (h : IdentifiedQuotientPathCoefficientData (k := k) I D)
    (X Y : ThinQuotientFreeCategory (k := k) (Q := Q))
    (hp : IsEmpty (Quiver.Path
      (LinearPathCategory.vertex Y) (LinearPathCategory.vertex X)))
    (g : D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
      D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y)) :
    h.retraction
        ((CategoryTheory.Quotient.functor I.rel).obj X)
        ((CategoryTheory.Quotient.functor I.rel).obj Y) g = 0 := by
  classical
  simpa only [CategoryTheory.Quotient.functor] using
    h.retraction_apply_of_isEmpty
      ((CategoryTheory.Quotient.functor I.rel).obj X)
      ((CategoryTheory.Quotient.functor I.rel).obj Y) hp g

private theorem retraction_obj_eq_projection
    (h : IdentifiedQuotientPathCoefficientData (k := k) I D)
    (X Y : ThinQuotientFreeCategory (k := k) (Q := Q))
    (g : D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
      D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y)) :
    h.retraction
        ((CategoryTheory.Quotient.functor I.rel).obj X)
        ((CategoryTheory.Quotient.functor I.rel).obj Y) g =
      thinQuotientPathProjection I D h.coefficient X Y g := by
  classical
  by_cases hp : Nonempty (Quiver.Path
      (LinearPathCategory.vertex Y) (LinearPathCategory.vertex X))
  · rw [h.retraction_apply_of_nonempty_obj X Y hp,
      thinQuotientPathProjection_apply_of_nonempty I D h.coefficient X Y hp]
  · have hp' : IsEmpty (Quiver.Path
        (LinearPathCategory.vertex Y) (LinearPathCategory.vertex X)) :=
      not_nonempty_iff.mp hp
    rw [h.retraction_apply_of_isEmpty_obj X Y hp',
      thinQuotientPathProjection_apply_of_isEmpty I D h.coefficient X Y hp']

@[simp] theorem retraction_map
    (h : IdentifiedQuotientPathCoefficientData (k := k) I D)
    {X Y : CategoryTheory.Quotient I.rel} (f : X ⟶ Y) :
    h.retraction X Y (D.map f) = f := by
  classical
  obtain ⟨f, rfl⟩ :=
    (CategoryTheory.Quotient.functor I.rel).map_surjective f
  have hlinear :
      (h.retraction X Y).comp
        ((CategoryTheory.Quotient.functor I.rel ⋙ D).mapLinearMap k) =
      (CategoryTheory.Quotient.functor I.rel).mapLinearMap k := by
    apply (LinearPathCategory.homPathBasis X.as Y.as).ext
    intro p
    simp only [LinearMap.comp_apply, LinearPathCategory.homPathBasis_apply]
    rw [h.retraction_apply_of_nonempty X Y ⟨p⟩]
    change h.coefficient (Classical.choice ⟨p⟩)
        (D.map ((CategoryTheory.Quotient.functor I.rel).map
          (LinearPathCategory.pathHom p))) •
      (CategoryTheory.Quotient.functor I.rel).map
          (LinearPathCategory.pathHom (Classical.choice ⟨p⟩)) =
        (CategoryTheory.Quotient.functor I.rel).map
          (LinearPathCategory.pathHom p)
    rw [← h.path_images_eq (Classical.choice ⟨p⟩) p]
    exact h.normalized_scaled (Classical.choice ⟨p⟩)
  exact DFunLike.congr_fun hlinear f

/-- Naturality for quotient images of path-basis whiskers. -/
private theorem naturality_path
    (h : IdentifiedQuotientPathCoefficientData (k := k) I D)
    {X' X Y Y' : ThinQuotientFreeCategory (k := k) (Q := Q)}
    (p : Quiver.Path (LinearPathCategory.vertex X)
      (LinearPathCategory.vertex X'))
    (g : D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
      D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y))
    (q : Quiver.Path (LinearPathCategory.vertex Y')
      (LinearPathCategory.vertex Y)) :
    h.retraction
        ((CategoryTheory.Quotient.functor I.rel).obj X')
        ((CategoryTheory.Quotient.functor I.rel).obj Y')
        (D.map ((CategoryTheory.Quotient.functor I.rel).map
            (LinearPathCategory.pathHom p)) ≫ g ≫
          D.map ((CategoryTheory.Quotient.functor I.rel).map
            (LinearPathCategory.pathHom q))) =
      (CategoryTheory.Quotient.functor I.rel).map
          (LinearPathCategory.pathHom p) ≫
        h.retraction
          ((CategoryTheory.Quotient.functor I.rel).obj X)
          ((CategoryTheory.Quotient.functor I.rel).obj Y) g ≫
        (CategoryTheory.Quotient.functor I.rel).map
          (LinearPathCategory.pathHom q) := by
  classical
  by_cases hlanding : Nonempty
      (Quiver.Path (LinearPathCategory.vertex Y')
        (LinearPathCategory.vertex X'))
  · let r := Classical.choice hlanding
    rw [h.retraction_apply_of_nonempty_obj X' Y' hlanding,
      h.retraction_obj_eq_projection X Y g]
    exact h.whisker_scaled p g q r
  · have hlanding' : IsEmpty
        (Quiver.Path (LinearPathCategory.vertex Y')
          (LinearPathCategory.vertex X')) := not_nonempty_iff.mp hlanding
    have hmiddle' : IsEmpty
        (Quiver.Path (LinearPathCategory.vertex Y)
          (LinearPathCategory.vertex X)) := by
      constructor
      intro s
      exact hlanding'.false (q.comp (s.comp p))
    rw [h.retraction_apply_of_isEmpty_obj X' Y' hlanding',
      h.retraction_apply_of_isEmpty_obj X Y hmiddle']
    simp

set_option maxHeartbeats 800000 in
/-- Pathwise coefficient equations extend to a cross-universe Hom-bifunctor
retraction when parallel paths agree in the bound quotient. -/
def homBifunctorRetraction
    (h : IdentifiedQuotientPathCoefficientData (k := k) I D) :
    HomBifunctorRetraction (k := k) D where
  retraction := h.retraction
  map_retraction := h.retraction_map
  naturality := by
    rintro ⟨X0⟩ ⟨X1⟩ ⟨Y0⟩ ⟨Y1⟩ a g b
    change D.obj ((CategoryTheory.Quotient.functor I.rel).obj X1) ⟶
      D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y0) at g
    obtain ⟨a, rfl⟩ :=
      (CategoryTheory.Quotient.functor I.rel).map_surjective a
    obtain ⟨b, rfl⟩ :=
      (CategoryTheory.Quotient.functor I.rel).map_surjective b
    let leftA : (X0 ⟶ X1) →ₗ[k]
        ((Y0 ⟶ Y1) →ₗ[k]
          ((CategoryTheory.Quotient.functor I.rel).obj X0 ⟶
            (CategoryTheory.Quotient.functor I.rel).obj Y1)) :=
      { toFun := fun a ↦
          { toFun := fun b ↦ h.retraction
              ((CategoryTheory.Quotient.functor I.rel).obj X0)
              ((CategoryTheory.Quotient.functor I.rel).obj Y1)
              (D.map ((CategoryTheory.Quotient.functor I.rel).map a) ≫ g ≫
                D.map ((CategoryTheory.Quotient.functor I.rel).map b))
            map_add' := by
              intro b c
              rw [(CategoryTheory.Quotient.functor I.rel).map_add,
                D.map_add, Preadditive.comp_add, Preadditive.comp_add,
                LinearMap.map_add]
            map_smul' := by
              intro r b
              rw [(CategoryTheory.Quotient.functor I.rel).map_smul,
                D.map_smul, Linear.comp_smul, Linear.comp_smul,
                LinearMap.map_smul]
              rfl }
        map_add' := by
          intro a c
          apply LinearMap.ext
          intro b
          change h.retraction
              ((CategoryTheory.Quotient.functor I.rel).obj X0)
              ((CategoryTheory.Quotient.functor I.rel).obj Y1)
                (D.map ((CategoryTheory.Quotient.functor I.rel).map (a + c)) ≫
                  g ≫ D.map ((CategoryTheory.Quotient.functor I.rel).map b)) =
            h.retraction
                ((CategoryTheory.Quotient.functor I.rel).obj X0)
                ((CategoryTheory.Quotient.functor I.rel).obj Y1)
                  (D.map ((CategoryTheory.Quotient.functor I.rel).map a) ≫
                    g ≫ D.map ((CategoryTheory.Quotient.functor I.rel).map b)) +
              h.retraction
                ((CategoryTheory.Quotient.functor I.rel).obj X0)
                ((CategoryTheory.Quotient.functor I.rel).obj Y1)
                  (D.map ((CategoryTheory.Quotient.functor I.rel).map c) ≫
                    g ≫ D.map ((CategoryTheory.Quotient.functor I.rel).map b))
          rw [(CategoryTheory.Quotient.functor I.rel).map_add,
            D.map_add, Preadditive.add_comp, LinearMap.map_add]
        map_smul' := by
          intro r a
          apply LinearMap.ext
          intro b
          change h.retraction
              ((CategoryTheory.Quotient.functor I.rel).obj X0)
              ((CategoryTheory.Quotient.functor I.rel).obj Y1)
                (D.map ((CategoryTheory.Quotient.functor I.rel).map (r • a)) ≫
                  g ≫ D.map ((CategoryTheory.Quotient.functor I.rel).map b)) =
            r • h.retraction
              ((CategoryTheory.Quotient.functor I.rel).obj X0)
              ((CategoryTheory.Quotient.functor I.rel).obj Y1)
                (D.map ((CategoryTheory.Quotient.functor I.rel).map a) ≫
                  g ≫ D.map ((CategoryTheory.Quotient.functor I.rel).map b))
          rw [(CategoryTheory.Quotient.functor I.rel).map_smul,
            D.map_smul, Linear.smul_comp, LinearMap.map_smul] }
    let rightA : (X0 ⟶ X1) →ₗ[k]
        ((Y0 ⟶ Y1) →ₗ[k]
          ((CategoryTheory.Quotient.functor I.rel).obj X0 ⟶
            (CategoryTheory.Quotient.functor I.rel).obj Y1)) :=
      { toFun := fun a ↦
          { toFun := fun b ↦
              (CategoryTheory.Quotient.functor I.rel).map a ≫
                h.retraction
                  ((CategoryTheory.Quotient.functor I.rel).obj X1)
                  ((CategoryTheory.Quotient.functor I.rel).obj Y0) g ≫
                  (CategoryTheory.Quotient.functor I.rel).map b
            map_add' := by
              intro b c
              rw [(CategoryTheory.Quotient.functor I.rel).map_add,
                Preadditive.comp_add, Preadditive.comp_add]
            map_smul' := by
              intro r b
              rw [(CategoryTheory.Quotient.functor I.rel).map_smul,
                Linear.comp_smul, Linear.comp_smul]
              rfl }
        map_add' := by
          intro a c
          apply LinearMap.ext
          intro b
          change (CategoryTheory.Quotient.functor I.rel).map (a + c) ≫
                h.retraction
                  ((CategoryTheory.Quotient.functor I.rel).obj X1)
                  ((CategoryTheory.Quotient.functor I.rel).obj Y0) g ≫
                  (CategoryTheory.Quotient.functor I.rel).map b =
            ((CategoryTheory.Quotient.functor I.rel).map a ≫
                h.retraction
                  ((CategoryTheory.Quotient.functor I.rel).obj X1)
                  ((CategoryTheory.Quotient.functor I.rel).obj Y0) g ≫
                  (CategoryTheory.Quotient.functor I.rel).map b) +
              ((CategoryTheory.Quotient.functor I.rel).map c ≫
                h.retraction
                  ((CategoryTheory.Quotient.functor I.rel).obj X1)
                  ((CategoryTheory.Quotient.functor I.rel).obj Y0) g ≫
                  (CategoryTheory.Quotient.functor I.rel).map b)
          rw [(CategoryTheory.Quotient.functor I.rel).map_add,
            Preadditive.add_comp]
        map_smul' := by
          intro r a
          apply LinearMap.ext
          intro b
          change (CategoryTheory.Quotient.functor I.rel).map (r • a) ≫
                h.retraction
                  ((CategoryTheory.Quotient.functor I.rel).obj X1)
                  ((CategoryTheory.Quotient.functor I.rel).obj Y0) g ≫
                  (CategoryTheory.Quotient.functor I.rel).map b =
            r • ((CategoryTheory.Quotient.functor I.rel).map a ≫
              h.retraction
                ((CategoryTheory.Quotient.functor I.rel).obj X1)
                ((CategoryTheory.Quotient.functor I.rel).obj Y0) g ≫
                (CategoryTheory.Quotient.functor I.rel).map b)
          rw [(CategoryTheory.Quotient.functor I.rel).map_smul,
            Linear.smul_comp] }
    have hA : leftA = rightA := by
      apply (LinearPathCategory.homPathBasis X0 X1).ext
      intro p
      apply (LinearPathCategory.homPathBasis Y0 Y1).ext
      intro q
      simp only [leftA, rightA, LinearPathCategory.homPathBasis_apply]
      exact h.naturality_path p g q
    exact DFunLike.congr_fun (DFunLike.congr_fun hA a) b

end IdentifiedQuotientPathCoefficientData

/-! ## Finite endpoint compiler

For concrete bound quivers it is more convenient to prescribe one coefficient
for every ordered pair of vertex occurrences and check covariance only for
arrows.  The next structure iterates those finite equations along paths and
produces the path-indexed data above.
-/

/-- Occurrence-sensitive endpoint coefficients for a bound quiver whose
parallel paths agree in the quotient. -/
structure CompatibleIdentifiedQuotientEndpointData
    (I : HomIdeal (ThinQuotientFreeCategory (k := k) (Q := Q)))
    [Preadditive (CategoryTheory.Quotient I.rel)]
    [Linear k (CategoryTheory.Quotient I.rel)]
    [(CategoryTheory.Quotient.functor I.rel).Additive]
    [(CategoryTheory.Quotient.functor I.rel).Linear k]
    (D : CategoryTheory.Quotient I.rel ⥤ C)
    [D.Additive] [D.Linear k] where
  path_images_eq : ∀ {a b : Q} (p q : Quiver.Path a b),
    (CategoryTheory.Quotient.functor I.rel).map
        (LinearPathCategory.pathHom p) =
      (CategoryTheory.Quotient.functor I.rel).map
        (LinearPathCategory.pathHom q)
  coefficient : ∀ X Y : ThinQuotientFreeCategory (k := k) (Q := Q),
    (D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
      D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y)) →ₗ[k] k
  identity : ∀ X : ThinQuotientFreeCategory (k := k) (Q := Q),
    coefficient X X (𝟙 (D.obj
      ((CategoryTheory.Quotient.functor I.rel).obj X))) = 1
  left_arrow : ∀
      {X' X : ThinQuotientFreeCategory (k := k) (Q := Q)}
      (e : LinearPathCategory.vertex X ⟶ LinearPathCategory.vertex X')
      (Y : ThinQuotientFreeCategory (k := k) (Q := Q))
      (g : D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
        D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y)),
    coefficient X' Y
        (D.map ((CategoryTheory.Quotient.functor I.rel).map
            (LinearPathCategory.pathHom (Quiver.Hom.toPath e))) ≫ g) =
      coefficient X Y g
  right_arrow : ∀
      (X : ThinQuotientFreeCategory (k := k) (Q := Q))
      {Y' Y : ThinQuotientFreeCategory (k := k) (Q := Q)}
      (e : LinearPathCategory.vertex Y' ⟶ LinearPathCategory.vertex Y)
      (g : D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
        D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y)),
    coefficient X Y'
        (g ≫ D.map ((CategoryTheory.Quotient.functor I.rel).map
          (LinearPathCategory.pathHom (Quiver.Hom.toPath e)))) =
      coefficient X Y g
  eq_zero_of_isEmpty : ∀
      (X Y : ThinQuotientFreeCategory (k := k) (Q := Q)),
    IsEmpty (Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) → ∀ g, coefficient X Y g = 0

namespace CompatibleIdentifiedQuotientEndpointData

variable {I : HomIdeal (ThinQuotientFreeCategory (k := k) (Q := Q))}
variable [Preadditive (CategoryTheory.Quotient I.rel)]
variable [Linear k (CategoryTheory.Quotient I.rel)]
variable [(CategoryTheory.Quotient.functor I.rel).Additive]
variable [(CategoryTheory.Quotient.functor I.rel).Linear k]
variable {D : CategoryTheory.Quotient I.rel ⥤ C}
variable [D.Additive] [D.Linear k]

/-- Iteration of left-arrow covariance along a path. -/
theorem left_path
    (h : CompatibleIdentifiedQuotientEndpointData (k := k) I D)
    {X' X : ThinQuotientFreeCategory (k := k) (Q := Q)}
    (p : Quiver.Path (LinearPathCategory.vertex X)
      (LinearPathCategory.vertex X'))
    (Y : ThinQuotientFreeCategory (k := k) (Q := Q))
    (g : D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
      D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y)) :
    h.coefficient X' Y
        (D.map ((CategoryTheory.Quotient.functor I.rel).map
          (LinearPathCategory.pathHom p)) ≫ g) =
      h.coefficient X Y g := by
  unfold LinearPathCategory.vertex at p
  change Q at X' X Y
  induction p with
  | nil =>
      simp
  | cons p e ih =>
      change h.coefficient _ Y
          (D.map ((CategoryTheory.Quotient.functor I.rel).map
            (LinearPathCategory.pathHom
              (p.comp (Quiver.Hom.toPath e)))) ≫ g) = _
      rw [← LinearPathCategory.pathHom_comp,
        Functor.map_comp, Functor.map_comp, Category.assoc]
      exact (h.left_arrow e Y _).trans ih

/-- Iteration of right-arrow covariance along a path. -/
theorem right_path
    (h : CompatibleIdentifiedQuotientEndpointData (k := k) I D)
    (X : ThinQuotientFreeCategory (k := k) (Q := Q))
    {Y' Y : ThinQuotientFreeCategory (k := k) (Q := Q)}
    (q : Quiver.Path (LinearPathCategory.vertex Y')
      (LinearPathCategory.vertex Y))
    (g : D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
      D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y)) :
    h.coefficient X Y'
        (g ≫ D.map ((CategoryTheory.Quotient.functor I.rel).map
          (LinearPathCategory.pathHom q))) =
      h.coefficient X Y g := by
  unfold LinearPathCategory.vertex at q
  change Q at X Y' Y
  induction q with
  | nil =>
      simp
  | cons q e ih =>
      change h.coefficient X _
          (g ≫ D.map ((CategoryTheory.Quotient.functor I.rel).map
            (LinearPathCategory.pathHom
              (q.comp (Quiver.Hom.toPath e))))) = _
      rw [← LinearPathCategory.pathHom_comp,
        Functor.map_comp, Functor.map_comp, ← Category.assoc]
      exact (ih (g ≫ D.map ((CategoryTheory.Quotient.functor I.rel).map
        (LinearPathCategory.pathHom (Quiver.Hom.toPath e))))).trans
          (h.right_arrow X e g)

/-- Two-sided path whiskering preserves the endpoint coefficient. -/
theorem whisker
    (h : CompatibleIdentifiedQuotientEndpointData (k := k) I D)
    {X' X Y Y' : ThinQuotientFreeCategory (k := k) (Q := Q)}
    (p : Quiver.Path (LinearPathCategory.vertex X)
      (LinearPathCategory.vertex X'))
    (g : D.obj ((CategoryTheory.Quotient.functor I.rel).obj X) ⟶
      D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y))
    (q : Quiver.Path (LinearPathCategory.vertex Y')
      (LinearPathCategory.vertex Y)) :
    h.coefficient X' Y'
        (D.map ((CategoryTheory.Quotient.functor I.rel).map
            (LinearPathCategory.pathHom p)) ≫ g ≫
          D.map ((CategoryTheory.Quotient.functor I.rel).map
            (LinearPathCategory.pathHom q))) =
      h.coefficient X Y g := by
  rw [← Category.assoc]
  exact (h.right_path X' q _).trans (h.left_path p Y g)

/-- Every quotient path is normalized by the coefficient of its endpoints. -/
theorem normalized
    (h : CompatibleIdentifiedQuotientEndpointData (k := k) I D)
    {X Y : ThinQuotientFreeCategory (k := k) (Q := Q)}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) :
    h.coefficient X Y
        (D.map ((CategoryTheory.Quotient.functor I.rel).map
          (LinearPathCategory.pathHom p))) = 1 := by
  have hp := h.left_path p Y
    (𝟙 (D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y)))
  have hp' : h.coefficient X Y
        (D.map ((CategoryTheory.Quotient.functor I.rel).map
          (LinearPathCategory.pathHom p))) =
      h.coefficient Y Y
        (𝟙 (D.obj ((CategoryTheory.Quotient.functor I.rel).obj Y))) := by
    simpa only [Category.comp_id] using hp
  exact hp'.trans (h.identity Y)

/-- Compile finite endpoint equations to the generic identified-path
retraction data. -/
def toIdentifiedQuotientPathCoefficientData
    (h : CompatibleIdentifiedQuotientEndpointData (k := k) I D) :
    IdentifiedQuotientPathCoefficientData (k := k) I D where
  path_images_eq := h.path_images_eq
  coefficient := fun {X Y} _ ↦ h.coefficient X Y
  normalized_scaled := by
    intro X Y p
    have hp := h.normalized p
    rw [hp, one_smul]
  whisker_scaled := by
    classical
    intro X' X Y Y' p g q r
    have hcoeff := h.whisker p g q
    rw [hcoeff]
    by_cases hmiddle : Nonempty (Quiver.Path
        (LinearPathCategory.vertex Y) (LinearPathCategory.vertex X))
    · rw [thinQuotientPathProjection_apply_of_nonempty
        I D (fun {_ _} _ ↦ h.coefficient _ _) X Y hmiddle]
      rw [Linear.smul_comp, Linear.comp_smul]
      rw [← (CategoryTheory.Quotient.functor I.rel).map_comp,
        ← (CategoryTheory.Quotient.functor I.rel).map_comp,
        LinearPathCategory.pathHom_comp,
        LinearPathCategory.pathHom_comp]
      rw [h.path_images_eq r
        (q.comp ((Classical.choice hmiddle).comp p))]
      simp only [Quiver.Path.comp_assoc]
    · have hmiddle' : IsEmpty (Quiver.Path
          (LinearPathCategory.vertex Y)
            (LinearPathCategory.vertex X)) := not_nonempty_iff.mp hmiddle
      rw [h.eq_zero_of_isEmpty _ _ hmiddle' g, zero_smul]
      rw [thinQuotientPathProjection_apply_of_isEmpty
        I D (fun {_ _} _ ↦ h.coefficient _ _) X Y hmiddle']
      simp

/-- The Hom-bifunctor retraction compiled from endpoint data. -/
def homBifunctorRetraction
    (h : CompatibleIdentifiedQuotientEndpointData (k := k) I D) :
    HomBifunctorRetraction (k := k) D :=
  h.toIdentifiedQuotientPathCoefficientData.homBifunctorRetraction

end CompatibleIdentifiedQuotientEndpointData

end LargeIndecomposable.ClosedZigzagCrossUniverse
