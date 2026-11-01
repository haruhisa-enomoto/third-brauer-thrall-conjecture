module

public import LargeIndecomposable.Cleaving.ClosedChains.CrossArrowCoefficient
public import LargeIndecomposable.Cleaving.ClosedChains.ArrowCoefficient

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.ClosedZigzagTransfer

universe u x

variable {k : Type u} [Field k]
variable {C : Type x} [Category.{u} C] [Preadditive C] [Linear k C]

open LargeIndecomposable.ClosedZigzag

/-- The closed-zigzag coefficient boundary with every zero equation replaced
by its source-theoretic strict principal-span statement.  Coefficients are
required to kill the endpoint-Jacobson layer of their own landing path.  Thus
the only non-formal cross datum is that each forbidden cross composite lies
strictly below the stable landing generator in the principal bimodule chain. -/
structure ClosedZigzagSpanCoefficientData
    (n : ℕ) (hn : 2 ≤ n)
    (D : LinearPathCategory.Category k (Vertex n)ᵒᵖ ⥤ C)
    [D.Additive] [D.Linear k] where
  coefficient : ∀
    {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ},
    Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X) →
      (D.obj X ⟶ D.obj Y) →ₗ[k] k
  normalized : ∀
    {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)),
    coefficient p (D.map (LinearPathCategory.pathHom p)) = 1
  endpoint_kernel : ∀
    {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)),
    endpointRadicalSubmodule (k := k)
        (D.map (LinearPathCategory.pathHom p)) ≤
      LinearMap.ker (coefficient p)
  identity_middle_whisker : ∀
    {X' X Y Y' : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex X)
      (LinearPathCategory.vertex X'))
    (g : D.obj X ⟶ D.obj Y)
    (q : Quiver.Path (LinearPathCategory.vertex Y')
      (LinearPathCategory.vertex Y))
    (r : Quiver.Path (LinearPathCategory.vertex Y')
      (LinearPathCategory.vertex X'))
    (s : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)),
    s.length = 0 →
      coefficient r
        (D.map (LinearPathCategory.pathHom p) ≫ g ≫
          D.map (LinearPathCategory.pathHom q)) = coefficient s g
  cross_span_lt : ∀
    {X' X Y Y' : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex X)
      (LinearPathCategory.vertex X'))
    (g : D.obj X ⟶ D.obj Y)
    (q : Quiver.Path (LinearPathCategory.vertex Y')
      (LinearPathCategory.vertex Y))
    (r : Quiver.Path (LinearPathCategory.vertex Y')
      (LinearPathCategory.vertex X')),
    IsEmpty (Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) →
      twoSidedEndomorphismSpan k
          (D.map (LinearPathCategory.pathHom p) ≫ g ≫
            D.map (LinearPathCategory.pathHom q)) <
        twoSidedEndomorphismSpan k
          (D.map (LinearPathCategory.pathHom r))

namespace ClosedZigzagSpanCoefficientData

variable {n : ℕ} {hn : 2 ≤ n}
variable {D : LinearPathCategory.Category k (Vertex n)ᵒᵖ ⥤ C}
variable [D.Additive] [D.Linear k]

/-- Strict principal-span drop puts every forbidden cross composite in the
endpoint-radical layer, so its normalized coefficient vanishes. -/
def toCrossCoefficientData
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [HasBGRSDistributiveHomStructure k C]
    (h : ClosedZigzagSpanCoefficientData (k := k) n hn D) :
    ClosedZigzagCrossCoefficientData (k := k) n hn D where
  coefficient := h.coefficient
  normalized := h.normalized
  identity_middle_whisker := h.identity_middle_whisker
  cross_whisker_vanish := by
    intro X' X Y Y' p g q r hm
    apply h.endpoint_kernel r
    exact mem_endpointRadicalSubmodule_of_span_lt
      (h.cross_span_lt p g q r hm)

/-- The source-specific strict-span boundary yields the full BGRS 3.2
Hom-bifunctor retraction. -/
def homBifunctorRetraction
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [HasBGRSDistributiveHomStructure k C]
    (h : ClosedZigzagSpanCoefficientData (k := k) n hn D) :
    HomBifunctorRetraction (k := k) D :=
  h.toCrossCoefficientData.homBifunctorRetraction

end ClosedZigzagSpanCoefficientData
end LargeIndecomposable.ClosedZigzagTransfer
