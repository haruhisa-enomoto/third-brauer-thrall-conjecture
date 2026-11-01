module

public import LargeIndecomposable.Cleaving.ClosedChains.ArrowCoefficient
public import LargeIndecomposable.Cleaving.ClosedChains.CrossUniverseThinPathRetraction

@[expose] public section

/-!
# Thin-path retractions from strict principal-span drops

For a thin free path category, the BGRS supplement calculation can be stated
without choosing complements.  Choose on every nonzero path image a normalized
linear coefficient killing its endpoint-Jacobson layer.  Naturality follows if
two explicit kinds of terms have strictly smaller principal two-sided span than
the landing path image:

* whiskered ambient morphisms for which the source has no middle path;
* the difference between a nontrivially whiskered morphism and the scalar
  multiple prescribed by the middle-path coefficient.

Distributivity turns each strict span drop into membership in the landing
endpoint-Jacobson layer.  This file compiles precisely those local statements
into the Hom-bifunctor retraction used by BGRS Proposition 3.2.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.ClosedZigzagTransfer

universe u v w x z

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]
variable {C : Type x} [Category.{z} C] [Preadditive C] [Linear k C]

abbrev ThinFreeLinearCategory := LinearPathCategory.Category k Q

/-- The canonical normalized endpoint-radical coefficient chosen for each
nonzero path image. -/
def normalizedThinPathCoefficient
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure k C]
    (D : ThinFreeLinearCategory (k := k) (Q := Q) ⥤ C)
    [D.Additive] [D.Linear k]
    (map_path_ne_zero : ∀
      {X Y : ThinFreeLinearCategory (k := k) (Q := Q)}
      (p : Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X)),
      D.map (LinearPathCategory.pathHom p) ≠ 0)
    {X Y : ThinFreeLinearCategory (k := k) (Q := Q)}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) :
    (D.obj X ⟶ D.obj Y) →ₗ[k] k :=
  Classical.choose
    (exists_normalized_endpointRadicalCoefficient
      (D.map (LinearPathCategory.pathHom p)) (map_path_ne_zero p))

@[simp]
theorem normalizedThinPathCoefficient_normalized
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure k C]
    (D : ThinFreeLinearCategory (k := k) (Q := Q) ⥤ C)
    [D.Additive] [D.Linear k]
    (map_path_ne_zero : ∀
      {X Y : ThinFreeLinearCategory (k := k) (Q := Q)}
      (p : Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X)),
      D.map (LinearPathCategory.pathHom p) ≠ 0)
    {X Y : ThinFreeLinearCategory (k := k) (Q := Q)}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) :
    normalizedThinPathCoefficient D map_path_ne_zero p
        (D.map (LinearPathCategory.pathHom p)) = 1 :=
  (Classical.choose_spec
    (exists_normalized_endpointRadicalCoefficient
      (D.map (LinearPathCategory.pathHom p)) (map_path_ne_zero p))).1

theorem endpointRadical_le_normalizedThinPathCoefficient_ker
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure k C]
    (D : ThinFreeLinearCategory (k := k) (Q := Q) ⥤ C)
    [D.Additive] [D.Linear k]
    (map_path_ne_zero : ∀
      {X Y : ThinFreeLinearCategory (k := k) (Q := Q)}
      (p : Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X)),
      D.map (LinearPathCategory.pathHom p) ≠ 0)
    {X Y : ThinFreeLinearCategory (k := k) (Q := Q)}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) :
    endpointRadicalSubmodule (k := k)
        (D.map (LinearPathCategory.pathHom p)) ≤
      LinearMap.ker
        (normalizedThinPathCoefficient D map_path_ne_zero p) :=
  (Classical.choose_spec
    (exists_normalized_endpointRadicalCoefficient
      (D.map (LinearPathCategory.pathHom p)) (map_path_ne_zero p))).2

/-- Every forbidden cross-composite has strictly smaller principal span than
the path into whose Hom space it lands. -/
def ThinPathCrossSpanDrops
    (D : ThinFreeLinearCategory (k := k) (Q := Q) ⥤ C)
    [D.Additive] [D.Linear k] : Prop :=
  ∀ {X' X Y Y' : ThinFreeLinearCategory (k := k) (Q := Q)}
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

/-- Every nontrivial whiskering differs from its prescribed path coefficient
by a term of strictly smaller principal span than the landing path. -/
def ThinPathWhiskerDeviationSpanDrops
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure k C]
    (D : ThinFreeLinearCategory (k := k) (Q := Q) ⥤ C)
    [D.Additive] [D.Linear k]
    (map_path_ne_zero : ∀
      {X Y : ThinFreeLinearCategory (k := k) (Q := Q)}
      (p : Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X)),
      D.map (LinearPathCategory.pathHom p) ≠ 0) : Prop :=
  ∀ {X' X Y Y' : ThinFreeLinearCategory (k := k) (Q := Q)}
    (p : Quiver.Path (LinearPathCategory.vertex X)
      (LinearPathCategory.vertex X'))
    (g : D.obj X ⟶ D.obj Y)
    (q : Quiver.Path (LinearPathCategory.vertex Y')
      (LinearPathCategory.vertex Y))
    (r : Quiver.Path (LinearPathCategory.vertex Y')
      (LinearPathCategory.vertex X'))
    (s : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)),
  p.length + q.length ≠ 0 →
    twoSidedEndomorphismSpan k
        (D.map (LinearPathCategory.pathHom p) ≫ g ≫
            D.map (LinearPathCategory.pathHom q) -
          normalizedThinPathCoefficient D map_path_ne_zero s g •
            D.map (LinearPathCategory.pathHom r)) <
      twoSidedEndomorphismSpan k
        (D.map (LinearPathCategory.pathHom r))

/-- Strict-span supplement data for a functor from a thin free path category.
The two span fields are the source-theoretic content of the supplement
inclusions; all subsequent coefficient equations are derived from them. -/
structure ThinPathStrictSpanData
    (D : ThinFreeLinearCategory (k := k) (Q := Q) ⥤ C)
    [D.Additive] [D.Linear k] where
  path_subsingleton : ∀ a b : Q, Subsingleton (Quiver.Path a b)
  coefficient : ∀ {X Y : ThinFreeLinearCategory (k := k) (Q := Q)},
    Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X) →
      (D.obj X ⟶ D.obj Y) →ₗ[k] k
  normalized : ∀ {X Y : ThinFreeLinearCategory (k := k) (Q := Q)}
      (p : Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X)),
    coefficient p (D.map (LinearPathCategory.pathHom p)) = 1
  endpoint_kernel : ∀
      {X Y : ThinFreeLinearCategory (k := k) (Q := Q)}
      (p : Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X)),
    endpointRadicalSubmodule (k := k)
        (D.map (LinearPathCategory.pathHom p)) ≤
      LinearMap.ker (coefficient p)
  cross_span_lt : ∀
      {X' X Y Y' : ThinFreeLinearCategory (k := k) (Q := Q)}
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
  whisker_deviation_span_lt : ∀
      {X' X Y Y' : ThinFreeLinearCategory (k := k) (Q := Q)}
      (p : Quiver.Path (LinearPathCategory.vertex X)
        (LinearPathCategory.vertex X'))
      (g : D.obj X ⟶ D.obj Y)
      (q : Quiver.Path (LinearPathCategory.vertex Y')
        (LinearPathCategory.vertex Y))
      (r : Quiver.Path (LinearPathCategory.vertex Y')
        (LinearPathCategory.vertex X'))
      (s : Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X)),
    p.length + q.length ≠ 0 →
      twoSidedEndomorphismSpan k
          (D.map (LinearPathCategory.pathHom p) ≫ g ≫
              D.map (LinearPathCategory.pathHom q) -
            coefficient s g •
              D.map (LinearPathCategory.pathHom r)) <
        twoSidedEndomorphismSpan k
          (D.map (LinearPathCategory.pathHom r))

namespace ThinPathStrictSpanData

variable {D : ThinFreeLinearCategory (k := k) (Q := Q) ⥤ C}
variable [D.Additive] [D.Linear k]

/-- Construct strict-span data using the canonical endpoint-radical
coefficient on every nonzero path image.  Thus the only supplied supplement
facts are the two explicit families of strict principal-span drops. -/
def ofPathImagesNonzero
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure k C]
    (path_subsingleton : ∀ a b : Q, Subsingleton (Quiver.Path a b))
    (map_path_ne_zero : ∀
      {X Y : ThinFreeLinearCategory (k := k) (Q := Q)}
      (p : Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X)),
      D.map (LinearPathCategory.pathHom p) ≠ 0)
    (cross_span_lt : ∀
      {X' X Y Y' : ThinFreeLinearCategory (k := k) (Q := Q)}
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
            (D.map (LinearPathCategory.pathHom r)))
    (whisker_deviation_span_lt : ∀
      {X' X Y Y' : ThinFreeLinearCategory (k := k) (Q := Q)}
      (p : Quiver.Path (LinearPathCategory.vertex X)
        (LinearPathCategory.vertex X'))
      (g : D.obj X ⟶ D.obj Y)
      (q : Quiver.Path (LinearPathCategory.vertex Y')
        (LinearPathCategory.vertex Y))
      (r : Quiver.Path (LinearPathCategory.vertex Y')
        (LinearPathCategory.vertex X'))
      (s : Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X)),
      p.length + q.length ≠ 0 →
        twoSidedEndomorphismSpan k
            (D.map (LinearPathCategory.pathHom p) ≫ g ≫
                D.map (LinearPathCategory.pathHom q) -
              normalizedThinPathCoefficient D map_path_ne_zero s g •
                D.map (LinearPathCategory.pathHom r)) <
          twoSidedEndomorphismSpan k
            (D.map (LinearPathCategory.pathHom r))) :
    ThinPathStrictSpanData (k := k) D where
  path_subsingleton := path_subsingleton
  coefficient := normalizedThinPathCoefficient D map_path_ne_zero
  normalized := normalizedThinPathCoefficient_normalized D map_path_ne_zero
  endpoint_kernel :=
    endpointRadical_le_normalizedThinPathCoefficient_ker D map_path_ne_zero
  cross_span_lt := cross_span_lt
  whisker_deviation_span_lt := whisker_deviation_span_lt

/-- The two strict principal-span conditions imply every coefficient
naturality equation. -/
def toThinPathCoefficientData
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure k C]
    (h : ThinPathStrictSpanData (k := k) D) :
    LargeIndecomposable.ClosedZigzagCrossUniverse.ThinPathCoefficientData
      (k := k) D where
  path_subsingleton := h.path_subsingleton
  coefficient := h.coefficient
  normalized := h.normalized
  whisker_coefficient := by
    intro X' X Y Y' p g q r
    letI : Subsingleton
        (Quiver.Path (LinearPathCategory.vertex Y)
          (LinearPathCategory.vertex X)) :=
      h.path_subsingleton _ _
    letI : Subsingleton
        (Quiver.Path (LinearPathCategory.vertex Y')
          (LinearPathCategory.vertex X')) :=
      h.path_subsingleton _ _
    by_cases hm : Nonempty
        (Quiver.Path (LinearPathCategory.vertex Y)
          (LinearPathCategory.vertex X))
    · rw [coefficientOrZero_of_nonempty _ _ hm]
      let s := Classical.choice hm
      change h.coefficient r
          (D.map (LinearPathCategory.pathHom p) ≫ g ≫
            D.map (LinearPathCategory.pathHom q)) =
        h.coefficient s g
      by_cases houter : p.length + q.length = 0
      · obtain ⟨hp0, hq0⟩ := Nat.add_eq_zero_iff.mp houter
        have hpEq := p.eq_of_length_zero hp0
        have hqEq := q.eq_of_length_zero hq0
        change X = X' at hpEq
        change Y' = Y at hqEq
        subst X'
        subst Y'
        rw [Quiver.Path.eq_nil_of_length_zero p hp0,
          Quiver.Path.eq_nil_of_length_zero q hq0]
        simp only [LinearPathCategory.pathHom_nil, D.map_id,
          Category.id_comp, Category.comp_id]
        rw [Subsingleton.elim r s]
      · have hdrop := h.whisker_deviation_span_lt p g q r s houter
        have hmem := mem_endpointRadicalSubmodule_of_span_lt hdrop
        have hzero := h.endpoint_kernel r hmem
        change h.coefficient r
            (D.map (LinearPathCategory.pathHom p) ≫ g ≫
                D.map (LinearPathCategory.pathHom q) -
              h.coefficient s g •
                D.map (LinearPathCategory.pathHom r)) = 0 at hzero
        rw [LinearMap.map_sub, LinearMap.map_smul, h.normalized,
          smul_eq_mul, mul_one, sub_eq_zero] at hzero
        exact hzero
    · have hm' : IsEmpty
          (Quiver.Path (LinearPathCategory.vertex Y)
            (LinearPathCategory.vertex X)) :=
        not_nonempty_iff.mp hm
      rw [coefficientOrZero_of_isEmpty _ _ hm']
      apply h.endpoint_kernel r
      exact mem_endpointRadicalSubmodule_of_span_lt
        (h.cross_span_lt p g q r hm')

/-- Strict principal-span supplements yield the full BGRS 3.2
Hom-bifunctor retraction. -/
def homBifunctorRetraction
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure k C]
    (h : ThinPathStrictSpanData (k := k) D) :
    LargeIndecomposable.ClosedZigzagCrossUniverse.HomBifunctorRetraction
      (k := k) D :=
  h.toThinPathCoefficientData.homBifunctorRetraction

/-- Nonzero path images together with the two strict-span supplement
conditions are a source-level criterion for cleaving any thin free diagram. -/
def homBifunctorRetractionOfPathImagesNonzeroAndStrictSpanDrops
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure k C]
    (path_subsingleton : ∀ a b : Q, Subsingleton (Quiver.Path a b))
    (map_path_ne_zero : ∀
      {X Y : ThinFreeLinearCategory (k := k) (Q := Q)}
      (p : Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X)),
      D.map (LinearPathCategory.pathHom p) ≠ 0)
    (cross_span_drops : ThinPathCrossSpanDrops (k := k) D)
    (whisker_deviation_span_drops :
      ThinPathWhiskerDeviationSpanDrops (k := k) D map_path_ne_zero) :
    LargeIndecomposable.ClosedZigzagCrossUniverse.HomBifunctorRetraction
      (k := k) D :=
  (ofPathImagesNonzero path_subsingleton map_path_ne_zero
    cross_span_drops whisker_deviation_span_drops).homBifunctorRetraction

end ThinPathStrictSpanData

end LargeIndecomposable.ClosedZigzagTransfer
