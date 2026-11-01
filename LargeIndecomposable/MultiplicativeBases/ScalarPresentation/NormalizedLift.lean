module

public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalSingularPath
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.SingularPairMatching
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.RepeatedSingularArrow

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable

universe u v w

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasBGRSPairDichotomy C]

open SingularPairNormalization

section Distinct

variable [Linear k C]
variable [∀ X : C, IsLocalRing (End X)]
variable [∀ X : C, IsArtinianRing (End X)]
variable [HasBGRSDistributiveHomStructure k C]

include k

/-- Distributivity rules out a repeated arrow in every packaged singular
pair used by the simultaneous matching construction. -/
theorem singularPair_firstArrow_ne_secondArrow
    (q : SingularPair (C := C)) :
    q.1.firstArrow ≠ q.1.secondArrow := by
  intro hArrow
  have hsingular :
      rayPathMap (q.1.first.toPath.comp q.1.second.toPath) = 0 ∧
        ∃ (first : q.1.middle.obj.as ⟶ q.1.source.obj.as)
          (second : q.1.target.obj.as ⟶ q.1.middle.obj.as),
          unitRay first = q.1.first.1 ∧
            unitRay second = q.1.second.1 ∧ second ≫ first ≠ 0 := by
    refine ⟨q.2.1, ?_⟩
    obtain ⟨first, second, hne⟩ := q.2.2
    exact ⟨first.hom, second.hom, first.unitRay_hom,
      second.unitRay_hom, hne⟩
  apply (singularPair_packedArrows_ne (k := k)
    q.1.first q.1.second hsingular)
  exact congrArg
    (fun a : Arrow (C := C) ↦ packRayArrow a.hom) hArrow

end Distinct

/-- The unpackaged length-two factorization interface implies the packaged
matching interface. -/
theorem hasSingularPairFactorization_of_bgrs
    (hstructure : HasBGRSSingularPairFactorization C) :
    HasSingularPairFactorization (C := C) := by
  intro i j p hp
  obtain ⟨x, y, left, pair, right, hlength, hsingular, hpEq⟩ :=
    hstructure p hp
  cases pair with
  | nil => simp at hlength
  | @cons z y pair second =>
      cases pair with
      | nil => simp at hlength
      | @cons x z rest first =>
          have hrest : rest.length = 0 := by simpa using hlength
          obtain rfl := Quiver.Path.eq_of_length_zero rest hrest
          obtain rfl := Quiver.Path.eq_nil_of_length_zero rest hrest
          let cp : ComposablePair (C := C) :=
            { source := x
              middle := z
              target := y
              first := first
              second := second }
          have hcp : cp.IsSingular := by
            refine ⟨?_, ?_⟩
            · have hray := hsingular.1
              simp only [rayPathMap, LinearPathCategory.pathMap_cons,
                LinearPathCategory.pathMap_nil, rayArrowMorphism] at hray
              rw [Category.comp_id] at hray
              change rayArrowMorphism second ≫
                rayArrowMorphism first = 0 at hray
              simpa [cp, ComposablePair.path] using hray
            · obtain ⟨L, hL⟩ := hsingular.2
              refine ⟨
                { hom := L.representative first
                  unitRay_hom := L.unitRay_representative first },
                { hom := L.representative second
                  unitRay_hom := L.unitRay_representative second }, ?_⟩
              change L.representative second ≫
                L.representative first ≠ 0
              simpa only [BGRSRayArrowLift.pathMap,
                LinearPathCategory.pathMap_cons,
                LinearPathCategory.pathMap_nil, Category.comp_id,
                Category.assoc] using hL
          let sq : SingularPair (C := C) := ⟨cp, hcp⟩
          refine ⟨sq, left, right, ?_⟩
          simpa [sq, cp, ComposablePair.path] using hpEq

section Assembly

variable [Linear k C]
variable [∀ X : C, IsLocalRing (End X)]
variable [∀ X : C, IsArtinianRing (End X)]
variable [HasBGRSDistributiveHomStructure k C]

include k

/-- The two remaining source inputs—exclusion of long critical singular
paths and disjointness of singular pairs—produce a global representative
choice detecting exactly the zero ray paths.  Distinctness of the two arrows
inside a pair is derived from distributivity. -/
theorem exists_zeroDetectingNormalizedLift_of_no_long_critical
    [IsFiniteRayCategory (BGRSRayCategory C)]
    (hlong : ∀ {i j : RayVertex (BGRSRayCategory C)}
      (p : Quiver.Path i j),
      IsCriticalBGRSLiftSingularPath p → ¬3 ≤ p.length)
    (hdisjoint : ∀ p q : SingularPair (C := C),
      p.1.firstArrow = q.1.firstArrow ∨
      p.1.firstArrow = q.1.secondArrow ∨
      p.1.secondArrow = q.1.firstArrow ∨
      p.1.secondArrow = q.1.secondArrow → p = q) :
    ∃ L : BGRSRayArrowLift (C := C),
      ∀ {i j : RayVertex (BGRSRayCategory C)}
        (p : Quiver.Path i j),
        L.pathMap p = 0 ↔ rayPathMap p = 0 := by
  apply SingularPairNormalization.exists_zeroDetectingNormalizedLift
    (singularPair_firstArrow_ne_secondArrow (k := k)) hdisjoint
  apply hasSingularPairFactorization_of_bgrs
  exact hasBGRSSingularPairFactorization_of_no_long_critical hlong

end Assembly

end LargeIndecomposable
