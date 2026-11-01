module

public import LargeIndecomposable.RayCategories.Distributive.ProperQuotientCorners
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalFigure14
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalFigure15

@[expose] public section

/-!
# Reduction of long critical singular paths to BGRS Figures 14 and 15

The two imported files contain the literal finite sources and their explicit
one-parameter module families.  This file isolates the remaining geometric
content of BGRS 4.3: a critical singular path of length at least three must
produce either the Figure-14 diagram or the bound Figure-15 diagram in the
primitive projectives, and the induced Hom bifunctor must split.

This is deliberately a diagram-and-complement callback.  It assumes neither
representation-infiniteness nor the desired exclusion of long critical paths.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.CriticalSingularFigures1415

open LargeIndecomposable.ClosedZigzagCrossUniverse

universe u uA x

variable {k : Type u} [Field k]
variable {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]
variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))
variable [HasWellDefinedBGRSRayProduct S.ProjectiveCategory]

/-- A literal Figure-14 diagram in the primitive projectives, together with
the Hom-bifunctor splitting which makes its source a cleaving diagram. -/
def HasFigure14CleavingWitness : Prop :=
  ∃ G : LargeIndecomposable.CriticalSingularFigure14.DiagramData
      (C := S.ProjectiveCategory),
    Nonempty (HomBifunctorRetraction (k := k) (G.functor (k := k)))

/-- A literal bound Figure-15 diagram in the primitive projectives, including
its displayed length-three zero relation, together with the Hom-bifunctor
splitting which makes its quotient source a cleaving diagram. -/
def HasFigure15CleavingWitness : Prop :=
  ∃ G : LargeIndecomposable.CriticalSingularFigure15.DiagramData
      (C := S.ProjectiveCategory),
    Nonempty (HomBifunctorRetraction (k := k) (G.functor (k := k)))

/-- Exact BGRS-4.3 extraction boundary.  For each critical singular ray path
of length at least three, it returns one of the two displayed cleaving
diagrams.  The result is concrete finite diagram data plus a linear splitting
of the induced Hom bifunctor; it is not an equivalent-strength infinitude
assumption. -/
def HasCriticalLongPathFigureExtraction : Prop :=
  ∀ {i j : RayVertex (BGRSRayCategory S.ProjectiveCategory)}
      (p : Quiver.Path i j),
    IsCriticalBGRSLiftSingularPath p → 3 ≤ p.length →
      HasFigure14CleavingWitness (k := k) S ∨
        HasFigure15CleavingWitness (k := k) S

/-- The two explicit source families contradict representation-finiteness as
soon as the literal Figure-14/15 extraction is available.  In particular,
the finite scalar-control calculation for the Figure-15 family has already
been proved in its source file. -/
theorem no_long_critical_of_figureExtraction [Infinite k]
    (hextract : HasCriticalLongPathFigureExtraction (k := k) S)
    (hfinite : LargeIndecomposable.IsRepresentationFinite k A) :
    ∀ {i j : RayVertex (BGRSRayCategory S.ProjectiveCategory)}
      (p : Quiver.Path i j),
      IsCriticalBGRSLiftSingularPath p → ¬3 ≤ p.length := by
  intro i j p hp hlength
  rcases hextract p hp hlength with h14 | h15w
  · rcases h14 with ⟨G, ⟨hG⟩⟩
    exact
      (LargeIndecomposable.CriticalSingularFigure14.not_isRepresentationFinite_of_figure14Data
        S G hG) hfinite
  · rcases h15w with ⟨G, ⟨hG⟩⟩
    exact
      (LargeIndecomposable.CriticalSingularFigure15.not_isRepresentationFinite_of_figure15Data
        S G hG) hfinite

/-- Reusable endpoint of the BGRS-4.3 reduction: the explicit Figures 14 and
15, plus the exact extraction/splitting callback, imply the singular-pair
factorization used by the later presentation theorem. -/
theorem hasBGRSSingularPairFactorization_of_figureExtraction
    [Infinite k]
    [IsFiniteRayCategory (BGRSRayCategory S.ProjectiveCategory)]
    (hextract : HasCriticalLongPathFigureExtraction (k := k) S)
    (hfinite : LargeIndecomposable.IsRepresentationFinite k A) :
    HasBGRSSingularPairFactorization S.ProjectiveCategory := by
  apply hasBGRSSingularPairFactorization_of_no_long_critical
  exact no_long_critical_of_figureExtraction S hextract hfinite

end LargeIndecomposable.CriticalSingularFigures1415
