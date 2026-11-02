module

public import LargeIndecomposable.MeshCategories.AuslanderReitenQuiver.ARQuiver
public import LargeIndecomposable.RayCategories.RayTables.Rays
public import LargeIndecomposable.MeshCategories.AuslanderReitenQuiver.ARBrick
public import LargeIndecomposable.StandardForm.Deformations.FilteredNormalForm
public import LargeIndecomposable.StandardForm.Main.StatementsPartOne
public import LargeIndecomposable.StandardForm.Main.StandardAlgebras
public import LargeIndecomposable.Modules.KrullSchmidt.SkeletonExists
public import LargeIndecomposable.Modules.Corners.BasicAlgebraCorner
public import LargeIndecomposable.MultiplicativeBases.Normed.A0Normed
public import LargeIndecomposable.RayCategories.RayTables.RayProduct
public import LargeIndecomposable.RayCategories.RayTables.RayTransport
public import LargeIndecomposable.StandardForm.Hochschild.CoefficientBound
public import LargeIndecomposable.StandardForm.Main.StandardRay

/-!
# Main theorems (statements)

Theorems A and B of the introduction, Theorem 11.7
(`thm:final-basis`), Corollary 5.5 (`cor:away-from-two-basis`), and
Theorem 11.8(2) (`thm:final-standardness`).

Throughout, `k` is algebraically closed and `A` is a finite-dimensional
`k`-algebra, in the same universe (the general Auslander--Reiten theory
works in one universe). "Characteristic different from two" is `ringChar k ≠ 2`.

## References

* *Multiplicative bases and deformations of representation-finite algebras*, <https://github.com/haruhisa-enomoto/multiplicative-bases-deformations>. Numbered statements cited here refer to it.
-/

@[expose] public section

set_option autoImplicit false

namespace LargeIndecomposable

universe u

variable (k : Type u) [Field k] [IsAlgClosed k]
  (A : Type u) [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- **Theorem B** (that paper; Corollary 5.5, `cor:away-from-two-basis`).
Every basic finite-dimensional representation-finite algebra over an
algebraically closed field of characteristic different from two is
standard. -/
theorem theoremB (hbasic : IsBasicAlgebra A) (hA : IsRepresentationFinite k Aᵐᵒᵖ)
    (hchar : ringChar k ≠ 2) :
    IsStandard k A := by
  letI : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k Aᵐᵒᵖ
  intro S
  classical
  obtain ⟨b⟩ := S.nonempty_arrowBases
  -- Proposition 5.4: surjective mesh derivatives give the filtered normal form
  refine S.isStandard_of_derivativesSurjective b fun m hm ↦ ?_
  -- Proposition 5.3, with the brick hypothesis from Lemma 5.2 and Proposition 2.10
  exact meshCorrectionSpaces S.arTranslationQuiver S.hasAtMostOneArrow (S.arCoefficients b)
    (fun x y ↦ S.finiteDimensional_meshHom b x y) hchar (S.brickHypothesis b) m hm

/-- **Corollary 5.5(2)** (`cor:away-from-two-basis`), existence part: a basic
representation-finite algebra over an algebraically closed field of
characteristic different from two has a normed multiplicative basis. The
standard equivalence of Theorem B identifies `A` with `A₀` (restricting to the
projective labels), and `A₀` has a normed multiplicative basis by
Proposition 4.14 and Corollary 3.3. -/
theorem basic_hasNormedBasis (hbasic : IsBasicAlgebra A) (hA : IsRepresentationFinite k Aᵐᵒᵖ)
    (hchar : ringChar k ≠ 2) : HasNormedMultiplicativeBasis k A := by
  letI : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k Aᵐᵒᵖ
  obtain ⟨S⟩ := exists_indSkeleton hA
  have hstd := theoremB k A hbasic hA hchar S
  obtain ⟨n, e, he, hprim, hb⟩ := hbasic
  exact S.hasNormedBasis_of_isStandard he hprim hb hstd

/-- **Theorem A away from characteristic two** (that paper; Theorem 11.7(1)
for `char k ≠ 2`, via Corollary 5.5(2) and Lemma 2.1): the basic algebra `eAe`
is a representation-finite full corner, it has a normed multiplicative basis,
and Lemma 2.1 lifts it to `A`. -/
theorem theoremA_of_ringChar_ne_two (hA : IsRepresentationFinite k Aᵐᵒᵖ) (hchar : ringChar k ≠ 2) :
    HasNormedMultiplicativeBasis k A := by
  obtain ⟨e, he, hfull, hbasic⟩ := exists_basic_full_corner k A
  haveI : FiniteDimensional k he.Corner := corner_finite he
  exact nonbasicBasis he hfull hbasic
    (basic_hasNormedBasis k he.Corner hbasic (corner_isRepresentationFinite hA he) hchar)

end LargeIndecomposable
