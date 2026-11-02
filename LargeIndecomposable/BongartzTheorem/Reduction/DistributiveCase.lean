module

public import LargeIndecomposable.MildContours.Basic.ExcAssembly
public import LargeIndecomposable.Crowns.Basic.LongNotInContour
public import LargeIndecomposable.BongartzTheorem.Reduction.DataForm
public import LargeIndecomposable.BongartzTheorem.Reduction.CoverDichotomy

/-!
# The main results from the dichotomy step alone

`ScalarProportionality` is proved (`MildContours/Basic/ExcAssembly.lean`), so BGRS multiplicative bases hold
(`twistedMulBasisExists_of_scalar`). Bongartz's Theorem 6, Theorem A and both corollaries
now depend only on `CoverDichotomy` (the dichotomy on the universal cover).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open Statement

universe u

/-- **BGRS multiplicative bases** for minimal representation-infinite distributive
algebras. -/
theorem twistedMulBasisExists : TwistedMulBasisExists.{u} := twistedMulBasisExists_of_scalar scalarProportionality

end LargeIndecomposable
