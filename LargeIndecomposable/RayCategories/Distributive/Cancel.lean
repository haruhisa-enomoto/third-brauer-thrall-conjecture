module

public import LargeIndecomposable.RayCategories.Distributive.FromDistributive
public import LargeIndecomposable.RayCategories.RoiterVanishing.KeyLemma

/-!
# Cancellation in the ray category of a distributive algebra

The ray category of a distributive algebra has left and right cancellation
for nonzero composites (BGRS; the ported `bgrsRayRepresentativeProduct_cancel_*`
lemmas). These are the hypotheses of the key lemma and of Fischbacher's
reduction.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

namespace SplitBasicData

universe u v w

variable {k : Type u} [Field k] [Infinite k] {B : Type v} [Ring B] [Algebra k B]
  [FiniteDimensional k B] {ι : Type w} [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι)

open LargeIndecomposable in
/-- Left cancellation in the ray category of a distributive algebra. -/
theorem leftCancel (hd : IsDistribIdeals B) :
    letI := S.distribHomStructure hd
    RayCat.LeftCancel S.toIdempotents.RayCategory := by
  letI := S.distribHomStructure hd
  intro X Y Z f g h hfg h0
  induction f using Quotient.inductionOn with
  | _ f =>
  induction g using Quotient.inductionOn with
  | _ g =>
  induction h using Quotient.inductionOn with
  | _ h =>
  change unitRay (bgrsRayRepresentativeProduct f g) = unitRay (bgrsRayRepresentativeProduct f h)
    at hfg
  change unitRay (bgrsRayRepresentativeProduct f g) ≠ 0 at h0
  rw [Ne, unitRay_eq_zero_iff] at h0
  rw [unitRay_eq_iff] at hfg
  exact (unitRay_eq_iff _ _).2
    (bgrsRayRepresentativeProduct_cancel_left_of_bgrsDistributiveHomStructure (k := k) f g h hfg h0)

open LargeIndecomposable in
/-- Right cancellation in the ray category of a distributive algebra. -/
theorem rightCancel (hd : IsDistribIdeals B) :
    letI := S.distribHomStructure hd
    RayCat.RightCancel S.toIdempotents.RayCategory := by
  letI := S.distribHomStructure hd
  intro X Y Z f g h hfg h0
  induction f using Quotient.inductionOn with
  | _ f =>
  induction g using Quotient.inductionOn with
  | _ g =>
  induction h using Quotient.inductionOn with
  | _ h =>
  change unitRay (bgrsRayRepresentativeProduct f h) = unitRay (bgrsRayRepresentativeProduct g h)
    at hfg
  change unitRay (bgrsRayRepresentativeProduct f h) ≠ 0 at h0
  rw [Ne, unitRay_eq_zero_iff] at h0
  rw [unitRay_eq_iff] at hfg
  exact (unitRay_eq_iff _ _).2
    (bgrsRayRepresentativeProduct_cancel_right_of_bgrsDistributiveHomStructure (k := k) f g h hfg h0)

end SplitBasicData

end LargeIndecomposable
