module

public import LargeIndecomposable.MildContours.Assembly.DeepContoursFromCore
public import LargeIndecomposable.MildContours.Assembly.TinyBridgeOp
public import LargeIndecomposable.MildContours.PennyFarthings.OpenAssembly
public import LargeIndecomposable.MildContours.PennyFarthings.OpenCase2
public import LargeIndecomposable.MildContours.DumbBells.RemainingFacts
public import LargeIndecomposable.MildContours.Diamonds.Conclusion
public import LargeIndecomposable.MildContours.Assembly.SplitBridge
public import LargeIndecomposable.MultiplicativeBases.Twisted.MulBasisFromDeep
public import LargeIndecomposable.MildContours.PennyFarthings.OpenLengthTwo

/-!
# `ScalarProportionality` from LPF and the exceptional categories

The core of [mild] Theorem 3 for the small ray category `P` of a minimal
representation-infinite distributive algebra, and for `Pᵒᵖ`, holds unless `P` or
`Pᵒᵖ` contains an exceptional dumb-bell (`DBExc`) or the exceptional
penny-farthing `Q₂'` (`PFExc`) (`RayCat.coreHyp_of_exc`, with the global facts
bridged: `noProjInj_small`, `noTiny_small`, `noTiny_small_op`, `noSplit_small`).
The remaining inputs are

* `LengthTwoPennyFarthing` ([mild] LPF, over all finite ray categories);
* `ExceptionalContoursExcluded`: for the exceptional categories, a zero-detecting lift for which the
  non-interlaced contours are deep or proportional (the standardness route).

`scalarProportionality_of_lpf_exc` assembles `ScalarProportionality`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable RayCat

universe u

/-- `OneSidedCyclic` passes to the opposite category. -/
lemma OneSidedCyclic.op {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] (h : OneSidedCyclic Q) :
    OneSidedCyclic Qᵒᵖ := by
  intro X Y
  have tf : ∀ f g : X ⟶ Y, TwoSidedEndomorphismFactors f g →
      TwoSidedEndomorphismFactors f.unop g.unop := by
    rintro f g ⟨a, b, hab⟩
    exact ⟨b.unop, a.unop, by rw [hab]; simp⟩
  rcases h Y.unop X.unop with h' | h'
  · refine Or.inr fun f g hg hfg ↦ ?_
    obtain ⟨b, hb⟩ := h' _ _ (fun h0 ↦ hg (Quiver.Hom.unop_inj (by simpa using h0))) (tf f g hfg)
    exact ⟨b.op, Quiver.Hom.unop_inj (by simpa using hb)⟩
  · refine Or.inl fun f g hg hfg ↦ ?_
    obtain ⟨a, ha⟩ := h' _ _ (fun h0 ↦ hg (Quiver.Hom.unop_inj (by simpa using h0))) (tf f g hfg)
    exact ⟨a.op, Quiver.Hom.unop_inj (by simpa using ha)⟩


end LargeIndecomposable
