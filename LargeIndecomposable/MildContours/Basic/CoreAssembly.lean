module

public import LargeIndecomposable.MildContours.Basic.DeepContoursFromCore
public import LargeIndecomposable.MildContours.Basic.TinyBridgeOp
public import LargeIndecomposable.MildContours.PennyFarthings.OpenAssembly
public import LargeIndecomposable.MildContours.PennyFarthings.OpenCase2
public import LargeIndecomposable.MildContours.DumbBells.RemainingFacts
public import LargeIndecomposable.MildContours.Diamonds.Conclusion
public import LargeIndecomposable.MildContours.Basic.SplitBridge
public import LargeIndecomposable.MultiplicativeBases.Twisted.MulBasisFromDeep
public import LargeIndecomposable.MildContours.PennyFarthings.OpenLengthTwo

/-!
# `ScalarNode` from LPF and the exceptional categories

The core of [mild] Theorem 3 for the small ray category `P` of a minimal
representation-infinite distributive algebra, and for `Pᵒᵖ`, holds unless `P` or
`Pᵒᵖ` contains an exceptional dumb-bell (`DBExc`) or the exceptional
penny-farthing `Q₂'` (`PFExc`) (`RayCat.coreHyp_of_exc`, with the global facts
bridged: `noProjInj_small`, `noTiny_small`, `noTiny_small_op`, `noSplit_small`).
The remaining inputs are

* `LPFNode` ([mild] LPF, over all finite ray categories);
* `ExcNode`: for the exceptional categories, a zero-detecting lift for which the
  non-interlaced contours are deep or proportional (the standardness route).

`scalarNode_of_lpf_exc` assembles `ScalarNode`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable RayCat

universe u

/-- A ray-level statement for all finite ray categories. -/
def ForAllRay (F : ∀ (Q : Type) [Category.{0} Q] [HasZeroMorphisms Q] [IsRayCategory Q]
    [Fintype Q] [DecidableEq Q] [IsFiniteRayCategory Q] (k : Type u) [Field k] [Infinite k],
    Prop) : Prop :=
  ∀ (Q : Type) [Category.{0} Q] [HasZeroMorphisms Q] [IsRayCategory Q] [Fintype Q]
    [DecidableEq Q] [IsFiniteRayCategory Q] (k : Type u) [Field k] [Infinite k], F Q k

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

/-- **The exceptional-category node** (open): when the small ray category of `B`
or its opposites contains an exceptional dumb-bell or `Q₂'`, there is a
zero-detecting lift for which non-interlaced contours are deep or proportional. -/
def ExcNode : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B] [Algebra k B]
    [FiniteDimensional k B] (ι : Type) [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι),
    IsMinimalRepInfinite B → ∀ hd : IsDistribIdeals B,
      letI := S.distribHomStructure hd
      letI := S.locallySmall hd
      letI := S.isFiniteRayCategory hd
      letI : IsRayCategory (RaySmall.{0} S.toIdempotents.RayCategory) := isRayCategory_of_finiteRayCategory
      letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
      letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
      letI := isRayCategory_of_finiteRayCategory (C := (RaySmall.{0} S.toIdempotents.RayCategory)ᵒᵖ)
      letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory)ᵒᵖ := Fintype.ofFinite _
      letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory)ᵒᵖ := Classical.decEq _
      letI := isRayCategory_of_finiteRayCategory (C := (RaySmall.{0} S.toIdempotents.RayCategory)ᵒᵖᵒᵖ)
      letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory)ᵒᵖᵒᵖ := Fintype.ofFinite _
      letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory)ᵒᵖᵒᵖ := Classical.decEq _
      (DBExc (RaySmall.{0} S.toIdempotents.RayCategory) ∨ PFExc (RaySmall.{0} S.toIdempotents.RayCategory) ∨
        DBExc (RaySmall.{0} S.toIdempotents.RayCategory)ᵒᵖ ∨ PFExc (RaySmall.{0} S.toIdempotents.RayCategory)ᵒᵖ ∨
        PFExc (RaySmall.{0} S.toIdempotents.RayCategory)ᵒᵖᵒᵖ) →
      ∃ L : LargeIndecomposable.BGRSRayArrowLift (C := S.toIdempotents.ProjectiveCategory),
        (∀ {i j : RayVertex S.toIdempotents.RayCategory} (p : Quiver.Path i j),
          L.pathMap p = 0 ↔ LargeIndecomposable.rayPathMap p = 0) ∧
        ∀ {i j : RayVertex S.toIdempotents.RayCategory} {p q : Quiver.Path i j},
          (rayPathContourRelation (C := S.toIdempotents.RayCategory)).related p q →
          ¬(properWhiskerInterlacementRelation
            (rayPathContourRelation (C := S.toIdempotents.RayCategory))).interlaced p q →
          S.toIdempotents.IsBGRSDeepRayPath p ∨ (SplitBasicIdempotents.scalarRel S.toIdempotents L).related p q


end LargeIndecomposable
