module

public import LargeIndecomposable.BongartzTheorem.Reduction.TheoremSix
public import LargeIndecomposable.MultiplicativeBases.Twisted.AssemblyMulBasis
public import LargeIndecomposable.RayCategories.Distributive.ProperQuotientCorners
public import LargeIndecomposable.RepresentationType.Basic.RepresentationFiniteForms
public import LargeIndecomposable.Modules.Duality.OppositeDuality
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.SingularPairDisjointness

/-!
# `TwistedMulBasisExists` from "only deep contours"

For a minimal representation-infinite distributive algebra `B`, BGRS §4
(adapted to mild algebras) gives a presentation whose path
values vanish exactly on the zero paths of the ray category. If moreover every
non-interlaced pair of paths with the same nonzero value is deep
(`OnlyDeepContours`, Bongartz's "On mild contours", Theorem 3), BGRS 2.9–2.10 give
a twisted multiplicative basis (`twistedMulBasisExists_of_onlyDeep`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Statement RayCat LargeIndecomposable

universe u

section Mild

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B] [FiniteDimensional k B]

/-- A minimal representation-infinite algebra is mild. -/
theorem mildAlg_of_minimal (hB : IsMinimalRepInfinite B) : MildAlg k B := fun J hJ ↦
  (isRepresentationFinite_iff_moduleForm k (B ⧸ J.asIdeal)).1 (hB.2 J hJ)

/-- `Bᵐᵒᵖ / J ≅ (B / J.unop)ᵐᵒᵖ`. -/
def quotMopEquiv (J : TwoSidedIdeal Bᵐᵒᵖ) :
    (Bᵐᵒᵖ ⧸ J.asIdeal) ≃+* (B ⧸ J.unop.asIdeal)ᵐᵒᵖ := by
  let φ : Bᵐᵒᵖ →+* (B ⧸ J.unop.asIdeal)ᵐᵒᵖ := RingHom.op (Ideal.Quotient.mk J.unop.asIdeal)
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective y.unop
    exact ⟨MulOpposite.op a, by
      change MulOpposite.op (Ideal.Quotient.mk J.unop.asIdeal a) = y
      rw [ha]; rfl⟩
  have hker : RingHom.ker φ = J.asIdeal := by
    ext x
    rw [RingHom.mem_ker, TwoSidedIdeal.mem_asIdeal]
    change MulOpposite.op (Ideal.Quotient.mk J.unop.asIdeal x.unop) = 0 ↔ _
    rw [MulOpposite.op_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem, TwoSidedIdeal.mem_asIdeal,
      TwoSidedIdeal.mem_unop_iff, MulOpposite.op_unop]
  exact (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hφ)

/-- The opposite of a minimal representation-infinite algebra is mild. -/
theorem mildAlg_mop_of_minimal (hB : IsMinimalRepInfinite B) : MildAlg k Bᵐᵒᵖ := by
  intro J hJ
  have hJ' : J.unop ≠ ⊥ := by
    intro h
    apply hJ
    ext x
    constructor
    · intro hx
      have : x.unop ∈ J.unop := by
        rw [TwoSidedIdeal.mem_unop_iff, MulOpposite.op_unop]; exact hx
      rw [h] at this
      have h0 : x.unop = 0 := this
      change x = 0
      rw [← MulOpposite.op_unop x, h0, MulOpposite.op_zero]
    · intro hx
      have h0 : x = 0 := hx
      rw [h0]; exact J.zero_mem
  have h1 := isRepresentationFinite_mop (k := k) (hB.2 J.unop hJ')
  have h2 := isRepresentationFinite_of_ringEquiv (quotMopEquiv J).symm h1
  exact (isRepresentationFinite_iff_moduleForm k (Bᵐᵒᵖ ⧸ J.asIdeal)).1 h2

variable (k) in
include k in
/-- The opposite of a minimal representation-infinite algebra is minimal
representation-infinite. -/
theorem isMinimalRepInfinite_mop (hB : IsMinimalRepInfinite B) : IsMinimalRepInfinite Bᵐᵒᵖ := by
  refine ⟨fun h ↦ hB.1 ?_, fun J hJ ↦ ?_⟩
  · have h1 := isRepresentationFinite_mop (k := k) h
    exact isRepresentationFinite_of_ringEquiv (RingEquiv.opOp B).symm h1
  · have hJ' : J.unop ≠ ⊥ := by
      intro h
      apply hJ
      ext x
      constructor
      · intro hx
        have : x.unop ∈ J.unop := by
          rw [TwoSidedIdeal.mem_unop_iff, MulOpposite.op_unop]; exact hx
        rw [h] at this
        have h0 : x.unop = 0 := this
        change x = 0
        rw [← MulOpposite.op_unop x, h0, MulOpposite.op_zero]
      · intro hx
        have h0 : x = 0 := hx
        rw [h0]; exact J.zero_mem
    have h1 := isRepresentationFinite_mop (k := k) (hB.2 J.unop hJ')
    exact isRepresentationFinite_of_ringEquiv (quotMopEquiv J).symm h1

lemma finite_twoSidedIdeal_mop [Finite (TwoSidedIdeal B)] : Finite (TwoSidedIdeal Bᵐᵒᵖ) :=
  Finite.of_equiv _ TwoSidedIdeal.opOrderIso.toEquiv

end Mild

/-- **The proportionality step**: for a minimal representation-infinite distributive
algebra there is a zero-detecting lift for which every non-interlaced pair of paths
with the same nonzero value is deep or has proportional values. This is what BGRS
2.9–2.10 need; `OnlyDeepContours` gives it with any zero-detecting normalized lift, and
the degenerate penny-farthing and the closed dumb-bell (where contours need not be
deep) are to be treated by an adapted lift. -/
def ScalarProportionality : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B] [Algebra k B]
    [FiniteDimensional k B] (ι : Type) [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι),
    IsMinimalRepInfinite B → ∀ hd : IsDistribIdeals B,
      letI := S.distribHomStructure hd
      letI := S.isFiniteRayCategory hd
      ∃ L : LargeIndecomposable.BGRSRayArrowLift (C := S.toIdempotents.ProjectiveCategory),
        (∀ {i j : RayVertex S.toIdempotents.RayCategory} (p : Quiver.Path i j),
          L.pathMap p = 0 ↔ LargeIndecomposable.rayPathMap p = 0) ∧
        ∀ {i j : RayVertex S.toIdempotents.RayCategory} {p q : Quiver.Path i j},
          (rayPathContourRelation (C := S.toIdempotents.RayCategory)).related p q →
          ¬(properWhiskerInterlacementRelation
            (rayPathContourRelation (C := S.toIdempotents.RayCategory))).interlaced p q →
          S.toIdempotents.IsBGRSDeepRayPath p ∨ (SplitBasicIdempotents.scalarRel S.toIdempotents L).related p q

/-- **`TwistedMulBasisExists` from `ScalarProportionality`** (BGRS 2.9–2.10). -/
theorem twistedMulBasisExists_of_scalar (h : ScalarProportionality.{u}) : TwistedMulBasisExists.{u} := by
  intro k _ _ B _ _ _ ι _ _ S hB hd
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isRayCategory hd
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  letI := S.isFiniteRayCategory hd
  have hfinI : Finite (TwoSidedIdeal B) := finite_twoSidedIdeal_of_isDistribIdeals k hd
  obtain ⟨L, hzero, hdp⟩ := h k B ι S hB hd
  have hscalar := fun {i j : RayVertex S.toIdempotents.RayCategory} {p q : Quiver.Path i j}
      (hpq : (rayPathContourRelation (C := S.toIdempotents.RayCategory)).related p q) ↦
    SplitBasicIdempotents.scalar_of_related_of_deep_or_scalar S.toIdempotents L hzero hdp hpq
  exact ⟨SplitBasicData.mulBasisOfLift' hzero hscalar (Set.toFinite _)⟩

end LargeIndecomposable
