module

public import LargeIndecomposable.RayCategories.Distributive.ProperQuotientCorners
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.RoiterFigure13EPositiveSupplements

@[expose] public section

/-!
# Roiter's square alternative from Figure 13

The exact Figure-13 hard branch is stated for morphisms which generate their
outer Hom spaces.  This file performs the reduction from arbitrary prohibited
morphisms to such generators.  The two local ingredients are that primitive-
projective endomorphism rings are commutative and that, over a commutative
endpoint ring, transit or cotransit passes from a generator to every element
of its principal two-sided span.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory

open LargeIndecomposable.ClosedZigzagTransfer

universe u v x

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

variable [LargeIndecomposable.HasBGRSDistributiveHomStructure
  k S.ProjectiveCategory]

/-- Every endomorphism ring of a chosen primitive projective is commutative.
If its radical is nonzero, a maximal radical parameter generates the whole
algebra; if the radical vanishes, the split residue map is injective. -/
theorem end_mul_comm (X : S.ProjectiveCategory) (a b : End X) :
    a * b = b * a := by
  letI : Module.Finite k (End X) := by
    change Module.Finite k (X ⟶ X)
    infer_instance
  by_cases hJ : Ring.jacobson (End X) = ⊥
  · have hres : S.projectiveEndResidue X (a * b - b * a) = 0 := by
      rw [map_sub, map_mul, map_mul, mul_comm, sub_self]
    have hmem : a * b - b * a ∈ Ring.jacobson (End X) := by
      rw [S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson,
        ← S.projectiveEndResidue_eq_zero_iff_val_mem_jacobson]
      exact hres
    rw [hJ] at hmem
    exact sub_eq_zero.mp (by simpa using hmem)
  · obtain ⟨tau, htauJ, htau0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot hJ
    let P : OrientedRadicalPowerParameter (k := k) X :=
      Classical.choice
        (nonempty_orientedRadicalPowerParameter_of_nonzero_radical
          (k := k) (C := S.ProjectiveCategory) X tau htauJ htau0)
    exact P.mul_comm a b

/-- Every endomorphism of a chosen primitive projective allows transit. -/
theorem end_allowsTransit (X : S.ProjectiveCategory) (f : End X) :
    LargeIndecomposable.AllowsTransit f := by
  intro a
  refine ⟨a, ?_⟩
  simpa only [End.mul_def] using
    congrArg End.asHom (end_mul_comm S X f a)

/-- Every endomorphism of a chosen primitive projective allows cotransit. -/
theorem end_allowsCotransit (X : S.ProjectiveCategory) (f : End X) :
    LargeIndecomposable.AllowsCotransit f := by
  intro b
  refine ⟨b, ?_⟩
  simpa only [End.mul_def] using
    congrArg End.asHom (end_mul_comm S X b f)

end LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory

namespace LargeIndecomposable.RoiterFigure13EAmbient

open LargeIndecomposable.ClosedZigzagTransfer
open LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory

universe u v x

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

variable [LargeIndecomposable.HasBGRSDistributiveHomStructure
  k S.ProjectiveCategory]

/-- Figure 13 proves Roiter's literal square-annihilation alternative for
arbitrary morphisms in the split-basic primitive-projective category. -/
theorem roiterTransitSquareAlternative
    (hfinite : LargeIndecomposable.MildAlg k A)
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfNotC : ¬ LargeIndecomposable.AllowsCotransit f)
    (hgNotT : ¬ LargeIndecomposable.AllowsTransit g) :
    LargeIndecomposable.LeftJacobsonSquareAnnihilates f ∨
      LargeIndecomposable.RightJacobsonSquareAnnihilates g := by
  by_contra hsquare
  push Not at hsquare
  obtain ⟨P, hleft, hright⟩ :=
    exists_radicalPowerParameter_sq_nonzero_of_not_squareAlternative
      S f g hsquare.1 hsquare.2
  obtain ⟨mu, hmuSpan⟩ :=
    exists_full_twoSidedEndomorphismSpan
      (k := k) (C := S.ProjectiveCategory) X Y
  obtain ⟨nu, hnuSpan⟩ :=
    exists_full_twoSidedEndomorphismSpan
      (k := k) (C := S.ProjectiveCategory) Y Z
  have hfmem : f ∈ LargeIndecomposable.twoSidedEndomorphismSpan k mu := by
    rw [hmuSpan]
    exact Submodule.mem_top
  have hgmem : g ∈ LargeIndecomposable.twoSidedEndomorphismSpan k nu := by
    rw [hnuSpan]
    exact Submodule.mem_top
  have hmuNotC : ¬ LargeIndecomposable.AllowsCotransit mu := by
    intro hmuC
    apply hfNotC
    exact hmuC.of_mem_twoSidedEndomorphismSpan
      (fun a b ↦ end_mul_comm S X a b) hfmem
  have hnuNotT : ¬ LargeIndecomposable.AllowsTransit nu := by
    intro hnuT
    apply hgNotT
    exact hnuT.of_mem_twoSidedEndomorphismSpan
      (fun a b ↦ end_mul_comm S Z a b) hgmem
  have hXY : X ≠ Y := by
    intro h
    subst Y
    exact hmuNotC (end_allowsCotransit S X mu)
  have hYZ : Y ≠ Z := by
    intro h
    subst Z
    exact hnuNotT (end_allowsTransit S Y nu)
  have hmuT : LargeIndecomposable.AllowsTransit mu :=
    (LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := S.ProjectiveCategory) mu).resolve_right hmuNotC
  have hnuC : LargeIndecomposable.AllowsCotransit nu :=
    (LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := S.ProjectiveCategory) nu).resolve_left hnuNotT
  obtain ⟨b, hfb⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit hmuT hfmem
  obtain ⟨a, hga⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsCotransit hnuC hgmem
  have hmuLeft : mu ≫ (P.tau ^ 2).asHom ≠ 0 := by
    intro hzero
    apply hleft
    calc
      f ≫ (P.tau ^ 2).asHom =
          (mu ≫ b.asHom) ≫ (P.tau ^ 2).asHom := by rw [hfb]
      _ = (mu ≫ (P.tau ^ 2).asHom) ≫ b.asHom := by
        simpa only [End.mul_def, Category.assoc] using
          congrArg (fun q : End Y ↦ mu ≫ q.asHom)
            (end_mul_comm S Y (P.tau ^ 2) b)
      _ = 0 := by rw [hzero]; simp
  have hnuRight : (P.tau ^ 2).asHom ≫ nu ≠ 0 := by
    intro hzero
    apply hright
    calc
      (P.tau ^ 2).asHom ≫ g =
          (P.tau ^ 2).asHom ≫ (a.asHom ≫ nu) := by rw [hga]
      _ = a.asHom ≫ ((P.tau ^ 2).asHom ≫ nu) := by
        simpa only [End.mul_def, Category.assoc] using
          congrArg (fun q : End Y ↦ q.asHom ≫ nu)
            (end_mul_comm S Y a (P.tau ^ 2))
      _ = 0 := by rw [hzero]; simp
  have hspecial : LargeIndecomposable.IsBGRSSpecialZero mu nu :=
    LargeIndecomposable.RoiterFigure13Quotient.isBGRSSpecialZero_of_exact_hard_branch
      S mu nu P hfinite hmuSpan hnuSpan hXY hYZ hmuNotC hnuNotT
        hmuLeft hnuRight
  obtain ⟨R⟩ := nonempty_zeroRepresentativePair_of_special
    S mu nu hspecial
  exact false_of_figure13_exact_hard_branch
    S mu nu P R hfinite hmuSpan hnuSpan hXY hYZ hmuNotC hnuNotT
      hmuLeft hnuRight

/-- BGRS 4.3(a): a prohibited pair carrying a nonzero middle-radical
sandwich has full principal span on both sides.  Otherwise a full generator
differs by a nonunit middle coefficient, so the displayed sandwich factors
through the square of the middle radical and Roiter's alternative kills it. -/
theorem full_outer_spans_of_nonzeroJacobsonSandwich
    (hfinite : LargeIndecomposable.MildAlg k A)
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfNotC : ¬ LargeIndecomposable.AllowsCotransit f)
    (hgNotT : ¬ LargeIndecomposable.AllowsTransit g)
    (hsandwich : LargeIndecomposable.HasNonzeroJacobsonSandwich f g) :
    LargeIndecomposable.twoSidedEndomorphismSpan k f = ⊤ ∧
      LargeIndecomposable.twoSidedEndomorphismSpan k g = ⊤ := by
  obtain ⟨mu, hmuSpan⟩ :=
    exists_full_twoSidedEndomorphismSpan
      (k := k) (C := S.ProjectiveCategory) X Y
  obtain ⟨nu, hnuSpan⟩ :=
    exists_full_twoSidedEndomorphismSpan
      (k := k) (C := S.ProjectiveCategory) Y Z
  have hfmem : f ∈ LargeIndecomposable.twoSidedEndomorphismSpan k mu := by
    rw [hmuSpan]
    exact Submodule.mem_top
  have hgmem : g ∈ LargeIndecomposable.twoSidedEndomorphismSpan k nu := by
    rw [hnuSpan]
    exact Submodule.mem_top
  have hmuNotC : ¬ LargeIndecomposable.AllowsCotransit mu := by
    intro hmuC
    apply hfNotC
    exact hmuC.of_mem_twoSidedEndomorphismSpan
      (fun a b ↦ end_mul_comm S X a b) hfmem
  have hnuNotT : ¬ LargeIndecomposable.AllowsTransit nu := by
    intro hnuT
    apply hgNotT
    exact hnuT.of_mem_twoSidedEndomorphismSpan
      (fun a b ↦ end_mul_comm S Z a b) hgmem
  have hmuT : LargeIndecomposable.AllowsTransit mu :=
    (LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := S.ProjectiveCategory) mu).resolve_right hmuNotC
  have hnuC : LargeIndecomposable.AllowsCotransit nu :=
    (LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := S.ProjectiveCategory) nu).resolve_left hnuNotT
  obtain ⟨b, hfb⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit hmuT hfmem
  obtain ⟨a, hga⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsCotransit hnuC hgmem
  rcases hsandwich with ⟨rho, hrho⟩
  constructor
  · by_contra hfspan
    have hbNotUnit : ¬ IsUnit b := by
      intro hb
      haveI : IsIso b.asHom :=
        (isUnit_iff_isIso b).1 hb
      have heq : LargeIndecomposable.UnitRayEquivalent mu f :=
        ⟨Iso.refl X, asIso b.asHom, by simpa using hfb⟩
      apply hfspan
      rw [← LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
        k heq, hmuSpan]
    have hbJ : b ∈ Ring.jacobson (End Y) :=
      (LargeIndecomposable.mem_ringJacobson_iff_not_isUnit (End Y) b).2
        hbNotUnit
    let q : End Y := End.of (b.asHom ≫ rho.1.asHom)
    have hqJ : q ∈ (Ring.jacobson (End Y)) ^ 2 := by
      change rho.1 * b ∈ (Ring.jacobson (End Y)) ^ 2
      rw [show (2 : ℕ) = 1 + 1 by omega,
        Ideal.IsTwoSided.pow_add, Submodule.pow_one]
      exact Ideal.mul_mem_mul rho.2 hbJ
    rcases roiterTransitSquareAlternative S hfinite mu g hmuNotC hgNotT with
      hleft | hright
    · apply hrho
      calc
        (f ≫ rho.1.asHom) ≫ g =
            ((mu ≫ b.asHom) ≫ rho.1.asHom) ≫ g := by rw [hfb]
        _ = (mu ≫ q.asHom) ≫ g := by
          simp only [q, Category.assoc]
        _ = 0 := by rw [hleft q hqJ]; simp
    · apply hrho
      calc
        (f ≫ rho.1.asHom) ≫ g =
            ((mu ≫ b.asHom) ≫ rho.1.asHom) ≫ g := by rw [hfb]
        _ = mu ≫ (q.asHom ≫ g) := by
          simp only [q, Category.assoc]
        _ = 0 := by rw [hright q hqJ]; simp
  · by_contra hgspan
    have haNotUnit : ¬ IsUnit a := by
      intro ha
      haveI : IsIso a.asHom :=
        (isUnit_iff_isIso a).1 ha
      have heq : LargeIndecomposable.UnitRayEquivalent nu g :=
        ⟨asIso a.asHom, Iso.refl Z, by simpa using hga⟩
      apply hgspan
      rw [← LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
        k heq, hnuSpan]
    have haJ : a ∈ Ring.jacobson (End Y) :=
      (LargeIndecomposable.mem_ringJacobson_iff_not_isUnit (End Y) a).2
        haNotUnit
    let q : End Y := End.of (rho.1.asHom ≫ a.asHom)
    have hqJ : q ∈ (Ring.jacobson (End Y)) ^ 2 := by
      change a * rho.1 ∈ (Ring.jacobson (End Y)) ^ 2
      rw [show (2 : ℕ) = 1 + 1 by omega,
        Ideal.IsTwoSided.pow_add, Submodule.pow_one]
      exact Ideal.mul_mem_mul haJ rho.2
    rcases roiterTransitSquareAlternative S hfinite f nu hfNotC hnuNotT with
      hleft | hright
    · apply hrho
      calc
        (f ≫ rho.1.asHom) ≫ g =
            (f ≫ rho.1.asHom) ≫ (a.asHom ≫ nu) := by rw [hga]
        _ = (f ≫ q.asHom) ≫ nu := by
          simp only [q, Category.assoc]
        _ = 0 := by rw [hleft q hqJ]; simp
    · apply hrho
      calc
        (f ≫ rho.1.asHom) ≫ g =
            (f ≫ rho.1.asHom) ≫ (a.asHom ≫ nu) := by rw [hga]
        _ = f ≫ (q.asHom ≫ nu) := by
          simp only [q, Category.assoc]
        _ = 0 := by rw [hright q hqJ]; simp

/-- The source's `P_i` zero-representative configuration therefore has full
outer Hom generators on both sides. -/
theorem zeroPairRadicalSandwich_full_outer_spans
    (hfinite : LargeIndecomposable.MildAlg k A)
    {X Y Z : S.ProjectiveCategory} {f : X ⟶ Y} {g : Y ⟶ Z}
    (D : LargeIndecomposable.BGRSZeroPairRadicalSandwich f g) :
    LargeIndecomposable.twoSidedEndomorphismSpan k D.left = ⊤ ∧
      LargeIndecomposable.twoSidedEndomorphismSpan k D.right = ⊤ :=
  full_outer_spans_of_nonzeroJacobsonSandwich S hfinite D.left D.right
    D.left_not_allowsCotransit D.right_not_allowsTransit D.nonzero_sandwich

/-- The class-valued form consumed by the existing rank-bound bridge. -/
theorem hasRoiterTransitSquareAlternative
    (hfinite : LargeIndecomposable.MildAlg k A) :
    LargeIndecomposable.HasRoiterTransitSquareAlternative
      k S.ProjectiveCategory where
  square_alternative f g hf hg :=
    roiterTransitSquareAlternative S hfinite f g hf hg

/-- Representation-finiteness now supplies the rank-one Roiter interface used
by critical-path propagation, with no remaining Figure-13 hypothesis. -/
theorem hasRoiterTransitRankBound
    (hfinite : LargeIndecomposable.MildAlg k A) :
    LargeIndecomposable.HasRoiterTransitRankBound
      k S.ProjectiveCategory :=
  LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.hasRoiterTransitRankBoundOfSquareAlternative
    S (fun f g hf hg ↦
      roiterTransitSquareAlternative S hfinite f g hf hg)

end LargeIndecomposable.RoiterFigure13EAmbient
