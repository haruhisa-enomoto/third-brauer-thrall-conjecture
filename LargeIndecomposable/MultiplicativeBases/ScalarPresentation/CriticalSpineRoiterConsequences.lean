module

public import LargeIndecomposable.RayCategories.Distributive.ProperQuotientCorners
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.RoiterTransitSquareAlternative
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalTransitPropagation
public import LargeIndecomposable.RayCategories.Distributive.BGRSRayArrowRadical

@[expose] public section

/-!
# Representation-finite Roiter consequences for a critical spine

This file removes the former Roiter typeclass premise from the critical-path
propagation results and records the full outer composites obtained in BGRS
4.3(a).
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.BGRSCriticalPathSpine

open LargeIndecomposable.RoiterFigure13EAmbient
open LargeIndecomposable.ClosedZigzagTransfer

universe u v x

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

variable [LargeIndecomposable.HasBGRSDistributiveHomStructure
  k S.ProjectiveCategory]

/-- At the initial critical cut, both the long suffix and the first arrow
generate their complete primitive-projective Hom spaces. -/
theorem initial_full_outer_spans
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    LargeIndecomposable.twoSidedEndomorphismSpan k
        (spine.lift.pathMap (spine.middle.comp spine.last.toPath)) = ⊤ ∧
      LargeIndecomposable.twoSidedEndomorphismSpan k
        (spine.lift.representative spine.first) = ⊤ := by
  obtain ⟨D⟩ := spine.initialZeroPairRadicalSandwich
  have hfull := zeroPairRadicalSandwich_full_outer_spans S hfinite D
  constructor
  · rw [LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
      k D.left_unitRayEquivalent]
    exact hfull.1
  · rw [LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
      k D.right_unitRayEquivalent]
    exact hfull.2

/-- At the terminal critical cut, both the last arrow and the long prefix
generate their complete primitive-projective Hom spaces. -/
theorem terminal_full_outer_spans
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    LargeIndecomposable.twoSidedEndomorphismSpan k
        (spine.lift.representative spine.last) = ⊤ ∧
      LargeIndecomposable.twoSidedEndomorphismSpan k
        (spine.lift.pathMap (spine.first.toPath.comp spine.middle)) = ⊤ := by
  obtain ⟨D⟩ := spine.terminalZeroPairRadicalSandwich
  have hfull := zeroPairRadicalSandwich_full_outer_spans S hfinite D
  constructor
  · rw [LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
      k D.left_unitRayEquivalent]
    exact hfull.1
  · rw [LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
      k D.right_unitRayEquivalent]
    exact hfull.2

/-- The two long outer composites denoted `delta alpha_n` and
`alpha_1 delta` in BGRS 4.3(a) are full Hom generators. -/
theorem long_outer_composites_full_spans
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    LargeIndecomposable.twoSidedEndomorphismSpan k
        (spine.lift.pathMap (spine.middle.comp spine.last.toPath)) = ⊤ ∧
      LargeIndecomposable.twoSidedEndomorphismSpan k
        (spine.lift.pathMap (spine.first.toPath.comp spine.middle)) = ⊤ :=
  ⟨(spine.initial_full_outer_spans S hfinite).1,
    (spine.terminal_full_outer_spans S hfinite).2⟩

/-- The middle composite `delta` of BGRS 4.3(a) itself generates its complete
primitive-projective Hom space.  Compare it with a full generator `mu`.
If `mu` allows transit, the full suffix forces the target coefficient to be
a unit; if it allows cotransit, the full prefix forces the source coefficient
to be a unit. -/
theorem middle_full_span
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    LargeIndecomposable.twoSidedEndomorphismSpan k
        (spine.lift.pathMap spine.middle) = ⊤ := by
  let delta := spine.lift.pathMap spine.middle
  obtain ⟨mu, hmuSpan⟩ :=
    exists_full_twoSidedEndomorphismSpan
      (k := k) (C := S.ProjectiveCategory)
      spine.rightInner.obj.as spine.leftInner.obj.as
  have hdeltaMem : delta ∈
      LargeIndecomposable.twoSidedEndomorphismSpan k mu := by
    rw [hmuSpan]
    exact Submodule.mem_top
  rcases
      LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
        (k := k) (C := S.ProjectiveCategory) mu with hmuT | hmuC
  · obtain ⟨b, hdelta⟩ :=
      LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit
        hmuT hdeltaMem
    have hsuffixFactor :
        spine.lift.pathMap (spine.middle.comp spine.last.toPath) =
          (spine.lift.representative spine.last ≫ mu) ≫ b.asHom := by
      rw [show spine.lift.pathMap
          (spine.middle.comp spine.last.toPath) =
            spine.lift.representative spine.last ≫ delta by
        simp only [delta, BGRSRayArrowLift.pathMap,
          LinearPathCategory.pathMap_comp, Quiver.Hom.toPath,
          LinearPathCategory.pathMap_cons,
          LinearPathCategory.pathMap_nil, Category.comp_id]]
      rw [hdelta]
      simp only [Category.assoc]
    have hbase : spine.lift.representative spine.last ≫ mu ≠ 0 := by
      intro hzero
      apply spine.lift_suffix_pathMap_ne_zero
      rw [hsuffixFactor, hzero]
      simp
    have hfactorFull :
        LargeIndecomposable.twoSidedEndomorphismSpan k
            ((spine.lift.representative spine.last ≫ mu) ≫ b.asHom) =
          ⊤ := by
      rw [← hsuffixFactor]
      exact (spine.long_outer_composites_full_spans S hfinite).1
    have hb : IsUnit b :=
      LargeIndecomposable.isUnit_of_twoSidedEndomorphismSpan_comp_right_eq_top
        (k := k) (C := S.ProjectiveCategory)
        (spine.lift.representative spine.last ≫ mu) b hbase hfactorFull
    haveI : IsIso b.asHom := (isUnit_iff_isIso b).1 hb
    have heq : LargeIndecomposable.UnitRayEquivalent mu delta :=
      ⟨Iso.refl _, asIso b.asHom, by simpa using hdelta⟩
    rw [← LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
      k heq, hmuSpan]
  · obtain ⟨a, hdelta⟩ :=
      LargeIndecomposable.exists_comp_of_mem_span_of_allowsCotransit
        hmuC hdeltaMem
    have hprefixFactor :
        spine.lift.pathMap (spine.first.toPath.comp spine.middle) =
          a.asHom ≫ (mu ≫ spine.lift.representative spine.first) := by
      rw [show spine.lift.pathMap
          (spine.first.toPath.comp spine.middle) =
            delta ≫ spine.lift.representative spine.first by
        simp only [delta, BGRSRayArrowLift.pathMap,
          LinearPathCategory.pathMap_comp, Quiver.Hom.toPath,
          LinearPathCategory.pathMap_cons,
          LinearPathCategory.pathMap_nil, Category.comp_id]]
      rw [hdelta]
      simp only [Category.assoc]
    have hbase : mu ≫ spine.lift.representative spine.first ≠ 0 := by
      intro hzero
      apply spine.lift_prefix_pathMap_ne_zero
      rw [hprefixFactor, hzero]
      simp
    have hfactorFull :
        LargeIndecomposable.twoSidedEndomorphismSpan k
            (a.asHom ≫
              (mu ≫ spine.lift.representative spine.first)) = ⊤ := by
      rw [← hprefixFactor]
      exact (spine.long_outer_composites_full_spans S hfinite).2
    have ha : IsUnit a :=
      LargeIndecomposable.isUnit_of_twoSidedEndomorphismSpan_comp_left_eq_top
        (k := k) (C := S.ProjectiveCategory) a
        (mu ≫ spine.lift.representative spine.first) hbase hfactorFull
    haveI : IsIso a.asHom := (isUnit_iff_isIso a).1 ha
    have heq : LargeIndecomposable.UnitRayEquivalent mu delta :=
      ⟨asIso a.asHom, Iso.refl _, by simpa using hdelta⟩
    rw [← LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
      k heq, hmuSpan]

/-- The middle composite `delta` does not factor through the terminal outer
vertex `a` of BGRS 4.3(a).  Such a factorization would make the full suffix a
left-endomorphism multiple through the last irreducible arrow.  Fullness
forces that endomorphism to be a unit, while the arrow makes it radical. -/
theorem middle_not_factors_through_terminal
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    ¬ ∃ (u : spine.rightInner.obj.as ⟶ j.obj.as)
        (v : j.obj.as ⟶ spine.leftInner.obj.as),
      spine.lift.pathMap spine.middle = u ≫ v := by
  rintro ⟨u, v, hdelta⟩
  let e : End j.obj.as :=
    End.of (spine.lift.representative spine.last ≫ u)
  have hsuffixFactor :
      spine.lift.pathMap (spine.middle.comp spine.last.toPath) =
        e.asHom ≫ v := by
    rw [show spine.lift.pathMap
        (spine.middle.comp spine.last.toPath) =
          spine.lift.representative spine.last ≫
            spine.lift.pathMap spine.middle by
      simp only [BGRSRayArrowLift.pathMap,
        LinearPathCategory.pathMap_comp, Quiver.Hom.toPath,
        LinearPathCategory.pathMap_cons,
        LinearPathCategory.pathMap_nil, Category.comp_id]]
    rw [hdelta]
    simp only [e, Category.assoc]
  have hv : v ≠ 0 := by
    intro hv
    apply spine.lift_suffix_pathMap_ne_zero
    rw [hsuffixFactor, hv]
    simp
  have hfull :
      LargeIndecomposable.twoSidedEndomorphismSpan k (e.asHom ≫ v) =
        ⊤ := by
    rw [← hsuffixFactor]
    exact (spine.long_outer_composites_full_spans S hfinite).1
  have heUnit : IsUnit e :=
    LargeIndecomposable.isUnit_of_twoSidedEndomorphismSpan_comp_left_eq_top
      (k := k) (C := S.ProjectiveCategory) e v hv hfull
  have heJac : e ∈ Ring.jacobson (End j.obj.as) := by
    rw [S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
    change (spine.lift.representative spine.last ≫ u).1 ∈
      Ring.jacobson A
    simp only [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val]
    exact (Ring.jacobson A).mul_mem_left u.1
      (S.rayArrowLift_representative_mem_jacobson spine.lift spine.last)
  exact ((LargeIndecomposable.mem_ringJacobson_iff_not_isUnit
    (End j.obj.as) e).1 heJac) heUnit

/-- The middle composite `delta` does not factor through the initial outer
vertex `b` of BGRS 4.3(a).  This is the source-end dual of
`middle_not_factors_through_terminal`. -/
theorem middle_not_factors_through_initial
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    ¬ ∃ (u : spine.rightInner.obj.as ⟶ i.obj.as)
        (v : i.obj.as ⟶ spine.leftInner.obj.as),
      spine.lift.pathMap spine.middle = u ≫ v := by
  rintro ⟨u, v, hdelta⟩
  let e : End i.obj.as :=
    End.of (v ≫ spine.lift.representative spine.first)
  have hprefixFactor :
      spine.lift.pathMap (spine.first.toPath.comp spine.middle) =
        u ≫ e.asHom := by
    rw [show spine.lift.pathMap
        (spine.first.toPath.comp spine.middle) =
          spine.lift.pathMap spine.middle ≫
            spine.lift.representative spine.first by
      simp only [BGRSRayArrowLift.pathMap,
        LinearPathCategory.pathMap_comp, Quiver.Hom.toPath,
        LinearPathCategory.pathMap_cons,
        LinearPathCategory.pathMap_nil, Category.comp_id]]
    rw [hdelta]
    simp only [e, Category.assoc]
  have hu : u ≠ 0 := by
    intro hu
    apply spine.lift_prefix_pathMap_ne_zero
    rw [hprefixFactor, hu]
    simp
  have hfull :
      LargeIndecomposable.twoSidedEndomorphismSpan k (u ≫ e.asHom) =
        ⊤ := by
    rw [← hprefixFactor]
    exact (spine.long_outer_composites_full_spans S hfinite).2
  have heUnit : IsUnit e :=
    LargeIndecomposable.isUnit_of_twoSidedEndomorphismSpan_comp_right_eq_top
      (k := k) (C := S.ProjectiveCategory) u e hu hfull
  have heJac : e ∈ Ring.jacobson (End i.obj.as) := by
    rw [S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
    change (v ≫ spine.lift.representative spine.first).1 ∈
      Ring.jacobson A
    simp only [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val]
    exact (Ring.jacobson A).mul_mem_right v.1
      (S.rayArrowLift_representative_mem_jacobson spine.lift spine.first)
  exact ((LargeIndecomposable.mem_ringJacobson_iff_not_isUnit
    (End i.obj.as) e).1 heJac) heUnit

/-- The complete middle composite `delta` allows both transit and cotransit.
Every arrow occurrence in the middle has the unconditional representation-
finite bitransit property, and both properties are preserved by composition. -/
theorem middle_allowsBitransit
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    LargeIndecomposable.AllowsTransit
        (spine.lift.pathMap spine.middle) ∧
      LargeIndecomposable.AllowsCotransit
        (spine.lift.pathMap spine.middle) := by
  letI : LargeIndecomposable.HasRoiterTransitRankBound
      k S.ProjectiveCategory := hasRoiterTransitRankBound S hfinite
  have pathBitransit : ∀
      {x y : LargeIndecomposable.RayVertex S.RayCategory}
      (q : Quiver.Path x y)
      (head : Quiver.Path spine.leftInner x)
      (tail : Quiver.Path y spine.rightInner),
      spine.middle = head.comp (q.comp tail) →
        LargeIndecomposable.AllowsTransit (spine.lift.pathMap q) ∧
          LargeIndecomposable.AllowsCotransit (spine.lift.pathMap q) := by
    intro x y q
    induction q with
    | nil =>
        intro head tail hmiddle
        constructor
        · intro a
          refine ⟨a, ?_⟩
          simp only [BGRSRayArrowLift.pathMap,
            LinearPathCategory.pathMap_nil, Category.comp_id,
            Category.id_comp]
        · intro b
          refine ⟨b, ?_⟩
          simp only [BGRSRayArrowLift.pathMap,
            LinearPathCategory.pathMap_nil, Category.comp_id,
            Category.id_comp]
    | @cons z y q next ih =>
        intro head tail hmiddle
        have htail :
            (q.cons next).comp tail =
              q.comp (next.toPath.comp tail) := by
          rw [show q.cons next = q.comp next.toPath by
            simp [Quiver.Hom.toPath]]
          exact Quiver.Path.comp_assoc _ _ _
        have hmiddlePrefix :
            spine.middle = head.comp
              (q.comp (next.toPath.comp tail)) := by
          simpa only [htail] using hmiddle
        have hq := ih head (next.toPath.comp tail) hmiddlePrefix
        have hmiddleNext :
            spine.middle = (head.comp q).comp
              (next.toPath.comp tail) := by
          rw [hmiddlePrefix]
          exact (Quiver.Path.comp_assoc _ _ _).symm
        have hnextOut :=
          spine.internalArrow_allowsBitransit
            (k := k) (head.comp q) next tail hmiddleNext
        have hnextEq : LargeIndecomposable.UnitRayEquivalent
            next.1.out (spine.lift.representative next) := by
          apply (LargeIndecomposable.unitRay_eq_iff _ _).1
          rw [LargeIndecomposable.unitRay_out,
            spine.lift.unitRay_representative]
        have hnext :
            LargeIndecomposable.AllowsTransit
                (spine.lift.representative next) ∧
              LargeIndecomposable.AllowsCotransit
                (spine.lift.representative next) :=
          ⟨hnextOut.1.of_unitRayEquivalent hnextEq,
            hnextOut.2.of_unitRayEquivalent hnextEq⟩
        simpa only [BGRSRayArrowLift.pathMap,
          LinearPathCategory.pathMap_cons] using
          ⟨hnext.1.comp hq.1, hnext.2.comp hq.2⟩
  simpa using pathBitransit spine.middle
    (Quiver.Path.nil) (Quiver.Path.nil) (by simp)

omit [IsAlgClosed k] in
/-- The endpoint sandwiches in a critical spine supply nonzero oriented
radical-power generators `sigma` at `c` and `rho` at `d`, as used in BGRS
4.3(b)--(c). -/
theorem nonempty_middle_radicalPowerParameters
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    Nonempty (LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
        (k := k) spine.leftInner.obj.as) ∧
      Nonempty (LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
        (k := k) spine.rightInner.obj.as) := by
  obtain ⟨sigma, -, hsigma⟩ := spine.exists_initial_radical_sandwich
  obtain ⟨rho, -, hrho⟩ := spine.exists_terminal_radical_sandwich
  have hsigma0 : sigma.1 ≠ 0 := by
    intro hzero
    apply hsigma
    have hzeroHom : sigma.1.asHom = 0 := congrArg End.asHom hzero
    rw [hzeroHom]
    simp
  have hrho0 : rho.1 ≠ 0 := by
    intro hzero
    apply hrho
    have hzeroHom : rho.1.asHom = 0 := congrArg End.asHom hzero
    rw [hzeroHom]
    simp
  exact ⟨
    LargeIndecomposable.ClosedZigzagTransfer.nonempty_orientedRadicalPowerParameter_of_nonzero_radical
      (k := k) (C := S.ProjectiveCategory) spine.leftInner.obj.as
      sigma.1 sigma.2 hsigma0,
    LargeIndecomposable.ClosedZigzagTransfer.nonempty_orientedRadicalPowerParameter_of_nonzero_radical
      (k := k) (C := S.ProjectiveCategory) spine.rightInner.obj.as
      rho.1 rho.2 hrho0⟩

/-- BGRS 4.3(b): if the chosen radical generator `sigma` at `c` factors as
`delta lambda` in the source convention (that is, `lambda ≫ delta` in the
reversed primitive-projective convention), then `lambda` generates the whole
reverse Hom space. -/
theorem reverse_full_span_of_sigma_eq_reverse_comp_middle
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    LargeIndecomposable.twoSidedEndomorphismSpan k lambda = ⊤ := by
  let delta := spine.lift.pathMap spine.middle
  obtain ⟨mu, hmuSpan⟩ :=
    exists_full_twoSidedEndomorphismSpan
      (k := k) (C := S.ProjectiveCategory)
      spine.leftInner.obj.as spine.rightInner.obj.as
  have hlambdaMem : lambda ∈
      LargeIndecomposable.twoSidedEndomorphismSpan k mu := by
    rw [hmuSpan]
    exact Submodule.mem_top
  have hdeltaJ : delta.1 ∈ Ring.jacobson A :=
    S.rayArrowLift_pathMap_mem_jacobson spine.lift spine.middle
      spine.middle_length_pos
  have hdeltaBitransit := spine.middle_allowsBitransit S hfinite
  rcases
      LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
        (k := k) (C := S.ProjectiveCategory) mu with hmuT | hmuC
  · obtain ⟨b, hlambda⟩ :=
      LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit
        hmuT hlambdaMem
    by_cases hb : IsUnit b
    · haveI : IsIso b.asHom := (isUnit_iff_isIso b).1 hb
      have heq : LargeIndecomposable.UnitRayEquivalent mu lambda :=
        ⟨Iso.refl _, asIso b.asHom, by simpa using hlambda⟩
      rw [← LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
        k heq, hmuSpan]
    · obtain ⟨c, hbc⟩ := hdeltaBitransit.1 b
      have hc : ¬ IsUnit c :=
        LargeIndecomposable.not_isUnit_right_of_transfer
          spine.lift_middle_pathMap_ne_zero b c hb hbc
      have hcJ : c ∈ Ring.jacobson (End spine.leftInner.obj.as) :=
        (LargeIndecomposable.mem_ringJacobson_iff_not_isUnit
          (End spine.leftInner.obj.as) c).2 hc
      let q : End spine.leftInner.obj.as := End.of (mu ≫ delta)
      have hqJ : q ∈ Ring.jacobson (End spine.leftInner.obj.as) := by
        rw [S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
        change (mu ≫ delta).1 ∈ Ring.jacobson A
        simp only [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val]
        exact (Ring.jacobson A).mul_mem_right mu.1 hdeltaJ
      have htauEq : P.tau = c * q := by
        apply End.ext
        calc
          P.tau.asHom = lambda ≫ delta := hfactor
          _ = (mu ≫ b.asHom) ≫ delta := by rw [hlambda]
          _ = mu ≫ (b.asHom ≫ delta) := Category.assoc _ _ _
          _ = mu ≫ (delta ≫ c.asHom) := by rw [hbc]
          _ = (c * q).asHom := by
            simp only [q, End.mul_def, Category.assoc]
      exfalso
      apply P.tau_not_mem_jacobson_sq
      rw [htauEq, show (2 : ℕ) = 1 + 1 by omega,
        Ideal.IsTwoSided.pow_add, Submodule.pow_one]
      exact Ideal.mul_mem_mul hcJ hqJ
  · obtain ⟨a, hlambda⟩ :=
      LargeIndecomposable.exists_comp_of_mem_span_of_allowsCotransit
        hmuC hlambdaMem
    by_cases ha : IsUnit a
    · haveI : IsIso a.asHom := (isUnit_iff_isIso a).1 ha
      have heq : LargeIndecomposable.UnitRayEquivalent mu lambda :=
        ⟨asIso a.asHom, Iso.refl _, by simpa using hlambda⟩
      rw [← LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
        k heq, hmuSpan]
    · have haJ : a ∈ Ring.jacobson (End spine.leftInner.obj.as) :=
        (LargeIndecomposable.mem_ringJacobson_iff_not_isUnit
          (End spine.leftInner.obj.as) a).2 ha
      let q : End spine.leftInner.obj.as := End.of (mu ≫ delta)
      have hqJ : q ∈ Ring.jacobson (End spine.leftInner.obj.as) := by
        rw [S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
        change (mu ≫ delta).1 ∈ Ring.jacobson A
        simp only [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val]
        exact (Ring.jacobson A).mul_mem_right mu.1 hdeltaJ
      have htauEq : P.tau = q * a := by
        apply End.ext
        calc
          P.tau.asHom = lambda ≫ delta := hfactor
          _ = (a.asHom ≫ mu) ≫ delta := by rw [hlambda]
          _ = (q * a).asHom := by
            simp only [q, End.mul_def, Category.assoc]
      exfalso
      apply P.tau_not_mem_jacobson_sq
      rw [htauEq, show (2 : ℕ) = 1 + 1 by omega,
        Ideal.IsTwoSided.pow_add, Submodule.pow_one]
      exact Ideal.mul_mem_mul hqJ haJ

/-- In the first branch of BGRS 4.3(b), the cycle `lambda delta` in the
primitive-projective convention is the chosen algebra generator of the
left-inner endomorphism ring. -/
theorem adjoin_reverse_comp_middle_eq_top
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    Algebra.adjoin k
        ({End.of (lambda ≫ spine.lift.pathMap spine.middle)} :
          Set (End spine.leftInner.obj.as)) = ⊤ := by
  letI : ∀ T : S.ProjectiveCategory, Module.Finite k (End T) := fun T ↦ by
    change Module.Finite k (T ⟶ T)
    infer_instance
  have hcycle : End.of (lambda ≫ spine.lift.pathMap spine.middle) =
      P.tau := by
    apply End.ext
    exact hfactor.symm
  simpa only [hcycle] using P.adjoin_eq_top

/-- The same cycle identity transfers the generator of the left-inner
endomorphism ring across `lambda`; hence `lambda` allows transit. -/
theorem reverse_allowsTransit_of_sigma_eq_reverse_comp_middle
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    LargeIndecomposable.AllowsTransit lambda := by
  letI : ∀ T : S.ProjectiveCategory, Module.Finite k (End T) := fun T ↦ by
    change Module.Finite k (T ⟶ T)
    infer_instance
  let theta : End spine.rightInner.obj.as :=
    End.of (spine.lift.pathMap spine.middle ≫ lambda)
  apply LargeIndecomposable.ClosedZigzagTransfer.allowsTransit_of_transfer_of_adjoin_eq_top
    lambda P.tau theta P.adjoin_eq_top
  calc
    P.tau.asHom ≫ lambda =
        (lambda ≫ spine.lift.pathMap spine.middle) ≫ lambda := by
      rw [hfactor]
    _ = lambda ≫ theta.asHom := by
      simp only [theta, Category.assoc]

omit [IsAlgClosed k] in
/-- The first outer irreducible arrow of a critical spine prohibits transit
in the primitive-projective orientation. -/
theorem first_not_allowsTransit
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    ¬LargeIndecomposable.AllowsTransit
      (spine.lift.representative spine.first) := by
  obtain ⟨D⟩ := spine.initialZeroPairRadicalSandwich
  intro hfirst
  exact D.right_not_allowsTransit
    (hfirst.of_unitRayEquivalent D.right_unitRayEquivalent)

omit [IsAlgClosed k] in
/-- The long suffix at the initial critical cut prohibits cotransit. -/
theorem suffix_not_allowsCotransit
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    ¬LargeIndecomposable.AllowsCotransit
      (spine.lift.pathMap (spine.middle.comp spine.last.toPath)) := by
  obtain ⟨D⟩ := spine.initialZeroPairRadicalSandwich
  intro hsuffix
  exact D.left_not_allowsCotransit
    (hsuffix.of_unitRayEquivalent D.left_unitRayEquivalent)

omit [IsAlgClosed k] in
/-- The last outer irreducible arrow of a critical spine prohibits cotransit
in the primitive-projective orientation. -/
theorem last_not_allowsCotransit
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    ¬LargeIndecomposable.AllowsCotransit
      (spine.lift.representative spine.last) := by
  obtain ⟨D⟩ := spine.terminalZeroPairRadicalSandwich
  intro hlast
  exact D.left_not_allowsCotransit
    (hlast.of_unitRayEquivalent D.left_unitRayEquivalent)

omit [IsAlgClosed k] in
/-- The long prefix at the terminal critical cut prohibits transit. -/
theorem prefix_not_allowsTransit
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    ¬LargeIndecomposable.AllowsTransit
      (spine.lift.pathMap (spine.first.toPath.comp spine.middle)) := by
  obtain ⟨D⟩ := spine.terminalZeroPairRadicalSandwich
  intro hprefix
  exact D.right_not_allowsTransit
    (hprefix.of_unitRayEquivalent D.right_unitRayEquivalent)

/-- Every oriented generator of the left-inner radical has a nonzero
initial endpoint sandwich.  Roiter's alternative kills the square of that
radical in the endpoint sandwich.  The special-zero witness is therefore in
the first radical layer, where any oriented parameter differs from it only by
a scalar modulo the radical square. -/
theorem initial_parameter_sandwich_ne_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as) :
    (spine.lift.pathMap (spine.middle.comp spine.last.toPath) ≫
        P.tau.asHom) ≫ spine.lift.representative spine.first ≠ 0 := by
  letI : ∀ T : S.ProjectiveCategory, Module.Finite k (End T) := fun T ↦ by
    change Module.Finite k (T ⟶ T)
    infer_instance
  let f := spine.lift.pathMap (spine.middle.comp spine.last.toPath)
  let g := spine.lift.representative spine.first
  obtain ⟨rho, -, hrho⟩ := spine.exists_initial_radical_sandwich
  have hsquare := roiterTransitSquareAlternative S hfinite f g
    (spine.suffix_not_allowsCotransit S)
    (spine.first_not_allowsTransit S)
  have hkill : ∀ a : End spine.leftInner.obj.as,
      a ∈ (Ring.jacobson (End spine.leftInner.obj.as)) ^ 2 →
        (f ≫ a.asHom) ≫ g = 0 := by
    intro a ha
    rcases hsquare with hleft | hright
    · rw [hleft a ha]
      simp
    · rw [Category.assoc, hright a ha]
      simp
  have hrhoNotSq : rho.1 ∉
      (Ring.jacobson (End spine.leftInner.obj.as)) ^ 2 := by
    intro hrhoSq
    apply hrho
    simpa only [f, g] using hkill rho.1 hrhoSq
  have hrho0 : rho.1 ≠ 0 := by
    intro hzero
    apply hrho
    have hzeroHom : rho.1.asHom = 0 := congrArg End.asHom hzero
    rw [hzeroHom]
    simp
  obtain ⟨n, hn, e, he, hrhoEq⟩ :=
    P.transitData.factors rho.1 rho.2 hrho0
  have hn1 : n = 1 := by
    by_contra hnOne
    have hn2 : 2 ≤ n := by omega
    have hpow : P.tau ^ n ∈
        (Ring.jacobson (End spine.leftInner.obj.as)) ^ 2 :=
      Ideal.pow_le_pow_right hn2
        (Ideal.pow_mem_pow P.mem_jacobson n)
    apply hrhoNotSq
    have hrhoRing : rho.1 = e * P.tau ^ n := by
      apply End.ext
      simpa only [End.mul_def] using hrhoEq
    rw [hrhoRing]
    exact (Ring.jacobson (End spine.leftInner.obj.as) ^ 2).mul_mem_left e hpow
  subst n
  by_contra htau
  let c : k := S.projectiveEndResidue spine.leftInner.obj.as e
  let r : End spine.leftInner.obj.as := e - c • (1 : End spine.leftInner.obj.as)
  have hrResidue : S.projectiveEndResidue spine.leftInner.obj.as r = 0 := by
    have hscalar : S.projectiveEndResidue spine.leftInner.obj.as
        (c • (1 : End spine.leftInner.obj.as)) = c := by
      exact (S.projectiveEndResidue spine.leftInner.obj.as).commutes c
    calc
      S.projectiveEndResidue spine.leftInner.obj.as r =
          S.projectiveEndResidue spine.leftInner.obj.as e -
            S.projectiveEndResidue spine.leftInner.obj.as
              (c • (1 : End spine.leftInner.obj.as)) := by
        exact map_sub (S.projectiveEndResidue spine.leftInner.obj.as) _ _
      _ = c - c := by rw [hscalar]
      _ = 0 := sub_self c
  have hrJ : r ∈ Ring.jacobson (End spine.leftInner.obj.as) := by
    rw [S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson,
      ← S.projectiveEndResidue_eq_zero_iff_val_mem_jacobson]
    exact hrResidue
  let q : End spine.leftInner.obj.as := r * P.tau
  have hqSq : q ∈ (Ring.jacobson (End spine.leftInner.obj.as)) ^ 2 := by
    change r * P.tau ∈ (Ring.jacobson (End spine.leftInner.obj.as)) ^ 2
    rw [show (2 : ℕ) = 1 + 1 by omega,
      Ideal.IsTwoSided.pow_add, Submodule.pow_one]
    exact Ideal.mul_mem_mul hrJ P.mem_jacobson
  have hqZero : (f ≫ q.asHom) ≫ g = 0 := hkill q hqSq
  have heDecomp : e.asHom = c • (𝟙 spine.leftInner.obj.as) + r.asHom := by
    change e = c • (1 : End spine.leftInner.obj.as) + r
    dsimp [r]
    module
  have hscalarComp :
      ((f ≫ P.tau.asHom) ≫ (c • (𝟙 spine.leftInner.obj.as))) ≫ g =
        c • ((f ≫ P.tau.asHom) ≫ g) := by
    simp only [Linear.comp_smul, Category.comp_id, Linear.smul_comp]
  apply hrho
  calc
    (spine.lift.pathMap (spine.middle.comp spine.last.toPath) ≫
          rho.1.asHom) ≫ spine.lift.representative spine.first =
        (f ≫ (P.tau.asHom ≫ e.asHom)) ≫ g := by
      rw [hrhoEq]
      simp only [pow_one, f, g]
    _ = (f ≫ P.tau.asHom) ≫
          (c • (𝟙 spine.leftInner.obj.as) + r.asHom) ≫ g := by
      rw [heDecomp]
      simp only [Category.assoc]
    _ = (((f ≫ P.tau.asHom) ≫ (c • (𝟙 spine.leftInner.obj.as))) ≫ g) +
          (((f ≫ P.tau.asHom) ≫ r.asHom) ≫ g) := by
      rw [← Category.assoc]
      rw [Preadditive.comp_add, Preadditive.add_comp]
    _ = c • ((f ≫ P.tau.asHom) ≫ g) +
          (f ≫ q.asHom) ≫ g := by
      rw [hscalarComp]
      simp only [q, End.mul_def, Category.assoc]
    _ = 0 := by rw [htau, hqZero, smul_zero, add_zero]

/-- Every oriented generator of the right-inner radical has a nonzero
terminal endpoint sandwich.  This is the terminal dual of
`initial_parameter_sandwich_ne_zero`. -/
theorem terminal_parameter_sandwich_ne_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (Q : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (spine.lift.representative spine.last ≫ Q.tau.asHom) ≫
        spine.lift.pathMap (spine.first.toPath.comp spine.middle) ≠ 0 := by
  letI : ∀ T : S.ProjectiveCategory, Module.Finite k (End T) := fun T ↦ by
    change Module.Finite k (T ⟶ T)
    infer_instance
  let f := spine.lift.representative spine.last
  let g := spine.lift.pathMap (spine.first.toPath.comp spine.middle)
  obtain ⟨rho, -, hrho⟩ := spine.exists_terminal_radical_sandwich
  have hsquare := roiterTransitSquareAlternative S hfinite f g
    (spine.last_not_allowsCotransit S)
    (spine.prefix_not_allowsTransit S)
  have hkill : ∀ a : End spine.rightInner.obj.as,
      a ∈ (Ring.jacobson (End spine.rightInner.obj.as)) ^ 2 →
        (f ≫ a.asHom) ≫ g = 0 := by
    intro a ha
    rcases hsquare with hleft | hright
    · rw [hleft a ha]
      simp
    · rw [Category.assoc, hright a ha]
      simp
  have hrhoNotSq : rho.1 ∉
      (Ring.jacobson (End spine.rightInner.obj.as)) ^ 2 := by
    intro hrhoSq
    apply hrho
    simpa only [f, g] using hkill rho.1 hrhoSq
  have hrho0 : rho.1 ≠ 0 := by
    intro hzero
    apply hrho
    have hzeroHom : rho.1.asHom = 0 := congrArg End.asHom hzero
    rw [hzeroHom]
    simp
  obtain ⟨n, hn, e, he, hrhoEq⟩ :=
    Q.transitData.factors rho.1 rho.2 hrho0
  have hn1 : n = 1 := by
    by_contra hnOne
    have hn2 : 2 ≤ n := by omega
    have hpow : Q.tau ^ n ∈
        (Ring.jacobson (End spine.rightInner.obj.as)) ^ 2 :=
      Ideal.pow_le_pow_right hn2
        (Ideal.pow_mem_pow Q.mem_jacobson n)
    apply hrhoNotSq
    have hrhoRing : rho.1 = e * Q.tau ^ n := by
      apply End.ext
      simpa only [End.mul_def] using hrhoEq
    rw [hrhoRing]
    exact (Ring.jacobson (End spine.rightInner.obj.as) ^ 2).mul_mem_left e hpow
  subst n
  by_contra htau
  let c : k := S.projectiveEndResidue spine.rightInner.obj.as e
  let r : End spine.rightInner.obj.as := e - c • (1 : End spine.rightInner.obj.as)
  have hrResidue : S.projectiveEndResidue spine.rightInner.obj.as r = 0 := by
    have hscalar : S.projectiveEndResidue spine.rightInner.obj.as
        (c • (1 : End spine.rightInner.obj.as)) = c := by
      exact (S.projectiveEndResidue spine.rightInner.obj.as).commutes c
    calc
      S.projectiveEndResidue spine.rightInner.obj.as r =
          S.projectiveEndResidue spine.rightInner.obj.as e -
            S.projectiveEndResidue spine.rightInner.obj.as
              (c • (1 : End spine.rightInner.obj.as)) := by
        exact map_sub (S.projectiveEndResidue spine.rightInner.obj.as) _ _
      _ = c - c := by rw [hscalar]
      _ = 0 := sub_self c
  have hrJ : r ∈ Ring.jacobson (End spine.rightInner.obj.as) := by
    rw [S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson,
      ← S.projectiveEndResidue_eq_zero_iff_val_mem_jacobson]
    exact hrResidue
  let q : End spine.rightInner.obj.as := r * Q.tau
  have hqSq : q ∈ (Ring.jacobson (End spine.rightInner.obj.as)) ^ 2 := by
    change r * Q.tau ∈ (Ring.jacobson (End spine.rightInner.obj.as)) ^ 2
    rw [show (2 : ℕ) = 1 + 1 by omega,
      Ideal.IsTwoSided.pow_add, Submodule.pow_one]
    exact Ideal.mul_mem_mul hrJ Q.mem_jacobson
  have hqZero : (f ≫ q.asHom) ≫ g = 0 := hkill q hqSq
  have heDecomp : e.asHom = c • (𝟙 spine.rightInner.obj.as) + r.asHom := by
    change e = c • (1 : End spine.rightInner.obj.as) + r
    dsimp [r]
    module
  have hscalarComp :
      ((f ≫ Q.tau.asHom) ≫ (c • (𝟙 spine.rightInner.obj.as))) ≫ g =
        c • ((f ≫ Q.tau.asHom) ≫ g) := by
    simp only [Linear.comp_smul, Category.comp_id, Linear.smul_comp]
  apply hrho
  calc
    (spine.lift.representative spine.last ≫ rho.1.asHom) ≫
          spine.lift.pathMap (spine.first.toPath.comp spine.middle) =
        (f ≫ (Q.tau.asHom ≫ e.asHom)) ≫ g := by
      rw [hrhoEq]
      simp only [pow_one, f, g]
    _ = (f ≫ Q.tau.asHom) ≫
          (c • (𝟙 spine.rightInner.obj.as) + r.asHom) ≫ g := by
      rw [heDecomp]
      simp only [Category.assoc]
    _ = (((f ≫ Q.tau.asHom) ≫ (c • (𝟙 spine.rightInner.obj.as))) ≫ g) +
          (((f ≫ Q.tau.asHom) ≫ r.asHom) ≫ g) := by
      rw [← Category.assoc]
      rw [Preadditive.comp_add, Preadditive.add_comp]
    _ = c • ((f ≫ Q.tau.asHom) ≫ g) +
          (f ≫ q.asHom) ≫ g := by
      rw [hscalarComp]
      simp only [q, End.mul_def, Category.assoc]
    _ = 0 := by rw [htau, hqZero, smul_zero, add_zero]

/-- In the factor branch `sigma = lambda delta`, the opposite cycle
`delta lambda` survives the first radical layer at the right-inner vertex.
If it belonged to the radical square, Roiter's terminal square alternative
would annihilate the nonzero initial sandwich of `sigma`. -/
theorem middle_comp_reverse_not_mem_jacobson_sq
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    End.of (spine.lift.pathMap spine.middle ≫ lambda) ∉
      (Ring.jacobson (End spine.rightInner.obj.as)) ^ 2 := by
  let delta := spine.lift.pathMap spine.middle
  let lastMap := spine.lift.representative spine.last
  let firstMap := spine.lift.representative spine.first
  let prefixMap := spine.lift.pathMap (spine.first.toPath.comp spine.middle)
  let theta : End spine.rightInner.obj.as := End.of (delta ≫ lambda)
  have hsquare := roiterTransitSquareAlternative S hfinite lastMap prefixMap
    (spine.last_not_allowsCotransit S)
    (spine.prefix_not_allowsTransit S)
  have hkill : ∀ a : End spine.rightInner.obj.as,
      a ∈ (Ring.jacobson (End spine.rightInner.obj.as)) ^ 2 →
        (lastMap ≫ a.asHom) ≫ prefixMap = 0 := by
    intro a ha
    rcases hsquare with hleft | hright
    · rw [hleft a ha]
      simp
    · rw [Category.assoc, hright a ha]
      simp
  intro hthetaSq
  have hthetaZero : (lastMap ≫ theta.asHom) ≫ prefixMap = 0 :=
    hkill theta hthetaSq
  have hsuffix :
      spine.lift.pathMap (spine.middle.comp spine.last.toPath) =
        lastMap ≫ delta := by
    simp only [lastMap, delta, BGRSRayArrowLift.pathMap,
      LinearPathCategory.pathMap_comp, Quiver.Hom.toPath,
      LinearPathCategory.pathMap_cons,
      LinearPathCategory.pathMap_nil, Category.comp_id]
  have hprefix : prefixMap = delta ≫ firstMap := by
    simp only [prefixMap, delta, firstMap, BGRSRayArrowLift.pathMap,
      LinearPathCategory.pathMap_comp, Quiver.Hom.toPath,
      LinearPathCategory.pathMap_cons,
      LinearPathCategory.pathMap_nil, Category.comp_id]
  apply spine.initial_parameter_sandwich_ne_zero S hfinite P
  calc
    (spine.lift.pathMap (spine.middle.comp spine.last.toPath) ≫
          P.tau.asHom) ≫ spine.lift.representative spine.first =
        ((lastMap ≫ delta) ≫ (lambda ≫ delta)) ≫ firstMap := by
      rw [hsuffix, hfactor]
    _ = (lastMap ≫ theta.asHom) ≫ prefixMap := by
      rw [hprefix]
      simp only [theta, Category.assoc]
    _ = 0 := hthetaZero

/-- The opposite cycle `delta lambda` generates the complete right-inner
endomorphism radical.  Its survival modulo the radical square forces exponent
one in the power normal form for any right-inner oriented parameter. -/
theorem middle_comp_reverse_span_eq_jacobson
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    LargeIndecomposable.twoSidedEndomorphismSpan k
        (End.of (spine.lift.pathMap spine.middle ≫ lambda)) =
      (Ring.jacobson (End spine.rightInner.obj.as)).restrictScalars k := by
  letI : ∀ T : S.ProjectiveCategory, Module.Finite k (End T) := fun T ↦ by
    change Module.Finite k (T ⟶ T)
    infer_instance
  let delta := spine.lift.pathMap spine.middle
  let theta : End spine.rightInner.obj.as := End.of (delta ≫ lambda)
  have hdeltaJ : delta.1 ∈ Ring.jacobson A :=
    S.rayArrowLift_pathMap_mem_jacobson spine.lift spine.middle
      spine.middle_length_pos
  have hthetaJ : theta ∈ Ring.jacobson (End spine.rightInner.obj.as) := by
    rw [S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
    change (delta ≫ lambda).1 ∈ Ring.jacobson A
    simp only [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val]
    exact (Ring.jacobson A).mul_mem_left lambda.1 hdeltaJ
  have hthetaNotSq : theta ∉
      (Ring.jacobson (End spine.rightInner.obj.as)) ^ 2 := by
    simpa only [theta, delta] using
      spine.middle_comp_reverse_not_mem_jacobson_sq S hfinite P lambda hfactor
  have htheta0 : theta ≠ 0 := by
    intro hzero
    apply hthetaNotSq
    rw [hzero]
    exact (Ring.jacobson (End spine.rightInner.obj.as) ^ 2).zero_mem
  let Q : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as :=
    Classical.choice (spine.nonempty_middle_radicalPowerParameters S).2
  obtain ⟨n, hn, e, he, hthetaEq⟩ :=
    Q.transitData.factors theta hthetaJ htheta0
  have hn1 : n = 1 := by
    by_contra hnOne
    have hn2 : 2 ≤ n := by omega
    have hpow : Q.tau ^ n ∈
        (Ring.jacobson (End spine.rightInner.obj.as)) ^ 2 :=
      Ideal.pow_le_pow_right hn2
        (Ideal.pow_mem_pow Q.mem_jacobson n)
    apply hthetaNotSq
    have hthetaRing : theta = e * Q.tau ^ n := by
      apply End.ext
      simpa only [End.mul_def] using hthetaEq
    rw [hthetaRing]
    exact (Ring.jacobson (End spine.rightInner.obj.as) ^ 2).mul_mem_left e hpow
  subst n
  haveI : IsIso e.asHom := (isUnit_iff_isIso e).1 he
  have heq : LargeIndecomposable.UnitRayEquivalent Q.tau.asHom theta.asHom :=
    ⟨Iso.refl _, asIso e.asHom, by
      change theta.asHom = (𝟙 spine.rightInner.obj.as) ≫
        Q.tau.asHom ≫ e.asHom
      rw [Category.id_comp]
      simpa only [pow_one] using hthetaEq⟩
  calc
    LargeIndecomposable.twoSidedEndomorphismSpan k
        (End.of (spine.lift.pathMap spine.middle ≫ lambda)) =
        LargeIndecomposable.twoSidedEndomorphismSpan k theta := by
      rfl
    _ = LargeIndecomposable.twoSidedEndomorphismSpan k Q.tau :=
      (LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
        k heq).symm
    _ = (Ring.jacobson (End spine.rightInner.obj.as)).restrictScalars k :=
      Q.span_eq

/-- Package the opposite cycle itself as the terminal oriented radical-power
parameter.  Its underlying endomorphism is definitionally
`delta ≫ lambda`. -/
def middleCompReverseRadicalPowerParameter
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as := by
  let theta : End spine.rightInner.obj.as :=
    End.of (spine.lift.pathMap spine.middle ≫ lambda)
  have hdeltaJ : (spine.lift.pathMap spine.middle).1 ∈ Ring.jacobson A :=
    S.rayArrowLift_pathMap_mem_jacobson spine.lift spine.middle
      spine.middle_length_pos
  have hthetaJ : theta ∈ Ring.jacobson (End spine.rightInner.obj.as) := by
    rw [S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
    change (spine.lift.pathMap spine.middle ≫ lambda).1 ∈ Ring.jacobson A
    simp only [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val]
    exact (Ring.jacobson A).mul_mem_left lambda.1 hdeltaJ
  have hthetaNotSq : theta ∉
      (Ring.jacobson (End spine.rightInner.obj.as)) ^ 2 := by
    exact spine.middle_comp_reverse_not_mem_jacobson_sq
      S hfinite P lambda hfactor
  have htheta0 : theta ≠ 0 := by
    intro hzero
    apply hthetaNotSq
    rw [hzero]
    exact (Ring.jacobson (End spine.rightInner.obj.as) ^ 2).zero_mem
  exact
    LargeIndecomposable.ClosedZigzagTransfer.orientedRadicalPowerParameter_of_span_eq
      theta hthetaJ htheta0
        (spine.middle_comp_reverse_span_eq_jacobson
          S hfinite P lambda hfactor)
        (LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
          (k := k) (C := S.ProjectiveCategory) theta)

@[simp]
theorem middleCompReverseRadicalPowerParameter_tau
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    (spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor).tau =
      End.of (spine.lift.pathMap spine.middle ≫ lambda) :=
  rfl

/-- In the terminal factor branch `rho = delta lambda`, the opposite cycle
`lambda delta` survives the first radical layer at the left-inner vertex. -/
theorem reverse_comp_middle_not_mem_jacobson_sq
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (Q : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : Q.tau.asHom =
      spine.lift.pathMap spine.middle ≫ lambda) :
    End.of (lambda ≫ spine.lift.pathMap spine.middle) ∉
      (Ring.jacobson (End spine.leftInner.obj.as)) ^ 2 := by
  let delta := spine.lift.pathMap spine.middle
  let lastMap := spine.lift.representative spine.last
  let firstMap := spine.lift.representative spine.first
  let suffixMap := spine.lift.pathMap (spine.middle.comp spine.last.toPath)
  let prefixMap := spine.lift.pathMap (spine.first.toPath.comp spine.middle)
  let theta : End spine.leftInner.obj.as := End.of (lambda ≫ delta)
  have hsquare := roiterTransitSquareAlternative S hfinite suffixMap firstMap
    (spine.suffix_not_allowsCotransit S)
    (spine.first_not_allowsTransit S)
  have hkill : ∀ a : End spine.leftInner.obj.as,
      a ∈ (Ring.jacobson (End spine.leftInner.obj.as)) ^ 2 →
        (suffixMap ≫ a.asHom) ≫ firstMap = 0 := by
    intro a ha
    rcases hsquare with hleft | hright
    · rw [hleft a ha]
      simp
    · rw [Category.assoc, hright a ha]
      simp
  intro hthetaSq
  have hthetaZero : (suffixMap ≫ theta.asHom) ≫ firstMap = 0 :=
    hkill theta hthetaSq
  have hsuffix : suffixMap = lastMap ≫ delta := by
    simp only [suffixMap, lastMap, delta, BGRSRayArrowLift.pathMap,
      LinearPathCategory.pathMap_comp, Quiver.Hom.toPath,
      LinearPathCategory.pathMap_cons, LinearPathCategory.pathMap_nil,
      Category.comp_id]
  have hprefix : prefixMap = delta ≫ firstMap := by
    simp only [prefixMap, delta, firstMap, BGRSRayArrowLift.pathMap,
      LinearPathCategory.pathMap_comp, Quiver.Hom.toPath,
      LinearPathCategory.pathMap_cons, LinearPathCategory.pathMap_nil,
      Category.comp_id]
  apply spine.terminal_parameter_sandwich_ne_zero S hfinite Q
  change (lastMap ≫ Q.tau.asHom) ≫ prefixMap = 0
  calc
    (lastMap ≫ Q.tau.asHom) ≫ prefixMap =
        (lastMap ≫ (delta ≫ lambda)) ≫ (delta ≫ firstMap) := by
      rw [hfactor, hprefix]
    _ = (suffixMap ≫ theta.asHom) ≫ firstMap := by
      rw [hsuffix]
      simp only [theta, Category.assoc]
    _ = 0 := hthetaZero

/-- The terminal factor branch's opposite cycle `lambda delta` generates the
complete left-inner endomorphism radical. -/
theorem reverse_comp_middle_span_eq_jacobson
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (Q : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : Q.tau.asHom =
      spine.lift.pathMap spine.middle ≫ lambda) :
    LargeIndecomposable.twoSidedEndomorphismSpan k
        (End.of (lambda ≫ spine.lift.pathMap spine.middle)) =
      (Ring.jacobson (End spine.leftInner.obj.as)).restrictScalars k := by
  letI : ∀ T : S.ProjectiveCategory, Module.Finite k (End T) := fun T ↦ by
    change Module.Finite k (T ⟶ T)
    infer_instance
  let delta := spine.lift.pathMap spine.middle
  let theta : End spine.leftInner.obj.as := End.of (lambda ≫ delta)
  have hdeltaJ : delta.1 ∈ Ring.jacobson A :=
    S.rayArrowLift_pathMap_mem_jacobson spine.lift spine.middle
      spine.middle_length_pos
  have hthetaJ : theta ∈ Ring.jacobson (End spine.leftInner.obj.as) := by
    rw [S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
    change (lambda ≫ delta).1 ∈ Ring.jacobson A
    simp only [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val]
    exact (Ring.jacobson A).mul_mem_right lambda.1 hdeltaJ
  have hthetaNotSq : theta ∉
      (Ring.jacobson (End spine.leftInner.obj.as)) ^ 2 := by
    simpa only [theta, delta] using
      spine.reverse_comp_middle_not_mem_jacobson_sq
        S hfinite Q lambda hfactor
  have htheta0 : theta ≠ 0 := by
    intro hzero
    apply hthetaNotSq
    rw [hzero]
    exact (Ring.jacobson (End spine.leftInner.obj.as) ^ 2).zero_mem
  let P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as :=
    Classical.choice (spine.nonempty_middle_radicalPowerParameters S).1
  obtain ⟨n, hn, e, he, hthetaEq⟩ :=
    P.transitData.factors theta hthetaJ htheta0
  have hn1 : n = 1 := by
    by_contra hnOne
    have hn2 : 2 ≤ n := by omega
    have hpow : P.tau ^ n ∈
        (Ring.jacobson (End spine.leftInner.obj.as)) ^ 2 :=
      Ideal.pow_le_pow_right hn2
        (Ideal.pow_mem_pow P.mem_jacobson n)
    apply hthetaNotSq
    have hthetaRing : theta = e * P.tau ^ n := by
      apply End.ext
      simpa only [End.mul_def] using hthetaEq
    rw [hthetaRing]
    exact (Ring.jacobson (End spine.leftInner.obj.as) ^ 2).mul_mem_left e hpow
  subst n
  haveI : IsIso e.asHom := (isUnit_iff_isIso e).1 he
  have heq : LargeIndecomposable.UnitRayEquivalent P.tau.asHom theta.asHom :=
    ⟨Iso.refl _, asIso e.asHom, by
      change theta.asHom = (𝟙 spine.leftInner.obj.as) ≫
        P.tau.asHom ≫ e.asHom
      rw [Category.id_comp]
      simpa only [pow_one] using hthetaEq⟩
  calc
    LargeIndecomposable.twoSidedEndomorphismSpan k
        (End.of (lambda ≫ spine.lift.pathMap spine.middle)) =
        LargeIndecomposable.twoSidedEndomorphismSpan k theta := by
      rfl
    _ = LargeIndecomposable.twoSidedEndomorphismSpan k P.tau :=
      (LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
        k heq).symm
    _ = (Ring.jacobson (End spine.leftInner.obj.as)).restrictScalars k :=
      P.span_eq

/-- Package the terminal factor branch's opposite cycle as the left-inner
oriented radical-power parameter. -/
def reverseCompMiddleRadicalPowerParameter
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (Q : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : Q.tau.asHom =
      spine.lift.pathMap spine.middle ≫ lambda) :
    LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as := by
  let theta : End spine.leftInner.obj.as :=
    End.of (lambda ≫ spine.lift.pathMap spine.middle)
  have hdeltaJ : (spine.lift.pathMap spine.middle).1 ∈ Ring.jacobson A :=
    S.rayArrowLift_pathMap_mem_jacobson spine.lift spine.middle
      spine.middle_length_pos
  have hthetaJ : theta ∈ Ring.jacobson (End spine.leftInner.obj.as) := by
    rw [S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
    change (lambda ≫ spine.lift.pathMap spine.middle).1 ∈ Ring.jacobson A
    simp only [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val]
    exact (Ring.jacobson A).mul_mem_right lambda.1 hdeltaJ
  have hthetaNotSq : theta ∉
      (Ring.jacobson (End spine.leftInner.obj.as)) ^ 2 := by
    exact spine.reverse_comp_middle_not_mem_jacobson_sq
      S hfinite Q lambda hfactor
  have htheta0 : theta ≠ 0 := by
    intro hzero
    apply hthetaNotSq
    rw [hzero]
    exact (Ring.jacobson (End spine.leftInner.obj.as) ^ 2).zero_mem
  exact
    LargeIndecomposable.ClosedZigzagTransfer.orientedRadicalPowerParameter_of_span_eq
      theta hthetaJ htheta0
        (spine.reverse_comp_middle_span_eq_jacobson
          S hfinite Q lambda hfactor)
        (LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
          (k := k) (C := S.ProjectiveCategory) theta)

@[simp]
theorem reverseCompMiddleRadicalPowerParameter_tau
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (Q : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : Q.tau.asHom =
      spine.lift.pathMap spine.middle ≫ lambda) :
    (spine.reverseCompMiddleRadicalPowerParameter
      S hfinite Q lambda hfactor).tau =
        End.of (lambda ≫ spine.lift.pathMap spine.middle) :=
  rfl

/-- Hence the opposite cycle is an algebra generator of the right-inner
endomorphism ring.  This discharges the hypothesis in the terminal outer
factor-exclusion theorem. -/
theorem adjoin_middle_comp_reverse_eq_top_of_sigma_eq_reverse_comp_middle
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    Algebra.adjoin k
        ({End.of (spine.lift.pathMap spine.middle ≫ lambda)} :
          Set (End spine.rightInner.obj.as)) = ⊤ := by
  letI : ∀ T : S.ProjectiveCategory, Module.Finite k (End T) := fun T ↦ by
    change Module.Finite k (T ⟶ T)
    infer_instance
  let delta := spine.lift.pathMap spine.middle
  let theta : End spine.rightInner.obj.as := End.of (delta ≫ lambda)
  have hdeltaJ : delta.1 ∈ Ring.jacobson A :=
    S.rayArrowLift_pathMap_mem_jacobson spine.lift spine.middle
      spine.middle_length_pos
  have hthetaJ : theta ∈ Ring.jacobson (End spine.rightInner.obj.as) := by
    rw [S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
    change (delta ≫ lambda).1 ∈ Ring.jacobson A
    simp only [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val]
    exact (Ring.jacobson A).mul_mem_left lambda.1 hdeltaJ
  have hthetaNotSq : theta ∉
      (Ring.jacobson (End spine.rightInner.obj.as)) ^ 2 := by
    simpa only [theta, delta] using
      spine.middle_comp_reverse_not_mem_jacobson_sq S hfinite P lambda hfactor
  have htheta0 : theta ≠ 0 := by
    intro hzero
    apply hthetaNotSq
    rw [hzero]
    exact (Ring.jacobson (End spine.rightInner.obj.as) ^ 2).zero_mem
  have hthetaSpan : LargeIndecomposable.twoSidedEndomorphismSpan k theta =
      (Ring.jacobson (End spine.rightInner.obj.as)).restrictScalars k := by
    change LargeIndecomposable.twoSidedEndomorphismSpan k
        (End.of (spine.lift.pathMap spine.middle ≫ lambda)) =
      (Ring.jacobson (End spine.rightInner.obj.as)).restrictScalars k
    exact spine.middle_comp_reverse_span_eq_jacobson
      S hfinite P lambda hfactor
  let Q : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as :=
    LargeIndecomposable.ClosedZigzagTransfer.orientedRadicalPowerParameter_of_span_eq
      theta hthetaJ htheta0 hthetaSpan
        (LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
          (k := k) (C := S.ProjectiveCategory) theta)
  have hQtau : Q.tau = theta := rfl
  change Algebra.adjoin k ({theta} : Set (End spine.rightInner.obj.as)) = ⊤
  simpa only [hQtau] using Q.adjoin_eq_top

/-- In the first branch of BGRS 4.3(b), `lambda` cannot factor through the
initial outer vertex `b`.  Such a factorization transfers the algebra
generator `sigma = lambda delta` across the first arrow and contradicts its
prohibited transit direction. -/
theorem reverse_not_factors_through_initial_of_sigma_eq_reverse_comp_middle
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    ¬ ∃ v : i.obj.as ⟶ spine.rightInner.obj.as,
      lambda = spine.lift.representative spine.first ≫ v := by
  letI : ∀ T : S.ProjectiveCategory, Module.Finite k (End T) := fun T ↦ by
    change Module.Finite k (T ⟶ T)
    infer_instance
  rintro ⟨v, hlambda⟩
  apply spine.first_not_allowsTransit S
  let b : End i.obj.as := End.of
    (v ≫ spine.lift.pathMap spine.middle ≫
      spine.lift.representative spine.first)
  apply LargeIndecomposable.ClosedZigzagTransfer.allowsTransit_of_transfer_of_adjoin_eq_top
    (spine.lift.representative spine.first) P.tau b P.adjoin_eq_top
  calc
    P.tau.asHom ≫ spine.lift.representative spine.first =
        (lambda ≫ spine.lift.pathMap spine.middle) ≫
          spine.lift.representative spine.first := by rw [hfactor]
    _ = spine.lift.representative spine.first ≫ b.asHom := by
      rw [hlambda]
      simp only [b, Category.assoc]

omit [IsAlgClosed k] in
/-- Once the opposite cycle `delta lambda` is known to generate the
right-inner endomorphism algebra, `lambda` cannot factor through the terminal
outer vertex `a`.  This is the exact source-dual transfer argument. -/
theorem reverse_not_factors_through_terminal_of_adjoin_middle_comp_reverse_eq_top
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hgen : Algebra.adjoin k
        ({End.of (spine.lift.pathMap spine.middle ≫ lambda)} :
          Set (End spine.rightInner.obj.as)) = ⊤) :
    ¬ ∃ u : spine.leftInner.obj.as ⟶ j.obj.as,
      lambda = u ≫ spine.lift.representative spine.last := by
  rintro ⟨u, hlambda⟩
  apply spine.last_not_allowsCotransit S
  let theta : End spine.rightInner.obj.as :=
    End.of (spine.lift.pathMap spine.middle ≫ lambda)
  let a : End j.obj.as := End.of
    (spine.lift.representative spine.last ≫
      spine.lift.pathMap spine.middle ≫ u)
  apply LargeIndecomposable.ClosedZigzagTransfer.allowsCotransit_of_transfer_of_adjoin_eq_top
    (spine.lift.representative spine.last) a theta hgen
  calc
    a.asHom ≫ spine.lift.representative spine.last =
        spine.lift.representative spine.last ≫
          spine.lift.pathMap spine.middle ≫
            (u ≫ spine.lift.representative spine.last) := by
      simp only [a, Category.assoc]
    _ = spine.lift.representative spine.last ≫ theta.asHom := by
      rw [← hlambda]

/-- The terminal outer exclusion in the first branch of BGRS 4.3(b), now
with its opposite-cycle generation hypothesis discharged. -/
theorem reverse_not_factors_through_terminal_of_sigma_eq_reverse_comp_middle
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    ¬ ∃ u : spine.leftInner.obj.as ⟶ j.obj.as,
      lambda = u ≫ spine.lift.representative spine.last := by
  apply spine.reverse_not_factors_through_terminal_of_adjoin_middle_comp_reverse_eq_top
    S lambda
  exact spine.adjoin_middle_comp_reverse_eq_top_of_sigma_eq_reverse_comp_middle
    S hfinite P lambda hfactor

/-- Thus the reverse Hom generator in the first factor branch avoids both
outer vertices, exactly as required before the Figure 14/15 case split. -/
theorem reverse_not_factors_through_outer_vertices_of_sigma_eq_reverse_comp_middle
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    (¬ ∃ v : i.obj.as ⟶ spine.rightInner.obj.as,
        lambda = spine.lift.representative spine.first ≫ v) ∧
      (¬ ∃ u : spine.leftInner.obj.as ⟶ j.obj.as,
        lambda = u ≫ spine.lift.representative spine.last) :=
  ⟨spine.reverse_not_factors_through_initial_of_sigma_eq_reverse_comp_middle
      S P lambda hfactor,
    spine.reverse_not_factors_through_terminal_of_sigma_eq_reverse_comp_middle
      S hfinite P lambda hfactor⟩

/-- The initial parameter composite cannot be absorbed across the first
outer arrow.  Such an absorption would transfer the algebra generator and
make that arrow allow transit.  This is the projective-opposite form of the
first nonmembership printed in BGRS 4.3(c). -/
theorem initial_parameter_comp_first_not_transfers
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as) :
    ¬ ∃ b : End i.obj.as,
      P.tau.asHom ≫ spine.lift.representative spine.first =
        spine.lift.representative spine.first ≫ b.asHom := by
  letI : ∀ T : S.ProjectiveCategory, Module.Finite k (End T) := fun T ↦ by
    change Module.Finite k (T ⟶ T)
    infer_instance
  rintro ⟨b, hb⟩
  apply spine.first_not_allowsTransit S
  exact
    LargeIndecomposable.ClosedZigzagTransfer.allowsTransit_of_transfer_of_adjoin_eq_top
      (spine.lift.representative spine.first) P.tau b P.adjoin_eq_top hb

/-- Dually, the last arrow cannot absorb the terminal parameter from its
target side.  This is the second outer nonmembership used in the Figure-14
and Figure-15 supplement calculations. -/
theorem last_comp_terminal_parameter_not_transfers
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (Q : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    ¬ ∃ a : End j.obj.as,
      a.asHom ≫ spine.lift.representative spine.last =
        spine.lift.representative spine.last ≫ Q.tau.asHom := by
  letI : ∀ T : S.ProjectiveCategory, Module.Finite k (End T) := fun T ↦ by
    change Module.Finite k (T ⟶ T)
    infer_instance
  rintro ⟨a, ha⟩
  apply spine.last_not_allowsCotransit S
  exact
    LargeIndecomposable.ClosedZigzagTransfer.allowsCotransit_of_transfer_of_adjoin_eq_top
      (spine.lift.representative spine.last) a Q.tau Q.adjoin_eq_top ha

/-- Under representation-finiteness, every split of the middle of a critical
spine carries the source's zero-representative radical-sandwich cut. -/
theorem zeroRepresentativeCut_at_middle_split_of_representationFinite
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    {y : LargeIndecomposable.RayVertex S.RayCategory}
    (midLeft : Quiver.Path spine.leftInner y)
    (midRight : Quiver.Path y spine.rightInner)
    (hmiddle : spine.middle = midLeft.comp midRight) :
    Nonempty (LargeIndecomposable.BGRSZeroRepresentativeCut
      (spine.first.toPath.comp midLeft)
      (midRight.comp spine.last.toPath)) := by
  letI : LargeIndecomposable.HasRoiterTransitRankBound
      k S.ProjectiveCategory := hasRoiterTransitRankBound S hfinite
  exact spine.zeroRepresentativeCut_at_middle_split
    (k := k) midLeft midRight hmiddle

/-- Under representation-finiteness, every arrow strictly inside a critical
path allows both transit and cotransit. -/
theorem internalArrow_allowsBitransit_of_representationFinite
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    {y z : LargeIndecomposable.RayVertex S.RayCategory}
    (head : Quiver.Path spine.leftInner y) (a : y ⟶ z)
    (tail : Quiver.Path z spine.rightInner)
    (hmiddle : spine.middle = head.comp (a.toPath.comp tail)) :
    LargeIndecomposable.AllowsTransit a.1.out ∧
      LargeIndecomposable.AllowsCotransit a.1.out := by
  letI : LargeIndecomposable.HasRoiterTransitRankBound
      k S.ProjectiveCategory := hasRoiterTransitRankBound S hfinite
  exact spine.internalArrow_allowsBitransit
    (k := k) head a tail hmiddle

end LargeIndecomposable.BGRSCriticalPathSpine
