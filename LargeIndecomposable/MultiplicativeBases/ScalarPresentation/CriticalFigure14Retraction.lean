module

public import LargeIndecomposable.RayCategories.Distributive.ProperQuotientCorners
public import LargeIndecomposable.Cleaving.ClosedChains.Figure14CoefficientCompiler
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalFigure14Quotient

@[expose] public section

/-!
# The exact Figure-14 quotient retraction

This file specializes the coherent Figure-14 coefficient compiler to the
source-exact selected-corner quotient constructed in
`CriticalFigure14Quotient`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.CriticalFigure14Quotient

open LargeIndecomposable.ClosedZigzagTransfer
open LargeIndecomposable.SplitBasicIdempotents
open LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory
open LargeIndecomposable.SplitBasicIdempotents.SelectedCorner

universe u v x

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

variable [LargeIndecomposable.HasBGRSDistributiveHomStructure
  k S.ProjectiveCategory]

omit [IsAlgClosed k]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure
      k S.ProjectiveCategory] in
private theorem projectiveFunctor_obj_finsetProjectiveObj_eq
    (t : Finset ι) (X : S.ProjectiveCategory)
    (hX : S.projectiveVertex X ∈ t) :
    (LargeIndecomposable.SplitBasicIdempotents.SelectedCorner.projectiveFunctor
      S (finsetPrimitiveEmbedding t)).obj
        (finsetProjectiveObj S t X hX) = X := by
  apply S.projectiveVertexEquiv.injective
  simp

omit [IsAlgClosed k] [Module.Finite k A]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure
      k S.ProjectiveCategory] in
@[simp]
private theorem projectiveEqToHom_val
    {X Y : S.ProjectiveCategory} (h : X = Y) :
    (eqToHom h : X ⟶ Y).1 =
      S.idempotent (S.projectiveVertex X) := by
  subst Y
  rfl

omit [IsAlgClosed k]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure
      k S.ProjectiveCategory] in
private theorem homCongr_finsetAmbientHom
    (t : Finset ι) {X Y : S.ProjectiveCategory}
    (hX : S.projectiveVertex X ∈ t)
    (hY : S.projectiveVertex Y ∈ t) (f : X ⟶ Y) :
    let eX := eqToIso
      (projectiveFunctor_obj_finsetProjectiveObj_eq S t X hX)
    let eY := eqToIso
      (projectiveFunctor_obj_finsetProjectiveObj_eq S t Y hY)
    CategoryTheory.Linear.homCongr k eX eY
      (finsetAmbientHom S t hX hY f) = f := by
  dsimp only
  apply Subtype.ext
  simp [CategoryTheory.Linear.homCongr_apply,
    ProjectiveCategory.idempotent_mul_val,
    ProjectiveCategory.val_mul_idempotent]

omit [IsAlgClosed k]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure
      k S.ProjectiveCategory] in
private theorem homCongr_projectiveFunctorMap_val
    (t : Finset ι) {X Y : S.ProjectiveCategory}
    (hX : S.projectiveVertex X ∈ t)
    (hY : S.projectiveVertex Y ∈ t)
    (f : finsetProjectiveObj S t X hX ⟶
      finsetProjectiveObj S t Y hY) :
    let E := LargeIndecomposable.SplitBasicIdempotents.SelectedCorner.projectiveFunctor
      S (finsetPrimitiveEmbedding t)
    let eX := eqToIso
      (projectiveFunctor_obj_finsetProjectiveObj_eq S t X hX)
    let eY := eqToIso
      (projectiveFunctor_obj_finsetProjectiveObj_eq S t Y hY)
    (CategoryTheory.Linear.homCongr k eX eY (E.map f)).1 = f.1.1 := by
  dsimp only
  simp [CategoryTheory.Linear.homCongr_apply]
  let E := LargeIndecomposable.SplitBasicIdempotents.SelectedCorner.projectiveFunctor
    S (finsetPrimitiveEmbedding t)
  have hleft : S.idempotent (S.projectiveVertex Y) * (E.map f).1 =
      (E.map f).1 := by
    simpa [E] using ProjectiveCategory.idempotent_mul_val S (E.map f)
  have hright : (E.map f).1 * S.idempotent (S.projectiveVertex X) =
      (E.map f).1 := by
    simpa [E] using ProjectiveCategory.val_mul_idempotent S (E.map f)
  change S.idempotent (S.projectiveVertex Y) * (E.map f).1 *
      S.idempotent (S.projectiveVertex X) = (E.map f).1
  rw [hleft, hright]

omit [IsAlgClosed k]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure
      k S.ProjectiveCategory] in
theorem finsetProjectiveHom_allowsTransit
    (t : Finset ι) {X Y : S.ProjectiveCategory}
    (hX : S.projectiveVertex X ∈ t)
    (hY : S.projectiveVertex Y ∈ t) (f : X ⟶ Y)
    (hf : LargeIndecomposable.AllowsTransit f) :
    LargeIndecomposable.AllowsTransit
      (finsetProjectiveHom S t hX hY f) := by
  let E := LargeIndecomposable.SplitBasicIdempotents.SelectedCorner.projectiveFunctor
    S (finsetPrimitiveEmbedding t)
  apply LargeIndecomposable.fullyFaithfulLinearFunctor_reflects_allowsTransit
    (k := k)
    E (finsetProjectiveHom S t hX hY f)
  let eX := eqToIso (projectiveFunctor_obj_finsetProjectiveObj_eq S t X hX)
  let eY := eqToIso (projectiveFunctor_obj_finsetProjectiveObj_eq S t Y hY)
  apply (LargeIndecomposable.homCongr_allowsTransit_iff
    (k := k) eX eY (E.map (finsetProjectiveHom S t hX hY f))).1
  have hmap : CategoryTheory.Linear.homCongr k eX eY
      (E.map (finsetProjectiveHom S t hX hY f)) = f := by
    simpa [eX, eY, E] using
      (homCongr_finsetAmbientHom (k := k) S t hX hY f)
  rw [hmap]
  exact hf

omit [IsAlgClosed k]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure
      k S.ProjectiveCategory] in
theorem finsetProjectiveHom_allowsCotransit
    (t : Finset ι) {X Y : S.ProjectiveCategory}
    (hX : S.projectiveVertex X ∈ t)
    (hY : S.projectiveVertex Y ∈ t) (f : X ⟶ Y)
    (hf : LargeIndecomposable.AllowsCotransit f) :
    LargeIndecomposable.AllowsCotransit
      (finsetProjectiveHom S t hX hY f) := by
  let E := LargeIndecomposable.SplitBasicIdempotents.SelectedCorner.projectiveFunctor
    S (finsetPrimitiveEmbedding t)
  apply LargeIndecomposable.fullyFaithfulLinearFunctor_reflects_allowsCotransit
    (k := k)
    E (finsetProjectiveHom S t hX hY f)
  let eX := eqToIso (projectiveFunctor_obj_finsetProjectiveObj_eq S t X hX)
  let eY := eqToIso (projectiveFunctor_obj_finsetProjectiveObj_eq S t Y hY)
  apply (LargeIndecomposable.homCongr_allowsCotransit_iff
    (k := k) eX eY (E.map (finsetProjectiveHom S t hX hY f))).1
  have hmap : CategoryTheory.Linear.homCongr k eX eY
      (E.map (finsetProjectiveHom S t hX hY f)) = f := by
    simpa [eX, eY, E] using
      (homCongr_finsetAmbientHom (k := k) S t hX hY f)
  rw [hmap]
  exact hf

omit [IsAlgClosed k]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure
      k S.ProjectiveCategory] in
/-- A full Hom generator remains full after passage to a finite selected
primitive corner. -/
theorem finsetProjectiveHom_span_eq_top
    (t : Finset ι) {X Y : S.ProjectiveCategory}
    (hX : S.projectiveVertex X ∈ t)
    (hY : S.projectiveVertex Y ∈ t) (f : X ⟶ Y)
    (hf : twoSidedEndomorphismSpan k f = ⊤) :
    twoSidedEndomorphismSpan k
      (finsetProjectiveHom S t hX hY f) = ⊤ := by
  let E := LargeIndecomposable.SplitBasicIdempotents.SelectedCorner.projectiveFunctor
    S (finsetPrimitiveEmbedding t)
  rw [← LargeIndecomposable.fullyFaithfulLinearFunctor_map_span_eq_top_iff E]
  let eX := eqToIso (projectiveFunctor_obj_finsetProjectiveObj_eq S t X hX)
  let eY := eqToIso (projectiveFunctor_obj_finsetProjectiveObj_eq S t Y hY)
  apply (LargeIndecomposable.homCongr_span_eq_top_iff
    (k := k) eX eY
      (E.map (finsetProjectiveHom S t hX hY f))).1
  have hmap : CategoryTheory.Linear.homCongr k eX eY
      (E.map (finsetProjectiveHom S t hX hY f)) = f := by
    simpa [eX, eY, E] using
      (homCongr_finsetAmbientHom (k := k) S t hX hY f)
  rw [hmap]
  exact hf

omit [IsAlgClosed k]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure
      k S.ProjectiveCategory] in
/-- A radical endomorphism generator retains its exact Jacobson span in a
finite selected primitive corner. -/
theorem finsetProjectiveEnd_span_eq_jacobson
    (t : Finset ι) (X : S.ProjectiveCategory)
    (hX : S.projectiveVertex X ∈ t) (tau : End X)
    (htauSpan : twoSidedEndomorphismSpan k tau =
      (Ring.jacobson (End X)).restrictScalars k) :
    twoSidedEndomorphismSpan k
        (End.of (finsetProjectiveHom S t hX hX tau.asHom)) =
      (Ring.jacobson
        (End (finsetProjectiveObj S t X hX))).restrictScalars k := by
  let X' := finsetProjectiveObj S t X hX
  let tau' : End X' := End.of (finsetProjectiveHom S t hX hX tau.asHom)
  let E := LargeIndecomposable.SplitBasicIdempotents.SelectedCorner.projectiveFunctor
    S (finsetPrimitiveEmbedding t)
  let eX := eqToIso (projectiveFunctor_obj_finsetProjectiveObj_eq S t X hX)
  have htauJ : tau ∈ Ring.jacobson (End X) := by
    have hmem : tau ∈
        (Ring.jacobson (End X)).restrictScalars k := by
      rw [← htauSpan]
      exact LargeIndecomposable.mem_twoSidedEndomorphismSpan k tau
    exact hmem
  have htau'ValJ : tau'.1 ∈
      Ring.jacobson
        (LargeIndecomposable.SplitBasicIdempotents.SelectedCorner
          S (finsetPrimitiveEmbedding t)) := by
    exact LargeIndecomposable.SplitBasicIdempotents.SelectedCorner.finsetProjectiveHom_val_mem_jacobson
      S t hX hX tau.asHom
      ((S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson X tau).1 htauJ)
  have htau'J : tau' ∈ Ring.jacobson (End X') := by
    exact ((LargeIndecomposable.SplitBasicIdempotents.SelectedCorner.splitBasic
      S (finsetPrimitiveEmbedding t)).projectiveEnd_mem_jacobson_iff_val_mem_jacobson
        X' tau').2 htau'ValJ
  change twoSidedEndomorphismSpan k tau' = _
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro h ⟨a, b, rfl⟩
    have hring : b * tau' * a ∈ Ring.jacobson (End X') :=
      (Ring.jacobson (End X')).mul_mem_right a
        ((Ring.jacobson (End X')).mul_mem_left b htau'J)
    change End.of ((a.asHom ≫ tau'.asHom) ≫ b.asHom) ∈
      Ring.jacobson (End X')
    rw [show End.of ((a.asHom ≫ tau'.asHom) ≫ b.asHom) =
        b * tau' * a by
      apply End.ext
      simp only [End.mul_def, Category.assoc]]
    exact hring
  · intro a ha
    let g : End X := End.of
      (CategoryTheory.Linear.homCongr k eX eX (E.map a))
    have haCornerVal : a.1 ∈
        Ring.jacobson
          (LargeIndecomposable.SplitBasicIdempotents.SelectedCorner
            S (finsetPrimitiveEmbedding t)) :=
      ((LargeIndecomposable.SplitBasicIdempotents.SelectedCorner.splitBasic
        S (finsetPrimitiveEmbedding t)).projectiveEnd_mem_jacobson_iff_val_mem_jacobson
          X' a).1 ha
    have haAmbientVal : a.1.1 ∈ Ring.jacobson A :=
      (LargeIndecomposable.SplitBasicIdempotents.SelectedCorner.mem_jacobson_iff_val_mem_jacobson
        S (finsetPrimitiveEmbedding t) a.1).1 haCornerVal
    have hgVal : g.1 ∈ Ring.jacobson A := by
      change (CategoryTheory.Linear.homCongr k eX eX (E.map a)).1 ∈
        Ring.jacobson A
      rw [homCongr_projectiveFunctorMap_val (k := k) S t hX hX a]
      exact haAmbientVal
    have hgJ : g ∈ Ring.jacobson (End X) :=
      (S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson X g).2 hgVal
    have hgSpan : g.asHom ∈ twoSidedEndomorphismSpan k tau.asHom := by
      change g ∈ twoSidedEndomorphismSpan k tau
      rw [htauSpan]
      exact hgJ
    have htauMap : CategoryTheory.Linear.homCongr k eX eX
        (E.map tau'.asHom) = tau.asHom := by
      simpa [eX, E, tau', X'] using
        (homCongr_finsetAmbientHom (k := k) S t hX hX tau.asHom)
    rw [← htauMap] at hgSpan
    have hback := LargeIndecomposable.homCongr_mem_twoSidedEndomorphismSpan
      (k := k) eX.symm eX.symm hgSpan
    have hmap : E.map a ∈
        twoSidedEndomorphismSpan k (E.map tau'.asHom) := by
      simpa [g, CategoryTheory.Linear.homCongr_apply,
        Category.assoc] using hback
    exact LargeIndecomposable.fullyFaithfulLinearFunctor_mem_span_of_map_mem
      (k := k) E hmap

omit [IsAlgClosed k]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure
      k S.ProjectiveCategory] in
/-- A radical primitive-projective full Hom generator has distinct source and
target objects. -/
theorem projectiveObj_ne_of_val_mem_jacobson_of_span_eq_top
    {X Y : S.ProjectiveCategory} (f : X ⟶ Y)
    (hfJ : f.1 ∈ Ring.jacobson A)
    (hspan : twoSidedEndomorphismSpan k f = ⊤) : X ≠ Y := by
  intro hXY
  subst Y
  have hfEndJ : End.of f ∈ Ring.jacobson (End X) :=
    (S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson
      X (End.of f)).2 hfJ
  have hle : twoSidedEndomorphismSpan k (End.of f) ≤
      (Ring.jacobson (End X)).restrictScalars k := by
    apply Submodule.span_le.2
    rintro g ⟨a, b, rfl⟩
    have hring : b * End.of f * a ∈ Ring.jacobson (End X) :=
      (Ring.jacobson (End X)).mul_mem_right a
        ((Ring.jacobson (End X)).mul_mem_left b hfEndJ)
    change End.of ((a.asHom ≫ f) ≫ b.asHom) ∈
      Ring.jacobson (End X)
    rw [show End.of ((a.asHom ≫ f) ≫ b.asHom) =
        b * End.of f * a by
      apply End.ext
      simp only [End.mul_def, Category.assoc]]
    exact hring
  have hone : (1 : End X) ∈ Ring.jacobson (End X) := by
    apply hle
    rw [hspan]
    exact Submodule.mem_top
  exact ((LargeIndecomposable.mem_ringJacobson_iff_not_isUnit
    (End X) 1).1 hone) isUnit_one

/-- A first-order coefficient for a radical generator vanishes on the
square of the local radical. -/
private theorem coefficient_eq_zero_of_mem_jacobson_sq
    {C : Type v} [Category C] [Preadditive C] [Linear k C]
    {X : C} [Module.Finite k (End X)] [IsLocalRing (End X)]
    [IsArtinianRing (End X)]
    (P : OrientedRadicalPowerParameter (k := k) X)
    (residue : End X →ₐ[k] k) (ell : End X →ₗ[k] k)
    (hell : ∀ a : End X, ell (a * P.tau) = residue a)
    (hresTau : residue P.tau = 0)
    (a : End X) (haSq : a ∈ (Ring.jacobson (End X)) ^ 2) :
    ell a = 0 := by
  by_cases ha0 : a = 0
  · subst a
    exact ell.map_zero
  have haJ : a ∈ Ring.jacobson (End X) :=
    (Ideal.pow_le_self (R := End X) (by omega)) haSq
  obtain ⟨n, hn, e, he, hae⟩ := P.transitData.factors a haJ ha0
  have hn2 : 2 ≤ n :=
    P.two_le_transitExponent_of_mem_sq haSq ha0 n hn e he hae
  have haRing : a = e * P.tau ^ n := by
    apply End.ext
    simpa only [End.mul_def] using hae
  have hnEq : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hpow : P.tau ^ n = P.tau ^ (n - 1) * P.tau := by
    conv_lhs => rw [← hnEq]
    exact pow_succ P.tau (n - 1)
  have haFactor : a = (e * P.tau ^ (n - 1)) * P.tau := by
    rw [haRing, hpow, mul_assoc]
  have hnsub : n - 1 ≠ 0 := by omega
  rw [haFactor, hell, map_mul, map_pow, hresTau,
    zero_pow hnsub, mul_zero]

omit [IsAlgClosed k]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure
      k S.ProjectiveCategory] in
/-- A split-basic residue kills every return cycle through a distinct
primitive-projective object. -/
theorem projectiveEndResidue_comp_eq_zero_of_ne
    {B : Type v} [Ring B] [Algebra k B]
    {K : Type x} [Fintype K] [DecidableEq K]
    (T : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := B) (ι := K))
    {X Y : T.ProjectiveCategory} (hXY : X ≠ Y)
    (l : X ⟶ Y) (r : Y ⟶ X) :
    T.projectiveEndResidue X (End.of (l ≫ r)) = 0 := by
  rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson]
  change r.1 * l.1 ∈ Ring.jacobson B
  exact (Ring.jacobson B).mul_mem_left r.1
    (ProjectiveCategory.offDiagonal_val_mem_jacobson T hXY l)

omit [IsAlgClosed k]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure
      k S.ProjectiveCategory] in
/-- A surviving full Hom generator cannot acquire a new factorization through
an object after passage to a radical quotient.  The lifted factorization
differs from the generator by an ideal-corner term of strictly smaller
principal span, hence lies on the same two-sided unit ray. -/
theorem factorsThrough_of_projectiveQuotientFunctor_map_factorsThrough
    {B : Type v} [Ring B] [Algebra k B] [Module.Finite k B]
    {K : Type x} [Fintype K] [DecidableEq K]
    (T : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := B) (ι := K))
    [LargeIndecomposable.HasBGRSDistributiveHomStructure
      k T.ProjectiveCategory]
    (I : TwoSidedIdeal B) (hI : I.asIdeal ≤ Ring.jacobson B)
    {X Y Z : T.ProjectiveCategory} (f : X ⟶ Y)
    (hIcorner : finiteIdealCorner T I X Y ≤
      twoSidedEndomorphismSpan k f)
    (hfsurvives : (T.projectiveQuotientFunctor I hI).map f ≠ 0)
    (lbar : (T.projectiveQuotientFunctor I hI).obj X ⟶
      (T.projectiveQuotientFunctor I hI).obj Z)
    (rbar : (T.projectiveQuotientFunctor I hI).obj Z ⟶
      (T.projectiveQuotientFunctor I hI).obj Y)
    (hfactor : (T.projectiveQuotientFunctor I hI).map f =
      lbar ≫ rbar) :
    ∃ (l : X ⟶ Z) (r : Z ⟶ Y), f = l ≫ r := by
  let F := T.projectiveQuotientFunctor I hI
  obtain ⟨l, hl⟩ := F.map_surjective lbar
  obtain ⟨r, hr⟩ := F.map_surjective rbar
  let d : X ⟶ Y := f - l ≫ r
  have hdmap : F.map d = 0 := by
    dsimp only [d]
    rw [F.map_sub, F.map_comp, hl, hr, ← hfactor]
    exact sub_self (F.map f)
  have hdI : d.1 ∈ I.asIdeal :=
    (T.projectiveQuotientFunctor_map_eq_zero_iff I hI d).1 hdmap
  have hfI : f.1 ∉ I.asIdeal := by
    intro hf
    apply hfsurvives
    exact (T.projectiveQuotientFunctor_map_eq_zero_iff I hI f).2 hf
  let W := finiteIdealCorner T I X Y
  have hdW : d ∈ W := hdI
  have hspanDLeW : twoSidedEndomorphismSpan k d ≤ W := by
    apply Submodule.span_le.2
    rintro q ⟨a, b, rfl⟩
    exact (finiteIdealCorner_isHomSubbimodule T I X Y).2 b
      ((finiteIdealCorner_isHomSubbimodule T I X Y).1 a hdW)
  have hdlt : twoSidedEndomorphismSpan k d <
      twoSidedEndomorphismSpan k f := by
    apply lt_of_le_of_ne
    · exact LargeIndecomposable.twoSidedEndomorphismSpan_le_of_mem
        (hIcorner hdW)
    · intro heq
      apply hfI
      have hfmem : f ∈ twoSidedEndomorphismSpan k d := by
        rw [heq]
        exact mem_twoSidedEndomorphismSpan k f
      exact hspanDLeW hfmem
  have hperturb := twoSidedEndomorphismSpan_sub_smul_eq_of_lt
    (k := k) f d 1 hdlt
  have hsub : f - d = l ≫ r := by
    dsimp only [d]
    module
  have hspanFactor : twoSidedEndomorphismSpan k (l ≫ r) =
      twoSidedEndomorphismSpan k f := by
    simpa only [one_smul, hsub] using hperturb
  have hunit : LargeIndecomposable.UnitRayEquivalent f (l ≫ r) :=
    LargeIndecomposable.unitRayEquivalent_of_twoSidedEndomorphismSpan_eq
      hspanFactor.symm
  obtain ⟨a, b, hab⟩ := hunit
  refine ⟨a.inv ≫ l, r ≫ b.inv, ?_⟩
  calc
    f = a.inv ≫ (a.hom ≫ f ≫ b.hom) ≫ b.inv := by simp
    _ = a.inv ≫ (l ≫ r) ≫ b.inv := by rw [← hab]
    _ = (a.inv ≫ l) ≫ (r ≫ b.inv) := by
      simp only [Category.assoc]

omit [IsAlgClosed k]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure
      k S.ProjectiveCategory] in
/-- For full generators with the Figure-14 initial orientations, exclusion of
factorization through the displayed outer generator excludes factorization
through the outer object by arbitrary morphisms. -/
private theorem not_factorsThrough_of_not_factorsThrough_initialGenerator
    {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [∀ T : C, IsLocalRing (End T)] [∀ T : C, IsArtinianRing (End T)]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure k C]
    {X Y Z : C} (f : X ⟶ Y) (outer : X ⟶ Z)
    (hfspan : twoSidedEndomorphismSpan k f = ⊤)
    (houterSpan : twoSidedEndomorphismSpan k outer = ⊤)
    (hfTransit : LargeIndecomposable.AllowsTransit f)
    (houterCotransit : LargeIndecomposable.AllowsCotransit outer)
    (hnot : ¬ ∃ r : Z ⟶ Y, f = outer ≫ r) :
    ¬ ∃ (l : X ⟶ Z) (r : Z ⟶ Y), f = l ≫ r := by
  rintro ⟨l, r, hlr⟩
  have hlmem : l ∈ twoSidedEndomorphismSpan k outer := by
    rw [houterSpan]
    exact Submodule.mem_top
  obtain ⟨a, ha⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsCotransit
      (k := k) houterCotransit hlmem
  let h := outer ≫ r
  have hfac : f = a.asHom ≫ h := by
    rw [hlr, ha]
    exact Category.assoc _ _ _
  have hf0 : f ≠ 0 := by
    intro hz
    apply hnot
    refine ⟨0, ?_⟩
    rw [hz]
    simp
  have hh0 : h ≠ 0 := by
    intro hz
    apply hf0
    rw [hfac, hz]
    simp
  have hfull : twoSidedEndomorphismSpan k (a.asHom ≫ h) = ⊤ := by
    rw [← hfac, hfspan]
  have haUnit : IsUnit a :=
    LargeIndecomposable.isUnit_of_twoSidedEndomorphismSpan_comp_left_eq_top
      a h hh0 hfull
  letI : IsIso a.asHom := (isUnit_iff_isIso a).1 haUnit
  let ai : End X := End.of (inv a.asHom)
  have haiUnit : IsUnit ai := (isUnit_iff_isIso ai).2 inferInstance
  obtain ⟨b, hab⟩ := hfTransit ai
  have hbUnit : IsUnit b := by
    by_contra hb
    exact (LargeIndecomposable.not_isUnit_left_of_transfer
      hf0 ai b hb hab) haiUnit
  letI : IsIso b.asHom := (isUnit_iff_isIso b).1 hbUnit
  have haiF : ai.asHom ≫ f = h := by
    rw [hfac]
    dsimp only [ai]
    simp
  apply hnot
  refine ⟨r ≫ inv b.asHom, ?_⟩
  calc
    f = h ≫ inv b.asHom := by rw [← haiF, hab]; simp
    _ = outer ≫ (r ≫ inv b.asHom) := by
      simp only [h, Category.assoc]

/-- The fully faithful embedding of the exact selected primitive-projective
category back into the ambient primitive-projective category. -/
abbrev selectedProjectiveFunctor
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :=
  LargeIndecomposable.SplitBasicIdempotents.SelectedCorner.projectiveFunctor
    S (selectedEmbedding S spine)

omit [IsAlgClosed k] in
@[simp]
theorem selectedProjectiveFunctor_obj_leftInner
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    (selectedProjectiveFunctor S spine).obj
      (selectedLeftInnerObj S spine) = spine.leftInner.obj.as := by
  apply S.projectiveVertexEquiv.injective
  simp [selectedProjectiveFunctor, selectedLeftInnerObj, selectedEmbedding]

omit [IsAlgClosed k] in
@[simp]
theorem selectedProjectiveFunctor_obj_rightInner
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    (selectedProjectiveFunctor S spine).obj
      (selectedRightInnerObj S spine) = spine.rightInner.obj.as := by
  apply S.projectiveVertexEquiv.injective
  simp [selectedProjectiveFunctor, selectedRightInnerObj, selectedEmbedding]

omit [IsAlgClosed k] in
@[simp]
theorem selectedProjectiveFunctor_obj_initial
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    (selectedProjectiveFunctor S spine).obj
      (selectedInitialObj S spine) = i.obj.as := by
  apply S.projectiveVertexEquiv.injective
  simp [selectedProjectiveFunctor, selectedInitialObj, selectedEmbedding]

omit [IsAlgClosed k] in
@[simp]
theorem selectedProjectiveFunctor_obj_terminal
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    (selectedProjectiveFunctor S spine).obj
      (selectedTerminalObj S spine) = j.obj.as := by
  apply S.projectiveVertexEquiv.injective
  simp [selectedProjectiveFunctor, selectedTerminalObj, selectedEmbedding]

/-- The critical middle path joins distinct ambient primitive projectives.
Indeed, it is radical but generates its complete Hom space. -/
theorem factorBranch_ambientRightInner_ne_leftInner
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    spine.rightInner.obj.as ≠ spine.leftInner.obj.as := by
  exact projectiveObj_ne_of_val_mem_jacobson_of_span_eq_top S
    (spine.lift.pathMap spine.middle)
    (S.rayArrowLift_pathMap_mem_jacobson spine.lift spine.middle
      spine.middle_length_pos)
    (spine.middle_full_span S hfinite)

/-- The first outer arrow joins distinct ambient primitive projectives. -/
theorem factorBranch_ambientLeftInner_ne_initial
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    spine.leftInner.obj.as ≠ i.obj.as := by
  exact projectiveObj_ne_of_val_mem_jacobson_of_span_eq_top S
    (spine.lift.representative spine.first)
    (S.rayArrowLift_representative_mem_jacobson spine.lift spine.first)
    (spine.initial_full_outer_spans S hfinite).2

/-- The last outer arrow joins distinct ambient primitive projectives. -/
theorem factorBranch_ambientTerminal_ne_rightInner
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    j.obj.as ≠ spine.rightInner.obj.as := by
  exact projectiveObj_ne_of_val_mem_jacobson_of_span_eq_top S
    (spine.lift.representative spine.last)
    (S.rayArrowLift_representative_mem_jacobson spine.lift spine.last)
    (spine.terminal_full_outer_spans S hfinite).1

set_option maxHeartbeats 800000 in
/-- In the first factor branch, the reverse generator admits no factorization
at all through the terminal object.  An arbitrary terminal second leg is a
target twist of the last arrow.  Fullness makes that twist invertible, and
the resulting unit multiple of the opposite local parameter still generates
the whole endomorphism algebra, contradicting the prohibited cotransit
direction of the last arrow. -/
theorem factorBranch_ambientLambda_not_factorsThrough_terminal
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    ¬ ∃ (l : spine.leftInner.obj.as ⟶ j.obj.as)
        (r : j.obj.as ⟶ spine.rightInner.obj.as),
      lambda = l ≫ r := by
  rintro ⟨l, r, hlr⟩
  let delta := spine.lift.pathMap spine.middle
  let last := spine.lift.representative spine.last
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  letI : Module.Finite k (End spine.rightInner.obj.as) := by
    change Module.Finite k
      (spine.rightInner.obj.as ⟶ spine.rightInner.obj.as)
    infer_instance
  have hlastSpan : twoSidedEndomorphismSpan k last = ⊤ :=
    (spine.terminal_full_outer_spans S hfinite).1
  have hlastT : LargeIndecomposable.AllowsTransit last := by
    rcases LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
        (k := k) last with hT | hC
    · exact hT
    · exact False.elim ((spine.last_not_allowsCotransit S) hC)
  have hrmem : r ∈ twoSidedEndomorphismSpan k last := by
    rw [hlastSpan]
    exact Submodule.mem_top
  obtain ⟨b, hr⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit
      (k := k) hlastT hrmem
  let h := l ≫ last
  have hlambda : lambda = h ≫ b.asHom := by
    calc
      lambda = l ≫ r := hlr
      _ = l ≫ (last ≫ b.asHom) := by rw [hr]
      _ = (l ≫ last) ≫ b.asHom := (Category.assoc _ _ _).symm
      _ = h ≫ b.asHom := rfl
  have hlambda0 : lambda ≠ 0 := by
    intro hz
    apply P.ne_zero
    apply End.ext
    change P.tau.asHom = 0
    rw [hfactor, hz]
    simp
  have hh0 : h ≠ 0 := by
    intro hz
    apply hlambda0
    rw [hlambda, hz]
    simp
  have hfull : twoSidedEndomorphismSpan k (h ≫ b.asHom) = ⊤ := by
    rw [← hlambda]
    exact spine.reverse_full_span_of_sigma_eq_reverse_comp_middle
      S hfinite P lambda hfactor
  have hbUnit : IsUnit b :=
    LargeIndecomposable.isUnit_of_twoSidedEndomorphismSpan_comp_right_eq_top
      h b hh0 hfull
  letI : IsIso b.asHom := (isUnit_iff_isIso b).1 hbUnit
  let binv : End spine.rightInner.obj.as := End.of (inv b.asHom)
  have hbinvUnit : IsUnit binv := (isUnit_iff_isIso binv).2 inferInstance
  let theta : End spine.rightInner.obj.as := End.of (delta ≫ h)
  have hQtau : Q.tau = b * theta := by
    apply End.ext
    rw [spine.middleCompReverseRadicalPowerParameter_tau
      S hfinite P lambda hfactor]
    simp only [theta, delta, End.mul_def, hlambda, Category.assoc]
  have hbbinv : b * binv = 1 := by
    apply End.ext
    dsimp only [binv]
    simp only [End.mul_def]
    change inv b.asHom ≫ b.asHom = 𝟙 spine.rightInner.obj.as
    simpa only [Category.comp_id] using
      IsIso.inv_hom_id_assoc b.asHom (𝟙 spine.rightInner.obj.as)
  have htheta : theta = Q.tau * binv := by
    rw [hQtau]
    calc
      theta = theta * (b * binv) := by rw [hbbinv, mul_one]
      _ = (theta * b) * binv := by rw [mul_assoc]
      _ = (b * theta) * binv := by
        rw [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.end_mul_comm
          S spine.rightInner.obj.as theta b]
  have hthetaGen : Algebra.adjoin k ({theta} : Set
      (End spine.rightInner.obj.as)) = ⊤ := by
    rw [htheta]
    exact Q.adjoin_mul_unit_eq_top binv hbinvUnit
  apply spine.reverse_not_factors_through_terminal_of_adjoin_middle_comp_reverse_eq_top
    S h hthetaGen
  exact ⟨l, rfl⟩

set_option maxHeartbeats 800000 in
/-- A radical-power generator at the right inner object admits no arbitrary
factorization through the terminal object.  Otherwise its terminal second
leg is a unit twist of the last arrow, and removing that unit leaves another
algebra generator whose factorization forces the forbidden cotransit
direction. -/
theorem factorBranch_ambientRightTau_not_factorsThrough_terminal
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    ¬ ∃ (l : spine.rightInner.obj.as ⟶ j.obj.as)
        (r : j.obj.as ⟶ spine.rightInner.obj.as),
      Q.tau.asHom = l ≫ r := by
  rintro ⟨l, r, hlr⟩
  let last := spine.lift.representative spine.last
  letI : Module.Finite k (End spine.rightInner.obj.as) := by
    change Module.Finite k
      (spine.rightInner.obj.as ⟶ spine.rightInner.obj.as)
    infer_instance
  have hlastSpan : twoSidedEndomorphismSpan k last = ⊤ :=
    (spine.terminal_full_outer_spans S hfinite).1
  have hlastT : LargeIndecomposable.AllowsTransit last := by
    rcases LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
        (k := k) last with hT | hC
    · exact hT
    · exact False.elim ((spine.last_not_allowsCotransit S) hC)
  have hrmem : r ∈ twoSidedEndomorphismSpan k last := by
    rw [hlastSpan]
    exact Submodule.mem_top
  obtain ⟨b, hr⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit
      (k := k) hlastT hrmem
  let theta : End spine.rightInner.obj.as := End.of (l ≫ last)
  have hQtau : Q.tau = b * theta := by
    apply End.ext
    calc
      Q.tau.asHom = l ≫ r := hlr
      _ = l ≫ (last ≫ b.asHom) := by rw [hr]
      _ = (b * theta).asHom := by
        simp only [theta, End.mul_def, Category.assoc]
  have hthetaJ : theta ∈
      Ring.jacobson (End spine.rightInner.obj.as) := by
    rw [S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
    change (l ≫ last).1 ∈ Ring.jacobson A
    simp only [comp_val]
    exact (Ring.jacobson A).mul_mem_right l.1
      (S.rayArrowLift_representative_mem_jacobson spine.lift spine.last)
  have hbUnit : IsUnit b := by
    by_contra hb
    have hbJ : b ∈ Ring.jacobson (End spine.rightInner.obj.as) :=
      (LargeIndecomposable.mem_ringJacobson_iff_not_isUnit
        (End spine.rightInner.obj.as) b).2 hb
    apply Q.tau_not_mem_jacobson_sq
    rw [hQtau, show (2 : ℕ) = 1 + 1 by omega,
      Ideal.IsTwoSided.pow_add, Submodule.pow_one]
    exact Ideal.mul_mem_mul hbJ hthetaJ
  letI : IsIso b.asHom := (isUnit_iff_isIso b).1 hbUnit
  let binv : End spine.rightInner.obj.as := End.of (inv b.asHom)
  have hbinvUnit : IsUnit binv := (isUnit_iff_isIso binv).2 inferInstance
  have hbbinv : b * binv = 1 := by
    apply End.ext
    change inv b.asHom ≫ b.asHom = 𝟙 spine.rightInner.obj.as
    simpa only [Category.comp_id] using
      IsIso.inv_hom_id_assoc b.asHom (𝟙 spine.rightInner.obj.as)
  have htheta : theta = Q.tau * binv := by
    rw [hQtau]
    calc
      theta = theta * (b * binv) := by rw [hbbinv, mul_one]
      _ = (theta * b) * binv := by rw [mul_assoc]
      _ = (b * theta) * binv := by
        rw [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.end_mul_comm
          S spine.rightInner.obj.as theta b]
  have hthetaGen : Algebra.adjoin k ({theta} : Set
      (End spine.rightInner.obj.as)) = ⊤ := by
    rw [htheta]
    exact Q.adjoin_mul_unit_eq_top binv hbinvUnit
  apply spine.last_not_allowsCotransit S
  let a : End j.obj.as := End.of (last ≫ l)
  apply LargeIndecomposable.ClosedZigzagTransfer.allowsCotransit_of_transfer_of_adjoin_eq_top
    last a theta hthetaGen
  calc
    a.asHom ≫ last = (last ≫ l) ≫ last := rfl
    _ = last ≫ (l ≫ last) := Category.assoc _ _ _
    _ = last ≫ theta.asHom := rfl

/-- Distinctness of the two inner objects reflects to the selected corner. -/
theorem factorBranch_selectedRightInner_ne_leftInner
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    selectedRightInnerObj S spine ≠ selectedLeftInnerObj S spine := by
  intro h
  apply factorBranch_ambientRightInner_ne_leftInner S hfinite spine
  have hv := congrArg (selectedProjectiveFunctor S spine).obj h
  simpa using hv

/-- Distinctness of the initial pair reflects to the selected corner. -/
theorem factorBranch_selectedLeftInner_ne_initial
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    selectedLeftInnerObj S spine ≠ selectedInitialObj S spine := by
  intro h
  apply factorBranch_ambientLeftInner_ne_initial S hfinite spine
  have hv := congrArg (selectedProjectiveFunctor S spine).obj h
  simpa using hv

/-- Distinctness of the terminal pair reflects to the selected corner. -/
theorem factorBranch_selectedTerminal_ne_rightInner
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    selectedTerminalObj S spine ≠ selectedRightInnerObj S spine := by
  intro h
  apply factorBranch_ambientTerminal_ne_rightInner S hfinite spine
  have hv := congrArg (selectedProjectiveFunctor S spine).obj h
  simpa using hv

/-- The selected reverse generator does not factor through the initial outer
object. -/
theorem factorBranch_selectedLambda_not_factors_through_initial
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    ¬ ∃ v : selectedInitialObj S spine ⟶
        selectedRightInnerObj S spine,
      selectedLambda S spine lambda = selectedFirst S spine ≫ v := by
  rintro ⟨v, hv⟩
  apply spine.reverse_not_factors_through_initial_of_sigma_eq_reverse_comp_middle
    S P lambda hfactor
  let E := selectedProjectiveFunctor S spine
  let eL := eqToIso (selectedProjectiveFunctor_obj_leftInner S spine)
  let eI := eqToIso (selectedProjectiveFunctor_obj_initial S spine)
  let eR := eqToIso (selectedProjectiveFunctor_obj_rightInner S spine)
  let vAmbient := CategoryTheory.Linear.homCongr k eI eR (E.map v)
  refine ⟨vAmbient, ?_⟩
  have hlambda : CategoryTheory.Linear.homCongr k eL eR
      (E.map (selectedLambda S spine lambda)) = lambda := by
    simpa [eL, eR, E, selectedProjectiveFunctor, selectedLambda] using
      (homCongr_finsetAmbientHom (k := k) S
        (selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine) lambda)
  have hfirst : CategoryTheory.Linear.homCongr k eL eI
      (E.map (selectedFirst S spine)) =
        spine.lift.representative spine.first := by
    simpa [eL, eI, E, selectedProjectiveFunctor, selectedFirst] using
      (homCongr_finsetAmbientHom (k := k) S
        (selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine)
        (initial_mem_selectedVertices S spine)
        (spine.lift.representative spine.first))
  have hcomp : CategoryTheory.Linear.homCongr k eL eR
      (E.map (selectedFirst S spine) ≫ E.map v) =
        CategoryTheory.Linear.homCongr k eL eI
            (E.map (selectedFirst S spine)) ≫ vAmbient := by
    simp [vAmbient, CategoryTheory.Linear.homCongr_apply, Category.assoc]
  calc
    lambda = CategoryTheory.Linear.homCongr k eL eR
        (E.map (selectedLambda S spine lambda)) := hlambda.symm
    _ = CategoryTheory.Linear.homCongr k eL eR
        (E.map (selectedFirst S spine ≫ v)) := by rw [hv]
    _ = spine.lift.representative spine.first ≫ vAmbient := by
      rw [Functor.map_comp, hcomp, hfirst]

/-- The selected reverse generator does not factor through the terminal outer
object. -/
theorem factorBranch_selectedLambda_not_factors_through_terminal
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    ¬ ∃ u : selectedLeftInnerObj S spine ⟶
        selectedTerminalObj S spine,
      selectedLambda S spine lambda = u ≫ selectedLast S spine := by
  rintro ⟨u, hu⟩
  apply spine.reverse_not_factors_through_terminal_of_sigma_eq_reverse_comp_middle
    S hfinite P lambda hfactor
  let E := selectedProjectiveFunctor S spine
  let eL := eqToIso (selectedProjectiveFunctor_obj_leftInner S spine)
  let eT := eqToIso (selectedProjectiveFunctor_obj_terminal S spine)
  let eR := eqToIso (selectedProjectiveFunctor_obj_rightInner S spine)
  let uAmbient := CategoryTheory.Linear.homCongr k eL eT (E.map u)
  refine ⟨uAmbient, ?_⟩
  have hlambda : CategoryTheory.Linear.homCongr k eL eR
      (E.map (selectedLambda S spine lambda)) = lambda := by
    simpa [eL, eR, E, selectedProjectiveFunctor, selectedLambda] using
      (homCongr_finsetAmbientHom (k := k) S
        (selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine) lambda)
  have hlast : CategoryTheory.Linear.homCongr k eT eR
      (E.map (selectedLast S spine)) =
        spine.lift.representative spine.last := by
    simpa [eT, eR, E, selectedProjectiveFunctor, selectedLast] using
      (homCongr_finsetAmbientHom (k := k) S
        (selectedVertices S spine)
        (terminal_mem_selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine)
        (spine.lift.representative spine.last))
  have hcomp : CategoryTheory.Linear.homCongr k eL eR
      (E.map u ≫ E.map (selectedLast S spine)) =
        uAmbient ≫ CategoryTheory.Linear.homCongr k eT eR
          (E.map (selectedLast S spine)) := by
    simp [uAmbient, CategoryTheory.Linear.homCongr_apply, Category.assoc]
  calc
    lambda = CategoryTheory.Linear.homCongr k eL eR
        (E.map (selectedLambda S spine lambda)) := hlambda.symm
    _ = CategoryTheory.Linear.homCongr k eL eR
        (E.map (u ≫ selectedLast S spine)) := by rw [hu]
    _ = uAmbient ≫ spine.lift.representative spine.last := by
      rw [Functor.map_comp, hcomp, hlast]

set_option maxHeartbeats 800000 in
/-- The selected reverse generator admits no arbitrary factorization through
the terminal outer object. -/
theorem factorBranch_selectedLambda_not_factorsThrough_terminal
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    ¬ ∃ (l : selectedLeftInnerObj S spine ⟶
          selectedTerminalObj S spine)
        (r : selectedTerminalObj S spine ⟶
          selectedRightInnerObj S spine),
      selectedLambda S spine lambda = l ≫ r := by
  rintro ⟨l, r, hlr⟩
  apply factorBranch_ambientLambda_not_factorsThrough_terminal
    S hfinite spine P lambda hfactor
  let E := selectedProjectiveFunctor S spine
  let eL := eqToIso (selectedProjectiveFunctor_obj_leftInner S spine)
  let eT := eqToIso (selectedProjectiveFunctor_obj_terminal S spine)
  let eR := eqToIso (selectedProjectiveFunctor_obj_rightInner S spine)
  let lAmbient := CategoryTheory.Linear.homCongr k eL eT (E.map l)
  let rAmbient := CategoryTheory.Linear.homCongr k eT eR (E.map r)
  refine ⟨lAmbient, rAmbient, ?_⟩
  have hlambda : CategoryTheory.Linear.homCongr k eL eR
      (E.map (selectedLambda S spine lambda)) = lambda := by
    simpa [eL, eR, E, selectedProjectiveFunctor, selectedLambda] using
      (homCongr_finsetAmbientHom (k := k) S
        (selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine) lambda)
  have hcomp : CategoryTheory.Linear.homCongr k eL eR
      (E.map l ≫ E.map r) = lAmbient ≫ rAmbient := by
    dsimp only [lAmbient, rAmbient]
    simp only [CategoryTheory.Linear.homCongr_apply, Category.assoc,
      Iso.hom_inv_id_assoc]
  calc
    lambda = CategoryTheory.Linear.homCongr k eL eR
        (E.map (selectedLambda S spine lambda)) := hlambda.symm
    _ = CategoryTheory.Linear.homCongr k eL eR
        (E.map (l ≫ r)) := by rw [hlr]
    _ = lAmbient ≫ rAmbient := by rw [Functor.map_comp, hcomp]

set_option maxHeartbeats 800000 in
/-- The selected left cycle cannot factor through the initial outer object;
otherwise the source parameter would transfer across the first arrow. -/
theorem factorBranch_selectedLeftTau_not_factors_through_initial
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as) :
    ¬ ∃ v : selectedInitialObj S spine ⟶
        selectedLeftInnerObj S spine,
      selectedLeftTau S spine P = selectedFirst S spine ≫ v := by
  rintro ⟨v, hv⟩
  apply spine.initial_parameter_comp_first_not_transfers S P
  let E := selectedProjectiveFunctor S spine
  let eL := eqToIso (selectedProjectiveFunctor_obj_leftInner S spine)
  let eI := eqToIso (selectedProjectiveFunctor_obj_initial S spine)
  let vAmbient := CategoryTheory.Linear.homCongr k eI eL (E.map v)
  let firstAmbient := spine.lift.representative spine.first
  have htau : CategoryTheory.Linear.homCongr k eL eL
      (E.map (selectedLeftTau S spine P)) = P.tau.asHom := by
    simpa [eL, E, selectedProjectiveFunctor, selectedLeftTau] using
      (homCongr_finsetAmbientHom (k := k) S
        (selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine) P.tau.asHom)
  have hfirst : CategoryTheory.Linear.homCongr k eL eI
      (E.map (selectedFirst S spine)) = firstAmbient := by
    simpa [eL, eI, E, firstAmbient, selectedProjectiveFunctor,
      selectedFirst] using
      (homCongr_finsetAmbientHom (k := k) S
        (selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine)
        (initial_mem_selectedVertices S spine)
        (spine.lift.representative spine.first))
  have hcomp : CategoryTheory.Linear.homCongr k eL eL
      (E.map (selectedFirst S spine) ≫ E.map v) =
        CategoryTheory.Linear.homCongr k eL eI
            (E.map (selectedFirst S spine)) ≫ vAmbient := by
    dsimp only [vAmbient]
    simp only [CategoryTheory.Linear.homCongr_apply, Category.assoc,
      Iso.hom_inv_id_assoc]
  have htauFactor : P.tau.asHom = firstAmbient ≫ vAmbient := by
    calc
      P.tau.asHom = CategoryTheory.Linear.homCongr k eL eL
          (E.map (selectedLeftTau S spine P)) := htau.symm
      _ = CategoryTheory.Linear.homCongr k eL eL
          (E.map (selectedFirst S spine ≫ v)) := by rw [hv]
      _ = firstAmbient ≫ vAmbient := by
        rw [Functor.map_comp, hcomp, hfirst]
  refine ⟨End.of (vAmbient ≫ firstAmbient), ?_⟩
  rw [htauFactor]
  change (firstAmbient ≫ vAmbient) ≫ firstAmbient =
    firstAmbient ≫ (vAmbient ≫ firstAmbient)
  exact Category.assoc _ _ _

set_option maxHeartbeats 800000 in
/-- The selected right cycle cannot factor through the terminal outer object;
otherwise the source parameter would transfer across the last arrow. -/
theorem factorBranch_selectedRightTau_not_factors_through_terminal
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    ¬ ∃ u : selectedRightInnerObj S spine ⟶
        selectedTerminalObj S spine,
      selectedRightTau S spine Q = u ≫ selectedLast S spine := by
  rintro ⟨u, hu⟩
  apply spine.last_comp_terminal_parameter_not_transfers S Q
  let E := selectedProjectiveFunctor S spine
  let eR := eqToIso (selectedProjectiveFunctor_obj_rightInner S spine)
  let eT := eqToIso (selectedProjectiveFunctor_obj_terminal S spine)
  let uAmbient := CategoryTheory.Linear.homCongr k eR eT (E.map u)
  let lastAmbient := spine.lift.representative spine.last
  have htau : CategoryTheory.Linear.homCongr k eR eR
      (E.map (selectedRightTau S spine Q)) = Q.tau.asHom := by
    simpa [eR, E, selectedProjectiveFunctor, selectedRightTau] using
      (homCongr_finsetAmbientHom (k := k) S
        (selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine) Q.tau.asHom)
  have hlast : CategoryTheory.Linear.homCongr k eT eR
      (E.map (selectedLast S spine)) = lastAmbient := by
    simpa [eT, eR, E, lastAmbient, selectedProjectiveFunctor,
      selectedLast] using
      (homCongr_finsetAmbientHom (k := k) S
        (selectedVertices S spine)
        (terminal_mem_selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine)
        (spine.lift.representative spine.last))
  have hcomp : CategoryTheory.Linear.homCongr k eR eR
      (E.map u ≫ E.map (selectedLast S spine)) =
        uAmbient ≫ CategoryTheory.Linear.homCongr k eT eR
          (E.map (selectedLast S spine)) := by
    dsimp only [uAmbient]
    simp only [CategoryTheory.Linear.homCongr_apply, Category.assoc,
      Iso.hom_inv_id_assoc]
  have htauFactor : Q.tau.asHom = uAmbient ≫ lastAmbient := by
    calc
      Q.tau.asHom = CategoryTheory.Linear.homCongr k eR eR
          (E.map (selectedRightTau S spine Q)) := htau.symm
      _ = CategoryTheory.Linear.homCongr k eR eR
          (E.map (u ≫ selectedLast S spine)) := by rw [hu]
      _ = uAmbient ≫ lastAmbient := by
        rw [Functor.map_comp, hcomp, hlast]
  refine ⟨End.of (lastAmbient ≫ uAmbient), ?_⟩
  rw [htauFactor]
  change (lastAmbient ≫ uAmbient) ≫ lastAmbient =
    lastAmbient ≫ (uAmbient ≫ lastAmbient)
  exact Category.assoc _ _ _

set_option maxHeartbeats 800000 in
/-- The selected right local generator admits no arbitrary factorization
through the terminal outer object. -/
theorem factorBranch_selectedRightTau_not_factorsThrough_terminal
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    ¬ ∃ (l : selectedRightInnerObj S spine ⟶
          selectedTerminalObj S spine)
        (r : selectedTerminalObj S spine ⟶
          selectedRightInnerObj S spine),
      selectedRightTau S spine Q = l ≫ r := by
  rintro ⟨l, r, hlr⟩
  apply factorBranch_ambientRightTau_not_factorsThrough_terminal
    S hfinite spine Q
  let E := selectedProjectiveFunctor S spine
  let eR := eqToIso (selectedProjectiveFunctor_obj_rightInner S spine)
  let eT := eqToIso (selectedProjectiveFunctor_obj_terminal S spine)
  let lAmbient := CategoryTheory.Linear.homCongr k eR eT (E.map l)
  let rAmbient := CategoryTheory.Linear.homCongr k eT eR (E.map r)
  refine ⟨lAmbient, rAmbient, ?_⟩
  have htau : CategoryTheory.Linear.homCongr k eR eR
      (E.map (selectedRightTau S spine Q)) = Q.tau.asHom := by
    simpa [eR, E, selectedProjectiveFunctor, selectedRightTau] using
      (homCongr_finsetAmbientHom (k := k) S
        (selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine) Q.tau.asHom)
  have hcomp : CategoryTheory.Linear.homCongr k eR eR
      (E.map l ≫ E.map r) = lAmbient ≫ rAmbient := by
    dsimp only [lAmbient, rAmbient]
    simp only [CategoryTheory.Linear.homCongr_apply, Category.assoc,
      Iso.hom_inv_id_assoc]
  calc
    Q.tau.asHom = CategoryTheory.Linear.homCongr k eR eR
        (E.map (selectedRightTau S spine Q)) := htau.symm
    _ = CategoryTheory.Linear.homCongr k eR eR
        (E.map (l ≫ r)) := by rw [hlr]
    _ = lAmbient ≫ rAmbient := by rw [Functor.map_comp, hcomp]

/-- The selected lift of the critical middle path still generates its whole
Hom space. -/
theorem factorBranch_selectedMiddle_span_eq_top
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    twoSidedEndomorphismSpan k (selectedMiddle S spine) = ⊤ := by
  let E := selectedProjectiveFunctor S spine
  rw [← LargeIndecomposable.fullyFaithfulLinearFunctor_map_span_eq_top_iff E]
  let eR := eqToIso (selectedProjectiveFunctor_obj_rightInner S spine)
  let eL := eqToIso (selectedProjectiveFunctor_obj_leftInner S spine)
  apply (LargeIndecomposable.homCongr_span_eq_top_iff
    (k := k) eR eL (E.map (selectedMiddle S spine))).1
  have hmap : CategoryTheory.Linear.homCongr k eR eL
      (E.map (selectedMiddle S spine)) =
        spine.lift.pathMap spine.middle := by
    simpa [eR, eL, E, selectedProjectiveFunctor, selectedMiddle] using
      (homCongr_finsetAmbientHom (k := k) S
        (selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine)
        (spine.lift.pathMap spine.middle))
  rw [hmap]
  exact spine.middle_full_span S hfinite

/-- The selected reverse arrow remains a full Hom generator in the first
Figure-14 factor branch. -/
theorem factorBranch_selectedLambda_span_eq_top
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    twoSidedEndomorphismSpan k (selectedLambda S spine lambda) = ⊤ := by
  let E := selectedProjectiveFunctor S spine
  rw [← LargeIndecomposable.fullyFaithfulLinearFunctor_map_span_eq_top_iff E]
  let eL := eqToIso (selectedProjectiveFunctor_obj_leftInner S spine)
  let eR := eqToIso (selectedProjectiveFunctor_obj_rightInner S spine)
  apply (LargeIndecomposable.homCongr_span_eq_top_iff
    (k := k) eL eR (E.map (selectedLambda S spine lambda))).1
  have hmap : CategoryTheory.Linear.homCongr k eL eR
      (E.map (selectedLambda S spine lambda)) = lambda := by
    simpa [eL, eR, E, selectedProjectiveFunctor, selectedLambda] using
      (homCongr_finsetAmbientHom (k := k) S
        (selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine) lambda)
  rw [hmap]
  exact spine.reverse_full_span_of_sigma_eq_reverse_comp_middle
    S hfinite P lambda hfactor

omit [IsAlgClosed k] in
/-- The selected lift of the left radical parameter still generates the
whole endomorphism radical of the selected left-inner projective. -/
theorem factorBranch_selectedLeftTau_span_eq_jacobson
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as) :
    twoSidedEndomorphismSpan k
        (End.of (selectedLeftTau S spine P)) =
      (Ring.jacobson
        (End (selectedLeftInnerObj S spine))).restrictScalars k := by
  exact finsetProjectiveEnd_span_eq_jacobson (k := k) S
    (selectedVertices S spine) spine.leftInner.obj.as
    (leftInner_mem_selectedVertices S spine) P.tau P.span_eq

omit [IsAlgClosed k] in
/-- The same selected-corner radical transport at the right-inner
projective. -/
theorem selectedRightTau_span_eq_jacobson
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    twoSidedEndomorphismSpan k
        (End.of (selectedRightTau S spine Q)) =
      (Ring.jacobson
        (End (selectedRightInnerObj S spine))).restrictScalars k := by
  exact finsetProjectiveEnd_span_eq_jacobson (k := k) S
    (selectedVertices S spine) spine.rightInner.obj.as
    (rightInner_mem_selectedVertices S spine) Q.tau Q.span_eq

/-- The selected first outer arrow remains a full Hom generator. -/
theorem factorBranch_selectedFirst_span_eq_top
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    twoSidedEndomorphismSpan k (selectedFirst S spine) = ⊤ := by
  let E := selectedProjectiveFunctor S spine
  rw [← LargeIndecomposable.fullyFaithfulLinearFunctor_map_span_eq_top_iff E]
  let eL := eqToIso (selectedProjectiveFunctor_obj_leftInner S spine)
  let eI := eqToIso (selectedProjectiveFunctor_obj_initial S spine)
  apply (LargeIndecomposable.homCongr_span_eq_top_iff
    (k := k) eL eI (E.map (selectedFirst S spine))).1
  have hmap : CategoryTheory.Linear.homCongr k eL eI
      (E.map (selectedFirst S spine)) =
        spine.lift.representative spine.first := by
    simpa [eL, eI, E, selectedProjectiveFunctor, selectedFirst] using
      (homCongr_finsetAmbientHom (k := k) S
        (selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine)
        (initial_mem_selectedVertices S spine)
        (spine.lift.representative spine.first))
  rw [hmap]
  exact (spine.initial_full_outer_spans S hfinite).2

/-- The selected last outer arrow remains a full Hom generator. -/
theorem factorBranch_selectedLast_span_eq_top
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    twoSidedEndomorphismSpan k (selectedLast S spine) = ⊤ := by
  let E := selectedProjectiveFunctor S spine
  rw [← LargeIndecomposable.fullyFaithfulLinearFunctor_map_span_eq_top_iff E]
  let eT := eqToIso (selectedProjectiveFunctor_obj_terminal S spine)
  let eR := eqToIso (selectedProjectiveFunctor_obj_rightInner S spine)
  apply (LargeIndecomposable.homCongr_span_eq_top_iff
    (k := k) eT eR (E.map (selectedLast S spine))).1
  have hmap : CategoryTheory.Linear.homCongr k eT eR
      (E.map (selectedLast S spine)) =
        spine.lift.representative spine.last := by
    simpa [eT, eR, E, selectedProjectiveFunctor, selectedLast] using
      (homCongr_finsetAmbientHom (k := k) S
        (selectedVertices S spine)
        (terminal_mem_selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine)
        (spine.lift.representative spine.last))
  rw [hmap]
  exact (spine.terminal_full_outer_spans S hfinite).1

/-- The selected initial outer composite remains a full Hom generator. -/
theorem factorBranch_selectedPrefix_span_eq_top
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    twoSidedEndomorphismSpan k
      (selectedMiddle S spine ≫ selectedFirst S spine) = ⊤ := by
  let E := selectedProjectiveFunctor S spine
  rw [← LargeIndecomposable.fullyFaithfulLinearFunctor_map_span_eq_top_iff E]
  let eR := eqToIso (selectedProjectiveFunctor_obj_rightInner S spine)
  let eI := eqToIso (selectedProjectiveFunctor_obj_initial S spine)
  apply (LargeIndecomposable.homCongr_span_eq_top_iff
    (k := k) eR eI
      (E.map (selectedMiddle S spine ≫ selectedFirst S spine))).1
  have hmap : CategoryTheory.Linear.homCongr k eR eI
      (E.map (selectedMiddle S spine ≫ selectedFirst S spine)) =
        spine.lift.pathMap spine.middle ≫
          spine.lift.representative spine.first := by
    let eL := eqToIso (selectedProjectiveFunctor_obj_leftInner S spine)
    have hmiddle : CategoryTheory.Linear.homCongr k eR eL
        (E.map (selectedMiddle S spine)) =
          spine.lift.pathMap spine.middle := by
      simpa [eR, eL, E, selectedProjectiveFunctor, selectedMiddle] using
        (homCongr_finsetAmbientHom (k := k) S
          (selectedVertices S spine)
          (rightInner_mem_selectedVertices S spine)
          (leftInner_mem_selectedVertices S spine)
          (spine.lift.pathMap spine.middle))
    have hfirst : CategoryTheory.Linear.homCongr k eL eI
        (E.map (selectedFirst S spine)) =
          spine.lift.representative spine.first := by
      simpa [eL, eI, E, selectedProjectiveFunctor, selectedFirst] using
        (homCongr_finsetAmbientHom (k := k) S
          (selectedVertices S spine)
          (leftInner_mem_selectedVertices S spine)
          (initial_mem_selectedVertices S spine)
          (spine.lift.representative spine.first))
    rw [Functor.map_comp]
    have hcongr : CategoryTheory.Linear.homCongr k eR eI
        (E.map (selectedMiddle S spine) ≫
          E.map (selectedFirst S spine)) =
        CategoryTheory.Linear.homCongr k eR eL
            (E.map (selectedMiddle S spine)) ≫
          CategoryTheory.Linear.homCongr k eL eI
            (E.map (selectedFirst S spine)) := by
      simp [CategoryTheory.Linear.homCongr_apply, Category.assoc]
    rw [hcongr, hmiddle, hfirst]
  rw [hmap]
  have hpath : spine.lift.pathMap
      (spine.first.toPath.comp spine.middle) =
        spine.lift.pathMap spine.middle ≫
          spine.lift.representative spine.first := by
    simp only [BGRSRayArrowLift.pathMap,
      LinearPathCategory.pathMap_comp, Quiver.Hom.toPath,
      LinearPathCategory.pathMap_cons,
      LinearPathCategory.pathMap_nil, Category.comp_id]
  rw [← hpath]
  exact (spine.long_outer_composites_full_spans S hfinite).2

/-- The selected terminal outer composite remains a full Hom generator. -/
theorem factorBranch_selectedSuffix_span_eq_top
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    twoSidedEndomorphismSpan k
      (selectedLast S spine ≫ selectedMiddle S spine) = ⊤ := by
  let E := selectedProjectiveFunctor S spine
  rw [← LargeIndecomposable.fullyFaithfulLinearFunctor_map_span_eq_top_iff E]
  let eT := eqToIso (selectedProjectiveFunctor_obj_terminal S spine)
  let eL := eqToIso (selectedProjectiveFunctor_obj_leftInner S spine)
  apply (LargeIndecomposable.homCongr_span_eq_top_iff
    (k := k) eT eL
      (E.map (selectedLast S spine ≫ selectedMiddle S spine))).1
  have hmap : CategoryTheory.Linear.homCongr k eT eL
      (E.map (selectedLast S spine ≫ selectedMiddle S spine)) =
        spine.lift.representative spine.last ≫
          spine.lift.pathMap spine.middle := by
    let eR := eqToIso (selectedProjectiveFunctor_obj_rightInner S spine)
    have hlast : CategoryTheory.Linear.homCongr k eT eR
        (E.map (selectedLast S spine)) =
          spine.lift.representative spine.last := by
      simpa [eT, eR, E, selectedProjectiveFunctor, selectedLast] using
        (homCongr_finsetAmbientHom (k := k) S
          (selectedVertices S spine)
          (terminal_mem_selectedVertices S spine)
          (rightInner_mem_selectedVertices S spine)
          (spine.lift.representative spine.last))
    have hmiddle : CategoryTheory.Linear.homCongr k eR eL
        (E.map (selectedMiddle S spine)) =
          spine.lift.pathMap spine.middle := by
      simpa [eR, eL, E, selectedProjectiveFunctor, selectedMiddle] using
        (homCongr_finsetAmbientHom (k := k) S
          (selectedVertices S spine)
          (rightInner_mem_selectedVertices S spine)
          (leftInner_mem_selectedVertices S spine)
          (spine.lift.pathMap spine.middle))
    rw [Functor.map_comp]
    have hcongr : CategoryTheory.Linear.homCongr k eT eL
        (E.map (selectedLast S spine) ≫
          E.map (selectedMiddle S spine)) =
        CategoryTheory.Linear.homCongr k eT eR
            (E.map (selectedLast S spine)) ≫
          CategoryTheory.Linear.homCongr k eR eL
            (E.map (selectedMiddle S spine)) := by
      simp [CategoryTheory.Linear.homCongr_apply, Category.assoc]
    rw [hcongr, hlast, hmiddle]
  rw [hmap]
  have hpath : spine.lift.pathMap
      (spine.middle.comp spine.last.toPath) =
        spine.lift.representative spine.last ≫
          spine.lift.pathMap spine.middle := by
    simp only [BGRSRayArrowLift.pathMap,
      LinearPathCategory.pathMap_comp, Quiver.Hom.toPath,
      LinearPathCategory.pathMap_cons,
      LinearPathCategory.pathMap_nil, Category.comp_id]
  rw [← hpath]
  exact (spine.long_outer_composites_full_spans S hfinite).1

/-- The selected middle path retains both transit directions. -/
theorem factorBranch_selectedMiddle_allowsBitransit
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    LargeIndecomposable.AllowsTransit (selectedMiddle S spine) ∧
      LargeIndecomposable.AllowsCotransit (selectedMiddle S spine) := by
  have hmiddle := spine.middle_allowsBitransit S hfinite
  exact
    ⟨finsetProjectiveHom_allowsTransit (k := k) S
        (selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine)
        (spine.lift.pathMap spine.middle) hmiddle.1,
      finsetProjectiveHom_allowsCotransit (k := k) S
        (selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine)
        (spine.lift.pathMap spine.middle) hmiddle.2⟩

/-- The selected reverse arrow retains transit in the first Figure-14
factor branch. -/
theorem factorBranch_selectedLambda_allowsTransit
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    LargeIndecomposable.AllowsTransit
      (selectedLambda S spine lambda) := by
  exact finsetProjectiveHom_allowsTransit (k := k) S
    (selectedVertices S spine)
    (leftInner_mem_selectedVertices S spine)
    (rightInner_mem_selectedVertices S spine) lambda
    (spine.reverse_allowsTransit_of_sigma_eq_reverse_comp_middle
      S P lambda hfactor)

omit [IsAlgClosed k] in
/-- Since the ambient first arrow cannot allow transit, distributivity puts
it in the cotransit branch; this direction reflects to the selected corner. -/
theorem factorBranch_selectedFirst_allowsCotransit
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    LargeIndecomposable.AllowsCotransit (selectedFirst S spine) := by
  have hfirst : LargeIndecomposable.AllowsCotransit
      (spine.lift.representative spine.first) := by
    rcases LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
        (k := k) (spine.lift.representative spine.first) with h | h
    · exact False.elim ((spine.first_not_allowsTransit S) h)
    · exact h
  exact finsetProjectiveHom_allowsCotransit (k := k) S
    (selectedVertices S spine)
    (leftInner_mem_selectedVertices S spine)
    (initial_mem_selectedVertices S spine)
    (spine.lift.representative spine.first) hfirst

omit [IsAlgClosed k] in
/-- Dually, the ambient last arrow cannot allow cotransit and therefore lies
in the transit branch, which reflects to the selected corner. -/
theorem factorBranch_selectedLast_allowsTransit
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    LargeIndecomposable.AllowsTransit (selectedLast S spine) := by
  have hlast : LargeIndecomposable.AllowsTransit
      (spine.lift.representative spine.last) := by
    rcases LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
        (k := k) (spine.lift.representative spine.last) with h | h
    · exact h
    · exact False.elim ((spine.last_not_allowsCotransit S) h)
  exact finsetProjectiveHom_allowsTransit (k := k) S
    (selectedVertices S spine)
    (terminal_mem_selectedVertices S spine)
    (rightInner_mem_selectedVertices S spine)
    (spine.lift.representative spine.last) hlast

/-- The selected reverse generator admits no factorization at all through the
initial outer object, not merely no factorization whose first leg is the
chosen outer generator. -/
theorem factorBranch_selectedLambda_not_factorsThrough_initial
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    ¬ ∃ (l : selectedLeftInnerObj S spine ⟶
          selectedInitialObj S spine)
        (r : selectedInitialObj S spine ⟶
          selectedRightInnerObj S spine),
      selectedLambda S spine lambda = l ≫ r := by
  letI : LargeIndecomposable.HasBGRSDistributiveHomStructure k
      (selectedSplitBasic S spine).ProjectiveCategory :=
    LargeIndecomposable.HasBGRSDistributiveHomStructure.of_fullyFaithful
      (selectedProjectiveFunctor S spine)
  exact not_factorsThrough_of_not_factorsThrough_initialGenerator
    (selectedLambda S spine lambda) (selectedFirst S spine)
    (factorBranch_selectedLambda_span_eq_top
      S hfinite spine P lambda hfactor)
    (factorBranch_selectedFirst_span_eq_top S hfinite spine)
    (factorBranch_selectedLambda_allowsTransit S spine P lambda hfactor)
    (factorBranch_selectedFirst_allowsCotransit S spine)
    (factorBranch_selectedLambda_not_factors_through_initial
      S spine P lambda hfactor)

/-- The selected left cycle admits no factorization through the initial outer
object.  Cotransit expresses the first leg through the chosen outer arrow,
and commutativity of the local endomorphism ring moves the remaining source
endomorphism to the other side. -/
theorem factorBranch_selectedLeftTau_not_factorsThrough_initial
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as) :
    ¬ ∃ (l : selectedLeftInnerObj S spine ⟶
          selectedInitialObj S spine)
        (r : selectedInitialObj S spine ⟶
          selectedLeftInnerObj S spine),
      selectedLeftTau S spine P = l ≫ r := by
  letI : LargeIndecomposable.HasBGRSDistributiveHomStructure k
      (selectedSplitBasic S spine).ProjectiveCategory :=
    LargeIndecomposable.HasBGRSDistributiveHomStructure.of_fullyFaithful
      (selectedProjectiveFunctor S spine)
  rintro ⟨l, r, hlr⟩
  have hlmem : l ∈ twoSidedEndomorphismSpan k
      (selectedFirst S spine) := by
    rw [factorBranch_selectedFirst_span_eq_top S hfinite spine]
    exact Submodule.mem_top
  obtain ⟨a, ha⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsCotransit
      (k := k) (factorBranch_selectedFirst_allowsCotransit S spine) hlmem
  apply factorBranch_selectedLeftTau_not_factors_through_initial S spine P
  refine ⟨r ≫ a.asHom, ?_⟩
  let c : End (selectedLeftInnerObj S spine) :=
    End.of (selectedFirst S spine ≫ r)
  have hcomm :=
    LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.end_mul_comm
      (selectedSplitBasic S spine) (selectedLeftInnerObj S spine) c a
  have hcommHom : a.asHom ≫ c.asHom = c.asHom ≫ a.asHom := by
    simpa only [End.mul_def] using congrArg End.asHom hcomm
  calc
    selectedLeftTau S spine P =
        (a.asHom ≫ selectedFirst S spine) ≫ r := by rw [hlr, ha]
    _ = a.asHom ≫ c.asHom := by
      simp only [c, Category.assoc]
    _ = c.asHom ≫ a.asHom := hcommHom
    _ = selectedFirst S spine ≫ (r ≫ a.asHom) := by
      simp only [c, Category.assoc]

/-- The chosen split-basic presentation of the exact selected Figure-14
quotient. -/
abbrev selectedQuotientSplitBasic
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :=
  (selectedSplitBasic S spine).quotient_of_le_jacobson
    (selectedRelationIdeal S spine P Q)
    (selectedRelationIdeal_le_jacobson S spine P Q)

omit [IsAlgClosed k] in
/-- A quotient by a radical ideal does not identify two distinct selected
primitive-projective objects. -/
private theorem selectedQuotientFunctor_obj_ne_of_ne
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as)
    {X Y : (selectedSplitBasic S spine).ProjectiveCategory}
    (hXY : X ≠ Y) :
    (selectedQuotientFunctor S spine P Q).obj X ≠
      (selectedQuotientFunctor S spine P Q).obj Y := by
  intro h
  apply hXY
  apply (selectedSplitBasic S spine).projectiveVertex_injective
  have hv := congrArg
    (selectedQuotientSplitBasic S spine P Q).projectiveVertex h
  simpa only
      [SplitBasicIdempotents.projectiveQuotientFunctor_obj_projectiveVertex]
    using hv

/-- The two inner Figure-14 objects remain distinct in the exact quotient. -/
theorem factorBranch_quotientRightInner_ne_leftInner
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (selectedQuotientFunctor S spine P Q).obj
        (selectedRightInnerObj S spine) ≠
      (selectedQuotientFunctor S spine P Q).obj
        (selectedLeftInnerObj S spine) :=
  selectedQuotientFunctor_obj_ne_of_ne S spine P Q
    (factorBranch_selectedRightInner_ne_leftInner S hfinite spine)

/-- The initial Figure-14 pair remains distinct in the exact quotient. -/
theorem factorBranch_quotientLeftInner_ne_initial
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (selectedQuotientFunctor S spine P Q).obj
        (selectedLeftInnerObj S spine) ≠
      (selectedQuotientFunctor S spine P Q).obj
        (selectedInitialObj S spine) :=
  selectedQuotientFunctor_obj_ne_of_ne S spine P Q
    (factorBranch_selectedLeftInner_ne_initial S hfinite spine)

/-- The terminal Figure-14 pair remains distinct in the exact quotient. -/
theorem factorBranch_quotientTerminal_ne_rightInner
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (Q : OrientedRadicalPowerParameter
      (k := k) spine.rightInner.obj.as) :
    (selectedQuotientFunctor S spine P Q).obj
        (selectedTerminalObj S spine) ≠
      (selectedQuotientFunctor S spine P Q).obj
        (selectedRightInnerObj S spine) :=
  selectedQuotientFunctor_obj_ne_of_ne S spine P Q
    (factorBranch_selectedTerminal_ne_rightInner S hfinite spine)

/-- The middle generator remains full in the exact selected Figure-14
quotient. -/
theorem factorBranch_quotientMiddle_span_eq_top
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    twoSidedEndomorphismSpan k
      ((selectedQuotientFunctor S spine P Q).map
        (selectedMiddle S spine)) = ⊤ := by
  dsimp only
  exact LargeIndecomposable.fullLinearFunctor_map_span_eq_top
    (selectedQuotientFunctor S spine P
      (spine.middleCompReverseRadicalPowerParameter
        S hfinite P lambda hfactor))
    (selectedMiddle S spine)
    (factorBranch_selectedMiddle_span_eq_top S hfinite spine)

/-- The reverse generator remains full in the exact selected Figure-14
quotient. -/
theorem factorBranch_quotientLambda_span_eq_top
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    twoSidedEndomorphismSpan k
      ((selectedQuotientFunctor S spine P Q).map
        (selectedLambda S spine lambda)) = ⊤ := by
  dsimp only
  exact LargeIndecomposable.fullLinearFunctor_map_span_eq_top
    (selectedQuotientFunctor S spine P
      (spine.middleCompReverseRadicalPowerParameter
        S hfinite P lambda hfactor))
    (selectedLambda S spine lambda)
    (factorBranch_selectedLambda_span_eq_top
      S hfinite spine P lambda hfactor)

/-- The first outer generator remains full in the exact selected Figure-14
quotient. -/
theorem factorBranch_quotientFirst_span_eq_top
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    twoSidedEndomorphismSpan k
      ((selectedQuotientFunctor S spine P Q).map
        (selectedFirst S spine)) = ⊤ := by
  dsimp only
  exact LargeIndecomposable.fullLinearFunctor_map_span_eq_top
    (selectedQuotientFunctor S spine P
      (spine.middleCompReverseRadicalPowerParameter
        S hfinite P lambda hfactor))
    (selectedFirst S spine)
    (factorBranch_selectedFirst_span_eq_top S hfinite spine)

/-- The last outer generator remains full in the exact selected Figure-14
quotient. -/
theorem factorBranch_quotientLast_span_eq_top
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    twoSidedEndomorphismSpan k
      ((selectedQuotientFunctor S spine P Q).map
        (selectedLast S spine)) = ⊤ := by
  dsimp only
  exact LargeIndecomposable.fullLinearFunctor_map_span_eq_top
    (selectedQuotientFunctor S spine P
      (spine.middleCompReverseRadicalPowerParameter
        S hfinite P lambda hfactor))
    (selectedLast S spine)
    (factorBranch_selectedLast_span_eq_top S hfinite spine)

/-- The initial outer composite remains full in the exact quotient. -/
theorem factorBranch_quotientPrefix_span_eq_top
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    twoSidedEndomorphismSpan k
      (F.map (selectedMiddle S spine) ≫
        F.map (selectedFirst S spine)) = ⊤ := by
  dsimp only
  simpa only [Functor.map_comp] using
    (LargeIndecomposable.fullLinearFunctor_map_span_eq_top
      (selectedQuotientFunctor S spine P
        (spine.middleCompReverseRadicalPowerParameter
          S hfinite P lambda hfactor))
      (selectedMiddle S spine ≫ selectedFirst S spine)
      (factorBranch_selectedPrefix_span_eq_top S hfinite spine))

/-- The terminal outer composite remains full in the exact quotient. -/
theorem factorBranch_quotientSuffix_span_eq_top
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    twoSidedEndomorphismSpan k
      (F.map (selectedLast S spine) ≫
        F.map (selectedMiddle S spine)) = ⊤ := by
  dsimp only
  simpa only [Functor.map_comp] using
    (LargeIndecomposable.fullLinearFunctor_map_span_eq_top
      (selectedQuotientFunctor S spine P
        (spine.middleCompReverseRadicalPowerParameter
          S hfinite P lambda hfactor))
      (selectedLast S spine ≫ selectedMiddle S spine)
      (factorBranch_selectedSuffix_span_eq_top S hfinite spine))

/-- The image of the selected left parameter generates the full
endomorphism radical after imposing the exact Figure-14 relations. -/
theorem factorBranch_quotientLeftTau_span_eq_jacobson
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    twoSidedEndomorphismSpan k
        (End.of (F.map (selectedLeftTau S spine P))) =
      (Ring.jacobson
        (End (F.obj (selectedLeftInnerObj S spine)))).restrictScalars k := by
  dsimp only
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  let F := selectedQuotientFunctor S spine P Q
  letI : Module.Finite k
      (selectedCorner S spine ⧸
        (selectedRelationIdeal S spine P Q).asIdeal) :=
    Module.Finite.quotient k
      (selectedRelationIdeal S spine P Q).asIdeal
  let tauBar : End (F.obj (selectedLeftInnerObj S spine)) :=
    End.of (F.map (selectedLeftTau S spine P))
  have htauSelected : End.of (selectedLeftTau S spine P) ∈
      Ring.jacobson (End (selectedLeftInnerObj S spine)) := by
    have hmem : End.of (selectedLeftTau S spine P) ∈
        (Ring.jacobson
          (End (selectedLeftInnerObj S spine))).restrictScalars k := by
      rw [← factorBranch_selectedLeftTau_span_eq_jacobson S spine P]
      exact LargeIndecomposable.mem_twoSidedEndomorphismSpan k
        (End.of (selectedLeftTau S spine P))
    exact hmem
  have htauJ : tauBar ∈
      Ring.jacobson (End (F.obj (selectedLeftInnerObj S spine))) := by
    apply ((selectedQuotientSplitBasic S spine P Q).projectiveEnd_mem_jacobson_iff_val_mem_jacobson
        (F.obj (selectedLeftInnerObj S spine)) tauBar).2
    change Ideal.Quotient.mk
        (selectedRelationIdeal S spine P Q).asIdeal
          (selectedLeftTau S spine P).1 ∈
      Ring.jacobson
        (selectedCorner S spine ⧸
          (selectedRelationIdeal S spine P Q).asIdeal)
    rw [LargeIndecomposable.TwoSidedIdeal.quotient_mk_mem_jacobson_iff
      (selectedRelationIdeal S spine P Q)
      (selectedRelationIdeal_le_jacobson S spine P Q)]
    exact ((selectedSplitBasic S spine).projectiveEnd_mem_jacobson_iff_val_mem_jacobson
        (selectedLeftInnerObj S spine)
        (End.of (selectedLeftTau S spine P))).1 htauSelected
  change twoSidedEndomorphismSpan k tauBar = _
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro h ⟨a, b, rfl⟩
    have hring : b * tauBar * a ∈
        Ring.jacobson (End (F.obj (selectedLeftInnerObj S spine))) :=
      (Ring.jacobson
        (End (F.obj (selectedLeftInnerObj S spine)))).mul_mem_right a
          ((Ring.jacobson
            (End (F.obj (selectedLeftInnerObj S spine)))).mul_mem_left b htauJ)
    change End.of ((a.asHom ≫ tauBar.asHom) ≫ b.asHom) ∈
      Ring.jacobson (End (F.obj (selectedLeftInnerObj S spine)))
    rw [show End.of ((a.asHom ≫ tauBar.asHom) ≫ b.asHom) =
        b * tauBar * a by
      apply End.ext
      simp only [End.mul_def, Category.assoc]]
    exact hring
  · intro a ha
    obtain ⟨b, hb⟩ := F.map_surjective a
    have haVal : a.1 ∈
        Ring.jacobson
          (selectedCorner S spine ⧸
            (selectedRelationIdeal S spine P Q).asIdeal) :=
      ((selectedQuotientSplitBasic S spine P Q).projectiveEnd_mem_jacobson_iff_val_mem_jacobson
          (F.obj (selectedLeftInnerObj S spine)) (End.of a)).1 ha
    have hbQuotient : Ideal.Quotient.mk
        (selectedRelationIdeal S spine P Q).asIdeal b.1 ∈
          Ring.jacobson
            (selectedCorner S spine ⧸
              (selectedRelationIdeal S spine P Q).asIdeal) := by
      rw [← (selectedSplitBasic S spine).projectiveQuotientFunctor_map_val]
      change (F.map b).1 ∈ _
      rw [hb]
      exact haVal
    have hbVal : b.1 ∈ Ring.jacobson (selectedCorner S spine) :=
      (LargeIndecomposable.TwoSidedIdeal.quotient_mk_mem_jacobson_iff
        (selectedRelationIdeal S spine P Q)
        (selectedRelationIdeal_le_jacobson S spine P Q) b.1).1 hbQuotient
    have hbJ : End.of b ∈
        Ring.jacobson (End (selectedLeftInnerObj S spine)) :=
      ((selectedSplitBasic S spine).projectiveEnd_mem_jacobson_iff_val_mem_jacobson
          (selectedLeftInnerObj S spine) (End.of b)).2 hbVal
    have hbSpan : b ∈ twoSidedEndomorphismSpan k
        (selectedLeftTau S spine P) := by
      change End.of b ∈ twoSidedEndomorphismSpan k
        (End.of (selectedLeftTau S spine P))
      rw [factorBranch_selectedLeftTau_span_eq_jacobson S spine P]
      exact hbJ
    have hmap := LargeIndecomposable.linearFunctor_map_mem_twoSidedEndomorphismSpan
      (k := k) F hbSpan
    change F.map b ∈ twoSidedEndomorphismSpan k tauBar at hmap
    simpa only [hb] using hmap

/-- The left radical parameter survives the exact Figure-14 quotient. -/
theorem factorBranch_quotientLeftTau_ne_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    (selectedQuotientFunctor S spine P Q).map
      (selectedLeftTau S spine P) ≠ 0 := by
  dsimp only
  intro hzero
  apply factorBranch_selectedLeftTau_not_mem_selectedRelationIdeal
    S hfinite spine P lambda hfactor
  exact (((selectedSplitBasic S spine).projectiveQuotientFunctor_map_eq_zero_iff
    (selectedRelationIdeal S spine P
      (spine.middleCompReverseRadicalPowerParameter
        S hfinite P lambda hfactor))
    (selectedRelationIdeal_le_jacobson S spine P
      (spine.middleCompReverseRadicalPowerParameter
        S hfinite P lambda hfactor))
    (selectedLeftTau S spine P)).1 hzero)

/-- The surviving left cycle, with the quotient orientation supplied by
distributivity, is the left radical-power parameter for the Figure-14
coefficient compiler. -/
def factorBranch_quotientLeftPowerParameter
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    OrientedRadicalPowerParameter (k := k)
      ((selectedQuotientFunctor S spine P Q).obj
        (selectedLeftInnerObj S spine)) := by
  dsimp only
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  let F := selectedQuotientFunctor S spine P Q
  letI : Module.Finite k
      (selectedCorner S spine ⧸
        (selectedRelationIdeal S spine P Q).asIdeal) :=
    Module.Finite.quotient k
      (selectedRelationIdeal S spine P Q).asIdeal
  let tauBar : End (F.obj (selectedLeftInnerObj S spine)) :=
    End.of (F.map (selectedLeftTau S spine P))
  have hspan : twoSidedEndomorphismSpan k tauBar =
      (Ring.jacobson
        (End (F.obj (selectedLeftInnerObj S spine)))).restrictScalars k :=
    factorBranch_quotientLeftTau_span_eq_jacobson
      S hfinite spine P lambda hfactor
  have htauJ : tauBar ∈
      Ring.jacobson (End (F.obj (selectedLeftInnerObj S spine))) := by
    have hmem := LargeIndecomposable.mem_twoSidedEndomorphismSpan k tauBar
    rw [hspan] at hmem
    exact hmem
  have htau0 : tauBar ≠ 0 := by
    have hmap := factorBranch_quotientLeftTau_ne_zero
      S hfinite spine P lambda hfactor
    intro hzero
    apply hmap
    exact congrArg End.asHom hzero
  have horientSelected :
      LargeIndecomposable.AllowsTransit (selectedLeftTau S spine P) ∨
        LargeIndecomposable.AllowsCotransit
          (selectedLeftTau S spine P) := by
    rcases P.power_factorization with hT | hC
    · exact Or.inl (finsetProjectiveHom_allowsTransit (k := k) S
        (selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine) P.tau.asHom
        hT.allows_transit)
    · exact Or.inr (finsetProjectiveHom_allowsCotransit (k := k) S
        (selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine)
        (leftInner_mem_selectedVertices S spine) P.tau.asHom
        hC.allows_cotransit)
  have horientBar :
      LargeIndecomposable.AllowsTransit
          (F.map (selectedLeftTau S spine P)) ∨
        LargeIndecomposable.AllowsCotransit
          (F.map (selectedLeftTau S spine P)) := by
    rcases horientSelected with hT | hC
    · exact Or.inl
        (LargeIndecomposable.fullLinearFunctor_map_allowsTransit
          (k := k) F (selectedLeftTau S spine P) hT)
    · exact Or.inr
        (LargeIndecomposable.fullLinearFunctor_map_allowsCotransit
          (k := k) F (selectedLeftTau S spine P) hC)
  exact
    LargeIndecomposable.ClosedZigzagTransfer.orientedRadicalPowerParameter_of_span_eq
      tauBar htauJ htau0 hspan horientBar

@[simp]
theorem factorBranch_quotientLeftPowerParameter_tau
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    (factorBranch_quotientLeftPowerParameter
      S hfinite spine P lambda hfactor).tau =
        End.of ((selectedQuotientFunctor S spine P
          (spine.middleCompReverseRadicalPowerParameter
            S hfinite P lambda hfactor)).map
              (selectedLeftTau S spine P)) := by
  rfl

/-- The surviving right cycle generates the right-inner endomorphism
radical in the exact quotient. -/
theorem factorBranch_quotientRightTau_span_eq_jacobson
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    twoSidedEndomorphismSpan k
        (End.of (F.map (selectedRightTau S spine Q))) =
      (Ring.jacobson
        (End (F.obj (selectedRightInnerObj S spine)))).restrictScalars k := by
  dsimp only
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  letI : Module.Finite k
      (selectedCorner S spine ⧸
        (selectedRelationIdeal S spine P Q).asIdeal) :=
    Module.Finite.quotient k
      (selectedRelationIdeal S spine P Q).asIdeal
  simpa only using
    (selectedSplitBasic S spine).projectiveQuotientFunctor_end_span_eq_jacobson
      (selectedRelationIdeal S spine P Q)
      (selectedRelationIdeal_le_jacobson S spine P Q)
      (selectedRightInnerObj S spine)
      (End.of (selectedRightTau S spine Q))
      (selectedRightTau_span_eq_jacobson S spine Q)

/-- The right radical parameter survives the exact quotient. -/
theorem factorBranch_quotientRightTau_ne_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    (selectedQuotientFunctor S spine P Q).map
      (selectedRightTau S spine Q) ≠ 0 := by
  dsimp only
  intro hzero
  apply factorBranch_selectedRightTau_not_mem_selectedRelationIdeal
    S hfinite spine P lambda hfactor
  exact (((selectedSplitBasic S spine).projectiveQuotientFunctor_map_eq_zero_iff
    (selectedRelationIdeal S spine P
      (spine.middleCompReverseRadicalPowerParameter
        S hfinite P lambda hfactor))
    (selectedRelationIdeal_le_jacobson S spine P
      (spine.middleCompReverseRadicalPowerParameter
        S hfinite P lambda hfactor))
    (selectedRightTau S spine
      (spine.middleCompReverseRadicalPowerParameter
        S hfinite P lambda hfactor))).1 hzero)

/-- The quotient right cycle as an oriented radical-power parameter. -/
def factorBranch_quotientRightPowerParameter
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    OrientedRadicalPowerParameter (k := k)
      ((selectedQuotientFunctor S spine P Q).obj
        (selectedRightInnerObj S spine)) := by
  dsimp only
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  let F := selectedQuotientFunctor S spine P Q
  letI : Module.Finite k
      (selectedCorner S spine ⧸
        (selectedRelationIdeal S spine P Q).asIdeal) :=
    Module.Finite.quotient k
      (selectedRelationIdeal S spine P Q).asIdeal
  let tauBar : End (F.obj (selectedRightInnerObj S spine)) :=
    End.of (F.map (selectedRightTau S spine Q))
  have hspan : twoSidedEndomorphismSpan k tauBar =
      (Ring.jacobson
        (End (F.obj (selectedRightInnerObj S spine)))).restrictScalars k :=
    factorBranch_quotientRightTau_span_eq_jacobson
      S hfinite spine P lambda hfactor
  have htauJ : tauBar ∈
      Ring.jacobson (End (F.obj (selectedRightInnerObj S spine))) := by
    have hmem := LargeIndecomposable.mem_twoSidedEndomorphismSpan k tauBar
    rw [hspan] at hmem
    exact hmem
  have htau0 : tauBar ≠ 0 := by
    have hmap := factorBranch_quotientRightTau_ne_zero
      S hfinite spine P lambda hfactor
    intro hzero
    apply hmap
    exact congrArg End.asHom hzero
  have horientSelected :
      LargeIndecomposable.AllowsTransit (selectedRightTau S spine Q) ∨
        LargeIndecomposable.AllowsCotransit
          (selectedRightTau S spine Q) := by
    rcases Q.power_factorization with hT | hC
    · exact Or.inl (finsetProjectiveHom_allowsTransit (k := k) S
        (selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine) Q.tau.asHom
        hT.allows_transit)
    · exact Or.inr (finsetProjectiveHom_allowsCotransit (k := k) S
        (selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine)
        (rightInner_mem_selectedVertices S spine) Q.tau.asHom
        hC.allows_cotransit)
  have horientBar :
      LargeIndecomposable.AllowsTransit
          (F.map (selectedRightTau S spine Q)) ∨
        LargeIndecomposable.AllowsCotransit
          (F.map (selectedRightTau S spine Q)) := by
    rcases horientSelected with hT | hC
    · exact Or.inl
        (LargeIndecomposable.fullLinearFunctor_map_allowsTransit
          (k := k) F (selectedRightTau S spine Q) hT)
    · exact Or.inr
        (LargeIndecomposable.fullLinearFunctor_map_allowsCotransit
          (k := k) F (selectedRightTau S spine Q) hC)
  exact
    LargeIndecomposable.ClosedZigzagTransfer.orientedRadicalPowerParameter_of_span_eq
      tauBar htauJ htau0 hspan horientBar

@[simp]
theorem factorBranch_quotientRightPowerParameter_tau
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    (factorBranch_quotientRightPowerParameter
      S hfinite spine P lambda hfactor).tau =
        End.of ((selectedQuotientFunctor S spine P
          (spine.middleCompReverseRadicalPowerParameter
            S hfinite P lambda hfactor)).map
              (selectedRightTau S spine
                (spine.middleCompReverseRadicalPowerParameter
                  S hfinite P lambda hfactor))) := by
  rfl

set_option maxHeartbeats 800000 in
/-- The surviving reverse generator cannot acquire a factorization through
the initial object in the exact selected quotient. -/
theorem factorBranch_quotientLambda_not_factorsThrough_initial
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    ¬ ∃ (l : F.obj (selectedLeftInnerObj S spine) ⟶
          F.obj (selectedInitialObj S spine))
        (r : F.obj (selectedInitialObj S spine) ⟶
          F.obj (selectedRightInnerObj S spine)),
      F.map (selectedLambda S spine lambda) = l ≫ r := by
  dsimp only
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  let T := selectedSplitBasic S spine
  let I := selectedRelationIdeal S spine P Q
  let F := selectedQuotientFunctor S spine P Q
  letI : LargeIndecomposable.HasBGRSDistributiveHomStructure k
      T.ProjectiveCategory :=
    LargeIndecomposable.HasBGRSDistributiveHomStructure.of_fullyFaithful
      (selectedProjectiveFunctor S spine)
  rintro ⟨lbar, rbar, hbar⟩
  have hIcorner : finiteIdealCorner T I
        (selectedLeftInnerObj S spine) (selectedRightInnerObj S spine) ≤
      twoSidedEndomorphismSpan k
        (selectedLambda S spine lambda) := by
    intro g _
    rw [factorBranch_selectedLambda_span_eq_top
      S hfinite spine P lambda hfactor]
    exact Submodule.mem_top
  have hlambdaSurvives : F.map (selectedLambda S spine lambda) ≠ 0 := by
    intro hz
    apply factorBranch_selectedQuotientFunctor_map_threefold_ne_zero
      S hfinite spine P lambda hfactor
    change F.map (selectedMiddle S spine ≫
      selectedLambda S spine lambda ≫ selectedMiddle S spine) = 0
    rw [Functor.map_comp, Functor.map_comp, hz,
      CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]
  obtain ⟨l, r, hlr⟩ :=
    factorsThrough_of_projectiveQuotientFunctor_map_factorsThrough
      T I (selectedRelationIdeal_le_jacobson S spine P Q)
      (selectedLambda S spine lambda) hIcorner hlambdaSurvives
      lbar rbar hbar
  exact factorBranch_selectedLambda_not_factorsThrough_initial
    S hfinite spine P lambda hfactor ⟨l, r, hlr⟩

set_option maxHeartbeats 800000 in
/-- The surviving left local cycle cannot acquire a factorization through the
initial object in the exact selected quotient. -/
theorem factorBranch_quotientLeftTau_not_factorsThrough_initial
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    ¬ ∃ (l : F.obj (selectedLeftInnerObj S spine) ⟶
          F.obj (selectedInitialObj S spine))
        (r : F.obj (selectedInitialObj S spine) ⟶
          F.obj (selectedLeftInnerObj S spine)),
      F.map (selectedLeftTau S spine P) = l ≫ r := by
  dsimp only
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  let T := selectedSplitBasic S spine
  let I := selectedRelationIdeal S spine P Q
  let F := selectedQuotientFunctor S spine P Q
  letI : LargeIndecomposable.HasBGRSDistributiveHomStructure k
      T.ProjectiveCategory :=
    LargeIndecomposable.HasBGRSDistributiveHomStructure.of_fullyFaithful
      (selectedProjectiveFunctor S spine)
  rintro ⟨lbar, rbar, hbar⟩
  have hIcorner : finiteIdealCorner T I
        (selectedLeftInnerObj S spine) (selectedLeftInnerObj S spine) ≤
      twoSidedEndomorphismSpan k (selectedLeftTau S spine P) := by
    intro g hg
    have hgVal : g.1 ∈ Ring.jacobson (selectedCorner S spine) :=
      selectedRelationIdeal_le_jacobson S spine P Q hg
    have hgEnd : End.of g ∈
        Ring.jacobson (End (selectedLeftInnerObj S spine)) :=
      ((selectedSplitBasic S spine).projectiveEnd_mem_jacobson_iff_val_mem_jacobson
        (selectedLeftInnerObj S spine) (End.of g)).2 hgVal
    change End.of g ∈ twoSidedEndomorphismSpan k
      (End.of (selectedLeftTau S spine P))
    rw [factorBranch_selectedLeftTau_span_eq_jacobson S spine P]
    exact hgEnd
  obtain ⟨l, r, hlr⟩ :=
    factorsThrough_of_projectiveQuotientFunctor_map_factorsThrough
      T I (selectedRelationIdeal_le_jacobson S spine P Q)
      (selectedLeftTau S spine P) hIcorner
      (factorBranch_quotientLeftTau_ne_zero
        S hfinite spine P lambda hfactor) lbar rbar hbar
  exact factorBranch_selectedLeftTau_not_factorsThrough_initial
    S hfinite spine P ⟨l, r, hlr⟩

set_option maxHeartbeats 800000 in
/-- The surviving reverse generator cannot acquire a factorization through
the terminal object in the exact selected quotient. -/
theorem factorBranch_quotientLambda_not_factorsThrough_terminal
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    ¬ ∃ (l : F.obj (selectedLeftInnerObj S spine) ⟶
          F.obj (selectedTerminalObj S spine))
        (r : F.obj (selectedTerminalObj S spine) ⟶
          F.obj (selectedRightInnerObj S spine)),
      F.map (selectedLambda S spine lambda) = l ≫ r := by
  dsimp only
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  let T := selectedSplitBasic S spine
  let I := selectedRelationIdeal S spine P Q
  let F := selectedQuotientFunctor S spine P Q
  letI : LargeIndecomposable.HasBGRSDistributiveHomStructure k
      T.ProjectiveCategory :=
    LargeIndecomposable.HasBGRSDistributiveHomStructure.of_fullyFaithful
      (selectedProjectiveFunctor S spine)
  rintro ⟨lbar, rbar, hbar⟩
  have hIcorner : finiteIdealCorner T I
        (selectedLeftInnerObj S spine) (selectedRightInnerObj S spine) ≤
      twoSidedEndomorphismSpan k
        (selectedLambda S spine lambda) := by
    intro g _
    rw [factorBranch_selectedLambda_span_eq_top
      S hfinite spine P lambda hfactor]
    exact Submodule.mem_top
  have hlambdaSurvives : F.map (selectedLambda S spine lambda) ≠ 0 := by
    intro hz
    apply factorBranch_selectedQuotientFunctor_map_threefold_ne_zero
      S hfinite spine P lambda hfactor
    change F.map (selectedMiddle S spine ≫
      selectedLambda S spine lambda ≫ selectedMiddle S spine) = 0
    rw [Functor.map_comp, Functor.map_comp, hz,
      CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]
  obtain ⟨l, r, hlr⟩ :=
    factorsThrough_of_projectiveQuotientFunctor_map_factorsThrough
      T I (selectedRelationIdeal_le_jacobson S spine P Q)
      (selectedLambda S spine lambda) hIcorner hlambdaSurvives
      lbar rbar hbar
  exact factorBranch_selectedLambda_not_factorsThrough_terminal
    S hfinite spine P lambda hfactor ⟨l, r, hlr⟩

set_option maxHeartbeats 800000 in
/-- The surviving right local cycle cannot acquire a factorization through
the terminal object in the exact selected quotient. -/
theorem factorBranch_quotientRightTau_not_factorsThrough_terminal
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    ¬ ∃ (l : F.obj (selectedRightInnerObj S spine) ⟶
          F.obj (selectedTerminalObj S spine))
        (r : F.obj (selectedTerminalObj S spine) ⟶
          F.obj (selectedRightInnerObj S spine)),
      F.map (selectedRightTau S spine Q) = l ≫ r := by
  dsimp only
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  let T := selectedSplitBasic S spine
  let I := selectedRelationIdeal S spine P Q
  let F := selectedQuotientFunctor S spine P Q
  letI : LargeIndecomposable.HasBGRSDistributiveHomStructure k
      T.ProjectiveCategory :=
    LargeIndecomposable.HasBGRSDistributiveHomStructure.of_fullyFaithful
      (selectedProjectiveFunctor S spine)
  rintro ⟨lbar, rbar, hbar⟩
  have hIcorner : finiteIdealCorner T I
        (selectedRightInnerObj S spine) (selectedRightInnerObj S spine) ≤
      twoSidedEndomorphismSpan k (selectedRightTau S spine Q) := by
    intro g hg
    have hgVal : g.1 ∈ Ring.jacobson (selectedCorner S spine) :=
      selectedRelationIdeal_le_jacobson S spine P Q hg
    have hgEnd : End.of g ∈
        Ring.jacobson (End (selectedRightInnerObj S spine)) :=
      ((selectedSplitBasic S spine).projectiveEnd_mem_jacobson_iff_val_mem_jacobson
        (selectedRightInnerObj S spine) (End.of g)).2 hgVal
    change End.of g ∈ twoSidedEndomorphismSpan k
      (End.of (selectedRightTau S spine Q))
    rw [selectedRightTau_span_eq_jacobson S spine Q]
    exact hgEnd
  obtain ⟨l, r, hlr⟩ :=
    factorsThrough_of_projectiveQuotientFunctor_map_factorsThrough
      T I (selectedRelationIdeal_le_jacobson S spine P Q)
      (selectedRightTau S spine Q) hIcorner
      (factorBranch_quotientRightTau_ne_zero
        S hfinite spine P lambda hfactor) lbar rbar hbar
  exact factorBranch_selectedRightTau_not_factorsThrough_terminal
    S hfinite spine Q ⟨l, r, hlr⟩

/-- The quotient left parameter is literally the surviving central cycle. -/
theorem factorBranch_quotient_left_cycle
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    (factorBranch_quotientLeftPowerParameter
      S hfinite spine P lambda hfactor).tau.asHom =
        F.map (selectedLambda S spine lambda) ≫
          F.map (selectedMiddle S spine) := by
  dsimp only
  rw [factorBranch_quotientLeftPowerParameter_tau]
  change (selectedQuotientFunctor S spine P
      (spine.middleCompReverseRadicalPowerParameter
        S hfinite P lambda hfactor)).map
      (selectedLeftTau S spine P) = _
  rw [← Functor.map_comp, factorBranch_selected_left_cycle
    S spine P lambda hfactor]

/-- The quotient right parameter is literally the surviving opposite
central cycle. -/
theorem factorBranch_quotient_right_cycle
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    (factorBranch_quotientRightPowerParameter
      S hfinite spine P lambda hfactor).tau.asHom =
        F.map (selectedMiddle S spine) ≫
          F.map (selectedLambda S spine lambda) := by
  dsimp only
  rw [factorBranch_quotientRightPowerParameter_tau]
  change (selectedQuotientFunctor S spine P
      (spine.middleCompReverseRadicalPowerParameter
        S hfinite P lambda hfactor)).map
      (selectedRightTau S spine
        (spine.middleCompReverseRadicalPowerParameter
          S hfinite P lambda hfactor)) = _
  rw [← Functor.map_comp, factorBranch_selected_right_cycle
    S hfinite spine P lambda hfactor]

/-- The quotient middle arrow retains both transit directions. -/
theorem factorBranch_quotientMiddle_allowsBitransit
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    LargeIndecomposable.AllowsTransit
        ((selectedQuotientFunctor S spine P Q).map
          (selectedMiddle S spine)) ∧
      LargeIndecomposable.AllowsCotransit
        ((selectedQuotientFunctor S spine P Q).map
          (selectedMiddle S spine)) := by
  dsimp only
  have hmiddle := factorBranch_selectedMiddle_allowsBitransit
    S hfinite spine
  exact
    ⟨LargeIndecomposable.fullLinearFunctor_map_allowsTransit
        (k := k)
        (selectedQuotientFunctor S spine P
          (spine.middleCompReverseRadicalPowerParameter
            S hfinite P lambda hfactor))
        (selectedMiddle S spine) hmiddle.1,
      LargeIndecomposable.fullLinearFunctor_map_allowsCotransit
        (k := k)
        (selectedQuotientFunctor S spine P
          (spine.middleCompReverseRadicalPowerParameter
            S hfinite P lambda hfactor))
        (selectedMiddle S spine) hmiddle.2⟩

/-- The quotient reverse arrow retains transit. -/
theorem factorBranch_quotientLambda_allowsTransit
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    LargeIndecomposable.AllowsTransit
      ((selectedQuotientFunctor S spine P Q).map
        (selectedLambda S spine lambda)) := by
  dsimp only
  exact LargeIndecomposable.fullLinearFunctor_map_allowsTransit
    (k := k)
    (selectedQuotientFunctor S spine P
      (spine.middleCompReverseRadicalPowerParameter
        S hfinite P lambda hfactor))
    (selectedLambda S spine lambda)
    (factorBranch_selectedLambda_allowsTransit S spine P lambda hfactor)

/-- The first outer quotient arrow retains cotransit. -/
theorem factorBranch_quotientFirst_allowsCotransit
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    LargeIndecomposable.AllowsCotransit
      ((selectedQuotientFunctor S spine P Q).map
        (selectedFirst S spine)) := by
  dsimp only
  exact LargeIndecomposable.fullLinearFunctor_map_allowsCotransit
    (k := k)
    (selectedQuotientFunctor S spine P
      (spine.middleCompReverseRadicalPowerParameter
        S hfinite P lambda hfactor))
    (selectedFirst S spine)
    (factorBranch_selectedFirst_allowsCotransit S spine)

/-- The last outer quotient arrow retains transit. -/
theorem factorBranch_quotientLast_allowsTransit
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    LargeIndecomposable.AllowsTransit
      ((selectedQuotientFunctor S spine P Q).map
        (selectedLast S spine)) := by
  dsimp only
  exact LargeIndecomposable.fullLinearFunctor_map_allowsTransit
    (k := k)
    (selectedQuotientFunctor S spine P
      (spine.middleCompReverseRadicalPowerParameter
        S hfinite P lambda hfactor))
    (selectedLast S spine)
    (factorBranch_selectedLast_allowsTransit S spine)

/-- The initial outer composite allows cotransit in the exact quotient. -/
theorem factorBranch_quotientPrefix_allowsCotransit
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    LargeIndecomposable.AllowsCotransit
      (F.map (selectedMiddle S spine) ≫
        F.map (selectedFirst S spine)) := by
  dsimp only
  exact (factorBranch_quotientMiddle_allowsBitransit
    S hfinite spine P lambda hfactor).2.comp
      (factorBranch_quotientFirst_allowsCotransit
        S hfinite spine P lambda hfactor)

/-- The terminal outer composite allows transit in the exact quotient. -/
theorem factorBranch_quotientSuffix_allowsTransit
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    LargeIndecomposable.AllowsTransit
      (F.map (selectedLast S spine) ≫
        F.map (selectedMiddle S spine)) := by
  dsimp only
  exact (factorBranch_quotientLast_allowsTransit
    S hfinite spine P lambda hfactor).comp
      (factorBranch_quotientMiddle_allowsBitransit
        S hfinite spine P lambda hfactor).1

set_option maxHeartbeats 800000 in
/-- Every quotient morphism from the right-inner object to the initial
object is killed when preceded by the reverse central arrow. -/
theorem factorBranch_quotient_lambda_comp_to_initial_eq_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    ∀ g : F.obj (selectedRightInnerObj S spine) ⟶
        F.obj (selectedInitialObj S spine),
      F.map (selectedLambda S spine lambda) ≫ g = 0 := by
  dsimp only
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  let F := selectedQuotientFunctor S spine P Q
  let Pbar := factorBranch_quotientLeftPowerParameter
    S hfinite spine P lambda hfactor
  let delta := F.map (selectedMiddle S spine)
  let lambdaBar := F.map (selectedLambda S spine lambda)
  let first := F.map (selectedFirst S spine)
  let Ybar := F.obj (selectedLeftInnerObj S spine)
  letI : Module.Finite k
      (selectedCorner S spine ⧸
        (selectedRelationIdeal S spine P Q).asIdeal) :=
    Module.Finite.quotient k
      (selectedRelationIdeal S spine P Q).asIdeal
  letI : Module.Finite k (End Ybar) := by
    change Module.Finite k (Ybar ⟶ Ybar)
    infer_instance
  have hprefixSpan : twoSidedEndomorphismSpan k
      (delta ≫ first) = ⊤ :=
    factorBranch_quotientPrefix_span_eq_top
      S hfinite spine P lambda hfactor
  have hprefixC : LargeIndecomposable.AllowsCotransit
      (delta ≫ first) :=
    factorBranch_quotientPrefix_allowsCotransit
      S hfinite spine P lambda hfactor
  have hdeltaT : LargeIndecomposable.AllowsTransit delta :=
    (factorBranch_quotientMiddle_allowsBitransit
      S hfinite spine P lambda hfactor).1
  have hsigma : Pbar.tau.asHom = lambdaBar ≫ delta :=
    factorBranch_quotient_left_cycle
      S hfinite spine P lambda hfactor
  have htauFirst : Pbar.tau.asHom ≫ first = 0 := by
    rw [factorBranch_quotientLeftPowerParameter_tau]
    change F.map (selectedLeftTau S spine P) ≫ first = 0
    rw [← Functor.map_comp]
    exact selectedQuotientFunctor_map_initial_relation_eq_zero
      S spine P Q
  intro g
  have hg : g ∈ twoSidedEndomorphismSpan k (delta ≫ first) := by
    rw [hprefixSpan]
    exact Submodule.mem_top
  obtain ⟨a, rfl⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsCotransit
      (k := k) hprefixC hg
  obtain ⟨b, hab⟩ := hdeltaT a
  have hcomm : Pbar.tau.asHom ≫ b.asHom =
      b.asHom ≫ Pbar.tau.asHom := by
    simpa only [End.mul_def] using congrArg End.asHom
      (Pbar.mul_comm b Pbar.tau)
  calc
    lambdaBar ≫ (a.asHom ≫ (delta ≫ first)) =
        (lambdaBar ≫ (a.asHom ≫ delta)) ≫ first := by
          simp only [Category.assoc]
    _ = (lambdaBar ≫ (delta ≫ b.asHom)) ≫ first := by
          rw [hab]
    _ = (Pbar.tau.asHom ≫ b.asHom) ≫ first := by
          rw [hsigma]
          simp only [Category.assoc]
    _ = (b.asHom ≫ Pbar.tau.asHom) ≫ first := by rw [hcomm]
    _ = b.asHom ≫ (Pbar.tau.asHom ≫ first) := by
          simp only [Category.assoc]
    _ = 0 := by rw [htauFirst]; simp

set_option maxHeartbeats 800000 in
/-- Dually, every quotient morphism from the terminal object to the
left-inner object is killed when followed by the reverse central arrow. -/
theorem factorBranch_quotient_from_terminal_comp_lambda_eq_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    ∀ g : F.obj (selectedTerminalObj S spine) ⟶
        F.obj (selectedLeftInnerObj S spine),
      g ≫ F.map (selectedLambda S spine lambda) = 0 := by
  dsimp only
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  let F := selectedQuotientFunctor S spine P Q
  let Qbar := factorBranch_quotientRightPowerParameter
    S hfinite spine P lambda hfactor
  let last := F.map (selectedLast S spine)
  let delta := F.map (selectedMiddle S spine)
  let lambdaBar := F.map (selectedLambda S spine lambda)
  have hsuffixSpan : twoSidedEndomorphismSpan k
      (last ≫ delta) = ⊤ :=
    factorBranch_quotientSuffix_span_eq_top
      S hfinite spine P lambda hfactor
  have hsuffixT : LargeIndecomposable.AllowsTransit
      (last ≫ delta) :=
    factorBranch_quotientSuffix_allowsTransit
      S hfinite spine P lambda hfactor
  have hlambdaT : LargeIndecomposable.AllowsTransit lambdaBar :=
    factorBranch_quotientLambda_allowsTransit
      S hfinite spine P lambda hfactor
  have hrho : Qbar.tau.asHom = delta ≫ lambdaBar :=
    factorBranch_quotient_right_cycle
      S hfinite spine P lambda hfactor
  have hlastTau : last ≫ Qbar.tau.asHom = 0 := by
    rw [factorBranch_quotientRightPowerParameter_tau]
    change last ≫ F.map (selectedRightTau S spine Q) = 0
    rw [← Functor.map_comp]
    exact selectedQuotientFunctor_map_terminal_relation_eq_zero
      S spine P Q
  intro g
  have hg : g ∈ twoSidedEndomorphismSpan k (last ≫ delta) := by
    rw [hsuffixSpan]
    exact Submodule.mem_top
  obtain ⟨b, rfl⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit
      (k := k) hsuffixT hg
  obtain ⟨a, hba⟩ := hlambdaT b
  calc
    ((last ≫ delta) ≫ b.asHom) ≫ lambdaBar =
        last ≫ delta ≫ (b.asHom ≫ lambdaBar) := by
          simp only [Category.assoc]
    _ = last ≫ delta ≫ (lambdaBar ≫ a.asHom) := by rw [hba]
    _ = (last ≫ Qbar.tau.asHom) ≫ a.asHom := by
          rw [hrho]
          simp only [Category.assoc]
    _ = 0 := by rw [hlastTau]; simp

/-- The initial-arm arrow coefficient therefore vanishes on every reverse
central arrow followed by a morphism to the initial object. -/
theorem factorBranch_quotientInitial_betaZero_lambda_comp_eq_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    let T := selectedQuotientSplitBasic S spine P Q
    ∀ arm : Figure14ArmCoefficientData
        (F.map (selectedMiddle S spine))
        (F.map (selectedFirst S spine))
        (T.projectiveEndResidue
          (F.obj (selectedRightInnerObj S spine)))
        (T.projectiveEndResidue
          (F.obj (selectedLeftInnerObj S spine)))
        (T.projectiveEndResidue
          (F.obj (selectedInitialObj S spine))),
    ∀ g : F.obj (selectedRightInnerObj S spine) ⟶
        F.obj (selectedInitialObj S spine),
      arm.betaZero
        (F.map (selectedLambda S spine lambda) ≫ g) = 0 := by
  dsimp only
  intro arm g
  rw [factorBranch_quotient_lambda_comp_to_initial_eq_zero
    S hfinite spine P lambda hfactor g]
  exact arm.betaZero.map_zero

/-- The terminal-arm arrow coefficient vanishes on every morphism from the
terminal object followed by the reverse central arrow. -/
theorem factorBranch_quotientTerminal_alphaZero_comp_lambda_eq_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    let T := selectedQuotientSplitBasic S spine P Q
    ∀ arm : Figure14ArmCoefficientData
        (F.map (selectedLast S spine))
        (F.map (selectedMiddle S spine))
        (T.projectiveEndResidue
          (F.obj (selectedTerminalObj S spine)))
        (T.projectiveEndResidue
          (F.obj (selectedRightInnerObj S spine)))
        (T.projectiveEndResidue
          (F.obj (selectedLeftInnerObj S spine))),
    ∀ g : F.obj (selectedTerminalObj S spine) ⟶
        F.obj (selectedLeftInnerObj S spine),
      arm.alphaZero
        (g ≫ F.map (selectedLambda S spine lambda)) = 0 := by
  dsimp only
  intro arm g
  rw [factorBranch_quotient_from_terminal_comp_lambda_eq_zero
    S hfinite spine P lambda hfactor g]
  exact arm.alphaZero.map_zero

/-- Every radical endomorphism at the left-inner quotient vertex is killed
when followed by the first outer arrow. -/
theorem factorBranch_quotient_initial_radical_action_eq_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    ∀ a : End (F.obj (selectedLeftInnerObj S spine)),
      a ∈ Ring.jacobson (End (F.obj (selectedLeftInnerObj S spine))) →
        a.asHom ≫ F.map (selectedFirst S spine) = 0 := by
  dsimp only
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  let F := selectedQuotientFunctor S spine P Q
  let Pbar := factorBranch_quotientLeftPowerParameter
    S hfinite spine P lambda hfactor
  letI : Module.Finite k
      (selectedCorner S spine ⧸
        (selectedRelationIdeal S spine P Q).asIdeal) :=
    Module.Finite.quotient k
      (selectedRelationIdeal S spine P Q).asIdeal
  letI : Module.Finite k
      (End (F.obj (selectedLeftInnerObj S spine))) := by
    change Module.Finite k
      (F.obj (selectedLeftInnerObj S spine) ⟶
        F.obj (selectedLeftInnerObj S spine))
    infer_instance
  have htauFirst : Pbar.tau.asHom ≫
      F.map (selectedFirst S spine) = 0 := by
    rw [factorBranch_quotientLeftPowerParameter_tau]
    change F.map (selectedLeftTau S spine P) ≫
      F.map (selectedFirst S spine) = 0
    rw [← Functor.map_comp]
    exact selectedQuotientFunctor_map_initial_relation_eq_zero S spine P Q
  intro a ha
  obtain ⟨q, hq⟩ := Pbar.cotransitData.generates a ha
  rw [hq, Category.assoc, htauFirst]
  simp

set_option maxHeartbeats 800000 in
/-- Inserting an invertible left-inner endomorphism cannot kill the initial
length-two arm in the exact quotient. -/
theorem factorBranch_quotient_initial_unit_sandwich_ne_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    ∀ a : End (F.obj (selectedLeftInnerObj S spine)), IsUnit a →
      (F.map (selectedMiddle S spine) ≫ a.asHom) ≫
        F.map (selectedFirst S spine) ≠ 0 := by
  dsimp only
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  let F := selectedQuotientFunctor S spine P Q
  let T := selectedQuotientSplitBasic S spine P Q
  let Ybar := F.obj (selectedLeftInnerObj S spine)
  let first := F.map (selectedFirst S spine)
  let delta := F.map (selectedMiddle S spine)
  letI : Module.Finite k
      (selectedCorner S spine ⧸
        (selectedRelationIdeal S spine P Q).asIdeal) :=
    Module.Finite.quotient k
      (selectedRelationIdeal S spine P Q).asIdeal
  intro a ha
  let c : k := T.projectiveEndResidue Ybar a
  let n : End Ybar := a - c • 1
  have hc : c ≠ 0 :=
    (T.projectiveEnd_isUnit_iff_residue_ne_zero Ybar a).1 ha
  have hnResidue : T.projectiveEndResidue Ybar n = 0 := by
    dsimp only [n, c]
    rw [map_sub, map_smul, map_one, smul_eq_mul, mul_one, sub_self]
  have hnJ : n ∈ Ring.jacobson (End Ybar) := by
    rw [T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson,
      ← T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson]
    exact hnResidue
  have hnFirst : n.asHom ≫ first = 0 :=
    factorBranch_quotient_initial_radical_action_eq_zero
      S hfinite spine P lambda hfactor n hnJ
  have haFirst : a.asHom ≫ first = c • first := by
    change (a.asHom - c • (𝟙 Ybar)) ≫ first = 0 at hnFirst
    rw [Preadditive.sub_comp, Linear.smul_comp, Category.id_comp] at hnFirst
    exact sub_eq_zero.mp hnFirst
  have hprefix : delta ≫ first ≠ 0 := by
    simpa only [delta, first, Functor.map_comp] using
      (factorBranch_selectedQuotientFunctor_map_prefix_ne_zero
        S hfinite spine P lambda hfactor)
  rw [Category.assoc, haFirst]
  change delta ≫ (c • first) ≠ 0
  rw [Linear.comp_smul]
  exact smul_ne_zero hc hprefix

/-- Every radical endomorphism at the right-inner quotient vertex is killed
when preceded by the last outer arrow. -/
theorem factorBranch_quotient_terminal_radical_action_eq_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    ∀ a : End (F.obj (selectedRightInnerObj S spine)),
      a ∈ Ring.jacobson (End (F.obj (selectedRightInnerObj S spine))) →
        F.map (selectedLast S spine) ≫ a.asHom = 0 := by
  dsimp only
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  let F := selectedQuotientFunctor S spine P Q
  let Pbar := factorBranch_quotientRightPowerParameter
    S hfinite spine P lambda hfactor
  letI : Module.Finite k
      (selectedCorner S spine ⧸
        (selectedRelationIdeal S spine P Q).asIdeal) :=
    Module.Finite.quotient k
      (selectedRelationIdeal S spine P Q).asIdeal
  letI : Module.Finite k
      (End (F.obj (selectedRightInnerObj S spine))) := by
    change Module.Finite k
      (F.obj (selectedRightInnerObj S spine) ⟶
        F.obj (selectedRightInnerObj S spine))
    infer_instance
  have hlastTau : F.map (selectedLast S spine) ≫
      Pbar.tau.asHom = 0 := by
    rw [factorBranch_quotientRightPowerParameter_tau]
    change F.map (selectedLast S spine) ≫
      F.map (selectedRightTau S spine Q) = 0
    rw [← Functor.map_comp]
    exact selectedQuotientFunctor_map_terminal_relation_eq_zero S spine P Q
  intro a ha
  obtain ⟨q, hq⟩ := Pbar.transitData.generates a ha
  rw [hq, ← Category.assoc, hlastTau]
  simp

set_option maxHeartbeats 800000 in
/-- Inserting an invertible right-inner endomorphism cannot kill the
terminal length-two arm in the exact quotient. -/
theorem factorBranch_quotient_terminal_unit_sandwich_ne_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    ∀ a : End (F.obj (selectedRightInnerObj S spine)), IsUnit a →
      (F.map (selectedLast S spine) ≫ a.asHom) ≫
        F.map (selectedMiddle S spine) ≠ 0 := by
  dsimp only
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  let F := selectedQuotientFunctor S spine P Q
  let T := selectedQuotientSplitBasic S spine P Q
  let Xbar := F.obj (selectedRightInnerObj S spine)
  let last := F.map (selectedLast S spine)
  let delta := F.map (selectedMiddle S spine)
  letI : Module.Finite k
      (selectedCorner S spine ⧸
        (selectedRelationIdeal S spine P Q).asIdeal) :=
    Module.Finite.quotient k
      (selectedRelationIdeal S spine P Q).asIdeal
  intro a ha
  let c : k := T.projectiveEndResidue Xbar a
  let n : End Xbar := a - c • 1
  have hc : c ≠ 0 :=
    (T.projectiveEnd_isUnit_iff_residue_ne_zero Xbar a).1 ha
  have hnResidue : T.projectiveEndResidue Xbar n = 0 := by
    dsimp only [n, c]
    rw [map_sub, map_smul, map_one, smul_eq_mul, mul_one, sub_self]
  have hnJ : n ∈ Ring.jacobson (End Xbar) := by
    rw [T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson,
      ← T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson]
    exact hnResidue
  have hlastN : last ≫ n.asHom = 0 :=
    factorBranch_quotient_terminal_radical_action_eq_zero
      S hfinite spine P lambda hfactor n hnJ
  have hlastA : last ≫ a.asHom = c • last := by
    change last ≫ (a.asHom - c • (𝟙 Xbar)) = 0 at hlastN
    rw [Preadditive.comp_sub, Linear.comp_smul, Category.comp_id] at hlastN
    exact sub_eq_zero.mp hlastN
  have hsuffix : last ≫ delta ≠ 0 := by
    simpa only [last, delta, Functor.map_comp] using
      (factorBranch_selectedQuotientFunctor_map_suffix_ne_zero
        S hfinite spine P lambda hfactor)
  rw [hlastA]
  change (c • last) ≫ delta ≠ 0
  rw [Linear.smul_comp]
  exact smul_ne_zero hc hsuffix

/-- The exact quotient central alternating chain carries the coherent
degree-zero and degree-one coefficient package required by Figure 14. -/
theorem factorBranch_quotientCentralCoefficientData
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    let T := selectedQuotientSplitBasic S spine P Q
    let Pbar := factorBranch_quotientLeftPowerParameter
      S hfinite spine P lambda hfactor
    Nonempty (Figure14CentralCoefficientData
      (F.map (selectedMiddle S spine))
      (F.map (selectedLambda S spine lambda))
      (T.projectiveEndResidue
        (F.obj (selectedRightInnerObj S spine)))
      (T.projectiveEndResidue
        (F.obj (selectedLeftInnerObj S spine)))
      Pbar.tau) := by
  dsimp only
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  let F := selectedQuotientFunctor S spine P Q
  let T := selectedQuotientSplitBasic S spine P Q
  let Pbar := factorBranch_quotientLeftPowerParameter
    S hfinite spine P lambda hfactor
  let Xbar := F.obj (selectedRightInnerObj S spine)
  let Ybar := F.obj (selectedLeftInnerObj S spine)
  let residueX := T.projectiveEndResidue Xbar
  let residueY := T.projectiveEndResidue Ybar
  letI : Module.Finite k
      (selectedCorner S spine ⧸
        (selectedRelationIdeal S spine P Q).asIdeal) :=
    Module.Finite.quotient k
      (selectedRelationIdeal S spine P Q).asIdeal
  letI : LargeIndecomposable.HasBGRSDistributiveHomStructure k
      (selectedSplitBasic S spine).ProjectiveCategory :=
    LargeIndecomposable.HasBGRSDistributiveHomStructure.of_fullyFaithful
      (selectedProjectiveFunctor S spine)
  letI : ∀ Z : T.ProjectiveCategory, Module.Finite k (End Z) :=
    fun Z ↦ by
      change Module.Finite k (Z ⟶ Z)
      infer_instance
  have hresidueX (a : End Xbar) :
      residueX a = 0 ↔ a ∈ Ring.jacobson (End Xbar) := by
    dsimp only [residueX]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  have hresidueY (a : End Ybar) :
      residueY a = 0 ↔ a ∈ Ring.jacobson (End Ybar) := by
    dsimp only [residueY]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  have hsigma : Pbar.tau.asHom =
      F.map (selectedLambda S spine lambda) ≫
        F.map (selectedMiddle S spine) :=
    factorBranch_quotient_left_cycle S hfinite spine P lambda hfactor
  have hthree :
      F.map (selectedMiddle S spine) ≫
        F.map (selectedLambda S spine lambda) ≫
          F.map (selectedMiddle S spine) ≠ 0 := by
    simpa only [Functor.map_comp] using
      (factorBranch_selectedQuotientFunctor_map_threefold_ne_zero
        S hfinite spine P lambda hfactor)
  have hdeltaTransit : LargeIndecomposable.AllowsTransit
      (F.map (selectedMiddle S spine)) :=
    (factorBranch_quotientMiddle_allowsBitransit
      S hfinite spine P lambda hfactor).1
  exact exists_figure14CentralCoefficientData
    (F.map (selectedMiddle S spine))
    (F.map (selectedLambda S spine lambda))
    residueX residueY hresidueX hresidueY Pbar hsigma hthree hdeltaTransit

set_option maxHeartbeats 800000 in
/-- The reverse-arrow coefficient in every exact quotient central package
vanishes on morphisms factoring through the initial outer object. -/
theorem factorBranch_quotientCentral_lambdaZero_first_comp_eq_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    let T := selectedQuotientSplitBasic S spine P Q
    let Pbar := factorBranch_quotientLeftPowerParameter
      S hfinite spine P lambda hfactor
    ∀ central : Figure14CentralCoefficientData
        (F.map (selectedMiddle S spine))
        (F.map (selectedLambda S spine lambda))
        (T.projectiveEndResidue
          (F.obj (selectedRightInnerObj S spine)))
        (T.projectiveEndResidue
          (F.obj (selectedLeftInnerObj S spine))) Pbar.tau,
      ∀ g : F.obj (selectedInitialObj S spine) ⟶
          F.obj (selectedRightInnerObj S spine),
        central.lambdaZero (F.map (selectedFirst S spine) ≫ g) = 0 := by
  dsimp only
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  let F := selectedQuotientFunctor S spine P Q
  let T := selectedQuotientSplitBasic S spine P Q
  let Xbar := F.obj (selectedRightInnerObj S spine)
  let Ybar := F.obj (selectedLeftInnerObj S spine)
  let Lbar := F.obj (selectedInitialObj S spine)
  let first := F.map (selectedFirst S spine)
  let lambdaBar := F.map (selectedLambda S spine lambda)
  let residueX := T.projectiveEndResidue Xbar
  letI : Module.Finite k
      (selectedCorner S spine ⧸
        (selectedRelationIdeal S spine P Q).asIdeal) :=
    Module.Finite.quotient k
      (selectedRelationIdeal S spine P Q).asIdeal
  intro central g
  have hresidueX (a : End Xbar) :
      residueX a = 0 ↔ a ∈ Ring.jacobson (End Xbar) := by
    dsimp only [residueX]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  have hmem : first ≫ g ∈
      twoSidedEndomorphismSpan k lambdaBar := by
    rw [factorBranch_quotientLambda_span_eq_top
      S hfinite spine P lambda hfactor]
    exact Submodule.mem_top
  obtain ⟨a, ha⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit
      (k := k)
      (factorBranch_quotientLambda_allowsTransit
        S hfinite spine P lambda hfactor) hmem
  rw [ha, central.lambdaZero_post]
  by_contra hres
  have haUnit : IsUnit a := by
    by_contra hnot
    apply hres
    exact (hresidueX a).2
      ((LargeIndecomposable.mem_ringJacobson_iff_not_isUnit
        (End Xbar) a).2 hnot)
  letI : IsIso a.asHom := (isUnit_iff_isIso a).1 haUnit
  apply factorBranch_quotientLambda_not_factorsThrough_initial
    S hfinite spine P lambda hfactor
  refine ⟨first, g ≫ inv a.asHom, ?_⟩
  calc
    lambdaBar = (lambdaBar ≫ a.asHom) ≫ inv a.asHom := by simp
    _ = (first ≫ g) ≫ inv a.asHom := by rw [← ha]
    _ = first ≫ (g ≫ inv a.asHom) := by
      simp only [Category.assoc]

set_option maxHeartbeats 800000 in
/-- The left-cycle coefficient in every exact quotient central package
vanishes on return cycles through the initial outer object. -/
theorem factorBranch_quotientCentral_sigmaOne_first_comp_eq_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    let T := selectedQuotientSplitBasic S spine P Q
    let Pbar := factorBranch_quotientLeftPowerParameter
      S hfinite spine P lambda hfactor
    ∀ central : Figure14CentralCoefficientData
        (F.map (selectedMiddle S spine))
        (F.map (selectedLambda S spine lambda))
        (T.projectiveEndResidue
          (F.obj (selectedRightInnerObj S spine)))
        (T.projectiveEndResidue
          (F.obj (selectedLeftInnerObj S spine))) Pbar.tau,
      ∀ g : F.obj (selectedInitialObj S spine) ⟶
          F.obj (selectedLeftInnerObj S spine),
        central.sigmaOne
          (End.of (F.map (selectedFirst S spine) ≫ g)) = 0 := by
  dsimp only
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  let F := selectedQuotientFunctor S spine P Q
  let T := selectedQuotientSplitBasic S spine P Q
  let Pbar := factorBranch_quotientLeftPowerParameter
    S hfinite spine P lambda hfactor
  let Ybar := F.obj (selectedLeftInnerObj S spine)
  let Lbar := F.obj (selectedInitialObj S spine)
  let first := F.map (selectedFirst S spine)
  let residueY := T.projectiveEndResidue Ybar
  letI : Module.Finite k
      (selectedCorner S spine ⧸
        (selectedRelationIdeal S spine P Q).asIdeal) :=
    Module.Finite.quotient k
      (selectedRelationIdeal S spine P Q).asIdeal
  letI : ∀ Z : T.ProjectiveCategory, Module.Finite k (End Z) :=
    fun Z ↦ by
      change Module.Finite k (Z ⟶ Z)
      infer_instance
  intro central g
  have hresidueY (b : End Ybar) :
      residueY b = 0 ↔ b ∈ Ring.jacobson (End Ybar) := by
    dsimp only [residueY]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  have hcycleResidue : residueY (End.of (first ≫ g)) = 0 :=
    projectiveEndResidue_comp_eq_zero_of_ne T
      (factorBranch_quotientLeftInner_ne_initial S hfinite spine P Q)
      first g
  have hcycleJ : End.of (first ≫ g) ∈
      Ring.jacobson (End Ybar) :=
    (hresidueY (End.of (first ≫ g))).1 hcycleResidue
  have hcycleMem : End.of (first ≫ g) ∈
      twoSidedEndomorphismSpan k Pbar.tau := by
    rw [factorBranch_quotientLeftPowerParameter_tau,
      factorBranch_quotientLeftTau_span_eq_jacobson
        S hfinite spine P lambda hfactor]
    exact hcycleJ
  obtain ⟨b, hb⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit
      (k := k) Pbar.tau_allowsTransit hcycleMem
  have hbHom : first ≫ g = Pbar.tau.asHom ≫ b.asHom := by
    simpa only using hb
  have hcycleEnd : End.of (first ≫ g) = b * Pbar.tau := by
    apply End.ext
    simpa only [End.mul_def] using hbHom
  rw [hcycleEnd, central.sigmaOne_mul_sigma]
  by_contra hres
  have hbUnit : IsUnit b := by
    by_contra hnot
    apply hres
    exact (hresidueY b).2
      ((LargeIndecomposable.mem_ringJacobson_iff_not_isUnit
        (End Ybar) b).2 hnot)
  letI : IsIso b.asHom := (isUnit_iff_isIso b).1 hbUnit
  apply factorBranch_quotientLeftTau_not_factorsThrough_initial
    S hfinite spine P lambda hfactor
  refine ⟨first, g ≫ inv b.asHom, ?_⟩
  calc
    F.map (selectedLeftTau S spine P) = Pbar.tau.asHom := by
      rw [factorBranch_quotientLeftPowerParameter_tau]
    _ = (first ≫ g) ≫ inv b.asHom := by
      rw [hbHom, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    _ = first ≫ (g ≫ inv b.asHom) := by
      simp only [Category.assoc]

set_option maxHeartbeats 800000 in
/-- The reverse-arrow coefficient in every exact quotient central package
vanishes on morphisms factoring through the terminal outer object. -/
theorem factorBranch_quotientCentral_lambdaZero_comp_last_eq_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    let T := selectedQuotientSplitBasic S spine P Q
    let Pbar := factorBranch_quotientLeftPowerParameter
      S hfinite spine P lambda hfactor
    ∀ central : Figure14CentralCoefficientData
        (F.map (selectedMiddle S spine))
        (F.map (selectedLambda S spine lambda))
        (T.projectiveEndResidue
          (F.obj (selectedRightInnerObj S spine)))
        (T.projectiveEndResidue
          (F.obj (selectedLeftInnerObj S spine))) Pbar.tau,
      ∀ g : F.obj (selectedLeftInnerObj S spine) ⟶
          F.obj (selectedTerminalObj S spine),
        central.lambdaZero (g ≫ F.map (selectedLast S spine)) = 0 := by
  dsimp only
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  let F := selectedQuotientFunctor S spine P Q
  let T := selectedQuotientSplitBasic S spine P Q
  let Xbar := F.obj (selectedRightInnerObj S spine)
  let lambdaBar := F.map (selectedLambda S spine lambda)
  let last := F.map (selectedLast S spine)
  let residueX := T.projectiveEndResidue Xbar
  letI : Module.Finite k
      (selectedCorner S spine ⧸
        (selectedRelationIdeal S spine P Q).asIdeal) :=
    Module.Finite.quotient k
      (selectedRelationIdeal S spine P Q).asIdeal
  intro central g
  have hresidueX (a : End Xbar) :
      residueX a = 0 ↔ a ∈ Ring.jacobson (End Xbar) := by
    dsimp only [residueX]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  have hmem : g ≫ last ∈
      twoSidedEndomorphismSpan k lambdaBar := by
    rw [factorBranch_quotientLambda_span_eq_top
      S hfinite spine P lambda hfactor]
    exact Submodule.mem_top
  obtain ⟨a, ha⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit
      (k := k)
      (factorBranch_quotientLambda_allowsTransit
        S hfinite spine P lambda hfactor) hmem
  rw [ha, central.lambdaZero_post]
  by_contra hres
  have haUnit : IsUnit a := by
    by_contra hnot
    apply hres
    exact (hresidueX a).2
      ((LargeIndecomposable.mem_ringJacobson_iff_not_isUnit
        (End Xbar) a).2 hnot)
  letI : IsIso a.asHom := (isUnit_iff_isIso a).1 haUnit
  apply factorBranch_quotientLambda_not_factorsThrough_terminal
    S hfinite spine P lambda hfactor
  refine ⟨g, last ≫ inv a.asHom, ?_⟩
  calc
    lambdaBar = (lambdaBar ≫ a.asHom) ≫ inv a.asHom := by simp
    _ = (g ≫ last) ≫ inv a.asHom := by rw [← ha]
    _ = g ≫ (last ≫ inv a.asHom) := by
      simp only [Category.assoc]

set_option maxHeartbeats 800000 in
/-- The right-cycle coefficient in every exact quotient central package
vanishes on return cycles through the terminal outer object. -/
theorem factorBranch_quotientCentral_rhoOne_comp_last_eq_zero
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    let T := selectedQuotientSplitBasic S spine P Q
    let Pbar := factorBranch_quotientLeftPowerParameter
      S hfinite spine P lambda hfactor
    ∀ central : Figure14CentralCoefficientData
        (F.map (selectedMiddle S spine))
        (F.map (selectedLambda S spine lambda))
        (T.projectiveEndResidue
          (F.obj (selectedRightInnerObj S spine)))
        (T.projectiveEndResidue
          (F.obj (selectedLeftInnerObj S spine))) Pbar.tau,
      ∀ g : F.obj (selectedRightInnerObj S spine) ⟶
          F.obj (selectedTerminalObj S spine),
        central.rhoOne
          (End.of (g ≫ F.map (selectedLast S spine))) = 0 := by
  dsimp only
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  let F := selectedQuotientFunctor S spine P Q
  let T := selectedQuotientSplitBasic S spine P Q
  let Qbar := factorBranch_quotientRightPowerParameter
    S hfinite spine P lambda hfactor
  let Ubar := F.obj (selectedTerminalObj S spine)
  let Xbar := F.obj (selectedRightInnerObj S spine)
  let delta := F.map (selectedMiddle S spine)
  let lambdaBar := F.map (selectedLambda S spine lambda)
  let last := F.map (selectedLast S spine)
  let residueX := T.projectiveEndResidue Xbar
  letI : Module.Finite k
      (selectedCorner S spine ⧸
        (selectedRelationIdeal S spine P Q).asIdeal) :=
    Module.Finite.quotient k
      (selectedRelationIdeal S spine P Q).asIdeal
  letI : ∀ Z : T.ProjectiveCategory, Module.Finite k (End Z) :=
    fun Z ↦ by
      change Module.Finite k (Z ⟶ Z)
      infer_instance
  intro central g
  have hresidueX (a : End Xbar) :
      residueX a = 0 ↔ a ∈ Ring.jacobson (End Xbar) := by
    dsimp only [residueX]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  have hcycleResidue : residueX (End.of (g ≫ last)) = 0 :=
    projectiveEndResidue_comp_eq_zero_of_ne T
      (factorBranch_quotientTerminal_ne_rightInner
        S hfinite spine P Q).symm g last
  have hcycleJ : End.of (g ≫ last) ∈
      Ring.jacobson (End Xbar) :=
    (hresidueX (End.of (g ≫ last))).1 hcycleResidue
  have hcycleMem : End.of (g ≫ last) ∈
      twoSidedEndomorphismSpan k Qbar.tau := by
    rw [factorBranch_quotientRightPowerParameter_tau,
      factorBranch_quotientRightTau_span_eq_jacobson
        S hfinite spine P lambda hfactor]
    exact hcycleJ
  obtain ⟨b, hb⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit
      (k := k) Qbar.tau_allowsTransit hcycleMem
  have hbHom : g ≫ last = Qbar.tau.asHom ≫ b.asHom := by
    simpa only using hb
  have hrho : Qbar.tau.asHom = delta ≫ lambdaBar :=
    factorBranch_quotient_right_cycle S hfinite spine P lambda hfactor
  have hrhoEnd : Qbar.tau = End.of (delta ≫ lambdaBar) := by
    apply End.ext
    exact hrho
  have hcycleEnd : End.of (g ≫ last) =
      b * End.of (delta ≫ lambdaBar) := by
    rw [← hrhoEnd]
    apply End.ext
    simpa only [End.mul_def] using hbHom
  rw [hcycleEnd, central.rhoOne_mul_rho]
  by_contra hres
  have hbUnit : IsUnit b := by
    by_contra hnot
    apply hres
    exact (hresidueX b).2
      ((LargeIndecomposable.mem_ringJacobson_iff_not_isUnit
        (End Xbar) b).2 hnot)
  letI : IsIso b.asHom := (isUnit_iff_isIso b).1 hbUnit
  apply factorBranch_quotientRightTau_not_factorsThrough_terminal
    S hfinite spine P lambda hfactor
  refine ⟨g, last ≫ inv b.asHom, ?_⟩
  calc
    F.map (selectedRightTau S spine Q) = Qbar.tau.asHom := by
      rw [factorBranch_quotientRightPowerParameter_tau]
    _ = (g ≫ last) ≫ inv b.asHom := by
      rw [hbHom, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    _ = g ≫ (last ≫ inv b.asHom) := by
      simp only [Category.assoc]

set_option maxHeartbeats 800000 in
/-- The initial directed arm carries coefficients whose occurrence of the
middle arrow is literally the central coefficient. -/
theorem factorBranch_quotientInitialArmCoefficientData
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    let T := selectedQuotientSplitBasic S spine P Q
    let Pbar := factorBranch_quotientLeftPowerParameter
      S hfinite spine P lambda hfactor
    let residueX := T.projectiveEndResidue
      (F.obj (selectedRightInnerObj S spine))
    let residueY := T.projectiveEndResidue
      (F.obj (selectedLeftInnerObj S spine))
    let residueL := T.projectiveEndResidue
      (F.obj (selectedInitialObj S spine))
    ∀ central : Figure14CentralCoefficientData
        (F.map (selectedMiddle S spine))
        (F.map (selectedLambda S spine lambda))
        residueX residueY Pbar.tau,
      Nonempty { arm : Figure14ArmCoefficientData
          (F.map (selectedMiddle S spine))
          (F.map (selectedFirst S spine))
          residueX residueY residueL //
        arm.alphaZero = central.deltaZero } := by
  dsimp only
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  let F := selectedQuotientFunctor S spine P Q
  let T := selectedQuotientSplitBasic S spine P Q
  let Xbar := F.obj (selectedRightInnerObj S spine)
  let Ybar := F.obj (selectedLeftInnerObj S spine)
  let Lbar := F.obj (selectedInitialObj S spine)
  let delta := F.map (selectedMiddle S spine)
  let first := F.map (selectedFirst S spine)
  let residueX := T.projectiveEndResidue Xbar
  let residueY := T.projectiveEndResidue Ybar
  let residueL := T.projectiveEndResidue Lbar
  letI : Module.Finite k
      (selectedCorner S spine ⧸
        (selectedRelationIdeal S spine P Q).asIdeal) :=
    Module.Finite.quotient k
      (selectedRelationIdeal S spine P Q).asIdeal
  letI : LargeIndecomposable.HasBGRSDistributiveHomStructure k
      (selectedSplitBasic S spine).ProjectiveCategory :=
    LargeIndecomposable.HasBGRSDistributiveHomStructure.of_fullyFaithful
      (selectedProjectiveFunctor S spine)
  have hresidueX (a : End Xbar) :
      residueX a = 0 ↔ a ∈ Ring.jacobson (End Xbar) := by
    dsimp only [residueX]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  have hresidueY (a : End Ybar) :
      residueY a = 0 ↔ a ∈ Ring.jacobson (End Ybar) := by
    dsimp only [residueY]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  have hresidueL (a : End Lbar) :
      residueL a = 0 ↔ a ∈ Ring.jacobson (End Lbar) := by
    dsimp only [residueL]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  have hdeltaSpan : twoSidedEndomorphismSpan k delta = ⊤ :=
    factorBranch_quotientMiddle_span_eq_top
      S hfinite spine P lambda hfactor
  have hfirstSpan : twoSidedEndomorphismSpan k first = ⊤ :=
    factorBranch_quotientFirst_span_eq_top
      S hfinite spine P lambda hfactor
  have hdeltaTransit : LargeIndecomposable.AllowsTransit delta :=
    (factorBranch_quotientMiddle_allowsBitransit
      S hfinite spine P lambda hfactor).1
  have hfirstCotransit : LargeIndecomposable.AllowsCotransit first :=
    factorBranch_quotientFirst_allowsCotransit
      S hfinite spine P lambda hfactor
  have hunit : ∀ a : End Ybar, IsUnit a →
      (delta ≫ a.asHom) ≫ first ≠ 0 :=
    factorBranch_quotient_initial_unit_sandwich_ne_zero
      S hfinite spine P lambda hfactor
  intro central
  obtain ⟨arm⟩ := exists_figure14ArmCoefficientData
    delta first residueX residueY residueL
    hresidueX hresidueY hresidueL
    hdeltaSpan hfirstSpan hdeltaTransit hfirstCotransit hunit
  refine ⟨⟨arm, ?_⟩⟩
  apply LinearMap.ext
  intro g
  have hg : g ∈ twoSidedEndomorphismSpan k delta := by
    rw [hdeltaSpan]
    exact Submodule.mem_top
  obtain ⟨a, rfl⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit
      (k := k) hdeltaTransit hg
  rw [arm.alphaZero_post, central.deltaZero_post]

set_option maxHeartbeats 800000 in
/-- The terminal directed arm carries coefficients whose occurrence of the
middle arrow is literally the central coefficient. -/
theorem factorBranch_quotientTerminalArmCoefficientData
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    let T := selectedQuotientSplitBasic S spine P Q
    let Pbar := factorBranch_quotientLeftPowerParameter
      S hfinite spine P lambda hfactor
    let residueU := T.projectiveEndResidue
      (F.obj (selectedTerminalObj S spine))
    let residueX := T.projectiveEndResidue
      (F.obj (selectedRightInnerObj S spine))
    let residueY := T.projectiveEndResidue
      (F.obj (selectedLeftInnerObj S spine))
    ∀ central : Figure14CentralCoefficientData
        (F.map (selectedMiddle S spine))
        (F.map (selectedLambda S spine lambda))
        residueX residueY Pbar.tau,
      Nonempty { arm : Figure14ArmCoefficientData
          (F.map (selectedLast S spine))
          (F.map (selectedMiddle S spine))
          residueU residueX residueY //
        arm.betaZero = central.deltaZero } := by
  dsimp only
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  let F := selectedQuotientFunctor S spine P Q
  let T := selectedQuotientSplitBasic S spine P Q
  let Ubar := F.obj (selectedTerminalObj S spine)
  let Xbar := F.obj (selectedRightInnerObj S spine)
  let Ybar := F.obj (selectedLeftInnerObj S spine)
  let last := F.map (selectedLast S spine)
  let delta := F.map (selectedMiddle S spine)
  let residueU := T.projectiveEndResidue Ubar
  let residueX := T.projectiveEndResidue Xbar
  let residueY := T.projectiveEndResidue Ybar
  letI : Module.Finite k
      (selectedCorner S spine ⧸
        (selectedRelationIdeal S spine P Q).asIdeal) :=
    Module.Finite.quotient k
      (selectedRelationIdeal S spine P Q).asIdeal
  letI : LargeIndecomposable.HasBGRSDistributiveHomStructure k
      (selectedSplitBasic S spine).ProjectiveCategory :=
    LargeIndecomposable.HasBGRSDistributiveHomStructure.of_fullyFaithful
      (selectedProjectiveFunctor S spine)
  have hresidueU (a : End Ubar) :
      residueU a = 0 ↔ a ∈ Ring.jacobson (End Ubar) := by
    dsimp only [residueU]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  have hresidueX (a : End Xbar) :
      residueX a = 0 ↔ a ∈ Ring.jacobson (End Xbar) := by
    dsimp only [residueX]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  have hresidueY (a : End Ybar) :
      residueY a = 0 ↔ a ∈ Ring.jacobson (End Ybar) := by
    dsimp only [residueY]
    rw [T.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← T.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  have hlastSpan : twoSidedEndomorphismSpan k last = ⊤ :=
    factorBranch_quotientLast_span_eq_top
      S hfinite spine P lambda hfactor
  have hdeltaSpan : twoSidedEndomorphismSpan k delta = ⊤ :=
    factorBranch_quotientMiddle_span_eq_top
      S hfinite spine P lambda hfactor
  have hlastTransit : LargeIndecomposable.AllowsTransit last :=
    factorBranch_quotientLast_allowsTransit
      S hfinite spine P lambda hfactor
  have hdeltaCotransit : LargeIndecomposable.AllowsCotransit delta :=
    (factorBranch_quotientMiddle_allowsBitransit
      S hfinite spine P lambda hfactor).2
  have hunit : ∀ a : End Xbar, IsUnit a →
      (last ≫ a.asHom) ≫ delta ≠ 0 :=
    factorBranch_quotient_terminal_unit_sandwich_ne_zero
      S hfinite spine P lambda hfactor
  intro central
  obtain ⟨arm⟩ := exists_figure14ArmCoefficientData
    last delta residueU residueX residueY
    hresidueU hresidueX hresidueY
    hlastSpan hdeltaSpan hlastTransit hdeltaCotransit hunit
  refine ⟨⟨arm, ?_⟩⟩
  apply LinearMap.ext
  intro g
  have hg : g ∈ twoSidedEndomorphismSpan k delta := by
    rw [hdeltaSpan]
    exact Submodule.mem_top
  obtain ⟨a, rfl⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsCotransit
      (k := k) hdeltaCotransit hg
  rw [arm.betaZero_pre, central.deltaZero_pre]

set_option maxHeartbeats 800000 in
/-- Once the four genuinely outer Figure-14 coefficient vanishings are
available, all remaining hypotheses of the repeated-center coefficient
compiler follow from the exact quotient construction. -/
def factorBranch_quotientThinPathCoefficientData_of_outer_vanishings
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    let T := selectedQuotientSplitBasic S spine P Q
    let Pbar := factorBranch_quotientLeftPowerParameter
      S hfinite spine P lambda hfactor
    let Ubar := F.obj (selectedTerminalObj S spine)
    let Xbar := F.obj (selectedRightInnerObj S spine)
    let Ybar := F.obj (selectedLeftInnerObj S spine)
    let Lbar := F.obj (selectedInitialObj S spine)
    let first := F.map (selectedFirst S spine)
    let delta := F.map (selectedMiddle S spine)
    let lambdaBar := F.map (selectedLambda S spine lambda)
    let last := F.map (selectedLast S spine)
    let residueU := T.projectiveEndResidue Ubar
    let residueX := T.projectiveEndResidue Xbar
    let residueY := T.projectiveEndResidue Ybar
    let residueL := T.projectiveEndResidue Lbar
    ∀ central : Figure14CentralCoefficientData
        delta lambdaBar residueX residueY Pbar.tau,
      ∀ initialArm : Figure14ArmCoefficientData
          delta first residueX residueY residueL,
        ∀ suffix : Figure14ArmCoefficientData
            last delta residueU residueX residueY,
          initialArm.alphaZero = central.deltaZero →
          suffix.betaZero = central.deltaZero →
          (∀ g : Lbar ⟶ Xbar,
            central.lambdaZero (first ≫ g) = 0) →
          (∀ g : Lbar ⟶ Ybar,
            central.sigmaOne (End.of (first ≫ g)) = 0) →
          (∀ g : Ybar ⟶ Ubar,
            central.lambdaZero (g ≫ last) = 0) →
          (∀ g : Xbar ⟶ Ubar,
            central.rhoOne (End.of (g ≫ last)) = 0) →
          LargeIndecomposable.ClosedZigzagCrossUniverse.ThinPathCoefficientData
            ((LargeIndecomposable.CriticalSingularFigure14.repeatedCenterDiagram
              first delta lambdaBar last).functor (k := k)) := by
  dsimp only
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  let F := selectedQuotientFunctor S spine P Q
  let T := selectedQuotientSplitBasic S spine P Q
  let Pbar := factorBranch_quotientLeftPowerParameter
    S hfinite spine P lambda hfactor
  let Ubar := F.obj (selectedTerminalObj S spine)
  let Xbar := F.obj (selectedRightInnerObj S spine)
  let Ybar := F.obj (selectedLeftInnerObj S spine)
  let Lbar := F.obj (selectedInitialObj S spine)
  let first := F.map (selectedFirst S spine)
  let delta := F.map (selectedMiddle S spine)
  let lambdaBar := F.map (selectedLambda S spine lambda)
  let last := F.map (selectedLast S spine)
  let residueU := T.projectiveEndResidue Ubar
  let residueX := T.projectiveEndResidue Xbar
  let residueY := T.projectiveEndResidue Ybar
  let residueL := T.projectiveEndResidue Lbar
  letI : Module.Finite k
      (selectedCorner S spine ⧸
        (selectedRelationIdeal S spine P Q).asIdeal) :=
    Module.Finite.quotient k
      (selectedRelationIdeal S spine P Q).asIdeal
  intro central initialArm suffix hinitialDelta hsuffixDelta
    hLambdaAfterFirstZero hSigmaThroughLZero
    hLambdaBeforeLastZero hRhoThroughUZero
  have hXY : Xbar ≠ Ybar :=
    factorBranch_quotientRightInner_ne_leftInner
      S hfinite spine P Q
  have hYL : Ybar ≠ Lbar :=
    factorBranch_quotientLeftInner_ne_initial
      S hfinite spine P Q
  have hUX : Ubar ≠ Xbar :=
    factorBranch_quotientTerminal_ne_rightInner
      S hfinite spine P Q
  have hYThroughXZero : ∀ (l : Ybar ⟶ Xbar) (r : Xbar ⟶ Ybar),
      residueY (End.of (l ≫ r)) = 0 := by
    intro l r
    exact projectiveEndResidue_comp_eq_zero_of_ne T hXY.symm l r
  have hXThroughYZero : ∀ (l : Xbar ⟶ Ybar) (r : Ybar ⟶ Xbar),
      residueX (End.of (l ≫ r)) = 0 := by
    intro l r
    exact projectiveEndResidue_comp_eq_zero_of_ne T hXY l r
  have hUThroughXZero : ∀ (l : Ubar ⟶ Xbar) (r : Xbar ⟶ Ubar),
      residueU (End.of (l ≫ r)) = 0 := by
    intro l r
    exact projectiveEndResidue_comp_eq_zero_of_ne T hUX l r
  have hXThroughUZero : ∀ (l : Xbar ⟶ Ubar) (r : Ubar ⟶ Xbar),
      residueX (End.of (l ≫ r)) = 0 := by
    intro l r
    exact projectiveEndResidue_comp_eq_zero_of_ne T hUX.symm l r
  have hYThroughLZero : ∀ (l : Ybar ⟶ Lbar) (r : Lbar ⟶ Ybar),
      residueY (End.of (l ≫ r)) = 0 := by
    intro l r
    exact projectiveEndResidue_comp_eq_zero_of_ne T hYL l r
  have hLThroughYZero : ∀ (l : Lbar ⟶ Ybar) (r : Ybar ⟶ Lbar),
      residueL (End.of (l ≫ r)) = 0 := by
    intro l r
    exact projectiveEndResidue_comp_eq_zero_of_ne T hYL.symm l r
  have hFirstAfterLambdaZero : ∀ g : Xbar ⟶ Lbar,
      initialArm.betaZero (lambdaBar ≫ g) = 0 :=
    factorBranch_quotientInitial_betaZero_lambda_comp_eq_zero
      S hfinite spine P lambda hfactor initialArm
  have hLastBeforeLambdaZero : ∀ g : Ubar ⟶ Ybar,
      suffix.alphaZero (g ≫ lambdaBar) = 0 :=
    factorBranch_quotientTerminal_alphaZero_comp_lambda_eq_zero
      S hfinite spine P lambda hfactor suffix
  have hsigma : Pbar.tau.asHom = lambdaBar ≫ delta :=
    factorBranch_quotient_left_cycle
      S hfinite spine P lambda hfactor
  have hdeltaSpan : twoSidedEndomorphismSpan k delta = ⊤ :=
    factorBranch_quotientMiddle_span_eq_top
      S hfinite spine P lambda hfactor
  have hlambdaSpan : twoSidedEndomorphismSpan k lambdaBar = ⊤ :=
    factorBranch_quotientLambda_span_eq_top
      S hfinite spine P lambda hfactor
  have hdeltaTransit : LargeIndecomposable.AllowsTransit delta :=
    (factorBranch_quotientMiddle_allowsBitransit
      S hfinite spine P lambda hfactor).1
  have hlambdaTransit : LargeIndecomposable.AllowsTransit lambdaBar :=
    factorBranch_quotientLambda_allowsTransit
      S hfinite spine P lambda hfactor
  exact
    LargeIndecomposable.CriticalSingularFigure14.repeatedCenterThinPathCoefficientData
      first delta lambdaBar last residueU residueX residueY residueL
      central initialArm suffix hinitialDelta hsuffixDelta hsigma
      hdeltaSpan hlambdaSpan hdeltaTransit hlambdaTransit
      hYThroughXZero hXThroughYZero hUThroughXZero hXThroughUZero
      hYThroughLZero hLThroughYZero hFirstAfterLambdaZero
      hLambdaAfterFirstZero hSigmaThroughLZero hLastBeforeLambdaZero
      hLambdaBeforeLastZero hRhoThroughUZero

set_option maxHeartbeats 1000000 in
/-- The exact quotient in the first factor branch of BGRS 4.3(b) carries a
complete coherent thin-path coefficient system for Figure 14. -/
theorem factorBranch_quotientThinPathCoefficientData
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    let Q := spine.middleCompReverseRadicalPowerParameter
      S hfinite P lambda hfactor
    let F := selectedQuotientFunctor S spine P Q
    Nonempty
      (LargeIndecomposable.ClosedZigzagCrossUniverse.ThinPathCoefficientData
        ((LargeIndecomposable.CriticalSingularFigure14.repeatedCenterDiagram
          (F.map (selectedFirst S spine))
          (F.map (selectedMiddle S spine))
          (F.map (selectedLambda S spine lambda))
          (F.map (selectedLast S spine))).functor (k := k))) := by
  dsimp only
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  let F := selectedQuotientFunctor S spine P Q
  let T := selectedQuotientSplitBasic S spine P Q
  let Pbar := factorBranch_quotientLeftPowerParameter
    S hfinite spine P lambda hfactor
  obtain ⟨central⟩ :=
    factorBranch_quotientCentralCoefficientData
      S hfinite spine P lambda hfactor
  obtain ⟨⟨initialArm, hinitialDelta⟩⟩ :=
    factorBranch_quotientInitialArmCoefficientData
      S hfinite spine P lambda hfactor central
  obtain ⟨⟨suffix, hsuffixDelta⟩⟩ :=
    factorBranch_quotientTerminalArmCoefficientData
      S hfinite spine P lambda hfactor central
  refine ⟨factorBranch_quotientThinPathCoefficientData_of_outer_vanishings
    S hfinite spine P lambda hfactor central initialArm suffix
      hinitialDelta hsuffixDelta ?_ ?_ ?_ ?_⟩
  · exact factorBranch_quotientCentral_lambdaZero_first_comp_eq_zero
      S hfinite spine P lambda hfactor central
  · exact factorBranch_quotientCentral_sigmaOne_first_comp_eq_zero
      S hfinite spine P lambda hfactor central
  · exact factorBranch_quotientCentral_lambdaZero_comp_last_eq_zero
      S hfinite spine P lambda hfactor central
  · exact factorBranch_quotientCentral_rhoOne_comp_last_eq_zero
      S hfinite spine P lambda hfactor central

/-- The exact local quotient in the first factor branch of BGRS 4.3(b) is a
cleaving Figure-14 quotient. -/
theorem factorBranch_localQuotientCandidate_isCleaving
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as)
    (hfactor : P.tau.asHom =
      lambda ≫ spine.lift.pathMap spine.middle) :
    (localQuotientCandidate S spine P
      (spine.middleCompReverseRadicalPowerParameter
        S hfinite P lambda hfactor) lambda).IsCleaving := by
  obtain ⟨coeff⟩ := factorBranch_quotientThinPathCoefficientData
    S hfinite spine P lambda hfactor
  exact ⟨coeff.homBifunctorRetraction⟩

/-- Representation-finiteness excludes the first factor branch of BGRS
4.3(b): the chosen local parameter cannot factor as the reverse arrow followed
by the middle arrow. -/
theorem factorBranch_sigma_ne_reverse_comp_middle
    (hfinite : LargeIndecomposable.MildAlg k A)
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    (P : OrientedRadicalPowerParameter
      (k := k) spine.leftInner.obj.as)
    (lambda : spine.leftInner.obj.as ⟶ spine.rightInner.obj.as) :
    P.tau.asHom ≠ lambda ≫ spine.lift.pathMap spine.middle := by
  intro hfactor
  let Q := spine.middleCompReverseRadicalPowerParameter
    S hfinite P lambda hfactor
  let G := localQuotientCandidate S spine P Q lambda
  have hcleaving : G.IsCleaving :=
    factorBranch_localQuotientCandidate_isCleaving
      S hfinite spine P lambda hfactor
  exact LargeIndecomposable.CriticalSingularLocalQuotientExtraction.false_of_figure14LocalQuotient_mild
    S G hcleaving hfinite (selectedRelationIdeal_ne_bot S hfinite spine P Q)

end LargeIndecomposable.CriticalFigure14Quotient
