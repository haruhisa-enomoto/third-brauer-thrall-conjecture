module

public import LargeIndecomposable.Cleaving.ClosedChains.CleavingTransfer
public import Mathlib.CategoryTheory.Idempotents.FunctorCategories
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace LargeIndecomposable.ClosedZigzagTransfer

universe u v w x

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]

/-- In an idempotent-complete preadditive category, an indecomposable object
has only the two trivial idempotent endomorphisms. -/
theorem end_eq_zero_or_one_of_idempotent
    {C : Type v} [Category.{w} C] [Preadditive C]
    [HasBinaryBiproducts C] [IsIdempotentComplete C]
    {X : C} (hX : Indecomposable X) (p : X ⟶ X)
    (hp : p ≫ p = p) : p = 0 ∨ p = 𝟙 X := by
  let q : X ⟶ X := 𝟙 X - p
  have hq_hom : q ≫ q = q := by
    dsimp [q]
    exact Idempotents.idem_of_id_sub_idem p hp
  obtain ⟨Y, i, e, hi, he⟩ :=
    IsIdempotentComplete.idempotents_split X p hp
  obtain ⟨Z, j, r, hj, hr⟩ :=
    IsIdempotentComplete.idempotents_split X q hq_hom
  have hpq : p ≫ q = 0 := by
    dsimp [q]
    simp only [Preadditive.comp_sub, Category.comp_id, hp, sub_self]
  have hqp : q ≫ p = 0 := by
    dsimp [q]
    simp only [Preadditive.sub_comp, Category.id_comp, hp, sub_self]
  have hqr : q ≫ r = r := by
    rw [← hr, Category.assoc, hj, Category.comp_id]
  have hpe : p ≫ e = e := by
    rw [← he, Category.assoc, hi, Category.comp_id]
  have hip : i ≫ p = i := by
    rw [← he, ← Category.assoc, hi, Category.id_comp]
  have hqj : j ≫ q = j := by
    rw [← hr, ← Category.assoc, hj, Category.id_comp]
  have hir : i ≫ r = 0 := by
    calc
      i ≫ r = (i ≫ p) ≫ (q ≫ r) := by rw [hip, hqr]
      _ = i ≫ (p ≫ q) ≫ r := by simp only [Category.assoc]
      _ = 0 := by rw [hpq]; simp
  have hje : j ≫ e = 0 := by
    calc
      j ≫ e = (j ≫ q) ≫ (p ≫ e) := by rw [hqj, hpe]
      _ = j ≫ (q ≫ p) ≫ e := by simp only [Category.assoc]
      _ = 0 := by rw [hqp]; simp
  let decomp : X ≅ Y ⊞ Z := {
    hom := biprod.lift e r
    inv := biprod.desc i j
    hom_inv_id := by
      rw [biprod.lift_desc, he, hr]
      dsimp [q]
      simp
    inv_hom_id := by
      apply biprod.hom_ext'
      · rw [biprod.inl_desc_assoc]
        apply biprod.hom_ext
        · simpa using hi
        · simpa using hir
      · rw [biprod.inr_desc_assoc]
        apply biprod.hom_ext
        · simpa using hje
        · simpa using hj }
  rcases hX.2 Y Z decomp with hY | hZ
  · left
    have hezero : e = 0 := hY.eq_of_tgt _ _
    rw [← he]
    simp only [hezero, zero_comp]
  · right
    have hrzero : r = 0 := hZ.eq_of_tgt _ _
    have hqzero : q = 0 := by
      rw [← hr, hrzero, zero_comp]
    dsimp [q] at hqzero
    exact (sub_eq_zero.mp hqzero).symm

/-- If a nontrivial ring has no nontrivial idempotents, its right regular
module (presented as a left module over the opposite ring) is
indecomposable. -/
theorem regularModule_indecomposable_of_idempotents
    {R : Type v} [Ring R] [Nontrivial R]
    (hidem : ∀ a : R, a * a = a → a = 0 ∨ a = 1) :
    Indecomposable (ModuleCat.of Rᵐᵒᵖ R) := by
  let M : ModuleCat.{v} Rᵐᵒᵖ := ModuleCat.of Rᵐᵒᵖ R
  let eR : R ≃+* CategoryTheory.End M :=
    (RingEquiv.moduleEndSelfOp R).trans (ModuleCat.endRingEquiv M).symm
  have hMzero : ¬ IsZero M := by
    intro hzero
    have hsub : Subsingleton R := ModuleCat.isZero_iff_subsingleton.mp hzero
    exact one_ne_zero (Subsingleton.elim (1 : R) (0 : R))
  refine ⟨hMzero, ?_⟩
  intro Y Z e
  let p : CategoryTheory.End M :=
    CategoryTheory.End.of
      (e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv)
  have hp : p * p = p := by
    apply CategoryTheory.End.ext
    change
      (e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv) ≫
          (e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv) =
        e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv
    simp [Category.assoc]
  let a : R := eR.symm p
  have ha : a * a = a := by
    apply eR.injective
    simpa only [a, map_mul, eR.apply_symm_apply] using hp
  rcases hidem a ha with ha0 | ha1
  · left
    have hp0 : p = 0 := by
      simpa only [a, eR.apply_symm_apply, map_zero] using congrArg eR ha0
    rw [IsZero.iff_id_eq_zero]
    have hp0hom :
        e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv =
          (0 : M ⟶ M) := by
      change p = 0
      exact hp0
    have hproj : biprod.fst ≫ biprod.inl =
        (0 : (Y ⊞ Z) ⟶ (Y ⊞ Z)) := by
      have h := congrArg
        (fun q : M ⟶ M => e.inv ≫ q ≫ e.hom) hp0hom
      simpa only [Category.assoc, Iso.inv_hom_id_assoc,
        Iso.inv_hom_id, Category.comp_id, comp_zero, zero_comp] using h
    have h := congrArg
      (fun q : (Y ⊞ Z) ⟶ (Y ⊞ Z) =>
        biprod.inl ≫ q ≫ biprod.fst) hproj
    simpa only [Category.assoc, biprod.inl_fst_assoc,
      biprod.inl_fst, Category.comp_id, comp_zero, zero_comp] using h
  · right
    have hp1 : p = 1 := by
      simpa only [a, eR.apply_symm_apply, map_one] using congrArg eR ha1
    rw [IsZero.iff_id_eq_zero]
    have hp1hom :
        e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv = 𝟙 M := by
      change p = 1
      exact hp1
    have hproj : biprod.fst ≫ biprod.inl = 𝟙 (Y ⊞ Z) := by
      calc
        biprod.fst ≫ biprod.inl =
            e.inv ≫
              (e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv) ≫
                e.hom := by
          simp only [Category.assoc, Iso.inv_hom_id_assoc]
          rw [← Category.assoc, e.inv_hom_id, Category.comp_id]
        _ = e.inv ≫ 𝟙 M ≫ e.hom := by rw [hp1hom]
        _ = e.inv ≫ e.hom := by rw [Category.id_comp]
        _ = 𝟙 (Y ⊞ Z) := e.inv_hom_id
    have h := congrArg
      (fun q : (Y ⊞ Z) ⟶ (Y ⊞ Z) =>
        biprod.inr ≫ q ≫ biprod.snd) hproj
    simpa only [Category.assoc, biprod.inr_fst_assoc, zero_comp,
      biprod.inr_snd, Category.id_comp, Category.comp_id] using h.symm

/-- A finite-dimensional nontrivial algebra with no nontrivial idempotents is
local.  This is obtained by applying the finite-dimensional Fitting theorem to
its indecomposable right regular module. -/
theorem isLocalRing_of_finite_of_idempotents
    {R : Type v} [Ring R] [Algebra k R] [Module.Finite k R]
    [Nontrivial R]
    (hidem : ∀ a : R, a * a = a → a = 0 ∨ a = 1) :
    IsLocalRing R := by
  letI : Module.Finite k Rᵐᵒᵖ := inferInstance
  let uModule : Module k (ULift.{v} R) := inferInstance
  let uFinite :
      @Module.Finite k (ULift.{v} R) _ _ uModule := inferInstance
  let uEquiv : ULift.{v} R ≃ₗ[k] R := ULift.moduleEquiv
  have orig_smul (c : k) (r : R) :
      c • r = algebraMap k R c * r := Algebra.smul_def c r
  let M : ModuleCat.{v} Rᵐᵒᵖ := ModuleCat.of Rᵐᵒᵖ R
  let mModule : Module k M :=
    @ModuleCat.Algebra.instModuleCarrier k _ Rᵐᵒᵖ _ _ M
  have hMfinite :
      @Module.Finite k M _ M.isAddCommGroup.toAddCommMonoid mModule := by
    letI : AddCommMonoid M := M.isAddCommGroup.toAddCommMonoid
    letI : SMul k M := mModule.toDistribMulAction.toSMul
    letI : Module k M := mModule
    letI : SMul k (ULift.{v} R) := uModule.toDistribMulAction.toSMul
    letI : Module k (ULift.{v} R) := uModule
    letI : Module.Finite k (ULift.{v} R) := uFinite
    let f : ULift.{v} R →ₗ[k] M := {
      toFun := uEquiv
      map_add' := uEquiv.map_add
      map_smul' := by
        intro c x
        have target_smul (c : k) (r : M) :
            c • r = r * algebraMap k R c := by rfl
        rw [uEquiv.map_smul, orig_smul, target_smul]
        exact Algebra.commutes c (uEquiv x) }
    exact Module.Finite.of_surjective f fun x => ⟨ULift.up x, rfl⟩
  have hMind : Indecomposable M := by
    dsimp [M]
    exact regularModule_indecomposable_of_idempotents hidem
  letI : IsLocalRing (CategoryTheory.End M) :=
    @moduleCat_end_isLocalRing k _ Rᵐᵒᵖ _ _ inferInstance
      M hMfinite hMind
  let eR : R ≃+* CategoryTheory.End M :=
    (RingEquiv.moduleEndSelfOp R).trans
      (ModuleCat.endRingEquiv M).symm
  exact RingEquiv.isLocalRing_noncomm eR.symm

/-- The empty biproduct is isomorphic to every zero object. -/
def zeroIsoEmptyBiproduct
    {C : Type v} [Category.{w} C] [Preadditive C]
    [HasFiniteBiproducts C] (X : C) (hX : IsZero X) :
    X ≅ ⨁ (fun i : Fin 0 => Fin.elim0 i) where
  hom := 0
  inv := 0
  hom_inv_id := hX.eq_of_src _ _
  inv_hom_id := by
    apply biproduct.hom_ext
    intro i
    exact Fin.elim0 i

/-- Concatenate two displayed finite biproduct decompositions. -/
def FiniteIndecomposableDecomposition.biprod
    {C : Type v} [Category.{w} C] [Preadditive C]
    [HasBinaryBiproducts C] [HasFiniteBiproducts C]
    {X Y : C}
    (dX : FiniteIndecomposableDecomposition X)
    (dY : FiniteIndecomposableDecomposition Y) :
    FiniteIndecomposableDecomposition (X ⊞ Y) := by
  classical
  let N : Fin (dX.n + dY.n) → C := fun i =>
    Sum.elim dX.summand dY.summand (finSumFinEquiv.symm i)
  let I : WalkingPair → Type
    | WalkingPair.left => Fin dX.n
    | WalkingPair.right => Fin dY.n
  let G : (i : WalkingPair) → I i → C
    | WalkingPair.left => dX.summand
    | WalkingPair.right => dY.summand
  let sigmaEquiv : (Σ i, I i) ≃ Fin (dX.n + dY.n) := {
    toFun
      | ⟨WalkingPair.left, j⟩ => finSumFinEquiv (Sum.inl j)
      | ⟨WalkingPair.right, j⟩ => finSumFinEquiv (Sum.inr j)
    invFun i :=
      match finSumFinEquiv.symm i with
      | Sum.inl j => ⟨WalkingPair.left, j⟩
      | Sum.inr j => ⟨WalkingPair.right, j⟩
    left_inv := by
      rintro ⟨i, j⟩
      cases i <;> simp [I]
    right_inv := by
      intro i
      obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective i <;> simp [I] }
  letI : ∀ i, HasBiproduct (G i) := fun i => by
    cases i <;> simp only [G, I] <;> infer_instance
  let pairToOuter :
      (⨁ dX.summand) ⊞ (⨁ dY.summand) ≅
        ⨁ (fun i => ⨁ G i) :=
    (biproduct.uniqueUpToIso
      (pairFunction (⨁ dX.summand) (⨁ dY.summand))
      ((BinaryBicone.toBiconeIsBilimit _).symm
        (BinaryBiproduct.isBilimit
          (⨁ dX.summand) (⨁ dY.summand)))).trans
      (biproduct.mapIso fun i => by
        cases i
        · change (⨁ dX.summand) ≅ (⨁ dX.summand)
          exact Iso.refl _
        · change (⨁ dY.summand) ≅ (⨁ dY.summand)
          exact Iso.refl _)
  let e : (⨁ dX.summand) ⊞ (⨁ dY.summand) ≅ ⨁ N :=
    pairToOuter |>.trans (biproductBiproductIso I G) |>.trans
      (biproduct.whiskerEquiv
        (f := fun q : Σ i, I i => G q.1 q.2) (g := N) sigmaEquiv fun q =>
        eqToIso (by
          rcases q with ⟨i, j⟩
          cases i <;> simp [N, G, I, sigmaEquiv]))
  exact {
    n := dX.n + dY.n
    summand := N
    indecomposable := by
      intro i
      obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective i
      · simpa [N] using dX.indecomposable j
      · simpa [N] using dY.indecomposable j
    isoBiproduct :=
      (biprod.mapIso dX.isoBiproduct dY.isoBiproduct).trans e }

/-- If the indexing category has finitely many objects and all values of a
module-valued functor are finite-dimensional, then its endomorphism algebra
is finite-dimensional.  Naturality cuts out a subspace of the finite product
of the component endomorphism spaces. -/
theorem functorEnd_finite
    {D : Type v} [Category.{w} D] [Fintype D]
    (F : D ⥤ ModuleCat.{x} k)
    (hfinite : ∀ X, Module.Finite k (F.obj X)) :
    Module.Finite k (CategoryTheory.End F) := by
  classical
  letI (X : D) : Module.Finite k (F.obj X) := hfinite X
  letI (X : D) : Module.Finite k (F.obj X ⟶ F.obj X) := by
    exact Module.Finite.equiv
      (ModuleCat.homLinearEquiv (S := k) (M := F.obj X)
        (N := F.obj X)).symm
  let app : CategoryTheory.End F →ₗ[k]
      ((X : D) → (F.obj X ⟶ F.obj X)) :=
    LinearMap.pi fun X => NatTrans.appLinearMap X
  apply Module.Finite.of_injective app
  intro f g hfg
  apply NatTrans.ext
  funext X
  exact congrFun hfg X

/-- An indecomposable finite-total-dimensional module-valued functor has a
local endomorphism ring. -/
theorem functor_end_isLocalRing
    {D : Type v} [Category.{w} D] [Fintype D]
    (F : D ⥤ ModuleCat.{x} k)
    (hfinite : ∀ X, Module.Finite k (F.obj X))
    (hF : Indecomposable F) :
    IsLocalRing (CategoryTheory.End F) := by
  letI : Module.Finite k (CategoryTheory.End F) :=
    functorEnd_finite F hfinite
  letI : Nontrivial (CategoryTheory.End F) :=
      nontrivial_of_ne (1 : CategoryTheory.End F) 0 (by
    intro h
    apply hF.1
    rw [IsZero.iff_id_eq_zero]
    change (𝟙 F : F ⟶ F) = 0 at h
    exact h)
  apply isLocalRing_of_finite_of_idempotents (k := k)
  intro p hp
  apply end_eq_zero_or_one_of_idempotent hF p
  change p ≫ p = p
  exact hp

/-- A nonzero functor with finitely many finite-dimensional values has
positive total component dimension. -/
private theorem functor_totalFinrank_pos_of_not_isZero
    {D : Type v} [Category.{w} D] [Fintype D]
    (F : D ⥤ ModuleCat.{x} k)
    (hfinite : ∀ X, Module.Finite k (F.obj X))
    (hzero : ¬ IsZero F) :
    0 < ∑ X, Module.finrank k (F.obj X) := by
  classical
  letI (X : D) : Module.Finite k (F.obj X) := hfinite X
  by_contra hpos
  have hsum : ∑ X, Module.finrank k (F.obj X) = 0 :=
    Nat.eq_zero_of_not_pos hpos
  apply hzero
  apply Functor.isZero F
  intro X
  rw [ModuleCat.isZero_iff_subsingleton]
  apply (Module.finrank_zero_iff (R := k) (M := F.obj X)).mp
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => Nat.zero_le _)).mp hsum X (Finset.mem_univ X)

/-- A functor on a category with finitely many objects, all of whose values
are finite-dimensional vector spaces, is a finite biproduct of
indecomposable functors.  The induction measure is the sum of the component
dimensions. -/
theorem finiteIndecomposableDecomposition_functor_exists
    {D : Type v} [Category.{w} D] [Fintype D]
    (M : D ⥤ ModuleCat.{x} k)
    (hMfinite : ∀ X, Module.Finite k (M.obj X)) :
    Nonempty (FiniteIndecomposableDecomposition M) := by
  classical
  generalize hn : (∑ X, Module.finrank k (M.obj X)) = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      by_cases hMzero : IsZero M
      · exact ⟨{
          n := 0
          summand := fun i => Fin.elim0 i
          indecomposable := fun i => Fin.elim0 i
          isoBiproduct := zeroIsoEmptyBiproduct M hMzero }⟩
      by_cases hMind : Indecomposable M
      · exact ⟨{
          n := 1
          summand := fun _ => M
          indecomposable := fun _ => hMind
          isoBiproduct :=
            (biproductUniqueIso (fun _ : Fin 1 => M)).symm }⟩
      have hsplit : ∃ X Y : D ⥤ ModuleCat.{x} k,
          ∃ e : M ≅ X ⊞ Y, ¬ IsZero X ∧ ¬ IsZero Y := by
        rw [Indecomposable] at hMind
        push Not at hMind
        exact hMind hMzero
      obtain ⟨X, Y, e, hXzero, hYzero⟩ := hsplit
      let iX : X ⟶ M := biprod.inl ≫ e.inv
      let pX : M ⟶ X := e.hom ≫ biprod.fst
      have hXfinite (d : D) : Module.Finite k (X.obj d) := by
        letI : Module.Finite k (M.obj d) := hMfinite d
        apply Module.Finite.of_injective (iX.app d).hom
        exact (show Function.LeftInverse (pX.app d) (iX.app d) from
          fun z => by
            change (iX ≫ pX).app d z = z
            simp [iX, pX, Category.assoc]).injective
      let iY : Y ⟶ M := biprod.inr ≫ e.inv
      let pY : M ⟶ Y := e.hom ≫ biprod.snd
      have hYfinite (d : D) : Module.Finite k (Y.obj d) := by
        letI : Module.Finite k (M.obj d) := hMfinite d
        apply Module.Finite.of_injective (iY.app d).hom
        exact (show Function.LeftInverse (pY.app d) (iY.app d) from
          fun z => by
            change (iY ≫ pY).app d z = z
            simp [iY, pY, Category.assoc]).injective
      letI (d : D) : Module.Finite k (M.obj d) := hMfinite d
      letI (d : D) : Module.Finite k (X.obj d) := hXfinite d
      letI (d : D) : Module.Finite k (Y.obj d) := hYfinite d
      have hdimAt (d : D) : Module.finrank k (M.obj d) =
          Module.finrank k (X.obj d) + Module.finrank k (Y.obj d) := by
        let ev := (evaluation D (ModuleCat.{x} k)).obj d
        letI : PreservesBinaryBiproduct X Y ev :=
          preservesBinaryBiproduct_of_preservesBinaryProduct ev
        let eComponent : M.obj d ≅ X.obj d ⊞ Y.obj d :=
          (ev.mapIso e).trans (ev.mapBiprod X Y)
        let eLinear : M.obj d ≃ₗ[k] X.obj d × Y.obj d :=
          ((eComponent.trans
            (ModuleCat.biprodIsoProd (X.obj d) (Y.obj d))).toLinearEquiv)
        calc
          Module.finrank k (M.obj d) =
              Module.finrank k (X.obj d × Y.obj d) := eLinear.finrank_eq
          _ = Module.finrank k (X.obj d) +
              Module.finrank k (Y.obj d) := Module.finrank_prod
      have hdim : (∑ d, Module.finrank k (M.obj d)) =
          (∑ d, Module.finrank k (X.obj d)) +
            ∑ d, Module.finrank k (Y.obj d) := by
        calc
          (∑ d, Module.finrank k (M.obj d)) =
              ∑ d, (Module.finrank k (X.obj d) +
                Module.finrank k (Y.obj d)) :=
            Finset.sum_congr rfl fun d _ => hdimAt d
          _ = (∑ d, Module.finrank k (X.obj d)) +
                ∑ d, Module.finrank k (Y.obj d) :=
            Finset.sum_add_distrib
      have hXpos : 0 < ∑ d, Module.finrank k (X.obj d) :=
        functor_totalFinrank_pos_of_not_isZero X hXfinite hXzero
      have hYpos : 0 < ∑ d, Module.finrank k (Y.obj d) :=
        functor_totalFinrank_pos_of_not_isZero Y hYfinite hYzero
      have hXlt : (∑ d, Module.finrank k (X.obj d)) < n := by
        rw [← hn, hdim]
        exact Nat.lt_add_of_pos_right hYpos
      have hYlt : (∑ d, Module.finrank k (Y.obj d)) < n := by
        rw [← hn, hdim]
        exact Nat.lt_add_of_pos_left hXpos
      obtain ⟨dX⟩ := ih (∑ d, Module.finrank k (X.obj d))
        hXlt X hXfinite rfl
      obtain ⟨dY⟩ := ih (∑ d, Module.finrank k (Y.obj d))
        hYlt Y hYfinite rfl
      let d := dX.biprod dY
      exact ⟨{
        n := d.n
        summand := d.summand
        indecomposable := d.indecomposable
        isoBiproduct := e.trans d.isoBiproduct }⟩

/-- A componentwise finite-dimensional module-valued functor on a category
with finitely many objects has only finitely many isomorphism classes of
indecomposable retracts. -/
def finiteIndecomposableRetractSpectrum_functor
    {D : Type v} [Category.{w} D] [Fintype D]
    (M : D ⥤ ModuleCat.{x} k)
    (hMfinite : ∀ X, Module.Finite k (M.obj X)) :
    FiniteIndecomposableRetractSpectrum M := by
  classical
  let d := Classical.choice
    (finiteIndecomposableDecomposition_functor_exists M hMfinite)
  have hsummandFinite (j : Fin d.n) (X : D) :
      Module.Finite k ((d.summand j).obj X) := by
    let i : d.summand j ⟶ M :=
      biproduct.ι d.summand j ≫ d.isoBiproduct.inv
    let p : M ⟶ d.summand j :=
      d.isoBiproduct.hom ≫ biproduct.π d.summand j
    letI : Module.Finite k (M.obj X) := hMfinite X
    apply Module.Finite.of_injective (i.app X).hom
    exact (show Function.LeftInverse (p.app X) (i.app X) from
      fun z => by
        change (i ≫ p).app X z = z
        simp [i, p, Category.assoc]).injective
  letI : ∀ j, IsLocalRing (CategoryTheory.End (d.summand j)) :=
    fun j => functor_end_isLocalRing (d.summand j)
      (hsummandFinite j) (d.indecomposable j)
  exact {
    n := d.n
    representative := d.summand
    complete := by
      intro N hN
      rintro ⟨i, p, hip⟩
      have hNfinite (X : D) : Module.Finite k (N.obj X) := by
        letI : Module.Finite k (M.obj X) := hMfinite X
        apply Module.Finite.of_injective (i.app X).hom
        exact (show Function.LeftInverse (p.app X) (i.app X) from
          fun z => by
            change (i ≫ p).app X z = z
            rw [hip]
            rfl).injective
      letI : IsLocalRing (CategoryTheory.End N) :=
        functor_end_isLocalRing N hNfinite hN
      apply indecomposable_retract_biproduct_iso_summand d.summand
      exact ⟨i ≫ d.isoBiproduct.hom,
        d.isoBiproduct.inv ≫ p, by
          simp only [Category.assoc, Iso.hom_inv_id_assoc, hip]⟩ }

/-- Quiver-representation specialization of the generic functor retract
spectrum theorem. -/
def finiteIndecomposableRetractSpectrum_quiverRep
    {Q : Type v} [Quiver.{w} Q] [Fintype Q]
    (M : LinearPathCategory.QuiverRep k Q)
    (hfinite : ∀ q, Module.Finite k (M.obj q)) :
    FiniteIndecomposableRetractSpectrum M := by
  letI : Fintype (Paths Q) := Fintype.ofEquiv Q (Equiv.refl Q)
  exact finiteIndecomposableRetractSpectrum_functor M hfinite

/-- Every finite-dimensional module is a finite biproduct of indecomposable
modules.  The proof terminates on the `k`-dimension. -/
theorem finiteIndecomposableDecomposition_exists
    [Module.Finite k A] (M : ModuleCat.{v} A) [Module.Finite k M] :
    Nonempty (FiniteIndecomposableDecomposition M) := by
  classical
  generalize hn : Module.finrank k M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      by_cases hMzero : IsZero M
      · exact ⟨{
          n := 0
          summand := fun i => Fin.elim0 i
          indecomposable := fun i => Fin.elim0 i
          isoBiproduct := zeroIsoEmptyBiproduct M hMzero }⟩
      by_cases hMind : Indecomposable M
      · exact ⟨{
          n := 1
          summand := fun _ => M
          indecomposable := fun _ => hMind
          isoBiproduct := (biproductUniqueIso (fun _ : Fin 1 => M)).symm }⟩
      have hsplit : ∃ X Y : ModuleCat.{v} A, ∃ e : M ≅ X ⊞ Y,
          ¬ IsZero X ∧ ¬ IsZero Y := by
        rw [Indecomposable] at hMind
        push Not at hMind
        exact hMind hMzero
      obtain ⟨X, Y, e, hXzero, hYzero⟩ := hsplit
      let iX : X ⟶ M := biprod.inl ≫ e.inv
      let pX : M ⟶ X := e.hom ≫ biprod.fst
      have hiX : Function.Injective (iX.hom.restrictScalars k) :=
        (show Function.LeftInverse pX iX from fun x => by
          change (iX ≫ pX) x = x
          simp [iX, pX, Category.assoc]).injective
      letI : Module.Finite k X := Module.Finite.of_injective
        (iX.hom.restrictScalars k) hiX
      let iY : Y ⟶ M := biprod.inr ≫ e.inv
      let pY : M ⟶ Y := e.hom ≫ biprod.snd
      have hiY : Function.Injective (iY.hom.restrictScalars k) :=
        (show Function.LeftInverse pY iY from fun y => by
          change (iY ≫ pY) y = y
          simp [iY, pY, Category.assoc]).injective
      letI : Module.Finite k Y := Module.Finite.of_injective
        (iY.hom.restrictScalars k) hiY
      let eLinear : M ≃ₗ[k] X × Y :=
        ((e.trans (ModuleCat.biprodIsoProd X Y)).toLinearEquiv).restrictScalars k
      have hdim : Module.finrank k M =
          Module.finrank k X + Module.finrank k Y := by
        calc
          Module.finrank k M = Module.finrank k (X × Y) := eLinear.finrank_eq
          _ = Module.finrank k X + Module.finrank k Y := Module.finrank_prod
      have hXnontrivial : Nontrivial X :=
        not_subsingleton_iff_nontrivial.mp
          ((not_iff_not.mpr ModuleCat.isZero_iff_subsingleton).mp hXzero)
      have hYnontrivial : Nontrivial Y :=
        not_subsingleton_iff_nontrivial.mp
          ((not_iff_not.mpr ModuleCat.isZero_iff_subsingleton).mp hYzero)
      letI : Nontrivial X := hXnontrivial
      letI : Nontrivial Y := hYnontrivial
      have hXlt : Module.finrank k X < n := by
        rw [← hn, hdim]
        exact Nat.lt_add_of_pos_right Module.finrank_pos
      have hYlt : Module.finrank k Y < n := by
        rw [← hn, hdim]
        exact Nat.lt_add_of_pos_left Module.finrank_pos
      obtain ⟨dX⟩ := ih (Module.finrank k X) hXlt X rfl
      obtain ⟨dY⟩ := ih (Module.finrank k Y) hYlt Y rfl
      let d := dX.biprod dY
      exact ⟨{
        n := d.n
        summand := d.summand
        indecomposable := d.indecomposable
        isoBiproduct := e.trans d.isoBiproduct }⟩

/-- A fixed finite-dimensional module has only finitely many isomorphism
classes of indecomposable retracts. -/
def finiteIndecomposableRetractSpectrum_module
    [Module.Finite k A] (M : ModuleCat.{v} A) [Module.Finite k M] :
    FiniteIndecomposableRetractSpectrum M := by
  classical
  let hM : Module.Finite k M := inferInstance
  let d := Classical.choice
    (finiteIndecomposableDecomposition_exists (k := k) M)
  letI : ∀ j, Module.Finite k (d.summand j) :=
    fun j => d.summand_finite hM j
  letI : ∀ j, IsLocalRing (CategoryTheory.End (d.summand j)) :=
    fun j => moduleCat_end_isLocalRing
      (k := k) (A := A) (d.summand j) (d.indecomposable j)
  exact {
    n := d.n
    representative := d.summand
    complete := by
      intro N hN
      rintro ⟨i, p, hip⟩
      letI : Module.Finite k N := Module.Finite.of_injective
        (i.hom.restrictScalars k)
        ((show Function.LeftInverse p i from fun x => by
          change (i ≫ p) x = x
          rw [hip]
          rfl).injective)
      letI : IsLocalRing (CategoryTheory.End N) :=
        moduleCat_end_isLocalRing (k := k) (A := A) N hN
      apply indecomposable_retract_biproduct_iso_summand d.summand
      exact ⟨i ≫ d.isoBiproduct.hom, d.isoBiproduct.inv ≫ p, by
        simp only [Category.assoc, Iso.hom_inv_id_assoc, hip]⟩ }

end LargeIndecomposable.ClosedZigzagTransfer
