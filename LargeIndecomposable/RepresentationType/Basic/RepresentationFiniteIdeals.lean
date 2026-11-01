module

public import LargeIndecomposable.RepresentationType.Basic.RepresentationFinite
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

@[expose] public section

/-!
# Representation-finiteness and two-sided ideals

Every finite-dimensional module over a representation-finite algebra is a
finite direct sum of members of a fixed finite indecomposable family.  Since
annihilators turn direct sums into intersections and every two-sided ideal is
the annihilator of its regular quotient, the two-sided ideal lattice is finite.
-/

set_option autoImplicit false
noncomputable section

namespace LargeIndecomposable

open CategoryTheory
open CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u v

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]

private def quotientRestrictLinearEquiv (I : TwoSidedIdeal A)
    (M : ModuleCat.{v} (A ⧸ I.asIdeal)) :
    M ≃ₗ[k] (ModuleCat.restrictScalars (Ideal.Quotient.mk I.asIdeal)).obj M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change (algebraMap k (A ⧸ I.asIdeal) c) • x =
      Ideal.Quotient.mk I.asIdeal (algebraMap k A c) • x
    rfl

private def quotientRestrictLift (I : TwoSidedIdeal A)
    {M N : ModuleCat.{v} (A ⧸ I.asIdeal)}
    (g : (ModuleCat.restrictScalars (Ideal.Quotient.mk I.asIdeal)).obj M ⟶
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I.asIdeal)).obj N) : M ⟶ N :=
  ModuleCat.ofHom {
    toFun := g
    map_add' := g.hom.map_add
    map_smul' := by
      intro b x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
      exact g.hom.map_smul a x }

private def quotientRestrictIso (I : TwoSidedIdeal A)
    {M N : ModuleCat.{v} (A ⧸ I.asIdeal)}
    (e : (ModuleCat.restrictScalars (Ideal.Quotient.mk I.asIdeal)).obj M ≅
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I.asIdeal)).obj N) : M ≅ N where
  hom := quotientRestrictLift I e.hom
  inv := quotientRestrictLift I e.inv
  hom_inv_id := by
    ext x
    change e.inv (e.hom x) = x
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp e.hom_inv_id) x
  inv_hom_id := by
    ext x
    change e.hom (e.inv x) = x
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp e.inv_hom_id) x

private theorem quotientRestrict_indecomposable (I : TwoSidedIdeal A)
    (M : ModuleCat.{v} (A ⧸ I.asIdeal)) (hM : Indecomposable M) :
    Indecomposable
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk I.asIdeal)).obj M) := by
  let q := Ideal.Quotient.mk I.asIdeal
  constructor
  · intro hzero
    apply hM.1
    rw [ModuleCat.isZero_iff_subsingleton] at hzero ⊢
    exact hzero
  · intro Y Z e
    let pY : Y ⟶ (ModuleCat.restrictScalars q).obj M := biprod.inl ≫ e.inv
    let rY : (ModuleCat.restrictScalars q).obj M ⟶ Y := e.hom ≫ biprod.fst
    have hpYrY : pY ≫ rY = 𝟙 Y := by simp [pY, rY, Category.assoc]
    have hleftY : Function.LeftInverse rY pY := by
      intro y
      change (pY ≫ rY) y = y
      rw [hpYrY]
      rfl
    let pZ : Z ⟶ (ModuleCat.restrictScalars q).obj M := biprod.inr ≫ e.inv
    let rZ : (ModuleCat.restrictScalars q).obj M ⟶ Z := e.hom ≫ biprod.snd
    have hpZrZ : pZ ≫ rZ = 𝟙 Z := by simp [pZ, rZ, Category.assoc]
    have hleftZ : Function.LeftInverse rZ pZ := by
      intro z
      change (pZ ≫ rZ) z = z
      rw [hpZrZ]
      rfl
    have hYtors : Module.IsTorsionBySet A Y I.asIdeal := by
      intro y a
      apply hleftY.injective
      change pY (a.1 • y) = pY 0
      rw [map_smul, map_zero]
      change q a.1 • pY y = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr a.2, zero_smul]
    have hZtors : Module.IsTorsionBySet A Z I.asIdeal := by
      intro z a
      apply hleftZ.injective
      change pZ (a.1 • z) = pZ 0
      rw [map_smul, map_zero]
      change q a.1 • pZ z = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr a.2, zero_smul]
    letI : Module (A ⧸ I.asIdeal) Y := hYtors.module
    letI : Module (A ⧸ I.asIdeal) Z := hZtors.module
    let YB : ModuleCat.{v} (A ⧸ I.asIdeal) := ModuleCat.of _ Y
    let ZB : ModuleCat.{v} (A ⧸ I.asIdeal) := ModuleCat.of _ Z
    let eA : (ModuleCat.restrictScalars q).obj M ≅ ModuleCat.of A (Y × Z) :=
      e.trans (ModuleCat.biprodIsoProd Y Z)
    let lA : (ModuleCat.restrictScalars q).obj M ≃ₗ[A] (Y × Z) :=
      eA.toLinearEquiv
    let lB : M ≃ₗ[A ⧸ I.asIdeal] (Y × Z) :=
      { toFun := lA
        invFun := lA.symm
        left_inv := lA.left_inv
        right_inv := lA.right_inv
        map_add' := lA.map_add
        map_smul' := by
          intro b x
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
          change lA (a • (show (ModuleCat.restrictScalars q).obj M from x)) =
            q a • lA x
          have hp : q a • lA x = a • lA x := by
            apply Prod.ext
            · exact hYtors.mk_smul a (lA x).1
            · exact hZtors.mk_smul a (lA x).2
          rw [hp]
          exact lA.map_smul a x }
    let eBProd : M ≅ ModuleCat.of (A ⧸ I.asIdeal) (Y × Z) :=
      lB.toModuleIso
    let eB : M ≅ YB ⊞ ZB :=
      eBProd.trans (ModuleCat.biprodIsoProd YB ZB).symm
    rcases hM.2 YB ZB eB with hYB | hZB
    · left
      rw [ModuleCat.isZero_iff_subsingleton] at hYB ⊢
      exact hYB
    · right
      rw [ModuleCat.isZero_iff_subsingleton] at hZB ⊢
      exact hZB

/-- Representation-finiteness descends to every algebra quotient. -/
theorem IsRepresentationFinite.quotient (hA : IsRepresentationFinite k A)
    (I : TwoSidedIdeal A) : IsRepresentationFinite k (A ⧸ I.asIdeal) := by
  obtain ⟨n, X, hX, hcover⟩ := hA
  let q := Ideal.Quotient.mk I.asIdeal
  let Occurs : Fin n → Prop := fun i =>
    ∃ M : ModuleCat.{v} (A ⧸ I.asIdeal),
      IsFiniteIndecomposable k (A ⧸ I.asIdeal) M ∧
        Nonempty ((ModuleCat.restrictScalars q).obj M ≅ X i)
  let C := {i : Fin n // Occurs i}
  letI : Fintype C := Fintype.ofFinite C
  let E : C ≃ Fin (Fintype.card C) := Fintype.equivFin C
  let Yc : C → ModuleCat.{v} (A ⧸ I.asIdeal) := fun i =>
    Classical.choose i.property
  have hYc (i : C) :
      IsFiniteIndecomposable k (A ⧸ I.asIdeal) (Yc i) ∧
        Nonempty ((ModuleCat.restrictScalars q).obj (Yc i) ≅ X i.1) :=
    Classical.choose_spec i.property
  refine ⟨Fintype.card C, fun j => Yc (E.symm j), ?_, ?_⟩
  · intro j
    exact (hYc (E.symm j)).1
  · intro M hM
    letI : Module.Finite k M := hM.1
    letI : Module.Finite k ((ModuleCat.restrictScalars q).obj M) :=
      Module.Finite.equiv (quotientRestrictLinearEquiv I M)
    have hMind : Indecomposable ((ModuleCat.restrictScalars q).obj M) :=
      quotientRestrict_indecomposable I M hM.2
    obtain ⟨i, ⟨eM⟩⟩ := hcover ((ModuleCat.restrictScalars q).obj M)
      ⟨inferInstance, hMind⟩
    let c : C := ⟨i, ⟨M, hM, ⟨eM⟩⟩⟩
    refine ⟨E c, ?_⟩
    change Nonempty (M ≅ Yc (E.symm (E c)))
    rw [E.symm_apply_apply]
    obtain ⟨eY⟩ := (hYc c).2
    exact ⟨quotientRestrictIso I (eM.trans eY.symm)⟩

/-- A finite-dimensional representation-finite algebra has only finitely many
two-sided ideals. -/
theorem IsRepresentationFinite.finite_twoSidedIdeal
    (hA : IsRepresentationFinite k A) [Module.Finite k A] :
    Finite (TwoSidedIdeal A) := by
  obtain ⟨n, X, _hX, hcover⟩ := hA
  let ann : ModuleCat.{v} A → TwoSidedIdeal A := fun M =>
    (Module.annihilator A M).toTwoSided
  have ann_iso {M N : ModuleCat.{v} A} (e : M ≅ N) :
      ann M = ann N := by
    apply TwoSidedIdeal.ext
    intro a
    simp only [ann, Ideal.mem_toTwoSided]
    rw [e.toLinearEquiv.annihilator_eq]
  have ann_prod (M N : ModuleCat.{v} A) :
      ann (ModuleCat.of A (M × N)) = ann M ⊓ ann N := by
    apply TwoSidedIdeal.ext
    intro a
    simp only [ann, Ideal.mem_toTwoSided, TwoSidedIdeal.mem_inf]
    rw [Module.annihilator_prod]
    rfl
  let P : ℕ → Prop := fun d =>
    ∀ (M : ModuleCat.{v} A) [Module.Finite k M],
      Module.finrank k M = d →
      ∃ s : Finset (Fin n), ann M = s.inf (fun i => ann (X i))
  have hP : ∀ d, P d := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro M hMfin hMdim
        by_cases hMzero : IsZero M
        · refine ⟨∅, ?_⟩
          rw [Finset.inf_empty]
          apply TwoSidedIdeal.ext
          intro a
          simp only [ann, Ideal.mem_toTwoSided]
          constructor
          · exact fun _ => TwoSidedIdeal.mem_top A
          · intro _
            rw [Module.mem_annihilator]
            intro m
            exact (ModuleCat.isZero_iff_subsingleton.mp hMzero).elim _ _
        by_cases hMind : Indecomposable M
        · obtain ⟨i, ⟨e⟩⟩ := hcover M ⟨inferInstance, hMind⟩
          refine ⟨{i}, ?_⟩
          rw [Finset.inf_singleton]
          exact ann_iso e
        · rw [Indecomposable] at hMind
          push Not at hMind
          rcases hMind hMzero with ⟨Y, Z, e, hY, hZ⟩
          let pY : Y ⟶ M := biprod.inl ≫ e.inv
          let rY : M ⟶ Y := e.hom ≫ biprod.fst
          have hpYrY : pY ≫ rY = 𝟙 Y := by
            simp [pY, rY, Category.assoc]
          have hleftY : Function.LeftInverse rY pY := by
            intro y
            change (pY ≫ rY) y = y
            rw [hpYrY]
            rfl
          letI : Module.Finite k Y :=
            Module.Finite.of_injective (pY.hom.restrictScalars k)
              hleftY.injective
          let pZ : Z ⟶ M := biprod.inr ≫ e.inv
          let rZ : M ⟶ Z := e.hom ≫ biprod.snd
          have hpZrZ : pZ ≫ rZ = 𝟙 Z := by
            simp [pZ, rZ, Category.assoc]
          have hleftZ : Function.LeftInverse rZ pZ := by
            intro z
            change (pZ ≫ rZ) z = z
            rw [hpZrZ]
            rfl
          letI : Module.Finite k Z :=
            Module.Finite.of_injective (pZ.hom.restrictScalars k)
              hleftZ.injective
          have hYnsub : ¬ Subsingleton Y :=
            (not_iff_not.2 ModuleCat.isZero_iff_subsingleton).1 hY
          have hZnsub : ¬ Subsingleton Z :=
            (not_iff_not.2 ModuleCat.isZero_iff_subsingleton).1 hZ
          letI : Nontrivial Y := not_subsingleton_iff_nontrivial.mp hYnsub
          letI : Nontrivial Z := not_subsingleton_iff_nontrivial.mp hZnsub
          have hdim : Module.finrank k M =
              Module.finrank k Y + Module.finrank k Z := by
            calc
              Module.finrank k M =
                  Module.finrank k (Y ⊞ Z : ModuleCat.{v} A) :=
                LinearEquiv.finrank_eq
                  (e.toLinearEquiv.restrictScalars k)
              _ = Module.finrank k (ModuleCat.of A (Y × Z)) :=
                LinearEquiv.finrank_eq
                  ((ModuleCat.biprodIsoProd Y Z).toLinearEquiv.restrictScalars k)
              _ = Module.finrank k Y + Module.finrank k Z :=
                Module.finrank_prod
          have hYlt : Module.finrank k Y < d := by
            rw [← hMdim, hdim]
            exact Nat.lt_add_of_pos_right Module.finrank_pos
          have hZlt : Module.finrank k Z < d := by
            rw [← hMdim, hdim]
            exact Nat.lt_add_of_pos_left Module.finrank_pos
          obtain ⟨sY, hsY⟩ := ih (Module.finrank k Y) hYlt Y rfl
          obtain ⟨sZ, hsZ⟩ := ih (Module.finrank k Z) hZlt Z rfl
          refine ⟨sY ∪ sZ, ?_⟩
          rw [Finset.inf_union, ← hsY, ← hsZ]
          exact (ann_iso e).trans <|
            (ann_iso (ModuleCat.biprodIsoProd Y Z)).trans (ann_prod Y Z)
  let decode : Finset (Fin n) → TwoSidedIdeal A := fun s =>
    s.inf (fun i => ann (X i))
  apply Finite.of_surjective decode
  intro I
  let M : ModuleCat.{v} A := ModuleCat.of A (A ⧸ I.asIdeal)
  letI : Module k M :=
    ModuleCat.Algebra.instModuleCarrier (S₀ := k) (S := A) (M := M)
  let qA : A →ₗ[A] M := I.asIdeal.mkQ
  let qk : A →ₗ[k] M :=
    { toFun := qA
      map_add' := qA.map_add
      map_smul' := by
        intro c x
        rw [Algebra.smul_def]
        exact qA.map_smul (algebraMap k A c) x }
  have hMfin : Module.Finite k M :=
    Module.Finite.of_surjective qk (by
      simpa [qk, qA] using I.asIdeal.mkQ_surjective)
  obtain ⟨s, hs⟩ := @hP (Module.finrank k M) M hMfin rfl
  refine ⟨s, ?_⟩
  change s.inf (fun i => ann (X i)) = I
  rw [← hs]
  apply TwoSidedIdeal.ext
  intro a
  simp only [ann, Ideal.mem_toTwoSided]
  change a ∈ Module.annihilator A (A ⧸ I.asIdeal) ↔ a ∈ I
  rw [Ideal.annihilator_quotient]
  rfl

end LargeIndecomposable
