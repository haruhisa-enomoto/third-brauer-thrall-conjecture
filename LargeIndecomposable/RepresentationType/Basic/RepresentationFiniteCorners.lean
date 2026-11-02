module

public import LargeIndecomposable.Modules.Morita.FullIdempotentMorita
public import LargeIndecomposable.Cleaving.ClosedChains.GenericFiniteness

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace LargeIndecomposable

open CategoryTheory
open CategoryTheory.Limits
open scoped ModuleCat.Algebra TensorProduct

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

universe u v

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {e : A} (he : IsIdempotentElem e)

local notation "B" => he.Corner
local notation "P" => IsIdempotentElem.leftIdeal (k := k) (e := e)

local instance : Algebra k B := IsIdempotentElem.cornerAlgebra he
local instance (N : ModuleCat.{v} B) :
    HasQuotient (TensorProduct k P N) (Submodule k (TensorProduct k P N)) :=
  @Submodule.hasQuotient k (TensorProduct k P N) _ _ TensorProduct.instModule

open ClosedZigzagTransfer

/-- Representation-finiteness descends to the corner cut out by any
idempotent. -/
theorem IsRepresentationFinite.of_idempotentCorner
    (hA : IsRepresentationFinite k A) [Module.Finite k A] :
    IsRepresentationFinite k B := by
  classical
  let cornerProj : A →ₗ[k] B :=
    { toFun := fun a => ⟨e * a * e, ⟨a, rfl⟩⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        change e * (a + b) * e = e * a * e + e * b * e
        rw [mul_add, add_mul]
      map_smul' := by
        intro c a
        apply Subtype.ext
        simp only [RingHom.id_apply]
        change e * (c • a) * e =
          (algebraMap k A c * e) * (e * a * e)
        rw [Algebra.smul_def]
        calc
          e * (algebraMap k A c * a) * e =
              (e * algebraMap k A c) * a * e := by
            rw [← mul_assoc e (algebraMap k A c) a]
          _ = (algebraMap k A c * e) * a * e := by
            rw [← Algebra.commutes c e]
          _ = (algebraMap k A c * e) * (e * a * e) := by
            simp only [mul_assoc]
            rw [← mul_assoc e e (a * e), he] }
  have cornerProj_surjective : Function.Surjective cornerProj := by
    intro x
    refine ⟨x.1, Subtype.ext ?_⟩
    obtain ⟨hxleft, hxright⟩ := (Subsemigroup.mem_corner_iff he).mp x.2
    change e * x.1 * e = x.1
    rw [hxleft, hxright]
  letI : Module.Finite k B :=
    Module.Finite.of_surjective cornerProj cornerProj_surjective
  obtain ⟨n, X, hX, hcover⟩ := hA
  let R : ModuleCat.{v} A ⥤ ModuleCat.{v} B :=
    IsIdempotentElem.cornerPartFunctor (k := k) (A := A) he
  letI : R.Additive :=
    { map_add := by
        intro X Y f g
        apply ModuleCat.hom_ext
        rfl }
  have hRXfinite (i : Fin n) : Module.Finite k (R.obj (X i)) := by
    letI : Module.Finite k (X i) := (hX i).1
    exact IsIdempotentElem.cornerPartObj_moduleFinite (k := k) he (X i)
  let d (i : Fin n) : FiniteIndecomposableDecomposition (R.obj (X i)) := by
    letI : Module.Finite k (R.obj (X i)) := hRXfinite i
    exact Classical.choice
      (finiteIndecomposableDecomposition_exists (k := k) (R.obj (X i)))
  let C := Σ i : Fin n, Fin (d i).n
  letI : Fintype C := Fintype.ofFinite C
  let q : C ≃ Fin (Fintype.card C) := Fintype.equivFin C
  let Y : Fin (Fintype.card C) → ModuleCat.{v} B := fun j =>
    (d (q.symm j).1).summand (q.symm j).2
  refine ⟨Fintype.card C, Y, ?_, ?_⟩
  · intro j
    letI : Module.Finite k (R.obj (X (q.symm j).1)) :=
      hRXfinite (q.symm j).1
    exact ⟨(d (q.symm j).1).summand_finite inferInstance (q.symm j).2,
      (d (q.symm j).1).indecomposable (q.symm j).2⟩
  · intro N hN
    letI : Module.Finite k N := hN.1
    let E : ModuleCat.{v} A :=
      (IsIdempotentElem.relativeTensorFunctor (k := k) (A := A) he).obj N
    let hEraw : Module.Finite k
        (IsIdempotentElem.relativeTensor (k := k) (he := he) N) :=
      IsIdempotentElem.relativeTensor_moduleFinite (k := k) he N
    let eK :
        IsIdempotentElem.relativeTensor (k := k) (he := he) N ≃ₗ[k] E :=
      { toFun := fun z => z
        invFun := fun z => z
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := by
          intro c z
          induction z using Quotient.inductionOn' with
          | _ z =>
              change Quotient.mk'' (c • z) = Quotient.mk''
                (IsIdempotentElem.tensorLeftAction (k := k) (he := he) N
                  (algebraMap k A c) z)
              apply congrArg Quotient.mk''
              simpa [Algebra.smul_def,
                IsIdempotentElem.tensorLeftAction_one] using
                (IsIdempotentElem.tensorLeftAction_algebra_smul
                  (k := k) he N c 1 z).symm }
    letI : Module.Finite k E := by
      letI := hEraw
      exact Module.Finite.equiv eK
    let dE : FiniteIndecomposableDecomposition E :=
      Classical.choice (finiteIndecomposableDecomposition_exists (k := k) E)
    let eN : N ≅ ⨁ fun j => R.obj (dE.summand j) :=
      (IsIdempotentElem.relativeCounitNatIso (k := k) (A := A) he).app N |>.symm |>.trans
        ((R.mapIso dE.isoBiproduct).trans (R.mapBiproduct dE.summand))
    letI : IsLocalRing (End N) :=
      moduleCat_end_isLocalRing (k := k) (A := B) N hN.2
    obtain ⟨j, hNj⟩ := localEnd_retract_biproduct_retract_summand
      (fun j => R.obj (dE.summand j))
      (show IsRetractOf N (⨁ fun j => R.obj (dE.summand j)) from
        ⟨eN.hom, eN.inv, eN.hom_inv_id⟩)
    obtain ⟨i, ⟨eji⟩⟩ := hcover (dE.summand j)
      ⟨dE.summand_finite inferInstance j, dE.indecomposable j⟩
    obtain ⟨inc, proj, hip⟩ := hNj
    have hretXi : IsRetractOf N (R.obj (X i)) := by
      let re := R.mapIso eji
      exact ⟨inc ≫ re.hom, re.inv ≫ proj, by
        simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hip⟩
    letI : Module.Finite k (R.obj (X i)) := hRXfinite i
    letI : ∀ t, Module.Finite k ((d i).summand t) := fun t =>
      (d i).summand_finite inferInstance t
    letI : ∀ t, IsLocalRing (End ((d i).summand t)) := fun t =>
      moduleCat_end_isLocalRing (k := k) (A := B) ((d i).summand t)
        ((d i).indecomposable t)
    rcases hretXi with ⟨incXi, projXi, hcompXi⟩
    obtain ⟨t, hNt⟩ := indecomposable_retract_biproduct_iso_summand
      (d i).summand
      (show IsRetractOf N (⨁ (d i).summand) from
        ⟨incXi ≫ (d i).isoBiproduct.hom,
          (d i).isoBiproduct.inv ≫ projXi,
          by simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hcompXi⟩)
    let c : C := ⟨i, t⟩
    refine ⟨q c, ?_⟩
    change Nonempty (N ≅ (d (q.symm (q c)).1).summand (q.symm (q c)).2)
    rw [q.symm_apply_apply]
    exact hNt

end LargeIndecomposable
