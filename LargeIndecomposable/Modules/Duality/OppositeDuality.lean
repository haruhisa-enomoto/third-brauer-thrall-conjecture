module

public import LargeIndecomposable.Modules.KrullSchmidt.IndecomposableFullyFaithful
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import LargeIndecomposable.RepresentationType.MinimalInfinite.Minimal

/-!
# `k`-duality and the opposite algebra

For a `k`-algebra `R` and an `R`-module `M` with a compatible `k`-structure,
the `k`-dual `M →ₗ[k] k` is an `Rᵐᵒᵖ`-module (`DualMod`). For finite-dimensional
`R`, duality shows that `R` is representation-finite iff `Rᵐᵒᵖ` is
(`isRepresentationFinite_mop`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory MulOpposite Statement Reduction

universe u

variable {k : Type u} [Field k] {R : Type u} [Ring R] [Algebra k R]

section DualMod

variable (k) (M : Type u) [AddCommGroup M] [Module k M]

/-- The `k`-dual of a `k`-module (with the transposed actions). -/
structure DualMod where
  /-- The underlying functional. -/
  val : M →ₗ[k] k

namespace DualMod

variable {k M}

lemma val_injective : Function.Injective (DualMod.val : DualMod k M → _) := by
  intro φ ψ h; cases φ; cases ψ; congr

instance : Zero (DualMod k M) := ⟨⟨0⟩⟩
instance : Add (DualMod k M) := ⟨fun φ ψ ↦ ⟨φ.val + ψ.val⟩⟩
instance : Neg (DualMod k M) := ⟨fun φ ↦ ⟨-φ.val⟩⟩
instance : Sub (DualMod k M) := ⟨fun φ ψ ↦ ⟨φ.val - ψ.val⟩⟩
instance : SMul ℕ (DualMod k M) := ⟨fun n φ ↦ ⟨n • φ.val⟩⟩
instance : SMul ℤ (DualMod k M) := ⟨fun n φ ↦ ⟨n • φ.val⟩⟩
instance : SMul k (DualMod k M) := ⟨fun c φ ↦ ⟨c • φ.val⟩⟩

instance : AddCommGroup (DualMod k M) :=
  val_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl)

/-- The underlying additive map. -/
def valHom : DualMod k M →+ (M →ₗ[k] k) := ⟨⟨DualMod.val, rfl⟩, fun _ _ ↦ rfl⟩

instance : Module k (DualMod k M) := val_injective.module k valHom (fun _ _ ↦ rfl)

@[simp] lemma val_add (φ ψ : DualMod k M) : (φ + ψ).val = φ.val + ψ.val := rfl

@[simp] lemma val_zero : (0 : DualMod k M).val = 0 := rfl

@[simp] lemma val_smul (c : k) (φ : DualMod k M) : (c • φ).val = c • φ.val := rfl

@[ext] lemma ext {φ ψ : DualMod k M} (h : ∀ m, φ.val m = ψ.val m) : φ = ψ := by
  cases φ; cases ψ; congr 1; exact LinearMap.ext h

/-- `DualMod k M` is the `k`-dual. -/
def linEquiv : DualMod k M ≃ₗ[k] Module.Dual k M where
  toFun := DualMod.val
  invFun := DualMod.mk
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

lemma finrank_eq [FiniteDimensional k M] : Module.finrank k (DualMod k M) = Module.finrank k M :=
  (linEquiv.finrank_eq).trans (Subspace.dual_finrank_eq)

instance [FiniteDimensional k M] : FiniteDimensional k (DualMod k M) :=
  Module.Finite.equiv linEquiv.symm

variable [Module R M] [IsScalarTower k R M]

instance (priority := 50) : SMul Rᵐᵒᵖ (DualMod k M) where
  smul r φ := ⟨φ.val ∘ₗ Module.toModuleEnd k M r.unop⟩

@[simp] lemma smul_apply (r : Rᵐᵒᵖ) (φ : DualMod k M) (m : M) :
    (r • φ).val m = φ.val (r.unop • m) := rfl

instance (priority := 50) : Module Rᵐᵒᵖ (DualMod k M) where
  one_smul φ := ext fun m ↦ by simp
  mul_smul r s φ := ext fun m ↦ by simp [mul_smul]
  smul_zero r := ext fun m ↦ by simp
  smul_add r φ ψ := ext fun m ↦ by simp
  add_smul r s φ := ext fun m ↦ by simp [add_smul]
  zero_smul φ := ext fun m ↦ by simp

instance : IsScalarTower k Rᵐᵒᵖ (DualMod k M) where
  smul_assoc c r φ := ext fun m ↦ by
    simp only [smul_apply, val_smul, LinearMap.smul_apply]
    rw [show (c • r).unop = c • r.unop from rfl, smul_assoc, φ.val.map_smul]

end DualMod

end DualMod

section DualOp

variable (k) (N : Type u) [AddCommGroup N] [Module k N] [Module Rᵐᵒᵖ N] [IsScalarTower k Rᵐᵒᵖ N]

namespace DualMod

/-- The dual of an `Rᵐᵒᵖ`-module is an `R`-module. -/
instance (priority := 50) instSMulR : SMul R (DualMod k N) where
  smul r φ := ⟨φ.val ∘ₗ Module.toModuleEnd k N (op r)⟩

variable {k N}

@[simp] lemma smulR_apply (r : R) (φ : DualMod k N) (n : N) :
    (r • φ).val n = φ.val (op r • n) := rfl

instance (priority := 50) instModuleR : Module R (DualMod k N) where
  one_smul φ := ext fun m ↦ by simp
  mul_smul r s φ := ext fun m ↦ by simp [mul_smul]
  smul_zero r := ext fun m ↦ by simp
  smul_add r φ ψ := ext fun m ↦ by simp
  add_smul r s φ := ext fun m ↦ by simp [add_smul]
  zero_smul φ := ext fun m ↦ by simp

instance : IsScalarTower k R (DualMod k N) where
  smul_assoc c r φ := ext fun n ↦ by
    simp only [smulR_apply, val_smul, LinearMap.smul_apply]
    rw [show op (c • r) = c • op r from rfl, smul_assoc, φ.val.map_smul]

/-- Evaluation into the double dual. -/
def ev : N →ₗ[Rᵐᵒᵖ] DualMod k (DualMod k N) where
  toFun n := ⟨⟨⟨fun φ ↦ φ.val n, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩⟩
  map_add' n n' := ext fun φ ↦ by simp
  map_smul' r n := ext fun φ ↦ by
    change φ.val (r • n) = φ.val (op r.unop • n)
    rw [op_unop]

lemma ev_injective [FiniteDimensional k N] : Function.Injective (ev (R := R) (k := k) (N := N)) := by
  intro n n' h
  rw [← sub_eq_zero]
  apply (Module.forall_dual_apply_eq_zero_iff k (n - n')).1
  intro φ
  have := congrArg (fun ψ : DualMod k (DualMod k N) ↦ ψ.val ⟨φ⟩) h
  simp only [ev] at this
  rw [map_sub, sub_eq_zero]
  exact this

lemma ev_val (n : N) (φ : DualMod k N) : (ev (R := R) n).val φ = φ.val n := rfl

/-- Evaluation as a `k`-linear map. -/
def evk : N →ₗ[k] DualMod k (DualMod k N) where
  toFun := ev (R := R)
  map_add' := (ev (R := R)).map_add
  map_smul' c n := ext fun φ ↦ φ.val.map_smul c n

lemma ev_bijective [FiniteDimensional k N] : Function.Bijective (ev (R := R) (k := k) (N := N)) := by
  refine ⟨ev_injective (R := R), ?_⟩
  have hinj : Function.Injective (evk (R := R) (k := k) (N := N)) := ev_injective (R := R)
  rw [LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [finrank_eq, finrank_eq])]
    at hinj
  exact hinj

/-- The double dual isomorphism. -/
def evEquiv [FiniteDimensional k N] : N ≃ₗ[Rᵐᵒᵖ] DualMod k (DualMod k N) :=
  LinearEquiv.ofBijective ev ev_bijective

/-- The transpose of an `R`-linear endomorphism of the dual. -/
def transpose (e : DualMod k N →ₗ[R] DualMod k N) :
    DualMod k (DualMod k N) →ₗ[Rᵐᵒᵖ] DualMod k (DualMod k N) where
  toFun ψ := ⟨ψ.val ∘ₗ e.restrictScalars k⟩
  map_add' _ _ := rfl
  map_smul' r ψ := ext fun φ ↦ by
    simp only [smul_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      RingHom.id_apply]
    rw [e.map_smul]

lemma transpose_apply (e : DualMod k N →ₗ[R] DualMod k N) (ψ : DualMod k (DualMod k N))
    (φ : DualMod k N) : (transpose e ψ).val φ = ψ.val (e φ) := rfl

lemma transpose_comp (e e' : DualMod k N →ₗ[R] DualMod k N) :
    transpose (e ∘ₗ e') = transpose e' ∘ₗ transpose e := rfl

lemma eq_zero_of_dual {X : Type u} [AddCommGroup X] [Module k X] (x : X)
    (h : ∀ ψ : DualMod k X, ψ.val x = 0) : x = 0 :=
  (Module.forall_dual_apply_eq_zero_iff k x).1 fun φ ↦ h ⟨φ⟩

/-- The dual of a finite-dimensional indecomposable `Rᵐᵒᵖ`-module is indecomposable. -/
lemma isIndecomposable [FiniteDimensional k N] (hN : IsIndecomposable Rᵐᵒᵖ N) :
    IsIndecomposable R (DualMod k N) := by
  rw [show IsIndecomposable R (DualMod k N) ↔ IsIndecomposable R (ModuleCat.of R (DualMod k N))
    from Iff.rfl, isIndecomposable_iff]
  rw [show IsIndecomposable Rᵐᵒᵖ N ↔ IsIndecomposable Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ N) from Iff.rfl,
    isIndecomposable_iff] at hN
  obtain ⟨hN0, hN⟩ := hN
  refine ⟨fun h0 ↦ hN0 ?_, fun f hf ↦ ?_⟩
  · rw [isZero_iff_not_nontrivial, not_nontrivial_iff_subsingleton] at h0 ⊢
    haveI := h0
    constructor
    intro n n'
    rw [← sub_eq_zero]
    exact eq_zero_of_dual (k := k) _ fun φ ↦ by
      rw [show φ = 0 from Subsingleton.elim _ _]
      rfl
  · let e : DualMod k N →ₗ[R] DualMod k N := f.hom
    have he : e ∘ₗ e = e := by
      change (f ≫ f).hom = f.hom
      rw [hf]
    let E := evEquiv (R := R) (k := k) (N := N)
    let g : N →ₗ[Rᵐᵒᵖ] N := E.symm.toLinearMap ∘ₗ transpose e ∘ₗ E.toLinearMap
    have hg : g ∘ₗ g = g := by
      apply LinearMap.ext
      intro n
      simp only [g, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply]
      congr 1
      rw [← LinearMap.comp_apply (transpose e), ← transpose_comp, he]
    rcases hN (ModuleCat.ofHom g) (by ext n; exact congrArg (fun h ↦ h n) hg) with h0 | h1
    · left
      refine ModuleCat.hom_ext (LinearMap.ext fun φ ↦ ?_)
      change e φ = 0
      apply eq_zero_of_dual (k := k)
      intro ψ
      obtain ⟨n, rfl⟩ := E.surjective ψ
      have := congrArg (fun h ↦ E (h.hom n)) h0
      simp only [ModuleCat.hom_ofHom, g, LinearMap.coe_comp, Function.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
      have h2 := congrArg (fun ψ : DualMod k (DualMod k N) ↦ ψ.val φ) this
      simpa [transpose_apply] using h2
    · right
      refine ModuleCat.hom_ext (LinearMap.ext fun φ ↦ ?_)
      change e φ = φ
      rw [← sub_eq_zero]
      apply eq_zero_of_dual (k := k)
      intro ψ
      obtain ⟨n, rfl⟩ := E.surjective ψ
      have := congrArg (fun h ↦ E (h.hom n)) h1
      simp only [ModuleCat.hom_ofHom, g, LinearMap.coe_comp, Function.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
      have h2 := congrArg (fun ψ : DualMod k (DualMod k N) ↦ ψ.val φ) this
      simp only [transpose_apply] at h2
      rw [map_sub, sub_eq_zero]
      simpa using h2

end DualMod

end DualOp

end LargeIndecomposable

namespace LargeIndecomposable

open CategoryTheory MulOpposite Statement Reduction

universe u

variable {k : Type u} [Field k] {R : Type u} [Ring R] [Algebra k R]

namespace DualMod

variable {X Y : Type u} [AddCommGroup X] [Module k X] [Module R X] [IsScalarTower k R X]
  [AddCommGroup Y] [Module k Y] [Module R Y] [IsScalarTower k R Y]

/-- Duality on isomorphisms (contravariant). -/
def congr (e : X ≃ₗ[R] Y) : DualMod k Y ≃ₗ[Rᵐᵒᵖ] DualMod k X where
  toFun ψ := ⟨ψ.val ∘ₗ e.toLinearMap.restrictScalars k⟩
  invFun ψ := ⟨ψ.val ∘ₗ e.symm.toLinearMap.restrictScalars k⟩
  map_add' _ _ := rfl
  map_smul' r ψ := ext fun x ↦ by
    simp only [smul_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe, RingHom.id_apply]
    rw [e.map_smul]
  left_inv ψ := ext fun x ↦ by simp
  right_inv ψ := ext fun x ↦ by simp

end DualMod

/-- The `k`-structure of an `R`-module through `algebraMap`. -/
abbrev kStr (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] (M : Type u)
    [AddCommGroup M] [Module R M] : Module k M :=
  Module.compHom M (algebraMap k R)

lemma kStr_tower (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] (M : Type u)
    [AddCommGroup M] [Module R M] :
    letI := kStr k (R := R) M
    IsScalarTower k R M := by
  letI := kStr k (R := R) M
  exact ⟨fun c r m ↦ by
    change (c • r) • m = algebraMap k R c • (r • m)
    rw [Algebra.smul_def, mul_smul]⟩

/-- **Duality.** A finite-dimensional representation-finite algebra has a
representation-finite opposite algebra. -/
theorem isRepresentationFinite_mop [FiniteDimensional k R] (h : IsRepresentationFinite R) :
    IsRepresentationFinite Rᵐᵒᵖ := by
  obtain ⟨n, B, hB⟩ := h
  let D : Fin n → ModuleCat.{u} Rᵐᵒᵖ := fun i ↦
    letI := kStr k (R := R) (B i)
    haveI := kStr_tower k (R := R) (B i)
    ModuleCat.of Rᵐᵒᵖ (DualMod k (B i))
  refine ⟨n, D, fun N _ _ _ hN ↦ ?_⟩
  letI := kStr k (R := Rᵐᵒᵖ) N
  haveI := kStr_tower k (R := Rᵐᵒᵖ) N
  haveI : Module.Finite k Rᵐᵒᵖ := Module.Finite.equiv (MulOpposite.opLinearEquiv k)
  haveI : FiniteDimensional k N := Module.Finite.trans Rᵐᵒᵖ N
  haveI : Module.Finite R (DualMod k N) := Module.Finite.of_restrictScalars_finite k R _
  obtain ⟨i, ⟨φ⟩⟩ := hB (DualMod k N) (DualMod.isIndecomposable hN)
  letI := kStr k (R := R) (B i)
  haveI := kStr_tower k (R := R) (B i)
  exact ⟨i, ⟨DualMod.evEquiv.trans (DualMod.congr φ.symm)⟩⟩

end LargeIndecomposable

namespace LargeIndecomposable

open CategoryTheory MulOpposite Statement Reduction

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]

/-- `Aᵐᵒᵖ ⧸ J ≅ (A ⧸ J.unop)ᵐᵒᵖ`. -/
def quotOpEquiv (J : TwoSidedIdeal Aᵐᵒᵖ) :
    Aᵐᵒᵖ ⧸ J.asIdeal ≃+* (A ⧸ J.unop.asIdeal)ᵐᵒᵖ := by
  let f : Aᵐᵒᵖ →+* (A ⧸ J.unop.asIdeal)ᵐᵒᵖ := (Ideal.Quotient.mk J.unop.asIdeal).op
  have hf : Function.Surjective f := fun x ↦ by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x.unop
    exact ⟨op a, by simp [f, ha]⟩
  have hker : RingHom.ker f = J.asIdeal := by
    ext x
    simp only [RingHom.mem_ker, f, RingHom.op_apply_apply, op_eq_zero_iff,
      Ideal.Quotient.eq_zero_iff_mem, TwoSidedIdeal.mem_asIdeal, TwoSidedIdeal.mem_unop_iff,
      Function.comp_apply, op_unop]
  exact (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hf)

/-- **Minimality is self-dual.** If every proper quotient of `A` is
representation-finite, so is every proper quotient of `Aᵐᵒᵖ`. -/
theorem hmin_op [FiniteDimensional k A]
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → IsRepresentationFinite (A ⧸ I.asIdeal))
    (J : TwoSidedIdeal Aᵐᵒᵖ) (hJ : J ≠ ⊥) : IsRepresentationFinite (Aᵐᵒᵖ ⧸ J.asIdeal) := by
  have hI : J.unop ≠ ⊥ := fun h ↦ hJ (by
    have := congrArg TwoSidedIdeal.op h
    rw [show J.unop.op = J from TwoSidedIdeal.opOrderIso.apply_symm_apply J] at this
    rw [this]
    ext x
    simp)
  have hfin : IsRepresentationFinite ((A ⧸ J.unop.asIdeal)ᵐᵒᵖ) :=
    isRepresentationFinite_mop (k := k) (hmin _ hI)
  exact isRepresentationFinite_of_ringEquiv (quotOpEquiv J).symm hfin

end LargeIndecomposable
