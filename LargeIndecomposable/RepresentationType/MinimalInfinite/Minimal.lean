module

public import LargeIndecomposable.Modules.Corners.BasicCorner
public import LargeIndecomposable.Modules.Morita.Inflation
public import LargeIndecomposable.Modules.KrullSchmidt.IndecomposableFullyFaithful
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Minimal representation-infinite quotients

The second step of Lemma 3.1: a representation-infinite finite-dimensional
algebra has a minimal representation-infinite quotient (one of least
dimension), and quotients of split basic algebras are split basic.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Statement

universe u

/-- A ring is minimal representation-infinite if it is representation-infinite
and all its proper quotients are representation-finite. -/
def IsMinimalRepInfinite (B : Type u) [Ring B] : Prop :=
  ¬ IsRepresentationFinite B ∧
    ∀ I : TwoSidedIdeal B, I ≠ ⊥ → IsRepresentationFinite (B ⧸ I.asIdeal)

section Transfer

variable {R S : Type u} [Ring R] [Ring S]

/-- Representation-finiteness is invariant under ring isomorphisms. -/
theorem isRepresentationFinite_of_ringEquiv (φ : R ≃+* S) (hR : IsRepresentationFinite R) :
    IsRepresentationFinite S := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := ModuleCat.restrictScalars φ.symm.toRingHom
  have : F.Full := Reduction.restrictScalars_full (π := φ.symm.toRingHom) φ.symm.surjective
  refine Reduction.isRepresentationFinite_of_two hR hR F F fun M _ _ ↦ Or.inl ?_
  let N : ModuleCat.{u} R := (ModuleCat.restrictScalars φ.toRingHom).obj M
  have hN : Module.Finite R N := by
    obtain ⟨T, hT⟩ := (Module.Finite.fg_top : (⊤ : Submodule S M).FG)
    refine ⟨⟨T, eq_top_iff.2 fun m hm' ↦ ?_⟩⟩
    clear hm'
    have hm : m ∈ Submodule.span S (T : Set M) := hT ▸ trivial
    induction hm using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul s x _ hx =>
      convert Submodule.smul_mem _ (φ.symm s) hx using 1
      change s • x = φ (φ.symm s) • x
      rw [RingEquiv.apply_symm_apply]
  exact ⟨N, hN, ⟨(ModuleCat.restrictScalarsComp'App φ.symm.toRingHom φ.toRingHom (RingHom.id S)
    (by ext; simp) M).symm ≪≫ ModuleCat.restrictScalarsId'App (RingHom.id S) rfl M⟩⟩

end Transfer

section Quotient

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]

variable (k) in
include k in
/-- The image of the radical lies in the radical of a quotient. -/
lemma mk_mem_jacobson_of_fd (K : TwoSidedIdeal A) {x : A} (hx : x ∈ Ring.jacobson A) :
    Ideal.Quotient.mk K.asIdeal x ∈ Ring.jacobson (A ⧸ K.asIdeal) := by
  refine Corner.mem_jacobson_of_forall_isUnit fun y' ↦ ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y'
  obtain ⟨N, hN⟩ := Corner.isNilpotent_of_mem_jacobson k ((Ring.jacobson A).mul_mem_left y hx)
  refine IsNilpotent.isUnit_one_sub ⟨N, ?_⟩
  rw [← map_mul, ← map_pow, hN, map_zero]

open scoped Classical in
/-- A quotient of a split basic algebra is split basic, with the nonzero
images of the idempotents. -/
def SplitBasicData.quotientNZ {ι : Type} [Fintype ι] (S : SplitBasicData k A ι)
    (K : TwoSidedIdeal A) :
    SplitBasicData k (A ⧸ K.asIdeal) {x : ι // Ideal.Quotient.mk K.asIdeal (S.e x) ≠ 0} where
  e x := Ideal.Quotient.mk K.asIdeal (S.e x.1)
  complete := by
    refine ⟨⟨fun x ↦ (S.complete.idem x.1).map _, fun x y hxy ↦ ?_⟩, ?_⟩
    · show _ * _ = 0
      rw [← map_mul, S.complete.ortho (fun h ↦ hxy (Subtype.ext h)), map_zero]
    · have h := Fintype.sum_subtype_add_sum_subtype
        (fun x ↦ Ideal.Quotient.mk K.asIdeal (S.e x) ≠ 0)
        (fun x ↦ Ideal.Quotient.mk K.asIdeal (S.e x))
      have h0 : ∑ x : {x // ¬ Ideal.Quotient.mk K.asIdeal (S.e x) ≠ 0},
          Ideal.Quotient.mk K.asIdeal (S.e x) = 0 :=
        Finset.sum_eq_zero fun x _ ↦ not_not.1 x.2
      rw [h0, add_zero] at h
      rw [h, ← map_sum, S.complete.complete, map_one]
  ne_zero x := x.2
  corner_diag x b := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨c, hc⟩ := S.corner_diag x.1 b
    refine ⟨c, ?_⟩
    have := mk_mem_jacobson_of_fd (k := k) K hc
    have e : Ideal.Quotient.mk K.asIdeal (S.e x.1 * b * S.e x.1 - c • S.e x.1) =
        Ideal.Quotient.mk K.asIdeal (S.e x.1) * Ideal.Quotient.mk K.asIdeal b *
          Ideal.Quotient.mk K.asIdeal (S.e x.1) - c • Ideal.Quotient.mk K.asIdeal (S.e x.1) := by
      rw [map_sub, map_mul, map_mul]
      congr 1
    exact e ▸ this
  corner_offdiag x y hxy b := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have := mk_mem_jacobson_of_fd (k := k) K (S.corner_offdiag x.1 y.1 (fun h ↦ hxy (Subtype.ext h)) b)
    rwa [map_mul, map_mul] at this

/-- The quotient by the kernel of a surjection, as a two-sided ideal. -/
def quotKerEquiv {S : Type u} [Ring S] (ψ : A →+* S) (hψ : Function.Surjective ψ) :
    A ⧸ (TwoSidedIdeal.ker ψ).asIdeal ≃+* S :=
  (Ideal.quotEquivOfEq (by ext x; simp [TwoSidedIdeal.mem_asIdeal, TwoSidedIdeal.mem_ker,
    RingHom.mem_ker])).trans (RingHom.quotientKerEquivOfSurjective hψ)

/-- The dimension of a two-sided ideal. -/
def idealDim (K : TwoSidedIdeal A) : ℕ := Module.finrank k (K.asIdeal.restrictScalars k)

lemma idealDim_lt {K K' : TwoSidedIdeal A} (h : K < K') : idealDim (k := k) K < idealDim (k := k) K' :=
  Submodule.finrank_lt_finrank_of_lt (by
    refine lt_of_le_of_ne (fun x hx ↦ ?_) fun he ↦ h.ne ?_
    · exact (TwoSidedIdeal.mem_asIdeal).2 (h.le ((TwoSidedIdeal.mem_asIdeal).1 hx))
    · ext x
      have := congrArg (x ∈ ·) he
      simpa [TwoSidedIdeal.mem_asIdeal] using this)

variable (k) in
include k in
/-- Lemma 3.1, second step: a representation-infinite finite-dimensional
algebra has a minimal representation-infinite quotient. -/
theorem exists_minimalRepInfinite_quotient (h : ¬ IsRepresentationFinite A) :
    ∃ K : TwoSidedIdeal A, IsMinimalRepInfinite (A ⧸ K.asIdeal) := by
  classical
  let P : ℕ → Prop := fun d ↦
    ∃ K : TwoSidedIdeal A, ¬ IsRepresentationFinite (A ⧸ K.asIdeal) ∧ idealDim (k := k) K = d
  have hP0 : P (idealDim (k := k) (TwoSidedIdeal.ker (RingHom.id A))) :=
    ⟨_, fun hf ↦ h (isRepresentationFinite_of_ringEquiv
      (quotKerEquiv (RingHom.id A) Function.surjective_id) hf), rfl⟩
  have hbound : ∀ d, P d → d ≤ Module.finrank k A := fun d ⟨K, _, hK⟩ ↦
    hK ▸ Submodule.finrank_le _
  let d₀ := Nat.findGreatest P (Module.finrank k A)
  obtain ⟨K, hK, hKd⟩ : P d₀ :=
    Nat.findGreatest_spec (hbound _ hP0) hP0
  refine ⟨K, hK, fun I hI ↦ ?_⟩
  by_contra hfin
  let ψ : A →+* (A ⧸ K.asIdeal) ⧸ I.asIdeal :=
    (Ideal.Quotient.mk I.asIdeal).comp (Ideal.Quotient.mk K.asIdeal)
  have hψ : Function.Surjective ψ :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  have hK' : P (idealDim (k := k) (TwoSidedIdeal.ker ψ)) :=
    ⟨_, fun hf ↦ hfin (isRepresentationFinite_of_ringEquiv (quotKerEquiv ψ hψ) hf), rfl⟩
  have hlt : K < TwoSidedIdeal.ker ψ := by
    refine lt_of_le_of_ne (fun x hx ↦ ?_) fun he ↦ hI ?_
    · rw [TwoSidedIdeal.mem_ker]
      change Ideal.Quotient.mk I.asIdeal (Ideal.Quotient.mk K.asIdeal x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.2 ((TwoSidedIdeal.mem_asIdeal).2 hx), map_zero]
    · rw [eq_bot_iff]
      intro b hb
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
      have ha : a ∈ TwoSidedIdeal.ker ψ := by
        rw [TwoSidedIdeal.mem_ker]
        exact Ideal.Quotient.eq_zero_iff_mem.2 ((TwoSidedIdeal.mem_asIdeal).2 hb)
      rw [← he] at ha
      rw [TwoSidedIdeal.mem_bot]
      exact Ideal.Quotient.eq_zero_iff_mem.2 ((TwoSidedIdeal.mem_asIdeal).2 ha)
  have := Nat.le_findGreatest (hbound _ hK') hK'
  have := idealDim_lt (k := k) hlt
  omega

end Quotient

end LargeIndecomposable
