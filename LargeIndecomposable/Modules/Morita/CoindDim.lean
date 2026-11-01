module

public import LargeIndecomposable.Modules.Morita.Coind
public import LargeIndecomposable.Modules.Duality.DimensionBasics
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.FieldTheory.Finiteness

/-!
# Linearity and dimensions for the Morita functor

For a `k`-algebra `A` and an idempotent `e`, the coinduction functor
`Morita.functor e : Mod eAe ⥤ Mod A` is `k`-linear. If `∑ᵢ₌₁ⁿ aᵢ e bᵢ = 1`,
then `dim M ≤ dim Hom_C(eA, M) ≤ n · dim M` (`le_dim`, `dim_le`); hence the
functor preserves finite-dimensionality and the dimension of every
infinite-dimensional module, as in the proof of Lemma 3.1.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement

universe u

namespace Morita

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A] {e : A}
  (he : IsIdempotentElem e)

theorem val_algebraMap (c : k) : Corner.val he (algebraMap k he.Corner c) = c • e := by
  rw [Algebra.algebraMap_eq_smul_one, Corner.val_smul, Corner.val_one]

theorem rmul_algebraMap (c : k) (x : rightIdeal e) :
    rmul he (algebraMap k A c) x = algebraMap k he.Corner c • x := by
  apply Subtype.ext
  rw [rmul_val, smul_val, val_algebraMap, ← Algebra.commutes, ← Algebra.smul_def,
    smul_mul_assoc, show e * (x : A) = x from x.2]

instance : (functor he).Linear k where
  map_smul {M N} f c := by
    refine ModuleCat.hom_ext (LinearMap.ext fun (φ : Obj he M) ↦ Obj.ext he fun x ↦ ?_)
    change algebraMap k he.Corner c • f.hom (φ x) = f.hom (φ (rmul he (algebraMap k A c) x))
    rw [rmul_algebraMap, map_smul, map_smul]

/-- `m ↦ (x ↦ (xe) m)` as a `k`-linear map. -/
def psiK (M : ModuleCat.{u} he.Corner) :
    RestrictScalars k he.Corner M →ₗ[k] RestrictScalars k A ((functor he).obj M) where
  toFun m := psi (M := M) (RestrictScalars.addEquiv k he.Corner M m)
  map_add' m n := by rw [map_add, psi_add]; rfl
  map_smul' c m := by
    rw [RingHom.id_apply, RestrictScalars.addEquiv_map_smul, psi_smul]
    show Corner.val he (algebraMap k he.Corner c) • psi (RestrictScalars.addEquiv k he.Corner M m) =
      (algebraMap k A c • psi (RestrictScalars.addEquiv k he.Corner M m) : Obj he M)
    refine Obj.ext he fun x ↦ ?_
    simp only [Obj.smul_apply, psi_apply]
    congr 1
    apply Corner.ext he
    simp only [cornerOf, Corner.val_mk, rmul_val, val_algebraMap]
    rw [← Algebra.commutes, ← Algebra.smul_def]
    simp only [mul_smul_comm, smul_mul_assoc, mul_assoc, he.eq]

theorem psiK_injective (M : ModuleCat.{u} he.Corner) : Function.Injective (psiK (k := k) he M) :=
  fun m n h ↦ by
    have := congrArg (fun φ : Obj he M ↦ φ (eP he)) h
    change psi (RestrictScalars.addEquiv k he.Corner M m) (eP he) =
      psi (RestrictScalars.addEquiv k he.Corner M n) (eP he) at this
    rw [psi_eP, psi_eP] at this
    exact (RestrictScalars.addEquiv k he.Corner M).injective this

/-- `φ ↦ (φ(e bᵢ))ᵢ` as a `k`-linear map. -/
def evalK (M : ModuleCat.{u} he.Corner) {n : ℕ} (b : Fin n → A) :
    RestrictScalars k A ((functor he).obj M) →ₗ[k] (Fin n → RestrictScalars k he.Corner M) where
  toFun φ i := (show Obj he M from φ) (eb he (b i))
  map_add' φ ψ := rfl
  map_smul' c φ := funext fun i ↦ by
    change (show Obj he M from φ) (rmul he (algebraMap k A c) (eb he (b i))) =
      algebraMap k he.Corner c • (show Obj he M from φ) (eb he (b i))
    rw [rmul_algebraMap, map_smul]

theorem evalK_injective (M : ModuleCat.{u} he.Corner) {n : ℕ} {a b : Fin n → A}
    (h : ∑ i, a i * e * b i = 1) : Function.Injective (evalK (k := k) he M b) := by
  intro φ ψ hφψ
  refine Obj.ext he (φ := (show Obj he M from φ)) (ψ := (show Obj he M from ψ)) fun p ↦ ?_
  rw [apply_eq_sum h _ p, apply_eq_sum h _ p]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact congrArg _ (congrFun hφψ i)

theorem le_dim (M : ModuleCat.{u} he.Corner) :
    dim k he.Corner M ≤ dim k A ((functor he).obj M) :=
  LinearMap.rank_le_of_injective _ (psiK_injective he M)

theorem dim_le {n : ℕ} {a b : Fin n → A} (h : ∑ i, a i * e * b i = 1)
    (M : ModuleCat.{u} he.Corner) :
    dim k A ((functor he).obj M) ≤ n * dim k he.Corner M := by
  have hr := LinearMap.rank_le_of_injective _ (evalK_injective (k := k) he M h)
  have : Module.Free k (RestrictScalars k he.Corner M) :=
    @Module.Free.of_divisionRing k _ _ _ (RestrictScalars.module k he.Corner M)
  rwa [rank_fun_eq_lift_mul, Fintype.card_fin, Cardinal.lift_id'] at hr

/-- The functor preserves the dimension of infinite-dimensional modules. -/
theorem dim_eq (hfull : IsFull e) (M : ModuleCat.{u} he.Corner)
    (hM : Cardinal.aleph0 ≤ dim k he.Corner M) :
    dim k A ((functor he).obj M) = dim k he.Corner M := by
  obtain ⟨n, a, b, h⟩ := hfull
  refine le_antisymm ((dim_le he h M).trans ?_) (le_dim he M)
  exact (Cardinal.mul_le_max_of_aleph0_le_right hM).trans
    (max_le (Cardinal.natCast_le_aleph0.trans hM) le_rfl)

/-- The functor preserves finite-dimensional modules. -/
theorem finite_obj (hfull : IsFull e) (M : ModuleCat.{u} he.Corner)
    [Module.Finite k (RestrictScalars k he.Corner M)] :
    Module.Finite k (RestrictScalars k A ((functor he).obj M)) := by
  obtain ⟨n, a, b, h⟩ := hfull
  have := isNoetherian_of_isNoetherianRing_of_finite k (Fin n → RestrictScalars k he.Corner M)
  exact Module.Finite.of_injective _ (evalK_injective (k := k) he M h)

/-- A module whose image is finite-dimensional is finite-dimensional. -/
theorem finite_of_finite_obj (M : ModuleCat.{u} he.Corner)
    [Module.Finite k (RestrictScalars k A ((functor he).obj M))] :
    Module.Finite k (RestrictScalars k he.Corner M) := by
  have : Module.Free k (RestrictScalars k he.Corner M) :=
    @Module.Free.of_divisionRing k _ _ _ (RestrictScalars.module k he.Corner M)
  rw [← Module.rank_lt_aleph0_iff]
  exact (le_dim he M).trans_lt (Module.rank_lt_aleph0 k _)

/-- Morita invariance of representation-finiteness, in the direction used in
Lemma 3.1: if the full corner `eAe` is representation-finite, so is `A`. -/
theorem isRepresentationFinite_of_corner [FiniteDimensional k A] (hfull : IsFull e)
    (hC : IsRepresentationFinite he.Corner) : IsRepresentationFinite A := by
  refine Reduction.isRepresentationFinite_of_two hC hC (functor he) (functor he)
    fun M _ _ ↦ Or.inl ⟨res he M, ?_, ⟨(unitIso hfull M).symm⟩⟩
  have : Module.Finite k (RestrictScalars k A M) := Reduction.finite_restrictScalars k M
  have : Module.Finite k (RestrictScalars k A ((functor he).obj (res he M))) :=
    Reduction.finite_of_iso k (unitIso hfull M)
  have := finite_of_finite_obj (k := k) he (res he M)
  exact Reduction.finite_of_finite_restrictScalars k (res he M)

end Morita

end LargeIndecomposable
