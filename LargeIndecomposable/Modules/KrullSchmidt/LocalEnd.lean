module

public import LargeIndecomposable.Statement
public import LargeIndecomposable.RepresentationEmbeddings.EmbeddingTheorem.FixedSummand
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Fitting's lemma and local endomorphism rings

For the predicate `Statement.IsIndecomposable` this file proves:

* a module is indecomposable iff it is nontrivial and its only idempotent
  endomorphisms are `0` and `1` (`isIndecomposable_iff`);
* Fitting's lemma: an endomorphism of an indecomposable module of finite length
  is nilpotent or invertible, so the endomorphism ring is local
  (`IsIndecomposable.isLocalRing_end`);
* for a module that is finite-dimensional over a field `k`, the radical of the
  endomorphism ring is nilpotent, so every product of `ℓ` nonunits vanishes for
  some `ℓ ≥ 1` (`exists_nonunitProductsVanish`). This is the hypothesis
  `(rad End_A(P))^ℓ = 0` of Lemma 5.1, in the form
  `FixedSummand.NonunitProductsVanish`.

The idempotent characterization and Fitting's lemma are adapted from
`Modules/KrullSchmidt/IndecomposableFitting.lean` and
`Modules/KrullSchmidt/LocalEndIndecomposable.lean` in
`multiplicative-bases-deformations` at commit
`7b9f39f221d8a420a1531f487a3b93ae6d26ce85` (themselves adapted from LargeIndecomposable).

## References

* *Multiplicative bases and deformations of representation-finite algebras*, <https://github.com/haruhisa-enomoto/multiplicative-bases-deformations>. Numbered statements cited here refer to it.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open Statement

universe u

variable {A : Type u} [Ring A] {M : Type u} [AddCommGroup M] [Module A M]

/-! ### Idempotents -/

/-- Indecomposability transfers along a linear equivalence. -/
theorem Statement.IsIndecomposable.of_linearEquiv {N : Type u} [AddCommGroup N] [Module A N]
    (h : IsIndecomposable A M) (e : M ≃ₗ[A] N) : IsIndecomposable A N := by
  have := h.1
  refine ⟨e.symm.toEquiv.nontrivial, fun P Q hPQ ↦ ?_⟩
  simpa using h.2 _ _ ((Submodule.orderIsoMapComap e.symm).isCompl hPQ)

/-- The idempotent endomorphisms of an indecomposable module are `0` and `1`. -/
theorem Statement.IsIndecomposable.eq_zero_or_eq_one (h : IsIndecomposable A M)
    {f : Module.End A M} (hf : IsIdempotentElem f) : f = 0 ∨ f = 1 := by
  rcases h.2 _ _ (LinearMap.IsIdempotentElem.isCompl hf) with hrange | hker
  · exact Or.inl (LinearMap.range_eq_bot.mp hrange)
  · refine Or.inr (LinearMap.ext fun x ↦ ?_)
    have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hker
    have hx : f (f x) = f x := DFunLike.congr_fun hf x
    simpa using hinj hx

/-- A module is indecomposable iff it is nontrivial and `0`, `1` are its only
idempotent endomorphisms. -/
theorem isIndecomposable_iff :
    IsIndecomposable A M ↔
      Nontrivial M ∧ ∀ f : Module.End A M, IsIdempotentElem f → f = 0 ∨ f = 1 := by
  refine ⟨fun h ↦ ⟨h.1, fun _ hf ↦ h.eq_zero_or_eq_one hf⟩, fun ⟨hM, h⟩ ↦ ⟨hM, ?_⟩⟩
  intro N P hNP
  rcases h (N.projection P hNP) (Submodule.isIdempotentElem_projection hNP) with h₀ | h₁
  · exact Or.inl (by simpa [h₀] using (Submodule.range_projection hNP).symm)
  · exact Or.inr (by simpa [h₁, Module.End.one_eq_id] using
      (Submodule.ker_projection hNP).symm)

omit [AddCommGroup M] [Module A M] in
/-- In a local ring the only idempotents are `0` and `1`. -/
theorem eq_zero_or_eq_one_of_isLocalRing {R : Type*} [Ring R] [IsLocalRing R] {e : R}
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · right
    obtain ⟨u, rfl⟩ := h
    simpa using congrArg (fun x ↦ (↑u⁻¹ : R) * x) he.eq
  · left
    obtain ⟨u, hu⟩ := h
    have h0 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
    rw [← hu] at h0
    simpa using congrArg (fun x ↦ (↑u⁻¹ : R) * x) h0

/-- A nontrivial module with local endomorphism ring is indecomposable. -/
theorem isIndecomposable_of_isLocalRing [Nontrivial M] [IsLocalRing (Module.End A M)] :
    IsIndecomposable A M :=
  isIndecomposable_iff.2 ⟨inferInstance, fun _ hf ↦ eq_zero_or_eq_one_of_isLocalRing hf⟩

/-- If `g ∘ f = id` with `P` nontrivial and `X` indecomposable, then `f` is
bijective: a nonzero split subobject of an indecomposable module is everything. -/
theorem Statement.IsIndecomposable.bijective_of_comp_eq_id {P : Type u} [AddCommGroup P]
    [Module A P] [Nontrivial P] (hX : IsIndecomposable A M) (f : P →ₗ[A] M) (g : M →ₗ[A] P)
    (hgf : g ∘ₗ f = LinearMap.id) : Function.Bijective f := by
  have hidem : IsIdempotentElem (f ∘ₗ g : Module.End A M) := by
    change (f ∘ₗ g) ∘ₗ (f ∘ₗ g) = f ∘ₗ g
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc g, hgf, LinearMap.id_comp]
  have hinj : Function.Injective f := fun x y hxy ↦ by
    have h : (g ∘ₗ f) x = (g ∘ₗ f) y := congrArg g hxy
    simpa [hgf] using h
  rcases hX.eq_zero_or_eq_one hidem with h0 | h1
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (0 : P)
    apply hx
    have : f x = 0 := by
      have := congrArg (fun φ : M →ₗ[A] M ↦ φ (f x)) h0
      simpa [← LinearMap.comp_apply g f, hgf] using this
    exact hinj (by rw [this, map_zero])
  · refine ⟨hinj, fun y ↦ ⟨g y, ?_⟩⟩
    have := congrArg (fun φ : M →ₗ[A] M ↦ φ y) h1
    simpa using this

/-! ### Fitting's lemma -/

section Fitting

variable [IsNoetherian A M] [IsArtinian A M]

/-- Fitting's lemma: an endomorphism of an indecomposable module of finite
length is nilpotent or bijective. -/
theorem Statement.IsIndecomposable.isNilpotent_or_bijective (h : IsIndecomposable A M)
    (f : Module.End A M) : IsNilpotent f ∨ Function.Bijective f := by
  obtain ⟨n, hn⟩ :=
    Filter.eventually_atTop.mp (LinearMap.eventually_isCompl_ker_pow_range_pow f)
  have hcompl := hn (n + 1) (Nat.le_succ n)
  rcases h.2 _ _ hcompl with hker | hrange
  · refine Or.inr ⟨?_, ?_⟩
    · have hinj : Function.Injective (f ^ (n + 1)) := LinearMap.ker_eq_bot.mp hker
      intro x y hxy
      refine hinj ?_
      simp only [pow_succ f n, Module.End.mul_apply, hxy]
    · have htop : LinearMap.range (f ^ (n + 1)) = ⊤ := by
        have hsup := hcompl.sup_eq_top
        rwa [hker, bot_sup_eq] at hsup
      have hle : LinearMap.range (f ^ (n + 1)) ≤ LinearMap.range f := by
        rw [pow_succ' f n]
        exact LinearMap.range_comp_le_range _ _
      exact LinearMap.range_eq_top.mp (top_le_iff.mp (htop ▸ hle))
  · exact Or.inl ⟨n + 1, LinearMap.range_eq_bot.mp hrange⟩

/-- Fitting's lemma with units of the endomorphism ring. -/
theorem Statement.IsIndecomposable.isNilpotent_or_isUnit (h : IsIndecomposable A M)
    (f : Module.End A M) : IsNilpotent f ∨ IsUnit f :=
  (h.isNilpotent_or_bijective f).imp id (Module.End.isUnit_iff f).mpr

/-- A nonunit endomorphism of an indecomposable module of finite length is
nilpotent. -/
theorem Statement.IsIndecomposable.isNilpotent_of_not_isUnit (h : IsIndecomposable A M)
    {f : Module.End A M} (hf : ¬ IsUnit f) : IsNilpotent f :=
  (h.isNilpotent_or_isUnit f).resolve_right hf

/-- The endomorphism ring of an indecomposable module of finite length is
local. -/
theorem Statement.IsIndecomposable.isLocalRing_end (h : IsIndecomposable A M) :
    IsLocalRing (Module.End A M) := by
  have := h.1
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f ↦ ?_
  exact (h.isNilpotent_or_isUnit f).symm.imp id IsNilpotent.isUnit_one_sub

/-- A module of finite length is indecomposable iff it is nontrivial with local
endomorphism ring. -/
theorem isIndecomposable_iff_isLocalRing_end :
    IsIndecomposable A M ↔ Nontrivial M ∧ IsLocalRing (Module.End A M) :=
  ⟨fun h ↦ ⟨h.1, h.isLocalRing_end⟩, fun ⟨_, _⟩ ↦ isIndecomposable_of_isLocalRing⟩

end Fitting

/-! ### Finite-dimensional modules -/

section FiniteDimensional

variable (k : Type u) [Field k] [Algebra k A] [Module k M] [IsScalarTower k A M]
  [Module.Finite k M]

include k in
/-- A module that is finite-dimensional over `k` is Noetherian over `A`. -/
theorem isNoetherian_of_finite : IsNoetherian A M := isNoetherian_of_tower k inferInstance

include k in
/-- A module that is finite-dimensional over `k` is Artinian over `A`. -/
theorem isArtinian_of_finite : IsArtinian A M := isArtinian_of_tower k inferInstance

/-- The endomorphism algebra of a finite-dimensional module is finite-dimensional. -/
theorem finite_end : Module.Finite k (Module.End A M) :=
  Module.Finite.of_injective (LinearMap.restrictScalarsₗ k A M M k)
    (LinearMap.restrictScalars_injective k)

include k in
/-- The radical of the endomorphism algebra of a finite-dimensional module is
nilpotent: some power `ℓ ≥ 1` of `Ring.jacobson (End_A M)` vanishes. -/
theorem exists_jacobson_end_pow_eq_bot :
    ∃ ℓ ≥ 1, Ring.jacobson (Module.End A M) ^ ℓ = ⊥ := by
  have := finite_end (A := A) (M := M) k
  have : IsArtinianRing (Module.End A M) := IsArtinianRing.of_finite k (Module.End A M)
  obtain ⟨n, hn⟩ := IsSemiprimaryRing.isNilpotent (R := Module.End A M)
  refine ⟨n + 1, Nat.le_add_left 1 n, ?_⟩
  rw [Submodule.pow_succ, hn, Submodule.zero_eq_bot, Submodule.bot_mul]

omit [Module A M] in
/-- A product of `ℓ` elements of a left ideal `I` lies in `I ^ ℓ`. -/
theorem prod_ofFn_mem_pow {R : Type*} [Ring R] (I : Ideal R) :
    ∀ {ℓ : ℕ} (f : Fin ℓ → R), (∀ i, f i ∈ I) → (List.ofFn f).prod ∈ I ^ ℓ
  | 0, _, _ => by simp [Submodule.pow_zero, Ideal.one_eq_top]
  | ℓ + 1, f, hf => by
    rw [List.ofFn_succ', List.prod_concat, Submodule.pow_succ]
    exact Ideal.mul_mem_mul (prod_ofFn_mem_pow I _ fun i ↦ hf _) (hf _)

/-- Lemma 5.1 hypothesis: for a finite-dimensional indecomposable module `P`
some `ℓ ≥ 1` has every product of `ℓ` nonunits of `End_A(P)` zero, that is
`(rad End_A(P))^ℓ = 0`. -/
theorem exists_nonunitProductsVanish (P : ModuleCat.{u} A) [Module k P] [IsScalarTower k A P]
    [Module.Finite k P] (hP : IsIndecomposable A P) :
    ∃ ℓ ≥ 1, FixedSummand.NonunitProductsVanish P ℓ := by
  have := isNoetherian_of_finite (A := A) (M := P) k
  have := isArtinian_of_finite (A := A) (M := P) k
  have := hP.isLocalRing_end
  obtain ⟨ℓ, hℓ, h⟩ := exists_jacobson_end_pow_eq_bot (A := A) (M := P) k
  refine ⟨ℓ, hℓ, FixedSummand.nonunitProductsVanish_of_isLocalRing fun f hf ↦ ?_⟩
  have := prod_ofFn_mem_pow _ f hf
  rwa [h, Submodule.mem_bot] at this

end FiniteDimensional

/-! ### Finite dimension through `RestrictScalars` -/

section RestrictScalars

variable (k : Type u) [Field k] [Algebra k A]

/-- The `k`-module structure of `RestrictScalars k A P`, put on `P` itself. -/
abbrev restrictScalarsModule (P : Type u) [AddCommGroup P] [Module A P] : Module k P :=
  Module.compHom P (algebraMap k A)

/-- With `restrictScalarsModule`, `k`, `A`, `P` form a scalar tower. -/
theorem isScalarTower_restrictScalarsModule (P : Type u) [AddCommGroup P] [Module A P] :
    letI := restrictScalarsModule k (A := A) P
    IsScalarTower k A P := by
  let _ := restrictScalarsModule k (A := A) P
  exact ⟨fun a b x ↦ by rw [Algebra.smul_def, mul_smul]; rfl⟩

/-- A module that is finite-dimensional over `k` (through `RestrictScalars`) has
finite length over `A`. -/
theorem isNoetherian_isArtinian_of_restrictScalars (P : Type u) [AddCommGroup P] [Module A P]
    [Module.Finite k (RestrictScalars k A P)] : IsNoetherian A P ∧ IsArtinian A P := by
  let _ := restrictScalarsModule k (A := A) P
  have := isScalarTower_restrictScalarsModule k (A := A) P
  have : Module.Finite k P := ‹Module.Finite k (RestrictScalars k A P)›
  exact ⟨isNoetherian_of_finite k, isArtinian_of_finite k⟩

/-- `exists_nonunitProductsVanish` with finite dimension stated through
`RestrictScalars`, as in `Statement.dim`. -/
theorem exists_nonunitProductsVanish' (P : ModuleCat.{u} A)
    [Module.Finite k (RestrictScalars k A P)] (hP : IsIndecomposable A P) :
    ∃ ℓ ≥ 1, FixedSummand.NonunitProductsVanish P ℓ := by
  let _ := restrictScalarsModule k (A := A) P
  have := isScalarTower_restrictScalarsModule k (A := A) P
  have : Module.Finite k P := ‹Module.Finite k (RestrictScalars k A P)›
  exact exists_nonunitProductsVanish k P hP

/-- The endomorphism ring of a finite-dimensional indecomposable module is
local, with finite dimension stated through `RestrictScalars`. -/
theorem Statement.IsIndecomposable.isLocalRing_end' (P : Type u) [AddCommGroup P]
    [Module A P] [Module.Finite k (RestrictScalars k A P)] (hP : IsIndecomposable A P) :
    IsLocalRing (Module.End A P) := by
  obtain ⟨_, _⟩ := isNoetherian_isArtinian_of_restrictScalars k (A := A) P
  exact hP.isLocalRing_end

end RestrictScalars

end LargeIndecomposable
