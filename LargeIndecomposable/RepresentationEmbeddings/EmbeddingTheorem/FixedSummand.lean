module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.Defs

/-!
# Maps factoring through sums of copies of a fixed module

Lemma 5.1. Fix a module `P`. On modules without a direct summand isomorphic to
`P`, the maps factoring through a direct sum `P^(I)` of copies of `P` form an
ideal `J`, and every composite of `ℓ + 1` maps of `J` vanishes as soon as every
product of `ℓ` nonunits of `End_A(P)` vanishes.

The manuscript assumes that `P` is finite-dimensional and indecomposable and
that `(rad End_A(P))^ℓ = 0`. Then `End_A(P)` is local (Fitting's lemma), so its
nonunits are exactly its radical, and the hypothesis used here,
`NonunitProductsVanish P ℓ`, is equivalent to the manuscript's; see
`nonunitProductsVanish_of_isLocalRing`. The proof below does not need the
finite generation of `P`: it tracks images of single vectors instead of
matrix columns.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory

universe u

variable {A : Type u} [Ring A] (P : ModuleCat.{u} A)

namespace FixedSummand

/-- `J(X, Y)`: the maps `X → Y` factoring through a direct sum `P^(I)` of
copies of `P`. -/
def FactorsThroughSum {X Y : ModuleCat.{u} A} (f : X ⟶ Y) : Prop :=
  ∃ (I : Type u) (g : X ⟶ ModuleCat.of A (I →₀ P)) (h : ModuleCat.of A (I →₀ P) ⟶ Y), f = g ≫ h

/-- `X` has no direct summand isomorphic to `P`: no `i : P → X`, `p : X → P`
with `p ∘ i = id`. -/
def NoSummand (X : ModuleCat.{u} A) : Prop := ∀ (i : P ⟶ X) (p : X ⟶ P), i ≫ p ≠ 𝟙 P

/-- Every product of `ℓ` nonunits of `End_A(P)` vanishes. For local
`End_A(P)` this says `(rad End_A(P))^ℓ = 0`. -/
def NonunitProductsVanish (ℓ : ℕ) : Prop :=
  ∀ f : Fin ℓ → Module.End A P, (∀ i, ¬ IsUnit (f i)) → (List.ofFn f).prod = 0

variable {P}

/-! ### Lemma 5.1(a): `J` is an ideal -/

lemma factorsThroughSum_zero (X Y : ModuleCat.{u} A) : FactorsThroughSum P (0 : X ⟶ Y) :=
  ⟨PEmpty, 0, 0, by simp⟩

lemma FactorsThroughSum.add {X Y : ModuleCat.{u} A} {f f' : X ⟶ Y}
    (hf : FactorsThroughSum P f) (hf' : FactorsThroughSum P f') : FactorsThroughSum P (f + f') := by
  obtain ⟨I, g, h, rfl⟩ := hf
  obtain ⟨I', g', h', rfl⟩ := hf'
  let e := Finsupp.sumFinsuppLEquivProdFinsupp (M := P) A (α := I) (β := I')
  refine ⟨I ⊕ I', ModuleCat.ofHom (e.symm.toLinearMap ∘ₗ g.hom.prod g'.hom),
    ModuleCat.ofHom (h.hom.coprod h'.hom ∘ₗ e.toLinearMap), ?_⟩
  ext x
  simp

lemma FactorsThroughSum.neg {X Y : ModuleCat.{u} A} {f : X ⟶ Y}
    (hf : FactorsThroughSum P f) : FactorsThroughSum P (-f) := by
  obtain ⟨I, g, h, rfl⟩ := hf
  exact ⟨I, g, -h, by simp⟩

lemma FactorsThroughSum.comp_left {X Y Z : ModuleCat.{u} A} {f : Y ⟶ Z}
    (hf : FactorsThroughSum P f) (g : X ⟶ Y) : FactorsThroughSum P (g ≫ f) := by
  obtain ⟨I, u, v, rfl⟩ := hf
  exact ⟨I, g ≫ u, v, by simp⟩

lemma FactorsThroughSum.comp_right {X Y Z : ModuleCat.{u} A} {f : X ⟶ Y}
    (hf : FactorsThroughSum P f) (g : Y ⟶ Z) : FactorsThroughSum P (f ≫ g) := by
  obtain ⟨I, u, v, rfl⟩ := hf
  exact ⟨I, u, v ≫ g, by simp⟩

/-! ### Lemma 5.1(b): `J^(ℓ+1) = 0` -/

variable (P) in
/-- `IsJComp P n f`: `f` is a composite of `n + 1` maps of `J`, each
intermediate module having no direct summand isomorphic to `P`. -/
inductive IsJComp : ℕ → {X Y : ModuleCat.{u} A} → (X ⟶ Y) → Prop
  | single {X Y : ModuleCat.{u} A} (f : X ⟶ Y) : FactorsThroughSum P f → IsJComp 0 f
  | comp {X Y Z : ModuleCat.{u} A} {n : ℕ} (f : X ⟶ Y) (g : Y ⟶ Z) :
      IsJComp n f → NoSummand P Y → FactorsThroughSum P g → IsJComp (n + 1) (f ≫ g)

variable (P) in
/-- Products of `n` nonunits of `End_A(P)`. -/
def prodNonunits (n : ℕ) : Set (Module.End A P) :=
  {s | ∃ f : Fin n → Module.End A P, (∀ i, ¬ IsUnit (f i)) ∧ (List.ofFn f).prod = s}

lemma one_mem_prodNonunits : (1 : Module.End A P) ∈ prodNonunits P 0 :=
  ⟨Fin.elim0, fun i ↦ i.elim0, by simp⟩

lemma mul_mem_prodNonunits {n : ℕ} {e s : Module.End A P} (he : ¬ IsUnit e)
    (hs : s ∈ prodNonunits P n) : e * s ∈ prodNonunits P (n + 1) := by
  obtain ⟨f, hf, rfl⟩ := hs
  exact ⟨Fin.cons e f, fun i ↦ Fin.cases he hf i, by simp [List.ofFn_succ]⟩

variable (P) in
/-- The vectors `single j (s x)` with `s` a product of `n` nonunits. -/
def gen (J : Type u) (n : ℕ) (x : P) : Set (J →₀ P) :=
  {y | ∃ j, ∃ s ∈ prodNonunits P n, y = Finsupp.single j (s x)}

variable (P) in
/-- A map `φ : P^(I) → P^(J)` all of whose matrix entries are sums of
products of `n` nonunits, tested on single vectors. -/
def Good (n : ℕ) {I J : Type u} (φ : (I →₀ P) →ₗ[A] (J →₀ P)) : Prop :=
  ∀ (i : I) (x : P), φ (Finsupp.single i x) ∈ AddSubmonoid.closure (gen P J n x)

lemma good_id (I : Type u) : Good P 0 (LinearMap.id : (I →₀ P) →ₗ[A] (I →₀ P)) :=
  fun i x ↦ AddSubmonoid.subset_closure ⟨i, 1, one_mem_prodNonunits, by simp⟩

/-- A composite `P → Y → P` through a module without summand `P` is a nonunit. -/
lemma not_isUnit_of_noSummand {Y : ModuleCat.{u} A} (hY : NoSummand P Y) (i : P →ₗ[A] Y)
    (p : Y →ₗ[A] P) : ¬ IsUnit (p ∘ₗ i : Module.End A P) := by
  rintro ⟨e, he⟩
  apply hY (ModuleCat.ofHom i) (ModuleCat.ofHom (↑e⁻¹ ∘ₗ p))
  ext x
  have : ((↑e⁻¹ : Module.End A P) * (p ∘ₗ i)) x = x := by rw [← he]; simp
  simpa using this

lemma Good.comp {n : ℕ} {I J K : Type u} {φ : (I →₀ P) →ₗ[A] (J →₀ P)} (hφ : Good P n φ)
    (μ : (J →₀ P) →ₗ[A] (K →₀ P))
    (hμ : ∀ j k, ¬ IsUnit (Finsupp.lapply k ∘ₗ μ ∘ₗ Finsupp.lsingle j : Module.End A P)) :
    Good P (n + 1) (μ ∘ₗ φ) := by
  intro i x
  have hle : AddSubmonoid.closure (gen P J n x) ≤
      (AddSubmonoid.closure (gen P K (n + 1) x)).comap μ.toAddMonoidHom := by
    rw [AddSubmonoid.closure_le]
    rintro _ ⟨j, s, hs, rfl⟩
    change μ (Finsupp.single j (s x)) ∈ AddSubmonoid.closure (gen P K (n + 1) x)
    rw [← Finsupp.sum_single (μ (Finsupp.single j (s x))), Finsupp.sum]
    refine sum_mem fun k _ ↦ AddSubmonoid.subset_closure ?_
    exact ⟨k, _, mul_mem_prodNonunits (hμ j k) hs, rfl⟩
  exact hle (hφ i x)

lemma Good.eq_zero {ℓ : ℕ} (H : NonunitProductsVanish P ℓ) {I J : Type u}
    {φ : (I →₀ P) →ₗ[A] (J →₀ P)} (hφ : Good P ℓ φ) : φ = 0 := by
  refine Finsupp.lhom_ext fun i x ↦ ?_
  have hle : AddSubmonoid.closure (gen P J ℓ x) ≤ ⊥ := by
    rw [AddSubmonoid.closure_le]
    rintro _ ⟨j, s, ⟨f, hf, rfl⟩, rfl⟩
    simp [H f hf]
  simpa using hle (hφ i x)

/-- The middle factor of a composite in `J^(n+1)` is a map between sums of
copies of `P` all of whose entries are sums of products of `n` nonunits. -/
lemma IsJComp.exists_good {n : ℕ} {X Y : ModuleCat.{u} A} {f : X ⟶ Y} (hf : IsJComp P n f) :
    ∃ (I J : Type u) (u : X ⟶ ModuleCat.of A (I →₀ P)) (φ : (I →₀ P) →ₗ[A] (J →₀ P))
      (v : ModuleCat.of A (J →₀ P) ⟶ Y), Good P n φ ∧ f = u ≫ ModuleCat.ofHom φ ≫ v := by
  induction hf with
  | single f hf =>
    obtain ⟨I, u, v, rfl⟩ := hf
    exact ⟨I, I, u, LinearMap.id, v, good_id I, by simp⟩
  | comp f g _ hY hg ih =>
    obtain ⟨I, J, u, φ, v, hφ, rfl⟩ := ih
    obtain ⟨K, u', v', rfl⟩ := hg
    refine ⟨I, K, u, (u'.hom ∘ₗ v.hom) ∘ₗ φ, v', hφ.comp _ fun j k ↦ ?_, by ext; simp⟩
    exact not_isUnit_of_noSummand hY (v.hom ∘ₗ Finsupp.lsingle j) (Finsupp.lapply k ∘ₗ u'.hom)

/-- Lemma 5.1(b): a composite of `ℓ + 1` maps of `J` through modules without a
direct summand isomorphic to `P` vanishes. -/
theorem IsJComp.eq_zero {ℓ : ℕ} (H : NonunitProductsVanish P ℓ) {X Y : ModuleCat.{u} A}
    {f : X ⟶ Y} (hf : IsJComp P ℓ f) : f = 0 := by
  obtain ⟨I, J, u, φ, v, hφ, rfl⟩ := hf.exists_good
  rw [hφ.eq_zero H]
  ext
  simp

/-- Lemma 5.1(b) for endomorphisms: an endomorphism in `J` of a module without
a direct summand isomorphic to `P` satisfies `f^(ℓ+1) = 0`. -/
theorem pow_eq_zero_of_factorsThroughSum {ℓ : ℕ} (H : NonunitProductsVanish P ℓ)
    {X : ModuleCat.{u} A} (hX : NoSummand P X) {f : X ⟶ X} (hf : FactorsThroughSum P f) :
    f.hom ^ (ℓ + 1) = 0 := by
  have key : ∀ n, IsJComp P n (ModuleCat.ofHom (f.hom ^ (n + 1))) := by
    intro n
    induction n with
    | zero => exact IsJComp.single _ (by simpa using hf)
    | succ n ih =>
      have := IsJComp.comp _ f ih hX hf
      rwa [show ModuleCat.ofHom (f.hom ^ (n + 1)) ≫ f = ModuleCat.ofHom (f.hom ^ (n + 1 + 1)) by
        ext; simp [pow_succ']] at this
  have := congrArg ModuleCat.Hom.hom ((key ℓ).eq_zero H)
  simpa using this

/-! ### The radical form of the hypothesis -/

/-- In a local ring, every nonunit lies in the Jacobson radical. -/
lemma mem_jacobson_of_not_isUnit {R : Type*} [Ring R] [IsLocalRing R] {x : R}
    (hx : ¬ IsUnit x) : x ∈ Ring.jacobson R := by
  -- a left inverse makes `x` a unit
  have hleft : ∀ w : R, w * x ≠ 1 := by
    intro w hw
    have he : (x * w) * (x * w) = x * w := by rw [mul_assoc, ← mul_assoc w, hw, one_mul]
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one (add_sub_cancel (x * w) 1) with h | h
    · obtain ⟨e, he'⟩ := h
      have h1 : x * w = 1 := by
        rw [← he'] at he ⊢
        have := congrArg (fun r : R ↦ ↑e⁻¹ * r) he
        simpa using this
      exact hx ⟨⟨x, w, h1, hw⟩, rfl⟩
    · have h0 : (1 - x * w) * x = 0 := by rw [sub_mul, mul_assoc, hw, mul_one, one_mul, sub_self]
      have hx0 : x = 0 := (h.mul_right_eq_zero).1 h0
      exact zero_ne_one (by rw [← hw, hx0, mul_zero])
  rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff]
  intro y
  have hyx : IsUnit (y * x + 1) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one (a := y * x + 1) (b := -(y * x)) (by abel) with
      h | h
    · exact h
    · obtain ⟨e, he⟩ := h.neg
      have hyx : y * x = e := by rw [he, neg_neg]
      exact absurd (by rw [mul_assoc, hyx, Units.inv_mul]) (hleft (↑e⁻¹ * y))
  obtain ⟨e, he⟩ := hyx
  refine ⟨↑e⁻¹, ?_⟩
  rw [mul_assoc, ← mul_add_one, ← he, Units.inv_mul, sub_self]
  exact Submodule.zero_mem _

/-- The manuscript's hypothesis `(rad End_A(P))^ℓ = 0`, for local `End_A(P)`,
gives `NonunitProductsVanish P ℓ`. -/
lemma nonunitProductsVanish_of_isLocalRing [IsLocalRing (Module.End A P)] {ℓ : ℕ}
    (H : ∀ f : Fin ℓ → Module.End A P, (∀ i, f i ∈ Ring.jacobson (Module.End A P)) →
      (List.ofFn f).prod = 0) :
    NonunitProductsVanish P ℓ :=
  fun f hf ↦ H f fun i ↦ mem_jacobson_of_not_isUnit (hf i)

end FixedSummand

end LargeIndecomposable
