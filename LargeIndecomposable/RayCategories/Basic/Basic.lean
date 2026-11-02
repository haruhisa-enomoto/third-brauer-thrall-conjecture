module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Data.Set.Finite.Basic

/-!
# Ray categories

Ray categories after Gabriel–Roiter, Section 13.4 (recalled in Bongartz, *Indecomposables
live in all smaller lengths*, Section 2.1). A ray category is a category `P`
with zero morphisms such that

1. objects are pairwise non-isomorphic (`P` is skeletal);
2. composition with a zero morphism is zero;
3. for each `x`, `P(x, y) = {0} = P(y, x)` for almost all `y`;
4. each `P(x, x)` is `{1, σ, …, σ^{n-1}}` with `σ^n = 0 ≠ σ^{n-1}`;
5. each `P(x, y)` is cyclic under `P(x, x)` or under `P(y, y)`;
6. `λ ≫ μ ≫ κ = λ ≫ ν ≫ κ ≠ 0` implies `μ = ν`.

The class `IsRayCategory` records the consequences of these axioms used in
this development (skeletal, locally finite, finite hom sets, nonzero
identities, nilpotent non-identity endomorphisms); the BGRS ray category of a
distributive algebra satisfies them (`RayCategories/Distributive/FromDistributive.lean`).
-/

@[expose] public section

set_option autoImplicit false

namespace LargeIndecomposable

open CategoryTheory Limits

universe v u

/-- The `n`-th power `e ≫ ⋯ ≫ e` of an endomorphism. -/
def rpow {C : Type u} [Category.{v} C] {x : C} (e : x ⟶ x) : ℕ → (x ⟶ x)
  | 0 => 𝟙 x
  | n + 1 => rpow e n ≫ e

section rpow

variable {C : Type u} [Category.{v} C] {x : C} (e : x ⟶ x)

@[simp] lemma rpow_zero : rpow e 0 = 𝟙 x := rfl

lemma rpow_succ (n : ℕ) : rpow e (n + 1) = rpow e n ≫ e := rfl

lemma rpow_add (m n : ℕ) : rpow e (m + n) = rpow e m ≫ rpow e n := by
  induction n with
  | zero => simp
  | succ n ih => rw [← Nat.add_assoc, rpow_succ, rpow_succ, ih, Category.assoc]

lemma rpow_succ' (n : ℕ) : rpow e (n + 1) = e ≫ rpow e n := by
  rw [Nat.add_comm, rpow_add]; simp [rpow_succ]

lemma rpow_mul (i n : ℕ) : rpow (rpow e i) n = rpow e (i * n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [rpow_succ, ih, Nat.mul_succ, rpow_add]

end rpow

/-- The axioms of a finite-type ray category used here: skeletal, locally
finite (axiom 3), finite hom sets with nonzero identities, and nilpotent
non-identity endomorphisms (consequences of axioms 4 and 5). Gabriel–Roiter's
cyclicity and cancellation axioms are not needed for the results below. -/
class IsRayCategory (P : Type u) [Category.{v} P] [HasZeroMorphisms P] : Prop where
  skeletal : Skeletal P
  /-- Axiom 3: an object is linked by nonzero morphisms to finitely many objects. -/
  finite_out : ∀ x : P, {y : P | ∃ f : x ⟶ y, f ≠ 0}.Finite
  finite_in : ∀ x : P, {y : P | ∃ f : y ⟶ x, f ≠ 0}.Finite
  finite_hom : ∀ x y : P, Finite (x ⟶ y)
  id_ne_zero : ∀ x : P, 𝟙 x ≠ 0
  /-- Non-identity endomorphisms are nilpotent. -/
  nil : ∀ (x : P) (e : x ⟶ x), e ≠ 𝟙 x → ∃ n, rpow e n = 0

end LargeIndecomposable
