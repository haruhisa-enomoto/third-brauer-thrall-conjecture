module

public import LargeIndecomposable.Cleaving.Diagrams.TreeTable

/-!
# The `D̃₆` shape of BO13a figure 6.1

Two sinks `y₀`, `y₁` joined through a source `m` (`y₀ ← m → y₁`), with two
further arrows into each sink: `t₀ → y₀ ← x₀` and `x₁ → y₁ ← t₁`
(`RayQuiver.MulBasis.not_d6s`). Also a builder `RayCat.copyD` for copies of
`D̃ₘ`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

open LargeIndecomposable.Foundations.Quiver in
/-- A copy of `D̃ₘ₊₄` from a vertex map sending its edges to edges. -/
def copyD {V : Type} (G : SimpleGraph V) (m : ℕ) (f : AffineD m → V) (hf : Function.Injective f)
    (hleaf : ∀ i, G.Adj (f (.leaf i)) (f (.spine (AffineD.leafTarget m i))))
    (hspine : ∀ j j' : Fin (m + 1), (j' : ℕ) = j + 1 → G.Adj (f (.spine j)) (f (.spine j'))) :
    (underlyingGraph (AffineD m)).Copy G :=
  copyOf G f hf fun a b e ↦ by
    rcases a with i | j <;> rcases b with i' | j'
    · exact isEmptyElim e
    · have h : j' = AffineD.leafTarget m i := e.down
      subst h
      exact hleaf i
    · exact isEmptyElim e
    · exact hspine j j' e.down

/-- Vertices of the `D̃₆` shape. -/
inductive D6S
  | t₀ | x₀ | y₀ | m | y₁ | x₁ | t₁
  deriving DecidableEq

namespace D6S

instance : Fintype D6S := ⟨{t₀, x₀, y₀, m, y₁, x₁, t₁}, by intro v; cases v <;> simp⟩

/-- The orientation. -/
def ob : D6S → D6S → Bool
  | t₀, y₀ | x₀, y₀ | m, y₀ | m, y₁ | x₁, y₁ | t₁, y₁ => true
  | _, _ => false

/-- The orientation as a relation. -/
abbrev o (u v : D6S) : Prop := ob u v = true

/-- The graph. -/
def G : SimpleGraph D6S := SimpleGraph.fromRel o

lemma adj_iff (u v : D6S) : G.Adj u v ↔ o u v ∨ o v u := by
  rw [G, SimpleGraph.fromRel_adj]
  cases u <;> cases v <;> decide

instance : DecidableRel G.Adj := fun u v ↦ decidable_of_iff _ (adj_iff u v).symm

lemma ho (u v : D6S) (h : o u v) : G.Adj u v := (adj_iff u v).2 (Or.inl h)

lemma hcov (u v : D6S) (h : G.Adj u v) : o u v ∨ o v u := (adj_iff u v).1 h

lemma hasym (u v : D6S) (h : o u v) : ¬o v u := by
  revert h; cases u <;> cases v <;> decide

/-- The parent function towards `y₀`. -/
def par : D6S → Option D6S
  | t₀ | x₀ | m => some y₀
  | y₁ => some m
  | x₁ | t₁ => some y₁
  | y₀ => none

/-- The height. -/
def ht : D6S → ℕ
  | y₀ => 0
  | t₀ | x₀ | m => 1
  | y₁ => 2
  | x₁ | t₁ => 3

lemma isAcyclic : G.IsAcyclic :=
  isAcyclic_of_parent G par ht (fun u v ↦ by rw [adj_iff]; cases u <;> cases v <;> decide)
    (fun u v h ↦ by cases u <;> cases v <;> simp_all [par, ht])

open LargeIndecomposable.Foundations.Quiver in
/-- The vertex map of the copy of `D̃₆`. -/
def cmap : AffineD 2 → D6S
  | .spine j => if (j : ℕ) = 0 then y₀ else if (j : ℕ) = 1 then m else y₁
  | .leaf i => if (i : ℕ) = 0 then t₀ else if (i : ℕ) = 1 then x₀ else if (i : ℕ) = 2 then x₁
    else t₁

open LargeIndecomposable.Foundations.Quiver in
/-- The copy of `D̃₆`. -/
def copy : (underlyingGraph (AffineD 2)).Copy G :=
  copyD G 2 cmap (by
    intro u v h
    rcases u with i | j <;> rcases v with i' | j'
    · fin_cases i <;> fin_cases i' <;> simp_all [cmap]
    · fin_cases i <;> fin_cases j' <;> simp_all [cmap]
    · fin_cases j <;> fin_cases i' <;> simp_all [cmap]
    · fin_cases j <;> fin_cases j' <;> simp_all [cmap])
    (fun i ↦ by
      fin_cases i
      · rw [AffineD.leafTarget_of_lt_two _ (by decide)]; simp [cmap]; decide
      · rw [AffineD.leafTarget_of_lt_two _ (by decide)]; simp [cmap]; decide
      · rw [AffineD.leafTarget_of_not_lt_two _ (by decide)]; simp [cmap]; decide
      · rw [AffineD.leafTarget_of_not_lt_two _ (by decide)]; simp [cmap]; decide)
    (fun j j' h ↦ by fin_cases j <;> fin_cases j' <;> simp_all [cmap] <;> decide)

section Diagram

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] {T₀ X₀ Y₀ M Y₁ X₁ T₁ : P}
  (a₀ : T₀ ⟶ Y₀) (W : X₀ ⟶ Y₀) (U : M ⟶ Y₀) (U' : M ⟶ Y₁) (W' : X₁ ⟶ Y₁) (a₁ : T₁ ⟶ Y₁)

/-- The objects. -/
def obj : D6S → P
  | t₀ => T₀ | x₀ => X₀ | y₀ => Y₀ | m => M | y₁ => Y₁ | x₁ => X₁ | t₁ => T₁

/-- The arrows. -/
def arr : ∀ u v : D6S, o u v → ((obj (T₀ := T₀) (X₀ := X₀) (Y₀ := Y₀) (M := M) (Y₁ := Y₁)
    (X₁ := X₁) (T₁ := T₁) u) ⟶ obj (T₀ := T₀) (X₀ := X₀) (Y₀ := Y₀) (M := M) (Y₁ := Y₁)
    (X₁ := X₁) (T₁ := T₁) v)
  | t₀, y₀, _ => a₀
  | x₀, y₀, _ => W
  | m, y₀, _ => U
  | m, y₁, _ => U'
  | x₁, y₁, _ => W'
  | t₁, y₁, _ => a₁
  | _, _, _ => 0

/-- The path values. -/
def tab : ∀ u v : D6S, Option ((obj (T₀ := T₀) (X₀ := X₀) (Y₀ := Y₀) (M := M) (Y₁ := Y₁)
    (X₁ := X₁) (T₁ := T₁) u) ⟶ obj (T₀ := T₀) (X₀ := X₀) (Y₀ := Y₀) (M := M) (Y₁ := Y₁)
    (X₁ := X₁) (T₁ := T₁) v)
  | t₀, t₀ => some (𝟙 _) | x₀, x₀ => some (𝟙 _) | y₀, y₀ => some (𝟙 _) | m, m => some (𝟙 _)
  | y₁, y₁ => some (𝟙 _) | x₁, x₁ => some (𝟙 _) | t₁, t₁ => some (𝟙 _)
  | t₀, y₀ => some a₀
  | x₀, y₀ => some W
  | m, y₀ => some U
  | m, y₁ => some U'
  | x₁, y₁ => some W'
  | t₁, y₁ => some a₁
  | _, _ => none

end Diagram

end D6S

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

set_option maxHeartbeats 4000000 in
open D6S in
include B in
/-- **No cleaving `D̃₆` diagram** `t₀ → y₀ ← x₀`, `y₀ ← m → y₁`, `x₁ → y₁ ← t₁` in
`P/τ` (BO13a figure 6.1). -/
theorem not_d6s
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) {T₀ X₀ Y₀ M Y₁ X₁ T₁ : P}
    (a₀ : T₀ ⟶ Y₀) (W : X₀ ⟶ Y₀) (U : M ⟶ Y₀) (U' : M ⟶ Y₁) (W' : X₁ ⟶ Y₁) (a₁ : T₁ ⟶ Y₁)
    (h0a₀ : ¬FactorsThroughMorphism τ a₀) (h0W : ¬FactorsThroughMorphism τ W)
    (h0U : ¬FactorsThroughMorphism τ U) (h0U' : ¬FactorsThroughMorphism τ U')
    (h0W' : ¬FactorsThroughMorphism τ W') (h0a₁ : ¬FactorsThroughMorphism τ a₁)
    (hia₀ : ¬IsIso a₀) (hiW : ¬IsIso W) (hiU : ¬IsIso U) (hiU' : ¬IsIso U') (hiW' : ¬IsIso W')
    (hia₁ : ¬IsIso a₁)
    (hUU' : ¬∃ g, U ≫ g = U') (hU'U : ¬∃ g, U' ≫ g = U)
    (h₀1 : ¬∃ g, g ≫ a₀ = W) (h₀2 : ¬∃ g, g ≫ a₀ = U) (h₀3 : ¬∃ g, g ≫ W = a₀)
    (h₀4 : ¬∃ g, g ≫ W = U) (h₀5 : ¬∃ g, g ≫ U = a₀) (h₀6 : ¬∃ g, g ≫ U = W)
    (h₁1 : ¬∃ g, g ≫ a₁ = W') (h₁2 : ¬∃ g, g ≫ a₁ = U') (h₁3 : ¬∃ g, g ≫ W' = a₁)
    (h₁4 : ¬∃ g, g ≫ W' = U') (h₁5 : ¬∃ g, g ≫ U' = a₁) (h₁6 : ¬∃ g, g ≫ U' = W') : False := by
  haveI : Fact (LargeIndecomposable.Foundations.Quiver.IsAcyclic (OT G o)) := ⟨OT.isAcyclic ho hasym isAcyclic⟩
  refine B.not_tree_table hmin hL hR τ hτ hτ0 G o ho hasym isAcyclic
    (OT.not_isRepresentationFinite_affineD ho hcov k 2 copy) obj (arr a₀ W U U' W' a₁)
    (tab a₀ W U U' W' a₁) (fun v ↦ by cases v <;> rfl) ?_ ?_ ?_ ?_ ?_
  · intro x y z h f hf
    cases y <;> cases z <;> (try exact absurd h (by decide)) <;> cases x <;>
      simp only [tab, reduceCtorEq, Option.some.injEq] at hf <;> subst hf <;>
      (rw [Category.id_comp]; rfl)
  · intro x y f hf hne
    cases x <;> cases y <;> (try exact absurd rfl hne) <;>
      simp only [tab, reduceCtorEq, Option.some.injEq] at hf <;>
      first
      | (subst hf; assumption)
      | (obtain rfl := Option.some.inj hf; assumption)
  · intro x y h
    cases x <;> cases y <;> first
      | exact absurd h (by decide)
      | assumption
  · intro x c c' y h h' f hne hf
    cases x <;> cases c <;> (try exact absurd h (by decide)) <;> cases c' <;>
      (try exact absurd h' (by decide)) <;> (try exact absurd rfl hne) <;> cases y <;>
      simp only [tab, reduceCtorEq, Option.some.injEq] at hf <;> subst hf <;>
      (rw [Category.comp_id]; assumption)
  · intro x c c' y h h' f hne hf
    cases y <;> cases c <;> (try exact absurd h (by decide)) <;> cases c' <;>
      (try exact absurd h' (by decide)) <;> (try exact absurd rfl hne) <;> cases x <;>
      simp only [tab, reduceCtorEq, Option.some.injEq] at hf <;> subst hf <;>
      (rw [Category.id_comp]; assumption)

end MulBasis

end RayQuiver

end LargeIndecomposable
