module

public import LargeIndecomposable.Cleaving.Shapes.ShapeD6

/-!
# The `D̃₇` shape of BO13a figure 6.2

`x' → b`, `b → zn`, `b → y₀ ← m → y₁`, `b' → y₁ ← te`
(`RayQuiver.MulBasis.not_f62`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

/-- Vertices of the shape of figure 6.2. -/
inductive F62
  | x' | b | zn | y₀ | m | y₁ | b' | te
  deriving DecidableEq

namespace F62

instance : Fintype F62 := ⟨{x', b, zn, y₀, m, y₁, b', te}, by intro v; cases v <;> simp⟩

/-- The orientation. -/
def ob : F62 → F62 → Bool
  | x', b | b, zn | b, y₀ | m, y₀ | m, y₁ | b', y₁ | te, y₁ => true
  | _, _ => false

/-- The orientation as a relation. -/
abbrev o (u v : F62) : Prop := ob u v = true

/-- The graph. -/
def G : SimpleGraph F62 := SimpleGraph.fromRel o

lemma adj_iff (u v : F62) : G.Adj u v ↔ o u v ∨ o v u := by
  rw [G, SimpleGraph.fromRel_adj]
  cases u <;> cases v <;> decide

instance : DecidableRel G.Adj := fun u v ↦ decidable_of_iff _ (adj_iff u v).symm

lemma ho (u v : F62) (h : o u v) : G.Adj u v := (adj_iff u v).2 (Or.inl h)

lemma hcov (u v : F62) (h : G.Adj u v) : o u v ∨ o v u := (adj_iff u v).1 h

lemma hasym (u v : F62) (h : o u v) : ¬o v u := by
  revert h; cases u <;> cases v <;> decide

/-- The parent function towards `y₀`. -/
def par : F62 → Option F62
  | b | m => some y₀
  | x' | zn => some b
  | y₁ => some m
  | b' | te => some y₁
  | y₀ => none

/-- The height. -/
def ht : F62 → ℕ
  | y₀ => 0
  | b | m => 1
  | x' | zn | y₁ => 2
  | b' | te => 3

lemma isAcyclic : G.IsAcyclic :=
  isAcyclic_of_parent G par ht (fun u v ↦ by rw [adj_iff]; cases u <;> cases v <;> decide)
    (fun u v h ↦ by cases u <;> cases v <;> simp_all [par, ht])

open LargeIndecomposable.Foundations.Quiver in
/-- The vertex map of the copy of `D̃₇`. -/
def cmap : AffineD 3 → F62
  | .spine j => if (j : ℕ) = 0 then b else if (j : ℕ) = 1 then y₀ else if (j : ℕ) = 2 then m
    else y₁
  | .leaf i => if (i : ℕ) = 0 then x' else if (i : ℕ) = 1 then zn else if (i : ℕ) = 2 then b'
    else te

open LargeIndecomposable.Foundations.Quiver in
/-- The copy of `D̃₇`. -/
def copy : (underlyingGraph (AffineD 3)).Copy G :=
  copyD G 3 cmap (by
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

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] {X' Bb Zn Y₀ M Y₁ B' Te : P}
  (r : X' ⟶ Bb) (s : Bb ⟶ Zn) (W : Bb ⟶ Y₀) (U : M ⟶ Y₀) (U' : M ⟶ Y₁) (W' : B' ⟶ Y₁)
  (e : Te ⟶ Y₁)

/-- The objects. -/
def obj : F62 → P
  | x' => X' | b => Bb | zn => Zn | y₀ => Y₀ | m => M | y₁ => Y₁ | b' => B' | te => Te

/-- The arrows. -/
def arr : ∀ u v : F62, o u v → ((obj (X' := X') (Bb := Bb) (Zn := Zn) (Y₀ := Y₀) (M := M)
    (Y₁ := Y₁) (B' := B') (Te := Te) u) ⟶ obj (X' := X') (Bb := Bb) (Zn := Zn) (Y₀ := Y₀)
    (M := M) (Y₁ := Y₁) (B' := B') (Te := Te) v)
  | x', b, _ => r
  | b, zn, _ => s
  | b, y₀, _ => W
  | m, y₀, _ => U
  | m, y₁, _ => U'
  | b', y₁, _ => W'
  | te, y₁, _ => e
  | _, _, _ => 0

/-- The path values. -/
def tab : ∀ u v : F62, Option ((obj (X' := X') (Bb := Bb) (Zn := Zn) (Y₀ := Y₀) (M := M)
    (Y₁ := Y₁) (B' := B') (Te := Te) u) ⟶ obj (X' := X') (Bb := Bb) (Zn := Zn) (Y₀ := Y₀)
    (M := M) (Y₁ := Y₁) (B' := B') (Te := Te) v)
  | x', x' => some (𝟙 _) | b, b => some (𝟙 _) | zn, zn => some (𝟙 _) | y₀, y₀ => some (𝟙 _)
  | m, m => some (𝟙 _) | y₁, y₁ => some (𝟙 _) | b', b' => some (𝟙 _) | te, te => some (𝟙 _)
  | x', b => some r
  | b, zn => some s
  | b, y₀ => some W
  | m, y₀ => some U
  | m, y₁ => some U'
  | b', y₁ => some W'
  | te, y₁ => some e
  | x', zn => some (r ≫ s)
  | x', y₀ => some (r ≫ W)
  | _, _ => none

end Diagram

end F62

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

set_option maxHeartbeats 4000000 in
open F62 in
include B in
/-- **No cleaving diagram of the shape of figure 6.2** in `P/τ`. -/
theorem not_f62
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) {X' Bb Zn Y₀ M Y₁ B' Te : P}
    (r : X' ⟶ Bb) (s : Bb ⟶ Zn) (W : Bb ⟶ Y₀) (U : M ⟶ Y₀) (U' : M ⟶ Y₁) (W' : B' ⟶ Y₁)
    (e : Te ⟶ Y₁)
    (h0r : ¬FactorsThroughMorphism τ r) (h0s : ¬FactorsThroughMorphism τ s)
    (h0W : ¬FactorsThroughMorphism τ W) (h0U : ¬FactorsThroughMorphism τ U)
    (h0U' : ¬FactorsThroughMorphism τ U') (h0W' : ¬FactorsThroughMorphism τ W')
    (h0e : ¬FactorsThroughMorphism τ e) (h0rs : ¬FactorsThroughMorphism τ (r ≫ s))
    (h0rW : ¬FactorsThroughMorphism τ (r ≫ W))
    (hir : ¬IsIso r) (his : ¬IsIso s) (hiW : ¬IsIso W) (hiU : ¬IsIso U) (hiU' : ¬IsIso U')
    (hiW' : ¬IsIso W') (hie : ¬IsIso e)
    (hsW : ¬∃ g, s ≫ g = W) (hWs : ¬∃ g, W ≫ g = s)
    (hUU' : ¬∃ g, U ≫ g = U') (hU'U : ¬∃ g, U' ≫ g = U)
    (hUW : ¬∃ g, g ≫ U = W) (hUrW : ¬∃ g, g ≫ U = r ≫ W) (hWU : ¬∃ g, g ≫ W = U)
    (h₁1 : ¬∃ g, g ≫ e = W') (h₁2 : ¬∃ g, g ≫ e = U') (h₁3 : ¬∃ g, g ≫ W' = e)
    (h₁4 : ¬∃ g, g ≫ W' = U') (h₁5 : ¬∃ g, g ≫ U' = e) (h₁6 : ¬∃ g, g ≫ U' = W') : False := by
  haveI : Fact (LargeIndecomposable.Foundations.Quiver.IsAcyclic (OT G o)) := ⟨OT.isAcyclic ho hasym isAcyclic⟩
  refine B.not_tree_table hmin hL hR τ hτ hτ0 G o ho hasym isAcyclic
    (OT.not_isRepresentationFinite_affineD ho hcov k 3 copy) obj (arr r s W U U' W' e)
    (tab r s W U U' W' e) (fun v ↦ by cases v <;> rfl) ?_ ?_ ?_ ?_ ?_
  · intro x y z h f hf
    cases y <;> cases z <;> (try exact absurd h (by decide)) <;> cases x <;>
      simp only [tab, reduceCtorEq, Option.some.injEq] at hf <;>
      (first | subst hf | obtain rfl := Option.some.inj hf) <;>
      first
      | (rw [Category.id_comp]; rfl)
      | rfl
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
      simp only [tab, reduceCtorEq, Option.some.injEq] at hf <;>
      (first | subst hf | obtain rfl := Option.some.inj hf) <;>
      (rw [Category.comp_id]; assumption)
  · intro x c c' y h h' f hne hf
    cases y <;> cases c <;> (try exact absurd h (by decide)) <;> cases c' <;>
      (try exact absurd h' (by decide)) <;> (try exact absurd rfl hne) <;> cases x <;>
      simp only [tab, reduceCtorEq, Option.some.injEq] at hf <;>
      (first | subst hf | obtain rfl := Option.some.inj hf) <;>
      first
      | (rw [Category.id_comp]; assumption)
      | assumption

end MulBasis

end RayQuiver

end LargeIndecomposable
