module

public import LargeIndecomposable.Cleaving.Basic.BipDiagram

/-!
# The `D̃₄` star

Four morphisms out of one object, none factoring through another and none
divisible by `τ`, form a cleaving `D̃₄` star in `P/τ`. Hence a minimal
representation-infinite `P` has no such four morphisms
(`RayQuiver.MulBasis.not_four_out`; BO13a, Lemma 6: "at most three arrows start
at `x`").
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable LargeIndecomposable.Foundations.Quiver

universe u

namespace RayCat

/-- The star orientation of `D̃₄`: all arrows out of the centre. -/
abbrev Star := Reo (AffineD 0) (fun _ _ ↦ True)

lemma star_hom_eq {v w : Star} (e : v ⟶ w) : ∃ i, v = ⟨.spine 0⟩ ∧ w = ⟨.leaf i⟩ := by
  rcases e with ⟨⟨-, h⟩ | ⟨⟨e⟩, -⟩⟩
  · exact absurd trivial h
  · rcases v with ⟨i | j⟩ <;> rcases w with ⟨i' | j'⟩
    · exact (IsEmpty.false e).elim
    · exact (IsEmpty.false e).elim
    · exact ⟨i', by rw [Fin.fin_one_eq_zero j], rfl⟩
    · have h1 : (j : ℕ) = j' + 1 := e.down
      omega

variable {P : Type} [Category.{0} P] (x : P) (α : Fin 4 → Σ y : P, x ⟶ y)

/-- The star diagram of four morphisms out of `x`. -/
def starφ : Star ⥤q P where
  obj v := match v.as with
    | .leaf i => (α i).1
    | .spine _ => x
  map {v w} e := match v, w, e with
    | ⟨.spine _⟩, ⟨.leaf i⟩, _ => (α i).2
    | ⟨.leaf _⟩, _, e => False.elim (by obtain ⟨i, h, -⟩ := star_hom_eq e; cases h)
    | ⟨.spine _⟩, ⟨.spine _⟩, e => False.elim (by obtain ⟨i, -, h⟩ := star_hom_eq e; cases h)

lemma starφ_map {j : Fin 1} {i : Fin 4} (e : (⟨.spine j⟩ : Star) ⟶ ⟨.leaf i⟩) :
    (starφ x α).map e = (α i).2 := rfl

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **No four mutually non-factoring morphisms out of one object** avoid a
non-invertible nonzero `τ`. -/
theorem not_four_out
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) (x : P) (α : Fin 4 → Σ y : P, x ⟶ y)
    (h0 : ∀ i, ¬FactorsThroughMorphism τ (α i).2) (hiso : ∀ i, ¬IsIso (α i).2)
    (hl : ∀ i j, i ≠ j → ¬∃ g, (α i).2 ≫ g = (α j).2) : False := by
  refine B.not_bip_diagram hmin hL hR τ hτ hτ0 (Reo.not_isRepresentationFinite_affineD k 0 _)
    ?_ (starφ x α) ?_ ?_ ?_ ?_
  · intro a b c e e'
    obtain ⟨i, -, rfl⟩ := star_hom_eq e
    obtain ⟨j, h, -⟩ := star_hom_eq e'
    cases h
  · intro v w e
    obtain ⟨i, rfl, rfl⟩ := star_hom_eq e
    exact h0 i
  · intro v w e
    obtain ⟨i, rfl, rfl⟩ := star_hom_eq e
    exact hiso i
  · intro v w w' e e' hne
    obtain ⟨i, rfl, rfl⟩ := star_hom_eq e
    obtain ⟨j, -, rfl⟩ := star_hom_eq e'
    exact hl i j (fun h ↦ hne (by rw [h]))
  · intro v v' w e e' hne
    obtain ⟨i, rfl, rfl⟩ := star_hom_eq e
    obtain ⟨j, rfl, -⟩ := star_hom_eq e'
    exact (hne rfl).elim

end MulBasis

end RayQuiver

end LargeIndecomposable
