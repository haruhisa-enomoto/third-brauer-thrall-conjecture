module

public import LargeIndecomposable.RayCategories.Basic.Long

/-!
# Zigzags and crowns

A zigzag in a ray category `P` (Gabriel–Roiter 13.9; Bongartz, *Indecomposables
live in all smaller lengths*, Section 2.1) is a sequence of morphisms
`(σ₁, ρ₁, σ₂, ρ₂, …)` with `σᵢ, ρᵢ` of common domain and `ρᵢ, σᵢ₊₁` of common
codomain such that none of `σᵢ = ρᵢ ≫ ξ`, `ρᵢ = σᵢ ≫ ξ`, `ρᵢ = ξ ≫ σᵢ₊₁`,
`σᵢ₊₁ = ξ ≫ ρᵢ` has a solution (diagrammatic order). A crown is a periodic
zigzag. A finite ray category containing a zigzag contains a crown
(`RayCat.exists_crown`): some pair `(σᵢ, ρᵢ)` repeats.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe v u

namespace RayCat

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P]

/-- One step of a zigzag: `σ, ρ` with common domain. -/
structure ZigStep (P : Type u) [Category.{v} P] where
  /-- The common domain. -/
  dom : P
  /-- The codomain of `σ`. -/
  cσ : P
  /-- The codomain of `ρ`. -/
  cρ : P
  σ : dom ⟶ cσ
  ρ : dom ⟶ cρ

/-- `σ` and `ρ` do not factor through each other on the left. -/
def ZigStep.Sep (s : ZigStep P) : Prop :=
  (¬∃ ξ : s.cρ ⟶ s.cσ, s.σ = s.ρ ≫ ξ) ∧ (¬∃ ξ : s.cσ ⟶ s.cρ, s.ρ = s.σ ≫ ξ)

/-- The link between `ρᵢ` and `σᵢ₊₁`: common codomain, no factorization on the
right. -/
def ZigLink (s t : ZigStep P) : Prop :=
  ∃ h : s.cρ = t.cσ, (¬∃ ξ : s.dom ⟶ t.dom, s.ρ ≫ eqToHom h = ξ ≫ t.σ) ∧
    (¬∃ ξ : t.dom ⟶ s.dom, t.σ = ξ ≫ s.ρ ≫ eqToHom h)

/-- A zigzag: an infinite sequence of separated steps with linked neighbours. -/
structure Zigzag (P : Type u) [Category.{v} P] where
  /-- The steps. -/
  step : ℕ → ZigStep P
  sep : ∀ i, (step i).Sep
  link : ∀ i, ZigLink (step i) (step (i + 1))

/-- A crown: a zigzag that is periodic. -/
def Zigzag.IsCrown (Z : Zigzag P) : Prop := ∃ n, 0 < n ∧ ∀ i, Z.step (i + n) = Z.step i

omit [HasZeroMorphisms P] in
/-- A finite ray category with a zigzag has a crown. -/
theorem exists_crown [Finite (ZigStep P)] (Z : Zigzag P) : ∃ Z' : Zigzag P, Z'.IsCrown := by
  obtain ⟨i, j, hij, he⟩ := Finite.exists_ne_map_eq_of_infinite Z.step
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm he.symm (lt_of_le_of_ne (not_lt.1 hlt) hij.symm)
  let n := j - i
  have hn : 0 < n := Nat.sub_pos_of_lt hlt
  let f : ℕ → ℕ := fun m ↦ i + m % n
  have hf : ∀ m, Z.step (f (m + 1)) = Z.step (f m + 1) := by
    intro m
    have hlt' : m % n < n := Nat.mod_lt _ hn
    have hmod : (m + 1) % n = (m % n + 1) % n := (Nat.mod_add_mod m n 1).symm
    by_cases h : m % n + 1 = n
    · have h0 : (m + 1) % n = 0 := by rw [hmod, h, Nat.mod_self]
      change Z.step (i + (m + 1) % n) = Z.step (i + m % n + 1)
      rw [h0, add_zero, add_assoc, h, show i + n = j by omega, he]
    · have h1 : (m + 1) % n = m % n + 1 := by rw [hmod, Nat.mod_eq_of_lt (by omega)]
      change Z.step (i + (m + 1) % n) = Z.step (i + m % n + 1)
      rw [h1, add_assoc]
  refine ⟨⟨fun m ↦ Z.step (f m), fun m ↦ Z.sep _, fun m ↦ ?_⟩, n, hn, fun m ↦ ?_⟩
  · rw [hf m]; exact Z.link _
  · simp [f, Nat.add_mod_right]

/-- A finite ray category containing a zigzag contains a crown. -/
theorem exists_crown_of_finite [IsRayCategory P] [Finite P] (Z : Zigzag P) :
    ∃ Z' : Zigzag P, Z'.IsCrown := by
  have : ∀ x y : P, Finite (x ⟶ y) := IsRayCategory.finite_hom
  have : Finite (ZigStep P) := Finite.of_injective
    (fun s : ZigStep P ↦ (⟨s.dom, s.cσ, s.cρ, s.σ, s.ρ⟩ : Σ (d c c' : P), (d ⟶ c) × (d ⟶ c')))
    (by
      rintro ⟨d, c, c', σ, ρ⟩ ⟨d', e, e', σ', ρ'⟩ h
      simp only [Sigma.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, h⟩ := eq_of_heq h |> Sigma.mk.inj
      obtain ⟨rfl, h⟩ := eq_of_heq h |> Sigma.mk.inj
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq h)
      rfl)
  exact exists_crown Z

end RayCat

end LargeIndecomposable
