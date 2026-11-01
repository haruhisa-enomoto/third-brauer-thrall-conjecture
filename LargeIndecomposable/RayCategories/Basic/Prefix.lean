module

public import LargeIndecomposable.RayCategories.RoiterVanishing.KeyLemma

/-!
# The prefix order on morphisms out of a point

For a point `b` of a ray category, `BMor b` collects the morphisms starting at
`b`; `ν ≤ μ` (`RayCat.BLe`) means `μ = ν ≫ ρ` (Fischbacher's order on `_bP`).
An infinite zigzag `x₀ ≤ U₀ ≥ x₁ ≤ U₁ ≥ …` of prefixes with consecutive lower
and consecutive upper terms incomparable gives chains of every length
(`RayCat.not_chainBounded_of_zigzag`); in a chain-bounded ray category such
zigzags do not exist. Fischbacher's tree arguments reduce to this.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe v u

namespace RayCat

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- Morphisms starting at `b`. -/
abbrev BMor (b : P) : Type (max u v) := Σ y : P, b ⟶ y

/-- The prefix order: `ν ≤ μ` if `μ = ν ≫ ρ`. -/
def BLe {b : P} (ν μ : BMor b) : Prop := ∃ ρ : ν.1 ⟶ μ.1, ν.2 ≫ ρ = μ.2

/-- Bounded chains: Fischbacher's chain-finiteness for finite ray categories. -/
def ChainBounded (P : Type u) [Category.{v} P] [HasZeroMorphisms P] : Prop :=
  ∃ N, ∀ l : List (RayMor P), IsChain 0 l → l.length ≤ N

omit [IsRayCategory P] in
lemma BLe.refl {b : P} (ν : BMor b) : BLe ν ν := ⟨𝟙 _, Category.comp_id _⟩

omit [IsRayCategory P] in
lemma BLe.trans {b : P} {ν μ κ : BMor b} (h₁ : BLe ν μ) (h₂ : BLe μ κ) : BLe ν κ := by
  obtain ⟨ρ, hρ⟩ := h₁
  obtain ⟨ρ', hρ'⟩ := h₂
  exact ⟨ρ ≫ ρ', by rw [← Category.assoc, hρ, hρ']⟩

omit [HasZeroMorphisms P] [IsRayCategory P] in
lemma BLe.comp {b : P} (ν : BMor b) {z : P} (ρ : ν.1 ⟶ z) : BLe ν ⟨z, ν.2 ≫ ρ⟩ := ⟨ρ, rfl⟩

/-- A prefix relation through an isomorphism is an equality. -/
lemma eq_of_comp_isIso {b : P} {ν μ : BMor b} (ρ : ν.1 ⟶ μ.1) (hρ : ν.2 ≫ ρ = μ.2) [IsIso ρ] :
    ν = μ := by
  obtain ⟨hx, rfl⟩ := eq_eqToHom_of_isIso ρ
  obtain ⟨y, f⟩ := ν
  obtain ⟨z, g⟩ := μ
  change y = z at hx
  subst hx
  simp only [eqToHom_refl, Category.comp_id] at hρ
  rw [hρ]

lemma BLe.antisymm {b : P} {ν μ : BMor b} (h₁ : BLe ν μ) (h₂ : BLe μ ν) (h0 : μ.2 ≠ 0) :
    ν = μ := by
  obtain ⟨ρ, hρ⟩ := h₁
  obtain ⟨ρ', hρ'⟩ := h₂
  have hν0 : ν.2 ≠ 0 := fun h ↦ h0 (by rw [← hρ, h, zero_comp])
  have e1 : ρ ≫ ρ' = 𝟙 _ := by
    by_contra he
    exact hν0 (IsRayCategory.eq_zero_of_comp_end ν.2 _ he (by rw [← Category.assoc, hρ, hρ']))
  have e2 : ρ' ≫ ρ = 𝟙 _ := by
    by_contra he
    exact h0 (IsRayCategory.eq_zero_of_comp_end μ.2 _ he (by rw [← Category.assoc, hρ', hρ]))
  have : IsIso ρ := ⟨⟨ρ', e1, e2⟩⟩
  obtain ⟨hx, rfl⟩ := eq_eqToHom_of_isIso ρ
  obtain ⟨y, f⟩ := ν
  obtain ⟨z, g⟩ := μ
  change y = z at hx
  subst hx
  simp only [eqToHom_refl, Category.comp_id] at hρ
  rw [hρ]

/-- Distinct irreducible prefixes are incomparable. -/
lemma eq_of_bLe_irreducible {b : P} {α α' : BMor b} (h : BLe α α') (hα : IsIrreducible α.2)
    (hα' : IsIrreducible α'.2) : α = α' := by
  obtain ⟨ρ, hρ⟩ := h
  rcases hα'.2.2 _ _ _ hρ.symm with h1 | h1
  · exact absurd h1 hα.2.1
  · obtain ⟨hx, rfl⟩ := eq_eqToHom_of_isIso ρ
    obtain ⟨y, f⟩ := α
    obtain ⟨z, g⟩ := α'
    change y = z at hx
    subst hx
    simp only [eqToHom_refl, Category.comp_id] at hρ
    rw [hρ]

section Zigzag

variable {b : P} (x U : ℕ → BMor b) (hxU : ∀ i, BLe (x i) (U i))
  (hxU' : ∀ i, BLe (x (i + 1)) (U i))

/-- `ρᵢ` with `Uᵢ = xᵢ ρᵢ`. -/
def zigA (i : ℕ) : RayMor P := ⟨(x i).1, (U i).1, (hxU i).choose⟩

/-- `ρ'ᵢ` with `Uᵢ = xᵢ₊₁ ρ'ᵢ`. -/
def zigB (i : ℕ) : RayMor P := ⟨(x (i + 1)).1, (U i).1, (hxU' i).choose⟩

/-- The entries of the chain of a zigzag: `ρᵢ` at `2i`, `ρ'ᵢ` at `2i + 1`. -/
def zigEntry (j : ℕ) : RayMor P :=
  if j % 2 = 0 then zigA x U hxU (j / 2) else zigB x U hxU' (j / 2)

omit [IsRayCategory P] in
lemma zigEntry_even (i : ℕ) : zigEntry x U hxU hxU' (2 * i) = zigA x U hxU i := by
  unfold zigEntry
  rw [if_pos (by omega)]
  exact congrArg _ (by omega)

omit [IsRayCategory P] in
lemma zigEntry_odd (i : ℕ) : zigEntry x U hxU hxU' (2 * i + 1) = zigB x U hxU' i := by
  unfold zigEntry
  rw [if_neg (by omega)]
  exact congrArg _ (by omega)

/-- A zigzag of prefixes gives chains of every length. -/
lemma isChain_zigzag (hR : RightCancel P) (hU0 : ∀ i, (U i).2 ≠ 0)
    (hx : ∀ i, ¬BLe (x i) (x (i + 1)) ∧ ¬BLe (x (i + 1)) (x i))
    (hU : ∀ i, ¬BLe (U i) (U (i + 1)) ∧ ¬BLe (U (i + 1)) (U i)) (L : ℕ) :
    IsChain 0 ((List.range L).map (zigEntry x U hxU hxU')) := by
  have hρ := fun i ↦ (hxU i).choose_spec
  have hρ' := fun i ↦ (hxU' i).choose_spec
  refine ⟨fun f hf ↦ ?_, fun j hj ↦ ?_⟩
  · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hf
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
    · rw [zigEntry_even]
      intro h0
      dsimp only [zigA] at h0
      exact hU0 i (by rw [← hρ i, h0]; exact comp_zero)
    · rw [zigEntry_odd]
      intro h0
      dsimp only [zigB] at h0
      exact hU0 i (by rw [← hρ' i, h0]; exact comp_zero)
  · simp only [List.getElem_map, List.getElem_range, add_zero]
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
    · rw [zigEntry_even, zigEntry_odd]
      simp only [zigA, zigB, Link, Nat.mul_mod_right, ↓reduceIte]
      refine ⟨rfl, ?_, ?_⟩
      · rintro ⟨c, hc⟩
        simp only [eqToHom_refl, Category.comp_id] at hc
        refine (hx i).1 ⟨c, hR _ _ (hxU' i).choose ?_ ?_⟩
        · rw [Category.assoc, hc, hρ, hρ']
        · rw [Category.assoc, hc, hρ]
          exact hU0 i
      · rintro ⟨c, hc⟩
        simp only [eqToHom_refl, Category.comp_id] at hc
        refine (hx i).2 ⟨c, hR _ _ (hxU i).choose ?_ ?_⟩
        · rw [Category.assoc, hc, hρ, hρ']
        · rw [Category.assoc, hc, hρ']
          exact hU0 i
    · rw [show 2 * i + 1 + 1 = 2 * (i + 1) by ring, zigEntry_even, zigEntry_odd]
      simp only [zigA, zigB, Link, Nat.mul_add_mod_self_left, Nat.mod_succ, one_ne_zero, ↓reduceIte]
      refine ⟨rfl, ?_, ?_⟩
      · rintro ⟨c, hc⟩
        simp only [eqToHom_refl, Category.id_comp] at hc
        refine (hU i).1 ⟨c, ?_⟩
        rw [← hρ' i, Category.assoc, hc, hρ]
      · rintro ⟨c, hc⟩
        simp only [eqToHom_refl, Category.id_comp] at hc
        refine (hU i).2 ⟨c, ?_⟩
        rw [← hρ (i + 1), Category.assoc, hc, hρ']

include hxU hxU' in
/-- In a chain-bounded ray category there is no zigzag of prefixes. -/
theorem not_chainBounded_of_zigzag (hR : RightCancel P) (hU0 : ∀ i, (U i).2 ≠ 0)
    (hx : ∀ i, ¬BLe (x i) (x (i + 1)) ∧ ¬BLe (x (i + 1)) (x i))
    (hU : ∀ i, ¬BLe (U i) (U (i + 1)) ∧ ¬BLe (U (i + 1)) (U i)) : ¬ChainBounded P := by
  rintro ⟨N, hN⟩
  have := hN _ (isChain_zigzag x U hxU hxU' hR hU0 hx hU (N + 1))
  simp at this

end Zigzag

end RayCat

end LargeIndecomposable
