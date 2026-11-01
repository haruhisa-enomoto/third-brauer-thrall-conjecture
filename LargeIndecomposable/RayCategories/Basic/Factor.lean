module

public import LargeIndecomposable.RayCategories.Basic.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Factorization into irreducible morphisms

In a ray category the nonzero morphisms are ordered by `μ ≤ ν` iff
`ν = α ≫ μ ≫ β`. Below a nonzero morphism there are finitely many nonzero
morphisms (axiom 3 and finite hom sets), and the order is antisymmetric
because non-identity endomorphisms are nilpotent. So every nonzero
non-identity morphism is a composite of irreducible ones
(`IsRayCategory.exists_irreducible_factorization`; Gabriel–Roiter 13.6).
-/

@[expose] public section

set_option autoImplicit false

namespace LargeIndecomposable

open CategoryTheory Limits

universe v u

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P]

/-- A morphism together with its source and target. -/
abbrev RayMor (P : Type u) [Category.{v} P] := Σ (a b : P), a ⟶ b

/-- `μ ≤ ν`: `ν = α ≫ μ ≫ β`. -/
def RayMor.Le (μ ν : RayMor P) : Prop := ∃ (α : ν.1 ⟶ μ.1) (β : μ.2.1 ⟶ ν.2.1), ν.2.2 = α ≫ μ.2.2 ≫ β

/-- A morphism is irreducible if it is nonzero, not an isomorphism, and every
factorization has an isomorphism factor. -/
def IsIrreducible {x y : P} (f : x ⟶ y) : Prop :=
  f ≠ 0 ∧ ¬IsIso f ∧ ∀ (z : P) (g : x ⟶ z) (h : z ⟶ y), f = g ≫ h → IsIso g ∨ IsIso h

namespace IsRayCategory

variable [IsRayCategory P]

/-- In a ray category an endomorphism is an identity or nilpotent. -/
lemma end_id_or_nil (x : P) (e : x ⟶ x) : e = 𝟙 x ∨ ∃ n, rpow e n = 0 := by
  by_cases h : e = 𝟙 x
  · exact Or.inl h
  · exact Or.inr (nil x e h)

/-- A morphism fixed by a non-identity endomorphism on the right is zero. -/
lemma eq_zero_of_comp_end {x y : P} (f : x ⟶ y) (e : y ⟶ y) (he : e ≠ 𝟙 y) (h : f ≫ e = f) :
    f = 0 := by
  obtain ⟨n, hn⟩ := (end_id_or_nil y e).resolve_left he
  have : ∀ m, f ≫ rpow e m = f := by
    intro m
    induction m with
    | zero => exact Category.comp_id f
    | succ m ih => rw [rpow_succ', ← Category.assoc, h, ih]
  rw [← this n, hn, comp_zero]

/-- A morphism fixed by a non-identity endomorphism on the left is zero. -/
lemma eq_zero_of_end_comp {x y : P} (f : x ⟶ y) (e : x ⟶ x) (he : e ≠ 𝟙 x) (h : e ≫ f = f) :
    f = 0 := by
  obtain ⟨n, hn⟩ := (end_id_or_nil x e).resolve_left he
  have : ∀ m, rpow e m ≫ f = f := by
    intro m
    induction m with
    | zero => exact Category.id_comp f
    | succ m ih => rw [rpow_succ, Category.assoc, h, ih]
  rw [← this n, hn, zero_comp]

/-- A nonzero morphism with `f = e₁ ≫ f ≫ e₂` has `e₁ = 𝟙` and `e₂ = 𝟙`. -/
lemma eq_id_of_two_sided {x y : P} (f : x ⟶ y) (hf : f ≠ 0) (e₁ : x ⟶ x) (e₂ : y ⟶ y)
    (h : f = e₁ ≫ f ≫ e₂) : e₁ = 𝟙 x ∧ e₂ = 𝟙 y := by
  have hm : ∀ m, f = rpow e₁ m ≫ f ≫ rpow e₂ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [rpow_succ, rpow_succ', Category.assoc]
      conv_lhs => rw [ih]
      conv_lhs => rw [h]
      simp [Category.assoc]
  constructor
  · by_contra he
    obtain ⟨n, hn⟩ := (end_id_or_nil x e₁).resolve_left he
    exact hf ((hm n).trans (by rw [hn, zero_comp]))
  · by_contra he
    obtain ⟨n, hn⟩ := (end_id_or_nil y e₂).resolve_left he
    exact hf ((hm n).trans (by rw [hn, comp_zero, comp_zero]))

/-- If `f = g ≫ h` with `f ≠ 0` and `h` not an isomorphism, then `f` is not
below `g`. -/
lemma not_le_left {x y z : P} (g : x ⟶ z) (h : z ⟶ y) (hf : g ≫ h ≠ 0) (hh : ¬IsIso h) :
    ¬RayMor.Le ⟨x, y, g ≫ h⟩ ⟨x, z, g⟩ := by
  rintro ⟨α, β, hg⟩
  change g = α ≫ (g ≫ h) ≫ β at hg
  have e1 : g ≫ h = α ≫ (g ≫ h) ≫ β ≫ h := by
    conv_lhs => rw [hg]
    simp [Category.assoc]
  obtain ⟨hα, hβh⟩ := eq_id_of_two_sided _ hf α (β ≫ h) e1
  have hg0 : g ≠ 0 := fun h0 ↦ hf (by rw [h0, zero_comp])
  have e2 : g = 𝟙 x ≫ g ≫ (h ≫ β) := by
    conv_lhs => rw [hg]
    rw [hα]
    simp [Category.assoc]
  obtain ⟨-, hhβ⟩ := eq_id_of_two_sided _ hg0 _ (h ≫ β) e2
  exact hh ⟨β, hhβ, hβh⟩

/-- If `f = g ≫ h` with `f ≠ 0` and `g` not an isomorphism, then `f` is not
below `h`. -/
lemma not_le_right {x y z : P} (g : x ⟶ z) (h : z ⟶ y) (hf : g ≫ h ≠ 0) (hg : ¬IsIso g) :
    ¬RayMor.Le ⟨x, y, g ≫ h⟩ ⟨z, y, h⟩ := by
  rintro ⟨α, β, hh⟩
  change h = α ≫ (g ≫ h) ≫ β at hh
  have e1 : g ≫ h = (g ≫ α) ≫ (g ≫ h) ≫ β := by
    conv_lhs => rw [hh]
    simp [Category.assoc]
  obtain ⟨hgα, hβ⟩ := eq_id_of_two_sided _ hf (g ≫ α) β e1
  have hh0 : h ≠ 0 := fun h0 ↦ hf (by rw [h0, comp_zero])
  have e2 : h = (α ≫ g) ≫ h ≫ 𝟙 y := by
    conv_lhs => rw [hh]
    rw [hβ]
    simp [Category.assoc]
  obtain ⟨hαg, -⟩ := eq_id_of_two_sided _ hh0 (α ≫ g) _ e2
  exact hg ⟨α, hgα, hαg⟩

omit [HasZeroMorphisms P] [IsRayCategory P] in
lemma le_trans {μ ν ρ : RayMor P} (h₁ : RayMor.Le μ ν) (h₂ : RayMor.Le ν ρ) : RayMor.Le μ ρ := by
  obtain ⟨α, β, h⟩ := h₁
  obtain ⟨α', β', h'⟩ := h₂
  exact ⟨α' ≫ α, β ≫ β', by rw [h', h]; simp [Category.assoc]⟩

/-- The nonzero morphisms below a morphism. -/
def below (ν : RayMor P) : Set (RayMor P) := {μ | μ.2.2 ≠ 0 ∧ RayMor.Le μ ν}

lemma below_finite (ν : RayMor P) (hν : ν.2.2 ≠ 0) : (below ν).Finite := by
  obtain ⟨x, y, f⟩ := ν
  let S : Set (RayMor P) := ⋃ a ∈ {a : P | ∃ g : x ⟶ a, g ≠ 0}, ⋃ b ∈ {b : P | ∃ g : b ⟶ y, g ≠ 0},
    Set.range (fun m : a ⟶ b ↦ (⟨a, b, m⟩ : RayMor P))
  have hS : S.Finite := by
    refine Set.Finite.biUnion (finite_out x) fun a _ ↦ Set.Finite.biUnion (finite_in y) fun b _ ↦ ?_
    have := finite_hom a b
    exact Set.finite_range _
  refine hS.subset fun μ hμ ↦ ?_
  obtain ⟨hμ0, α, β, hf⟩ := hμ
  obtain ⟨a, b, m⟩ := μ
  change f = α ≫ m ≫ β at hf
  simp only [S, Set.mem_iUnion, Set.mem_range]
  refine ⟨a, ⟨α, fun h0 ↦ hν (by rw [hf, h0, zero_comp])⟩, b,
    ⟨β, fun h0 ↦ hν (by rw [hf, h0, comp_zero, comp_zero])⟩, m, rfl⟩

omit [HasZeroMorphisms P] [IsRayCategory P] in
lemma le_refl (μ : RayMor P) : RayMor.Le μ μ := ⟨𝟙 _, 𝟙 _, by simp⟩

lemma ncard_below_lt {μ ν : RayMor P} (hν : ν.2.2 ≠ 0) (hle : RayMor.Le μ ν)
    (hnot : ¬RayMor.Le ν μ) : (below μ).ncard < (below ν).ncard := by
  refine Set.ncard_lt_ncard ?_ (below_finite ν hν)
  refine ⟨fun ρ hρ ↦ ⟨hρ.1, le_trans hρ.2 hle⟩, fun hsub ↦ hnot (hsub ⟨hν, le_refl ν⟩).2⟩

end IsRayCategory

/-- Composites of irreducible morphisms. -/
inductive IrrComp : ∀ {x y : P}, (x ⟶ y) → Prop
  | irr {x y : P} {f : x ⟶ y} : IsIrreducible f → IrrComp f
  | comp {x y z : P} {g : x ⟶ z} {h : z ⟶ y} : IrrComp g → IrrComp h → IrrComp (g ≫ h)

namespace IsRayCategory

variable [IsRayCategory P]

/-- Every nonzero morphism that is not an isomorphism is a composite of
irreducible morphisms (Gabriel–Roiter 13.6). -/
theorem irrComp {x y : P} (f : x ⟶ y) (hf : f ≠ 0) (hiso : ¬IsIso f) : IrrComp f := by
  suffices key : ∀ n (μ : RayMor P), (below μ).ncard = n → μ.2.2 ≠ 0 → ¬IsIso μ.2.2 →
      IrrComp μ.2.2 from key _ ⟨x, y, f⟩ rfl hf hiso
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro ⟨a, b, f⟩ rfl hf hiso
    change IrrComp f
    by_cases hirr : IsIrreducible f
    · exact .irr hirr
    · simp only [IsIrreducible, not_and, not_forall, not_or] at hirr
      obtain ⟨z, g, h, rfl, hg, hh⟩ := hirr hf hiso
      have hg0 : g ≠ 0 := fun h0 ↦ hf (by rw [h0, zero_comp])
      have hh0 : h ≠ 0 := fun h0 ↦ hf (by rw [h0, comp_zero])
      refine .comp (ih _ ?_ ⟨a, z, g⟩ rfl hg0 hg) (ih _ ?_ ⟨z, b, h⟩ rfl hh0 hh)
      · exact ncard_below_lt (ν := ⟨a, b, g ≫ h⟩) hf ⟨𝟙 _, h, by simp⟩ (not_le_left g h hf hh)
      · exact ncard_below_lt (ν := ⟨a, b, g ≫ h⟩) hf ⟨g, 𝟙 _, by simp⟩ (not_le_right g h hf hg)

end IsRayCategory

end LargeIndecomposable
