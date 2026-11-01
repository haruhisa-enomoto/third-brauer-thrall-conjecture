module

public import LargeIndecomposable.RayCategories.Distributive.BGRSRayCategory
public import LargeIndecomposable.MildContours.Basic.Global

/-!
# Deep rays and annihilation by the radical

In the BGRS ray category of a preadditive category `C` whose endomorphism
rings have nilpotent Jacobson radicals, a ray is right-deep exactly when its
representatives are killed by every morphism after them whose ray is not
invertible (`rightDeep_kill`, `rightDeep_of_kill`), and dually for left-deep
rays. The point is that a zero ray product may hide a nonzero composite (a
"special zero" `μ ≫ ν = (μ ≫ ρ) ≫ ν` with `ρ` radical); iterating this with
the nilpotency of the radical gives a genuine zero.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable RayCat

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasWellDefinedBGRSRayProduct C]

/-- The ray of a representative. -/
abbrev rayOf {X Y : C} (f : X ⟶ Y) : BGRSRayCategory.mk X ⟶ BGRSRayCategory.mk Y := unitRay f

lemma rayOf_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    rayOf f ≫ rayOf g = rayOf (bgrsRayRepresentativeProduct f g) :=
  BGRSRayCategory.comp_unitRay f g

lemma rayOf_eq_zero_iff {X Y : C} (f : X ⟶ Y) : rayOf f = 0 ↔ f = 0 :=
  unitRay_eq_zero_iff f

/-- A radical endomorphism has a non-invertible ray. -/
lemma not_isIso_rayOf_of_mem_jacobson (hid : ∀ X : C, (𝟙 X : X ⟶ X) ≠ 0) {Y : C} (ρ : End Y)
    (hρ : ρ ∈ Ring.jacobson (End Y)) : ¬IsIso (rayOf ρ.asHom) := by
  intro h
  haveI : IsIso (rayOf ρ.asHom) := h
  haveI : IsIso ρ.asHom := BGRSRayCategory.representative_isIso_of_isIso hid ρ.asHom
  haveI : Nontrivial (End Y) := ⟨⟨1, 0, hid Y⟩⟩
  obtain ⟨u, hu⟩ := (isUnit_iff_isIso ρ).2 inferInstance
  have h1 : (1 : End Y) ∈ Ring.jacobson (End Y) := by
    have := Ideal.mul_mem_left (Ring.jacobson (End Y)) (↑u⁻¹ : End Y) hρ
    rwa [← hu, Units.inv_mul] at this
  exact (Ring.jacobson_lt_top (End Y)).ne ((Ideal.eq_top_iff_one _).2 h1)

omit [HasWellDefinedBGRSRayProduct C] in
lemma list_prod_mem_jacobson {Y : C} (l : List (End Y)) (hne : l ≠ [])
    (hl : ∀ a ∈ l, a ∈ Ring.jacobson (End Y)) : l.prod ∈ Ring.jacobson (End Y) := by
  induction l with
  | nil => exact (hne rfl).elim
  | cons a l _ =>
    rw [List.prod_cons]
    exact Ideal.mul_mem_right _ _ (hl a (by simp))

section Deep

variable (hid : ∀ X : C, (𝟙 X : X ⟶ X) ≠ 0)
  (hnil : ∀ Y : C, ∃ N : ℕ, ∀ l : List (End Y), l.length = N →
    (∀ a ∈ l, a ∈ Ring.jacobson (End Y)) → l.prod = 0)
include hid hnil

/-- **A right-deep ray is killed by the radical of its target** (representative
level). -/
theorem rightDeep_kill_endo {X Y : C} (μ : X ⟶ Y) (hμ : RightDeep (rayOf μ)) (ρ : End Y)
    (hρ : ρ ∈ Ring.jacobson (End Y)) : μ ≫ ρ.asHom = 0 := by
  obtain ⟨N, hN⟩ := hnil Y
  have key : ∀ k : ℕ, ∀ l : List (End Y), l.length + k = N → l ≠ [] →
      (∀ a ∈ l, a ∈ Ring.jacobson (End Y)) → μ ≫ l.prod.asHom = 0 := by
    intro k
    induction k with
    | zero =>
        intro l hl _ hJ
        rw [hN l (by omega) hJ]
        simp
    | succ k ih =>
        intro l hl hne hJ
        have hp := list_prod_mem_jacobson l hne hJ
        have h0 := hμ (rayOf l.prod.asHom) (not_isIso_rayOf_of_mem_jacobson hid _ hp)
        rw [rayOf_comp, rayOf_eq_zero_iff] at h0
        by_cases hs : IsBGRSSpecialZero μ l.prod.asHom
        · obtain ⟨ρ', hρ'⟩ := hs
          rw [hρ', Category.assoc]
          have := ih (l ++ [ρ'.1]) (by simp; omega) (by simp)
            (fun a ha ↦ by
              rcases List.mem_append.1 ha with ha | ha
              · exact hJ a ha
              · rw [List.mem_singleton.1 ha]; exact ρ'.2)
          rw [List.prod_append, List.prod_singleton] at this
          convert this using 2
        · rwa [bgrsRayRepresentativeProduct_eq_comp_of_not_special hs] at h0
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hid Y (by simpa using hN [] rfl (by simp))
  simpa using key (N - 1) [ρ] (by simp; omega) (by simp) (by simpa using hρ)

/-- **A right-deep ray is killed by every non-invertible ray after it** (representative
level). -/
theorem rightDeep_kill {X Y : C} (μ : X ⟶ Y) (hμ : RightDeep (rayOf μ)) {W : C} (ζ : Y ⟶ W)
    (hζ : ¬IsIso (rayOf ζ)) : μ ≫ ζ = 0 := by
  have h0 := hμ (rayOf ζ) hζ
  rw [rayOf_comp, rayOf_eq_zero_iff] at h0
  by_cases hs : IsBGRSSpecialZero μ ζ
  · obtain ⟨ρ', hρ'⟩ := hs
    rw [hρ', rightDeep_kill_endo hid hnil μ hμ ρ'.1 ρ'.2, zero_comp]
  · rwa [bgrsRayRepresentativeProduct_eq_comp_of_not_special hs] at h0

/-- **A left-deep ray is killed by the radical of its source.** -/
theorem leftDeep_kill_endo {X Y : C} (μ : X ⟶ Y) (hμ : LeftDeep (rayOf μ)) (ρ : End X)
    (hρ : ρ ∈ Ring.jacobson (End X)) : ρ.asHom ≫ μ = 0 := by
  obtain ⟨N, hN⟩ := hnil X
  have key : ∀ k : ℕ, ∀ l : List (End X), l.length + k = N → l ≠ [] →
      (∀ a ∈ l, a ∈ Ring.jacobson (End X)) → l.prod.asHom ≫ μ = 0 := by
    intro k
    induction k with
    | zero =>
        intro l hl _ hJ
        rw [hN l (by omega) hJ]
        simp
    | succ k ih =>
        intro l hl hne hJ
        have hp := list_prod_mem_jacobson l hne hJ
        have h0 := hμ (rayOf l.prod.asHom) (not_isIso_rayOf_of_mem_jacobson hid _ hp)
        rw [rayOf_comp, rayOf_eq_zero_iff] at h0
        by_cases hs : IsBGRSSpecialZero l.prod.asHom μ
        · obtain ⟨ρ', hρ'⟩ := hs
          rw [hρ']
          have := ih (ρ'.1 :: l) (by simp; omega) (by simp)
            (fun a ha ↦ by
              rcases List.mem_cons.1 ha with ha | ha
              · rw [ha]; exact ρ'.2
              · exact hJ a ha)
          rw [List.prod_cons] at this
          convert this using 1
        · rwa [bgrsRayRepresentativeProduct_eq_comp_of_not_special hs] at h0
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hid X (by simpa using hN [] rfl (by simp))
  simpa using key (N - 1) [ρ] (by simp; omega) (by simp) (by simpa using hρ)

/-- **A left-deep ray is killed by every non-invertible ray before it.** -/
theorem leftDeep_kill {X Y : C} (μ : X ⟶ Y) (hμ : LeftDeep (rayOf μ)) {W : C} (ζ : W ⟶ X)
    (hζ : ¬IsIso (rayOf ζ)) : ζ ≫ μ = 0 := by
  have h0 := hμ (rayOf ζ) hζ
  rw [rayOf_comp, rayOf_eq_zero_iff] at h0
  by_cases hs : IsBGRSSpecialZero ζ μ
  · obtain ⟨ρ', hρ'⟩ := hs
    rw [hρ', Category.assoc, leftDeep_kill_endo hid hnil μ hμ ρ'.1 ρ'.2, comp_zero]
  · rwa [bgrsRayRepresentativeProduct_eq_comp_of_not_special hs] at h0

omit hid hnil in
/-- Conversely, a representative killed by all non-invertible rays after it has a
right-deep ray. -/
theorem rightDeep_of_kill {X Y : C} (μ : X ⟶ Y)
    (h : ∀ {W : C} (ζ : Y ⟶ W), ¬IsIso (rayOf ζ) → μ ≫ ζ = 0) : RightDeep (rayOf μ) := by
  intro W' ζ' hζ'
  obtain ⟨ζ, rfl⟩ := unitRay_surjective _ _ ζ'
  change rayOf μ ≫ rayOf ζ = 0
  rw [rayOf_comp, rayOf_eq_zero_iff]
  by_cases hs : IsBGRSSpecialZero μ ζ
  · exact bgrsRayRepresentativeProduct_eq_zero_of_special hs
  · rw [bgrsRayRepresentativeProduct_eq_comp_of_not_special hs]; exact h ζ hζ'

omit hid hnil in
/-- Conversely for left-deep rays. -/
theorem leftDeep_of_kill {X Y : C} (μ : X ⟶ Y)
    (h : ∀ {W : C} (ζ : W ⟶ X), ¬IsIso (rayOf ζ) → ζ ≫ μ = 0) : LeftDeep (rayOf μ) := by
  intro W' ζ' hζ'
  obtain ⟨ζ, rfl⟩ := unitRay_surjective _ _ ζ'
  change rayOf ζ ≫ rayOf μ = 0
  rw [rayOf_comp, rayOf_eq_zero_iff]
  by_cases hs : IsBGRSSpecialZero ζ μ
  · exact bgrsRayRepresentativeProduct_eq_zero_of_special hs
  · rw [bgrsRayRepresentativeProduct_eq_comp_of_not_special hs]; exact h ζ hζ'

/-- `leftDeep_kill_endo` needs only that radical endomorphisms of the source compose
to zero with the ray. -/
theorem leftDeep_kill_endo' {X Y : C} (μ : X ⟶ Y)
    (hμ : ∀ ρ : End X, ρ ∈ Ring.jacobson (End X) → rayOf ρ.asHom ≫ rayOf μ = 0) (ρ : End X)
    (hρ : ρ ∈ Ring.jacobson (End X)) : ρ.asHom ≫ μ = 0 := by
  obtain ⟨N, hN⟩ := hnil X
  have key : ∀ k : ℕ, ∀ l : List (End X), l.length + k = N → l ≠ [] →
      (∀ a ∈ l, a ∈ Ring.jacobson (End X)) → l.prod.asHom ≫ μ = 0 := by
    intro k
    induction k with
    | zero =>
        intro l hl _ hJ
        rw [hN l (by omega) hJ]
        simp
    | succ k ih =>
        intro l hl hne hJ
        have hp := list_prod_mem_jacobson l hne hJ
        have h0 := hμ l.prod hp
        rw [rayOf_comp, rayOf_eq_zero_iff] at h0
        by_cases hs : IsBGRSSpecialZero l.prod.asHom μ
        · obtain ⟨ρ', hρ'⟩ := hs
          rw [hρ']
          have := ih (ρ'.1 :: l) (by simp; omega) (by simp)
            (fun a ha ↦ by
              rcases List.mem_cons.1 ha with ha | ha
              · rw [ha]; exact ρ'.2
              · exact hJ a ha)
          rw [List.prod_cons] at this
          convert this using 1
        · rwa [bgrsRayRepresentativeProduct_eq_comp_of_not_special hs] at h0
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hid X (by simpa using hN [] rfl (by simp))
  simpa using key (N - 1) [ρ] (by simp; omega) (by simp) (by simpa using hρ)

/-- `rightDeep_kill_endo` needs only that radical endomorphisms of the target compose
to zero with the ray. -/
theorem rightDeep_kill_endo' {X Y : C} (μ : X ⟶ Y)
    (hμ : ∀ ρ : End Y, ρ ∈ Ring.jacobson (End Y) → rayOf μ ≫ rayOf ρ.asHom = 0) (ρ : End Y)
    (hρ : ρ ∈ Ring.jacobson (End Y)) : μ ≫ ρ.asHom = 0 := by
  obtain ⟨N, hN⟩ := hnil Y
  have key : ∀ k : ℕ, ∀ l : List (End Y), l.length + k = N → l ≠ [] →
      (∀ a ∈ l, a ∈ Ring.jacobson (End Y)) → μ ≫ l.prod.asHom = 0 := by
    intro k
    induction k with
    | zero =>
        intro l hl _ hJ
        rw [hN l (by omega) hJ]
        simp
    | succ k ih =>
        intro l hl hne hJ
        have hp := list_prod_mem_jacobson l hne hJ
        have h0 := hμ l.prod hp
        rw [rayOf_comp, rayOf_eq_zero_iff] at h0
        by_cases hs : IsBGRSSpecialZero μ l.prod.asHom
        · obtain ⟨ρ', hρ'⟩ := hs
          rw [hρ', Category.assoc]
          have := ih (l ++ [ρ'.1]) (by simp; omega) (by simp)
            (fun a ha ↦ by
              rcases List.mem_append.1 ha with ha | ha
              · exact hJ a ha
              · rw [List.mem_singleton.1 ha]; exact ρ'.2)
          rw [List.prod_append, List.prod_singleton] at this
          convert this using 2
        · rwa [bgrsRayRepresentativeProduct_eq_comp_of_not_special hs] at h0
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hid Y (by simpa using hN [] rfl (by simp))
  simpa using key (N - 1) [ρ] (by simp; omega) (by simp) (by simpa using hρ)

end Deep

end LargeIndecomposable
