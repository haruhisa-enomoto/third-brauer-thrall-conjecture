module

public import LargeIndecomposable.Crowns.Basic.MinimalCrown
public import LargeIndecomposable.RayCategories.Basic.Prefix
public import LargeIndecomposable.RayCategories.RoiterVanishing.KeyLemma

/-!
# BO13a, Lemma 4 a): the posets `x/P` have no crowns

For an object `x` of `P`, the nonzero morphisms out of `x` are ordered by
`φ ⪯ ψ` iff `ψ = φ ≫ χ` (`BLe`). A crown of this poset (`RayCat.PosetCrown`)
gives a crown of `P` (`RayCat.PosetCrown.toClosedChain`, using cancellation);
that crown avoids a non-invertible morphism of maximal depth, so it cannot
exist when `P` carries a twisted multiplicative basis of a minimal
representation-infinite algebra (`RayQuiver.MulBasis.isEmpty_posetCrown`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- A crown in the poset `x/P` of nonzero morphisms out of `x`. -/
structure PosetCrown (x : P) (m : ℕ) where
  a : Fin (m + 1) → BMor x
  c : Fin (m + 1) → BMor x
  c_ne : ∀ i, (c i).2 ≠ 0
  le₁ : ∀ i, BLe (a i) (c i)
  le₂ : ∀ i, BLe (a (i + 1)) (c i)
  inc_a₁ : ∀ i, ¬BLe (a i) (a (i + 1))
  inc_a₂ : ∀ i, ¬BLe (a (i + 1)) (a i)
  inc_c₁ : ∀ i, ¬BLe (c i) (c (i + 1))
  inc_c₂ : ∀ i, ¬BLe (c (i + 1)) (c i)

namespace PosetCrown

variable {x : P} {m : ℕ} (C : PosetCrown x m)

/-- The crown of `P` given by the connecting morphisms. -/
def toClosedChain (hR : RightCancel P) : ClosedChain P m where
  x i := (C.a i).1
  z i := (C.c i).1
  ρ i := (C.le₁ i).choose
  σ i := (C.le₂ i).choose
  ρ_ne i h := C.c_ne i (by rw [← (C.le₁ i).choose_spec, h, comp_zero])
  σ_ne i h := C.c_ne i (by rw [← (C.le₂ i).choose_spec, h, comp_zero])
  peak₁ i := by
    rintro ⟨d, hd⟩
    refine C.inc_a₁ i ⟨d, hR _ _ (C.le₂ i).choose ?_ ?_⟩
    · rw [Category.assoc, hd, (C.le₁ i).choose_spec, (C.le₂ i).choose_spec]
    · rw [Category.assoc, hd, (C.le₁ i).choose_spec]; exact C.c_ne i
  peak₂ i := by
    rintro ⟨d, hd⟩
    refine C.inc_a₂ i ⟨d, hR _ _ (C.le₁ i).choose ?_ ?_⟩
    · rw [Category.assoc, hd, (C.le₁ i).choose_spec, (C.le₂ i).choose_spec]
    · rw [Category.assoc, hd, (C.le₂ i).choose_spec]; exact C.c_ne i
  valley₁ i := by
    rintro ⟨d, hd⟩
    refine C.inc_c₁ i ⟨d, ?_⟩
    rw [← (C.le₂ i).choose_spec, Category.assoc, hd, (C.le₁ (i + 1)).choose_spec]
  valley₂ i := by
    rintro ⟨d, hd⟩
    refine C.inc_c₂ i ⟨d, ?_⟩
    rw [← (C.le₁ (i + 1)).choose_spec, Category.assoc, hd, (C.le₂ i).choose_spec]

lemma not_isIso_a (i : Fin (m + 1)) : ¬IsIso (C.a i).2 := by
  intro h
  exact C.inc_a₁ i ⟨inv (C.a i).2 ≫ (C.a (i + 1)).2, by simp⟩

lemma not_isIso_a' (i : Fin (m + 1)) : ¬IsIso (C.a (i + 1)).2 := by
  intro h
  exact C.inc_a₂ i ⟨inv (C.a (i + 1)).2 ≫ (C.a i).2, by simp⟩

end PosetCrown

/-- Depth does not decrease under precomposition. -/
lemma depth_le_comp_left {x y z : P} (f : x ⟶ y) (g : y ⟶ z) (h : f ≫ g ≠ 0) :
    depth g ≤ depth (f ≫ g) := by
  by_cases hf : IsIso f
  · obtain ⟨hxy, rfl⟩ := RayQuiver.eq_id_of_isIso f
    subst hxy
    simp
  · exact (depth_lt_comp_left f g h hf).le

end RayCat

namespace RayQuiver

namespace MulBasis

open RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [LargeIndecomposable.IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **BO13a, Lemma 4 a)**: the posets `x/P` contain no crown. -/
theorem isEmpty_posetCrown
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hR : RightCancel P) (x : P) (m : ℕ) : IsEmpty (PosetCrown x m) := by
  refine ⟨fun C ↦ ?_⟩
  classical
  -- a nonzero non-invertible morphism of maximal depth
  let S : Set (RayMor P) := {μ | μ.2.2 ≠ 0 ∧ ¬IsIso μ.2.2}
  have hS : S.Finite := Set.toFinite _
  have hne : S.Nonempty := by
    obtain ⟨ρ0, hρ0⟩ := C.le₁ 0
    refine ⟨⟨_, _, (C.c 0).2⟩, C.c_ne 0, fun h ↦ C.not_isIso_a 0 ?_⟩
    rw [← hρ0] at h
    exact RayCat.isIso_of_isIso_comp _ _ (fun h0 ↦ C.c_ne 0 (by rw [← hρ0, h0, zero_comp])) h
  obtain ⟨τ, ⟨hτ0, hτ⟩, hmax⟩ := Set.exists_max_image S (fun μ ↦ depth μ.2.2) hS hne
  have key : ∀ {y z : P} (a : x ⟶ y) (e : y ⟶ z) (c : x ⟶ z), a ≫ e = c → c ≠ 0 → ¬IsIso a →
      ¬LargeIndecomposable.FactorsThroughMorphism τ.2.2 e := by
    rintro y z a e c hc hc0 ha ⟨α, β, rfl⟩
    have hc' : ¬IsIso c := fun h ↦ ha (RayCat.isIso_of_isIso_comp _ _ (fun h0 ↦ hc0 (by
      rw [← hc, h0, zero_comp])) (hc ▸ h))
    have h1 : depth τ.2.2 ≤ depth (τ.2.2 ≫ β) :=
      depth_le_comp_right _ _ (fun h0 ↦ hc0 (by rw [← hc, h0, comp_zero, comp_zero]))
    have h2 : depth (τ.2.2 ≫ β) ≤ depth (α ≫ τ.2.2 ≫ β) :=
      depth_le_comp_left _ _ (fun h0 ↦ hc0 (by rw [← hc, h0, comp_zero]))
    have h3 : depth (α ≫ τ.2.2 ≫ β) < depth (a ≫ α ≫ τ.2.2 ≫ β) :=
      depth_lt_comp_left _ _ (by rwa [hc]) ha
    have h4 := hmax ⟨_, _, c⟩ ⟨hc0, hc'⟩
    simp only at h4
    rw [← hc] at h4
    omega
  rcases B.crown_meets hmin τ.2.2 hτ hτ0 (C.toClosedChain hR) with ⟨i, hi⟩ | ⟨i, hi⟩
  · exact key (C.a i).2 _ (C.c i).2 (C.le₁ i).choose_spec (C.c_ne i) (C.not_isIso_a i) hi
  · exact key (C.a (i + 1)).2 _ (C.c i).2 (C.le₂ i).choose_spec (C.c_ne i) (C.not_isIso_a' i) hi

include B in
/-- **No crown of length two in `x/P`**: two incomparable morphisms out of `x`
cannot both lie below two incomparable morphisms (used for BO13a, Lemma 4 b)
and the choice of `ψ` in Lemma 6). -/
theorem not_four_le
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hR : RightCancel P) {x : P} (a₀ a₁ c₀ c₁ : BMor x) (hc₀ : c₀.2 ≠ 0) (hc₁ : c₁.2 ≠ 0)
    (h00 : BLe a₀ c₀) (h10 : BLe a₁ c₀) (h01 : BLe a₀ c₁) (h11 : BLe a₁ c₁)
    (ha₁ : ¬BLe a₀ a₁) (ha₂ : ¬BLe a₁ a₀) (hc₁' : ¬BLe c₀ c₁) (hc₂ : ¬BLe c₁ c₀) : False := by
  let C : PosetCrown x 1 :=
    { a := ![a₀, a₁]
      c := ![c₀, c₁]
      c_ne := fun i ↦ by fin_cases i <;> simpa
      le₁ := fun i ↦ by fin_cases i <;> simpa
      le₂ := fun i ↦ by fin_cases i <;> simpa
      inc_a₁ := fun i ↦ by fin_cases i <;> simpa
      inc_a₂ := fun i ↦ by fin_cases i <;> simpa
      inc_c₁ := fun i ↦ by fin_cases i <;> simpa
      inc_c₂ := fun i ↦ by fin_cases i <;> simpa }
  exact (B.isEmpty_posetCrown hmin hR x 1).false C

end MulBasis

end RayQuiver

end LargeIndecomposable
