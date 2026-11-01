module

public import LargeIndecomposable.AuslanderReiten.AlmostSplit.RightAS

/-!
# Minimal right almost split maps

If `g : E → Z` is right almost split and `φ : E → E` satisfies `g φ = g`, then `g` restricted to
the range of `φ` is again right almost split (`isRightAS_range`). Choosing `E` of least dimension
gives a right almost split map that is right minimal: every such `φ` is bijective
(`exists_minimal_rightAS`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- `g` restricted to the range of an endomorphism `φ` with `g φ = g`. -/
lemma isRightAS_range {E Z : FDMod k A} {g : E ⟶ Z} (hg : IsRightAS g) (φ : E ⟶ E)
    (hφ : φ ≫ g = g) :
    IsRightAS (show FDMod.ofSub (LinearMap.range (FDMod.lin φ)) ⟶ Z from
      FDMod.lin g ∘ₗ (LinearMap.range (FDMod.lin φ)).subtype) := by
  refine ⟨fun ⟨s, hs⟩ ↦ hg.1 ⟨s ≫ (show FDMod.ofSub (LinearMap.range (FDMod.lin φ)) ⟶ E from
    (LinearMap.range (FDMod.lin φ)).subtype), hs⟩, fun W u hu ↦ ?_⟩
  obtain ⟨v, hv⟩ := hg.2 W u hu
  refine ⟨show W →ₗ[A] LinearMap.range (FDMod.lin φ) from
    (FDMod.lin φ ∘ₗ FDMod.lin v).codRestrict _ fun w ↦ LinearMap.mem_range_self _ _, ?_⟩
  rw [← hv]
  refine LinearMap.ext fun w ↦ ?_
  change FDMod.lin g (FDMod.lin φ (FDMod.lin v w)) = FDMod.lin g (FDMod.lin v w)
  exact LinearMap.congr_fun hφ (FDMod.lin v w)

/-- **Minimal right almost split maps exist.** -/
theorem exists_minimal_rightAS [FiniteDimensional k A] (Z : FDMod k A)
    [IsLocalRing (Module.End A Z)] :
    ∃ (E : FDMod k A) (g : E ⟶ Z), IsRightAS g ∧
      ∀ φ : E ⟶ E, φ ≫ g = g → Function.Bijective (FDMod.lin φ) := by
  classical
  have hex : ∃ n, ∃ (E : FDMod k A) (g : E ⟶ Z), IsRightAS g ∧ finrank k E = n := by
    obtain ⟨E, g, hg⟩ := FDMod.exists_rightAS Z
    exact ⟨_, E, g, hg, rfl⟩
  obtain ⟨E, g, hg, hn⟩ := Nat.find_spec hex
  refine ⟨E, g, hg, fun φ hφ ↦ ?_⟩
  have hR := isRightAS_range hg φ hφ
  have hle := Nat.find_min' hex ⟨_, _, hR, rfl⟩
  rw [← hn] at hle
  have hsurj : Function.Surjective (FDMod.lin φ) := by
    have hrank : finrank k ((LinearMap.range (FDMod.lin φ)).restrictScalars k) = finrank k E :=
      le_antisymm (Submodule.finrank_le _) hle
    have htop : (LinearMap.range (FDMod.lin φ)).restrictScalars k = ⊤ :=
      Submodule.eq_top_of_finrank_eq hrank
    intro y
    have : y ∈ (LinearMap.range (FDMod.lin φ)).restrictScalars k := by rw [htop]; trivial
    exact this
  have hinj : Function.Injective ((FDMod.lin φ).restrictScalars k) :=
    LinearMap.injective_iff_surjective.2 hsurj
  exact ⟨hinj, hsurj⟩

end LargeIndecomposable.AR
