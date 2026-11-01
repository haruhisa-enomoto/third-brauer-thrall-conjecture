module

public import LargeIndecomposable.AuslanderReiten.AlmostSplit.ARSeqL

/-!
# Uniqueness of minimal almost split maps

Two left minimal left almost split maps out of the same module are isomorphic under the source
(`leftAS_unique`), and dually for right minimal right almost split maps (`rightAS_unique`).
Left almost split maps between restrictions descend to the quotient algebra (`isLeftAS_unres`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- **Uniqueness of left minimal left almost split maps.** -/
theorem leftAS_unique {U E E' : FDMod k A} {f : U ⟶ E} {f' : U ⟶ E'} (hf : IsLeftAS f)
    (hf' : IsLeftAS f') (hmin : ∀ φ : E ⟶ E, f ≫ φ = f → Function.Bijective (FDMod.lin φ))
    (hmin' : ∀ φ : E' ⟶ E', f' ≫ φ = f' → Function.Bijective (FDMod.lin φ)) :
    ∃ a : E ⟶ E', f ≫ a = f' ∧ Function.Bijective (FDMod.lin a) := by
  obtain ⟨a, ha⟩ := hf.2 E' f' hf'.1
  obtain ⟨b, hb⟩ := hf'.2 E f hf.1
  have h1 := hmin (a ≫ b) (by rw [← Category.assoc, ha, hb])
  have h2 := hmin' (b ≫ a) (by rw [← Category.assoc, hb, ha])
  refine ⟨a, ha, ?_, ?_⟩
  · intro x y hxy
    apply h1.1
    change FDMod.lin b (FDMod.lin a x) = FDMod.lin b (FDMod.lin a y)
    rw [hxy]
  · intro y
    obtain ⟨x, hx⟩ := h2.2 y
    exact ⟨FDMod.lin b x, hx⟩

/-- **Uniqueness of right minimal right almost split maps.** -/
theorem rightAS_unique {Z E E' : FDMod k A} {g : E ⟶ Z} {g' : E' ⟶ Z} (hg : IsRightAS g)
    (hg' : IsRightAS g') (hmin : ∀ φ : E ⟶ E, φ ≫ g = g → Function.Bijective (FDMod.lin φ))
    (hmin' : ∀ φ : E' ⟶ E', φ ≫ g' = g' → Function.Bijective (FDMod.lin φ)) :
    ∃ a : E ⟶ E', a ≫ g' = g ∧ Function.Bijective (FDMod.lin a) := by
  obtain ⟨a, ha⟩ := hg'.2 E g hg.1
  obtain ⟨b, hb⟩ := hg.2 E' g' hg'.1
  have h1 := hmin (a ≫ b) (by rw [Category.assoc, hb, ha])
  have h2 := hmin' (b ≫ a) (by rw [Category.assoc, ha, hb])
  refine ⟨a, ha, ?_, ?_⟩
  · intro x y hxy
    apply h1.1
    change FDMod.lin b (FDMod.lin a x) = FDMod.lin b (FDMod.lin a y)
    rw [hxy]
  · intro y
    obtain ⟨x, hx⟩ := h2.2 y
    exact ⟨FDMod.lin b x, hx⟩

section Restrict

variable {A' : Type u} [Ring A'] [Algebra k A'] {φ : A →ₐ[k] A'} (hφ : Function.Surjective φ)

include hφ in
lemma splitMono_res_iff {W Z : FDMod k A'} (v : Z ⟶ W) :
    (∃ r : resFD φ W ⟶ resFD φ Z, resHom φ v ≫ r = 𝟙 _) ↔ ∃ r : W ⟶ Z, v ≫ r = 𝟙 Z := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨unresHom hφ r, LinearMap.ext fun z ↦ LinearMap.congr_fun hr (ofX z)⟩
  · rintro ⟨r, hr⟩
    exact ⟨resHom φ r, LinearMap.ext fun z ↦ LinearMap.congr_fun hr (toX z)⟩

include hφ in
/-- **A left almost split map of `A`-modules between restrictions is left almost split over
`A'`.** -/
theorem isLeftAS_unres {U E : FDMod k A'} {f : U ⟶ E} (hf : IsLeftAS (resHom φ f)) :
    IsLeftAS f := by
  refine ⟨fun hs ↦ hf.1 ((splitMono_res_iff hφ f).2 hs), fun W v hv ↦ ?_⟩
  obtain ⟨t, ht⟩ := hf.2 (resFD φ W) (resHom φ v) fun hs ↦ hv ((splitMono_res_iff hφ v).1 hs)
  exact ⟨unresHom hφ t, LinearMap.ext fun w ↦ LinearMap.congr_fun ht (ofX w)⟩

end Restrict

end LargeIndecomposable.AR
