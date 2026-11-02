module

public import LargeIndecomposable.DirectedAlgebras.Directing.DirMod

/-!
# The radical of a vertex projective

For a live point `x`, `rad P(x) = {a ∈ A e_x | e_x a = 0}` (`radP`). Every proper submodule of
`P(x)` lies in it (`le_radP`), so the inclusion `rad P(x) → P(x)` is right almost split
(`isRightAS_radP`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

namespace DirData

variable (D : DirData k A)

/-- The radical of `P(x)`. -/
def radP (x : D.ι) : Submodule A (projE (k := k) (D.idem x)) where
  carrier := {a | D.e x * (a : A) = 0}
  add_mem' {a b} ha hb := by
    change D.e x * ((a : A) + (b : A)) = 0
    rw [mul_add, show D.e x * (a : A) = 0 from ha, show D.e x * (b : A) = 0 from hb, add_zero]
  zero_mem' := mul_zero (D.e x)
  smul_mem' c a ha := by
    change D.e x * (c * (a : A)) = 0
    have ha' : D.e x * (a : A) = 0 := ha
    have hae : (a : A) * D.e x = (a : A) := a.2
    have : c * (a : A) = c * (∑ y, D.e y) * (a : A) := by rw [D.sum, mul_one]
    rw [this, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_eq_zero fun y _ ↦ ?_
    by_cases hy : y = x
    · subst hy
      calc D.e y * (c * D.e y * (a : A)) = D.e y * c * (D.e y * (a : A)) := by
            simp only [mul_assoc]
        _ = 0 := by rw [ha', mul_zero]
    · have h0 := D.corner_cross (Ne.symm hy) c (a : A)
      have key : (D.e x * c * D.e y) * (D.e y * (a : A) * D.e x) =
          D.e x * (c * D.e y * (a : A)) := by
        calc _ = D.e x * (c * (D.e y * D.e y) * ((a : A) * D.e x)) := by simp only [mul_assoc]
          _ = _ := by rw [D.e_mul_e, hae]
      rw [← key, h0]

/-- The radical as an object. -/
abbrev RadP (x : D.ι) : FDMod k A := FDMod.ofSub (D.radP x)

lemma e_mul_mem (x : D.ι) (a : projE (k := k) (D.idem x)) :
    ∃ c : k, D.e x * (a : A) = c • D.e x := by
  obtain ⟨c, hc⟩ := D.local_ x (a : A)
  refine ⟨c, ?_⟩
  rw [← hc]
  have : (a : A) * D.e x = (a : A) := a.2
  rw [mul_assoc, this]

/-- **Proper submodules of `P(x)` lie in the radical.** -/
theorem le_radP (x : D.ι) (N : Submodule A (projE (k := k) (D.idem x)))
    (hN : (⟨D.e x, e_mem (D.idem x)⟩ : projE (k := k) (D.idem x)) ∉ N) : N ≤ D.radP x := by
  intro a ha
  obtain ⟨c, hc⟩ := D.e_mul_mem x a
  by_cases h0 : c = 0
  · change D.e x * (a : A) = 0
    rw [hc, h0, zero_smul]
  · exfalso
    apply hN
    have h1 : (algebraMap k A c⁻¹ * D.e x) • a ∈ N := N.smul_mem _ ha
    convert h1 using 1
    apply Subtype.ext
    change D.e x = (algebraMap k A c⁻¹ * D.e x) * (a : A)
    rw [mul_assoc, hc, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ h0, one_smul]

/-- The inclusion of the radical. -/
def radInc (x : D.ι) : D.RadP x ⟶ projE (k := k) (D.idem x) := (FDMod.ofLin ((D.radP x).subtype))

/-- **The inclusion `rad P(x) → P(x)` is right almost split.** -/
theorem isRightAS_radP (x : D.ι) (hx : x ∈ D.T) : IsRightAS (D.radInc x) := by
  refine ⟨fun ⟨s, hs⟩ ↦ ?_, fun W u hu ↦ ?_⟩
  · have h1 := LinearMap.congr_fun (congrArg FDMod.lin hs) ⟨D.e x, e_mem (D.idem x)⟩
    have h2 : D.e x * ((FDMod.lin s ⟨D.e x, e_mem (D.idem x)⟩ : D.radP x) : A) = 0 :=
      (FDMod.lin s ⟨D.e x, e_mem (D.idem x)⟩).2
    have h3 : ((FDMod.lin s ⟨D.e x, e_mem (D.idem x)⟩ : D.radP x) : A) = D.e x :=
      congrArg Subtype.val h1
    rw [h3, D.e_mul_e] at h2
    exact D.ne x hx h2
  · have hN : (⟨D.e x, e_mem (D.idem x)⟩ : projE (k := k) (D.idem x)) ∉
        LinearMap.range (FDMod.lin u) := by
      rintro ⟨w, hw⟩
      apply hu
      have hw' : D.e x • w ∈ eSub W (D.e x) := by
        change D.e x • (D.e x • w) = D.e x • w
        rw [← mul_smul, D.e_mul_e]
      refine ⟨(FDMod.ofLin ((homProjEquiv (k := k) (D.idem x) W).symm ⟨_, hw'⟩)), (FDMod.hom_ext (LinearMap.ext fun a ↦ ?_))⟩
      apply Subtype.ext
      change ((FDMod.lin u ((a : A) • (D.e x • w)) : projE (k := k) (D.idem x)) : A) = (a : A)
      rw [map_smul, map_smul, hw]
      change (a : A) * (D.e x * D.e x) = (a : A)
      rw [D.e_mul_e]
      exact a.2
    have hle := D.le_radP x _ hN
    refine ⟨FDMod.ofLin (show W →ₗ[A] D.radP x from LinearMap.codRestrict _ (FDMod.lin u)
      fun w ↦ hle (LinearMap.mem_range_self _ w)), rfl⟩

end DirData

end LargeIndecomposable.AR
