module

public import LargeIndecomposable.RepresentationType.MinimalInfinite.Minimal
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Minimal representation-infinite algebras are connected

If `e` is a central idempotent of `B` and both `B / Be` and `B / B(1-e)` are
representation-finite, so is `B`: an indecomposable module is killed by `e`
or by `1 - e` (`isRepresentationFinite_of_centralIdempotent`). Hence a
minimal representation-infinite algebra has no central idempotent other than
`0` and `1` (`IsMinimalRepInfinite.central_idempotent`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Statement

universe u

variable {B : Type u} [Ring B]

/-- The two-sided ideal `B e` of a central element `e`. -/
def centralIdeal (e : B) (hc : ∀ b, e * b = b * e) : TwoSidedIdeal B :=
  TwoSidedIdeal.mk' {x | ∃ b, x = b * e} ⟨0, by simp⟩
    (fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ ⟨a + b, by rw [ha, hb, add_mul]⟩)
    (fun ⟨a, ha⟩ ↦ ⟨-a, by rw [ha, neg_mul]⟩)
    (fun {x _} ⟨a, ha⟩ ↦ ⟨x * a, by rw [ha, mul_assoc]⟩)
    (fun {_ y} ⟨a, ha⟩ ↦ ⟨a * y, by rw [ha, mul_assoc, hc, ← mul_assoc]⟩)

lemma mem_centralIdeal (e : B) (hc : ∀ b, e * b = b * e) (x : B) :
    x ∈ centralIdeal e hc ↔ ∃ b, x = b * e :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ x

/-- A finitely generated indecomposable module killed by a two-sided ideal `I`
is inflated from one of the listed `B / I`-modules. -/
lemma exists_iso_of_isTorsion (I : TwoSidedIdeal B) {n : ℕ}
    (X : Fin n → ModuleCat.{u} (B ⧸ I.asIdeal))
    (hX : ∀ (M : Type u) [AddCommGroup M] [Module (B ⧸ I.asIdeal) M]
      [Module.Finite (B ⧸ I.asIdeal) M], IsIndecomposable (B ⧸ I.asIdeal) M →
        ∃ i, Nonempty (M ≃ₗ[B ⧸ I.asIdeal] X i))
    (M : Type u) [AddCommGroup M] [Module B M] [Module.Finite B M] (hind : IsIndecomposable B M)
    (htor : ∀ x ∈ I, ∀ m : M, x • m = 0) :
    ∃ i, Nonempty (M ≃ₗ[B] (ModuleCat.restrictScalars (Ideal.Quotient.mk I.asIdeal)).obj (X i)) := by
  have hM : Module.IsTorsionBySet B M (I.asIdeal : Set B) := fun m x ↦ htor x.1 x.2 m
  letI : Module (B ⧸ I.asIdeal) M := hM.module
  haveI : IsScalarTower B (B ⧸ I.asIdeal) M := hM.isScalarTower
  haveI : Module.Finite (B ⧸ I.asIdeal) M := Module.Finite.of_restrictScalars_finite B _ M
  have hind' : IsIndecomposable (B ⧸ I.asIdeal) M := by
    refine ⟨hind.1, fun N N' hc ↦ ?_⟩
    rcases hind.2 (N.restrictScalars B) (N'.restrictScalars B)
      ((Submodule.isCompl_restrictScalars_iff B).2 hc) with h | h
    · exact Or.inl ((Submodule.restrictScalars_eq_bot_iff _ _ _).1 h)
    · exact Or.inr ((Submodule.restrictScalars_eq_bot_iff _ _ _).1 h)
  obtain ⟨i, ⟨f⟩⟩ := hX M hind'
  refine ⟨i, ⟨{ f with
    map_smul' := fun b m ↦ ?_ }⟩⟩
  change f (b • m) = Ideal.Quotient.mk I.asIdeal b • f m
  rw [← f.map_smul]
  rfl

/-- **Splitting along a central idempotent.** -/
theorem isRepresentationFinite_of_centralIdempotent (e : B) (he : e * e = e)
    (hc : ∀ b, e * b = b * e) (hc' : ∀ b, (1 - e) * b = b * (1 - e))
    (h₁ : IsRepresentationFinite (B ⧸ (centralIdeal e hc).asIdeal))
    (h₂ : IsRepresentationFinite (B ⧸ (centralIdeal (1 - e) hc').asIdeal)) :
    IsRepresentationFinite B := by
  obtain ⟨n₁, X₁, hX₁⟩ := h₁
  obtain ⟨n₂, X₂, hX₂⟩ := h₂
  refine ⟨n₁ + n₂, Fin.append
    (fun i ↦ (ModuleCat.restrictScalars (Ideal.Quotient.mk _)).obj (X₁ i))
    (fun i ↦ (ModuleCat.restrictScalars (Ideal.Quotient.mk _)).obj (X₂ i)), ?_⟩
  intro M _ _ _ hind
  let φ : M →ₗ[B] M :=
    { toFun := fun m ↦ e • m
      map_add' := fun _ _ ↦ smul_add _ _ _
      map_smul' := fun b m ↦ by
        change e • b • m = b • e • m
        rw [← mul_smul, ← mul_smul, hc] }
  have hφ : IsIdempotentElem φ := by
    ext m
    change e • e • m = e • m
    rw [← mul_smul, he]
  rcases hind.2 _ _ (LinearMap.IsIdempotentElem.isCompl hφ) with h | h
  · -- `e` kills `M`
    have htor : ∀ x ∈ centralIdeal e hc, ∀ m : M, x • m = 0 := by
      intro x hx m
      obtain ⟨b, rfl⟩ := (mem_centralIdeal e hc x).1 hx
      have : e • m ∈ LinearMap.range φ := ⟨m, rfl⟩
      rw [h] at this
      rw [mul_smul, (Submodule.mem_bot B).1 this, smul_zero]
    obtain ⟨i, hi⟩ := exists_iso_of_isTorsion _ X₁ hX₁ M hind htor
    exact ⟨Fin.castAdd n₂ i, by rwa [Fin.append_left]⟩
  · -- `1 - e` kills `M`
    have hid : ∀ m : M, e • m = m := by
      intro m
      have : φ (e • m - m) = 0 := by
        change e • (e • m - m) = 0
        rw [smul_sub, ← mul_smul, he, sub_self]
      have := (LinearMap.ker_eq_bot.1 h) (this.trans φ.map_zero.symm)
      exact sub_eq_zero.1 this
    have htor : ∀ x ∈ centralIdeal (1 - e) hc', ∀ m : M, x • m = 0 := by
      intro x hx m
      obtain ⟨b, rfl⟩ := (mem_centralIdeal (1 - e) hc' x).1 hx
      rw [mul_smul, sub_smul, one_smul, hid, sub_self, smul_zero]
    obtain ⟨i, hi⟩ := exists_iso_of_isTorsion _ X₂ hX₂ M hind htor
    exact ⟨Fin.natAdd n₁ i, by rwa [Fin.append_right]⟩

/-- A minimal representation-infinite algebra has no central idempotent other
than `0` and `1`. -/
theorem IsMinimalRepInfinite.central_idempotent (hB : IsMinimalRepInfinite B) (e : B)
    (he : e * e = e) (hc : ∀ b, e * b = b * e) : e = 0 ∨ e = 1 := by
  by_contra h
  push Not at h
  have hc' : ∀ b, (1 - e) * b = b * (1 - e) := fun b ↦ by rw [sub_mul, mul_sub, hc, one_mul, mul_one]
  refine hB.1 (isRepresentationFinite_of_centralIdempotent e he hc hc' (hB.2 _ ?_) (hB.2 _ ?_))
  · intro h0
    apply h.1
    have : e ∈ centralIdeal e hc := (mem_centralIdeal e hc e).2 ⟨1, (one_mul e).symm⟩
    rw [h0] at this
    exact (TwoSidedIdeal.mem_bot B).1 this
  · intro h0
    apply h.2
    have : 1 - e ∈ centralIdeal (1 - e) hc' := (mem_centralIdeal _ hc' _).2 ⟨1, (one_mul _).symm⟩
    rw [h0] at this
    exact (sub_eq_zero.1 ((TwoSidedIdeal.mem_bot B).1 this)).symm

end LargeIndecomposable
