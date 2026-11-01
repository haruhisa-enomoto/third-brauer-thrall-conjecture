module

public import LargeIndecomposable.DirectedAlgebras.EulerForm.EulerHom
public import LargeIndecomposable.AuslanderReiten.AlmostSplit.ARSeq

/-!
# The Euler form computes `Hom - Ext¹` in projective dimension one

The dimension vector of `A` is the vector of row sums of the Cartan matrix (`dimv_self`), and a
free module `Aⁿ` has `n` times that dimension vector. For a module `Z` with a free presentation
`0 → Aⁿ¹ → Aⁿ⁰ → Z → 0`, `dim Z = (n₀ - n₁) dim A`, so
`⟨dim Z, dim W⟩ = dim Hom(Z, W) - dim Ext¹(Z, W)` (`euler_eq_hom_sub_ext1`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open Module Matrix

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (D : DirData k A)

/-- `e_j A` splits along the right idempotents. -/
def rowEquiv (j : D.ι) : eSub (FDMod.self : FDMod k A) (D.e j) ≃ₗ[k]
    ∀ i, eSub (projE (k := k) (D.idem i)) (D.e j) where
  toFun a i := ⟨⟨(a : A) * D.e i, by
      change (a : A) * D.e i * D.e i = (a : A) * D.e i
      rw [mul_assoc, (D.idem i).eq]⟩, by
      apply Subtype.ext
      change D.e j * ((a : A) * D.e i) = (a : A) * D.e i
      rw [← mul_assoc]
      exact congrArg (· * D.e i) a.2⟩
  map_add' a b := by funext i; exact Subtype.ext (Subtype.ext (add_mul _ _ _))
  map_smul' c a := by funext i; exact Subtype.ext (Subtype.ext (smul_mul_assoc _ _ _))
  invFun v := ⟨∑ i, ((v i : projE (k := k) (D.idem i)) : A), by
    change D.e j • ∑ i, ((v i : projE (k := k) (D.idem i)) : A) = _
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ congrArg Subtype.val (v i).2⟩
  left_inv a := by
    apply Subtype.ext
    change ∑ i, (a : A) * D.e i = a
    rw [← Finset.mul_sum, D.sum, mul_one]
  right_inv v := by
    funext i
    apply Subtype.ext; apply Subtype.ext
    change (∑ l, ((v l : projE (k := k) (D.idem l)) : A)) * D.e i = (v i : A)
    rw [Finset.sum_mul, Finset.sum_eq_single i]
    · exact ((v i : projE (k := k) (D.idem i))).2
    · intro l _ hli
      have h1 : ((v l : projE (k := k) (D.idem l)) : A) * D.e l = (v l : A) :=
        ((v l : projE (k := k) (D.idem l))).2
      rw [← h1, mul_assoc, D.orth l i hli, mul_zero]
    · simp

/-- **The dimension vector of `A`**: row sums of the Cartan matrix. -/
theorem dimv_self (j : D.ι) :
    (dimv D.e (FDMod.self : FDMod k A) j : ℤ) = ∑ i, cartan D j i := by
  unfold dimv cartan
  rw [(rowEquiv D j).finrank_eq, Module.finrank_pi_fintype]
  push_cast
  rfl

/-- `e_j Aⁿ` is `(e_j A)ⁿ`. -/
def freeEquiv (n : ℕ) (j : D.ι) : eSub (FDMod.free n : FDMod k A) (D.e j) ≃ₗ[k]
    (Fin n → eSub (FDMod.self : FDMod k A) (D.e j)) where
  toFun f l := ⟨(f : Fin n → A) l, by
    have h : D.e j • (f : Fin n → A) = f := f.2
    exact congrFun h l⟩
  map_add' f g := rfl
  map_smul' c f := rfl
  invFun v := ⟨fun l ↦ (v l : A), funext fun l ↦ (v l).2⟩
  left_inv f := rfl
  right_inv v := rfl

lemma dimv_free (n : ℕ) (j : D.ι) :
    dimv D.e (FDMod.free n : FDMod k A) j = n * dimv D.e (FDMod.self : FDMod k A) j := by
  unfold dimv
  rw [(freeEquiv D n j).finrank_eq, Module.finrank_pi_fintype]
  simp

/-- The relation map of a presentation, `Aⁿ¹ → Aⁿ⁰`. -/
def FreePres.rowA {Z : FDMod k A} (P : FreePres A Z) :
    (FDMod.free P.n₁ : FDMod k A) ⟶ (FDMod.free P.n₀ : FDMod k A) :=
  P.syz.subtype ∘ₗ P.rowMap

/-- **The dimension vector from a projective presentation of length one.** -/
theorem dimv_pres {Z : FDMod k A} (P : FreePres A Z) (hF : P.Free) (j : D.ι) :
    (dimv D.e Z j : ℤ) = ((P.n₀ : ℤ) - P.n₁) * ∑ i, cartan D j i := by
  have hinj : Function.Injective (FDMod.lin P.rowA) :=
    Subtype.val_injective.comp (P.rowMap_injective hF)
  have hsurj : Function.Surjective (FDMod.lin (show (FDMod.free P.n₀ : FDMod k A) ⟶ Z from P.gen)) :=
    fun x ↦ P.span x
  have hex : LinearMap.range (FDMod.lin P.rowA) =
      LinearMap.ker (FDMod.lin (show (FDMod.free P.n₀ : FDMod k A) ⟶ Z from P.gen)) := by
    ext p
    constructor
    · rintro ⟨r, rfl⟩
      exact (P.rowMap r).2
    · intro hp
      obtain ⟨r, hr⟩ := P.syz_eq_span p hp
      exact ⟨r, by rw [hr]; rfl⟩
  have h := dimv_exact D.e D.idem P.rowA _ hinj hsurj hex j
  rw [dimv_free, dimv_free] at h
  have hs := dimv_self D j
  have : ((P.n₀ * dimv D.e (FDMod.self : FDMod k A) j : ℕ) : ℤ) =
      ((P.n₁ * dimv D.e (FDMod.self : FDMod k A) j : ℕ) : ℤ) + dimv D.e Z j := by
    exact_mod_cast h
  push_cast at this
  rw [← hs]
  linarith

/-- **The Euler form is `dim Hom - dim Ext¹` in projective dimension one.** -/
theorem euler_eq_hom_sub_ext1 (hT : ∀ x, x ∈ D.T) {Z W : FDMod k A} (P : FreePres A Z)
    (hF : P.Free) :
    euler D (fun j ↦ (dimv D.e Z j : ℤ)) (fun j ↦ (dimv D.e W j : ℤ)) =
      (finrank k (Z →ₗ[A] W) : ℤ) - finrank k (Ext1 (k := k) W P) := by
  rw [finrank_hom_sub_ext1 P hF, finrank_eq_sum_dimv D.e D.idem D.orth D.sum W]
  have hZ : (fun j ↦ (dimv D.e Z j : ℤ)) = ((P.n₀ : ℤ) - P.n₁) • (cartan D *ᵥ fun _ ↦ 1) := by
    funext j
    rw [dimv_pres D P hF j]
    simp [mulVec, dotProduct]
  have hu : IsUnit (cartan D).det := by rw [det_cartan D hT]; exact isUnit_one
  unfold euler
  rw [hZ, mulVec_smul, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
  simp [dotProduct, Finset.mul_sum]

end LargeIndecomposable.AR
