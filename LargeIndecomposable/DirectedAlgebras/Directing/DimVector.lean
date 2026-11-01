module

public import LargeIndecomposable.Modules.Idempotents.IdemProj

/-!
# Dimension vectors

For a complete family of orthogonal idempotents `e : ι → A`, a finite-dimensional module is the
direct sum of the subspaces `e_x M` (`piEquiv`), so its dimension is the sum of the entries of its
dimension vector `dimv M x = dim e_x M` (`finrank_eq_sum_dimv`). Isomorphic modules have equal
dimension vectors (`dimv_congr`), and dimension vectors add on direct sums (`dimv_prod`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → A) (he : ∀ x, IsIdempotentElem (e x))
  (horth : ∀ x y, x ≠ y → e x * e y = 0) (hsum : ∑ x, e x = 1)

/-- The dimension vector. -/
def dimv (M : FDMod k A) (x : ι) : ℕ := finrank k (eSub M (e x))

include he horth hsum in
/-- **A module is the sum of its idempotent pieces.** -/
def piEquiv (M : FDMod k A) : M ≃ₗ[k] ∀ x, eSub M (e x) where
  toFun m x := ⟨e x • m, by
    change e x • e x • m = e x • m
    rw [← mul_smul, (he x).eq]⟩
  map_add' m n := by funext x; exact Subtype.ext (smul_add _ _ _)
  map_smul' c m := by funext x; exact Subtype.ext (smul_comm _ _ _)
  invFun v := ∑ x, (v x : M)
  left_inv m := by
    change ∑ x, e x • m = m
    rw [← Finset.sum_smul, hsum, one_smul]
  right_inv v := by
    funext y
    apply Subtype.ext
    change e y • ∑ x, (v x : M) = v y
    rw [Finset.smul_sum, Finset.sum_eq_single y]
    · exact (v y).2
    · intro x _ hxy
      rw [← (v x).2, ← mul_smul, horth y x (Ne.symm hxy), zero_smul]
    · simp

include he horth hsum in
/-- **The dimension is the sum of the dimension vector.** -/
theorem finrank_eq_sum_dimv (M : FDMod k A) : finrank k M = ∑ x, dimv e M x := by
  rw [(piEquiv e he horth hsum M).finrank_eq, Module.finrank_pi_fintype]
  rfl

/-- An `A`-linear map restricts to the idempotent pieces. -/
def eSubMap {M N : FDMod k A} (f : M ⟶ N) (x : ι) : eSub M (e x) →ₗ[k] eSub N (e x) where
  toFun m := ⟨FDMod.lin f m, by
    change e x • FDMod.lin f m = FDMod.lin f m
    rw [← map_smul, show e x • (m : M) = m from m.2]⟩
  map_add' m n := Subtype.ext (map_add _ _ _)
  map_smul' c m := Subtype.ext ((FDMod.lin f).map_smul_of_tower c m)

/-- **Isomorphic modules have equal dimension vectors.** -/
theorem dimv_congr {M N : FDMod k A} (φ : M ≅ N) (x : ι) : dimv e M x = dimv e N x := by
  unfold dimv
  refine LinearEquiv.finrank_eq (LinearEquiv.ofLinear (eSubMap e φ.hom x) (eSubMap e φ.inv x)
    ?_ ?_)
  · refine LinearMap.ext fun m ↦ Subtype.ext ?_
    change FDMod.lin φ.hom (FDMod.lin φ.inv m) = m
    rw [← LinearMap.comp_apply, ← FDMod.lin_comp, φ.inv_hom_id, FDMod.lin_id]; rfl
  · refine LinearMap.ext fun m ↦ Subtype.ext ?_
    change FDMod.lin φ.inv (FDMod.lin φ.hom m) = m
    rw [← LinearMap.comp_apply, ← FDMod.lin_comp, φ.hom_inv_id, FDMod.lin_id]; rfl

include he in
/-- **Dimension vectors are additive on short exact sequences.** -/
theorem dimv_exact {M N L : FDMod k A} (f : M ⟶ N) (g : N ⟶ L)
    (hf : Function.Injective (FDMod.lin f)) (hg : Function.Surjective (FDMod.lin g))
    (hex : LinearMap.range (FDMod.lin f) = LinearMap.ker (FDMod.lin g)) (x : ι) :
    dimv e N x = dimv e M x + dimv e L x := by
  unfold dimv
  have hf' : Function.Injective (eSubMap e f x) := fun m m' h ↦
    Subtype.ext (hf (congrArg Subtype.val h))
  have hg' : Function.Surjective (eSubMap e g x) := by
    intro l
    obtain ⟨n, hn⟩ := hg (l : L)
    refine ⟨⟨e x • n, ?_⟩, Subtype.ext ?_⟩
    · change e x • e x • n = e x • n
      rw [← mul_smul, (he x).eq]
    · change FDMod.lin g (e x • n) = l
      rw [map_smul, hn]
      exact l.2
  have hker : LinearMap.ker (eSubMap e g x) = LinearMap.range (eSubMap e f x) := by
    ext n
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro h
      have h0 : FDMod.lin g (n : N) = 0 := congrArg Subtype.val h
      obtain ⟨m, hm⟩ : (n : N) ∈ LinearMap.range (FDMod.lin f) := by
        rw [hex]; exact h0
      refine ⟨⟨e x • m, ?_⟩, Subtype.ext ?_⟩
      · change e x • e x • m = e x • m
        rw [← mul_smul, (he x).eq]
      · change FDMod.lin f (e x • m) = n
        rw [map_smul, hm]
        exact n.2
    · rintro ⟨m, rfl⟩
      apply Subtype.ext
      change FDMod.lin g (FDMod.lin f m) = 0
      have : FDMod.lin f m ∈ LinearMap.ker (FDMod.lin g) := by rw [← hex]; exact ⟨m, rfl⟩
      exact this
  have h1 := LinearMap.finrank_range_add_finrank_ker (eSubMap e g x)
  rw [LinearMap.range_eq_top.2 hg', finrank_top, hker,
    LinearMap.finrank_range_of_inj hf'] at h1
  omega

end LargeIndecomposable.AR
