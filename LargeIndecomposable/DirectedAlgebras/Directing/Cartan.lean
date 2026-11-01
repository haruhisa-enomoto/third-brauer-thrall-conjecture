module

public import LargeIndecomposable.DirectedAlgebras.Directing.DirData
public import LargeIndecomposable.DirectedAlgebras.Directing.DimVector

/-!
# The Cartan matrix of a directed algebra

The Cartan matrix has entries `dim e_j A e_i` (`cartan`). For a directed algebra it is lower
triangular along a linear extension of the path order with ones on the diagonal, so its
determinant is one (`det_cartan`) and it is invertible over `ℤ`. The Euler form
`⟨u, v⟩ = (C⁻¹ u) · v` satisfies `⟨dim P(i), v⟩ = v_i` (`euler_cartan_col`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open Module Matrix

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (D : DirData k A)

/-- **The Cartan matrix**: `C j i = dim e_j A e_i`. -/
def cartan : Matrix D.ι D.ι ℤ := fun j i ↦ (finrank k (eSub (projE (k := k) (D.idem i)) (D.e j)) : ℤ)

/-- The path order. -/
def pathOrder : PartialOrder D.ι where
  le x y := Relation.ReflTransGen D.Arr x y
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  le_antisymm x y hxy hyx := by
    by_contra hne
    exact D.acyc x y (D.transGen_of_ne hxy hne) hyx

lemma eSub_eq_bot {i j : D.ι} (h : ¬Relation.ReflTransGen D.Arr i j) :
    eSub (projE (k := k) (D.idem i)) (D.e j) = ⊥ := by
  rw [eq_bot_iff]
  intro m hm
  rw [Submodule.mem_bot]
  by_contra hm0
  apply h
  apply D.hom i j (m : A)
  have h1 : (m : A) * D.e i = m := m.2
  have h2 : D.e j * (m : A) = m := congrArg Subtype.val hm
  rw [h2, h1]
  exact fun h0 ↦ hm0 (Subtype.ext h0)

lemma cartan_eq_zero {i j : D.ι} (h : ¬Relation.ReflTransGen D.Arr i j) : cartan D j i = 0 := by
  simp [cartan, eSub_eq_bot D h]

lemma cartan_diag {i : D.ι} (hi : i ∈ D.T) : cartan D i i = 1 := by
  have he : (⟨D.e i, e_mem (D.idem i)⟩ : leftIdeal (D.idem i)) ∈ eSub (projE (k := k) (D.idem i))
      (D.e i) := Subtype.ext (D.idem i).eq
  have hspan : eSub (projE (k := k) (D.idem i)) (D.e i) =
      Submodule.span k {(⟨D.e i, e_mem (D.idem i)⟩ : projE (k := k) (D.idem i))} := by
    refine le_antisymm (fun m hm ↦ ?_) ((Submodule.span_le).2 (Set.singleton_subset_iff.2 he))
    obtain ⟨c, hc⟩ := D.local_ i (m : A)
    rw [Submodule.mem_span_singleton]
    refine ⟨c, Subtype.ext ?_⟩
    have h1 : (m : A) * D.e i = m := m.2
    have h2 : D.e i * (m : A) = m := congrArg Subtype.val hm
    change c • D.e i = (m : A)
    rw [← hc, h2, h1]
  unfold cartan
  rw [hspan, finrank_span_singleton]
  · rfl
  · intro h0
    exact D.ne i hi (congrArg Subtype.val h0)

/-- **The Cartan matrix of a directed algebra has determinant one.** -/
theorem det_cartan (hT : ∀ x, x ∈ D.T) : (cartan D).det = 1 := by
  obtain ⟨lo, hmono⟩ : ∃ lo : LinearOrder D.ι,
      ∀ x y : D.ι, Relation.ReflTransGen D.Arr x y → lo.le x y := by
    letI : PartialOrder D.ι := pathOrder D
    exact ⟨(inferInstance : LinearOrder (LinearExtension D.ι)), fun x y h ↦
      (toLinearExtension (α := D.ι)).monotone h⟩
  letI := lo
  have hM : (cartan D).IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    apply cartan_eq_zero D
    intro h
    exact absurd (hmono _ _ h) (not_le_of_gt hij')
  rw [det_of_isLowerTriangular _ hM]
  exact Finset.prod_eq_one fun i _ ↦ cartan_diag D (hT i)

/-- **The Euler form** `⟨u, v⟩ = (C⁻¹ u) · v`. -/
def euler (u v : D.ι → ℤ) : ℤ := ((cartan D)⁻¹ *ᵥ u) ⬝ᵥ v

/-- **`⟨dim P(i), v⟩ = v_i`.** -/
theorem euler_cartan_col (hT : ∀ x, x ∈ D.T) (i : D.ι) (v : D.ι → ℤ) :
    euler D (fun j ↦ cartan D j i) v = v i := by
  have hcol : (fun j ↦ cartan D j i) = cartan D *ᵥ Pi.single i 1 := by
    funext j
    simp [mulVec, dotProduct, Pi.single_apply]
  have hu : IsUnit (cartan D).det := by rw [det_cartan D hT]; exact isUnit_one
  unfold euler
  rw [hcol, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
  simp [dotProduct, Pi.single_apply]

end LargeIndecomposable.AR
