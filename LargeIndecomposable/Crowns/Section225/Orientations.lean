module

public import LargeIndecomposable.Crowns.Section225.Reflecting

/-!
# BO13a Lemma 8 and §2.2.5 in other positions of the crown

The reversed crown `C.rev` (same category) turns long `ρ`-entries into long `σ`-entries.

* `RayCat.Crown.rev_f_of`: `C.rev.f t = C.f q` when `t + q ≡ 1`.
* `MulBasis.lemma8_mk`, `MulBasis.lemma8_rho`: Lemma 8 for a long `ρ (t+2)` (its
  neighbour `σ (t+1)`).
* `MulBasis.s225_perm_mk`, `MulBasis.s225_perm_rho`: contours of long `ρ`-entries are
  reflecting.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

/-- Positions `t` of `C.rev` and `q` of `C` with `t + q ≡ 1` carry the same entry. -/
lemma Crown.rev_f_of (C : Crown P) (t q m : ℕ) (h : t + q = 2 * C.n * m + 1) :
    C.rev.f t = C.f q := by
  change C.f (2 * C.n * (t + 1) + 1 - t) = C.f q
  have hn := C.hn
  have ht : t + 1 ≤ 2 * C.n * (t + 1) := Nat.le_mul_of_pos_left _ (by omega)
  rcases le_total m (t + 1) with hm | hm
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
    have e : 2 * C.n * (t + 1) = 2 * C.n * m + 2 * C.n * k := by rw [hk]; ring
    rw [show 2 * C.n * (t + 1) + 1 - t = q + 2 * C.n * k by omega, C.f_add_mul]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
    have e : 2 * C.n * m = 2 * C.n * (t + 1) + 2 * C.n * k := by rw [hk]; ring
    rw [show q = 2 * C.n * (t + 1) + 1 - t + 2 * C.n * k by omega, C.f_add_mul]

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- `lemma8` with the entries given by `RayMor` equations. -/
theorem lemma8_mk
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (hC : C.IsMin) (hS : L6Shapes k) (hS8 : L8Shapes k) (s : ℕ)
    {X Y₀ Y₁ X₂ : P} {σ : X ⟶ Y₀} {ρ : X ⟶ Y₁} {σ₂ : X₂ ⟶ Y₁}
    (hσe : (⟨_, _, C.toZChain.σ (s + 2)⟩ : RayMor P) = ⟨X, Y₀, σ⟩)
    (hρe : (⟨_, _, C.toZChain.ρ (s + 3)⟩ : RayMor P) = ⟨X, Y₁, ρ⟩)
    (hσ₂e : (⟨_, _, C.toZChain.σ (s + 3)⟩ : RayMor P) = ⟨X₂, Y₁, σ₂⟩) (hσ : IsLong σ)
    {a : RayVert P} (v₁ : Quiver.Path (RayVert.mk X) a) (v₂ : Quiver.Path a (RayVert.mk Y₀))
    (w : Quiver.Path (RayVert.mk X) (RayVert.mk Y₀)) (hv₁ : 0 < v₁.length) (hv₂ : 0 < v₂.length)
    (hv : pathVal (v₁.comp v₂) = σ) (hw : pathVal w = σ) (hni : ¬Interlaced (v₁.comp v₂) w)
    (ρ₁' : a.out ⟶ Y₁) (hρ₁' : pathVal v₁ ≫ ρ₁' = ρ) (σ₂' : X₂ ⟶ a.out)
    (hσ₂' : σ₂' ≫ ρ₁' = σ₂) : False := by
  cases hσe
  cases hρe
  cases hσ₂e
  exact B.lemma8 hmin hL hR hQ hcont C hC hS hS8 s hσ v₁ v₂ w hv₁ hv₂ hv hw hni ρ₁' hρ₁' σ₂' hσ₂'

include B in
/-- **Lemma 8 for a long `ρ (t+2)`**: if `σ (t+1) = v₁ ≫ ρ'` for a contour `(v₁ v₂, w)` of
`ρ (t+2)`, then `ρ (t+1)` does not factor as `σ' ≫ ρ'`. -/
theorem lemma8_rho
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (hC : C.IsMin) (hS : L6Shapes k) (hS8 : L8Shapes k) (t : ℕ)
    (hρ : IsLong (C.toZChain.ρ (t + 2)))
    {a : RayVert P} (v₁ : Quiver.Path (RayVert.mk (C.toZChain.x (t + 2))) a)
    (v₂ : Quiver.Path a (RayVert.mk (C.toZChain.z (t + 2))))
    (w : Quiver.Path (RayVert.mk (C.toZChain.x (t + 2))) (RayVert.mk (C.toZChain.z (t + 2))))
    (hv₁ : 0 < v₁.length) (hv₂ : 0 < v₂.length)
    (hv : pathVal (v₁.comp v₂) = C.toZChain.ρ (t + 2)) (hw : pathVal w = C.toZChain.ρ (t + 2))
    (hni : ¬Interlaced (v₁.comp v₂) w)
    (ρ' : a.out ⟶ C.toZChain.z (t + 1)) (hρ' : pathVal v₁ ≫ ρ' = C.toZChain.σ (t + 1))
    (σ' : C.toZChain.x (t + 1) ⟶ a.out) (hσ' : σ' ≫ ρ' = C.toZChain.ρ (t + 1)) : False := by
  have hn := C.hn
  set s' := C.n * (t + 4) - t - 4 with hs'
  have hm : C.n * (t + 4) ≥ t + 4 := Nat.le_mul_of_pos_left _ hn
  have e1 : (⟨_, _, C.rev.toZChain.σ (s' + 2)⟩ : RayMor P) = ⟨_, _, C.toZChain.ρ (t + 2)⟩ := by
    rw [Crown.toZChain_σ, Crown.toZChain_ρ]
    exact C.rev_f_of _ _ (t + 4) (by rw [hs', show 2 * C.n * (t + 4) = 2 * (C.n * (t + 4)) by ring]; omega)
  have e2 : (⟨_, _, C.rev.toZChain.ρ (s' + 3)⟩ : RayMor P) = ⟨_, _, C.toZChain.σ (t + 1)⟩ := by
    rw [Crown.toZChain_σ, Crown.toZChain_ρ]
    exact C.rev_f_of _ _ (t + 4) (by rw [hs', show 2 * C.n * (t + 4) = 2 * (C.n * (t + 4)) by ring]; omega)
  have e3 : (⟨_, _, C.rev.toZChain.σ (s' + 3)⟩ : RayMor P) = ⟨_, _, C.toZChain.ρ (t + 1)⟩ := by
    rw [Crown.toZChain_σ, Crown.toZChain_ρ]
    exact C.rev_f_of _ _ (t + 4) (by rw [hs', show 2 * C.n * (t + 4) = 2 * (C.n * (t + 4)) by ring]; omega)
  exact B.lemma8_mk hmin hL hR hQ hcont C.rev hC.rev hS hS8 s' e1 e2 e3 hρ v₁ v₂ w hv₁ hv₂ hv hw
    hni ρ' hρ' σ' hσ'

include B in
/-- `s225_perm` with the entries given by `RayMor` equations. -/
theorem s225_perm_mk
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (hC : C.IsMin) (hS : L6Shapes k) (hS8 : L8Shapes k) (s : ℕ)
    {X Y₀ Y₁ Xn : P} {σ : X ⟶ Y₀} {ρ : X ⟶ Y₁} {ρn : Xn ⟶ Y₀}
    (hσe : (⟨_, _, C.toZChain.σ (s + 2)⟩ : RayMor P) = ⟨X, Y₀, σ⟩)
    (hρe : (⟨_, _, C.toZChain.ρ (s + 3)⟩ : RayMor P) = ⟨X, Y₁, ρ⟩)
    (hρne : (⟨_, _, C.toZChain.ρ (s + 2)⟩ : RayMor P) = ⟨Xn, Y₀, ρn⟩) (hσ : IsLong σ)
    {a b : RayVert P} (α : RayVert.mk X ⟶ a) (v' : Quiver.Path a (RayVert.mk Y₀))
    (w₁ : Quiver.Path (RayVert.mk X) b) (ω : b ⟶ RayVert.mk Y₀)
    (hv : pathVal (α.toPath.comp v') = σ) (hw : pathVal (w₁.cons ω) = σ)
    (hni : ¬Interlaced (α.toPath.comp v') (w₁.cons ω))
    (hα : ∃ g, α.1 ≫ g = ρ) (hω : ∃ g, g ≫ ω.1 = ρn) : False := by
  cases hσe
  cases hρe
  cases hρne
  exact B.s225_perm hmin hL hR hQ hcont C hC hS hS8 s hσ α v' w₁ ω hv hw hni hα hω

include B in
/-- **Contours of long `ρ`-entries are reflecting.** -/
theorem s225_perm_rho
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (hC : C.IsMin) (hS : L6Shapes k) (hS8 : L8Shapes k) (t : ℕ)
    (hρ : IsLong (C.toZChain.ρ (t + 2))) {a b : RayVert P}
    (α : RayVert.mk (C.toZChain.x (t + 2)) ⟶ a)
    (v' : Quiver.Path a (RayVert.mk (C.toZChain.z (t + 2))))
    (w₁ : Quiver.Path (RayVert.mk (C.toZChain.x (t + 2))) b)
    (ω : b ⟶ RayVert.mk (C.toZChain.z (t + 2)))
    (hv : pathVal (α.toPath.comp v') = C.toZChain.ρ (t + 2))
    (hw : pathVal (w₁.cons ω) = C.toZChain.ρ (t + 2))
    (hni : ¬Interlaced (α.toPath.comp v') (w₁.cons ω))
    (hα : ∃ g, α.1 ≫ g = C.toZChain.σ (t + 1)) (hω : ∃ g, g ≫ ω.1 = C.toZChain.σ (t + 2)) :
    False := by
  have hn := C.hn
  set s' := C.n * (t + 4) - t - 4 with hs'
  have hm : C.n * (t + 4) ≥ t + 4 := Nat.le_mul_of_pos_left _ hn
  have e1 : (⟨_, _, C.rev.toZChain.σ (s' + 2)⟩ : RayMor P) = ⟨_, _, C.toZChain.ρ (t + 2)⟩ := by
    rw [Crown.toZChain_σ, Crown.toZChain_ρ]
    exact C.rev_f_of _ _ (t + 4) (by rw [hs', show 2 * C.n * (t + 4) = 2 * (C.n * (t + 4)) by ring]; omega)
  have e2 : (⟨_, _, C.rev.toZChain.ρ (s' + 3)⟩ : RayMor P) = ⟨_, _, C.toZChain.σ (t + 1)⟩ := by
    rw [Crown.toZChain_σ, Crown.toZChain_ρ]
    exact C.rev_f_of _ _ (t + 4) (by rw [hs', show 2 * C.n * (t + 4) = 2 * (C.n * (t + 4)) by ring]; omega)
  have e3 : (⟨_, _, C.rev.toZChain.ρ (s' + 2)⟩ : RayMor P) = ⟨_, _, C.toZChain.σ (t + 2)⟩ := by
    rw [Crown.toZChain_σ, Crown.toZChain_ρ]
    exact C.rev_f_of _ _ (t + 4) (by rw [hs', show 2 * C.n * (t + 4) = 2 * (C.n * (t + 4)) by ring]; omega)
  exact B.s225_perm_mk hmin hL hR hQ hcont C.rev hC.rev hS hS8 s' e1 e2 e3 hρ α v' w₁ ω hv hw hni
    hα hω

end MulBasis

end RayQuiver

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

/-- Positions `t` of `C.op.rev` and `q` of `C` with `t + q ≡ 2` carry dual entries. -/
lemma Crown.oprev_f_of (C : Crown P) (t q m : ℕ) (hq : 1 ≤ q) (h : t + q = 2 * C.n * m + 2) :
    C.op.rev.f t = opRM (C.f q) := by
  rw [C.op.rev_f_of t (q - 1) m (by change t + (q - 1) = 2 * C.n * m + 1; omega)]
  change opRM (C.f (q - 1 + 1)) = _
  rw [Nat.sub_add_cancel hq]

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

open Opposite in
include B in
/-- **Lemma 8 at the peak side of a long `σ (s+2)`**: if `ρ (s+2) = r ≫ v₂` for a contour
`(v₁ v₂, w)`, then `σ (s+1)` does not factor as `r ≫ c` (Lemma 8 in `Pᵒᵖ` for
`C.op.rev`). -/
theorem lemma8_peak
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (hC : C.IsMin) (hS : L6Shapes k) (hS8 : L8Shapes k) (s : ℕ)
    (hσ : IsLong (C.toZChain.σ (s + 2))) {a : RayVert P}
    (v₁ : Quiver.Path (RayVert.mk (C.toZChain.x (s + 3))) a)
    (v₂ : Quiver.Path a (RayVert.mk (C.toZChain.z (s + 2))))
    (w : Quiver.Path (RayVert.mk (C.toZChain.x (s + 3))) (RayVert.mk (C.toZChain.z (s + 2))))
    (hv₁ : 0 < v₁.length) (hv₂ : 0 < v₂.length)
    (hv : pathVal (v₁.comp v₂) = C.toZChain.σ (s + 2)) (hw : pathVal w = C.toZChain.σ (s + 2))
    (hni : ¬Interlaced (v₁.comp v₂) w)
    (r : C.toZChain.x (s + 2) ⟶ a.out) (hr : r ≫ pathVal v₂ = C.toZChain.ρ (s + 2))
    (c : a.out ⟶ C.toZChain.z (s + 1)) (hc : r ≫ c = C.toZChain.σ (s + 1)) : False := by
  let _ : IsRayCategory Pᵒᵖ := isRayCategory_of_finiteRayCategory
  let _ : Fintype Pᵒᵖ := Fintype.ofFinite _
  let _ : DecidableEq Pᵒᵖ := Classical.decEq _
  have _ : FiniteDimensional k A := B.finiteDimensional
  have hn := C.hn
  set s' := C.n * (s + 4) - s - 4 with hs'
  have hm : C.n * (s + 4) ≥ s + 4 := Nat.le_mul_of_pos_left _ hn
  have e1 : (⟨_, _, C.op.rev.toZChain.σ (s' + 2)⟩ : RayMor Pᵒᵖ) =
      ⟨Opposite.op (C.toZChain.z (s + 2)), Opposite.op (C.toZChain.x (s + 3)), (C.toZChain.σ (s + 2)).op⟩ := by
    rw [Crown.toZChain_σ, C.oprev_f_of _ (2 * (s + 2) + 1) (s + 4) (by omega)
      (by rw [hs', show 2 * C.n * (s + 4) = 2 * (C.n * (s + 4)) by ring]; omega),
      ← Crown.toZChain_σ]
    rfl
  have e2 : (⟨_, _, C.op.rev.toZChain.ρ (s' + 3)⟩ : RayMor Pᵒᵖ) =
      ⟨Opposite.op (C.toZChain.z (s + 2)), Opposite.op (C.toZChain.x (s + 2)), (C.toZChain.ρ (s + 2)).op⟩ := by
    rw [Crown.toZChain_ρ, C.oprev_f_of _ (2 * (s + 2)) (s + 4) (by omega)
      (by rw [hs', show 2 * C.n * (s + 4) = 2 * (C.n * (s + 4)) by ring]; omega)]
    rfl
  have e3 : (⟨_, _, C.op.rev.toZChain.σ (s' + 3)⟩ : RayMor Pᵒᵖ) =
      ⟨Opposite.op (C.toZChain.z (s + 1)), Opposite.op (C.toZChain.x (s + 2)), (C.toZChain.σ (s + 1)).op⟩ := by
    rw [Crown.toZChain_σ, C.oprev_f_of _ (2 * (s + 1) + 1) (s + 4) (by omega)
      (by rw [hs', show 2 * C.n * (s + 4) = 2 * (C.n * (s + 4)) by ring]; omega),
      ← Crown.toZChain_σ]
    rfl
  refine (B.op).lemma8_mk (hmin_op (k := k) hmin) (leftCancel_op hR) (rightCancel_op hL)
    (oneSidedCyclic_op hQ) (hcont_op hcont) C.op.rev hC.op.rev hS hS8 s' e1 e2 e3
    ((isLong_op_iff _).2 hσ) (revPath v₂) (revPath v₁) (revPath w)
    (by rw [length_revPath v₂]; exact hv₂) (by rw [length_revPath v₁]; exact hv₁) ?_ ?_ ?_ r.op ?_ c.op
    ?_
  · rw [← revPath_comp v₁ v₂, pathVal_revPath (v₁.comp v₂), hv]
  · rw [pathVal_revPath w, hw]
  · intro h
    apply hni
    rw [← revPath_comp v₁ v₂] at h
    have := interlaced_unrevPath (P := P) h
    rwa [unrevPath_revPath (v₁.comp v₂), unrevPath_revPath w] at this
  · rw [pathVal_revPath v₂, ← op_comp, hr]
  · rw [← op_comp, hc]

open Opposite in
include B in
/-- **Lemma 8 at the peak side of a long `ρ (t+2)`**: if `σ (t+2) = r ≫ v₂` for a contour
`(v₁ v₂, w)`, then `ρ (t+3)` does not factor as `r ≫ c` (Lemma 8 in `Pᵒᵖ` for `C.op`). -/
theorem lemma8_rho_peak
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (hC : C.IsMin) (hS : L6Shapes k) (hS8 : L8Shapes k) (t : ℕ)
    (hρ : IsLong (C.toZChain.ρ (t + 2))) {a : RayVert P}
    (v₁ : Quiver.Path (RayVert.mk (C.toZChain.x (t + 2))) a)
    (v₂ : Quiver.Path a (RayVert.mk (C.toZChain.z (t + 2))))
    (w : Quiver.Path (RayVert.mk (C.toZChain.x (t + 2))) (RayVert.mk (C.toZChain.z (t + 2))))
    (hv₁ : 0 < v₁.length) (hv₂ : 0 < v₂.length)
    (hv : pathVal (v₁.comp v₂) = C.toZChain.ρ (t + 2)) (hw : pathVal w = C.toZChain.ρ (t + 2))
    (hni : ¬Interlaced (v₁.comp v₂) w)
    (r : C.toZChain.x (t + 3) ⟶ a.out) (hr : r ≫ pathVal v₂ = C.toZChain.σ (t + 2))
    (c : a.out ⟶ C.toZChain.z (t + 3)) (hc : r ≫ c = C.toZChain.ρ (t + 3)) : False := by
  let _ : IsRayCategory Pᵒᵖ := isRayCategory_of_finiteRayCategory
  let _ : Fintype Pᵒᵖ := Fintype.ofFinite _
  let _ : DecidableEq Pᵒᵖ := Classical.decEq _
  have _ : FiniteDimensional k A := B.finiteDimensional
  have hn := C.hn
  set s' := t + C.n - 1 with hs'
  have e1 : (⟨_, _, C.op.toZChain.σ (s' + 2)⟩ : RayMor Pᵒᵖ) =
      ⟨Opposite.op (C.toZChain.z (t + 2)), Opposite.op (C.toZChain.x (t + 2)), (C.toZChain.ρ (t + 2)).op⟩ := by
    rw [Crown.toZChain_σ]
    change opRM (C.f (2 * (s' + 2) + 1 + 1)) = _
    rw [show 2 * (s' + 2) + 1 + 1 = 2 * (t + 2) + 2 * C.n * 1 by omega, C.f_add_mul]
    rfl
  have e2 : (⟨_, _, C.op.toZChain.ρ (s' + 3)⟩ : RayMor Pᵒᵖ) =
      ⟨Opposite.op (C.toZChain.z (t + 2)), Opposite.op (C.toZChain.x (t + 3)), (C.toZChain.σ (t + 2)).op⟩ := by
    rw [Crown.toZChain_ρ]
    change opRM (C.f (2 * (s' + 3) + 1)) = _
    rw [show 2 * (s' + 3) + 1 = 2 * (t + 2) + 1 + 2 * C.n * 1 by omega, C.f_add_mul,
      ← Crown.toZChain_σ]
    rfl
  have e3 : (⟨_, _, C.op.toZChain.σ (s' + 3)⟩ : RayMor Pᵒᵖ) =
      ⟨Opposite.op (C.toZChain.z (t + 3)), Opposite.op (C.toZChain.x (t + 3)), (C.toZChain.ρ (t + 3)).op⟩ := by
    rw [Crown.toZChain_σ]
    change opRM (C.f (2 * (s' + 3) + 1 + 1)) = _
    rw [show 2 * (s' + 3) + 1 + 1 = 2 * (t + 3) + 2 * C.n * 1 by omega, C.f_add_mul]
    rfl
  refine (B.op).lemma8_mk (hmin_op (k := k) hmin) (leftCancel_op hR) (rightCancel_op hL)
    (oneSidedCyclic_op hQ) (hcont_op hcont) C.op hC.op hS hS8 s' e1 e2 e3
    ((isLong_op_iff _).2 hρ) (revPath v₂) (revPath v₁) (revPath w)
    (by rw [length_revPath v₂]; exact hv₂) (by rw [length_revPath v₁]; exact hv₁) ?_ ?_ ?_ r.op ?_ c.op
    ?_
  · rw [← revPath_comp v₁ v₂, pathVal_revPath (v₁.comp v₂), hv]
  · rw [pathVal_revPath w, hw]
  · intro h
    apply hni
    rw [← revPath_comp v₁ v₂] at h
    have := interlaced_unrevPath (P := P) h
    rwa [unrevPath_revPath (v₁.comp v₂), unrevPath_revPath w] at this
  · rw [pathVal_revPath v₂, ← op_comp, hr]
  · rw [← op_comp, hc]

end MulBasis

end RayQuiver

end LargeIndecomposable
