module

public import LargeIndecomposable.Crowns.Lemma5.Wrap
public import LargeIndecomposable.MultiplicativeBases.Twisted.MulBasisOp
public import LargeIndecomposable.Modules.Duality.OppositeDuality

/-!
# BO13a Lemma 5 a) for the other neighbour

`MulBasis.lemma5a_mk` restates Lemma 5 a) with the chain morphisms given by
equations of `RayMor`s. Applying it to the crown `C.op.rev` in `Pᵒᵖ` gives the
mirror statement (`MulBasis.lemma5a_last`): if `σ s` is long, then `ρ s` (the
neighbour with the same codomain) factors through a last arrow of any contour
of `σ s`. The transfers of long morphisms and contours to `Pᵒᵖ` are
`RayCat.isLong_op_iff` and `RayCat.not_notInContour_unop`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable Opposite

universe u

namespace RayCat

section Op

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

lemma ftm_op_iff {a b x y : P} (μ : a ⟶ b) (f : x ⟶ y) :
    FactorsThroughMorphism μ.op f.op ↔ FactorsThroughMorphism μ f := by
  constructor
  · rintro ⟨c, d, h⟩
    refine ⟨d.unop, c.unop, ?_⟩
    apply Quiver.Hom.op_inj
    rw [h]
    simp
  · rintro ⟨c, d, h⟩
    exact ⟨d.op, c.op, by rw [h]; simp⟩

lemma isLongAt_op {a b : P} {μ : a ⟶ b} (h : IsLongAt μ) : IsLongAt μ.op := by
  intro X Y F hF hftm
  obtain ⟨x⟩ := X
  obtain ⟨y⟩ := Y
  have hF' : F.unop ≠ 0 := fun h0 ↦ hF (by rw [← Quiver.Hom.op_unop F, h0]; rfl)
  obtain ⟨hy, hx, he⟩ := h F.unop hF' ((ftm_op_iff μ F.unop).1 hftm)
  subst hy hx
  refine ⟨rfl, rfl, ?_⟩
  apply Quiver.Hom.unop_inj
  simpa using he

lemma isLongAt_unop {A B : Pᵒᵖ} {μ : A ⟶ B} (h : IsLongAt μ) : IsLongAt μ.unop := by
  intro x y f hf hftm
  have hf' : f.op ≠ 0 := fun h0 ↦ hf (Quiver.Hom.op_inj (by rw [h0]; rfl))
  obtain ⟨hy, hx, he⟩ := h f.op hf' ((ftm_op_iff μ.unop f).2 hftm)
  subst hy hx
  refine ⟨rfl, rfl, ?_⟩
  apply Quiver.Hom.op_inj
  simpa using he

lemma isLong_op_iff {x y : P} (f : x ⟶ y) : IsLong f.op ↔ IsLong f := by
  constructor
  · rintro ⟨h0, hi, hr, hl⟩
    exact ⟨fun h ↦ h0 (by rw [h]; rfl), fun h ↦ hi inferInstance,
      fun h ↦ hr ((isIrreducible_op f).2 h), isLongAt_unop hl⟩
  · rintro ⟨h0, hi, hr, hl⟩
    exact ⟨fun h ↦ h0 (Quiver.Hom.op_inj (by rw [h]; rfl)), fun h ↦ hi ((isIso_op_iff f).1 h),
      fun h ↦ hr ((isIrreducible_op f).1 h), isLongAt_op hl⟩

lemma not_notInContour_unop {A B : Pᵒᵖ} {μ : A ⟶ B} (h : ¬NotInContour μ.unop) :
    ¬NotInContour μ := by
  intro hop
  apply h
  intro v w hv hw
  have hi := hop (revPath (x := RayVert.mk B.unop) (y := RayVert.mk A.unop) v)
    (revPath (x := RayVert.mk B.unop) (y := RayVert.mk A.unop) w)
    (by rw [pathVal_revPath, hv]; rfl) (by rw [pathVal_revPath, hw]; rfl)
  have := interlaced_unrevPath hi
  rwa [unrevPath_revPath, unrevPath_revPath] at this

lemma hcont_op (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ) {A B : Pᵒᵖ}
    (μ : A ⟶ B) (hμ : IsLong μ) : ¬NotInContour μ :=
  not_notInContour_unop (hcont _ ((isLong_op_iff μ.unop).1 hμ))

end Op

section CrownEntries

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

lemma rayMor_eq_of_eqToHom (g : RayMor P) {X Y : P} (h1 : g.1 = X) (h2 : g.2.1 = Y) :
    (⟨X, Y, eqToHom h1.symm ≫ g.2.2 ≫ eqToHom h2⟩ : RayMor P) = g := by
  obtain ⟨g1, g2, g3⟩ := g
  subst h1 h2
  simp

lemma isLong_of_rayMor_eq {f g : RayMor P} (h : f = g) (hf : IsLong f.2.2) : IsLong g.2.2 :=
  h ▸ hf

variable [IsRayCategory P]

lemma Crown.toZChain_σ (C : Crown P) (s : ℕ) :
    (⟨_, _, C.toZChain.σ s⟩ : RayMor P) = C.f (2 * s + 1) :=
  rayMor_eq_of_eqToHom _ (C.valley s).1 (C.peak s).1.symm

lemma Crown.toZChain_ρ (C : Crown P) (s : ℕ) :
    (⟨_, _, C.toZChain.ρ s⟩ : RayMor P) = C.f (2 * s) := rfl

lemma Crown.isLong_σ_add (C : Crown P) (s : ℕ) (h : IsLong (C.toZChain.σ s)) :
    IsLong (C.toZChain.σ (s + C.n)) := by
  have e : (⟨_, _, C.toZChain.σ (s + C.n)⟩ : RayMor P) = ⟨_, _, C.toZChain.σ s⟩ := by
    rw [Crown.toZChain_σ, Crown.toZChain_σ, show 2 * (s + C.n) + 1 = 2 * s + 1 + 2 * C.n by ring,
      C.per]
  exact isLong_of_rayMor_eq e.symm h

lemma idx_σ (n s : ℕ) (hn : 0 < n) :
    2 * n * (2 * (n * (2 * s + 1) - s) + 1 + 1) + 1 - (2 * (n * (2 * s + 1) - s) + 1) + 1 =
      2 * s + 1 + 2 * n * (2 * (n * (2 * s + 1) - s) + 2 - (2 * s + 1)) := by
  obtain ⟨N, hN⟩ : ∃ N, N = n * (2 * s + 1) := ⟨_, rfl⟩
  rw [← hN]
  have hle : 2 * s + 1 ≤ N := hN ▸ Nat.le_mul_of_pos_left _ hn
  generalize hK : 2 * (N - s) + 2 - (2 * s + 1) = K
  have e : 2 * (N - s) + 1 + 1 = K + (2 * s + 1) := by omega
  have key : 2 * n * (K + (2 * s + 1)) = 2 * n * K + 2 * N := by rw [mul_add, hN]; ring
  rw [e, key]
  omega

lemma idx_ρ (n s : ℕ) (hn : 0 < n) :
    2 * n * (2 * (n * (2 * s + 1) - s + 1) + 1) + 1 - 2 * (n * (2 * s + 1) - s + 1) + 1 =
      2 * s + 2 * n * (2 * (n * (2 * s + 1) - s) + 3 - (2 * s + 1)) := by
  obtain ⟨N, hN⟩ : ∃ N, N = n * (2 * s + 1) := ⟨_, rfl⟩
  rw [← hN]
  have hle : 2 * s + 1 ≤ N := hN ▸ Nat.le_mul_of_pos_left _ hn
  generalize hK : 2 * (N - s) + 3 - (2 * s + 1) = K
  have e : 2 * (N - s + 1) + 1 = K + (2 * s + 1) := by omega
  have key : 2 * n * (K + (2 * s + 1)) = 2 * n * K + 2 * N := by rw [mul_add, hN]; ring
  have hK1 : 1 ≤ K := by omega
  have hnK : 2 ≤ 2 * n * K := by nlinarith
  rw [e, key]
  omega

end CrownEntries

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **BO13a Lemma 5 a)**, with the chain morphisms given by `RayMor` equations. -/
theorem lemma5a_mk
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (Z : ZChain P) (s : ℕ) {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁}
    (hσe : (⟨_, _, Z.σ s⟩ : RayMor P) = ⟨x, y₀, σ⟩)
    (hρe : (⟨_, _, Z.ρ (s + 1)⟩ : RayMor P) = ⟨x, y₁, ρ⟩)
    (hσ : IsLong σ) (hnext : ∃ j, IsLong (Z.σ (s + 1 + j)))
    {a₁ b₁ : RayVert P} (α : RayVert.mk x ⟶ a₁) (β : RayVert.mk x ⟶ b₁)
    (v' : Quiver.Path a₁ (RayVert.mk y₀)) (w' : Quiver.Path b₁ (RayVert.mk y₀))
    (hv : pathVal (α.toPath.comp v') = σ) (hw : pathVal (β.toPath.comp w') = σ)
    (hni : ¬Interlaced (α.toPath.comp v') (β.toPath.comp w'))
    (hα : ¬∃ g, α.1 ≫ g = ρ) (hβ : ¬∃ g, β.1 ≫ g = ρ) : False := by
  cases hρe
  cases hσe
  exact B.lemma5a hmin hL hR hQ hcont Z s hσ hnext α β v' w' hv hw hni hα hβ

include B in
/-- **BO13a Lemma 5 a), dual form.** If `σ s` is long in the chain of a crown,
then `ρ s` factors through a last arrow of any contour of `σ s`. -/
theorem lemma5a_last
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (s : ℕ) (hσ : IsLong (C.toZChain.σ s)) {a₁ b₁ : RayVert P}
    (α : a₁ ⟶ RayVert.mk (C.toZChain.z s)) (β : b₁ ⟶ RayVert.mk (C.toZChain.z s))
    (v' : Quiver.Path (RayVert.mk (C.toZChain.x (s + 1))) a₁)
    (w' : Quiver.Path (RayVert.mk (C.toZChain.x (s + 1))) b₁)
    (hv : pathVal (v'.cons α) = C.toZChain.σ s) (hw : pathVal (w'.cons β) = C.toZChain.σ s)
    (hni : ¬Interlaced (v'.cons α) (w'.cons β))
    (hα : ¬∃ g, g ≫ α.1 = C.toZChain.ρ s) (hβ : ¬∃ g, g ≫ β.1 = C.toZChain.ρ s) : False := by
  let _ : IsRayCategory Pᵒᵖ := isRayCategory_of_finiteRayCategory
  let _ : Fintype Pᵒᵖ := Fintype.ofFinite _
  let _ : DecidableEq Pᵒᵖ := Classical.decEq _
  have _ : FiniteDimensional k A := B.finiteDimensional
  have hn := C.hn
  set s' := C.n * (2 * s + 1) - s with hs'
  have eσ : (⟨_, _, (C.op.rev).toZChain.σ s'⟩ : RayMor Pᵒᵖ) =
      ⟨Opposite.op (C.toZChain.z s), Opposite.op (C.toZChain.x (s + 1)), (C.toZChain.σ s).op⟩ := by
    rw [Crown.toZChain_σ]
    change opRM (C.f (2 * C.n * (2 * s' + 1 + 1) + 1 - (2 * s' + 1) + 1)) = _
    rw [hs', idx_σ C.n s hn, C.f_add_mul, ← Crown.toZChain_σ]
    rfl
  have eρ : (⟨_, _, (C.op.rev).toZChain.ρ (s' + 1)⟩ : RayMor Pᵒᵖ) =
      ⟨Opposite.op (C.toZChain.z s), Opposite.op (C.toZChain.x s), (C.toZChain.ρ s).op⟩ := by
    rw [Crown.toZChain_ρ]
    change opRM (C.f (2 * C.n * (2 * (s' + 1) + 1) + 1 - 2 * (s' + 1) + 1)) = _
    rw [hs', idx_ρ C.n s hn, C.f_add_mul, ← Crown.toZChain_ρ]
    rfl
  have hσ' : IsLong (C.toZChain.σ s).op := (isLong_op_iff _).2 hσ
  refine (B.op).lemma5a_mk (hmin_op (k := k) hmin) (leftCancel_op hR) (rightCancel_op hL)
    (oneSidedCyclic_op hQ) (hcont_op hcont) (C.op.rev).toZChain s' eσ eρ hσ'
    ⟨C.n - 1, ?_⟩ (revArr α) (revArr β) (revPath v') (revPath w') ?_ ?_ ?_ ?_ ?_
  · have h := Crown.isLong_σ_add (C.op.rev) s' (isLong_of_rayMor_eq eσ.symm hσ')
    rwa [show s' + 1 + (C.n - 1) = s' + (C.op.rev).n by
      change _ = s' + C.n
      omega]
  · change pathVal (revPath (v'.cons α)) = _
    rw [pathVal_revPath, hv]
  · change pathVal (revPath (w'.cons β)) = _
    rw [pathVal_revPath, hw]
  · intro h
    apply hni
    have := interlaced_unrevPath (P := P) h
    change Interlaced (unrevPath (revPath (v'.cons α))) (unrevPath (revPath (w'.cons β))) at this
    rwa [unrevPath_revPath, unrevPath_revPath] at this
  · rintro ⟨g, hg⟩
    exact hα ⟨g.unop, Quiver.Hom.op_inj (by rw [op_comp]; exact hg)⟩
  · rintro ⟨g, hg⟩
    exact hβ ⟨g.unop, Quiver.Hom.op_inj (by rw [op_comp]; exact hg)⟩

end MulBasis

end RayQuiver

end LargeIndecomposable
