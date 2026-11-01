module

public import LargeIndecomposable.Crowns.Lemma6.CaseII

/-!
# BO13a Lemma 6: long morphisms are not neighbours

In a minimal crown of a minimal representation-infinite ray category all of
whose long morphisms lie in contours, no two neighbours are long
(`MulBasis.lemma6`). For neighbours with a common domain this is
`MulBasis.l6_dom` (cases I, I', II); for neighbours with a common codomain it
is the same statement for `Pᵒᵖ` and the dual crown (`MulBasis.l6_cod`).

The thin categories used as cleaving diagrams are collected in
`MulBasis.L6Shapes`; their representation-infiniteness is a hypothesis here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

namespace Crown

/-- The crown of `P` underlying a crown of `Pᵒᵖ`. -/
def unop (C : Crown Pᵒᵖ) : Crown P where
  n := C.n
  hn := C.hn
  f t := unopRM (C.f (t + 1))
  per t := by rw [show t + 2 * C.n + 1 = t + 1 + 2 * C.n by ring, C.per]
  peak i := (peak_iff_valley_op _ _).2 (C.valley i)
  valley i := by
    have h := C.peak (i + 1)
    have e1 : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
    have e2 : 2 * (i + 1) + 1 = 2 * i + 2 + 1 := by ring
    rw [e2, e1] at h
    exact (valley_iff_peak_op _ _).2 h
  ne t h := C.ne (t + 1) (by have := congrArg Quiver.Hom.op h; exact this)

lemma weight_op (C : Crown P) : C.op.weight = C.weight := by
  change ∑ t ∈ Finset.range (2 * C.n), depth (opRM (C.f (t + 1))).2.2 = C.weight
  rw [C.weight_shift 1]
  exact Finset.sum_congr rfl (fun t _ ↦ depth_op _)

lemma weight_unop (C : Crown Pᵒᵖ) : C.unop.weight = C.weight := by
  change ∑ t ∈ Finset.range (2 * C.n), depth (unopRM (C.f (t + 1))).2.2 = C.weight
  rw [C.weight_shift 1]
  exact Finset.sum_congr rfl (fun t _ ↦ (depth_op _).symm)

lemma IsMin.op {C : Crown P} (hC : C.IsMin) : C.op.IsMin := by
  intro C'
  rcases hC C'.unop with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.1, by rw [weight_op]; rw [weight_unop] at h; exact h.2⟩

end Crown

end RayCat

namespace RayQuiver

namespace MulBasis

/-- The representation-infinite thin categories used in BO13a Lemma 6. -/
structure L6Shapes (k : Type u) [Field k] : Prop where
  f63 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F63.thin) k)
  f64 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F64.thin) k)
  f66 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F66.thin) k)
  f67 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F67.thin) k)
  f68 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F68.thin) k)
  f610 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F610.thin) k)
  f611 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F611.thin) k)
  f612 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F612.thin) k)
  f617 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F617.thin) k)

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **BO13a Lemma 6, neighbours with a common domain**: `σ (r+1)` and `ρ (r+2)`
are not both long in a minimal crown. -/
theorem l6_dom
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (hC : C.IsMin) (r : ℕ)
    (hσ : IsLong (C.toZChain.σ (r + 1))) (hρ : IsLong (C.toZChain.ρ (r + 2)))
    (hS : L6Shapes k) : False := by
  by_cases hσ₂ : IsLong (C.toZChain.σ (r + 2))
  · exact B.l6_caseI hmin hL hR hQ hcont C hC r hσ hρ hσ₂ hS.f63 hS.f64 hS.f66
  by_cases hρn : IsLong (C.toZChain.ρ (r + 1))
  · exact B.l6_caseI' hmin hL hR hQ hcont C hC r hσ hρ hρn hS.f63 hS.f64 hS.f66
  exact B.l6_caseII hmin hL hR hQ hcont C hC r hσ hρ hρn hσ₂ hS.f67 hS.f68 hS.f610 hS.f611
    hS.f612 hS.f617

include B in
/-- **BO13a Lemma 6, neighbours with a common codomain**: `ρ (r+1)` and `σ (r+1)`
are not both long in a minimal crown (`l6_dom` for the dual crown). -/
theorem l6_cod
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (hC : C.IsMin) (r : ℕ)
    (hρn : IsLong (C.toZChain.ρ (r + 1))) (hσ : IsLong (C.toZChain.σ (r + 1)))
    (hS : L6Shapes k) : False := by
  let _ : IsRayCategory Pᵒᵖ := isRayCategory_of_finiteRayCategory
  let _ : Fintype Pᵒᵖ := Fintype.ofFinite _
  let _ : DecidableEq Pᵒᵖ := Classical.decEq _
  have _ : FiniteDimensional k A := B.finiteDimensional
  have hn := C.hn
  obtain ⟨s, hs⟩ : ∃ s, s = r + C.n - 1 := ⟨_, rfl⟩
  have e1 : (⟨_, _, C.op.toZChain.σ (s + 1)⟩ : RayMor Pᵒᵖ) =
      opRM ⟨_, _, C.toZChain.ρ (r + 1)⟩ := by
    rw [Crown.toZChain_σ, Crown.toZChain_ρ]
    change opRM (C.f (2 * (s + 1) + 1 + 1)) = opRM (C.f (2 * (r + 1)))
    rw [show 2 * (s + 1) + 1 + 1 = 2 * (r + 1) + 2 * C.n * 1 by omega, C.f_add_mul]
  have e2 : (⟨_, _, C.op.toZChain.ρ (s + 2)⟩ : RayMor Pᵒᵖ) =
      opRM ⟨_, _, C.toZChain.σ (r + 1)⟩ := by
    rw [Crown.toZChain_ρ, Crown.toZChain_σ]
    change opRM (C.f (2 * (s + 2) + 1)) = opRM (C.f (2 * (r + 1) + 1))
    rw [show 2 * (s + 2) + 1 = 2 * (r + 1) + 1 + 2 * C.n * 1 by omega, C.f_add_mul]
  exact (B.op).l6_dom (hmin_op (k := k) hmin) (leftCancel_op hR) (rightCancel_op hL)
    (oneSidedCyclic_op hQ) (hcont_op hcont) C.op hC.op s
    (isLong_of_rayMor_eq e1.symm ((isLong_op_iff _).2 hρn))
    (isLong_of_rayMor_eq e2.symm ((isLong_op_iff _).2 hσ)) hS

include B in
/-- **BO13a Lemma 6**: no two neighbours of a minimal crown are long. -/
theorem lemma6
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (hC : C.IsMin) (hS : L6Shapes k) (t : ℕ) (h1 : IsLong (C.f t).2.2)
    (h2 : IsLong (C.f (t + 1)).2.2) : False := by
  have hn := C.hn
  rcases Nat.even_or_odd t with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · obtain ⟨r, hr⟩ : ∃ r, r = q + 2 * C.n - 1 := ⟨_, rfl⟩
    have e1 : (⟨_, _, C.toZChain.ρ (r + 1)⟩ : RayMor P) = C.f (q + q) := by
      rw [Crown.toZChain_ρ, show 2 * (r + 1) = q + q + 2 * C.n * 2 by omega, C.f_add_mul]
    have e2 : (⟨_, _, C.toZChain.σ (r + 1)⟩ : RayMor P) = C.f (q + q + 1) := by
      rw [Crown.toZChain_σ, show 2 * (r + 1) + 1 = q + q + 1 + 2 * C.n * 2 by omega,
        C.f_add_mul]
    exact B.l6_cod hmin hL hR hQ hcont C hC r (isLong_of_rayMor_eq e1.symm h1)
      (isLong_of_rayMor_eq e2.symm h2) hS
  · obtain ⟨r, hr⟩ : ∃ r, r = q + 2 * C.n - 1 := ⟨_, rfl⟩
    have e1 : (⟨_, _, C.toZChain.σ (r + 1)⟩ : RayMor P) = C.f (2 * q + 1) := by
      rw [Crown.toZChain_σ, show 2 * (r + 1) + 1 = 2 * q + 1 + 2 * C.n * 2 by omega,
        C.f_add_mul]
    have e2 : (⟨_, _, C.toZChain.ρ (r + 2)⟩ : RayMor P) = C.f (2 * q + 1 + 1) := by
      rw [Crown.toZChain_ρ, show 2 * (r + 2) = 2 * q + 1 + 1 + 2 * C.n * 2 by omega,
        C.f_add_mul]
    exact B.l6_dom hmin hL hR hQ hcont C hC r (isLong_of_rayMor_eq e1.symm h1)
      (isLong_of_rayMor_eq e2.symm h2) hS

end MulBasis

end RayQuiver

end LargeIndecomposable
