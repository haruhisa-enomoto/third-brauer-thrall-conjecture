module

public import LargeIndecomposable.Crowns.Lemma6.CaseIUMain

/-!
# Symmetries for BO13a Lemma 6

* `RayCat.L6Data.swap`: the data of figure 6.0 with the roles of `σ` and `ρ`
  exchanged.
* `RayCat.Crown.rev_f`: entries of the reversed crown; `Crown.weight_rev`,
  `Crown.IsMin.rev`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

/-- Figure 6.0 with `σ` and `ρ` exchanged. -/
def L6Data.swap {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (D : L6Data σ ρ) : L6Data ρ σ where
  a := D.a
  α := D.α
  m := D.m
  χ := D.χ
  u₂ := D.u₂'
  u₂' := D.u₂
  b := D.b'
  β := D.β'
  w := D.w'
  b' := D.b
  β' := D.β
  w' := D.w
  hu₂ := D.hu₂'
  hu₂' := D.hu₂
  hσu := D.hρu
  hρu := D.hσu
  hσw := D.hρw
  hρw := D.hσw
  hniσ := D.hniρ
  hniρ := D.hniσ
  hmax φ h1 h2 h3 := D.hmax φ h1 h3 h2

namespace Crown

variable (C : Crown P)

/-- **Entries of the reversed crown**: position `p` of `C.rev` is position `q`
of `C` when `p + q ≡ 1`. -/
lemma rev_f (p q : ℕ) (h : (p + q) % (2 * C.n) = 1 % (2 * C.n)) : C.rev.f p = C.f q := by
  change C.f (2 * C.n * (p + 1) + 1 - p) = C.f q
  rw [C.f_mod, C.f_mod q]
  congr 1
  have hp : p ≤ 2 * C.n * (p + 1) + 1 := by
    have := C.hn
    nlinarith
  have e1 : (2 * C.n * (p + 1) + 1 - p + p) % (2 * C.n) = 1 % (2 * C.n) := by
    rw [Nat.sub_add_cancel hp, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
  exact Nat.ModEq.add_right_cancel' p (e1.trans (h.symm.trans (by rw [add_comm])))

/-- The weight of the reversed crown. -/
lemma weight_rev : C.rev.weight = C.weight := by
  have hn := C.hn
  have e1 : ∀ t ∈ Finset.range (2 * C.n),
      depth (C.rev.f t).2.2 = depth (C.f (2 * C.n + 1 - t)).2.2 := by
    intro t ht
    simp only [Finset.mem_range] at ht
    change depth (C.f (2 * C.n * (t + 1) + 1 - t)).2.2 = _
    rw [show 2 * C.n * (t + 1) + 1 - t = (2 * C.n + 1 - t) + 2 * C.n * t by
      rw [Nat.mul_succ]; omega, C.f_add_mul]
  change ∑ t ∈ Finset.range (2 * C.n), depth (C.rev.f t).2.2 = C.weight
  rw [Finset.sum_congr rfl e1, ← Finset.sum_range_reflect, C.weight_shift 2]
  refine Finset.sum_congr rfl (fun j hj ↦ ?_)
  simp only [Finset.mem_range] at hj
  rw [show 2 * C.n + 1 - (2 * C.n - 1 - j) = j + 2 by omega]

lemma IsMin.rev {C : Crown P} (hC : C.IsMin) : C.rev.IsMin := by
  intro C'
  rcases hC C' with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.1, by rw [weight_rev]; exact h.2⟩

variable [IsRayCategory P]

lemma rev_σ (t q : ℕ) (h : (2 * t + 1 + q) % (2 * C.n) = 1 % (2 * C.n)) :
    (⟨_, _, C.rev.toZChain.σ t⟩ : RayMor P) = C.f q :=
  (toZChain_σ C.rev t).trans (C.rev_f _ _ h)

lemma rev_ρ (t q : ℕ) (h : (2 * t + q) % (2 * C.n) = 1 % (2 * C.n)) :
    (⟨_, _, C.rev.toZChain.ρ t⟩ : RayMor P) = C.f q :=
  (toZChain_ρ C.rev t).trans (C.rev_f _ _ h)

/-- The index in the reversed crown matching `r` (`r' + r + 3 ≡ 0 mod n`). -/
def revIdx (r : ℕ) : ℕ := C.n * (r + 3) - (r + 3)

lemma revIdx_add (r : ℕ) : C.revIdx r + r + 3 = C.n * (r + 3) := by
  have := C.hn
  unfold revIdx
  have : r + 3 ≤ C.n * (r + 3) := Nat.le_mul_of_pos_left _ this
  omega

lemma revIdx_mod (r k : ℕ) : (2 * (C.revIdx r + r + 3) + 1 + 2 * C.n * k) % (2 * C.n) =
    1 % (2 * C.n) := by
  rw [C.revIdx_add, show 2 * (C.n * (r + 3)) + 1 + 2 * C.n * k = 1 + 2 * C.n * (r + 3 + k) by ring,
    Nat.add_mul_mod_self_left]

end Crown

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **BO13a Lemma 6, case I'**: `σ₁`, `ρ₁` and `ρₙ` long is impossible (case I
for the reversed crown). -/
theorem l6_caseI'
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (hC : C.IsMin) (r : ℕ)
    (hσ : IsLong (C.toZChain.σ (r + 1))) (hρ : IsLong (C.toZChain.ρ (r + 2)))
    (hρn : IsLong (C.toZChain.ρ (r + 1)))
    (hD63 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F63.thin) k))
    (hD64 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F64.thin) k))
    (hD66 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F66.thin) k)) :
    False := by
  set r' := C.revIdx r with hr'
  have e1 : (⟨_, _, C.rev.toZChain.σ (r' + 1)⟩ : RayMor P) = ⟨_, _, C.toZChain.ρ (r + 2)⟩ := by
    rw [C.rev_σ (r' + 1) (2 * (r + 2)) (by
      have := C.revIdx_mod r 0
      rw [← hr'] at this
      rw [show 2 * (r' + 1) + 1 + 2 * (r + 2) = 2 * (r' + r + 3) + 1 + 2 * C.n * 0 by ring]
      exact this)]
    rfl
  have e2 : (⟨_, _, C.rev.toZChain.ρ (r' + 2)⟩ : RayMor P) = ⟨_, _, C.toZChain.σ (r + 1)⟩ := by
    rw [C.rev_ρ (r' + 2) (2 * (r + 1) + 1) (by
      have := C.revIdx_mod r 0
      rw [← hr'] at this
      rw [show 2 * (r' + 2) + (2 * (r + 1) + 1) = 2 * (r' + r + 3) + 1 + 2 * C.n * 0 by ring]
      exact this), Crown.toZChain_σ]
  have e3 : (⟨_, _, C.rev.toZChain.σ (r' + 2)⟩ : RayMor P) = ⟨_, _, C.toZChain.ρ (r + 1)⟩ := by
    rw [C.rev_σ (r' + 2) (2 * (r + 1)) (by
      have := C.revIdx_mod r 0
      rw [← hr'] at this
      rw [show 2 * (r' + 2) + 1 + 2 * (r + 1) = 2 * (r' + r + 3) + 1 + 2 * C.n * 0 by ring]
      exact this)]
    rfl
  exact B.l6_caseI hmin hL hR hQ hcont C.rev hC.rev r' (isLong_of_rayMor_eq e1.symm hρ)
    (isLong_of_rayMor_eq e2.symm hσ) (isLong_of_rayMor_eq e3.symm hρn) hD63 hD64 hD66

end MulBasis

end RayQuiver

end LargeIndecomposable
