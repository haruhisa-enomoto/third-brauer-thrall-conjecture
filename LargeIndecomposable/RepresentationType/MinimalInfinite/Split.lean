module

public import LargeIndecomposable.RepresentationType.MinimalInfinite.Connected

/-!
# Splitting a point into a receiver and an emitter

Let `1 = e₁ + e_z + e₂` be orthogonal idempotents of `B` such that, writing
`e_j B e_i` for the morphisms `i → j`, there is no morphism between the parts
`1` and `2`, none from `z` to `1` and none from `2` to `z`, and `e_z B e_z = k e_z`.
Then every module is the direct sum of `e₁U + X` and `e₂U + Y`, where
`X ⊆ e_z U` is killed by `e₂ B e_z` and `Y` is a complement. So an
indecomposable module is killed by `e_z B e₁` or by `e₂ B e_z`, and a minimal
representation-infinite algebra admits no such splitting with both blocks
nonzero (`IsMinimalRepInfinite.not_split`). This replaces the emitter-receiver
splitting used by Bongartz ([mild] §4, [Standard] §3).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Statement

universe u

section

variable {B : Type u} [Ring B]

/-- Elements killing a module generate a two-sided ideal killing it. -/
lemma span_smul_eq_zero {M : Type u} [AddCommGroup M] [Module B M] (S : Set B)
    (hS : ∀ s ∈ S, ∀ m : M, s • m = 0) : ∀ x ∈ TwoSidedIdeal.span S, ∀ m : M, x • m = 0 := by
  intro x hx
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx => exact hS x hx
  | zero => intro m; exact zero_smul _ _
  | add x y _ _ hx hy => intro m; rw [add_smul, hx, hy, add_zero]
  | neg x _ hx => intro m; rw [neg_smul, hx, neg_zero]
  | left_absorb a x _ hx => intro m; rw [mul_smul, hx, smul_zero]
  | right_absorb b x _ hx => intro m; rw [mul_smul, hx]

end

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

/-- Data of a splitting of a point `z`. -/
structure SplitPoint (k : Type u) [Field k] (B : Type u) [Ring B] [Algebra k B] where
  e₁ : B
  ez : B
  e₂ : B
  sum : e₁ + ez + e₂ = 1
  h11 : e₁ * e₁ = e₁
  hzz : ez * ez = ez
  h22 : e₂ * e₂ = e₂
  h1z : e₁ * ez = 0
  hz1 : ez * e₁ = 0
  h12 : e₁ * e₂ = 0
  h21 : e₂ * e₁ = 0
  hz2 : ez * e₂ = 0
  h2z : e₂ * ez = 0
  /-- No morphism from `2` to `1`. -/
  b12 : ∀ b, e₁ * b * e₂ = 0
  /-- No morphism from `1` to `2`. -/
  b21 : ∀ b, e₂ * b * e₁ = 0
  /-- No morphism from `z` to `1`. -/
  b1z : ∀ b, e₁ * b * ez = 0
  /-- No morphism from `2` to `z`. -/
  bz2 : ∀ b, ez * b * e₂ = 0
  /-- `z` has only scalar endomorphisms. -/
  bzz : ∀ b, ∃ c : k, ez * b * ez = algebraMap k B c * ez

namespace SplitPoint

variable (D : SplitPoint k B)

lemma decomp (b : B) : b = (D.e₁ + D.ez + D.e₂) * b * (D.e₁ + D.ez + D.e₂) := by
  rw [D.sum, one_mul, mul_one]

/-- **The splitting**: an indecomposable module is killed by `e_z B e₁` or by
`e₂ B e_z`. -/
theorem killed (U : Type u) [AddCommGroup U] [Module B U] (hU : IsIndecomposable B U) :
    (∀ b (u : U), (D.ez * b * D.e₁) • u = 0) ∨ ∀ b (u : U), (D.e₂ * b * D.ez) • u = 0 := by
  letI : Module k U := Module.compHom U (algebraMap k B)
  have hsm : ∀ (c : k) (u : U), c • u = algebraMap k B c • u := fun _ _ ↦ rfl
  have hcomm : ∀ (c : k) (b : B), algebraMap k B c * b = b * algebraMap k B c :=
    fun c b ↦ Algebra.commutes c b
  have hsum : ∀ u : U, u = D.e₁ • u + D.ez • u + D.e₂ • u := fun u ↦ by
    rw [← add_smul, ← add_smul, D.sum, one_smul]
  have hbsum : ∀ (b : B) (u : U), b • u = (b * D.e₁) • u + (b * D.ez) • u + (b * D.e₂) • u :=
    fun b u ↦ by rw [← add_smul, ← add_smul, ← mul_add, ← mul_add, D.sum, mul_one]
  have z0 : ∀ (a : B) (u : U), a = 0 → a • u = 0 := fun a u h ↦ by rw [h, zero_smul]
  -- the subspaces `e_z U ⊇ X`
  let Ez : Submodule k U :=
    { carrier := {u | D.ez • u = u}
      add_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_setOf_eq] at *; rw [smul_add, ha, hb]
      zero_mem' := smul_zero _
      smul_mem' := fun c u hu ↦ by
        simp only [Set.mem_setOf_eq] at *
        rw [hsm, smul_smul, ← hcomm, mul_smul, hu] }
  let X : Submodule k U :=
    { carrier := {u | D.ez • u = u ∧ ∀ b, (D.e₂ * b) • u = 0}
      add_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_setOf_eq] at *
        exact ⟨by rw [smul_add, ha.1, hb.1], fun c ↦ by rw [smul_add, ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨smul_zero _, fun _ ↦ smul_zero _⟩
      smul_mem' := fun c u hu ↦ by
        simp only [Set.mem_setOf_eq] at *
        refine ⟨by rw [hsm, smul_smul, ← hcomm, mul_smul, hu.1], fun b ↦ ?_⟩
        rw [hsm, smul_smul, show D.e₂ * b * algebraMap k B c = algebraMap k B c * (D.e₂ * b) by
          rw [hcomm], mul_smul, hu.2, smul_zero] }
  have hXE : X ≤ Ez := fun u hu ↦ hu.1
  obtain ⟨Y₀, hY₀⟩ := Submodule.exists_isCompl X
  let Y : Submodule k U := Ez ⊓ Y₀
  have hXY : ∀ u, u ∈ X → u ∈ Y → u = 0 := fun u hx hy ↦
    (Submodule.disjoint_def.1 hY₀.disjoint) u hx hy.2
  have hsplit : ∀ u ∈ Ez, ∃ x ∈ X, ∃ y ∈ Y, u = x + y := by
    intro u hu
    have : u ∈ X ⊔ Y₀ := by rw [hY₀.sup_eq_top]; trivial
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 this
    refine ⟨x, hx, y, ⟨?_, hy⟩, rfl⟩
    have := Ez.sub_mem hu (hXE hx)
    simpa using this
  -- `e_z B e_z` acts by scalars on `e_z U`
  have hscal : ∀ b (u : U), D.ez • u = u → ∃ c : k, (D.ez * b) • u = c • u := by
    intro b u hu
    obtain ⟨c, hc⟩ := D.bzz b
    refine ⟨c, ?_⟩
    rw [← hu, smul_smul, hc, mul_smul, hu, hsm]
  have hEz : ∀ u : U, D.ez • D.ez • u = D.ez • u := fun u ↦ by rw [smul_smul, D.hzz]
  let U₁ : Submodule B U :=
    { carrier := {u | D.e₂ • u = 0 ∧ D.ez • u ∈ X}
      add_mem' := fun {a b} ha hb ↦ ⟨by rw [smul_add, ha.1, hb.1, add_zero], by
        rw [smul_add]; exact X.add_mem ha.2 hb.2⟩
      zero_mem' := ⟨smul_zero _, by rw [smul_zero]; exact X.zero_mem⟩
      smul_mem' := fun b u hu ↦ by
        obtain ⟨h2, hx⟩ := hu
        have t1 : ∀ a : B, (a * D.e₂) • u = 0 := fun a ↦ by rw [mul_smul, h2, smul_zero]
        have t2 : ∀ a : B, (D.e₂ * a * D.ez) • u = 0 := fun a ↦ by
          rw [mul_smul, hx.2]
        refine ⟨?_, ?_⟩
        · change D.e₂ • b • u = 0
          rw [smul_smul, hbsum, t1, add_zero, D.b21, zero_smul, zero_add]
          exact t2 b
        · change D.ez • b • u ∈ X
          rw [smul_smul, hbsum, t1, add_zero]
          refine X.add_mem ⟨?_, fun c ↦ ?_⟩ ?_
          · rw [smul_smul, ← mul_assoc, ← mul_assoc, D.hzz]
          · rw [smul_smul, show D.e₂ * c * (D.ez * b * D.e₁) = D.e₂ * (c * D.ez * b) * D.e₁ by
              simp only [mul_assoc], D.b21, zero_smul]
          · obtain ⟨c, hc⟩ := hscal b (D.ez • u) hx.1
            rw [mul_smul, hc]
            exact X.smul_mem c hx }
  let U₂ : Submodule B U :=
    { carrier := {u | D.e₁ • u = 0 ∧ D.ez • u ∈ Y}
      add_mem' := fun {a b} ha hb ↦ ⟨by rw [smul_add, ha.1, hb.1, add_zero], by
        rw [smul_add]; exact Y.add_mem ha.2 hb.2⟩
      zero_mem' := ⟨smul_zero _, by rw [smul_zero]; exact Y.zero_mem⟩
      smul_mem' := fun b u hu ↦ by
        obtain ⟨h1, hy⟩ := hu
        have t1 : ∀ a : B, (a * D.e₁) • u = 0 := fun a ↦ by rw [mul_smul, h1, smul_zero]
        refine ⟨?_, ?_⟩
        · change D.e₁ • b • u = 0
          rw [smul_smul, hbsum, t1, zero_add, D.b1z, D.b12, zero_smul, add_zero]
        · change D.ez • b • u ∈ Y
          rw [smul_smul, hbsum, t1, zero_add, D.bz2, zero_smul, add_zero]
          obtain ⟨c, hc⟩ := hscal b (D.ez • u) hy.1
          rw [mul_smul, hc]
          exact Y.smul_mem c hy }
  have hdec : ∀ u : U, ∃ u₁ ∈ U₁, ∃ u₂ ∈ U₂, u = u₁ + u₂ := by
    intro u
    obtain ⟨x, hx, y, hy, hxy⟩ := hsplit _ (hEz u)
    have hx' : D.ez • x = x := hx.1
    have hy' : D.ez • y = y := hy.1
    refine ⟨D.e₁ • u + x, ⟨?_, ?_⟩, D.e₂ • u + y, ⟨?_, ?_⟩, ?_⟩
    · rw [smul_add, smul_smul, D.h21, zero_smul, zero_add, ← hx', smul_smul, D.h2z, zero_smul]
    · rw [smul_add, smul_smul, D.hz1, zero_smul, zero_add, hx']; exact hx
    · rw [smul_add, smul_smul, D.h12, zero_smul, zero_add, ← hy', smul_smul, D.h1z, zero_smul]
    · rw [smul_add, smul_smul, D.hz2, zero_smul, zero_add, hy']; exact hy
    · conv_lhs => rw [hsum u, hxy]
      abel
  have hcompl : IsCompl U₁ U₂ := by
    refine ⟨Submodule.disjoint_def.2 fun u h₁ h₂ ↦ ?_, codisjoint_iff_le_sup.2 fun u _ ↦ ?_⟩
    · have h0 := hXY _ h₁.2 h₂.2
      rw [hsum u, h₂.1, h0, h₁.1, zero_add, add_zero]
    · obtain ⟨u₁, h₁, u₂, h₂, rfl⟩ := hdec u
      exact Submodule.add_mem_sup h₁ h₂
  rcases hU.2 U₁ U₂ hcompl with h | h
  · left
    intro b u
    obtain ⟨u₁, h₁, u₂, h₂, rfl⟩ := hdec u
    have h₁' : u₁ ∈ (⊥ : Submodule B U) := h ▸ h₁
    rw [(Submodule.mem_bot B).1 h₁', zero_add, mul_smul, h₂.1, smul_zero]
  · right
    intro b u
    obtain ⟨u₁, h₁, u₂, h₂, rfl⟩ := hdec u
    have h₂' : u₂ ∈ (⊥ : Submodule B U) := h ▸ h₂
    rw [(Submodule.mem_bot B).1 h₂', add_zero, mul_smul]
    exact h₁.2.2 b

/-- **No splitting in a minimal representation-infinite algebra.** -/
theorem not_minimal (hB : IsMinimalRepInfinite B) (h₁ : ∃ b, D.ez * b * D.e₁ ≠ 0)
    (h₂ : ∃ b, D.e₂ * b * D.ez ≠ 0) : False := by
  let I₁ : TwoSidedIdeal B := TwoSidedIdeal.span {x | ∃ b, x = D.ez * b * D.e₁}
  let I₂ : TwoSidedIdeal B := TwoSidedIdeal.span {x | ∃ b, x = D.e₂ * b * D.ez}
  have hI₁ : I₁ ≠ ⊥ := by
    obtain ⟨b, hb⟩ := h₁
    intro h0
    have : D.ez * b * D.e₁ ∈ I₁ := TwoSidedIdeal.subset_span ⟨b, rfl⟩
    rw [h0] at this
    exact hb ((TwoSidedIdeal.mem_bot B).1 this)
  have hI₂ : I₂ ≠ ⊥ := by
    obtain ⟨b, hb⟩ := h₂
    intro h0
    have : D.e₂ * b * D.ez ∈ I₂ := TwoSidedIdeal.subset_span ⟨b, rfl⟩
    rw [h0] at this
    exact hb ((TwoSidedIdeal.mem_bot B).1 this)
  obtain ⟨n₁, X₁, hX₁⟩ := hB.2 I₁ hI₁
  obtain ⟨n₂, X₂, hX₂⟩ := hB.2 I₂ hI₂
  refine hB.1 ⟨n₁ + n₂, Fin.append
    (fun i ↦ (ModuleCat.restrictScalars (Ideal.Quotient.mk _)).obj (X₁ i))
    (fun i ↦ (ModuleCat.restrictScalars (Ideal.Quotient.mk _)).obj (X₂ i)), ?_⟩
  intro M _ _ _ hind
  rcases D.killed M hind with h | h
  · have htor : ∀ x ∈ I₁, ∀ m : M, x • m = 0 :=
      span_smul_eq_zero _ (by rintro _ ⟨b, rfl⟩ m; exact h b m)
    obtain ⟨i, hi⟩ := exists_iso_of_isTorsion _ X₁ hX₁ M hind htor
    exact ⟨Fin.castAdd n₂ i, by rwa [Fin.append_left]⟩
  · have htor : ∀ x ∈ I₂, ∀ m : M, x • m = 0 :=
      span_smul_eq_zero _ (by rintro _ ⟨b, rfl⟩ m; exact h b m)
    obtain ⟨i, hi⟩ := exists_iso_of_isTorsion _ X₂ hX₂ M hind htor
    exact ⟨Fin.natAdd n₁ i, by rwa [Fin.append_right]⟩

end SplitPoint

end LargeIndecomposable
