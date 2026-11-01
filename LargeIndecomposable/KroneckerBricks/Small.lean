module

public import LargeIndecomposable.BongartzTheorem.Reduction.Corollaries

/-!
# Kronecker bricks of dimension at most `|k|`

For a set `Λ ⊆ k` of scalars, the Kronecker module
`T_Λ = (k^(Λ), k ⊕ k^(Λ); a, b)` with `a(c) = (0, c)` and
`b(c) = (∑_λ c_λ, (λ c_λ)_λ)` is a brick: an endomorphism `(g, h)` satisfies
`(λ - μ) g(e_μ)_λ = h(1, 0)_λ`, which forces `h(1, 0)` to have no second
component and `g` to be diagonal; the first component of `b` then makes `g`
scalar. Its dimension is `1 + 2|Λ|`.

In terms of `P¹`, `T_Λ` is the Kronecker module of the sheaf `O(∑_{λ ∈ Λ} λ)`
(rational functions with at most simple poles in `Λ`). This gives the
Göbel–Simson bricks of every infinite dimension `κ ≤ |k|`, over any field.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair

universe u

variable {k : Type u} [Field k]

namespace Bricks

variable (Λ : Set k)

/-- The sum of the coordinates. -/
def sumMap : (Λ →₀ k) →ₗ[k] k := Finsupp.linearCombination k fun _ ↦ (1 : k)

/-- Multiplication of the coordinate `λ` by `λ`. -/
def diagMap : (Λ →₀ k) →ₗ[k] (Λ →₀ k) := Finsupp.linearCombination k fun l ↦ Finsupp.single l (l : k)

lemma sumMap_single (l : Λ) (t : k) : sumMap Λ (Finsupp.single l t) = t := by
  simp [sumMap]

lemma diagMap_single (l : Λ) (t : k) : diagMap Λ (Finsupp.single l t) = Finsupp.single l ((l : k) * t) := by
  simp [diagMap, Finsupp.smul_single, mul_comm]

/-- The Kronecker module `T_Λ`. -/
def T : Kron k :=
  Kron.mk (ModuleCat.of k (Λ →₀ k)) (ModuleCat.of k (k × (Λ →₀ k)))
    (ModuleCat.ofHom (LinearMap.inr k k _)) (ModuleCat.ofHom ((sumMap Λ).prod (diagMap Λ)))

theorem isBrick (hΛ : Λ.Nonempty) : IsBrickKron (T Λ) := by
  refine ⟨fun h ↦ ?_, fun f ↦ ?_⟩
  · obtain ⟨l, hl⟩ := hΛ
    have h1 : IsZero ((T Λ).obj zero) := h.obj zero
    have hs : Subsingleton ((T Λ).obj zero) := ModuleCat.isZero_iff_subsingleton.1 h1
    have : (Finsupp.single (⟨l, hl⟩ : Λ) (1 : k)) = 0 := @Subsingleton.elim _ hs _ _
    simpa using congrArg (fun c ↦ c ⟨l, hl⟩) this
  set g : (Λ →₀ k) →ₗ[k] (Λ →₀ k) := (f.app zero).hom
  set h : k × (Λ →₀ k) →ₗ[k] k × (Λ →₀ k) := (f.app one).hom
  have ha : ∀ c, h (0, c) = (0, g c) := fun c ↦
    congrArg (fun φ ↦ φ.hom c) (Kron.a_comp f)
  have hb : ∀ c, h (sumMap Λ c, diagMap Λ c) = (sumMap Λ (g c), diagMap Λ (g c)) := fun c ↦
    congrArg (fun φ ↦ φ.hom c) (Kron.b_comp f)
  set α := (h (1, 0)).1
  set γ := (h (1, 0)).2
  -- the equation at `e_μ`
  have key : ∀ (μ : Λ), α = sumMap Λ (g (Finsupp.single μ 1)) ∧
      γ + (μ : k) • g (Finsupp.single μ 1) = diagMap Λ (g (Finsupp.single μ 1)) := by
    intro μ
    have e := hb (Finsupp.single μ 1)
    rw [sumMap_single, diagMap_single, mul_one,
      show ((1 : k), Finsupp.single μ (μ : k)) = (1, 0) + (0, (μ : k) • Finsupp.single μ 1) by
        simp [Finsupp.smul_single], map_add, ha, map_smul] at e
    refine ⟨?_, by simpa using congrArg Prod.snd e⟩
    have := congrArg Prod.fst e
    simpa [α] using this
  have hcoord : ∀ (μ l : Λ), γ l = ((l : k) - μ) * g (Finsupp.single μ 1) l := by
    intro μ l
    have := congrArg (fun c ↦ c l) (key μ).2
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at this
    have hd : diagMap Λ (g (Finsupp.single μ 1)) l = (l : k) * g (Finsupp.single μ 1) l := by
      conv_lhs => rw [← Finsupp.sum_single (g (Finsupp.single μ 1))]
      rw [Finsupp.sum, map_sum, Finsupp.finsetSum_apply]
      simp only [diagMap_single]
      rw [Finset.sum_eq_single l]
      · simp
      · intro b _ hb; simp [hb]
      · intro hl; simp [Finsupp.notMem_support_iff.1 hl]
    rw [hd] at this
    linear_combination this
  have hγ : γ = 0 := by
    ext l
    simpa using hcoord l l
  have hdiag : ∀ μ : Λ, g (Finsupp.single μ 1) = Finsupp.single μ α := by
    intro μ
    have hoff : ∀ l, l ≠ μ → g (Finsupp.single μ 1) l = 0 := by
      intro l hl
      have := hcoord μ l
      rw [hγ, Finsupp.coe_zero, Pi.zero_apply] at this
      have hne : (l : k) - μ ≠ 0 := sub_ne_zero.2 fun e ↦ hl (Subtype.ext e)
      exact (mul_eq_zero.1 this.symm).resolve_left hne
    have hx : g (Finsupp.single μ 1) = Finsupp.single μ (g (Finsupp.single μ 1) μ) := by
      ext l
      by_cases hl : l = μ
      · subst hl; simp
      · simp [Ne.symm hl, hoff l hl]
    have hα : α = g (Finsupp.single μ 1) μ := by
      rw [(key μ).1]
      conv_lhs => rw [hx]
      exact sumMap_single _ _ _
    conv_lhs => rw [hx]
    rw [hα]
  have hg : g = α • LinearMap.id := by
    refine Finsupp.lhom_ext' fun μ ↦ LinearMap.ext_ring ?_
    simp [hdiag]
  refine ⟨α, Kron.hom_ext ?_ ?_⟩
  · ext c
    change g c = α • c
    rw [hg]; rfl
  · ext ⟨t, c⟩
    change h (t, c) = α • (t, c)
    rw [show (t, c) = t • ((1 : k), (0 : Λ →₀ k)) + (0, c) by simp, map_add, map_smul, ha, hg]
    change t • (α, γ) + _ = _
    rw [hγ]
    simp [mul_comm]

lemma dim_T : (T Λ).dim = 1 + Cardinal.lift.{u} (Cardinal.mk Λ) + Cardinal.lift.{u} (Cardinal.mk Λ) := by
  change Module.rank k (Λ →₀ k) + Module.rank k (k × (Λ →₀ k)) = _
  rw [rank_prod', rank_finsupp_self, Module.rank_self]
  ring

end Bricks

/-- Göbel–Simson bricks for dimensions up to `|k|`: for an infinite cardinal
`κ ≤ |k|` there is a Kronecker brick of dimension `κ`. -/
theorem exists_brick_of_le_card (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (hk : κ ≤ Cardinal.mk k) : ∃ T : Kron k, T.dim = κ ∧ IsBrickKron T := by
  obtain ⟨Λ, hΛ⟩ := Cardinal.le_mk_iff_exists_subset.1 (show κ ≤ Cardinal.mk (Set.univ : Set k) by
    rwa [Cardinal.mk_univ])
  refine ⟨Bricks.T Λ, ?_, Bricks.isBrick Λ ?_⟩
  · rw [Bricks.dim_T, Cardinal.lift_id, hΛ.2]
    rw [add_assoc, Cardinal.add_eq_self hκ, Cardinal.add_eq_right hκ (Cardinal.one_le_aleph0.trans hκ)]
  · rw [← Set.nonempty_coe_sort, ← Cardinal.mk_ne_zero_iff, hΛ.2]
    exact (Cardinal.aleph0_pos.trans_le hκ).ne'


/-- The remaining part of the Göbel–Simson input: Kronecker bricks of every
dimension `κ > |k|`. -/
def KroneckerBricksLarge : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (κ : Cardinal.{u}), Cardinal.mk k < κ →
    ∃ T : Kron k, T.dim = κ ∧ IsBrickKron T

/-- Göbel–Simson Corollary 1.3 from its large case. -/
theorem kroneckerBricks_of_large (H : KroneckerBricksLarge.{u}) : KroneckerBricks.{u} := by
  intro k _ _ κ hκ
  rcases le_or_gt κ (Cardinal.mk k) with h | h
  · exact exists_brick_of_le_card κ hκ h
  · exact H k κ h

end LargeIndecomposable
