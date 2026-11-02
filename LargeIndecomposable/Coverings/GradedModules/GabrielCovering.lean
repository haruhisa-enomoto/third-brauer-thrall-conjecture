module

public import LargeIndecomposable.Coverings.GradedModules.GradedRightAlmostSplit

/-!
# Gabriel's covering theorem, graded form

Let `A` be a finite-dimensional algebra graded by a torsion-free group, such that every
graded-indecomposable projective has a graded maximal submodule. If the
graded-indecomposable modules are, up to isomorphism of `A`-modules, among finitely many
`Y₁, …, Y_r`, then every indecomposable `A`-module is isomorphic to some `Yⱼ`
(`gabriel_density`; Gabriel 1981, 3.6, in the language of graded modules).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.Graded

open Module AR CategoryTheory

universe u

variable {G : Type*} [Group G] [DecidableEq G]
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] {Γ : GrAlg G k A}

/-- Objects carrying a graded-indecomposable grading. -/
def GrInd (Γ : GrAlg G k A) (X : FDMod k A) : Prop :=
  ∃ γ : GrMod Γ X, IsGrIndec γ ∧ Nontrivial X

/-- Every graded-indecomposable projective has a graded maximal submodule. -/
def GrRadHyp (Γ : GrAlg G k A) : Prop :=
  ∀ (Z : FDMod k A) (μ : GrMod Γ Z), IsGrIndec μ → Nontrivial Z → IsFreeSummand A Z →
    ∃ U : Submodule A Z, IsGrSub μ U ∧ IsCoatom U

/-- Right almost split families in the projective case. -/
theorem grRASFam_proj [FiniteDimensional k A] (htf : TorsionFree G) (Z : FDMod k A)
    (μ : GrMod Γ Z) (hind : IsGrIndec μ) [Nontrivial Z] (hZ : IsFreeSummand A Z)
    {U : Submodule A Z} (hU : IsGrSub μ U) (hUc : IsCoatom U) :
    Nonempty (RASFam (GrInd Γ) Z) := by
  classical
  haveI : IsLocalRing (Module.End A Z) := (isIndecMod htf hind).isLocalRing (k := k)
  haveI : IsNoetherian A Z := isNoetherian_of_tower k inferInstance
  let Uobj := FDMod.ofSub U
  obtain ⟨d⟩ := exists_grDecomp Uobj (μ.sub hU)
  refine ⟨RASFam.mk d.ι d.obj (fun i ↦ ⟨d.gr i, d.indec i, d.nt i⟩)
    (fun i ↦ (FDMod.ofLin (show d.obj i →ₗ[A] Z from U.subtype ∘ₗ d.inc i))) ?_ ?_⟩
  · rintro ⟨h, hh⟩
    apply hUc.1
    rw [eq_top_iff]; intro z _
    have := LinearMap.congr_fun hh z
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe,
      id_eq] at this
    rw [← this]
    exact U.sum_mem fun i _ ↦ (d.inc i (FDMod.lin (h i) z)).2
  · intro W v hv
    have hrange : LinearMap.range (FDMod.lin v) ≤ U := by
      by_cases htop : LinearMap.range (FDMod.lin v) = ⊤
      · exact absurd (hZ.lift _ (LinearMap.range_eq_top.1 htop)) fun ⟨s, hs⟩ ↦ hv ⟨(FDMod.ofLin s), hs⟩
      · obtain ⟨V, hV, hle⟩ :=
          (eq_top_or_exists_le_coatom (LinearMap.range (FDMod.lin v))).resolve_left htop
        rw [hZ.maximal_unique hV hUc] at hle
        exact hle
    let t : W →ₗ[A] U := (FDMod.lin v).codRestrict U fun w ↦ hrange (LinearMap.mem_range_self _ w)
    refine ⟨fun i ↦ (FDMod.ofLin (show W →ₗ[A] d.obj i from d.proj i ∘ₗ t)), ?_⟩
    ext w
    have := LinearMap.congr_fun d.sum_id (t w)
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe,
      id_eq] at this
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply]
    change _ = ∑ i, U.subtype (d.inc i (d.proj i (t w)))
    rw [← map_sum U.subtype, this]
    rfl

/-- `DA` as an object. -/
abbrev DAobj (k A : Type u) [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] :
    FDMod k A where
  carrier := DA k A

/-- **Cogenerator**: every nonzero module maps nonzero into a graded-indecomposable. -/
theorem exists_map_grInd [FiniteDimensional k A] (N : FDMod k A) [Nontrivial N] :
    ∃ X, GrInd Γ X ∧ ∃ f : N ⟶ X, FDMod.lin f ≠ 0 := by
  classical
  obtain ⟨n, hn⟩ := exists_ne (0 : N)
  obtain ⟨l, hl, -⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
    (p := (⊥ : Submodule k N)) (x := n) (by simpa using hn) inferInstance
  let φ : N →ₗ[A] DA k A := dualToHomDA (A := A) l
  have hφ : φ ≠ 0 := by
    intro h0
    apply hl
    have := homDAToDual_dualToHomDA (A := A) l
    rw [← this]
    show (φ n).ev 1 = 0
    rw [h0]; rfl
  obtain ⟨d⟩ := exists_grDecomp (DAobj k A) (grDA Γ 1)
  have : ∃ i, d.proj i ∘ₗ φ ≠ 0 := by
    by_contra hall; push Not at hall
    apply hφ
    ext x : 1
    have := LinearMap.congr_fun d.sum_id (φ x)
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe,
      id_eq] at this
    rw [← this, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun i _ ↦ by
      have := LinearMap.congr_fun (hall i) x
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply] at this
      rw [this, map_zero]
  obtain ⟨i, hi⟩ := this
  exact ⟨d.obj i, ⟨d.gr i, d.indec i, d.nt i⟩, (FDMod.ofLin (d.proj i ∘ₗ φ)), hi⟩

/-- **Gabriel's covering theorem (density).** -/
theorem gabriel_density [FiniteDimensional k A] (htf : TorsionFree G) (hrad : GrRadHyp Γ)
    {r : ℕ} (Y : Fin r → FDMod k A)
    (hcover : ∀ X : FDMod k A, GrInd Γ X → ∃ j, ∃ f : Y j →ₗ[A] X, Function.Bijective f)
    (N : FDMod k A) (hN : IsIndecMod A N) [Nontrivial N] :
    ∃ j, ∃ f : Y j →ₗ[A] N, Function.Bijective f := by
  classical
  let b := Finset.univ.sup fun j ↦ finrank k (Y j)
  have hind : ∀ X, GrInd Γ X → IsIndecMod A X := fun X ⟨γ, hγ, _⟩ ↦ isIndecMod htf hγ
  have hdim : ∀ X, GrInd Γ X → finrank k X ≤ b := by
    intro X hX
    obtain ⟨j, f, hf⟩ := hcover X hX
    have : finrank k X = finrank k (Y j) :=
      ((LinearEquiv.ofBijective f hf).restrictScalars k).finrank_eq.symm
    rw [this]
    exact Finset.le_sup (f := fun j ↦ finrank k (Y j)) (Finset.mem_univ j)
  have hnt : ∀ X, GrInd Γ X → Nontrivial X := fun X ⟨_, _, h⟩ ↦ h
  have fam : ∀ X, GrInd Γ X → Nonempty (RASFam (GrInd Γ) X) := by
    intro X ⟨γ, hγ, hXnt⟩
    by_cases hp : IsFreeSummand A X
    · obtain ⟨U, hU, hUc⟩ := hrad X γ hγ hXnt hp
      exact grRASFam_proj htf X γ hγ hp hU hUc
    · exact grRASFam htf X γ hγ hp
  obtain ⟨X, hX, f, hf⟩ := auslander hind hdim hnt fam (fun N' _ ↦ exists_map_grInd N') N hN
    inferInstance
  obtain ⟨j, g, hg⟩ := hcover X hX
  let e := (LinearEquiv.ofBijective (FDMod.lin f) hf).symm.toLinearMap ∘ₗ g
  exact ⟨j, e, (LinearEquiv.ofBijective (FDMod.lin f) hf).symm.bijective.comp hg⟩

end LargeIndecomposable.Graded
