module

public import LargeIndecomposable.AuslanderReiten.AlmostSplit.RightAlmostSplit

/-!
# Right almost split maps into indecomposable projectives; all indecomposables

A summand of a finite free module lifts along surjections (`IsFreeSummand.lift`). If its
endomorphism ring is local, it has a unique maximal submodule, and the inclusion of that
submodule is right almost split (`exists_rightAlmostSplit_of_freeSummand`). Together with
`exists_rightAlmostSplit`, every finite-dimensional module with local endomorphism ring
has a right almost split map (`exists_rightAlmostSplit'`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open Module

universe w

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
variable {Z : Type*} [AddCommGroup Z] [Module A Z]

/-- A summand of a finite free module lifts along surjections. -/
lemma IsFreeSummand.lift (hZ : IsFreeSummand A Z) {X : Type*} [AddCommGroup X] [Module A X]
    (π : X →ₗ[A] Z) (hπ : Function.Surjective π) : ∃ s : Z →ₗ[A] X, π ∘ₗ s = LinearMap.id := by
  classical
  obtain ⟨m, α, β, hαβ⟩ := hZ
  choose x hx using fun j : Fin m ↦ hπ (β (Pi.single j 1))
  let t : (Fin m → A) →ₗ[A] X :=
    { toFun p := ∑ j, p j • x j
      map_add' p q := by simp [add_smul, Finset.sum_add_distrib]
      map_smul' a p := by simp [mul_smul, Finset.smul_sum] }
  have ht : π ∘ₗ t = β := by
    refine LinearMap.ext fun p ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, t, LinearMap.coe_mk, AddHom.coe_mk,
      map_sum, map_smul, hx]
    simp_rw [← map_smul, ← map_sum]
    congr 1
    funext i; simp [Pi.single_apply, Finset.sum_apply]
  exact ⟨t ∘ₗ α, by rw [← LinearMap.comp_assoc, ht, hαβ]⟩

/-- **Unique maximal submodule** of a projective with local endomorphism ring. -/
lemma IsFreeSummand.maximal_unique [IsLocalRing (Module.End A Z)] (hZ : IsFreeSummand A Z)
    {U V : Submodule A Z} (hU : IsCoatom U) (hV : IsCoatom V) : U = V := by
  by_contra hne
  have hsup : U ⊔ V = ⊤ := by
    by_contra h
    exact hne ((hU.le_iff.1 le_sup_left).resolve_left h |>.symm.trans
      ((hV.le_iff.1 le_sup_right).resolve_left h))
  let π : (U × V) →ₗ[A] Z := U.subtype ∘ₗ LinearMap.fst A U V + V.subtype ∘ₗ LinearMap.snd A U V
  have hπ : Function.Surjective π := by
    intro z
    have : z ∈ U ⊔ V := by rw [hsup]; trivial
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 this
    exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), by simp [π]⟩
  obtain ⟨s, hs⟩ := hZ.lift π hπ
  let e₁ : Module.End A Z := U.subtype ∘ₗ LinearMap.fst A U V ∘ₗ s
  let e₂ : Module.End A Z := V.subtype ∘ₗ LinearMap.snd A U V ∘ₗ s
  have he : e₁ + e₂ = 1 := by
    rw [← Module.End.one_eq_id] at hs
    rw [← hs]; ext z; simp [e₁, e₂, π]
  have hunit : IsUnit e₁ ∨ IsUnit e₂ := by
    by_contra h; push Not at h
    exact (IsLocalRing.nonunits_add h.1 h.2) (he ▸ isUnit_one)
  rcases hunit with h | h
  · apply hU.1
    rw [eq_top_iff]; intro z _
    obtain ⟨y, rfl⟩ := (Module.End.isUnit_iff e₁).1 h |>.2 z
    simp [e₁]
  · apply hV.1
    rw [eq_top_iff]; intro z _
    obtain ⟨y, rfl⟩ := (Module.End.isUnit_iff e₂).1 h |>.2 z
    simp [e₂]

variable [Module k Z] [IsScalarTower k A Z]

/-- **Right almost split map into an indecomposable projective**: the inclusion of the
unique maximal submodule. -/
theorem exists_rightAlmostSplit_of_freeSummand [IsLocalRing (Module.End A Z)]
    [FiniteDimensional k Z] (hZ : IsFreeSummand A Z) :
    ∃ U : Submodule A Z, (¬∃ s : Z →ₗ[A] U, U.subtype ∘ₗ s = LinearMap.id) ∧
      ∀ (W : Type w) [AddCommGroup W] [Module A W] (u : W →ₗ[A] Z),
        (¬∃ s : Z →ₗ[A] W, u ∘ₗ s = LinearMap.id) → ∃ v : W →ₗ[A] U, U.subtype ∘ₗ v = u := by
  classical
  have hZnt : Nontrivial Z := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have : (1 : Module.End A Z) = 0 := LinearMap.ext fun z ↦ Subsingleton.elim _ _
    exact one_ne_zero this
  -- `Z` is Noetherian over `A`, so `⊥` lies under a coatom
  haveI : IsNoetherian A Z := isNoetherian_of_tower k inferInstance
  obtain ⟨U, hU, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule A Z)).resolve_left bot_ne_top
  refine ⟨U, ?_, fun W _ _ u hu ↦ ?_⟩
  · rintro ⟨s, hs⟩
    apply hU.1
    rw [eq_top_iff]; intro z _
    have := LinearMap.congr_fun hs z
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearMap.id_coe, id_eq] at this
    rw [← this]; exact (s z).2
  · -- the range of `u` is a proper submodule, hence below `U`
    have hrange : LinearMap.range u ≤ U := by
      by_cases htop : LinearMap.range u = ⊤
      · exact absurd (hZ.lift u (LinearMap.range_eq_top.1 htop)) hu
      · obtain ⟨V, hV, hle⟩ := (eq_top_or_exists_le_coatom (LinearMap.range u)).resolve_left htop
        rw [hZ.maximal_unique hV hU] at hle
        exact hle
    exact ⟨u.codRestrict U fun w ↦ hrange (LinearMap.mem_range_self u w), rfl⟩

end LargeIndecomposable.AR
