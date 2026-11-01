module

public import LargeIndecomposable.Modules.Homological.Presentation

/-!
# Existence of right almost split maps

Let `A` be a `k`-algebra and `Z` a module with a free presentation `P`, local
endomorphism ring, and not a summand of a finite free module. Put `τZ = ker (ν F)`.
Choose a functional `η` on `End_A(Z)` vanishing on the non-units with `η(1) ≠ 0`, and
`φ : Z → DAⁿ⁰` with `θ(φ)(e(z)) = η(e)`. Then `φ` lands in the range of `ν F`, and the
pullback `E = {(x, λ) | φ x = ν F λ}` with its projection `g : E → Z` is right almost
split (`exists_rightAlmostSplit`): `g` is not a split epimorphism, and every map
`u : W → Z` that is not a split epimorphism factors through `g`.

The proof is the Auslander–Reiten formula `Ext¹(W, τZ) ≅ D Hom(Z, W)` (modulo maps
through projectives) made explicit with the presentation; no `Ext` functor is needed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open Module

universe w

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

variable (A) in
/-- `Z` is a direct summand of a finite free module. -/
def IsFreeSummand (Z : Type*) [AddCommGroup Z] [Module A Z] : Prop :=
  ∃ (m : ℕ) (α : Z →ₗ[A] (Fin m → A)) (β : (Fin m → A) →ₗ[A] Z), β ∘ₗ α = LinearMap.id

/-- `relMap` as a `k`-linear map. -/
def relMapLin {W : Type*} [AddCommGroup W] [Module A W] [Module k W] [IsScalarTower k A W]
    {n₀ n₁ : ℕ} (F : Fin n₁ → Fin n₀ → A) : (Fin n₀ → W) →ₗ[k] (Fin n₁ → W) where
  toFun := relMap F
  map_add' p q := by funext i; simp [relMap, smul_add, Finset.sum_add_distrib]
  map_smul' c p := by
    funext i
    simp [relMap, Finset.smul_sum, smul_comm (F i _) c]

variable {Z : Type*} [AddCommGroup Z] [Module A Z] [Module k Z] [IsScalarTower k A Z]

/-- The pullback `{(x, λ) | φ x = ν F λ}` for `φ = θ⁻¹(θ)`. -/
def pullbackE (P : FreePres A Z) (θ : Module.Dual k (Fin P.n₀ → Z)) :
    Submodule A (Z × (Fin P.n₁ → DA k A)) :=
  LinearMap.ker (thetaInv A θ ∘ₗ LinearMap.fst A Z _ - nu P.F ∘ₗ LinearMap.snd A Z _)

lemma mem_pullbackE (P : FreePres A Z) (θ : Module.Dual k (Fin P.n₀ → Z))
    (p : Z × (Fin P.n₁ → DA k A)) : p ∈ pullbackE P θ ↔ thetaInv A θ p.1 = nu P.F p.2 := by
  simp [pullbackE, sub_eq_zero]

/-- **Right almost split maps from a functional.** If `θ` on `Zⁿ⁰` does not vanish on the
generator tuple and vanishes on `(e zⱼ)ⱼ` for every non-unit `e`, the projection
`pullbackE P θ → Z` is right almost split. -/
theorem rightAlmostSplit_of_theta (hnp : ¬IsFreeSummand A Z) (P : FreePres A Z)
    (θ : Module.Dual k (Fin P.n₀ → Z)) (hθ1 : θ (fun j ↦ P.z j) ≠ 0)
    (hθ0 : ∀ e : Module.End A Z, ¬IsUnit e → θ (fun j ↦ e (P.z j)) = 0) :
    (¬∃ s : Z →ₗ[A] pullbackE P θ,
        (LinearMap.fst A Z _ ∘ₗ (pullbackE P θ).subtype) ∘ₗ s = LinearMap.id) ∧
      ∀ (W : Type w) [AddCommGroup W] [Module A W] [Module k W] [IsScalarTower k A W]
        (u : W →ₗ[A] Z), (¬∃ s : Z →ₗ[A] W, u ∘ₗ s = LinearMap.id) →
        ∃ v : W →ₗ[A] pullbackE P θ, (LinearMap.fst A Z _ ∘ₗ (pullbackE P θ).subtype) ∘ₗ v = u := by
  classical
  let φ : Z →ₗ[A] (Fin P.n₀ → DA k A) := thetaInv A θ
  have hφ : theta φ = θ := theta_thetaInv θ
  have key : ∀ {W : Type w} [AddCommGroup W] [Module A W] [Module k W] [IsScalarTower k A W]
      (u : W →ₗ[A] Z) (v : Z →ₗ[A] W),
      theta (φ ∘ₗ u) (fun j ↦ v (P.z j)) = θ (fun j ↦ (u ∘ₗ v) (P.z j)) := by
    intro W _ _ _ _ u v
    rw [← hφ]; rfl
  have key₁ : ∀ v : Module.End A Z, theta φ (fun j ↦ v (P.z j)) = θ (fun j ↦ v (P.z j)) :=
    fun v ↦ by rw [hφ]
  -- maps factoring through `A` are non-units
  have hrank : ∀ (α : Z →ₗ[A] A) (x : Z), ¬IsUnit (LinearMap.smulRight α x) := by
    rintro α x ⟨e, he⟩
    apply hnp
    refine ⟨1, LinearMap.pi (fun _ ↦ α) ∘ₗ (e⁻¹ : (Module.End A Z)ˣ).val,
      { toFun p := p 0 • x
        map_add' p q := by simp [add_smul]
        map_smul' a p := by simp [mul_smul] }, ?_⟩
    have : (({ toFun p := p 0 • x
               map_add' p q := by simp [add_smul]
               map_smul' a p := by simp [mul_smul] } : (Fin 1 → A) →ₗ[A] Z) ∘ₗ
        LinearMap.pi (fun _ ↦ α)) = LinearMap.smulRight α x := by
      ext y; simp
    rw [← LinearMap.comp_assoc, this, ← he]
    exact e.mul_inv
  -- `φ` lands in the range of `ν F`
  have hrange : ∀ x, φ x ∈ LinearMap.range (nu (k := k) P.F) := by
    intro x
    refine P.mem_range_nu _ fun α ↦ ?_
    have : ∑ j, (φ x j).ev (α (P.z j)) = theta φ (fun j ↦ (LinearMap.smulRight α x) (P.z j)) := by
      simp only [theta_apply, LinearMap.smulRight_apply, map_smul, Pi.smul_apply, DA.ev_smulA,
        one_mul]
    rw [this, key₁]
    exact hθ0 _ (hrank α x)
  set E := pullbackE P θ
  have memE : ∀ p, p ∈ E ↔ φ p.1 = nu P.F p.2 := mem_pullbackE P θ
  refine ⟨?_, fun W _ _ _ _ u hu ↦ ?_⟩
  · -- `g` is not a split epimorphism
    rintro ⟨s, hs⟩
    let ψ : Z →ₗ[A] (Fin P.n₁ → DA k A) := LinearMap.snd A Z _ ∘ₗ E.subtype ∘ₗ s
    have hψ : nu P.F ∘ₗ ψ = φ := by
      ext x : 1
      have h1 := (memE _).1 (s x).2
      have h2 : ((s x : E) : Z × (Fin P.n₁ → DA k A)).1 = x := by
        have := LinearMap.congr_fun hs x
        simpa using this
      rw [h2] at h1
      exact h1.symm
    apply hθ1
    have := key₁ 1
    rw [← hψ] at this
    have e1 : θ (fun j ↦ P.z j) = θ (fun j ↦ (1 : Module.End A Z) (P.z j)) := rfl
    rw [e1, ← this, theta_nu_comp]
    have h0 : relMap P.F (fun j ↦ (1 : Module.End A Z) (P.z j)) = 0 := by
      funext i; simpa [relMap] using P.rel i
    rw [h0, map_zero]
  · -- factorization of non-split maps
    let ℓ := theta (φ ∘ₗ u)
    have hker : LinearMap.ker (relMapLin (k := k) (W := W) P.F) ≤ LinearMap.ker ℓ := by
      intro w hw
      obtain ⟨v, hv⟩ := P.lift w hw
      have hw' : w = fun j ↦ v (P.z j) := funext fun j ↦ (hv j).symm
      rw [LinearMap.mem_ker, hw', key u v]
      refine hθ0 _ fun hunit ↦ hu ?_
      obtain ⟨e, he⟩ := hunit
      refine ⟨v ∘ₗ (e⁻¹ : (Module.End A Z)ˣ).val, ?_⟩
      rw [← LinearMap.comp_assoc]
      change (u ∘ₗ v) * _ = 1
      rw [← he]
      exact e.mul_inv
    obtain ⟨ℓ', hℓ'⟩ := exists_comp_of_ker_le _ ℓ hker
    let ψ : W →ₗ[A] (Fin P.n₁ → DA k A) := thetaInv A ℓ'
    have hψ : nu P.F ∘ₗ ψ = φ ∘ₗ u := by
      apply theta_injective
      refine LinearMap.ext fun w ↦ ?_
      rw [theta_nu_comp, theta_thetaInv]
      exact congrArg (fun f ↦ f w) hℓ'
    refine ⟨LinearMap.codRestrict E (LinearMap.prod u ψ) fun w ↦ (memE _).2 ?_, ?_⟩
    · exact (congrArg (fun f ↦ f w) hψ).symm
    · ext w; rfl

/-- A functional on a local endomorphism ring vanishing on the non-units, nonzero at `1`. -/
theorem exists_eta [IsLocalRing (Module.End A Z)] :
    ∃ η : Module.Dual k (Module.End A Z), η 1 ≠ 0 ∧ ∀ e, ¬IsUnit e → η e = 0 := by
  have smul_unit : ∀ (c : k) (e : Module.End A Z), IsUnit (c • e) → IsUnit e := by
    intro c e he
    obtain ⟨b, hb1, hb2⟩ := isUnit_iff_exists.1 he
    refine isUnit_iff_exists.2 ⟨c • b, ?_, ?_⟩
    · ext x
      have := congrArg (fun f : Module.End A Z ↦ f x) hb1
      simp only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at this ⊢
      rw [LinearMap.map_smul_of_tower]; exact this
    · ext x
      have := congrArg (fun f : Module.End A Z ↦ f x) hb2
      simp only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply,
        LinearMap.map_smul_of_tower] at this ⊢
      exact this
  let M : Submodule k (Module.End A Z) :=
    { carrier := nonunits _
      add_mem' := fun ha hb ↦ IsLocalRing.nonunits_add ha hb
      zero_mem' := zero_mem_nonunits.2 zero_ne_one
      smul_mem' := fun c e he hce ↦ he (smul_unit c e hce) }
  have one_notMem : (1 : Module.End A Z) ∉ M := fun h ↦ h isUnit_one
  obtain ⟨η, hη1, hηM⟩ := Submodule.exists_dual_map_eq_bot_of_notMem one_notMem inferInstance
  refine ⟨η, hη1, fun e he ↦ ?_⟩
  have : η e ∈ M.map η := Submodule.mem_map_of_mem (show e ∈ M from he)
  rwa [hηM, Submodule.mem_bot] at this

/-- The generator evaluation `e ↦ (e zⱼ)ⱼ` is injective, so a functional on `End(Z)`
comes from a functional on `Zⁿ⁰`. -/
theorem exists_theta_of_eta (P : FreePres A Z) (η : Module.Dual k (Module.End A Z)) :
    ∃ θ : Module.Dual k (Fin P.n₀ → Z), ∀ e : Module.End A Z, θ (fun j ↦ e (P.z j)) = η e := by
  let ι : Module.End A Z →ₗ[k] (Fin P.n₀ → Z) :=
    { toFun e j := e (P.z j)
      map_add' e e' := rfl
      map_smul' c e := rfl }
  have hι : LinearMap.ker ι ≤ LinearMap.ker η := by
    intro e he
    have : e = 0 := P.hom_ext fun j ↦ by
      rw [LinearMap.zero_apply]; exact congrFun (LinearMap.mem_ker.1 he) j
    simp [this]
  obtain ⟨θ, hθ⟩ := exists_comp_of_ker_le ι η hι
  exact ⟨θ, fun e ↦ congrArg (fun f ↦ f e) hθ⟩

/-- **Existence of right almost split maps.** -/
theorem exists_rightAlmostSplit [IsLocalRing (Module.End A Z)] (hnp : ¬IsFreeSummand A Z)
    (P : FreePres A Z) :
    ∃ E : Submodule A (Z × (Fin P.n₁ → DA k A)),
      (¬∃ s : Z →ₗ[A] E, (LinearMap.fst A Z _ ∘ₗ E.subtype) ∘ₗ s = LinearMap.id) ∧
      ∀ (W : Type w) [AddCommGroup W] [Module A W] [Module k W] [IsScalarTower k A W]
        (u : W →ₗ[A] Z), (¬∃ s : Z →ₗ[A] W, u ∘ₗ s = LinearMap.id) →
        ∃ v : W →ₗ[A] E, (LinearMap.fst A Z _ ∘ₗ E.subtype) ∘ₗ v = u := by
  obtain ⟨η, hη1, hη0⟩ := exists_eta (k := k) (A := A) (Z := Z)
  obtain ⟨θ, hθe⟩ := exists_theta_of_eta P η
  exact ⟨pullbackE P θ, rightAlmostSplit_of_theta hnp P θ
    (by rw [show (fun j ↦ P.z j) = fun j ↦ (1 : Module.End A Z) (P.z j) from rfl, hθe]; exact hη1)
    (fun e he ↦ by rw [hθe]; exact hη0 e he)⟩

end LargeIndecomposable.AR
