module

public import LargeIndecomposable.BongartzTheorem.Reduction.Corollaries

/-!
# Gluing two orthogonal bricks along a non-split extension

For Kronecker modules `C, B` and maps `α, β : V_B → W_C`, the extension module
`E(α, β)` has `V = V_C × V_B`, `W = W_C × W_B` and block upper-triangular arrow
maps. If `C` and `B` are Hom-orthogonal bricks and the extension does not split
(`(α, β)` is not of the form `(a_C φ − ψ a_B, b_C φ − ψ b_B)`), then `E(α, β)`
is a brick (`Bricks.isBrick_ext`). This is the basic step for building large
bricks by gluing (route note on Göbel–Simson).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair

universe u

variable {k : Type u} [Field k]

namespace Bricks

lemma brick_app {X : Kron k} (hX : IsBrickKron X) (f : X ⟶ X) :
    ∃ c : k, (∀ v, (f.app zero).hom v = c • v) ∧ ∀ w, (f.app one).hom w = c • w := by
  obtain ⟨c, hc⟩ := hX.2 f
  subst hc
  exact ⟨c, fun _ ↦ rfl, fun _ ↦ rfl⟩

variable (C B : Kron k) (α β : B.V →ₗ[k] C.W)

/-- The block upper-triangular arrow map `(v, w) ↦ (a_C v + α w, a_B w)`. -/
def triMap (aC : C.V →ₗ[k] C.W) (aB : B.V →ₗ[k] B.W) (γ : B.V →ₗ[k] C.W) :
    (C.V × B.V) →ₗ[k] (C.W × B.W) :=
  (aC ∘ₗ LinearMap.fst k _ _ + γ ∘ₗ LinearMap.snd k _ _).prod (aB ∘ₗ LinearMap.snd k _ _)

lemma triMap_apply (aC : C.V →ₗ[k] C.W) (aB : B.V →ₗ[k] B.W) (γ : B.V →ₗ[k] C.W) (x : C.V × B.V) :
    triMap C B aC aB γ x = (aC x.1 + γ x.2, aB x.2) := rfl

/-- The extension module `E(α, β)` of `B` by `C`. -/
def ext : Kron k :=
  Kron.mk (ModuleCat.of k (C.V × B.V)) (ModuleCat.of k (C.W × B.W))
    (ModuleCat.ofHom (triMap C B C.a.hom B.a.hom α)) (ModuleCat.ofHom (triMap C B C.b.hom B.b.hom β))

/-- The extension splits: `(α, β) = (a_C φ − ψ a_B, b_C φ − ψ b_B)`. -/
def Splits : Prop :=
  ∃ (φ : B.V →ₗ[k] C.V) (ψ : B.W →ₗ[k] C.W),
    α = C.a.hom ∘ₗ φ - ψ ∘ₗ B.a.hom ∧ β = C.b.hom ∘ₗ φ - ψ ∘ₗ B.b.hom

variable {C B α β}

/-- Gluing two Hom-orthogonal bricks along a non-split extension gives a brick. -/
theorem isBrick_ext (hC : IsBrickKron C) (hB : IsBrickKron B) (hCB : ∀ f : C ⟶ B, f = 0)
    (hBC : ∀ f : B ⟶ C, f = 0) (hns : ¬Splits C B α β) : IsBrickKron (ext C B α β) := by
  refine ⟨fun hz ↦ hC.1 (Functor.isZero C fun j ↦ ?_), fun f ↦ ?_⟩
  · have hs : Subsingleton ((ext C B α β).obj j) := ModuleCat.isZero_iff_subsingleton.1 (hz.obj j)
    rw [ModuleCat.isZero_iff_subsingleton]
    cases j
    · exact ⟨fun x y ↦ congrArg Prod.fst (@Subsingleton.elim _ hs ((x, 0) : C.V × B.V) (y, 0))⟩
    · exact ⟨fun x y ↦ congrArg Prod.fst (@Subsingleton.elim _ hs ((x, 0) : C.W × B.W) (y, 0))⟩
  set F : (C.V × B.V) →ₗ[k] (C.V × B.V) := (f.app zero).hom
  set G : (C.W × B.W) →ₗ[k] (C.W × B.W) := (f.app one).hom
  have hFa : ∀ x, G (triMap C B C.a.hom B.a.hom α x) = triMap C B C.a.hom B.a.hom α (F x) :=
    fun x ↦ Kron.a_apply f x
  have hFb : ∀ x, G (triMap C B C.b.hom B.b.hom β x) = triMap C B C.b.hom B.b.hom β (F x) :=
    fun x ↦ Kron.b_apply f x
  have hFsplit : ∀ x : C.V × B.V, F x = F (x.1, 0) + F (0, x.2) := fun x ↦ by
    rw [← map_add]; simp
  have hGsplit : ∀ x : C.W × B.W, G x = G (x.1, 0) + G (0, x.2) := fun x ↦ by
    rw [← map_add]; simp
  -- the component `C → B` vanishes
  let g0 : C.V →ₗ[k] B.V := LinearMap.snd k _ _ ∘ₗ F ∘ₗ LinearMap.inl k _ _
  let h0 : C.W →ₗ[k] B.W := LinearMap.snd k _ _ ∘ₗ G ∘ₗ LinearMap.inl k _ _
  have r0 : ∀ v, h0 (C.a.hom v) = B.a.hom (g0 v) := fun v ↦ by
    have := congrArg Prod.snd (hFa (v, 0)); simpa [triMap_apply, g0, h0] using this
  have r1 : ∀ v, h0 (C.b.hom v) = B.b.hom (g0 v) := fun v ↦ by
    have := congrArg Prod.snd (hFb (v, 0)); simpa [triMap_apply, g0, h0] using this
  have hr := hCB (Kron.homMk (ModuleCat.ofHom g0) (ModuleCat.ofHom h0)
    (ModuleCat.hom_ext (LinearMap.ext r0)) (ModuleCat.hom_ext (LinearMap.ext r1)))
  have hg0 : ∀ v, g0 v = 0 := fun v ↦ congrArg (fun φ : C ⟶ B ↦ (φ.app zero).hom v) hr
  have hh0 : ∀ w, h0 w = 0 := fun w ↦ congrArg (fun φ : C ⟶ B ↦ (φ.app one).hom w) hr
  -- the component `C → C` is a scalar `c`
  let p0 : C.V →ₗ[k] C.V := LinearMap.fst k _ _ ∘ₗ F ∘ₗ LinearMap.inl k _ _
  let p1 : C.W →ₗ[k] C.W := LinearMap.fst k _ _ ∘ₗ G ∘ₗ LinearMap.inl k _ _
  have pa : ∀ v, p1 (C.a.hom v) = C.a.hom (p0 v) := fun v ↦ by
    have := congrArg Prod.fst (hFa (v, 0))
    have h := hg0 v
    simp only [triMap_apply, map_zero, add_zero, g0, LinearMap.comp_apply, LinearMap.inl_apply,
      LinearMap.snd_apply] at this h
    simpa [p0, p1, h] using this
  have pb : ∀ v, p1 (C.b.hom v) = C.b.hom (p0 v) := fun v ↦ by
    have := congrArg Prod.fst (hFb (v, 0))
    have h := hg0 v
    simp only [triMap_apply, map_zero, add_zero, g0, LinearMap.comp_apply, LinearMap.inl_apply,
      LinearMap.snd_apply] at this h
    simpa [p0, p1, h] using this
  obtain ⟨c, hc0, hc1⟩ := brick_app hC (Kron.homMk (ModuleCat.ofHom p0) (ModuleCat.ofHom p1)
    (ModuleCat.hom_ext (LinearMap.ext fun v ↦ pa v)) (ModuleCat.hom_ext (LinearMap.ext fun v ↦ pb v)))
  -- the component `B → B` is a scalar `d`
  let s0 : B.V →ₗ[k] B.V := LinearMap.snd k _ _ ∘ₗ F ∘ₗ LinearMap.inr k _ _
  let s1 : B.W →ₗ[k] B.W := LinearMap.snd k _ _ ∘ₗ G ∘ₗ LinearMap.inr k _ _
  have sa : ∀ w, s1 (B.a.hom w) = B.a.hom (s0 w) := fun w ↦ by
    have := congrArg Prod.snd (hFa (0, w))
    rw [hGsplit] at this
    have h := hh0 (α w)
    simp only [triMap_apply, map_zero, zero_add, h0, LinearMap.comp_apply, LinearMap.inl_apply,
      LinearMap.snd_apply] at this h
    simpa [s0, s1, h] using this
  have sb : ∀ w, s1 (B.b.hom w) = B.b.hom (s0 w) := fun w ↦ by
    have := congrArg Prod.snd (hFb (0, w))
    rw [hGsplit] at this
    have h := hh0 (β w)
    simp only [triMap_apply, map_zero, zero_add, h0, LinearMap.comp_apply, LinearMap.inl_apply,
      LinearMap.snd_apply] at this h
    simpa [s0, s1, h] using this
  obtain ⟨d, hd0, hd1⟩ := brick_app hB (Kron.homMk (ModuleCat.ofHom s0) (ModuleCat.ofHom s1)
    (ModuleCat.hom_ext (LinearMap.ext fun w ↦ sa w)) (ModuleCat.hom_ext (LinearMap.ext fun w ↦ sb w)))
  have hc0' : ∀ v, p0 v = c • v := hc0
  have hc1' : ∀ w, p1 w = c • w := hc1
  have hd0' : ∀ w, s0 w = d • w := hd0
  have hd1' : ∀ w, s1 w = d • w := hd1
  -- the component `B → C`
  let q0 : B.V →ₗ[k] C.V := LinearMap.fst k _ _ ∘ₗ F ∘ₗ LinearMap.inr k _ _
  let q1 : B.W →ₗ[k] C.W := LinearMap.fst k _ _ ∘ₗ G ∘ₗ LinearMap.inr k _ _
  have qa : ∀ w, (d - c) • α w = q1 (B.a.hom w) - C.a.hom (q0 w) := fun w ↦ by
    have := congrArg Prod.fst (hFa (0, w))
    rw [hGsplit] at this
    simp only [triMap_apply, map_zero, zero_add] at this
    change p1 (α w) + q1 (B.a.hom w) = C.a.hom (q0 w) + α (s0 w) at this
    rw [hc1', hd0', map_smul] at this
    rw [sub_smul, eq_sub_iff_add_eq]
    calc d • α w - c • α w + C.a.hom (q0 w) = (C.a.hom (q0 w) + d • α w) - c • α w := by abel
      _ = (c • α w + q1 (B.a.hom w)) - c • α w := by rw [this]
      _ = q1 (B.a.hom w) := by abel
  have qb : ∀ w, (d - c) • β w = q1 (B.b.hom w) - C.b.hom (q0 w) := fun w ↦ by
    have := congrArg Prod.fst (hFb (0, w))
    rw [hGsplit] at this
    simp only [triMap_apply, map_zero, zero_add] at this
    change p1 (β w) + q1 (B.b.hom w) = C.b.hom (q0 w) + β (s0 w) at this
    rw [hc1', hd0', map_smul] at this
    rw [sub_smul, eq_sub_iff_add_eq]
    calc d • β w - c • β w + C.b.hom (q0 w) = (C.b.hom (q0 w) + d • β w) - c • β w := by abel
      _ = (c • β w + q1 (B.b.hom w)) - c • β w := by rw [this]
      _ = q1 (B.b.hom w) := by abel
  by_cases hcd : d = c
  · subst hcd
    have hq : ∀ (w : B.V), C.a.hom (q0 w) = q1 (B.a.hom w) ∧ C.b.hom (q0 w) = q1 (B.b.hom w) := by
      intro w
      have h1 := qa w
      have h2 := qb w
      rw [sub_self, zero_smul] at h1 h2
      exact ⟨(sub_eq_zero.1 h1.symm).symm, (sub_eq_zero.1 h2.symm).symm⟩
    have hz := hBC (Kron.homMk (ModuleCat.ofHom q0) (ModuleCat.ofHom q1)
      (ModuleCat.hom_ext (LinearMap.ext fun w ↦ (hq w).1.symm))
      (ModuleCat.hom_ext (LinearMap.ext fun w ↦ (hq w).2.symm)))
    have hq0 : ∀ w, q0 w = 0 := fun w ↦ congrArg (fun φ : B ⟶ C ↦ (φ.app zero).hom w) hz
    have hq1 : ∀ w, q1 w = 0 := fun w ↦ congrArg (fun φ : B ⟶ C ↦ (φ.app one).hom w) hz
    refine ⟨d, Kron.hom_ext (ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
      (ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))⟩
    · change F x = d • x
      rw [hFsplit x]
      refine Prod.ext ?_ ?_
      · change p0 x.1 + q0 x.2 = d • x.1
        rw [hc0', hq0, add_zero]
      · change g0 x.1 + s0 x.2 = d • x.2
        rw [hg0, hd0', zero_add]
    · change G x = d • x
      rw [hGsplit x]
      refine Prod.ext ?_ ?_
      · change p1 x.1 + q1 x.2 = d • x.1
        rw [hc1', hq1, add_zero]
      · change h0 x.1 + s1 x.2 = d • x.2
        rw [hh0, hd1', zero_add]
  · exfalso
    apply hns
    have hdc : d - c ≠ 0 := sub_ne_zero.2 hcd
    refine ⟨-(d - c)⁻¹ • q0, -(d - c)⁻¹ • q1, LinearMap.ext fun w ↦ ?_, LinearMap.ext fun w ↦ ?_⟩
    · simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
      have h := qa w
      have e : α w = (d - c)⁻¹ • ((d - c) • α w) := by
        rw [smul_smul, inv_mul_cancel₀ hdc, one_smul]
      rw [e, h, smul_sub]
      simp only [neg_smul, sub_neg_eq_add]
      abel
    · simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
      have h := qb w
      have e : β w = (d - c)⁻¹ • ((d - c) • β w) := by
        rw [smul_smul, inv_mul_cancel₀ hdc, one_smul]
      rw [e, h, smul_sub]
      simp only [neg_smul, sub_neg_eq_add]
      abel

end Bricks

end LargeIndecomposable
