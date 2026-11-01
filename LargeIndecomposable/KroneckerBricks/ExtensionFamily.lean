module

public import LargeIndecomposable.KroneckerBricks.Extension
public import Mathlib.LinearAlgebra.DFinsupp

/-!
# Gluing a family of orthogonal bricks

For Kronecker modules `C` and `B i` (`i : ι`) and maps `α i, β i : V_{B i} → W_C`,
the extension module `E` has `V = V_C × ⨁ V_{B i}`, `W = W_C × ⨁ W_{B i}` and
block upper-triangular arrow maps. If `C` and the `B i` are pairwise
Hom-orthogonal bricks and every component extension is non-split, `E` is a
brick (`Bricks.isBrick_extFamily`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair

universe u

variable {k : Type u} [Field k]

namespace Bricks

variable {ι : Type u} [DecidableEq ι] (C : Kron k) (B : ι → Kron k)

/-- `⨁ V_{B i}`. -/
abbrev SumV : Type u := Π₀ i, (B i).V

/-- `⨁ W_{B i}`. -/
abbrev SumW : Type u := Π₀ i, (B i).W

/-- The diagonal arrow map `⨁ V_{B i} → ⨁ W_{B i}`. -/
def sumMapK (g : ∀ i, (B i).V →ₗ[k] (B i).W) : SumV B →ₗ[k] SumW B :=
  DFinsupp.mapRange.linearMap g

/-- The arrow map `(v, x) ↦ (a_C v + ∑ γ_i x_i, (g_i x_i))`. -/
def famMap (aC : C.V →ₗ[k] C.W) (g : ∀ i, (B i).V →ₗ[k] (B i).W) (γ : ∀ i, (B i).V →ₗ[k] C.W) :
    (C.V × SumV B) →ₗ[k] (C.W × SumW B) :=
  (aC ∘ₗ LinearMap.fst k _ _ + DFinsupp.lsum k γ ∘ₗ LinearMap.snd k _ _).prod
    (sumMapK B g ∘ₗ LinearMap.snd k _ _)

variable (α β : ∀ i, (B i).V →ₗ[k] C.W)

/-- The extension module of the family. -/
def extFamily : Kron k :=
  Kron.mk (ModuleCat.of k (C.V × SumV B)) (ModuleCat.of k (C.W × SumW B))
    (ModuleCat.ofHom (famMap C B C.a.hom (fun i ↦ (B i).a.hom) α))
    (ModuleCat.ofHom (famMap C B C.b.hom (fun i ↦ (B i).b.hom) β))

lemma famMap_apply (aC : C.V →ₗ[k] C.W) (g : ∀ i, (B i).V →ₗ[k] (B i).W)
    (γ : ∀ i, (B i).V →ₗ[k] C.W) (v : C.V) (x : SumV B) :
    famMap C B aC g γ (v, x) = (aC v + DFinsupp.lsum k γ x, DFinsupp.mapRange.linearMap g x) := rfl

lemma famMap_fst (aC : C.V →ₗ[k] C.W) (g : ∀ i, (B i).V →ₗ[k] (B i).W)
    (γ : ∀ i, (B i).V →ₗ[k] C.W) (x : C.V × SumV B) :
    (famMap C B aC g γ x).1 = aC x.1 + DFinsupp.lsum k γ x.2 := rfl

lemma famMap_snd (aC : C.V →ₗ[k] C.W) (g : ∀ i, (B i).V →ₗ[k] (B i).W)
    (γ : ∀ i, (B i).V →ₗ[k] C.W) (x : C.V × SumV B) (i : ι) :
    (famMap C B aC g γ x).2 i = g i (x.2 i) := by
  simp [famMap, sumMapK, DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_apply]

variable {C B α β}

/-- Gluing a pairwise Hom-orthogonal family of bricks along non-split extensions
gives a brick. -/
theorem isBrick_extFamily (hC : IsBrickKron C) (hB : ∀ i, IsBrickKron (B i))
    (hCB : ∀ i (f : C ⟶ B i), f = 0) (hBC : ∀ i (f : B i ⟶ C), f = 0)
    (hBB : ∀ i j, i ≠ j → ∀ f : B i ⟶ B j, f = 0) (hns : ∀ i, ¬Splits C (B i) (α i) (β i)) :
    IsBrickKron (extFamily C B α β) := by
  refine ⟨fun hz ↦ hC.1 (Functor.isZero C fun j ↦ ?_), fun f ↦ ?_⟩
  · have hs : Subsingleton ((extFamily C B α β).obj j) :=
      ModuleCat.isZero_iff_subsingleton.1 (hz.obj j)
    rw [ModuleCat.isZero_iff_subsingleton]
    cases j
    · exact ⟨fun x y ↦ congrArg Prod.fst (@Subsingleton.elim _ hs ((x, 0) : C.V × SumV B) (y, 0))⟩
    · exact ⟨fun x y ↦ congrArg Prod.fst (@Subsingleton.elim _ hs ((x, 0) : C.W × SumW B) (y, 0))⟩
  set F : (C.V × SumV B) →ₗ[k] (C.V × SumV B) := (f.app zero).hom
  set G : (C.W × SumW B) →ₗ[k] (C.W × SumW B) := (f.app one).hom
  have hFa : ∀ x, G (famMap C B C.a.hom (fun i ↦ (B i).a.hom) α x) =
      famMap C B C.a.hom (fun i ↦ (B i).a.hom) α (F x) := fun x ↦ Kron.a_apply f x
  have hFb : ∀ x, G (famMap C B C.b.hom (fun i ↦ (B i).b.hom) β x) =
      famMap C B C.b.hom (fun i ↦ (B i).b.hom) β (F x) := fun x ↦ Kron.b_apply f x
  have hGsplit : ∀ (w : C.W) (y : SumW B), G (w, y) = G (w, 0) + G (0, y) := fun w y ↦ by
    rw [← map_add]; simp
  -- the components `C → B i` vanish
  have hCBi : ∀ i, (∀ v, (F (v, 0)).2 i = 0) ∧ ∀ w, (G (w, 0)).2 i = 0 := by
    intro i
    let g0 : C.V →ₗ[k] (B i).V := DFinsupp.lapply i ∘ₗ LinearMap.snd k _ _ ∘ₗ F ∘ₗ LinearMap.inl k _ _
    let h0 : C.W →ₗ[k] (B i).W := DFinsupp.lapply i ∘ₗ LinearMap.snd k _ _ ∘ₗ G ∘ₗ LinearMap.inl k _ _
    have r0 : ∀ v, h0 (C.a.hom v) = (B i).a.hom (g0 v) := fun v ↦ by
      have := congrArg (fun x ↦ x.2 i) (hFa (v, 0))
      simpa [famMap_apply, famMap_snd, g0, h0] using this
    have r1 : ∀ v, h0 (C.b.hom v) = (B i).b.hom (g0 v) := fun v ↦ by
      have := congrArg (fun x ↦ x.2 i) (hFb (v, 0))
      simpa [famMap_apply, famMap_snd, g0, h0] using this
    have hr := hCB i (Kron.homMk (ModuleCat.ofHom g0) (ModuleCat.ofHom h0)
      (ModuleCat.hom_ext (LinearMap.ext r0)) (ModuleCat.hom_ext (LinearMap.ext r1)))
    exact ⟨fun v ↦ congrArg (fun φ : C ⟶ B i ↦ (φ.app zero).hom v) hr,
      fun w ↦ congrArg (fun φ : C ⟶ B i ↦ (φ.app one).hom w) hr⟩
  have hF2 : ∀ v, (F (v, 0)).2 = 0 := fun v ↦ DFinsupp.ext fun i ↦ (hCBi i).1 v
  have hG2 : ∀ w, (G (w, 0)).2 = 0 := fun w ↦ DFinsupp.ext fun i ↦ (hCBi i).2 w
  -- the component `C → C` is a scalar `c`
  let p0 : C.V →ₗ[k] C.V := LinearMap.fst k _ _ ∘ₗ F ∘ₗ LinearMap.inl k _ _
  let p1 : C.W →ₗ[k] C.W := LinearMap.fst k _ _ ∘ₗ G ∘ₗ LinearMap.inl k _ _
  have pa : ∀ v, p1 (C.a.hom v) = C.a.hom (p0 v) := fun v ↦ by
    have := congrArg Prod.fst (hFa (v, 0))
    rw [famMap_fst, famMap_apply, hF2] at this
    simpa [p0, p1] using this
  have pb : ∀ v, p1 (C.b.hom v) = C.b.hom (p0 v) := fun v ↦ by
    have := congrArg Prod.fst (hFb (v, 0))
    rw [famMap_fst, famMap_apply, hF2] at this
    simpa [p0, p1] using this
  obtain ⟨c, hc0, hc1⟩ := brick_app hC (Kron.homMk (ModuleCat.ofHom p0) (ModuleCat.ofHom p1)
    (ModuleCat.hom_ext (LinearMap.ext fun v ↦ pa v)) (ModuleCat.hom_ext (LinearMap.ext fun v ↦ pb v)))
  have hc0' : ∀ v, (F (v, 0)).1 = c • v := hc0
  have hc1' : ∀ w, (G (w, 0)).1 = c • w := hc1
  -- the components `B j → B i`
  let sV : ∀ j i, (B j).V →ₗ[k] (B i).V := fun j i ↦
    DFinsupp.lapply i ∘ₗ LinearMap.snd k _ _ ∘ₗ F ∘ₗ LinearMap.inr k _ _ ∘ₗ
      DFinsupp.lsingle (R := k) (M := fun i ↦ ((B i).V : Type u)) j
  let sW : ∀ j i, (B j).W →ₗ[k] (B i).W := fun j i ↦
    DFinsupp.lapply i ∘ₗ LinearMap.snd k _ _ ∘ₗ G ∘ₗ LinearMap.inr k _ _ ∘ₗ
      DFinsupp.lsingle (R := k) (M := fun i ↦ ((B i).W : Type u)) j
  have sa : ∀ j i y, sW j i ((B j).a.hom y) = (B i).a.hom (sV j i y) := fun j i y ↦ by
    have := congrArg (fun x ↦ x.2 i) (hFa (0, DFinsupp.single j y))
    simp only [famMap_snd] at this
    rw [famMap_apply, hGsplit] at this
    simp only [map_zero, zero_add, Prod.snd_add, DFinsupp.add_apply, hG2, DFinsupp.zero_apply,
      DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single] at this
    exact this
  have sb : ∀ j i y, sW j i ((B j).b.hom y) = (B i).b.hom (sV j i y) := fun j i y ↦ by
    have := congrArg (fun x ↦ x.2 i) (hFb (0, DFinsupp.single j y))
    simp only [famMap_snd] at this
    rw [famMap_apply, hGsplit] at this
    simp only [map_zero, zero_add, Prod.snd_add, DFinsupp.add_apply, hG2, DFinsupp.zero_apply,
      DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single] at this
    exact this
  have hsMor : ∀ j i, Kron.homMk (X := B j) (Y := B i) (ModuleCat.ofHom (sV j i))
      (ModuleCat.ofHom (sW j i)) (ModuleCat.hom_ext (LinearMap.ext fun y ↦ sa j i y))
      (ModuleCat.hom_ext (LinearMap.ext fun y ↦ sb j i y)) = Kron.homMk (X := B j) (Y := B i)
        (ModuleCat.ofHom (sV j i)) (ModuleCat.ofHom (sW j i))
        (ModuleCat.hom_ext (LinearMap.ext fun y ↦ sa j i y))
        (ModuleCat.hom_ext (LinearMap.ext fun y ↦ sb j i y)) := fun _ _ ↦ rfl
  have hoff : ∀ j i, j ≠ i → (∀ y, sV j i y = 0) ∧ ∀ w, sW j i w = 0 := by
    intro j i hji
    have hz := hBB j i hji (Kron.homMk (ModuleCat.ofHom (sV j i)) (ModuleCat.ofHom (sW j i))
      (ModuleCat.hom_ext (LinearMap.ext fun y ↦ sa j i y))
      (ModuleCat.hom_ext (LinearMap.ext fun y ↦ sb j i y)))
    exact ⟨fun y ↦ congrArg (fun φ : B j ⟶ B i ↦ (φ.app zero).hom y) hz,
      fun w ↦ congrArg (fun φ : B j ⟶ B i ↦ (φ.app one).hom w) hz⟩
  have hdiag : ∀ j, ∃ d : k, (∀ y, sV j j y = d • y) ∧ ∀ w, sW j j w = d • w := fun j ↦
    brick_app (hB j) (Kron.homMk (ModuleCat.ofHom (sV j j)) (ModuleCat.ofHom (sW j j))
      (ModuleCat.hom_ext (LinearMap.ext fun y ↦ sa j j y))
      (ModuleCat.hom_ext (LinearMap.ext fun y ↦ sb j j y)))
  choose d hd0 hd1 using hdiag
  have hF2s : ∀ j y, (F (0, DFinsupp.single j y)).2 = DFinsupp.single j (d j • y) := by
    intro j y
    ext i
    by_cases hij : i = j
    · subst hij
      rw [DFinsupp.single_eq_same]
      exact hd0 i y
    · rw [DFinsupp.single_eq_of_ne hij]
      exact (hoff j i (Ne.symm hij)).1 y
  have hG2s : ∀ j w, (G (0, DFinsupp.single j w)).2 = DFinsupp.single j (d j • w) := by
    intro j w
    ext i
    by_cases hij : i = j
    · subst hij
      rw [DFinsupp.single_eq_same]
      exact hd1 i w
    · rw [DFinsupp.single_eq_of_ne hij]
      exact (hoff j i (Ne.symm hij)).2 w
  -- the components `B j → C`
  have hq : ∀ j, (∀ y, (F (0, DFinsupp.single j y)).1 = 0) ∧
      (∀ w, (G (0, DFinsupp.single j w)).1 = 0) ∧ d j = c := by
    intro j
    let q0 : (B j).V →ₗ[k] C.V :=
      LinearMap.fst k _ _ ∘ₗ F ∘ₗ LinearMap.inr k _ _ ∘ₗ
        DFinsupp.lsingle (R := k) (M := fun i ↦ ((B i).V : Type u)) j
    let q1 : (B j).W →ₗ[k] C.W :=
      LinearMap.fst k _ _ ∘ₗ G ∘ₗ LinearMap.inr k _ _ ∘ₗ
        DFinsupp.lsingle (R := k) (M := fun i ↦ ((B i).W : Type u)) j
    have eqa : ∀ y, (d j - c) • α j y = q1 ((B j).a.hom y) - C.a.hom (q0 y) := fun y ↦ by
      have := congrArg Prod.fst (hFa (0, DFinsupp.single j y))
      rw [famMap_fst, famMap_apply, hGsplit, hF2s] at this
      simp only [map_zero, zero_add, Prod.fst_add, DFinsupp.lsum_single,
        DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single, hc1', map_smul] at this
      change c • α j y + q1 ((B j).a.hom y) = C.a.hom (q0 y) + d j • α j y at this
      rw [sub_smul, eq_sub_iff_add_eq]
      calc d j • α j y - c • α j y + C.a.hom (q0 y) = (C.a.hom (q0 y) + d j • α j y) - c • α j y := by abel
        _ = (c • α j y + q1 ((B j).a.hom y)) - c • α j y := by rw [this]
        _ = q1 ((B j).a.hom y) := by abel
    have eqb : ∀ y, (d j - c) • β j y = q1 ((B j).b.hom y) - C.b.hom (q0 y) := fun y ↦ by
      have := congrArg Prod.fst (hFb (0, DFinsupp.single j y))
      rw [famMap_fst, famMap_apply, hGsplit, hF2s] at this
      simp only [map_zero, zero_add, Prod.fst_add, DFinsupp.lsum_single,
        DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single, hc1', map_smul] at this
      change c • β j y + q1 ((B j).b.hom y) = C.b.hom (q0 y) + d j • β j y at this
      rw [sub_smul, eq_sub_iff_add_eq]
      calc d j • β j y - c • β j y + C.b.hom (q0 y) = (C.b.hom (q0 y) + d j • β j y) - c • β j y := by abel
        _ = (c • β j y + q1 ((B j).b.hom y)) - c • β j y := by rw [this]
        _ = q1 ((B j).b.hom y) := by abel
    have hdc : d j = c := by
      by_contra hne
      apply hns j
      have hdc : d j - c ≠ 0 := sub_ne_zero.2 hne
      refine ⟨-(d j - c)⁻¹ • q0, -(d j - c)⁻¹ • q1, LinearMap.ext fun y ↦ ?_, LinearMap.ext fun y ↦ ?_⟩
      · simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
        have e : α j y = (d j - c)⁻¹ • ((d j - c) • α j y) := by
          rw [smul_smul, inv_mul_cancel₀ hdc, one_smul]
        rw [e, eqa y, smul_sub]
        simp only [neg_smul, sub_neg_eq_add]
        abel
      · simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
        have e : β j y = (d j - c)⁻¹ • ((d j - c) • β j y) := by
          rw [smul_smul, inv_mul_cancel₀ hdc, one_smul]
        rw [e, eqb y, smul_sub]
        simp only [neg_smul, sub_neg_eq_add]
        abel
    have hqa : ∀ y, C.a.hom (q0 y) = q1 ((B j).a.hom y) := fun y ↦ by
      have := eqa y; rw [hdc, sub_self, zero_smul] at this; exact (sub_eq_zero.1 this.symm).symm
    have hqb : ∀ y, C.b.hom (q0 y) = q1 ((B j).b.hom y) := fun y ↦ by
      have := eqb y; rw [hdc, sub_self, zero_smul] at this; exact (sub_eq_zero.1 this.symm).symm
    have hz := hBC j (Kron.homMk (ModuleCat.ofHom q0) (ModuleCat.ofHom q1)
      (ModuleCat.hom_ext (LinearMap.ext fun y ↦ (hqa y).symm))
      (ModuleCat.hom_ext (LinearMap.ext fun y ↦ (hqb y).symm)))
    exact ⟨fun y ↦ congrArg (fun φ : B j ⟶ C ↦ (φ.app zero).hom y) hz,
      fun w ↦ congrArg (fun φ : B j ⟶ C ↦ (φ.app one).hom w) hz, hdc⟩
  refine ⟨c, Kron.hom_ext (ModuleCat.hom_ext ?_) (ModuleCat.hom_ext ?_)⟩
  · change F = c • LinearMap.id
    refine LinearMap.prod_ext (LinearMap.ext fun v ↦ ?_) (DFinsupp.lhom_ext' fun j ↦
      LinearMap.ext fun y ↦ ?_)
    · refine Prod.ext (hc0' v) ?_
      change (F (v, 0)).2 = (c • ((v, 0) : C.V × SumV B)).2
      rw [hF2]; simp
    · refine Prod.ext ?_ ?_
      · change (F (0, DFinsupp.single j y)).1 = (c • ((0, DFinsupp.single j y) : C.V × SumV B)).1
        rw [(hq j).1 y]; simp
      · change (F (0, DFinsupp.single j y)).2 = (c • ((0, DFinsupp.single j y) : C.V × SumV B)).2
        rw [hF2s, (hq j).2.2]; simp
  · change G = c • LinearMap.id
    refine LinearMap.prod_ext (LinearMap.ext fun w ↦ ?_) (DFinsupp.lhom_ext' fun j ↦
      LinearMap.ext fun y ↦ ?_)
    · refine Prod.ext (hc1' w) ?_
      change (G (w, 0)).2 = (c • ((w, 0) : C.W × SumW B)).2
      rw [hG2]; simp
    · refine Prod.ext ?_ ?_
      · change (G (0, DFinsupp.single j y)).1 = (c • ((0, DFinsupp.single j y) : C.W × SumW B)).1
        rw [(hq j).2.1 y]; simp
      · change (G (0, DFinsupp.single j y)).2 = (c • ((0, DFinsupp.single j y) : C.W × SumW B)).2
        rw [hG2s, (hq j).2.2]; simp

end Bricks

end LargeIndecomposable
