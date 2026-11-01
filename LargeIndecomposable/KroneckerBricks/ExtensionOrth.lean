module

public import LargeIndecomposable.KroneckerBricks.ExtensionFamily

/-!
# Orthogonality of glued bricks

For a pairwise Hom-orthogonal family of bricks `C`, `B i` with non-split
extension classes `(α i, β i)` and subsets `S, S'` of the index set, the glued
modules `E_S` and `E_{S'}` (`Bricks.subExt`) satisfy `Hom(E_S, E_{S'}) = 0`
when `S ⊄ S'` (`Bricks.hom_subExt_eq_zero`): a component `B_j`, `j ∈ S \ S'`,
forces the scalar on `C` to vanish.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair

universe u

variable {k : Type u} [Field k]

namespace Bricks

variable {ι : Type u} [DecidableEq ι] (C : Kron k) (B : ι → Kron k) (α β : ∀ i, (B i).V →ₗ[k] C.W)

/-- The module glued from the members of `S`. -/
def subExt (S : Set ι) : Kron k :=
  extFamily C (fun i : S ↦ B i) (fun i ↦ α i) (fun i ↦ β i)

variable {C B α β}

/-- Glued modules over `S ⊄ S'` are orthogonal: `Hom(E_S, E_{S'}) = 0`. -/
theorem hom_subExt_eq_zero (hC : IsBrickKron C) (hB : ∀ i, IsBrickKron (B i))
    (hCB : ∀ i (f : C ⟶ B i), f = 0) (hBC : ∀ i (f : B i ⟶ C), f = 0)
    (hBB : ∀ i j, i ≠ j → ∀ f : B i ⟶ B j, f = 0) (hns : ∀ i, ¬Splits C (B i) (α i) (β i))
    {S S' : Set ι} {j : ι} (hjS : j ∈ S) (hjS' : j ∉ S')
    (f : subExt C B α β S ⟶ subExt C B α β S') : f = 0 := by
  set F : (C.V × SumV (fun i : S ↦ B i)) →ₗ[k] (C.V × SumV (fun i : S' ↦ B i)) := (f.app zero).hom
  set G : (C.W × SumW (fun i : S ↦ B i)) →ₗ[k] (C.W × SumW (fun i : S' ↦ B i)) := (f.app one).hom
  have hFa : ∀ x, G (famMap C _ C.a.hom (fun i : S ↦ (B i).a.hom) (fun i ↦ α i) x) =
      famMap C _ C.a.hom (fun i : S' ↦ (B i).a.hom) (fun i ↦ α i) (F x) := fun x ↦ Kron.a_apply f x
  have hFb : ∀ x, G (famMap C _ C.b.hom (fun i : S ↦ (B i).b.hom) (fun i ↦ β i) x) =
      famMap C _ C.b.hom (fun i : S' ↦ (B i).b.hom) (fun i ↦ β i) (F x) := fun x ↦ Kron.b_apply f x
  have hGsplit : ∀ (w : C.W) (y : SumW (fun i : S ↦ B i)), G (w, y) = G (w, 0) + G (0, y) :=
    fun w y ↦ by rw [← map_add]; simp
  -- the components `C → B i` vanish
  have hCBi : ∀ i : S', (∀ v, (F (v, 0)).2 i = 0) ∧ ∀ w, (G (w, 0)).2 i = 0 := by
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
  -- the components `B s → B s'`
  let sV : ∀ (s : S) (s' : S'), (B s).V →ₗ[k] (B s').V := fun s s' ↦
    DFinsupp.lapply s' ∘ₗ LinearMap.snd k _ _ ∘ₗ F ∘ₗ LinearMap.inr k _ _ ∘ₗ
      DFinsupp.lsingle (R := k) (M := fun i : S ↦ ((B i).V : Type u)) s
  let sW : ∀ (s : S) (s' : S'), (B s).W →ₗ[k] (B s').W := fun s s' ↦
    DFinsupp.lapply s' ∘ₗ LinearMap.snd k _ _ ∘ₗ G ∘ₗ LinearMap.inr k _ _ ∘ₗ
      DFinsupp.lsingle (R := k) (M := fun i : S ↦ ((B i).W : Type u)) s
  have sa : ∀ s s' y, sW s s' ((B s).a.hom y) = (B s').a.hom (sV s s' y) := fun s s' y ↦ by
    have := congrArg (fun x ↦ x.2 s') (hFa (0, DFinsupp.single s y))
    simp only [famMap_snd] at this
    rw [famMap_apply, hGsplit] at this
    simp only [map_zero, zero_add, Prod.snd_add, DFinsupp.add_apply, hG2, DFinsupp.zero_apply,
      DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single] at this
    exact this
  have sb : ∀ s s' y, sW s s' ((B s).b.hom y) = (B s').b.hom (sV s s' y) := fun s s' y ↦ by
    have := congrArg (fun x ↦ x.2 s') (hFb (0, DFinsupp.single s y))
    simp only [famMap_snd] at this
    rw [famMap_apply, hGsplit] at this
    simp only [map_zero, zero_add, Prod.snd_add, DFinsupp.add_apply, hG2, DFinsupp.zero_apply,
      DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single] at this
    exact this
  have hoff : ∀ (s : S) (s' : S'), (s : ι) ≠ s' → (∀ y, sV s s' y = 0) ∧ ∀ w, sW s s' w = 0 := by
    intro s s' hne
    have hz := hBB s s' hne (Kron.homMk (ModuleCat.ofHom (sV s s')) (ModuleCat.ofHom (sW s s'))
      (ModuleCat.hom_ext (LinearMap.ext fun y ↦ sa s s' y))
      (ModuleCat.hom_ext (LinearMap.ext fun y ↦ sb s s' y)))
    exact ⟨fun y ↦ congrArg (fun φ : B s ⟶ B s' ↦ (φ.app zero).hom y) hz,
      fun w ↦ congrArg (fun φ : B s ⟶ B s' ↦ (φ.app one).hom w) hz⟩
  classical
  have hdiag : ∀ s : S, ∃ e : k,
      (∀ y, (F (0, DFinsupp.single s y)).2 =
        if h : (s : ι) ∈ S' then DFinsupp.single ⟨s, h⟩ (e • y) else 0) ∧
      (∀ w, (G (0, DFinsupp.single s w)).2 =
        if h : (s : ι) ∈ S' then DFinsupp.single ⟨s, h⟩ (e • w) else 0) ∧
      ((s : ι) ∉ S' → e = 0) := by
    intro s
    by_cases h : (s : ι) ∈ S'
    · obtain ⟨d, hd0, hd1⟩ := brick_app (hB s) (Kron.homMk (ModuleCat.ofHom (sV s ⟨s, h⟩))
        (ModuleCat.ofHom (sW s ⟨s, h⟩)) (ModuleCat.hom_ext (LinearMap.ext fun y ↦ sa s ⟨s, h⟩ y))
        (ModuleCat.hom_ext (LinearMap.ext fun y ↦ sb s ⟨s, h⟩ y)))
      refine ⟨d, fun y ↦ ?_, fun w ↦ ?_, fun h' ↦ absurd h h'⟩
      · rw [dif_pos h]
        ext s''
        by_cases hs : s'' = ⟨s, h⟩
        · subst hs; rw [DFinsupp.single_eq_same]; exact hd0 y
        · rw [DFinsupp.single_eq_of_ne hs]
          exact (hoff s s'' fun e ↦ hs (Subtype.ext e.symm)).1 y
      · rw [dif_pos h]
        ext s''
        by_cases hs : s'' = ⟨s, h⟩
        · subst hs; rw [DFinsupp.single_eq_same]; exact hd1 w
        · rw [DFinsupp.single_eq_of_ne hs]
          exact (hoff s s'' fun e ↦ hs (Subtype.ext e.symm)).2 w
    · refine ⟨0, fun y ↦ ?_, fun w ↦ ?_, fun _ ↦ rfl⟩
      · rw [dif_neg h]
        ext s''
        exact (hoff s s'' fun e ↦ h (e ▸ s''.2)).1 y
      · rw [dif_neg h]
        ext s''
        exact (hoff s s'' fun e ↦ h (e ▸ s''.2)).2 w
  choose e he0 he1 he2 using hdiag
  -- the value of `lsum` on these components
  have hlsα : ∀ (s : S) y, DFinsupp.lsum k (fun i : S' ↦ α i) (F (0, DFinsupp.single s y)).2 =
      e s • α s y := by
    intro s y
    rw [he0]
    split_ifs with h
    · rw [DFinsupp.lsum_single, map_smul]
    · rw [map_zero, he2 s h, zero_smul]
  have hlsβ : ∀ (s : S) y, DFinsupp.lsum k (fun i : S' ↦ β i) (F (0, DFinsupp.single s y)).2 =
      e s • β s y := by
    intro s y
    rw [he0]
    split_ifs with h
    · rw [DFinsupp.lsum_single, map_smul]
    · rw [map_zero, he2 s h, zero_smul]
  -- the components `B s → C`
  have hq : ∀ s : S, (∀ y, (F (0, DFinsupp.single s y)).1 = 0) ∧
      (∀ w, (G (0, DFinsupp.single s w)).1 = 0) ∧ e s = c := by
    intro s
    let q0 : (B s).V →ₗ[k] C.V :=
      LinearMap.fst k _ _ ∘ₗ F ∘ₗ LinearMap.inr k _ _ ∘ₗ
        DFinsupp.lsingle (R := k) (M := fun i : S ↦ ((B i).V : Type u)) s
    let q1 : (B s).W →ₗ[k] C.W :=
      LinearMap.fst k _ _ ∘ₗ G ∘ₗ LinearMap.inr k _ _ ∘ₗ
        DFinsupp.lsingle (R := k) (M := fun i : S ↦ ((B i).W : Type u)) s
    have eqa : ∀ y, (e s - c) • α s y = q1 ((B s).a.hom y) - C.a.hom (q0 y) := fun y ↦ by
      have := congrArg Prod.fst (hFa (0, DFinsupp.single s y))
      rw [famMap_fst, famMap_apply, hGsplit, hlsα] at this
      simp only [map_zero, zero_add, Prod.fst_add, DFinsupp.lsum_single,
        DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single, hc1'] at this
      change c • α s y + q1 ((B s).a.hom y) = C.a.hom (q0 y) + e s • α s y at this
      rw [sub_smul, eq_sub_iff_add_eq]
      calc e s • α s y - c • α s y + C.a.hom (q0 y) = (C.a.hom (q0 y) + e s • α s y) - c • α s y := by abel
        _ = (c • α s y + q1 ((B s).a.hom y)) - c • α s y := by rw [this]
        _ = q1 ((B s).a.hom y) := by abel
    have eqb : ∀ y, (e s - c) • β s y = q1 ((B s).b.hom y) - C.b.hom (q0 y) := fun y ↦ by
      have := congrArg Prod.fst (hFb (0, DFinsupp.single s y))
      rw [famMap_fst, famMap_apply, hGsplit, hlsβ] at this
      simp only [map_zero, zero_add, Prod.fst_add, DFinsupp.lsum_single,
        DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single, hc1'] at this
      change c • β s y + q1 ((B s).b.hom y) = C.b.hom (q0 y) + e s • β s y at this
      rw [sub_smul, eq_sub_iff_add_eq]
      calc e s • β s y - c • β s y + C.b.hom (q0 y) = (C.b.hom (q0 y) + e s • β s y) - c • β s y := by abel
        _ = (c • β s y + q1 ((B s).b.hom y)) - c • β s y := by rw [this]
        _ = q1 ((B s).b.hom y) := by abel
    have hec : e s = c := by
      by_contra hne
      apply hns s
      have hdc : e s - c ≠ 0 := sub_ne_zero.2 hne
      refine ⟨-(e s - c)⁻¹ • q0, -(e s - c)⁻¹ • q1, LinearMap.ext fun y ↦ ?_, LinearMap.ext fun y ↦ ?_⟩
      · simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
        have e' : α s y = (e s - c)⁻¹ • ((e s - c) • α s y) := by
          rw [smul_smul, inv_mul_cancel₀ hdc, one_smul]
        rw [e', eqa y, smul_sub]
        simp only [neg_smul, sub_neg_eq_add]
        abel
      · simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
        have e' : β s y = (e s - c)⁻¹ • ((e s - c) • β s y) := by
          rw [smul_smul, inv_mul_cancel₀ hdc, one_smul]
        rw [e', eqb y, smul_sub]
        simp only [neg_smul, sub_neg_eq_add]
        abel
    have hqa : ∀ y, C.a.hom (q0 y) = q1 ((B s).a.hom y) := fun y ↦ by
      have := eqa y; rw [hec, sub_self, zero_smul] at this; exact (sub_eq_zero.1 this.symm).symm
    have hqb : ∀ y, C.b.hom (q0 y) = q1 ((B s).b.hom y) := fun y ↦ by
      have := eqb y; rw [hec, sub_self, zero_smul] at this; exact (sub_eq_zero.1 this.symm).symm
    have hz := hBC s (Kron.homMk (ModuleCat.ofHom q0) (ModuleCat.ofHom q1)
      (ModuleCat.hom_ext (LinearMap.ext fun y ↦ (hqa y).symm))
      (ModuleCat.hom_ext (LinearMap.ext fun y ↦ (hqb y).symm)))
    exact ⟨fun y ↦ congrArg (fun φ : B s ⟶ C ↦ (φ.app zero).hom y) hz,
      fun w ↦ congrArg (fun φ : B s ⟶ C ↦ (φ.app one).hom w) hz, hec⟩
  -- `c = 0` from the member `j ∉ S'`
  have hc : c = 0 := ((hq ⟨j, hjS⟩).2.2).symm.trans (he2 ⟨j, hjS⟩ hjS')
  have he : ∀ s, e s = 0 := fun s ↦ ((hq s).2.2).trans hc
  refine Kron.hom_ext (ModuleCat.hom_ext ?_) (ModuleCat.hom_ext ?_)
  · change F = 0
    refine LinearMap.prod_ext (LinearMap.ext fun v ↦ ?_) (DFinsupp.lhom_ext' fun s ↦
      LinearMap.ext fun y ↦ ?_)
    · exact Prod.ext ((hc0' v).trans (by rw [hc, zero_smul]; rfl)) (hF2 v)
    · refine Prod.ext ((hq s).1 y) ?_
      change (F (0, DFinsupp.single s y)).2 = 0
      rw [he0, he s, zero_smul]
      split_ifs <;> simp
  · change G = 0
    refine LinearMap.prod_ext (LinearMap.ext fun w ↦ ?_) (DFinsupp.lhom_ext' fun s ↦
      LinearMap.ext fun y ↦ ?_)
    · exact Prod.ext ((hc1' w).trans (by rw [hc, zero_smul]; rfl)) (hG2 w)
    · refine Prod.ext ((hq s).2.1 y) ?_
      change (G (0, DFinsupp.single s y)).2 = 0
      rw [he1, he s, zero_smul]
      split_ifs <;> simp

variable (C B α β) in
/-- The lift of a class `(α₀, β₀) : V_C → W_{B j}` to a class from `E_S` to `E_{S'}`
(`j ∈ S'`): `(v, x) ↦ (0, single j (α₀ v))`. -/
def liftClass (S S' : Set ι) {j : ι} (hj : j ∈ S') (γ : C.V →ₗ[k] (B j).W) :
    (subExt C B α β S).V →ₗ[k] (subExt C B α β S').W :=
  LinearMap.inr k _ _ ∘ₗ DFinsupp.lsingle (R := k) (M := fun i : S' ↦ ((B i).W : Type u)) ⟨j, hj⟩ ∘ₗ
    γ ∘ₗ LinearMap.fst k _ _

/-- Lifted classes of non-split classes do not split. -/
theorem not_splits_lift {S S' : Set ι} {j : ι} (hj : j ∈ S') {α₀ β₀ : C.V →ₗ[k] (B j).W}
    (hns : ¬Splits (B j) C α₀ β₀) :
    ¬Splits (subExt C B α β S') (subExt C B α β S) (liftClass C B α β S S' hj α₀)
      (liftClass C B α β S S' hj β₀) := by
  rintro ⟨φ₀, ψ₀, hα, hβ⟩
  let φ : (C.V × SumV (fun i : S ↦ B i)) →ₗ[k] (C.V × SumV (fun i : S' ↦ B i)) := φ₀
  let ψ : (C.W × SumW (fun i : S ↦ B i)) →ₗ[k] (C.W × SumW (fun i : S' ↦ B i)) := ψ₀
  have ha : ∀ x, liftClass C B α β S S' hj α₀ x =
      famMap C _ C.a.hom (fun i : S' ↦ (B i).a.hom) (fun i ↦ α i) (φ x) -
        ψ (famMap C _ C.a.hom (fun i : S ↦ (B i).a.hom) (fun i ↦ α i) x) :=
    fun x ↦ LinearMap.congr_fun hα x
  have hb : ∀ x, liftClass C B α β S S' hj β₀ x =
      famMap C _ C.b.hom (fun i : S' ↦ (B i).b.hom) (fun i ↦ β i) (φ x) -
        ψ (famMap C _ C.b.hom (fun i : S ↦ (B i).b.hom) (fun i ↦ β i) x) :=
    fun x ↦ LinearMap.congr_fun hβ x
  apply hns
  refine ⟨DFinsupp.lapply (⟨j, hj⟩ : S') ∘ₗ LinearMap.snd k _ _ ∘ₗ φ ∘ₗ LinearMap.inl k _ _,
    DFinsupp.lapply (⟨j, hj⟩ : S') ∘ₗ LinearMap.snd k _ _ ∘ₗ ψ ∘ₗ LinearMap.inl k _ _,
    LinearMap.ext fun v ↦ ?_, LinearMap.ext fun v ↦ ?_⟩
  · have := congrArg (fun x ↦ x.2 ⟨j, hj⟩) (ha (v, 0))
    simp only [liftClass, LinearMap.comp_apply, LinearMap.inr_apply, DFinsupp.lsingle_apply,
      DFinsupp.single_eq_same, LinearMap.fst_apply, Prod.snd_sub, DFinsupp.sub_apply,
      famMap_snd, famMap_apply, map_zero, add_zero] at this
    exact (DFinsupp.single_eq_same (β := fun i : S' ↦ ((B i).W : Type u))).symm.trans this
  · have := congrArg (fun x ↦ x.2 ⟨j, hj⟩) (hb (v, 0))
    simp only [liftClass, LinearMap.comp_apply, LinearMap.inr_apply, DFinsupp.lsingle_apply,
      DFinsupp.single_eq_same, LinearMap.fst_apply, Prod.snd_sub, DFinsupp.sub_apply,
      famMap_snd, famMap_apply, map_zero, add_zero] at this
    exact (DFinsupp.single_eq_same (β := fun i : S' ↦ ((B i).W : Type u))).symm.trans this

section Inclusion

variable (C B α β)

/-- Extension of index sets for `V`. -/
def extendV {S S' : Set ι} (h : S ⊆ S') :
    SumV (fun i : S ↦ B i) →ₗ[k] SumV (fun i : S' ↦ B i) :=
  DFinsupp.lsum k fun s : S ↦ DFinsupp.lsingle (R := k) (M := fun i : S' ↦ ((B i).V : Type u))
    ⟨s, h s.2⟩

/-- Extension of index sets for `W`. -/
def extendW {S S' : Set ι} (h : S ⊆ S') :
    SumW (fun i : S ↦ B i) →ₗ[k] SumW (fun i : S' ↦ B i) :=
  DFinsupp.lsum k fun s : S ↦ DFinsupp.lsingle (R := k) (M := fun i : S' ↦ ((B i).W : Type u))
    ⟨s, h s.2⟩

lemma extendV_single {S S' : Set ι} (h : S ⊆ S') (s : S) (y : (B s).V) :
    extendV B h (DFinsupp.single s y) = DFinsupp.single ⟨s, h s.2⟩ y := by
  simp [extendV]

lemma extendW_single {S S' : Set ι} (h : S ⊆ S') (s : S) (y : (B s).W) :
    extendW B h (DFinsupp.single s y) = DFinsupp.single ⟨s, h s.2⟩ y := by
  simp [extendW]

lemma lsum_extendV {S S' : Set ι} (h : S ⊆ S') (γ : ∀ i, (B i).V →ₗ[k] C.W) :
    DFinsupp.lsum k (fun i : S' ↦ γ i) ∘ₗ extendV B h = DFinsupp.lsum k (fun i : S ↦ γ i) :=
  DFinsupp.lhom_ext' fun s ↦ LinearMap.ext fun y ↦ by
    simp [extendV_single]

lemma mapRange_extendV {S S' : Set ι} (h : S ⊆ S') (g : ∀ i, (B i).V →ₗ[k] (B i).W) :
    sumMapK (fun i : S' ↦ B i) (fun i ↦ g i) ∘ₗ extendV B h =
      extendW B h ∘ₗ sumMapK (fun i : S ↦ B i) (fun i ↦ g i) :=
  DFinsupp.lhom_ext' fun s ↦ LinearMap.ext fun y ↦ by
    simp [extendV_single, extendW_single, sumMapK, DFinsupp.mapRange.linearMap_apply,
      DFinsupp.mapRange_single]

/-- The underlying map of the inclusion on `V`. -/
def inclV {S S' : Set ι} (h : S ⊆ S') :
    (C.V × SumV (fun i : S ↦ B i)) →ₗ[k] (C.V × SumV (fun i : S' ↦ B i)) :=
  (LinearMap.fst k _ _).prod (extendV B h ∘ₗ LinearMap.snd k _ _)

/-- The underlying map of the inclusion on `W`. -/
def inclW {S S' : Set ι} (h : S ⊆ S') :
    (C.W × SumW (fun i : S ↦ B i)) →ₗ[k] (C.W × SumW (fun i : S' ↦ B i)) :=
  (LinearMap.fst k _ _).prod (extendW B h ∘ₗ LinearMap.snd k _ _)

lemma incl_comm {S S' : Set ι} (h : S ⊆ S') (aC : C.V →ₗ[k] C.W) (g : ∀ i, (B i).V →ₗ[k] (B i).W)
    (γ : ∀ i, (B i).V →ₗ[k] C.W) (x : C.V × SumV (fun i : S ↦ B i)) :
    inclW C B h (famMap C _ aC (fun i : S ↦ g i) (fun i ↦ γ i) x) =
      famMap C _ aC (fun i : S' ↦ g i) (fun i ↦ γ i) (inclV C B h x) := by
  obtain ⟨v, y⟩ := x
  simp only [inclW, inclV, LinearMap.prod_apply, LinearMap.fst_apply, LinearMap.comp_apply,
    LinearMap.snd_apply, famMap_apply, Pi.prod]
  refine Prod.ext ?_ ?_
  · change aC v + DFinsupp.lsum k (fun i : S ↦ γ i) y =
      aC v + DFinsupp.lsum k (fun i : S' ↦ γ i) (extendV B h y)
    rw [← LinearMap.comp_apply (DFinsupp.lsum k (fun i : S' ↦ γ i)), lsum_extendV]
  · change extendW B h (sumMapK (fun i : S ↦ B i) (fun i ↦ g i) y) =
      sumMapK (fun i : S' ↦ B i) (fun i ↦ g i) (extendV B h y)
    rw [← LinearMap.comp_apply (sumMapK _ _), mapRange_extendV]
    rfl

/-- The inclusion `E_S ⟶ E_{S'}` for `S ⊆ S'`. -/
def subIncl {S S' : Set ι} (h : S ⊆ S') : subExt C B α β S ⟶ subExt C B α β S' :=
  Kron.homMk (ModuleCat.ofHom (inclV C B h)) (ModuleCat.ofHom (inclW C B h))
    (ModuleCat.hom_ext (LinearMap.ext fun x ↦
      incl_comm C B h C.a.hom (fun i ↦ (B i).a.hom) α x))
    (ModuleCat.hom_ext (LinearMap.ext fun x ↦
      incl_comm C B h C.b.hom (fun i ↦ (B i).b.hom) β x))

end Inclusion

/-- For `S ⊆ S'`, every map `E_S → E_{S'}` is a scalar multiple of the inclusion. -/
theorem hom_subExt_of_subset (hC : IsBrickKron C) (hB : ∀ i, IsBrickKron (B i))
    (hCB : ∀ i (f : C ⟶ B i), f = 0) (hBC : ∀ i (f : B i ⟶ C), f = 0)
    (hBB : ∀ i j, i ≠ j → ∀ f : B i ⟶ B j, f = 0) (hns : ∀ i, ¬Splits C (B i) (α i) (β i))
    {S S' : Set ι} (hSS' : S ⊆ S')
    (f : subExt C B α β S ⟶ subExt C B α β S') : ∃ c : k, f = c • subIncl C B α β hSS' := by
  set F : (C.V × SumV (fun i : S ↦ B i)) →ₗ[k] (C.V × SumV (fun i : S' ↦ B i)) := (f.app zero).hom
  set G : (C.W × SumW (fun i : S ↦ B i)) →ₗ[k] (C.W × SumW (fun i : S' ↦ B i)) := (f.app one).hom
  have hFa : ∀ x, G (famMap C _ C.a.hom (fun i : S ↦ (B i).a.hom) (fun i ↦ α i) x) =
      famMap C _ C.a.hom (fun i : S' ↦ (B i).a.hom) (fun i ↦ α i) (F x) := fun x ↦ Kron.a_apply f x
  have hFb : ∀ x, G (famMap C _ C.b.hom (fun i : S ↦ (B i).b.hom) (fun i ↦ β i) x) =
      famMap C _ C.b.hom (fun i : S' ↦ (B i).b.hom) (fun i ↦ β i) (F x) := fun x ↦ Kron.b_apply f x
  have hGsplit : ∀ (w : C.W) (y : SumW (fun i : S ↦ B i)), G (w, y) = G (w, 0) + G (0, y) :=
    fun w y ↦ by rw [← map_add]; simp
  -- the components `C → B i` vanish
  have hCBi : ∀ i : S', (∀ v, (F (v, 0)).2 i = 0) ∧ ∀ w, (G (w, 0)).2 i = 0 := by
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
  -- the components `B s → B s'`
  let sV : ∀ (s : S) (s' : S'), (B s).V →ₗ[k] (B s').V := fun s s' ↦
    DFinsupp.lapply s' ∘ₗ LinearMap.snd k _ _ ∘ₗ F ∘ₗ LinearMap.inr k _ _ ∘ₗ
      DFinsupp.lsingle (R := k) (M := fun i : S ↦ ((B i).V : Type u)) s
  let sW : ∀ (s : S) (s' : S'), (B s).W →ₗ[k] (B s').W := fun s s' ↦
    DFinsupp.lapply s' ∘ₗ LinearMap.snd k _ _ ∘ₗ G ∘ₗ LinearMap.inr k _ _ ∘ₗ
      DFinsupp.lsingle (R := k) (M := fun i : S ↦ ((B i).W : Type u)) s
  have sa : ∀ s s' y, sW s s' ((B s).a.hom y) = (B s').a.hom (sV s s' y) := fun s s' y ↦ by
    have := congrArg (fun x ↦ x.2 s') (hFa (0, DFinsupp.single s y))
    simp only [famMap_snd] at this
    rw [famMap_apply, hGsplit] at this
    simp only [map_zero, zero_add, Prod.snd_add, DFinsupp.add_apply, hG2, DFinsupp.zero_apply,
      DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single] at this
    exact this
  have sb : ∀ s s' y, sW s s' ((B s).b.hom y) = (B s').b.hom (sV s s' y) := fun s s' y ↦ by
    have := congrArg (fun x ↦ x.2 s') (hFb (0, DFinsupp.single s y))
    simp only [famMap_snd] at this
    rw [famMap_apply, hGsplit] at this
    simp only [map_zero, zero_add, Prod.snd_add, DFinsupp.add_apply, hG2, DFinsupp.zero_apply,
      DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single] at this
    exact this
  have hoff : ∀ (s : S) (s' : S'), (s : ι) ≠ s' → (∀ y, sV s s' y = 0) ∧ ∀ w, sW s s' w = 0 := by
    intro s s' hne
    have hz := hBB s s' hne (Kron.homMk (ModuleCat.ofHom (sV s s')) (ModuleCat.ofHom (sW s s'))
      (ModuleCat.hom_ext (LinearMap.ext fun y ↦ sa s s' y))
      (ModuleCat.hom_ext (LinearMap.ext fun y ↦ sb s s' y)))
    exact ⟨fun y ↦ congrArg (fun φ : B s ⟶ B s' ↦ (φ.app zero).hom y) hz,
      fun w ↦ congrArg (fun φ : B s ⟶ B s' ↦ (φ.app one).hom w) hz⟩
  classical
  have hdiag : ∀ s : S, ∃ e : k,
      (∀ y, (F (0, DFinsupp.single s y)).2 =
        if h : (s : ι) ∈ S' then DFinsupp.single ⟨s, h⟩ (e • y) else 0) ∧
      (∀ w, (G (0, DFinsupp.single s w)).2 =
        if h : (s : ι) ∈ S' then DFinsupp.single ⟨s, h⟩ (e • w) else 0) ∧
      ((s : ι) ∉ S' → e = 0) := by
    intro s
    by_cases h : (s : ι) ∈ S'
    · obtain ⟨d, hd0, hd1⟩ := brick_app (hB s) (Kron.homMk (ModuleCat.ofHom (sV s ⟨s, h⟩))
        (ModuleCat.ofHom (sW s ⟨s, h⟩)) (ModuleCat.hom_ext (LinearMap.ext fun y ↦ sa s ⟨s, h⟩ y))
        (ModuleCat.hom_ext (LinearMap.ext fun y ↦ sb s ⟨s, h⟩ y)))
      refine ⟨d, fun y ↦ ?_, fun w ↦ ?_, fun h' ↦ absurd h h'⟩
      · rw [dif_pos h]
        ext s''
        by_cases hs : s'' = ⟨s, h⟩
        · subst hs; rw [DFinsupp.single_eq_same]; exact hd0 y
        · rw [DFinsupp.single_eq_of_ne hs]
          exact (hoff s s'' fun e ↦ hs (Subtype.ext e.symm)).1 y
      · rw [dif_pos h]
        ext s''
        by_cases hs : s'' = ⟨s, h⟩
        · subst hs; rw [DFinsupp.single_eq_same]; exact hd1 w
        · rw [DFinsupp.single_eq_of_ne hs]
          exact (hoff s s'' fun e ↦ hs (Subtype.ext e.symm)).2 w
    · refine ⟨0, fun y ↦ ?_, fun w ↦ ?_, fun _ ↦ rfl⟩
      · rw [dif_neg h]
        ext s''
        exact (hoff s s'' fun e ↦ h (e ▸ s''.2)).1 y
      · rw [dif_neg h]
        ext s''
        exact (hoff s s'' fun e ↦ h (e ▸ s''.2)).2 w
  choose e he0 he1 he2 using hdiag
  -- the value of `lsum` on these components
  have hlsα : ∀ (s : S) y, DFinsupp.lsum k (fun i : S' ↦ α i) (F (0, DFinsupp.single s y)).2 =
      e s • α s y := by
    intro s y
    rw [he0]
    split_ifs with h
    · rw [DFinsupp.lsum_single, map_smul]
    · rw [map_zero, he2 s h, zero_smul]
  have hlsβ : ∀ (s : S) y, DFinsupp.lsum k (fun i : S' ↦ β i) (F (0, DFinsupp.single s y)).2 =
      e s • β s y := by
    intro s y
    rw [he0]
    split_ifs with h
    · rw [DFinsupp.lsum_single, map_smul]
    · rw [map_zero, he2 s h, zero_smul]
  -- the components `B s → C`
  have hq : ∀ s : S, (∀ y, (F (0, DFinsupp.single s y)).1 = 0) ∧
      (∀ w, (G (0, DFinsupp.single s w)).1 = 0) ∧ e s = c := by
    intro s
    let q0 : (B s).V →ₗ[k] C.V :=
      LinearMap.fst k _ _ ∘ₗ F ∘ₗ LinearMap.inr k _ _ ∘ₗ
        DFinsupp.lsingle (R := k) (M := fun i : S ↦ ((B i).V : Type u)) s
    let q1 : (B s).W →ₗ[k] C.W :=
      LinearMap.fst k _ _ ∘ₗ G ∘ₗ LinearMap.inr k _ _ ∘ₗ
        DFinsupp.lsingle (R := k) (M := fun i : S ↦ ((B i).W : Type u)) s
    have eqa : ∀ y, (e s - c) • α s y = q1 ((B s).a.hom y) - C.a.hom (q0 y) := fun y ↦ by
      have := congrArg Prod.fst (hFa (0, DFinsupp.single s y))
      rw [famMap_fst, famMap_apply, hGsplit, hlsα] at this
      simp only [map_zero, zero_add, Prod.fst_add, DFinsupp.lsum_single,
        DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single, hc1'] at this
      change c • α s y + q1 ((B s).a.hom y) = C.a.hom (q0 y) + e s • α s y at this
      rw [sub_smul, eq_sub_iff_add_eq]
      calc e s • α s y - c • α s y + C.a.hom (q0 y) = (C.a.hom (q0 y) + e s • α s y) - c • α s y := by abel
        _ = (c • α s y + q1 ((B s).a.hom y)) - c • α s y := by rw [this]
        _ = q1 ((B s).a.hom y) := by abel
    have eqb : ∀ y, (e s - c) • β s y = q1 ((B s).b.hom y) - C.b.hom (q0 y) := fun y ↦ by
      have := congrArg Prod.fst (hFb (0, DFinsupp.single s y))
      rw [famMap_fst, famMap_apply, hGsplit, hlsβ] at this
      simp only [map_zero, zero_add, Prod.fst_add, DFinsupp.lsum_single,
        DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single, hc1'] at this
      change c • β s y + q1 ((B s).b.hom y) = C.b.hom (q0 y) + e s • β s y at this
      rw [sub_smul, eq_sub_iff_add_eq]
      calc e s • β s y - c • β s y + C.b.hom (q0 y) = (C.b.hom (q0 y) + e s • β s y) - c • β s y := by abel
        _ = (c • β s y + q1 ((B s).b.hom y)) - c • β s y := by rw [this]
        _ = q1 ((B s).b.hom y) := by abel
    have hec : e s = c := by
      by_contra hne
      apply hns s
      have hdc : e s - c ≠ 0 := sub_ne_zero.2 hne
      refine ⟨-(e s - c)⁻¹ • q0, -(e s - c)⁻¹ • q1, LinearMap.ext fun y ↦ ?_, LinearMap.ext fun y ↦ ?_⟩
      · simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
        have e' : α s y = (e s - c)⁻¹ • ((e s - c) • α s y) := by
          rw [smul_smul, inv_mul_cancel₀ hdc, one_smul]
        rw [e', eqa y, smul_sub]
        simp only [neg_smul, sub_neg_eq_add]
        abel
      · simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
        have e' : β s y = (e s - c)⁻¹ • ((e s - c) • β s y) := by
          rw [smul_smul, inv_mul_cancel₀ hdc, one_smul]
        rw [e', eqb y, smul_sub]
        simp only [neg_smul, sub_neg_eq_add]
        abel
    have hqa : ∀ y, C.a.hom (q0 y) = q1 ((B s).a.hom y) := fun y ↦ by
      have := eqa y; rw [hec, sub_self, zero_smul] at this; exact (sub_eq_zero.1 this.symm).symm
    have hqb : ∀ y, C.b.hom (q0 y) = q1 ((B s).b.hom y) := fun y ↦ by
      have := eqb y; rw [hec, sub_self, zero_smul] at this; exact (sub_eq_zero.1 this.symm).symm
    have hz := hBC s (Kron.homMk (ModuleCat.ofHom q0) (ModuleCat.ofHom q1)
      (ModuleCat.hom_ext (LinearMap.ext fun y ↦ (hqa y).symm))
      (ModuleCat.hom_ext (LinearMap.ext fun y ↦ (hqb y).symm)))
    exact ⟨fun y ↦ congrArg (fun φ : B s ⟶ C ↦ (φ.app zero).hom y) hz,
      fun w ↦ congrArg (fun φ : B s ⟶ C ↦ (φ.app one).hom w) hz, hec⟩
  refine ⟨c, Kron.hom_ext (ModuleCat.hom_ext ?_) (ModuleCat.hom_ext ?_)⟩
  · change F = c • inclV C B hSS'
    refine LinearMap.prod_ext (LinearMap.ext fun v ↦ ?_) (DFinsupp.lhom_ext' fun s ↦
      LinearMap.ext fun y ↦ ?_)
    · refine Prod.ext (hc0' v) ?_
      change (F (v, 0)).2 = (c • inclV C B hSS' (v, 0)).2
      rw [hF2]; simp [inclV]
    · refine Prod.ext ((hq s).1 y |>.trans (by simp [inclV])) ?_
      change (F (0, DFinsupp.single s y)).2 = (c • inclV C B hSS' (0, DFinsupp.single s y)).2
      rw [he0, dif_pos (hSS' s.2), (hq s).2.2]
      simp [inclV, extendV_single]
  · change G = c • inclW C B hSS'
    refine LinearMap.prod_ext (LinearMap.ext fun w ↦ ?_) (DFinsupp.lhom_ext' fun s ↦
      LinearMap.ext fun y ↦ ?_)
    · refine Prod.ext (hc1' w) ?_
      change (G (w, 0)).2 = (c • inclW C B hSS' (w, 0)).2
      rw [hG2]; simp [inclW]
    · refine Prod.ext ((hq s).2.1 y |>.trans (by simp [inclW])) ?_
      change (G (0, DFinsupp.single s y)).2 = (c • inclW C B hSS' (0, DFinsupp.single s y)).2
      rw [he1, dif_pos (hSS' s.2), (hq s).2.2]
      simp [inclW, extendW_single]



end Bricks

end LargeIndecomposable
