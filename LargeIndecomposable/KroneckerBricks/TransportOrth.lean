module

public import LargeIndecomposable.KroneckerBricks.Regular

/-!
# Orthogonality and non-split classes for transports

Morphisms into or out of a glued module vanish when they vanish on the pieces
(`Bricks.hom_extFamily_eq_zero`, `Bricks.hom_to_extFamily_eq_zero`). Hence a
Kronecker module orthogonal to all pieces of an anchored family is orthogonal
to every transport along it. A non-split class with quotient the anchor `C`
extends to a non-split class with quotient any transport, through the copy of
`C` inside the transport (`Bricks.Anchored.exists_not_splits_transport`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair TensorProduct

universe u

variable {k : Type u} [Field k]

namespace Kron

/-- A morphism of Kronecker modules from two commuting linear maps. -/
abbrev homMkL {X Y : Kron k} (φ : X.V →ₗ[k] Y.V) (ψ : X.W →ₗ[k] Y.W)
    (ha : ∀ v, ψ (X.a.hom v) = Y.a.hom (φ v)) (hb : ∀ v, ψ (X.b.hom v) = Y.b.hom (φ v)) :
    X ⟶ Y :=
  homMk (ModuleCat.ofHom φ) (ModuleCat.ofHom ψ)
    (ModuleCat.hom_ext (LinearMap.ext fun v ↦ ha v))
    (ModuleCat.hom_ext (LinearMap.ext fun v ↦ hb v))

end Kron

namespace Bricks

section Family

variable {ι : Type u} [DecidableEq ι] {C : Kron k} {B : ι → Kron k}
  {α β : ∀ i, (B i).V →ₗ[k] C.W}

/-- Morphisms out of a glued module vanish if they vanish on the pieces. -/
theorem hom_extFamily_eq_zero {Y : Kron k} (hC : ∀ f : C ⟶ Y, f = 0)
    (hB : ∀ i (f : B i ⟶ Y), f = 0) (f : extFamily C B α β ⟶ Y) : f = 0 := by
  set F : (C.V × SumV B) →ₗ[k] Y.V := (f.app zero).hom
  set Gm : (C.W × SumW B) →ₗ[k] Y.W := (f.app one).hom
  have hFa : ∀ x, Gm (famMap C B C.a.hom (fun i ↦ (B i).a.hom) α x) = Y.a.hom (F x) :=
    fun x ↦ Kron.a_apply f x
  have hFb : ∀ x, Gm (famMap C B C.b.hom (fun i ↦ (B i).b.hom) β x) = Y.b.hom (F x) :=
    fun x ↦ Kron.b_apply f x
  -- the anchor part
  have hfC := hC (Kron.homMkL (F ∘ₗ LinearMap.inl k _ _) (Gm ∘ₗ LinearMap.inl k _ _)
    (fun v ↦ by
      have := hFa (v, 0)
      rw [famMap_apply] at this
      simpa using this)
    (fun v ↦ by
      have := hFb (v, 0)
      rw [famMap_apply] at this
      simpa using this))
  have hCV : ∀ v, F (v, 0) = 0 := fun v ↦
    congrArg (fun g : C ⟶ Y ↦ (g.app zero).hom v) hfC
  have hCW : ∀ w, Gm (w, 0) = 0 := fun w ↦
    congrArg (fun g : C ⟶ Y ↦ (g.app one).hom w) hfC
  -- the pieces
  have hBi : ∀ i, F ∘ₗ LinearMap.inr k _ _ ∘ₗ
      DFinsupp.lsingle (R := k) (M := fun i ↦ (B i).V) i = 0 ∧
      Gm ∘ₗ LinearMap.inr k _ _ ∘ₗ DFinsupp.lsingle (R := k) (M := fun i ↦ (B i).W) i = 0 := by
    intro i
    have hf := hB i (Kron.homMkL
      (F ∘ₗ LinearMap.inr k _ _ ∘ₗ DFinsupp.lsingle (R := k) (M := fun i ↦ (B i).V) i)
      (Gm ∘ₗ LinearMap.inr k _ _ ∘ₗ DFinsupp.lsingle (R := k) (M := fun i ↦ (B i).W) i)
      (fun v ↦ by
        change Gm (0, DFinsupp.single i ((B i).a.hom v)) = Y.a.hom (F (0, DFinsupp.single i v))
        have := hFa (0, DFinsupp.single i v)
        rw [famMap_apply] at this
        rw [← this]
        have e : ((C.a.hom 0 + DFinsupp.lsum k α (DFinsupp.single i v),
            DFinsupp.mapRange.linearMap (fun i ↦ (B i).a.hom) (DFinsupp.single i v)) :
            C.W × SumW B) = (α i v, 0) + (0, DFinsupp.single i ((B i).a.hom v)) := by
          ext <;> simp [DFinsupp.mapRange_single]
        rw [e, map_add, hCW, zero_add])
      (fun v ↦ by
        change Gm (0, DFinsupp.single i ((B i).b.hom v)) = Y.b.hom (F (0, DFinsupp.single i v))
        have := hFb (0, DFinsupp.single i v)
        rw [famMap_apply] at this
        rw [← this]
        have e : ((C.b.hom 0 + DFinsupp.lsum k β (DFinsupp.single i v),
            DFinsupp.mapRange.linearMap (fun i ↦ (B i).b.hom) (DFinsupp.single i v)) :
            C.W × SumW B) = (β i v, 0) + (0, DFinsupp.single i ((B i).b.hom v)) := by
          ext <;> simp [DFinsupp.mapRange_single]
        rw [e, map_add, hCW, zero_add]))
    exact ⟨LinearMap.ext fun v ↦ congrArg (fun g : B i ⟶ Y ↦ (g.app zero).hom v) hf,
      LinearMap.ext fun v ↦ congrArg (fun g : B i ⟶ Y ↦ (g.app one).hom v) hf⟩
  have hV : F ∘ₗ LinearMap.inr k _ _ = 0 := DFinsupp.lhom_ext' fun i ↦ (hBi i).1
  have hW : Gm ∘ₗ LinearMap.inr k _ _ = 0 := DFinsupp.lhom_ext' fun i ↦ (hBi i).2
  refine Kron.hom_ext ?_ ?_
  · ext ⟨v, x⟩
    change F (v, x) = 0
    rw [show ((v, x) : C.V × SumV B) = (v, 0) + (0, x) by simp, map_add, hCV, zero_add]
    exact LinearMap.congr_fun hV x
  · ext ⟨v, x⟩
    change Gm (v, x) = 0
    rw [show ((v, x) : C.W × SumW B) = (v, 0) + (0, x) by simp, map_add, hCW, zero_add]
    exact LinearMap.congr_fun hW x

/-- Morphisms into a glued module vanish if they vanish into the pieces. -/
theorem hom_to_extFamily_eq_zero {Y : Kron k} (hC : ∀ f : Y ⟶ C, f = 0)
    (hB : ∀ i (f : Y ⟶ B i), f = 0) (f : Y ⟶ extFamily C B α β) : f = 0 := by
  set F : Y.V →ₗ[k] (C.V × SumV B) := (f.app zero).hom
  set Gm : Y.W →ₗ[k] (C.W × SumW B) := (f.app one).hom
  have hFa : ∀ x, Gm (Y.a.hom x) = famMap C B C.a.hom (fun i ↦ (B i).a.hom) α (F x) :=
    fun x ↦ Kron.a_apply f x
  have hFb : ∀ x, Gm (Y.b.hom x) = famMap C B C.b.hom (fun i ↦ (B i).b.hom) β (F x) :=
    fun x ↦ Kron.b_apply f x
  have hpi : ∀ i, (DFinsupp.lapply i ∘ₗ LinearMap.snd k _ _ ∘ₗ F = 0) ∧
      (DFinsupp.lapply i ∘ₗ LinearMap.snd k _ _ ∘ₗ Gm = 0) := by
    intro i
    have hf := hB i (Kron.homMkL (DFinsupp.lapply i ∘ₗ LinearMap.snd k _ _ ∘ₗ F)
      (DFinsupp.lapply i ∘ₗ LinearMap.snd k _ _ ∘ₗ Gm)
      (fun v ↦ by
        change (Gm (Y.a.hom v)).2 i = _
        rw [hFa, famMap_snd]
        rfl)
      (fun v ↦ by
        change (Gm (Y.b.hom v)).2 i = _
        rw [hFb, famMap_snd]
        rfl))
    exact ⟨LinearMap.ext fun v ↦ congrArg (fun g : Y ⟶ B i ↦ (g.app zero).hom v) hf,
      LinearMap.ext fun v ↦ congrArg (fun g : Y ⟶ B i ↦ (g.app one).hom v) hf⟩
  have hF2 : ∀ v, (F v).2 = 0 := fun v ↦ DFinsupp.ext fun i ↦
    LinearMap.congr_fun (hpi i).1 v
  have hG2 : ∀ w, (Gm w).2 = 0 := fun w ↦ DFinsupp.ext fun i ↦
    LinearMap.congr_fun (hpi i).2 w
  have hf := hC (Kron.homMkL (LinearMap.fst k _ _ ∘ₗ F) (LinearMap.fst k _ _ ∘ₗ Gm)
    (fun v ↦ by
      change (Gm (Y.a.hom v)).1 = _
      rw [hFa, famMap_fst, hF2, map_zero, add_zero]
      rfl)
    (fun v ↦ by
      change (Gm (Y.b.hom v)).1 = _
      rw [hFb, famMap_fst, hF2, map_zero, add_zero]
      rfl))
  refine Kron.hom_ext ?_ ?_
  · ext v
    change F v = 0
    exact Prod.ext (congrArg (fun g : Y ⟶ C ↦ (g.app zero).hom v) hf) (hF2 v)
  · ext w
    change Gm w = 0
    exact Prod.ext (congrArg (fun g : Y ⟶ C ↦ (g.app one).hom w) hf) (hG2 w)

/-- The anchor inside a glued module. -/
def inclC : C ⟶ extFamily C B α β :=
  Kron.homMkL (LinearMap.inl k _ _) (LinearMap.inl k _ _)
    (fun v ↦ by
      change ((C.a.hom v, 0) : C.W × SumW B) = famMap C B C.a.hom (fun i ↦ (B i).a.hom) α (v, 0)
      rw [famMap_apply]
      simp)
    (fun v ↦ by
      change ((C.b.hom v, 0) : C.W × SumW B) = famMap C B C.b.hom (fun i ↦ (B i).b.hom) β (v, 0)
      rw [famMap_apply]
      simp)

end Family

/-- A splitting restricts along a morphism into the quotient. -/
lemma Splits.restrict {Z X Y : Kron k} {α β : X.V →ₗ[k] Z.W} (h : Splits Z X α β) (j : Y ⟶ X) :
    Splits Z Y (α ∘ₗ (j.app zero).hom) (β ∘ₗ (j.app zero).hom) := by
  obtain ⟨φ, ψ, hα, hβ⟩ := h
  refine ⟨φ ∘ₗ (j.app zero).hom, ψ ∘ₗ (j.app one).hom, ?_, ?_⟩
  · rw [hα]
    ext v
    simp only [LinearMap.sub_apply, LinearMap.comp_apply]
    rw [Kron.a_apply]
  · rw [hβ]
    ext v
    simp only [LinearMap.sub_apply, LinearMap.comp_apply]
    rw [Kron.b_apply]

/-- Coordinates of a morphism into `N ⊗ Y` vanish when `Hom(X, Y) = 0`. -/
lemma coeff_zero {X Y : Kron k} {N : Type u} [AddCommGroup N] [Module k N]
    (hz : ∀ f : X ⟶ Y, f = 0) (φ : X.V →ₗ[k] N ⊗[k] Y.V) (ψ : X.W →ₗ[k] N ⊗[k] Y.W)
    (ha : (Y.a.hom).lTensor N ∘ₗ φ = ψ ∘ₗ X.a.hom) (hb : (Y.b.hom).lTensor N ∘ₗ φ = ψ ∘ₗ X.b.hom) :
    φ = 0 ∧ ψ = 0 := by
  classical
  let ℬ := Module.Free.chooseBasis k N
  have hm : ∀ i, coordL ℬ i _ ∘ₗ φ = 0 ∧ coordL ℬ i _ ∘ₗ ψ = 0 := by
    intro i
    have hf := hz (Kron.homMkL (coordL ℬ i _ ∘ₗ φ) (coordL ℬ i _ ∘ₗ ψ)
      (fun v ↦ by
        change (coordL ℬ i _ ∘ₗ ψ ∘ₗ X.a.hom) v = (Y.a.hom ∘ₗ coordL ℬ i _ ∘ₗ φ) v
        rw [← ha, ← LinearMap.comp_assoc, coordL_lTensor, LinearMap.comp_assoc])
      (fun v ↦ by
        change (coordL ℬ i _ ∘ₗ ψ ∘ₗ X.b.hom) v = (Y.b.hom ∘ₗ coordL ℬ i _ ∘ₗ φ) v
        rw [← hb, ← LinearMap.comp_assoc, coordL_lTensor, LinearMap.comp_assoc]))
    exact ⟨LinearMap.ext fun v ↦ congrArg (fun g : X ⟶ Y ↦ (g.app zero).hom v) hf,
      LinearMap.ext fun v ↦ congrArg (fun g : X ⟶ Y ↦ (g.app one).hom v) hf⟩
  refine ⟨LinearMap.ext fun v ↦ ?_, LinearMap.ext fun v ↦ ?_⟩
  · apply (TensorProduct.equivFinsuppOfBasisLeft ℬ).injective
    ext i
    rw [← coordL_apply, LinearMap.zero_apply, map_zero, Finsupp.zero_apply]
    exact LinearMap.congr_fun (hm i).1 v
  · apply (TensorProduct.equivFinsuppOfBasisLeft ℬ).injective
    ext i
    rw [← coordL_apply, LinearMap.zero_apply, map_zero, Finsupp.zero_apply]
    exact LinearMap.congr_fun (hm i).2 v

lemma tmul_right_inj' {G M : Type u} [AddCommGroup G] [Module k G] [AddCommGroup M] [Module k M]
    {g : G} (hg : g ≠ 0) {y y' : M} (h : g ⊗ₜ[k] y = g ⊗ₜ[k] y') : y = y' := by
  obtain ⟨lam, hl⟩ := Module.Projective.exists_dual_eq_one k hg
  have := congrArg (fun t ↦ (TensorProduct.lid k M) (TensorProduct.map lam LinearMap.id t)) h
  simpa [hl] using this

namespace Anchored

variable {J : Type u} [DecidableEq J] (σ : Anchored k J)
variable {G : Type u} [AddCommGroup G] [Module k G] (Gs : J → Submodule k G)

/-- The generator morphism `F_{{j}} → H`, `x ↦ g ⊗ x`. -/
def genMor {j : J} {g : G} (hg : g ∈ Gs j) : σ.F {j} ⟶ σ.transport Gs :=
  Kron.homMkL (σ.genV Gs hg) (σ.genW Gs hg) (fun v ↦ (σ.aH_genV Gs hg v).symm)
    (fun v ↦ (σ.bH_genV Gs hg v).symm)

/-- Transports are orthogonal to modules orthogonal to every `F_{{j}}` (outgoing). -/
theorem hom_transport_to_eq_zero {Z : Kron k} (hz : ∀ j (f : σ.F {j} ⟶ Z), f = 0)
    (f : σ.transport Gs ⟶ Z) : f = 0 := by
  set F : σ.tV Gs →ₗ[k] Z.V := (f.app zero).hom
  set Gm : σ.tW Gs →ₗ[k] Z.W := (f.app one).hom
  have h := fun j g (hg : g ∈ Gs j) ↦ hz j (σ.genMor Gs hg ≫ f)
  refine Kron.hom_ext ?_ ?_
  · ext ⟨v, hv⟩
    change F ⟨v, hv⟩ = 0
    induction hv using σ.tV_induction Gs with
    | gen n g hg x =>
      exact congrArg (fun φ : σ.F {n} ⟶ Z ↦ (φ.app zero).hom x) (h n g hg)
    | zero => exact map_zero F
    | add v w hv hw ihv ihw =>
      have : (⟨v + w, (σ.tV Gs).add_mem hv hw⟩ : σ.tV Gs) = ⟨v, hv⟩ + ⟨w, hw⟩ := rfl
      rw [this, map_add, ihv, ihw, add_zero]
  · ext ⟨v, hv⟩
    change Gm ⟨v, hv⟩ = 0
    induction hv using σ.tW_induction Gs with
    | gen n g hg x =>
      exact congrArg (fun φ : σ.F {n} ⟶ Z ↦ (φ.app one).hom x) (h n g hg)
    | zero => exact map_zero Gm
    | add v w hv hw ihv ihw =>
      have : (⟨v + w, (σ.tW Gs).add_mem hv hw⟩ : σ.tW Gs) = ⟨v, hv⟩ + ⟨w, hw⟩ := rfl
      rw [this, map_add, ihv, ihw, add_zero]

/-- Transports are orthogonal to modules orthogonal to `F_J` (incoming). -/
theorem hom_to_transport_eq_zero {Z : Kron k} (hz : ∀ f : Z ⟶ σ.F Set.univ, f = 0)
    (f : Z ⟶ σ.transport Gs) : f = 0 := by
  set F : Z.V →ₗ[k] σ.tV Gs := (f.app zero).hom
  set Gm : Z.W →ₗ[k] σ.tW Gs := (f.app one).hom
  obtain ⟨h1, h2⟩ := coeff_zero (N := G) hz ((σ.tV Gs).subtype ∘ₗ F) ((σ.tW Gs).subtype ∘ₗ Gm)
    (LinearMap.ext fun v ↦ (congrArg Subtype.val (Kron.a_apply f v)).symm)
    (LinearMap.ext fun v ↦ (congrArg Subtype.val (Kron.b_apply f v)).symm)
  refine Kron.hom_ext ?_ ?_
  · ext v
    exact Subtype.ext (LinearMap.congr_fun h1 v)
  · ext v
    exact Subtype.ext (LinearMap.congr_fun h2 v)

/-- A non-split class onto the anchor extends to one onto the transport. -/
theorem exists_not_splits_transport {Z : Kron k} {α0 β0 : σ.C.V →ₗ[k] Z.W}
    (hns : ¬Splits Z σ.C α0 β0) {j0 : J} {g0 : G} (hg0 : g0 ∈ Gs j0) (hne : g0 ≠ 0) :
    ∃ α β : (σ.transport Gs).V →ₗ[k] Z.W, ¬Splits Z (σ.transport Gs) α β := by
  let ι0 : σ.C ⟶ σ.transport Gs := inclC ≫ σ.genMor Gs hg0
  have hinj : Function.Injective (ι0.app zero).hom := by
    intro c c' h
    have := congrArg Subtype.val h
    change g0 ⊗ₜ σ.iV j0 (c, 0) = g0 ⊗ₜ σ.iV j0 (c', 0) at this
    exact congrArg Prod.fst (tmul_right_inj' hne this)
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (ι0.app zero).hom
    (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨α0 ∘ₗ p, β0 ∘ₗ p, fun hs ↦ hns ?_⟩
  have := hs.restrict ι0
  rwa [LinearMap.comp_assoc, LinearMap.comp_assoc, hp, LinearMap.comp_id, LinearMap.comp_id]
    at this

end Anchored

/-- Reindex an anchored family along an injection. -/
def Anchored.comap {J J' : Type u} (σ : Anchored k J) (e : J' ↪ J) : Anchored k J' where
  C := σ.C
  B j := σ.B (e j)
  α j := σ.α (e j)
  β j := σ.β (e j)
  hC := σ.hC
  hB j := σ.hB (e j)
  hCB j := σ.hCB (e j)
  hBC j := σ.hBC (e j)
  hBB i j h := σ.hBB (e i) (e j) (e.injective.ne h)
  hns j := σ.hns (e j)
  c0 := σ.c0
  hc0 := σ.hc0
  y j := σ.y (e j)
  hy j := σ.hy (e j)

end Bricks

end LargeIndecomposable
