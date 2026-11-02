module

public import LargeIndecomposable.MildContours.Setup.Setup
public import LargeIndecomposable.Cleaving.Diagrams.TreeTable
public import LargeIndecomposable.Cleaving.Diagrams.ThinDiagram
public import LargeIndecomposable.Crowns.Basic.CrownFunctor

/-!
# Diagram contradictions from `MildHyp`

`MildHyp` versions of the generic cleaving contradictions of the BO13a work
(`MulBasis.not_thin_diagram`, `MulBasis.not_ot_diagram`,
`MulBasis.not_tree_table`), which only used the representation-finiteness of
proper residues. The proofs apply with the hypothesis replaced.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable RayQuiver

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]

open Classical in
theorem MildHyp.not_pathCat_cleaving (hM : MildHyp k P)
    {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) {Q : Type} [Quiver.{0} Q] [Fintype Q] [DecidableEq Q]
    [∀ a b : Q, Finite (a ⟶ b)] [Fact (LargeIndecomposable.Foundations.Quiver.IsAcyclic Q)]
    (hD : ¬Statement.IsRepresentationFinite (Linearization (PathCat Q) k))
    (F : PathCat Q ⥤ RayCat.Res τ) [F.PreservesZeroMorphisms] (hc : PathCat.ArrowCleaving F) :
    False := by
  letI := LargeIndecomposable.rayResidueCategory_isFiniteRayCategory τ hτ
  letI : IsRayCategory (RayCat.Res τ) := isRayCategory_of_finiteRayCategory
  letI : Fintype (RayCat.Res τ) := Fintype.ofFinite _
  letI : DecidableEq (RayCat.Res τ) := Classical.decEq _
  have hfin := hM.res τ hτ hτ0
  refine hD (isRepresentationFinite_of_cleaving (B := linMulBasis k (RayCat.Res τ)) (F := F)
    (PathCat.isCleaving_of_arrows hc (leftCancel_quotient _ hM.left) (rightCancel_quotient _ hM.right))
    (fun _ _ _ ↦ rfl) hfin)

open Classical in
theorem MildHyp.not_thin_diagram (hM : MildHyp k P)
    {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) {V : Type} [Fintype V] [DecidableEq V] {T : ThinData V}
    (hD : ¬Statement.IsRepresentationFinite (Linearization (ThinCat T) k)) (Ar : ThinArrows T)
    (obj : V → P) (mor : ∀ x y, T.le x y → (obj x ⟶ obj y))
    (mor_id : ∀ x, mor x x (T.refl x) = 𝟙 _)
    (mor_comp : ∀ x y z (h : T.le x y) (h' : T.le y z),
      mor x y h ≫ mor y z h' = if hn : T.nz x y z then mor x z (T.nz_le x y z h h' hn) else 0)
    (h0 : ∀ x y h, ¬FactorsThroughMorphism τ (mor x y h))
    (hleft : ∀ x z y (ha : Ar.ar x z) (hy : T.le x y),
      (∃ g, mor x z (Ar.ar_le x z ha) ≫ g = mor x y hy) → T.le z y ∧ T.nz x z y)
    (hright : ∀ x z y (ha : Ar.ar z y) (hx : T.le x y),
      (∃ g, g ≫ mor z y (Ar.ar_le z y ha) = mor x y hx) → T.le x z ∧ T.nz x z y) : False := by
  letI := rayResidueCategory_isFiniteRayCategory τ hτ
  letI : IsRayCategory (RayCat.Res τ) := isRayCategory_of_finiteRayCategory
  let D : ThinFunctorData T (RayCat.Res τ) :=
    { obj := fun x ↦ (resF τ).obj (obj x)
      mor := fun x y h ↦ (resF τ).map (mor x y h)
      mor_id := fun x ↦ by rw [mor_id]; exact (resF τ).map_id _
      mor_comp := fun x y z h h' ↦ by
        rw [← Functor.map_comp, mor_comp]
        split_ifs <;> simp }
  refine hM.not_thin_cleaving τ hτ hτ0 hD D Ar ⟨?_, ?_, ?_⟩
  · intro x y h hz
    exact h0 x y h ((rayResidueFunctor_map_eq_zero_iff τ _).1 hz)
  · rintro x z y ha hy ⟨g, hg⟩
    refine hleft x z y ha hy ⟨lift τ g, (resF_map_injective τ (h0 _ _ _) ?_).symm⟩
    rw [Functor.map_comp, resF_lift]
    exact hg.symm
  · rintro x z y ha hx ⟨g, hg⟩
    refine hright x z y ha hx ⟨lift τ g, (resF_map_injective τ (h0 _ _ _) ?_).symm⟩
    rw [Functor.map_comp, resF_lift]
    exact hg.symm

open Classical in
theorem MildHyp.not_ot_diagram (hM : MildHyp k P)
    {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (o : V → V → Prop) (ho : ∀ a b, o a b → G.Adj a b) (hasym : ∀ a b, o a b → ¬o b a)
    (hG : G.IsAcyclic) [Fact (LargeIndecomposable.Foundations.Quiver.IsAcyclic (OT G o))]
    (hD : ¬Statement.IsRepresentationFinite (Linearization (PathCat (OT G o)) k))
    (φ : OT G o ⥤q P)
    (h0 : ∀ {x y : OT G o} (p : Quiver.Path x y), 0 < p.length →
      ¬FactorsThroughMorphism τ (pval φ p))
    (hiso : ∀ {x y : OT G o} (e : x ⟶ y), ¬IsIso (φ.map e))
    (hl : ∀ {x c c' y : OT G o} (e : x ⟶ c) (e' : x ⟶ c') (q : Quiver.Path c' y), c ≠ c' →
      ¬∃ g, φ.map e ≫ g = pval φ (e'.toPath.comp q))
    (hr : ∀ {x c c' y : OT G o} (e : c ⟶ y) (e' : c' ⟶ y) (q : Quiver.Path x c'), c ≠ c' →
      ¬∃ g, g ≫ φ.map e = pval φ (q.cons e')) :
    False := by
  letI := rayResidueCategory_isFiniteRayCategory τ hτ
  letI : IsRayCategory (RayCat.Res τ) := isRayCategory_of_finiteRayCategory
  let F := PathCat.lift (φ ⋙q (resF τ).toPrefunctor)
  have hFp : ∀ {x y : OT G o} (p : Quiver.Path x y),
      F.map (PathCat.ofPath p) = (resF τ).map (pval φ p) := fun p ↦ by
    rw [PathCat.lift_map_ofPath, composePath_comp_functor]
  have h0' : ∀ {x y : OT G o} (p : Quiver.Path x y), ¬FactorsThroughMorphism τ (pval φ p) := by
    intro x y p
    cases p with
    | nil => exact not_factorsThrough_id hτ _
    | cons p e => exact h0 _ (by simp)
  have hval : ∀ {x y : OT G o} (e : x ⟶ y), pval φ e.toPath = φ.map e := fun e ↦
    Category.id_comp _
  refine hM.not_pathCat_cleaving τ hτ hτ0 hD F
    (OT.arrowCleaving ho hasym hG (fun p ↦ ?_) (fun e ↦ ?_) (fun e e' q h ↦ ?_)
      (fun e e' q h ↦ ?_))
  · rw [hFp]
    exact fun h ↦ h0' p ((rayResidueFunctor_map_eq_zero_iff τ _).1 h)
  · rw [hFp, hval]
    intro hi
    obtain ⟨c, hc1, -⟩ := hi.out
    let c' : (resF τ).obj (φ.obj _) ⟶ (resF τ).obj (φ.obj _) := c
    have h1 : 𝟙 _ = φ.map e ≫ lift τ c' := by
      refine resF_map_injective τ (not_factorsThrough_id hτ _) ?_
      rw [Functor.map_comp, resF_lift, CategoryTheory.Functor.map_id]
      exact hc1.symm
    have hne : φ.map e ≠ 0 := fun h ↦ h0' e.toPath (by rw [hval, h]; exact ⟨0, 0, by simp⟩)
    exact hiso e (isIso_of_isIso_comp _ _ hne (by rw [← h1]; infer_instance))
  · rw [hFp, hFp, hval]
    rintro ⟨g, hg⟩
    let g' : (resF τ).obj (φ.obj _) ⟶ (resF τ).obj (φ.obj _) := g
    have hg' : (resF τ).map (φ.map e) ≫ (resF τ).map (lift τ g') =
        (resF τ).map (pval φ (e'.toPath.comp q)) := by rw [resF_lift]; exact hg
    refine hl e e' q h ⟨lift τ g', (resF_map_injective τ (h0' _) ?_).symm⟩
    rw [Functor.map_comp, hg']
  · rw [hFp, hFp, hval]
    rintro ⟨g, hg⟩
    let g' : (resF τ).obj (φ.obj _) ⟶ (resF τ).obj (φ.obj _) := g
    have hg' : (resF τ).map (lift τ g') ≫ (resF τ).map (φ.map e) =
        (resF τ).map (pval φ (q.cons e')) := by rw [resF_lift]; exact hg
    refine hr e e' q h ⟨lift τ g', (resF_map_injective τ (h0' _) ?_).symm⟩
    rw [Functor.map_comp, hg']

open Classical in
theorem MildHyp.not_tree_table (hM : MildHyp k P)
    {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (o : V → V → Prop) (ho : ∀ a b, o a b → G.Adj a b) (hasym : ∀ a b, o a b → ¬o b a)
    (hG : G.IsAcyclic) [Fact (LargeIndecomposable.Foundations.Quiver.IsAcyclic (OT G o))]
    (hD : ¬Statement.IsRepresentationFinite (Linearization (PathCat (OT G o)) k))
    (obj : V → P) (arr : ∀ a b, o a b → (obj a ⟶ obj b)) (M : ∀ a b : V, Option (obj a ⟶ obj b))
    (hid : ∀ a, M a a = some (𝟙 _))
    (hstep : ∀ a b c (h : o b c) f, M a b = some f → M a c = some (f ≫ arr b c h))
    (h0 : ∀ x y f, M x y = some f → x ≠ y → ¬FactorsThroughMorphism τ f)
    (hiso : ∀ x y (h : o x y), ¬IsIso (arr x y h))
    (hl : ∀ x c c' y (h : o x c) (h' : o x c') f, c ≠ c' → M c' y = some f →
      ¬∃ g, arr x c h ≫ g = arr x c' h' ≫ f)
    (hr : ∀ x c c' y (h : o c y) (h' : o c' y) f, c ≠ c' → M x c' = some f →
      ¬∃ g, g ≫ arr c y h = f ≫ arr c' y h') : False := by
  have hne : ∀ u w : OT G o, u ≠ w → u.as ≠ w.as := fun u w h h' ↦ h (by
    cases u; cases w; simp_all)
  refine hM.not_ot_diagram τ hτ hτ0 G o ho hasym hG hD (OT.diag obj arr) ?_ ?_ ?_ ?_
  · intro x y p hp
    refine h0 _ _ _ (OT.pval_eq_of_table obj arr M hid hstep p) fun hxy ↦ ?_
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    change x = y at hxy
    subst hxy
    have := OT.path_eq ho hasym hG p .nil
    subst this
    simp at hp
  · intro x y e
    exact hiso _ _ _
  · intro x c c' y e e' q hcc
    have := hl x.as c.as c'.as y.as (OT.hom_down e) (OT.hom_down e') _ (hne _ _ hcc)
      (OT.pval_eq_of_table obj arr M hid hstep q)
    rintro ⟨g, hg⟩
    refine this ⟨g, ?_⟩
    change (OT.diag obj arr).map e ≫ g = _
    rw [hg]
    simp [pval, Prefunctor.mapPath_comp, composePath_comp]
    rfl
  · intro x c c' y e e' q hcc
    exact hr x.as c.as c'.as y.as (OT.hom_down e) (OT.hom_down e') _ (hne _ _ hcc)
      (OT.pval_eq_of_table obj arr M hid hstep q)

/-- **No closed chain (crown) in a proper residue**, conditions in `P`. -/
theorem MildHyp.not_closedChain (hM : MildHyp k P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) {m : ℕ} (x z : Fin (m + 1) → P) (ρ : ∀ i, x i ⟶ z i)
    (σ : ∀ i, x (i + 1) ⟶ z i) (h0ρ : ∀ i, ¬FactorsThroughMorphism τ (ρ i))
    (h0σ : ∀ i, ¬FactorsThroughMorphism τ (σ i))
    (peak₁ : ∀ i, ¬∃ c, c ≫ σ i = ρ i) (peak₂ : ∀ i, ¬∃ c, c ≫ ρ i = σ i)
    (valley₁ : ∀ i, ¬∃ c, σ i ≫ c = ρ (i + 1)) (valley₂ : ∀ i, ¬∃ c, ρ (i + 1) ≫ c = σ i) :
    False := by
  letI := rayResidueCategory_isFiniteRayCategory τ hτ
  letI : IsRayCategory (RayCat.Res τ) := isRayCategory_of_finiteRayCategory
  letI : Fintype (RayCat.Res τ) := Fintype.ofFinite _
  letI : DecidableEq (RayCat.Res τ) := Classical.decEq _
  let C : ClosedChain (RayCat.Res τ) m :=
    { x := fun i ↦ (resF τ).obj (x i)
      z := fun i ↦ (resF τ).obj (z i)
      ρ := fun i ↦ (resF τ).map (ρ i)
      σ := fun i ↦ (resF τ).map (σ i)
      ρ_ne := fun i h ↦ h0ρ i ((rayResidueFunctor_map_eq_zero_iff τ _).1 h)
      σ_ne := fun i h ↦ h0σ i ((rayResidueFunctor_map_eq_zero_iff τ _).1 h)
      peak₁ := fun i ⟨c, hc⟩ ↦ peak₁ i ⟨lift τ c, (resF_map_injective τ (h0ρ i)
        (by rw [Functor.map_comp, resF_lift]; exact hc.symm)).symm⟩
      peak₂ := fun i ⟨c, hc⟩ ↦ peak₂ i ⟨lift τ c, (resF_map_injective τ (h0σ i)
        (by rw [Functor.map_comp, resF_lift]; exact hc.symm)).symm⟩
      valley₁ := fun i ⟨c, hc⟩ ↦ valley₁ i ⟨lift τ c, (resF_map_injective τ (h0ρ (i + 1))
        (by rw [Functor.map_comp, resF_lift]; exact hc.symm)).symm⟩
      valley₂ := fun i ⟨c, hc⟩ ↦ valley₂ i ⟨lift τ c, (resF_map_injective τ (h0σ i)
        (by rw [Functor.map_comp, resF_lift]; exact hc.symm)).symm⟩ }
  exact C.not_isRepresentationFinite (linMulBasis k (RayCat.Res τ)) (hM.res τ hτ hτ0)

/-- **No crown `x₀ → z₀ ← x₁ → z₁ ← x₀` in a proper residue.** -/
theorem MildHyp.not_crown2 (hM : MildHyp k P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) {x₀ x₁ z₀ z₁ : P} (ρ₀ : x₀ ⟶ z₀) (σ₀ : x₁ ⟶ z₀) (ρ₁ : x₁ ⟶ z₁)
    (σ₁ : x₀ ⟶ z₁)
    (h₁ : ¬FactorsThroughMorphism τ ρ₀) (h₂ : ¬FactorsThroughMorphism τ σ₀)
    (h₃ : ¬FactorsThroughMorphism τ ρ₁) (h₄ : ¬FactorsThroughMorphism τ σ₁)
    (p₁ : ¬∃ c, c ≫ σ₀ = ρ₀) (p₂ : ¬∃ c, c ≫ ρ₀ = σ₀)
    (p₃ : ¬∃ c, c ≫ σ₁ = ρ₁) (p₄ : ¬∃ c, c ≫ ρ₁ = σ₁)
    (v₁ : ¬∃ c, σ₀ ≫ c = ρ₁) (v₂ : ¬∃ c, ρ₁ ≫ c = σ₀)
    (v₃ : ¬∃ c, σ₁ ≫ c = ρ₀) (v₄ : ¬∃ c, ρ₀ ≫ c = σ₁) : False := by
  let xs : Fin 2 → P := ![x₀, x₁]
  let zs : Fin 2 → P := ![z₀, z₁]
  let ρs : ∀ i, xs i ⟶ zs i := fun i ↦ match i with
    | 0 => ρ₀
    | 1 => ρ₁
  let σs : ∀ i, xs (i + 1) ⟶ zs i := fun i ↦ match i with
    | 0 => σ₀
    | 1 => σ₁
  refine hM.not_closedChain τ hτ hτ0 (m := 1) xs zs ρs σs ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (intro i; fin_cases i) <;> assumption

/-- **No crown of length six in a proper residue.** -/
theorem MildHyp.not_crown3 (hM : MildHyp k P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) {x₀ x₁ x₂ z₀ z₁ z₂ : P} (ρ₀ : x₀ ⟶ z₀) (σ₀ : x₁ ⟶ z₀) (ρ₁ : x₁ ⟶ z₁)
    (σ₁ : x₂ ⟶ z₁) (ρ₂ : x₂ ⟶ z₂) (σ₂ : x₀ ⟶ z₂)
    (h₁ : ¬FactorsThroughMorphism τ ρ₀) (h₂ : ¬FactorsThroughMorphism τ σ₀)
    (h₃ : ¬FactorsThroughMorphism τ ρ₁) (h₄ : ¬FactorsThroughMorphism τ σ₁)
    (h₅ : ¬FactorsThroughMorphism τ ρ₂) (h₆ : ¬FactorsThroughMorphism τ σ₂)
    (p₁ : ¬∃ c, c ≫ σ₀ = ρ₀) (p₂ : ¬∃ c, c ≫ ρ₀ = σ₀)
    (p₃ : ¬∃ c, c ≫ σ₁ = ρ₁) (p₄ : ¬∃ c, c ≫ ρ₁ = σ₁)
    (p₅ : ¬∃ c, c ≫ σ₂ = ρ₂) (p₆ : ¬∃ c, c ≫ ρ₂ = σ₂)
    (v₁ : ¬∃ c, σ₀ ≫ c = ρ₁) (v₂ : ¬∃ c, ρ₁ ≫ c = σ₀)
    (v₃ : ¬∃ c, σ₁ ≫ c = ρ₂) (v₄ : ¬∃ c, ρ₂ ≫ c = σ₁)
    (v₅ : ¬∃ c, σ₂ ≫ c = ρ₀) (v₆ : ¬∃ c, ρ₀ ≫ c = σ₂) : False := by
  let xs : Fin 3 → P := ![x₀, x₁, x₂]
  let zs : Fin 3 → P := ![z₀, z₁, z₂]
  let ρs : ∀ i, xs i ⟶ zs i := fun i ↦ match i with
    | 0 => ρ₀
    | 1 => ρ₁
    | 2 => ρ₂
  let σs : ∀ i, xs (i + 1) ⟶ zs i := fun i ↦ match i with
    | 0 => σ₀
    | 1 => σ₁
    | 2 => σ₂
  refine hM.not_closedChain τ hτ hτ0 (m := 2) xs zs ρs σs ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (intro i; fin_cases i) <;> assumption

end RayCat

end LargeIndecomposable
