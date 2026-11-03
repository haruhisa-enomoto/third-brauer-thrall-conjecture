module

public import LargeIndecomposable.RepresentationEmbeddings.ColimitExtension.Lift
public import LargeIndecomposable.RepresentationEmbeddings.ColimitExtension.CSub
public import LargeIndecomposable.RepresentationEmbeddings.Control.Retraction

/-!
# Proposition 2.5: extending retractions by filtered colimits

Let `Φ : D_fin → mod A` have finite-dimensional values, and let `ρ^fin` be
retractions for `Φ` on `C_fin` (Definition 2.4). Then the colimit extension
`F` has retractions on `C`; if every composite of `n` maps in kernels of
`ρ^fin` vanishes, the same holds for the new retractions.

The retraction of `f : F(X) → F(Y)` is glued from the finite retractions of
lifts `Φ(T_{V₀}) → Φ(T_{V₁})` of `f` along the cofinal subrepresentations
`T_{V₀}` of Lemma 2.2(3) (`Kron.CompatFamily.glue`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]

namespace Extension

variable (Φ : Dfin k ⥤ ModuleCat.{u} A)

variable (R : Retractions k (Ψfin Φ))

/-- The Kronecker morphism `T_{V₀} → Y` obtained from the finite retraction of a
lift `φ : Φ(T_{V₀}) → Φ(T_{V₁})`. -/
def σ {X Y : D k} (V₀ : Kron.FinV X.obj) (V₁ : Kron.FinV Y.obj)
    (φ : (Ψfin Φ).obj (stage X V₀) ⟶ (Ψfin Φ).obj (stage Y V₁)) :
    (Kron.FinV.sub V₀).toKron ⟶ Y.obj :=
  InCfin.kh (R.ρ (stage X V₀) (stage Y V₁) φ) ≫ (Kron.FinV.sub V₁).ι

lemma σ_trans {X Y : D k} (V₀ : Kron.FinV X.obj) {V₁ V₂ : Kron.FinV Y.obj}
    (h : V₁.toFinSub ≤ V₂.toFinSub)
    (φ : (Ψfin Φ).obj (stage X V₀) ⟶ (Ψfin Φ).obj (stage Y V₁)) :
    σ Φ R V₀ V₂ (φ ≫ trans Φ Y h) = σ Φ R V₀ V₁ φ := by
  have : φ ≫ trans Φ Y h = φ ≫ (Ψfin Φ).map (stageMap Y h) := rfl
  rw [σ, σ, this, R.map_comp, R.ρ_map]
  calc (InCfin.kh (R.ρ (stage X V₀) (stage Y V₁) φ) ≫ InCfin.kh (stageMap Y h)) ≫
        (Kron.FinV.sub V₂).ι
      = InCfin.kh (R.ρ (stage X V₀) (stage Y V₁) φ) ≫
          (Kron.Sub.homOfLE h ≫ (Kron.FinV.sub V₂).ι) := Category.assoc _ _ _
    _ = _ := congrArg (InCfin.kh (R.ρ (stage X V₀) (stage Y V₁) φ) ≫ ·) (Kron.Sub.homOfLE_ι h)

lemma σ_trans_left {X Y : D k} {V₀ V₀' : Kron.FinV X.obj} (h : V₀'.toFinSub ≤ V₀.toFinSub)
    (V₁ : Kron.FinV Y.obj)
    (φ : (Ψfin Φ).obj (stage X V₀) ⟶ (Ψfin Φ).obj (stage Y V₁)) :
    σ Φ R V₀' V₁ (trans Φ X h ≫ φ) = Kron.Sub.homOfLE h ≫ σ Φ R V₀ V₁ φ := by
  have : trans Φ X h ≫ φ = (Ψfin Φ).map (stageMap X h) ≫ φ := rfl
  rw [σ, σ, this, R.map_comp, R.ρ_map]
  exact Category.assoc _ _ _

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable [FiniteDimensional k A] (hfin : ∀ X : Dfin k, Module.Finite k (RestrictScalars k A (Φ.obj X)))

include hfin in
/-- A homomorphism `F(X) → F(Y)` with `Y ∈ C`, restricted to `Φ(T_{V₀})`, factors
through some `Φ(T_{V₁})` with `V₁` above a given subspace. -/
lemma exists_liftV {X Y : D k} (hY : InC Y.obj) (f : (functor Φ).obj X ⟶ (functor Φ).obj Y)
    (V₀ : Kron.FinV X.obj) (V₁₀ : Kron.FinV Y.obj) :
    ∃ (V₁ : Kron.FinV Y.obj) (_ : V₁₀.toFinSub ≤ V₁.toFinSub)
      (φ : (Ψfin Φ).obj (stage X V₀) ⟶ (Ψfin Φ).obj (stage Y V₁)),
      φ ≫ ιF Φ Y V₁.toFinSub = ιF Φ X V₀.toFinSub ≫ f := by
  have : Module.Finite k ((Ψfin Φ).obj (stage X V₀)) := hfin ((finDiagram X).obj V₀.toFinSub)
  have : Module.Finite k (Φ.obj ((finDiagram X).obj V₀.toFinSub)) :=
    hfin ((finDiagram X).obj V₀.toFinSub)
  obtain ⟨U, hU, φ, hφ⟩ := exists_lift Φ Y (ιF Φ X V₀.toFinSub ≫ f) V₁₀.toFinSub
  obtain ⟨V₁, hV₁⟩ := Kron.FinV.exists_le hY U
  refine ⟨V₁, hU.trans hV₁, φ ≫ trans Φ Y hV₁, ?_⟩
  rw [Category.assoc, trans_ιF, hφ]

omit [FiniteDimensional k A] in
include hfin in
/-- `σ` does not depend on the lift. -/
lemma σ_eq {X Y : D k} (hY : InC Y.obj) (V₀ : Kron.FinV X.obj) {V₁ V₂ : Kron.FinV Y.obj}
    (φ : (Ψfin Φ).obj (stage X V₀) ⟶ (Ψfin Φ).obj (stage Y V₁))
    (ψ : (Ψfin Φ).obj (stage X V₀) ⟶ (Ψfin Φ).obj (stage Y V₂))
    (h : φ ≫ ιF Φ Y V₁.toFinSub = ψ ≫ ιF Φ Y V₂.toFinSub) :
    σ Φ R V₀ V₁ φ = σ Φ R V₀ V₂ ψ := by
  have : Module.Finite k ((Ψfin Φ).obj (stage X V₀)) := hfin ((finDiagram X).obj V₀.toFinSub)
  have : Module.Finite k (Φ.obj ((finDiagram X).obj V₀.toFinSub)) :=
    hfin ((finDiagram X).obj V₀.toFinSub)
  let V₃ := Kron.FinV.sup V₁ V₂
  have h₁ : V₁.toFinSub ≤ V₃.toFinSub := Kron.FinV.toFinSub_mono (Kron.FinV.le_sup_left _ _)
  have h₂ : V₂.toFinSub ≤ V₃.toFinSub := Kron.FinV.toFinSub_mono (Kron.FinV.le_sup_right _ _)
  obtain ⟨U, hU, he⟩ := exists_trans_eq Φ Y V₃.toFinSub (φ ≫ trans Φ Y h₁) (ψ ≫ trans Φ Y h₂)
    (by rw [Category.assoc, Category.assoc, trans_ιF, trans_ιF, h])
  obtain ⟨V₄, hV₄⟩ := Kron.FinV.exists_le hY U
  have e₁ : φ ≫ trans Φ Y (h₁.trans (hU.trans hV₄)) = ψ ≫ trans Φ Y (h₂.trans (hU.trans hV₄)) := by
    rw [← trans_trans Φ Y h₁ (hU.trans hV₄), ← trans_trans Φ Y h₂ (hU.trans hV₄),
      ← trans_trans Φ Y hU hV₄]
    calc φ ≫ trans Φ Y h₁ ≫ trans Φ Y hU ≫ trans Φ Y hV₄
        = ((φ ≫ trans Φ Y h₁) ≫ trans Φ Y hU) ≫ trans Φ Y hV₄ := by simp only [Category.assoc]
      _ = ((ψ ≫ trans Φ Y h₂) ≫ trans Φ Y hU) ≫ trans Φ Y hV₄ := by rw [he]
      _ = _ := by simp only [Category.assoc]
  rw [← σ_trans Φ R V₀ (h₁.trans (hU.trans hV₄)) φ, ← σ_trans Φ R V₀ (h₂.trans (hU.trans hV₄)) ψ, e₁]

/-- The chosen lift of `f` at `V₀`. -/
def liftV {X Y : D k} (hY : InC Y.obj) (f : (functor Φ).obj X ⟶ (functor Φ).obj Y)
    (V₀ : Kron.FinV X.obj) :
    Σ V₁ : Kron.FinV Y.obj,
      (Ψfin Φ).obj (stage X V₀) ⟶ (Ψfin Φ).obj (stage Y V₁) :=
  ⟨(exists_liftV Φ hfin hY f V₀ ⟨⊥, inferInstance⟩).choose,
    (exists_liftV Φ hfin hY f V₀ ⟨⊥, inferInstance⟩).choose_spec.choose_spec.choose⟩

lemma liftV_spec {X Y : D k} (hY : InC Y.obj) (f : (functor Φ).obj X ⟶ (functor Φ).obj Y)
    (V₀ : Kron.FinV X.obj) :
    (liftV Φ hfin hY f V₀).2 ≫ ιF Φ Y (liftV Φ hfin hY f V₀).1.toFinSub =
      ιF Φ X V₀.toFinSub ≫ f :=
  (exists_liftV Φ hfin hY f V₀ ⟨⊥, inferInstance⟩).choose_spec.choose_spec.choose_spec

/-- The compatible family of Kronecker morphisms `T_{V₀} → Y` attached to `f`. -/
def family {X Y : D k} (hY : InC Y.obj) (f : (functor Φ).obj X ⟶ (functor Φ).obj Y) :
    Kron.CompatFamily X.obj Y.obj where
  s V₀ := σ Φ R V₀ _ (liftV Φ hfin hY f V₀).2
  compat {V₀ V₁} h := by
    refine (σ_trans_left Φ R (Kron.FinV.toFinSub_mono h) _ _).symm.trans
      (σ_eq Φ R hfin hY V₀ _ _ ?_)
    rw [Category.assoc, liftV_spec, liftV_spec, ← Category.assoc, trans_ιF]

lemma family_s {X Y : D k} (hY : InC Y.obj) (f : (functor Φ).obj X ⟶ (functor Φ).obj Y)
    (V₀ : Kron.FinV X.obj) (V₁ : Kron.FinV Y.obj)
    (φ : (Ψfin Φ).obj (stage X V₀) ⟶ (Ψfin Φ).obj (stage Y V₁))
    (hφ : φ ≫ ιF Φ Y V₁.toFinSub = ιF Φ X V₀.toFinSub ≫ f) :
    (family Φ R hfin hY f).s V₀ = σ Φ R V₀ V₁ φ :=
  σ_eq Φ R hfin hY V₀ _ _ (by rw [liftV_spec, hφ])

/-- The glued Kronecker morphism `ρ(f) : X → Y`. -/
def ρK {X Y : D k} (hX : InC X.obj) (hY : InC Y.obj) (f : (functor Φ).obj X ⟶ (functor Φ).obj Y) :
    X.obj ⟶ Y.obj :=
  (family Φ R hfin hY f).glue hX

lemma ι_ρK {X Y : D k} (hX : InC X.obj) (hY : InC Y.obj)
    (f : (functor Φ).obj X ⟶ (functor Φ).obj Y) (V₀ : Kron.FinV X.obj) (V₁ : Kron.FinV Y.obj)
    (φ : (Ψfin Φ).obj (stage X V₀) ⟶ (Ψfin Φ).obj (stage Y V₁))
    (hφ : φ ≫ ιF Φ Y V₁.toFinSub = ιF Φ X V₀.toFinSub ≫ f) :
    (Kron.FinV.sub V₀).ι ≫ ρK Φ R hfin hX hY f = σ Φ R V₀ V₁ φ := by
  rw [ρK, Kron.CompatFamily.ι_glue, family_s Φ R hfin hY f V₀ V₁ φ hφ]

omit [FiniteDimensional k A] in
lemma σ_add {X Y : D k} (V₀ : Kron.FinV X.obj) (V₁ : Kron.FinV Y.obj)
    (φ ψ : (Ψfin Φ).obj (stage X V₀) ⟶ (Ψfin Φ).obj (stage Y V₁)) :
    σ Φ R V₀ V₁ (φ + ψ) = σ Φ R V₀ V₁ φ + σ Φ R V₀ V₁ ψ := by
  rw [σ, σ, σ, map_add]
  exact Preadditive.add_comp ..

omit [FiniteDimensional k A] in
lemma σ_smul {X Y : D k} (V₀ : Kron.FinV X.obj) (V₁ : Kron.FinV Y.obj) (c : k)
    (φ : (Ψfin Φ).obj (stage X V₀) ⟶ (Ψfin Φ).obj (stage Y V₁)) :
    σ Φ R V₀ V₁ (c • φ) = c • σ Φ R V₀ V₁ φ := by
  rw [σ, σ, map_smul]
  exact Linear.smul_comp ..

omit [FiniteDimensional k A] in
lemma σ_comp {X Y Z : D k} (V₀ : Kron.FinV X.obj) (V₁ : Kron.FinV Y.obj) (V₂ : Kron.FinV Z.obj)
    (φ : (Ψfin Φ).obj (stage X V₀) ⟶ (Ψfin Φ).obj (stage Y V₁))
    (ψ : (Ψfin Φ).obj (stage Y V₁) ⟶ (Ψfin Φ).obj (stage Z V₂)) :
    σ Φ R V₀ V₂ (φ ≫ ψ) = InCfin.kh (R.ρ (stage X V₀) (stage Y V₁) φ) ≫ σ Φ R V₁ V₂ ψ := by
  rw [σ, σ, R.map_comp]
  exact Category.assoc _ _ _

lemma Kron.Sub.eq_zero_of_comp_ι {X : Kron k} {U : Kron.Sub X} {Z : Kron k} (g : Z ⟶ U.toKron)
    (h : g ≫ U.ι = 0) : g = 0 := by
  apply Kron.hom_ext
  · ext v
    exact Subtype.ext (congrArg (fun φ : Z ⟶ X ↦ (φ.app zero).hom v) h)
  · ext w
    exact Subtype.ext (congrArg (fun φ : Z ⟶ X ↦ (φ.app one).hom w) h)

/-- The retraction of `f` is zero exactly when its finite retractions are. -/
lemma ρK_eq_zero_iff {X Y : D k} (hX : InC X.obj) (hY : InC Y.obj)
    (f : (functor Φ).obj X ⟶ (functor Φ).obj Y) (V₀ : Kron.FinV X.obj) (V₁ : Kron.FinV Y.obj)
    (φ : (Ψfin Φ).obj (stage X V₀) ⟶ (Ψfin Φ).obj (stage Y V₁))
    (hφ : φ ≫ ιF Φ Y V₁.toFinSub = ιF Φ X V₀.toFinSub ≫ f) (h0 : ρK Φ R hfin hX hY f = 0) :
    R.ρ (stage X V₀) (stage Y V₁) φ = 0 := by
  have h := ι_ρK Φ R hfin hX hY f V₀ V₁ φ hφ
  rw [h0, Limits.comp_zero, σ] at h
  have := Kron.Sub.eq_zero_of_comp_ι _ h.symm
  ext1; ext1; exact this

/-- Proposition 2.5: the retractions for `F` on `C`. -/
def retractions : Retractions k ((InCD (k := k)).ι ⋙ functor Φ) where
  ρ X Y :=
    { toFun f := ObjectProperty.homMk (ObjectProperty.homMk (ρK Φ R hfin X.2 Y.2 f))
      map_add' f g := by
        ext1; ext1
        refine Kron.hom_ext_finV X.2 fun V₀ ↦ ?_
        obtain ⟨V₁, -, φ, hφ⟩ := exists_liftV Φ hfin Y.2 f V₀ ⟨⊥, inferInstance⟩
        obtain ⟨V₂, -, ψ, hψ⟩ := exists_liftV Φ hfin Y.2 g V₀ ⟨⊥, inferInstance⟩
        let V₃ := Kron.FinV.sup V₁ V₂
        have h₁ : V₁.toFinSub ≤ V₃.toFinSub := Kron.FinV.toFinSub_mono (Kron.FinV.le_sup_left _ _)
        have h₂ : V₂.toFinSub ≤ V₃.toFinSub := Kron.FinV.toFinSub_mono (Kron.FinV.le_sup_right _ _)
        change _ ≫ ρK Φ R hfin X.2 Y.2 (f + g) = _ ≫ (ρK Φ R hfin X.2 Y.2 f + ρK Φ R hfin X.2 Y.2 g)
        rw [ι_ρK Φ R hfin X.2 Y.2 (f + g) V₀ V₃ (φ ≫ trans Φ Y.obj h₁ + ψ ≫ trans Φ Y.obj h₂)
          (by rw [Preadditive.add_comp, Category.assoc, Category.assoc, trans_ιF, trans_ιF, hφ, hψ,
            Preadditive.comp_add]; rfl),
          Preadditive.comp_add, ι_ρK Φ R hfin X.2 Y.2 f V₀ V₁ φ hφ,
          ι_ρK Φ R hfin X.2 Y.2 g V₀ V₂ ψ hψ, σ_add, σ_trans, σ_trans]
      map_smul' c f := by
        ext1; ext1
        refine Kron.hom_ext_finV X.2 fun V₀ ↦ ?_
        obtain ⟨V₁, -, φ, hφ⟩ := exists_liftV Φ hfin Y.2 f V₀ ⟨⊥, inferInstance⟩
        change _ ≫ ρK Φ R hfin X.2 Y.2 (c • f) = _ ≫ (c • ρK Φ R hfin X.2 Y.2 f)
        rw [ι_ρK Φ R hfin X.2 Y.2 (c • f) V₀ V₁ (c • φ)
          (by rw [Linear.smul_comp, hφ, Linear.comp_smul]; rfl),
          Linear.comp_smul, ι_ρK Φ R hfin X.2 Y.2 f V₀ V₁ φ hφ, σ_smul] }
  map_comp {X Y Z} f g := by
    ext1; ext1
    refine Kron.hom_ext_finV X.2 fun V₀ ↦ ?_
    obtain ⟨V₁, -, φ, hφ⟩ := exists_liftV Φ hfin Y.2 f V₀ ⟨⊥, inferInstance⟩
    obtain ⟨V₂, -, ψ, hψ⟩ := exists_liftV Φ hfin Z.2 g V₁ ⟨⊥, inferInstance⟩
    change _ ≫ ρK Φ R hfin X.2 Z.2 (f ≫ g) = _ ≫ (ρK Φ R hfin X.2 Y.2 f ≫ ρK Φ R hfin Y.2 Z.2 g)
    have e₁ := ι_ρK Φ R hfin Y.2 Z.2 g V₁ V₂ ψ hψ
    have e₂ : (Kron.FinV.sub V₀).ι ≫ ρK Φ R hfin X.2 Y.2 f =
        InCfin.kh (R.ρ _ _ φ) ≫ (Kron.FinV.sub V₁).ι := ι_ρK Φ R hfin X.2 Y.2 f V₀ V₁ φ hφ
    rw [ι_ρK Φ R hfin X.2 Z.2 (f ≫ g) V₀ V₂ (φ ≫ ψ)
      (by rw [Category.assoc, hψ, ← Category.assoc]; erw [hφ]; rw [Category.assoc]; rfl),
      σ_comp, ← e₁]
    exact ((Category.assoc ..).symm.trans (congrArg (· ≫ ρK Φ R hfin Y.2 Z.2 g) e₂.symm)).trans
      (Category.assoc ..)
  ρ_map {X Y} u := by
    ext1; ext1
    refine Kron.hom_ext_finV X.2 fun V₀ ↦ ?_
    obtain ⟨V₁, hV₁⟩ := Kron.FinV.exists_le Y.2 (Kron.FinSub.map u.hom.hom V₀.toFinSub)
    let ψ : stage X.obj V₀ ⟶ stage Y.obj V₁ :=
      ObjectProperty.homMk (restrict u.hom V₀.toFinSub V₁.toFinSub hV₁)
    change _ ≫ ρK Φ R hfin X.2 Y.2 ((functor Φ).map u.hom) = _
    rw [ι_ρK Φ R hfin X.2 Y.2 _ V₀ V₁ ((Ψfin Φ).map ψ) (ιF_map Φ u.hom _ _ hV₁).symm, σ, R.ρ_map]
    exact Kron.Sub.restrict_ι u.hom.hom V₀.toFinSub.1 V₁.toFinSub.1 hV₁

/-- The finite lifts of a composite of maps in kernels of the new retractions
form a composite of maps in kernels of the finite retractions. -/
lemma kerChain_lift {n : ℕ} {X Y : (InCD (k := k)).FullSubcategory}
    {f : ((InCD (k := k)).ι ⋙ functor Φ).obj X ⟶ ((InCD (k := k)).ι ⋙ functor Φ).obj Y}
    (hf : (retractions Φ R hfin).KerChain n f) (V₀ : Kron.FinV X.obj.obj) :
    ∃ (V₁ : Kron.FinV Y.obj.obj) (φ : (Ψfin Φ).obj (stage X.obj V₀) ⟶ (Ψfin Φ).obj (stage Y.obj V₁)),
      φ ≫ ιF Φ Y.obj V₁.toFinSub = ιF Φ X.obj V₀.toFinSub ≫ f ∧ R.KerChain n φ := by
  induction hf with
  | nil X => exact ⟨V₀, 𝟙 _, by simp, Retractions.KerChain.nil _⟩
  | @cons n X Y Z f g _ hg ih =>
    obtain ⟨V₁, φ, hφ, hφn⟩ := ih V₀
    obtain ⟨V₂, -, ψ, hψ⟩ := exists_liftV Φ hfin Z.2 g V₁ ⟨⊥, inferInstance⟩
    refine ⟨V₂, φ ≫ ψ, ?_, Retractions.KerChain.cons hφn ?_⟩
    · rw [Category.assoc, hψ, ← Category.assoc]; erw [hφ]; rw [Category.assoc]
    · refine ρK_eq_zero_iff Φ R hfin Y.2 Z.2 g V₁ V₂ ψ hψ ?_
      have h₁ : InCD.kh ((retractions Φ R hfin).ρ Y Z g) = ρK Φ R hfin Y.2 Z.2 g := rfl
      rw [← h₁, hg]
      rfl

/-- Proposition 2.5, nilpotence: the bound of the finite retractions passes to
the retractions on `C`. -/
lemma nilpotentBound {n : ℕ} (hn : R.NilpotentBound n) :
    (retractions Φ R hfin).NilpotentBound n := by
  intro X Y f hf
  refine ιF_hom_ext Φ fun U ↦ ?_
  obtain ⟨V₀, hV₀⟩ := Kron.FinV.exists_le X.2 U
  obtain ⟨V₁, φ, hφ, hφn⟩ := kerChain_lift Φ R hfin hf V₀
  rw [Limits.comp_zero]
  erw [← trans_ιF Φ X.obj hV₀]
  rw [Category.assoc]
  erw [← hφ]
  rw [hn φ hφn, Limits.zero_comp, Limits.comp_zero]

end Extension

end LargeIndecomposable
