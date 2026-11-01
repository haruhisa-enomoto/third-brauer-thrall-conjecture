module

public import LargeIndecomposable.RepresentationEmbeddings.ColimitExtension.HomExtension
public import LargeIndecomposable.RepresentationEmbeddings.ColimitExtension.FixedSummand
public import LargeIndecomposable.RepresentationEmbeddings.Control.Consequences
public import LargeIndecomposable.RepresentationEmbeddings.ColimitExtension.Colimit
public import LargeIndecomposable.RepresentationEmbeddings.ColimitExtension.Cancellation

/-!
# `F(T₀)` has no summand `F(S₋)` for `T₀ ∈ C`

The first paragraph of the proof of Theorem 2.7. The manuscript decomposes a
finite-dimensional `T₁ ⊆ T₀` in `C` into indecomposables and applies the
Krull–Schmidt theorem. We argue with the retractions instead: if
`P = Φ(S₋)` is a summand of `Φ(T₁)` through an idempotent `ε`, then `ε` and
`Φ(ρ(ε))` agree modulo the nilpotent kernel of `ρ`, hence are conjugate, so
`P ≅ Φ(T₁')` for the summand `T₁' = im ρ(ε)` of `T₁`. Since `T₁' ∈ C`, it is
not isomorphic to `S₋`, contradicting reflection of isomorphism classes.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair

universe u

variable {k : Type u} [Field k]

/-! ### The image of an idempotent of a Kronecker module -/

namespace Kron

variable {X : Kron k} (η : X ⟶ X) (hη : η ≫ η = η)

/-- The image of an endomorphism, as a subrepresentation. -/
def imSub : Kron.Sub X where
  V := LinearMap.range (η.app zero).hom
  W := LinearMap.range (η.app one).hom
  map_a := by rintro _ ⟨v, rfl⟩; exact ⟨X.a.hom v, Kron.a_apply η v⟩
  map_b := by rintro _ ⟨v, rfl⟩; exact ⟨X.b.hom v, Kron.b_apply η v⟩

include hη in
lemma app_idem (j : WalkingParallelPair) (x : X.obj j) :
    (η.app j).hom ((η.app j).hom x) = (η.app j).hom x := by
  rw [← ModuleCat.comp_apply, ← NatTrans.comp_app, hη]

/-- The corestriction `X → im η`. -/
def imRetr : X ⟶ (imSub η).toKron :=
  Kron.homMk (ModuleCat.ofHom ((η.app zero).hom.rangeRestrict))
    (ModuleCat.ofHom ((η.app one).hom.rangeRestrict))
    (by ext v; exact Subtype.ext (Kron.a_apply η v))
    (by ext v; exact Subtype.ext (Kron.b_apply η v))

lemma imRetr_ι : imRetr η ≫ (imSub η).ι = η := by
  apply Kron.hom_ext <;> rfl

include hη in
lemma ι_imRetr : (imSub η).ι ≫ imRetr η = 𝟙 _ := by
  apply Kron.hom_ext
  · ext ⟨_, v, rfl⟩
    exact Subtype.ext (app_idem η hη zero v)
  · ext ⟨_, w, rfl⟩
    exact Subtype.ext (app_idem η hη one w)

/-- The image of an endomorphism of a module in `C` is in `C`. -/
lemma inC_imSub (hX : InC X) : InC (imSub η).toKron := by
  refine ⟨(imSub η).inD hX.1, ?_⟩
  rw [eq_top_iff]
  rintro ⟨_, w, rfl⟩ -
  have hw : w ∈ LinearMap.range X.a.hom ⊔ LinearMap.range X.b.hom := hX.2 ▸ trivial
  obtain ⟨_, ⟨v, rfl⟩, _, ⟨v', rfl⟩, rfl⟩ := Submodule.mem_sup.1 hw
  let x : LinearMap.range (η.app zero).hom := ⟨_, LinearMap.mem_range_self (η.app zero).hom v⟩
  let x' : LinearMap.range (η.app zero).hom := ⟨_, LinearMap.mem_range_self (η.app zero).hom v'⟩
  have e : (⟨(η.app one).hom (X.a.hom v + X.b.hom v'), ⟨_, rfl⟩⟩ :
      LinearMap.range (η.app one).hom) =
      (imSub η).toKron.a.hom x + (imSub η).toKron.b.hom x' := by
    apply Subtype.ext
    change (η.app one).hom (X.a.hom v + X.b.hom v') =
      X.a.hom ((η.app zero).hom v) + X.b.hom ((η.app zero).hom v')
    rw [map_add, Kron.a_apply, Kron.b_apply]
  have h := Submodule.add_mem_sup (LinearMap.mem_range_self ((imSub η).toKron.a.hom) x)
    (LinearMap.mem_range_self ((imSub η).toKron.b.hom) x')
  convert h using 1
  exact e

lemma isFiniteDimensional_imSub (hX : X.IsFiniteDimensional) :
    (imSub η).toKron.IsFiniteDimensional := by
  obtain ⟨h0, h1⟩ := hX
  exact ⟨inferInstanceAs (FiniteDimensional k (LinearMap.range (η.app zero).hom)),
    inferInstanceAs (FiniteDimensional k (LinearMap.range (η.app one).hom))⟩

end Kron

lemma not_inC_Sminus : ¬ InC (Kron.Sminus k) := by
  rintro ⟨-, h⟩
  have : (1 : k) ∈ (⊤ : Submodule k k) := trivial
  rw [← h] at this
  obtain ⟨_, ⟨v, rfl⟩, _, ⟨v', rfl⟩, h1⟩ := Submodule.mem_sup.1 this
  simp at h1

variable {A : Type u} [Ring A] [Algebra k A]

namespace Extension

variable (Φ : Dfin k ⥤ ModuleCat.{u} A) (R : Retractions k (Ψfin Φ))

/-- `S₋` as an object of `D_fin`. -/
def SminusFin : Dfin k := ⟨Sminus.obj, Sminus.2, Sminus_isFiniteDimensional⟩

lemma Retractions.iter_eq_pow {M : ModuleCat.{u} A} (e : M ⟶ M) (m : ℕ) :
    Retractions.iter e m = ((show End M from e) ^ m : End M) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Retractions.iter, ih, pow_succ', End.mul_def]

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable [FiniteDimensional k A] (hfin : ∀ X : Dfin k, Module.Finite k (RestrictScalars k A (Φ.obj X)))

include hfin in
/-- First paragraph of the proof of Theorem 2.7: for `T₀ ∈ C`, the module
`F(T₀)` has no direct summand isomorphic to `Φ(S₋)`. -/
theorem noSummand {n : ℕ} (hn : R.NilpotentBound n)
    (hnot : ∀ X : Dfin k, InC X.obj → IsEmpty (Φ.obj SminusFin ≅ Φ.obj X))
    (T₀ : D k) (hT₀ : InC T₀.obj) :
    FixedSummand.NoSummand (Φ.obj SminusFin) ((functor Φ).obj T₀) := by
  intro i p hip
  -- factor `i` through a stage `Φ(T_{V₀})`
  have : Module.Finite k (Φ.obj SminusFin) := hfin _
  obtain ⟨U, -, i₀, hi₀⟩ := exists_lift Φ T₀ i ⟨⊥, Kron.Sub.isFin_bot⟩
  obtain ⟨V₀, hV₀⟩ := Kron.FinV.exists_le hT₀ U
  let T₁ := stage T₀ V₀
  let i' : Φ.obj SminusFin ⟶ (Ψfin Φ).obj T₁ := i₀ ≫ trans Φ T₀ hV₀
  let p' : (Ψfin Φ).obj T₁ ⟶ Φ.obj SminusFin := ιF Φ T₀ V₀.toFinSub ≫ p
  have hip' : i' ≫ p' = 𝟙 _ := by
    simp only [i', p', Category.assoc]
    rw [← Category.assoc (trans Φ T₀ hV₀), trans_ιF, ← Category.assoc, hi₀, hip]
  -- the idempotent `ε` and its retraction `η`
  let ε : (Ψfin Φ).obj T₁ ⟶ (Ψfin Φ).obj T₁ := p' ≫ i'
  have hε : ε ≫ ε = ε := by
    simp only [ε, Category.assoc]; rw [← Category.assoc i', hip', Category.id_comp]
  let η : T₁ ⟶ T₁ := R.ρ T₁ T₁ ε
  have hη : η ≫ η = η := by simp only [η]; rw [← R.map_comp, hε]
  let f : (Ψfin Φ).obj T₁ ⟶ (Ψfin Φ).obj T₁ := (Ψfin Φ).map η
  -- the conjugating unit
  let w : (Ψfin Φ).obj T₁ ⟶ (Ψfin Φ).obj T₁ := ε ≫ f + (𝟙 _ - ε) ≫ (𝟙 _ - f)
  have hρw : R.ρ T₁ T₁ (𝟙 _ - w) = 0 := by
    simp only [w, map_sub, map_add, R.map_comp, R.ρ_id, f, R.ρ_map]
    change 𝟙 T₁ - (η ≫ η + (𝟙 T₁ - η) ≫ (𝟙 T₁ - η)) = 0
    simp [Preadditive.sub_comp, Preadditive.comp_sub, hη]
  have hw : IsIso w := by
    have hnil : IsNilpotent (show End ((Ψfin Φ).obj T₁) from 𝟙 _ - w) :=
      ⟨n, by rw [← Retractions.iter_eq_pow]; exact hn _ (R.kerChain_iter _ hρw n)⟩
    have := isIso_id_sub_of_isNilpotent _ hnil
    simpa using this
  have hεw : ε ≫ w = w ≫ f := by
    have hff : f ≫ f = f := by simp only [f]; rw [← Functor.map_comp, hη]
    simp only [w, Preadditive.comp_add, Preadditive.add_comp, Preadditive.comp_sub,
      Preadditive.sub_comp, Category.comp_id, Category.id_comp, Category.assoc, hff,
      ← Category.assoc ε ε, hε]
    abel
  -- the summand `T₁' = im η` of `T₁`
  let ηK : T₁.obj.obj ⟶ T₁.obj.obj := InCfin.kh η
  have hηK : ηK ≫ ηK = ηK := by
    change InCfin.kh (η ≫ η) = _; rw [hη]
  let T₁' : Dfin k := ⟨(Kron.imSub ηK).toKron, (Kron.imSub ηK).inD T₁.obj.2.1,
    Kron.isFiniteDimensional_imSub ηK T₁.obj.2.2⟩
  let ιT : T₁' ⟶ T₁.obj := ObjectProperty.homMk (Kron.imSub ηK).ι
  let rT : T₁.obj ⟶ T₁' := ObjectProperty.homMk (Kron.imRetr ηK)
  have hrι : rT ≫ ιT = η.hom := by ext1; exact Kron.imRetr_ι ηK
  have hιr : ιT ≫ rT = 𝟙 _ := by ext1; exact Kron.ι_imRetr ηK hηK
  -- `Φ(S₋) ≅ Φ(T₁')`
  let e : Φ.obj SminusFin ≅ Φ.obj T₁' :=
    { hom := i' ≫ w ≫ Φ.map rT
      inv := Φ.map ιT ≫ inv w ≫ p'
      hom_inv_id := by
        have h₁ : w ≫ Φ.map rT ≫ Φ.map ιT ≫ inv w = ε := by
          rw [← Category.assoc (Φ.map rT), ← Φ.map_comp, hrι]
          change w ≫ f ≫ inv w = ε
          rw [← Category.assoc, ← hεw, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
        calc i' ≫ (w ≫ Φ.map rT) ≫ Φ.map ιT ≫ inv w ≫ p'
            = i' ≫ (w ≫ Φ.map rT ≫ Φ.map ιT ≫ inv w) ≫ p' := by simp only [Category.assoc]
          _ = (i' ≫ p') ≫ (i' ≫ p') := by rw [h₁]; simp only [ε, Category.assoc]
          _ = 𝟙 _ := by rw [hip', Category.id_comp]
      inv_hom_id := by
        have h₁ : inv w ≫ ε ≫ w = f := by rw [hεw, IsIso.inv_hom_id_assoc]
        calc (Φ.map ιT ≫ inv w ≫ p') ≫ i' ≫ w ≫ Φ.map rT
            = Φ.map ιT ≫ (inv w ≫ ε ≫ w) ≫ Φ.map rT := by simp only [ε, Category.assoc]
          _ = Φ.map (ιT ≫ (rT ≫ ιT) ≫ rT) := by
            rw [h₁, hrι]; simp only [Φ.map_comp]; rfl
          _ = 𝟙 _ := by
            rw [show (ιT ≫ (rT ≫ ιT) ≫ rT) = 𝟙 _ by
              rw [← Category.assoc, ← Category.assoc, hιr, Category.id_comp, hιr], Φ.map_id] }
  exact (hnot T₁' (Kron.inC_imSub ηK T₁.2)).false e

end Extension

end LargeIndecomposable
