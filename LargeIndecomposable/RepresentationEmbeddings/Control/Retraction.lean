module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Algebra.Category.ModuleCat.Algebra

/-!
# Retractions

Definition 2.3 of the manuscript: for a `k`-linear functor `Ψ : 𝒞 ⥤ Mod A`,
retractions for `Ψ` are `k`-linear maps
`ρ_{X,Y} : Hom(Ψ X, Ψ Y) → Hom(X, Y)` compatible with composition and left
inverse to `Ψ`. The domain `𝒞` is any `k`-linear category; in the applications
it is `D`, `D_fin`, or a full subcategory such as `C` or `C_fin`.

`Retractions.KerChain R n f` says that `f` is a composite of `n` composable
maps lying in kernels of the retractions, and `Retractions.NilpotentBound R n`
says that every such composite is zero.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory

universe v v' w w' u

variable (k : Type u) [Field k] {A : Type u} [Ring A] [Algebra k A]
  {𝒞 : Type w} [Category.{v} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]

/-- Definition 2.3: retractions for `Ψ` on `𝒞`. -/
structure Retractions (Ψ : 𝒞 ⥤ ModuleCat.{u} A) where
  /-- The retraction `ρ_{X,Y} : Hom(Ψ X, Ψ Y) → Hom(X, Y)`. -/
  ρ : ∀ X Y : 𝒞, (Ψ.obj X ⟶ Ψ.obj Y) →ₗ[k] (X ⟶ Y)
  map_comp : ∀ {X Y Z : 𝒞} (f : Ψ.obj X ⟶ Ψ.obj Y) (g : Ψ.obj Y ⟶ Ψ.obj Z),
    ρ X Z (f ≫ g) = ρ X Y f ≫ ρ Y Z g
  ρ_map : ∀ {X Y : 𝒞} (u : X ⟶ Y), ρ X Y (Ψ.map u) = u

namespace Retractions

variable {k} {Ψ : 𝒞 ⥤ ModuleCat.{u} A} (R : Retractions k Ψ)

lemma ρ_id (X : 𝒞) : R.ρ X X (𝟙 _) = 𝟙 X := by
  simpa using R.ρ_map (𝟙 X)

/-- Retractions are natural in both variables. -/
lemma ρ_map_comp_map {X X' Y Y' : 𝒞} (u : X ⟶ X') (f : Ψ.obj X' ⟶ Ψ.obj Y') (v : Y' ⟶ Y) :
    R.ρ X Y (Ψ.map u ≫ f ≫ Ψ.map v) = u ≫ R.ρ X' Y' f ≫ v := by
  rw [R.map_comp, R.map_comp, R.ρ_map, R.ρ_map]

include R in
/-- A functor with retractions is faithful. -/
lemma map_injective {X Y : 𝒞} : Function.Injective (Ψ.map : (X ⟶ Y) → _) := by
  intro u u' h
  rw [← R.ρ_map u, ← R.ρ_map u', h]

/-- `KerChain R n f`: `f` is a composite of `n` composable maps lying in
kernels of the retractions (the empty composite is an identity). -/
inductive KerChain : ℕ → ∀ {X Y : 𝒞}, (Ψ.obj X ⟶ Ψ.obj Y) → Prop
  | nil (X : 𝒞) : KerChain 0 (𝟙 (Ψ.obj X))
  | cons {n : ℕ} {X Y Z : 𝒞} {f : Ψ.obj X ⟶ Ψ.obj Y} {g : Ψ.obj Y ⟶ Ψ.obj Z} :
      KerChain n f → R.ρ Y Z g = 0 → KerChain (n + 1) (f ≫ g)

/-- Every composite of `n` composable maps lying in kernels of the
retractions is zero. -/
def NilpotentBound (n : ℕ) : Prop :=
  ∀ {X Y : 𝒞} (f : Ψ.obj X ⟶ Ψ.obj Y), R.KerChain n f → f = 0

section Transport

variable {𝒞' : Type w'} [Category.{v'} 𝒞'] [Preadditive 𝒞'] [Linear k 𝒞']

/-- The inverse of `G.map` for a fully faithful `k`-linear functor, as a
`k`-linear map. -/
def preimageₗ {G : 𝒞' ⥤ 𝒞} (hG : G.FullyFaithful) [G.Additive] [G.Linear k] (X Y : 𝒞') :
    (G.obj X ⟶ G.obj Y) →ₗ[k] (X ⟶ Y) where
  toFun := hG.preimage
  map_add' f g := hG.map_injective (by simp [Functor.map_add])
  map_smul' c f := hG.map_injective (by simp [Functor.map_smul])

/-- Retractions restrict along a fully faithful `k`-linear functor
`G : 𝒞' ⥤ 𝒞` (for example the inclusion of a full subcategory). -/
def precomp {G : 𝒞' ⥤ 𝒞} (hG : G.FullyFaithful) [G.Additive] [G.Linear k] : Retractions k (G ⋙ Ψ) where
  ρ X Y := preimageₗ hG X Y ∘ₗ R.ρ (G.obj X) (G.obj Y)
  map_comp f g := hG.map_injective (by simp [preimageₗ, R.map_comp])
  ρ_map u := hG.map_injective (by simp [preimageₗ, R.ρ_map])

@[simp]
lemma precomp_ρ {G : 𝒞' ⥤ 𝒞} (hG : G.FullyFaithful) [G.Additive] [G.Linear k] (X Y : 𝒞')
    (f : (G ⋙ Ψ).obj X ⟶ (G ⋙ Ψ).obj Y) :
    G.map ((R.precomp hG).ρ X Y f) = R.ρ (G.obj X) (G.obj Y) f := by
  simp [precomp, preimageₗ]

lemma kerChain_precomp {G : 𝒞' ⥤ 𝒞} (hG : G.FullyFaithful) [G.Additive] [G.Linear k] {n : ℕ} {X Y : 𝒞'}
    {f : (G ⋙ Ψ).obj X ⟶ (G ⋙ Ψ).obj Y} (h : (R.precomp hG).KerChain n f) :
    R.KerChain n f := by
  induction h with
  | nil X => exact KerChain.nil _
  | cons _ hg ih =>
    refine KerChain.cons ih ?_
    rw [← R.precomp_ρ hG, hg, Functor.map_zero]

lemma NilpotentBound.precomp {G : 𝒞' ⥤ 𝒞} (hG : G.FullyFaithful) [G.Additive] [G.Linear k] {n : ℕ}
    (h : R.NilpotentBound n) : (R.precomp hG).NilpotentBound n :=
  fun f hf ↦ h f (R.kerChain_precomp hG hf)

variable {B : Type u} [Ring B] [Algebra k B]

/-- The inverse of `G.map` for a fully faithful `k`-linear functor between
module categories, as a `k`-linear map. -/
def preimageModₗ {G : ModuleCat.{u} A ⥤ ModuleCat.{u} B} (hG : G.FullyFaithful) [G.Additive] [G.Linear k]
    (M N : ModuleCat.{u} A) : (G.obj M ⟶ G.obj N) →ₗ[k] (M ⟶ N) where
  toFun := hG.preimage
  map_add' f g := hG.map_injective (by simp [Functor.map_add])
  map_smul' c f := hG.map_injective (by simp [Functor.map_smul])

/-- Retractions transport along a fully faithful `k`-linear functor of module
categories `G` (for example inflation along a surjection `B → A`). -/
def postcomp {G : ModuleCat.{u} A ⥤ ModuleCat.{u} B} (hG : G.FullyFaithful) [G.Additive] [G.Linear k] :
    Retractions k (Ψ ⋙ G) where
  ρ X Y := R.ρ X Y ∘ₗ preimageModₗ hG (Ψ.obj X) (Ψ.obj Y)
  map_comp f g := by
    simp only [LinearMap.coe_comp, Function.comp_apply, preimageModₗ, LinearMap.coe_mk,
      AddHom.coe_mk, Functor.FullyFaithful.preimage_comp, R.map_comp]
  ρ_map u := by
    simp only [LinearMap.coe_comp, Function.comp_apply, preimageModₗ, LinearMap.coe_mk,
      AddHom.coe_mk, Functor.comp_map, Functor.FullyFaithful.preimage_map, R.ρ_map]

lemma kerChain_postcomp {G : ModuleCat.{u} A ⥤ ModuleCat.{u} B} (hG : G.FullyFaithful)
    [G.Additive] [G.Linear k] {n : ℕ} {X Y : 𝒞} {f : (Ψ ⋙ G).obj X ⟶ (Ψ ⋙ G).obj Y}
    (h : (R.postcomp hG).KerChain n f) : R.KerChain n (hG.preimage f) := by
  induction h with
  | nil X => simpa using KerChain.nil X
  | cons _ hg ih =>
    rw [Functor.FullyFaithful.preimage_comp]
    exact KerChain.cons ih hg

lemma NilpotentBound.postcomp {G : ModuleCat.{u} A ⥤ ModuleCat.{u} B} (hG : G.FullyFaithful)
    [G.Additive] [G.Linear k] {n : ℕ} (h : R.NilpotentBound n) : (R.postcomp hG).NilpotentBound n := by
  intro X Y f hf
  have := h _ (R.kerChain_postcomp hG hf)
  simpa using congrArg G.map this

end Transport

end Retractions

end LargeIndecomposable
