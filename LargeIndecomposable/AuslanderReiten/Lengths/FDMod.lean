module

public import LargeIndecomposable.AuslanderReiten.Lengths.HaradaSai
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The category of finite-dimensional modules; the Harada–Sai lemma

`FDMod k A`: `A`-modules that are finite-dimensional over `k`, with `A`-linear maps.

`haradaSai`: in a chain `X₀ → X₁ → ⋯ → X_m` of indecomposables of dimension `≤ b` whose
maps are not bijective, the composite is zero once `m ≥ 2ᵇ − 1`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]

/-- A finite-dimensional `A`-module. -/
structure FDMod where
  carrier : Type u
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module A carrier]
  [isModuleK : Module k carrier]
  [isScalarTower : IsScalarTower k A carrier]
  [isFD : FiniteDimensional k carrier]

attribute [instance] FDMod.isAddCommGroup FDMod.isModule FDMod.isModuleK FDMod.isScalarTower
  FDMod.isFD

namespace FDMod

variable {k A}

instance : CoeSort (FDMod k A) (Type u) := ⟨FDMod.carrier⟩

/-- The underlying object of `ModuleCat A`. -/
abbrev toModuleCatObj (X : FDMod k A) : ModuleCat.{u} A := ModuleCat.of A X

/-- Morphisms are morphisms of the underlying `A`-modules in `ModuleCat A`: `FDMod k A` is the
category induced from `ModuleCat A`. -/
instance : Category (FDMod k A) :=
  inferInstanceAs (Category (InducedCategory (ModuleCat.{u} A) (toModuleCatObj (k := k) (A := A))))

/-- The fully faithful functor to `ModuleCat A`. -/
def toModuleCat : FDMod k A ⥤ ModuleCat.{u} A :=
  inducedFunctor (toModuleCatObj (k := k) (A := A))

/-- `toModuleCat` is fully faithful. -/
def toModuleCatFullyFaithful : (toModuleCat (k := k) (A := A)).FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance : (toModuleCat (k := k) (A := A)).Full := InducedCategory.full _
instance : (toModuleCat (k := k) (A := A)).Faithful := InducedCategory.faithful _

/-- The underlying linear map. -/
def lin {X Y : FDMod k A} (f : X ⟶ Y) : X →ₗ[A] Y := InducedCategory.Hom.hom f |>.hom

/-- The morphism given by an `A`-linear map. -/
def ofLin {X Y : FDMod k A} (f : X →ₗ[A] Y) : X ⟶ Y := InducedCategory.homMk (ModuleCat.ofHom f)

@[simp] lemma lin_ofLin {X Y : FDMod k A} (f : X →ₗ[A] Y) : lin (ofLin f) = f := rfl

@[simp] lemma ofLin_lin {X Y : FDMod k A} (f : X ⟶ Y) : ofLin (lin f) = f := rfl

instance : Preadditive (FDMod k A) :=
  inferInstanceAs (Preadditive (InducedCategory (ModuleCat.{u} A) (toModuleCatObj (k := k) (A := A))))

instance : Functor.Additive (toModuleCat (k := k) (A := A)) where

@[simp] lemma lin_zero {X Y : FDMod k A} : lin (0 : X ⟶ Y) = 0 := rfl

@[simp] lemma lin_add {X Y : FDMod k A} (f g : X ⟶ Y) : lin (f + g) = lin f + lin g := rfl

@[simp] lemma lin_neg {X Y : FDMod k A} (f : X ⟶ Y) : lin (-f) = -lin f := rfl

@[simp] lemma lin_sub {X Y : FDMod k A} (f g : X ⟶ Y) : lin (f - g) = lin f - lin g := rfl

@[simp] lemma lin_sum {X Y : FDMod k A} {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    lin (∑ i ∈ s, f i) = ∑ i ∈ s, lin (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, lin_add, ih]

@[simp] lemma ofLin_zero {X Y : FDMod k A} : ofLin (0 : X →ₗ[A] Y) = 0 := rfl

@[simp] lemma ofLin_add {X Y : FDMod k A} (f g : X →ₗ[A] Y) :
    ofLin (f + g) = ofLin f + ofLin g := rfl

lemma lin_injective {X Y : FDMod k A} : Function.Injective (lin : (X ⟶ Y) → (X →ₗ[A] Y)) :=
  fun f g h => by rw [← ofLin_lin f, ← ofLin_lin g, h]

@[ext] lemma hom_ext {X Y : FDMod k A} {f g : X ⟶ Y} (h : lin f = lin g) : f = g :=
  lin_injective h

@[simp] lemma lin_comp {X Y Z : FDMod k A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    lin (f ≫ g) = lin g ∘ₗ lin f := rfl

@[simp] lemma lin_id (X : FDMod k A) : lin (𝟙 X) = LinearMap.id := rfl

lemma comp_def {X Y Z : FDMod k A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = ofLin (lin g ∘ₗ lin f) := rfl

lemma id_def (X : FDMod k A) : 𝟙 X = ofLin (LinearMap.id : X →ₗ[A] X) := rfl

@[simp] lemma ofLin_comp {X Y Z : FDMod k A} (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z) :
    ofLin f ≫ ofLin g = ofLin (g ∘ₗ f) := rfl

lemma comp_eq_iff {X Y Z : FDMod k A} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) :
    f ≫ g = h ↔ lin g ∘ₗ lin f = lin h :=
  ⟨fun e => by rw [← lin_comp, e], fun e => hom_ext (by rw [lin_comp, e])⟩

lemma comp_eq_id_iff {X Y : FDMod k A} (f : X ⟶ Y) (g : Y ⟶ X) :
    f ≫ g = 𝟙 X ↔ lin g ∘ₗ lin f = LinearMap.id := by
  rw [comp_eq_iff, lin_id]

instance {X Y : FDMod k A} : FunLike (X ⟶ Y) X Y where
  coe f := lin f
  coe_injective f g h := lin_injective (LinearMap.coe_injective h)

instance {X Y : FDMod k A} : LinearMapClass (X ⟶ Y) A X Y where
  map_add f := (lin f).map_add
  map_smulₛₗ f := (lin f).map_smul

/-- Applying a morphism is applying its linear map; `simp` normalizes to `lin`. -/
@[simp] lemma coe_eq_lin {X Y : FDMod k A} (f : X ⟶ Y) : ⇑f = ⇑(lin f) := rfl

end FDMod

variable {k A}

/-- **The Harada–Sai lemma.** -/
theorem haradaSai {b m : ℕ} (F : ComposableArrows (FDMod k A) m)
    (hind : ∀ i, IsIndecMod A (F.obj i)) (hdim : ∀ i, finrank k (F.obj i) ≤ b)
    (hnb : ∀ (i : ℕ) (hi : i + 1 ≤ m),
      ¬Function.Bijective (FDMod.lin (F.map' i (i + 1) (by omega) hi)))
    (hm : 2 ^ b - 1 ≤ m) : FDMod.lin (F.map' 0 m (by omega) le_rfl) = 0 := by
  -- the rank of a composite of `2ⁿ - 1` maps is at most `b - n`
  have claim : ∀ n ≤ b, ∀ i j (hij : i ≤ j) (hjm : j ≤ m), j = i + (2 ^ n - 1) →
      rk k (FDMod.lin (F.map' i j hij hjm)) ≤ b - n := by
    intro n
    induction n with
    | zero =>
      intro _ i j hij hjm hj
      simp only [pow_zero, Nat.sub_self, add_zero] at hj
      subst hj
      rw [F.map'_self _ hjm, FDMod.lin_id]
      unfold rk
      rw [LinearMap.range_id, Submodule.restrictScalars_top, finrank_top]
      exact hdim _
    | succ n ih =>
      intro hn i j hij hjm hj
      have h1 := Nat.one_le_two_pow (n := n)
      have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
      set p := i + (2 ^ n - 1) with hp
      obtain rfl : j = p + 1 + (2 ^ n - 1) := by omega
      rw [F.map'_comp i p _ (by omega) (by omega) hjm,
        F.map'_comp p (p + 1) _ (by omega) (by omega) hjm]
      simp only [FDMod.lin_comp]
      have hstep := haradaSai_step (k := k) (hind _) (hind _)
        (FDMod.lin (F.map' i p (by omega) (by omega)))
        (FDMod.lin (F.map' p (p + 1) (by omega) (by omega)))
        (FDMod.lin (F.map' (p + 1) (p + 1 + (2 ^ n - 1)) (by omega) hjm))
        (hnb p (by omega)) (c := b - n) (by omega)
        (ih (by omega) i p (by omega) (by omega) rfl)
        (ih (by omega) (p + 1) _ (by omega) hjm rfl)
      exact (by omega : ∀ x, x < b - n → x ≤ b - (n + 1)) _ hstep
  have h0 := claim b le_rfl 0 (2 ^ b - 1) (by omega) hm (by omega)
  rw [Nat.sub_self, Nat.le_zero] at h0
  have hz : FDMod.lin (F.map' 0 (2 ^ b - 1) (by omega) hm) = 0 := by
    unfold rk at h0
    have := Submodule.finrank_eq_zero.1 h0
    ext x
    have hx : FDMod.lin (F.map' 0 (2 ^ b - 1) (by omega) hm) x ∈
        (LinearMap.range (FDMod.lin (F.map' 0 (2 ^ b - 1) (by omega) hm))).restrictScalars k :=
      LinearMap.mem_range_self _ x
    rw [this] at hx
    rw [LinearMap.zero_apply]
    exact (Submodule.mem_bot k).1 hx
  rw [F.map'_comp 0 (2 ^ b - 1) m (by omega) hm le_rfl, FDMod.lin_comp, hz,
    LinearMap.comp_zero]

end LargeIndecomposable.AR
