module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The `k`-linear category of a basic algebra

Section 3.3 of the manuscript fixes a complete set of primitive orthogonal
idempotents `e_i` of the basic algebra `A` and considers the `k`-linear
category `𝒜` with these vertices as objects and morphism spaces
`𝒜(i, j) = e_j A e_i`, composition being multiplication. It identifies
`A`-modules with `𝒜`-modules.

This file defines

* `LinMod k C`: modules over a `k`-linear category `C`, that is, `k`-linear
  functors `C ⥤ Mod k`;
* `IdempotentFamily A ι`: a complete family `e : ι → A` of orthogonal
  idempotents (primitivity is never used, so it is not recorded);
* `AlgebraCategory k E`: the category `𝒜`;
* `AlgebraCategory.toModule`: the functor `M ↦ ⊕ᵢ M(i)` from `𝒜`-modules to
  `A`-modules, where `a` acts through the blocks `e_j a e_i`. It is `k`-linear,
  fully faithful (`fullyFaithfulToModule`), exact and faithful
  (`range_map_eq_ker_map`, `injective_map_iff`, `surjective_map_iff`), and it
  preserves finite dimension (`finite_toModule`); its underlying `k`-space is
  `∏ᵢ M(i)` (`restrictScalarsEquiv`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory

universe v w u

/-! ### Modules over a `k`-linear category -/

section LinMod

variable (k : Type u) [Field k] (C : Type w) [Category.{v} C] [Preadditive C] [Linear k C]

/-- A functor `C ⥤ Mod k` is a module over the `k`-linear category `C` if it is
additive and `k`-linear. -/
def IsLinearModule : ObjectProperty (C ⥤ ModuleCat.{u} k) := fun X ↦ X.Additive ∧ X.Linear k

/-- Modules over a `k`-linear category `C`: `k`-linear functors `C ⥤ Mod k`,
with natural transformations as morphisms. -/
abbrev LinMod : Type (max w v (u + 1)) := (IsLinearModule k C).FullSubcategory

variable {k C}

instance (X : LinMod k C) : X.obj.Additive := X.property.1

instance (X : LinMod k C) : X.obj.Linear k := X.property.2

/-- The module over `C` given by a `k`-linear functor. -/
abbrev LinMod.mk (X : C ⥤ ModuleCat.{u} k) [X.Additive] [X.Linear k] : LinMod k C :=
  ⟨X, inferInstance, inferInstance⟩

lemma LinMod.hom_ext {X Y : LinMod k C} {f g : X ⟶ Y} (h : ∀ x, f.hom.app x = g.hom.app x) :
    f = g := by
  ext x : 3
  rw [h x]

@[simp]
lemma LinMod.add_app {X Y : LinMod k C} (f g : X ⟶ Y) (x : C) :
    (f + g).hom.app x = f.hom.app x + g.hom.app x := rfl

@[simp]
lemma LinMod.zero_app {X Y : LinMod k C} (x : C) : (0 : X ⟶ Y).hom.app x = 0 := rfl

@[simp]
lemma LinMod.smul_app {X Y : LinMod k C} (c : k) (f : X ⟶ Y) (x : C) :
    (c • f).hom.app x = c • f.hom.app x := rfl

@[simp]
lemma LinMod.sub_app {X Y : LinMod k C} (f g : X ⟶ Y) (x : C) :
    (f - g).hom.app x = f.hom.app x - g.hom.app x := rfl

@[simp]
lemma LinMod.neg_app {X Y : LinMod k C} (f : X ⟶ Y) (x : C) :
    (-f).hom.app x = -f.hom.app x := rfl

@[simp]
lemma LinMod.comp_app {X Y Z : LinMod k C} (f : X ⟶ Y) (g : Y ⟶ Z) (x : C) :
    (f ≫ g).hom.app x = f.hom.app x ≫ g.hom.app x := rfl

@[simp]
lemma LinMod.id_app (X : LinMod k C) (x : C) : (𝟙 X : X ⟶ X).hom.app x = 𝟙 _ := rfl

lemma LinMod.sum_app {X Y : LinMod k C} {α : Type*} (s : Finset α) (f : α → (X ⟶ Y))
    (x : C) : (∑ a ∈ s, f a).hom.app x = ∑ a ∈ s, (f a).hom.app x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

end LinMod

/-! ### Complete families of orthogonal idempotents -/

/-- A complete family of orthogonal idempotents `e : ι → A`: idempotent,
pairwise orthogonal, with sum `1`. In the manuscript the `e_i` are moreover
primitive (the vertices of the basic algebra `A`); primitivity is not used in
the constructions of this file. -/
structure IdempotentFamily (A : Type u) [Ring A] (ι : Type u) [Fintype ι] where
  /-- The idempotents. -/
  e : ι → A
  mul_self : ∀ i, e i * e i = e i
  mul_eq_zero : ∀ i j, i ≠ j → e i * e j = 0
  sum_eq_one : ∑ i, e i = 1

namespace IdempotentFamily

variable {A : Type u} [Ring A] {ι : Type u} [Fintype ι] (E : IdempotentFamily A ι)

lemma mul_e (i j : ι) [Decidable (i = j)] : E.e i * E.e j = if i = j then E.e i else 0 := by
  split_ifs with h
  · subst h; exact E.mul_self i
  · exact E.mul_eq_zero i j h

variable (k : Type u) [Field k] [Algebra k A]

/-- The corner `e_j A e_i`, the morphism space `𝒜(i, j)`. -/
def corner (i j : ι) : Submodule k A where
  carrier := {a | E.e j * a * E.e i = a}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [mul_add, add_mul, ha, hb]
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_ofPred_eq] at *
    rw [mul_smul_comm, smul_mul_assoc, ha]

variable {E k}

lemma mem_corner {i j : ι} {a : A} : a ∈ E.corner k i j ↔ E.e j * a * E.e i = a := Iff.rfl

lemma e_mul_of_mem {i j : ι} {a : A} (h : a ∈ E.corner k i j) : E.e j * a = a := by
  rw [← (mem_corner.1 h), ← mul_assoc, ← mul_assoc, E.mul_self]

lemma mul_e_of_mem {i j : ι} {a : A} (h : a ∈ E.corner k i j) : a * E.e i = a := by
  rw [← (mem_corner.1 h), mul_assoc, E.mul_self]

lemma blk_mem (a : A) (i j : ι) : E.e j * a * E.e i ∈ E.corner k i j := by
  rw [mem_corner, ← mul_assoc, ← mul_assoc, E.mul_self, mul_assoc, mul_assoc, mul_assoc,
    E.mul_self]

lemma mul_mem {i j l : ι} {a b : A} (ha : a ∈ E.corner k j l) (hb : b ∈ E.corner k i j) :
    a * b ∈ E.corner k i l := by
  rw [mem_corner, ← mul_assoc, e_mul_of_mem ha, mul_assoc, mul_e_of_mem hb]

lemma e_mem (i : ι) : E.e i ∈ E.corner k i i := by
  rw [mem_corner, E.mul_self, E.mul_self]

end IdempotentFamily

/-! ### The category `𝒜` -/

/-- The `k`-linear category `𝒜` of Section 3.3: objects are the vertices `i`,
morphisms `i ⟶ j` are the elements of `e_j A e_i`, and composition is
multiplication. -/
@[nolint unusedArguments]
def AlgebraCategory (k : Type u) [Field k] {A : Type u} [Ring A] [Algebra k A] {ι : Type u}
    [Fintype ι] (_E : IdempotentFamily A ι) : Type u := ι

variable (k : Type u) [Field k] {A : Type u} [Ring A] [Algebra k A] {ι : Type u} [Fintype ι]

namespace AlgebraCategory

variable {k} (E : IdempotentFamily A ι)

instance : Category.{u} (AlgebraCategory k E) where
  Hom i j := E.corner k i j
  id i := ⟨E.e i, IdempotentFamily.e_mem (E := E) i⟩
  comp f g := ⟨g.1 * f.1, IdempotentFamily.mul_mem g.2 f.2⟩
  id_comp f := Subtype.ext (IdempotentFamily.mul_e_of_mem f.2)
  comp_id f := Subtype.ext (IdempotentFamily.e_mul_of_mem f.2)
  assoc f g h := Subtype.ext (mul_assoc h.1 g.1 f.1).symm

instance [DecidableEq ι] : DecidableEq (AlgebraCategory k E) := inferInstanceAs (DecidableEq ι)

instance : Fintype (AlgebraCategory k E) := inferInstanceAs (Fintype ι)

/-- The vertex `i` as an object of `𝒜`. -/
abbrev of (k : Type u) [Field k] [Algebra k A] (E : IdempotentFamily A ι) (i : ι) :
    AlgebraCategory k E := i

variable {E}

/-- The element of `A` underlying a morphism of `𝒜`. -/
abbrev val {i j : AlgebraCategory k E} (f : i ⟶ j) : A := Subtype.val (p := (· ∈ E.corner k i j)) f

lemma mem {i j : AlgebraCategory k E} (f : i ⟶ j) : val f ∈ E.corner k i j := f.2

@[ext]
lemma hom_ext {i j : AlgebraCategory k E} {f g : i ⟶ j} (h : val f = val g) : f = g :=
  Subtype.ext h

@[simp]
lemma val_comp {i j l : AlgebraCategory k E} (f : i ⟶ j) (g : j ⟶ l) :
    val (f ≫ g) = val g * val f := rfl

@[simp]
lemma val_id (i : AlgebraCategory k E) : val (𝟙 i) = E.e i := rfl

instance : Preadditive (AlgebraCategory k E) where
  homGroup i j := inferInstanceAs (AddCommGroup (E.corner k i j))
  add_comp _ _ _ f f' g := Subtype.ext (mul_add g.1 f.1 f'.1)
  comp_add _ _ _ f g g' := Subtype.ext (add_mul g.1 g'.1 f.1)

instance : Linear k (AlgebraCategory k E) where
  homModule i j := inferInstanceAs (Module k (E.corner k i j))
  smul_comp _ _ _ c f g := Subtype.ext (mul_smul_comm c g.1 f.1)
  comp_smul _ _ _ f c g := Subtype.ext (smul_mul_assoc c g.1 f.1)

@[simp] lemma val_add {i j : AlgebraCategory k E} (f g : i ⟶ j) : val (f + g) = val f + val g :=
  rfl

@[simp] lemma val_zero {i j : AlgebraCategory k E} : val (0 : i ⟶ j) = 0 := rfl

@[simp] lemma val_neg {i j : AlgebraCategory k E} (f : i ⟶ j) : val (-f) = -val f := rfl

@[simp] lemma val_sub {i j : AlgebraCategory k E} (f g : i ⟶ j) : val (f - g) = val f - val g :=
  rfl

@[simp] lemma val_smul {i j : AlgebraCategory k E} (c : k) (f : i ⟶ j) : val (c • f) = c • val f :=
  rfl

lemma val_sum {i j : AlgebraCategory k E} {α : Type*} (s : Finset α) (f : α → (i ⟶ j)) :
    val (∑ a ∈ s, f a) = ∑ a ∈ s, val (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, val_add, ih]

/-- The morphism of `𝒜` with value `a`, given that `a ∈ e_j A e_i`. -/
def homMk {i j : AlgebraCategory k E} (a : A) (h : a ∈ E.corner k i j) : i ⟶ j := ⟨a, h⟩

@[simp] lemma val_homMk {i j : AlgebraCategory k E} (a : A) (h : a ∈ E.corner k i j) :
    val (homMk a h) = a := rfl

/-- The block `e_j a e_i : i ⟶ j` of an element `a ∈ A`. -/
def blk (a : A) (i j : AlgebraCategory k E) : i ⟶ j := ⟨E.e j * a * E.e i, E.blk_mem a i j⟩

@[simp] lemma val_blk (a : A) (i j : AlgebraCategory k E) : val (blk a i j) = E.e j * a * E.e i :=
  rfl

lemma blk_of_mem {i j : AlgebraCategory k E} (f : i ⟶ j) : blk (val f) i j = f :=
  Subtype.ext f.2

lemma blk_add (a b : A) (i j : AlgebraCategory k E) : blk (a + b) i j = blk a i j + blk b i j :=
  Subtype.ext (by simp [blk, mul_add, add_mul])

lemma blk_smul (c : k) (a : A) (i j : AlgebraCategory k E) : blk (c • a) i j = c • blk a i j :=
  Subtype.ext (by simp [blk])

lemma blk_zero (i j : AlgebraCategory k E) : blk (0 : A) i j = 0 :=
  Subtype.ext (by simp [blk])

lemma blk_mul (a b : A) (i l : AlgebraCategory k E) :
    blk (a * b) i l = ∑ j : ι, blk b i (of k E j) ≫ blk a (of k E j) l := by
  ext
  rw [val_sum]
  simp only [val_blk, val_comp]
  have : E.e l * (a * b) * E.e i = E.e l * a * (∑ j, E.e j) * b * E.e i := by
    rw [E.sum_eq_one, mul_one]; simp only [mul_assoc]
  rw [this, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h := E.mul_self j
  calc E.e l * a * E.e j * b * E.e i
      = E.e l * a * (E.e j * E.e j) * b * E.e i := by rw [h]
    _ = E.e l * a * E.e j * (E.e j * b * E.e i) := by simp only [mul_assoc]

lemma blk_one_self (i : ι) : blk (1 : A) (of k E i) (of k E i) = 𝟙 _ := by
  ext; simp [E.mul_self]

lemma blk_one_of_ne {i j : ι} (h : i ≠ j) : blk (1 : A) (of k E i) (of k E j) = 0 := by
  ext; simp [E.mul_eq_zero j i (Ne.symm h)]

lemma blk_val_of_ne_left {i j : ι} (f : of k E i ⟶ of k E j) {i' : ι} (h : i' ≠ i) (l : ι) :
    blk (val f) (of k E i') (of k E l) = 0 := by
  have hf : val f * E.e i = val f := IdempotentFamily.mul_e_of_mem f.2
  ext
  change E.e l * val f * E.e i' = 0
  rw [← hf, mul_assoc (E.e l), mul_assoc, E.mul_eq_zero i i' (Ne.symm h), mul_zero, mul_zero]

lemma blk_val_of_ne_right {i j : ι} (f : of k E i ⟶ of k E j) (i' : ι) {l : ι} (h : l ≠ j) :
    blk (val f) (of k E i') (of k E l) = 0 := by
  have hf : E.e j * val f = val f := IdempotentFamily.e_mul_of_mem f.2
  ext
  change E.e l * val f * E.e i' = 0
  rw [← hf, ← mul_assoc, E.mul_eq_zero l j h, zero_mul, zero_mul]

lemma blk_e_of_ne_left (l : ι) {i : ι} (h : i ≠ l) (j : ι) :
    blk (E.e l) (of k E i) (of k E j) = 0 :=
  blk_val_of_ne_left (𝟙 (of k E l)) h j

lemma blk_e_of_ne_right (l i : ι) {j : ι} (h : j ≠ l) :
    blk (E.e l) (of k E i) (of k E j) = 0 :=
  blk_val_of_ne_right (𝟙 (of k E l)) i h

lemma blk_e_self (l : ι) : blk (E.e l) (of k E l) (of k E l) = 𝟙 _ :=
  blk_of_mem (𝟙 (of k E l))

/-! ### From `𝒜`-modules to `A`-modules -/

variable (M : LinMod k (AlgebraCategory k E))

/-- The underlying `k`-space `⊕ᵢ M(i)` of the `A`-module of an `𝒜`-module. -/
@[nolint unusedArguments]
abbrev Carrier (M : LinMod k (AlgebraCategory k E)) : Type u := ∀ i : ι, M.obj.obj (of k E i)


namespace Carrier

variable {M}

@[ext]
lemma ext {v w : Carrier M} (h : ∀ i, v i = w i) : v = w := funext h

@[simp] lemma add_apply (v w : Carrier M) (i : ι) : (v + w) i = v i + w i := rfl

@[simp] lemma zero_apply (i : ι) : (0 : Carrier M) i = 0 := rfl

@[simp] lemma smul_apply (c : k) (v : Carrier M) (i : ι) : (c • v) i = c • v i := rfl

@[simp] lemma sum_apply {α : Type*} (s : Finset α) (v : α → Carrier M) (i : ι) :
    (∑ a ∈ s, v a) i = ∑ a ∈ s, v a i := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, ih]

/-- The vector supported at the vertex `i`. -/
def single (i : ι) (m : M.obj.obj (of k E i)) : Carrier M := by
  classical
  exact Pi.single (M := fun l : ι ↦ M.obj.obj (of k E l)) i m

lemma single_eq [DecidableEq ι] (i : ι) (m : M.obj.obj (of k E i)) :
    single i m = Pi.single (M := fun l : ι ↦ M.obj.obj (of k E l)) i m := by
  simp only [single]
  congr
  exact Subsingleton.elim _ _

@[simp] lemma single_apply_self (i : ι) (m : M.obj.obj (of k E i)) :
    single i m i = m := by
  classical
  rw [single_eq]
  exact Pi.single_eq_same (M := fun l : ι ↦ M.obj.obj (of k E l)) i m

lemma single_apply_of_ne {i l : ι} (h : l ≠ i) (m : M.obj.obj (of k E i)) :
    single i m l = 0 := by
  classical
  rw [single_eq]
  exact Pi.single_eq_of_ne (M := fun l : ι ↦ M.obj.obj (of k E l)) h m

@[simp] lemma single_add (i : ι) (m m' : M.obj.obj (of k E i)) :
    single i (m + m') = single i m + single i m' := by
  classical
  simp only [single_eq]
  exact Pi.single_add (f := fun l : ι ↦ M.obj.obj (of k E l)) i m m'

@[simp] lemma single_smul (i : ι) (c : k) (m : M.obj.obj (of k E i)) :
    single i (c • m) = c • single i m := by
  classical
  simp only [single_eq]
  exact (Pi.single_smul (f := fun l : ι ↦ M.obj.obj (of k E l)) i c m)

lemma sum_single (v : Carrier M) : ∑ i : ι, single i (v i) = v := by
  classical
  simp only [single_eq]
  exact Finset.univ_sum_single (M := fun l : ι ↦ M.obj.obj (of k E l)) v

end Carrier

/-- The action of `a ∈ A` on `⊕ᵢ M(i)`: the matrix with blocks `M(e_j a e_i)`. -/
def actLin (a : A) : Carrier M →ₗ[k] Carrier M where
  toFun v j := ∑ i : ι, (M.obj.map (blk a (of k E i) (of k E j))).hom (v i)
  map_add' v w := Carrier.ext fun j ↦ by
    rw [Carrier.add_apply]; simp [Finset.sum_add_distrib]
  map_smul' c v := Carrier.ext fun j ↦ by
    rw [Carrier.smul_apply]; simp [Finset.smul_sum]

lemma actLin_apply (a : A) (v : Carrier M) (j : ι) :
    actLin M a v j = ∑ i : ι, (M.obj.map (blk a (of k E i) (of k E j))).hom (v i) := rfl

/-- The action of `A` on `⊕ᵢ M(i)`, as a `k`-algebra homomorphism. -/
def act : A →ₐ[k] Module.End k (Carrier M) where
  toFun := actLin M
  map_one' := by
    classical
    refine LinearMap.ext fun v ↦ Carrier.ext fun j ↦ ?_
    rw [actLin_apply, Finset.sum_eq_single j]
    · simp [blk_one_self]
    · intro i _ hij
      simp [blk_one_of_ne hij]
    · simp
  map_mul' a b := by
    refine LinearMap.ext fun v ↦ Carrier.ext fun l ↦ ?_
    simp only [Module.End.mul_apply, actLin_apply, blk_mul, Functor.map_sum, Functor.map_comp,
      ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp, LinearMap.comp_apply, map_sum]
    exact Finset.sum_comm
  map_zero' := by
    refine LinearMap.ext fun v ↦ Carrier.ext fun j ↦ ?_
    simp [actLin_apply, blk_zero]
  map_add' a b := by
    refine LinearMap.ext fun v ↦ Carrier.ext fun j ↦ ?_
    simp [actLin_apply, blk_add, Finset.sum_add_distrib]
  commutes' c := by
    classical
    refine LinearMap.ext fun v ↦ Carrier.ext fun j ↦ ?_
    simp only [actLin_apply, Algebra.algebraMap_eq_smul_one, blk_smul, Functor.map_smul,
      ModuleCat.hom_smul, LinearMap.smul_apply]
    rw [Finset.sum_eq_single j]
    · simp [blk_one_self]
    · intro i _ hij
      simp [blk_one_of_ne hij]
    · simp

instance : Module A (Carrier M) := Module.compHom _ (act M).toRingHom

lemma smul_def (a : A) (v : Carrier M) : a • v = actLin M a v := rfl

lemma smul_apply (a : A) (v : Carrier M) (j : ι) :
    (a • v) j = ∑ i : ι, (M.obj.map (blk a (of k E i) (of k E j))).hom (v i) := rfl

instance : IsScalarTower k A (Carrier M) where
  smul_assoc c a v := by
    rw [smul_def, smul_def, show actLin M (c • a) = act M (c • a) from rfl, map_smul]
    rfl

lemma smul_single {i j : ι} (u : of k E i ⟶ of k E j) (m : M.obj.obj (of k E i)) :
    val u • Carrier.single i m = Carrier.single (M := M) j ((M.obj.map u).hom m) := by
  ext l
  rw [smul_apply, Finset.sum_eq_single i]
  · rw [Carrier.single_apply_self]
    by_cases hl : l = j
    · subst hl
      simp [blk_of_mem]
    · rw [blk_val_of_ne_right u i hl, Carrier.single_apply_of_ne hl]
      simp
  · intro i' _ hi'
    rw [Carrier.single_apply_of_ne hi']
    simp
  · simp

lemma e_smul (j : ι) (v : Carrier M) :
    E.e j • v = Carrier.single j (v j) := by
  ext l
  rw [smul_apply, Finset.sum_eq_single j]
  · by_cases hl : l = j
    · subst hl
      simp [blk_e_self]
    · rw [blk_e_of_ne_right j j hl, Carrier.single_apply_of_ne hl]
      simp
  · intro i' _ hi'
    rw [blk_e_of_ne_left j hi']
    simp
  · simp

/-- The `A`-module `⊕ᵢ M(i)` of an `𝒜`-module `M`. -/
abbrev toModuleObj : ModuleCat.{u} A := ModuleCat.of A (Carrier M)

variable {M}

/-- The `A`-linear map `⊕ᵢ fᵢ` of a morphism `f` of `𝒜`-modules. -/
def toModuleMap {N : LinMod k (AlgebraCategory k E)} (f : M ⟶ N) : Carrier M →ₗ[A] Carrier N where
  toFun v i := (f.hom.app (of k E i)).hom (v i)
  map_add' v w := by funext i; simp
  map_smul' a v := by
    funext j
    simp only [RingHom.id_apply, smul_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← ModuleCat.comp_apply, f.hom.naturality, ModuleCat.comp_apply]

@[simp]
lemma toModuleMap_apply {N : LinMod k (AlgebraCategory k E)} (f : M ⟶ N) (v : Carrier M)
    (i : ι) : toModuleMap f v i = (f.hom.app (of k E i)).hom (v i) := rfl

variable (E k)

/-- The functor `M ↦ ⊕ᵢ M(i)` identifying `𝒜`-modules with `A`-modules. -/
def toModule : LinMod k (AlgebraCategory k E) ⥤ ModuleCat.{u} A where
  obj M := toModuleObj M
  map f := ModuleCat.ofHom (toModuleMap f)
  map_id _ := rfl
  map_comp _ _ := rfl

variable {E k}

@[simp]
lemma toModule_map_apply {N : LinMod k (AlgebraCategory k E)} (f : M ⟶ N) (v : Carrier M)
    (i : ι) : ((toModule k E).map f).hom v i = (f.hom.app (of k E i)).hom (v i) := rfl

instance : (toModule k E).Additive where
  map_add := rfl

instance : (toModule k E).Linear k where
  map_smul {M N} f c := by
    ext v : 2
    refine Carrier.ext fun i ↦ ?_
    change c • (f.hom.app (of k E i)).hom (v i) = (algebraMap k A c • toModuleMap f v) i
    rw [algebraMap_smul]
    rfl

/-- An `A`-linear map between the `A`-modules of `𝒜`-modules, as a map of carriers. -/
abbrev homLin {N : LinMod k (AlgebraCategory k E)}
    (g : (toModule k E).obj M ⟶ (toModule k E).obj N) : Carrier M →ₗ[A] Carrier N := g.hom

/-- The preimage of an `A`-linear map: its component at `i` is `m ↦ g(single i m)ᵢ`. -/
def preimageApp {N : LinMod k (AlgebraCategory k E)}
    (g : (toModule k E).obj M ⟶ (toModule k E).obj N) (i : ι) :
    M.obj.obj (of k E i) ⟶ N.obj.obj (of k E i) :=
  ModuleCat.ofHom
    { toFun m := homLin g (Carrier.single i m) i
      map_add' m m' := by
        rw [Carrier.single_add, map_add]
        rfl
      map_smul' c m := by
        rw [RingHom.id_apply, Carrier.single_smul]
        have h := (homLin g).map_smul (algebraMap k A c) (Carrier.single (M := M) i m)
        rw [algebraMap_smul, algebraMap_smul] at h
        exact congrFun h i }

lemma map_single {N : LinMod k (AlgebraCategory k E)}
    (g : (toModule k E).obj M ⟶ (toModule k E).obj N) (i : ι) (m : M.obj.obj (of k E i)) :
    homLin g (Carrier.single i m) = Carrier.single i (homLin g (Carrier.single i m) i) := by
  have h := e_smul M i (Carrier.single i m)
  rw [Carrier.single_apply_self] at h
  conv_lhs => rw [← h, map_smul, e_smul]

lemma preimageApp_apply {N : LinMod k (AlgebraCategory k E)}
    (g : (toModule k E).obj M ⟶ (toModule k E).obj N) (i : ι) (m : M.obj.obj (of k E i)) :
    (preimageApp g i).hom m = homLin g (Carrier.single i m) i := rfl

/-- The natural transformation corresponding to an `A`-linear map. -/
def preimage {N : LinMod k (AlgebraCategory k E)}
    (g : (toModule k E).obj M ⟶ (toModule k E).obj N) : M ⟶ N := by
  refine ObjectProperty.homMk
    { app := preimageApp g
      naturality := fun (i j : ι) u ↦ ?_ }
  ext m
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  change homLin g (Carrier.single j ((M.obj.map u).hom m)) j =
    (N.obj.map u).hom (homLin g (Carrier.single i m) i)
  rw [← smul_single (M := M) u m, map_smul,
    map_single g i m, smul_single, Carrier.single_apply_self, Carrier.single_apply_self]

lemma preimage_app {N : LinMod k (AlgebraCategory k E)}
    (g : (toModule k E).obj M ⟶ (toModule k E).obj N) (i : ι) (m : M.obj.obj (of k E i)) :
    ((preimage g).hom.app (of k E i)).hom m = homLin g (Carrier.single i m) i := rfl

lemma map_preimage {N : LinMod k (AlgebraCategory k E)}
    (g : (toModule k E).obj M ⟶ (toModule k E).obj N) : (toModule k E).map (preimage g) = g := by
  classical
  refine ModuleCat.hom_ext (LinearMap.ext fun (v : Carrier M) ↦ Carrier.ext fun i ↦ ?_)
  change ((preimage g).hom.app (of k E i)).hom (v i) = homLin g v i
  rw [preimage_app]
  conv_rhs => rw [← Carrier.sum_single v]
  rw [map_sum, Carrier.sum_apply, Finset.sum_eq_single i]
  · intro l _ hl
    rw [map_single g l, Carrier.single_apply_of_ne (Ne.symm hl)]
  · simp

/-- The functor from `𝒜`-modules to `A`-modules is fully faithful. -/
def fullyFaithfulToModule : (toModule k E).FullyFaithful where
  preimage := preimage
  map_preimage := map_preimage
  preimage_map {M N} f := by
    classical
    refine LinMod.hom_ext fun (i : ι) ↦ ?_
    ext m
    rw [preimage_app]
    change ((f.hom.app (of k E i)).hom (Carrier.single (M := M) i m i)) = _
    rw [Carrier.single_apply_self]

instance : (toModule k E).Full := (fullyFaithfulToModule (k := k) (E := E)).full

instance : (toModule k E).Faithful := (fullyFaithfulToModule (k := k) (E := E)).faithful

/-! ### Exactness and dimension -/

lemma injective_map_iff {N : LinMod k (AlgebraCategory k E)} (f : M ⟶ N) :
    Function.Injective ((toModule k E).map f).hom ↔
      ∀ i : ι, Function.Injective (f.hom.app (of k E i)).hom := by
  change Function.Injective (toModuleMap f) ↔ _
  constructor
  · intro h i m m' hm
    have := h (a₁ := Carrier.single (M := M) i m) (a₂ := Carrier.single (M := M) i m') (by
        refine Carrier.ext fun l ↦ ?_
        rw [toModuleMap_apply, toModuleMap_apply]
        by_cases hl : l = i
        · subst hl; simpa using hm
        · simp [Carrier.single_apply_of_ne hl])
    simpa using congrFun this i
  · intro h v v' hv
    exact Carrier.ext fun i ↦ h i (congrFun hv i)

lemma surjective_map_iff {N : LinMod k (AlgebraCategory k E)} (f : M ⟶ N) :
    Function.Surjective ((toModule k E).map f).hom ↔
      ∀ i : ι, Function.Surjective (f.hom.app (of k E i)).hom := by
  change Function.Surjective (toModuleMap f) ↔ _
  constructor
  · intro h i n
    obtain ⟨v, hv⟩ := h (Carrier.single (M := N) i n)
    refine ⟨v i, ?_⟩
    have := congrFun hv i
    rw [toModuleMap_apply, Carrier.single_apply_self] at this
    exact this
  · intro h w
    choose g hg using h
    exact ⟨fun i ↦ g i (w i), Carrier.ext fun i ↦ hg i (w i)⟩

lemma range_map_eq_ker_map {N P : LinMod k (AlgebraCategory k E)} (f : M ⟶ N) (g : N ⟶ P)
    (h : ∀ i : ι, LinearMap.range (f.hom.app (of k E i)).hom =
      LinearMap.ker (g.hom.app (of k E i)).hom) :
    LinearMap.range ((toModule k E).map f).hom = LinearMap.ker ((toModule k E).map g).hom := by
  change LinearMap.range (toModuleMap f) = LinearMap.ker (toModuleMap g)
  ext w
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨v, rfl⟩
    refine Carrier.ext fun i ↦ ?_
    rw [toModuleMap_apply, toModuleMap_apply]
    have : (f.hom.app (of k E i)).hom (v i) ∈ LinearMap.ker (g.hom.app (of k E i)).hom :=
      h i ▸ LinearMap.mem_range_self _ _
    exact this
  · intro hw
    have : ∀ i : ι, ∃ m, (f.hom.app (of k E i)).hom m = w i := fun i ↦ by
      have : w i ∈ LinearMap.ker (g.hom.app (of k E i)).hom := congrFun hw i
      rw [← h i] at this
      exact this
    choose v hv using this
    exact ⟨v, Carrier.ext hv⟩

variable (M)

/-- The underlying `k`-space of the `A`-module of `M` is `∏ᵢ M(i)`. -/
def restrictScalarsEquiv :
    RestrictScalars k A ((toModule k E).obj M) ≃ₗ[k] ∀ i : ι, M.obj.obj (of k E i) where
  toFun v := (RestrictScalars.addEquiv k A _ v : Carrier M)
  invFun v := (RestrictScalars.addEquiv k A _).symm (v : Carrier M)
  map_add' _ _ := rfl
  map_smul' c v := by
    have := RestrictScalars.addEquiv_map_smul (R := k) (S := A) (M := Carrier M) c v
    exact this.trans (algebraMap_smul A c _)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The `A`-module of an `𝒜`-module with finite-dimensional vertex spaces is
finite-dimensional. -/
lemma finite_toModule [∀ i : ι, Module.Finite k (M.obj.obj (of k E i))] :
    Module.Finite k (RestrictScalars k A ((toModule k E).obj M)) :=
  Module.Finite.equiv (restrictScalarsEquiv M).symm

/-- The dimension of the `A`-module of `M` is `∑ᵢ dim M(i)`. -/
lemma rank_toModule :
    Module.rank k (RestrictScalars k A ((toModule k E).obj M)) =
      Cardinal.sum fun i : ι ↦ Module.rank k (M.obj.obj (of k E i)) := by
  rw [(restrictScalarsEquiv M).rank_eq, rank_pi]

end AlgebraCategory

end LargeIndecomposable
