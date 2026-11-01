module

public import LargeIndecomposable.Foundations.PathCategories.LinearPathCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor

@[expose] public section

/-!
# The universal realization of a free linear path category

A reversed quiver representation in a linear category assigns an object to
every vertex and a morphism `F j ⟶ F i` to every quiver arrow `i ⟶ j`.
Concatenating those representatives and extending linearly gives the expected
linear functor from the free linear path category.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.LinearPathCategory

universe u v w z

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]
variable {C : Type z} [CategoryTheory.Category C] [Preadditive C]
  [CategoryTheory.Linear k C]

/-- Evaluate a path under a reversed assignment of quiver arrows. -/
def pathMap (F₀ : Q → C)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i)) :
    ∀ {i j : Q}, Quiver.Path i j → (F₀ j ⟶ F₀ i)
  | _, _, .nil => 𝟙 _
  | _, _, .cons p a => F₁ a ≫ pathMap F₀ F₁ p

omit [Preadditive C] in
@[simp]
theorem pathMap_nil (F₀ : Q → C)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i)) (i : Q) :
    pathMap F₀ F₁ (Quiver.Path.nil : Quiver.Path i i) = 𝟙 (F₀ i) := by
  simp [pathMap]

omit [Preadditive C] in
@[simp]
theorem pathMap_cons (F₀ : Q → C)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    {i j l : Q} (p : Quiver.Path i j) (a : j ⟶ l) :
    pathMap F₀ F₁ (p.cons a) = F₁ a ≫ pathMap F₀ F₁ p := by
  simp [pathMap]

omit [Preadditive C] in
/-- Reversed path evaluation turns concatenation into categorical
composition. -/
theorem pathMap_comp (F₀ : Q → C)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    {i j l : Q} (p : Quiver.Path i j) (q : Quiver.Path j l) :
    pathMap F₀ F₁ (p.comp q) = pathMap F₀ F₁ q ≫ pathMap F₀ F₁ p := by
  induction q with
  | nil => simp
  | cons q a ih => simp [ih, Category.assoc]

/-- Linear extension of reversed path evaluation to a Hom space of the free
linear path category. -/
def homMap (F₀ : Q → C)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    (x y : Category k Q) :
    (x ⟶ y) →ₗ[k] (F₀ (vertex x) ⟶ F₀ (vertex y)) :=
  (Finsupp.linearCombination k fun p :
      Quiver.Path (vertex y) (vertex x) ↦ pathMap F₀ F₁ p).comp
    (homPathLinearEquiv x y).toLinearMap

@[simp]
theorem homMap_pathHom (F₀ : Q → C)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    {x y : Category k Q}
    (p : Quiver.Path (vertex y) (vertex x)) :
    homMap F₀ F₁ x y (pathHom p) = pathMap F₀ F₁ p := by
  simp [homMap]

/-- A scalar multiple of one path basis vector, transported back from the
Finsupp coordinates. -/
theorem homPathLinearEquiv_symm_single {x y : Category k Q}
    (p : Quiver.Path (vertex y) (vertex x)) (r : k) :
    (homPathLinearEquiv x y).symm (Finsupp.single p r) = r • pathHom p := by
  rw [← Finsupp.smul_single_one]
  exact (homPathLinearEquiv x y).symm.map_smul r (Finsupp.single p 1)

/-- The linear realization functor determined by a reversed assignment of
quiver arrows. -/
def lift (F₀ : Q → C)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i)) :
    Category k Q ⥤ C where
  obj x := F₀ (vertex x)
  map {x y} f := homMap F₀ F₁ x y f
  map_id x := by
    change homMap F₀ F₁ x x (𝟙 x) = 𝟙 (F₀ (vertex x))
    rw [← pathHom_nil x, homMap_pathHom, pathMap_nil]
  map_comp {x y z} f g := by
    let f' := homPathLinearEquiv x y f
    let g' := homPathLinearEquiv y z g
    rw [← (homPathLinearEquiv x y).symm_apply_apply f]
    rw [← (homPathLinearEquiv y z).symm_apply_apply g]
    change homMap F₀ F₁ x z
        ((homPathLinearEquiv x y).symm f' ≫
          (homPathLinearEquiv y z).symm g') =
      homMap F₀ F₁ x y ((homPathLinearEquiv x y).symm f') ≫
        homMap F₀ F₁ y z ((homPathLinearEquiv y z).symm g')
    induction f' using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ hf₁ hf₂ =>
        simp only [map_add, Preadditive.add_comp, hf₁, hf₂]
    | single p r =>
        induction g' using Finsupp.induction_linear with
        | zero => simp
        | add g₁ g₂ hg₁ hg₂ =>
            simp only [map_add, Preadditive.comp_add, hg₁, hg₂]
        | single q s =>
            rw [homPathLinearEquiv_symm_single,
              homPathLinearEquiv_symm_single]
            simp only [CategoryTheory.Linear.smul_comp,
              CategoryTheory.Linear.comp_smul, map_smul,
              LinearPathCategory.pathHom_comp, homMap_pathHom,
              pathMap_comp, smul_smul]

instance lift_additive (F₀ : Q → C)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i)) :
    (lift (k := k) F₀ F₁).Additive where
  map_add := by
    intro x y f g
    exact (homMap F₀ F₁ x y).map_add f g

instance lift_linear (F₀ : Q → C)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i)) :
    (lift (k := k) F₀ F₁).Linear k where
  map_smul f r := (homMap F₀ F₁ _ _).map_smul r f

@[simp]
theorem lift_obj (F₀ : Q → C)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    (x : Category k Q) :
    (lift (k := k) F₀ F₁).obj x = F₀ (vertex x) :=
  rfl

@[simp]
theorem lift_map_pathHom (F₀ : Q → C)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    {x y : Category k Q}
    (p : Quiver.Path (vertex y) (vertex x)) :
    (lift (k := k) F₀ F₁).map (pathHom p) = pathMap F₀ F₁ p := by
  simp [lift]

end LargeIndecomposable.LinearPathCategory
