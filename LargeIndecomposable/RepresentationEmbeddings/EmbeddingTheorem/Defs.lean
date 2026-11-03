module

public import LargeIndecomposable.KroneckerModules.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# The colimit extension of a functor on `D_fin`

For a functor `Φ : D_fin → Mod A` and `T ∈ D`, put
`F(T) = colim_{U ⊆ T, dim U < ∞} Φ(U)`,
the right side of the colimit comparison (3.6). This file builds this functor
`Extension.functor Φ : D ⥤ Mod A`, indexing the colimit by the directed poset
`Kron.FinSub T` of finite-dimensional subrepresentations. The functors of
Theorem 3.14 are identified with such extensions (`Comparison.isoExtension`),
which gives their colimit and dimension properties.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A]

namespace Extension

/-- The diagram of finite-dimensional subrepresentations of `X ∈ D`, as
objects of `D_fin`. -/
def finDiagram (X : D k) : Kron.FinSub X.obj ⥤ Dfin k where
  obj U := ⟨U.1.toKron, U.1.inD X.2, U.2⟩
  map h := ObjectProperty.homMk (Kron.Sub.homOfLE (leOfHom h))
  map_id U := by ext1; exact Kron.Sub.homOfLE_refl U.1
  map_comp h h' := by ext1; exact (Kron.Sub.homOfLE_comp (leOfHom h) (leOfHom h')).symm

variable (Φ : Dfin k ⥤ ModuleCat.{u} A)

/-- The diagram `U ↦ Φ(U)`. -/
abbrev diag (X : D k) : Kron.FinSub X.obj ⥤ ModuleCat.{u} A := finDiagram X ⋙ Φ

/-- The value `F(X) = colim Φ(U)`. -/
abbrev obj (X : D k) : ModuleCat.{u} A := colimit (diag Φ X)

/-- The canonical map `Φ(U) → F(X)`. -/
abbrev ι (X : D k) (U : Kron.FinSub X.obj) : Φ.obj ((finDiagram X).obj U) ⟶ obj Φ X :=
  colimit.ι (diag Φ X) U

@[reassoc (attr := simp)]
lemma ι_w (X : D k) {U U' : Kron.FinSub X.obj} (h : U ≤ U') :
    Φ.map ((finDiagram X).map (homOfLE h)) ≫ ι Φ X U' = ι Φ X U :=
  colimit.w (diag Φ X) (homOfLE h)

/-- The restriction of `f : X ⟶ Y` to `U ⊆ X` and `U' ⊆ Y` with `f(U) ⊆ U'`,
as a morphism of `D_fin`. -/
def restrict {X Y : D k} (f : X ⟶ Y) (U : Kron.FinSub X.obj) (U' : Kron.FinSub Y.obj)
    (h : U.1.map f.hom ≤ U'.1) : (finDiagram X).obj U ⟶ (finDiagram Y).obj U' :=
  ObjectProperty.homMk (Kron.Sub.restrict f.hom U.1 U'.1 h)

lemma restrict_comp_map {X Y : D k} (f : X ⟶ Y) (U : Kron.FinSub X.obj)
    {U' U'' : Kron.FinSub Y.obj} (h : U.1.map f.hom ≤ U'.1) (hU : U' ≤ U'') :
    restrict f U U' h ≫ (finDiagram Y).map (homOfLE hU) = restrict f U U'' (h.trans hU) := by
  ext1; exact Kron.Sub.restrict_homOfLE f.hom U.1 h hU

lemma map_restrict_ι_of_le {X Y : D k} (f : X ⟶ Y) (U : Kron.FinSub X.obj)
    {U' U'' : Kron.FinSub Y.obj} (h : U.1.map f.hom ≤ U'.1) (hU : U' ≤ U'') :
    Φ.map (restrict f U U'' (h.trans hU)) ≫ ι Φ Y U'' = Φ.map (restrict f U U' h) ≫ ι Φ Y U' := by
  rw [← restrict_comp_map f U h hU, Φ.map_comp, Category.assoc, ι_w]

/-- `Φ(f|_U) ≫ ι_{U'}` does not depend on the choice of `U' ⊇ f(U)`. -/
lemma map_restrict_ι {X Y : D k} (f : X ⟶ Y) (U : Kron.FinSub X.obj)
    (U' U'' : Kron.FinSub Y.obj) (h : U.1.map f.hom ≤ U'.1) (h' : U.1.map f.hom ≤ U''.1) :
    Φ.map (restrict f U U' h) ≫ ι Φ Y U' = Φ.map (restrict f U U'' h') ≫ ι Φ Y U'' := by
  have e₁ := map_restrict_ι_of_le Φ f U (U' := Kron.FinSub.map f.hom U) le_rfl h
  have e₂ := map_restrict_ι_of_le Φ f U (U' := Kron.FinSub.map f.hom U) le_rfl h'
  exact e₁.trans e₂.symm

/-- The cocone used to define `F(f)`. -/
def mapCocone {X Y : D k} (f : X ⟶ Y) : Cocone (diag Φ X) where
  pt := obj Φ Y
  ι :=
    { app U := Φ.map (restrict f U (Kron.FinSub.map f.hom U) le_rfl) ≫
        ι Φ Y (Kron.FinSub.map f.hom U)
      naturality U₁ U₂ g := by
        have hle := leOfHom g
        simp only [Functor.const_obj_obj, Functor.comp_obj, Functor.comp_map,
          Functor.const_obj_map, Category.comp_id]
        rw [← Category.assoc, ← Φ.map_comp]
        have : (finDiagram X).map g ≫ restrict f U₂ (Kron.FinSub.map f.hom U₂) le_rfl =
            restrict f U₁ (Kron.FinSub.map f.hom U₂) (Kron.Sub.map_mono f.hom hle) := by
          ext1; exact Kron.Sub.homOfLE_restrict f.hom hle _ le_rfl
        rw [this]
        exact map_restrict_ι Φ f U₁ _ _ _ _ }

/-- `F(f)`. -/
def map {X Y : D k} (f : X ⟶ Y) : obj Φ X ⟶ obj Φ Y := colimit.desc (diag Φ X) (mapCocone Φ f)


@[reassoc]
lemma ι_map {X Y : D k} (f : X ⟶ Y) (U : Kron.FinSub X.obj) (U' : Kron.FinSub Y.obj)
    (h : U.1.map f.hom ≤ U'.1) :
    ι Φ X U ≫ map Φ f = Φ.map (restrict f U U' h) ≫ ι Φ Y U' := by
  exact (colimit.ι_desc (mapCocone Φ f) U).trans (map_restrict_ι Φ f U _ _ _ _)

lemma hom_ext' {X : D k} {M : ModuleCat.{u} A} {φ ψ : obj Φ X ⟶ M}
    (h : ∀ U, ι Φ X U ≫ φ = ι Φ X U ≫ ψ) : φ = ψ :=
  colimit.hom_ext h

/-- The extension `F : D ⥤ Mod A` of `Φ` by filtered colimits. -/
def functor : D k ⥤ ModuleCat.{u} A where
  obj := obj Φ
  map := map Φ
  map_id X := by
    refine hom_ext' Φ fun U ↦ ?_
    rw [ι_map Φ (𝟙 X) U U (Kron.Sub.map_id_le U.1), Category.comp_id]
    have : restrict (𝟙 X) U U (Kron.Sub.map_id_le U.1) = 𝟙 _ := by
      ext1; apply Kron.hom_ext <;> rfl
    rw [this, Φ.map_id, Category.id_comp]
  map_comp {X Y Z} f g := by
    refine hom_ext' Φ fun U ↦ ?_
    rw [ι_map Φ (f ≫ g) U (Kron.FinSub.map g.hom (Kron.FinSub.map f.hom U))
        (Kron.Sub.map_comp_le f.hom g.hom U.1),
      ι_map_assoc Φ f U (Kron.FinSub.map f.hom U) le_rfl,
      ι_map Φ g _ (Kron.FinSub.map g.hom (Kron.FinSub.map f.hom U)) le_rfl,
      ← Category.assoc, ← Φ.map_comp]
    congr 2
    ext1
    exact Kron.Sub.restrict_comp f.hom g.hom U.1 _ _ le_rfl le_rfl
      (Kron.Sub.map_comp_le f.hom g.hom U.1)

end Extension

end LargeIndecomposable
