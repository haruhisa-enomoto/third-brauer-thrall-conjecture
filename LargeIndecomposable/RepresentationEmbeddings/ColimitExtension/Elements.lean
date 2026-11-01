module

public import LargeIndecomposable.RepresentationEmbeddings.ColimitExtension.Defs
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures

/-!
# Elements of the colimit extension

Elementwise description of `F(X) = colim_{U} Φ(U)` (manuscript (1.1)): every
element comes from some `Φ(U)`, and an element of `Φ(U)` vanishes in `F(X)`
exactly when it vanishes in some `Φ(U')` with `U ⊆ U'`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A]

/-- A module that is finite-dimensional over `k` is finitely generated over
`A`. -/
lemma finite_of_restrictScalars [Algebra k A] {M : Type u} [AddCommGroup M]
    [Module A M] (h : Module.Finite k (RestrictScalars k A M)) : Module.Finite A M := by
  let := RestrictScalars.moduleOrig k A M
  exact Module.Finite.of_restrictScalars_finite k A (RestrictScalars k A M)

namespace Extension

variable (Φ : Dfin k ⥤ ModuleCat.{u} A)

/-- The canonical map `Φ(U) → F(X)`, with target `(functor Φ).obj X`. -/
abbrev ιF (X : D k) (U : Kron.FinSub X.obj) : Φ.obj ((finDiagram X).obj U) ⟶ (functor Φ).obj X :=
  ι Φ X U

/-- Every element of `F(X)` comes from some `Φ(U)`. -/
lemma exists_rep (X : D k) (x : (functor Φ).obj X) :
    ∃ (U : Kron.FinSub X.obj) (y : Φ.obj ((finDiagram X).obj U)), (ιF Φ X U).hom y = x :=
  Concrete.colimit_exists_rep (diag Φ X) x

/-- Every element of `F(X)` comes from some `Φ(U')` with `U' ⊇ U`. -/
lemma exists_rep_ge (X : D k) (U : Kron.FinSub X.obj) (x : (functor Φ).obj X) :
    ∃ (U' : Kron.FinSub X.obj) (_ : U ≤ U') (y : Φ.obj ((finDiagram X).obj U')),
      (ιF Φ X U').hom y = x := by
  obtain ⟨U', h, y, hy⟩ :=
    Concrete.exists_hom_ι_eq_of_isColimit (diag Φ X) (colimit.isColimit _) x U
  exact ⟨U', leOfHom h, y, hy⟩

lemma ιF_apply_of_le (X : D k) {U U' : Kron.FinSub X.obj} (h : U ≤ U')
    (y : Φ.obj ((finDiagram X).obj U)) :
    (ιF Φ X U').hom ((Φ.map ((finDiagram X).map (homOfLE h))).hom y) = (ιF Φ X U).hom y := by
  change (Φ.map ((finDiagram X).map (homOfLE h)) ≫ ι Φ X U').hom y = _
  rw [ι_w]
  rfl

/-- An element of `Φ(U)` vanishes in `F(X)` iff it vanishes in some `Φ(U')`,
`U ⊆ U'`. -/
lemma ιF_eq_zero_iff (X : D k) (U : Kron.FinSub X.obj) (y : Φ.obj ((finDiagram X).obj U)) :
    (ιF Φ X U).hom y = 0 ↔
      ∃ (U' : Kron.FinSub X.obj) (h : U ≤ U'),
        (Φ.map ((finDiagram X).map (homOfLE h))).hom y = 0 := by
  constructor
  · intro hy
    obtain ⟨U', i, hi⟩ := Concrete.colimit_rep_eq_zero A (diag Φ X) U y hy
    exact ⟨U', leOfHom i, hi⟩
  · rintro ⟨U', h, hy⟩
    rw [← ιF_apply_of_le Φ X h, hy, map_zero]

/-- Two elements of `Φ(U)` and `Φ(U')` agree in `F(X)` iff they agree in some
common `Φ(U'')`. -/
lemma ιF_eq_iff (X : D k) (U U' : Kron.FinSub X.obj) (y : Φ.obj ((finDiagram X).obj U))
    (y' : Φ.obj ((finDiagram X).obj U')) :
    (ιF Φ X U).hom y = (ιF Φ X U').hom y' ↔
      ∃ (U'' : Kron.FinSub X.obj) (h : U ≤ U'') (h' : U' ≤ U''),
        (Φ.map ((finDiagram X).map (homOfLE h))).hom y =
          (Φ.map ((finDiagram X).map (homOfLE h'))).hom y' := by
  constructor
  · intro hy
    obtain ⟨U'', i, i', hi⟩ := Concrete.colimit_exists_of_rep_eq (diag Φ X) y y' hy
    exact ⟨U'', leOfHom i, leOfHom i', hi⟩
  · rintro ⟨U'', h, h', hy⟩
    rw [← ιF_apply_of_le Φ X h, ← ιF_apply_of_le Φ X h', hy]

lemma ιF_map {X Y : D k} (f : X ⟶ Y) (U : Kron.FinSub X.obj) (U' : Kron.FinSub Y.obj)
    (h : U.1.map f.hom ≤ U'.1) :
    ιF Φ X U ≫ (functor Φ).map f = Φ.map (restrict f U U' h) ≫ ιF Φ Y U' :=
  ι_map Φ f U U' h

/-- `F(f)` on a representative. -/
lemma map_ιF_apply {X Y : D k} (f : X ⟶ Y) (U : Kron.FinSub X.obj) (U' : Kron.FinSub Y.obj)
    (h : U.1.map f.hom ≤ U'.1) (y : Φ.obj ((finDiagram X).obj U)) :
    ((functor Φ).map f).hom ((ιF Φ X U).hom y) =
      (ιF Φ Y U').hom ((Φ.map (restrict f U U' h)).hom y) := by
  rw [← ModuleCat.comp_apply, ιF_map Φ f U U' h, ModuleCat.comp_apply]

lemma ιF_hom_ext {X : D k} {M : ModuleCat.{u} A} {φ ψ : (functor Φ).obj X ⟶ M}
    (h : ∀ U, ιF Φ X U ≫ φ = ιF Φ X U ≫ ψ) : φ = ψ :=
  hom_ext' Φ h

/-- A morphism from a finite-dimensional module that vanishes in `F(X)`
already vanishes in some `Φ(U')`: finite-dimensional modules are finitely
generated. -/
lemma exists_comp_eq_zero [Algebra k A] (X : D k) {M : ModuleCat.{u} A}
    (hM : Module.Finite k (RestrictScalars k A M)) (U : Kron.FinSub X.obj)
    (φ : M ⟶ Φ.obj ((finDiagram X).obj U)) (hφ : φ ≫ ιF Φ X U = 0) :
    ∃ (U' : Kron.FinSub X.obj) (h : U ≤ U'), φ ≫ Φ.map ((finDiagram X).map (homOfLE h)) = 0 := by
  classical
  have : Module.Finite A M := finite_of_restrictScalars hM
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := M)
  have h0 : ∀ m : M, (ιF Φ X U).hom (φ.hom m) = 0 := fun m ↦ by
    rw [← ModuleCat.comp_apply, hφ]; rfl
  choose g hg hg0 using fun m ↦ (ιF_eq_zero_iff Φ X U (φ.hom m)).1 (h0 m)
  obtain ⟨U', hU'⟩ := Finset.exists_le (insert U (s.image g))
  have hle : U ≤ U' := hU' _ (Finset.mem_insert_self _ _)
  refine ⟨U', hle, ?_⟩
  ext1
  refine LinearMap.ext_on hs fun m hm ↦ ?_
  have hgU : g m ≤ U' := hU' _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hm))
  have : (finDiagram X).map (homOfLE hle) =
      (finDiagram X).map (homOfLE (hg m)) ≫ (finDiagram X).map (homOfLE hgU) := by
    rw [← Functor.map_comp]; rfl
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, this, Φ.map_comp, hg0, map_zero,
    ModuleCat.hom_zero, LinearMap.zero_apply]

end Extension

end LargeIndecomposable
