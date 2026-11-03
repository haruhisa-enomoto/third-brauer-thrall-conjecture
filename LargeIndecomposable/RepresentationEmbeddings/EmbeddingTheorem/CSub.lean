module

public import LargeIndecomposable.RepresentationEmbeddings.EmbeddingTheorem.Defs
public import LargeIndecomposable.KroneckerModules.Glue

/-!
# The subcategory `C`

`C` is the full subcategory of `D` of Kronecker modules with neither simple
module as a direct summand (Definition 2.1).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A]

/-- The subcategory `C` of `D`. -/
abbrev InCD : ObjectProperty (D k) := fun X ↦ InC X.obj

/-- The underlying Kronecker morphism of a morphism of `C`. -/
abbrev InCD.kh {X Y : (InCD (k := k)).FullSubcategory} (f : X ⟶ Y) : X.obj.obj ⟶ Y.obj.obj :=
  f.hom.hom

end LargeIndecomposable
