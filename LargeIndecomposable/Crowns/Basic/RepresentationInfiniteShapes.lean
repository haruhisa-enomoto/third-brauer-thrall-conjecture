module

public import LargeIndecomposable.Crowns.Lemma8.Statement
public import LargeIndecomposable.Cleaving.Shapes.ShapeF93
public import LargeIndecomposable.Cleaving.Families.FamF63
public import LargeIndecomposable.Cleaving.Families.FamF64
public import LargeIndecomposable.Cleaving.Families.FamF66
public import LargeIndecomposable.Cleaving.Families.FamF67
public import LargeIndecomposable.Cleaving.Families.FamF68
public import LargeIndecomposable.Cleaving.Families.FamF610
public import LargeIndecomposable.Cleaving.Families.FamF611
public import LargeIndecomposable.Cleaving.Families.FamF612
public import LargeIndecomposable.Cleaving.Families.FamF617
public import LargeIndecomposable.Cleaving.Families.FamF73
public import LargeIndecomposable.Cleaving.Families.FamF83
public import LargeIndecomposable.Cleaving.Families.FamF84
public import LargeIndecomposable.Cleaving.Families.FamF8R1D
public import LargeIndecomposable.Cleaving.Families.FamF86
public import LargeIndecomposable.Cleaving.Families.FamF87
public import LargeIndecomposable.Cleaving.Families.FamF810
public import LargeIndecomposable.Cleaving.Families.FamF810D
public import LargeIndecomposable.Cleaving.Families.FamF93

/-!
# The representation-infinite shapes of BO13a §2.2

Every thin category used as a cleaving source in BO13a Lemmas 6–8 and §2.2.5
is representation-infinite over an infinite field (`Ray/Fam*.lean`: explicit
one-parameter families of bricks).
-/

@[expose] public section

set_option autoImplicit false

namespace LargeIndecomposable

open RayCat

universe u

namespace RayQuiver

namespace MulBasis

variable (k : Type u) [Field k] [Infinite k]

/-- The shapes of BO13a Lemma 6. -/
theorem l6Shapes : L6Shapes k :=
  ⟨F63.not_isRepresentationFinite, F64.not_isRepresentationFinite,
    F66.not_isRepresentationFinite, F67.not_isRepresentationFinite,
    F68.not_isRepresentationFinite, F610.not_isRepresentationFinite,
    F611.not_isRepresentationFinite, F612.not_isRepresentationFinite,
    F617.not_isRepresentationFinite⟩

/-- The shapes of BO13a Lemmas 7 and 8. -/
theorem l8Shapes : L8Shapes k :=
  ⟨F73.not_isRepresentationFinite, F83.not_isRepresentationFinite,
    F84.not_isRepresentationFinite, F8R1D.not_isRepresentationFinite,
    F86.not_isRepresentationFinite, F87.not_isRepresentationFinite,
    F810.not_isRepresentationFinite, F810D.not_isRepresentationFinite⟩

/-- GR category 12 (BO13a figure 9.3). -/
theorem f93Shape : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F93.thin) k) :=
  F93.not_isRepresentationFinite

end MulBasis

end RayQuiver

end LargeIndecomposable
