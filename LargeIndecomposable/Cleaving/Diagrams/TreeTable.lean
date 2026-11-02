module

public import LargeIndecomposable.Cleaving.Diagrams.TreeShapes

/-!
# Tree diagrams given by a table of path values

For an oriented tree, the value of every path from `a` to `b` is read off a
table `M a b : Option (obj a ⟶ obj b)` that is closed under appending arrows
(`RayCat.OT.pval_eq_of_table`). This turns the cleaving conditions of
`MulBasis.not_ot_diagram` into conditions on vertices only
(`MulBasis.not_tree_table`). `RayCat.copyOf` builds a graph copy of a quiver
from a vertex map.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

/-- A graph copy of the underlying graph of a quiver from a vertex map. -/
def copyOf {Q V : Type} [Quiver Q] (G : SimpleGraph V) (f : Q → V) (hf : Function.Injective f)
    (hadj : ∀ a b : Q, (a ⟶ b) → G.Adj (f a) (f b)) :
    (LargeIndecomposable.Foundations.Quiver.underlyingGraph Q).Copy G where
  toHom := ⟨f, fun {a b} h ↦ by
    rcases (LargeIndecomposable.Foundations.Quiver.underlyingGraph_adj.1 h).2 with ⟨e⟩ | ⟨e⟩
    · exact hadj a b e.some
    · exact (hadj b a e.some).symm⟩
  injective' := hf

namespace OT

variable {V : Type} {G : SimpleGraph V} {o : V → V → Prop}

/-- The prefunctor of a diagram given by objects and arrows. -/
def diag {P : Type} [Category.{0} P] (obj : V → P) (arr : ∀ a b, o a b → (obj a ⟶ obj b)) :
    OT G o ⥤q P where
  obj u := obj u.as
  map {u w} e := arr u.as w.as (hom_down e)

/-- **Path values from a table.** -/
lemma pval_eq_of_table {P : Type} [Category.{0} P] (obj : V → P)
    (arr : ∀ a b, o a b → (obj a ⟶ obj b)) (M : ∀ a b : V, Option (obj a ⟶ obj b))
    (hid : ∀ a, M a a = some (𝟙 _))
    (hstep : ∀ a b c (h : o b c) f, M a b = some f → M a c = some (f ≫ arr b c h)) {a b : OT G o}
    (p : Quiver.Path a b) : M a.as b.as = some (pval (diag (G := G) obj arr) p) := by
  induction p with
  | nil => exact hid a.as
  | cons p e ih => exact hstep _ _ _ (hom_down e) _ ih

end OT

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **No tree cleaving diagram in `P/τ`**, conditions on vertices. -/
theorem not_tree_table
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (o : V → V → Prop) (ho : ∀ a b, o a b → G.Adj a b) (hasym : ∀ a b, o a b → ¬o b a)
    (hG : G.IsAcyclic) [Fact (LargeIndecomposable.Foundations.Quiver.IsAcyclic (OT G o))]
    (hD : ¬Statement.IsRepresentationFinite (Linearization (PathCat (OT G o)) k))
    (obj : V → P) (arr : ∀ a b, o a b → (obj a ⟶ obj b)) (M : ∀ a b : V, Option (obj a ⟶ obj b))
    (hid : ∀ a, M a a = some (𝟙 _))
    (hstep : ∀ a b c (h : o b c) f, M a b = some f → M a c = some (f ≫ arr b c h))
    (h0 : ∀ x y f, M x y = some f → x ≠ y → ¬FactorsThroughMorphism τ f)
    (hiso : ∀ x y (h : o x y), ¬IsIso (arr x y h))
    (hl : ∀ x c c' y (h : o x c) (h' : o x c') f, c ≠ c' → M c' y = some f →
      ¬∃ g, arr x c h ≫ g = arr x c' h' ≫ f)
    (hr : ∀ x c c' y (h : o c y) (h' : o c' y) f, c ≠ c' → M x c' = some f →
      ¬∃ g, g ≫ arr c y h = f ≫ arr c' y h') : False := by
  have hne : ∀ u w : OT G o, u ≠ w → u.as ≠ w.as := fun u w h h' ↦ h (by
    cases u; cases w; simp_all)
  refine B.not_ot_diagram hmin hL hR τ hτ hτ0 G o ho hasym hG hD (OT.diag obj arr) ?_ ?_ ?_ ?_
  · intro x y p hp
    refine h0 _ _ _ (OT.pval_eq_of_table obj arr M hid hstep p) fun hxy ↦ ?_
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    change x = y at hxy
    subst hxy
    have := OT.path_eq ho hasym hG p .nil
    subst this
    simp at hp
  · intro x y e
    exact hiso _ _ _
  · intro x c c' y e e' q hcc
    have := hl x.as c.as c'.as y.as (OT.hom_down e) (OT.hom_down e') _ (hne _ _ hcc)
      (OT.pval_eq_of_table obj arr M hid hstep q)
    rintro ⟨g, hg⟩
    refine this ⟨g, ?_⟩
    change (OT.diag obj arr).map e ≫ g = _
    rw [hg]
    simp [pval, Prefunctor.mapPath_comp, composePath_comp]
    rfl
  · intro x c c' y e e' q hcc
    exact hr x.as c.as c'.as y.as (OT.hom_down e) (OT.hom_down e') _ (hne _ _ hcc)
      (OT.pval_eq_of_table obj arr M hid hstep q)

end MulBasis

end RayQuiver

end LargeIndecomposable
