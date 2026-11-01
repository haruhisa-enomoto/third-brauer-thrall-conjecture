module

public import LargeIndecomposable.RayCategories.Basic.Factor
public import Mathlib.CategoryTheory.Groupoid.FreeGroupoid
public import Mathlib.CategoryTheory.Quotient

/-!
# The fundamental groupoid of a ray category

The quiver of a ray category `P` has the irreducible morphisms as arrows
(`RayVert P`). Its fundamental groupoid is the free groupoid on this quiver
modulo the homotopy relation `v ≃ w` for paths `v, w` with the same nonzero
value in `P` (Gabriel–Roiter 14.1; Bongartz, *Indecomposables live in all
smaller lengths*, Section 2). The vertex groups are the fundamental groups
`Π(P, x)` that the universal cover of `P` realizes as deck groups.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe v u

namespace RayCat

variable (P : Type u) [Category.{v} P] [HasZeroMorphisms P]

/-- The vertices of the quiver of `P` (a type synonym, so that the arrows are
the irreducible morphisms rather than all morphisms). -/
def RayVert : Type u := P

variable {P} in
/-- The object of `P` underlying a vertex. -/
abbrev RayVert.out (x : RayVert P) : P := x

variable {P} in
/-- The vertex of an object of `P`. -/
abbrev RayVert.mk (x : P) : RayVert P := x

/-- The quiver of `P`: the arrows are the irreducible morphisms. -/
instance : Quiver (RayVert P) where
  Hom x y := {f : x.out ⟶ y.out // IsIrreducible f}

variable {P}

/-- The value in `P` of a path of the quiver. -/
def pathVal {x : RayVert P} : ∀ {y : RayVert P}, Quiver.Path x y → (x.out ⟶ y.out)
  | _, .nil => 𝟙 x.out
  | _, .cons p e => pathVal p ≫ e.1

/-- A path as a morphism of the free groupoid. -/
def pathFG {x : RayVert P} : ∀ {y : RayVert P}, Quiver.Path x y →
    ((Quiver.FreeGroupoid.of (RayVert P)).obj x ⟶ (Quiver.FreeGroupoid.of (RayVert P)).obj y)
  | _, .nil => 𝟙 _
  | _, .cons p e => pathFG p ≫ (Quiver.FreeGroupoid.of (RayVert P)).map e

/-- The homotopy relation: paths with the same nonzero value are identified. -/
inductive homotopy : HomRel (Quiver.FreeGroupoid (RayVert P))
  | path {x y : RayVert P} (p q : Quiver.Path x y) (h : pathVal p = pathVal q) (h0 : pathVal p ≠ 0) :
      homotopy (pathFG p) (pathFG q)

variable (P) in
/-- The fundamental groupoid of `P`. -/
abbrev FundGroupoid : Type u := CategoryTheory.Quotient (homotopy (P := P))

example : Groupoid (FundGroupoid P) := inferInstance

/-- Paths with the same nonzero value are homotopic. -/
lemma homotopic_of_pathVal_eq {x y : RayVert P} (p q : Quiver.Path x y) (h : pathVal p = pathVal q)
    (h0 : pathVal p ≠ 0) :
    (CategoryTheory.Quotient.functor homotopy).map (pathFG p) =
      (CategoryTheory.Quotient.functor homotopy).map (pathFG q) :=
  CategoryTheory.Quotient.sound _ (homotopy.path p q h h0)

lemma pathVal_comp {x y : RayVert P} (p : Quiver.Path x y) : ∀ {z : RayVert P}
    (q : Quiver.Path y z), pathVal (p.comp q) = pathVal p ≫ pathVal q
  | _, .nil => by simp [pathVal]
  | _, .cons q e => by
    rw [Quiver.Path.comp_cons, pathVal, pathVal, pathVal_comp p q, Category.assoc]

lemma pathFG_comp {x y : RayVert P} (p : Quiver.Path x y) : ∀ {z : RayVert P}
    (q : Quiver.Path y z), pathFG (p.comp q) = pathFG p ≫ pathFG q
  | _, .nil => by simp [pathFG]
  | _, .cons q e => by
    rw [Quiver.Path.comp_cons, pathFG, pathFG, pathFG_comp p q, Category.assoc]

variable [IsRayCategory P]

omit [IsRayCategory P] in
/-- Composites of irreducible morphisms are values of paths. -/
lemma exists_path_of_irrComp {y z : P} (f : y ⟶ z) (hf : IrrComp f) :
    ∃ p : Quiver.Path (RayVert.mk y) (RayVert.mk z), pathVal p = f := by
  induction hf with
  | @irr y z f hirr =>
    exact ⟨(Quiver.Path.nil).cons (⟨f, hirr⟩ : {f : RayVert.out (RayVert.mk y) ⟶ RayVert.out
      (RayVert.mk z) // IsIrreducible f}), Category.id_comp f⟩
  | @comp y z w g h _ _ ihg ihh =>
    obtain ⟨p, hp⟩ := ihg
    obtain ⟨q, hq⟩ := ihh
    exact ⟨p.comp q, by rw [pathVal_comp, hp, hq]⟩

/-- Every nonzero morphism of a ray category is the value of a path. -/
lemma exists_path {y z : P} (f : y ⟶ z) (hf : f ≠ 0) :
    ∃ p : Quiver.Path (RayVert.mk y) (RayVert.mk z), pathVal p = f := by
  by_cases hiso : IsIso f
  · have hyz : y = z := IsRayCategory.skeletal ⟨asIso f⟩
    subst hyz
    have e : 𝟙 y = f ≫ 𝟙 y ≫ inv f := by simp
    have hf1 := (IsRayCategory.eq_id_of_two_sided _ (IsRayCategory.id_ne_zero y) f (inv f) e).1
    exact ⟨Quiver.Path.nil, by rw [hf1]; rfl⟩
  · exact exists_path_of_irrComp f (IsRayCategory.irrComp f hf hiso)

/-- The homotopy class of a nonzero morphism. -/
def cls {y z : P} (f : y ⟶ z) (hf : f ≠ 0) :
    ((CategoryTheory.Quotient.mk (r := homotopy (P := P))
      ((Quiver.FreeGroupoid.of (RayVert P)).obj (RayVert.mk y))) ⟶
      CategoryTheory.Quotient.mk ((Quiver.FreeGroupoid.of (RayVert P)).obj (RayVert.mk z))) :=
  (CategoryTheory.Quotient.functor homotopy).map (pathFG (exists_path f hf).choose)

lemma cls_eq {y z : P} (f : y ⟶ z) (hf : f ≠ 0) (p : Quiver.Path (RayVert.mk y) (RayVert.mk z))
    (hp : pathVal p = f) : cls f hf = (CategoryTheory.Quotient.functor homotopy).map (pathFG p) :=
  homotopic_of_pathVal_eq _ _ ((exists_path f hf).choose_spec.trans hp.symm)
    (by rw [(exists_path f hf).choose_spec]; exact hf)

/-- The class of a nonzero composite is the composite of the classes. -/
lemma cls_comp {y z w : P} (f : y ⟶ z) (g : z ⟶ w) (hfg : f ≫ g ≠ 0) :
    cls (f ≫ g) hfg = cls f (fun h ↦ hfg (by rw [h, zero_comp])) ≫
      cls g (fun h ↦ hfg (by rw [h, comp_zero])) := by
  have hf : f ≠ 0 := fun h ↦ hfg (by rw [h, zero_comp])
  have hg : g ≠ 0 := fun h ↦ hfg (by rw [h, comp_zero])
  obtain ⟨p, hp⟩ := exists_path f hf
  obtain ⟨q, hq⟩ := exists_path g hg
  rw [cls_eq f hf p hp, cls_eq g hg q hq, cls_eq _ hfg (p.comp q) (by rw [pathVal_comp, hp, hq]),
    pathFG_comp, Functor.map_comp]

end RayCat

end LargeIndecomposable
