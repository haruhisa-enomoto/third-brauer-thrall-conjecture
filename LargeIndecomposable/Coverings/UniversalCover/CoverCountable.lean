module

public import LargeIndecomposable.Coverings.UniversalCover.Cover

/-!
# The universal cover of a finite ray category is countable

Paths of a quiver with countably many vertices and arrows are countable (`countable_path`,
via the list of their arrows); hence so are the morphisms of the free groupoid, of the
fundamental groupoid, and the objects of the universal cover (`countable_cover`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

/-- The arrows of a path, as a list. -/
def arrList {V : Type*} [Quiver V] {a : V} : ∀ {b : V}, Quiver.Path a b → List (Σ x y : V, x ⟶ y)
  | _, .nil => []
  | _, .cons p e => ⟨_, _, e⟩ :: arrList p

lemma arrList_injective {V : Type*} [Quiver V] {a : V} :
    ∀ {b : V} (p q : Quiver.Path a b), arrList p = arrList q → p = q
  | _, .nil, .nil, _ => rfl
  | _, .nil, .cons _ _, h => by simp [arrList] at h
  | _, .cons _ _, .nil, h => by simp [arrList] at h
  | _, .cons (b := y₁) p e, .cons (b := y₂) q e', h => by
    simp only [arrList, List.cons.injEq, Sigma.mk.inj_iff] at h
    obtain ⟨⟨rfl, h2⟩, h3⟩ := h
    have h4 : e = e' := by
      simp only [heq_eq_eq, Sigma.mk.inj_iff, true_and] at h2
      exact h2
    subst h4
    rw [arrList_injective p q h3]

lemma countable_path {V : Type*} [Quiver V] [Countable V] [∀ a b : V, Countable (a ⟶ b)]
    (a b : V) : Countable (Quiver.Path a b) :=
  Function.Injective.countable (f := arrList) fun p q h ↦ arrList_injective p q h

lemma countable_freeGroupoid_hom {V : Type*} [Quiver V] [Countable V]
    [∀ a b : V, Countable (a ⟶ b)] (X Y : Quiver.FreeGroupoid V) : Countable (X ⟶ Y) := by
  haveI : ∀ a b : Quiver.Symmetrify V, Countable (a ⟶ b) := fun (a b : V) ↦
    (inferInstance : Countable ((a ⟶ b) ⊕ (b ⟶ a)))
  haveI : Countable (Quiver.Symmetrify V) := inferInstanceAs (Countable V)
  haveI := countable_path (V := Quiver.Symmetrify V) X.as Y.as
  exact inferInstanceAs (Countable (Quot _))

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Finite P]

lemma countable_fund_hom (X Y : FundGroupoid P) : Countable (X ⟶ Y) := by
  haveI : ∀ a b : RayVert P, Countable (a ⟶ b) := fun (a b : P) ↦
    haveI := IsRayCategory.finite_hom a b
    (inferInstance : Countable {f : a ⟶ b // IsIrreducible f})
  haveI : Countable (RayVert P) := inferInstanceAs (Countable P)
  haveI := countable_freeGroupoid_hom (V := RayVert P) X.as Y.as
  exact inferInstanceAs (Countable (Quot _))

/-- **The universal cover of a finite ray category is countable.** -/
instance countable_cover (x₀ : P) : Countable (Cover x₀) := by
  haveI : ∀ y : P, Countable (vtx x₀ ⟶ vtx y) := fun y ↦ countable_fund_hom _ _
  refine Function.Injective.countable (f := fun c : Cover x₀ ↦ (⟨c.y, c.u⟩ : Σ y, vtx x₀ ⟶ vtx y))
    ?_
  rintro ⟨y, u⟩ ⟨y', u'⟩ h
  simp only [Sigma.mk.inj_iff] at h
  obtain ⟨rfl, h⟩ := h
  rw [eq_of_heq h]

end LargeIndecomposable.RayCat
