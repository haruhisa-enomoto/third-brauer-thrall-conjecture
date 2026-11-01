module

public import LargeIndecomposable.FundamentalGroups.Basic.Fundamental
public import Mathlib

/-!
# Integer cocycles on ray categories

An integer weight `c` on the arrows of the quiver of a ray category such that two
paths with the same nonzero value have the same total weight (`IsCocycle`) induces a
functor from the fundamental groupoid to the integers (`cocycleFunctor`). Hence a walk
of nonzero total weight is not null-homotopic (`not_trivial_of_weight`).

Cocycles detect simple connectedness: in a simply connected ray category every cocycle is
a coboundary (`isCoboundary_of_simplyConnected`); conversely, a nontrivial homomorphism
from the fundamental group to `ℤ` gives a cocycle that is not a coboundary
(`not_isCoboundary_homCocycle`), so a free fundamental group is trivial as soon as every
cocycle is a coboundary (`eq_one_of_forall_isCoboundary`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

universe v u

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P]

/-- An integer weight on the arrows. -/
abbrev ArrowWeight (P : Type u) [Category.{v} P] [HasZeroMorphisms P] : Type _ :=
  ∀ {x y : RayVert P}, (x ⟶ y) → ℤ

/-- The total weight of a path. -/
def pathWeight (c : ArrowWeight P) {x : RayVert P} : ∀ {y : RayVert P}, Quiver.Path x y → ℤ
  | _, .nil => 0
  | _, .cons p e => pathWeight c p + c e

/-- Paths with the same nonzero value have the same weight. -/
def IsCocycle (c : ArrowWeight P) : Prop :=
  ∀ {x y : RayVert P} (p q : Quiver.Path x y), pathVal p = pathVal q → pathVal p ≠ 0 →
    pathWeight c p = pathWeight c q

/-- The weight as a prefunctor into the integers (a one-object groupoid). -/
def weightPrefunctor (c : ArrowWeight P) : RayVert P ⥤q SingleObj (Multiplicative ℤ) where
  obj _ := SingleObj.star _
  map e := Multiplicative.ofAdd (c e)

/-- The weight on the free groupoid. -/
def freeWeight (c : ArrowWeight P) : Quiver.FreeGroupoid (RayVert P) ⥤ SingleObj (Multiplicative ℤ) :=
  Quiver.FreeGroupoid.lift (weightPrefunctor c)

lemma freeWeight_pathFG (c : ArrowWeight P) {x : RayVert P} :
    ∀ {y : RayVert P} (p : Quiver.Path x y),
      (freeWeight c).map (pathFG p) = Multiplicative.ofAdd (pathWeight c p)
  | _, .nil => by simp [pathFG, pathWeight]; rfl
  | _, .cons p e => by
    rw [pathFG, CategoryTheory.Functor.map_comp, freeWeight_pathFG c p, pathWeight]
    have h2 : (freeWeight c).map ((Quiver.FreeGroupoid.of (RayVert P)).map e) =
        Multiplicative.ofAdd (c e) := by
      have h := Quiver.FreeGroupoid.lift_spec (weightPrefunctor c)
      exact congrArg (fun (F : RayVert P ⥤q SingleObj (Multiplicative ℤ)) ↦
        (F.map e : Multiplicative ℤ)) h
    rw [h2, SingleObj.comp_as_mul, ← ofAdd_add, add_comm]

/-- **A cocycle induces a functor on the fundamental groupoid.** -/
def cocycleFunctor (c : ArrowWeight P) (hc : IsCocycle c) :
    FundGroupoid P ⥤ SingleObj (Multiplicative ℤ) :=
  CategoryTheory.Quotient.lift homotopy (freeWeight c) fun _ _ _ _ h ↦ by
    cases h with
    | path p q hpq h0 => rw [freeWeight_pathFG, freeWeight_pathFG, hc p q hpq h0]

lemma cocycleFunctor_map (c : ArrowWeight P) (hc : IsCocycle c) {X Y}
    (f : X ⟶ Y) :
    (cocycleFunctor c hc).map ((CategoryTheory.Quotient.functor homotopy).map f) =
      (freeWeight c).map f :=
  CategoryTheory.Quotient.lift_map_functor_map _ _ _ f

/-- **A closed walk of nonzero weight is not null-homotopic.** -/
theorem not_trivial_of_weight (c : ArrowWeight P) (hc : IsCocycle c) {X : Quiver.FreeGroupoid (RayVert P)}
    (w : X ⟶ X) (hw : (freeWeight c).map w ≠ 1) :
    (CategoryTheory.Quotient.functor homotopy).map w ≠ 𝟙 _ := by
  intro h
  apply hw
  have := cocycleFunctor_map c hc w
  rw [h, CategoryTheory.Functor.map_id] at this
  exact this.symm

/-- A coboundary: the weight of an arrow is the difference of a potential. -/
def IsCoboundary (c : ArrowWeight P) : Prop :=
  ∃ φ : RayVert P → ℤ, ∀ {x y : RayVert P} (e : x ⟶ y), c e = φ y - φ x

/-- The vertex of the fundamental groupoid of a quiver vertex. -/
abbrev fvtx (x : RayVert P) : FundGroupoid P :=
  CategoryTheory.Quotient.mk ((Quiver.FreeGroupoid.of (RayVert P)).obj x)

/-- The class of an arrow in the fundamental groupoid. -/
abbrev arrCls {x y : RayVert P} (e : x ⟶ y) : fvtx x ⟶ fvtx y :=
  (CategoryTheory.Quotient.functor homotopy).map ((Quiver.FreeGroupoid.of (RayVert P)).map e)

/-- **In a simply connected ray category every cocycle is a coboundary**: if all
parallel morphisms of the fundamental groupoid agree, the weight of an arrow is the
difference of the weights of chosen morphisms from a base point. -/
theorem isCoboundary_of_simplyConnected (c : ArrowWeight P) (hc : IsCocycle c)
    (x₀ : RayVert P) (hpath : ∀ y : RayVert P, Nonempty (fvtx x₀ ⟶ fvtx y))
    (hsc : ∀ (X Y : FundGroupoid P) (f g : X ⟶ Y), f = g) : IsCoboundary c := by
  let F := cocycleFunctor c hc
  let φ : RayVert P → ℤ := fun y ↦ Multiplicative.toAdd (F.map (hpath y).some)
  refine ⟨φ, fun {x y} e ↦ ?_⟩
  have h1 : (hpath x).some ≫ arrCls e = (hpath y).some := hsc _ _ _ _
  have h2 := congrArg F.map h1
  rw [CategoryTheory.Functor.map_comp, SingleObj.comp_as_mul] at h2
  have h3 : F.map (arrCls e) = Multiplicative.ofAdd (c e) := by
    change (cocycleFunctor c hc).map ((CategoryTheory.Quotient.functor homotopy).map
      ((Quiver.FreeGroupoid.of (RayVert P)).map e)) = _
    rw [cocycleFunctor_map]
    have h := Quiver.FreeGroupoid.lift_spec (weightPrefunctor c)
    exact congrArg (fun (G : RayVert P ⥤q SingleObj (Multiplicative ℤ)) ↦
      (G.map e : Multiplicative ℤ)) h
  rw [h3] at h2
  have h4 : Multiplicative.toAdd (Multiplicative.ofAdd (c e) * F.map (hpath x).some) =
      Multiplicative.toAdd (F.map (hpath y).some) := congrArg Multiplicative.toAdd h2
  rw [toAdd_mul, toAdd_ofAdd] at h4
  change c e = Multiplicative.toAdd (F.map (hpath y).some) -
    Multiplicative.toAdd (F.map (hpath x).some)
  omega

section Converse

/-- The underlying quiver vertex of a vertex of the free groupoid. -/
def fgv (a : Quiver.FreeGroupoid (RayVert P)) : RayVert P := a.as

/-- The functor of a potential: a morphism `a ⟶ b` has value `φ b - φ a`. -/
def potFunctor (φ : RayVert P → ℤ) :
    Quiver.FreeGroupoid (RayVert P) ⥤ SingleObj (Multiplicative ℤ) where
  obj _ := SingleObj.star _
  map {a b} _ := Multiplicative.ofAdd (φ (fgv b) - φ (fgv a))
  map_id a := by rw [sub_self]; rfl
  map_comp {a b c} _ _ := by
    rw [SingleObj.comp_as_mul, ← ofAdd_add]; congr 1; ring

/-- The weight of a coboundary is the functor of its potential. -/
lemma freeWeight_eq_potFunctor (c : ArrowWeight P) (φ : RayVert P → ℤ)
    (hφ : ∀ {x y : RayVert P} (e : x ⟶ y), c e = φ y - φ x) :
    freeWeight c = potFunctor φ := by
  refine (Quiver.FreeGroupoid.lift_unique (weightPrefunctor c) (potFunctor φ)
    (Prefunctor.ext (V := RayVert P) (fun _ ↦ rfl) fun x y e ↦ ?_)).symm
  change Multiplicative.ofAdd (φ y - φ x) = Multiplicative.ofAdd (c e)
  rw [hφ e]

variable (x₀ : RayVert P) (γ : ∀ X : FundGroupoid P, fvtx x₀ ⟶ X)
  (h : End (fvtx x₀) →* Multiplicative ℤ)

/-- A morphism of the fundamental groupoid, transported to the base point. -/
def conj {X Y : FundGroupoid P} (f : X ⟶ Y) : End (fvtx x₀) := γ X ≫ f ≫ inv (γ Y)

lemma conj_comp {X Y Z : FundGroupoid P} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conj x₀ γ (f ≫ g) = conj x₀ γ g * conj x₀ γ f := by
  rw [End.mul_def]
  simp [conj, Category.assoc]

lemma conj_id (X : FundGroupoid P) : conj x₀ γ (𝟙 X) = 1 := by
  change γ X ≫ 𝟙 X ≫ inv (γ X) = 𝟙 _
  simp

/-- The functor of a homomorphism of the fundamental group. -/
def homFunctor : FundGroupoid P ⥤ SingleObj (Multiplicative ℤ) where
  obj _ := SingleObj.star _
  map f := h (conj x₀ γ f)
  map_id X := by rw [conj_id, map_one]; rfl
  map_comp f g := by rw [conj_comp, map_mul, SingleObj.comp_as_mul]

/-- The cocycle of a homomorphism of the fundamental group. -/
def homCocycle : ArrowWeight P := fun e ↦ Multiplicative.toAdd (h (conj x₀ γ (arrCls e)))

lemma freeWeight_homCocycle :
    freeWeight (homCocycle x₀ γ h) =
      CategoryTheory.Quotient.functor homotopy ⋙ homFunctor x₀ γ h := by
  refine (Quiver.FreeGroupoid.lift_unique (weightPrefunctor (homCocycle x₀ γ h))
    (CategoryTheory.Quotient.functor homotopy ⋙ homFunctor x₀ γ h)
    (Prefunctor.ext (V := RayVert P) (fun _ ↦ rfl) fun x y e ↦ ?_)).symm
  change h (conj x₀ γ (arrCls e)) = Multiplicative.ofAdd (Multiplicative.toAdd _)
  rfl

lemma isCocycle_homCocycle : IsCocycle (homCocycle x₀ γ h) := by
  intro x y p q hpq h0
  have e := congrArg (homFunctor x₀ γ h).map (homotopic_of_pathVal_eq p q hpq h0)
  have ep := freeWeight_pathFG (homCocycle x₀ γ h) p
  have eq := freeWeight_pathFG (homCocycle x₀ γ h) q
  rw [freeWeight_homCocycle] at ep eq
  change _ = (homFunctor x₀ γ h).map _ at e
  have : Multiplicative.ofAdd (pathWeight (homCocycle x₀ γ h) p) =
      Multiplicative.ofAdd (pathWeight (homCocycle x₀ γ h) q) := ep.symm.trans (e.trans eq)
  exact Multiplicative.ofAdd.injective this

/-- An endomorphism viewed in the endomorphism group. -/
abbrev asEnd {X : FundGroupoid P} (f : X ⟶ X) : End X := f

/-- **A nontrivial homomorphism from the fundamental group to `ℤ` gives a cocycle that is
not a coboundary.** -/
theorem not_isCoboundary_homCocycle (hh : h ≠ 1) : ¬IsCoboundary (homCocycle x₀ γ h) := by
  rintro ⟨φ, hφ⟩
  apply hh
  ext g
  obtain ⟨w, hw⟩ := (CategoryTheory.Quotient.functor homotopy).map_surjective g
  have e1 : (homFunctor x₀ γ h).map g = 1 := by
    rw [← hw]
    change (CategoryTheory.Quotient.functor homotopy ⋙ homFunctor x₀ γ h).map w = 1
    rw [← freeWeight_homCocycle, freeWeight_eq_potFunctor _ φ hφ]
    change Multiplicative.ofAdd (φ _ - φ _) = 1
    rw [sub_self]; rfl
  change h (conj x₀ γ g) = 1 at e1
  set γ0 := γ (fvtx x₀)
  have e2 : conj x₀ γ g = asEnd (inv γ0) * g * asEnd γ0 := by
    simp only [conj, End.mul_def, asEnd, Category.assoc]; rfl
  have e3 : h (asEnd (inv γ0)) * h (asEnd γ0) = 1 := by
    rw [← map_mul]
    have : asEnd (inv γ0) * asEnd γ0 = 1 := by
      change γ0 ≫ inv γ0 = 𝟙 _
      simp
    rw [this, map_one]
  rw [e2, map_mul, map_mul, mul_comm (h (asEnd (inv γ0))), mul_assoc, e3, mul_one] at e1
  rw [e1]; rfl

omit h in
include γ in
/-- **Cocycle criterion for simple connectedness**: if the fundamental group is free and
every cocycle is a coboundary, the fundamental group is trivial. -/
theorem eq_one_of_forall_isCoboundary [IsFreeGroup (End (fvtx x₀))]
    (hall : ∀ c : ArrowWeight P, IsCocycle c → IsCoboundary c) (g : End (fvtx x₀)) :
    g = 1 := by
  classical
  have hE : IsEmpty (IsFreeGroup.Generators (End (fvtx x₀))) := by
    refine ⟨fun a ↦ ?_⟩
    let f : IsFreeGroup.Generators (End (fvtx x₀)) → Multiplicative ℤ :=
      fun b ↦ if b = a then Multiplicative.ofAdd (1 : ℤ) else 1
    have hne : IsFreeGroup.lift f ≠ 1 := by
      intro h1
      have := IsFreeGroup.lift_of f a
      rw [h1] at this
      simp only [f, if_true, MonoidHom.one_apply] at this
      exact absurd (congrArg Multiplicative.toAdd this) (by simp)
    exact not_isCoboundary_homCocycle x₀ γ _ hne (hall _ (isCocycle_homCocycle x₀ γ _))
  have := IsFreeGroup.ext_hom (G := End (fvtx x₀)) (H := End (fvtx x₀))
    (f := { toFun := id, map_one' := rfl, map_mul' := fun _ _ ↦ rfl }) (g := 1)
    fun a ↦ hE.elim a
  exact DFunLike.congr_fun this g

end Converse

end LargeIndecomposable.RayCat
