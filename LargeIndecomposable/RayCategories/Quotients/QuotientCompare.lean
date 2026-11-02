module

public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Comparing two quotients of one category

If every generator of a relation `r` holds in the quotient by `s` and every
generator of `s` holds in the quotient by `r`, the identity of `C` descends to
inverse functors between the two quotients (`quotientMap`), and the
endomorphism monoids of corresponding objects are isomorphic (`endEquivOfRel`).
Used to compare the fundamental groupoids of a ray category `P` and of `P/μ`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] (r s : HomRel C)

/-- The functor `C/s ⥤ C/r` induced by the identity. -/
def quotientMap (h : ∀ {X Y : C} (f g : X ⟶ Y), s f g →
    (CategoryTheory.Quotient.functor r).map f = (CategoryTheory.Quotient.functor r).map g) :
    CategoryTheory.Quotient s ⥤ CategoryTheory.Quotient r :=
  CategoryTheory.Quotient.lift s (CategoryTheory.Quotient.functor r) fun _ _ f g hfg ↦ h f g hfg

lemma quotientMap_map (h : ∀ {X Y : C} (f g : X ⟶ Y), s f g →
    (CategoryTheory.Quotient.functor r).map f = (CategoryTheory.Quotient.functor r).map g)
    {X Y : C} (f : X ⟶ Y) :
    (quotientMap r s h).map ((CategoryTheory.Quotient.functor s).map f) =
      (CategoryTheory.Quotient.functor r).map f :=
  CategoryTheory.Quotient.lift_map_functor_map _ _ _ f

variable {r s}

/-- Mutually compatible relations give isomorphic endomorphism monoids. -/
def endEquivOfRel
    (hrs : ∀ {X Y : C} (f g : X ⟶ Y), r f g →
      (CategoryTheory.Quotient.functor s).map f = (CategoryTheory.Quotient.functor s).map g)
    (hsr : ∀ {X Y : C} (f g : X ⟶ Y), s f g →
      (CategoryTheory.Quotient.functor r).map f = (CategoryTheory.Quotient.functor r).map g)
    (X : C) :
    End ((CategoryTheory.Quotient.functor s).obj X) ≃*
      End ((CategoryTheory.Quotient.functor r).obj X) where
  toFun f := (quotientMap r s hsr).map f
  invFun f := (quotientMap s r hrs).map f
  left_inv f := by
    obtain ⟨f, rfl⟩ := (CategoryTheory.Quotient.functor s).map_surjective f
    change (quotientMap s r hrs).map ((quotientMap r s hsr).map _) = _
    erw [quotientMap_map r s hsr f, quotientMap_map s r hrs f]
  right_inv f := by
    obtain ⟨f, rfl⟩ := (CategoryTheory.Quotient.functor r).map_surjective f
    change (quotientMap r s hsr).map ((quotientMap s r hrs).map _) = _
    erw [quotientMap_map s r hrs f, quotientMap_map r s hsr f]
  map_mul' f g := (quotientMap r s hsr).map_comp g f

section Functors

variable {D : Type*} [Category D] {r : HomRel C} {s : HomRel D}

/-- An isomorphism of categories carrying the relations into each other gives
isomorphic endomorphism monoids of the quotients. -/
def endEquivOfFunctors (Φ : C ⥤ D) (Ψ : D ⥤ C) (hΨΦ : Φ ⋙ Ψ = 𝟭 C) (hΦΨ : Ψ ⋙ Φ = 𝟭 D)
    (hrs : ∀ {X Y : C} (f g : X ⟶ Y), r f g → (CategoryTheory.Quotient.functor s).map (Φ.map f) =
      (CategoryTheory.Quotient.functor s).map (Φ.map g))
    (hsr : ∀ {X Y : D} (f g : X ⟶ Y), s f g → (CategoryTheory.Quotient.functor r).map (Ψ.map f) =
      (CategoryTheory.Quotient.functor r).map (Ψ.map g))
    (X : C) :
    End ((CategoryTheory.Quotient.functor r).obj X) ≃*
      End ((CategoryTheory.Quotient.functor s).obj (Φ.obj X)) := by
  let Qr := CategoryTheory.Quotient.functor r
  let Qs := CategoryTheory.Quotient.functor s
  let Φ' := CategoryTheory.Quotient.lift r (Φ ⋙ Qs) fun _ _ f g h ↦ hrs f g h
  let Ψ' := CategoryTheory.Quotient.lift s (Ψ ⋙ Qr) fun _ _ f g h ↦ hsr f g h
  have hΦ' : ∀ {X Y : C} (f : X ⟶ Y), Φ'.map (Qr.map f) = Qs.map (Φ.map f) := fun f ↦
    CategoryTheory.Quotient.lift_map_functor_map _ _ _ f
  have hΨ' : ∀ {X Y : D} (g : X ⟶ Y), Ψ'.map (Qs.map g) = Qr.map (Ψ.map g) := fun g ↦
    CategoryTheory.Quotient.lift_map_functor_map _ _ _ g
  have hX : Ψ.obj (Φ.obj X) = X := Functor.congr_obj hΨΦ X
  have hX' : Qr.obj (Ψ.obj (Φ.obj X)) = Qr.obj X := by rw [hX]
  exact
    { toFun f := Φ'.map f
      invFun g := eqToHom hX'.symm ≫ Ψ'.map g ≫ eqToHom hX'
      left_inv f := by
        obtain ⟨f, rfl⟩ := Qr.map_surjective f
        change eqToHom hX'.symm ≫ Ψ'.map (Φ'.map _) ≫ eqToHom hX' = _
        rw [hΦ', hΨ']
        have := Functor.congr_hom hΨΦ f
        simp only [Functor.comp_map, Functor.id_map] at this
        rw [this, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
        simp
      right_inv g := by
        obtain ⟨g, rfl⟩ := Qs.map_surjective g
        change Φ'.map (eqToHom hX'.symm ≫ Ψ'.map (Qs.map g) ≫ eqToHom hX') = _
        rw [hΨ', Functor.map_comp, Functor.map_comp, hΦ', eqToHom_map, eqToHom_map]
        have := Functor.congr_hom hΦΨ g
        simp only [Functor.comp_map, Functor.id_map] at this
        rw [this, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
        simp
      map_mul' f g := Φ'.map_comp g f }

end Functors

end LargeIndecomposable
