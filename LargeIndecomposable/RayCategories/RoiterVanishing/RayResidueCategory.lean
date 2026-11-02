module

public import Mathlib.CategoryTheory.Quotient
public import LargeIndecomposable.RayCategories.Basic.FiniteRayCategory

@[expose] public section

/-!
# Residue categories of categories with zero morphisms

BGRS 8.6 passes from a ray category `P` to the residue category `P / μ`,
where one nonzero morphism `μ` and every morphism factoring through it are
annihilated.  This file constructs that quotient for an arbitrary category
with zero morphisms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A two-sided collection of morphisms containing all zero morphisms. -/
structure ZeroHomIdeal (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] where
  mem : ∀ {X Y : C}, (X ⟶ Y) → Prop
  zero_mem : ∀ X Y : C, mem (0 : X ⟶ Y)
  comp_mem_left : ∀ {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z},
    mem g → mem (f ≫ g)
  comp_mem_right : ∀ {X Y Z : C} {f : X ⟶ Y} (g : Y ⟶ Z),
    mem f → mem (f ≫ g)

/-- A zero Hom ideal is proper when it contains no identity morphism. -/
def ZeroHomIdeal.IsProper (I : ZeroHomIdeal C) : Prop :=
  ∀ X : C, ¬I.mem (𝟙 X)

/-- A zero Hom ideal is nonzero when it contains a nonzero morphism. -/
def ZeroHomIdeal.IsNonzero (I : ZeroHomIdeal C) : Prop :=
  ∃ (X Y : C) (f : X ⟶ Y), I.mem f ∧ f ≠ 0

namespace ZeroHomIdeal

variable (I : ZeroHomIdeal C)

/-- Collapse all members of a zero Hom ideal to one zero class and make no
other identifications. -/
def rel : HomRel C :=
  fun {X Y} (f g : X ⟶ Y) ↦ f = g ∨ (I.mem f ∧ I.mem g)

instance rel_congruence : Congruence I.rel where
  equivalence := by
    intro X Y
    refine ⟨?_, ?_, ?_⟩
    · intro f
      exact Or.inl rfl
    · intro f g h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · intro f g h hfg hgh
      rcases hfg with hfg | hfg
      · subst g
        exact hgh
      · rcases hgh with hgh | hgh
        · subst h
          exact Or.inr hfg
        · exact Or.inr ⟨hfg.1, hgh.2⟩
  comp_left := by
    intro X Y Z f g g' h
    rcases h with h | h
    · exact Or.inl (congrArg (fun q ↦ f ≫ q) h)
    · exact Or.inr ⟨I.comp_mem_left f h.1, I.comp_mem_left f h.2⟩
  comp_right := by
    intro X Y Z f f' g h
    rcases h with h | h
    · exact Or.inl (congrArg (fun q ↦ q ≫ g) h)
    · exact Or.inr ⟨I.comp_mem_right g h.1, I.comp_mem_right g h.2⟩

/-- The categorical quotient by a zero Hom ideal again has zero morphisms. -/
instance quotientHasZeroMorphisms :
    HasZeroMorphisms (CategoryTheory.Quotient I.rel) where
  zero X Y := ⟨Quot.mk _ (0 : X.as ⟶ Y.as)⟩
  comp_zero := by
    intro X Y f Z
    induction f using Quot.inductionOn with
    | _ f =>
        change Quot.mk _ (f ≫ 0) = Quot.mk _ 0
        rw [comp_zero]
  zero_comp := by
    intro X Y Z f
    induction f using Quot.inductionOn with
    | _ f =>
        change Quot.mk _ (0 ≫ f) = Quot.mk _ 0
        rw [zero_comp]

/-- A quotient of a category with finitely many objects again has finitely
many objects. -/
instance quotientFinite [Finite C] :
    Finite (CategoryTheory.Quotient I.rel) :=
  Finite.of_injective CategoryTheory.Quotient.as (by
    intro X Y h
    exact CategoryTheory.Quotient.ext h)

/-- The quotient functor sends a morphism to zero exactly when it belongs to
the collapsed zero Hom ideal. -/
theorem functor_map_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    (CategoryTheory.Quotient.functor I.rel).map f = 0 ↔ I.mem f := by
  rw [← (CategoryTheory.Quotient.functor I.rel).map_zero X Y,
    CategoryTheory.Quotient.functor_map_eq_iff]
  change (f = 0 ∨ (I.mem f ∧ I.mem 0)) ↔ I.mem f
  constructor
  · intro h
    rcases h with h | h
    · subst f
      exact I.zero_mem X Y
    · exact h.1
  · intro h
    exact Or.inr ⟨h, I.zero_mem X Y⟩

/-- A morphism survives a zero-ideal quotient exactly when it is not in the
ideal. -/
theorem functor_map_ne_zero_iff {X Y : C} (f : X ⟶ Y) :
    (CategoryTheory.Quotient.functor I.rel).map f ≠ 0 ↔ ¬I.mem f :=
  not_congr (I.functor_map_eq_zero_iff f)

/-- For a proper zero Hom ideal, equality to an identity in the quotient is
already equality to that identity before quotienting. -/
theorem functor_map_eq_id_iff (hI : I.IsProper)
    {X : C} (f : End X) :
    (CategoryTheory.Quotient.functor I.rel).map f =
        (CategoryTheory.Quotient.functor I.rel).map (𝟙 X) ↔
      f = 𝟙 X := by
  rw [CategoryTheory.Quotient.functor_map_eq_iff]
  change (f = 𝟙 X ∨ (I.mem f ∧ I.mem (𝟙 X))) ↔ f = 𝟙 X
  constructor
  · intro h
    rcases h with h | h
    · exact h
    · exact False.elim (hI X h.2)
  · exact Or.inl

/-- The quotient functor of a proper zero Hom ideal reflects isomorphisms. -/
theorem functor_map_isIso_iff (hI : I.IsProper)
    {X Y : C} (f : X ⟶ Y) :
    IsIso ((CategoryTheory.Quotient.functor I.rel).map f) ↔ IsIso f := by
  let q := CategoryTheory.Quotient.functor I.rel
  constructor
  · intro hf
    letI : IsIso (q.map f) := hf
    let g : Y ⟶ X := Quot.out (inv (q.map f))
    have hg : q.map g = inv (q.map f) := by
      simp [q, g, CategoryTheory.Quotient.functor]
    have hfgMap : q.map (f ≫ g) = q.map (𝟙 X) := by
      rw [q.map_comp, hg, IsIso.hom_inv_id, q.map_id]
    have hgfMap : q.map (g ≫ f) = q.map (𝟙 Y) := by
      rw [q.map_comp, hg, IsIso.inv_hom_id, q.map_id]
    have hfg : f ≫ g = 𝟙 X :=
      I.functor_map_eq_id_iff hI (f ≫ g) |>.1 hfgMap
    have hgf : g ≫ f = 𝟙 Y :=
      I.functor_map_eq_id_iff hI (g ≫ f) |>.1 hgfMap
    exact ⟨⟨g, hfg, hgf⟩⟩
  · intro hf
    letI : IsIso f := hf
    infer_instance

/-- The irreducible arrows in a proper zero-ideal quotient are exactly the
images of original irreducible arrows which do not belong to the ideal. -/
theorem functor_map_isIrreducible_iff (hI : I.IsProper)
    {X Y : C} (f : X ⟶ Y) :
    IsIrreducibleRayMorphism
        ((CategoryTheory.Quotient.functor I.rel).map f) ↔
      IsIrreducibleRayMorphism f ∧ ¬I.mem f := by
  let q := CategoryTheory.Quotient.functor I.rel
  constructor
  · intro hf
    have hmem : ¬I.mem f :=
      (I.functor_map_ne_zero_iff f).1 hf.1
    refine ⟨⟨?_, ?_, ?_⟩, hmem⟩
    · intro hzero
      subst f
      exact hmem (I.zero_mem X Y)
    · intro hIso
      exact hf.2.1 ((I.functor_map_isIso_iff hI f).2 hIso)
    · intro W a b hab
      have habMap : q.map a ≫ q.map b = q.map f := by
        rw [← q.map_comp, hab]
      rcases hf.2.2 (q.obj W) (q.map a) (q.map b) habMap with ha | hb
      · exact Or.inl ((I.functor_map_isIso_iff hI a).1 ha)
      · exact Or.inr ((I.functor_map_isIso_iff hI b).1 hb)
  · rintro ⟨hf, hmem⟩
    refine ⟨(I.functor_map_ne_zero_iff f).2 hmem, ?_, ?_⟩
    · intro hIso
      exact hf.2.1 ((I.functor_map_isIso_iff hI f).1 hIso)
    · rintro ⟨W⟩ a b hab
      let a' : X ⟶ W := Quot.out a
      let b' : W ⟶ Y := Quot.out b
      have ha : q.map a' = a := by
        simp [q, a', CategoryTheory.Quotient.functor]
      have hb : q.map b' = b := by
        simp [q, b', CategoryTheory.Quotient.functor]
      change Quot.mk (@HomRel.CompClosure C _ I.rel X W) a' = a at ha
      change Quot.mk (@HomRel.CompClosure C _ I.rel W Y) b' = b at hb
      have habMap : q.map (a' ≫ b') = q.map f := by
        change Quot.mk (@HomRel.CompClosure C _ I.rel X Y) (a' ≫ b') =
          Quot.mk (@HomRel.CompClosure C _ I.rel X Y) f
        rw [← CategoryTheory.Quotient.comp_mk I.rel a' b', ha, hb]
        exact hab
      have hrel : I.rel (a' ≫ b') f :=
        (CategoryTheory.Quotient.functor_map_eq_iff
          I.rel (a' ≫ b') f).1 habMap
      have hab' : a' ≫ b' = f := by
        rcases hrel with hrel | hrel
        · exact hrel
        · exact False.elim (hmem hrel.2)
      rcases hf.2.2 W a' b' hab' with haIso | hbIso
      · left
        rw [← ha]
        exact (I.functor_map_isIso_iff hI a').2 haIso
      · right
        rw [← hb]
        exact (I.functor_map_isIso_iff hI b').2 hbIso

/-- Postfactorizations of a morphism which survives the quotient lift exactly
to postfactorizations before quotienting. -/
theorem exists_postfactor_map_iff
    {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
    (hg : ¬I.mem g) :
    (∃ h : (CategoryTheory.Quotient.functor I.rel).obj Y ⟶
        (CategoryTheory.Quotient.functor I.rel).obj Z,
      (CategoryTheory.Quotient.functor I.rel).map f ≫ h =
        (CategoryTheory.Quotient.functor I.rel).map g) ↔
      ∃ h : Y ⟶ Z, f ≫ h = g := by
  let q := CategoryTheory.Quotient.functor I.rel
  constructor
  · rintro ⟨h, hh⟩
    let h' : Y ⟶ Z := Quot.out h
    have hh' : q.map h' = h := by
      simp [q, h', CategoryTheory.Quotient.functor]
    have hmap : q.map (f ≫ h') = q.map g := by
      rw [q.map_comp, hh', hh]
    have hrel : I.rel (f ≫ h') g :=
      (CategoryTheory.Quotient.functor_map_eq_iff
        I.rel (f ≫ h') g).1 hmap
    rcases hrel with hrel | hrel
    · exact ⟨h', hrel⟩
    · exact False.elim (hg hrel.2)
  · rintro ⟨h, hh⟩
    refine ⟨q.map h, ?_⟩
    rw [← q.map_comp, hh]

/-- Prefactorizations of a morphism which survives the quotient lift exactly
to prefactorizations before quotienting. -/
theorem exists_prefactor_map_iff
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hf : ¬I.mem f) :
    (∃ h : (CategoryTheory.Quotient.functor I.rel).obj X ⟶
        (CategoryTheory.Quotient.functor I.rel).obj Y,
      h ≫ (CategoryTheory.Quotient.functor I.rel).map g =
        (CategoryTheory.Quotient.functor I.rel).map f) ↔
      ∃ h : X ⟶ Y, h ≫ g = f := by
  let q := CategoryTheory.Quotient.functor I.rel
  constructor
  · rintro ⟨h, hh⟩
    let h' : X ⟶ Y := Quot.out h
    have hh' : q.map h' = h := by
      simp [q, h', CategoryTheory.Quotient.functor]
    have hmap : q.map (h' ≫ g) = q.map f := by
      rw [q.map_comp, hh', hh]
    have hrel : I.rel (h' ≫ g) f :=
      (CategoryTheory.Quotient.functor_map_eq_iff
        I.rel (h' ≫ g) f).1 hmap
    rcases hrel with hrel | hrel
    · exact ⟨h', hrel⟩
    · exact False.elim (hf hrel.2)
  · rintro ⟨h, hh⟩
    refine ⟨q.map h, ?_⟩
    rw [← q.map_comp, hh]

/-- A quotient of a finite ray category by a proper zero Hom ideal is again a
finite ray category (basic axioms).  Properness prevents quotient isomorphisms and identity
classes from being created by the collapse. -/
theorem quotientIsFiniteRayCategory0 [IsFiniteRayCategory0 C]
    (hI : I.IsProper) :
    IsFiniteRayCategory0 (CategoryTheory.Quotient I.rel) where
  id_ne_zero := by
    rintro ⟨X⟩ hzero
    change (CategoryTheory.Quotient.functor I.rel).map (𝟙 X) =
      (CategoryTheory.Quotient.functor I.rel).map 0 at hzero
    rw [CategoryTheory.Quotient.functor_map_eq_iff] at hzero
    rcases hzero with hzero | hzero
    · exact IsFiniteRayCategory0.id_ne_zero X hzero
    · exact hI X hzero.1
  hom_finite := by
    intro X Y
    letI : Finite (X.as ⟶ Y.as) :=
      IsFiniteRayCategory0.hom_finite X.as Y.as
    exact Finite.of_surjective
      (fun f : X.as ⟶ Y.as ↦ Quot.mk _ f) Quot.mk_surjective
  endomorphism_nilpotent := by
    rintro ⟨X⟩ f hf
    induction f using Quot.inductionOn with
    | _ f =>
        have hf' : f ≠ 𝟙 X := by
          intro h
          apply hf
          subst f
          rfl
        obtain ⟨n, hn, hpow⟩ :=
          IsFiniteRayCategory0.endomorphism_nilpotent f hf'
        refine ⟨n, hn, ?_⟩
        change (((CategoryTheory.Quotient.functor I.rel).mapEnd X) f) ^ n = 0
        rw [← map_pow, hpow]
        rfl
  skeletal := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨e⟩
    let q := CategoryTheory.Quotient.functor I.rel
    let f : X ⟶ Y := Quot.out e.hom
    let g : Y ⟶ X := Quot.out e.inv
    have hf : q.map f = e.hom := by
      simp [q, f, CategoryTheory.Quotient.functor]
    have hg : q.map g = e.inv := by
      simp [q, g, CategoryTheory.Quotient.functor]
    change Quot.mk _ f = e.hom at hf
    change Quot.mk _ g = e.inv at hg
    have hhomInv := e.hom_inv_id
    change CategoryTheory.Quotient.comp I.rel e.hom e.inv =
      𝟙 ({ as := X } : CategoryTheory.Quotient I.rel) at hhomInv
    have hinvHom := e.inv_hom_id
    change CategoryTheory.Quotient.comp I.rel e.inv e.hom =
      𝟙 ({ as := Y } : CategoryTheory.Quotient I.rel) at hinvHom
    have hfgMap : q.map (f ≫ g) = q.map (𝟙 X) := by
      change Quot.mk (@HomRel.CompClosure C _ I.rel X X) (f ≫ g) =
        Quot.mk (@HomRel.CompClosure C _ I.rel X X) (𝟙 X)
      rw [← CategoryTheory.Quotient.comp_mk I.rel f g, hf, hg, hhomInv]
      rfl
    have hgfMap : q.map (g ≫ f) = q.map (𝟙 Y) := by
      change Quot.mk (@HomRel.CompClosure C _ I.rel Y Y) (g ≫ f) =
        Quot.mk (@HomRel.CompClosure C _ I.rel Y Y) (𝟙 Y)
      rw [← CategoryTheory.Quotient.comp_mk I.rel g f, hg, hf, hinvHom]
      rfl
    have hfg : f ≫ g = 𝟙 X :=
      I.functor_map_eq_id_iff hI (f ≫ g) |>.1 hfgMap
    have hgf : g ≫ f = 𝟙 Y :=
      I.functor_map_eq_id_iff hI (g ≫ f) |>.1 hgfMap
    apply CategoryTheory.Quotient.ext
    exact IsFiniteRayCategory0.skeletal
      ⟨⟨f, g, hfg, hgf⟩⟩

/-- A quotient of a finite ray category by a proper zero Hom ideal is again a
finite ray category.  Properness prevents quotient isomorphisms and identity
classes from being created by the collapse. -/
theorem quotientIsFiniteRayCategory [IsFiniteRayCategory C]
    (hI : I.IsProper) :
    IsFiniteRayCategory (CategoryTheory.Quotient I.rel) where
  id_ne_zero := by
    rintro ⟨X⟩ hzero
    change (CategoryTheory.Quotient.functor I.rel).map (𝟙 X) =
      (CategoryTheory.Quotient.functor I.rel).map 0 at hzero
    rw [CategoryTheory.Quotient.functor_map_eq_iff] at hzero
    rcases hzero with hzero | hzero
    · exact IsFiniteRayCategory.id_ne_zero X hzero
    · exact hI X hzero.1
  hom_finite := by
    intro X Y
    letI : Finite (X.as ⟶ Y.as) :=
      IsFiniteRayCategory.hom_finite X.as Y.as
    exact Finite.of_surjective
      (fun f : X.as ⟶ Y.as ↦ Quot.mk _ f) Quot.mk_surjective
  endomorphism_nilpotent := by
    rintro ⟨X⟩ f hf
    induction f using Quot.inductionOn with
    | _ f =>
        have hf' : f ≠ 𝟙 X := by
          intro h
          apply hf
          subst f
          rfl
        obtain ⟨n, hn, hpow⟩ :=
          IsFiniteRayCategory.endomorphism_nilpotent f hf'
        refine ⟨n, hn, ?_⟩
        change (((CategoryTheory.Quotient.functor I.rel).mapEnd X) f) ^ n = 0
        rw [← map_pow, hpow]
        rfl
  skeletal := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨e⟩
    let q := CategoryTheory.Quotient.functor I.rel
    let f : X ⟶ Y := Quot.out e.hom
    let g : Y ⟶ X := Quot.out e.inv
    have hf : q.map f = e.hom := by
      simp [q, f, CategoryTheory.Quotient.functor]
    have hg : q.map g = e.inv := by
      simp [q, g, CategoryTheory.Quotient.functor]
    change Quot.mk _ f = e.hom at hf
    change Quot.mk _ g = e.inv at hg
    have hhomInv := e.hom_inv_id
    change CategoryTheory.Quotient.comp I.rel e.hom e.inv =
      𝟙 ({ as := X } : CategoryTheory.Quotient I.rel) at hhomInv
    have hinvHom := e.inv_hom_id
    change CategoryTheory.Quotient.comp I.rel e.inv e.hom =
      𝟙 ({ as := Y } : CategoryTheory.Quotient I.rel) at hinvHom
    have hfgMap : q.map (f ≫ g) = q.map (𝟙 X) := by
      change Quot.mk (@HomRel.CompClosure C _ I.rel X X) (f ≫ g) =
        Quot.mk (@HomRel.CompClosure C _ I.rel X X) (𝟙 X)
      rw [← CategoryTheory.Quotient.comp_mk I.rel f g, hf, hg, hhomInv]
      rfl
    have hgfMap : q.map (g ≫ f) = q.map (𝟙 Y) := by
      change Quot.mk (@HomRel.CompClosure C _ I.rel Y Y) (g ≫ f) =
        Quot.mk (@HomRel.CompClosure C _ I.rel Y Y) (𝟙 Y)
      rw [← CategoryTheory.Quotient.comp_mk I.rel g f, hg, hf, hinvHom]
      rfl
    have hfg : f ≫ g = 𝟙 X :=
      I.functor_map_eq_id_iff hI (f ≫ g) |>.1 hfgMap
    have hgf : g ≫ f = 𝟙 Y :=
      I.functor_map_eq_id_iff hI (g ≫ f) |>.1 hgfMap
    apply CategoryTheory.Quotient.ext
    exact IsFiniteRayCategory.skeletal
      ⟨⟨f, g, hfg, hgf⟩⟩
  factorization_comparable := by
    intro X Y f g
    induction f using Quot.inductionOn with
    | _ f =>
        induction g using Quot.inductionOn with
        | _ g =>
            rcases IsFiniteRayCategory.factorization_comparable f g with
              h | h
            · left
              obtain ⟨a, b, hab⟩ := h
              refine ⟨Quot.mk _ a, Quot.mk _ b, ?_⟩
              exact congrArg (fun q ↦ Quot.mk _ q) hab
            · right
              obtain ⟨a, b, hab⟩ := h
              refine ⟨Quot.mk _ a, Quot.mk _ b, ?_⟩
              exact congrArg (fun q ↦ Quot.mk _ q) hab
  source_stabilizer_trivial := by
    intro X Y Z f g a hfgne heq
    induction f using Quot.inductionOn with
    | _ f =>
        induction g using Quot.inductionOn with
        | _ g =>
            induction a using Quot.inductionOn with
            | _ a =>
                have hfgne' : f ≫ g ≠ 0 := by
                  intro hzero
                  apply hfgne
                  change Quot.mk _ (f ≫ g) = Quot.mk _ 0
                  rw [hzero]
                have hfgNotMem : ¬I.mem (f ≫ g) := by
                  intro hmem
                  apply hfgne
                  change (CategoryTheory.Quotient.functor I.rel).map
                    (f ≫ g) = 0
                  exact (I.functor_map_eq_zero_iff (f ≫ g)).2 hmem
                have hrel : I.rel ((a ≫ f) ≫ g) (f ≫ g) := by
                  apply (CategoryTheory.Quotient.functor_map_eq_iff
                    I.rel ((a ≫ f) ≫ g) (f ≫ g)).1
                  exact heq
                have heq' : (a ≫ f) ≫ g = f ≫ g := by
                  rcases hrel with hrel | hrel
                  · exact hrel
                  · exact False.elim (hfgNotMem hrel.2)
                have ha :=
                  IsFiniteRayCategory.source_stabilizer_trivial
                    f g a hfgne' heq'
                subst a
                rfl

end ZeroHomIdeal

/-- Morphisms lying in the two-sided zero ideal generated by `mu`. -/
def FactorsThroughMorphism {A B X Y : C} (mu : A ⟶ B)
    (f : X ⟶ Y) : Prop :=
  ∃ (a : X ⟶ A) (b : B ⟶ Y), f = a ≫ mu ≫ b

/-- The two-sided zero Hom ideal generated by one morphism. -/
def principalZeroHomIdeal {A B : C} (mu : A ⟶ B) :
    ZeroHomIdeal C where
  mem f := FactorsThroughMorphism mu f
  zero_mem X Y := ⟨0, 0, by simp⟩
  comp_mem_left := by
    intro X Y Z f g hg
    obtain ⟨a, b, rfl⟩ := hg
    exact ⟨f ≫ a, b, by simp [Category.assoc]⟩
  comp_mem_right := by
    intro X Y Z f g hf
    obtain ⟨a, b, rfl⟩ := hf
    exact ⟨a, b ≫ g, by simp [Category.assoc]⟩

/-- The principal zero Hom ideal generated by a nonzero morphism is nonzero. -/
theorem principalZeroHomIdeal_isNonzero_of_ne_zero
    {X Y : C} (mu : X ⟶ Y) (hmu : mu ≠ 0) :
    (principalZeroHomIdeal mu).IsNonzero := by
  refine ⟨X, Y, mu, ?_, hmu⟩
  exact ⟨𝟙 X, 𝟙 Y, by simp⟩

/-- In a ray category, the principal zero Hom ideal generated by a
noninvertible morphism is proper. -/
theorem principalZeroHomIdeal_isProper_of_not_isIso
    [IsFiniteRayCategory C] {A B : C} (mu : A ⟶ B)
    (hmu : ¬IsIso mu) :
    (principalZeroHomIdeal mu).IsProper := by
  intro X hX
  obtain ⟨a, b, hab⟩ := hX
  haveI : IsIso (a ≫ mu ≫ b) := by
    rw [← hab]
    infer_instance
  have hmub : IsIso (mu ≫ b) :=
    (ray_isIso_factors a (mu ≫ b)).2
  letI : IsIso (mu ≫ b) := hmub
  exact hmu (ray_isIso_factors mu b).1

/-- The residue category obtained by annihilating `mu`. -/
abbrev RayResidueCategory {A B : C} (mu : A ⟶ B) :=
  CategoryTheory.Quotient (principalZeroHomIdeal mu).rel

/-- The canonical functor to the residue category. -/
abbrev rayResidueFunctor {A B : C} (mu : A ⟶ B) :
    C ⥤ RayResidueCategory mu :=
  CategoryTheory.Quotient.functor (principalZeroHomIdeal mu).rel

/-- Annihilating a noninvertible morphism of a finite ray category leaves a
finite ray category. -/
theorem rayResidueCategory_isFiniteRayCategory
    [IsFiniteRayCategory C] {A B : C} (mu : A ⟶ B)
    (hmu : ¬IsIso mu) :
    IsFiniteRayCategory (RayResidueCategory mu) :=
  (principalZeroHomIdeal mu).quotientIsFiniteRayCategory
    (principalZeroHomIdeal_isProper_of_not_isIso mu hmu)

/-- A morphism vanishes in the residue category exactly when it factors
through the annihilated morphism. -/
theorem rayResidueFunctor_map_eq_zero_iff
    {A B X Y : C} (mu : A ⟶ B) (f : X ⟶ Y) :
    (rayResidueFunctor mu).map f = 0 ↔ FactorsThroughMorphism mu f :=
  (principalZeroHomIdeal mu).functor_map_eq_zero_iff f

/-- The distinguished morphism itself vanishes in its residue category. -/
@[simp]
theorem rayResidueFunctor_map_generator_eq_zero
    {A B : C} (mu : A ⟶ B) :
    (rayResidueFunctor mu).map mu = 0 := by
  rw [rayResidueFunctor_map_eq_zero_iff]
  exact ⟨𝟙 A, 𝟙 B, by simp⟩

end LargeIndecomposable
