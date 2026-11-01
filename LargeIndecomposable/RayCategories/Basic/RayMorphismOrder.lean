module

public import LargeIndecomposable.RayCategories.Basic.FiniteRayCategory

@[expose] public section

/-!
# The factorization preorder of nonzero ray morphisms

For a source object `x`, BGRS writes `x/P` for the nonzero morphisms starting
at `x`, ordered by postfactorization.  This file packages that preorder and its
finiteness in a finite ray category.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A nonzero morphism with both endpoints fixed. -/
abbrev NonzeroHom (X Y : C) := {f : X ⟶ Y // f ≠ 0}

/-- A nonzero morphism with fixed source and varying target. -/
structure NonzeroMorphismFrom (x : C) where
  target : C
  hom : x ⟶ target
  ne_zero : hom ≠ 0

namespace NonzeroMorphismFrom

variable {x : C}

/-- Extensionality for nonzero morphisms out of a fixed source. -/
theorem ext {f g : NonzeroMorphismFrom x}
    (htarget : f.target = g.target)
    (hhom : f.hom ≫ eqToHom htarget = g.hom) : f = g := by
  cases f with
  | mk ft ff hf =>
      cases g with
      | mk gt gf hg =>
          dsimp at htarget
          subst gt
          simp only [eqToHom_refl, Category.comp_id] at hhom
          subst gf
          rfl

/-- Postfactorization order on nonzero morphisms from `x`. -/
instance : LE (NonzeroMorphismFrom x) where
  le f g := ∃ h : f.target ⟶ g.target, f.hom ≫ h = g.hom

theorem le_iff (f g : NonzeroMorphismFrom x) :
    f ≤ g ↔ ∃ h : f.target ⟶ g.target, f.hom ≫ h = g.hom :=
  Iff.rfl

/-- Factorization gives a preorder before using the additional ray-category
cancellation axioms which make `x/P` antisymmetric. -/
instance : Preorder (NonzeroMorphismFrom x) where
  le_refl f := ⟨𝟙 f.target, Category.comp_id _⟩
  le_trans f g h hfg hgh := by
    obtain ⟨a, ha⟩ := hfg
    obtain ⟨b, hb⟩ := hgh
    refine ⟨a ≫ b, ?_⟩
    rw [← Category.assoc, ha, hb]

/-- Mutual postfactorization of nonzero ray morphisms forces equality. -/
theorem le_antisymm [IsFiniteRayCategory C]
    {f g : NonzeroMorphismFrom x} (hfg : f ≤ g) (hgf : g ≤ f) :
    f = g := by
  obtain ⟨a, ha⟩ := hfg
  obtain ⟨b, hb⟩ := hgf
  have hab : a ≫ b = 𝟙 f.target := by
    apply ray_right_stabilizer_trivial f.hom (a ≫ b) f.ne_zero
    rw [← Category.assoc, ha, hb]
  have hba : b ≫ a = 𝟙 g.target := by
    apply ray_right_stabilizer_trivial g.hom (b ≫ a) g.ne_zero
    rw [← Category.assoc, hb, ha]
  letI : IsIso a := ⟨⟨b, hab, hba⟩⟩
  obtain ⟨htarget, haeq⟩ := ray_isIso_eq_eqToHom a
  apply NonzeroMorphismFrom.ext htarget
  rw [← haeq]
  exact ha

/-- The BGRS factorization order `x/P` is a partial order. -/
instance [IsFiniteRayCategory C] : PartialOrder (NonzeroMorphismFrom x) where
  toPreorder := inferInstance
  le_antisymm := fun _ _ hfg hgf ↦
    NonzeroMorphismFrom.le_antisymm hfg hgf

/-- The fixed-source morphism preorder is finite when the object type and all
ray-category Hom sets are finite. -/
instance [Finite C] [IsFiniteRayCategory C] :
    Finite (NonzeroMorphismFrom x) := by
  letI (X Y : C) : Finite (X ⟶ Y) :=
    IsFiniteRayCategory.hom_finite X Y
  letI : Fintype C := Fintype.ofFinite C
  letI (X Y : C) : Fintype (X ⟶ Y) := Fintype.ofFinite (X ⟶ Y)
  let toSigma : NonzeroMorphismFrom x → Σ Y : C, x ⟶ Y :=
    fun f ↦ ⟨f.target, f.hom⟩
  apply Finite.of_injective toSigma
  intro f g h
  cases f with
  | mk ft ff hf =>
      cases g with
      | mk gt gf hg =>
          dsimp [toSigma] at h
          cases h
          rfl

/-- A proper noninvertible postfactor gives a strict inequality in `x/P`. -/
theorem lt_of_postfactor_noniso [IsFiniteRayCategory C]
    {f g : NonzeroMorphismFrom x} (a : f.target ⟶ g.target)
    (hfg : f.hom ≫ a = g.hom) (ha : ¬IsIso a) :
    f < g := by
  refine lt_of_le_not_ge ⟨a, hfg⟩ ?_
  rintro ⟨b, hgf⟩
  have hab : a ≫ b = 𝟙 f.target := by
    apply ray_right_stabilizer_trivial f.hom (a ≫ b) f.ne_zero
    rw [← Category.assoc, hfg, hgf]
  have hba : b ≫ a = 𝟙 g.target := by
    apply ray_right_stabilizer_trivial g.hom (b ≫ a) g.ne_zero
    rw [← Category.assoc, hgf, hfg]
  exact ha ⟨⟨b, hab, hba⟩⟩

/-- If a noninvertible morphism factors through an irreducible one in the
fixed-source order, then the two elements are mutually comparable. -/
theorem reverse_le_of_le_irreducible_of_noniso [IsFiniteRayCategory C]
    {f g : NonzeroMorphismFrom x} (hfg : f ≤ g)
    (hg : IsIrreducibleRayMorphism g.hom) (hf : ¬IsIso f.hom) :
    g ≤ f := by
  obtain ⟨a, ha⟩ := hfg
  rcases hg.2.2 f.target f.hom a ha with hfIso | haIso
  · exact (hf hfIso).elim
  · letI : IsIso a := haIso
    refine ⟨inv a, ?_⟩
    rw [← ha, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end NonzeroMorphismFrom

/-- A nonzero morphism with fixed target and varying source. -/
structure NonzeroMorphismTo (y : C) where
  source : C
  hom : source ⟶ y
  ne_zero : hom ≠ 0

namespace NonzeroMorphismTo

variable {y : C}

/-- Extensionality for nonzero morphisms into a fixed target. -/
theorem ext {f g : NonzeroMorphismTo y}
    (hsource : f.source = g.source)
    (hhom : eqToHom hsource ≫ g.hom = f.hom) : f = g := by
  cases f with
  | mk fs ff hf =>
      cases g with
      | mk gs gf hg =>
          dsimp at hsource
          subst gs
          simp only [eqToHom_refl, Category.id_comp] at hhom
          subst gf
          rfl

/-- Prefactorization order on nonzero morphisms into `y`. -/
instance : LE (NonzeroMorphismTo y) where
  le f g := ∃ h : f.source ⟶ g.source, h ≫ g.hom = f.hom

theorem le_iff (f g : NonzeroMorphismTo y) :
    f ≤ g ↔ ∃ h : f.source ⟶ g.source, h ≫ g.hom = f.hom :=
  Iff.rfl

/-- Prefactorization gives a preorder before ray cancellation is used. -/
instance : Preorder (NonzeroMorphismTo y) where
  le_refl f := ⟨𝟙 f.source, Category.id_comp _⟩
  le_trans f g h hfg hgh := by
    obtain ⟨a, ha⟩ := hfg
    obtain ⟨b, hb⟩ := hgh
    refine ⟨a ≫ b, ?_⟩
    rw [Category.assoc, hb, ha]

/-- Mutual prefactorization of nonzero ray morphisms forces equality. -/
theorem le_antisymm [IsFiniteRayCategory C]
    {f g : NonzeroMorphismTo y} (hfg : f ≤ g) (hgf : g ≤ f) :
    f = g := by
  obtain ⟨a, ha⟩ := hfg
  obtain ⟨b, hb⟩ := hgf
  have hab : a ≫ b = 𝟙 f.source := by
    apply ray_left_stabilizer_trivial f.hom (a ≫ b) f.ne_zero
    rw [Category.assoc, hb, ha]
  have hba : b ≫ a = 𝟙 g.source := by
    apply ray_left_stabilizer_trivial g.hom (b ≫ a) g.ne_zero
    rw [Category.assoc, ha, hb]
  letI : IsIso a := ⟨⟨b, hab, hba⟩⟩
  obtain ⟨hsource, haeq⟩ := ray_isIso_eq_eqToHom a
  apply NonzeroMorphismTo.ext hsource
  rw [← haeq]
  exact ha

/-- The fixed-target prefactorization preorder is a partial order. -/
instance [IsFiniteRayCategory C] : PartialOrder (NonzeroMorphismTo y) where
  toPreorder := inferInstance
  le_antisymm := fun _ _ hfg hgf ↦
    NonzeroMorphismTo.le_antisymm hfg hgf

/-- The fixed-target morphism order is finite when objects and Hom sets are
finite. -/
instance [Finite C] [IsFiniteRayCategory C] :
    Finite (NonzeroMorphismTo y) := by
  letI (X Y : C) : Finite (X ⟶ Y) :=
    IsFiniteRayCategory.hom_finite X Y
  letI : Fintype C := Fintype.ofFinite C
  letI (X Y : C) : Fintype (X ⟶ Y) := Fintype.ofFinite (X ⟶ Y)
  let toSigma : NonzeroMorphismTo y → Σ X : C, X ⟶ y :=
    fun f ↦ ⟨f.source, f.hom⟩
  apply Finite.of_injective toSigma
  intro f g h
  cases f with
  | mk fs ff hf =>
      cases g with
      | mk gs gf hg =>
          dsimp [toSigma] at h
          cases h
          rfl

/-- A proper noninvertible prefactor gives a strict inequality in the
fixed-target order. -/
theorem lt_of_prefactor_noniso [IsFiniteRayCategory C]
    {f g : NonzeroMorphismTo y} (a : f.source ⟶ g.source)
    (hfg : a ≫ g.hom = f.hom) (ha : ¬IsIso a) :
    f < g := by
  refine lt_of_le_not_ge ⟨a, hfg⟩ ?_
  rintro ⟨b, hgf⟩
  have hab : a ≫ b = 𝟙 f.source := by
    apply ray_left_stabilizer_trivial f.hom (a ≫ b) f.ne_zero
    rw [Category.assoc, hgf, hfg]
  have hba : b ≫ a = 𝟙 g.source := by
    apply ray_left_stabilizer_trivial g.hom (b ≫ a) g.ne_zero
    rw [Category.assoc, hfg, hgf]
  exact ha ⟨⟨b, hab, hba⟩⟩

/-- If a noninvertible morphism lies above an irreducible one in the
fixed-target order, irreducibility reverses the comparison. -/
theorem reverse_le_of_le_irreducible_of_noniso [IsFiniteRayCategory C]
    {f g : NonzeroMorphismTo y} (hfg : f ≤ g)
    (hf : IsIrreducibleRayMorphism f.hom) (hg : ¬IsIso g.hom) :
    g ≤ f := by
  obtain ⟨a, ha⟩ := hfg
  rcases hf.2.2 g.source a g.hom ha with haIso | hgIso
  · letI : IsIso a := haIso
    refine ⟨inv a, ?_⟩
    rw [← ha, ← Category.assoc, IsIso.inv_hom_id,
      Category.id_comp]
  · exact (hg hgIso).elim

end NonzeroMorphismTo

namespace NonzeroHom

/-- Forget the fixed target of a nonzero morphism. -/
abbrev toMorphismFrom {X Y : C} (f : NonzeroHom X Y) :
    NonzeroMorphismFrom X where
  target := Y
  hom := f.1
  ne_zero := f.2

/-- Forget the fixed source of a nonzero morphism. -/
abbrev toMorphismTo {X Y : C} (f : NonzeroHom X Y) :
    NonzeroMorphismTo Y where
  source := X
  hom := f.1
  ne_zero := f.2

end NonzeroHom

/-- A nonzero irreducible path determines a member of the factorization
preorder out of its terminal ray vertex object. -/
def rayPathMorphism {i j : RayVertex C} (p : Quiver.Path i j)
    (hp : rayPathMap p ≠ 0) : NonzeroMorphismFrom j.obj where
  target := i.obj
  hom := rayPathMap p
  ne_zero := hp

/-- The same nonzero reversed-quiver path, viewed in the factorization order
with its category-theoretic target fixed. -/
def rayPathMorphismTo {i j : RayVertex C} (p : Quiver.Path i j)
    (hp : rayPathMap p ≠ 0) : NonzeroMorphismTo i.obj where
  source := j.obj
  hom := rayPathMap p
  ne_zero := hp

/-- Related ray paths determine the same nonzero morphism in `x/P`. -/
theorem rayPathMorphism_eq_of_related
    {i j : RayVertex C} (p q : Quiver.Path i j)
    (hpq : (rayPathContourRelation (C := C)).related p q) :
    rayPathMorphism p hpq.1 =
      rayPathMorphism q (by
        rw [← hpq.2]
        exact hpq.1) := by
  refine NonzeroMorphismFrom.ext
    (f := rayPathMorphism p hpq.1)
    (g := rayPathMorphism q (by
      rw [← hpq.2]
      exact hpq.1))
    (htarget := rfl) ?_
  change rayPathMap p ≫ 𝟙 i.obj = rayPathMap q
  simpa using hpq.2

/-- Related ray paths also determine the same element of the fixed-target
factorization order. -/
theorem rayPathMorphismTo_eq_of_related
    {i j : RayVertex C} (p q : Quiver.Path i j)
    (hpq : (rayPathContourRelation (C := C)).related p q) :
    rayPathMorphismTo p hpq.1 =
      rayPathMorphismTo q (by
        rw [← hpq.2]
        exact hpq.1) := by
  refine NonzeroMorphismTo.ext
    (f := rayPathMorphismTo p hpq.1)
    (g := rayPathMorphismTo q (by
      rw [← hpq.2]
      exact hpq.1))
    (hsource := rfl) ?_
  change 𝟙 j.obj ≫ rayPathMap q = rayPathMap p
  simpa using hpq.2.symm

end LargeIndecomposable
