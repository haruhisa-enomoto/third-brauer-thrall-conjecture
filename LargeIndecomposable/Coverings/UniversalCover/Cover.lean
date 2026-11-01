module

public import LargeIndecomposable.FundamentalGroups.Basic.Fundamental
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Algebra.Group.Action.Defs

/-!
# The universal cover of a ray category

For a ray category `P` and a base object `x₀`, the universal cover `P̃` has
objects `(y, u)` with `u : x₀ ⟶ y` in the fundamental groupoid, and a nonzero
morphism `(y, u) ⟶ (z, w)` is a nonzero `f : y ⟶ z` with `w = u ≫ [f]`; the
other morphism is zero (Gabriel–Roiter 14.1; BGRS Section 10). Composition is
that of `P`, replaced by zero when the composite vanishes. The projection
`(y, u) ↦ y` is a functor `P̃ ⥤ P` (`Cover.proj`), `P̃` satisfies the ray axioms,
and the fundamental group `Π(P, x₀)` acts freely on the objects, transitively
on each fibre (`Cover.smul_eq_self`, `Cover.exists_smul_eq`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe v u

namespace RayCat

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- The vertex of the fundamental groupoid at an object. -/
abbrev vtx (y : P) : FundGroupoid P :=
  CategoryTheory.Quotient.mk ((Quiver.FreeGroupoid.of (RayVert P)).obj (RayVert.mk y))

lemma cls_id (y : P) : cls (𝟙 y) (IsRayCategory.id_ne_zero y) = 𝟙 (vtx y) := by
  rw [cls_eq (𝟙 y) _ Quiver.Path.nil rfl]
  exact (CategoryTheory.Quotient.functor homotopy).map_id _

variable (x₀ : P)

/-- The objects of the universal cover. -/
structure Cover where
  /-- The underlying object. -/
  y : P
  /-- The homotopy class of a walk from the base object. -/
  u : vtx x₀ ⟶ vtx y

namespace Cover

variable {x₀}

/-- The nonzero morphisms of the universal cover. -/
def NZHom (a b : Cover x₀) : Type v :=
  {f : a.y ⟶ b.y // ∃ hf : f ≠ 0, b.u = a.u ≫ cls f hf}

/-- Composition of nonzero morphisms, zero if the composite vanishes. -/
def compNZ {a b c : Cover x₀} (f : NZHom a b) (g : NZHom b c) : Option (NZHom a c) := by
  classical
  exact if h : f.1 ≫ g.1 = 0 then none else
    some ⟨f.1 ≫ g.1, h, by
      have hf := f.2.choose_spec
      have hg := g.2.choose_spec
      calc c.u = b.u ≫ cls g.1 g.2.choose := hg
        _ = (a.u ≫ cls f.1 f.2.choose) ≫ cls g.1 g.2.choose := by rw [← hf]
        _ = a.u ≫ cls (f.1 ≫ g.1) h := by rw [cls_comp f.1 g.1 h, Category.assoc]⟩

/-- The underlying morphism of `P` (zero for `none`). -/
def val {a b : Cover x₀} : Option (NZHom a b) → (a.y ⟶ b.y)
  | none => 0
  | some f => f.1

lemma val_injective {a b : Cover x₀} : Function.Injective (val (a := a) (b := b)) := by
  rintro (_ | f) (_ | g) h
  · rfl
  · exact absurd h.symm g.2.1
  · exact absurd h f.2.1
  · exact congrArg some (Subtype.ext h)

/-- The composite of two morphisms. -/
def comp' {a b c : Cover x₀} (f : Option (NZHom a b)) (g : Option (NZHom b c)) :
    Option (NZHom a c) :=
  f.bind fun f ↦ g.bind fun g ↦ compNZ f g

lemma val_comp' {a b c : Cover x₀} (f : Option (NZHom a b)) (g : Option (NZHom b c)) :
    val (comp' f g) = val f ≫ val g := by
  rcases f with _ | f
  · exact (zero_comp).symm
  rcases g with _ | g
  · exact (comp_zero).symm
  change val (compNZ f g) = f.1 ≫ g.1
  unfold compNZ
  split_ifs with h
  · exact h.symm
  · rfl

/-- The category structure: a morphism is `none` (zero) or a nonzero morphism. -/
instance : Category.{v} (Cover x₀) where
  Hom a b := Option (NZHom a b)
  id a := some ⟨𝟙 a.y, IsRayCategory.id_ne_zero a.y, by rw [cls_id, Category.comp_id]⟩
  comp f g := comp' f g
  id_comp f := val_injective (by rw [val_comp']; exact Category.id_comp _)
  comp_id f := val_injective (by rw [val_comp']; exact Category.comp_id _)
  assoc f g h := val_injective (by rw [val_comp', val_comp', val_comp', val_comp', Category.assoc])

lemma val_comp {a b c : Cover x₀} (f : a ⟶ b) (g : b ⟶ c) : val (f ≫ g) = val f ≫ val g :=
  val_comp' f g

lemma val_id (a : Cover x₀) : val (𝟙 a) = 𝟙 a.y := rfl

instance : HasZeroMorphisms (Cover x₀) where
  zero _ _ := ⟨none⟩
  comp_zero _ _ := val_injective (by rw [val_comp]; exact comp_zero)
  zero_comp _ _ _ _ := val_injective (by rw [val_comp]; exact zero_comp)

lemma val_zero {a b : Cover x₀} : val (0 : a ⟶ b) = 0 := rfl

lemma val_eq_zero_iff {a b : Cover x₀} (f : a ⟶ b) : val f = 0 ↔ f = 0 :=
  ⟨fun h ↦ val_injective h, fun h ↦ h ▸ val_zero⟩

variable (x₀) in
/-- The covering functor `P̃ ⥤ P`. -/
def proj : Cover x₀ ⥤ P where
  obj a := a.y
  map f := val f
  map_id _ := rfl
  map_comp f g := val_comp f g

lemma val_rpow {a : Cover x₀} (e : a ⟶ a) : ∀ n, val (rpow e n) = rpow (val e) n
  | 0 => rfl
  | n + 1 => by rw [rpow_succ, rpow_succ, val_comp, val_rpow e n]

omit [IsRayCategory P] in
lemma ext' {a b : Cover x₀} (hy : a.y = b.y) (hu : b.u = a.u ≫ eqToHom (by rw [hy])) : a = b := by
  obtain ⟨y, u⟩ := a
  obtain ⟨y', u'⟩ := b
  change y = y' at hy
  subst hy
  simp only [eqToHom_refl, Category.comp_id] at hu
  rw [hu]

instance : IsRayCategory (Cover x₀) where
  skeletal a b h := by
    obtain ⟨i⟩ := h
    have h1 : val i.hom ≫ val i.inv = 𝟙 a.y := by rw [← val_comp, i.hom_inv_id]; rfl
    have h2 : val i.inv ≫ val i.hom = 𝟙 b.y := by rw [← val_comp, i.inv_hom_id]; rfl
    have hy : a.y = b.y := IsRayCategory.skeletal ⟨⟨_, _, h1, h2⟩⟩
    obtain ⟨y, u⟩ := a
    obtain ⟨y', u'⟩ := b
    change y = y' at hy
    subst hy
    rcases hi : i.hom with _ | f
    · exact absurd (by rw [hi] at h1; simpa [val] using h1.symm) (IsRayCategory.id_ne_zero y)
    · have hf1 : f.1 = 𝟙 y := by
        have e : 𝟙 y = f.1 ≫ 𝟙 y ≫ val i.inv := by rw [Category.id_comp, ← h1, hi]; rfl
        exact (IsRayCategory.eq_id_of_two_sided _ (IsRayCategory.id_ne_zero y) _ _ e).1
      obtain ⟨hf, hfu⟩ := f.2
      change u' = u ≫ cls f.1 hf at hfu
      have : cls f.1 hf = 𝟙 (vtx y) := by
        rw [← cls_id]; congr 1
      rw [this, Category.comp_id] at hfu
      rw [hfu]
  finite_out a := by
    classical
    have hfin := IsRayCategory.finite_out a.y
    let T : Set (Cover x₀) := ⋃ z ∈ {z : P | ∃ f : a.y ⟶ z, f ≠ 0},
      Set.range (fun f : {f : a.y ⟶ z // f ≠ 0} ↦ (⟨z, a.u ≫ cls f.1 f.2⟩ : Cover x₀))
    have hT : T.Finite := Set.Finite.biUnion hfin fun z _ ↦ by
      have := IsRayCategory.finite_hom a.y z
      exact Set.finite_range _
    refine hT.subset ?_
    rintro b ⟨f, hf⟩
    rcases f with _ | f
    · exact absurd rfl hf
    · obtain ⟨hf0, hfu⟩ := f.2
      simp only [T, Set.mem_iUnion, Set.mem_range]
      refine ⟨b.y, ⟨f.1, hf0⟩, ⟨f.1, hf0⟩, ext' rfl ?_⟩
      rw [eqToHom_refl, Category.comp_id]
      exact hfu
  finite_in a := by
    classical
    have hfin := IsRayCategory.finite_in a.y
    let T : Set (Cover x₀) := ⋃ z ∈ {z : P | ∃ f : z ⟶ a.y, f ≠ 0},
      Set.range (fun f : {f : z ⟶ a.y // f ≠ 0} ↦ (⟨z, a.u ≫ inv (cls f.1 f.2)⟩ : Cover x₀))
    have hT : T.Finite := Set.Finite.biUnion hfin fun z _ ↦ by
      have := IsRayCategory.finite_hom z a.y
      exact Set.finite_range _
    refine hT.subset ?_
    rintro b ⟨f, hf⟩
    rcases f with _ | f
    · exact absurd rfl hf
    · obtain ⟨hf0, hfu⟩ := f.2
      simp only [T, Set.mem_iUnion, Set.mem_range]
      refine ⟨b.y, ⟨f.1, hf0⟩, ⟨f.1, hf0⟩, ext' rfl ?_⟩
      rw [eqToHom_refl, Category.comp_id]
      change a.u = b.u ≫ cls f.1 hf0 at hfu
      generalize cls f.1 hf0 = c at hfu ⊢
      rw [hfu, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  finite_hom a b := by
    have := IsRayCategory.finite_hom a.y b.y
    change Finite (Option (NZHom a b))
    unfold NZHom
    infer_instance
  id_ne_zero a h := Option.some_ne_none _ h
  nil a e he := by
    have hv : val e ≠ 𝟙 a.y := fun h ↦ he (val_injective (h.trans (val_id a).symm))
    obtain ⟨n, hn⟩ := IsRayCategory.nil a.y (val e) hv
    exact ⟨n, (val_eq_zero_iff _).1 ((val_rpow e n).trans hn)⟩

variable (x₀) in
/-- The fundamental group `Π(P, x₀)`. -/
abbrev Pi1 : Type _ := Aut (vtx x₀)

/-- The deck action on objects: `g · (y, u) = (y, g ≫ u)`. -/
instance : MulAction (Pi1 x₀) (Cover x₀) where
  smul g a := ⟨a.y, g.inv ≫ a.u⟩
  one_smul a := by
    change (⟨a.y, 𝟙 _ ≫ a.u⟩ : Cover x₀) = a
    rw [Category.id_comp]
  mul_smul g h a := by
    change (⟨a.y, (g * h).inv ≫ a.u⟩ : Cover x₀) = ⟨a.y, g.inv ≫ h.inv ≫ a.u⟩
    rw [show (g * h).inv = g.inv ≫ h.inv from rfl, Category.assoc]

omit [IsRayCategory P] in
lemma smul_y (g : Pi1 x₀) (a : Cover x₀) : (g • a).y = a.y := rfl

omit [IsRayCategory P] in
lemma smul_u (g : Pi1 x₀) (a : Cover x₀) : (g • a).u = g.inv ≫ a.u := rfl

omit [IsRayCategory P] in
/-- The deck action is free. -/
theorem smul_eq_self {g : Pi1 x₀} {a : Cover x₀} (h : g • a = a) : g = 1 := by
  obtain ⟨y, u⟩ := a
  have hu : g.inv ≫ u = u := eq_of_heq (Cover.mk.inj h).2
  have : g.inv = 𝟙 _ := by simpa using congrArg (· ≫ inv u) hu
  have h1 : g.hom = 𝟙 _ :=
    calc g.hom = g.hom ≫ g.inv := by rw [this, Category.comp_id]
      _ = 𝟙 _ := g.hom_inv_id
  exact Aut.ext h1

omit [IsRayCategory P] in
/-- Objects over the same object of `P` lie in one orbit. -/
theorem exists_smul_eq {a b : Cover x₀} (h : a.y = b.y) : ∃ g : Pi1 x₀, g • a = b := by
  obtain ⟨y, u⟩ := a
  obtain ⟨y', u'⟩ := b
  change y = y' at h
  subst h
  refine ⟨(asIso (u' ≫ inv u)).symm, ?_⟩
  change (⟨y, (u' ≫ inv u) ≫ u⟩ : Cover x₀) = _
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

omit [IsRayCategory P] in
lemma smul_mk (g : Pi1 x₀) (y : P) (u : vtx x₀ ⟶ vtx y) :
    g • (⟨y, u⟩ : Cover x₀) = ⟨y, g.inv ≫ u⟩ := rfl

/-- A deck transformation on nonzero morphisms. -/
def deckNZ (g : Pi1 x₀) {a b : Cover x₀} (f : NZHom a b) : NZHom (g • a) (g • b) :=
  ⟨f.1, f.2.1, by
    change g.inv ≫ b.u = (g.inv ≫ a.u) ≫ cls f.1 f.2.1
    exact (congrArg (fun t ↦ g.inv ≫ t) f.2.2).trans (Category.assoc _ _ _).symm⟩

lemma val_map_deck (g : Pi1 x₀) {a b : Cover x₀} (o : Option (NZHom a b)) :
    val (o.map (deckNZ g)) = val o := by
  rcases o with _ | f <;> rfl

/-- The deck transformation of `g` as an automorphism functor of the cover. -/
def deck (g : Pi1 x₀) : Cover x₀ ⥤ Cover x₀ where
  obj a := g • a
  map f := Option.map (deckNZ g) f
  map_id a := rfl
  map_comp f g' := val_injective (by
    change val ((comp' f g').map (deckNZ g)) =
      val (comp' (f.map (deckNZ g)) (g'.map (deckNZ g)))
    rw [val_map_deck, val_comp', val_comp', val_map_deck, val_map_deck])

lemma val_deck_map (g : Pi1 x₀) {a b : Cover x₀} (f : a ⟶ b) : val ((deck g).map f) = val f :=
  val_map_deck g f

/-- Deck transformations lie over `P`. -/
lemma proj_deck (g : Pi1 x₀) {a b : Cover x₀} (f : a ⟶ b) :
    (proj x₀).map ((deck g).map f) = (proj x₀).map f :=
  val_deck_map g f

end Cover

end RayCat

end LargeIndecomposable
