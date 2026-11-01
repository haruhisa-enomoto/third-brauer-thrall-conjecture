module

public import LargeIndecomposable.RayCategories.RoiterVanishing.RayResidueMeasure
public import LargeIndecomposable.RayCategories.RoiterVanishing.RayEfficientHookContour

@[expose] public section

/-!
# Maximal nonzero ray paths through an arrow

BGRS 8.6 chooses a nonzero path of maximal length through the last arrow of
an efficient tackle and annihilates its ray in a residue category.  This file
packages that finite maximization and its immediate extension obstructions.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A nonzero irreducible path with a specified occurrence of one selected
arrow. -/
structure NonzeroRayPathThroughArrow
    (a : BundledQuiverArrow (RayVertex C)) where
  source : RayVertex C
  target : RayVertex C
  path : Quiver.Path source target
  occurrence : BundledArrowOccurrence a path
  map_ne_zero : rayPathMap path ≠ 0

namespace NonzeroRayPathThroughArrow

variable {a : BundledQuiverArrow (RayVertex C)}

/-- The length of a nonzero path through the selected arrow. -/
abbrev length (p : NonzeroRayPathThroughArrow (C := C) a) : ℕ :=
  p.path.length

/-- Forget the chosen path and occurrence, retaining its represented nonzero
category morphism with varying endpoints. -/
def toNonzeroCategoryMorphism
    (p : NonzeroRayPathThroughArrow (C := C) a) :
    NonzeroCategoryMorphism C :=
  ⟨p.target.obj, p.source.obj, rayPathMap p.path, p.map_ne_zero⟩

/-- The selected arrow itself is a nonzero path through that arrow. -/
def ofArrow (a : BundledQuiverArrow (RayVertex C)) :
    NonzeroRayPathThroughArrow (C := C) a where
  source := a.1
  target := a.2.1
  path := a.2.2.toPath
  occurrence :=
    { before := Quiver.Path.nil
      after := Quiver.Path.nil
      path_eq := by
        simp only [Quiver.Path.comp_nil, Quiver.Path.nil_comp] }
  map_ne_zero := by
    rw [rayPathMap_toPath]
    exact a.2.2.property.1

/-- A path through an arrow is nonempty. -/
theorem length_ne_zero (p : NonzeroRayPathThroughArrow (C := C) a) :
    p.length ≠ 0 := by
  intro hzero
  change p.path.length = 0 at hzero
  rw [p.occurrence.path_eq] at hzero
  simp at hzero

/-- Maximality among all nonzero irreducible paths containing the same
selected arrow. -/
def IsMaximal (p : NonzeroRayPathThroughArrow (C := C) a) : Prop :=
  ∀ q : NonzeroRayPathThroughArrow (C := C) a, q.length ≤ p.length

/-- The set of lengths realized by nonzero paths through one arrow. -/
def IsLength (a : BundledQuiverArrow (RayVertex C)) (n : ℕ) : Prop :=
  ∃ p : NonzeroRayPathThroughArrow (C := C) a, p.length = n

/-- A selected arrow lies on a maximal-length nonzero path. -/
theorem exists_isMaximal
    [Finite C] [IsFiniteRayCategory C]
    (a : BundledQuiverArrow (RayVertex C)) :
    ∃ p : NonzeroRayPathThroughArrow (C := C) a, p.IsMaximal := by
  classical
  let bound := Nat.card (NonzeroCategoryMorphism C)
  have harrow : IsLength (C := C) a (ofArrow a).length :=
    ⟨ofArrow a, rfl⟩
  have harrowBound : (ofArrow a).length ≤ bound := by
    have hlt := rayPath_length_lt_nonzeroCategoryMorphism_card
      (ofArrow a).path (ofArrow a).map_ne_zero
    exact Nat.le_of_lt hlt
  obtain ⟨p, hpLength⟩ := Nat.findGreatest_spec
    (P := IsLength (C := C) a) harrowBound harrow
  refine ⟨p, ?_⟩
  intro q
  rw [hpLength]
  apply Nat.le_findGreatest
  · have hlt := rayPath_length_lt_nonzeroCategoryMorphism_card
      q.path q.map_ne_zero
    exact Nat.le_of_lt hlt
  · exact ⟨q, rfl⟩

/-- Prepending a nonidentity path to a maximal path through the selected arrow
forces the resulting ray path to vanish. -/
theorem IsMaximal.rayPathMap_prepend_eq_zero
    [Finite C] [IsFiniteRayCategory C]
    (p : NonzeroRayPathThroughArrow (C := C) a) (hp : p.IsMaximal)
    {w : RayVertex C} (r : Quiver.Path w p.source)
    (hr : r.length ≠ 0) :
    rayPathMap (r.comp p.path) = 0 := by
  by_contra hnonzero
  let q : NonzeroRayPathThroughArrow (C := C) a :=
    { source := w
      target := p.target
      path := r.comp p.path
      occurrence := p.occurrence.prepend r
      map_ne_zero := hnonzero }
  have hle := hp q
  change (r.comp p.path).length ≤ p.path.length at hle
  simp at hle
  omega

/-- Appending a nonidentity path to a maximal path through the selected arrow
forces the resulting ray path to vanish. -/
theorem IsMaximal.rayPathMap_append_eq_zero
    [Finite C] [IsFiniteRayCategory C]
    (p : NonzeroRayPathThroughArrow (C := C) a) (hp : p.IsMaximal)
    {z : RayVertex C} (r : Quiver.Path p.target z)
    (hr : r.length ≠ 0) :
    rayPathMap (p.path.comp r) = 0 := by
  by_contra hnonzero
  let q : NonzeroRayPathThroughArrow (C := C) a :=
    { source := p.source
      target := z
      path := p.path.comp r
      occurrence := p.occurrence.append r
      map_ne_zero := hnonzero }
  have hle := hp q
  change (p.path.comp r).length ≤ p.path.length at hle
  simp at hle
  omega

/-- A nonzero morphism prepended categorically to a maximal path must be an
isomorphism whenever the composite remains nonzero. -/
theorem IsMaximal.leftFactor_isIso
    [Finite C] [IsFiniteRayCategory C]
    (p : NonzeroRayPathThroughArrow (C := C) a) (hp : p.IsMaximal)
    {X : C} (f : X ⟶ p.target.obj) (hf : f ≠ 0)
    (hcomp : f ≫ rayPathMap p.path ≠ 0) :
    IsIso f := by
  let fNonzero : NonzeroHom X p.target.obj := ⟨f, hf⟩
  obtain ⟨q⟩ := rayPathPresentation_nonempty_of_finite fNonzero
  let htarget : RayVertex.mk p.target.obj = p.target :=
    rayVertexEquiv.left_inv p.target
  let qPath : Quiver.Path p.target (RayVertex.mk X) :=
    htarget ▸ q.path
  have hqMap : rayPathMap qPath = f := by
    dsimp [qPath, htarget]
    simpa using q.map_eq
  have hqNonzero : rayPathMap (p.path.comp qPath) ≠ 0 := by
    simp only [rayPathMap, LinearPathCategory.pathMap_comp]
    change rayPathMap qPath ≫ rayPathMap p.path ≠ 0
    rw [hqMap]
    exact hcomp
  let extended : NonzeroRayPathThroughArrow (C := C) a :=
    { source := p.source
      target := RayVertex.mk X
      path := p.path.comp qPath
      occurrence := p.occurrence.append qPath
      map_ne_zero := hqNonzero }
  have hqLength : qPath.length = 0 := by
    have hle := hp extended
    change (p.path.comp qPath).length ≤ p.path.length at hle
    simp at hle
    omega
  rw [← hqMap]
  exact rayPathMap_isIso_of_length_eq_zero qPath hqLength

/-- A nonzero morphism appended categorically to a maximal path must be an
isomorphism whenever the composite remains nonzero. -/
theorem IsMaximal.rightFactor_isIso
    [Finite C] [IsFiniteRayCategory C]
    (p : NonzeroRayPathThroughArrow (C := C) a) (hp : p.IsMaximal)
    {Y : C} (g : p.source.obj ⟶ Y) (hg : g ≠ 0)
    (hcomp : rayPathMap p.path ≫ g ≠ 0) :
    IsIso g := by
  let gNonzero : NonzeroHom p.source.obj Y := ⟨g, hg⟩
  obtain ⟨q⟩ := rayPathPresentation_nonempty_of_finite gNonzero
  let hsource : RayVertex.mk p.source.obj = p.source :=
    rayVertexEquiv.left_inv p.source
  let qPath : Quiver.Path (RayVertex.mk Y) p.source :=
    hsource ▸ q.path
  have hqMap : rayPathMap qPath = g := by
    dsimp [qPath, hsource]
    simpa using q.map_eq
  have hqNonzero : rayPathMap (qPath.comp p.path) ≠ 0 := by
    simp only [rayPathMap, LinearPathCategory.pathMap_comp]
    change rayPathMap p.path ≫ rayPathMap qPath ≠ 0
    rw [hqMap]
    exact hcomp
  let extended : NonzeroRayPathThroughArrow (C := C) a :=
    { source := RayVertex.mk Y
      target := p.target
      path := qPath.comp p.path
      occurrence := p.occurrence.prepend qPath
      map_ne_zero := hqNonzero }
  have hqLength : qPath.length = 0 := by
    have hle := hp extended
    change (qPath.comp p.path).length ≤ p.path.length at hle
    simp at hle
    omega
  rw [← hqMap]
  exact rayPathMap_isIso_of_length_eq_zero qPath hqLength

/-- Every nonzero factorization through the ray of a maximal path has
invertible outer factors. -/
theorem IsMaximal.outerFactors_isIso_of_factorsThrough
    [Finite C] [IsFiniteRayCategory C]
    (p : NonzeroRayPathThroughArrow (C := C) a) (hp : p.IsMaximal)
    {X Y : C} (f : X ⟶ Y) (hf : f ≠ 0)
    (hfactor : FactorsThroughMorphism (rayPathMap p.path) f) :
    ∃ (l : X ⟶ p.target.obj) (r : p.source.obj ⟶ Y),
      f = l ≫ rayPathMap p.path ≫ r ∧ IsIso l ∧ IsIso r := by
  obtain ⟨l, r, hfactor⟩ := hfactor
  have hl : l ≠ 0 := by
    intro hzero
    apply hf
    rw [hfactor, hzero]
    simp
  have hr : r ≠ 0 := by
    intro hzero
    apply hf
    rw [hfactor, hzero]
    simp
  have hlcomp : l ≫ rayPathMap p.path ≠ 0 := by
    intro hzero
    apply hf
    rw [hfactor, ← Category.assoc, hzero]
    simp
  have hcompr : rayPathMap p.path ≫ r ≠ 0 := by
    intro hzero
    apply hf
    rw [hfactor, hzero]
    simp
  exact ⟨l, r, hfactor,
    hp.leftFactor_isIso p l hl hlcomp,
    hp.rightFactor_isIso p r hr hcompr⟩

/-- In the Hom set of the maximal path itself, its principal ideal contains
no other nonzero ray. -/
theorem IsMaximal.eq_of_factorsThrough_sameEndpoints
    [Finite C] [IsFiniteRayCategory C]
    (p : NonzeroRayPathThroughArrow (C := C) a) (hp : p.IsMaximal)
    (f : p.target.obj ⟶ p.source.obj) (hf : f ≠ 0)
    (hfactor : FactorsThroughMorphism (rayPathMap p.path) f) :
    f = rayPathMap p.path := by
  obtain ⟨l, r, hfactor, hl, hr⟩ :=
    hp.outerFactors_isIso_of_factorsThrough p f hf hfactor
  letI : IsIso l := hl
  letI : IsIso r := hr
  rw [hfactor, ray_endomorphism_eq_id_of_isIso l,
    ray_endomorphism_eq_id_of_isIso r]
  simp

/-- Globally, the only nonzero morphism in the principal ideal of a maximal
path ray is that ray itself. -/
theorem IsMaximal.eq_toNonzeroCategoryMorphism_of_factorsThrough
    [Finite C] [IsFiniteRayCategory C]
    (p : NonzeroRayPathThroughArrow (C := C) a) (hp : p.IsMaximal)
    (f : NonzeroCategoryMorphism C)
    (hfactor : FactorsThroughMorphism (rayPathMap p.path) f.hom) :
    f = p.toNonzeroCategoryMorphism := by
  rcases f with ⟨X, Y, f, hf⟩
  obtain ⟨l, r, hfactor, hl, hr⟩ :=
    hp.outerFactors_isIso_of_factorsThrough p f hf hfactor
  letI : IsIso l := hl
  letI : IsIso r := hr
  have hX : X = p.target.obj :=
    IsFiniteRayCategory.skeletal ⟨asIso l⟩
  have hY : p.source.obj = Y :=
    IsFiniteRayCategory.skeletal ⟨asIso r⟩
  subst X
  subst Y
  rw [ray_endomorphism_eq_id_of_isIso l,
    ray_endomorphism_eq_id_of_isIso r] at hfactor
  simp at hfactor
  subst f
  rfl

/-- Membership in the principal ideal of a maximal path ray is exactly
equality with that one nonzero category morphism. -/
theorem IsMaximal.factorsThrough_iff_eq_toNonzeroCategoryMorphism
    [Finite C] [IsFiniteRayCategory C]
    (p : NonzeroRayPathThroughArrow (C := C) a) (hp : p.IsMaximal)
    (f : NonzeroCategoryMorphism C) :
    FactorsThroughMorphism (rayPathMap p.path) f.hom ↔
      f = p.toNonzeroCategoryMorphism := by
  constructor
  · exact hp.eq_toNonzeroCategoryMorphism_of_factorsThrough p f
  · rintro rfl
    change FactorsThroughMorphism
      (rayPathMap p.path) (rayPathMap p.path)
    exact ⟨𝟙 p.target.obj, 𝟙 p.source.obj, by simp⟩

/-- The residue functor of a maximal path kills a nonzero morphism exactly
when it is the distinguished maximal ray. -/
theorem IsMaximal.residue_map_ne_zero_iff_ne
    [Finite C] [IsFiniteRayCategory C]
    (p : NonzeroRayPathThroughArrow (C := C) a) (hp : p.IsMaximal)
    (f : NonzeroCategoryMorphism C) :
    (rayResidueFunctor (rayPathMap p.path)).map f.hom ≠ 0 ↔
      f ≠ p.toNonzeroCategoryMorphism := by
  constructor
  · intro hmap hfeq
    apply hmap
    apply (rayResidueFunctor_map_eq_zero_iff
      (rayPathMap p.path) f.hom).2
    exact (hp.factorsThrough_iff_eq_toNonzeroCategoryMorphism p f).2 hfeq
  · intro hf hmap
    apply hf
    apply (hp.factorsThrough_iff_eq_toNonzeroCategoryMorphism p f).1
    exact (rayResidueFunctor_map_eq_zero_iff
      (rayPathMap p.path) f.hom).1 hmap

/-- For a fixed-endpoint nonzero morphism, membership in the maximal path's
principal ideal is equality with the distinguished global ray. -/
theorem IsMaximal.principalZeroHomIdeal_mem_iff_eq
    [Finite C] [IsFiniteRayCategory C]
    (p : NonzeroRayPathThroughArrow (C := C) a) (hp : p.IsMaximal)
    {X Y : C} (f : NonzeroHom X Y) :
    (principalZeroHomIdeal (rayPathMap p.path)).mem f.1 ↔
      f.toNonzeroCategoryMorphism = p.toNonzeroCategoryMorphism := by
  exact hp.factorsThrough_iff_eq_toNonzeroCategoryMorphism
    p f.toNonzeroCategoryMorphism

/-- The ray morphism represented by a path through an arrow is
noninvertible, so its principal residue category is proper. -/
theorem map_not_isIso
    [IsFiniteRayCategory C]
    (p : NonzeroRayPathThroughArrow (C := C) a) :
    ¬IsIso (rayPathMap p.path) :=
  rayPathMap_not_isIso_of_length_ne_zero p.path p.length_ne_zero

/-- Annihilating the ray of a maximal path through an arrow strictly lowers
the total nonzero-morphism induction measure. -/
theorem residue_nonzeroMorphism_card_lt
    [Finite C] [IsFiniteRayCategory C]
    (p : NonzeroRayPathThroughArrow (C := C) a) :
    letI : IsFiniteRayCategory (RayResidueCategory (rayPathMap p.path)) :=
      rayResidueCategory_isFiniteRayCategory
        (rayPathMap p.path) p.map_not_isIso
    Nat.card (NonzeroCategoryMorphism
        (RayResidueCategory (rayPathMap p.path))) <
      Nat.card (NonzeroCategoryMorphism C) := by
  letI : IsFiniteRayCategory (RayResidueCategory (rayPathMap p.path)) :=
    rayResidueCategory_isFiniteRayCategory
      (rayPathMap p.path) p.map_not_isIso
  exact rayResidueCategory_nonzeroMorphism_card_lt
    (rayPathMap p.path) p.map_ne_zero p.map_not_isIso

end NonzeroRayPathThroughArrow

namespace RayTackle

/-- Every component of a tackle is different from one selected global
nonzero morphism.  This is the source's "components different from `mu`"
condition in BGRS 8.6. -/
def AvoidsNonzeroCategoryMorphism (mu : NonzeroCategoryMorphism C) :
    RayTackle C → Prop
  | .hook _ t =>
      (∀ i, (t.rho i).toNonzeroCategoryMorphism ≠ mu) ∧
        (∀ i, (t.sigma i).toNonzeroCategoryMorphism ≠ mu)
  | .cohook _ t =>
      (∀ i, (t.rho i).toNonzeroCategoryMorphism ≠ mu) ∧
        (∀ i, (t.sigma i).toNonzeroCategoryMorphism ≠ mu)

end RayTackle

/-- For the principal ideal of a maximal path, a tackle survives the quotient
exactly when all of its components are different from the selected ray. -/
theorem NonzeroRayPathThroughArrow.IsMaximal.componentsSurvive_principal_iff
    [Finite C] [IsFiniteRayCategory C]
    {a : BundledQuiverArrow (RayVertex C)}
    (p : NonzeroRayPathThroughArrow (C := C) a) (hp : p.IsMaximal)
    (t : RayTackle C) :
    t.ComponentsSurvive (principalZeroHomIdeal (rayPathMap p.path)) ↔
      t.AvoidsNonzeroCategoryMorphism p.toNonzeroCategoryMorphism := by
  cases t <;>
    simp only [RayTackle.ComponentsSurvive,
      RayTackle.AvoidsNonzeroCategoryMorphism,
      hp.principalZeroHomIdeal_mem_iff_eq]

/-- Map a tackle avoiding the selected maximal ray into its principal residue
category. -/
def RayTackle.mapMaximalPathResidue
    [Finite C] [IsFiniteRayCategory C]
    {a : BundledQuiverArrow (RayVertex C)}
    (p : NonzeroRayPathThroughArrow (C := C) a) (hp : p.IsMaximal)
    (t : RayTackle C)
    (ht : t.AvoidsNonzeroCategoryMorphism p.toNonzeroCategoryMorphism) :
    RayTackle (RayResidueCategory (rayPathMap p.path)) :=
  t.mapQuotient (principalZeroHomIdeal (rayPathMap p.path))
    (principalZeroHomIdeal_isProper_of_not_isIso
      (rayPathMap p.path) p.map_not_isIso)
    ((hp.componentsSurvive_principal_iff p t).2 ht)

/-- Lift a tackle from the principal residue of a maximal path to chosen
original representatives. -/
def RayTackle.quotOutMaximalPathResidue
    [IsFiniteRayCategory C]
    {a : BundledQuiverArrow (RayVertex C)}
    (p : NonzeroRayPathThroughArrow (C := C) a)
    (t : RayTackle (RayResidueCategory (rayPathMap p.path))) :
    RayTackle C :=
  t.quotOut (principalZeroHomIdeal_isProper_of_not_isIso
    (rayPathMap p.path) p.map_not_isIso)

/-- Every tackle lifted from the maximal-path residue avoids precisely the
distinguished maximal ray. -/
theorem RayTackle.quotOutMaximalPathResidue_avoids
    [Finite C] [IsFiniteRayCategory C]
    {a : BundledQuiverArrow (RayVertex C)}
    (p : NonzeroRayPathThroughArrow (C := C) a) (hp : p.IsMaximal)
    (t : RayTackle (RayResidueCategory (rayPathMap p.path))) :
    (t.quotOutMaximalPathResidue p).AvoidsNonzeroCategoryMorphism
      p.toNonzeroCategoryMorphism := by
  apply (hp.componentsSurvive_principal_iff
    p (t.quotOutMaximalPathResidue p)).1
  exact RayTackle.componentsSurvive_quotOut
    (principalZeroHomIdeal_isProper_of_not_isIso
      (rayPathMap p.path) p.map_not_isIso) t

/-- The last hook of a tackle lies on a maximal-length nonzero path. -/
theorem RayHookTackle.exists_maximalNonzeroRayPathThroughLastArrow
    [Finite C] [IsFiniteRayCategory C]
    {m : ℕ} (t : RayHookTackle (C := C) m) :
    ∃ p : NonzeroRayPathThroughArrow
        (C := C) (bundledQuiverArrow t.lastArrow),
      p.IsMaximal :=
  NonzeroRayPathThroughArrow.exists_isMaximal
    (bundledQuiverArrow t.lastArrow)

/-- The last cohook of a tackle lies on a maximal-length nonzero path. -/
theorem RayCohookTackle.exists_maximalNonzeroRayPathThroughLastArrow
    [Finite C] [IsFiniteRayCategory C]
    {m : ℕ} (t : RayCohookTackle (C := C) m) :
    ∃ p : NonzeroRayPathThroughArrow
        (C := C) (bundledQuiverArrow t.lastArrow),
      p.IsMaximal :=
  NonzeroRayPathThroughArrow.exists_isMaximal
    (bundledQuiverArrow t.lastArrow)

end LargeIndecomposable
