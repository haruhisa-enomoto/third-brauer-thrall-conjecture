module

public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Set.Card
public import LargeIndecomposable.RayCategories.Basic.RayMorphismOrder

@[expose] public section

/-!
# Depth of a nonzero ray morphism

BGRS 8.4 defines the depth of a nonzero ray morphism as the maximal length of
an irreducible path representing it.  This file packages that definition under
an existence-and-boundedness class, then derives the class from finiteness and
the finite ray-category axioms.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- An irreducible-path presentation of a fixed nonzero ray morphism. -/
structure RayPathPresentation {x : C} (f : NonzeroMorphismFrom x) where
  path : Quiver.Path (RayVertex.mk f.target) (RayVertex.mk x)
  map_eq : rayPathMap path = f.hom

namespace RayPathPresentation

variable {x : C} {f : NonzeroMorphismFrom x}

/-- The length of a ray-path presentation. -/
abbrev length (p : RayPathPresentation f) : ℕ := p.path.length

end RayPathPresentation

/-- `B` bounds the lengths of all irreducible paths presenting `f`. -/
def RayPathLengthBound {x : C} (f : NonzeroMorphismFrom x) (B : ℕ) : Prop :=
  ∀ p : RayPathPresentation f, p.length ≤ B

/-- The explicit hypothesis that every nonzero ray morphism has at least one
irreducible-path presentation and that all such presentations have bounded
length. -/
class HasFiniteRayPathDepth (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] : Prop where
  presentation_nonempty : ∀ {x : C} (f : NonzeroMorphismFrom x),
    Nonempty (RayPathPresentation f)
  exists_length_bound : ∀ {x : C} (f : NonzeroMorphismFrom x),
    ∃ B : ℕ, RayPathLengthBound f B

/-- Every noninvertible nonzero ray morphism admits a factorization whose
left factor is irreducible.  Termination is supplied by the finite
fixed-source factorization order. -/
theorem exists_irreducible_left_factor [Finite C] [IsFiniteRayCategory C]
    {X : C} (f : NonzeroMorphismFrom X) (hf : ¬IsIso f.hom) :
    ∃ (Z : C) (g : NonzeroHom X Z) (h : NonzeroHom Z f.target),
      IsIrreducibleRayMorphism g.1 ∧ g.1 ≫ h.1 = f.hom := by
  classical
  let wf : WellFounded
      ((· < ·) : NonzeroMorphismFrom X → NonzeroMorphismFrom X → Prop) :=
    Finite.wellFounded_of_trans_of_irrefl _
  revert hf
  apply wf.induction f
  intro a ih ha
  by_cases hirr : IsIrreducibleRayMorphism a.hom
  · let g : NonzeroHom X a.target := ⟨a.hom, a.ne_zero⟩
    let h : NonzeroHom a.target a.target :=
      ⟨𝟙 a.target, IsFiniteRayCategory.id_ne_zero a.target⟩
    exact ⟨a.target, g, h, hirr, Category.comp_id _⟩
  · have hfactor :
        ∃ (Z : C) (g : X ⟶ Z) (h : Z ⟶ a.target),
          g ≫ h = a.hom ∧ ¬IsIso g ∧ ¬IsIso h := by
      by_contra hex
      apply hirr
      refine ⟨a.ne_zero, ha, ?_⟩
      intro Z g h hgh
      by_contra hnoniso
      apply hex
      push Not at hnoniso
      exact ⟨Z, g, h, hgh, hnoniso⟩
    obtain ⟨Z, g, h, hgh, hgIso, hhIso⟩ := hfactor
    have hg0 : g ≠ 0 := by
      intro hg
      apply a.ne_zero
      rw [← hgh, hg, zero_comp]
    have hh0 : h ≠ 0 := by
      intro hh
      apply a.ne_zero
      rw [← hgh, hh, comp_zero]
    let gFrom : NonzeroMorphismFrom X := ⟨Z, g, hg0⟩
    have hga : gFrom < a :=
      NonzeroMorphismFrom.lt_of_postfactor_noniso h hgh hhIso
    obtain ⟨W, r, s, hr, hrs⟩ := ih gFrom hga hgIso
    change r.1 ≫ s.1 = g at hrs
    have hsh0 : s.1 ≫ h ≠ 0 := by
      intro hzero
      apply a.ne_zero
      rw [← hgh, ← hrs, Category.assoc, hzero, comp_zero]
    let sh : NonzeroHom W a.target := ⟨s.1 ≫ h, hsh0⟩
    refine ⟨W, r, sh, hr, ?_⟩
    dsimp [sh]
    rw [← Category.assoc, hrs, hgh]

/-- An invertible nonzero ray morphism has the length-zero presentation. -/
def rayPathPresentationOfIsIso [IsFiniteRayCategory C]
    {X Y : C} (f : NonzeroHom X Y) [IsIso f.1] :
    RayPathPresentation f.toMorphismFrom := by
  let hXY : X = Y := Classical.choose (ray_isIso_eq_eqToHom f.1)
  have hf : f.1 = eqToHom hXY :=
    Classical.choose_spec (ray_isIso_eq_eqToHom f.1)
  cases hXY
  exact
    { path := Quiver.Path.nil
      map_eq := by
        simpa only [rayPathMap, LinearPathCategory.pathMap_nil,
          eqToHom_refl] using hf.symm }

/-- An irreducible ray morphism has its evident one-arrow presentation. -/
def rayPathPresentationOfIrreducible
    {X Y : C} (f : NonzeroHom X Y)
    (hf : IsIrreducibleRayMorphism f.1) :
    RayPathPresentation f.toMorphismFrom := by
  let a : RayVertex.mk Y ⟶ RayVertex.mk X := ⟨f.1, hf⟩
  exact
    { path := Quiver.Hom.toPath a
      map_eq := by
        rw [rayPathMap_toPath]
        rfl }

/-- Every nonzero morphism in a finite ray category is represented by an
irreducible path.  The recursion repeatedly removes an irreducible left
factor and terminates in the finite fixed-target order. -/
theorem rayPathPresentation_nonempty_of_finite
    [Finite C] [IsFiniteRayCategory C]
    {X Y : C} (f : NonzeroHom X Y) :
    Nonempty (RayPathPresentation f.toMorphismFrom) := by
  classical
  let wf : WellFounded
      (fun a b : NonzeroMorphismTo Y ↦ b < a) :=
    Finite.wellFounded_of_trans_of_irrefl _
  let P : NonzeroMorphismTo Y → Prop := fun a ↦
    Nonempty (RayPathPresentation
      (NonzeroHom.toMorphismFrom
        (⟨a.hom, a.ne_zero⟩ : NonzeroHom a.source Y)))
  have hP : P f.toMorphismTo := by
    apply wf.induction f.toMorphismTo
    intro a ih
    let aHom : NonzeroHom a.source Y := ⟨a.hom, a.ne_zero⟩
    change Nonempty (RayPathPresentation aHom.toMorphismFrom)
    by_cases haIso : IsIso a.hom
    · letI : IsIso a.hom := haIso
      exact ⟨rayPathPresentationOfIsIso aHom⟩
    · obtain ⟨Z, g, h, hg, hgh⟩ :=
        exists_irreducible_left_factor aHom.toMorphismFrom haIso
      have halt : a < h.toMorphismTo :=
        NonzeroMorphismTo.lt_of_prefactor_noniso g.1 hgh hg.2.1
      obtain ⟨ph⟩ := ih h.toMorphismTo halt
      let ag : RayVertex.mk Z ⟶ RayVertex.mk a.source := ⟨g.1, hg⟩
      refine ⟨⟨ph.path.comp (Quiver.Hom.toPath ag), ?_⟩⟩
      simp only [rayPathMap, LinearPathCategory.pathMap_comp]
      change rayPathMap (Quiver.Hom.toPath ag) ≫ rayPathMap ph.path = aHom.1
      rw [rayPathMap_toPath]
      rw [ph.map_eq]
      exact hgh
  exact hP

/-- The finite-cardinality rank of a nonzero ray morphism in its fixed-source
factorization order. -/
def rayMorphismLowerCard [Finite C] [IsFiniteRayCategory C]
    {X : C} (f : NonzeroMorphismFrom X) : ℕ :=
  (Set.Iic f).ncard

/-- A principal lower interval contains its endpoint. -/
theorem rayMorphismLowerCard_pos [Finite C] [IsFiniteRayCategory C]
    {X : C} (f : NonzeroMorphismFrom X) :
    0 < rayMorphismLowerCard f := by
  unfold rayMorphismLowerCard
  exact (Set.ncard_pos (Set.toFinite _)).2
    ⟨f, Set.mem_Iic.mpr le_rfl⟩

/-- Strict factorization strictly increases the fixed-source cardinal rank. -/
theorem rayMorphismLowerCard_lt_of_lt [Finite C] [IsFiniteRayCategory C]
    {X : C} {f g : NonzeroMorphismFrom X} (hfg : f < g) :
    rayMorphismLowerCard f < rayMorphismLowerCard g := by
  unfold rayMorphismLowerCard
  exact Set.ncard_lt_ncard (Set.Iic_ssubset_Iic.2 hfg)
    (Set.toFinite _)

/-- A nonzero irreducible path has length strictly below the cardinality of
the corresponding principal lower interval. -/
theorem rayPath_length_add_one_le_lowerCard
    [Finite C] [IsFiniteRayCategory C]
    {i j : RayVertex C} (p : Quiver.Path i j) (hp : rayPathMap p ≠ 0) :
    p.length + 1 ≤ rayMorphismLowerCard (rayPathMorphism p hp) := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ {i j : RayVertex C} (p : Quiver.Path i j), p.length = n →
      ∀ hp : rayPathMap p ≠ 0,
        p.length + 1 ≤ rayMorphismLowerCard (rayPathMorphism p hp)
  have hP : ∀ n : ℕ, P n := by
    intro n
    induction n with
    | zero =>
        intro i j p hlen hp
        have hpos := rayMorphismLowerCard_pos (rayPathMorphism p hp)
        omega
    | succ n ih =>
        intro i j p hlen hp
        obtain ⟨k, a, q, hqLen, hpath⟩ :=
          Quiver.Path.eq_toPath_comp_of_length_eq_succ p hlen
        have hq0 : rayPathMap q ≠ 0 := by
          intro hq
          apply hp
          rw [hpath]
          have hcomp := LinearPathCategory.pathMap_comp
            RayVertex.obj rayArrowMorphism (Quiver.Hom.toPath a) q
          change rayPathMap (Quiver.Hom.toPath a |>.comp q) =
            rayPathMap q ≫ rayPathMap (Quiver.Hom.toPath a) at hcomp
          rw [hcomp, hq, zero_comp]
        have hfactor :
            (rayPathMorphism q hq0).hom ≫ rayArrowMorphism a =
              (rayPathMorphism p hp).hom := by
          change rayPathMap q ≫ rayArrowMorphism a = rayPathMap p
          rw [hpath]
          have hcomp := LinearPathCategory.pathMap_comp
            RayVertex.obj rayArrowMorphism (Quiver.Hom.toPath a) q
          change rayPathMap (Quiver.Hom.toPath a |>.comp q) =
            rayPathMap q ≫ rayPathMap (Quiver.Hom.toPath a) at hcomp
          rw [hcomp]
          rw [rayPathMap_toPath]
        have hlt : rayPathMorphism q hq0 < rayPathMorphism p hp :=
          NonzeroMorphismFrom.lt_of_postfactor_noniso
            (rayArrowMorphism a) hfactor a.property.2.1
        have hcard := rayMorphismLowerCard_lt_of_lt hlt
        have hqBound := ih q hqLen hq0
        omega
  exact hP p.length p rfl hp

/-- Every presentation length is bounded by the finite fixed-source
factorization rank of its morphism. -/
theorem rayPathPresentation_length_le_lowerCard
    [Finite C] [IsFiniteRayCategory C]
    {X : C} {f : NonzeroMorphismFrom X} (p : RayPathPresentation f) :
    p.length ≤ rayMorphismLowerCard f := by
  have hp0 : rayPathMap p.path ≠ 0 := by
    rw [p.map_eq]
    exact f.ne_zero
  have hbound := rayPath_length_add_one_le_lowerCard p.path hp0
  have heq : rayPathMorphism p.path hp0 = f := by
    apply NonzeroMorphismFrom.ext
      (f := rayPathMorphism p.path hp0) (g := f) rfl
    change rayPathMap p.path ≫ 𝟙 f.target = f.hom
    simpa using p.map_eq
  rw [heq] at hbound
  change p.path.length ≤ rayMorphismLowerCard f
  omega

/-- Finite ray-category axioms imply the existence and boundedness required
to define BGRS morphism depth. -/
instance finiteRayCategory_hasFiniteRayPathDepth
    [Finite C] [IsFiniteRayCategory C] : HasFiniteRayPathDepth C where
  presentation_nonempty {x} f := by
    let fHom : NonzeroHom x f.target := ⟨f.hom, f.ne_zero⟩
    exact rayPathPresentation_nonempty_of_finite fHom
  exists_length_bound f :=
    ⟨rayMorphismLowerCard f, fun p ↦
      rayPathPresentation_length_le_lowerCard p⟩

/-- A chosen upper bound on the presentation lengths of `f`. -/
def rayPathLengthBound [HasFiniteRayPathDepth C]
    {x : C} (f : NonzeroMorphismFrom x) : ℕ :=
  Classical.choose (HasFiniteRayPathDepth.exists_length_bound f)

/-- Every presentation length is below the chosen bound. -/
theorem rayPathPresentation_length_le_bound [HasFiniteRayPathDepth C]
    {x : C} (f : NonzeroMorphismFrom x) (p : RayPathPresentation f) :
    p.length ≤ rayPathLengthBound f :=
  Classical.choose_spec (HasFiniteRayPathDepth.exists_length_bound f) p

/-- A natural number occurs as the length of a presentation of `f`. -/
def IsRayPathPresentationLength {x : C} (f : NonzeroMorphismFrom x)
    (n : ℕ) : Prop :=
  ∃ p : RayPathPresentation f, p.length = n

/-- The BGRS depth of a nonzero ray morphism: the greatest length of an
irreducible path presenting it. -/
def rayMorphismDepth [HasFiniteRayPathDepth C]
    {x : C} (f : NonzeroMorphismFrom x) : ℕ :=
  by
    classical
    exact Nat.findGreatest (IsRayPathPresentationLength f)
      (rayPathLengthBound f)

/-- Depth of a nonzero morphism whose two endpoints are fixed. -/
abbrev NonzeroHom.depth [HasFiniteRayPathDepth C]
    {X Y : C} (f : NonzeroHom X Y) : ℕ :=
  rayMorphismDepth f.toMorphismFrom

/-- Every presentation has length at most the depth. -/
theorem RayPathPresentation.length_le_depth [HasFiniteRayPathDepth C]
    {x : C} {f : NonzeroMorphismFrom x} (p : RayPathPresentation f) :
    p.length ≤ rayMorphismDepth f := by
  classical
  unfold rayMorphismDepth
  apply Nat.le_findGreatest (rayPathPresentation_length_le_bound f p)
  exact ⟨p, rfl⟩

/-- The depth is attained by an irreducible-path presentation. -/
theorem exists_rayPathPresentation_length_eq_depth
    [HasFiniteRayPathDepth C] {x : C} (f : NonzeroMorphismFrom x) :
    ∃ p : RayPathPresentation f, p.length = rayMorphismDepth f := by
  classical
  obtain ⟨p⟩ := HasFiniteRayPathDepth.presentation_nonempty f
  unfold rayMorphismDepth
  have hp : IsRayPathPresentationLength f p.length := ⟨p, rfl⟩
  exact Nat.findGreatest_spec (P := IsRayPathPresentationLength f)
    (rayPathPresentation_length_le_bound f p) hp

/-- A nonzero irreducible path is a presentation of its associated ray
morphism. -/
def rayPathPresentation {i j : RayVertex C} (p : Quiver.Path i j)
    (hp : rayPathMap p ≠ 0) :
    RayPathPresentation (rayPathMorphism p hp) where
  path := p
  map_eq := rfl

/-- The length of every nonzero irreducible path is at most the depth of its
associated ray morphism. -/
theorem rayPath_length_le_depth [HasFiniteRayPathDepth C]
    {i j : RayVertex C} (p : Quiver.Path i j) (hp : rayPathMap p ≠ 0) :
    p.length ≤ rayMorphismDepth (rayPathMorphism p hp) :=
  (rayPathPresentation p hp).length_le_depth

/-- Related ray paths have the same morphism depth. -/
theorem rayMorphismDepth_eq_of_related [HasFiniteRayPathDepth C]
    {i j : RayVertex C} (p q : Quiver.Path i j)
    (hpq : (rayPathContourRelation (C := C)).related p q) :
    rayMorphismDepth (rayPathMorphism p hpq.1) =
      rayMorphismDepth (rayPathMorphism q (by
        rw [← hpq.2]
        exact hpq.1)) := by
  exact congrArg rayMorphismDepth
    (rayPathMorphism_eq_of_related p q hpq)

/-- A nonempty irreducible path in a ray category cannot evaluate to an
isomorphism. -/
theorem rayPathMap_not_isIso_of_length_ne_zero [IsFiniteRayCategory C]
    {i j : RayVertex C} (p : Quiver.Path i j) (hp : p.length ≠ 0) :
    ¬IsIso (rayPathMap p) := by
  intro hIso
  cases p with
  | nil => simp at hp
  | @cons l _ p a =>
      haveI : IsIso (rayPathMap (p.cons a)) := hIso
      haveI : IsIso (rayArrowMorphism a ≫ rayPathMap p) := by
        simpa only [rayPathMap, LinearPathCategory.pathMap_cons]
          using hIso
      exact a.property.2.1 (ray_isIso_factors
        (rayArrowMorphism a) (rayPathMap p)).1

/-- Every irreducible morphism has BGRS depth exactly one. -/
theorem rayMorphismDepth_eq_one_of_irreducible
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    {X Y : C} (f : NonzeroHom X Y)
    (hf : IsIrreducibleRayMorphism f.1) :
    f.depth = 1 := by
  have hpresentation_length_le_one :
      ∀ p : RayPathPresentation f.toMorphismFrom, p.length ≤ 1 := by
    intro p
    by_contra hle
    have htwo : 2 ≤ p.length := by omega
    change 2 ≤ p.path.length at htwo
    have hlen : p.path.length = (p.path.length - 1) + 1 := by
      exact (Nat.sub_add_cancel (Nat.le_trans (by omega) htwo)).symm
    obtain ⟨j, a, q, hqLen, hpath⟩ :=
      Quiver.Path.eq_toPath_comp_of_length_eq_succ p.path hlen
    have hq : q.length ≠ 0 := by
      change 2 ≤ p.path.length at htwo
      omega
    have hfactor : rayPathMap q ≫ rayArrowMorphism a = f.1 := by
      calc
        rayPathMap q ≫ rayArrowMorphism a =
            rayPathMap (Quiver.Hom.toPath a |>.comp q) := by
          simp only [rayPathMap, LinearPathCategory.pathMap_comp,
            rayPathMap_toPath]
        _ = rayPathMap p.path := by rw [← hpath]
        _ = f.1 := p.map_eq
    rcases hf.2.2 j.obj (rayPathMap q) (rayArrowMorphism a)
        hfactor with hqIso | haIso
    · exact rayPathMap_not_isIso_of_length_ne_zero q hq hqIso
    · exact a.property.2.1 haIso
  have hdepth_le : f.depth ≤ 1 := by
    obtain ⟨p, hp⟩ :=
      exists_rayPathPresentation_length_eq_depth f.toMorphismFrom
    change rayMorphismDepth f.toMorphismFrom ≤ 1
    rw [← hp]
    exact hpresentation_length_le_one p
  let a :
      (RayVertex.mk Y ⟶ RayVertex.mk X) := ⟨f.1, hf⟩
  let p : RayPathPresentation f.toMorphismFrom :=
    { path := Quiver.Hom.toPath a
      map_eq := by
        rw [rayPathMap_toPath]
        rfl }
  have hone_le : 1 ≤ f.depth := by
    simpa [p, RayPathPresentation.length, a] using p.length_le_depth
  exact Nat.le_antisymm hdepth_le hone_le

end LargeIndecomposable
