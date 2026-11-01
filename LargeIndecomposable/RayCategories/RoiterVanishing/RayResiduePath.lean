module

public import LargeIndecomposable.RayCategories.Contours.ProperPathInterlacement
public import LargeIndecomposable.RayCategories.Contours.EssentialPathContour
public import LargeIndecomposable.RayCategories.RoiterVanishing.RayResidueTackle
public import LargeIndecomposable.RayCategories.RoiterVanishing.RoiterLocalCorrectionCases
public import LargeIndecomposable.RayCategories.Basic.RayMaximalPath
public import LargeIndecomposable.RayCategories.Contours.RayRankedPathInterlacement

@[expose] public section

/-!
# Paths in ray residue categories

Lift the reversed irreducible quiver of a proper zero-ideal quotient back to
the original ray category.  This is the path-level transport needed in the
residue induction of BGRS 8.6.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {k : Type*} [Field k]

namespace ZeroHomIdeal

/-- If a composite lies outside a zero Hom ideal, then its first factor lies
outside the ideal. -/
theorem not_mem_left_of_comp_not_mem (I : ZeroHomIdeal C)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : ¬I.mem (f ≫ g)) : ¬I.mem f := by
  intro hf
  exact hfg (I.postcomp g hf)

/-- If a composite lies outside a zero Hom ideal, then its second factor lies
outside the ideal. -/
theorem not_mem_right_of_comp_not_mem (I : ZeroHomIdeal C)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : ¬I.mem (f ≫ g)) : ¬I.mem g := by
  intro hg
  exact hfg (I.precomp f hg)

/-- A proper zero Hom ideal contains no isomorphism. -/
theorem not_mem_of_isIso (I : ZeroHomIdeal C) (hI : I.IsProper)
    {X Y : C} (f : X ⟶ Y) [IsIso f] : ¬I.mem f := by
  intro hf
  apply hI Y
  have hmem := I.precomp (inv f) hf
  simpa using hmem

/-- The vertex of the quotient ray quiver induced by an original ray
vertex. -/
def rayQuiverQuotientObj (I : ZeroHomIdeal C) (i : RayVertex C) :
    RayVertex (CategoryTheory.Quotient I.rel) :=
  ⟨(CategoryTheory.Quotient.functor I.rel).obj i.obj⟩

/-- Map an original irreducible ray arrow which survives a proper zero-ideal
quotient. -/
def mapSurvivingRayArrow (I : ZeroHomIdeal C) (hI : I.IsProper)
    {i j : RayVertex C} (a : i ⟶ j) (ha : ¬I.mem (rayArrowMorphism a)) :
    I.rayQuiverQuotientObj i ⟶ I.rayQuiverQuotientObj j :=
  ⟨(CategoryTheory.Quotient.functor I.rel).map (rayArrowMorphism a),
    (I.functor_map_isIrreducible_iff hI (rayArrowMorphism a)).2
      ⟨a.2, ha⟩⟩

@[simp]
theorem rayArrowMorphism_mapSurvivingRayArrow
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    {i j : RayVertex C} (a : i ⟶ j) (ha : ¬I.mem (rayArrowMorphism a)) :
    rayArrowMorphism (I.mapSurvivingRayArrow hI a ha) =
      (CategoryTheory.Quotient.functor I.rel).map
        (rayArrowMorphism a) :=
  rfl

/-- Every arrow in a ray path survives a zero-ideal quotient. -/
def RayPathSurvives (I : ZeroHomIdeal C) :
    {i j : RayVertex C} → Quiver.Path i j → Prop
  | _, _, .nil => True
  | _, _, .cons p a => I.RayPathSurvives p ∧ ¬I.mem (rayArrowMorphism a)

/-- If the evaluation of a ray path is outside a zero Hom ideal, then each of
its irreducible arrows is outside the ideal. -/
theorem rayPathSurvives_of_rayPathMap_not_mem
    (I : ZeroHomIdeal C) {i j : RayVertex C} (p : Quiver.Path i j)
    (hp : ¬I.mem (rayPathMap p)) :
    I.RayPathSurvives p := by
  induction p with
  | nil =>
      simp [RayPathSurvives]
  | cons p a ih =>
      simp only [RayPathSurvives]
      refine ⟨ih ?_, ?_⟩
      · intro hmem
        apply hp
        simpa [rayPathMap, LinearPathCategory.pathMap_cons] using
          I.precomp (rayArrowMorphism a) hmem
      · intro hmem
        apply hp
        simpa [rayPathMap, LinearPathCategory.pathMap_cons] using
          I.postcomp (rayPathMap p) hmem

/-- If a composite ray path survives, both component paths survive at the
level of their evaluated morphisms. -/
theorem rayPathMap_components_not_mem_of_comp_not_mem
    (I : ZeroHomIdeal C) {i j l : RayVertex C}
    (p : Quiver.Path i j) (q : Quiver.Path j l)
    (hpq : ¬I.mem (rayPathMap (p.comp q))) :
    ¬I.mem (rayPathMap p) ∧ ¬I.mem (rayPathMap q) := by
  have hpq' : ¬I.mem (rayPathMap q ≫ rayPathMap p) := by
    simpa only [rayPathMap, LinearPathCategory.pathMap_comp] using hpq
  exact ⟨I.not_mem_right_of_comp_not_mem _ _ hpq',
    I.not_mem_left_of_comp_not_mem _ _ hpq'⟩

/-- Map a path all of whose arrows survive to the quotient ray quiver. -/
def mapSurvivingRayPath (I : ZeroHomIdeal C) (hI : I.IsProper) :
    {i j : RayVertex C} → (p : Quiver.Path i j) →
      I.RayPathSurvives p →
      Quiver.Path (I.rayQuiverQuotientObj i)
        (I.rayQuiverQuotientObj j)
  | _, _, .nil, _ => .nil
  | _, _, .cons p a, hp => by
      simp only [RayPathSurvives] at hp
      exact (I.mapSurvivingRayPath hI p hp.1).cons
        (I.mapSurvivingRayArrow hI a hp.2)

/-- Concatenating two surviving ray paths gives a surviving path. -/
theorem rayPathSurvives_comp
    (I : ZeroHomIdeal C) {i j l : RayVertex C}
    (p : Quiver.Path i j) (q : Quiver.Path j l)
    (hp : I.RayPathSurvives p) (hq : I.RayPathSurvives q) :
    I.RayPathSurvives (p.comp q) := by
  induction q with
  | nil => simpa using hp
  | cons q a ih =>
      simp only [RayPathSurvives] at hq
      simp only [Quiver.Path.comp_cons, RayPathSurvives]
      exact ⟨ih hq.1, hq.2⟩

/-- Mapping surviving paths to a quotient preserves path concatenation. -/
theorem mapSurvivingRayPath_comp
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    {i j l : RayVertex C} (p : Quiver.Path i j)
    (q : Quiver.Path j l)
    (hp : I.RayPathSurvives p) (hq : I.RayPathSurvives q) :
    I.mapSurvivingRayPath hI (p.comp q)
        (I.rayPathSurvives_comp p q hp hq) =
      (I.mapSurvivingRayPath hI p hp).comp
        (I.mapSurvivingRayPath hI q hq) := by
  induction q with
  | nil => simp [mapSurvivingRayPath]
  | cons q a ih =>
      simp only [RayPathSurvives] at hq
      rcases hq with ⟨hq, ha⟩
      simp [mapSurvivingRayPath, ih hq]

@[simp]
theorem mapSurvivingRayPath_length
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    {i j : RayVertex C} (p : Quiver.Path i j)
    (hp : I.RayPathSurvives p) :
    (I.mapSurvivingRayPath hI p hp).length = p.length := by
  induction p with
  | nil => simp [mapSurvivingRayPath]
  | cons p a ih =>
      simp only [RayPathSurvives] at hp
      rcases hp with ⟨hp, ha⟩
      simp [mapSurvivingRayPath, ih hp]

/-- Evaluation commutes with mapping a surviving original ray path to the
quotient. -/
theorem rayPathMap_mapSurvivingRayPath
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    {i j : RayVertex C} (p : Quiver.Path i j)
    (hp : I.RayPathSurvives p) :
    rayPathMap (I.mapSurvivingRayPath hI p hp) =
      (CategoryTheory.Quotient.functor I.rel).map (rayPathMap p) := by
  induction p with
  | nil => simp [mapSurvivingRayPath, rayPathMap, rayQuiverQuotientObj]
  | cons p a ih =>
      simp only [RayPathSurvives] at hp
      rcases hp with ⟨hp, ha⟩
      simp [mapSurvivingRayPath, rayPathMap,
        LinearPathCategory.pathMap_cons, ih hp]

/-- Lift quotient arrow weights to original ray arrows, using weight one on
arrows annihilated by the quotient. -/
def liftQuotientArrowUnitWeight
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    (e : ArrowUnitWeight k
      (RayVertex (CategoryTheory.Quotient I.rel))) :
    ArrowUnitWeight k (RayVertex C) := by
  classical
  exact fun {_ _} a =>
    if ha : ¬I.mem (rayArrowMorphism a) then
      e (I.mapSurvivingRayArrow hI a ha)
    else 1

@[simp]
theorem liftQuotientArrowUnitWeight_apply_of_not_mem
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    (e : ArrowUnitWeight k
      (RayVertex (CategoryTheory.Quotient I.rel)))
    {i j : RayVertex C} (a : i ⟶ j)
    (ha : ¬I.mem (rayArrowMorphism a)) :
    I.liftQuotientArrowUnitWeight hI e a =
      e (I.mapSurvivingRayArrow hI a ha) := by
  simp [liftQuotientArrowUnitWeight, ha]

/-- Lifted quotient weights give every surviving original path exactly the
weight of its mapped quotient path. -/
theorem path_weight_liftQuotientArrowUnitWeight
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    (e : ArrowUnitWeight k
      (RayVertex (CategoryTheory.Quotient I.rel)))
    {i j : RayVertex C} (p : Quiver.Path i j)
    (hp : I.RayPathSurvives p) :
    p.weight (I.liftQuotientArrowUnitWeight hI e) =
      (I.mapSurvivingRayPath hI p hp).weight e := by
  induction p with
  | nil => simp [mapSurvivingRayPath]
  | cons p a ih =>
      simp only [RayPathSurvives] at hp
      rcases hp with ⟨hp, ha⟩
      simp [mapSurvivingRayPath, Quiver.Path.weight_cons,
        I.liftQuotientArrowUnitWeight_apply_of_not_mem hI e a ha,
        ih hp]

/-- Path-weight ratios are transported exactly from a quotient correction to
any pair of surviving original paths. -/
theorem pathWeightRatio_liftQuotientArrowUnitWeight
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    (e : ArrowUnitWeight k
      (RayVertex (CategoryTheory.Quotient I.rel)))
    {i j : RayVertex C} (p q : Quiver.Path i j)
    (hp : I.RayPathSurvives p) (hq : I.RayPathSurvives q) :
    pathWeightRatio (I.liftQuotientArrowUnitWeight hI e) p q =
      pathWeightRatio e (I.mapSurvivingRayPath hI p hp)
        (I.mapSurvivingRayPath hI q hq) := by
  simp [pathWeightRatio,
    I.path_weight_liftQuotientArrowUnitWeight hI e p hp,
    I.path_weight_liftQuotientArrowUnitWeight hI e q hq]

/-- A related pair whose common nonzero ray survives remains related after
mapping both paths to the quotient ray quiver. -/
theorem rayPathContourRelation_related_mapSurvivingRayPath
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    {i j : RayVertex C} (p q : Quiver.Path i j)
    (hp : I.RayPathSurvives p) (hq : I.RayPathSurvives q)
    (hpNotMem : ¬I.mem (rayPathMap p))
    (hpq : (rayPathContourRelation (C := C)).related p q) :
    (rayPathContourRelation
      (C := CategoryTheory.Quotient I.rel)).related
        (I.mapSurvivingRayPath hI p hp)
        (I.mapSurvivingRayPath hI q hq) := by
  refine ⟨?_, ?_⟩
  · rw [I.rayPathMap_mapSurvivingRayPath hI p hp]
    exact (I.functor_map_ne_zero_iff (rayPathMap p)).2 hpNotMem
  · rw [I.rayPathMap_mapSurvivingRayPath hI p hp,
      I.rayPathMap_mapSurvivingRayPath hI q hq, hpq.2]

/-- A path evaluation outside a zero Hom ideal is nonzero. -/
theorem rayPathMap_ne_zero_of_not_mem
    (I : ZeroHomIdeal C) {i j : RayVertex C}
    (p : Quiver.Path i j) (hp : ¬I.mem (rayPathMap p)) :
    rayPathMap p ≠ 0 := by
  intro hzero
  apply hp
  rw [hzero]
  exact I.zero_mem _ _

/-- Related ray paths lie simultaneously inside or outside a zero Hom
ideal. -/
theorem rayPathMap_right_not_mem_of_related
    (I : ZeroHomIdeal C) {i j : RayVertex C}
    {p q : Quiver.Path i j}
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (hp : ¬I.mem (rayPathMap p)) :
    ¬I.mem (rayPathMap q) := by
  simpa only [← hpq.2] using hp

/-- An elementary proper-whisker replacement along a ray which survives the
quotient maps to an elementary replacement in the quotient. -/
theorem exists_properWhiskerInterlacementStep_mapSurvivingRayPath
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    {a b : RayVertex C} {p q : Quiver.Path a b}
    (hpq : ProperWhiskerInterlacementStep
      (rayPathContourRelation (C := C)) p q)
    (hpNotMem : ¬I.mem (rayPathMap p)) :
    ∃ (hp : I.RayPathSurvives p) (hq : I.RayPathSurvives q),
      ProperWhiskerInterlacementStep
        (rayPathContourRelation (C := CategoryTheory.Quotient I.rel))
        (I.mapSurvivingRayPath hI p hp)
        (I.mapSurvivingRayPath hI q hq) := by
  obtain ⟨i, j, s, x, y, t, hxy, houter, hproper,
    hpEq, hqEq⟩ := hpq
  subst p
  subst q
  have houterRight :
      ¬I.mem (rayPathMap ((s.comp y).comp t)) := by
    intro hmem
    apply hpNotMem
    rw [houter.2]
    exact hmem
  obtain ⟨hsxNotMem, htNotMem⟩ :=
    I.rayPathMap_components_not_mem_of_comp_not_mem
      (s.comp x) t hpNotMem
  obtain ⟨hsNotMem, hxNotMem⟩ :=
    I.rayPathMap_components_not_mem_of_comp_not_mem s x hsxNotMem
  obtain ⟨hsyNotMem, _⟩ :=
    I.rayPathMap_components_not_mem_of_comp_not_mem
      (s.comp y) t houterRight
  obtain ⟨_, hyNotMem⟩ :=
    I.rayPathMap_components_not_mem_of_comp_not_mem s y hsyNotMem
  let hs : I.RayPathSurvives s :=
    I.rayPathSurvives_of_rayPathMap_not_mem s hsNotMem
  let hx : I.RayPathSurvives x :=
    I.rayPathSurvives_of_rayPathMap_not_mem x hxNotMem
  let hy : I.RayPathSurvives y :=
    I.rayPathSurvives_of_rayPathMap_not_mem y hyNotMem
  let ht : I.RayPathSurvives t :=
    I.rayPathSurvives_of_rayPathMap_not_mem t htNotMem
  let hsx : I.RayPathSurvives (s.comp x) :=
    I.rayPathSurvives_comp s x hs hx
  let hsy : I.RayPathSurvives (s.comp y) :=
    I.rayPathSurvives_comp s y hs hy
  let hp : I.RayPathSurvives ((s.comp x).comp t) :=
    I.rayPathSurvives_comp (s.comp x) t hsx ht
  let hq : I.RayPathSurvives ((s.comp y).comp t) :=
    I.rayPathSurvives_comp (s.comp y) t hsy ht
  have hpMapEq :
      I.mapSurvivingRayPath hI ((s.comp x).comp t) hp =
        ((I.mapSurvivingRayPath hI s hs).comp
          (I.mapSurvivingRayPath hI x hx)).comp
          (I.mapSurvivingRayPath hI t ht) := by
    calc
      I.mapSurvivingRayPath hI ((s.comp x).comp t) hp =
          (I.mapSurvivingRayPath hI (s.comp x) hsx).comp
            (I.mapSurvivingRayPath hI t ht) :=
        I.mapSurvivingRayPath_comp hI (s.comp x) t hsx ht
      _ = ((I.mapSurvivingRayPath hI s hs).comp
            (I.mapSurvivingRayPath hI x hx)).comp
            (I.mapSurvivingRayPath hI t ht) := by
        rw [I.mapSurvivingRayPath_comp hI s x hs hx]
  have hqMapEq :
      I.mapSurvivingRayPath hI ((s.comp y).comp t) hq =
        ((I.mapSurvivingRayPath hI s hs).comp
          (I.mapSurvivingRayPath hI y hy)).comp
          (I.mapSurvivingRayPath hI t ht) := by
    calc
      I.mapSurvivingRayPath hI ((s.comp y).comp t) hq =
          (I.mapSurvivingRayPath hI (s.comp y) hsy).comp
            (I.mapSurvivingRayPath hI t ht) :=
        I.mapSurvivingRayPath_comp hI (s.comp y) t hsy ht
      _ = ((I.mapSurvivingRayPath hI s hs).comp
            (I.mapSurvivingRayPath hI y hy)).comp
            (I.mapSurvivingRayPath hI t ht) := by
        rw [I.mapSurvivingRayPath_comp hI s y hs hy]
  refine ⟨hp, hq, ?_⟩
  refine ⟨I.rayQuiverQuotientObj i, I.rayQuiverQuotientObj j,
    I.mapSurvivingRayPath hI s hs,
    I.mapSurvivingRayPath hI x hx,
    I.mapSurvivingRayPath hI y hy,
    I.mapSurvivingRayPath hI t ht,
    I.rayPathContourRelation_related_mapSurvivingRayPath hI
      x y hx hy hxNotMem hxy, ?_, ?_, ?_, ?_⟩
  · have houterQ :=
      I.rayPathContourRelation_related_mapSurvivingRayPath hI
        ((s.comp x).comp t) ((s.comp y).comp t)
        hp hq hpNotMem houter
    rw [hpMapEq, hqMapEq] at houterQ
    exact houterQ
  · simpa only [I.mapSurvivingRayPath_length hI] using hproper
  · exact hpMapEq
  · exact hqMapEq

/-- Proper-whisker interlacement along one surviving ray maps to
proper-whisker interlacement in the quotient. -/
theorem exists_properWhiskerInterlaced_mapSurvivingRayPath
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    {a b : RayVertex C} {p q : Quiver.Path a b}
    (hpq : (properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p q)
    (hpNotMem : ¬I.mem (rayPathMap p)) :
    ∃ (hp : I.RayPathSurvives p) (hq : I.RayPathSurvives q),
      (properWhiskerInterlacementRelation
        (rayPathContourRelation
          (C := CategoryTheory.Quotient I.rel))).interlaced
        (I.mapSurvivingRayPath hI p hp)
        (I.mapSurvivingRayPath hI q hq) := by
  change Relation.EqvGen _ p q at hpq
  rw [← Relation.EqvGen.reflTransGen_symmGen] at hpq
  induction hpq with
  | refl =>
      let hp : I.RayPathSurvives p :=
        I.rayPathSurvives_of_rayPathMap_not_mem p hpNotMem
      exact ⟨hp, hp, Relation.EqvGen.refl _⟩
  | @tail r s hpr hrs ih =>
      obtain ⟨hp, hr, hprQ⟩ := ih
      have hprInterlaced : (properWhiskerInterlacementRelation
          (rayPathContourRelation (C := C))).interlaced p r := by
        change Relation.EqvGen _ p r
        rw [← Relation.EqvGen.reflTransGen_symmGen]
        exact hpr
      have hpp : (rayPathContourRelation (C := C)).related p p :=
        ⟨I.rayPathMap_ne_zero_of_not_mem p hpNotMem, rfl⟩
      have hprRelated := related_of_properWhiskerInterlaced
        (rayPathContourRelation (C := C)) hprInterlaced hpp
      have hrNotMem : ¬I.mem (rayPathMap r) :=
        I.rayPathMap_right_not_mem_of_related hprRelated hpNotMem
      rcases hrs with hrs | hsr
      · obtain ⟨hr', hs, hrsQ⟩ :=
          I.exists_properWhiskerInterlacementStep_mapSurvivingRayPath
            hI hrs hrNotMem
        refine ⟨hp, hs, Relation.EqvGen.trans _ _ _ hprQ ?_⟩
        have hrsQI := properWhiskerInterlaced_of_step
          (rayPathContourRelation
            (C := CategoryTheory.Quotient I.rel)) hrsQ
        cases Subsingleton.elim hr' hr
        exact hrsQI
      · have hsrRelated :=
          related_of_properWhiskerInterlacementStep
            (rayPathContourRelation (C := C)) hsr
        have hsNotMem : ¬I.mem (rayPathMap s) := by
          simpa only [hsrRelated.2] using hrNotMem
        obtain ⟨hs, hr', hsrQ⟩ :=
          I.exists_properWhiskerInterlacementStep_mapSurvivingRayPath
            hI hsr hsNotMem
        refine ⟨hp, hs, Relation.EqvGen.trans _ _ _ hprQ ?_⟩
        have hsrQI := properWhiskerInterlaced_of_step
          (rayPathContourRelation
            (C := CategoryTheory.Quotient I.rel)) hsrQ
        cases Subsingleton.elim hr' hr
        exact Relation.EqvGen.symm _ _ hsrQI

/-- Map an original selected ray contour whose common ray survives to the
corresponding selected quotient contour. -/
def mapSurvivingRelatedRayContour
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    (K : RelatedContour (rayPathContourRelation (C := C)))
    (hK : ¬I.mem (rayPathMap K.1.left)) :
    RelatedContour
      (rayPathContourRelation (C := CategoryTheory.Quotient I.rel)) := by
  let hp : I.RayPathSurvives K.1.left :=
    I.rayPathSurvives_of_rayPathMap_not_mem K.1.left hK
  have hrightNotMem : ¬I.mem (rayPathMap K.1.right) := by
    simpa only [K.property.2] using hK
  let hq : I.RayPathSurvives K.1.right :=
    I.rayPathSurvives_of_rayPathMap_not_mem K.1.right hrightNotMem
  exact ⟨⟨I.rayQuiverQuotientObj K.1.source,
      I.rayQuiverQuotientObj K.1.target,
      I.mapSurvivingRayPath hI K.1.left hp,
      I.mapSurvivingRayPath hI K.1.right hq⟩,
    I.rayPathContourRelation_related_mapSurvivingRayPath hI
      K.1.left K.1.right hp hq hK K.property⟩

/-- The coboundary of a lifted quotient correction agrees with the quotient
coboundary on every original contour whose nonzero ray survives. -/
theorem contourCoboundary_liftQuotientArrowUnitWeight
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    (e : ArrowUnitWeight k
      (RayVertex (CategoryTheory.Quotient I.rel)))
    (K : RelatedContour (rayPathContourRelation (C := C)))
    (hK : ¬I.mem (rayPathMap K.1.left)) :
    contourCoboundary (k := k) (I.liftQuotientArrowUnitWeight hI e) K.1 =
      contourCoboundary (k := k) e
        (I.mapSurvivingRelatedRayContour hI K hK).1 := by
  let hp : I.RayPathSurvives K.1.left :=
    I.rayPathSurvives_of_rayPathMap_not_mem K.1.left hK
  have hrightNotMem : ¬I.mem (rayPathMap K.1.right) := by
    simpa only [K.property.2] using hK
  let hq : I.RayPathSurvives K.1.right :=
    I.rayPathSurvives_of_rayPathMap_not_mem K.1.right hrightNotMem
  exact I.pathWeightRatio_liftQuotientArrowUnitWeight hI e
    K.1.left K.1.right hp hq

/-- Choose original irreducible representatives of all arrows in the reversed
ray quiver of a proper zero-ideal quotient. -/
def rayQuiverQuotOutPrefunctor (I : ZeroHomIdeal C) (hI : I.IsProper) :
    RayVertex (CategoryTheory.Quotient I.rel) ⥤q RayVertex C where
  obj i := ⟨i.obj.as⟩
  map a := ⟨Quot.out a.1, I.quotOut_isIrreducible hI a.1 a.2⟩

@[simp]
theorem rayQuiverQuotOutPrefunctor_obj_obj
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    (i : RayVertex (CategoryTheory.Quotient I.rel)) :
    (CategoryTheory.Quotient.functor I.rel).obj
        ((I.rayQuiverQuotOutPrefunctor hI).obj i).obj = i.obj := by
  rcases i with ⟨⟨i⟩⟩
  rfl

@[simp]
theorem rayQuiverQuotOutPrefunctor_obj_rayQuiverQuotientObj
    (I : ZeroHomIdeal C) (hI : I.IsProper) (i : RayVertex C) :
    (I.rayQuiverQuotOutPrefunctor hI).obj
        (I.rayQuiverQuotientObj i) = i := by
  rcases i with ⟨i⟩
  rfl

/-- Lift an outgoing quotient ray arrow to its chosen irreducible
representative in the original ray quiver. -/
def outgoingQuiverArrowQuotOut (I : ZeroHomIdeal C) (hI : I.IsProper)
    (x : RayVertex (CategoryTheory.Quotient I.rel)) :
    OutgoingQuiverArrow x →
      OutgoingQuiverArrow ((I.rayQuiverQuotOutPrefunctor hI).obj x) :=
  fun a => ⟨(I.rayQuiverQuotOutPrefunctor hI).obj a.1,
    (I.rayQuiverQuotOutPrefunctor hI).map a.2⟩

/-- Choosing irreducible representatives is injective on the arrows leaving
a fixed quotient ray vertex. -/
theorem outgoingQuiverArrowQuotOut_injective
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    (x : RayVertex (CategoryTheory.Quotient I.rel)) :
    Function.Injective (I.outgoingQuiverArrowQuotOut hI x) := by
  rintro ⟨y, a⟩ ⟨z, b⟩ h
  simp only [outgoingQuiverArrowQuotOut, rayQuiverQuotOutPrefunctor,
    Sigma.mk.injEq] at h
  obtain ⟨hyz, hab⟩ := h
  apply Sigma.ext
  · rcases x with ⟨⟨x⟩⟩
    rcases y with ⟨⟨y⟩⟩
    rcases z with ⟨⟨z⟩⟩
    simp_all
  · rcases x with ⟨⟨x⟩⟩
    rcases y with ⟨⟨y⟩⟩
    rcases z with ⟨⟨z⟩⟩
    have hyz' : y = z := by simpa using hyz
    subst z
    have hab' : Quot.out a.1 = Quot.out b.1 := by
      exact congrArg Subtype.val (eq_of_heq hab)
    apply heq_of_eq
    apply Subtype.ext
    change a.1 = b.1
    rw [← Quot.out_eq a.1, ← Quot.out_eq b.1, hab']

/-- Lift an incoming quotient ray arrow to its chosen irreducible
representative in the original ray quiver. -/
def incomingQuiverArrowQuotOut (I : ZeroHomIdeal C) (hI : I.IsProper)
    (z : RayVertex (CategoryTheory.Quotient I.rel)) :
    IncomingQuiverArrow z →
      IncomingQuiverArrow ((I.rayQuiverQuotOutPrefunctor hI).obj z) :=
  fun a => ⟨(I.rayQuiverQuotOutPrefunctor hI).obj a.1,
    (I.rayQuiverQuotOutPrefunctor hI).map a.2⟩

/-- Choosing irreducible representatives is injective on the arrows entering
a fixed quotient ray vertex. -/
theorem incomingQuiverArrowQuotOut_injective
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    (z : RayVertex (CategoryTheory.Quotient I.rel)) :
    Function.Injective (I.incomingQuiverArrowQuotOut hI z) := by
  rintro ⟨x, a⟩ ⟨y, b⟩ h
  simp only [incomingQuiverArrowQuotOut, rayQuiverQuotOutPrefunctor,
    Sigma.mk.injEq] at h
  obtain ⟨hxy, hab⟩ := h
  apply Sigma.ext
  · rcases z with ⟨⟨z⟩⟩
    rcases x with ⟨⟨x⟩⟩
    rcases y with ⟨⟨y⟩⟩
    simp_all
  · rcases z with ⟨⟨z⟩⟩
    rcases x with ⟨⟨x⟩⟩
    rcases y with ⟨⟨y⟩⟩
    have hxy' : x = y := by simpa using hxy
    subst y
    have hab' : Quot.out a.1 = Quot.out b.1 := by
      exact congrArg Subtype.val (eq_of_heq hab)
    apply heq_of_eq
    apply Subtype.ext
    change a.1 = b.1
    rw [← Quot.out_eq a.1, ← Quot.out_eq b.1, hab']

/-- The BGRS start/stop valency bound descends through every proper zero-Hom
ideal quotient. -/
theorem quotientHasRayValencyAtMostThree
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    [Finite C] [IsFiniteRayCategory C] [HasRayValencyAtMostThree C] :
    HasRayValencyAtMostThree (CategoryTheory.Quotient I.rel) := by
  letI : IsFiniteRayCategory (CategoryTheory.Quotient I.rel) :=
    I.quotientIsFiniteRayCategory hI
  constructor
  · intro x
    letI : Finite (OutgoingQuiverArrow
        ((I.rayQuiverQuotOutPrefunctor hI).obj x)) :=
      outgoingQuiverArrow_finite _
    exact (Nat.card_le_card_of_injective
      (I.outgoingQuiverArrowQuotOut hI x)
      (I.outgoingQuiverArrowQuotOut_injective hI x)).trans
        (HasRayValencyAtMostThree.outgoing_card_le _)
  · intro z
    letI : Finite (IncomingQuiverArrow
        ((I.rayQuiverQuotOutPrefunctor hI).obj z)) :=
      incomingQuiverArrow_finite _
    exact (Nat.card_le_card_of_injective
      (I.incomingQuiverArrowQuotOut hI z)
      (I.incomingQuiverArrowQuotOut_injective hI z)).trans
        (HasRayValencyAtMostThree.incoming_card_le _)

/-- Mapping the chosen original representative of a quotient ray arrow back
to the quotient recovers that arrow's morphism. -/
theorem functor_map_rayArrowMorphism_rayQuiverQuotOut
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    {i j : RayVertex (CategoryTheory.Quotient I.rel)} (a : i ⟶ j) :
    (CategoryTheory.Quotient.functor I.rel).map
        (rayArrowMorphism ((I.rayQuiverQuotOutPrefunctor hI).map a)) =
      rayArrowMorphism a := by
  rcases i with ⟨⟨i⟩⟩
  rcases j with ⟨⟨j⟩⟩
  change Quot.mk _ (Quot.out a.1) = a.1
  exact Quot.out_eq a.1

/-- Mapping a chosen original representative of a quotient ray arrow back to
the quotient recovers the quotient arrow. -/
theorem mapSurvivingRayArrow_rayQuiverQuotOut
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    {i j : RayVertex (CategoryTheory.Quotient I.rel)} (a : i ⟶ j)
    (ha : ¬I.mem (rayArrowMorphism
      ((I.rayQuiverQuotOutPrefunctor hI).map a))) :
    I.mapSurvivingRayArrow hI
        ((I.rayQuiverQuotOutPrefunctor hI).map a) ha = a := by
  rcases i with ⟨⟨i⟩⟩
  rcases j with ⟨⟨j⟩⟩
  apply Subtype.ext
  exact I.functor_map_rayArrowMorphism_rayQuiverQuotOut hI a

/-- Choosing an original representative after mapping a surviving original
ray arrow to the quotient recovers that arrow. -/
theorem rayQuiverQuotOut_map_mapSurvivingRayArrow
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    {i j : RayVertex C} (a : i ⟶ j)
    (ha : ¬I.mem (rayArrowMorphism a)) :
    (I.rayQuiverQuotOutPrefunctor hI).map
        (I.mapSurvivingRayArrow hI a ha) = a := by
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  apply Subtype.ext
  change Quot.out
      ((CategoryTheory.Quotient.functor I.rel).map a.1) = a.1
  have hmap : (CategoryTheory.Quotient.functor I.rel).map
      (Quot.out ((CategoryTheory.Quotient.functor I.rel).map a.1)) =
        (CategoryTheory.Quotient.functor I.rel).map a.1 := by
    exact Quot.out_eq _
  have hrel : I.rel
      (Quot.out ((CategoryTheory.Quotient.functor I.rel).map a.1)) a.1 :=
    (CategoryTheory.Quotient.functor_map_eq_iff _ _ _).1 hmap
  rcases hrel with hrel | hrel
  · exact hrel
  · exact False.elim (ha hrel.2)

/-- Every nonzero proper zero-Hom residue has global ray valency at most three. -/
class HasThreeValentNonzeroProperRayResidues
    (C : Type u) [Category.{v} C] [HasZeroMorphisms C] : Prop where
  valency : ∀ (I : ZeroHomIdeal C),
    I.IsProper → I.IsNonzero →
      HasRayValencyAtMostThree (CategoryTheory.Quotient I.rel)

/-- Global three-valency is stronger than three-valency of every nonzero
proper zero-Hom residue. -/
instance hasThreeValentNonzeroProperRayResidues_of_global
    [Finite C] [IsFiniteRayCategory C] [HasRayValencyAtMostThree C] :
    HasThreeValentNonzeroProperRayResidues C where
  valency I hI _ := I.quotientHasRayValencyAtMostThree hI

private theorem irreducible_not_mem_principal_comp
    [IsFiniteRayCategory C]
    {X Y Z W V : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsIrreducibleRayMorphism f) (hg : IsIrreducibleRayMorphism g)
    (a : W ⟶ V) (ha : IsIrreducibleRayMorphism a) :
    ¬(principalZeroHomIdeal (f ≫ g)).mem a := by
  intro hmem
  rcases hmem with ⟨l, r, h⟩
  have hfac : (l ≫ f) ≫ (g ≫ r) = a := by
    simpa only [Category.assoc] using h.symm
  rcases ha.2.2 Y (l ≫ f) (g ≫ r) hfac with hleft | hright
  · letI : IsIso (l ≫ f) := hleft
    exact hf.2.1 (ray_isIso_factors l f).2
  · letI : IsIso (g ≫ r) := hright
    exact hg.2.1 (ray_isIso_factors g r).1

private theorem principal_comp_isProper
    [IsFiniteRayCategory C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsIrreducibleRayMorphism f) :
    (principalZeroHomIdeal (f ≫ g)).IsProper := by
  apply principalZeroHomIdeal_isProper_of_not_isIso
  intro hfg
  letI : IsIso (f ≫ g) := hfg
  exact hf.2.1 (ray_isIso_factors f g).1

private theorem fourArrow_outgoing_aux
    [Finite C] [IsFiniteRayCategory C]
    [HasThreeValentNonzeroProperRayResidues C]
    {x y z : RayVertex C} (a : x ⟶ y) (b : y ⟶ z)
    (hfour : 4 ≤ Nat.card (OutgoingQuiverArrow x)) :
    rayPathMap (a.toPath.comp b.toPath) = 0 := by
  by_contra hpath
  have hcomp : rayArrowMorphism b ≫ rayArrowMorphism a ≠ 0 := by
    simpa only [rayPathMap, LinearPathCategory.pathMap_comp,
      rayPathMap_toPath] using hpath
  let I : ZeroHomIdeal C :=
    principalZeroHomIdeal (rayArrowMorphism b ≫ rayArrowMorphism a)
  have hI : I.IsProper := by
    dsimp only [I]
    exact principal_comp_isProper (rayArrowMorphism b)
      (rayArrowMorphism a) b.2
  have hInz : I.IsNonzero := by
    dsimp only [I]
    exact principalZeroHomIdeal_isNonzero_of_ne_zero
      (rayArrowMorphism b ≫ rayArrowMorphism a) hcomp
  letI : IsFiniteRayCategory (CategoryTheory.Quotient I.rel) :=
    I.quotientIsFiniteRayCategory hI
  letI : HasRayValencyAtMostThree (CategoryTheory.Quotient I.rel) :=
    HasThreeValentNonzeroProperRayResidues.valency I hI hInz
  have survive (d : OutgoingQuiverArrow x) :
      ¬I.mem (rayArrowMorphism d.2) := by
    dsimp only [I]
    exact irreducible_not_mem_principal_comp
      (rayArrowMorphism b) (rayArrowMorphism a) b.2 a.2
      (rayArrowMorphism d.2) d.2.2
  let forward : OutgoingQuiverArrow x →
      OutgoingQuiverArrow (I.rayQuiverQuotientObj x) := fun d =>
    ⟨I.rayQuiverQuotientObj d.1,
      I.mapSurvivingRayArrow hI d.2 (survive d)⟩
  have hforward : Function.Injective forward := by
    intro d e hde
    have hback := congrArg
      (I.outgoingQuiverArrowQuotOut hI (I.rayQuiverQuotientObj x)) hde
    simp only [forward, ZeroHomIdeal.outgoingQuiverArrowQuotOut,
      I.rayQuiverQuotOut_map_mapSurvivingRayArrow] at hback
    change d = e at hback
    exact hback
  letI : Finite (OutgoingQuiverArrow (I.rayQuiverQuotientObj x)) :=
    outgoingQuiverArrow_finite _
  have hcard : Nat.card (OutgoingQuiverArrow x) ≤
      Nat.card (OutgoingQuiverArrow (I.rayQuiverQuotientObj x)) :=
    Nat.card_le_card_of_injective forward hforward
  have hthree : Nat.card
      (OutgoingQuiverArrow (I.rayQuiverQuotientObj x)) ≤ 3 :=
    HasRayValencyAtMostThree.outgoing_card_le _
  omega

private theorem fourArrow_incoming_aux
    [Finite C] [IsFiniteRayCategory C]
    [HasThreeValentNonzeroProperRayResidues C]
    {x y z : RayVertex C} (a : x ⟶ y) (b : y ⟶ z)
    (hfour : 4 ≤ Nat.card (IncomingQuiverArrow z)) :
    rayPathMap (a.toPath.comp b.toPath) = 0 := by
  by_contra hpath
  have hcomp : rayArrowMorphism b ≫ rayArrowMorphism a ≠ 0 := by
    simpa only [rayPathMap, LinearPathCategory.pathMap_comp,
      rayPathMap_toPath] using hpath
  let I : ZeroHomIdeal C :=
    principalZeroHomIdeal (rayArrowMorphism b ≫ rayArrowMorphism a)
  have hI : I.IsProper := by
    dsimp only [I]
    exact principal_comp_isProper (rayArrowMorphism b)
      (rayArrowMorphism a) b.2
  have hInz : I.IsNonzero := by
    dsimp only [I]
    exact principalZeroHomIdeal_isNonzero_of_ne_zero
      (rayArrowMorphism b ≫ rayArrowMorphism a) hcomp
  letI : IsFiniteRayCategory (CategoryTheory.Quotient I.rel) :=
    I.quotientIsFiniteRayCategory hI
  letI : HasRayValencyAtMostThree (CategoryTheory.Quotient I.rel) :=
    HasThreeValentNonzeroProperRayResidues.valency I hI hInz
  have survive (d : IncomingQuiverArrow z) :
      ¬I.mem (rayArrowMorphism d.2) := by
    dsimp only [I]
    exact irreducible_not_mem_principal_comp
      (rayArrowMorphism b) (rayArrowMorphism a) b.2 a.2
      (rayArrowMorphism d.2) d.2.2
  let forward : IncomingQuiverArrow z →
      IncomingQuiverArrow (I.rayQuiverQuotientObj z) := fun d =>
    ⟨I.rayQuiverQuotientObj d.1,
      I.mapSurvivingRayArrow hI d.2 (survive d)⟩
  have hforward : Function.Injective forward := by
    intro d e hde
    have hback := congrArg
      (I.incomingQuiverArrowQuotOut hI (I.rayQuiverQuotientObj z)) hde
    simp only [forward, ZeroHomIdeal.incomingQuiverArrowQuotOut,
      I.rayQuiverQuotOut_map_mapSurvivingRayArrow] at hback
    change d = e at hback
    exact hback
  letI : Finite (IncomingQuiverArrow (I.rayQuiverQuotientObj z)) :=
    incomingQuiverArrow_finite _
  have hcard : Nat.card (IncomingQuiverArrow z) ≤
      Nat.card (IncomingQuiverArrow (I.rayQuiverQuotientObj z)) :=
    Nat.card_le_card_of_injective forward hforward
  have hthree : Nat.card
      (IncomingQuiverArrow (I.rayQuiverQuotientObj z)) ≤ 3 :=
    HasRayValencyAtMostThree.incoming_card_le _
  omega

/-- Three-valency of every nonzero proper residue gives the source four-arrow
zero-composition property. -/
theorem hasRayFourArrowZeroCompositions_of_threeValentNonzeroProperRayResidues
    [Finite C] [IsFiniteRayCategory C]
    [HasThreeValentNonzeroProperRayResidues C] :
    HasRayFourArrowZeroCompositions C where
  outgoing_zero := fourArrow_outgoing_aux
  incoming_zero := fourArrow_incoming_aux

/-- Lift a quotient ray path arrow by arrow to chosen original
representatives. -/
abbrev quotOutRayPath (I : ZeroHomIdeal C) (hI : I.IsProper)
    {i j : RayVertex (CategoryTheory.Quotient I.rel)}
    (p : Quiver.Path i j) :
    Quiver.Path ((I.rayQuiverQuotOutPrefunctor hI).obj i)
      ((I.rayQuiverQuotOutPrefunctor hI).obj j) :=
  (I.rayQuiverQuotOutPrefunctor hI).mapPath p

/-- Every chosen original arrow in a lifted quotient ray path lies outside
the collapsed zero Hom ideal. -/
theorem rayPathSurvives_quotOutRayPath
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    {i j : RayVertex (CategoryTheory.Quotient I.rel)}
    (p : Quiver.Path i j) :
    I.RayPathSurvives (I.quotOutRayPath hI p) := by
  induction p with
  | nil => simp [quotOutRayPath, RayPathSurvives]
  | cons p a ih =>
      simp only [quotOutRayPath, Prefunctor.mapPath_cons, RayPathSurvives]
      refine ⟨ih, ?_⟩
      simpa only [rayQuiverQuotOutPrefunctor, rayArrowMorphism,
        quotOutNonzeroHom] using
        I.quotOutNonzeroHom_not_mem
          (⟨a.1, a.2.1⟩ : NonzeroHom _ _)

/-- Mapping a lifted quotient path back to the quotient ray quiver recovers
the original quotient path. -/
theorem mapSurvivingRayPath_quotOutRayPath
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    {i j : RayVertex (CategoryTheory.Quotient I.rel)}
    (p : Quiver.Path i j) :
    I.mapSurvivingRayPath hI (I.quotOutRayPath hI p)
        (I.rayPathSurvives_quotOutRayPath hI p) = p := by
  induction p with
  | nil =>
      simp [quotOutRayPath, mapSurvivingRayPath]
  | cons p a ih =>
      simp [quotOutRayPath, mapSurvivingRayPath, ih,
        I.mapSurvivingRayArrow_rayQuiverQuotOut hI a]

@[simp]
theorem quotOutRayPath_length (I : ZeroHomIdeal C) (hI : I.IsProper)
    {i j : RayVertex (CategoryTheory.Quotient I.rel)}
    (p : Quiver.Path i j) :
    (I.quotOutRayPath hI p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p a ih => simp [quotOutRayPath, ih]

/-- Lifting a mapped surviving original path recovers the original path. -/
theorem quotOutRayPath_mapSurvivingRayPath
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    {i j : RayVertex C} (p : Quiver.Path i j)
    (hp : I.RayPathSurvives p) :
    I.quotOutRayPath hI (I.mapSurvivingRayPath hI p hp) = p := by
  induction p with
  | nil =>
      simp [quotOutRayPath, mapSurvivingRayPath]
  | cons p a ih =>
      simp only [RayPathSurvives] at hp
      rcases hp with ⟨hp, ha⟩
      simp [quotOutRayPath, mapSurvivingRayPath, ih hp,
        I.rayQuiverQuotOut_map_mapSurvivingRayArrow hI a ha]

/-- Evaluating a lifted quotient ray path and mapping it back to the quotient
recovers the original quotient path evaluation. -/
theorem functor_map_rayPathMap_quotOutRayPath
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    {i j : RayVertex (CategoryTheory.Quotient I.rel)}
    (p : Quiver.Path i j) :
    (CategoryTheory.Quotient.functor I.rel).map
        (rayPathMap (I.quotOutRayPath hI p)) =
      rayPathMap p := by
  induction p with
  | nil =>
      rcases i with ⟨⟨i⟩⟩
      rcases j with ⟨⟨j⟩⟩
      simp [quotOutRayPath, rayQuiverQuotOutPrefunctor, rayPathMap]
      change (𝟙 ({ as := i } : CategoryTheory.Quotient I.rel)) = 𝟙 _
      rfl
  | @cons b c p a ih =>
      rcases i with ⟨⟨i⟩⟩
      rcases j with ⟨⟨j⟩⟩
      rcases b with ⟨⟨b⟩⟩
      rcases c with ⟨⟨c⟩⟩
      simp only [quotOutRayPath, Prefunctor.mapPath_cons,
        rayPathMap, LinearPathCategory.pathMap_cons,
        (CategoryTheory.Quotient.functor I.rel).map_comp]
      rw [I.functor_map_rayArrowMorphism_rayQuiverQuotOut hI a, ih]

/-- A nonzero quotient ray path lifts to a nonzero original ray path. -/
theorem rayPathMap_quotOutRayPath_ne_zero
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    {i j : RayVertex (CategoryTheory.Quotient I.rel)}
    (p : Quiver.Path i j) (hp : rayPathMap p ≠ 0) :
    rayPathMap (I.quotOutRayPath hI p) ≠ 0 := by
  intro hzero
  apply hp
  rw [← I.functor_map_rayPathMap_quotOutRayPath hI p, hzero]
  exact (CategoryTheory.Quotient.functor I.rel).map_zero _ _

/-- Long-path endpoint valency descends through a proper zero-Hom quotient. -/
theorem quotientHasRayLongPathEndpointValencyAtMostThree
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    [Finite C] [IsFiniteRayCategory C]
    [HasRayLongPathEndpointValencyAtMostThree C] :
    HasRayLongPathEndpointValencyAtMostThree
      (CategoryTheory.Quotient I.rel) := by
  letI : IsFiniteRayCategory (CategoryTheory.Quotient I.rel) :=
    I.quotientIsFiniteRayCategory hI
  constructor
  · intro x z p hp hpLength
    letI : Finite (OutgoingQuiverArrow
        ((I.rayQuiverQuotOutPrefunctor hI).obj x)) :=
      outgoingQuiverArrow_finite _
    exact (Nat.card_le_card_of_injective
      (I.outgoingQuiverArrowQuotOut hI x)
      (I.outgoingQuiverArrowQuotOut_injective hI x)).trans
        (HasRayLongPathEndpointValencyAtMostThree.outgoing_card_le
          (I.quotOutRayPath hI p)
          (I.rayPathMap_quotOutRayPath_ne_zero hI p hp)
          (by simpa only [I.quotOutRayPath_length hI] using hpLength))
  · intro x z p hp hpLength
    letI : Finite (IncomingQuiverArrow
        ((I.rayQuiverQuotOutPrefunctor hI).obj z)) :=
      incomingQuiverArrow_finite _
    exact (Nat.card_le_card_of_injective
      (I.incomingQuiverArrowQuotOut hI z)
      (I.incomingQuiverArrowQuotOut_injective hI z)).trans
        (HasRayLongPathEndpointValencyAtMostThree.incoming_card_le
          (I.quotOutRayPath hI p)
          (I.rayPathMap_quotOutRayPath_ne_zero hI p hp)
          (by simpa only [I.quotOutRayPath_length hI] using hpLength))

/-- Equal nonzero quotient paths lift to equal nonzero original paths. -/
theorem rayPathContourRelation_related_quotOutRayPath
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    {i j : RayVertex (CategoryTheory.Quotient I.rel)}
    {p q : Quiver.Path i j}
    (hpq : (rayPathContourRelation
      (C := CategoryTheory.Quotient I.rel)).related p q) :
    (rayPathContourRelation (C := C)).related
      (I.quotOutRayPath hI p) (I.quotOutRayPath hI q) := by
  refine ⟨I.rayPathMap_quotOutRayPath_ne_zero hI p hpq.1, ?_⟩
  have hmap :
      (CategoryTheory.Quotient.functor I.rel).map
          (rayPathMap (I.quotOutRayPath hI p)) =
        (CategoryTheory.Quotient.functor I.rel).map
          (rayPathMap (I.quotOutRayPath hI q)) := by
    rw [I.functor_map_rayPathMap_quotOutRayPath hI p,
      I.functor_map_rayPathMap_quotOutRayPath hI q]
    exact hpq.2
  have hrel : I.rel
      (rayPathMap (I.quotOutRayPath hI p))
      (rayPathMap (I.quotOutRayPath hI q)) :=
    (CategoryTheory.Quotient.functor_map_eq_iff _ _ _).1 hmap
  rcases hrel with hrel | hrel
  · exact hrel
  · exfalso
    apply hpq.1
    rw [← I.functor_map_rayPathMap_quotOutRayPath hI p]
    exact (I.functor_map_eq_zero_iff
      (rayPathMap (I.quotOutRayPath hI p))).2 hrel.1

/-- An elementary proper-whisker step in a quotient lifts to an elementary
proper-whisker step between the chosen original paths. -/
theorem properWhiskerInterlacementStep_quotOutRayPath
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    {a b : RayVertex (CategoryTheory.Quotient I.rel)}
    {p q : Quiver.Path a b}
    (hpq : ProperWhiskerInterlacementStep
      (rayPathContourRelation (C := CategoryTheory.Quotient I.rel)) p q) :
    ProperWhiskerInterlacementStep (rayPathContourRelation (C := C))
      (I.quotOutRayPath hI p) (I.quotOutRayPath hI q) := by
  obtain ⟨i, j, s, x, y, t, hxy, houter, hproper, hp, hq⟩ := hpq
  refine ⟨(I.rayQuiverQuotOutPrefunctor hI).obj i,
    (I.rayQuiverQuotOutPrefunctor hI).obj j,
    I.quotOutRayPath hI s, I.quotOutRayPath hI x,
    I.quotOutRayPath hI y, I.quotOutRayPath hI t,
    I.rayPathContourRelation_related_quotOutRayPath hI hxy,
    ?_, ?_, ?_, ?_⟩
  · simpa only [Prefunctor.mapPath_comp] using
      I.rayPathContourRelation_related_quotOutRayPath hI houter
  · simpa only [I.quotOutRayPath_length hI] using hproper
  · simpa only [Prefunctor.mapPath_comp] using
      congrArg (fun r => I.quotOutRayPath hI r) hp
  · simpa only [Prefunctor.mapPath_comp] using
      congrArg (fun r => I.quotOutRayPath hI r) hq

/-- Proper-whisker interlacement in a quotient lifts to proper-whisker
interlacement between the chosen original representatives. -/
theorem properWhiskerInterlaced_quotOutRayPath
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    {a b : RayVertex (CategoryTheory.Quotient I.rel)}
    {p q : Quiver.Path a b}
    (hpq : (properWhiskerInterlacementRelation
      (rayPathContourRelation
        (C := CategoryTheory.Quotient I.rel))).interlaced p q) :
    (properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced
        (I.quotOutRayPath hI p) (I.quotOutRayPath hI q) := by
  change Relation.EqvGen _ p q at hpq
  change Relation.EqvGen _
    (I.quotOutRayPath hI p) (I.quotOutRayPath hI q)
  induction hpq with
  | rel x y hxy =>
      exact Relation.EqvGen.rel _ _
        (I.properWhiskerInterlacementStep_quotOutRayPath hI hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y hxy ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact Relation.EqvGen.trans _ _ _ ihxy ihyz

/-- On a common ray which survives the quotient, proper-whisker
interlacement is preserved and reflected by mapping paths to the quotient. -/
theorem properWhiskerInterlaced_mapSurvivingRayPath_iff
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    {a b : RayVertex C} (p q : Quiver.Path a b)
    (hp : I.RayPathSurvives p) (hq : I.RayPathSurvives q)
    (hpNotMem : ¬I.mem (rayPathMap p)) :
    (properWhiskerInterlacementRelation
      (rayPathContourRelation
        (C := CategoryTheory.Quotient I.rel))).interlaced
        (I.mapSurvivingRayPath hI p hp)
        (I.mapSurvivingRayPath hI q hq) ↔
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))).interlaced p q := by
  constructor
  · intro hpq
    have hpq' := I.properWhiskerInterlaced_quotOutRayPath hI hpq
    rw [I.quotOutRayPath_mapSurvivingRayPath hI p hp,
      I.quotOutRayPath_mapSurvivingRayPath hI q hq] at hpq'
    exact hpq'
  · intro hpq
    obtain ⟨hp', hq', hpq'⟩ :=
      I.exists_properWhiskerInterlaced_mapSurvivingRayPath
        hI hpq hpNotMem
    cases Subsingleton.elim hp' hp
    cases Subsingleton.elim hq' hq
    exact hpq'

/-- An essential contour on a ray which survives remains essential after
mapping to the quotient. -/
theorem isEssentialPathContour_mapSurvivingRayPath
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    {a b : RayVertex C} (p q : Quiver.Path a b)
    (hp : I.RayPathSurvives p) (hq : I.RayPathSurvives q)
    (hpNotMem : ¬I.mem (rayPathMap p))
    (hpq : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q) :
    IsEssentialPathContour
      (rayPathContourRelation
        (C := CategoryTheory.Quotient I.rel))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation
          (C := CategoryTheory.Quotient I.rel)))
      (I.mapSurvivingRayPath hI p hp)
      (I.mapSurvivingRayPath hI q hq) := by
  constructor
  · exact I.rayPathContourRelation_related_mapSurvivingRayPath
      hI p q hp hq hpNotMem hpq.1
  · intro hinterlaced
    exact hpq.2 ((I.properWhiskerInterlaced_mapSurvivingRayPath_iff
      hI p q hp hq hpNotMem).1 hinterlaced)

/-- Lift a selected equal-nonzero quotient contour to the contour between its
chosen original path representatives. -/
def quotOutRelatedRayContour
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    (K : RelatedContour
      (rayPathContourRelation (C := CategoryTheory.Quotient I.rel))) :
    RelatedContour (rayPathContourRelation (C := C)) :=
  ⟨⟨(I.rayQuiverQuotOutPrefunctor hI).obj K.1.source,
      (I.rayQuiverQuotOutPrefunctor hI).obj K.1.target,
      I.quotOutRayPath hI K.1.left,
      I.quotOutRayPath hI K.1.right⟩,
    I.rayPathContourRelation_related_quotOutRayPath hI K.property⟩

@[simp]
theorem quotOutRelatedRayContour_relatedContour
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    {i j : RayVertex (CategoryTheory.Quotient I.rel)}
    (p q : Quiver.Path i j)
    (hpq : (rayPathContourRelation
      (C := CategoryTheory.Quotient I.rel)).related p q) :
    I.quotOutRelatedRayContour hI
        (relatedContour
          (rayPathContourRelation (C := CategoryTheory.Quotient I.rel))
          p q hpq) =
      relatedContour (rayPathContourRelation (C := C))
        (I.quotOutRayPath hI p) (I.quotOutRayPath hI q)
        (I.rayPathContourRelation_related_quotOutRayPath hI hpq) := by
  rfl

/-- Restricting a surviving original contour to the quotient and then
choosing original representatives recovers the original contour. -/
theorem quotOutRelatedRayContour_mapSurvivingRelatedRayContour
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    (K : RelatedContour (rayPathContourRelation (C := C)))
    (hK : ¬I.mem (rayPathMap K.1.left)) :
    I.quotOutRelatedRayContour hI
        (I.mapSurvivingRelatedRayContour hI K hK) = K := by
  rcases K with ⟨⟨source, target, left, right⟩, hrelated⟩
  apply Subtype.ext
  simp [quotOutRelatedRayContour, mapSurvivingRelatedRayContour,
    I.quotOutRayPath_mapSurvivingRayPath hI]

/-- Restrict an original ray contour function to a proper zero-ideal quotient
by evaluating it on chosen original path representatives. -/
def quotOutContourScalarFunction
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    (c : contourScalarFunctionSubgroup (k := k)
      (rayPathContourRelation (C := C))) :
    contourScalarFunctionSubgroup (k := k)
      (rayPathContourRelation (C := CategoryTheory.Quotient I.rel)) := by
  refine ⟨fun K => c.1 (I.quotOutRelatedRayContour hI K), ?_⟩
  constructor
  · intro i j p q r hpq hqr
    change c.1 (I.quotOutRelatedRayContour hI
        (relatedContour
          (rayPathContourRelation
            (C := CategoryTheory.Quotient I.rel)) p r
          ((rayPathContourRelation
            (C := CategoryTheory.Quotient I.rel)).trans hpq hqr))) =
      c.1 (I.quotOutRelatedRayContour hI
          (relatedContour
            (rayPathContourRelation
              (C := CategoryTheory.Quotient I.rel)) p q hpq)) *
        c.1 (I.quotOutRelatedRayContour hI
          (relatedContour
            (rayPathContourRelation
              (C := CategoryTheory.Quotient I.rel)) q r hqr))
    rw [I.quotOutRelatedRayContour_relatedContour hI,
      I.quotOutRelatedRayContour_relatedContour hI,
      I.quotOutRelatedRayContour_relatedContour hI]
    exact c.property.1
      (I.quotOutRayPath hI p) (I.quotOutRayPath hI q)
        (I.quotOutRayPath hI r)
        (I.rayPathContourRelation_related_quotOutRayPath hI hpq)
        (I.rayPathContourRelation_related_quotOutRayPath hI hqr)
  · intro a i j b u p q v hpq hwhisker
    change c.1 (I.quotOutRelatedRayContour hI
        (relatedContour
          (rayPathContourRelation
            (C := CategoryTheory.Quotient I.rel))
          ((u.comp p).comp v) ((u.comp q).comp v) hwhisker)) =
      c.1 (I.quotOutRelatedRayContour hI
        (relatedContour
          (rayPathContourRelation
            (C := CategoryTheory.Quotient I.rel)) p q hpq))
    have hwhisker' : (rayPathContourRelation (C := C)).related
        (((I.quotOutRayPath hI u).comp (I.quotOutRayPath hI p)).comp
          (I.quotOutRayPath hI v))
        (((I.quotOutRayPath hI u).comp (I.quotOutRayPath hI q)).comp
          (I.quotOutRayPath hI v)) := by
      simpa only [← Prefunctor.mapPath_comp] using
        I.rayPathContourRelation_related_quotOutRayPath hI hwhisker
    rw [I.quotOutRelatedRayContour_relatedContour hI,
      I.quotOutRelatedRayContour_relatedContour hI]
    simpa only [Prefunctor.mapPath_comp] using
      c.property.2 (I.quotOutRayPath hI u)
        (I.quotOutRayPath hI p) (I.quotOutRayPath hI q)
        (I.quotOutRayPath hI v)
        (I.rayPathContourRelation_related_quotOutRayPath hI hpq)
        hwhisker'

@[simp]
theorem contourScalarFamily_quotOutContourScalarFunction
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    (c : contourScalarFunctionSubgroup (k := k)
      (rayPathContourRelation (C := C)))
    (K : RelatedContour
      (rayPathContourRelation (C := CategoryTheory.Quotient I.rel))) :
    contourScalarFamily
        (rayPathContourRelation (C := CategoryTheory.Quotient I.rel))
        (I.quotOutContourScalarFunction hI c) K =
      contourScalarFamily (rayPathContourRelation (C := C)) c
        (I.quotOutRelatedRayContour hI K) :=
  rfl

/-- Restriction of a contour function has its original value on every
surviving original contour mapped to the quotient. -/
theorem contourScalarFamily_quotOutContourScalarFunction_mapSurviving
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    (c : contourScalarFunctionSubgroup (k := k)
      (rayPathContourRelation (C := C)))
    (K : RelatedContour (rayPathContourRelation (C := C)))
    (hK : ¬I.mem (rayPathMap K.1.left)) :
    contourScalarFamily
        (rayPathContourRelation (C := CategoryTheory.Quotient I.rel))
        (I.quotOutContourScalarFunction hI c)
        (I.mapSurvivingRelatedRayContour hI K hK) =
      contourScalarFamily (rayPathContourRelation (C := C)) c K := by
  rw [I.contourScalarFamily_quotOutContourScalarFunction hI,
    I.quotOutRelatedRayContour_mapSurvivingRelatedRayContour hI]

/-- Clinging to a surviving original ray descends to clinging to its image
for the restricted quotient contour function. -/
theorem contourFunctionClingsToPath_quotOutContourScalarFunction
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    (c : contourScalarFunctionSubgroup (k := k)
      (rayPathContourRelation (C := C)))
    {a b : RayVertex C} (p : Quiver.Path a b)
    (hp : I.RayPathSurvives p)
    (hpNotMem : ¬I.mem (rayPathMap p))
    (hclings : ContourFunctionClingsToPath
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) c p) :
    ContourFunctionClingsToPath
      (rayPathContourRelation (C := CategoryTheory.Quotient I.rel))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation
          (C := CategoryTheory.Quotient I.rel)))
      (I.quotOutContourScalarFunction hI c)
      (I.mapSurvivingRayPath hI p hp) := by
  intro q hpq
  let qOut := I.quotOutRayPath hI q
  have hpqOut := I.rayPathContourRelation_related_quotOutRayPath hI hpq
  rw [I.quotOutRayPath_mapSurvivingRayPath hI p hp] at hpqOut
  obtain ⟨p', q', hppI, hppR, hqqI, hqqR, hpq'R, hvalue⟩ :=
    hclings qOut hpqOut
  have hp'NotMem : ¬I.mem (rayPathMap p') :=
    I.rayPathMap_right_not_mem_of_related hppR hpNotMem
  have hqOutNotMem : ¬I.mem (rayPathMap qOut) :=
    I.rayPathMap_right_not_mem_of_related hpqOut hpNotMem
  have hq'NotMem : ¬I.mem (rayPathMap q') :=
    I.rayPathMap_right_not_mem_of_related hqqR hqOutNotMem
  let hp' : I.RayPathSurvives p' :=
    I.rayPathSurvives_of_rayPathMap_not_mem p' hp'NotMem
  let hq' : I.RayPathSurvives q' :=
    I.rayPathSurvives_of_rayPathMap_not_mem q' hq'NotMem
  let hqOut : I.RayPathSurvives qOut :=
    I.rayPathSurvives_quotOutRayPath hI q
  let pQ := I.mapSurvivingRayPath hI p' hp'
  let qQ := I.mapSurvivingRayPath hI q' hq'
  have hppIQ : (properWhiskerInterlacementRelation
      (rayPathContourRelation
        (C := CategoryTheory.Quotient I.rel))).interlaced
      (I.mapSurvivingRayPath hI p hp) pQ :=
    (I.properWhiskerInterlaced_mapSurvivingRayPath_iff
      hI p p' hp hp' hpNotMem).2 hppI
  have hppRQ : (rayPathContourRelation
      (C := CategoryTheory.Quotient I.rel)).related
      (I.mapSurvivingRayPath hI p hp) pQ :=
    I.rayPathContourRelation_related_mapSurvivingRayPath
      hI p p' hp hp' hpNotMem hppR
  have hqqIQ : (properWhiskerInterlacementRelation
      (rayPathContourRelation
        (C := CategoryTheory.Quotient I.rel))).interlaced q qQ := by
    have hqqIQ' := (I.properWhiskerInterlaced_mapSurvivingRayPath_iff
      hI qOut q' hqOut hq' hqOutNotMem).2 hqqI
    rw [show I.mapSurvivingRayPath hI qOut hqOut = q by
      exact I.mapSurvivingRayPath_quotOutRayPath hI q] at hqqIQ'
    exact hqqIQ'
  have hqqRQ : (rayPathContourRelation
      (C := CategoryTheory.Quotient I.rel)).related q qQ := by
    have hqqRQ' := I.rayPathContourRelation_related_mapSurvivingRayPath
      hI qOut q' hqOut hq' hqOutNotMem hqqR
    rw [show I.mapSurvivingRayPath hI qOut hqOut = q by
      exact I.mapSurvivingRayPath_quotOutRayPath hI q] at hqqRQ'
    exact hqqRQ'
  have hpq'RQ : (rayPathContourRelation
      (C := CategoryTheory.Quotient I.rel)).related pQ qQ :=
    I.rayPathContourRelation_related_mapSurvivingRayPath
      hI p' q' hp' hq' hp'NotMem hpq'R
  refine ⟨pQ, qQ, hppIQ, hppRQ, hqqIQ, hqqRQ, hpq'RQ, ?_⟩
  let K : RelatedContour (rayPathContourRelation (C := C)) :=
    relatedContour (rayPathContourRelation (C := C)) p' q' hpq'R
  have hvalueMap :=
    I.contourScalarFamily_quotOutContourScalarFunction_mapSurviving
      hI c K hp'NotMem
  have hKQ : I.mapSurvivingRelatedRayContour hI K hp'NotMem =
      relatedContour
        (rayPathContourRelation
          (C := CategoryTheory.Quotient I.rel)) pQ qQ hpq'RQ := by
    apply Subtype.ext
    simp [K, pQ, qQ, mapSurvivingRelatedRayContour]
    congr
  have hvalueMap' : contourScalarFamily
      (rayPathContourRelation (C := CategoryTheory.Quotient I.rel))
      (I.quotOutContourScalarFunction hI c)
      (relatedContour
        (rayPathContourRelation
          (C := CategoryTheory.Quotient I.rel)) pQ qQ hpq'RQ) =
      contourScalarFamily (rayPathContourRelation (C := C)) c K := by
    rw [← hKQ]
    exact hvalueMap
  exact hvalueMap'.trans hvalue

/-- Clinging of the restricted quotient contour function lifts back to
clinging of the original contour function on a surviving ray. -/
theorem contourFunctionClingsToPath_of_quotOutContourScalarFunction
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    (c : contourScalarFunctionSubgroup (k := k)
      (rayPathContourRelation (C := C)))
    {a b : RayVertex C} (p : Quiver.Path a b)
    (hp : I.RayPathSurvives p)
    (hpNotMem : ¬I.mem (rayPathMap p))
    (hclings : ContourFunctionClingsToPath
      (rayPathContourRelation (C := CategoryTheory.Quotient I.rel))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation
          (C := CategoryTheory.Quotient I.rel)))
      (I.quotOutContourScalarFunction hI c)
      (I.mapSurvivingRayPath hI p hp)) :
    ContourFunctionClingsToPath
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) c p := by
  intro q hpq
  have hqNotMem : ¬I.mem (rayPathMap q) :=
    I.rayPathMap_right_not_mem_of_related hpq hpNotMem
  let hq : I.RayPathSurvives q :=
    I.rayPathSurvives_of_rayPathMap_not_mem q hqNotMem
  have hpqQ := I.rayPathContourRelation_related_mapSurvivingRayPath
    hI p q hp hq hpNotMem hpq
  obtain ⟨pQ, qQ, hppI, hppR, hqqI, hqqR, hpqQR, hvalue⟩ :=
    hclings (I.mapSurvivingRayPath hI q hq) hpqQ
  let pOut := I.quotOutRayPath hI pQ
  let qOut := I.quotOutRayPath hI qQ
  have hppIOut := I.properWhiskerInterlaced_quotOutRayPath hI hppI
  rw [I.quotOutRayPath_mapSurvivingRayPath hI p hp] at hppIOut
  have hppROut := I.rayPathContourRelation_related_quotOutRayPath hI hppR
  rw [I.quotOutRayPath_mapSurvivingRayPath hI p hp] at hppROut
  have hqqIOut := I.properWhiskerInterlaced_quotOutRayPath hI hqqI
  rw [I.quotOutRayPath_mapSurvivingRayPath hI q hq] at hqqIOut
  have hqqROut := I.rayPathContourRelation_related_quotOutRayPath hI hqqR
  rw [I.quotOutRayPath_mapSurvivingRayPath hI q hq] at hqqROut
  have hpqOutR := I.rayPathContourRelation_related_quotOutRayPath hI hpqQR
  refine ⟨pOut, qOut, hppIOut, hppROut, hqqIOut, hqqROut,
    hpqOutR, ?_⟩
  have hvalue' :=
    I.contourScalarFamily_quotOutContourScalarFunction hI c
      (relatedContour
        (rayPathContourRelation
          (C := CategoryTheory.Quotient I.rel)) pQ qQ hpqQR)
  rw [I.quotOutRelatedRayContour_relatedContour hI] at hvalue'
  exact hvalue'.symm.trans hvalue

/-- On every surviving ray, path-level clinging is equivalent before and
after restricting the contour function to a proper zero-ideal quotient. -/
theorem contourFunctionClingsToPath_quotOutContourScalarFunction_iff
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    (c : contourScalarFunctionSubgroup (k := k)
      (rayPathContourRelation (C := C)))
    {a b : RayVertex C} (p : Quiver.Path a b)
    (hp : I.RayPathSurvives p)
    (hpNotMem : ¬I.mem (rayPathMap p)) :
    ContourFunctionClingsToPath
        (rayPathContourRelation (C := CategoryTheory.Quotient I.rel))
        (properWhiskerInterlacementRelation
          (rayPathContourRelation
            (C := CategoryTheory.Quotient I.rel)))
        (I.quotOutContourScalarFunction hI c)
        (I.mapSurvivingRayPath hI p hp) ↔
      ContourFunctionClingsToPath
        (rayPathContourRelation (C := C))
        (properWhiskerInterlacementRelation
          (rayPathContourRelation (C := C))) c p := by
  constructor
  · exact I.contourFunctionClingsToPath_of_quotOutContourScalarFunction
      hI c p hp hpNotMem
  · exact I.contourFunctionClingsToPath_quotOutContourScalarFunction
      hI c p hp hpNotMem

/-- Exactness of the restricted quotient contour function lifts to one arrow
correction realizing the original contour function on every ray which
survives the quotient. -/
theorem exists_liftQuotientArrowUnitWeight_of_isExact_quotOut
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    (c : contourScalarFunctionSubgroup (k := k)
      (rayPathContourRelation (C := C)))
    (hexact : IsExactContourFunction
      (rayPathContourRelation (C := CategoryTheory.Quotient I.rel))
      (I.quotOutContourScalarFunction hI c)) :
    ∃ e : ArrowUnitWeight k (RayVertex C),
      ∀ (K : RelatedContour (rayPathContourRelation (C := C)))
        (_hK : ¬I.mem (rayPathMap K.1.left)),
        contourScalarFamily (rayPathContourRelation (C := C)) c K =
          contourCoboundary (k := k) e K.1 := by
  obtain ⟨e, he⟩ :=
    isExactContourScalarFamily_of_isExactContourFunction
      (rayPathContourRelation (C := CategoryTheory.Quotient I.rel))
      (I.quotOutContourScalarFunction hI c) hexact
  refine ⟨I.liftQuotientArrowUnitWeight hI e, ?_⟩
  intro K hK
  calc
    contourScalarFamily (rayPathContourRelation (C := C)) c K =
        contourScalarFamily
          (rayPathContourRelation (C := CategoryTheory.Quotient I.rel))
          (I.quotOutContourScalarFunction hI c)
          (I.mapSurvivingRelatedRayContour hI K hK) :=
      (I.contourScalarFamily_quotOutContourScalarFunction_mapSurviving
        hI c K hK).symm
    _ = contourCoboundary (k := k) e
        (I.mapSurvivingRelatedRayContour hI K hK).1 :=
      he (I.mapSurvivingRelatedRayContour hI K hK)
    _ = contourCoboundary (k := k)
        (I.liftQuotientArrowUnitWeight hI e) K.1 :=
      (I.contourCoboundary_liftQuotientArrowUnitWeight hI e K hK).symm

/-- If the restricted quotient contour function is exact, one lifted
correction makes the corrected original contour function cling to every ray
which survives the quotient. -/
theorem exists_liftQuotientArrowUnitWeight_clingsToPath_of_isExact_quotOut
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    (c : contourScalarFunctionSubgroup (k := k)
      (rayPathContourRelation (C := C)))
    (hexact : IsExactContourFunction
      (rayPathContourRelation (C := CategoryTheory.Quotient I.rel))
      (I.quotOutContourScalarFunction hI c)) :
    ∃ e : ArrowUnitWeight k (RayVertex C),
      ∀ {a b : RayVertex C} (p : Quiver.Path a b),
        ¬I.mem (rayPathMap p) →
          ContourFunctionClingsToPath
            (rayPathContourRelation (C := C))
            (properWhiskerInterlacementRelation
              (rayPathContourRelation (C := C)))
            (c * (contourFunctionCoboundaryHom (k := k)
              (rayPathContourRelation (C := C)) e)⁻¹) p := by
  obtain ⟨e, he⟩ :=
    I.exists_liftQuotientArrowUnitWeight_of_isExact_quotOut hI c hexact
  refine ⟨e, ?_⟩
  intro a b p hpNotMem q hpq
  have hpp : (rayPathContourRelation (C := C)).related p p :=
    (rayPathContourRelation (C := C)).trans hpq
      ((rayPathContourRelation (C := C)).symm hpq)
  have hqq : (rayPathContourRelation (C := C)).related q q :=
    (rayPathContourRelation (C := C)).trans
      ((rayPathContourRelation (C := C)).symm hpq) hpq
  refine ⟨p, q,
    (properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).refl p,
    hpp,
    (properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).refl q,
    hqq, hpq, ?_⟩
  apply contourScalarFamily_mul_inv_coboundary_eq_one_of_ratio
    (rayPathContourRelation (C := C)) c e
      (relatedContour (rayPathContourRelation (C := C)) p q hpq)
  exact (he
    (relatedContour (rayPathContourRelation (C := C)) p q hpq)
    hpNotMem).symm

/-- An arrow correction is invisible on the essential contours which
survive a zero-Hom-ideal quotient when its path-weight ratio is one on every
such contour.  Interlaced contours are deliberately omitted: clinging can
use a reflexive representative on those contours without inspecting their
scalar value. -/
def ArrowUnitWeightInvisibleOnSurvivingEssentialContours
    (J : ZeroHomIdeal C) (e : ArrowUnitWeight k (RayVertex C)) : Prop :=
  ∀ {a b : RayVertex C} (p q : Quiver.Path a b),
    (rayPathContourRelation (C := C)).related p q →
      ¬J.mem (rayPathMap p) →
        ¬(properWhiskerInterlacementRelation
          (rayPathContourRelation (C := C))).interlaced p q →
          pathWeightRatio e p q = 1

/-- A Boolean arrow selector is balanced on surviving essential contours when
both sides of each such contour contain the same number of selected arrows. -/
def ArrowSelectorBalancedOnSurvivingEssentialContours
    (J : ZeroHomIdeal C) (select : ArrowSelector (RayVertex C)) : Prop :=
  ∀ {a b : RayVertex C} (p q : Quiver.Path a b),
    (rayPathContourRelation (C := C)).related p q →
      ¬J.mem (rayPathMap p) →
        ¬(properWhiskerInterlacementRelation
          (rayPathContourRelation (C := C))).interlaced p q →
          selectedArrowCount select p = selectedArrowCount select q

/-- One bundled arrow is absent from the essential contours surviving the
quotient when it has no occurrence on the left side of any such contour.
Symmetry gives the same conclusion on the right side. -/
def BundledArrowAbsentFromSurvivingEssentialContours
    (J : ZeroHomIdeal C) (selected : BundledQuiverArrow (RayVertex C)) :
    Prop :=
  ∀ {a b : RayVertex C} (p q : Quiver.Path a b),
    (rayPathContourRelation (C := C)).related p q →
      ¬J.mem (rayPathMap p) →
        ¬(properWhiskerInterlacementRelation
          (rayPathContourRelation (C := C))).interlaced p q →
          IsEmpty (BundledArrowOccurrence selected p)

/-- Absence of one arrow from every surviving essential contour makes its
singleton selector balanced there. -/
theorem arrowSelectorBalancedOnSurvivingEssentialContours_single_of_absent
    (J : ZeroHomIdeal C) (selected : BundledQuiverArrow (RayVertex C))
    (habsent : J.BundledArrowAbsentFromSurvivingEssentialContours selected) :
    J.ArrowSelectorBalancedOnSurvivingEssentialContours
      (singleArrowSelector selected) := by
  intro a b p q hpq hpNotMem hpqNot
  have hpZero : selectedArrowCount (singleArrowSelector selected) p = 0 := by
    by_contra hpCount
    obtain ⟨o⟩ :=
      exists_bundledArrowOccurrence_of_selectedArrowCount_ne_zero
        selected p hpCount
    exact (habsent p q hpq hpNotMem hpqNot).false o
  have hqNotMem : ¬J.mem (rayPathMap q) := by
    rw [← hpq.2]
    exact hpNotMem
  have hqZero : selectedArrowCount (singleArrowSelector selected) q = 0 := by
    by_contra hqCount
    obtain ⟨o⟩ :=
      exists_bundledArrowOccurrence_of_selectedArrowCount_ne_zero
        selected q hqCount
    exact (habsent q p
      ((rayPathContourRelation (C := C)).symm hpq) hqNotMem
      (fun hqp ↦ hpqNot ((properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))).symm hqp))).false o
  rw [hpZero, hqZero]

/-- The selector which marks no arrow. -/
def emptyArrowSelector : ArrowSelector (RayVertex C) :=
  fun _ ↦ false

@[simp]
theorem selectedArrowCount_emptyArrowSelector
    {a b : RayVertex C} (p : Quiver.Path a b) :
    selectedArrowCount (emptyArrowSelector (C := C)) p = 0 := by
  induction p with
  | nil => simp [selectedArrowCount]
  | cons p a ih => simpa [selectedArrowCount, emptyArrowSelector] using ih

/-- The empty selector is balanced on every surviving contour. -/
theorem arrowSelectorBalancedOnSurvivingEssentialContours_empty
    (J : ZeroHomIdeal C) :
    J.ArrowSelectorBalancedOnSurvivingEssentialContours
      (emptyArrowSelector (C := C)) := by
  intro a b p q hpq hpNotMem hpqNot
  simp

/-- Equal occurrence counts on surviving essential contours make every
single-selector arrow weight invisible there, for any chosen unit scalar. -/
theorem arrowUnitWeightInvisibleOnSurvivingEssentialContours_selector
    (J : ZeroHomIdeal C) (select : ArrowSelector (RayVertex C))
    (d : kˣ)
    (hbalanced : J.ArrowSelectorBalancedOnSurvivingEssentialContours select) :
    J.ArrowUnitWeightInvisibleOnSurvivingEssentialContours
      (selectorUnitWeight select d) := by
  intro a b p q hpq hpNotMem hpqNot
  exact pathWeightRatio_selectorUnitWeight_eq_one_of_count_eq
    select d p q (hbalanced p q hpq hpNotMem hpqNot)

/-- A finite selector family is balanced on surviving essential contours when
each of its selectors is balanced there. -/
def ArrowSelectorFamilyBalancedOnSurvivingEssentialContours
    {T : Type*} (J : ZeroHomIdeal C)
    (select : T → ArrowSelector (RayVertex C)) : Prop :=
  ∀ t, J.ArrowSelectorBalancedOnSurvivingEssentialContours (select t)

/-- A pair of selectors with the same weight is jointly balanced on surviving
essential contours when their total occurrence count is the same on both
sides.  This is weaker than requiring the two selectors to be balanced
separately and is the condition used by the paired correction. -/
def ArrowSelectorPairBalancedOnSurvivingEssentialContours
    (J : ZeroHomIdeal C) (primary companion : ArrowSelector (RayVertex C)) :
    Prop :=
  ∀ {a b : RayVertex C} (p q : Quiver.Path a b),
    (rayPathContourRelation (C := C)).related p q →
      ¬J.mem (rayPathMap p) →
        ¬(properWhiskerInterlacementRelation
          (rayPathContourRelation (C := C))).interlaced p q →
          selectedArrowCount primary p + selectedArrowCount companion p =
            selectedArrowCount primary q + selectedArrowCount companion q

/-- Joint selector balance makes the paired same-weight correction
invisible on every surviving essential contour. -/
theorem arrowUnitWeightInvisibleOnSurvivingEssentialContours_selectorPair
    (J : ZeroHomIdeal C) (primary companion : ArrowSelector (RayVertex C))
    (d : kˣ)
    (hbalanced : J.ArrowSelectorPairBalancedOnSurvivingEssentialContours
      primary companion) :
    J.ArrowUnitWeightInvisibleOnSurvivingEssentialContours
      (selectorUnitWeight primary d⁻¹ *
        selectorUnitWeight companion d⁻¹) := by
  intro a b p q hpq hpNotMem hpqNot
  have hcount := hbalanced p q hpq hpNotMem hpqNot
  rw [pathWeightRatio_mul]
  simp only [pathWeightRatio, path_weight_selectorUnitWeight]
  calc
    (d⁻¹ ^ selectedArrowCount primary p)⁻¹ *
          d⁻¹ ^ selectedArrowCount primary q *
        ((d⁻¹ ^ selectedArrowCount companion p)⁻¹ *
          d⁻¹ ^ selectedArrowCount companion q) =
      ((d⁻¹) ^ (selectedArrowCount primary p +
          selectedArrowCount companion p))⁻¹ *
        (d⁻¹) ^ (selectedArrowCount primary q +
          selectedArrowCount companion q) := by
            rw [pow_add, pow_add]
            group
    _ = 1 := by rw [hcount]; simp

/-- A finite family of selector weights is invisible on surviving essential
contours as soon as every selector in the family has equal occurrence counts
on both sides. -/
theorem arrowUnitWeightInvisibleOnSurvivingEssentialContours_selectorFamily
    {T : Type*} [Fintype T]
    (J : ZeroHomIdeal C) (select : T → ArrowSelector (RayVertex C))
    (d : T → kˣ)
    (hbalanced :
      J.ArrowSelectorFamilyBalancedOnSurvivingEssentialContours select) :
    J.ArrowUnitWeightInvisibleOnSurvivingEssentialContours
      (selectorFamilyUnitWeight select d) := by
  intro a b p q hpq hpNotMem hpqNot
  exact pathWeightRatio_selectorFamilyUnitWeight_eq_one_of_count_eq
    select d p q (fun t ↦ hbalanced t p q hpq hpNotMem hpqNot)

/-- Invisibility on surviving essential contours is closed under pointwise
multiplication of arrow weights. -/
theorem ArrowUnitWeightInvisibleOnSurvivingEssentialContours.mul
    (J : ZeroHomIdeal C) {e f : ArrowUnitWeight k (RayVertex C)}
    (he : J.ArrowUnitWeightInvisibleOnSurvivingEssentialContours e)
    (hf : J.ArrowUnitWeightInvisibleOnSurvivingEssentialContours f) :
    J.ArrowUnitWeightInvisibleOnSurvivingEssentialContours (e * f) := by
  intro a b p q hpq hpNotMem hpqNot
  rw [pathWeightRatio_mul, he p q hpq hpNotMem hpqNot,
    hf p q hpq hpNotMem hpqNot]
  simp

/-- The paired `N = 2` correction under the joint total-count balance
condition.  Separate balance of the two selectors is unnecessary: equality
of their total occurrence counts is exactly what makes the same-weight pair
invisible in the residue. -/
theorem exists_roiterTwoClassPairedCorrection_invisibleOnSurviving_of_pairBalanced
    (J : ZeroHomIdeal C)
    (c : contourScalarFunctionSubgroup (k := k)
      (rayPathContourRelation (C := C)))
    {i j : RayVertex C} (p q : Quiver.Path i j)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (primary companion : ArrowSelector (RayVertex C))
    (hprimaryP : selectedArrowCount primary p = 1)
    (hprimaryQ : selectedArrowCount primary q = 0)
    (hcompanion : selectedArrowCount companion p =
      selectedArrowCount companion q)
    (hpairBalanced :
      J.ArrowSelectorPairBalancedOnSurvivingEssentialContours
        primary companion) :
    ∃ e : ArrowUnitWeight k (RayVertex C),
      J.ArrowUnitWeightInvisibleOnSurvivingEssentialContours e ∧
        contourScalarFamily (rayPathContourRelation (C := C))
          (inverseCoboundaryCorrection
            (rayPathContourRelation (C := C)) c e)
          (relatedContour (rayPathContourRelation (C := C)) p q hpq) = 1 := by
  let R := rayPathContourRelation (C := C)
  let d := contourScalarFamily R c (relatedContour R p q hpq)
  let e : ArrowUnitWeight k (RayVertex C) :=
    selectorUnitWeight primary d⁻¹ * selectorUnitWeight companion d⁻¹
  refine ⟨e, ?_, ?_⟩
  · exact J.arrowUnitWeightInvisibleOnSurvivingEssentialContours_selectorPair
      primary companion d hpairBalanced
  · apply contourScalarFamily_mul_inv_coboundary_eq_one_of_ratio
    change pathWeightRatio e p q =
      contourScalarFamily R c (relatedContour R p q hpq)
    dsimp only [e]
    rw [pathWeightRatio_mul,
      pathWeightRatio_selectorUnitWeight_inv_of_count_one_zero
        primary d p q hprimaryP hprimaryQ,
      pathWeightRatio_selectorUnitWeight_eq_one_of_count_eq
        companion d⁻¹ p q hcompanion]
    simp [d]

/-- The paired `N = 2` correction, strengthened with the residue-preservation
property.  If both sparse selectors are balanced on surviving essential
contours, the same-weight pair both normalizes the chosen killed contour and
is invisible on every surviving essential contour. -/
theorem exists_roiterTwoClassPairedCorrection_invisibleOnSurviving
    (J : ZeroHomIdeal C)
    (c : contourScalarFunctionSubgroup (k := k)
      (rayPathContourRelation (C := C)))
    {i j : RayVertex C} (p q : Quiver.Path i j)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (primary companion : ArrowSelector (RayVertex C))
    (hprimaryP : selectedArrowCount primary p = 1)
    (hprimaryQ : selectedArrowCount primary q = 0)
    (hcompanion : selectedArrowCount companion p =
      selectedArrowCount companion q)
    (hprimaryBalanced :
      J.ArrowSelectorBalancedOnSurvivingEssentialContours primary)
    (hcompanionBalanced :
      J.ArrowSelectorBalancedOnSurvivingEssentialContours companion) :
    ∃ e : ArrowUnitWeight k (RayVertex C),
      J.ArrowUnitWeightInvisibleOnSurvivingEssentialContours e ∧
        contourScalarFamily (rayPathContourRelation (C := C))
          (inverseCoboundaryCorrection
            (rayPathContourRelation (C := C)) c e)
          (relatedContour (rayPathContourRelation (C := C)) p q hpq) = 1 := by
  let R := rayPathContourRelation (C := C)
  let d := contourScalarFamily R c (relatedContour R p q hpq)
  let e : ArrowUnitWeight k (RayVertex C) :=
    selectorUnitWeight primary d⁻¹ * selectorUnitWeight companion d⁻¹
  refine ⟨e, ?_, ?_⟩
  · apply ArrowUnitWeightInvisibleOnSurvivingEssentialContours.mul J
    · exact J.arrowUnitWeightInvisibleOnSurvivingEssentialContours_selector
        primary d⁻¹ hprimaryBalanced
    · exact J.arrowUnitWeightInvisibleOnSurvivingEssentialContours_selector
        companion d⁻¹ hcompanionBalanced
  · apply contourScalarFamily_mul_inv_coboundary_eq_one_of_ratio
    change pathWeightRatio e p q =
      contourScalarFamily R c (relatedContour R p q hpq)
    dsimp only [e]
    rw [pathWeightRatio_mul,
      pathWeightRatio_selectorUnitWeight_inv_of_count_one_zero
        primary d p q hprimaryP hprimaryQ,
      pathWeightRatio_selectorUnitWeight_eq_one_of_count_eq
        companion d⁻¹ p q hcompanion]
    simp [d]

/-- The two-selector `N = 3` correction, strengthened with residue
preservation.  Balance of the `beta` and `gamma` selectors on every surviving
essential contour makes the usual two-anchor correction invisible there,
while its two independently chosen weights normalize all three killed
interlacement-class pairs. -/
theorem exists_roiterThreeClassCorrection_invisibleOnSurviving
    (J : ZeroHomIdeal C)
    (c : contourScalarFunctionSubgroup (k := k)
      (rayPathContourRelation (C := C)))
    {i j : RayVertex C} (p q r : Quiver.Path i j)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (hqr : (rayPathContourRelation (C := C)).related q r)
    (beta gamma : ArrowSelector (RayVertex C))
    (hbetaP : selectedArrowCount beta p = 0)
    (hbetaQ : selectedArrowCount beta q = 1)
    (hbetaR : selectedArrowCount beta r = 0)
    (hgammaP : selectedArrowCount gamma p = 1)
    (hgammaQ : selectedArrowCount gamma q = 0)
    (hgammaR : selectedArrowCount gamma r = 0)
    (hbetaBalanced :
      J.ArrowSelectorBalancedOnSurvivingEssentialContours beta)
    (hgammaBalanced :
      J.ArrowSelectorBalancedOnSurvivingEssentialContours gamma) :
    ∃ e : ArrowUnitWeight k (RayVertex C),
      J.ArrowUnitWeightInvisibleOnSurvivingEssentialContours e ∧
        contourScalarFamily (rayPathContourRelation (C := C))
            (inverseCoboundaryCorrection
              (rayPathContourRelation (C := C)) c e)
            (relatedContour (rayPathContourRelation (C := C)) p q hpq) = 1 ∧
          contourScalarFamily (rayPathContourRelation (C := C))
            (inverseCoboundaryCorrection
              (rayPathContourRelation (C := C)) c e)
            (relatedContour (rayPathContourRelation (C := C)) p r
              ((rayPathContourRelation (C := C)).trans hpq hqr)) = 1 ∧
          contourScalarFamily (rayPathContourRelation (C := C))
            (inverseCoboundaryCorrection
              (rayPathContourRelation (C := C)) c e)
            (relatedContour (rayPathContourRelation (C := C)) q r hqr) = 1 := by
  let R := rayPathContourRelation (C := C)
  let dpr := contourScalarFamily R c
    (relatedContour R p r (R.trans hpq hqr))
  let dqr := contourScalarFamily R c (relatedContour R q r hqr)
  let e : ArrowUnitWeight k (RayVertex C) :=
    selectorUnitWeight beta dqr⁻¹ * selectorUnitWeight gamma dpr⁻¹
  refine ⟨e, ?_, ?_⟩
  · apply ArrowUnitWeightInvisibleOnSurvivingEssentialContours.mul J
    · exact J.arrowUnitWeightInvisibleOnSurvivingEssentialContours_selector
        beta dqr⁻¹ hbetaBalanced
    · exact J.arrowUnitWeightInvisibleOnSurvivingEssentialContours_selector
        gamma dpr⁻¹ hgammaBalanced
  · apply inverseCoboundaryCorrection_eq_one_on_relatedTriple
      R c e p q r hpq hqr
    · dsimp only [e]
      rw [pathWeightRatio_mul,
        pathWeightRatio_selectorUnitWeight_eq_one_of_count_eq
          beta dqr⁻¹ p r (hbetaP.trans hbetaR.symm),
        pathWeightRatio_selectorUnitWeight_inv_of_count_one_zero
          gamma dpr p r hgammaP hgammaR]
      simp [dpr]
    · dsimp only [e]
      rw [pathWeightRatio_mul,
        pathWeightRatio_selectorUnitWeight_inv_of_count_one_zero
          beta dqr q r hbetaQ hbetaR,
        pathWeightRatio_selectorUnitWeight_eq_one_of_count_eq
          gamma dpr⁻¹ q r (hgammaQ.trans hgammaR.symm)]
      simp [dqr]

/-- A correction invisible on surviving essential contours preserves
clinging to every surviving ray.  If the tested pair is already interlaced,
reflexive representatives prove clinging directly.  Otherwise the old
clinging representatives still form an essential contour on the same
surviving ray, so the correction is trivial on them. -/
theorem contourFunctionClingsToPath_mul_inv_coboundary_of_invisibleOnSurviving
    (J : ZeroHomIdeal C)
    (c : contourScalarFunctionSubgroup (k := k)
      (rayPathContourRelation (C := C)))
    (e : ArrowUnitWeight k (RayVertex C))
    (hinvisible :
      J.ArrowUnitWeightInvisibleOnSurvivingEssentialContours e)
    {a b : RayVertex C} (p : Quiver.Path a b)
    (hpNotMem : ¬J.mem (rayPathMap p))
    (hclings : ContourFunctionClingsToPath
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) c p) :
    ContourFunctionClingsToPath
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C)))
      (c * (contourFunctionCoboundaryHom (k := k)
        (rayPathContourRelation (C := C)) e)⁻¹) p := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  intro q hpq
  by_cases hpqI : PI.interlaced p q
  · have hpp : R.related p p := R.trans hpq (R.symm hpq)
    refine ⟨p, p, PI.refl p, hpp, PI.symm hpqI,
      R.symm hpq, hpp, ?_⟩
    exact contourScalarFunction_self R
      (c * (contourFunctionCoboundaryHom (k := k) R e)⁻¹) p hpp
  · obtain ⟨p', q', hppI, hppR, hqqI, hqqR, hpq'R, hpq'⟩ :=
      hclings q hpq
    have hp'q'Not : ¬PI.interlaced p' q' := by
      intro hp'q'I
      exact hpqI (PI.trans hppI (PI.trans hp'q'I (PI.symm hqqI)))
    have hp'NotMem : ¬J.mem (rayPathMap p') :=
      J.rayPathMap_right_not_mem_of_related hppR hpNotMem
    have hweight : pathWeightRatio e p' q' = 1 :=
      hinvisible p' q' hpq'R hp'NotMem hp'q'Not
    refine ⟨p', q', hppI, hppR, hqqI, hqqR, hpq'R, ?_⟩
    rw [contourScalarFamily_mul_inv_coboundary_apply, hpq']
    change 1 * (pathWeightRatio e p' q')⁻¹ = 1
    rw [hweight]
    simp

/-- The exact remaining local obligation after quotient induction at one
distinguished ray: for every contour function, find a correction which is
invisible on all surviving essential contours and makes the function cling
to the distinguished path.  The BGRS `N = 1,2,3` analysis is intended to
establish this predicate for the maximal path through an efficient tackle's
last arrow. -/
def HasInvisibleCorrectionClingingToPath
    (J : ZeroHomIdeal C) {a b : RayVertex C}
    (p : Quiver.Path a b) : Prop :=
  ∀ c : contourScalarFunctionSubgroup (k := k)
      (rayPathContourRelation (C := C)),
    ∃ e : ArrowUnitWeight k (RayVertex C),
      J.ArrowUnitWeightInvisibleOnSurvivingEssentialContours e ∧
        ContourFunctionClingsToPath
          (rayPathContourRelation (C := C))
          (properWhiskerInterlacementRelation
            (rayPathContourRelation (C := C)))
          (c * (contourFunctionCoboundaryHom (k := k)
            (rayPathContourRelation (C := C)) e)⁻¹) p

/-- The ray-level form of the local residue obligation: one invisible
correction makes the contour function cling to every path representing the
same nonzero ray as `p`.  This is the form needed to pass from a selected
maximal path to every nonzero path killed by its principal ideal. -/
def HasInvisibleCorrectionClingingOnRelatedPaths
    (J : ZeroHomIdeal C) {a b : RayVertex C}
    (p : Quiver.Path a b) : Prop :=
  ∀ c : contourScalarFunctionSubgroup (k := k)
      (rayPathContourRelation (C := C)),
    ∃ e : ArrowUnitWeight k (RayVertex C),
      J.ArrowUnitWeightInvisibleOnSurvivingEssentialContours e ∧
        ∀ (q : Quiver.Path a b),
          (rayPathContourRelation (C := C)).related p q →
            ContourFunctionClingsToPath
              (rayPathContourRelation (C := C))
              (properWhiskerInterlacementRelation
                (rayPathContourRelation (C := C)))
              (c * (contourFunctionCoboundaryHom (k := k)
                (rayPathContourRelation (C := C)) e)⁻¹) q

/-- Ray-level clinging specializes to the selected path itself. -/
theorem HasInvisibleCorrectionClingingOnRelatedPaths.toPath
    (J : ZeroHomIdeal C) {a b : RayVertex C}
    {p : Quiver.Path a b}
    (hlocal : J.HasInvisibleCorrectionClingingOnRelatedPaths (k := k) p)
    (hpp : (rayPathContourRelation (C := C)).related p p) :
    J.HasInvisibleCorrectionClingingToPath (k := k) p := by
  intro c
  obtain ⟨e, hinvisible, hclings⟩ := hlocal c
  exact ⟨e, hinvisible, hclings p hpp⟩

/-- The exact ray-level `N = 1` branch.  With only one interlacement class,
the identity arrow weight is invisible and the original contour function
already clings to every representative of the selected ray. -/
theorem hasInvisibleCorrectionClingingOnRelatedPaths_of_card_eq_one
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    (J : ZeroHomIdeal C)
    {i j : RayVertex C} (p : Quiver.Path i j)
    (hp : p.length ≠ 0)
    (hpp : (rayPathContourRelation (C := C)).related p p)
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 1) :
    J.HasInvisibleCorrectionClingingOnRelatedPaths (k := k) p := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  letI : Finite (OutgoingQuiverArrow i) := outgoingQuiverArrow_finite i
  letI : Finite (RelatedPathInterlacementClass PI p) :=
    relatedRayPathInterlacementClass_finite_of_initial
      p (rayPathMap_not_isIso_of_length_ne_zero p hp)
  intro c
  let e : ArrowUnitWeight k (RayVertex C) := 1
  refine ⟨e, ?_, ?_⟩
  · intro a b q r hqr hqNotMem hqrNot
    exact pathWeightRatio_one (k := k) q r
  · intro q hpq
    have hqLength : q.length ≠ 0 :=
      rayPath_length_ne_zero_of_related_of_not_isIso
        (rayPathMap_not_isIso_of_length_ne_zero p hp) hpq
    have hclings : ContourFunctionClingsToPath R PI c q :=
      contourFunctionClingsToPath_of_related_interlaced
        R PI c q (by
          intro r hqr
          have hpr : R.related p r := R.trans hpq hqr
          have hpqI : PI.interlaced p q :=
            rayPaths_interlaced_of_card_eq_one p hp hpp hcard q hpq
          have hprI : PI.interlaced p r :=
            rayPaths_interlaced_of_card_eq_one p hp hpp hcard r hpr
          exact PI.trans (PI.symm hpqI) hprI)
    have heq : contourFunctionCoboundaryHom (k := k) R e = 1 :=
      (contourFunctionCoboundaryHom (k := k) R).map_one
    change ContourFunctionClingsToPath R PI
      (c * (contourFunctionCoboundaryHom (k := k) R e)⁻¹) q
    rw [heq]
    simpa using hclings

/-- The residue-ready `N = 2` local correction.  Two balanced sparse
selectors normalize the contour between the two interlacement classes while
remaining invisible on every surviving essential contour; the normalization
then makes the corrected function cling to the selected killed ray. -/
theorem hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass
    (J : ZeroHomIdeal C)
    {i j : RayVertex C} (p q : Quiver.Path i j)
    (hpp : (rayPathContourRelation (C := C)).related p p)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (hpqNot : ¬(properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p q)
    [Finite (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p)]
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 2)
    (primary companion : ArrowSelector (RayVertex C))
    (hprimaryP : selectedArrowCount primary p = 1)
    (hprimaryQ : selectedArrowCount primary q = 0)
    (hcompanion : selectedArrowCount companion p =
      selectedArrowCount companion q)
    (hprimaryBalanced :
      J.ArrowSelectorBalancedOnSurvivingEssentialContours primary)
    (hcompanionBalanced :
      J.ArrowSelectorBalancedOnSurvivingEssentialContours companion) :
    J.HasInvisibleCorrectionClingingOnRelatedPaths (k := k) p := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  intro c
  obtain ⟨e, hinvisible, hone⟩ :=
    J.exists_roiterTwoClassPairedCorrection_invisibleOnSurviving
      c p q hpq primary companion hprimaryP hprimaryQ hcompanion
        hprimaryBalanced hcompanionBalanced
  refine ⟨e, hinvisible, ?_⟩
  exact contourFunctionClingsToRelatedPaths_of_card_eq_two_of_anchor_eq_one
    R PI (inverseCoboundaryCorrection R c e) p q hpp hpq hpqNot
      hcard hone

/-- The source-faithful jointly balanced `N = 2` correction, packaged at the
ray-level residue interface. -/
theorem hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass_of_pairBalanced
    (J : ZeroHomIdeal C)
    {i j : RayVertex C} (p q : Quiver.Path i j)
    (hpp : (rayPathContourRelation (C := C)).related p p)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (hpqNot : ¬(properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p q)
    [Finite (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p)]
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 2)
    (primary companion : ArrowSelector (RayVertex C))
    (hprimaryP : selectedArrowCount primary p = 1)
    (hprimaryQ : selectedArrowCount primary q = 0)
    (hcompanion : selectedArrowCount companion p =
      selectedArrowCount companion q)
    (hpairBalanced :
      J.ArrowSelectorPairBalancedOnSurvivingEssentialContours
        primary companion) :
    J.HasInvisibleCorrectionClingingOnRelatedPaths (k := k) p := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  intro c
  obtain ⟨e, hinvisible, hone⟩ :=
    J.exists_roiterTwoClassPairedCorrection_invisibleOnSurviving_of_pairBalanced
      c p q hpq primary companion hprimaryP hprimaryQ hcompanion
        hpairBalanced
  refine ⟨e, hinvisible, ?_⟩
  exact contourFunctionClingsToRelatedPaths_of_card_eq_two_of_anchor_eq_one
    R PI (inverseCoboundaryCorrection R c e) p q hpp hpq hpqNot
      hcard hone

/-- The source's easy `N = 2` branch: a single selected arrow normalizes the
killed anchor contour, and absence of that arrow from every surviving
essential contour makes the correction invisible there. -/
theorem hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass_of_singleArrowAbsent
    (J : ZeroHomIdeal C)
    {i j : RayVertex C} (p q : Quiver.Path i j)
    (hpp : (rayPathContourRelation (C := C)).related p p)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (hpqNot : ¬(properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p q)
    [Finite (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p)]
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 2)
    (selected : BundledQuiverArrow (RayVertex C))
    (hselectedP : selectedArrowCount (singleArrowSelector selected) p = 1)
    (hselectedQ : selectedArrowCount (singleArrowSelector selected) q = 0)
    (habsent : J.BundledArrowAbsentFromSurvivingEssentialContours selected) :
    J.HasInvisibleCorrectionClingingOnRelatedPaths (k := k) p := by
  apply J.hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass
    p q hpp hpq hpqNot hcard
    (singleArrowSelector selected) (emptyArrowSelector (C := C))
    hselectedP hselectedQ
  · simp
  · exact J.arrowSelectorBalancedOnSurvivingEssentialContours_single_of_absent
      selected habsent
  · exact J.arrowSelectorBalancedOnSurvivingEssentialContours_empty

/-- The orientation-reversed easy `N = 2` branch: if the selected arrow occurs
zero times on the anchor path and once on the other class representative, its
direct contour-scalar weight normalizes the anchor. -/
theorem hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass_of_singleArrowAbsent_zero_one
    (J : ZeroHomIdeal C)
    {i j : RayVertex C} (p q : Quiver.Path i j)
    (hpp : (rayPathContourRelation (C := C)).related p p)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (hpqNot : ¬(properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p q)
    [Finite (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p)]
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 2)
    (selected : BundledQuiverArrow (RayVertex C))
    (hselectedP : selectedArrowCount
      (singleArrowSelector selected) p = 0)
    (hselectedQ : selectedArrowCount
      (singleArrowSelector selected) q = 1)
    (habsent : J.BundledArrowAbsentFromSurvivingEssentialContours selected) :
    J.HasInvisibleCorrectionClingingOnRelatedPaths (k := k) p := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  intro c
  let d := contourScalarFamily R c (relatedContour R p q hpq)
  let e : ArrowUnitWeight k (RayVertex C) :=
    selectorUnitWeight (singleArrowSelector selected) d
  refine ⟨e, ?_, ?_⟩
  · exact J.arrowUnitWeightInvisibleOnSurvivingEssentialContours_selector
      (singleArrowSelector selected) d
      (J.arrowSelectorBalancedOnSurvivingEssentialContours_single_of_absent
        selected habsent)
  · have hone : contourScalarFamily R
        (inverseCoboundaryCorrection R c e)
        (relatedContour R p q hpq) = 1 := by
      apply contourScalarFamily_mul_inv_coboundary_eq_one_of_ratio
      change pathWeightRatio e p q =
        contourScalarFamily R c (relatedContour R p q hpq)
      simp [e, pathWeightRatio, path_weight_selectorUnitWeight,
        hselectedP, hselectedQ, d]
    exact contourFunctionClingsToRelatedPaths_of_card_eq_two_of_anchor_eq_one
      R PI (inverseCoboundaryCorrection R c e) p q hpp hpq hpqNot
        hcard hone

/-- Final-arrow packaging of the orientation-reversed easy `N = 2` branch:
the selected final arrow of `q` has counts zero and one on `p` and `q`. -/
theorem hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass_finalArrow_of_absent_zero_one
    (J : ZeroHomIdeal C)
    {i j : RayVertex C} (p q : Quiver.Path i j)
    (hpp : (rayPathContourRelation (C := C)).related p p)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (hpqNot : ¬(properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p q)
    [Finite (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p)]
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 2)
    (dp : PathFinalDecomposition p) (dq : PathFinalDecomposition q)
    (harrow : bundledQuiverArrow dq.arrow ≠
      bundledQuiverArrow dp.arrow)
    (hsuffix : EssentialContourArrowSuffixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C)))
      (bundledQuiverArrow dq.arrow))
    (habsent : J.BundledArrowAbsentFromSurvivingEssentialContours
      (bundledQuiverArrow dq.arrow)) :
    J.HasInvisibleCorrectionClingingOnRelatedPaths (k := k) p := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  have hessential : IsEssentialPathContour R PI p q := ⟨hpq, hpqNot⟩
  apply J.hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass_of_singleArrowAbsent_zero_one
    p q hpp hpq hpqNot hcard (bundledQuiverArrow dq.arrow)
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dq.arrow)) p =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dq.arrow))
            (dp.head.comp dp.arrow.toPath) := congrArg _ dp.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_final_eq_zero_of_ne
        dq.arrow dp.head dp.arrow harrow.symm (by
          apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
            R PI (bundledQuiverArrow dq.arrow) dp.head dp.arrow q
          · simpa only [dp.path_eq] using hessential
          · exact hsuffix)
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dq.arrow)) q =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dq.arrow))
            (dq.head.comp dq.arrow.toPath) := congrArg _ dq.path_eq
      _ = 1 := selectedArrowCount_singleArrowSelector_final_eq_one
        dq.head dq.arrow (by
          apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
            R PI (bundledQuiverArrow dq.arrow) dq.head dq.arrow p
          · simpa only [dq.path_eq] using hessential.symm
          · exact hsuffix)
  · exact habsent

/-- Final-arrow form of the easy `N = 2` branch.  Suffix triviality gives the
anchor occurrence counts, while absence of the selected final arrow from the
surviving essential contours gives residue invisibility. -/
theorem hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass_finalArrow_of_absent
    (J : ZeroHomIdeal C)
    {i j : RayVertex C} (p q : Quiver.Path i j)
    (hpp : (rayPathContourRelation (C := C)).related p p)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (hpqNot : ¬(properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p q)
    [Finite (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p)]
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 2)
    (dp : PathFinalDecomposition p) (dq : PathFinalDecomposition q)
    (harrow : bundledQuiverArrow dq.arrow ≠ bundledQuiverArrow dp.arrow)
    (hsuffix : EssentialContourArrowSuffixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C)))
      (bundledQuiverArrow dp.arrow))
    (habsent : J.BundledArrowAbsentFromSurvivingEssentialContours
      (bundledQuiverArrow dp.arrow)) :
    J.HasInvisibleCorrectionClingingOnRelatedPaths (k := k) p := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  have hessential : IsEssentialPathContour R PI p q := ⟨hpq, hpqNot⟩
  apply J.hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass_of_singleArrowAbsent
    p q hpp hpq hpqNot hcard (bundledQuiverArrow dp.arrow)
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow)) p =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow))
            (dp.head.comp dp.arrow.toPath) := congrArg _ dp.path_eq
      _ = 1 := selectedArrowCount_singleArrowSelector_final_eq_one
        dp.head dp.arrow (by
          apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
            R PI (bundledQuiverArrow dp.arrow) dp.head dp.arrow q
          · simpa only [dp.path_eq] using hessential
          · exact hsuffix)
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow)) q =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow))
            (dq.head.comp dq.arrow.toPath) := congrArg _ dq.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_final_eq_zero_of_ne
        dp.arrow dq.head dq.arrow harrow (by
          apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
            R PI (bundledQuiverArrow dp.arrow) dq.head dq.arrow p
          · simpa only [dq.path_eq] using hessential.symm
          · exact hsuffix)
  · exact habsent

/-- Initial-arrow dual of the easy `N = 2` branch. -/
theorem hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass_initialArrow_of_absent
    (J : ZeroHomIdeal C)
    {i j : RayVertex C} (p q : Quiver.Path i j)
    (hpp : (rayPathContourRelation (C := C)).related p p)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (hpqNot : ¬(properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p q)
    [Finite (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p)]
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 2)
    (dp : PathInitialDecomposition p) (dq : PathInitialDecomposition q)
    (harrow : bundledQuiverArrow dq.arrow ≠ bundledQuiverArrow dp.arrow)
    (hprefix : EssentialContourArrowPrefixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C)))
      (bundledQuiverArrow dp.arrow))
    (habsent : J.BundledArrowAbsentFromSurvivingEssentialContours
      (bundledQuiverArrow dp.arrow)) :
    J.HasInvisibleCorrectionClingingOnRelatedPaths (k := k) p := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  have hessential : IsEssentialPathContour R PI p q := ⟨hpq, hpqNot⟩
  apply J.hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass_of_singleArrowAbsent
    p q hpp hpq hpqNot hcard (bundledQuiverArrow dp.arrow)
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow)) p =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow))
            (dp.arrow.toPath.comp dp.tail) := congrArg _ dp.path_eq
      _ = 1 := selectedArrowCount_singleArrowSelector_initial_eq_one
        dp.arrow dp.tail (by
          apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
            R PI (bundledQuiverArrow dp.arrow) dp.arrow dp.tail q
          · simpa only [dp.path_eq] using hessential
          · exact hprefix)
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow)) q =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow))
            (dq.arrow.toPath.comp dq.tail) := congrArg _ dq.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_initial_eq_zero_of_ne
        dp.arrow dq.arrow dq.tail harrow (by
          apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
            R PI (bundledQuiverArrow dp.arrow) dq.arrow dq.tail p
          · simpa only [dq.path_eq] using hessential.symm
          · exact hprefix)
  · exact habsent

/-- Initial-arrow packaging of the orientation-reversed easy `N = 2` branch:
the selected initial arrow of `q` has counts zero and one on `p` and `q`. -/
theorem hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass_initialArrow_of_absent_zero_one
    (J : ZeroHomIdeal C)
    {i j : RayVertex C} (p q : Quiver.Path i j)
    (hpp : (rayPathContourRelation (C := C)).related p p)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (hpqNot : ¬(properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p q)
    [Finite (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p)]
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 2)
    (dp : PathInitialDecomposition p) (dq : PathInitialDecomposition q)
    (harrow : bundledQuiverArrow dq.arrow ≠
      bundledQuiverArrow dp.arrow)
    (hprefix : EssentialContourArrowPrefixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C)))
      (bundledQuiverArrow dq.arrow))
    (habsent : J.BundledArrowAbsentFromSurvivingEssentialContours
      (bundledQuiverArrow dq.arrow)) :
    J.HasInvisibleCorrectionClingingOnRelatedPaths (k := k) p := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  have hessential : IsEssentialPathContour R PI p q := ⟨hpq, hpqNot⟩
  apply J.hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass_of_singleArrowAbsent_zero_one
    p q hpp hpq hpqNot hcard (bundledQuiverArrow dq.arrow)
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dq.arrow)) p =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dq.arrow))
            (dp.arrow.toPath.comp dp.tail) := congrArg _ dp.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_initial_eq_zero_of_ne
        dq.arrow dp.arrow dp.tail harrow.symm (by
          apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
            R PI (bundledQuiverArrow dq.arrow) dp.arrow dp.tail q
          · simpa only [dp.path_eq] using hessential
          · exact hprefix)
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dq.arrow)) q =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dq.arrow))
            (dq.arrow.toPath.comp dq.tail) := congrArg _ dq.path_eq
      _ = 1 := selectedArrowCount_singleArrowSelector_initial_eq_one
        dq.arrow dq.tail (by
          apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
            R PI (bundledQuiverArrow dq.arrow) dq.arrow dq.tail p
          · simpa only [dq.path_eq] using hessential.symm
          · exact hprefix)
  · exact habsent

/-- The selected-path specialization of the residue-ready `N = 2` local
correction. -/
theorem hasInvisibleCorrectionClingingToPath_of_roiterTwoClass
    (J : ZeroHomIdeal C)
    {i j : RayVertex C} (p q : Quiver.Path i j)
    (hpp : (rayPathContourRelation (C := C)).related p p)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (hpqNot : ¬(properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p q)
    [Finite (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p)]
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 2)
    (primary companion : ArrowSelector (RayVertex C))
    (hprimaryP : selectedArrowCount primary p = 1)
    (hprimaryQ : selectedArrowCount primary q = 0)
    (hcompanion : selectedArrowCount companion p =
      selectedArrowCount companion q)
    (hprimaryBalanced :
      J.ArrowSelectorBalancedOnSurvivingEssentialContours primary)
    (hcompanionBalanced :
      J.ArrowSelectorBalancedOnSurvivingEssentialContours companion) :
    J.HasInvisibleCorrectionClingingToPath (k := k) p := by
  apply HasInvisibleCorrectionClingingOnRelatedPaths.toPath J
    (J.hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass
      p q hpp hpq hpqNot hcard primary companion hprimaryP hprimaryQ
        hcompanion hprimaryBalanced hcompanionBalanced)
  exact hpp

/-- The residue-ready `N = 3` local correction.  The two balanced selectors
normalize all three contours between the three interlacement classes while
remaining invisible on survivors, hence the corrected function clings to the
selected killed ray. -/
theorem hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterThreeClass
    (J : ZeroHomIdeal C)
    {i j : RayVertex C} (p q r : Quiver.Path i j)
    (hpp : (rayPathContourRelation (C := C)).related p p)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (hqr : (rayPathContourRelation (C := C)).related q r)
    (hpqNot : ¬(properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p q)
    (hprNot : ¬(properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p r)
    (hqrNot : ¬(properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced q r)
    [Finite (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p)]
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 3)
    (beta gamma : ArrowSelector (RayVertex C))
    (hbetaP : selectedArrowCount beta p = 0)
    (hbetaQ : selectedArrowCount beta q = 1)
    (hbetaR : selectedArrowCount beta r = 0)
    (hgammaP : selectedArrowCount gamma p = 1)
    (hgammaQ : selectedArrowCount gamma q = 0)
    (hgammaR : selectedArrowCount gamma r = 0)
    (hbetaBalanced :
      J.ArrowSelectorBalancedOnSurvivingEssentialContours beta)
    (hgammaBalanced :
      J.ArrowSelectorBalancedOnSurvivingEssentialContours gamma) :
    J.HasInvisibleCorrectionClingingOnRelatedPaths (k := k) p := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  intro c
  obtain ⟨e, hinvisible, honePQ, honePR, honeQR⟩ :=
    J.exists_roiterThreeClassCorrection_invisibleOnSurviving
      c p q r hpq hqr beta gamma hbetaP hbetaQ hbetaR
        hgammaP hgammaQ hgammaR hbetaBalanced hgammaBalanced
  refine ⟨e, hinvisible, ?_⟩
  exact
    contourFunctionClingsToRelatedPaths_of_card_eq_three_of_anchors_eq_one
      R PI (inverseCoboundaryCorrection R c e) p q r hpp hpq hqr
        hpqNot hprNot hqrNot hcard honePQ honePR honeQR

/-- Final-arrow packaging of the residue-ready `N = 3` correction under
separate balance of the two selected singleton selectors. -/
theorem hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterThreeClass_finalArrow_of_balanced
    (J : ZeroHomIdeal C)
    {i j : RayVertex C} (p q r : Quiver.Path i j)
    (hpq : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (hqr : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) q r)
    (hpr : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p r)
    [Finite (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p)]
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 3)
    (dp : PathFinalDecomposition p) (dq : PathFinalDecomposition q)
    (dr : PathFinalDecomposition r)
    (hpqArrow : bundledQuiverArrow dp.arrow ≠ bundledQuiverArrow dq.arrow)
    (hprArrow : bundledQuiverArrow dp.arrow ≠ bundledQuiverArrow dr.arrow)
    (hqrArrow : bundledQuiverArrow dq.arrow ≠ bundledQuiverArrow dr.arrow)
    (hbetaSuffix : EssentialContourArrowSuffixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation (rayPathContourRelation (C := C)))
      (bundledQuiverArrow dq.arrow))
    (hgammaSuffix : EssentialContourArrowSuffixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation (rayPathContourRelation (C := C)))
      (bundledQuiverArrow dp.arrow))
    (hbetaBalanced : J.ArrowSelectorBalancedOnSurvivingEssentialContours
      (singleArrowSelector (bundledQuiverArrow dq.arrow)))
    (hgammaBalanced : J.ArrowSelectorBalancedOnSurvivingEssentialContours
      (singleArrowSelector (bundledQuiverArrow dp.arrow))) :
    J.HasInvisibleCorrectionClingingOnRelatedPaths (k := k) p := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  have hpp : R.related p p := R.trans hpq.1 (R.symm hpq.1)
  apply J.hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterThreeClass
    p q r hpp hpq.1 hqr.1 hpq.2 hpr.2 hqr.2 hcard
    (singleArrowSelector (bundledQuiverArrow dq.arrow))
    (singleArrowSelector (bundledQuiverArrow dp.arrow))
  · calc
      selectedArrowCount (singleArrowSelector (bundledQuiverArrow dq.arrow)) p =
        selectedArrowCount (singleArrowSelector (bundledQuiverArrow dq.arrow))
          (dp.head.comp dp.arrow.toPath) := congrArg _ dp.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_final_eq_zero_of_ne
        dq.arrow dp.head dp.arrow hpqArrow (by
          apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
            R PI (bundledQuiverArrow dq.arrow) dp.head dp.arrow q
          · simpa only [dp.path_eq] using hpq
          · exact hbetaSuffix)
  · calc
      selectedArrowCount (singleArrowSelector (bundledQuiverArrow dq.arrow)) q =
        selectedArrowCount (singleArrowSelector (bundledQuiverArrow dq.arrow))
          (dq.head.comp dq.arrow.toPath) := congrArg _ dq.path_eq
      _ = 1 := selectedArrowCount_singleArrowSelector_final_eq_one
        dq.head dq.arrow (by
          apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
            R PI (bundledQuiverArrow dq.arrow) dq.head dq.arrow p
          · simpa only [dq.path_eq] using hpq.symm
          · exact hbetaSuffix)
  · calc
      selectedArrowCount (singleArrowSelector (bundledQuiverArrow dq.arrow)) r =
        selectedArrowCount (singleArrowSelector (bundledQuiverArrow dq.arrow))
          (dr.head.comp dr.arrow.toPath) := congrArg _ dr.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_final_eq_zero_of_ne
        dq.arrow dr.head dr.arrow hqrArrow.symm (by
          apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
            R PI (bundledQuiverArrow dq.arrow) dr.head dr.arrow q
          · simpa only [dr.path_eq] using hqr.symm
          · exact hbetaSuffix)
  · calc
      selectedArrowCount (singleArrowSelector (bundledQuiverArrow dp.arrow)) p =
        selectedArrowCount (singleArrowSelector (bundledQuiverArrow dp.arrow))
          (dp.head.comp dp.arrow.toPath) := congrArg _ dp.path_eq
      _ = 1 := selectedArrowCount_singleArrowSelector_final_eq_one
        dp.head dp.arrow (by
          apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
            R PI (bundledQuiverArrow dp.arrow) dp.head dp.arrow q
          · simpa only [dp.path_eq] using hpq
          · exact hgammaSuffix)
  · calc
      selectedArrowCount (singleArrowSelector (bundledQuiverArrow dp.arrow)) q =
        selectedArrowCount (singleArrowSelector (bundledQuiverArrow dp.arrow))
          (dq.head.comp dq.arrow.toPath) := congrArg _ dq.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_final_eq_zero_of_ne
        dp.arrow dq.head dq.arrow hpqArrow.symm (by
          apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
            R PI (bundledQuiverArrow dp.arrow) dq.head dq.arrow p
          · simpa only [dq.path_eq] using hpq.symm
          · exact hgammaSuffix)
  · calc
      selectedArrowCount (singleArrowSelector (bundledQuiverArrow dp.arrow)) r =
        selectedArrowCount (singleArrowSelector (bundledQuiverArrow dp.arrow))
          (dr.head.comp dr.arrow.toPath) := congrArg _ dr.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_final_eq_zero_of_ne
        dp.arrow dr.head dr.arrow hprArrow.symm (by
          apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
            R PI (bundledQuiverArrow dp.arrow) dr.head dr.arrow p
          · simpa only [dr.path_eq] using hpr.symm
          · exact hgammaSuffix)
  · exact hbetaBalanced
  · exact hgammaBalanced

/-- Initial-arrow packaging of the residue-ready `N = 3` correction under
separate balance of the two selected singleton selectors. -/
theorem hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterThreeClass_initialArrow_of_balanced
    (J : ZeroHomIdeal C)
    {i j : RayVertex C} (p q r : Quiver.Path i j)
    (hpq : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (hqr : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) q r)
    (hpr : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p r)
    [Finite (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p)]
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 3)
    (dp : PathInitialDecomposition p) (dq : PathInitialDecomposition q)
    (dr : PathInitialDecomposition r)
    (hpqArrow : bundledQuiverArrow dp.arrow ≠ bundledQuiverArrow dq.arrow)
    (hprArrow : bundledQuiverArrow dp.arrow ≠ bundledQuiverArrow dr.arrow)
    (hqrArrow : bundledQuiverArrow dq.arrow ≠ bundledQuiverArrow dr.arrow)
    (hbetaPrefix : EssentialContourArrowPrefixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation (rayPathContourRelation (C := C)))
      (bundledQuiverArrow dq.arrow))
    (hgammaPrefix : EssentialContourArrowPrefixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation (rayPathContourRelation (C := C)))
      (bundledQuiverArrow dp.arrow))
    (hbetaBalanced : J.ArrowSelectorBalancedOnSurvivingEssentialContours
      (singleArrowSelector (bundledQuiverArrow dq.arrow)))
    (hgammaBalanced : J.ArrowSelectorBalancedOnSurvivingEssentialContours
      (singleArrowSelector (bundledQuiverArrow dp.arrow))) :
    J.HasInvisibleCorrectionClingingOnRelatedPaths (k := k) p := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  have hpp : R.related p p := R.trans hpq.1 (R.symm hpq.1)
  apply J.hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterThreeClass
    p q r hpp hpq.1 hqr.1 hpq.2 hpr.2 hqr.2 hcard
    (singleArrowSelector (bundledQuiverArrow dq.arrow))
    (singleArrowSelector (bundledQuiverArrow dp.arrow))
  · calc
      selectedArrowCount (singleArrowSelector (bundledQuiverArrow dq.arrow)) p =
        selectedArrowCount (singleArrowSelector (bundledQuiverArrow dq.arrow))
          (dp.arrow.toPath.comp dp.tail) := congrArg _ dp.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_initial_eq_zero_of_ne
        dq.arrow dp.arrow dp.tail hpqArrow (by
          apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
            R PI (bundledQuiverArrow dq.arrow) dp.arrow dp.tail q
          · simpa only [dp.path_eq] using hpq
          · exact hbetaPrefix)
  · calc
      selectedArrowCount (singleArrowSelector (bundledQuiverArrow dq.arrow)) q =
        selectedArrowCount (singleArrowSelector (bundledQuiverArrow dq.arrow))
          (dq.arrow.toPath.comp dq.tail) := congrArg _ dq.path_eq
      _ = 1 := selectedArrowCount_singleArrowSelector_initial_eq_one
        dq.arrow dq.tail (by
          apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
            R PI (bundledQuiverArrow dq.arrow) dq.arrow dq.tail p
          · simpa only [dq.path_eq] using hpq.symm
          · exact hbetaPrefix)
  · calc
      selectedArrowCount (singleArrowSelector (bundledQuiverArrow dq.arrow)) r =
        selectedArrowCount (singleArrowSelector (bundledQuiverArrow dq.arrow))
          (dr.arrow.toPath.comp dr.tail) := congrArg _ dr.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_initial_eq_zero_of_ne
        dq.arrow dr.arrow dr.tail hqrArrow.symm (by
          apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
            R PI (bundledQuiverArrow dq.arrow) dr.arrow dr.tail q
          · simpa only [dr.path_eq] using hqr.symm
          · exact hbetaPrefix)
  · calc
      selectedArrowCount (singleArrowSelector (bundledQuiverArrow dp.arrow)) p =
        selectedArrowCount (singleArrowSelector (bundledQuiverArrow dp.arrow))
          (dp.arrow.toPath.comp dp.tail) := congrArg _ dp.path_eq
      _ = 1 := selectedArrowCount_singleArrowSelector_initial_eq_one
        dp.arrow dp.tail (by
          apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
            R PI (bundledQuiverArrow dp.arrow) dp.arrow dp.tail q
          · simpa only [dp.path_eq] using hpq
          · exact hgammaPrefix)
  · calc
      selectedArrowCount (singleArrowSelector (bundledQuiverArrow dp.arrow)) q =
        selectedArrowCount (singleArrowSelector (bundledQuiverArrow dp.arrow))
          (dq.arrow.toPath.comp dq.tail) := congrArg _ dq.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_initial_eq_zero_of_ne
        dp.arrow dq.arrow dq.tail hpqArrow.symm (by
          apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
            R PI (bundledQuiverArrow dp.arrow) dq.arrow dq.tail p
          · simpa only [dq.path_eq] using hpq.symm
          · exact hgammaPrefix)
  · calc
      selectedArrowCount (singleArrowSelector (bundledQuiverArrow dp.arrow)) r =
        selectedArrowCount (singleArrowSelector (bundledQuiverArrow dp.arrow))
          (dr.arrow.toPath.comp dr.tail) := congrArg _ dr.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_initial_eq_zero_of_ne
        dp.arrow dr.arrow dr.tail hprArrow.symm (by
          apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
            R PI (bundledQuiverArrow dp.arrow) dr.arrow dr.tail p
          · simpa only [dr.path_eq] using hpr.symm
          · exact hgammaPrefix)
  · exact hbetaBalanced
  · exact hgammaBalanced

/-- The selected-path specialization of the residue-ready `N = 3` local
correction. -/
theorem hasInvisibleCorrectionClingingToPath_of_roiterThreeClass
    (J : ZeroHomIdeal C)
    {i j : RayVertex C} (p q r : Quiver.Path i j)
    (hpp : (rayPathContourRelation (C := C)).related p p)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (hqr : (rayPathContourRelation (C := C)).related q r)
    (hpqNot : ¬(properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p q)
    (hprNot : ¬(properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p r)
    (hqrNot : ¬(properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced q r)
    [Finite (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p)]
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 3)
    (beta gamma : ArrowSelector (RayVertex C))
    (hbetaP : selectedArrowCount beta p = 0)
    (hbetaQ : selectedArrowCount beta q = 1)
    (hbetaR : selectedArrowCount beta r = 0)
    (hgammaP : selectedArrowCount gamma p = 1)
    (hgammaQ : selectedArrowCount gamma q = 0)
    (hgammaR : selectedArrowCount gamma r = 0)
    (hbetaBalanced :
      J.ArrowSelectorBalancedOnSurvivingEssentialContours beta)
    (hgammaBalanced :
      J.ArrowSelectorBalancedOnSurvivingEssentialContours gamma) :
    J.HasInvisibleCorrectionClingingToPath (k := k) p := by
  apply HasInvisibleCorrectionClingingOnRelatedPaths.toPath J
    (J.hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterThreeClass
      p q r hpp hpq hqr hpqNot hprNot hqrNot hcard beta gamma
        hbetaP hbetaQ hbetaR hgammaP hgammaQ hgammaR
        hbetaBalanced hgammaBalanced)
  exact hpp

/-- One complete residue-induction step.  Exactness of the restricted
quotient contour function first supplies a lifted correction which makes the
original function cling to every surviving ray.  A local invisible correction
then adds the distinguished killed ray without disturbing any survivor.  The
two successive corrections are combined into one arrow-weight family. -/
theorem exists_combinedCorrection_clings_survivors_and_path_of_isExact_quotOut
    (J : ZeroHomIdeal C) (hJ : J.IsProper)
    (c : contourScalarFunctionSubgroup (k := k)
      (rayPathContourRelation (C := C)))
    {a b : RayVertex C} (p : Quiver.Path a b)
    (hlocal : J.HasInvisibleCorrectionClingingToPath (k := k) p)
    (hexact : IsExactContourFunction
      (rayPathContourRelation (C := CategoryTheory.Quotient J.rel))
      (J.quotOutContourScalarFunction hJ c)) :
    ∃ e : ArrowUnitWeight k (RayVertex C),
      (∀ {i j : RayVertex C} (q : Quiver.Path i j),
        ¬J.mem (rayPathMap q) →
          ContourFunctionClingsToPath
            (rayPathContourRelation (C := C))
            (properWhiskerInterlacementRelation
              (rayPathContourRelation (C := C)))
            (c * (contourFunctionCoboundaryHom (k := k)
              (rayPathContourRelation (C := C)) e)⁻¹) q) ∧
        ContourFunctionClingsToPath
          (rayPathContourRelation (C := C))
          (properWhiskerInterlacementRelation
            (rayPathContourRelation (C := C)))
          (c * (contourFunctionCoboundaryHom (k := k)
            (rayPathContourRelation (C := C)) e)⁻¹) p := by
  let R := rayPathContourRelation (C := C)
  obtain ⟨e₀, hsurvive⟩ :=
    J.exists_liftQuotientArrowUnitWeight_clingsToPath_of_isExact_quotOut
      hJ c hexact
  obtain ⟨e₁, hinvisible, hpath⟩ := hlocal
    (c * (contourFunctionCoboundaryHom (k := k) R e₀)⁻¹)
  let e : ArrowUnitWeight k (RayVertex C) := e₀ * e₁
  have hcombine :
      c * (contourFunctionCoboundaryHom (k := k) R e)⁻¹ =
        (c * (contourFunctionCoboundaryHom (k := k) R e₀)⁻¹) *
          (contourFunctionCoboundaryHom (k := k) R e₁)⁻¹ := by
    change c * (contourFunctionCoboundaryHom (k := k) R (e₀ * e₁))⁻¹ =
      (c * (contourFunctionCoboundaryHom (k := k) R e₀)⁻¹) *
        (contourFunctionCoboundaryHom (k := k) R e₁)⁻¹
    have hmap :
        contourFunctionCoboundaryHom (k := k) R (e₀ * e₁) =
          contourFunctionCoboundaryHom (k := k) R e₀ *
            contourFunctionCoboundaryHom (k := k) R e₁ :=
      (contourFunctionCoboundaryHom (k := k) R).map_mul e₀ e₁
    rw [hmap, mul_inv_rev]
    ac_rfl
  refine ⟨e, ?_, ?_⟩
  · intro i j q hqNotMem
    rw [hcombine]
    exact J.contourFunctionClingsToPath_mul_inv_coboundary_of_invisibleOnSurviving
      (c * (contourFunctionCoboundaryHom (k := k) R e₀)⁻¹)
      e₁ hinvisible q hqNotMem (hsurvive q hqNotMem)
  · rw [hcombine]
    exact hpath

/-- The ideal-level local correction obligation.  Besides being invisible on
all surviving essential contours, the correction makes the contour function
cling to every nonzero path annihilated by the ideal.  For the principal
ideal of a maximal ray, the annihilated nonzero paths all represent exactly
that one ray. -/
def HasInvisibleCorrectionClingingOnIdeal
    (J : ZeroHomIdeal C) : Prop :=
  ∀ c : contourScalarFunctionSubgroup (k := k)
      (rayPathContourRelation (C := C)),
    ∃ e : ArrowUnitWeight k (RayVertex C),
      J.ArrowUnitWeightInvisibleOnSurvivingEssentialContours e ∧
        ∀ {a b : RayVertex C} (p : Quiver.Path a b),
          J.mem (rayPathMap p) → rayPathMap p ≠ 0 →
            ContourFunctionClingsToPath
              (rayPathContourRelation (C := C))
              (properWhiskerInterlacementRelation
                (rayPathContourRelation (C := C)))
              (c * (contourFunctionCoboundaryHom (k := k)
                (rayPathContourRelation (C := C)) e)⁻¹) p

/-- For a maximal path, ray-level clinging is exactly enough for the
ideal-level residue obligation.  Every nonzero path in the maximal path's
principal ideal has the same global endpoints and evaluation as the selected
path, hence is one of its related representatives. -/
theorem hasInvisibleCorrectionClingingOnIdeal_principal_of_maximal
    [Finite C] [IsFiniteRayCategory C]
    {a : BundledQuiverArrow (RayVertex C)}
    (p : NonzeroRayPathThroughArrow (C := C) a) (hp : p.IsMaximal)
    (hlocal : HasInvisibleCorrectionClingingOnRelatedPaths (k := k)
      (principalZeroHomIdeal (rayPathMap p.path)) p.path) :
    HasInvisibleCorrectionClingingOnIdeal (k := k)
      (principalZeroHomIdeal (rayPathMap p.path)) := by
  let J := principalZeroHomIdeal (rayPathMap p.path)
  intro c
  obtain ⟨e, hinvisible, hclings⟩ := hlocal c
  refine ⟨e, hinvisible, ?_⟩
  intro i j q hqMem hqNonzero
  let f : NonzeroHom j.obj i.obj := ⟨rayPathMap q, hqNonzero⟩
  have hglobal :
      f.toNonzeroCategoryMorphism = p.toNonzeroCategoryMorphism :=
    (hp.principalZeroHomIdeal_mem_iff_eq p f).1 hqMem
  have hdata := (NonzeroCategoryMorphism.ext_iff).1 hglobal
  dsimp [NonzeroHom.toNonzeroCategoryMorphism,
    NonzeroRayPathThroughArrow.toNonzeroCategoryMorphism, f] at hdata
  have hj : j = p.target := RayVertex.ext hdata.1
  have hi : i = p.source := RayVertex.ext hdata.2.1
  subst j
  subst i
  have hmap : rayPathMap q = rayPathMap p.path :=
    eq_of_heq hdata.2.2
  apply hclings q
  exact ⟨p.map_ne_zero, hmap.symm⟩

/-- The exact principal-ideal `N = 1` branch for a maximal ray. -/
theorem hasInvisibleCorrectionClingingOnIdeal_principal_of_maximal_of_card_eq_one
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    {a : BundledQuiverArrow (RayVertex C)}
    (p : NonzeroRayPathThroughArrow (C := C) a) (hp : p.IsMaximal)
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p.path) = 1) :
    ZeroHomIdeal.HasInvisibleCorrectionClingingOnIdeal (k := k)
      (principalZeroHomIdeal (rayPathMap p.path)) := by
  apply hasInvisibleCorrectionClingingOnIdeal_principal_of_maximal p hp
  exact hasInvisibleCorrectionClingingOnRelatedPaths_of_card_eq_one
    (principalZeroHomIdeal (rayPathMap p.path)) p.path
      p.length_ne_zero ⟨p.map_ne_zero, rfl⟩ hcard

/-- Assemble the maximal-ray local correction from the two genuinely
nontrivial cardinal cases; the `N = 1` case is discharged internally. -/
theorem hasInvisibleCorrectionClingingOnIdeal_principal_of_maximal_of_card_two_three
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [HasRayLongPathEndpointValencyAtMostThree C]
    {a : BundledQuiverArrow (RayVertex C)}
    (p : NonzeroRayPathThroughArrow (C := C) a) (hp : p.IsMaximal)
    (hTwo : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p.path) = 2 →
      ZeroHomIdeal.HasInvisibleCorrectionClingingOnIdeal (k := k)
        (principalZeroHomIdeal (rayPathMap p.path)))
    (hThree : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p.path) = 3 →
      ZeroHomIdeal.HasInvisibleCorrectionClingingOnIdeal (k := k)
        (principalZeroHomIdeal (rayPathMap p.path))) :
    ZeroHomIdeal.HasInvisibleCorrectionClingingOnIdeal (k := k)
      (principalZeroHomIdeal (rayPathMap p.path)) := by
  rcases relatedRayPathInterlacementClass_card_eq_one_or_two_or_three
      p.path p.length_ne_zero ⟨p.map_ne_zero, rfl⟩ with hOne | hTwo' | hThree'
  · exact hasInvisibleCorrectionClingingOnIdeal_principal_of_maximal_of_card_eq_one
      p hp hOne
  · exact hTwo hTwo'
  · exact hThree hThree'

/-- The ideal-level `N = 1` branch.  If every nonzero ray annihilated by the
ideal has only one interlacement class, the constant-one arrow correction is
invisible on survivors and the original contour function already clings on
all annihilated rays. -/
theorem hasInvisibleCorrectionClingingOnIdeal_of_killed_related_interlaced
    (J : ZeroHomIdeal C)
    (hone : ∀ {a b : RayVertex C} (p : Quiver.Path a b),
      J.mem (rayPathMap p) → rayPathMap p ≠ 0 →
        ∀ (q : Quiver.Path a b),
          (rayPathContourRelation (C := C)).related p q →
            (properWhiskerInterlacementRelation
              (rayPathContourRelation (C := C))).interlaced p q) :
    J.HasInvisibleCorrectionClingingOnIdeal (k := k) := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  intro c
  let e : ArrowUnitWeight k (RayVertex C) := 1
  refine ⟨e, ?_, ?_⟩
  · intro a b p q hpq hpNotMem hpqNot
    exact pathWeightRatio_one (k := k) p q
  · intro a b p hpMem hpNonzero
    have hclings : ContourFunctionClingsToPath R PI c p :=
      contourFunctionClingsToPath_of_related_interlaced
        R PI c p (hone p hpMem hpNonzero)
    have heq : contourFunctionCoboundaryHom (k := k) R e = 1 := by
      exact (contourFunctionCoboundaryHom (k := k) R).map_one
    change ContourFunctionClingsToPath R PI
      (c * (contourFunctionCoboundaryHom (k := k) R e)⁻¹) p
    rw [heq]
    simpa using hclings

/-- The cardinal form of the ideal-level `N = 1` branch.  In a finite ray
category, saying that every annihilated nonzero ray has exactly one
proper-whisker interlacement class supplies the pointwise interlacement
hypothesis used by the constant-one correction. -/
theorem hasInvisibleCorrectionClingingOnIdeal_of_killed_card_eq_one
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    (J : ZeroHomIdeal C) (hJ : J.IsProper)
    (hcard : ∀ {a b : RayVertex C} (p : Quiver.Path a b),
      J.mem (rayPathMap p) → rayPathMap p ≠ 0 →
        Nat.card (RelatedPathInterlacementClass
          (properWhiskerInterlacementRelation
            (rayPathContourRelation (C := C))) p) = 1) :
    J.HasInvisibleCorrectionClingingOnIdeal (k := k) := by
  apply J.hasInvisibleCorrectionClingingOnIdeal_of_killed_related_interlaced
  intro a b p hpMem hpNonzero q hpq
  have hpLength : p.length ≠ 0 := by
    intro hpZero
    have hpIso : IsIso (rayPathMap p) :=
      rayPathMap_isIso_of_length_eq_zero p hpZero
    letI : IsIso (rayPathMap p) := hpIso
    exact J.not_mem_of_isIso hJ (rayPathMap p) hpMem
  exact rayPaths_interlaced_of_card_eq_one p hpLength
    ⟨hpNonzero, rfl⟩ (hcard p hpMem hpNonzero) q hpq

/-- Ideal-level residue closure.  If the quotient restriction is exact and
the ideal admits the local invisible correction, one combined arrow weight
makes the corrected original contour function cling to every nonzero ray
path: quotient induction handles paths outside the ideal, while the local
correction handles paths inside it. -/
theorem exists_combinedCorrection_clings_every_nonzeroPath_of_isExact_quotOut
    (J : ZeroHomIdeal C) (hJ : J.IsProper)
    (c : contourScalarFunctionSubgroup (k := k)
      (rayPathContourRelation (C := C)))
    (hlocal : J.HasInvisibleCorrectionClingingOnIdeal (k := k))
    (hexact : IsExactContourFunction
      (rayPathContourRelation (C := CategoryTheory.Quotient J.rel))
      (J.quotOutContourScalarFunction hJ c)) :
    ∃ e : ArrowUnitWeight k (RayVertex C),
      ∀ {a b : RayVertex C} (p : Quiver.Path a b),
        rayPathMap p ≠ 0 →
          ContourFunctionClingsToPath
            (rayPathContourRelation (C := C))
            (properWhiskerInterlacementRelation
              (rayPathContourRelation (C := C)))
            (c * (contourFunctionCoboundaryHom (k := k)
              (rayPathContourRelation (C := C)) e)⁻¹) p := by
  let R := rayPathContourRelation (C := C)
  obtain ⟨e₀, hsurvive⟩ :=
    J.exists_liftQuotientArrowUnitWeight_clingsToPath_of_isExact_quotOut
      hJ c hexact
  obtain ⟨e₁, hinvisible, hkilled⟩ := hlocal
    (c * (contourFunctionCoboundaryHom (k := k) R e₀)⁻¹)
  let e : ArrowUnitWeight k (RayVertex C) := e₀ * e₁
  have hcombine :
      c * (contourFunctionCoboundaryHom (k := k) R e)⁻¹ =
        (c * (contourFunctionCoboundaryHom (k := k) R e₀)⁻¹) *
          (contourFunctionCoboundaryHom (k := k) R e₁)⁻¹ := by
    change c * (contourFunctionCoboundaryHom (k := k) R (e₀ * e₁))⁻¹ =
      (c * (contourFunctionCoboundaryHom (k := k) R e₀)⁻¹) *
        (contourFunctionCoboundaryHom (k := k) R e₁)⁻¹
    have hmap :
        contourFunctionCoboundaryHom (k := k) R (e₀ * e₁) =
          contourFunctionCoboundaryHom (k := k) R e₀ *
            contourFunctionCoboundaryHom (k := k) R e₁ :=
      (contourFunctionCoboundaryHom (k := k) R).map_mul e₀ e₁
    rw [hmap, mul_inv_rev]
    ac_rfl
  refine ⟨e, ?_⟩
  intro a b p hpNonzero
  rw [hcombine]
  by_cases hpMem : J.mem (rayPathMap p)
  · exact hkilled p hpMem hpNonzero
  · exact J.contourFunctionClingsToPath_mul_inv_coboundary_of_invisibleOnSurviving
      (c * (contourFunctionCoboundaryHom (k := k) R e₀)⁻¹)
      e₁ hinvisible p hpMem (hsurvive p hpMem)

/-- If one inverse coboundary correction makes a contour function cling to
every nonzero ray path, any clinging-detects-identity theorem promotes that
correction to an exactness witness for the original contour function. -/
theorem isExactContourFunction_of_correction_clings_every_nonzeroRayPath
    (c : contourScalarFunctionSubgroup (k := k)
      (rayPathContourRelation (C := C)))
    (hdetect : ClingingAtEverySourceDetectsIdentity (k := k)
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))))
    (e : ArrowUnitWeight k (RayVertex C))
    (hclings : ∀ {a b : RayVertex C} (p : Quiver.Path a b),
      rayPathMap p ≠ 0 →
        ContourFunctionClingsToPath
          (rayPathContourRelation (C := C))
          (properWhiskerInterlacementRelation
            (rayPathContourRelation (C := C)))
          (c * (contourFunctionCoboundaryHom (k := k)
            (rayPathContourRelation (C := C)) e)⁻¹) p) :
    IsExactContourFunction (rayPathContourRelation (C := C)) c := by
  let R := rayPathContourRelation (C := C)
  let d := c * (contourFunctionCoboundaryHom (k := k) R e)⁻¹
  have hd : d = 1 := hdetect d (by
    intro x y p q hpq
    exact hclings p hpq.1 q hpq)
  refine ⟨e, ?_⟩
  have hmul := congrArg
    (fun f : contourScalarFunctionSubgroup (k := k) R ↦
      f * contourFunctionCoboundaryHom (k := k) R e) hd
  have hcoboundary : c = contourFunctionCoboundaryHom (k := k) R e := by
    simpa [d] using hmul
  exact hcoboundary.symm

/-- Abstract exactness closure for one proper zero-ideal residue.  Quotient
exactness, the local invisible correction on the annihilated rays, and a
clinging-detects-identity result together imply exactness of the original
contour function. -/
theorem isExactContourFunction_of_isExact_quotOut_of_invisibleCorrection
    (J : ZeroHomIdeal C) (hJ : J.IsProper)
    (c : contourScalarFunctionSubgroup (k := k)
      (rayPathContourRelation (C := C)))
    (hdetect : ClingingAtEverySourceDetectsIdentity (k := k)
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))))
    (hlocal : J.HasInvisibleCorrectionClingingOnIdeal (k := k))
    (hexact : IsExactContourFunction
      (rayPathContourRelation (C := CategoryTheory.Quotient J.rel))
      (J.quotOutContourScalarFunction hJ c)) :
    IsExactContourFunction (rayPathContourRelation (C := C)) c := by
  obtain ⟨e, he⟩ :=
    J.exists_combinedCorrection_clings_every_nonzeroPath_of_isExact_quotOut
      hJ c hlocal hexact
  exact isExactContourFunction_of_correction_clings_every_nonzeroRayPath
    c hdetect e he

/-- In a finite ray category, the concrete morphism-depth rank discharges the
clinging-detects-identity hypothesis in the one-residue exactness closure. -/
theorem isExactContourFunction_of_isExact_quotOut_of_invisibleCorrection_finite
    [Finite C] [IsFiniteRayCategory C]
    (J : ZeroHomIdeal C) (hJ : J.IsProper)
    (c : contourScalarFunctionSubgroup (k := k)
      (rayPathContourRelation (C := C)))
    (hlocal : J.HasInvisibleCorrectionClingingOnIdeal (k := k))
    (hexact : IsExactContourFunction
      (rayPathContourRelation (C := CategoryTheory.Quotient J.rel))
      (J.quotOutContourScalarFunction hJ c)) :
    IsExactContourFunction (rayPathContourRelation (C := C)) c := by
  exact J.isExactContourFunction_of_isExact_quotOut_of_invisibleCorrection
    hJ c rayClingingAtEverySourceDetectsIdentity hlocal hexact

end ZeroHomIdeal

end LargeIndecomposable
