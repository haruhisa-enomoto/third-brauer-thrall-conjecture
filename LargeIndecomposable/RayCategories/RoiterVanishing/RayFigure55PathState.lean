module

public import LargeIndecomposable.RayCategories.RoiterVanishing.RayEfficientHookContour
public import LargeIndecomposable.RayCategories.RoiterVanishing.RayTacklePairReplacement

@[expose] public section

/-!
# Nonidentity path factors in the Figure 55 walk

The alternating efficiency argument in BGRS 8.4 produces categorical
factorizations through earlier tackle components.  Figure 55 then chooses
nonidentity irreducible paths presenting those factors and uses them in the
interlacement induction.  This file proves that the forced factors cannot be
invertible and packages positive-length path presentations of them.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Replacing an inner ray path by another path with the same nonzero
evaluation, inside a proper common context, gives both a related outer path
and one elementary interlacement step. -/
theorem rayPaths_related_and_interlaced_of_inner_map_eq
    {a i j b : RayVertex C}
    (s : Quiver.Path a i) (p q : Quiver.Path i j)
    (t : Quiver.Path j b)
    (houter : rayPathMap ((s.comp p).comp t) ≠ 0)
    (hmap : rayPathMap p = rayPathMap q)
    (hproper : 0 < s.length + t.length) :
    (rayPathContourRelation (C := C)).related
        ((s.comp p).comp t) ((s.comp q).comp t) ∧
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))).interlaced
          ((s.comp p).comp t) ((s.comp q).comp t) := by
  have hp : rayPathMap p ≠ 0 := by
    intro hpzero
    apply houter
    dsimp only [rayPathMap]
    rw [LinearPathCategory.pathMap_comp,
      LinearPathCategory.pathMap_comp]
    change LinearPathCategory.pathMap RayVertex.obj
      (fun {_ _} a ↦ rayArrowMorphism a) p = 0 at hpzero
    rw [hpzero]
    simp
  have hpq : (rayPathContourRelation (C := C)).related p q :=
    ⟨hp, hmap⟩
  have houterRelated :=
    rayPathContourRelation_whisker s p q t hpq houter
  refine ⟨houterRelated, ?_⟩
  apply properWhiskerInterlaced_of_step
    (rayPathContourRelation (C := C))
  exact ⟨i, j, s, p, q, t, hpq, houterRelated, hproper, rfl, rfl⟩

/-- A Figure 55 inner replacement preserves membership in the original
path's interlacement class. -/
theorem rayPaths_interlaced_of_interlaced_of_inner_map_eq
    {a i j b : RayVertex C}
    (base : Quiver.Path a b)
    (s : Quiver.Path a i) (p q : Quiver.Path i j)
    (t : Quiver.Path j b)
    (hbase : (properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced
        base ((s.comp p).comp t))
    (houter : rayPathMap ((s.comp p).comp t) ≠ 0)
    (hmap : rayPathMap p = rayPathMap q)
    (hproper : 0 < s.length + t.length) :
    (properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced
        base ((s.comp q).comp t) := by
  apply (properWhiskerInterlacementRelation
    (rayPathContourRelation (C := C))).trans hbase
  exact (rayPaths_related_and_interlaced_of_inner_map_eq
    s p q t houter hmap hproper).2

/-- The path invariant carried backward in BGRS Figure 55.  The current path
`r` represents the same nonzero ray as the essential contour side `p` and
lies in its proper-whisker interlacement class. -/
structure Figure55PathState
    {x z : RayVertex C} (p q r : Quiver.Path x z) : Prop where
  essential : IsEssentialPathContour
    (rayPathContourRelation (C := C))
    (properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))) p q
  related_left : (rayPathContourRelation (C := C)).related p r
  interlaced_left : (properWhiskerInterlacementRelation
    (rayPathContourRelation (C := C))).interlaced p r

namespace Figure55PathState

/-- The original left contour path is the initial Figure 55 path state. -/
theorem self {x z : RayVertex C} {p q : Quiver.Path x z}
    (hessential : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q) :
    Figure55PathState p q p :=
  ⟨hessential, ⟨hessential.1.1, rfl⟩,
    (properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).refl p⟩

/-- A Figure 55 path state can never lie in the other essential contour
side's interlacement class. -/
theorem not_interlaced_right
    {x z : RayVertex C} {p q r : Quiver.Path x z}
    (h : Figure55PathState p q r) :
    ¬(properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced r q := by
  intro hrq
  apply h.essential.2
  exact (properWhiskerInterlacementRelation
    (rayPathContourRelation (C := C))).trans h.interlaced_left hrq

/-- Replacing an equal inner path inside a proper context advances the
Figure 55 state while preserving the fixed essential contour. -/
theorem replaceInner
    {x z i j : RayVertex C}
    (p q : Quiver.Path x z)
    (s : Quiver.Path x i) (old new : Quiver.Path i j)
    (t : Quiver.Path j z)
    (hstate : Figure55PathState p q ((s.comp old).comp t))
    (hmap : rayPathMap old = rayPathMap new)
    (hproper : 0 < s.length + t.length) :
    Figure55PathState p q ((s.comp new).comp t) := by
  have hcurrent : rayPathMap ((s.comp old).comp t) ≠ 0 := by
    rw [← hstate.related_left.2]
    exact hstate.related_left.1
  have hstep := rayPaths_related_and_interlaced_of_inner_map_eq
    s old new t hcurrent hmap hproper
  exact
    { essential := hstate.essential
      related_left := (rayPathContourRelation (C := C)).trans
        hstate.related_left hstep.1
      interlaced_left := (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))).trans
          hstate.interlaced_left hstep.2 }

/-- In a Figure 55 state with a nonidentity suffix, the initial arrow of the
other essential contour side cannot factor the exposed leading morphism.
Such a factorization would replace the lead by an equal path beginning with
that arrow, placing the new path in both interlacement classes. -/
theorem not_exists_comp_rightInitial_eq_lead
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {x z m : RayVertex C} {p q r : Quiver.Path x z}
    (hstate : Figure55PathState p q r)
    (lead : Quiver.Path x m) (tail : Quiver.Path m z)
    (hr : r = lead.comp tail) (htail : tail.length ≠ 0)
    (dq : PathEndpointDecomposition q) :
    ¬∃ h : m.obj ⟶ dq.initialMiddle.obj,
      h ≠ 0 ∧ h ≫ rayArrowMorphism dq.initial = rayPathMap lead := by
  rintro ⟨h, hne, hfactor⟩
  let hHom : NonzeroHom m.obj dq.initialMiddle.obj := ⟨h, hne⟩
  obtain ⟨rh⟩ :=
    HasFiniteRayPathDepth.presentation_nonempty hHom.toMorphismFrom
  let inner : Quiver.Path x m := dq.initial.toPath.comp rh.path
  have hinnerMap : rayPathMap inner = h ≫ rayArrowMorphism dq.initial := by
    calc
      rayPathMap inner =
          rayPathMap rh.path ≫ rayPathMap dq.initial.toPath := by
        exact LinearPathCategory.pathMap_comp
          RayVertex.obj rayArrowMorphism dq.initial.toPath rh.path
      _ = h ≫ rayArrowMorphism dq.initial := by
        rw [rayPathMap_toPath, rh.map_eq]
  have hleadInner : rayPathMap lead = rayPathMap inner :=
    hfactor.symm.trans hinnerMap.symm
  have hstateOld : Figure55PathState p q
      ((Quiver.Path.nil.comp lead).comp tail) := by
    simpa only [Quiver.Path.nil_comp, ← hr] using hstate
  have hstateNew : Figure55PathState p q (inner.comp tail) := by
    simpa only [Quiver.Path.nil_comp] using
      hstateOld.replaceInner p q Quiver.Path.nil lead inner tail
        hleadInner (by simpa using Nat.pos_of_ne_zero htail)
  let dr : PathInitialDecomposition (inner.comp tail) :=
    { middle := dq.initialMiddle
      arrow := dq.initial
      tail := rh.path.comp tail
      path_eq := by
        dsimp only [inner]
        exact Quiver.Path.comp_assoc _ _ _ }
  exact (initialArrow_ne_of_related_interlaced_of_essential
    hstateNew.essential hstateNew.related_left
      hstateNew.interlaced_left dr dq.toInitial) rfl

/-- The orientation-dual endpoint obstruction.  With a nonidentity prefix,
the final arrow of the other contour side cannot factor the exposed trailing
morphism of a Figure 55 state. -/
theorem not_exists_rightFinal_comp_eq_rest
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {x z m : RayVertex C} {p q r : Quiver.Path x z}
    (hstate : Figure55PathState p q r)
    (before : Quiver.Path x m) (rest : Quiver.Path m z)
    (hr : r = before.comp rest) (hbefore : before.length ≠ 0)
    (dq : PathEndpointDecomposition q) :
    ¬∃ h : dq.finalMiddle.obj ⟶ m.obj,
      h ≠ 0 ∧ rayArrowMorphism dq.final ≫ h = rayPathMap rest := by
  rintro ⟨h, hne, hfactor⟩
  let hHom : NonzeroHom dq.finalMiddle.obj m.obj := ⟨h, hne⟩
  obtain ⟨rh⟩ :=
    HasFiniteRayPathDepth.presentation_nonempty hHom.toMorphismFrom
  let inner : Quiver.Path m z := rh.path.comp dq.final.toPath
  have hinnerMap : rayPathMap inner = rayArrowMorphism dq.final ≫ h := by
    calc
      rayPathMap inner =
          rayPathMap dq.final.toPath ≫ rayPathMap rh.path := by
        exact LinearPathCategory.pathMap_comp
          RayVertex.obj rayArrowMorphism rh.path dq.final.toPath
      _ = rayArrowMorphism dq.final ≫ h := by
        rw [rayPathMap_toPath, rh.map_eq]
  have hrestInner : rayPathMap rest = rayPathMap inner :=
    hfactor.symm.trans hinnerMap.symm
  have hstateOld : Figure55PathState p q
      ((before.comp rest).comp Quiver.Path.nil) := by
    simpa only [Quiver.Path.comp_nil, ← hr] using hstate
  have hstateNew : Figure55PathState p q (before.comp inner) := by
    simpa only [Quiver.Path.comp_nil] using
      hstateOld.replaceInner p q before rest inner Quiver.Path.nil
        hrestInner (by simpa using Nat.pos_of_ne_zero hbefore)
  let dr : PathFinalDecomposition (before.comp inner) :=
    { middle := dq.finalMiddle
      head := before.comp rh.path
      arrow := dq.final
      path_eq := by
        dsimp only [inner]
        exact (Quiver.Path.comp_assoc _ _ _).symm }
  exact (finalArrow_ne_of_related_interlaced_of_essential
    hstateNew.essential hstateNew.related_left
      hstateNew.interlaced_left dr dq.toFinal) rfl

/-- The nonzero category morphism represented by the leading part of a
Figure 55 state path. -/
def leadNonzeroHom
    {x z m : RayVertex C} {p q r : Quiver.Path x z}
    (hstate : Figure55PathState p q r)
    (lead : Quiver.Path x m) (tail : Quiver.Path m z)
    (hr : r = lead.comp tail) : NonzeroHom m.obj x.obj :=
  ⟨rayPathMap lead, by
    intro hzero
    apply hstate.related_left.1
    rw [hstate.related_left.2, hr]
    dsimp only [rayPathMap]
    rw [LinearPathCategory.pathMap_comp]
    change LinearPathCategory.pathMap RayVertex.obj
      (fun {_ _} a ↦ rayArrowMorphism a) lead = 0 at hzero
    rw [hzero]
    simp⟩

/-- The nonzero category morphism represented by the trailing part of a
Figure 55 state path. -/
def restNonzeroHom
    {x z m : RayVertex C} {p q r : Quiver.Path x z}
    (hstate : Figure55PathState p q r)
    (before : Quiver.Path x m) (rest : Quiver.Path m z)
    (hr : r = before.comp rest) : NonzeroHom z.obj m.obj :=
  ⟨rayPathMap rest, by
    intro hzero
    apply hstate.related_left.1
    rw [hstate.related_left.2, hr]
    dsimp only [rayPathMap]
    rw [LinearPathCategory.pathMap_comp]
    change LinearPathCategory.pathMap RayVertex.obj
      (fun {_ _} a ↦ rayArrowMorphism a) rest = 0 at hzero
    rw [hzero]
    simp⟩

/-- State-level form of the peak incomparability used in Figure 55.  A
depth-greater-than-one leading morphism is target-incomparable with the
other contour side's initial irreducible arrow. -/
theorem targetIncomparable_lead_rightInitial
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {x z m : RayVertex C} {p q r : Quiver.Path x z}
    (hstate : Figure55PathState p q r)
    (lead : Quiver.Path x m) (tail : Quiver.Path m z)
    (hr : r = lead.comp tail) (htail : tail.length ≠ 0)
    (dq : PathEndpointDecomposition q)
    (hdepth : 1 < (hstate.leadNonzeroHom lead tail hr).depth) :
    RayTargetIncomparable
      (hstate.leadNonzeroHom lead tail hr)
      dq.toInitial.rayArrowNonzeroHom := by
  let f := hstate.leadNonzeroHom lead tail hr
  let g := dq.toInitial.rayArrowNonzeroHom
  apply rayTargetIncomparable_of_not_exists_factor_of_one_lt_depth
    f g hdepth dq.initial.property
  intro hfactor
  apply hstate.not_exists_comp_rightInitial_eq_lead
    lead tail hr htail dq
  obtain ⟨h, hh⟩ := hfactor
  refine ⟨h, ?_, hh⟩
  rintro rfl
  apply f.2
  dsimp [g, PathInitialDecomposition.rayArrowNonzeroHom,
    PathEndpointDecomposition.toInitial] at hh
  simpa using hh.symm

/-- If a Figure 55 state starts with a single irreducible arrow and has a
nonidentity suffix, that arrow is target-incomparable with the initial arrow
of the other contour side.  Unlike the depth-greater-than-one version, the
reverse factorization is excluded by replacing the other side's initial arrow
inside its nonidentity tail and comparing the resulting initial-arrow class. -/
theorem targetIncomparable_initialArrow_rightInitial
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {x z m : RayVertex C} {p q r : Quiver.Path x z}
    (hstate : Figure55PathState p q r)
    (a : x ⟶ m) (tail : Quiver.Path m z)
    (hr : r = a.toPath.comp tail) (htail : tail.length ≠ 0)
    (dq : PathEndpointDecomposition q) :
    RayTargetIncomparable
      (hstate.leadNonzeroHom a.toPath tail hr)
      dq.toInitial.rayArrowNonzeroHom := by
  let f := hstate.leadNonzeroHom a.toPath tail hr
  let g := dq.toInitial.rayArrowNonzeroHom
  constructor
  · intro hfactor
    apply hstate.not_exists_comp_rightInitial_eq_lead
      a.toPath tail hr htail dq
    obtain ⟨h, hh⟩ := hfactor
    refine ⟨h, ?_, hh⟩
    rintro rfl
    apply f.2
    dsimp [g, PathInitialDecomposition.rayArrowNonzeroHom,
      PathEndpointDecomposition.toInitial] at hh
    simpa [f, Figure55PathState.leadNonzeroHom] using hh.symm
  · change ¬∃ h : dq.initialMiddle.obj ⟶ m.obj,
      h ≫ f.1 = rayArrowMorphism dq.initial
    rintro ⟨h, hh⟩
    have hne : h ≠ 0 := by
      rintro rfl
      exact dq.initial.property.1 (hh.symm.trans Limits.zero_comp)
    let hHom : NonzeroHom dq.initialMiddle.obj m.obj := ⟨h, hne⟩
    obtain ⟨rh⟩ :=
      HasFiniteRayPathDepth.presentation_nonempty hHom.toMorphismFrom
    let inner : Quiver.Path x dq.initialMiddle :=
      a.toPath.comp rh.path
    let q' : Quiver.Path x z := inner.comp dq.toInitial.tail
    have hinnerMap :
        rayPathMap inner = hHom.1 ≫ rayArrowMorphism a := by
      calc
        rayPathMap inner =
            rayPathMap rh.path ≫ rayPathMap a.toPath := by
          exact LinearPathCategory.pathMap_comp
            RayVertex.obj rayArrowMorphism a.toPath rh.path
        _ = hHom.1 ≫ rayArrowMorphism a := by
          rw [rayPathMap_toPath, rh.map_eq]
    have hmap : rayPathMap dq.initial.toPath = rayPathMap inner := by
      calc
        rayPathMap dq.initial.toPath = rayArrowMorphism dq.initial := by
          exact rayPathMap_toPath dq.initial
        _ = h ≫ f.1 := hh.symm
        _ = h ≫ rayArrowMorphism a := by
          simp [f, Figure55PathState.leadNonzeroHom]
        _ = rayPathMap inner := by
          simpa [hHom] using hinnerMap.symm
    have hqNonzero : rayPathMap q ≠ 0 := by
      rw [← hstate.essential.1.2]
      exact hstate.essential.1.1
    have hqForm : q =
        dq.initial.toPath.comp dq.toInitial.tail :=
      dq.toInitial.path_eq
    have houter : rayPathMap
        ((Quiver.Path.nil.comp dq.initial.toPath).comp
          dq.toInitial.tail) ≠ 0 := by
      rw [hqForm] at hqNonzero
      simpa only [Quiver.Path.nil_comp] using hqNonzero
    have hproper : 0 <
        (Quiver.Path.nil : Quiver.Path x x).length +
          dq.toInitial.tail.length := by
      simp [PathEndpointDecomposition.toInitial]
    have hstep := rayPaths_related_and_interlaced_of_inner_map_eq
      Quiver.Path.nil dq.initial.toPath inner dq.toInitial.tail
        houter hmap hproper
    have hqq' : (rayPathContourRelation (C := C)).related q q' := by
      rw [hqForm]
      simpa only [Quiver.Path.nil_comp, q'] using hstep.1
    have hiqq' : (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))).interlaced q q' := by
      rw [hqForm]
      simpa only [Quiver.Path.nil_comp, q'] using hstep.2
    have hrq : (rayPathContourRelation (C := C)).related r q :=
      (rayPathContourRelation (C := C)).trans
        ((rayPathContourRelation (C := C)).symm hstate.related_left)
        hstate.essential.1
    have hrq' : (rayPathContourRelation (C := C)).related r q' :=
      (rayPathContourRelation (C := C)).trans hrq hqq'
    let dr : PathInitialDecomposition r :=
      { middle := m
        arrow := a
        tail := tail
        path_eq := hr }
    let dq' : PathInitialDecomposition q' :=
      { middle := m
        arrow := a
        tail := rh.path.comp dq.toInitial.tail
        path_eq := by
          dsimp only [q', inner]
          exact Quiver.Path.comp_assoc _ _ _ }
    have hirq' : (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))).interlaced r q' := by
      apply rayPaths_interlaced_of_initialDecomposition_code_eq
        dr dq' hrq'
      rfl
    apply hstate.not_interlaced_right
    exact (properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).trans hirq'
        ((properWhiskerInterlacementRelation
          (rayPathContourRelation (C := C))).symm hiqq')

/-- If a Figure 55 state ends with a single irreducible arrow and has a
nonidentity prefix, that arrow is source-incomparable with the final arrow of
the other contour side.  This is the final-arrow dual of
`targetIncomparable_initialArrow_rightInitial`. -/
theorem sourceIncomparable_finalArrow_rightFinal
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {x z m : RayVertex C} {p q r : Quiver.Path x z}
    (hstate : Figure55PathState p q r)
    (head : Quiver.Path x m) (a : m ⟶ z)
    (hr : r = head.comp a.toPath) (hhead : head.length ≠ 0)
    (dq : PathEndpointDecomposition q) :
    RaySourceIncomparable
      (hstate.restNonzeroHom head a.toPath hr)
      dq.toFinal.rayArrowNonzeroHom := by
  let f := hstate.restNonzeroHom head a.toPath hr
  let g := dq.toFinal.rayArrowNonzeroHom
  constructor
  · change ¬∃ h : m.obj ⟶ dq.finalMiddle.obj,
      f.1 ≫ h = rayArrowMorphism dq.final
    rintro ⟨h, hh⟩
    have hne : h ≠ 0 := by
      rintro rfl
      exact dq.final.property.1 (hh.symm.trans Limits.comp_zero)
    let hHom : NonzeroHom m.obj dq.finalMiddle.obj := ⟨h, hne⟩
    obtain ⟨rh⟩ :=
      HasFiniteRayPathDepth.presentation_nonempty hHom.toMorphismFrom
    let inner : Quiver.Path dq.finalMiddle z :=
      rh.path.comp a.toPath
    let q' : Quiver.Path x z := dq.toFinal.head.comp inner
    have hinnerMap :
        rayPathMap inner = rayArrowMorphism a ≫ hHom.1 := by
      calc
        rayPathMap inner =
            rayPathMap a.toPath ≫ rayPathMap rh.path := by
          exact LinearPathCategory.pathMap_comp
            RayVertex.obj rayArrowMorphism rh.path a.toPath
        _ = rayArrowMorphism a ≫ hHom.1 := by
          rw [rayPathMap_toPath, rh.map_eq]
    have hmap : rayPathMap dq.final.toPath = rayPathMap inner := by
      calc
        rayPathMap dq.final.toPath = rayArrowMorphism dq.final := by
          exact rayPathMap_toPath dq.final
        _ = f.1 ≫ h := hh.symm
        _ = rayArrowMorphism a ≫ h := by
          simp [f, Figure55PathState.restNonzeroHom]
        _ = rayPathMap inner := by
          simpa [hHom] using hinnerMap.symm
    have hqNonzero : rayPathMap q ≠ 0 := by
      rw [← hstate.essential.1.2]
      exact hstate.essential.1.1
    have hqForm : q =
        dq.toFinal.head.comp dq.final.toPath :=
      dq.toFinal.path_eq
    have houter : rayPathMap
        ((dq.toFinal.head.comp dq.final.toPath).comp
          (Quiver.Path.nil : Quiver.Path z z)) ≠ 0 := by
      rw [hqForm] at hqNonzero
      simpa only [Quiver.Path.comp_nil] using hqNonzero
    have hproper : 0 <
        dq.toFinal.head.length +
          (Quiver.Path.nil : Quiver.Path z z).length := by
      simp [PathEndpointDecomposition.toFinal]
    have hstep := rayPaths_related_and_interlaced_of_inner_map_eq
      dq.toFinal.head dq.final.toPath inner Quiver.Path.nil
        houter hmap hproper
    have hqq' : (rayPathContourRelation (C := C)).related q q' := by
      rw [hqForm]
      simpa only [Quiver.Path.comp_nil, q'] using hstep.1
    have hiqq' : (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))).interlaced q q' := by
      rw [hqForm]
      simpa only [Quiver.Path.comp_nil, q'] using hstep.2
    have hrq : (rayPathContourRelation (C := C)).related r q :=
      (rayPathContourRelation (C := C)).trans
        ((rayPathContourRelation (C := C)).symm hstate.related_left)
        hstate.essential.1
    have hrq' : (rayPathContourRelation (C := C)).related r q' :=
      (rayPathContourRelation (C := C)).trans hrq hqq'
    let dr : PathFinalDecomposition r :=
      { middle := m
        head := head
        arrow := a
        path_eq := hr }
    let dq' : PathFinalDecomposition q' :=
      { middle := m
        head := dq.toFinal.head.comp rh.path
        arrow := a
        path_eq := by
          dsimp only [q', inner]
          exact (Quiver.Path.comp_assoc _ _ _).symm }
    have hirq' : (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))).interlaced r q' := by
      apply rayPaths_interlaced_of_finalDecomposition_code_eq
        dr dq' hrq'
      rfl
    apply hstate.not_interlaced_right
    exact (properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).trans hirq'
        ((properWhiskerInterlacementRelation
          (rayPathContourRelation (C := C))).symm hiqq')
  · intro hfactor
    apply hstate.not_exists_rightFinal_comp_eq_rest
      head a.toPath hr hhead dq
    obtain ⟨h, hh⟩ := hfactor
    refine ⟨h, ?_, hh⟩
    rintro rfl
    apply f.2
    dsimp [g, PathFinalDecomposition.rayArrowNonzeroHom,
      PathEndpointDecomposition.toFinal] at hh
    simpa [f, Figure55PathState.restNonzeroHom] using hh.symm

/-- The orientation-dual valley incomparability.  A depth-greater-than-one
trailing morphism is source-incomparable with the other contour side's final
irreducible arrow. -/
theorem sourceIncomparable_rest_rightFinal
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {x z m : RayVertex C} {p q r : Quiver.Path x z}
    (hstate : Figure55PathState p q r)
    (before : Quiver.Path x m) (rest : Quiver.Path m z)
    (hr : r = before.comp rest) (hbefore : before.length ≠ 0)
    (dq : PathEndpointDecomposition q)
    (hdepth : 1 < (hstate.restNonzeroHom before rest hr).depth) :
    RaySourceIncomparable
      (hstate.restNonzeroHom before rest hr)
      dq.toFinal.rayArrowNonzeroHom := by
  let f := hstate.restNonzeroHom before rest hr
  let g := dq.toFinal.rayArrowNonzeroHom
  apply raySourceIncomparable_of_not_exists_factor_of_one_lt_depth
    f g hdepth dq.final.property
  intro hfactor
  apply hstate.not_exists_rightFinal_comp_eq_rest
    before rest hr hbefore dq
  obtain ⟨h, hh⟩ := hfactor
  refine ⟨h, ?_, hh⟩
  rintro rfl
  apply f.2
  dsimp [g, PathFinalDecomposition.rayArrowNonzeroHom,
    PathEndpointDecomposition.toFinal] at hh
  simpa using hh.symm

end Figure55PathState

namespace RayPathPresentation

/-- A presentation of a noninvertible ray morphism has positive length. -/
theorem length_ne_zero_of_not_isIso
    [IsFiniteRayCategory C]
    {x : C} {f : NonzeroMorphismFrom x}
    (p : RayPathPresentation f) (hf : ¬IsIso f.hom) :
    p.path.length ≠ 0 := by
  intro hzero
  apply hf
  rw [← p.map_eq]
  exact rayPathMap_isIso_of_length_eq_zero p.path hzero

end RayPathPresentation

namespace NonzeroHom

/-- Choose a positive-length irreducible-path presentation of a noninvertible
nonzero ray morphism. -/
theorem exists_presentation_length_ne_zero
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    {X Y : C} (f : NonzeroHom X Y) (hf : ¬IsIso f.1) :
    ∃ p : RayPathPresentation f.toMorphismFrom, p.path.length ≠ 0 := by
  obtain ⟨p⟩ :=
    HasFiniteRayPathDepth.presentation_nonempty f.toMorphismFrom
  exact ⟨p, p.length_ne_zero_of_not_isIso hf⟩

end NonzeroHom

namespace RayHookChain

/-- The factor through the retained `rho_n` forced by hook-side efficiency
cannot be invertible.  Otherwise the old `rho_n` would factor through the
omitted `sigma_n`, contradicting their peak incomparability. -/
theorem exists_noniso_factorThroughCutoffRho_of_isEfficientAt
    [HasFiniteRayPathDepth C] {m n : ℕ}
    (t : RayHookTackle (C := C) m) (hcut : n < m) {y X Z : C}
    (ht : (RayTackle.hook m t).IsEfficientAt y)
    (f : NonzeroHom X
      ((RayHookChain.prefixAt t hcut).z (Fin.last n)))
    (g : NonzeroHom X Z)
    (a : X ⟶ t.x ((Fin.last n).castLE hcut).succ)
    (hfactor : a ≫ (RayHookChain.cutoffSigma t hcut).1 = f.1)
    (hvalley : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : (RayHookChain.cutoffSigma t hcut).depth < f.depth) :
    ∃ q : X ⟶ (RayHookChain.prefixAt t hcut).x (Fin.last n),
      q ≠ 0 ∧ ¬IsIso q ∧
        q ≫ ((RayHookChain.prefixAt t hcut).rho (Fin.last n)).1 = f.1 := by
  obtain ⟨q, hqne, hq⟩ :=
    RayHookChain.exists_factorThroughCutoffRho_of_isEfficientAt
      t hcut ht f g a hfactor hvalley hg hfdepth
  refine ⟨q, hqne, ?_, hq⟩
  intro hqIso
  letI : IsIso q := hqIso
  apply (RayHookChain.cutoff_peak_incomparable t hcut).1
  refine ⟨inv q ≫ a, ?_⟩
  calc
    (inv q ≫ a) ≫ (RayHookChain.cutoffSigma t hcut).1 =
        inv q ≫ (a ≫ (RayHookChain.cutoffSigma t hcut).1) := by
      rw [Category.assoc]
    _ = inv q ≫ f.1 := by rw [hfactor]
    _ = inv q ≫
        (q ≫ ((RayHookChain.prefixAt t hcut).rho (Fin.last n)).1) := by
      rw [hq]
    _ = ((RayHookChain.prefixAt t hcut).rho (Fin.last n)).1 := by
      simp

/-- Hook-side efficiency supplies the positive-length path `p_i` used by the
next Figure 55 interlacement step. -/
theorem exists_nonidentityPresentation_factorThroughCutoffRho_of_isEfficientAt
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C] {m n : ℕ}
    (t : RayHookTackle (C := C) m) (hcut : n < m) {y X Z : C}
    (ht : (RayTackle.hook m t).IsEfficientAt y)
    (f : NonzeroHom X
      ((RayHookChain.prefixAt t hcut).z (Fin.last n)))
    (g : NonzeroHom X Z)
    (a : X ⟶ t.x ((Fin.last n).castLE hcut).succ)
    (hfactor : a ≫ (RayHookChain.cutoffSigma t hcut).1 = f.1)
    (hvalley : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : (RayHookChain.cutoffSigma t hcut).depth < f.depth) :
    ∃ q : NonzeroHom X
        ((RayHookChain.prefixAt t hcut).x (Fin.last n)),
      ¬IsIso q.1 ∧
        ∃ p : RayPathPresentation q.toMorphismFrom,
          p.path.length ≠ 0 ∧
            q.1 ≫
              ((RayHookChain.prefixAt t hcut).rho (Fin.last n)).1 = f.1 := by
  obtain ⟨q, hqne, hqNoniso, hq⟩ :=
    RayHookChain.exists_noniso_factorThroughCutoffRho_of_isEfficientAt
      t hcut ht f g a hfactor hvalley hg hfdepth
  let qHom : NonzeroHom X
      ((RayHookChain.prefixAt t hcut).x (Fin.last n)) := ⟨q, hqne⟩
  obtain ⟨p, hp⟩ := qHom.exists_presentation_length_ne_zero hqNoniso
  exact ⟨qHom, hqNoniso, p, hp, hq⟩

/-- The cross-orientation factor through `rho_n` forced by efficiency of the
original cohook tackle cannot be invertible.  Otherwise the old `rho_n`
would factor through the omitted `sigma_n`, contradicting the old tackle
peak. -/
theorem exists_noniso_factorThroughCutoffRho_of_cohook_isEfficientAt
    [HasFiniteRayPathDepth C] {m n : ℕ}
    (t : RayCohookTackle (C := C) m) (hcut : n < m) {y X Z : C}
    (ht : (RayTackle.cohook m t).IsEfficientAt y)
    (f : NonzeroHom X
      ((RayHookChain.prefixOfCohookAt t hcut).z (Fin.last n)))
    (g : NonzeroHom X Z)
    (a : X ⟶ t.x ((Fin.last n).castLE hcut).succ.castSucc)
    (hfactor : a ≫ (RayHookChain.cutoffSigmaOfCohook t hcut).1 = f.1)
    (hvalley : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : (RayHookChain.cutoffSigmaOfCohook t hcut).depth < f.depth) :
    ∃ q : X ⟶ (RayHookChain.prefixOfCohookAt t hcut).x (Fin.last n),
      q ≠ 0 ∧ ¬IsIso q ∧
        q ≫ ((RayHookChain.prefixOfCohookAt t hcut).rho (Fin.last n)).1 =
          f.1 := by
  obtain ⟨q, hqne, hq⟩ :=
    RayHookChain.exists_factorThroughCutoffRho_of_cohook_isEfficientAt
      t hcut ht f g a hfactor hvalley hg hfdepth
  refine ⟨q, hqne, ?_, hq⟩
  intro hqIso
  letI : IsIso q := hqIso
  apply (RayHookChain.cutoffOfCohook_peak_incomparable t hcut).1
  refine ⟨inv q ≫ a, ?_⟩
  calc
    (inv q ≫ a) ≫ (RayHookChain.cutoffSigmaOfCohook t hcut).1 =
        inv q ≫ (a ≫ (RayHookChain.cutoffSigmaOfCohook t hcut).1) := by
      rw [Category.assoc]
    _ = inv q ≫ f.1 := by rw [hfactor]
    _ = inv q ≫ (q ≫
        ((RayHookChain.prefixOfCohookAt t hcut).rho (Fin.last n)).1) := by
      rw [hq]
    _ = ((RayHookChain.prefixOfCohookAt t hcut).rho (Fin.last n)).1 := by
      simp

/-- Efficiency of one fixed cohook tackle supplies the positive-length
factor path used by its hook-shaped Figure 55 cutoff. -/
theorem exists_nonidentityPresentation_factorThroughCutoffRho_of_cohook_isEfficientAt
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C] {m n : ℕ}
    (t : RayCohookTackle (C := C) m) (hcut : n < m) {y X Z : C}
    (ht : (RayTackle.cohook m t).IsEfficientAt y)
    (f : NonzeroHom X
      ((RayHookChain.prefixOfCohookAt t hcut).z (Fin.last n)))
    (g : NonzeroHom X Z)
    (a : X ⟶ t.x ((Fin.last n).castLE hcut).succ.castSucc)
    (hfactor : a ≫ (RayHookChain.cutoffSigmaOfCohook t hcut).1 = f.1)
    (hvalley : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : (RayHookChain.cutoffSigmaOfCohook t hcut).depth < f.depth) :
    ∃ q : NonzeroHom X
        ((RayHookChain.prefixOfCohookAt t hcut).x (Fin.last n)),
      ¬IsIso q.1 ∧
        ∃ p : RayPathPresentation q.toMorphismFrom,
          p.path.length ≠ 0 ∧
            q.1 ≫
              ((RayHookChain.prefixOfCohookAt t hcut).rho (Fin.last n)).1 =
                f.1 := by
  obtain ⟨q, hqne, hqNoniso, hq⟩ :=
    RayHookChain.exists_noniso_factorThroughCutoffRho_of_cohook_isEfficientAt
      t hcut ht f g a hfactor hvalley hg hfdepth
  let qHom : NonzeroHom X
      ((RayHookChain.prefixOfCohookAt t hcut).x (Fin.last n)) :=
    ⟨q, hqne⟩
  obtain ⟨p, hp⟩ := qHom.exists_presentation_length_ne_zero hqNoniso
  exact ⟨qHom, hqNoniso, p, hp, hq⟩

end RayHookChain

namespace RayCohookChain

/-- The factor through the retained `sigma_n` forced by cohook-side
efficiency cannot be invertible.  Otherwise the old `sigma_n` would factor
through the omitted `rho_(n+1)`, contradicting their valley
incomparability. -/
theorem exists_noniso_factorThroughCutoffSigma_of_isEfficientAt
    [HasFiniteRayPathDepth C] {m n : ℕ}
    (t : RayCohookTackle (C := C) m) (hcut : n < m) {y X Z : C}
    (ht : (RayTackle.cohook m t).IsEfficientAt y)
    (f : NonzeroHom
      ((RayCohookChain.prefixAt t hcut).x (Fin.last (n + 1))) Z)
    (g : NonzeroHom X Z)
    (b : t.z ((Fin.last n).castLE hcut).succ ⟶ Z)
    (hfactor : (RayCohookChain.cutoffRho t hcut).1 ≫ b = f.1)
    (hpeak : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : (RayCohookChain.cutoffRho t hcut).depth < f.depth) :
    ∃ q : (RayCohookChain.prefixAt t hcut).z (Fin.last n) ⟶ Z,
      q ≠ 0 ∧ ¬IsIso q ∧
        ((RayCohookChain.prefixAt t hcut).sigma (Fin.last n)).1 ≫ q =
          f.1 := by
  obtain ⟨q, hqne, hq⟩ :=
    RayCohookChain.exists_factorThroughCutoffSigma_of_isEfficientAt
      t hcut ht f g b hfactor hpeak hg hfdepth
  refine ⟨q, hqne, ?_, hq⟩
  intro hqIso
  letI : IsIso q := hqIso
  apply (RayCohookChain.cutoff_valley_incomparable t hcut).2
  refine ⟨b ≫ inv q, ?_⟩
  calc
    (RayCohookChain.cutoffRho t hcut).1 ≫ (b ≫ inv q) =
        ((RayCohookChain.cutoffRho t hcut).1 ≫ b) ≫ inv q := by
      rw [Category.assoc]
    _ = f.1 ≫ inv q := by rw [hfactor]
    _ = (((RayCohookChain.prefixAt t hcut).sigma (Fin.last n)).1 ≫ q) ≫
        inv q := congrArg (fun r ↦ r ≫ inv q) hq.symm
    _ = ((RayCohookChain.prefixAt t hcut).sigma (Fin.last n)).1 := by
      simp

/-- Cohook-side efficiency supplies the positive-length path `u_i` used by
the next Figure 55 interlacement step. -/
theorem exists_nonidentityPresentation_factorThroughCutoffSigma_of_isEfficientAt
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C] {m n : ℕ}
    (t : RayCohookTackle (C := C) m) (hcut : n < m) {y X Z : C}
    (ht : (RayTackle.cohook m t).IsEfficientAt y)
    (f : NonzeroHom
      ((RayCohookChain.prefixAt t hcut).x (Fin.last (n + 1))) Z)
    (g : NonzeroHom X Z)
    (b : t.z ((Fin.last n).castLE hcut).succ ⟶ Z)
    (hfactor : (RayCohookChain.cutoffRho t hcut).1 ≫ b = f.1)
    (hpeak : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : (RayCohookChain.cutoffRho t hcut).depth < f.depth) :
    ∃ q : NonzeroHom
        ((RayCohookChain.prefixAt t hcut).z (Fin.last n)) Z,
      ¬IsIso q.1 ∧
        ∃ p : RayPathPresentation q.toMorphismFrom,
          p.path.length ≠ 0 ∧
            ((RayCohookChain.prefixAt t hcut).sigma (Fin.last n)).1 ≫
              q.1 = f.1 := by
  obtain ⟨q, hqne, hqNoniso, hq⟩ :=
    RayCohookChain.exists_noniso_factorThroughCutoffSigma_of_isEfficientAt
      t hcut ht f g b hfactor hpeak hg hfdepth
  let qHom : NonzeroHom
      ((RayCohookChain.prefixAt t hcut).z (Fin.last n)) Z := ⟨q, hqne⟩
  obtain ⟨p, hp⟩ := qHom.exists_presentation_length_ne_zero hqNoniso
  exact ⟨qHom, hqNoniso, p, hp, hq⟩

/-- The cross-orientation factor through `sigma_n` forced by efficiency of
the original hook tackle cannot be invertible.  Otherwise the omitted
`rho_(n+1)` would factor through the retained `sigma_n`, contradicting the
old tackle valley. -/
theorem exists_noniso_factorThroughCutoffSigma_of_hook_isEfficientAt
    [HasFiniteRayPathDepth C] {m n : ℕ}
    (t : RayHookTackle (C := C) m) (hcut : n < m) {y X Z : C}
    (ht : (RayTackle.hook m t).IsEfficientAt y)
    (f : NonzeroHom
      ((RayCohookChain.prefixOfHookAt t hcut).x (Fin.last (n + 1))) Z)
    (g : NonzeroHom X Z)
    (b : t.z ((Fin.last n).castLE hcut).succ ⟶ Z)
    (hfactor : (RayCohookChain.cutoffRhoOfHook t hcut).1 ≫ b = f.1)
    (hpeak : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : (RayCohookChain.cutoffRhoOfHook t hcut).depth < f.depth) :
    ∃ q : (RayCohookChain.prefixOfHookAt t hcut).z (Fin.last n) ⟶ Z,
      q ≠ 0 ∧ ¬IsIso q ∧
        ((RayCohookChain.prefixOfHookAt t hcut).sigma (Fin.last n)).1 ≫ q =
          f.1 := by
  obtain ⟨q, hqne, hq⟩ :=
    RayCohookChain.exists_factorThroughCutoffSigma_of_hook_isEfficientAt
      t hcut ht f g b hfactor hpeak hg hfdepth
  refine ⟨q, hqne, ?_, hq⟩
  intro hqIso
  letI : IsIso q := hqIso
  apply (RayCohookChain.cutoffOfHook_valley_incomparable t hcut).2
  refine ⟨b ≫ inv q, ?_⟩
  calc
    (RayCohookChain.cutoffRhoOfHook t hcut).1 ≫ (b ≫ inv q) =
        ((RayCohookChain.cutoffRhoOfHook t hcut).1 ≫ b) ≫ inv q := by
      rw [Category.assoc]
    _ = f.1 ≫ inv q := by rw [hfactor]
    _ = (((RayCohookChain.prefixOfHookAt t hcut).sigma
          (Fin.last n)).1 ≫ q) ≫ inv q :=
      congrArg (fun r ↦ r ≫ inv q) hq.symm
    _ = ((RayCohookChain.prefixOfHookAt t hcut).sigma
          (Fin.last n)).1 := by
      simp

/-- Efficiency of one fixed hook tackle supplies the positive-length factor
path used by its cohook-shaped Figure 55 cutoff. -/
theorem exists_nonidentityPresentation_factorThroughCutoffSigma_of_hook_isEfficientAt
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C] {m n : ℕ}
    (t : RayHookTackle (C := C) m) (hcut : n < m) {y X Z : C}
    (ht : (RayTackle.hook m t).IsEfficientAt y)
    (f : NonzeroHom
      ((RayCohookChain.prefixOfHookAt t hcut).x (Fin.last (n + 1))) Z)
    (g : NonzeroHom X Z)
    (b : t.z ((Fin.last n).castLE hcut).succ ⟶ Z)
    (hfactor : (RayCohookChain.cutoffRhoOfHook t hcut).1 ≫ b = f.1)
    (hpeak : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : (RayCohookChain.cutoffRhoOfHook t hcut).depth < f.depth) :
    ∃ q : NonzeroHom
        ((RayCohookChain.prefixOfHookAt t hcut).z (Fin.last n)) Z,
      ¬IsIso q.1 ∧
        ∃ p : RayPathPresentation q.toMorphismFrom,
          p.path.length ≠ 0 ∧
            ((RayCohookChain.prefixOfHookAt t hcut).sigma
                (Fin.last n)).1 ≫ q.1 = f.1 := by
  obtain ⟨q, hqne, hqNoniso, hq⟩ :=
    RayCohookChain.exists_noniso_factorThroughCutoffSigma_of_hook_isEfficientAt
      t hcut ht f g b hfactor hpeak hg hfdepth
  let qHom : NonzeroHom
      ((RayCohookChain.prefixOfHookAt t hcut).z (Fin.last n)) Z :=
    ⟨q, hqne⟩
  obtain ⟨p, hp⟩ := qHom.exists_presentation_length_ne_zero hqNoniso
  exact ⟨qHom, hqNoniso, p, hp, hq⟩

end RayCohookChain

namespace Figure55PathState

/-- A cohook cutoff consumes the leading half of a Figure 55 path state and
the other contour side's initial arrow.  The state supplies the new peak,
and efficiency returns the next positive-length factor through `sigma_n`. -/
theorem exists_nonidentityFactorThroughCutoffSigma
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m n : ℕ} (tackle : RayCohookTackle (C := C) m)
    (hcut : n < m) {y Z : C} {w : RayVertex C}
    {p q r : Quiver.Path (RayVertex.mk Z) w}
    (hstate : Figure55PathState p q r)
    (lead : Quiver.Path (RayVertex.mk Z)
      (RayVertex.mk ((RayCohookChain.prefixAt tackle hcut).x
        (Fin.last (n + 1)))))
    (tail : Quiver.Path
      (RayVertex.mk ((RayCohookChain.prefixAt tackle hcut).x
        (Fin.last (n + 1)))) w)
    (hr : r = lead.comp tail) (htail : tail.length ≠ 0)
    (dq : PathEndpointDecomposition q)
    (ht : (RayTackle.cohook m tackle).IsEfficientAt y)
    (b : tackle.z ((Fin.last n).castLE hcut).succ ⟶ Z)
    (hfactor : (RayCohookChain.cutoffRho tackle hcut).1 ≫ b =
      (hstate.leadNonzeroHom lead tail hr).1)
    (hfdepth : (RayCohookChain.cutoffRho tackle hcut).depth <
      (hstate.leadNonzeroHom lead tail hr).depth)
    (hone : 1 < (hstate.leadNonzeroHom lead tail hr).depth) :
    ∃ factor : NonzeroHom
        ((RayCohookChain.prefixAt tackle hcut).z (Fin.last n)) Z,
      ¬IsIso factor.1 ∧
        ∃ path : RayPathPresentation factor.toMorphismFrom,
          path.path.length ≠ 0 ∧
            ((RayCohookChain.prefixAt tackle hcut).sigma
                (Fin.last n)).1 ≫ factor.1 =
              (hstate.leadNonzeroHom lead tail hr).1 := by
  apply RayCohookChain.exists_nonidentityPresentation_factorThroughCutoffSigma_of_isEfficientAt
      tackle hcut ht (hstate.leadNonzeroHom lead tail hr)
        dq.toInitial.rayArrowNonzeroHom b hfactor
  · exact hstate.targetIncomparable_lead_rightInitial
      lead tail hr htail dq hone
  · exact dq.initial.property
  · exact hfdepth

/-- A cohook-shaped cutoff of one fixed efficient hook tackle consumes the
leading half of a Figure 55 state.  The state supplies the new peak and the
cross-orientation efficiency theorem supplies a positive-length factor
through the retained `sigma_n`. -/
theorem exists_nonidentityFactorThroughCutoffSigmaOfHook
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m n : ℕ} (tackle : RayHookTackle (C := C) m)
    (hcut : n < m) {y Z : C} {w : RayVertex C}
    {p q r : Quiver.Path (RayVertex.mk Z) w}
    (hstate : Figure55PathState p q r)
    (lead : Quiver.Path (RayVertex.mk Z)
      (RayVertex.mk ((RayCohookChain.prefixOfHookAt tackle hcut).x
        (Fin.last (n + 1)))))
    (tail : Quiver.Path
      (RayVertex.mk ((RayCohookChain.prefixOfHookAt tackle hcut).x
        (Fin.last (n + 1)))) w)
    (hr : r = lead.comp tail) (htail : tail.length ≠ 0)
    (dq : PathEndpointDecomposition q)
    (ht : (RayTackle.hook m tackle).IsEfficientAt y)
    (b : tackle.z ((Fin.last n).castLE hcut).succ ⟶ Z)
    (hfactor : (RayCohookChain.cutoffRhoOfHook tackle hcut).1 ≫ b =
      (hstate.leadNonzeroHom lead tail hr).1)
    (hfdepth : (RayCohookChain.cutoffRhoOfHook tackle hcut).depth <
      (hstate.leadNonzeroHom lead tail hr).depth)
    (hone : 1 < (hstate.leadNonzeroHom lead tail hr).depth) :
    ∃ factor : NonzeroHom
        ((RayCohookChain.prefixOfHookAt tackle hcut).z (Fin.last n)) Z,
      ¬IsIso factor.1 ∧
        ∃ path : RayPathPresentation factor.toMorphismFrom,
          path.path.length ≠ 0 ∧
            ((RayCohookChain.prefixOfHookAt tackle hcut).sigma
                (Fin.last n)).1 ≫ factor.1 =
              (hstate.leadNonzeroHom lead tail hr).1 := by
  apply RayCohookChain.exists_nonidentityPresentation_factorThroughCutoffSigma_of_hook_isEfficientAt
      tackle hcut ht (hstate.leadNonzeroHom lead tail hr)
        dq.toInitial.rayArrowNonzeroHom b hfactor
  · exact hstate.targetIncomparable_lead_rightInitial
      lead tail hr htail dq hone
  · exact dq.initial.property
  · exact hfdepth

/-- A hook cutoff consumes the trailing half of a Figure 55 path state and
the other contour side's final arrow.  The state supplies the new valley,
and efficiency returns the next positive-length factor through `rho_n`. -/
theorem exists_nonidentityFactorThroughCutoffRho
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m n : ℕ} (tackle : RayHookTackle (C := C) m)
    (hcut : n < m) {y X : C} {w : RayVertex C}
    {p q r : Quiver.Path w (RayVertex.mk X)}
    (hstate : Figure55PathState p q r)
    (before : Quiver.Path w
      (RayVertex.mk ((RayHookChain.prefixAt tackle hcut).z
        (Fin.last n))))
    (rest : Quiver.Path
      (RayVertex.mk ((RayHookChain.prefixAt tackle hcut).z
        (Fin.last n))) (RayVertex.mk X))
    (hr : r = before.comp rest) (hbefore : before.length ≠ 0)
    (dq : PathEndpointDecomposition q)
    (ht : (RayTackle.hook m tackle).IsEfficientAt y)
    (a : X ⟶ tackle.x ((Fin.last n).castLE hcut).succ)
    (hfactor : a ≫ (RayHookChain.cutoffSigma tackle hcut).1 =
      (hstate.restNonzeroHom before rest hr).1)
    (hfdepth : (RayHookChain.cutoffSigma tackle hcut).depth <
      (hstate.restNonzeroHom before rest hr).depth)
    (hone : 1 < (hstate.restNonzeroHom before rest hr).depth) :
    ∃ factor : NonzeroHom X
        ((RayHookChain.prefixAt tackle hcut).x (Fin.last n)),
      ¬IsIso factor.1 ∧
        ∃ path : RayPathPresentation factor.toMorphismFrom,
          path.path.length ≠ 0 ∧
            factor.1 ≫
                ((RayHookChain.prefixAt tackle hcut).rho (Fin.last n)).1 =
              (hstate.restNonzeroHom before rest hr).1 := by
  apply RayHookChain.exists_nonidentityPresentation_factorThroughCutoffRho_of_isEfficientAt
      tackle hcut ht (hstate.restNonzeroHom before rest hr)
        dq.toFinal.rayArrowNonzeroHom a hfactor
  · exact hstate.sourceIncomparable_rest_rightFinal
      before rest hr hbefore dq hone
  · exact dq.final.property
  · exact hfdepth

/-- A hook-shaped cutoff of one fixed efficient cohook tackle consumes the
trailing half of a Figure 55 state.  The state supplies the new valley and
the cross-orientation efficiency theorem supplies a positive-length factor
through the retained `rho_n`. -/
theorem exists_nonidentityFactorThroughCutoffRhoOfCohook
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m n : ℕ} (tackle : RayCohookTackle (C := C) m)
    (hcut : n < m) {y X : C} {w : RayVertex C}
    {p q r : Quiver.Path w (RayVertex.mk X)}
    (hstate : Figure55PathState p q r)
    (before : Quiver.Path w
      (RayVertex.mk ((RayHookChain.prefixOfCohookAt tackle hcut).z
        (Fin.last n))))
    (rest : Quiver.Path
      (RayVertex.mk ((RayHookChain.prefixOfCohookAt tackle hcut).z
        (Fin.last n))) (RayVertex.mk X))
    (hr : r = before.comp rest) (hbefore : before.length ≠ 0)
    (dq : PathEndpointDecomposition q)
    (ht : (RayTackle.cohook m tackle).IsEfficientAt y)
    (a : X ⟶ tackle.x ((Fin.last n).castLE hcut).succ.castSucc)
    (hfactor : a ≫ (RayHookChain.cutoffSigmaOfCohook tackle hcut).1 =
      (hstate.restNonzeroHom before rest hr).1)
    (hfdepth : (RayHookChain.cutoffSigmaOfCohook tackle hcut).depth <
      (hstate.restNonzeroHom before rest hr).depth)
    (hone : 1 < (hstate.restNonzeroHom before rest hr).depth) :
    ∃ factor : NonzeroHom X
        ((RayHookChain.prefixOfCohookAt tackle hcut).x (Fin.last n)),
      ¬IsIso factor.1 ∧
        ∃ path : RayPathPresentation factor.toMorphismFrom,
          path.path.length ≠ 0 ∧
            factor.1 ≫
                ((RayHookChain.prefixOfCohookAt tackle hcut).rho
                  (Fin.last n)).1 =
              (hstate.restNonzeroHom before rest hr).1 := by
  apply RayHookChain.exists_nonidentityPresentation_factorThroughCutoffRho_of_cohook_isEfficientAt
      tackle hcut ht (hstate.restNonzeroHom before rest hr)
        dq.toFinal.rayArrowNonzeroHom a hfactor
  · exact hstate.sourceIncomparable_rest_rightFinal
      before rest hr hbefore dq hone
  · exact dq.final.property
  · exact hfdepth

/-- The complete cohook-to-hook local state transition.  Present the retained
`sigma_n` and the new positive-length factor, concatenate their paths, and
replace the old lead by that equal composite inside the Figure 55 state. -/
theorem exists_nextState_of_cohookCutoff
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m n : ℕ} (tackle : RayCohookTackle (C := C) m)
    (hcut : n < m) {y Z : C} {w : RayVertex C}
    {p q r : Quiver.Path (RayVertex.mk Z) w}
    (hstate : Figure55PathState p q r)
    (lead : Quiver.Path (RayVertex.mk Z)
      (RayVertex.mk ((RayCohookChain.prefixAt tackle hcut).x
        (Fin.last (n + 1)))))
    (tail : Quiver.Path
      (RayVertex.mk ((RayCohookChain.prefixAt tackle hcut).x
        (Fin.last (n + 1)))) w)
    (hr : r = lead.comp tail) (htail : tail.length ≠ 0)
    (dq : PathEndpointDecomposition q)
    (ht : (RayTackle.cohook m tackle).IsEfficientAt y)
    (b : tackle.z ((Fin.last n).castLE hcut).succ ⟶ Z)
    (hfactor : (RayCohookChain.cutoffRho tackle hcut).1 ≫ b =
      (hstate.leadNonzeroHom lead tail hr).1)
    (hfdepth : (RayCohookChain.cutoffRho tackle hcut).depth <
      (hstate.leadNonzeroHom lead tail hr).depth)
    (hone : 1 < (hstate.leadNonzeroHom lead tail hr).depth) :
    ∃ factor : NonzeroHom
        ((RayCohookChain.prefixAt tackle hcut).z (Fin.last n)) Z,
      ¬IsIso factor.1 ∧
        ∃ factorPath : RayPathPresentation factor.toMorphismFrom,
          factorPath.path.length ≠ 0 ∧
            ∃ sigmaPath : RayPathPresentation
              (((RayCohookChain.prefixAt tackle hcut).sigma
                (Fin.last n)).toMorphismFrom),
              ((RayCohookChain.prefixAt tackle hcut).sigma
                  (Fin.last n)).1 ≫ factor.1 =
                (hstate.leadNonzeroHom lead tail hr).1 ∧
              Figure55PathState p q
                ((factorPath.path.comp sigmaPath.path).comp tail) := by
  obtain ⟨factor, hfactorNoniso, factorPath, hfactorPath, hcompose⟩ :=
    hstate.exists_nonidentityFactorThroughCutoffSigma tackle hcut
      lead tail hr htail dq ht b hfactor hfdepth hone
  obtain ⟨sigmaPath⟩ := HasFiniteRayPathDepth.presentation_nonempty
    (((RayCohookChain.prefixAt tackle hcut).sigma
      (Fin.last n)).toMorphismFrom)
  have hlast : (Fin.last n).succ = Fin.last (n + 1) := by
    apply Fin.ext
    rfl
  cases hlast
  have hmap : rayPathMap lead =
      rayPathMap (factorPath.path.comp sigmaPath.path) := by
    calc
      rayPathMap lead =
          (hstate.leadNonzeroHom lead tail hr).1 := rfl
      _ = ((RayCohookChain.prefixAt tackle hcut).sigma
            (Fin.last n)).1 ≫ factor.1 := hcompose.symm
      _ = rayPathMap sigmaPath.path ≫ rayPathMap factorPath.path := by
        rw [sigmaPath.map_eq, factorPath.map_eq]
      _ = rayPathMap (factorPath.path.comp sigmaPath.path) := by
        exact (LinearPathCategory.pathMap_comp
          RayVertex.obj rayArrowMorphism factorPath.path sigmaPath.path).symm
  have hstateOld : Figure55PathState p q
      ((Quiver.Path.nil.comp lead).comp tail) := by
    simpa only [Quiver.Path.nil_comp, ← hr] using hstate
  have hstateNext : Figure55PathState p q
      ((factorPath.path.comp sigmaPath.path).comp tail) := by
    convert hstateOld.replaceInner p q Quiver.Path.nil lead
        (factorPath.path.comp sigmaPath.path) tail hmap
          (by simpa using Nat.pos_of_ne_zero htail) using 1 <;> simp
  exact ⟨factor, hfactorNoniso, factorPath, hfactorPath,
    sigmaPath, hcompose, hstateNext⟩

/-- The cohook-shaped local state transition inside one fixed efficient hook
tackle.  It has the same path replacement as a cohook cutoff, but its
efficiency comparison is against the original hook tackle. -/
theorem exists_nextState_of_cohookCutoffOfHook
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m n : ℕ} (tackle : RayHookTackle (C := C) m)
    (hcut : n < m) {y Z : C} {w : RayVertex C}
    {p q r : Quiver.Path (RayVertex.mk Z) w}
    (hstate : Figure55PathState p q r)
    (lead : Quiver.Path (RayVertex.mk Z)
      (RayVertex.mk ((RayCohookChain.prefixOfHookAt tackle hcut).x
        (Fin.last (n + 1)))))
    (tail : Quiver.Path
      (RayVertex.mk ((RayCohookChain.prefixOfHookAt tackle hcut).x
        (Fin.last (n + 1)))) w)
    (hr : r = lead.comp tail) (htail : tail.length ≠ 0)
    (dq : PathEndpointDecomposition q)
    (ht : (RayTackle.hook m tackle).IsEfficientAt y)
    (b : tackle.z ((Fin.last n).castLE hcut).succ ⟶ Z)
    (hfactor : (RayCohookChain.cutoffRhoOfHook tackle hcut).1 ≫ b =
      (hstate.leadNonzeroHom lead tail hr).1)
    (hfdepth : (RayCohookChain.cutoffRhoOfHook tackle hcut).depth <
      (hstate.leadNonzeroHom lead tail hr).depth)
    (hone : 1 < (hstate.leadNonzeroHom lead tail hr).depth) :
    ∃ factor : NonzeroHom
        ((RayCohookChain.prefixOfHookAt tackle hcut).z (Fin.last n)) Z,
      ¬IsIso factor.1 ∧
        ∃ factorPath : RayPathPresentation factor.toMorphismFrom,
          factorPath.path.length ≠ 0 ∧
            ∃ sigmaPath : RayPathPresentation
              (((RayCohookChain.prefixOfHookAt tackle hcut).sigma
                (Fin.last n)).toMorphismFrom),
              ((RayCohookChain.prefixOfHookAt tackle hcut).sigma
                  (Fin.last n)).1 ≫ factor.1 =
                (hstate.leadNonzeroHom lead tail hr).1 ∧
              Figure55PathState p q
                ((factorPath.path.comp sigmaPath.path).comp tail) := by
  obtain ⟨factor, hfactorNoniso, factorPath, hfactorPath, hcompose⟩ :=
    hstate.exists_nonidentityFactorThroughCutoffSigmaOfHook tackle hcut
      lead tail hr htail dq ht b hfactor hfdepth hone
  obtain ⟨sigmaPath⟩ := HasFiniteRayPathDepth.presentation_nonempty
    (((RayCohookChain.prefixOfHookAt tackle hcut).sigma
      (Fin.last n)).toMorphismFrom)
  have hlast : (Fin.last n).succ = Fin.last (n + 1) := by
    apply Fin.ext
    rfl
  cases hlast
  have hmap : rayPathMap lead =
      rayPathMap (factorPath.path.comp sigmaPath.path) := by
    calc
      rayPathMap lead =
          (hstate.leadNonzeroHom lead tail hr).1 := rfl
      _ = ((RayCohookChain.prefixOfHookAt tackle hcut).sigma
            (Fin.last n)).1 ≫ factor.1 := hcompose.symm
      _ = rayPathMap sigmaPath.path ≫ rayPathMap factorPath.path := by
        rw [sigmaPath.map_eq, factorPath.map_eq]
      _ = rayPathMap (factorPath.path.comp sigmaPath.path) := by
        exact (LinearPathCategory.pathMap_comp
          RayVertex.obj rayArrowMorphism factorPath.path sigmaPath.path).symm
  have hstateOld : Figure55PathState p q
      ((Quiver.Path.nil.comp lead).comp tail) := by
    simpa only [Quiver.Path.nil_comp, ← hr] using hstate
  have hstateNext : Figure55PathState p q
      ((factorPath.path.comp sigmaPath.path).comp tail) := by
    convert hstateOld.replaceInner p q Quiver.Path.nil lead
        (factorPath.path.comp sigmaPath.path) tail hmap
          (by simpa using Nat.pos_of_ne_zero htail) using 1 <;> simp
  exact ⟨factor, hfactorNoniso, factorPath, hfactorPath,
    sigmaPath, hcompose, hstateNext⟩

/-- The complete hook-to-cohook local state transition.  Present the retained
`rho_n`, concatenate it with the new positive-length factor path, and replace
the old rest by that equal composite. -/
theorem exists_nextState_of_hookCutoff
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m n : ℕ} (tackle : RayHookTackle (C := C) m)
    (hcut : n < m) {y X : C} {w : RayVertex C}
    {p q r : Quiver.Path w (RayVertex.mk X)}
    (hstate : Figure55PathState p q r)
    (before : Quiver.Path w
      (RayVertex.mk ((RayHookChain.prefixAt tackle hcut).z
        (Fin.last n))))
    (rest : Quiver.Path
      (RayVertex.mk ((RayHookChain.prefixAt tackle hcut).z
        (Fin.last n))) (RayVertex.mk X))
    (hr : r = before.comp rest) (hbefore : before.length ≠ 0)
    (dq : PathEndpointDecomposition q)
    (ht : (RayTackle.hook m tackle).IsEfficientAt y)
    (a : X ⟶ tackle.x ((Fin.last n).castLE hcut).succ)
    (hfactor : a ≫ (RayHookChain.cutoffSigma tackle hcut).1 =
      (hstate.restNonzeroHom before rest hr).1)
    (hfdepth : (RayHookChain.cutoffSigma tackle hcut).depth <
      (hstate.restNonzeroHom before rest hr).depth)
    (hone : 1 < (hstate.restNonzeroHom before rest hr).depth) :
    ∃ factor : NonzeroHom X
        ((RayHookChain.prefixAt tackle hcut).x (Fin.last n)),
      ¬IsIso factor.1 ∧
        ∃ factorPath : RayPathPresentation factor.toMorphismFrom,
          factorPath.path.length ≠ 0 ∧
            ∃ rhoPath : RayPathPresentation
              (((RayHookChain.prefixAt tackle hcut).rho
                (Fin.last n)).toMorphismFrom),
              factor.1 ≫
                  ((RayHookChain.prefixAt tackle hcut).rho (Fin.last n)).1 =
                (hstate.restNonzeroHom before rest hr).1 ∧
              Figure55PathState p q
                (before.comp (rhoPath.path.comp factorPath.path)) := by
  obtain ⟨factor, hfactorNoniso, factorPath, hfactorPath, hcompose⟩ :=
    hstate.exists_nonidentityFactorThroughCutoffRho tackle hcut
      before rest hr hbefore dq ht a hfactor hfdepth hone
  obtain ⟨rhoPath⟩ := HasFiniteRayPathDepth.presentation_nonempty
    (((RayHookChain.prefixAt tackle hcut).rho
      (Fin.last n)).toMorphismFrom)
  have hmap : rayPathMap rest =
      rayPathMap (rhoPath.path.comp factorPath.path) := by
    calc
      rayPathMap rest =
          (hstate.restNonzeroHom before rest hr).1 := rfl
      _ = factor.1 ≫
          ((RayHookChain.prefixAt tackle hcut).rho (Fin.last n)).1 :=
        hcompose.symm
      _ = rayPathMap factorPath.path ≫ rayPathMap rhoPath.path := by
        rw [factorPath.map_eq, rhoPath.map_eq]
      _ = rayPathMap (rhoPath.path.comp factorPath.path) := by
        exact (LinearPathCategory.pathMap_comp
          RayVertex.obj rayArrowMorphism rhoPath.path factorPath.path).symm
  have hstateOld : Figure55PathState p q
      ((before.comp rest).comp Quiver.Path.nil) := by
    simpa only [Quiver.Path.comp_nil, ← hr] using hstate
  have hstateNext : Figure55PathState p q
      (before.comp (rhoPath.path.comp factorPath.path)) := by
    simpa only [Quiver.Path.comp_nil] using
      hstateOld.replaceInner p q before rest
        (rhoPath.path.comp factorPath.path) Quiver.Path.nil hmap
          (by simpa using Nat.pos_of_ne_zero hbefore)
  exact ⟨factor, hfactorNoniso, factorPath, hfactorPath,
    rhoPath, hcompose, hstateNext⟩

/-- The hook-shaped local state transition inside one fixed efficient cohook
tackle.  It has the same path replacement as a hook cutoff, but its
efficiency comparison is against the original cohook tackle. -/
theorem exists_nextState_of_hookCutoffOfCohook
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m n : ℕ} (tackle : RayCohookTackle (C := C) m)
    (hcut : n < m) {y X : C} {w : RayVertex C}
    {p q r : Quiver.Path w (RayVertex.mk X)}
    (hstate : Figure55PathState p q r)
    (before : Quiver.Path w
      (RayVertex.mk ((RayHookChain.prefixOfCohookAt tackle hcut).z
        (Fin.last n))))
    (rest : Quiver.Path
      (RayVertex.mk ((RayHookChain.prefixOfCohookAt tackle hcut).z
        (Fin.last n))) (RayVertex.mk X))
    (hr : r = before.comp rest) (hbefore : before.length ≠ 0)
    (dq : PathEndpointDecomposition q)
    (ht : (RayTackle.cohook m tackle).IsEfficientAt y)
    (a : X ⟶ tackle.x ((Fin.last n).castLE hcut).succ.castSucc)
    (hfactor : a ≫ (RayHookChain.cutoffSigmaOfCohook tackle hcut).1 =
      (hstate.restNonzeroHom before rest hr).1)
    (hfdepth : (RayHookChain.cutoffSigmaOfCohook tackle hcut).depth <
      (hstate.restNonzeroHom before rest hr).depth)
    (hone : 1 < (hstate.restNonzeroHom before rest hr).depth) :
    ∃ factor : NonzeroHom X
        ((RayHookChain.prefixOfCohookAt tackle hcut).x (Fin.last n)),
      ¬IsIso factor.1 ∧
        ∃ factorPath : RayPathPresentation factor.toMorphismFrom,
          factorPath.path.length ≠ 0 ∧
            ∃ rhoPath : RayPathPresentation
              (((RayHookChain.prefixOfCohookAt tackle hcut).rho
                (Fin.last n)).toMorphismFrom),
              factor.1 ≫
                  ((RayHookChain.prefixOfCohookAt tackle hcut).rho
                    (Fin.last n)).1 =
                (hstate.restNonzeroHom before rest hr).1 ∧
              Figure55PathState p q
                (before.comp (rhoPath.path.comp factorPath.path)) := by
  obtain ⟨factor, hfactorNoniso, factorPath, hfactorPath, hcompose⟩ :=
    hstate.exists_nonidentityFactorThroughCutoffRhoOfCohook tackle hcut
      before rest hr hbefore dq ht a hfactor hfdepth hone
  obtain ⟨rhoPath⟩ := HasFiniteRayPathDepth.presentation_nonempty
    (((RayHookChain.prefixOfCohookAt tackle hcut).rho
      (Fin.last n)).toMorphismFrom)
  have hmap : rayPathMap rest =
      rayPathMap (rhoPath.path.comp factorPath.path) := by
    calc
      rayPathMap rest =
          (hstate.restNonzeroHom before rest hr).1 := rfl
      _ = factor.1 ≫
          ((RayHookChain.prefixOfCohookAt tackle hcut).rho
            (Fin.last n)).1 := hcompose.symm
      _ = rayPathMap factorPath.path ≫ rayPathMap rhoPath.path := by
        rw [factorPath.map_eq, rhoPath.map_eq]
      _ = rayPathMap (rhoPath.path.comp factorPath.path) := by
        exact (LinearPathCategory.pathMap_comp
          RayVertex.obj rayArrowMorphism rhoPath.path factorPath.path).symm
  have hstateOld : Figure55PathState p q
      ((before.comp rest).comp Quiver.Path.nil) := by
    simpa only [Quiver.Path.comp_nil, ← hr] using hstate
  have hstateNext : Figure55PathState p q
      (before.comp (rhoPath.path.comp factorPath.path)) := by
    simpa only [Quiver.Path.comp_nil] using
      hstateOld.replaceInner p q before rest
        (rhoPath.path.comp factorPath.path) Quiver.Path.nil hmap
          (by simpa using Nat.pos_of_ne_zero hbefore)
  exact ⟨factor, hfactorNoniso, factorPath, hfactorPath,
    rhoPath, hcompose, hstateNext⟩

end Figure55PathState

end LargeIndecomposable
