module

public import LargeIndecomposable.RayCategories.Contours.EssentialPathContour
public import LargeIndecomposable.RayCategories.Contours.RayPathInterlacement
public import LargeIndecomposable.RayCategories.RoiterVanishing.RayTackleExtension

@[expose] public section

/-!
# Efficient ray hooks in essential contours

Connect the hook and cohook of a BGRS tackle to the reversed irreducible
quiver.  Because BGRS composes paths from left to right, its prefix before an
efficient hook becomes the suffix after the corresponding reversed-quiver
arrow.  This file also isolates the separate quiver-prefix improvement
interface used by the initial-arrow contour-correction route.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace RayHookTackle

/-- The reversed irreducible-quiver arrow represented by the last hook of a
hook tackle. -/
def lastArrow {m : ℕ} (t : RayHookTackle (C := C) m) :
    (RayVertex.mk (t.z (Fin.last m)) : RayVertex C) ⟶
      RayVertex.mk (t.x (Fin.last m)) :=
  ⟨(t.rho (Fin.last m)).1, t.last_irreducible⟩

@[simp]
theorem rayArrowMorphism_lastArrow {m : ℕ}
    (t : RayHookTackle (C := C) m) :
    rayArrowMorphism t.lastArrow = (t.rho (Fin.last m)).1 :=
  rfl

@[simp]
theorem rayPathMap_lastArrow_toPath {m : ℕ}
    (t : RayHookTackle (C := C) m) :
    rayPathMap t.lastArrow.toPath = (t.rho (Fin.last m)).1 := by
  calc
    rayPathMap t.lastArrow.toPath = rayArrowMorphism t.lastArrow := by
      exact rayPathMap_toPath t.lastArrow
    _ = (t.rho (Fin.last m)).1 := rfl

end RayHookTackle

namespace RayCohookTackle

/-- The reversed irreducible-quiver arrow represented by the last cohook of a
cohook tackle. -/
def lastArrow {m : ℕ} (t : RayCohookTackle (C := C) m) :
    (RayVertex.mk (t.z (Fin.last m)) : RayVertex C) ⟶
      RayVertex.mk (t.x (Fin.last m).succ) :=
  ⟨(t.sigma (Fin.last m)).1, t.last_irreducible⟩

@[simp]
theorem rayArrowMorphism_lastArrow {m : ℕ}
    (t : RayCohookTackle (C := C) m) :
    rayArrowMorphism t.lastArrow = (t.sigma (Fin.last m)).1 :=
  rfl

@[simp]
theorem rayPathMap_lastArrow_toPath {m : ℕ}
    (t : RayCohookTackle (C := C) m) :
    rayPathMap t.lastArrow.toPath = (t.sigma (Fin.last m)).1 := by
  calc
    rayPathMap t.lastArrow.toPath = rayArrowMorphism t.lastArrow := by
      exact rayPathMap_toPath t.lastArrow
    _ = (t.sigma (Fin.last m)).1 := rfl

end RayCohookTackle

/-- An occurrence in a reversed ray path evaluates as the suffix, followed by
the selected category arrow, followed by the prefix. -/
theorem rayPathMap_eq_after_comp_arrow_comp_before_of_occurrence
    (a : BundledQuiverArrow (RayVertex C))
    {x z : RayVertex C} (p : Quiver.Path x z)
    (o : BundledArrowOccurrence a p) :
    rayPathMap p =
      (rayPathMap o.after ≫ rayArrowMorphism (a.2.2)) ≫
        rayPathMap o.before := by
  calc
    rayPathMap p =
        rayPathMap ((o.before.comp (a.2.2).toPath).comp o.after) :=
      congrArg (fun s => rayPathMap s) o.path_eq
    _ = (rayPathMap o.after ≫ rayArrowMorphism (a.2.2)) ≫
        rayPathMap o.before := by
      dsimp only [rayPathMap]
      rw [LinearPathCategory.pathMap_comp,
        LinearPathCategory.pathMap_comp]
      simp [Quiver.Hom.toPath, Category.assoc]

/-- A nonzero path containing a selected arrow has a nonzero prefix
evaluation. -/
theorem rayPathMap_before_ne_zero_of_occurrence
    (a : BundledQuiverArrow (RayVertex C))
    {x z : RayVertex C} (p : Quiver.Path x z)
    (o : BundledArrowOccurrence a p) (hp : rayPathMap p ≠ 0) :
    rayPathMap o.before ≠ 0 := by
  intro hzero
  apply hp
  rw [rayPathMap_eq_after_comp_arrow_comp_before_of_occurrence a p o,
    hzero]
  simp

/-- The suffix followed by the selected arrow also remains nonzero inside a
nonzero ray path. -/
theorem rayPathMap_after_comp_arrow_ne_zero_of_occurrence
    (a : BundledQuiverArrow (RayVertex C))
    {x z : RayVertex C} (p : Quiver.Path x z)
    (o : BundledArrowOccurrence a p) (hp : rayPathMap p ≠ 0) :
    rayPathMap o.after ≫ rayArrowMorphism (a.2.2) ≠ 0 := by
  intro hzero
  apply hp
  rw [rayPathMap_eq_after_comp_arrow_comp_before_of_occurrence a p o,
    hzero]
  simp

/-- The selected arrow followed, in category order, by the quiver prefix also
remains nonzero inside a nonzero ray path. -/
theorem rayPathMap_before_comp_arrow_ne_zero_of_occurrence
    (a : BundledQuiverArrow (RayVertex C))
    {x z : RayVertex C} (p : Quiver.Path x z)
    (o : BundledArrowOccurrence a p) (hp : rayPathMap p ≠ 0) :
    rayPathMap (o.before.comp (a.2.2).toPath) ≠ 0 := by
  have hlead : rayPathMap (o.before.comp (a.2.2).toPath) =
      rayArrowMorphism (a.2.2) ≫ rayPathMap o.before := by
    dsimp only [rayPathMap]
    rw [LinearPathCategory.pathMap_comp]
    simp [Quiver.Hom.toPath]
  intro hzero
  apply hp
  rw [rayPathMap_eq_after_comp_arrow_comp_before_of_occurrence a p o,
    Category.assoc, ← hlead, hzero]
  simp

namespace BundledArrowOccurrence

/-- The category morphism represented by the selected arrow together with
its quiver prefix.  Reversal of the ray quiver makes it a morphism from the
arrow target object to the ambient path source object. -/
def prefixNonzeroHom (a : BundledQuiverArrow (RayVertex C))
    {x z : RayVertex C} (p : Quiver.Path x z)
    (o : BundledArrowOccurrence a p) (hp : rayPathMap p ≠ 0) :
    NonzeroHom (a.2.1).obj x.obj :=
  ⟨rayPathMap (o.before.comp (a.2.2).toPath),
    rayPathMap_before_comp_arrow_ne_zero_of_occurrence a p o hp⟩

/-- A selected arrow beneath a nonidentity quiver prefix represents a
category morphism of depth strictly greater than one. -/
theorem one_lt_prefixNonzeroHom_depth
    [HasFiniteRayPathDepth C]
    (a : BundledQuiverArrow (RayVertex C))
    {x z : RayVertex C} (p : Quiver.Path x z)
    (o : BundledArrowOccurrence a p) (hp : rayPathMap p ≠ 0)
    (hbefore : o.before.length ≠ 0) :
    1 < (o.prefixNonzeroHom a p hp).depth := by
  let lead : Quiver.Path x (a.2.1) :=
    o.before.comp (a.2.2).toPath
  have hlead : rayPathMap lead ≠ 0 :=
    rayPathMap_before_comp_arrow_ne_zero_of_occurrence a p o hp
  have hbound := rayPath_length_le_depth lead hlead
  have hlength : 2 ≤ lead.length := by
    simp [lead]
    omega
  have heq : rayPathMorphism lead hlead =
      (o.prefixNonzeroHom a p hp).toMorphismFrom := by
    apply NonzeroMorphismFrom.ext rfl
    simp [lead]
  have hdepth : lead.length ≤ (o.prefixNonzeroHom a p hp).depth := by
    change lead.length ≤ rayMorphismDepth
      (o.prefixNonzeroHom a p hp).toMorphismFrom
    rw [← heq]
    exact hbound
  omega

/-- The category morphism represented by the selected arrow together with
its quiver suffix. -/
def remainderNonzeroHom (a : BundledQuiverArrow (RayVertex C))
    {x z : RayVertex C} (p : Quiver.Path x z)
    (o : BundledArrowOccurrence a p) (hp : rayPathMap p ≠ 0) :
    NonzeroHom z.obj (a.1).obj :=
  ⟨rayPathMap ((a.2.2).toPath.comp o.after), by
    have hnonzero :=
      rayPathMap_after_comp_arrow_ne_zero_of_occurrence a p o hp
    dsimp only [rayPathMap]
    rw [LinearPathCategory.pathMap_comp]
    simpa [Quiver.Hom.toPath] using hnonzero⟩

/-- A selected arrow above a nonidentity quiver suffix represents a category
morphism of depth strictly greater than one. -/
theorem one_lt_remainderNonzeroHom_depth
    [HasFiniteRayPathDepth C]
    (a : BundledQuiverArrow (RayVertex C))
    {x z : RayVertex C} (p : Quiver.Path x z)
    (o : BundledArrowOccurrence a p) (hp : rayPathMap p ≠ 0)
    (hafter : o.after.length ≠ 0) :
    1 < (o.remainderNonzeroHom a p hp).depth := by
  let rest : Quiver.Path (a.1) z := (a.2.2).toPath.comp o.after
  have hrest : rayPathMap rest ≠ 0 :=
    (o.remainderNonzeroHom a p hp).2
  have hbound := rayPath_length_le_depth rest hrest
  have hlength : 2 ≤ rest.length := by
    simp [rest]
    omega
  have heq : rayPathMorphism rest hrest =
      (o.remainderNonzeroHom a p hp).toMorphismFrom := by
    apply NonzeroMorphismFrom.ext rfl
    simp [rest]
  have hdepth : rest.length ≤ (o.remainderNonzeroHom a p hp).depth := by
    change rest.length ≤ rayMorphismDepth
      (o.remainderNonzeroHom a p hp).toMorphismFrom
    rw [← heq]
    exact hbound
  omega

end BundledArrowOccurrence

/-- A length-zero ray path evaluates to an isomorphism. -/
theorem rayPathMap_isIso_of_length_eq_zero
    {x z : RayVertex C} (p : Quiver.Path x z) (hp : p.length = 0) :
    IsIso (rayPathMap p) := by
  cases p with
  | nil =>
      change IsIso (LinearPathCategory.pathMap RayVertex.obj
        (fun {_ _} a => rayArrowMorphism a)
        (Quiver.Path.nil : Quiver.Path x x))
      rw [LinearPathCategory.pathMap_nil]
      infer_instance
  | cons p a => simp at hp

/-- In an essential ray contour, if one side has at least two arrows then so
does the other.  Equality with a length-zero path would make the long side
invertible, while equality with a length-one path would make it irreducible;
both contradict its first-arrow factorization. -/
theorem essentialRayContour_right_length_two_le_of_left_length_two_le
    [IsFiniteRayCategory C]
    {x z : RayVertex C} (p q : Quiver.Path x z)
    (hessential : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (hpLength : 2 ≤ p.length) :
    2 ≤ q.length := by
  by_contra hqLength
  have hcases : q.length = 0 ∨ q.length = 1 := by
    omega
  rcases hcases with hqZero | hqOne
  · have hqIso : IsIso (rayPathMap q) :=
      rayPathMap_isIso_of_length_eq_zero q hqZero
    have hpIso : IsIso (rayPathMap p) := by
      rw [hessential.1.2]
      exact hqIso
    exact rayPathMap_not_isIso_of_length_ne_zero p (by omega) hpIso
  · have hqIrreducible : IsIrreducibleRayMorphism (rayPathMap q) :=
      rayPathMap_isIrreducible_of_length_eq_one q hqOne
    have hpIrreducible : IsIrreducibleRayMorphism (rayPathMap p) := by
      rw [hessential.1.2]
      exact hqIrreducible
    let dp := chosenPathInitialDecomposition p (by omega)
    have htail : dp.tail.length ≠ 0 := by
      have hlength := congrArg Quiver.Path.length dp.path_eq
      simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
        at hlength
      omega
    have hfactor : rayPathMap dp.tail ≫
        rayArrowMorphism dp.arrow = rayPathMap p := by
      calc
        rayPathMap dp.tail ≫ rayArrowMorphism dp.arrow =
            rayPathMap dp.tail ≫ rayPathMap dp.arrow.toPath := by
          rw [rayPathMap_toPath]
        _ = rayPathMap (dp.arrow.toPath.comp dp.tail) := by
          exact (LinearPathCategory.pathMap_comp
            RayVertex.obj rayArrowMorphism dp.arrow.toPath dp.tail).symm
        _ = rayPathMap p := congrArg rayPathMap dp.path_eq.symm
    rcases hpIrreducible.2.2 dp.middle.obj
        (rayPathMap dp.tail) (rayArrowMorphism dp.arrow)
        hfactor with htailIso | harrowIso
    · exact rayPathMap_not_isIso_of_length_ne_zero
        dp.tail htail htailIso
    · exact dp.arrow.property.2.1 harrowIso

/-- If a selected occurrence has a nonidentity suffix, its contour side has
length at least two, so the other side exposes both endpoint arrows. -/
theorem nonempty_pathEndpointDecomposition_right_of_occurrence_after_ne_zero
    [IsFiniteRayCategory C]
    (a : BundledQuiverArrow (RayVertex C))
    {x z : RayVertex C} (p q : Quiver.Path x z)
    (hessential : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (o : BundledArrowOccurrence a p) (hafter : o.after.length ≠ 0) :
    Nonempty (PathEndpointDecomposition q) := by
  refine ⟨chosenPathEndpointDecomposition q
    (essentialRayContour_right_length_two_le_of_left_length_two_le
      p q hessential ?_)⟩
  rw [o.path_eq]
  simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
  omega

/-- If the left side of an essential ray contour contains an arrow after a
nonidentity prefix, then the other side has at least two arrows.  Thus the
first and last arrows used in the opening step of BGRS 8.4 both exist. -/
theorem essentialRayContour_right_length_two_le_of_occurrence_before_ne_zero
    [IsFiniteRayCategory C]
    (a : BundledQuiverArrow (RayVertex C))
    {x z : RayVertex C} (p q : Quiver.Path x z)
    (hessential : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (o : BundledArrowOccurrence a p) (hbefore : o.before.length ≠ 0) :
    2 ≤ q.length := by
  have hpLength : p.length ≠ 0 := by
    rw [o.path_eq]
    simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
    omega
  by_contra hqLength
  have hcases : q.length = 0 ∨ q.length = 1 := by
    omega
  rcases hcases with hqZero | hqOne
  · have hqIso : IsIso (rayPathMap q) :=
      rayPathMap_isIso_of_length_eq_zero q hqZero
    have hpIso : IsIso (rayPathMap p) := by
      rw [hessential.1.2]
      exact hqIso
    exact rayPathMap_not_isIso_of_length_ne_zero p hpLength hpIso
  · have hqIrreducible : IsIrreducibleRayMorphism (rayPathMap q) :=
      rayPathMap_isIrreducible_of_length_eq_one q hqOne
    have hpIrreducible : IsIrreducibleRayMorphism (rayPathMap p) := by
      rw [hessential.1.2]
      exact hqIrreducible
    have hfactor :
        (rayPathMap o.after ≫ rayArrowMorphism (a.2.2)) ≫
            rayPathMap o.before = rayPathMap p :=
      (rayPathMap_eq_after_comp_arrow_comp_before_of_occurrence
        a p o).symm
    rcases hpIrreducible.2.2 (a.1).obj
        (rayPathMap o.after ≫ rayArrowMorphism (a.2.2))
        (rayPathMap o.before) hfactor with hleftIso | hbeforeIso
    · let rest : Quiver.Path (a.1) z :=
        (a.2.2).toPath.comp o.after
      have hrestLength : rest.length ≠ 0 := by
        simp [rest]
      have hrestMap : rayPathMap rest =
          rayPathMap o.after ≫ rayArrowMorphism (a.2.2) := by
        dsimp only [rest, rayPathMap]
        rw [LinearPathCategory.pathMap_comp]
        simp [Quiver.Hom.toPath]
      have hrestIso : IsIso (rayPathMap rest) := by
        rw [hrestMap]
        exact hleftIso
      exact rayPathMap_not_isIso_of_length_ne_zero
        rest hrestLength hrestIso
    · exact rayPathMap_not_isIso_of_length_ne_zero
        o.before hbefore hbeforeIso

/-- The other side of such an essential contour admits the source's normal
form `alpha * middle * zeta`, with both endpoint arrows exposed. -/
theorem nonempty_pathEndpointDecomposition_right_of_essential_occurrence
    [IsFiniteRayCategory C]
    (a : BundledQuiverArrow (RayVertex C))
    {x z : RayVertex C} (p q : Quiver.Path x z)
    (hessential : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (o : BundledArrowOccurrence a p) (hbefore : o.before.length ≠ 0) :
    Nonempty (PathEndpointDecomposition q) :=
  ⟨chosenPathEndpointDecomposition q
    (essentialRayContour_right_length_two_le_of_occurrence_before_ne_zero
      a p q hessential o hbefore)⟩

/-- No representative in the left interlacement class of an essential ray
contour can have the same initial arrow as the right path. -/
theorem initialArrow_ne_of_related_interlaced_of_essential
    [HasRayCancellation C]
    {x z : RayVertex C} {p q p' : Quiver.Path x z}
    (hessential : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (hpp' : (rayPathContourRelation (C := C)).related p p')
    (hip' : (properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p p')
    (dp' : PathInitialDecomposition p')
    (dq : PathInitialDecomposition q) :
    (⟨dp'.middle, dp'.arrow⟩ : OutgoingQuiverArrow x) ≠
      ⟨dq.middle, dq.arrow⟩ := by
  intro hcode
  apply hessential.2
  apply (properWhiskerInterlacementRelation
    (rayPathContourRelation (C := C))).trans hip'
  apply rayPaths_interlaced_of_initialDecomposition_code_eq dp' dq
  · exact (rayPathContourRelation (C := C)).trans
      ((rayPathContourRelation (C := C)).symm hpp') hessential.1
  · exact hcode

/-- Dually, no representative in the left interlacement class of an
essential ray contour can have the same final arrow as the right path. -/
theorem finalArrow_ne_of_related_interlaced_of_essential
    [HasRayCancellation C]
    {x z : RayVertex C} {p q p' : Quiver.Path x z}
    (hessential : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (hpp' : (rayPathContourRelation (C := C)).related p p')
    (hip' : (properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p p')
    (dp' : PathFinalDecomposition p')
    (dq : PathFinalDecomposition q) :
    (⟨dp'.middle, dp'.arrow⟩ : IncomingQuiverArrow z) ≠
      ⟨dq.middle, dq.arrow⟩ := by
  intro hcode
  apply hessential.2
  apply (properWhiskerInterlacementRelation
    (rayPathContourRelation (C := C))).trans hip'
  apply rayPaths_interlaced_of_finalDecomposition_code_eq dp' dq
  · exact (rayPathContourRelation (C := C)).trans
      ((rayPathContourRelation (C := C)).symm hpp') hessential.1
  · exact hcode

/-- The first factorization obstruction in the proof of BGRS 8.4.  If the
last arrow of the other contour side factored the ray represented by the
selected arrow and its suffix, replacing that inner ray beneath the
nonidentity prefix would give an interlaced representative with the same
last arrow, contradicting essentiality. -/
theorem not_exists_finalArrow_comp_eq_occurrenceRemainder
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    (a : BundledQuiverArrow (RayVertex C))
    {x z : RayVertex C} (p q : Quiver.Path x z)
    (hessential : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (o : BundledArrowOccurrence a p) (hbefore : o.before.length ≠ 0)
    (dq : PathEndpointDecomposition q) :
    ¬∃ h : dq.finalMiddle.obj ⟶ (a.1).obj,
      h ≠ 0 ∧
        rayArrowMorphism dq.final ≫ h =
          rayPathMap ((a.2.2).toPath.comp o.after) := by
  rintro ⟨h, hne, hfactor⟩
  let hHom : NonzeroHom dq.finalMiddle.obj (a.1).obj := ⟨h, hne⟩
  obtain ⟨rh⟩ :=
    HasFiniteRayPathDepth.presentation_nonempty hHom.toMorphismFrom
  let rest : Quiver.Path (a.1) z := (a.2.2).toPath.comp o.after
  let inner : Quiver.Path (a.1) z := rh.path.comp dq.final.toPath
  let p' : Quiver.Path x z := o.before.comp inner
  have hrestMap : rayPathMap rest =
      rayPathMap o.after ≫ rayArrowMorphism (a.2.2) := by
    dsimp only [rest, rayPathMap]
    rw [LinearPathCategory.pathMap_comp]
    simp [Quiver.Hom.toPath]
  have hrestNe : rayPathMap rest ≠ 0 := by
    rw [hrestMap]
    exact rayPathMap_after_comp_arrow_ne_zero_of_occurrence
      a p o hessential.1.1
  have hinnerMap : rayPathMap inner = rayArrowMorphism dq.final ≫ h := by
    calc
      rayPathMap inner =
          rayPathMap dq.final.toPath ≫ rayPathMap rh.path := by
        exact LinearPathCategory.pathMap_comp
          RayVertex.obj rayArrowMorphism rh.path dq.final.toPath
      _ = rayArrowMorphism dq.final ≫ h := by
        rw [rayPathMap_toPath, rh.map_eq]
  have hrestInner : (rayPathContourRelation (C := C)).related rest inner := by
    refine ⟨hrestNe, ?_⟩
    exact hfactor.symm.trans hinnerMap.symm
  have hpEq : p = o.before.comp rest := by
    calc
      p = (o.before.comp (a.2.2).toPath).comp o.after := o.path_eq
      _ = o.before.comp rest := by
        simp only [rest, Quiver.Path.comp_assoc]
  have houter : (rayPathContourRelation (C := C)).related
      (o.before.comp rest) (o.before.comp inner) := by
    have houterNe : rayPathMap
        ((o.before.comp rest).comp Quiver.Path.nil) ≠ 0 := by
      simpa only [Quiver.Path.comp_nil, ← hpEq] using hessential.1.1
    simpa only [Quiver.Path.comp_nil] using
      rayPathContourRelation_whisker o.before rest inner
        Quiver.Path.nil hrestInner houterNe
  have hpp' : (rayPathContourRelation (C := C)).related p p' := by
    simpa only [hpEq, p'] using houter
  have hip' : (properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p p' := by
    apply properWhiskerInterlaced_of_step
      (rayPathContourRelation (C := C))
    refine ⟨a.1, z, o.before, rest, inner, Quiver.Path.nil,
      hrestInner, ?_, ?_, ?_, ?_⟩
    · simpa only [Quiver.Path.comp_nil] using houter
    · simpa using Nat.pos_of_ne_zero hbefore
    · simpa only [Quiver.Path.comp_nil] using hpEq
    · simp [p']
  let dp' : PathFinalDecomposition p' :=
    { middle := dq.finalMiddle
      head := o.before.comp rh.path
      arrow := dq.final
      path_eq := by
        dsimp only [p', inner]
        exact (Quiver.Path.comp_assoc _ _ _).symm }
  exact (finalArrow_ne_of_related_interlaced_of_essential
    hessential hpp' hip' dp' dq.toFinal) rfl

/-- The dual endpoint obstruction.  With a nonidentity suffix, the initial
arrow of the other contour side cannot be a right factor (in categorical
composition order) of the prefix together with the selected arrow. -/
theorem not_exists_comp_initialArrow_eq_occurrencePrefix
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    (a : BundledQuiverArrow (RayVertex C))
    {x z : RayVertex C} (p q : Quiver.Path x z)
    (hessential : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (o : BundledArrowOccurrence a p) (hafter : o.after.length ≠ 0)
    (dq : PathEndpointDecomposition q) :
    ¬∃ h : (a.2.1).obj ⟶ dq.initialMiddle.obj,
      h ≠ 0 ∧
        h ≫ rayArrowMorphism dq.initial =
          rayPathMap (o.before.comp (a.2.2).toPath) := by
  rintro ⟨h, hne, hfactor⟩
  let hHom : NonzeroHom (a.2.1).obj dq.initialMiddle.obj := ⟨h, hne⟩
  obtain ⟨rh⟩ :=
    HasFiniteRayPathDepth.presentation_nonempty hHom.toMorphismFrom
  let lead : Quiver.Path x (a.2.1) :=
    o.before.comp (a.2.2).toPath
  let inner : Quiver.Path x (a.2.1) :=
    dq.initial.toPath.comp rh.path
  let p' : Quiver.Path x z := inner.comp o.after
  have hleadMap : rayPathMap lead =
      rayArrowMorphism (a.2.2) ≫ rayPathMap o.before := by
    dsimp only [lead, rayPathMap]
    rw [LinearPathCategory.pathMap_comp]
    simp [Quiver.Hom.toPath]
  have hleadNe : rayPathMap lead ≠ 0 := by
    intro hzero
    apply hessential.1.1
    rw [rayPathMap_eq_after_comp_arrow_comp_before_of_occurrence a p o]
    rw [hleadMap] at hzero
    simp [hzero]
  have hinnerMap : rayPathMap inner = h ≫ rayArrowMorphism dq.initial := by
    calc
      rayPathMap inner =
          rayPathMap rh.path ≫ rayPathMap dq.initial.toPath := by
        exact LinearPathCategory.pathMap_comp
          RayVertex.obj rayArrowMorphism dq.initial.toPath rh.path
      _ = h ≫ rayArrowMorphism dq.initial := by
        rw [rayPathMap_toPath, rh.map_eq]
  have hleadInner : (rayPathContourRelation (C := C)).related lead inner := by
    refine ⟨hleadNe, ?_⟩
    exact hfactor.symm.trans hinnerMap.symm
  have hpEq : p = lead.comp o.after := by
    exact o.path_eq
  have houter : (rayPathContourRelation (C := C)).related
      (lead.comp o.after) (inner.comp o.after) := by
    have houterNe : rayPathMap
        ((Quiver.Path.nil.comp lead).comp o.after) ≠ 0 := by
      simpa only [Quiver.Path.nil_comp, ← hpEq] using hessential.1.1
    simpa only [Quiver.Path.nil_comp] using
      rayPathContourRelation_whisker Quiver.Path.nil lead inner
        o.after hleadInner houterNe
  have hpp' : (rayPathContourRelation (C := C)).related p p' := by
    simpa only [hpEq, p'] using houter
  have hip' : (properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p p' := by
    apply properWhiskerInterlaced_of_step
      (rayPathContourRelation (C := C))
    refine ⟨x, a.2.1, Quiver.Path.nil, lead, inner, o.after,
      hleadInner, ?_, ?_, ?_, ?_⟩
    · simpa only [Quiver.Path.nil_comp] using houter
    · simpa using Nat.pos_of_ne_zero hafter
    · simpa only [Quiver.Path.nil_comp] using hpEq
    · simp [p']
  let dp' : PathInitialDecomposition p' :=
    { middle := dq.initialMiddle
      arrow := dq.initial
      tail := rh.path.comp o.after
      path_eq := by
        dsimp only [p', inner]
        exact Quiver.Path.comp_assoc _ _ _ }
  exact (initialArrow_ne_of_related_interlaced_of_essential
    hessential hpp' hip' dp' dq.toInitial) rfl

/-- For an essential contour occurrence with nonidentity prefix and suffix,
the category morphism represented by the selected arrow and its prefix is
target-incomparable with the other contour side's initial irreducible arrow.
The endpoint obstruction supplies one factorization direction; depth greater
than one supplies the other automatically. -/
theorem rayTargetIncomparable_occurrencePrefix_initialArrow_of_essential
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    (a : BundledQuiverArrow (RayVertex C))
    {x z : RayVertex C} (p q : Quiver.Path x z)
    (hessential : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (o : BundledArrowOccurrence a p)
    (hbefore : o.before.length ≠ 0) (hafter : o.after.length ≠ 0)
    (dq : PathEndpointDecomposition q) :
    RayTargetIncomparable
      (o.prefixNonzeroHom a p hessential.1.1)
      dq.toInitial.rayArrowNonzeroHom := by
  let f := o.prefixNonzeroHom a p hessential.1.1
  let g := dq.toInitial.rayArrowNonzeroHom
  apply rayTargetIncomparable_of_not_exists_factor_of_one_lt_depth
    f g (o.one_lt_prefixNonzeroHom_depth
      a p hessential.1.1 hbefore) dq.initial.property
  intro hfactor
  apply not_exists_comp_initialArrow_eq_occurrencePrefix
    a p q hessential o hafter dq
  obtain ⟨h, hh⟩ := hfactor
  refine ⟨h, ?_, ?_⟩
  · rintro rfl
    apply f.2
    dsimp [g, PathInitialDecomposition.rayArrowNonzeroHom,
      PathEndpointDecomposition.toInitial] at hh
    simpa using hh.symm
  · exact hh

/-- The orientation-dual essential-contour conclusion: with nonidentity
prefix and suffix, the occurrence remainder is source-incomparable with the
other contour side's final irreducible arrow. -/
theorem raySourceIncomparable_occurrenceRemainder_finalArrow_of_essential
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    (a : BundledQuiverArrow (RayVertex C))
    {x z : RayVertex C} (p q : Quiver.Path x z)
    (hessential : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (o : BundledArrowOccurrence a p)
    (hbefore : o.before.length ≠ 0) (hafter : o.after.length ≠ 0)
    (dq : PathEndpointDecomposition q) :
    RaySourceIncomparable
      (o.remainderNonzeroHom a p hessential.1.1)
      dq.toFinal.rayArrowNonzeroHom := by
  let f := o.remainderNonzeroHom a p hessential.1.1
  let g := dq.toFinal.rayArrowNonzeroHom
  apply raySourceIncomparable_of_not_exists_factor_of_one_lt_depth
    f g (o.one_lt_remainderNonzeroHom_depth
      a p hessential.1.1 hafter) dq.final.property
  intro hfactor
  apply not_exists_finalArrow_comp_eq_occurrenceRemainder
    a p q hessential o hbefore dq
  obtain ⟨h, hh⟩ := hfactor
  refine ⟨h, ?_, ?_⟩
  · rintro rfl
    apply f.2
    dsimp [g, PathFinalDecomposition.rayArrowNonzeroHom,
      PathEndpointDecomposition.toFinal] at hh
    simpa using hh.symm
  · exact hh

namespace RayHookTackle

/-- Specialization of the first Figure 55 propagation step to the concrete
selected-arrow prefix.  Failure of compatibility forces that prefix morphism
to factor through the preceding `sigma`. -/
theorem exists_precedingSigma_factor_of_not_occurrencePrefixCompatible
    {n : ℕ} (t : RayHookTackle (C := C) (n + 1))
    {x z : RayVertex C} (p : Quiver.Path x z)
    (o : BundledArrowOccurrence
      (bundledQuiverArrow t.lastArrow) p)
    (hp : rayPathMap p ≠ 0)
    (hnot : ¬t.LastReplacementCompatible
      (o.prefixNonzeroHom (bundledQuiverArrow t.lastArrow) p hp)) :
    ∃ h : t.z (Fin.last n).castSucc ⟶ x.obj,
      h ≠ 0 ∧ (t.sigma (Fin.last n)).1 ≫ h =
        (o.prefixNonzeroHom
          (bundledQuiverArrow t.lastArrow) p hp).1 := by
  apply t.exists_precedingSigma_factor_of_not_lastReplacementCompatible
    (o.prefixNonzeroHom (bundledQuiverArrow t.lastArrow) p hp)
    (rayPathMap o.before) ?_ hnot
  calc
    (t.rho (Fin.last (n + 1))).1 ≫ rayPathMap o.before =
        rayPathMap t.lastArrow.toPath ≫ rayPathMap o.before := by
      rw [t.rayPathMap_lastArrow_toPath]
    _ = rayPathMap (o.before.comp t.lastArrow.toPath) := by
      exact (LinearPathCategory.pathMap_comp
        RayVertex.obj rayArrowMorphism o.before t.lastArrow.toPath).symm

/-- The concrete final step of the Figure 55 construction.  Once the
selected-arrow prefix is compatible with the preceding tackle morphism and
target-incomparable with a new irreducible cohook, it produces a same-start
tackle with strictly larger efficiency. -/
theorem exists_lex_greater_cohook_of_occurrencePrefix
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    {m : ℕ} (t : RayHookTackle (C := C) m)
    {x z : RayVertex C} (p : Quiver.Path x z)
    (o : BundledArrowOccurrence
      (bundledQuiverArrow t.lastArrow) p)
    (hp : rayPathMap p ≠ 0) (hbefore : o.before.length ≠ 0)
    {X : C} (g : NonzeroHom X x.obj)
    (hg : IsIrreducibleRayMorphism g.1)
    (hcompatible : t.LastReplacementCompatible
      (o.prefixNonzeroHom (bundledQuiverArrow t.lastArrow) p hp))
    (hfg : RayTargetIncomparable
      (o.prefixNonzeroHom (bundledQuiverArrow t.lastArrow) p hp) g) :
    ∃ s : RayTackle C,
      s.start = (RayTackle.hook m t).start ∧
        List.Lex (fun a b : ℕ ↦ a < b)
          (RayTackle.hook m t).efficiency s.efficiency := by
  let f := o.prefixNonzeroHom
    (bundledQuiverArrow t.lastArrow) p hp
  let s := t.extendLastToCohook f g hcompatible hfg hg
  refine ⟨RayTackle.cohook m s, ?_, ?_⟩
  · simp [RayTackle.start, s]
  · exact t.efficiency_lex_extendLastToCohook
      f g hcompatible hfg hg
      (o.one_lt_prefixNonzeroHom_depth
        (bundledQuiverArrow t.lastArrow) p hp hbefore)

/-- The source-faithful Figure 55 endpoint step.  For an essential occurrence
with nonidentity paths on both sides of the selected hook, compatibility with
the preceding tackle morphism is the only remaining input: essentiality
proves target incomparability with the other contour side's initial arrow,
and the resulting cohook tackle is strictly more efficient. -/
theorem exists_lex_greater_cohook_of_essential_occurrence
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m : ℕ} (t : RayHookTackle (C := C) m)
    {x z : RayVertex C} (p q : Quiver.Path x z)
    (hessential : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (o : BundledArrowOccurrence
      (bundledQuiverArrow t.lastArrow) p)
    (hbefore : o.before.length ≠ 0) (hafter : o.after.length ≠ 0)
    (dq : PathEndpointDecomposition q)
    (hcompatible : t.LastReplacementCompatible
      (o.prefixNonzeroHom (bundledQuiverArrow t.lastArrow)
        p hessential.1.1)) :
    ∃ s : RayTackle C,
      s.start = (RayTackle.hook m t).start ∧
        List.Lex (fun a b : ℕ ↦ a < b)
          (RayTackle.hook m t).efficiency s.efficiency := by
  apply t.exists_lex_greater_cohook_of_occurrencePrefix
    p o hessential.1.1 hbefore dq.toInitial.rayArrowNonzeroHom
    dq.initial.property hcompatible
  exact rayTargetIncomparable_occurrencePrefix_initialArrow_of_essential
    (bundledQuiverArrow t.lastArrow) p q hessential o
      hbefore hafter dq

/-- A quiver-prefix improvement interface: every essential-contour occurrence
with a nonidentity quiver prefix produces a tackle at the same start with a
strictly larger efficiency word.  In the reversed ray quiver this is not the
direct orientation of the source's BGRS 8.4 statement. -/
def HasEssentialPrefixImprovement [HasFiniteRayPathDepth C]
    {m : ℕ} (t : RayHookTackle (C := C) m) : Prop :=
  ∀ {x z : RayVertex C} (p q : Quiver.Path x z),
    IsEssentialPathContour
        (rayPathContourRelation (C := C))
        (properWhiskerInterlacementRelation
          (rayPathContourRelation (C := C))) p q →
      ∀ o : BundledArrowOccurrence (bundledQuiverArrow t.lastArrow) p,
        o.before.length ≠ 0 →
          ∃ s : RayTackle C,
            s.start = (RayTackle.hook m t).start ∧
              List.Lex (fun a b : ℕ => a < b)
                (RayTackle.hook m t).efficiency s.efficiency

/-- Once quiver-prefix improvement is available, maximal efficiency gives
quiver-prefix triviality for a hook. -/
theorem essentialContourArrowPrefixTrivial_of_isEfficientAt
    [HasFiniteRayPathDepth C]
    {m : ℕ} (t : RayHookTackle (C := C) m) (y : C)
    (ht : (RayTackle.hook m t).IsEfficientAt y)
    (himprove : t.HasEssentialPrefixImprovement) :
    EssentialContourArrowPrefixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C)))
      (bundledQuiverArrow t.lastArrow) := by
  intro x z p q hessential o
  by_contra hlength
  obtain ⟨s, hsStart, hlex⟩ :=
    himprove p q hessential o hlength
  exact ht.2 s (hsStart.trans ht.1) hlex

end RayHookTackle

namespace RayCohookTackle

/-- Dual specialization of the first Figure 55 propagation step.  Failure of
compatibility forces the concrete occurrence remainder to factor through the
old last `rho`. -/
theorem exists_factorThroughLastRho_of_not_occurrenceRemainderCompatible
    {m : ℕ} (t : RayCohookTackle (C := C) m)
    {x z : RayVertex C} (p : Quiver.Path x z)
    (o : BundledArrowOccurrence
      (bundledQuiverArrow t.lastArrow) p)
    (hp : rayPathMap p ≠ 0)
    (hnot : ¬t.LastReplacementCompatible
      (o.remainderNonzeroHom (bundledQuiverArrow t.lastArrow) p hp)) :
    ∃ h : z.obj ⟶ t.x (Fin.last m).castSucc,
      h ≠ 0 ∧ h ≫ (t.rho (Fin.last m)).1 =
        (o.remainderNonzeroHom
          (bundledQuiverArrow t.lastArrow) p hp).1 := by
  apply t.exists_factorThroughLastRho_of_not_lastReplacementCompatible
    (o.remainderNonzeroHom (bundledQuiverArrow t.lastArrow) p hp)
    (rayPathMap o.after) ?_ hnot
  calc
    rayPathMap o.after ≫ (t.sigma (Fin.last m)).1 =
        rayPathMap o.after ≫ rayPathMap t.lastArrow.toPath := by
      exact (congrArg (fun q ↦ rayPathMap o.after ≫ q)
        t.rayPathMap_lastArrow_toPath).symm
    _ = rayPathMap (t.lastArrow.toPath.comp o.after) := by
      exact (LinearPathCategory.pathMap_comp
        RayVertex.obj rayArrowMorphism t.lastArrow.toPath o.after).symm

/-- The concrete dual final step of Figure 55.  A compatible occurrence
remainder which is source-incomparable with a new irreducible hook produces a
same-start tackle with strictly larger efficiency. -/
theorem exists_lex_greater_hook_of_occurrenceRemainder
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    {m : ℕ} (t : RayCohookTackle (C := C) m)
    {x z : RayVertex C} (p : Quiver.Path x z)
    (o : BundledArrowOccurrence
      (bundledQuiverArrow t.lastArrow) p)
    (hp : rayPathMap p ≠ 0) (hafter : o.after.length ≠ 0)
    {Z : C} (g : NonzeroHom z.obj Z)
    (hg : IsIrreducibleRayMorphism g.1)
    (hcompatible : t.LastReplacementCompatible
      (o.remainderNonzeroHom (bundledQuiverArrow t.lastArrow) p hp))
    (hfg : RaySourceIncomparable
      (o.remainderNonzeroHom (bundledQuiverArrow t.lastArrow) p hp) g) :
    ∃ s : RayTackle C,
      s.start = (RayTackle.cohook m t).start ∧
        List.Lex (fun a b : ℕ ↦ a < b)
          (RayTackle.cohook m t).efficiency s.efficiency := by
  let f := o.remainderNonzeroHom
    (bundledQuiverArrow t.lastArrow) p hp
  let s := t.extendLastToHook f g hcompatible hfg hg
  refine ⟨RayTackle.hook (m + 1) s, ?_, ?_⟩
  · simp [RayTackle.start, s]
  · exact t.efficiency_lex_extendLastToHook
      f g hcompatible hfg hg
      (o.one_lt_remainderNonzeroHom_depth
        (bundledQuiverArrow t.lastArrow) p hp hafter)

/-- For an essential occurrence with nonidentity paths on both sides of the
selected cohook, compatibility with the preceding tackle morphism is the only
remaining input to obtain a strictly more efficient hook tackle. -/
theorem exists_lex_greater_hook_of_essential_occurrence
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m : ℕ} (t : RayCohookTackle (C := C) m)
    {x z : RayVertex C} (p q : Quiver.Path x z)
    (hessential : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (o : BundledArrowOccurrence
      (bundledQuiverArrow t.lastArrow) p)
    (hbefore : o.before.length ≠ 0) (hafter : o.after.length ≠ 0)
    (dq : PathEndpointDecomposition q)
    (hcompatible : t.LastReplacementCompatible
      (o.remainderNonzeroHom (bundledQuiverArrow t.lastArrow)
        p hessential.1.1)) :
    ∃ s : RayTackle C,
      s.start = (RayTackle.cohook m t).start ∧
        List.Lex (fun a b : ℕ ↦ a < b)
          (RayTackle.cohook m t).efficiency s.efficiency := by
  apply t.exists_lex_greater_hook_of_occurrenceRemainder
    p o hessential.1.1 hafter dq.toFinal.rayArrowNonzeroHom
    dq.final.property hcompatible
  exact raySourceIncomparable_occurrenceRemainder_finalArrow_of_essential
    (bundledQuiverArrow t.lastArrow) p q hessential o
      hbefore hafter dq

/-- The dual quiver-prefix improvement statement for the cohook of an
efficient tackle. -/
def HasEssentialPrefixImprovement [HasFiniteRayPathDepth C]
    {m : ℕ} (t : RayCohookTackle (C := C) m) : Prop :=
  ∀ {x z : RayVertex C} (p q : Quiver.Path x z),
    IsEssentialPathContour
        (rayPathContourRelation (C := C))
        (properWhiskerInterlacementRelation
          (rayPathContourRelation (C := C))) p q →
      ∀ o : BundledArrowOccurrence (bundledQuiverArrow t.lastArrow) p,
        o.before.length ≠ 0 →
          ∃ s : RayTackle C,
            s.start = (RayTackle.cohook m t).start ∧
              List.Lex (fun a b : ℕ => a < b)
                (RayTackle.cohook m t).efficiency s.efficiency

/-- Maximal efficiency converts the dual quiver-prefix improvement statement
into quiver-prefix triviality for a cohook. -/
theorem essentialContourArrowPrefixTrivial_of_isEfficientAt
    [HasFiniteRayPathDepth C]
    {m : ℕ} (t : RayCohookTackle (C := C) m) (y : C)
    (ht : (RayTackle.cohook m t).IsEfficientAt y)
    (himprove : t.HasEssentialPrefixImprovement) :
    EssentialContourArrowPrefixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C)))
      (bundledQuiverArrow t.lastArrow) := by
  intro x z p q hessential o
  by_contra hlength
  obtain ⟨s, hsStart, hlex⟩ :=
    himprove p q hessential o hlength
  exact ht.2 s (hsStart.trans ht.1) hlex

end RayCohookTackle

end LargeIndecomposable
