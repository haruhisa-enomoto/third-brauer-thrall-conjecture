module

public import LargeIndecomposable.RayCategories.RoiterVanishing.RayFigure55HookWalk

@[expose] public section

/-!
# The fixed-cohook Figure 55 backward walk

Package the two local path replacements of BGRS Figure 55 into a decreasing
rho-index state while comparing every candidate with one fixed efficient
cohook tackle.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace RayCohookTackle

/-- The first rho of a cohook tackle lies in its first peak and is therefore
noninvertible. -/
theorem rho_zero_not_isIso {m : ℕ} (t : RayCohookTackle (C := C) m) :
    ¬IsIso (t.rho 0).1 :=
  (t.peak_incomparable 0).not_isIso_left

/-- Increasing the first rho depth strictly increases a cohook efficiency
word, independently of the remaining singleton-candidate entry. -/
theorem efficiency_lex_pair_of_rho_zero_depth_lt
    [HasFiniteRayPathDepth C]
    {m : ℕ} (t : RayCohookTackle (C := C) m) {a b : ℕ}
    (h : (t.rho 0).depth < a) :
    List.Lex (fun r s : ℕ ↦ r < s) t.efficiency [a, b] := by
  unfold RayCohookTackle.efficiency
  rw [List.ofFn_succ]
  cases hsigma : List.ofFn (fun i : Fin (m + 1) ↦
      (t.sigma i).depth) with
  | nil => exact List.Lex.rel h
  | cons d ds => exact List.Lex.rel h

end RayCohookTackle

/-- A rho-stage in the Figure 55 walk for one fixed cohook tackle. -/
structure Figure55CohookRhoStage
    {m : ℕ} (t : RayCohookTackle (C := C) m)
    {x z : RayVertex C} (p q : Quiver.Path x z)
    (i : Fin (m + 1)) where
  left : Quiver.Path x (RayVertex.mk (t.z i))
  rhoPath : RayPathPresentation (t.rho i).toMorphismFrom
  right : Quiver.Path (RayVertex.mk (t.x i.castSucc)) z
  left_length_ne_zero : left.length ≠ 0
  right_length_ne_zero : right.length ≠ 0
  state : Figure55PathState p q ((left.comp rhoPath.path).comp right)

namespace Figure55CohookRhoStage

/-- An essential occurrence of the final cohook with nonidentity context on
both sides produces the initial rho-stage.  Efficiency rules out the direct
compatible hook extension, so the occurrence remainder factors through the
last rho; the factor is noninvertible and supplies the positive right path. -/
theorem nonempty_of_occurrence
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m : ℕ} (t : RayCohookTackle (C := C) m)
    {y : C} (ht : (RayTackle.cohook m t).IsEfficientAt y)
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (hessential : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (o : BundledArrowOccurrence (bundledQuiverArrow t.lastArrow) p)
    (hbefore : o.before.length ≠ 0) (hafter : o.after.length ≠ 0)
    (dq : PathEndpointDecomposition q) :
    Nonempty (Figure55CohookRhoStage t p q (Fin.last m)) := by
  let f := o.remainderNonzeroHom
    (bundledQuiverArrow t.lastArrow) p hessential.1.1
  have hnot : ¬t.LastReplacementCompatible f := by
    intro hcompatible
    obtain ⟨candidate, hstart, hlex⟩ :=
      t.exists_lex_greater_hook_of_essential_occurrence
        p q hessential o hbefore hafter dq hcompatible
    exact ht.2 candidate (hstart.trans ht.1) hlex
  obtain ⟨h, hne, hfactor⟩ :=
    t.exists_factorThroughLastRho_of_not_occurrenceRemainderCompatible
      p o hessential.1.1 hnot
  have hfactor0 : h ≫ (t.rho (Fin.last m)).1 =
      rayPathMap (t.lastArrow.toPath.comp o.after) := by
    simpa [BundledArrowOccurrence.remainderNonzeroHom,
      bundledQuiverArrow] using hfactor
  have holdMap : rayPathMap (t.lastArrow.toPath.comp o.after) =
      rayPathMap o.after ≫ (t.sigma (Fin.last m)).1 := by
    calc
      rayPathMap (t.lastArrow.toPath.comp o.after) =
          rayPathMap o.after ≫ rayPathMap t.lastArrow.toPath := by
        exact LinearPathCategory.pathMap_comp
          RayVertex.obj rayArrowMorphism t.lastArrow.toPath o.after
      _ = rayPathMap o.after ≫ (t.sigma (Fin.last m)).1 := by
        exact congrArg (fun r ↦ rayPathMap o.after ≫ r)
          t.rayPathMap_lastArrow_toPath
  have hnoniso : ¬IsIso h := by
    intro hh
    letI : IsIso h := hh
    apply (t.peak_incomparable (Fin.last m)).1
    refine ⟨inv h ≫ rayPathMap o.after, ?_⟩
    calc
      (inv h ≫ rayPathMap o.after) ≫
          (t.sigma (Fin.last m)).1 =
          inv h ≫ (rayPathMap o.after ≫
            (t.sigma (Fin.last m)).1) := by rw [Category.assoc]
      _ = inv h ≫ rayPathMap
          (t.lastArrow.toPath.comp o.after) :=
        congrArg (fun r ↦ inv h ≫ r) holdMap.symm
      _ = inv h ≫ (h ≫ (t.rho (Fin.last m)).1) := by
        exact congrArg (fun r ↦ inv h ≫ r) hfactor0.symm
      _ = (t.rho (Fin.last m)).1 := by simp
  let hHom : NonzeroHom z.obj (t.x (Fin.last m).castSucc) := ⟨h, hne⟩
  obtain ⟨hPath, hhPath⟩ :=
    hHom.exists_presentation_length_ne_zero hnoniso
  obtain ⟨rhoPath⟩ := HasFiniteRayPathDepth.presentation_nonempty
    (t.rho (Fin.last m)).toMorphismFrom
  let oldRest := t.lastArrow.toPath.comp o.after
  let newRest := rhoPath.path.comp hPath.path
  have hpEq : p = o.before.comp oldRest := by
    calc
      p = (o.before.comp t.lastArrow.toPath).comp o.after := o.path_eq
      _ = o.before.comp oldRest := by
        exact Quiver.Path.comp_assoc _ _ _
  have hmap : rayPathMap oldRest = rayPathMap newRest := by
    calc
      rayPathMap oldRest = h ≫ (t.rho (Fin.last m)).1 := by
        exact hfactor0.symm
      _ = rayPathMap hPath.path ≫ rayPathMap rhoPath.path := by
        rw [hPath.map_eq, rhoPath.map_eq]
      _ = rayPathMap newRest := by
        exact (LinearPathCategory.pathMap_comp
          RayVertex.obj rayArrowMorphism rhoPath.path hPath.path).symm
  have hstateOld : Figure55PathState p q
      ((o.before.comp oldRest).comp Quiver.Path.nil) := by
    simpa only [Quiver.Path.comp_nil, ← hpEq] using
      Figure55PathState.self hessential
  have hstateNew : Figure55PathState p q (o.before.comp newRest) := by
    simpa only [Quiver.Path.comp_nil] using
      hstateOld.replaceInner p q o.before oldRest newRest
        Quiver.Path.nil hmap (by simpa using Nat.pos_of_ne_zero hbefore)
  refine ⟨
    { left := o.before
      rhoPath := rhoPath
      right := hPath.path
      left_length_ne_zero := hbefore
      right_length_ne_zero := hhPath
      state := ?_ }⟩
  change Figure55PathState p q
    ((o.before.comp rhoPath.path).comp hPath.path)
  rw [Quiver.Path.comp_assoc]
  exact hstateNew

/-- A rho-stage at index zero contradicts cohook efficiency through the same
singleton cohook candidate used in the fixed-hook terminal argument. -/
theorem false_of_index_zero
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m : ℕ} (t : RayCohookTackle (C := C) m)
    {y : C} (ht : (RayTackle.cohook m t).IsEfficientAt y)
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (dq : PathEndpointDecomposition q)
    (s : Figure55CohookRhoStage t p q (0 : Fin (m + 1))) : False := by
  let lead : Quiver.Path x (RayVertex.mk (t.x 0)) :=
    s.left.comp s.rhoPath.path
  let tail : Quiver.Path (RayVertex.mk (t.x 0)) z := s.right
  have hleadFactor : (t.rho 0).1 ≫ rayPathMap s.left =
      rayPathMap lead := by
    dsimp only [lead]
    calc
      (t.rho 0).1 ≫ rayPathMap s.left =
          rayPathMap s.rhoPath.path ≫ rayPathMap s.left := by
        rw [s.rhoPath.map_eq]
      _ = rayPathMap (s.left.comp s.rhoPath.path) := by
        exact (LinearPathCategory.pathMap_comp
          RayVertex.obj rayArrowMorphism s.left s.rhoPath.path).symm
  have hleadNonzero : (t.rho 0).1 ≫ rayPathMap s.left ≠ 0 := by
    rw [hleadFactor]
    exact (s.state.leadNonzeroHom lead tail rfl).2
  have hleadDepth : (t.rho 0).depth <
      (s.state.leadNonzeroHom lead tail rfl).depth := by
    have hlt := (t.rho 0).depth_lt_postcompRayPath s.left
      hleadNonzero s.left_length_ne_zero
    have heq : ((t.rho 0).postcompRayPath
        s.left hleadNonzero).toMorphismFrom =
        (s.state.leadNonzeroHom lead tail rfl).toMorphismFrom := by
      apply NonzeroMorphismFrom.ext
        (f := ((t.rho 0).postcompRayPath
          s.left hleadNonzero).toMorphismFrom)
        (g := (s.state.leadNonzeroHom lead tail rfl).toMorphismFrom) rfl
      simpa [NonzeroHom.postcompRayPath,
        Figure55PathState.leadNonzeroHom] using hleadFactor
    change rayMorphismDepth (t.rho 0).toMorphismFrom <
      rayMorphismDepth
        (s.state.leadNonzeroHom lead tail rfl).toMorphismFrom
    rw [← heq]
    exact hlt
  have hleadOne :
      1 < (s.state.leadNonzeroHom lead tail rfl).depth := by
    have hone : 1 ≤ (t.rho 0).depth :=
      (t.rho 0).one_le_depth_of_not_isIso t.rho_zero_not_isIso
    omega
  let f := s.state.leadNonzeroHom lead tail rfl
  let g := dq.toInitial.rayArrowNonzeroHom
  have hpeak : RayTargetIncomparable f g := by
    exact s.state.targetIncomparable_lead_rightInitial lead tail rfl
      s.right_length_ne_zero dq hleadOne
  let candidate := RayCohookTackle.singleton f g hpeak dq.initial.property
  apply ht.2 (RayTackle.cohook 0 candidate)
  · change candidate.x 0 = y
    exact (RayCohookTackle.singleton_x_zero
      f g hpeak dq.initial.property).trans ht.1
  · change List.Lex (fun r s : ℕ ↦ r < s)
      t.efficiency candidate.efficiency
    rw [RayCohookTackle.singleton_efficiency]
    exact t.efficiency_lex_pair_of_rho_zero_depth_lt hleadDepth

/-- One complete pair of Figure 55 replacements lowers a fixed cohook
tackle's rho index from `n+1` to `n`. -/
theorem descend
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m n : ℕ} (t : RayCohookTackle (C := C) m) (hcut : n < m)
    {y : C} (ht : (RayTackle.cohook m t).IsEfficientAt y)
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (dq : PathEndpointDecomposition q)
    (s : Figure55CohookRhoStage t p q
      ((Fin.last (n + 1)).castLE (by omega))) :
    Nonempty (Figure55CohookRhoStage t p q
      ((Fin.last n).castLE (by omega))) := by
  let c := RayCohookChain.prefixAt t hcut
  have hxNext : c.x (Fin.last (n + 1)) =
      t.x ((Fin.last (n + 1)).castLE (by omega)) := by
    simp [c, RayCohookChain.prefixAt, Fin.take]
  cases hxNext
  let lead : Quiver.Path x
      (RayVertex.mk (c.x (Fin.last (n + 1)))) :=
    s.left.comp s.rhoPath.path
  let tail : Quiver.Path (RayVertex.mk (c.x (Fin.last (n + 1)))) z :=
    s.right
  have hleadFactor : (RayCohookChain.cutoffRho t hcut).1 ≫
      rayPathMap s.left = rayPathMap lead := by
    dsimp only [lead]
    have hn1 : n + 2 ≤ m + 1 := by omega
    have hi : ((Fin.last n).castLE hcut).succ =
        (Fin.last (n + 1)).castLE hn1 := by
      exact Fin.ext (by rfl)
    cases hi
    calc
      (RayCohookChain.cutoffRho t hcut).1 ≫ rayPathMap s.left =
          (t.rho ((Fin.last (n + 1)).castLE hn1)).1 ≫
            rayPathMap s.left := by
        simp [RayCohookChain.cutoffRho, NonzeroHom.cast]
        congr 2
      _ = rayPathMap s.rhoPath.path ≫ rayPathMap s.left := by
        rw [s.rhoPath.map_eq]
      _ = rayPathMap (s.left.comp s.rhoPath.path) := by
        exact (LinearPathCategory.pathMap_comp
          RayVertex.obj rayArrowMorphism s.left s.rhoPath.path).symm
  have hleadNonzero : (RayCohookChain.cutoffRho t hcut).1 ≫
      rayPathMap s.left ≠ 0 := by
    rw [hleadFactor]
    exact (s.state.leadNonzeroHom lead tail rfl).2
  have hleadDepth : (RayCohookChain.cutoffRho t hcut).depth <
      (s.state.leadNonzeroHom lead tail rfl).depth := by
    have hlt := (RayCohookChain.cutoffRho t hcut).depth_lt_postcompRayPath
      s.left hleadNonzero s.left_length_ne_zero
    have heq : ((RayCohookChain.cutoffRho t hcut).postcompRayPath
        s.left hleadNonzero).toMorphismFrom =
        (s.state.leadNonzeroHom lead tail rfl).toMorphismFrom := by
      apply NonzeroMorphismFrom.ext
        (f := ((RayCohookChain.cutoffRho t hcut).postcompRayPath
          s.left hleadNonzero).toMorphismFrom)
        (g := (s.state.leadNonzeroHom lead tail rfl).toMorphismFrom) rfl
      simpa [NonzeroHom.postcompRayPath,
        Figure55PathState.leadNonzeroHom] using hleadFactor
    change rayMorphismDepth
        (RayCohookChain.cutoffRho t hcut).toMorphismFrom <
      rayMorphismDepth
        (s.state.leadNonzeroHom lead tail rfl).toMorphismFrom
    rw [← heq]
    exact hlt
  have hleadOne :
      1 < (s.state.leadNonzeroHom lead tail rfl).depth := by
    have hone : 1 ≤ (RayCohookChain.cutoffRho t hcut).depth :=
      (RayCohookChain.cutoffRho t hcut).one_le_depth_of_not_isIso
        (RayCohookChain.cutoff_valley_incomparable t hcut).not_isIso_right
    omega
  obtain ⟨leftNext, hleftNextNoniso, leftPath, hleftPath,
      sigmaPath, hsigmaCompose, hstateSigma⟩ :=
    s.state.exists_nextState_of_cohookCutoff t hcut
      lead tail rfl s.right_length_ne_zero dq ht (rayPathMap s.left)
        hleadFactor hleadDepth hleadOne
  let rest : Quiver.Path
      (RayVertex.mk ((RayHookChain.prefixOfCohookAt t hcut).z
        (Fin.last n))) z := by
    simpa [RayHookChain.prefixOfCohookAt, RayCohookChain.prefixAt,
      Fin.take] using sigmaPath.path.comp tail
  have hstateSigma' : Figure55PathState p q (leftPath.path.comp rest) := by
    simpa [rest, Quiver.Path.comp_assoc] using hstateSigma
  have hrestFactor : rayPathMap s.right ≫
      (RayHookChain.cutoffSigmaOfCohook t hcut).1 =
        rayPathMap rest := by
    dsimp only [rest, tail]
    have hsigmaMap : (RayHookChain.cutoffSigmaOfCohook t hcut).1 =
        rayPathMap sigmaPath.path := by
      rw [sigmaPath.map_eq]
      simp [RayHookChain.cutoffSigmaOfCohook,
        RayHookChain.prefixOfCohookAt, RayCohookChain.prefixAt,
        NonzeroHom.cast, Fin.take]
    calc
      rayPathMap s.right ≫ (RayHookChain.cutoffSigmaOfCohook t hcut).1 =
          rayPathMap s.right ≫ rayPathMap sigmaPath.path := by
        rw [hsigmaMap]
      _ = rayPathMap (sigmaPath.path.comp s.right) := by
        exact (LinearPathCategory.pathMap_comp
          RayVertex.obj rayArrowMorphism sigmaPath.path s.right).symm
  have hrestNonzero : rayPathMap s.right ≫
      (RayHookChain.cutoffSigmaOfCohook t hcut).1 ≠ 0 := by
    rw [hrestFactor]
    exact (hstateSigma'.restNonzeroHom leftPath.path rest rfl).2
  have hrestDepth : (RayHookChain.cutoffSigmaOfCohook t hcut).depth <
      (hstateSigma'.restNonzeroHom leftPath.path rest rfl).depth := by
    have hlt := (RayHookChain.cutoffSigmaOfCohook t hcut).depth_lt_precompRayPath
      s.right hrestNonzero s.right_length_ne_zero
    have heq : ((RayHookChain.cutoffSigmaOfCohook t hcut).precompRayPath
        s.right hrestNonzero).toMorphismFrom =
        (hstateSigma'.restNonzeroHom leftPath.path rest rfl).toMorphismFrom := by
      apply NonzeroMorphismFrom.ext
        (f := ((RayHookChain.cutoffSigmaOfCohook t hcut).precompRayPath
          s.right hrestNonzero).toMorphismFrom)
        (g := (hstateSigma'.restNonzeroHom
          leftPath.path rest rfl).toMorphismFrom) rfl
      change (rayPathMap s.right ≫
        (RayHookChain.cutoffSigmaOfCohook t hcut).1) ≫ 𝟙 _ =
          rayPathMap rest
      simpa only [Category.comp_id] using hrestFactor
    change rayMorphismDepth
        (RayHookChain.cutoffSigmaOfCohook t hcut).toMorphismFrom <
      rayMorphismDepth
        (hstateSigma'.restNonzeroHom leftPath.path rest rfl).toMorphismFrom
    rw [← heq]
    exact hlt
  have hrestOne :
      1 < (hstateSigma'.restNonzeroHom leftPath.path rest rfl).depth := by
    have hone : 1 ≤ (RayHookChain.cutoffSigmaOfCohook t hcut).depth :=
      (RayHookChain.cutoffSigmaOfCohook t hcut).one_le_depth_of_not_isIso
        (RayHookChain.cutoffOfCohook_peak_incomparable t hcut).not_isIso_right
    omega
  obtain ⟨rightNext, hrightNextNoniso, rightPath, hrightPath,
      rhoPath, hrhoCompose, hstateRho⟩ :=
    hstateSigma'.exists_nextState_of_hookCutoffOfCohook t hcut
      leftPath.path rest rfl hleftPath dq ht (rayPathMap s.right)
        hrestFactor hrestDepth hrestOne
  refine ⟨
    { left := ?_
      rhoPath := ?_
      right := ?_
      left_length_ne_zero := ?_
      right_length_ne_zero := ?_
      state := ?_ }⟩
  · simpa [RayCohookChain.prefixAt, Fin.take] using leftPath.path
  · simpa [RayHookChain.prefixOfCohookAt, Fin.take] using rhoPath
  · simpa [RayHookChain.prefixOfCohookAt, Fin.take] using rightPath.path
  · simpa [RayCohookChain.prefixAt, Fin.take] using hleftPath
  · simpa [RayHookChain.prefixOfCohookAt, Fin.take] using hrightPath
  · simpa [Quiver.Path.comp_assoc, RayCohookChain.prefixAt,
      RayHookChain.prefixOfCohookAt, Fin.take] using hstateRho

/-- Iterating the fixed-cohook pair descent from any rho index reaches zero. -/
theorem nonempty_index_zero_of_stage
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m k : ℕ} (t : RayCohookTackle (C := C) m) (hk : k ≤ m)
    {y : C} (ht : (RayTackle.cohook m t).IsEfficientAt y)
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (dq : PathEndpointDecomposition q)
    (s : Figure55CohookRhoStage t p q
      ((Fin.last k).castLE (by omega))) :
    Nonempty (Figure55CohookRhoStage t p q (0 : Fin (m + 1))) := by
  induction k with
  | zero => exact ⟨by simpa using s⟩
  | succ k ih =>
      have hcut : k < m := by omega
      obtain ⟨snext⟩ := s.descend t hcut ht dq
      exact ih (by omega) snext

/-- No positive-context rho-stage can occur inside an efficient cohook
tackle. -/
theorem false_of_stage
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m k : ℕ} (t : RayCohookTackle (C := C) m) (hk : k ≤ m)
    {y : C} (ht : (RayTackle.cohook m t).IsEfficientAt y)
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (dq : PathEndpointDecomposition q)
    (s : Figure55CohookRhoStage t p q
      ((Fin.last k).castLE (by omega))) : False := by
  obtain ⟨szero⟩ := s.nonempty_index_zero_of_stage t hk ht dq
  exact szero.false_of_index_zero t ht dq

/-- A final cohook cannot occur in an essential contour with nonidentity
quiver context on both sides. -/
theorem false_of_occurrence
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m : ℕ} (t : RayCohookTackle (C := C) m)
    {y : C} (ht : (RayTackle.cohook m t).IsEfficientAt y)
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (hessential : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (o : BundledArrowOccurrence (bundledQuiverArrow t.lastArrow) p)
    (hbefore : o.before.length ≠ 0) (hafter : o.after.length ≠ 0)
    (dq : PathEndpointDecomposition q) : False := by
  obtain ⟨s⟩ := nonempty_of_occurrence
    t ht hessential o hbefore hafter dq
  exact s.false_of_stage t (k := m) (by omega) ht dq

/-- The dual opening contradiction when the quiver suffix is the identity.
The selected cohook itself is source-incomparable with the other contour
side's final arrow, so appending that arrow gives an efficiency word which
strictly extends the original word after the same final depth. -/
theorem false_of_occurrence_of_after_eq_zero
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m : ℕ} (t : RayCohookTackle (C := C) m)
    {y : C} (ht : (RayTackle.cohook m t).IsEfficientAt y)
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (hessential : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (o : BundledArrowOccurrence (bundledQuiverArrow t.lastArrow) p)
    (hbefore : o.before.length ≠ 0) (hafter : o.after.length = 0)
    (dq : PathEndpointDecomposition q) : False := by
  have hz : RayVertex.mk (t.x (Fin.last m).succ) = z :=
    Quiver.Path.eq_of_length_zero o.after hafter
  subst z
  have hafterNil : o.after = Quiver.Path.nil :=
    Quiver.Path.eq_nil_of_length_zero o.after hafter
  have hpEq : p = o.before.comp t.lastArrow.toPath := by
    simpa only [hafterNil, Quiver.Path.comp_nil, bundledQuiverArrow]
      using o.path_eq
  let state := Figure55PathState.self hessential
  let f := state.restNonzeroHom o.before t.lastArrow.toPath hpEq
  let g := dq.toFinal.rayArrowNonzeroHom
  have hf : f = t.sigma (Fin.last m) := by
    apply Subtype.ext
    change rayPathMap t.lastArrow.toPath = (t.sigma (Fin.last m)).1
    exact t.rayPathMap_lastArrow_toPath
  have hfg : RaySourceIncomparable f g :=
    state.sourceIncomparable_finalArrow_rightFinal
      o.before t.lastArrow hpEq hbefore dq
  have hcompatible : t.LastReplacementCompatible f := by
    rw [hf]
    exact t.peak_incomparable (Fin.last m)
  have hfIrreducible : IsIrreducibleRayMorphism f.1 := by
    rw [hf]
    exact t.last_irreducible
  have hfdepth : f.depth = 1 :=
    rayMorphismDepth_eq_one_of_irreducible f hfIrreducible
  let candidate := t.extendLastToHook
    f g hcompatible hfg dq.final.property
  apply ht.2 (RayTackle.hook (m + 1) candidate)
  · change candidate.x 0 = y
    exact (t.extendLastToHook_x_zero
      f g hcompatible hfg dq.final.property).trans ht.1
  · exact t.efficiency_lex_extendLastToHook_of_depth_eq_one
      f g hcompatible hfg dq.final.property hfdepth

/-- Source-faithful dual of BGRS 8.4 for an efficient cohook tackle.  Duality
interchanges the source's prefix and suffix; after reversing the ray quiver,
the occurrence's quiver prefix must therefore be an identity path. -/
theorem before_length_eq_zero_of_occurrence
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m : ℕ} (t : RayCohookTackle (C := C) m)
    {y : C} (ht : (RayTackle.cohook m t).IsEfficientAt y)
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (hessential : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (o : BundledArrowOccurrence (bundledQuiverArrow t.lastArrow) p) :
    o.before.length = 0 := by
  by_contra hbefore
  obtain ⟨dq⟩ :=
    nonempty_pathEndpointDecomposition_right_of_essential_occurrence
      (bundledQuiverArrow t.lastArrow) p q hessential o hbefore
  by_cases hafter : o.after.length = 0
  · exact false_of_occurrence_of_after_eq_zero
      t ht hessential o hbefore hafter dq
  · exact false_of_occurrence t ht hessential o hbefore hafter dq

/-- Every occurrence of the cohook of an efficient tackle in the left side
of an essential reversed-ray contour has trivial prefix. -/
theorem essentialContourArrowPrefixTrivial_of_isEfficientAt
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m : ℕ} (t : RayCohookTackle (C := C) m)
    {y : C} (ht : (RayTackle.cohook m t).IsEfficientAt y) :
    EssentialContourArrowPrefixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C)))
      (bundledQuiverArrow t.lastArrow) := by
  intro x z p q hessential o
  exact before_length_eq_zero_of_occurrence t ht hessential o

end Figure55CohookRhoStage

end LargeIndecomposable
