module

public import LargeIndecomposable.RayCategories.RoiterVanishing.RayFigure55PathState

@[expose] public section

/-!
# The fixed-hook Figure 55 backward walk

This file packages the two local path replacements of BGRS Figure 55 into a
decreasing-index state for one fixed efficient hook tackle.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace RaySourceIncomparable

/-- Either member of a source-incomparable pair is noninvertible. -/
theorem not_isIso_left {X Y Z : C} {f : NonzeroHom X Y}
    {g : NonzeroHom X Z} (hfg : RaySourceIncomparable f g) :
    ¬IsIso f.1 := by
  intro hf
  letI : IsIso f.1 := hf
  apply hfg.1
  refine ⟨inv f.1 ≫ g.1, ?_⟩
  simp

/-- Either member of a source-incomparable pair is noninvertible. -/
theorem not_isIso_right {X Y Z : C} {f : NonzeroHom X Y}
    {g : NonzeroHom X Z} (hfg : RaySourceIncomparable f g) :
    ¬IsIso g.1 := by
  intro hg
  letI : IsIso g.1 := hg
  apply hfg.2
  refine ⟨inv g.1 ≫ f.1, ?_⟩
  simp

end RaySourceIncomparable

namespace RayTargetIncomparable

/-- Either member of a target-incomparable pair is noninvertible. -/
theorem not_isIso_left {X Y Z : C} {f : NonzeroHom X Z}
    {g : NonzeroHom Y Z} (hfg : RayTargetIncomparable f g) :
    ¬IsIso f.1 := by
  intro hf
  letI : IsIso f.1 := hf
  apply hfg.2
  refine ⟨g.1 ≫ inv f.1, ?_⟩
  simp

/-- Either member of a target-incomparable pair is noninvertible. -/
theorem not_isIso_right {X Y Z : C} {f : NonzeroHom X Z}
    {g : NonzeroHom Y Z} (hfg : RayTargetIncomparable f g) :
    ¬IsIso g.1 := by
  intro hg
  letI : IsIso g.1 := hg
  apply hfg.1
  refine ⟨f.1 ≫ inv g.1, ?_⟩
  simp

end RayTargetIncomparable

namespace NonzeroHom

/-- A noninvertible nonzero ray morphism has positive depth. -/
theorem one_le_depth_of_not_isIso
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    {X Y : C} (f : NonzeroHom X Y) (hf : ¬IsIso f.1) :
    1 ≤ f.depth := by
  obtain ⟨p, hp⟩ := f.exists_presentation_length_ne_zero hf
  have hle := p.length_le_depth
  change p.path.length ≤ f.depth at hle
  omega

end NonzeroHom

namespace RayCohookTackle

/-- The length-zero cohook tackle with prescribed common-target morphisms. -/
def singleton {X Y Z : C} (f : NonzeroHom X Z) (g : NonzeroHom Y Z)
    (hpeak : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) : RayCohookTackle (C := C) 0 := by
  let xs : Fin 2 → C := Fin.lastCases Y (fun _ : Fin 1 ↦ X)
  let zs : Fin 1 → C := fun _ ↦ Z
  have hxCast (i : Fin 1) : xs i.castSucc = X := by
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    exact Fin.lastCases_castSucc 0
  have hxSucc (i : Fin 1) : xs i.succ = Y := by
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    exact Fin.lastCases_last
  refine
    { x := xs
      z := zs
      rho := fun i ↦ f.cast (hxCast i).symm (by simp [zs])
      sigma := fun i ↦ g.cast (hxSucc i).symm (by simp [zs])
      peak_incomparable := fun i ↦ ?_
      valley_incomparable := fun i ↦ Fin.elim0 i
      last_irreducible := ?_ }
  · have hi : i = 0 := Fin.ext (by omega)
    subst i
    simpa only using hpeak.cast (hxCast 0).symm (hxSucc 0).symm
      (by simp [zs])
  · simpa only using isIrreducibleMorphism_cast
      (hxSucc (Fin.last 0)).symm (by simp [zs]) g hg

@[simp]
theorem singleton_x_zero {X Y Z : C} (f : NonzeroHom X Z)
    (g : NonzeroHom Y Z) (hpeak : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    (RayCohookTackle.singleton f g hpeak hg).x 0 = X := by
  change Fin.lastCases Y (fun _ : Fin 1 ↦ X) 0 = X
  simpa using (Fin.lastCases_castSucc
    (motive := fun _ : Fin 2 ↦ C)
    (last := Y) (cast := fun _ : Fin 1 ↦ X) (0 : Fin 1))

@[simp]
theorem singleton_efficiency
    [HasFiniteRayPathDepth C]
    {X Y Z : C} (f : NonzeroHom X Z) (g : NonzeroHom Y Z)
    (hpeak : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    (RayCohookTackle.singleton f g hpeak hg).efficiency =
      [f.depth, g.depth] := by
  simp [singleton, RayCohookTackle.efficiency, alternateLists]

end RayCohookTackle

namespace RayHookTackle

/-- The first rho in a hook tackle is noninvertible.  For a singleton tackle
it is the irreducible hook; otherwise it lies in the first peak. -/
theorem rho_zero_not_isIso {m : ℕ} (t : RayHookTackle (C := C) m) :
    ¬IsIso (t.rho 0).1 := by
  cases m with
  | zero =>
      simpa using t.last_irreducible.2.1
  | succ n =>
      exact (t.peak_incomparable 0).not_isIso_left

/-- Increasing the depth of the first rho strictly increases the whole
efficiency word, independently of the remaining candidate word. -/
theorem efficiency_lex_pair_of_rho_zero_depth_lt
    [HasFiniteRayPathDepth C]
    {m : ℕ} (t : RayHookTackle (C := C) m) {a b : ℕ}
    (h : (t.rho 0).depth < a) :
    List.Lex (fun r s : ℕ ↦ r < s) t.efficiency [a, b] := by
  unfold RayHookTackle.efficiency
  rw [List.ofFn_succ]
  cases hsigma : List.ofFn (fun i : Fin m ↦ (t.sigma i).depth) with
  | nil =>
      exact List.Lex.rel h
  | cons d ds =>
      exact List.Lex.rel h

end RayHookTackle

/-- A rho-stage in the Figure 55 walk for one fixed hook tackle.  The current
path passes through `rho_i`, with nonidentity paths on both sides, and remains
in the interlacement class of the fixed essential contour side. -/
structure Figure55HookRhoStage
    {m : ℕ} (t : RayHookTackle (C := C) m)
    {x z : RayVertex C} (p q : Quiver.Path x z)
    (i : Fin (m + 1)) where
  left : Quiver.Path x (RayVertex.mk (t.z i))
  rhoPath : RayPathPresentation (t.rho i).toMorphismFrom
  right : Quiver.Path (RayVertex.mk (t.x i)) z
  left_length_ne_zero : left.length ≠ 0
  right_length_ne_zero : right.length ≠ 0
  state : Figure55PathState p q ((left.comp rhoPath.path).comp right)

namespace Figure55HookRhoStage

/-- The selected final hook occurrence is the initial rho-stage. -/
def ofOccurrence
    {m : ℕ} (t : RayHookTackle (C := C) m)
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (hessential : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (o : BundledArrowOccurrence (bundledQuiverArrow t.lastArrow) p)
    (hbefore : o.before.length ≠ 0) (hafter : o.after.length ≠ 0) :
    Figure55HookRhoStage t p q (Fin.last m) where
  left := o.before
  rhoPath :=
    { path := t.lastArrow.toPath
      map_eq := t.rayPathMap_lastArrow_toPath }
  right := o.after
  left_length_ne_zero := hbefore
  right_length_ne_zero := hafter
  state := by
    simpa only [bundledQuiverArrow, o.path_eq] using
      Figure55PathState.self hessential

/-- A rho-stage at index zero contradicts efficiency: the current leading
composite and the other contour side's initial arrow form a singleton cohook
tackle whose first depth is strictly larger. -/
theorem false_of_index_zero
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m : ℕ} (t : RayHookTackle (C := C) m)
    {y : C} (ht : (RayTackle.hook m t).IsEfficientAt y)
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (dq : PathEndpointDecomposition q)
    (s : Figure55HookRhoStage t p q (0 : Fin (m + 1))) : False := by
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

/-- One complete pair of Figure 55 replacements lowers a fixed hook
tackle's rho index from `n+1` to `n`. -/
theorem descend
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m n : ℕ} (t : RayHookTackle (C := C) m) (hcut : n < m)
    {y : C} (ht : (RayTackle.hook m t).IsEfficientAt y)
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (dq : PathEndpointDecomposition q)
    (s : Figure55HookRhoStage t p q
      ((Fin.last (n + 1)).castLE (by omega))) :
    Nonempty (Figure55HookRhoStage t p q
      ((Fin.last n).castLE (by omega))) := by
  let c := RayCohookChain.prefixOfHookAt t hcut
  have hxNext : c.x (Fin.last (n + 1)) =
      t.x ((Fin.last (n + 1)).castLE (by omega)) := by
    simp [c, RayCohookChain.prefixOfHookAt, Fin.take]
  cases hxNext
  let lead : Quiver.Path x
      (RayVertex.mk (c.x (Fin.last (n + 1)))) :=
    s.left.comp s.rhoPath.path
  let tail : Quiver.Path (RayVertex.mk (c.x (Fin.last (n + 1)))) z :=
    s.right
  have hleadFactor :
      (RayCohookChain.cutoffRhoOfHook t hcut).1 ≫ rayPathMap s.left =
        rayPathMap lead := by
    dsimp only [lead]
    have hn1 : n + 2 ≤ m + 1 := by omega
    have hi : ((Fin.last n).castLE hcut).succ =
        (Fin.last (n + 1)).castLE hn1 := by
      exact Fin.ext (by rfl)
    cases hi
    calc
      (RayCohookChain.cutoffRhoOfHook t hcut).1 ≫ rayPathMap s.left =
          (t.rho ((Fin.last (n + 1)).castLE hn1)).1 ≫
            rayPathMap s.left := by
        simp [RayCohookChain.cutoffRhoOfHook, NonzeroHom.cast]
        congr 2
      _ = rayPathMap s.rhoPath.path ≫ rayPathMap s.left := by
        rw [s.rhoPath.map_eq]
      _ = rayPathMap (s.left.comp s.rhoPath.path) := by
        exact (LinearPathCategory.pathMap_comp
          RayVertex.obj rayArrowMorphism s.left s.rhoPath.path).symm
  have hleadNonzero :
      (RayCohookChain.cutoffRhoOfHook t hcut).1 ≫
          rayPathMap s.left ≠ 0 := by
    rw [hleadFactor]
    exact (s.state.leadNonzeroHom lead tail rfl).2
  have hleadDepth :
      (RayCohookChain.cutoffRhoOfHook t hcut).depth <
        (s.state.leadNonzeroHom lead tail rfl).depth := by
    have hlt :=
      (RayCohookChain.cutoffRhoOfHook t hcut).depth_lt_postcompRayPath
        s.left hleadNonzero s.left_length_ne_zero
    have heq :
        ((RayCohookChain.cutoffRhoOfHook t hcut).postcompRayPath
          s.left hleadNonzero).toMorphismFrom =
          (s.state.leadNonzeroHom lead tail rfl).toMorphismFrom := by
      apply NonzeroMorphismFrom.ext
        (f := ((RayCohookChain.cutoffRhoOfHook t hcut).postcompRayPath
          s.left hleadNonzero).toMorphismFrom)
        (g := (s.state.leadNonzeroHom lead tail rfl).toMorphismFrom) rfl
      simpa [NonzeroHom.postcompRayPath,
        Figure55PathState.leadNonzeroHom] using hleadFactor
    change rayMorphismDepth
        ((RayCohookChain.cutoffRhoOfHook t hcut).toMorphismFrom) <
      rayMorphismDepth
        (s.state.leadNonzeroHom lead tail rfl).toMorphismFrom
    rw [← heq]
    exact hlt
  have hleadOne :
      1 < (s.state.leadNonzeroHom lead tail rfl).depth := by
    have hone : 1 ≤ (RayCohookChain.cutoffRhoOfHook t hcut).depth :=
      (RayCohookChain.cutoffRhoOfHook t hcut).one_le_depth_of_not_isIso
        (RayCohookChain.cutoffOfHook_valley_incomparable t hcut).not_isIso_right
    omega
  obtain ⟨leftNext, hleftNextNoniso, leftPath, hleftPath,
      sigmaPath, hsigmaCompose, hstateSigma⟩ :=
    s.state.exists_nextState_of_cohookCutoffOfHook t hcut
      lead tail rfl s.right_length_ne_zero dq ht (rayPathMap s.left)
        hleadFactor hleadDepth hleadOne
  let rest : Quiver.Path
      (RayVertex.mk ((RayHookChain.prefixAt t hcut).z (Fin.last n))) z := by
    simpa [RayHookChain.prefixAt, RayCohookChain.prefixOfHookAt,
      Fin.take] using sigmaPath.path.comp tail
  have hstateSigma' : Figure55PathState p q (leftPath.path.comp rest) := by
    simpa [rest, Quiver.Path.comp_assoc] using hstateSigma
  have hrestFactor : rayPathMap s.right ≫
      (RayHookChain.cutoffSigma t hcut).1 = rayPathMap rest := by
    dsimp only [rest, tail]
    have hsigmaMap : (RayHookChain.cutoffSigma t hcut).1 =
        rayPathMap sigmaPath.path := by
      rw [sigmaPath.map_eq]
      simp [RayHookChain.cutoffSigma, RayHookChain.prefixAt,
        RayCohookChain.prefixOfHookAt, NonzeroHom.cast, Fin.take]
    calc
      rayPathMap s.right ≫ (RayHookChain.cutoffSigma t hcut).1 =
          rayPathMap s.right ≫ rayPathMap sigmaPath.path := by
        rw [hsigmaMap]
      _ = rayPathMap (sigmaPath.path.comp s.right) := by
        exact (LinearPathCategory.pathMap_comp
          RayVertex.obj rayArrowMorphism sigmaPath.path s.right).symm
  have hrestNonzero : rayPathMap s.right ≫
      (RayHookChain.cutoffSigma t hcut).1 ≠ 0 := by
    rw [hrestFactor]
    exact (hstateSigma'.restNonzeroHom leftPath.path rest rfl).2
  have hrestDepth : (RayHookChain.cutoffSigma t hcut).depth <
      (hstateSigma'.restNonzeroHom leftPath.path rest rfl).depth := by
    have hlt := (RayHookChain.cutoffSigma t hcut).depth_lt_precompRayPath
      s.right hrestNonzero s.right_length_ne_zero
    have heq : ((RayHookChain.cutoffSigma t hcut).precompRayPath
        s.right hrestNonzero).toMorphismFrom =
        (hstateSigma'.restNonzeroHom leftPath.path rest rfl).toMorphismFrom := by
      apply NonzeroMorphismFrom.ext
        (f := ((RayHookChain.cutoffSigma t hcut).precompRayPath
          s.right hrestNonzero).toMorphismFrom)
        (g := (hstateSigma'.restNonzeroHom
          leftPath.path rest rfl).toMorphismFrom) rfl
      change (rayPathMap s.right ≫
        (RayHookChain.cutoffSigma t hcut).1) ≫ 𝟙 _ = rayPathMap rest
      simpa only [Category.comp_id] using hrestFactor
    change rayMorphismDepth (RayHookChain.cutoffSigma t hcut).toMorphismFrom <
      rayMorphismDepth
        (hstateSigma'.restNonzeroHom leftPath.path rest rfl).toMorphismFrom
    rw [← heq]
    exact hlt
  have hrestOne :
      1 < (hstateSigma'.restNonzeroHom leftPath.path rest rfl).depth := by
    have hone : 1 ≤ (RayHookChain.cutoffSigma t hcut).depth :=
      (RayHookChain.cutoffSigma t hcut).one_le_depth_of_not_isIso
        (RayHookChain.cutoff_peak_incomparable t hcut).not_isIso_right
    omega
  obtain ⟨rightNext, hrightNextNoniso, rightPath, hrightPath,
      rhoPath, hrhoCompose, hstateRho⟩ :=
    hstateSigma'.exists_nextState_of_hookCutoff t hcut
      leftPath.path rest rfl hleftPath dq ht (rayPathMap s.right)
        hrestFactor hrestDepth hrestOne
  refine ⟨
    { left := ?_
      rhoPath := ?_
      right := ?_
      left_length_ne_zero := ?_
      right_length_ne_zero := ?_
      state := ?_ }⟩
  · simpa [RayCohookChain.prefixOfHookAt, Fin.take] using leftPath.path
  · simpa [RayHookChain.prefixAt, Fin.take] using rhoPath
  · simpa [RayHookChain.prefixAt, Fin.take] using rightPath.path
  · simpa [RayCohookChain.prefixOfHookAt, Fin.take] using hleftPath
  · simpa [RayHookChain.prefixAt, Fin.take] using hrightPath
  · simpa [Quiver.Path.comp_assoc, RayHookChain.prefixAt,
      RayCohookChain.prefixOfHookAt, Fin.take] using hstateRho

/-- Iterating the pair descent from any rho index reaches index zero. -/
theorem nonempty_index_zero_of_stage
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m k : ℕ} (t : RayHookTackle (C := C) m) (hk : k ≤ m)
    {y : C} (ht : (RayTackle.hook m t).IsEfficientAt y)
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (dq : PathEndpointDecomposition q)
    (s : Figure55HookRhoStage t p q
      ((Fin.last k).castLE (by omega))) :
    Nonempty (Figure55HookRhoStage t p q (0 : Fin (m + 1))) := by
  induction k with
  | zero =>
      exact ⟨by simpa using s⟩
  | succ k ih =>
      have hcut : k < m := by omega
      obtain ⟨snext⟩ := s.descend t hcut ht dq
      exact ih (by omega) snext

/-- No positive-context rho-stage can occur inside an efficient hook tackle. -/
theorem false_of_stage
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m k : ℕ} (t : RayHookTackle (C := C) m) (hk : k ≤ m)
    {y : C} (ht : (RayTackle.hook m t).IsEfficientAt y)
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (dq : PathEndpointDecomposition q)
    (s : Figure55HookRhoStage t p q
      ((Fin.last k).castLE (by omega))) : False := by
  obtain ⟨szero⟩ := s.nonempty_index_zero_of_stage t hk ht dq
  exact szero.false_of_index_zero t ht dq

/-- Figure 55 rules out an essential occurrence of the last hook with
nonidentity paths on both sides. -/
theorem false_of_occurrence
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m : ℕ} (t : RayHookTackle (C := C) m)
    {y : C} (ht : (RayTackle.hook m t).IsEfficientAt y)
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (hessential : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (o : BundledArrowOccurrence (bundledQuiverArrow t.lastArrow) p)
    (hbefore : o.before.length ≠ 0) (hafter : o.after.length ≠ 0)
    (dq : PathEndpointDecomposition q) : False := by
  let s := Figure55HookRhoStage.ofOccurrence
    t hessential o hbefore hafter
  exact s.false_of_stage t (k := m) (by omega) ht dq

/-- The opening Figure 55 contradiction when the quiver prefix is the
identity.  The selected hook itself is target-incomparable with the other
contour side's initial arrow, so appending that arrow gives an efficiency word
which strictly extends the original word after the same final depth. -/
theorem false_of_occurrence_of_before_eq_zero
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m : ℕ} (t : RayHookTackle (C := C) m)
    {y : C} (ht : (RayTackle.hook m t).IsEfficientAt y)
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (hessential : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (o : BundledArrowOccurrence (bundledQuiverArrow t.lastArrow) p)
    (hbefore : o.before.length = 0) (hafter : o.after.length ≠ 0)
    (dq : PathEndpointDecomposition q) : False := by
  have hx : x = RayVertex.mk (t.z (Fin.last m)) :=
    Quiver.Path.eq_of_length_zero o.before hbefore
  subst x
  have hbeforeNil : o.before = Quiver.Path.nil :=
    Quiver.Path.eq_nil_of_length_zero o.before hbefore
  have hpEq : p = t.lastArrow.toPath.comp o.after := by
    simpa only [hbeforeNil, Quiver.Path.nil_comp, bundledQuiverArrow]
      using o.path_eq
  let state := Figure55PathState.self hessential
  let f := state.leadNonzeroHom t.lastArrow.toPath o.after hpEq
  let g := dq.toInitial.rayArrowNonzeroHom
  have hfg : RayTargetIncomparable f g :=
    state.targetIncomparable_initialArrow_rightInitial
      t.lastArrow o.after hpEq hafter dq
  have hcompatible : t.LastReplacementCompatible f := by
    cases m with
    | zero => trivial
    | succ n =>
        change RaySourceIncomparable (t.sigma (Fin.last n)) f
        simpa [f, state, Figure55PathState.leadNonzeroHom] using
          t.valley_incomparable (Fin.last n)
  have hfIrreducible : IsIrreducibleRayMorphism f.1 := by
    simpa [f, state, Figure55PathState.leadNonzeroHom] using
      t.last_irreducible
  have hfdepth : f.depth = 1 :=
    rayMorphismDepth_eq_one_of_irreducible f hfIrreducible
  let candidate := t.extendLastToCohook
    f g hcompatible hfg dq.initial.property
  apply ht.2 (RayTackle.cohook m candidate)
  · change candidate.x 0 = y
    exact (t.extendLastToCohook_x_zero
      f g hcompatible hfg dq.initial.property).trans ht.1
  · exact t.efficiency_lex_extendLastToCohook_of_depth_eq_one
      f g hcompatible hfg dq.initial.property hfdepth

/-- Source-faithful BGRS 8.4 for an efficient hook tackle.  BGRS composes
paths from left to right, whereas the Lean ray quiver is reversed; hence the
source's prefix `p` in `v = p * tau * u` is the occurrence's `after` path.
It must be an identity path. -/
theorem after_length_eq_zero_of_occurrence
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m : ℕ} (t : RayHookTackle (C := C) m)
    {y : C} (ht : (RayTackle.hook m t).IsEfficientAt y)
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (hessential : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (o : BundledArrowOccurrence (bundledQuiverArrow t.lastArrow) p) :
    o.after.length = 0 := by
  by_contra hafter
  obtain ⟨dq⟩ :=
    nonempty_pathEndpointDecomposition_right_of_occurrence_after_ne_zero
      (bundledQuiverArrow t.lastArrow) p q hessential o hafter
  by_cases hbefore : o.before.length = 0
  · exact false_of_occurrence_of_before_eq_zero
      t ht hessential o hbefore hafter dq
  · exact false_of_occurrence t ht hessential o hbefore hafter dq

/-- Every occurrence of the hook of an efficient tackle in the left side of
an essential reversed-ray contour has trivial suffix. -/
theorem essentialContourArrowSuffixTrivial_of_isEfficientAt
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    [HasRayCancellation C]
    {m : ℕ} (t : RayHookTackle (C := C) m)
    {y : C} (ht : (RayTackle.hook m t).IsEfficientAt y) :
    EssentialContourArrowSuffixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C)))
      (bundledQuiverArrow t.lastArrow) := by
  intro x z p q hessential o
  exact after_length_eq_zero_of_occurrence t ht hessential o

end Figure55HookRhoStage

end LargeIndecomposable
