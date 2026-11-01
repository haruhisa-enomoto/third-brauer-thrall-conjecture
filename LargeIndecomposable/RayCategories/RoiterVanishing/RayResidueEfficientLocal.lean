module

public import LargeIndecomposable.RayCategories.RoiterVanishing.RayResidueInduction
public import LargeIndecomposable.RayCategories.RoiterVanishing.RayFigure55HookWalk
public import LargeIndecomposable.RayCategories.RoiterVanishing.RayFigure55CohookWalk

@[expose] public section

/-!
# Efficient-tackle local corrections in a ray residue

Specialize the residue-ready sparse corrections to the last arrow of an
efficient hook or cohook tackle.  BGRS 8.4 supplies suffix or prefix
triviality, respectively; the easy `N = 2` branch additionally assumes that
this selected arrow belongs to no essential contour surviving the residue.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {k : Type*} [Field k]
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Every nonzero morphism between the objects represented by two ray vertices
has an irreducible-path presentation with exactly those vertices as its path
endpoints. -/
theorem exists_rayPathMap_eq_of_ne_zero
    [Finite C] [IsFiniteRayCategory C]
    {i j : RayVertex C} (f : j.obj ⟶ i.obj) (hf : f ≠ 0) :
    ∃ p : Quiver.Path i j, rayPathMap p = f := by
  let fNonzero : NonzeroHom j.obj i.obj := ⟨f, hf⟩
  obtain ⟨p⟩ := rayPathPresentation_nonempty_of_finite fNonzero
  cases i
  cases j
  exact ⟨p.path, p.map_eq⟩

/-- The three-arrow figure predicate is stable under endpoint casts. -/
theorem isRayThreeArrowFigure_cast
    {X X' B B' G G' D D' : C}
    (hX : X = X') (hB : B = B') (hG : G = G') (hD : D = D')
    (beta : NonzeroHom X B) (gamma : NonzeroHom X G)
    (delta : NonzeroHom X D)
    (hfigure : IsRayThreeArrowFigure beta.toMorphismFrom
      gamma.toMorphismFrom delta.toMorphismFrom) :
    IsRayThreeArrowFigure
      (NonzeroHom.cast hX hB beta).toMorphismFrom
      (NonzeroHom.cast hX hG gamma).toMorphismFrom
      (NonzeroHom.cast hX hD delta).toMorphismFrom := by
  subst X'
  subst B'
  subst G'
  subst D'
  simpa using hfigure

/-- The fixed-target three-arrow figure predicate is stable under endpoint
casts. -/
theorem isRayCoThreeArrowFigure_cast
    {X X' B B' G G' D D' : C}
    (hX : X = X') (hB : B = B') (hG : G = G') (hD : D = D')
    (beta : NonzeroHom B X) (gamma : NonzeroHom G X)
    (delta : NonzeroHom D X)
    (hfigure : IsRayCoThreeArrowFigure beta.toMorphismTo
      gamma.toMorphismTo delta.toMorphismTo) :
    IsRayCoThreeArrowFigure
      (NonzeroHom.cast hB hX beta).toMorphismTo
      (NonzeroHom.cast hG hX gamma).toMorphismTo
      (NonzeroHom.cast hD hX delta).toMorphismTo := by
  subst X'
  subst B'
  subst G'
  subst D'
  simpa using hfigure

def quiverArrowCast {Q : Type u} [Quiver.{v} Q]
    {i j i' j' : Q} (hi : i = i') (hj : j = j') (a : i ⟶ j) :
    i' ⟶ j' := by
  subst i'
  subst j'
  exact a

private theorem bundledQuiverArrow_eq_of_quiverArrowCast_eq
    {Q : Type u} [Quiver.{v} Q]
    {i j i' j' : Q} (hi : i = i') (hj : j = j')
    (a : i ⟶ j) (b : i' ⟶ j')
    (h : quiverArrowCast hi hj a = b) :
    bundledQuiverArrow a = bundledQuiverArrow b := by
  cases hi
  cases hj
  simpa [quiverArrowCast] using congrArg bundledQuiverArrow h

private theorem quiverArrowCast_eq_of_rayNonzeroHom_cast_eq
    {i j i' j' : RayVertex C} (hi : i = i') (hj : j = j')
    (a : i ⟶ j) (b : i' ⟶ j')
    (h : NonzeroHom.cast (congrArg RayVertex.obj hj)
      (congrArg RayVertex.obj hi)
      (⟨rayArrowMorphism a, a.property.1⟩ : NonzeroHom j.obj i.obj) =
      (⟨rayArrowMorphism b, b.property.1⟩ : NonzeroHom j'.obj i'.obj)) :
    quiverArrowCast hi hj a = b := by
  cases hi
  cases hj
  apply Subtype.ext
  have hv := congrArg Subtype.val h
  simp [NonzeroHom.cast] at hv
  change a.1 = b.1
  change a.1 = b.1 at hv
  exact hv

private theorem nonzeroHom_cast_comp
    {X Y X' Y' X'' Y'' : C}
    (hx : X = X') (hy : Y = Y') (hx' : X' = X'')
    (hy' : Y' = Y'') (f : NonzeroHom X Y) :
    NonzeroHom.cast hx' hy' (NonzeroHom.cast hx hy f) =
      NonzeroHom.cast (hx.trans hx') (hy.trans hy') f := by
  subst X'
  subst Y'
  subst X''
  subst Y''
  rfl

/-- Endpoint casts along self-equalities are propositionally trivial. -/
private theorem nonzeroHom_cast_self
    {X Y : C} (hx : X = X) (hy : Y = Y) (f : NonzeroHom X Y) :
    NonzeroHom.cast hx hy f = f := by
  have hx' : hx = rfl := Subsingleton.elim _ _
  have hy' : hy = rfl := Subsingleton.elim _ _
  rw [hx', hy']
  rfl

/-- Strictly postcomposing a common upper bound transports its two incoming
arrow presentations into one proper-whisker interlacement at the upper ray. -/
theorem exists_interlaced_presentations_of_strict_commonUpper
    [Finite C] [IsFiniteRayCategory C]
    {z : RayVertex C} (a b : IncomingQuiverArrow z)
    (u mu : NonzeroMorphismFrom z.obj)
    (hau : (incomingQuiverArrowNonzeroHom (C := C) a).toMorphismFrom ≤ u)
    (hbu : (incomingQuiverArrowNonzeroHom (C := C) b).toMorphismFrom ≤ u)
    (huMu : u ≤ mu) (hMuNotLeU : ¬mu ≤ u) :
    ∃ (pa pb : Quiver.Path (RayVertex.mk mu.target) z)
      (da : PathFinalDecomposition pa) (db : PathFinalDecomposition pb),
      rayPathMap pa = mu.hom ∧ rayPathMap pb = mu.hom ∧
        (⟨da.middle, da.arrow⟩ : IncomingQuiverArrow z) = a ∧
        (⟨db.middle, db.arrow⟩ : IncomingQuiverArrow z) = b ∧
        (properWhiskerInterlacementRelation
          (rayPathContourRelation (C := C))).interlaced pa pb := by
  obtain ⟨fa, hfa⟩ := hau
  obtain ⟨fb, hfb⟩ := hbu
  obtain ⟨h, hh⟩ := huMu
  have hfa0 : fa ≠ 0 := by
    intro hz; apply u.ne_zero; rw [← hfa, hz, comp_zero]
  have hfb0 : fb ≠ 0 := by
    intro hz; apply u.ne_zero; rw [← hfb, hz, comp_zero]
  have hh0 : h ≠ 0 := by
    intro hz; apply mu.ne_zero; rw [← hh, hz, comp_zero]
  have hhNotIso : ¬IsIso h := by
    intro hIso
    letI : IsIso h := hIso
    apply hMuNotLeU
    refine ⟨inv h, ?_⟩
    rw [← hh, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  obtain ⟨qa, hqa⟩ := exists_rayPathMap_eq_of_ne_zero
    (C := C) (i := RayVertex.mk u.target) (j := a.1) fa hfa0
  obtain ⟨qb, hqb⟩ := exists_rayPathMap_eq_of_ne_zero
    (C := C) (i := RayVertex.mk u.target) (j := b.1) fb hfb0
  obtain ⟨t, ht⟩ := exists_rayPathMap_eq_of_ne_zero
    (C := C) (i := RayVertex.mk mu.target)
      (j := RayVertex.mk u.target) h hh0
  have htLength : t.length ≠ 0 := by
    intro ht0; apply hhNotIso; rw [← ht]
    exact rayPathMap_isIso_of_length_eq_zero t ht0
  let va := qa.comp a.2.toPath
  let vb := qb.comp b.2.toPath
  have hva : rayPathMap va = u.hom := by
    calc
      rayPathMap va = rayPathMap a.2.toPath ≫ rayPathMap qa := by
        exact LinearPathCategory.pathMap_comp
          RayVertex.obj rayArrowMorphism qa a.2.toPath
      _ = rayArrowMorphism a.2 ≫ fa := by rw [rayPathMap_toPath, hqa]
      _ = u.hom := hfa
  have hvb : rayPathMap vb = u.hom := by
    calc
      rayPathMap vb = rayPathMap b.2.toPath ≫ rayPathMap qb := by
        exact LinearPathCategory.pathMap_comp
          RayVertex.obj rayArrowMorphism qb b.2.toPath
      _ = rayArrowMorphism b.2 ≫ fb := by rw [rayPathMap_toPath, hqb]
      _ = u.hom := hfb
  let pa := t.comp va
  let pb := t.comp vb
  have hpa : rayPathMap pa = mu.hom := by
    simp only [pa, rayPathMap, LinearPathCategory.pathMap_comp]
    change rayPathMap va ≫ rayPathMap t = mu.hom
    rw [hva, ht]
    exact hh
  have hpb : rayPathMap pb = mu.hom := by
    simp only [pb, rayPathMap, LinearPathCategory.pathMap_comp]
    change rayPathMap vb ≫ rayPathMap t = mu.hom
    rw [hvb, ht]
    exact hh
  let da : PathFinalDecomposition pa := {
    middle := a.1
    head := t.comp qa
    arrow := a.2
    path_eq := by simp [pa, va] }
  let db : PathFinalDecomposition pb := {
    middle := b.1
    head := t.comp qb
    arrow := b.2
    path_eq := by simp [pb, vb] }
  have hinterlaced : (properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced pa pb := by
    have hstep := rayPaths_related_and_interlaced_of_inner_map_eq
      t va vb Quiver.Path.nil
      (by rw [Quiver.Path.comp_nil, hpa]; exact mu.ne_zero)
      (hva.trans hvb.symm)
      (by simpa using Nat.pos_of_ne_zero htLength)
    simpa [pa, pb] using hstep.2
  exact ⟨pa, pb, da, db, hpa, hpb, rfl, rfl, hinterlaced⟩

/-- Strictly precomposing a common lower bound transports its two outgoing
arrow presentations into one proper-whisker interlacement at the lower ray. -/
theorem exists_interlaced_presentations_of_strict_commonLower
    [Finite C] [IsFiniteRayCategory C]
    {x : RayVertex C} (a b : OutgoingQuiverArrow x)
    (u mu : NonzeroMorphismTo x.obj)
    (hua : u ≤ (outgoingQuiverArrowNonzeroHom (C := C) a).toMorphismTo)
    (hub : u ≤ (outgoingQuiverArrowNonzeroHom (C := C) b).toMorphismTo)
    (hMuU : mu ≤ u) (hUNotLeMu : ¬u ≤ mu) :
    ∃ (pa pb : Quiver.Path x (RayVertex.mk mu.source))
      (da : PathInitialDecomposition pa) (db : PathInitialDecomposition pb),
      rayPathMap pa = mu.hom ∧ rayPathMap pb = mu.hom ∧
        (⟨da.middle, da.arrow⟩ : OutgoingQuiverArrow x) = a ∧
        (⟨db.middle, db.arrow⟩ : OutgoingQuiverArrow x) = b ∧
        (properWhiskerInterlacementRelation
          (rayPathContourRelation (C := C))).interlaced pa pb := by
  obtain ⟨fa, hfa⟩ := hua
  obtain ⟨fb, hfb⟩ := hub
  obtain ⟨h, hh⟩ := hMuU
  have hfa0 : fa ≠ 0 := by
    intro hz; apply u.ne_zero; rw [← hfa, hz, zero_comp]
  have hfb0 : fb ≠ 0 := by
    intro hz; apply u.ne_zero; rw [← hfb, hz, zero_comp]
  have hh0 : h ≠ 0 := by
    intro hz; apply mu.ne_zero; rw [← hh, hz, zero_comp]
  have hhNotIso : ¬IsIso h := by
    intro hIso
    letI : IsIso h := hIso
    apply hUNotLeMu
    refine ⟨inv h, ?_⟩
    rw [← hh, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  obtain ⟨qa, hqa⟩ := exists_rayPathMap_eq_of_ne_zero
    (C := C) (i := a.1) (j := RayVertex.mk u.source) fa hfa0
  obtain ⟨qb, hqb⟩ := exists_rayPathMap_eq_of_ne_zero
    (C := C) (i := b.1) (j := RayVertex.mk u.source) fb hfb0
  obtain ⟨t, ht⟩ := exists_rayPathMap_eq_of_ne_zero
    (C := C) (i := RayVertex.mk u.source)
      (j := RayVertex.mk mu.source) h hh0
  have htLength : t.length ≠ 0 := by
    intro ht0; apply hhNotIso; rw [← ht]
    exact rayPathMap_isIso_of_length_eq_zero t ht0
  let va := a.2.toPath.comp qa
  let vb := b.2.toPath.comp qb
  have hva : rayPathMap va = u.hom := by
    calc
      rayPathMap va = rayPathMap qa ≫ rayPathMap a.2.toPath := by
        exact LinearPathCategory.pathMap_comp
          RayVertex.obj rayArrowMorphism a.2.toPath qa
      _ = fa ≫ rayArrowMorphism a.2 := by rw [rayPathMap_toPath, hqa]
      _ = u.hom := hfa
  have hvb : rayPathMap vb = u.hom := by
    calc
      rayPathMap vb = rayPathMap qb ≫ rayPathMap b.2.toPath := by
        exact LinearPathCategory.pathMap_comp
          RayVertex.obj rayArrowMorphism b.2.toPath qb
      _ = fb ≫ rayArrowMorphism b.2 := by rw [rayPathMap_toPath, hqb]
      _ = u.hom := hfb
  let pa := va.comp t
  let pb := vb.comp t
  have hpa : rayPathMap pa = mu.hom := by
    simp only [pa, rayPathMap, LinearPathCategory.pathMap_comp]
    change rayPathMap t ≫ rayPathMap va = mu.hom
    rw [hva, ht]
    exact hh
  have hpb : rayPathMap pb = mu.hom := by
    simp only [pb, rayPathMap, LinearPathCategory.pathMap_comp]
    change rayPathMap t ≫ rayPathMap vb = mu.hom
    rw [hvb, ht]
    exact hh
  let da : PathInitialDecomposition pa := {
    middle := a.1
    arrow := a.2
    tail := qa.comp t
    path_eq := by simp [pa, va] }
  let db : PathInitialDecomposition pb := {
    middle := b.1
    arrow := b.2
    tail := qb.comp t
    path_eq := by simp [pb, vb] }
  have hinterlaced : (properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced pa pb := by
    have hstep := rayPaths_related_and_interlaced_of_inner_map_eq
      Quiver.Path.nil va vb t
      (by rw [Quiver.Path.nil_comp, hpa]; exact mu.ne_zero)
      (hva.trans hvb.symm)
      (by simpa using Nat.pos_of_ne_zero htLength)
    simpa [pa, pb] using hstep.2
  exact ⟨pa, pb, da, db, hpa, hpb, rfl, rfl, hinterlaced⟩

/-- The composite ray of an essential contour is the pair supremum of its two
final-arrow rays in the fixed-source factorization order. -/
theorem isRayPairSupremum_rayPathMorphism_of_essential_finalDecompositions
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [IsRayCrownFree C]
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (dp : PathFinalDecomposition p) (dq : PathFinalDecomposition q)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (hpqNot : ¬(properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p q) :
    IsRayPairSupremum
      dp.rayArrowNonzeroHom.toMorphismFrom
      dq.rayArrowNonzeroHom.toMorphismFrom
      (rayPathMorphism p hpq.1) := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  let mu := rayPathMorphism p hpq.1
  have hq : rayPathMap q ≠ 0 := by
    rw [← hpq.2]
    exact hpq.1
  have hdpMu : dp.rayArrowNonzeroHom.toMorphismFrom ≤ mu :=
    dp.rayArrow_le_rayPathMorphism hpq.1
  have hdqMu : dq.rayArrowNonzeroHom.toMorphismFrom ≤ mu := by
    change dq.rayArrowNonzeroHom.toMorphismFrom ≤
      rayPathMorphism p hpq.1
    rw [rayPathMorphism_eq_of_related p q hpq]
    exact dq.rayArrow_le_rayPathMorphism hq
  refine ⟨hdpMu, hdqMu, ?_⟩
  intro u hdpu hdqu
  let apCode : IncomingQuiverArrow z := ⟨dp.middle, dp.arrow⟩
  let aqCode : IncomingQuiverArrow z := ⟨dq.middle, dq.arrow⟩
  have hcodes : apCode ≠ aqCode := by
    intro hcode
    apply hpqNot
    exact rayPaths_interlaced_of_finalDecomposition_code_eq
      dp dq hpq hcode
  have hsource : RaySourceIncomparable
      dp.rayArrowNonzeroHom dq.rayArrowNonzeroHom := by
    simpa [apCode, aqCode, incomingQuiverArrowNonzeroHom,
      PathFinalDecomposition.rayArrowNonzeroHom] using
      (incomingQuiverArrow_raySourceIncomparable_of_ne
        (C := C) hcodes)
  have hinc : OrderIncomparable
      dp.rayArrowNonzeroHom.toMorphismFrom
      dq.rayArrowNonzeroHom.toMorphismFrom := by
    exact (raySourceIncomparable_iff
      dp.rayArrowNonzeroHom dq.rayArrowNonzeroHom).1 hsource
  have hcomparable : mu ≤ u ∨ u ≤ mu :=
    comparable_commonUpperBounds_of_noFourCrown
      (IsRayCrownFree.no_four z.obj) hinc
      hdpMu hdqMu hdpu hdqu
  rcases hcomparable with hmu | humu
  · exact hmu
  · obtain ⟨h, huh⟩ := humu
    by_cases hIso : IsIso h
    · letI : IsIso h := hIso
      refine ⟨inv h, ?_⟩
      change u.hom ≫ h = mu.hom at huh
      rw [← huh, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    · exfalso
      have hh : h ≠ 0 := by
        intro hz
        apply hpq.1
        change u.hom ≫ h = rayPathMap p at huh
        rw [hz, comp_zero] at huh
        exact huh.symm
      obtain ⟨a, ha⟩ := hdpu
      obtain ⟨b, hb⟩ := hdqu
      change rayArrowMorphism dp.arrow ≫ a = u.hom at ha
      change rayArrowMorphism dq.arrow ≫ b = u.hom at hb
      change u.hom ≫ h = rayPathMap p at huh
      have ha0 : a ≠ 0 := by
        intro hz
        apply u.ne_zero
        rw [← ha, hz, comp_zero]
      have hb0 : b ≠ 0 := by
        intro hz
        apply u.ne_zero
        rw [← hb, hz, comp_zero]
      obtain ⟨pa, hpa⟩ := exists_rayPathMap_eq_of_ne_zero
        (C := C) (i := RayVertex.mk u.target) (j := dp.middle) a ha0
      obtain ⟨pb, hpb⟩ := exists_rayPathMap_eq_of_ne_zero
        (C := C) (i := RayVertex.mk u.target) (j := dq.middle) b hb0
      obtain ⟨t, ht⟩ := exists_rayPathMap_eq_of_ne_zero
        (C := C) (i := x) (j := RayVertex.mk u.target) h hh
      have htLength : t.length ≠ 0 := by
        intro ht0
        apply hIso
        rw [← ht]
        exact rayPathMap_isIso_of_length_eq_zero t ht0
      let vp := pa.comp dp.arrow.toPath
      let vq := pb.comp dq.arrow.toPath
      have hvp : rayPathMap vp = u.hom := by
        calc
          rayPathMap vp =
              rayPathMap dp.arrow.toPath ≫ rayPathMap pa := by
            exact LinearPathCategory.pathMap_comp
              RayVertex.obj rayArrowMorphism pa dp.arrow.toPath
          _ = rayArrowMorphism dp.arrow ≫ a := by
            rw [rayPathMap_toPath, hpa]
          _ = u.hom := ha
      have hvq : rayPathMap vq = u.hom := by
        calc
          rayPathMap vq =
              rayPathMap dq.arrow.toPath ≫ rayPathMap pb := by
            exact LinearPathCategory.pathMap_comp
              RayVertex.obj rayArrowMorphism pb dq.arrow.toPath
          _ = rayArrowMorphism dq.arrow ≫ b := by
            rw [rayPathMap_toPath, hpb]
          _ = u.hom := hb
      have houterP : rayPathMap ((t.comp vp).comp Quiver.Path.nil) =
          rayPathMap p := by
        simp only [Quiver.Path.comp_nil, rayPathMap,
          LinearPathCategory.pathMap_comp]
        change rayPathMap vp ≫ rayPathMap t = rayPathMap p
        rw [hvp, ht]
        exact huh
      have houterQ : rayPathMap ((t.comp vq).comp Quiver.Path.nil) =
          rayPathMap p := by
        simp only [Quiver.Path.comp_nil, rayPathMap,
          LinearPathCategory.pathMap_comp]
        change rayPathMap vq ≫ rayPathMap t = rayPathMap p
        rw [hvq, ht]
        exact huh
      have hstep : PI.interlaced
          ((t.comp vp).comp Quiver.Path.nil)
          ((t.comp vq).comp Quiver.Path.nil) :=
        (rayPaths_related_and_interlaced_of_inner_map_eq
          t vp vq Quiver.Path.nil
          (by rw [houterP]; exact hpq.1)
          (hvp.trans hvq.symm)
          (by simpa using Nat.pos_of_ne_zero htLength)).2
      have hpPath : ((t.comp vp).comp Quiver.Path.nil) =
          (t.comp pa).comp dp.arrow.toPath := by
        simp [vp]
      have hqPath : ((t.comp vq).comp Quiver.Path.nil) =
          (t.comp pb).comp dq.arrow.toPath := by
        simp [vq]
      have hip : PI.interlaced p
          ((t.comp vp).comp Quiver.Path.nil) := by
        rw [dp.path_eq, hpPath]
        apply rayPaths_interlaced_of_commonFinalArrow
        refine ⟨?_, ?_⟩
        · rw [← dp.path_eq]
          exact hpq.1
        · rw [← dp.path_eq, ← hpPath]
          exact houterP.symm
      have hiq : PI.interlaced q
          ((t.comp vq).comp Quiver.Path.nil) := by
        rw [dq.path_eq, hqPath]
        apply rayPaths_interlaced_of_commonFinalArrow
        refine ⟨?_, ?_⟩
        · rw [← dq.path_eq]
          exact hq
        · rw [← dq.path_eq, ← hqPath]
          exact hpq.2.symm.trans houterQ.symm
      exact hpqNot (PI.trans hip (PI.trans hstep (PI.symm hiq)))

/-- The orientation-dual statement: the composite ray of an essential contour
is the pair infimum of its two initial-arrow rays in the fixed-target
factorization order. -/
theorem isRayPairInfimum_rayPathMorphismTo_of_essential_initialDecompositions
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [IsRayCocrownFree C]
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (dp : PathInitialDecomposition p) (dq : PathInitialDecomposition q)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (hpqNot : ¬(properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p q) :
    IsRayPairInfimum
      dp.rayArrowNonzeroHom.toMorphismTo
      dq.rayArrowNonzeroHom.toMorphismTo
      (rayPathMorphismTo p hpq.1) := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  let mu := rayPathMorphismTo p hpq.1
  have hq : rayPathMap q ≠ 0 := by
    rw [← hpq.2]
    exact hpq.1
  have hMuDp : mu ≤ dp.rayArrowNonzeroHom.toMorphismTo :=
    dp.rayPathMorphismTo_le_rayArrow hpq.1
  have hMuDq : mu ≤ dq.rayArrowNonzeroHom.toMorphismTo := by
    change rayPathMorphismTo p hpq.1 ≤
      dq.rayArrowNonzeroHom.toMorphismTo
    rw [rayPathMorphismTo_eq_of_related p q hpq]
    exact dq.rayPathMorphismTo_le_rayArrow hq
  refine ⟨hMuDp, hMuDq, ?_⟩
  intro u hudp hudq
  let apCode : OutgoingQuiverArrow x := ⟨dp.middle, dp.arrow⟩
  let aqCode : OutgoingQuiverArrow x := ⟨dq.middle, dq.arrow⟩
  have hcodes : apCode ≠ aqCode := by
    intro hcode
    apply hpqNot
    exact rayPaths_interlaced_of_initialDecomposition_code_eq
      dp dq hpq hcode
  have htarget : RayTargetIncomparable
      dp.rayArrowNonzeroHom dq.rayArrowNonzeroHom := by
    simpa [apCode, aqCode, outgoingQuiverArrowNonzeroHom,
      PathInitialDecomposition.rayArrowNonzeroHom] using
      (outgoingQuiverArrow_rayTargetIncomparable_of_ne
        (C := C) hcodes)
  have hinc : OrderIncomparable
      dp.rayArrowNonzeroHom.toMorphismTo
      dq.rayArrowNonzeroHom.toMorphismTo := htarget
  have hcomparable : mu ≤ u ∨ u ≤ mu :=
    comparable_commonLowerBounds_of_noFourCrown
      (IsRayCocrownFree.no_four x.obj) hinc
      hMuDp hMuDq hudp hudq
  rcases hcomparable with hmuu | humu
  · obtain ⟨h, huh⟩ := hmuu
    by_cases hIso : IsIso h
    · letI : IsIso h := hIso
      refine ⟨inv h, ?_⟩
      change h ≫ u.hom = mu.hom at huh
      rw [← huh, ← Category.assoc, IsIso.inv_hom_id,
        Category.id_comp]
    · exfalso
      have hh : h ≠ 0 := by
        intro hz
        apply hpq.1
        change h ≫ u.hom = rayPathMap p at huh
        rw [hz, zero_comp] at huh
        exact huh.symm
      obtain ⟨a, ha⟩ := hudp
      obtain ⟨b, hb⟩ := hudq
      change a ≫ rayArrowMorphism dp.arrow = u.hom at ha
      change b ≫ rayArrowMorphism dq.arrow = u.hom at hb
      change h ≫ u.hom = rayPathMap p at huh
      have ha0 : a ≠ 0 := by
        intro hz
        apply u.ne_zero
        rw [← ha, hz, zero_comp]
      have hb0 : b ≠ 0 := by
        intro hz
        apply u.ne_zero
        rw [← hb, hz, zero_comp]
      obtain ⟨pa, hpa⟩ := exists_rayPathMap_eq_of_ne_zero
        (C := C) (i := dp.middle) (j := RayVertex.mk u.source) a ha0
      obtain ⟨pb, hpb⟩ := exists_rayPathMap_eq_of_ne_zero
        (C := C) (i := dq.middle) (j := RayVertex.mk u.source) b hb0
      obtain ⟨t, ht⟩ := exists_rayPathMap_eq_of_ne_zero
        (C := C) (i := RayVertex.mk u.source) (j := z) h hh
      have htLength : t.length ≠ 0 := by
        intro ht0
        apply hIso
        rw [← ht]
        exact rayPathMap_isIso_of_length_eq_zero t ht0
      let vp := dp.arrow.toPath.comp pa
      let vq := dq.arrow.toPath.comp pb
      have hvp : rayPathMap vp = u.hom := by
        calc
          rayPathMap vp = rayPathMap pa ≫
              rayPathMap dp.arrow.toPath := by
            exact LinearPathCategory.pathMap_comp
              RayVertex.obj rayArrowMorphism dp.arrow.toPath pa
          _ = a ≫ rayArrowMorphism dp.arrow := by
            rw [rayPathMap_toPath, hpa]
          _ = u.hom := ha
      have hvq : rayPathMap vq = u.hom := by
        calc
          rayPathMap vq = rayPathMap pb ≫
              rayPathMap dq.arrow.toPath := by
            exact LinearPathCategory.pathMap_comp
              RayVertex.obj rayArrowMorphism dq.arrow.toPath pb
          _ = b ≫ rayArrowMorphism dq.arrow := by
            rw [rayPathMap_toPath, hpb]
          _ = u.hom := hb
      have houterP : rayPathMap
          ((Quiver.Path.nil.comp vp).comp t) = rayPathMap p := by
        simp only [Quiver.Path.nil_comp, rayPathMap,
          LinearPathCategory.pathMap_comp]
        change rayPathMap t ≫ rayPathMap vp = rayPathMap p
        rw [hvp, ht]
        exact huh
      have houterQ : rayPathMap
          ((Quiver.Path.nil.comp vq).comp t) = rayPathMap p := by
        simp only [Quiver.Path.nil_comp, rayPathMap,
          LinearPathCategory.pathMap_comp]
        change rayPathMap t ≫ rayPathMap vq = rayPathMap p
        rw [hvq, ht]
        exact huh
      have hstep : PI.interlaced
          ((Quiver.Path.nil.comp vp).comp t)
          ((Quiver.Path.nil.comp vq).comp t) :=
        (rayPaths_related_and_interlaced_of_inner_map_eq
          Quiver.Path.nil vp vq t
          (by rw [houterP]; exact hpq.1)
          (hvp.trans hvq.symm)
          (by simpa using Nat.pos_of_ne_zero htLength)).2
      have hpPath : ((Quiver.Path.nil.comp vp).comp t) =
          dp.arrow.toPath.comp (pa.comp t) := by
        simp [vp]
      have hqPath : ((Quiver.Path.nil.comp vq).comp t) =
          dq.arrow.toPath.comp (pb.comp t) := by
        simp [vq]
      have hip : PI.interlaced p
          ((Quiver.Path.nil.comp vp).comp t) := by
        rw [dp.path_eq, hpPath]
        apply rayPaths_interlaced_of_commonInitialArrow
        refine ⟨?_, ?_⟩
        · rw [← dp.path_eq]
          exact hpq.1
        · rw [← dp.path_eq, ← hpPath]
          exact houterP.symm
      have hiq : PI.interlaced q
          ((Quiver.Path.nil.comp vq).comp t) := by
        rw [dq.path_eq, hqPath]
        apply rayPaths_interlaced_of_commonInitialArrow
        refine ⟨?_, ?_⟩
        · rw [← dq.path_eq]
          exact hq
        · rw [← dq.path_eq, ← hqPath]
          exact hpq.2.symm.trans houterQ.symm
      exact hpqNot (PI.trans hip (PI.trans hstep (PI.symm hiq)))
  · exact humu

/-- If a killed essential contour and a surviving essential contour share one
final arrow, then their other final arrows are distinct.  Otherwise the two
pair-supremum descriptions force the surviving composite into the killed
principal ideal. -/
theorem otherFinalArrow_ne_of_principal_survivor
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [IsRayCrownFree C]
    {x y z : RayVertex C}
    {p q : Quiver.Path x z} {r s : Quiver.Path y z}
    (hpq : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (hrs : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) r s)
    (hrSurvives : ¬(principalZeroHomIdeal (rayPathMap p)).mem
      (rayPathMap r))
    (dp : PathFinalDecomposition p) (dq : PathFinalDecomposition q)
    (dr : PathFinalDecomposition r) (ds : PathFinalDecomposition s)
    (hshared : (⟨dp.middle, dp.arrow⟩ : IncomingQuiverArrow z) =
      ⟨dr.middle, dr.arrow⟩) :
    (⟨dq.middle, dq.arrow⟩ : IncomingQuiverArrow z) ≠
      ⟨ds.middle, ds.arrow⟩ := by
  intro hother
  let mu := rayPathMorphism p hpq.1.1
  let nu := rayPathMorphism r hrs.1.1
  have hpSup :=
    isRayPairSupremum_rayPathMorphism_of_essential_finalDecompositions
      dp dq hpq.1 hpq.2
  have hrSup :=
    isRayPairSupremum_rayPathMorphism_of_essential_finalDecompositions
      dr ds hrs.1 hrs.2
  have hdpNu : dp.rayArrowNonzeroHom.toMorphismFrom ≤ nu := by
    have h := hrSup.1
    change (incomingQuiverArrowNonzeroHom (C := C)
      (⟨dr.middle, dr.arrow⟩ : IncomingQuiverArrow z)).toMorphismFrom ≤
        nu at h
    rw [← hshared] at h
    exact h
  have hdqNu : dq.rayArrowNonzeroHom.toMorphismFrom ≤ nu := by
    have h := hrSup.2.1
    change (incomingQuiverArrowNonzeroHom (C := C)
      (⟨ds.middle, ds.arrow⟩ : IncomingQuiverArrow z)).toMorphismFrom ≤
        nu at h
    rw [← hother] at h
    exact h
  have hmuNu : mu ≤ nu := hpSup.2.2 nu hdpNu hdqNu
  apply hrSurvives
  change FactorsThroughMorphism (rayPathMap p) (rayPathMap r)
  obtain ⟨h, hh⟩ := hmuNu
  refine ⟨𝟙 z.obj, h, ?_⟩
  change rayPathMap r = 𝟙 z.obj ≫ rayPathMap p ≫ h
  simpa [mu, nu, rayPathMorphism] using hh.symm

/-- If a surviving essential contour shares a final arrow with a killed
essential contour, that shared arrow lies below every pair supremum of the two
other final arrows.  The contrary orientation would interlace the killed
contour through two strict common-upper-bound presentations. -/
theorem sharedFinalArrow_le_outerSupremum_of_principal_survivor
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [IsRayCrownFree C]
    {x y z : RayVertex C}
    {p q : Quiver.Path x z} {r s : Quiver.Path y z}
    (hpq : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (hrs : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) r s)
    (hrSurvives : ¬(principalZeroHomIdeal (rayPathMap p)).mem
      (rayPathMap r))
    (dp : PathFinalDecomposition p) (dq : PathFinalDecomposition q)
    (dr : PathFinalDecomposition r) (ds : PathFinalDecomposition s)
    (hshared : (⟨dp.middle, dp.arrow⟩ : IncomingQuiverArrow z) =
      ⟨dr.middle, dr.arrow⟩)
    (outer : NonzeroMorphismFrom z.obj)
    (houter : IsRayPairSupremum
      dq.rayArrowNonzeroHom.toMorphismFrom
      ds.rayArrowNonzeroHom.toMorphismFrom outer) :
    dp.rayArrowNonzeroHom.toMorphismFrom ≤ outer := by
  by_contra hbad
  let gamma := dp.rayArrowNonzeroHom.toMorphismFrom
  let beta := dq.rayArrowNonzeroHom.toMorphismFrom
  let delta := ds.rayArrowNonzeroHom.toMorphismFrom
  let mu := rayPathMorphism p hpq.1.1
  let nu := rayPathMorphism r hrs.1.1
  let I := properWhiskerInterlacementRelation
    (rayPathContourRelation (C := C))
  have hpSup := isRayPairSupremum_rayPathMorphism_of_essential_finalDecompositions
    dp dq hpq.1 hpq.2
  have hrSup := isRayPairSupremum_rayPathMorphism_of_essential_finalDecompositions
    dr ds hrs.1 hrs.2
  have hgammaEq : dr.rayArrowNonzeroHom.toMorphismFrom = gamma := by
    change (incomingQuiverArrowNonzeroHom (C := C)
      (⟨dr.middle, dr.arrow⟩ : IncomingQuiverArrow z)).toMorphismFrom = gamma
    rw [← hshared]
    rfl
  have hrSup' : IsRayPairSupremum gamma delta nu := by
    simpa [delta, nu, hgammaEq] using hrSup
  have hbetaDeltaCode :
      (⟨dq.middle, dq.arrow⟩ : IncomingQuiverArrow z) ≠
        ⟨ds.middle, ds.arrow⟩ :=
    otherFinalArrow_ne_of_principal_survivor hpq hrs hrSurvives
      dp dq dr ds hshared
  have hgammaBetaCode :
      (⟨dp.middle, dp.arrow⟩ : IncomingQuiverArrow z) ≠
        ⟨dq.middle, dq.arrow⟩ := by
    intro h
    exact hpq.2
      (rayPaths_interlaced_of_finalDecomposition_code_eq dp dq hpq.1 h)
  have hgammaDeltaCode :
      (⟨dp.middle, dp.arrow⟩ : IncomingQuiverArrow z) ≠
        ⟨ds.middle, ds.arrow⟩ := by
    intro h
    apply hrs.2
    exact rayPaths_interlaced_of_finalDecomposition_code_eq dr ds hrs.1
      (hshared.symm.trans h)
  have hgammaBeta : OrderIncomparable gamma beta := by
    exact (raySourceIncomparable_iff
      dp.rayArrowNonzeroHom dq.rayArrowNonzeroHom).1 (by
        simpa [gamma, beta, incomingQuiverArrowNonzeroHom,
          PathFinalDecomposition.rayArrowNonzeroHom] using
          (incomingQuiverArrow_raySourceIncomparable_of_ne
            (C := C) hgammaBetaCode))
  have hgammaDelta : OrderIncomparable gamma delta := by
    exact (raySourceIncomparable_iff
      dp.rayArrowNonzeroHom ds.rayArrowNonzeroHom).1 (by
        simpa [gamma, delta, incomingQuiverArrowNonzeroHom,
          PathFinalDecomposition.rayArrowNonzeroHom] using
          (incomingQuiverArrow_raySourceIncomparable_of_ne
            (C := C) hgammaDeltaCode))
  have hbetaDelta : OrderIncomparable beta delta := by
    exact (raySourceIncomparable_iff
      dq.rayArrowNonzeroHom ds.rayArrowNonzeroHom).1 (by
        simpa [beta, delta, incomingQuiverArrowNonzeroHom,
          PathFinalDecomposition.rayArrowNonzeroHom] using
          (incomingQuiverArrow_raySourceIncomparable_of_ne
            (C := C) hbetaDeltaCode))
  have hmuNotLeNu : ¬mu ≤ nu := by
    intro hmuNu
    apply hrSurvives
    change FactorsThroughMorphism (rayPathMap p) (rayPathMap r)
    obtain ⟨h, hh⟩ := hmuNu
    refine ⟨𝟙 z.obj, h, ?_⟩
    change rayPathMap r = 𝟙 z.obj ≫ rayPathMap p ≫ h
    simpa [mu, nu, rayPathMorphism] using hh.symm
  rcases rayPairSuprema_dominating_of_crownFree
      hgammaBeta hgammaDelta hbetaDelta hpSup houter hrSup' with
    hnuTop | houterTop | hmuTop
  · exact hmuNotLeNu hnuTop.1
  · exact hbad (hpSup.1.trans houterTop.1)
  · have hmuNotLeOuter : ¬mu ≤ outer := by
      intro hmuOuter
      exact hbad (hpSup.1.trans hmuOuter)
    have hdrNu : (incomingQuiverArrowNonzeroHom (C := C)
        (⟨dr.middle, dr.arrow⟩ : IncomingQuiverArrow z)).toMorphismFrom ≤ nu := by
      simpa [nu, incomingQuiverArrowNonzeroHom,
        PathFinalDecomposition.rayArrowNonzeroHom] using hrSup.1
    have hdsNu : (incomingQuiverArrowNonzeroHom (C := C)
        (⟨ds.middle, ds.arrow⟩ : IncomingQuiverArrow z)).toMorphismFrom ≤ nu := by
      simpa [nu, incomingQuiverArrowNonzeroHom,
        PathFinalDecomposition.rayArrowNonzeroHom] using hrSup.2.1
    obtain ⟨pr, ps, dpr, dps, hpr, hps, hdpr, hdps, hiRS⟩ :=
      exists_interlaced_presentations_of_strict_commonUpper (C := C)
        (⟨dr.middle, dr.arrow⟩ : IncomingQuiverArrow z)
        (⟨ds.middle, ds.arrow⟩ : IncomingQuiverArrow z)
        nu mu hdrNu hdsNu hmuTop.2 hmuNotLeNu
    have hdqOuter : (incomingQuiverArrowNonzeroHom (C := C)
        (⟨dq.middle, dq.arrow⟩ : IncomingQuiverArrow z)).toMorphismFrom ≤ outer := by
      simpa [incomingQuiverArrowNonzeroHom,
        PathFinalDecomposition.rayArrowNonzeroHom] using houter.1
    have hdsOuter : (incomingQuiverArrowNonzeroHom (C := C)
        (⟨ds.middle, ds.arrow⟩ : IncomingQuiverArrow z)).toMorphismFrom ≤ outer := by
      simpa [incomingQuiverArrowNonzeroHom,
        PathFinalDecomposition.rayArrowNonzeroHom] using houter.2.1
    obtain ⟨pb, pd, dpb, dpd, hpb, hpd, hdpb, hdpd, hiBD⟩ :=
      exists_interlaced_presentations_of_strict_commonUpper (C := C)
        (⟨dq.middle, dq.arrow⟩ : IncomingQuiverArrow z)
        (⟨ds.middle, ds.arrow⟩ : IncomingQuiverArrow z)
        outer mu hdqOuter hdsOuter hmuTop.1 hmuNotLeOuter
    have hppr : (rayPathContourRelation (C := C)).related p pr := by
      refine ⟨hpq.1.1, ?_⟩
      simpa [mu, rayPathMorphism] using hpr.symm
    have hq : rayPathMap q ≠ 0 := by
      rw [← hpq.1.2]
      exact hpq.1.1
    have hqpb : (rayPathContourRelation (C := C)).related q pb := by
      refine ⟨hq, ?_⟩
      calc
        rayPathMap q = rayPathMap p := hpq.1.2.symm
        _ = mu.hom := rfl
        _ = rayPathMap pb := hpb.symm
    have hpspd : (rayPathContourRelation (C := C)).related ps pd := by
      refine ⟨?_, hps.trans hpd.symm⟩
      rw [hps]
      exact mu.ne_zero
    have hiPPr : I.interlaced p pr :=
      rayPaths_interlaced_of_finalDecomposition_code_eq dp dpr hppr
        (hshared.trans hdpr.symm)
    have hiQPb : I.interlaced q pb :=
      rayPaths_interlaced_of_finalDecomposition_code_eq dq dpb hqpb
        hdpb.symm
    have hiPsPd : I.interlaced ps pd :=
      rayPaths_interlaced_of_finalDecomposition_code_eq dps dpd hpspd
        (hdps.trans hdpd.symm)
    apply hpq.2
    exact I.trans hiPPr
      (I.trans hiRS
        (I.trans hiPsPd
          (I.trans (I.symm hiBD) (I.symm hiQPb))))

/-- A killed essential contour and a surviving essential contour sharing a
final arrow automatically have the BGRS Figure 58-or-60 orientation. -/
theorem isRayThreeArrowFigure_of_essential_finalContours_principal_survivor
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [IsRayCrownFree C]
    {x y z : RayVertex C}
    {p q : Quiver.Path x z} {r s : Quiver.Path y z}
    (hpq : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (hrs : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) r s)
    (hrSurvives : ¬(principalZeroHomIdeal (rayPathMap p)).mem (rayPathMap r))
    (dp : PathFinalDecomposition p) (dq : PathFinalDecomposition q)
    (dr : PathFinalDecomposition r) (ds : PathFinalDecomposition s)
    (hshared : (⟨dp.middle, dp.arrow⟩ : IncomingQuiverArrow z) =
      ⟨dr.middle, dr.arrow⟩) :
    IsRayThreeArrowFigure
      dq.rayArrowNonzeroHom.toMorphismFrom
      dp.rayArrowNonzeroHom.toMorphismFrom
      ds.rayArrowNonzeroHom.toMorphismFrom := by
  have hpSup := isRayPairSupremum_rayPathMorphism_of_essential_finalDecompositions
    dp dq hpq.1 hpq.2
  have hrSup := isRayPairSupremum_rayPathMorphism_of_essential_finalDecompositions
    dr ds hrs.1 hrs.2
  by_cases houter : ∃ outer : NonzeroMorphismFrom z.obj,
      IsRayPairSupremum dq.rayArrowNonzeroHom.toMorphismFrom
        ds.rayArrowNonzeroHom.toMorphismFrom outer
  · obtain ⟨outer, houter⟩ := houter
    exact Or.inl ⟨outer, houter,
      sharedFinalArrow_le_outerSupremum_of_principal_survivor
        hpq hrs hrSurvives dp dq dr ds hshared outer houter⟩
  · refine Or.inr ⟨?_, ?_, houter⟩
    · exact ⟨rayPathMorphism p hpq.1.1,
        hpSup.2.1, hpSup.1,
        fun u hbeta hgamma => hpSup.2.2 u hgamma hbeta⟩
    · refine ⟨rayPathMorphism r hrs.1.1, ?_⟩
      have hgammaEq : dr.rayArrowNonzeroHom.toMorphismFrom =
          dp.rayArrowNonzeroHom.toMorphismFrom := by
        change (incomingQuiverArrowNonzeroHom (C := C)
          (⟨dr.middle, dr.arrow⟩ : IncomingQuiverArrow z)).toMorphismFrom =
            dp.rayArrowNonzeroHom.toMorphismFrom
        rw [← hshared]
        rfl
      simpa [hgammaEq] using hrSup

/-- At an incoming-three-valent endpoint, every surviving essential contour
uses the two surviving arrows in opposite order once the killed-versus-
surviving contours have the BGRS three-arrow orientation. -/
theorem survivingEssentialContour_finalArrow_pair_eq_sharedPair_of_figure
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [IsRayCrownFree C]
    {x y w z : RayVertex C}
    {p q : Quiver.Path x z} {r s : Quiver.Path y z}
    {u v : Quiver.Path w z}
    (hpq : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (hrs : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) r s)
    (huv : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) u v)
    (hrSurvives : ¬(principalZeroHomIdeal (rayPathMap p)).mem
      (rayPathMap r))
    (huSurvives : ¬(principalZeroHomIdeal (rayPathMap p)).mem
      (rayPathMap u))
    (dp : PathFinalDecomposition p) (dq : PathFinalDecomposition q)
    (dr : PathFinalDecomposition r) (ds : PathFinalDecomposition s)
    (du : PathFinalDecomposition u) (dv : PathFinalDecomposition v)
    (hshared : (⟨dp.middle, dp.arrow⟩ : IncomingQuiverArrow z) =
      ⟨dr.middle, dr.arrow⟩)
    (hfigure : IsRayThreeArrowFigure
      dq.rayArrowNonzeroHom.toMorphismFrom
      dp.rayArrowNonzeroHom.toMorphismFrom
      ds.rayArrowNonzeroHom.toMorphismFrom)
    (hcard : Nat.card (IncomingQuiverArrow z) ≤ 3) :
    ((⟨du.middle, du.arrow⟩ : IncomingQuiverArrow z) =
        ⟨dp.middle, dp.arrow⟩ ∧
      (⟨dv.middle, dv.arrow⟩ : IncomingQuiverArrow z) =
        ⟨ds.middle, ds.arrow⟩) ∨
    ((⟨du.middle, du.arrow⟩ : IncomingQuiverArrow z) =
        ⟨ds.middle, ds.arrow⟩ ∧
      (⟨dv.middle, dv.arrow⟩ : IncomingQuiverArrow z) =
        ⟨dp.middle, dp.arrow⟩) := by
  let beta : IncomingQuiverArrow z := ⟨dq.middle, dq.arrow⟩
  let gamma : IncomingQuiverArrow z := ⟨dp.middle, dp.arrow⟩
  let delta : IncomingQuiverArrow z := ⟨ds.middle, ds.arrow⟩
  let epsilon : IncomingQuiverArrow z := ⟨du.middle, du.arrow⟩
  let phi : IncomingQuiverArrow z := ⟨dv.middle, dv.arrow⟩
  let mu := rayPathMorphism p hpq.1.1
  let eta := rayPathMorphism u huv.1.1
  have hbetaGamma : beta ≠ gamma := by
    intro h
    apply hpq.2
    apply rayPaths_interlaced_of_finalDecomposition_code_eq dp dq hpq.1
    exact h.symm
  have hgammaDelta : gamma ≠ delta := by
    intro h
    apply hrs.2
    apply rayPaths_interlaced_of_finalDecomposition_code_eq dr ds hrs.1
    calc
      (⟨dr.middle, dr.arrow⟩ : IncomingQuiverArrow z) = gamma := hshared.symm
      _ = delta := h
  have hbetaDelta : beta ≠ delta :=
    otherFinalArrow_ne_of_principal_survivor hpq hrs hrSurvives
      dp dq dr ds hshared
  have hepsilonPhi : epsilon ≠ phi := by
    intro h
    apply huv.2
    exact rayPaths_interlaced_of_finalDecomposition_code_eq du dv huv.1 h
  have hpSup0 :=
    isRayPairSupremum_rayPathMorphism_of_essential_finalDecompositions
      dp dq hpq.1 hpq.2
  have hpSup : IsRayPairSupremum
      dq.rayArrowNonzeroHom.toMorphismFrom
      dp.rayArrowNonzeroHom.toMorphismFrom mu :=
    ⟨hpSup0.2.1, hpSup0.1,
      fun t hbeta hgamma => hpSup0.2.2 t hgamma hbeta⟩
  have huvSup0 :=
    isRayPairSupremum_rayPathMorphism_of_essential_finalDecompositions
      du dv huv.1 huv.2
  have hmem_of_mu_le_eta (hmueta : mu ≤ eta) :
      (principalZeroHomIdeal (rayPathMap p)).mem (rayPathMap u) := by
    change FactorsThroughMorphism (rayPathMap p) (rayPathMap u)
    obtain ⟨h, hh⟩ := hmueta
    refine ⟨𝟙 z.obj, h, ?_⟩
    change rayPathMap u = 𝟙 z.obj ≫ rayPathMap p ≫ h
    simpa [mu, eta, rayPathMorphism] using hh.symm
  have hNoBetaGamma :
      ¬((epsilon = beta ∧ phi = gamma) ∨
        (epsilon = gamma ∧ phi = beta)) := by
    intro hpair
    have huvSup : IsRayPairSupremum
        dq.rayArrowNonzeroHom.toMorphismFrom
        dp.rayArrowNonzeroHom.toMorphismFrom eta := by
      change IsRayPairSupremum
        (incomingQuiverArrowNonzeroHom (C := C) epsilon).toMorphismFrom
        (incomingQuiverArrowNonzeroHom (C := C) phi).toMorphismFrom
        eta at huvSup0
      rcases hpair with hpair | hpair
      · rw [hpair.1, hpair.2] at huvSup0
        simpa [beta, gamma, incomingQuiverArrowNonzeroHom,
          PathFinalDecomposition.rayArrowNonzeroHom] using huvSup0
      · rw [hpair.1, hpair.2] at huvSup0
        refine ⟨huvSup0.2.1, huvSup0.1, ?_⟩
        intro t hbeta hgamma
        exact huvSup0.2.2 t hgamma hbeta
    apply huSurvives
    exact hmem_of_mu_le_eta
      (hpSup.2.2 eta huvSup.1 huvSup.2.1)
  have hNoBetaDelta :
      ¬((epsilon = beta ∧ phi = delta) ∨
        (epsilon = delta ∧ phi = beta)) := by
    intro hpair
    have huvSup : IsRayPairSupremum
        dq.rayArrowNonzeroHom.toMorphismFrom
        ds.rayArrowNonzeroHom.toMorphismFrom eta := by
      change IsRayPairSupremum
        (incomingQuiverArrowNonzeroHom (C := C) epsilon).toMorphismFrom
        (incomingQuiverArrowNonzeroHom (C := C) phi).toMorphismFrom
        eta at huvSup0
      rcases hpair with hpair | hpair
      · rw [hpair.1, hpair.2] at huvSup0
        simpa [beta, delta, incomingQuiverArrowNonzeroHom,
          PathFinalDecomposition.rayArrowNonzeroHom] using huvSup0
      · rw [hpair.1, hpair.2] at huvSup0
        refine ⟨huvSup0.2.1, huvSup0.1, ?_⟩
        intro t hbeta hdelta
        exact huvSup0.2.2 t hdelta hbeta
    rcases hfigure with htop | hsixty
    · obtain ⟨outer, houterSup, hgammaOuter⟩ := htop
      have houterEta : outer ≤ eta :=
        houterSup.2.2 eta huvSup.1 huvSup.2.1
      have hmuEta : mu ≤ eta := hpSup.2.2 eta
        huvSup.1 (hgammaOuter.trans houterEta)
      exact huSurvives (hmem_of_mu_le_eta hmuEta)
    · exact hsixty.2.2 ⟨eta, huvSup⟩
  letI : Finite (IncomingQuiverArrow z) :=
    incomingQuiverArrow_finite z
  have hepsilonCases :
      epsilon = beta ∨ epsilon = gamma ∨ epsilon = delta :=
    eq_first_or_eq_second_or_eq_third_of_natCard_le_three
      hcard hbetaGamma hbetaDelta hgammaDelta
  have hphiCases : phi = beta ∨ phi = gamma ∨ phi = delta :=
    eq_first_or_eq_second_or_eq_third_of_natCard_le_three
      hcard hbetaGamma hbetaDelta hgammaDelta
  rcases hepsilonCases with heBeta | heGamma | heDelta <;>
    rcases hphiCases with hpBeta | hpGamma | hpDelta
  · exact (hepsilonPhi (heBeta.trans hpBeta.symm)).elim
  · exact (hNoBetaGamma (Or.inl ⟨heBeta, hpGamma⟩)).elim
  · exact (hNoBetaDelta (Or.inl ⟨heBeta, hpDelta⟩)).elim
  · exact (hNoBetaGamma (Or.inr ⟨heGamma, hpBeta⟩)).elim
  · exact (hepsilonPhi (heGamma.trans hpGamma.symm)).elim
  · exact Or.inl ⟨heGamma, hpDelta⟩
  · exact (hNoBetaDelta (Or.inr ⟨heDelta, hpBeta⟩)).elim
  · exact Or.inr ⟨heDelta, hpGamma⟩
  · exact (hepsilonPhi (heDelta.trans hpDelta.symm)).elim

/-- The initial-arrow dual: if killed and surviving essential contours share
one initial arrow, their other initial arrows are distinct. -/
theorem otherInitialArrow_ne_of_principal_survivor
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [IsRayCocrownFree C]
    {x z w : RayVertex C}
    {p q : Quiver.Path x z} {r s : Quiver.Path x w}
    (hpq : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (hrs : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) r s)
    (hrSurvives : ¬(principalZeroHomIdeal (rayPathMap p)).mem
      (rayPathMap r))
    (dp : PathInitialDecomposition p) (dq : PathInitialDecomposition q)
    (dr : PathInitialDecomposition r) (ds : PathInitialDecomposition s)
    (hshared : (⟨dp.middle, dp.arrow⟩ : OutgoingQuiverArrow x) =
      ⟨dr.middle, dr.arrow⟩) :
    (⟨dq.middle, dq.arrow⟩ : OutgoingQuiverArrow x) ≠
      ⟨ds.middle, ds.arrow⟩ := by
  intro hother
  let mu := rayPathMorphismTo p hpq.1.1
  let nu := rayPathMorphismTo r hrs.1.1
  have hpInf :=
    isRayPairInfimum_rayPathMorphismTo_of_essential_initialDecompositions
      dp dq hpq.1 hpq.2
  have hrInf :=
    isRayPairInfimum_rayPathMorphismTo_of_essential_initialDecompositions
      dr ds hrs.1 hrs.2
  have hNuDp : nu ≤ dp.rayArrowNonzeroHom.toMorphismTo := by
    have h := hrInf.1
    change nu ≤ (outgoingQuiverArrowNonzeroHom (C := C)
      (⟨dr.middle, dr.arrow⟩ : OutgoingQuiverArrow x)).toMorphismTo at h
    rw [← hshared] at h
    exact h
  have hNuDq : nu ≤ dq.rayArrowNonzeroHom.toMorphismTo := by
    have h := hrInf.2.1
    change nu ≤ (outgoingQuiverArrowNonzeroHom (C := C)
      (⟨ds.middle, ds.arrow⟩ : OutgoingQuiverArrow x)).toMorphismTo at h
    rw [← hother] at h
    exact h
  have hNuMu : nu ≤ mu := hpInf.2.2 nu hNuDp hNuDq
  apply hrSurvives
  change FactorsThroughMorphism (rayPathMap p) (rayPathMap r)
  obtain ⟨h, hh⟩ := hNuMu
  refine ⟨h, 𝟙 x.obj, ?_⟩
  change rayPathMap r = h ≫ rayPathMap p ≫ 𝟙 x.obj
  simpa [mu, nu, rayPathMorphismTo] using hh.symm

/-- Fixed-target dual of the final-arrow orientation theorem: every pair
infimum of the two other initial arrows lies below the shared initial arrow. -/
theorem sharedInitialArrow_outerInfimum_le_of_principal_survivor
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [IsRayCocrownFree C]
    {x z w : RayVertex C}
    {p q : Quiver.Path x z} {r s : Quiver.Path x w}
    (hpq : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (hrs : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) r s)
    (hrSurvives : ¬(principalZeroHomIdeal (rayPathMap p)).mem
      (rayPathMap r))
    (dp : PathInitialDecomposition p) (dq : PathInitialDecomposition q)
    (dr : PathInitialDecomposition r) (ds : PathInitialDecomposition s)
    (hshared : (⟨dp.middle, dp.arrow⟩ : OutgoingQuiverArrow x) =
      ⟨dr.middle, dr.arrow⟩)
    (outer : NonzeroMorphismTo x.obj)
    (houter : IsRayPairInfimum
      dq.rayArrowNonzeroHom.toMorphismTo
      ds.rayArrowNonzeroHom.toMorphismTo outer) :
    outer ≤ dp.rayArrowNonzeroHom.toMorphismTo := by
  by_contra hbad
  let gamma := dp.rayArrowNonzeroHom.toMorphismTo
  let beta := dq.rayArrowNonzeroHom.toMorphismTo
  let delta := ds.rayArrowNonzeroHom.toMorphismTo
  let mu := rayPathMorphismTo p hpq.1.1
  let nu := rayPathMorphismTo r hrs.1.1
  let I := properWhiskerInterlacementRelation
    (rayPathContourRelation (C := C))
  have hpInf :=
    isRayPairInfimum_rayPathMorphismTo_of_essential_initialDecompositions
      dp dq hpq.1 hpq.2
  have hrInf :=
    isRayPairInfimum_rayPathMorphismTo_of_essential_initialDecompositions
      dr ds hrs.1 hrs.2
  have hgammaEq : dr.rayArrowNonzeroHom.toMorphismTo = gamma := by
    change (outgoingQuiverArrowNonzeroHom (C := C)
      (⟨dr.middle, dr.arrow⟩ : OutgoingQuiverArrow x)).toMorphismTo = gamma
    rw [← hshared]
    rfl
  have hrInf' : IsRayPairInfimum gamma delta nu := by
    simpa [delta, nu, hgammaEq] using hrInf
  have hbetaDeltaCode :
      (⟨dq.middle, dq.arrow⟩ : OutgoingQuiverArrow x) ≠
        ⟨ds.middle, ds.arrow⟩ :=
    otherInitialArrow_ne_of_principal_survivor hpq hrs hrSurvives
      dp dq dr ds hshared
  have hgammaBetaCode :
      (⟨dp.middle, dp.arrow⟩ : OutgoingQuiverArrow x) ≠
        ⟨dq.middle, dq.arrow⟩ := by
    intro h
    exact hpq.2
      (rayPaths_interlaced_of_initialDecomposition_code_eq dp dq hpq.1 h)
  have hgammaDeltaCode :
      (⟨dp.middle, dp.arrow⟩ : OutgoingQuiverArrow x) ≠
        ⟨ds.middle, ds.arrow⟩ := by
    intro h
    apply hrs.2
    exact rayPaths_interlaced_of_initialDecomposition_code_eq dr ds hrs.1
      (hshared.symm.trans h)
  have hgammaBeta : OrderIncomparable gamma beta := by
    have htarget : RayTargetIncomparable
        dp.rayArrowNonzeroHom dq.rayArrowNonzeroHom := by
      simpa [outgoingQuiverArrowNonzeroHom,
        PathInitialDecomposition.rayArrowNonzeroHom] using
        (outgoingQuiverArrow_rayTargetIncomparable_of_ne
          (C := C) hgammaBetaCode)
    exact htarget
  have hgammaDelta : OrderIncomparable gamma delta := by
    have htarget : RayTargetIncomparable
        dp.rayArrowNonzeroHom ds.rayArrowNonzeroHom := by
      simpa [outgoingQuiverArrowNonzeroHom,
        PathInitialDecomposition.rayArrowNonzeroHom] using
        (outgoingQuiverArrow_rayTargetIncomparable_of_ne
          (C := C) hgammaDeltaCode)
    exact htarget
  have hbetaDelta : OrderIncomparable beta delta := by
    have htarget : RayTargetIncomparable
        dq.rayArrowNonzeroHom ds.rayArrowNonzeroHom := by
      simpa [outgoingQuiverArrowNonzeroHom,
        PathInitialDecomposition.rayArrowNonzeroHom] using
        (outgoingQuiverArrow_rayTargetIncomparable_of_ne
          (C := C) hbetaDeltaCode)
    exact htarget
  have hnuNotLeMu : ¬nu ≤ mu := by
    intro hnuMu
    apply hrSurvives
    change FactorsThroughMorphism (rayPathMap p) (rayPathMap r)
    obtain ⟨h, hh⟩ := hnuMu
    refine ⟨h, 𝟙 x.obj, ?_⟩
    change rayPathMap r = h ≫ rayPathMap p ≫ 𝟙 x.obj
    simpa [mu, nu, rayPathMorphismTo] using hh.symm
  rcases rayPairInfima_subordinate_of_cocrownFree
      hgammaBeta hgammaDelta hbetaDelta hpInf houter hrInf' with
    hnuBottom | houterBottom | hmuBottom
  · exact hnuNotLeMu hnuBottom.1
  · exact hbad (houterBottom.1.trans hpInf.1)
  · have houterNotLeMu : ¬outer ≤ mu := by
      intro houterMu
      exact hbad (houterMu.trans hpInf.1)
    have hnuDr : nu ≤ (outgoingQuiverArrowNonzeroHom (C := C)
        (⟨dr.middle, dr.arrow⟩ : OutgoingQuiverArrow x)).toMorphismTo := by
      simpa [nu, outgoingQuiverArrowNonzeroHom,
        PathInitialDecomposition.rayArrowNonzeroHom] using hrInf.1
    have hnuDs : nu ≤ (outgoingQuiverArrowNonzeroHom (C := C)
        (⟨ds.middle, ds.arrow⟩ : OutgoingQuiverArrow x)).toMorphismTo := by
      simpa [nu, outgoingQuiverArrowNonzeroHom,
        PathInitialDecomposition.rayArrowNonzeroHom] using hrInf.2.1
    obtain ⟨pr, ps, dpr, dps, hpr, hps, hdpr, hdps, hiRS⟩ :=
      exists_interlaced_presentations_of_strict_commonLower (C := C)
        (⟨dr.middle, dr.arrow⟩ : OutgoingQuiverArrow x)
        (⟨ds.middle, ds.arrow⟩ : OutgoingQuiverArrow x)
        nu mu hnuDr hnuDs hmuBottom.2 hnuNotLeMu
    have houterDq : outer ≤ (outgoingQuiverArrowNonzeroHom (C := C)
        (⟨dq.middle, dq.arrow⟩ : OutgoingQuiverArrow x)).toMorphismTo := by
      simpa [outgoingQuiverArrowNonzeroHom,
        PathInitialDecomposition.rayArrowNonzeroHom] using houter.1
    have houterDs : outer ≤ (outgoingQuiverArrowNonzeroHom (C := C)
        (⟨ds.middle, ds.arrow⟩ : OutgoingQuiverArrow x)).toMorphismTo := by
      simpa [outgoingQuiverArrowNonzeroHom,
        PathInitialDecomposition.rayArrowNonzeroHom] using houter.2.1
    obtain ⟨pb, pd, dpb, dpd, hpb, hpd, hdpb, hdpd, hiBD⟩ :=
      exists_interlaced_presentations_of_strict_commonLower (C := C)
        (⟨dq.middle, dq.arrow⟩ : OutgoingQuiverArrow x)
        (⟨ds.middle, ds.arrow⟩ : OutgoingQuiverArrow x)
        outer mu houterDq houterDs hmuBottom.1 houterNotLeMu
    have hppr : (rayPathContourRelation (C := C)).related p pr := by
      refine ⟨hpq.1.1, ?_⟩
      simpa [mu, rayPathMorphismTo] using hpr.symm
    have hq : rayPathMap q ≠ 0 := by
      rw [← hpq.1.2]
      exact hpq.1.1
    have hqpb : (rayPathContourRelation (C := C)).related q pb := by
      refine ⟨hq, ?_⟩
      calc
        rayPathMap q = rayPathMap p := hpq.1.2.symm
        _ = mu.hom := rfl
        _ = rayPathMap pb := hpb.symm
    have hpspd : (rayPathContourRelation (C := C)).related ps pd := by
      refine ⟨?_, hps.trans hpd.symm⟩
      rw [hps]
      exact mu.ne_zero
    have hiPPr : I.interlaced p pr :=
      rayPaths_interlaced_of_initialDecomposition_code_eq dp dpr hppr
        (hshared.trans hdpr.symm)
    have hiQPb : I.interlaced q pb :=
      rayPaths_interlaced_of_initialDecomposition_code_eq dq dpb hqpb
        hdpb.symm
    have hiPsPd : I.interlaced ps pd :=
      rayPaths_interlaced_of_initialDecomposition_code_eq dps dpd hpspd
        (hdps.trans hdpd.symm)
    apply hpq.2
    exact I.trans hiPPr
      (I.trans hiRS
        (I.trans hiPsPd
          (I.trans (I.symm hiBD) (I.symm hiQPb))))

/-- A killed essential contour and a surviving essential contour sharing an
initial arrow automatically have the fixed-target Figure 58-or-60 dual. -/
theorem isRayCoThreeArrowFigure_of_essential_initialContours_principal_survivor
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [IsRayCocrownFree C]
    {x z w : RayVertex C}
    {p q : Quiver.Path x z} {r s : Quiver.Path x w}
    (hpq : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (hrs : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) r s)
    (hrSurvives : ¬(principalZeroHomIdeal (rayPathMap p)).mem (rayPathMap r))
    (dp : PathInitialDecomposition p) (dq : PathInitialDecomposition q)
    (dr : PathInitialDecomposition r) (ds : PathInitialDecomposition s)
    (hshared : (⟨dp.middle, dp.arrow⟩ : OutgoingQuiverArrow x) =
      ⟨dr.middle, dr.arrow⟩) :
    IsRayCoThreeArrowFigure
      dq.rayArrowNonzeroHom.toMorphismTo
      dp.rayArrowNonzeroHom.toMorphismTo
      ds.rayArrowNonzeroHom.toMorphismTo := by
  have hpInf :=
    isRayPairInfimum_rayPathMorphismTo_of_essential_initialDecompositions
      dp dq hpq.1 hpq.2
  have hrInf :=
    isRayPairInfimum_rayPathMorphismTo_of_essential_initialDecompositions
      dr ds hrs.1 hrs.2
  by_cases houter : ∃ outer : NonzeroMorphismTo x.obj,
      IsRayPairInfimum dq.rayArrowNonzeroHom.toMorphismTo
        ds.rayArrowNonzeroHom.toMorphismTo outer
  · obtain ⟨outer, houter⟩ := houter
    exact Or.inl ⟨outer, houter,
      sharedInitialArrow_outerInfimum_le_of_principal_survivor
        hpq hrs hrSurvives dp dq dr ds hshared outer houter⟩
  · refine Or.inr ⟨?_, ?_, houter⟩
    · exact ⟨rayPathMorphismTo p hpq.1.1,
        hpInf.2.1, hpInf.1,
        fun u hbeta hgamma => hpInf.2.2 u hgamma hbeta⟩
    · refine ⟨rayPathMorphismTo r hrs.1.1, ?_⟩
      have hgammaEq : dr.rayArrowNonzeroHom.toMorphismTo =
          dp.rayArrowNonzeroHom.toMorphismTo := by
        change (outgoingQuiverArrowNonzeroHom (C := C)
          (⟨dr.middle, dr.arrow⟩ : OutgoingQuiverArrow x)).toMorphismTo =
            dp.rayArrowNonzeroHom.toMorphismTo
        rw [← hshared]
        rfl
      simpa [hgammaEq] using hrInf

/-- At an outgoing-three-valent endpoint, every surviving essential contour
uses the two surviving initial arrows in opposite order. -/
theorem survivingEssentialContour_initialArrow_pair_eq_sharedPair_of_figure
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [IsRayCocrownFree C]
    {x z y w : RayVertex C}
    {p q : Quiver.Path x z} {r s : Quiver.Path x y}
    {u v : Quiver.Path x w}
    (hpq : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (hrs : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) r s)
    (huv : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) u v)
    (hrSurvives : ¬(principalZeroHomIdeal (rayPathMap p)).mem
      (rayPathMap r))
    (huSurvives : ¬(principalZeroHomIdeal (rayPathMap p)).mem
      (rayPathMap u))
    (dp : PathInitialDecomposition p) (dq : PathInitialDecomposition q)
    (dr : PathInitialDecomposition r) (ds : PathInitialDecomposition s)
    (du : PathInitialDecomposition u) (dv : PathInitialDecomposition v)
    (hshared : (⟨dp.middle, dp.arrow⟩ : OutgoingQuiverArrow x) =
      ⟨dr.middle, dr.arrow⟩)
    (hcard : Nat.card (OutgoingQuiverArrow x) ≤ 3)
    (hfigure : IsRayCoThreeArrowFigure
      dq.rayArrowNonzeroHom.toMorphismTo
      dp.rayArrowNonzeroHom.toMorphismTo
      ds.rayArrowNonzeroHom.toMorphismTo) :
    ((⟨du.middle, du.arrow⟩ : OutgoingQuiverArrow x) =
        ⟨dp.middle, dp.arrow⟩ ∧
      (⟨dv.middle, dv.arrow⟩ : OutgoingQuiverArrow x) =
        ⟨ds.middle, ds.arrow⟩) ∨
    ((⟨du.middle, du.arrow⟩ : OutgoingQuiverArrow x) =
        ⟨ds.middle, ds.arrow⟩ ∧
      (⟨dv.middle, dv.arrow⟩ : OutgoingQuiverArrow x) =
        ⟨dp.middle, dp.arrow⟩) := by
  let beta : OutgoingQuiverArrow x := ⟨dq.middle, dq.arrow⟩
  let gamma : OutgoingQuiverArrow x := ⟨dp.middle, dp.arrow⟩
  let delta : OutgoingQuiverArrow x := ⟨ds.middle, ds.arrow⟩
  let epsilon : OutgoingQuiverArrow x := ⟨du.middle, du.arrow⟩
  let phi : OutgoingQuiverArrow x := ⟨dv.middle, dv.arrow⟩
  let mu := rayPathMorphismTo p hpq.1.1
  let eta := rayPathMorphismTo u huv.1.1
  have hbetaGamma : beta ≠ gamma := by
    intro h
    apply hpq.2
    apply rayPaths_interlaced_of_initialDecomposition_code_eq dp dq hpq.1
    exact h.symm
  have hgammaDelta : gamma ≠ delta := by
    intro h
    apply hrs.2
    apply rayPaths_interlaced_of_initialDecomposition_code_eq dr ds hrs.1
    calc
      (⟨dr.middle, dr.arrow⟩ : OutgoingQuiverArrow x) = gamma :=
        hshared.symm
      _ = delta := h
  have hbetaDelta : beta ≠ delta :=
    otherInitialArrow_ne_of_principal_survivor hpq hrs hrSurvives
      dp dq dr ds hshared
  have hepsilonPhi : epsilon ≠ phi := by
    intro h
    apply huv.2
    exact rayPaths_interlaced_of_initialDecomposition_code_eq du dv huv.1 h
  have hpInf0 :=
    isRayPairInfimum_rayPathMorphismTo_of_essential_initialDecompositions
      dp dq hpq.1 hpq.2
  have hpInf : IsRayPairInfimum
      dq.rayArrowNonzeroHom.toMorphismTo
      dp.rayArrowNonzeroHom.toMorphismTo mu :=
    ⟨hpInf0.2.1, hpInf0.1,
      fun t hbeta hgamma => hpInf0.2.2 t hgamma hbeta⟩
  have huvInf0 :=
    isRayPairInfimum_rayPathMorphismTo_of_essential_initialDecompositions
      du dv huv.1 huv.2
  have hmem_of_eta_le_mu (hetamu : eta ≤ mu) :
      (principalZeroHomIdeal (rayPathMap p)).mem (rayPathMap u) := by
    change FactorsThroughMorphism (rayPathMap p) (rayPathMap u)
    obtain ⟨h, hh⟩ := hetamu
    refine ⟨h, 𝟙 x.obj, ?_⟩
    change rayPathMap u = h ≫ rayPathMap p ≫ 𝟙 x.obj
    simpa [mu, eta, rayPathMorphismTo] using hh.symm
  have hNoBetaGamma :
      ¬((epsilon = beta ∧ phi = gamma) ∨
        (epsilon = gamma ∧ phi = beta)) := by
    intro hpair
    have huvInf : IsRayPairInfimum
        dq.rayArrowNonzeroHom.toMorphismTo
        dp.rayArrowNonzeroHom.toMorphismTo eta := by
      change IsRayPairInfimum
        (outgoingQuiverArrowNonzeroHom (C := C) epsilon).toMorphismTo
        (outgoingQuiverArrowNonzeroHom (C := C) phi).toMorphismTo
        eta at huvInf0
      rcases hpair with hpair | hpair
      · rw [hpair.1, hpair.2] at huvInf0
        simpa [beta, gamma, outgoingQuiverArrowNonzeroHom,
          PathInitialDecomposition.rayArrowNonzeroHom] using huvInf0
      · rw [hpair.1, hpair.2] at huvInf0
        refine ⟨huvInf0.2.1, huvInf0.1, ?_⟩
        intro t hbeta hgamma
        exact huvInf0.2.2 t hgamma hbeta
    apply huSurvives
    exact hmem_of_eta_le_mu
      (hpInf.2.2 eta huvInf.1 huvInf.2.1)
  have hNoBetaDelta :
      ¬((epsilon = beta ∧ phi = delta) ∨
        (epsilon = delta ∧ phi = beta)) := by
    intro hpair
    have huvInf : IsRayPairInfimum
        dq.rayArrowNonzeroHom.toMorphismTo
        ds.rayArrowNonzeroHom.toMorphismTo eta := by
      change IsRayPairInfimum
        (outgoingQuiverArrowNonzeroHom (C := C) epsilon).toMorphismTo
        (outgoingQuiverArrowNonzeroHom (C := C) phi).toMorphismTo
        eta at huvInf0
      rcases hpair with hpair | hpair
      · rw [hpair.1, hpair.2] at huvInf0
        simpa [beta, delta, outgoingQuiverArrowNonzeroHom,
          PathInitialDecomposition.rayArrowNonzeroHom] using huvInf0
      · rw [hpair.1, hpair.2] at huvInf0
        refine ⟨huvInf0.2.1, huvInf0.1, ?_⟩
        intro t hbeta hdelta
        exact huvInf0.2.2 t hdelta hbeta
    rcases hfigure with hbottom | hsixty
    · obtain ⟨outer, houterInf, houterGamma⟩ := hbottom
      have hetaOuter : eta ≤ outer :=
        houterInf.2.2 eta huvInf.1 huvInf.2.1
      have hetaMu : eta ≤ mu := hpInf.2.2 eta
        huvInf.1 (hetaOuter.trans houterGamma)
      exact huSurvives (hmem_of_eta_le_mu hetaMu)
    · exact hsixty.2.2 ⟨eta, huvInf⟩
  letI : Finite (OutgoingQuiverArrow x) :=
    outgoingQuiverArrow_finite x
  have hepsilonCases :
      epsilon = beta ∨ epsilon = gamma ∨ epsilon = delta :=
    eq_first_or_eq_second_or_eq_third_of_natCard_le_three
      hcard hbetaGamma hbetaDelta hgammaDelta
  have hphiCases : phi = beta ∨ phi = gamma ∨ phi = delta :=
    eq_first_or_eq_second_or_eq_third_of_natCard_le_three
      hcard hbetaGamma hbetaDelta hgammaDelta
  rcases hepsilonCases with heBeta | heGamma | heDelta <;>
    rcases hphiCases with hpBeta | hpGamma | hpDelta
  · exact (hepsilonPhi (heBeta.trans hpBeta.symm)).elim
  · exact (hNoBetaGamma (Or.inl ⟨heBeta, hpGamma⟩)).elim
  · exact (hNoBetaDelta (Or.inl ⟨heBeta, hpDelta⟩)).elim
  · exact (hNoBetaGamma (Or.inr ⟨heGamma, hpBeta⟩)).elim
  · exact (hepsilonPhi (heGamma.trans hpGamma.symm)).elim
  · exact Or.inl ⟨heGamma, hpDelta⟩
  · exact (hNoBetaDelta (Or.inr ⟨heDelta, hpBeta⟩)).elim
  · exact Or.inr ⟨heDelta, hpGamma⟩
  · exact (hepsilonPhi (heDelta.trans hpDelta.symm)).elim

/-- The remaining local BGRS obligation after the automatic `N = 1` branch:
for every maximal ray through the last arrow of an efficient tackle, supply
the correction in the cardinal-two and cardinal-three cases. -/
def HasHardInvisibleCorrectionsOnEfficientMaximalRays
    (k : Type*) [Field k]
    (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
    [Finite C] [IsFiniteRayCategory C] : Prop :=
  ∀ (t : RayTackle C) (y : C), t.IsEfficientAt y →
    ∀ (p : NonzeroRayPathThroughArrow (C := C) t.lastBundledArrow),
      p.IsMaximal →
        (Nat.card (RelatedPathInterlacementClass
          (properWhiskerInterlacementRelation
            (rayPathContourRelation (C := C))) p.path) = 2 →
          ZeroHomIdeal.HasInvisibleCorrectionClingingOnIdeal (k := k)
            (principalZeroHomIdeal (rayPathMap p.path))) ∧
        (Nat.card (RelatedPathInterlacementClass
          (properWhiskerInterlacementRelation
            (rayPathContourRelation (C := C))) p.path) = 3 →
          ZeroHomIdeal.HasInvisibleCorrectionClingingOnIdeal (k := k)
            (principalZeroHomIdeal (rayPathMap p.path)))

/-- The hard `N = 2,3` efficient-tackle obligations imply the complete local
input consumed by source-faithful residue induction. -/
theorem HasHardInvisibleCorrectionsOnEfficientMaximalRays.toLocalCorrections
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [HasRayLongPathEndpointValencyAtMostThree C]
    (h : HasHardInvisibleCorrectionsOnEfficientMaximalRays k C) :
    HasInvisibleCorrectionsOnEfficientMaximalRays k C := by
  intro t y ht p hp
  obtain ⟨hTwo, hThree⟩ := h t y ht p hp
  exact ZeroHomIdeal.hasInvisibleCorrectionClingingOnIdeal_principal_of_maximal_of_card_two_three
    p hp hTwo hThree

/-- The complete finite residue induction now needs only the two hard local
cardinal cases, uniformly over categories no larger than the original one. -/
theorem contourFunctionCohomologyVanishes_of_hardEfficientMaximalRayResidueInduction
    [Finite C] [IsFiniteRayCategory C]
    [HasRayCancellation C] [HasNoInfiniteRayChain C]
    [HasRayLongPathEndpointValencyAtMostThree C]
    (hhard : ∀ (D : Type u) [Category.{v} D] [HasZeroMorphisms D]
        [Finite D] [IsFiniteRayCategory D]
        [HasRayCancellation D] [HasNoInfiniteRayChain D]
        [HasRayLongPathEndpointValencyAtMostThree D],
      Nat.card (NonzeroCategoryMorphism D) ≤
          Nat.card (NonzeroCategoryMorphism C) →
        HasHardInvisibleCorrectionsOnEfficientMaximalRays k D) :
    ContourFunctionCohomologyVanishes (k := k)
      (rayPathContourRelation (C := C)) := by
  apply contourFunctionCohomologyVanishes_of_efficientMaximalRayResidueInduction_with_valency
  intro D _ _ _ _ _ _ _ hbound
  exact (hhard D hbound).toLocalCorrections

namespace BundledArrowOccurrence

/-- An arrow occurrence with identity suffix gives a final-arrow
decomposition whose bundled final arrow is the selected arrow. -/
theorem exists_finalDecomposition_of_afterLengthZero
    {a : BundledQuiverArrow (RayVertex C)}
    {x y : RayVertex C} {p : Quiver.Path x y}
    (o : BundledArrowOccurrence a p) (hafter : o.after.length = 0) :
    ∃ d : PathFinalDecomposition p, bundledQuiverArrow d.arrow = a := by
  have hay : a.2.1 = y := Quiver.Path.eq_of_length_zero o.after hafter
  subst y
  let d : PathFinalDecomposition p :=
    { middle := a.1
      head := o.before
      arrow := a.2.2
      path_eq := by
        calc
          p = (o.before.comp a.2.2.toPath).comp o.after := o.path_eq
          _ = o.before.comp a.2.2.toPath := by
            rw [Quiver.Path.eq_nil_of_length_zero o.after hafter]
            simp }
  exact ⟨d, rfl⟩

/-- The orientation-dual construction with the selected bundled initial
arrow recorded explicitly. -/
theorem exists_initialDecomposition_of_beforeLengthZero
    {a : BundledQuiverArrow (RayVertex C)}
    {x y : RayVertex C} {p : Quiver.Path x y}
    (o : BundledArrowOccurrence a p) (hbefore : o.before.length = 0) :
    ∃ d : PathInitialDecomposition p, bundledQuiverArrow d.arrow = a := by
  have hxa : x = a.1 := Quiver.Path.eq_of_length_zero o.before hbefore
  subst x
  let d : PathInitialDecomposition p :=
    { middle := a.2.1
      arrow := a.2.2
      tail := o.after
      path_eq := by
        calc
          p = (o.before.comp a.2.2.toPath).comp o.after := o.path_eq
          _ = a.2.2.toPath.comp o.after := by
            rw [Quiver.Path.eq_nil_of_length_zero o.before hbefore]
            rfl }
  exact ⟨d, rfl⟩

end BundledArrowOccurrence

/-- Bundling an arrow with the already fixed final vertex is injective. -/
theorem bundledQuiverArrow_injective_on_incoming {z : RayVertex C} :
    Function.Injective (fun a : IncomingQuiverArrow z ↦
      bundledQuiverArrow a.2) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  simp only [bundledQuiverArrow, Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  cases h
  rfl

/-- Bundling an arrow with the already fixed initial vertex is injective. -/
theorem bundledQuiverArrow_injective_on_outgoing {x : RayVertex C} :
    Function.Injective (fun a : OutgoingQuiverArrow x ↦
      bundledQuiverArrow a.2) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  simp only [bundledQuiverArrow, Sigma.mk.injEq] at h
  exact eq_of_heq h.2

/-- Equality of bundled arrows transports the associated nonzero ray
morphisms through the induced endpoint equalities. -/
theorem rayArrowNonzeroHom_cast_eq_of_bundledQuiverArrow_eq
    {i j i' j' : RayVertex C} (a : i ⟶ j) (b : i' ⟶ j')
    (h : bundledQuiverArrow a = bundledQuiverArrow b) :
    NonzeroHom.cast
        (congrArg (fun e : BundledQuiverArrow (RayVertex C) => e.2.1.obj) h)
        (congrArg (fun e : BundledQuiverArrow (RayVertex C) => e.1.obj) h)
        (⟨rayArrowMorphism a, a.property.1⟩ : NonzeroHom j.obj i.obj) =
      (⟨rayArrowMorphism b, b.property.1⟩ : NonzeroHom j'.obj i'.obj) := by
  have hi : i = i' :=
    congrArg (fun e : BundledQuiverArrow (RayVertex C) => e.1) h
  have hj : j = j' :=
    congrArg (fun e : BundledQuiverArrow (RayVertex C) => e.2.1) h
  subst i'
  subst j'
  have habCode : (⟨i, a⟩ : IncomingQuiverArrow j) = ⟨i, b⟩ :=
    bundledQuiverArrow_injective_on_incoming h
  cases habCode
  rfl

/-- Failure of final-arrow absence exposes a surviving essential contour whose
left side ends in the selected arrow and whose right side ends in a different
arrow.  This is the endpoint witness used in the hard hook branch of BGRS
8.6(c). -/
theorem ZeroHomIdeal.exists_survivingEssentialContour_finalDecompositions_of_not_absent
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    (J : ZeroHomIdeal C)
    (selected : BundledQuiverArrow (RayVertex C))
    (hsuffix : EssentialContourArrowSuffixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) selected)
    (hnot : ¬J.BundledArrowAbsentFromSurvivingEssentialContours selected) :
    ∃ (x z : RayVertex C) (p q : Quiver.Path x z)
        (dp : PathFinalDecomposition p) (dq : PathFinalDecomposition q),
      (rayPathContourRelation (C := C)).related p q ∧
        ¬J.mem (rayPathMap p) ∧
        ¬(properWhiskerInterlacementRelation
          (rayPathContourRelation (C := C))).interlaced p q ∧
        bundledQuiverArrow dp.arrow = selected ∧
        bundledQuiverArrow dq.arrow ≠ selected := by
  classical
  simp only [BundledArrowAbsentFromSurvivingEssentialContours] at hnot
  push Not at hnot
  obtain ⟨x, z, p, q, hpq, hpNotMem, hpqNot, hocc⟩ := hnot
  obtain ⟨o⟩ := hocc
  have hessential : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q :=
    ⟨hpq, hpqNot⟩
  have hafter : o.after.length = 0 := hsuffix p q hessential o
  obtain ⟨dp, hdpArrow⟩ :=
    o.exists_finalDecomposition_of_afterLengthZero hafter
  have hpLength : p.length ≠ 0 := by
    intro hpZero
    have hlength := congrArg Quiver.Path.length o.path_eq
    simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath,
      hpZero] at hlength
    omega
  have hqLength : q.length ≠ 0 :=
    rayPath_length_ne_zero_of_related_of_not_isIso
      (rayPathMap_not_isIso_of_length_ne_zero p hpLength) hpq
  let dq := chosenPathFinalDecomposition q hqLength
  have hdqArrow : bundledQuiverArrow dq.arrow ≠ selected := by
    intro hdq
    apply hpqNot
    apply rayPaths_interlaced_of_finalDecomposition_code_eq dp dq hpq
    apply bundledQuiverArrow_injective_on_incoming
    change bundledQuiverArrow dp.arrow = bundledQuiverArrow dq.arrow
    rw [hdpArrow, hdq]
  exact ⟨x, z, p, q, dp, dq, hpq, hpNotMem, hpqNot,
    hdpArrow, hdqArrow⟩

/-- The orientation-dual witness: failure of initial-arrow absence exposes a
surviving essential contour whose two sides begin with the selected arrow and
a different arrow. -/
theorem ZeroHomIdeal.exists_survivingEssentialContour_initialDecompositions_of_not_absent
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    (J : ZeroHomIdeal C)
    (selected : BundledQuiverArrow (RayVertex C))
    (hprefix : EssentialContourArrowPrefixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) selected)
    (hnot : ¬J.BundledArrowAbsentFromSurvivingEssentialContours selected) :
    ∃ (x z : RayVertex C) (p q : Quiver.Path x z)
        (dp : PathInitialDecomposition p) (dq : PathInitialDecomposition q),
      (rayPathContourRelation (C := C)).related p q ∧
        ¬J.mem (rayPathMap p) ∧
        ¬(properWhiskerInterlacementRelation
          (rayPathContourRelation (C := C))).interlaced p q ∧
        bundledQuiverArrow dp.arrow = selected ∧
        bundledQuiverArrow dq.arrow ≠ selected := by
  classical
  simp only [BundledArrowAbsentFromSurvivingEssentialContours] at hnot
  push Not at hnot
  obtain ⟨x, z, p, q, hpq, hpNotMem, hpqNot, hocc⟩ := hnot
  obtain ⟨o⟩ := hocc
  have hessential : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q :=
    ⟨hpq, hpqNot⟩
  have hbefore : o.before.length = 0 := hprefix p q hessential o
  obtain ⟨dp, hdpArrow⟩ :=
    o.exists_initialDecomposition_of_beforeLengthZero hbefore
  have hpLength : p.length ≠ 0 := by
    intro hpZero
    have hlength := congrArg Quiver.Path.length o.path_eq
    simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath,
      hpZero] at hlength
    omega
  have hqLength : q.length ≠ 0 :=
    rayPath_length_ne_zero_of_related_of_not_isIso
      (rayPathMap_not_isIso_of_length_ne_zero p hpLength) hpq
  let dq := chosenPathInitialDecomposition q hqLength
  have hdqArrow : bundledQuiverArrow dq.arrow ≠ selected := by
    intro hdq
    apply hpqNot
    apply rayPaths_interlaced_of_initialDecomposition_code_eq dp dq hpq
    apply bundledQuiverArrow_injective_on_outgoing
    change bundledQuiverArrow dp.arrow = bundledQuiverArrow dq.arrow
    rw [hdpArrow, hdq]
  exact ⟨x, z, p, q, dp, dq, hpq, hpNotMem, hpqNot,
    hdpArrow, hdqArrow⟩

/-- The endpoint form of joint selector balance for two final-arrow
selectors.  BGRS 8.4 reduces all occurrences of efficient hooks to these four
final-arrow indicators. -/
def ZeroHomIdeal.FinalArrowPairBalanceOnSurvivingEssentialContours
    (J : ZeroHomIdeal C)
    (primary companion : BundledQuiverArrow (RayVertex C)) : Prop :=
  ∀ {x z : RayVertex C} (p q : Quiver.Path x z),
    (rayPathContourRelation (C := C)).related p q →
      ¬J.mem (rayPathMap p) →
        ¬(properWhiskerInterlacementRelation
          (rayPathContourRelation (C := C))).interlaced p q →
          ∀ (dp : PathFinalDecomposition p)
            (dq : PathFinalDecomposition q),
            selectedArrowCount (singleArrowSelector primary)
                  dp.arrow.toPath +
                selectedArrowCount (singleArrowSelector companion)
                  dp.arrow.toPath =
              selectedArrowCount (singleArrowSelector primary)
                  dq.arrow.toPath +
                selectedArrowCount (singleArrowSelector companion)
                  dq.arrow.toPath

/-- The oriented three-arrow geometry makes the two surviving final-arrow
selectors jointly balanced at every surviving essential contour. -/
theorem ZeroHomIdeal.finalArrowPairBalance_principal_of_sharedSurvivingContour_of_figure
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [IsRayCrownFree C]
    {x y z : RayVertex C}
    {p q : Quiver.Path x z} {r s : Quiver.Path y z}
    (hpq : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (hrs : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) r s)
    (hrSurvives : ¬(principalZeroHomIdeal (rayPathMap p)).mem
      (rayPathMap r))
    (dp : PathFinalDecomposition p) (dq : PathFinalDecomposition q)
    (dr : PathFinalDecomposition r) (ds : PathFinalDecomposition s)
    (hshared : (⟨dp.middle, dp.arrow⟩ : IncomingQuiverArrow z) =
      ⟨dr.middle, dr.arrow⟩)
    (hfigure : IsRayThreeArrowFigure
      dq.rayArrowNonzeroHom.toMorphismFrom
      dp.rayArrowNonzeroHom.toMorphismFrom
      ds.rayArrowNonzeroHom.toMorphismFrom)
    (hcard : Nat.card (IncomingQuiverArrow z) ≤ 3) :
    (principalZeroHomIdeal (rayPathMap p)).FinalArrowPairBalanceOnSurvivingEssentialContours
        (bundledQuiverArrow dp.arrow)
        (bundledQuiverArrow ds.arrow) := by
  have hprimaryCompanion :
      bundledQuiverArrow dp.arrow ≠ bundledQuiverArrow ds.arrow := by
    intro h
    have hcode :
        (⟨dp.middle, dp.arrow⟩ : IncomingQuiverArrow z) =
          ⟨ds.middle, ds.arrow⟩ :=
      bundledQuiverArrow_injective_on_incoming h
    apply hrs.2
    apply rayPaths_interlaced_of_finalDecomposition_code_eq dr ds hrs.1
    exact hshared.symm.trans hcode
  intro w z' u v huv huSurvives huvNot du dv
  by_cases hzz : z' = z
  · subst z'
    have hpair :=
      survivingEssentialContour_finalArrow_pair_eq_sharedPair_of_figure
        hpq hrs ⟨huv, huvNot⟩ hrSurvives huSurvives
        dp dq dr ds du dv hshared hfigure hcard
    rcases hpair with hpair | hpair
    · have hdu : bundledQuiverArrow du.arrow =
          bundledQuiverArrow dp.arrow :=
        congrArg (fun a : IncomingQuiverArrow z =>
          bundledQuiverArrow a.2) hpair.1
      have hdv : bundledQuiverArrow dv.arrow =
          bundledQuiverArrow ds.arrow :=
        congrArg (fun a : IncomingQuiverArrow z =>
          bundledQuiverArrow a.2) hpair.2
      rw [← hdu, ← hdv]
      exact selectedArrowCount_singleArrowSelector_pair_swap
        du.arrow dv.arrow
        (fun h => hprimaryCompanion
          (hdu.symm.trans (h.trans hdv)))
    · have hdu : bundledQuiverArrow du.arrow =
          bundledQuiverArrow ds.arrow :=
        congrArg (fun a : IncomingQuiverArrow z =>
          bundledQuiverArrow a.2) hpair.1
      have hdv : bundledQuiverArrow dv.arrow =
          bundledQuiverArrow dp.arrow :=
        congrArg (fun a : IncomingQuiverArrow z =>
          bundledQuiverArrow a.2) hpair.2
      rw [← hdu, ← hdv]
      exact
        (selectedArrowCount_singleArrowSelector_pair_swap
          dv.arrow du.arrow
          (fun h => hprimaryCompanion
            (hdv.symm.trans (h.trans hdu)))).symm
  · have hduPrimary : bundledQuiverArrow du.arrow ≠
        bundledQuiverArrow dp.arrow := by
      intro h
      apply hzz
      exact congrArg
        (fun a : BundledQuiverArrow (RayVertex C) => a.2.1) h
    have hduCompanion : bundledQuiverArrow du.arrow ≠
        bundledQuiverArrow ds.arrow := by
      intro h
      apply hzz
      exact congrArg
        (fun a : BundledQuiverArrow (RayVertex C) => a.2.1) h
    have hdvPrimary : bundledQuiverArrow dv.arrow ≠
        bundledQuiverArrow dp.arrow := by
      intro h
      apply hzz
      exact congrArg
        (fun a : BundledQuiverArrow (RayVertex C) => a.2.1) h
    have hdvCompanion : bundledQuiverArrow dv.arrow ≠
        bundledQuiverArrow ds.arrow := by
      intro h
      apply hzz
      exact congrArg
        (fun a : BundledQuiverArrow (RayVertex C) => a.2.1) h
    rw [selectedArrowCount_singleArrowSelector_toPath_of_ne
          dp.arrow du.arrow hduPrimary,
      selectedArrowCount_singleArrowSelector_toPath_of_ne
          ds.arrow du.arrow hduCompanion,
      selectedArrowCount_singleArrowSelector_toPath_of_ne
          dp.arrow dv.arrow hdvPrimary,
      selectedArrowCount_singleArrowSelector_toPath_of_ne
          ds.arrow dv.arrow hdvCompanion]

/-- The preceding balance is automatic from a killed essential contour and
one surviving essential contour sharing its distinguished final arrow. -/
theorem ZeroHomIdeal.finalArrowPairBalance_principal_of_sharedSurvivingContour
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [IsRayCrownFree C]
    {x y z : RayVertex C}
    {p q : Quiver.Path x z} {r s : Quiver.Path y z}
    (hpq : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (hrs : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) r s)
    (hrSurvives : ¬(principalZeroHomIdeal (rayPathMap p)).mem
      (rayPathMap r))
    (dp : PathFinalDecomposition p) (dq : PathFinalDecomposition q)
    (dr : PathFinalDecomposition r) (ds : PathFinalDecomposition s)
    (hshared : (⟨dp.middle, dp.arrow⟩ : IncomingQuiverArrow z) =
      ⟨dr.middle, dr.arrow⟩)
    (hcard : Nat.card (IncomingQuiverArrow z) ≤ 3) :
    (principalZeroHomIdeal (rayPathMap p)).FinalArrowPairBalanceOnSurvivingEssentialContours
        (bundledQuiverArrow dp.arrow)
        (bundledQuiverArrow ds.arrow) := by
  apply ZeroHomIdeal.finalArrowPairBalance_principal_of_sharedSurvivingContour_of_figure
    hpq hrs hrSurvives dp dq dr ds hshared
  · exact isRayThreeArrowFigure_of_essential_finalContours_principal_survivor
      hpq hrs hrSurvives dp dq dr ds hshared
  · exact hcard

/-- A three-arrow cover and gamma/delta pair balance force beta to be absent
from every surviving essential contour once beta is suffix-trivial. -/
theorem ZeroHomIdeal.bundledArrowAbsent_of_finalArrowPairBalance_of_cover
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    (J : ZeroHomIdeal C)
    {z : RayVertex C}
    (beta gamma delta : IncomingQuiverArrow z)
    (hbetaGamma : beta ≠ gamma)
    (hbetaDelta : beta ≠ delta)
    (hcover : ∀ a : IncomingQuiverArrow z,
      a = beta ∨ a = gamma ∨ a = delta)
    (hbetaSuffix : EssentialContourArrowSuffixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C)))
      (bundledQuiverArrow beta.2))
    (hpair : J.FinalArrowPairBalanceOnSurvivingEssentialContours
      (bundledQuiverArrow gamma.2) (bundledQuiverArrow delta.2)) :
    J.BundledArrowAbsentFromSurvivingEssentialContours
      (bundledQuiverArrow beta.2) := by
  classical
  by_contra hnot
  obtain ⟨x, z', p, q, dp, dq, hpq, hpNotMem, hpqNot,
      hdpArrow, hdqArrow⟩ :=
    J.exists_survivingEssentialContour_finalDecompositions_of_not_absent
      (bundledQuiverArrow beta.2) hbetaSuffix hnot
  have hzz : z' = z := congrArg
    (fun a : BundledQuiverArrow (RayVertex C) => a.2.1) hdpArrow
  subst z'
  let dqCode : IncomingQuiverArrow z := ⟨dq.middle, dq.arrow⟩
  have hdqCodeNe : dqCode ≠ beta := by
    intro h
    exact hdqArrow (congrArg (fun a : IncomingQuiverArrow z =>
      bundledQuiverArrow a.2) h)
  have hdpGamma : bundledQuiverArrow dp.arrow ≠
      bundledQuiverArrow gamma.2 := by
    intro h
    apply hbetaGamma
    apply bundledQuiverArrow_injective_on_incoming
    change bundledQuiverArrow beta.2 = bundledQuiverArrow gamma.2
    rw [← hdpArrow]
    exact h
  have hdpDelta : bundledQuiverArrow dp.arrow ≠
      bundledQuiverArrow delta.2 := by
    intro h
    apply hbetaDelta
    apply bundledQuiverArrow_injective_on_incoming
    change bundledQuiverArrow beta.2 = bundledQuiverArrow delta.2
    rw [← hdpArrow]
    exact h
  have hgammaDp : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow gamma.2))
      dp.arrow.toPath = 0 :=
    selectedArrowCount_singleArrowSelector_toPath_of_ne
      gamma.2 dp.arrow hdpGamma
  have hdeltaDp : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow delta.2))
      dp.arrow.toPath = 0 :=
    selectedArrowCount_singleArrowSelector_toPath_of_ne
      delta.2 dp.arrow hdpDelta
  have hbalance := hpair p q hpq hpNotMem hpqNot dp dq
  rcases hcover dqCode with hdqBeta | hdqGamma | hdqDelta
  · exact hdqCodeNe hdqBeta
  · have hdqGammaBundle : bundledQuiverArrow dq.arrow =
        bundledQuiverArrow gamma.2 := congrArg
      (fun a : IncomingQuiverArrow z => bundledQuiverArrow a.2) hdqGamma
    have hgammaDq : selectedArrowCount
        (singleArrowSelector (bundledQuiverArrow gamma.2))
        dq.arrow.toPath = 1 := by
      rw [← hdqGammaBundle]
      exact selectedArrowCount_singleArrowSelector_toPath dq.arrow
    rw [hgammaDp, hdeltaDp, hgammaDq] at hbalance
    omega
  · have hdqDeltaBundle : bundledQuiverArrow dq.arrow =
        bundledQuiverArrow delta.2 := congrArg
      (fun a : IncomingQuiverArrow z => bundledQuiverArrow a.2) hdqDelta
    have hdeltaDq : selectedArrowCount
        (singleArrowSelector (bundledQuiverArrow delta.2))
        dq.arrow.toPath = 1 := by
      rw [← hdqDeltaBundle]
      exact selectedArrowCount_singleArrowSelector_toPath dq.arrow
    rw [hgammaDp, hdeltaDp, hdeltaDq] at hbalance
    omega

/-- The final-arrow pairing supplied by the hook geometry is exactly the
joint selector balance needed for the paired residue correction. -/
theorem ZeroHomIdeal.arrowSelectorPairBalanced_single_of_finalArrowPairBalance
    [Finite C] [IsFiniteRayCategory C]
    (J : ZeroHomIdeal C)
    (primary companion : BundledQuiverArrow (RayVertex C))
    (hprimary : EssentialContourArrowSuffixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) primary)
    (hcompanion : EssentialContourArrowSuffixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) companion)
    (hpair : J.FinalArrowPairBalanceOnSurvivingEssentialContours
      primary companion) :
    J.ArrowSelectorPairBalancedOnSurvivingEssentialContours
      (singleArrowSelector primary) (singleArrowSelector companion) := by
  classical
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  intro x z p q hpq hpNotMem hpqNot
  have hpLength : p.length ≠ 0 := by
    intro hpZero
    have hpqEq := rayPath_eq_of_related_of_length_eq_zero
      p q hpq hpZero
    subst q
    exact hpqNot (PI.refl p)
  have hqLength : q.length ≠ 0 :=
    rayPath_length_ne_zero_of_related_of_not_isIso
      (rayPathMap_not_isIso_of_length_ne_zero p hpLength) hpq
  let dp := chosenPathFinalDecomposition p hpLength
  let dq := chosenPathFinalDecomposition q hqLength
  have hessential : IsEssentialPathContour R PI p q := ⟨hpq, hpqNot⟩
  have hprimaryPHead : selectedArrowCount
      (singleArrowSelector primary) dp.head = 0 := by
    apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
      R PI primary dp.head dp.arrow q
    · rw [← dp.path_eq]
      exact hessential
    · exact hprimary
  have hcompanionPHead : selectedArrowCount
      (singleArrowSelector companion) dp.head = 0 := by
    apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
      R PI companion dp.head dp.arrow q
    · rw [← dp.path_eq]
      exact hessential
    · exact hcompanion
  have hessentialSymm : IsEssentialPathContour R PI q p :=
    ⟨R.symm hpq, fun hqp ↦ hpqNot (PI.symm hqp)⟩
  have hprimaryQHead : selectedArrowCount
      (singleArrowSelector primary) dq.head = 0 := by
    apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
      R PI primary dq.head dq.arrow p
    · rw [← dq.path_eq]
      exact hessentialSymm
    · exact hprimary
  have hcompanionQHead : selectedArrowCount
      (singleArrowSelector companion) dq.head = 0 := by
    apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
      R PI companion dq.head dq.arrow p
    · rw [← dq.path_eq]
      exact hessentialSymm
    · exact hcompanion
  have hprimaryP : selectedArrowCount (singleArrowSelector primary) p =
      selectedArrowCount (singleArrowSelector primary) dp.arrow.toPath := by
    conv_lhs => rw [dp.path_eq]
    rw [selectedArrowCount_comp, hprimaryPHead]
    simp
  have hcompanionP : selectedArrowCount (singleArrowSelector companion) p =
      selectedArrowCount (singleArrowSelector companion) dp.arrow.toPath := by
    conv_lhs => rw [dp.path_eq]
    rw [selectedArrowCount_comp, hcompanionPHead]
    simp
  have hprimaryQ : selectedArrowCount (singleArrowSelector primary) q =
      selectedArrowCount (singleArrowSelector primary) dq.arrow.toPath := by
    conv_lhs => rw [dq.path_eq]
    rw [selectedArrowCount_comp, hprimaryQHead]
    simp
  have hcompanionQ : selectedArrowCount (singleArrowSelector companion) q =
      selectedArrowCount (singleArrowSelector companion) dq.arrow.toPath := by
    conv_lhs => rw [dq.path_eq]
    rw [selectedArrowCount_comp, hcompanionQHead]
    simp
  rw [hprimaryP, hcompanionP, hprimaryQ, hcompanionQ]
  exact hpair p q hpq hpNotMem hpqNot dp dq

/-- In a three-class final-arrow configuration, suffix triviality of one
selected endpoint arrow forces that arrow to be absent from every surviving
essential contour of the principal residue. -/
theorem ZeroHomIdeal.bundledArrowAbsent_principal_of_three_essential_finalContours
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [IsRayCrownFree C]
    {x z : RayVertex C} {p q r : Quiver.Path x z}
    (hpq : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (hpr : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p r)
    (hqr : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) q r)
    (dp : PathFinalDecomposition p) (dq : PathFinalDecomposition q)
    (dr : PathFinalDecomposition r)
    (hcard : Nat.card (IncomingQuiverArrow z) ≤ 3)
    (hsuffix : EssentialContourArrowSuffixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C)))
      (bundledQuiverArrow dp.arrow)) :
    ZeroHomIdeal.BundledArrowAbsentFromSurvivingEssentialContours
      (principalZeroHomIdeal (rayPathMap p))
      (bundledQuiverArrow dp.arrow) := by
  classical
  let J := principalZeroHomIdeal (rayPathMap p)
  let alpha : IncomingQuiverArrow z := ⟨dp.middle, dp.arrow⟩
  let beta : IncomingQuiverArrow z := ⟨dq.middle, dq.arrow⟩
  let gamma : IncomingQuiverArrow z := ⟨dr.middle, dr.arrow⟩
  have hAlphaBeta : alpha ≠ beta := by
    intro h
    apply hpq.2
    exact rayPaths_interlaced_of_finalDecomposition_code_eq dp dq hpq.1 h
  have hAlphaGamma : alpha ≠ gamma := by
    intro h
    apply hpr.2
    exact rayPaths_interlaced_of_finalDecomposition_code_eq dp dr hpr.1 h
  have hBetaGamma : beta ≠ gamma := by
    intro h
    apply hqr.2
    exact rayPaths_interlaced_of_finalDecomposition_code_eq dq dr hqr.1 h
  letI : Finite (IncomingQuiverArrow z) := incomingQuiverArrow_finite z
  have hcover : ∀ a : IncomingQuiverArrow z,
      a = alpha ∨ a = beta ∨ a = gamma := fun a =>
    eq_first_or_eq_second_or_eq_third_of_natCard_le_three
      hcard hAlphaBeta hAlphaGamma hBetaGamma
  by_contra hnot
  obtain ⟨w, z', u, v, du, dv, huv, huNotMem, huvNot,
      hduArrow, hdvArrow⟩ :=
    J.exists_survivingEssentialContour_finalDecompositions_of_not_absent
      (bundledQuiverArrow dp.arrow) hsuffix (by simpa [J] using hnot)
  have hzz : z' = z := congrArg
    (fun a : BundledQuiverArrow (RayVertex C) => a.2.1) hduArrow
  subst z'
  let epsilon : IncomingQuiverArrow z := ⟨du.middle, du.arrow⟩
  let phi : IncomingQuiverArrow z := ⟨dv.middle, dv.arrow⟩
  have hEpsilonAlpha : epsilon = alpha := by
    apply bundledQuiverArrow_injective_on_incoming
    exact hduArrow
  have hPhiAlpha : phi ≠ alpha := by
    intro h
    apply hdvArrow
    exact congrArg
      (fun a : IncomingQuiverArrow z => bundledQuiverArrow a.2) h
  let mu := rayPathMorphism p hpq.1.1
  let eta := rayPathMorphism u huv.1
  have hpqSup :=
    isRayPairSupremum_rayPathMorphism_of_essential_finalDecompositions
      dp dq hpq.1 hpq.2
  have hprSup :=
    isRayPairSupremum_rayPathMorphism_of_essential_finalDecompositions
      dp dr hpr.1 hpr.2
  have huvSup :=
    isRayPairSupremum_rayPathMorphism_of_essential_finalDecompositions
      du dv huv huvNot
  have hmem_of_mu_le_eta (hmuEta : mu ≤ eta) :
      (principalZeroHomIdeal (rayPathMap p)).mem (rayPathMap u) := by
    change FactorsThroughMorphism (rayPathMap p) (rayPathMap u)
    obtain ⟨h, hh⟩ := hmuEta
    refine ⟨𝟙 z.obj, h, ?_⟩
    change rayPathMap u = 𝟙 z.obj ≫ rayPathMap p ≫ h
    simpa [mu, eta, rayPathMorphism] using hh.symm
  rcases hcover phi with hPhiAlpha' | hPhiBeta | hPhiGamma
  · exact hPhiAlpha hPhiAlpha'
  · have huvSup' : IsRayPairSupremum
        dp.rayArrowNonzeroHom.toMorphismFrom
        dq.rayArrowNonzeroHom.toMorphismFrom eta := by
      change IsRayPairSupremum
        (incomingQuiverArrowNonzeroHom (C := C) epsilon).toMorphismFrom
        (incomingQuiverArrowNonzeroHom (C := C) phi).toMorphismFrom
        eta at huvSup
      rw [hEpsilonAlpha, hPhiBeta] at huvSup
      simpa [alpha, beta, eta, incomingQuiverArrowNonzeroHom,
        PathFinalDecomposition.rayArrowNonzeroHom] using huvSup
    apply huNotMem
    exact hmem_of_mu_le_eta
      (hpqSup.2.2 eta huvSup'.1 huvSup'.2.1)
  · have huvSup' : IsRayPairSupremum
        dp.rayArrowNonzeroHom.toMorphismFrom
        dr.rayArrowNonzeroHom.toMorphismFrom eta := by
      change IsRayPairSupremum
        (incomingQuiverArrowNonzeroHom (C := C) epsilon).toMorphismFrom
        (incomingQuiverArrowNonzeroHom (C := C) phi).toMorphismFrom
        eta at huvSup
      rw [hEpsilonAlpha, hPhiGamma] at huvSup
      simpa [alpha, gamma, eta, incomingQuiverArrowNonzeroHom,
        PathFinalDecomposition.rayArrowNonzeroHom] using huvSup
    apply huNotMem
    exact hmem_of_mu_le_eta
      (hprSup.2.2 eta huvSup'.1 huvSup'.2.1)

/-- The fixed-target dual of the preceding Figure-59 absence theorem. -/
theorem ZeroHomIdeal.bundledArrowAbsent_principal_of_three_essential_initialContours
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [IsRayCocrownFree C]
    {x z : RayVertex C} {p q r : Quiver.Path x z}
    (hpq : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (hpr : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p r)
    (hqr : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) q r)
    (dp : PathInitialDecomposition p) (dq : PathInitialDecomposition q)
    (dr : PathInitialDecomposition r)
    (hcard : Nat.card (OutgoingQuiverArrow x) ≤ 3)
    (hprefix : EssentialContourArrowPrefixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C)))
      (bundledQuiverArrow dp.arrow)) :
    ZeroHomIdeal.BundledArrowAbsentFromSurvivingEssentialContours
      (principalZeroHomIdeal (rayPathMap p))
      (bundledQuiverArrow dp.arrow) := by
  classical
  let J := principalZeroHomIdeal (rayPathMap p)
  let alpha : OutgoingQuiverArrow x := ⟨dp.middle, dp.arrow⟩
  let beta : OutgoingQuiverArrow x := ⟨dq.middle, dq.arrow⟩
  let gamma : OutgoingQuiverArrow x := ⟨dr.middle, dr.arrow⟩
  have hAlphaBeta : alpha ≠ beta := by
    intro h
    apply hpq.2
    exact rayPaths_interlaced_of_initialDecomposition_code_eq dp dq hpq.1 h
  have hAlphaGamma : alpha ≠ gamma := by
    intro h
    apply hpr.2
    exact rayPaths_interlaced_of_initialDecomposition_code_eq dp dr hpr.1 h
  have hBetaGamma : beta ≠ gamma := by
    intro h
    apply hqr.2
    exact rayPaths_interlaced_of_initialDecomposition_code_eq dq dr hqr.1 h
  letI : Finite (OutgoingQuiverArrow x) := outgoingQuiverArrow_finite x
  have hcover : ∀ a : OutgoingQuiverArrow x,
      a = alpha ∨ a = beta ∨ a = gamma := fun a =>
    eq_first_or_eq_second_or_eq_third_of_natCard_le_three
      hcard hAlphaBeta hAlphaGamma hBetaGamma
  by_contra hnot
  obtain ⟨x', w, u, v, du, dv, huv, huNotMem, huvNot,
      hduArrow, hdvArrow⟩ :=
    J.exists_survivingEssentialContour_initialDecompositions_of_not_absent
      (bundledQuiverArrow dp.arrow) hprefix (by simpa [J] using hnot)
  have hxx : x' = x := congrArg
    (fun a : BundledQuiverArrow (RayVertex C) => a.1) hduArrow
  subst x'
  let epsilon : OutgoingQuiverArrow x := ⟨du.middle, du.arrow⟩
  let phi : OutgoingQuiverArrow x := ⟨dv.middle, dv.arrow⟩
  have hEpsilonAlpha : epsilon = alpha := by
    apply bundledQuiverArrow_injective_on_outgoing
    exact hduArrow
  have hPhiAlpha : phi ≠ alpha := by
    intro h
    apply hdvArrow
    exact congrArg
      (fun a : OutgoingQuiverArrow x => bundledQuiverArrow a.2) h
  let mu := rayPathMorphismTo p hpq.1.1
  let eta := rayPathMorphismTo u huv.1
  have hpqInf :=
    isRayPairInfimum_rayPathMorphismTo_of_essential_initialDecompositions
      dp dq hpq.1 hpq.2
  have hprInf :=
    isRayPairInfimum_rayPathMorphismTo_of_essential_initialDecompositions
      dp dr hpr.1 hpr.2
  have huvInf :=
    isRayPairInfimum_rayPathMorphismTo_of_essential_initialDecompositions
      du dv huv huvNot
  have hmem_of_eta_le_mu (hetaMu : eta ≤ mu) :
      (principalZeroHomIdeal (rayPathMap p)).mem (rayPathMap u) := by
    change FactorsThroughMorphism (rayPathMap p) (rayPathMap u)
    obtain ⟨h, hh⟩ := hetaMu
    refine ⟨h, 𝟙 x.obj, ?_⟩
    change rayPathMap u = h ≫ rayPathMap p ≫ 𝟙 x.obj
    simpa [mu, eta, rayPathMorphismTo] using hh.symm
  rcases hcover phi with hPhiAlpha' | hPhiBeta | hPhiGamma
  · exact hPhiAlpha hPhiAlpha'
  · have huvInf' : IsRayPairInfimum
        dp.rayArrowNonzeroHom.toMorphismTo
        dq.rayArrowNonzeroHom.toMorphismTo eta := by
      change IsRayPairInfimum
        (outgoingQuiverArrowNonzeroHom (C := C) epsilon).toMorphismTo
        (outgoingQuiverArrowNonzeroHom (C := C) phi).toMorphismTo
        eta at huvInf
      rw [hEpsilonAlpha, hPhiBeta] at huvInf
      simpa [alpha, beta, eta, outgoingQuiverArrowNonzeroHom,
        PathInitialDecomposition.rayArrowNonzeroHom] using huvInf
    apply huNotMem
    exact hmem_of_eta_le_mu
      (hpqInf.2.2 eta huvInf'.1 huvInf'.2.1)
  · have huvInf' : IsRayPairInfimum
        dp.rayArrowNonzeroHom.toMorphismTo
        dr.rayArrowNonzeroHom.toMorphismTo eta := by
      change IsRayPairInfimum
        (outgoingQuiverArrowNonzeroHom (C := C) epsilon).toMorphismTo
        (outgoingQuiverArrowNonzeroHom (C := C) phi).toMorphismTo
        eta at huvInf
      rw [hEpsilonAlpha, hPhiGamma] at huvInf
      simpa [alpha, gamma, eta, outgoingQuiverArrowNonzeroHom,
        PathInitialDecomposition.rayArrowNonzeroHom] using huvInf
    apply huNotMem
    exact hmem_of_eta_le_mu
      (hprInf.2.2 eta huvInf'.1 huvInf'.2.1)

/-- Two suffix-trivial final arrows with balanced endpoints give the paired
`N = 2` correction when the primary arrow occurs only on the anchor side. -/
theorem ZeroHomIdeal.hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass_finalArrow_of_pairBalanced
    [Finite C] [IsFiniteRayCategory C]
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
    (companion : IncomingQuiverArrow j)
    (hotherPrimary : bundledQuiverArrow dq.arrow ≠
      bundledQuiverArrow dp.arrow)
    (hprimaryCompanion : bundledQuiverArrow dp.arrow ≠
      bundledQuiverArrow companion.2)
    (hotherCompanion : bundledQuiverArrow dq.arrow ≠
      bundledQuiverArrow companion.2)
    (hprimarySuffix : EssentialContourArrowSuffixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C)))
      (bundledQuiverArrow dp.arrow))
    (hcompanionSuffix : EssentialContourArrowSuffixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C)))
      (bundledQuiverArrow companion.2))
    (hpair : J.FinalArrowPairBalanceOnSurvivingEssentialContours
      (bundledQuiverArrow dp.arrow)
      (bundledQuiverArrow companion.2)) :
    J.HasInvisibleCorrectionClingingOnRelatedPaths (k := k) p := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  have hessential : IsEssentialPathContour R PI p q := ⟨hpq, hpqNot⟩
  apply J.hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass_of_pairBalanced
    p q hpp hpq hpqNot hcard
    (singleArrowSelector (bundledQuiverArrow dp.arrow))
    (singleArrowSelector (bundledQuiverArrow companion.2))
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
          · exact hprimarySuffix)
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow)) q =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow))
          (dq.head.comp dq.arrow.toPath) := congrArg _ dq.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_final_eq_zero_of_ne
        dp.arrow dq.head dq.arrow hotherPrimary (by
          apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
            R PI (bundledQuiverArrow dp.arrow) dq.head dq.arrow p
          · simpa only [dq.path_eq] using hessential.symm
          · exact hprimarySuffix)
  · have hcompanionP : selectedArrowCount
        (singleArrowSelector (bundledQuiverArrow companion.2)) p = 0 := by
      calc
        _ = selectedArrowCount
            (singleArrowSelector (bundledQuiverArrow companion.2))
            (dp.head.comp dp.arrow.toPath) := congrArg _ dp.path_eq
        _ = 0 := selectedArrowCount_singleArrowSelector_final_eq_zero_of_ne
          companion.2 dp.head dp.arrow hprimaryCompanion (by
            apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
              R PI (bundledQuiverArrow companion.2) dp.head dp.arrow q
            · simpa only [dp.path_eq] using hessential
            · exact hcompanionSuffix)
    have hcompanionQ : selectedArrowCount
        (singleArrowSelector (bundledQuiverArrow companion.2)) q = 0 := by
      calc
        _ = selectedArrowCount
            (singleArrowSelector (bundledQuiverArrow companion.2))
            (dq.head.comp dq.arrow.toPath) := congrArg _ dq.path_eq
        _ = 0 := selectedArrowCount_singleArrowSelector_final_eq_zero_of_ne
          companion.2 dq.head dq.arrow hotherCompanion (by
            apply selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
              R PI (bundledQuiverArrow companion.2) dq.head dq.arrow p
            · simpa only [dq.path_eq] using hessential.symm
            · exact hcompanionSuffix)
    exact hcompanionP.trans hcompanionQ.symm
  · intro a b
    exact J.arrowSelectorPairBalanced_single_of_finalArrowPairBalance
      (a := a) (b := b)
      (bundledQuiverArrow dp.arrow) (bundledQuiverArrow companion.2)
      hprimarySuffix hcompanionSuffix hpair

/-- The endpoint form of joint selector balance for two initial-arrow
selectors, dual to `FinalArrowPairBalanceOnSurvivingEssentialContours`. -/
def ZeroHomIdeal.InitialArrowPairBalanceOnSurvivingEssentialContours
    (J : ZeroHomIdeal C)
    (primary companion : BundledQuiverArrow (RayVertex C)) : Prop :=
  ∀ {x z : RayVertex C} (p q : Quiver.Path x z),
    (rayPathContourRelation (C := C)).related p q →
      ¬J.mem (rayPathMap p) →
        ¬(properWhiskerInterlacementRelation
          (rayPathContourRelation (C := C))).interlaced p q →
          ∀ (dp : PathInitialDecomposition p)
            (dq : PathInitialDecomposition q),
            selectedArrowCount (singleArrowSelector primary)
                  dp.arrow.toPath +
                selectedArrowCount (singleArrowSelector companion)
                  dp.arrow.toPath =
              selectedArrowCount (singleArrowSelector primary)
                  dq.arrow.toPath +
                selectedArrowCount (singleArrowSelector companion)
                  dq.arrow.toPath

/-- The fixed-target three-arrow geometry makes the two surviving
initial-arrow selectors jointly balanced on every surviving contour. -/
theorem ZeroHomIdeal.initialArrowPairBalance_principal_of_sharedSurvivingContour_of_figure
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [IsRayCocrownFree C]
    {x z w : RayVertex C}
    {p q : Quiver.Path x z} {r s : Quiver.Path x w}
    (hpq : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (hrs : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) r s)
    (hrSurvives : ¬(principalZeroHomIdeal (rayPathMap p)).mem
      (rayPathMap r))
    (dp : PathInitialDecomposition p) (dq : PathInitialDecomposition q)
    (dr : PathInitialDecomposition r) (ds : PathInitialDecomposition s)
    (hshared : (⟨dp.middle, dp.arrow⟩ : OutgoingQuiverArrow x) =
      ⟨dr.middle, dr.arrow⟩)
    (hcard : Nat.card (OutgoingQuiverArrow x) ≤ 3)
    (hfigure : IsRayCoThreeArrowFigure
      dq.rayArrowNonzeroHom.toMorphismTo
      dp.rayArrowNonzeroHom.toMorphismTo
      ds.rayArrowNonzeroHom.toMorphismTo) :
    (principalZeroHomIdeal (rayPathMap p)).InitialArrowPairBalanceOnSurvivingEssentialContours
        (bundledQuiverArrow dp.arrow)
        (bundledQuiverArrow ds.arrow) := by
  have hprimaryCompanion :
      bundledQuiverArrow dp.arrow ≠ bundledQuiverArrow ds.arrow := by
    intro h
    have hcode :
        (⟨dp.middle, dp.arrow⟩ : OutgoingQuiverArrow x) =
          ⟨ds.middle, ds.arrow⟩ :=
      bundledQuiverArrow_injective_on_outgoing h
    apply hrs.2
    apply rayPaths_interlaced_of_initialDecomposition_code_eq dr ds hrs.1
    exact hshared.symm.trans hcode
  intro x' z' u v huv huSurvives huvNot du dv
  by_cases hxx : x' = x
  · subst x'
    have hpair :=
      survivingEssentialContour_initialArrow_pair_eq_sharedPair_of_figure
        hpq hrs ⟨huv, huvNot⟩ hrSurvives huSurvives
        dp dq dr ds du dv hshared hcard hfigure
    rcases hpair with hpair | hpair
    · have hdu : bundledQuiverArrow du.arrow =
          bundledQuiverArrow dp.arrow :=
        congrArg (fun a : OutgoingQuiverArrow x =>
          bundledQuiverArrow a.2) hpair.1
      have hdv : bundledQuiverArrow dv.arrow =
          bundledQuiverArrow ds.arrow :=
        congrArg (fun a : OutgoingQuiverArrow x =>
          bundledQuiverArrow a.2) hpair.2
      rw [← hdu, ← hdv]
      exact selectedArrowCount_singleArrowSelector_pair_swap
        du.arrow dv.arrow
        (fun h => hprimaryCompanion
          (hdu.symm.trans (h.trans hdv)))
    · have hdu : bundledQuiverArrow du.arrow =
          bundledQuiverArrow ds.arrow :=
        congrArg (fun a : OutgoingQuiverArrow x =>
          bundledQuiverArrow a.2) hpair.1
      have hdv : bundledQuiverArrow dv.arrow =
          bundledQuiverArrow dp.arrow :=
        congrArg (fun a : OutgoingQuiverArrow x =>
          bundledQuiverArrow a.2) hpair.2
      rw [← hdu, ← hdv]
      exact
        (selectedArrowCount_singleArrowSelector_pair_swap
          dv.arrow du.arrow
          (fun h => hprimaryCompanion
            (hdv.symm.trans (h.trans hdu)))).symm
  · have hduPrimary : bundledQuiverArrow du.arrow ≠
        bundledQuiverArrow dp.arrow := by
      intro h
      apply hxx
      exact congrArg
        (fun a : BundledQuiverArrow (RayVertex C) => a.1) h
    have hduCompanion : bundledQuiverArrow du.arrow ≠
        bundledQuiverArrow ds.arrow := by
      intro h
      apply hxx
      exact congrArg
        (fun a : BundledQuiverArrow (RayVertex C) => a.1) h
    have hdvPrimary : bundledQuiverArrow dv.arrow ≠
        bundledQuiverArrow dp.arrow := by
      intro h
      apply hxx
      exact congrArg
        (fun a : BundledQuiverArrow (RayVertex C) => a.1) h
    have hdvCompanion : bundledQuiverArrow dv.arrow ≠
        bundledQuiverArrow ds.arrow := by
      intro h
      apply hxx
      exact congrArg
        (fun a : BundledQuiverArrow (RayVertex C) => a.1) h
    rw [selectedArrowCount_singleArrowSelector_toPath_of_ne
          dp.arrow du.arrow hduPrimary,
      selectedArrowCount_singleArrowSelector_toPath_of_ne
          ds.arrow du.arrow hduCompanion,
      selectedArrowCount_singleArrowSelector_toPath_of_ne
          dp.arrow dv.arrow hdvPrimary,
      selectedArrowCount_singleArrowSelector_toPath_of_ne
          ds.arrow dv.arrow hdvCompanion]

/-- The preceding initial-arrow balance follows automatically from a killed
essential contour and a surviving shared-arrow essential contour. -/
theorem ZeroHomIdeal.initialArrowPairBalance_principal_of_sharedSurvivingContour
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [IsRayCocrownFree C]
    {x z w : RayVertex C}
    {p q : Quiver.Path x z} {r s : Quiver.Path x w}
    (hpq : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p q)
    (hrs : IsEssentialPathContour
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) r s)
    (hrSurvives : ¬(principalZeroHomIdeal (rayPathMap p)).mem
      (rayPathMap r))
    (dp : PathInitialDecomposition p) (dq : PathInitialDecomposition q)
    (dr : PathInitialDecomposition r) (ds : PathInitialDecomposition s)
    (hshared : (⟨dp.middle, dp.arrow⟩ : OutgoingQuiverArrow x) =
      ⟨dr.middle, dr.arrow⟩)
    (hcard : Nat.card (OutgoingQuiverArrow x) ≤ 3) :
    (principalZeroHomIdeal (rayPathMap p)).InitialArrowPairBalanceOnSurvivingEssentialContours
        (bundledQuiverArrow dp.arrow)
        (bundledQuiverArrow ds.arrow) := by
  apply ZeroHomIdeal.initialArrowPairBalance_principal_of_sharedSurvivingContour_of_figure
    hpq hrs hrSurvives dp dq dr ds hshared hcard
  exact isRayCoThreeArrowFigure_of_essential_initialContours_principal_survivor
    hpq hrs hrSurvives dp dq dr ds hshared

/-- The initial-arrow dual of beta absence from a local three-arrow cover. -/
theorem ZeroHomIdeal.bundledArrowAbsent_of_initialArrowPairBalance_of_cover
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    (J : ZeroHomIdeal C)
    {x : RayVertex C}
    (beta gamma delta : OutgoingQuiverArrow x)
    (hbetaGamma : beta ≠ gamma)
    (hbetaDelta : beta ≠ delta)
    (hcover : ∀ a : OutgoingQuiverArrow x,
      a = beta ∨ a = gamma ∨ a = delta)
    (hbetaPrefix : EssentialContourArrowPrefixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C)))
      (bundledQuiverArrow beta.2))
    (hpair : J.InitialArrowPairBalanceOnSurvivingEssentialContours
      (bundledQuiverArrow gamma.2) (bundledQuiverArrow delta.2)) :
    J.BundledArrowAbsentFromSurvivingEssentialContours
      (bundledQuiverArrow beta.2) := by
  classical
  by_contra hnot
  obtain ⟨x', z, p, q, dp, dq, hpq, hpNotMem, hpqNot,
      hdpArrow, hdqArrow⟩ :=
    J.exists_survivingEssentialContour_initialDecompositions_of_not_absent
      (bundledQuiverArrow beta.2) hbetaPrefix hnot
  have hxx : x' = x := congrArg
    (fun a : BundledQuiverArrow (RayVertex C) => a.1) hdpArrow
  subst x'
  let dqCode : OutgoingQuiverArrow x := ⟨dq.middle, dq.arrow⟩
  have hdqCodeNe : dqCode ≠ beta := by
    intro h
    exact hdqArrow (congrArg (fun a : OutgoingQuiverArrow x =>
      bundledQuiverArrow a.2) h)
  have hdpGamma : bundledQuiverArrow dp.arrow ≠
      bundledQuiverArrow gamma.2 := by
    intro h
    apply hbetaGamma
    apply bundledQuiverArrow_injective_on_outgoing
    change bundledQuiverArrow beta.2 = bundledQuiverArrow gamma.2
    rw [← hdpArrow]
    exact h
  have hdpDelta : bundledQuiverArrow dp.arrow ≠
      bundledQuiverArrow delta.2 := by
    intro h
    apply hbetaDelta
    apply bundledQuiverArrow_injective_on_outgoing
    change bundledQuiverArrow beta.2 = bundledQuiverArrow delta.2
    rw [← hdpArrow]
    exact h
  have hgammaDp : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow gamma.2))
      dp.arrow.toPath = 0 :=
    selectedArrowCount_singleArrowSelector_toPath_of_ne
      gamma.2 dp.arrow hdpGamma
  have hdeltaDp : selectedArrowCount
      (singleArrowSelector (bundledQuiverArrow delta.2))
      dp.arrow.toPath = 0 :=
    selectedArrowCount_singleArrowSelector_toPath_of_ne
      delta.2 dp.arrow hdpDelta
  have hbalance := hpair p q hpq hpNotMem hpqNot dp dq
  rcases hcover dqCode with hdqBeta | hdqGamma | hdqDelta
  · exact hdqCodeNe hdqBeta
  · have hdqGammaBundle : bundledQuiverArrow dq.arrow =
        bundledQuiverArrow gamma.2 := congrArg
      (fun a : OutgoingQuiverArrow x => bundledQuiverArrow a.2) hdqGamma
    have hgammaDq : selectedArrowCount
        (singleArrowSelector (bundledQuiverArrow gamma.2))
        dq.arrow.toPath = 1 := by
      rw [← hdqGammaBundle]
      exact selectedArrowCount_singleArrowSelector_toPath dq.arrow
    rw [hgammaDp, hdeltaDp, hgammaDq] at hbalance
    omega
  · have hdqDeltaBundle : bundledQuiverArrow dq.arrow =
        bundledQuiverArrow delta.2 := congrArg
      (fun a : OutgoingQuiverArrow x => bundledQuiverArrow a.2) hdqDelta
    have hdeltaDq : selectedArrowCount
        (singleArrowSelector (bundledQuiverArrow delta.2))
        dq.arrow.toPath = 1 := by
      rw [← hdqDeltaBundle]
      exact selectedArrowCount_singleArrowSelector_toPath dq.arrow
    rw [hgammaDp, hdeltaDp, hdeltaDq] at hbalance
    omega

/-- The initial-arrow pairing supplied by the cohook geometry is exactly the
joint selector balance needed for the paired residue correction. -/
theorem ZeroHomIdeal.arrowSelectorPairBalanced_single_of_initialArrowPairBalance
    [Finite C] [IsFiniteRayCategory C]
    (J : ZeroHomIdeal C)
    (primary companion : BundledQuiverArrow (RayVertex C))
    (hprimary : EssentialContourArrowPrefixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) primary)
    (hcompanion : EssentialContourArrowPrefixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) companion)
    (hpair : J.InitialArrowPairBalanceOnSurvivingEssentialContours
      primary companion) :
    J.ArrowSelectorPairBalancedOnSurvivingEssentialContours
      (singleArrowSelector primary) (singleArrowSelector companion) := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  intro x z p q hpq hpNotMem hpqNot
  have hpLength : p.length ≠ 0 := by
    intro hpZero
    have hpqEq := rayPath_eq_of_related_of_length_eq_zero
      p q hpq hpZero
    subst q
    exact hpqNot (PI.refl p)
  have hqLength : q.length ≠ 0 :=
    rayPath_length_ne_zero_of_related_of_not_isIso
      (rayPathMap_not_isIso_of_length_ne_zero p hpLength) hpq
  let dp := chosenPathInitialDecomposition p hpLength
  let dq := chosenPathInitialDecomposition q hqLength
  have hessential : IsEssentialPathContour R PI p q := ⟨hpq, hpqNot⟩
  have hprimaryPTail : selectedArrowCount
      (singleArrowSelector primary) dp.tail = 0 := by
    apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
      R PI primary dp.arrow dp.tail q
    · rw [← dp.path_eq]
      exact hessential
    · exact hprimary
  have hcompanionPTail : selectedArrowCount
      (singleArrowSelector companion) dp.tail = 0 := by
    apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
      R PI companion dp.arrow dp.tail q
    · rw [← dp.path_eq]
      exact hessential
    · exact hcompanion
  have hessentialSymm : IsEssentialPathContour R PI q p :=
    ⟨R.symm hpq, fun hqp ↦ hpqNot (PI.symm hqp)⟩
  have hprimaryQTail : selectedArrowCount
      (singleArrowSelector primary) dq.tail = 0 := by
    apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
      R PI primary dq.arrow dq.tail p
    · rw [← dq.path_eq]
      exact hessentialSymm
    · exact hprimary
  have hcompanionQTail : selectedArrowCount
      (singleArrowSelector companion) dq.tail = 0 := by
    apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
      R PI companion dq.arrow dq.tail p
    · rw [← dq.path_eq]
      exact hessentialSymm
    · exact hcompanion
  have hprimaryP : selectedArrowCount (singleArrowSelector primary) p =
      selectedArrowCount (singleArrowSelector primary) dp.arrow.toPath := by
    conv_lhs => rw [dp.path_eq]
    rw [selectedArrowCount_comp, hprimaryPTail]
    simp
  have hcompanionP : selectedArrowCount (singleArrowSelector companion) p =
      selectedArrowCount (singleArrowSelector companion) dp.arrow.toPath := by
    conv_lhs => rw [dp.path_eq]
    rw [selectedArrowCount_comp, hcompanionPTail]
    simp
  have hprimaryQ : selectedArrowCount (singleArrowSelector primary) q =
      selectedArrowCount (singleArrowSelector primary) dq.arrow.toPath := by
    conv_lhs => rw [dq.path_eq]
    rw [selectedArrowCount_comp, hprimaryQTail]
    simp
  have hcompanionQ : selectedArrowCount (singleArrowSelector companion) q =
      selectedArrowCount (singleArrowSelector companion) dq.arrow.toPath := by
    conv_lhs => rw [dq.path_eq]
    rw [selectedArrowCount_comp, hcompanionQTail]
    simp
  rw [hprimaryP, hcompanionP, hprimaryQ, hcompanionQ]
  exact hpair p q hpq hpNotMem hpqNot dp dq

/-- Initial-arrow dual of the paired final-arrow `N = 2` correction. -/
theorem ZeroHomIdeal.hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass_initialArrow_of_pairBalanced
    [Finite C] [IsFiniteRayCategory C]
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
    (companion : OutgoingQuiverArrow i)
    (hotherPrimary : bundledQuiverArrow dq.arrow ≠
      bundledQuiverArrow dp.arrow)
    (hprimaryCompanion : bundledQuiverArrow dp.arrow ≠
      bundledQuiverArrow companion.2)
    (hotherCompanion : bundledQuiverArrow dq.arrow ≠
      bundledQuiverArrow companion.2)
    (hprimaryPrefix : EssentialContourArrowPrefixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C)))
      (bundledQuiverArrow dp.arrow))
    (hcompanionPrefix : EssentialContourArrowPrefixTrivial
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C)))
      (bundledQuiverArrow companion.2))
    (hpair : J.InitialArrowPairBalanceOnSurvivingEssentialContours
      (bundledQuiverArrow dp.arrow)
      (bundledQuiverArrow companion.2)) :
    J.HasInvisibleCorrectionClingingOnRelatedPaths (k := k) p := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  have hessential : IsEssentialPathContour R PI p q := ⟨hpq, hpqNot⟩
  apply J.hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass_of_pairBalanced
    p q hpp hpq hpqNot hcard
    (singleArrowSelector (bundledQuiverArrow dp.arrow))
    (singleArrowSelector (bundledQuiverArrow companion.2))
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
          · exact hprimaryPrefix)
  · calc
      selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow)) q =
        selectedArrowCount
          (singleArrowSelector (bundledQuiverArrow dp.arrow))
          (dq.arrow.toPath.comp dq.tail) := congrArg _ dq.path_eq
      _ = 0 := selectedArrowCount_singleArrowSelector_initial_eq_zero_of_ne
        dp.arrow dq.arrow dq.tail hotherPrimary (by
          apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
            R PI (bundledQuiverArrow dp.arrow) dq.arrow dq.tail p
          · simpa only [dq.path_eq] using hessential.symm
          · exact hprimaryPrefix)
  · have hcompanionP : selectedArrowCount
        (singleArrowSelector (bundledQuiverArrow companion.2)) p = 0 := by
      calc
        _ = selectedArrowCount
            (singleArrowSelector (bundledQuiverArrow companion.2))
            (dp.arrow.toPath.comp dp.tail) := congrArg _ dp.path_eq
        _ = 0 := selectedArrowCount_singleArrowSelector_initial_eq_zero_of_ne
          companion.2 dp.arrow dp.tail hprimaryCompanion (by
            apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
              R PI (bundledQuiverArrow companion.2) dp.arrow dp.tail q
            · simpa only [dp.path_eq] using hessential
            · exact hcompanionPrefix)
    have hcompanionQ : selectedArrowCount
        (singleArrowSelector (bundledQuiverArrow companion.2)) q = 0 := by
      calc
        _ = selectedArrowCount
            (singleArrowSelector (bundledQuiverArrow companion.2))
            (dq.arrow.toPath.comp dq.tail) := congrArg _ dq.path_eq
        _ = 0 := selectedArrowCount_singleArrowSelector_initial_eq_zero_of_ne
          companion.2 dq.arrow dq.tail hotherCompanion (by
            apply selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
              R PI (bundledQuiverArrow companion.2) dq.arrow dq.tail p
            · simpa only [dq.path_eq] using hessential.symm
            · exact hcompanionPrefix)
    exact hcompanionP.trans hcompanionQ.symm
  · intro a b
    exact J.arrowSelectorPairBalanced_single_of_initialArrowPairBalance
      (a := a) (b := b)
      (bundledQuiverArrow dp.arrow) (bundledQuiverArrow companion.2)
      hprimaryPrefix hcompanionPrefix hpair

namespace RayHookTackle

/-- The final object introduced by replacing the last hook is the target of
the replacement morphism. -/
private theorem replaceLast_z_last
    {m : ℕ} (t : RayHookTackle (C := C) m)
    {Z : C} (f : NonzeroHom (t.x (Fin.last m)) Z)
    (hf : IsIrreducibleRayMorphism f.1)
    (hcomp : t.LastReplacementCompatible f) :
    (t.replaceLast f hf hcomp).z (Fin.last m) = Z := by
  cases m <;> simp [RayHookTackle.replaceLast]

/-- After transporting endpoints, the replaced last rho is the replacement
morphism itself. -/
private theorem replaceLast_rho_last_cast
    {m : ℕ} (t : RayHookTackle (C := C) m)
    {Z : C} (f : NonzeroHom (t.x (Fin.last m)) Z)
    (hf : IsIrreducibleRayMorphism f.1)
    (hcomp : t.LastReplacementCompatible f) :
    NonzeroHom.cast (t.replaceLast_x f hf hcomp (Fin.last m))
      (t.replaceLast_z_last f hf hcomp)
      ((t.replaceLast f hf hcomp).rho (Fin.last m)) = f := by
  cases m with
  | zero => simp [RayHookTackle.replaceLast, NonzeroHom.cast]
  | succ n =>
    simp [RayHookTackle.replaceLast]
    rw [nonzeroHom_cast_comp]
    apply nonzeroHom_cast_self

/-- The last arrow of a replaced hook tackle is the bundled reversed arrow of
the replacement morphism. -/
theorem bundledQuiverArrow_replaceLast_lastArrow_eq
    {m : ℕ} (t : RayHookTackle (C := C) m)
    {Z : C} (f : NonzeroHom (t.x (Fin.last m)) Z)
    (hf : IsIrreducibleRayMorphism f.1)
    (hcomp : t.LastReplacementCompatible f) :
    bundledQuiverArrow (t.replaceLast f hf hcomp).lastArrow =
      bundledQuiverArrow
        (⟨f.1, hf⟩ : (RayVertex.mk Z : RayVertex C) ⟶
          RayVertex.mk (t.x (Fin.last m))) := by
  let t' := t.replaceLast f hf hcomp
  let a : (RayVertex.mk Z : RayVertex C) ⟶
      RayVertex.mk (t.x (Fin.last m)) := ⟨f.1, hf⟩
  have hi : RayVertex.mk (t'.z (Fin.last m)) = RayVertex.mk Z :=
    RayVertex.ext (t.replaceLast_z_last f hf hcomp)
  have hj : RayVertex.mk (t'.x (Fin.last m)) =
      RayVertex.mk (t.x (Fin.last m)) :=
    RayVertex.ext (t.replaceLast_x f hf hcomp (Fin.last m))
  apply bundledQuiverArrow_eq_of_quiverArrowCast_eq hi hj t'.lastArrow a
  apply quiverArrowCast_eq_of_rayNonzeroHom_cast_eq hi hj
  exact t.replaceLast_rho_last_cast f hf hcomp

private theorem bundledQuiverArrow_hookCastBack
    {m : ℕ} (t : RayHookTackle (C := C) m)
    {i j : RayVertex C} (a : i ⟶ j)
    (hx : j.obj = t.x (Fin.last m)) :
    bundledQuiverArrow
      (⟨(NonzeroHom.cast hx rfl
        (⟨rayArrowMorphism a, a.property.1⟩ : NonzeroHom j.obj i.obj)).1,
          isIrreducibleMorphism_cast hx rfl
            (⟨rayArrowMorphism a, a.property.1⟩ : NonzeroHom j.obj i.obj)
            a.property⟩ :
        (RayVertex.mk i.obj : RayVertex C) ⟶
          RayVertex.mk (t.x (Fin.last m))) = bundledQuiverArrow a := by
  let f := NonzeroHom.cast hx rfl
    (⟨rayArrowMorphism a, a.property.1⟩ : NonzeroHom j.obj i.obj)
  let ac : (RayVertex.mk i.obj : RayVertex C) ⟶
      RayVertex.mk (t.x (Fin.last m)) :=
    ⟨f.1, isIrreducibleMorphism_cast hx rfl
      (⟨rayArrowMorphism a, a.property.1⟩ : NonzeroHom j.obj i.obj)
      a.property⟩
  have hi : (RayVertex.mk i.obj : RayVertex C) = i := RayVertex.ext rfl
  have hj : (RayVertex.mk (t.x (Fin.last m)) : RayVertex C) = j :=
    RayVertex.ext hx.symm
  change bundledQuiverArrow ac = bundledQuiverArrow a
  apply bundledQuiverArrow_eq_of_quiverArrowCast_eq hi hj ac a
  apply quiverArrowCast_eq_of_rayNonzeroHom_cast_eq hi hj
  change NonzeroHom.cast (congrArg RayVertex.obj hj)
      (congrArg RayVertex.obj hi) f =
    (⟨rayArrowMorphism a, a.property.1⟩ : NonzeroHom j.obj i.obj)
  dsimp only [f]
  rw [nonzeroHom_cast_comp]
  apply nonzeroHom_cast_self

/-- Cast-back form used when a path decomposition supplies the replacement
arrow at a propositionally equal endpoint. -/
theorem bundledQuiverArrow_replaceLast_lastArrow_eq_of_cast
    {m : ℕ} (t : RayHookTackle (C := C) m)
    {i j : RayVertex C} (a : i ⟶ j)
    (hx : j.obj = t.x (Fin.last m))
    (hf : IsIrreducibleRayMorphism
      (NonzeroHom.cast hx rfl
        (⟨rayArrowMorphism a, a.property.1⟩ :
          NonzeroHom j.obj i.obj)).1)
    (hcomp : t.LastReplacementCompatible
      (NonzeroHom.cast hx rfl
        (⟨rayArrowMorphism a, a.property.1⟩ :
          NonzeroHom j.obj i.obj))) :
    bundledQuiverArrow
      (t.replaceLast (NonzeroHom.cast hx rfl
        (⟨rayArrowMorphism a, a.property.1⟩ :
          NonzeroHom j.obj i.obj)) hf hcomp).lastArrow =
      bundledQuiverArrow a := by
  calc
    _ = bundledQuiverArrow
        (⟨(NonzeroHom.cast hx rfl
          (⟨rayArrowMorphism a, a.property.1⟩ :
            NonzeroHom j.obj i.obj)).1, hf⟩ :
          (RayVertex.mk i.obj : RayVertex C) ⟶
            RayVertex.mk (t.x (Fin.last m))) :=
      t.bundledQuiverArrow_replaceLast_lastArrow_eq _ hf hcomp
    _ = bundledQuiverArrow a := by
      have hcanonical : hf = isIrreducibleMorphism_cast hx rfl
          (⟨rayArrowMorphism a, a.property.1⟩ :
            NonzeroHom j.obj i.obj) a.property :=
        Subsingleton.elim _ _
      subst hcanonical
      exact bundledQuiverArrow_hookCastBack t a hx

/-- Easy `N = 2` branch for an efficient hook.  The selected maximal path is
normalized by weighting the hook itself; BGRS 8.4 makes it the final arrow of
the selected contour side, and arrow absence makes that weight invisible in
the residue. -/
theorem hasInvisibleCorrectionClingingOnIdeal_principal_of_card_eq_two_of_lastArrowAbsent
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    {m : ℕ} (t : RayHookTackle (C := C) m) {y : C}
    (ht : (RayTackle.hook m t).IsEfficientAt y)
    (p : NonzeroRayPathThroughArrow
      (C := C) (bundledQuiverArrow t.lastArrow))
    (hp : p.IsMaximal)
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p.path) = 2)
    (habsent : ZeroHomIdeal.BundledArrowAbsentFromSurvivingEssentialContours
      (principalZeroHomIdeal (rayPathMap p.path))
      (bundledQuiverArrow t.lastArrow)) :
    ZeroHomIdeal.HasInvisibleCorrectionClingingOnIdeal (k := k)
      (principalZeroHomIdeal (rayPathMap p.path)) := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  have hpp : R.related p.path p.path := ⟨p.map_ne_zero, rfl⟩
  letI : Finite (OutgoingQuiverArrow p.source) :=
    outgoingQuiverArrow_finite p.source
  letI : Finite (RelatedPathInterlacementClass PI p.path) :=
    relatedRayPathInterlacementClass_finite_of_initial
      p.path p.map_not_isIso
  obtain ⟨q, hpq, hpqNot⟩ :=
    exists_related_not_interlaced_of_ray_card_eq_two
      p.path p.length_ne_zero hpp hcard
  have hqLength : q.length ≠ 0 :=
    rayPath_length_ne_zero_of_related_of_not_isIso
      p.map_not_isIso hpq
  have hessential : IsEssentialPathContour R PI p.path q :=
    ⟨hpq, hpqNot⟩
  have hafter : p.occurrence.after.length = 0 :=
    Figure55HookRhoStage.after_length_eq_zero_of_occurrence
      t ht hessential p.occurrence
  obtain ⟨dp, hdpArrow⟩ :=
    p.occurrence.exists_finalDecomposition_of_afterLengthZero hafter
  let dq := chosenPathFinalDecomposition q hqLength
  have harrow : bundledQuiverArrow dq.arrow ≠
      bundledQuiverArrow dp.arrow := by
    intro harrow
    apply hpqNot
    apply rayPaths_interlaced_of_finalDecomposition_code_eq dp dq hpq
    exact (bundledQuiverArrow_injective_on_incoming harrow).symm
  apply ZeroHomIdeal.hasInvisibleCorrectionClingingOnIdeal_principal_of_maximal
    p hp
  apply ZeroHomIdeal.hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass_finalArrow_of_absent
    (principalZeroHomIdeal (rayPathMap p.path))
    p.path q hpp hpq hpqNot hcard dp dq harrow
  · rw [hdpArrow]
    exact Figure55HookRhoStage.essentialContourArrowSuffixTrivial_of_isEfficientAt
      t ht
  · rw [hdpArrow]
    exact habsent

/-- The complete hard `N = 2` hook branch.  If the original hook is absent
from all surviving contours, use the easy singleton correction.  Otherwise
the surviving three-arrow figure and BGRS 8.5 produce an efficient beta or
delta replacement, yielding respectively the orientation-reversed singleton
correction or the balanced gamma/delta correction. -/
theorem hasInvisibleCorrectionClingingOnIdeal_principal_of_card_eq_two
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [HasRayLongPathEndpointValencyAtMostThree C] [IsRayCrownFree C]
    {m : ℕ} (t : RayHookTackle (C := C) m) {y : C}
    (ht : (RayTackle.hook m t).IsEfficientAt y)
    (p : NonzeroRayPathThroughArrow
      (C := C) (bundledQuiverArrow t.lastArrow))
    (hp : p.IsMaximal)
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p.path) = 2) :
    ZeroHomIdeal.HasInvisibleCorrectionClingingOnIdeal (k := k)
      (principalZeroHomIdeal (rayPathMap p.path)) := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  let J := principalZeroHomIdeal (rayPathMap p.path)
  by_cases habsent : J.BundledArrowAbsentFromSurvivingEssentialContours
      (bundledQuiverArrow t.lastArrow)
  · exact
      t.hasInvisibleCorrectionClingingOnIdeal_principal_of_card_eq_two_of_lastArrowAbsent
        ht p hp hcard habsent
  · have hpp : R.related p.path p.path := ⟨p.map_ne_zero, rfl⟩
    have hpLengthTwo : 2 ≤ p.path.length := by
      have hpNotOne : p.path.length ≠ 1 := by
        intro hpOne
        have hOne :=
          relatedRayPathInterlacementClass_card_eq_one_of_length_eq_one
            p.path hpOne hpp
        have hOne' : Nat.card (RelatedPathInterlacementClass
            (properWhiskerInterlacementRelation
              (rayPathContourRelation (C := C))) p.path) = 1 := by
          simpa [R] using hOne
        have : (2 : ℕ) = 1 := hcard.symm.trans hOne'
        simp at this
      have hpNotZero : p.path.length ≠ 0 := p.length_ne_zero
      omega
    have hincomingCard : Nat.card (IncomingQuiverArrow p.target) ≤ 3 :=
      HasRayLongPathEndpointValencyAtMostThree.incoming_card_le
        p.path p.map_ne_zero hpLengthTwo
    letI : Finite (OutgoingQuiverArrow p.source) :=
      outgoingQuiverArrow_finite p.source
    letI : Finite (RelatedPathInterlacementClass PI p.path) :=
      relatedRayPathInterlacementClass_finite_of_initial
        p.path p.map_not_isIso
    obtain ⟨q, hpq, hpqNot⟩ :=
      exists_related_not_interlaced_of_ray_card_eq_two
        p.path p.length_ne_zero hpp hcard
    have hqLength : q.length ≠ 0 :=
      rayPath_length_ne_zero_of_related_of_not_isIso p.map_not_isIso hpq
    have hpqEssential : IsEssentialPathContour R PI p.path q :=
      ⟨hpq, hpqNot⟩
    have hafter : p.occurrence.after.length = 0 :=
      Figure55HookRhoStage.after_length_eq_zero_of_occurrence
        t ht hpqEssential p.occurrence
    obtain ⟨dp, hdpArrow⟩ :=
      p.occurrence.exists_finalDecomposition_of_afterLengthZero hafter
    let dq := chosenPathFinalDecomposition q hqLength
    have hgammaBeta : bundledQuiverArrow dp.arrow ≠
        bundledQuiverArrow dq.arrow := by
      intro h
      apply hpqNot
      apply rayPaths_interlaced_of_finalDecomposition_code_eq dp dq hpq
      exact bundledQuiverArrow_injective_on_incoming h
    have hsuffix : EssentialContourArrowSuffixTrivial
        (rayPathContourRelation (C := C))
        (properWhiskerInterlacementRelation
          (rayPathContourRelation (C := C)))
        (bundledQuiverArrow t.lastArrow) :=
      Figure55HookRhoStage.essentialContourArrowSuffixTrivial_of_isEfficientAt
        t ht
    have hgammaSuffix : EssentialContourArrowSuffixTrivial R PI
        (bundledQuiverArrow dp.arrow) := by
      rw [hdpArrow]
      exact hsuffix
    obtain ⟨a, z, r, s, dr, ds, hrs, hrSurvives, hrsNot,
        hdrArrow, hdsArrow⟩ :=
      J.exists_survivingEssentialContour_finalDecompositions_of_not_absent
        (bundledQuiverArrow t.lastArrow) hsuffix habsent
    have hz : z = p.target := by
      exact congrArg
        (fun e : BundledQuiverArrow (RayVertex C) => e.2.1)
        (hdrArrow.trans hdpArrow.symm)
    subst z
    have hrsEssential : IsEssentialPathContour R PI r s :=
      ⟨hrs, hrsNot⟩
    have hshared :
        (⟨dp.middle, dp.arrow⟩ : IncomingQuiverArrow p.target) =
          ⟨dr.middle, dr.arrow⟩ := by
      apply bundledQuiverArrow_injective_on_incoming
      exact hdpArrow.trans hdrArrow.symm
    have hfigure :=
      isRayThreeArrowFigure_of_essential_finalContours_principal_survivor
        hpqEssential hrsEssential hrSurvives dp dq dr ds hshared
    let hSource : p.target.obj = t.x (Fin.last m) :=
      congrArg
        (fun e : BundledQuiverArrow (RayVertex C) => e.2.1.obj)
        hdpArrow
    let hGammaTarget : dp.middle.obj = t.z (Fin.last m) :=
      congrArg
        (fun e : BundledQuiverArrow (RayVertex C) => e.1.obj)
        hdpArrow
    let beta : NonzeroHom (t.x (Fin.last m)) dq.middle.obj :=
      NonzeroHom.cast hSource rfl dq.rayArrowNonzeroHom
    let gamma : NonzeroHom (t.x (Fin.last m)) (t.z (Fin.last m)) :=
      NonzeroHom.cast hSource hGammaTarget dp.rayArrowNonzeroHom
    let delta : NonzeroHom (t.x (Fin.last m)) ds.middle.obj :=
      NonzeroHom.cast hSource rfl ds.rayArrowNonzeroHom
    have hgamma : gamma = t.rho (Fin.last m) := by
      apply Subtype.ext
      have h := congrArg Subtype.val
        (rayArrowNonzeroHom_cast_eq_of_bundledQuiverArrow_eq
          dp.arrow t.lastArrow hdpArrow)
      simpa [gamma, hSource, hGammaTarget, bundledQuiverArrow,
        RayHookTackle.lastArrow, rayArrowMorphism,
        PathFinalDecomposition.rayArrowNonzeroHom] using h
    have hfigure' : IsRayThreeArrowFigure
        beta.toMorphismFrom
        (t.rho (Fin.last m)).toMorphismFrom
        delta.toMorphismFrom := by
      rw [← hgamma]
      exact isRayThreeArrowFigure_cast hSource rfl hGammaTarget rfl
        dq.rayArrowNonzeroHom dp.rayArrowNonzeroHom
          ds.rayArrowNonzeroHom hfigure
    have hbeta : IsIrreducibleRayMorphism beta.1 := by
      exact isIrreducibleMorphism_cast hSource rfl
        dq.rayArrowNonzeroHom dq.arrow.property
    have hdelta : IsIrreducibleRayMorphism delta.1 := by
      exact isIrreducibleMorphism_cast hSource rfl
        ds.rayArrowNonzeroHom ds.arrow.property
    let betaCode : IncomingQuiverArrow p.target :=
      ⟨dq.middle, dq.arrow⟩
    let gammaCode : IncomingQuiverArrow p.target :=
      ⟨dp.middle, dp.arrow⟩
    let deltaCode : IncomingQuiverArrow p.target :=
      ⟨ds.middle, ds.arrow⟩
    have hbetaGammaCode : betaCode ≠ gammaCode := by
      intro h
      exact hgammaBeta (congrArg
        (fun c : IncomingQuiverArrow p.target =>
          bundledQuiverArrow c.2) h.symm)
    have hbetaDeltaCode : betaCode ≠ deltaCode :=
      otherFinalArrow_ne_of_principal_survivor hpqEssential hrsEssential
        hrSurvives dp dq dr ds hshared
    have hgammaDeltaCode : gammaCode ≠ deltaCode := by
      intro h
      apply hrsNot
      apply rayPaths_interlaced_of_finalDecomposition_code_eq dr ds hrs
      exact hshared.symm.trans h
    have hgammaDelta : bundledQuiverArrow dp.arrow ≠
        bundledQuiverArrow ds.arrow := by
      intro h
      exact hgammaDeltaCode
        (bundledQuiverArrow_injective_on_incoming h)
    have hbetaDelta : bundledQuiverArrow dq.arrow ≠
        bundledQuiverArrow ds.arrow := by
      intro h
      exact hbetaDeltaCode
        (bundledQuiverArrow_injective_on_incoming h)
    letI : Finite (IncomingQuiverArrow p.target) :=
      incomingQuiverArrow_finite p.target
    have hcover : ∀ e : IncomingQuiverArrow p.target,
        e = betaCode ∨ e = gammaCode ∨ e = deltaCode := fun e =>
      eq_first_or_eq_second_or_eq_third_of_natCard_le_three
        hincomingCard hbetaGammaCode hbetaDeltaCode hgammaDeltaCode
    have hpairBalance :
        J.FinalArrowPairBalanceOnSurvivingEssentialContours
          (bundledQuiverArrow dp.arrow)
          (bundledQuiverArrow ds.arrow) := by
      dsimp [J]
      exact
        ZeroHomIdeal.finalArrowPairBalance_principal_of_sharedSurvivingContour
          hpqEssential hrsEssential hrSurvives dp dq dr ds hshared
            hincomingCard
    apply
      ZeroHomIdeal.hasInvisibleCorrectionClingingOnIdeal_principal_of_maximal
        p hp
    rcases t.exists_efficient_replacement_of_figure
        ht beta delta hbeta hdelta hfigure' with
      ⟨hbetaCompatible, hbetaEfficient⟩ |
        ⟨hdeltaCompatible, hdeltaEfficient⟩
    · have hbetaReplaceArrow : bundledQuiverArrow
          (t.replaceLast beta hbeta hbetaCompatible).lastArrow =
          bundledQuiverArrow dq.arrow := by
        exact bundledQuiverArrow_replaceLast_lastArrow_eq_of_cast
          t dq.arrow hSource hbeta hbetaCompatible
      have hbetaSuffix : EssentialContourArrowSuffixTrivial R PI
          (bundledQuiverArrow dq.arrow) := by
        rw [← hbetaReplaceArrow]
        exact
          Figure55HookRhoStage.essentialContourArrowSuffixTrivial_of_isEfficientAt
            (t.replaceLast beta hbeta hbetaCompatible) hbetaEfficient
      have hbetaAbsent :
          J.BundledArrowAbsentFromSurvivingEssentialContours
            (bundledQuiverArrow dq.arrow) := by
        apply J.bundledArrowAbsent_of_finalArrowPairBalance_of_cover
          betaCode gammaCode deltaCode hbetaGammaCode hbetaDeltaCode
            hcover hbetaSuffix
        exact hpairBalance
      exact
        J.hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass_finalArrow_of_absent_zero_one
          p.path q hpp hpq hpqNot hcard dp dq hgammaBeta.symm
            hbetaSuffix hbetaAbsent
    · have hdeltaReplaceArrow : bundledQuiverArrow
          (t.replaceLast delta hdelta hdeltaCompatible).lastArrow =
          bundledQuiverArrow ds.arrow := by
        exact bundledQuiverArrow_replaceLast_lastArrow_eq_of_cast
          t ds.arrow hSource hdelta hdeltaCompatible
      have hdeltaSuffix : EssentialContourArrowSuffixTrivial R PI
          (bundledQuiverArrow ds.arrow) := by
        rw [← hdeltaReplaceArrow]
        exact
          Figure55HookRhoStage.essentialContourArrowSuffixTrivial_of_isEfficientAt
            (t.replaceLast delta hdelta hdeltaCompatible) hdeltaEfficient
      apply
        J.hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass_finalArrow_of_pairBalanced
          p.path q hpp hpq hpqNot hcard dp dq deltaCode
            hgammaBeta.symm hgammaDelta hbetaDelta hgammaSuffix
              hdeltaSuffix
      exact hpairBalance

/-- The complete Figure-59 `N = 3` correction for an efficient hook. -/
theorem hasInvisibleCorrectionClingingOnIdeal_principal_of_card_eq_three
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [HasRayLongPathEndpointValencyAtMostThree C] [IsRayCrownFree C]
    {m : ℕ} (t : RayHookTackle (C := C) m) {y : C}
    (ht : (RayTackle.hook m t).IsEfficientAt y)
    (p : NonzeroRayPathThroughArrow
      (C := C) (bundledQuiverArrow t.lastArrow))
    (hp : p.IsMaximal)
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p.path) = 3) :
    ZeroHomIdeal.HasInvisibleCorrectionClingingOnIdeal (k := k)
      (principalZeroHomIdeal (rayPathMap p.path)) := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  let J := principalZeroHomIdeal (rayPathMap p.path)
  have hpp : R.related p.path p.path := ⟨p.map_ne_zero, rfl⟩
  have hpLengthTwo : 2 ≤ p.path.length := by
    have hpNotOne : p.path.length ≠ 1 := by
      intro hpOne
      have hOne :=
        relatedRayPathInterlacementClass_card_eq_one_of_length_eq_one
          p.path hpOne hpp
      have hOne' : Nat.card (RelatedPathInterlacementClass
          (properWhiskerInterlacementRelation
            (rayPathContourRelation (C := C))) p.path) = 1 := by
        simpa [R] using hOne
      have : (3 : ℕ) = 1 := hcard.symm.trans hOne'
      simp at this
    have hpNotZero : p.path.length ≠ 0 := p.length_ne_zero
    omega
  have hincomingCard : Nat.card (IncomingQuiverArrow p.target) ≤ 3 :=
    HasRayLongPathEndpointValencyAtMostThree.incoming_card_le
      p.path p.map_ne_zero hpLengthTwo
  letI : Finite (OutgoingQuiverArrow p.source) :=
    outgoingQuiverArrow_finite p.source
  letI : Finite (RelatedPathInterlacementClass PI p.path) :=
    relatedRayPathInterlacementClass_finite_of_initial
      p.path p.map_not_isIso
  obtain ⟨q, r, hpq, hpr, hpqNot, hprNot, hqrNot⟩ :=
    exists_two_pairwise_noninterlaced_related_of_ray_card_eq_three
      p.path p.length_ne_zero hpp hcard
  have hqr : R.related q r := R.trans (R.symm hpq) hpr
  have hqLength : q.length ≠ 0 :=
    rayPath_length_ne_zero_of_related_of_not_isIso p.map_not_isIso hpq
  have hrLength : r.length ≠ 0 :=
    rayPath_length_ne_zero_of_related_of_not_isIso p.map_not_isIso hpr
  have hpqEssential : IsEssentialPathContour R PI p.path q :=
    ⟨hpq, hpqNot⟩
  have hprEssential : IsEssentialPathContour R PI p.path r :=
    ⟨hpr, hprNot⟩
  have hqrEssential : IsEssentialPathContour R PI q r :=
    ⟨hqr, hqrNot⟩
  have hafter : p.occurrence.after.length = 0 :=
    Figure55HookRhoStage.after_length_eq_zero_of_occurrence
      t ht hpqEssential p.occurrence
  obtain ⟨dp, hdpArrow⟩ :=
    p.occurrence.exists_finalDecomposition_of_afterLengthZero hafter
  let dq := chosenPathFinalDecomposition q hqLength
  let dr := chosenPathFinalDecomposition r hrLength
  have hgammaBeta : bundledQuiverArrow dp.arrow ≠
      bundledQuiverArrow dq.arrow := by
    intro h
    apply hpqNot
    apply rayPaths_interlaced_of_finalDecomposition_code_eq dp dq hpq
    exact bundledQuiverArrow_injective_on_incoming h
  have hgammaDelta : bundledQuiverArrow dp.arrow ≠
      bundledQuiverArrow dr.arrow := by
    intro h
    apply hprNot
    apply rayPaths_interlaced_of_finalDecomposition_code_eq dp dr hpr
    exact bundledQuiverArrow_injective_on_incoming h
  have hbetaDelta : bundledQuiverArrow dq.arrow ≠
      bundledQuiverArrow dr.arrow := by
    intro h
    apply hqrNot
    apply rayPaths_interlaced_of_finalDecomposition_code_eq dq dr hqr
    exact bundledQuiverArrow_injective_on_incoming h
  have hgammaSuffix : EssentialContourArrowSuffixTrivial R PI
      (bundledQuiverArrow dp.arrow) := by
    rw [hdpArrow]
    exact Figure55HookRhoStage.essentialContourArrowSuffixTrivial_of_isEfficientAt
      t ht
  have hqrSup :=
    isRayPairSupremum_rayPathMorphism_of_essential_finalDecompositions
      dq dr hqr hqrNot
  have hfigure : IsRayThreeArrowFigure
      dq.rayArrowNonzeroHom.toMorphismFrom
      dp.rayArrowNonzeroHom.toMorphismFrom
      dr.rayArrowNonzeroHom.toMorphismFrom := by
    refine Or.inl ⟨rayPathMorphism q hqr.1, hqrSup, ?_⟩
    rw [← rayPathMorphism_eq_of_related p.path q hpq]
    exact dp.rayArrow_le_rayPathMorphism p.map_ne_zero
  let hSource : p.target.obj = t.x (Fin.last m) :=
    congrArg
      (fun e : BundledQuiverArrow (RayVertex C) => e.2.1.obj)
      hdpArrow
  let hGammaTarget : dp.middle.obj = t.z (Fin.last m) :=
    congrArg
      (fun e : BundledQuiverArrow (RayVertex C) => e.1.obj)
      hdpArrow
  let beta : NonzeroHom (t.x (Fin.last m)) dq.middle.obj :=
    NonzeroHom.cast hSource rfl dq.rayArrowNonzeroHom
  let gamma : NonzeroHom (t.x (Fin.last m)) (t.z (Fin.last m)) :=
    NonzeroHom.cast hSource hGammaTarget dp.rayArrowNonzeroHom
  let delta : NonzeroHom (t.x (Fin.last m)) dr.middle.obj :=
    NonzeroHom.cast hSource rfl dr.rayArrowNonzeroHom
  have hgamma : gamma = t.rho (Fin.last m) := by
    apply Subtype.ext
    have h := congrArg Subtype.val
      (rayArrowNonzeroHom_cast_eq_of_bundledQuiverArrow_eq
        dp.arrow t.lastArrow hdpArrow)
    simpa [gamma, hSource, hGammaTarget, bundledQuiverArrow,
      RayHookTackle.lastArrow, rayArrowMorphism,
      PathFinalDecomposition.rayArrowNonzeroHom] using h
  have hfigure' : IsRayThreeArrowFigure
      beta.toMorphismFrom
      (t.rho (Fin.last m)).toMorphismFrom
      delta.toMorphismFrom := by
    rw [← hgamma]
    exact isRayThreeArrowFigure_cast hSource rfl hGammaTarget rfl
      dq.rayArrowNonzeroHom dp.rayArrowNonzeroHom
        dr.rayArrowNonzeroHom hfigure
  have hbeta : IsIrreducibleRayMorphism beta.1 := by
    exact isIrreducibleMorphism_cast hSource rfl
      dq.rayArrowNonzeroHom dq.arrow.property
  have hdelta : IsIrreducibleRayMorphism delta.1 := by
    exact isIrreducibleMorphism_cast hSource rfl
      dr.rayArrowNonzeroHom dr.arrow.property
  have hgammaAbsent : J.BundledArrowAbsentFromSurvivingEssentialContours
      (bundledQuiverArrow dp.arrow) := by
    dsimp [J]
    exact ZeroHomIdeal.bundledArrowAbsent_principal_of_three_essential_finalContours
      hpqEssential hprEssential hqrEssential dp dq dr hincomingCard
        hgammaSuffix
  apply
    ZeroHomIdeal.hasInvisibleCorrectionClingingOnIdeal_principal_of_maximal
      p hp
  rcases t.exists_efficient_replacement_of_figure
      ht beta delta hbeta hdelta hfigure' with
    ⟨hbetaCompatible, hbetaEfficient⟩ |
      ⟨hdeltaCompatible, hdeltaEfficient⟩
  · have hbetaReplaceArrow : bundledQuiverArrow
        (t.replaceLast beta hbeta hbetaCompatible).lastArrow =
        bundledQuiverArrow dq.arrow := by
      exact bundledQuiverArrow_replaceLast_lastArrow_eq_of_cast
        t dq.arrow hSource hbeta hbetaCompatible
    have hbetaSuffix : EssentialContourArrowSuffixTrivial R PI
        (bundledQuiverArrow dq.arrow) := by
      rw [← hbetaReplaceArrow]
      exact
        Figure55HookRhoStage.essentialContourArrowSuffixTrivial_of_isEfficientAt
          (t.replaceLast beta hbeta hbetaCompatible) hbetaEfficient
    have hbetaAbsent : J.BundledArrowAbsentFromSurvivingEssentialContours
        (bundledQuiverArrow dq.arrow) := by
      have h : ZeroHomIdeal.BundledArrowAbsentFromSurvivingEssentialContours
          (principalZeroHomIdeal (rayPathMap q))
          (bundledQuiverArrow dq.arrow) :=
        ZeroHomIdeal.bundledArrowAbsent_principal_of_three_essential_finalContours
          hpqEssential.symm hqrEssential hprEssential dq dp dr
            hincomingCard hbetaSuffix
      have hmap : rayPathMap q = rayPathMap p.path := hpq.2.symm
      intro a b u v huv huNot huvNot
      apply h u v huv
      · simpa [J, hmap] using huNot
      · exact huvNot
    exact J.hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterThreeClass_finalArrow_of_balanced
      p.path q r hpqEssential hqrEssential hprEssential hcard
        dp dq dr hgammaBeta hgammaDelta hbetaDelta hbetaSuffix
          hgammaSuffix
          (J.arrowSelectorBalancedOnSurvivingEssentialContours_single_of_absent
            (bundledQuiverArrow dq.arrow) hbetaAbsent)
          (J.arrowSelectorBalancedOnSurvivingEssentialContours_single_of_absent
            (bundledQuiverArrow dp.arrow) hgammaAbsent)
  · have hdeltaReplaceArrow : bundledQuiverArrow
        (t.replaceLast delta hdelta hdeltaCompatible).lastArrow =
        bundledQuiverArrow dr.arrow := by
      exact bundledQuiverArrow_replaceLast_lastArrow_eq_of_cast
        t dr.arrow hSource hdelta hdeltaCompatible
    have hdeltaSuffix : EssentialContourArrowSuffixTrivial R PI
        (bundledQuiverArrow dr.arrow) := by
      rw [← hdeltaReplaceArrow]
      exact
        Figure55HookRhoStage.essentialContourArrowSuffixTrivial_of_isEfficientAt
          (t.replaceLast delta hdelta hdeltaCompatible) hdeltaEfficient
    have hdeltaAbsent : J.BundledArrowAbsentFromSurvivingEssentialContours
        (bundledQuiverArrow dr.arrow) := by
      have h : ZeroHomIdeal.BundledArrowAbsentFromSurvivingEssentialContours
          (principalZeroHomIdeal (rayPathMap r))
          (bundledQuiverArrow dr.arrow) :=
        ZeroHomIdeal.bundledArrowAbsent_principal_of_three_essential_finalContours
          hprEssential.symm hqrEssential.symm hpqEssential dr dp dq
            hincomingCard hdeltaSuffix
      have hmap : rayPathMap r = rayPathMap p.path := hpr.2.symm
      intro a b u v huv huNot huvNot
      apply h u v huv
      · simpa [J, hmap] using huNot
      · exact huvNot
    exact J.hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterThreeClass_finalArrow_of_balanced
      p.path r q hprEssential hqrEssential.symm hpqEssential hcard
        dp dr dq hgammaDelta hgammaBeta hbetaDelta.symm hdeltaSuffix
          hgammaSuffix
          (J.arrowSelectorBalancedOnSurvivingEssentialContours_single_of_absent
            (bundledQuiverArrow dr.arrow) hdeltaAbsent)
          (J.arrowSelectorBalancedOnSurvivingEssentialContours_single_of_absent
            (bundledQuiverArrow dp.arrow) hgammaAbsent)

end RayHookTackle

namespace RayCohookTackle

private theorem cohook_replaceLast_x_last
    {m : ℕ} (t : RayCohookTackle (C := C) m)
    {X : C} (f : NonzeroHom X (t.z (Fin.last m)))
    (hf : IsIrreducibleRayMorphism f.1)
    (hcomp : t.LastReplacementCompatible f) :
    (t.replaceLast f hf hcomp).x (Fin.last m).succ = X := by
  simp [RayCohookTackle.replaceLast]

private theorem cohook_replaceLast_sigma_last_cast
    {m : ℕ} (t : RayCohookTackle (C := C) m)
    {X : C} (f : NonzeroHom X (t.z (Fin.last m)))
    (hf : IsIrreducibleRayMorphism f.1)
    (hcomp : t.LastReplacementCompatible f) :
    NonzeroHom.cast (cohook_replaceLast_x_last t f hf hcomp) rfl
      ((t.replaceLast f hf hcomp).sigma (Fin.last m)) = f := by
  simp [RayCohookTackle.replaceLast]
  rw [nonzeroHom_cast_comp]
  apply nonzeroHom_cast_self

/-- The last arrow of a replaced cohook tackle is the bundled reversed arrow
of the replacement morphism. -/
theorem bundledQuiverArrow_replaceLast_lastArrow_eq
    {m : ℕ} (t : RayCohookTackle (C := C) m)
    {X : C} (f : NonzeroHom X (t.z (Fin.last m)))
    (hf : IsIrreducibleRayMorphism f.1)
    (hcomp : t.LastReplacementCompatible f) :
    bundledQuiverArrow (t.replaceLast f hf hcomp).lastArrow =
      bundledQuiverArrow
        (⟨f.1, hf⟩ :
          (RayVertex.mk (t.z (Fin.last m)) : RayVertex C) ⟶
            RayVertex.mk X) := by
  let t' := t.replaceLast f hf hcomp
  let a : (RayVertex.mk (t.z (Fin.last m)) : RayVertex C) ⟶
      RayVertex.mk X := ⟨f.1, hf⟩
  have hi : RayVertex.mk (t'.z (Fin.last m)) =
      RayVertex.mk (t.z (Fin.last m)) := RayVertex.ext rfl
  have hj : RayVertex.mk (t'.x (Fin.last m).succ) =
      RayVertex.mk X :=
    RayVertex.ext (cohook_replaceLast_x_last t f hf hcomp)
  apply bundledQuiverArrow_eq_of_quiverArrowCast_eq hi hj t'.lastArrow a
  apply quiverArrowCast_eq_of_rayNonzeroHom_cast_eq hi hj
  exact cohook_replaceLast_sigma_last_cast t f hf hcomp

private theorem bundledQuiverArrow_cohookCastBack
    {m : ℕ} (t : RayCohookTackle (C := C) m)
    {i j : RayVertex C} (a : i ⟶ j)
    (hz : i.obj = t.z (Fin.last m)) :
    bundledQuiverArrow
      (⟨(NonzeroHom.cast rfl hz
        (⟨rayArrowMorphism a, a.property.1⟩ : NonzeroHom j.obj i.obj)).1,
          isIrreducibleMorphism_cast rfl hz
            (⟨rayArrowMorphism a, a.property.1⟩ : NonzeroHom j.obj i.obj)
            a.property⟩ :
        (RayVertex.mk (t.z (Fin.last m)) : RayVertex C) ⟶
          RayVertex.mk j.obj) = bundledQuiverArrow a := by
  let f := NonzeroHom.cast rfl hz
    (⟨rayArrowMorphism a, a.property.1⟩ : NonzeroHom j.obj i.obj)
  let ac : (RayVertex.mk (t.z (Fin.last m)) : RayVertex C) ⟶
      RayVertex.mk j.obj :=
    ⟨f.1, isIrreducibleMorphism_cast rfl hz
      (⟨rayArrowMorphism a, a.property.1⟩ : NonzeroHom j.obj i.obj)
      a.property⟩
  have hi : (RayVertex.mk (t.z (Fin.last m)) : RayVertex C) = i :=
    RayVertex.ext hz.symm
  have hj : (RayVertex.mk j.obj : RayVertex C) = j := RayVertex.ext rfl
  change bundledQuiverArrow ac = bundledQuiverArrow a
  apply bundledQuiverArrow_eq_of_quiverArrowCast_eq hi hj ac a
  apply quiverArrowCast_eq_of_rayNonzeroHom_cast_eq hi hj
  change NonzeroHom.cast (congrArg RayVertex.obj hj)
      (congrArg RayVertex.obj hi) f =
    (⟨rayArrowMorphism a, a.property.1⟩ : NonzeroHom j.obj i.obj)
  dsimp only [f]
  rw [nonzeroHom_cast_comp]
  apply nonzeroHom_cast_self

/-- Fixed-target cast-back form of the replacement-arrow transport. -/
theorem bundledQuiverArrow_replaceLast_lastArrow_eq_of_cast
    {m : ℕ} (t : RayCohookTackle (C := C) m)
    {i j : RayVertex C} (a : i ⟶ j)
    (hz : i.obj = t.z (Fin.last m))
    (hf : IsIrreducibleRayMorphism
      (NonzeroHom.cast rfl hz
        (⟨rayArrowMorphism a, a.property.1⟩ :
          NonzeroHom j.obj i.obj)).1)
    (hcomp : t.LastReplacementCompatible
      (NonzeroHom.cast rfl hz
        (⟨rayArrowMorphism a, a.property.1⟩ : NonzeroHom j.obj i.obj))) :
    bundledQuiverArrow
      (t.replaceLast (NonzeroHom.cast rfl hz
        (⟨rayArrowMorphism a, a.property.1⟩ : NonzeroHom j.obj i.obj))
        hf hcomp).lastArrow = bundledQuiverArrow a := by
  calc
    _ = bundledQuiverArrow
        (⟨(NonzeroHom.cast rfl hz
          (⟨rayArrowMorphism a, a.property.1⟩ :
            NonzeroHom j.obj i.obj)).1,
            hf⟩ :
          (RayVertex.mk (t.z (Fin.last m)) : RayVertex C) ⟶
            RayVertex.mk j.obj) :=
      t.bundledQuiverArrow_replaceLast_lastArrow_eq _ hf hcomp
    _ = bundledQuiverArrow a := by
      have hcanonical : hf = isIrreducibleMorphism_cast rfl hz
          (⟨rayArrowMorphism a, a.property.1⟩ :
            NonzeroHom j.obj i.obj) a.property :=
        Subsingleton.elim _ _
      subst hcanonical
      exact bundledQuiverArrow_cohookCastBack t a hz

/-- Orientation-dual easy `N = 2` branch for an efficient cohook. -/
theorem hasInvisibleCorrectionClingingOnIdeal_principal_of_card_eq_two_of_lastArrowAbsent
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    {m : ℕ} (t : RayCohookTackle (C := C) m) {y : C}
    (ht : (RayTackle.cohook m t).IsEfficientAt y)
    (p : NonzeroRayPathThroughArrow
      (C := C) (bundledQuiverArrow t.lastArrow))
    (hp : p.IsMaximal)
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p.path) = 2)
    (habsent : ZeroHomIdeal.BundledArrowAbsentFromSurvivingEssentialContours
      (principalZeroHomIdeal (rayPathMap p.path))
      (bundledQuiverArrow t.lastArrow)) :
    ZeroHomIdeal.HasInvisibleCorrectionClingingOnIdeal (k := k)
      (principalZeroHomIdeal (rayPathMap p.path)) := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  have hpp : R.related p.path p.path := ⟨p.map_ne_zero, rfl⟩
  letI : Finite (OutgoingQuiverArrow p.source) :=
    outgoingQuiverArrow_finite p.source
  letI : Finite (RelatedPathInterlacementClass PI p.path) :=
    relatedRayPathInterlacementClass_finite_of_initial
      p.path p.map_not_isIso
  obtain ⟨q, hpq, hpqNot⟩ :=
    exists_related_not_interlaced_of_ray_card_eq_two
      p.path p.length_ne_zero hpp hcard
  have hqLength : q.length ≠ 0 :=
    rayPath_length_ne_zero_of_related_of_not_isIso
      p.map_not_isIso hpq
  have hessential : IsEssentialPathContour R PI p.path q :=
    ⟨hpq, hpqNot⟩
  have hbefore : p.occurrence.before.length = 0 :=
    Figure55CohookRhoStage.before_length_eq_zero_of_occurrence
      t ht hessential p.occurrence
  obtain ⟨dp, hdpArrow⟩ :=
    p.occurrence.exists_initialDecomposition_of_beforeLengthZero hbefore
  let dq := chosenPathInitialDecomposition q hqLength
  have harrow : bundledQuiverArrow dq.arrow ≠
      bundledQuiverArrow dp.arrow := by
    intro harrow
    apply hpqNot
    apply rayPaths_interlaced_of_initialDecomposition_code_eq dp dq hpq
    exact (bundledQuiverArrow_injective_on_outgoing harrow).symm
  apply ZeroHomIdeal.hasInvisibleCorrectionClingingOnIdeal_principal_of_maximal
    p hp
  apply ZeroHomIdeal.hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass_initialArrow_of_absent
    (principalZeroHomIdeal (rayPathMap p.path))
    p.path q hpp hpq hpqNot hcard dp dq harrow
  · rw [hdpArrow]
    exact Figure55CohookRhoStage.essentialContourArrowPrefixTrivial_of_isEfficientAt
      t ht
  · rw [hdpArrow]
    exact habsent

/-- The complete hard N = 2 cohook branch. -/
theorem hasInvisibleCorrectionClingingOnIdeal_principal_of_card_eq_two
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [HasRayLongPathEndpointValencyAtMostThree C] [IsRayCocrownFree C]
    {m : ℕ} (t : RayCohookTackle (C := C) m) {y : C}
    (ht : (RayTackle.cohook m t).IsEfficientAt y)
    (p : NonzeroRayPathThroughArrow
      (C := C) (bundledQuiverArrow t.lastArrow))
    (hp : p.IsMaximal)
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p.path) = 2) :
    ZeroHomIdeal.HasInvisibleCorrectionClingingOnIdeal (k := k)
      (principalZeroHomIdeal (rayPathMap p.path)) := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  let J := principalZeroHomIdeal (rayPathMap p.path)
  by_cases habsent : J.BundledArrowAbsentFromSurvivingEssentialContours
      (bundledQuiverArrow t.lastArrow)
  · exact
      t.hasInvisibleCorrectionClingingOnIdeal_principal_of_card_eq_two_of_lastArrowAbsent
        ht p hp hcard habsent
  · have hpp : R.related p.path p.path := ⟨p.map_ne_zero, rfl⟩
    have hpLengthTwo : 2 ≤ p.path.length := by
      have hpNotOne : p.path.length ≠ 1 := by
        intro hpOne
        have hOne :=
          relatedRayPathInterlacementClass_card_eq_one_of_length_eq_one
            p.path hpOne hpp
        have hOne' : Nat.card (RelatedPathInterlacementClass
            (properWhiskerInterlacementRelation
              (rayPathContourRelation (C := C))) p.path) = 1 := by
          simpa [R] using hOne
        have : (2 : ℕ) = 1 := hcard.symm.trans hOne'
        simp at this
      have hpNotZero : p.path.length ≠ 0 := p.length_ne_zero
      omega
    have houtgoingCard :
        Nat.card (OutgoingQuiverArrow p.source) ≤ 3 :=
      HasRayLongPathEndpointValencyAtMostThree.outgoing_card_le
        p.path p.map_ne_zero hpLengthTwo
    letI : Finite (OutgoingQuiverArrow p.source) :=
      outgoingQuiverArrow_finite p.source
    letI : Finite (RelatedPathInterlacementClass PI p.path) :=
      relatedRayPathInterlacementClass_finite_of_initial
        p.path p.map_not_isIso
    obtain ⟨q, hpq, hpqNot⟩ :=
      exists_related_not_interlaced_of_ray_card_eq_two
        p.path p.length_ne_zero hpp hcard
    have hqLength : q.length ≠ 0 :=
      rayPath_length_ne_zero_of_related_of_not_isIso p.map_not_isIso hpq
    have hpqEssential : IsEssentialPathContour R PI p.path q :=
      ⟨hpq, hpqNot⟩
    have hbefore : p.occurrence.before.length = 0 :=
      Figure55CohookRhoStage.before_length_eq_zero_of_occurrence
        t ht hpqEssential p.occurrence
    obtain ⟨dp, hdpArrow⟩ :=
      p.occurrence.exists_initialDecomposition_of_beforeLengthZero hbefore
    let dq := chosenPathInitialDecomposition q hqLength
    have hbetaGamma : bundledQuiverArrow dq.arrow ≠
        bundledQuiverArrow dp.arrow := by
      intro h
      apply hpqNot
      apply rayPaths_interlaced_of_initialDecomposition_code_eq dp dq hpq
      exact (bundledQuiverArrow_injective_on_outgoing h).symm
    have hprefix : EssentialContourArrowPrefixTrivial
        (rayPathContourRelation (C := C))
        (properWhiskerInterlacementRelation
          (rayPathContourRelation (C := C)))
        (bundledQuiverArrow t.lastArrow) :=
      Figure55CohookRhoStage.essentialContourArrowPrefixTrivial_of_isEfficientAt
        t ht
    have hgammaPrefix : EssentialContourArrowPrefixTrivial R PI
        (bundledQuiverArrow dp.arrow) := by
      rw [hdpArrow]
      exact hprefix
    obtain ⟨x', z, r, s, dr, ds, hrs, hrSurvives, hrsNot,
        hdrArrow, hdsArrow⟩ :=
      J.exists_survivingEssentialContour_initialDecompositions_of_not_absent
        (bundledQuiverArrow t.lastArrow) hprefix habsent
    have hx : x' = p.source := by
      exact congrArg
        (fun e : BundledQuiverArrow (RayVertex C) => e.1)
        (hdrArrow.trans hdpArrow.symm)
    subst x'
    have hrsEssential : IsEssentialPathContour R PI r s :=
      ⟨hrs, hrsNot⟩
    have hshared :
        (⟨dp.middle, dp.arrow⟩ : OutgoingQuiverArrow p.source) =
          ⟨dr.middle, dr.arrow⟩ := by
      apply bundledQuiverArrow_injective_on_outgoing
      exact hdpArrow.trans hdrArrow.symm
    have hfigure :=
      isRayCoThreeArrowFigure_of_essential_initialContours_principal_survivor
        hpqEssential hrsEssential hrSurvives dp dq dr ds hshared
    let hTarget : p.source.obj = t.z (Fin.last m) :=
      congrArg
        (fun e : BundledQuiverArrow (RayVertex C) => e.1.obj)
        hdpArrow
    let hGammaSource : dp.middle.obj = t.x (Fin.last m).succ :=
      congrArg
        (fun e : BundledQuiverArrow (RayVertex C) => e.2.1.obj)
        hdpArrow
    let beta : NonzeroHom dq.middle.obj (t.z (Fin.last m)) :=
      NonzeroHom.cast rfl hTarget dq.rayArrowNonzeroHom
    let gamma :
        NonzeroHom (t.x (Fin.last m).succ) (t.z (Fin.last m)) :=
      NonzeroHom.cast hGammaSource hTarget dp.rayArrowNonzeroHom
    let delta : NonzeroHom ds.middle.obj (t.z (Fin.last m)) :=
      NonzeroHom.cast rfl hTarget ds.rayArrowNonzeroHom
    have hgamma : gamma = t.sigma (Fin.last m) := by
      apply Subtype.ext
      have h := congrArg Subtype.val
        (rayArrowNonzeroHom_cast_eq_of_bundledQuiverArrow_eq
          dp.arrow t.lastArrow hdpArrow)
      simpa [gamma, hTarget, hGammaSource, bundledQuiverArrow,
        RayCohookTackle.lastArrow, rayArrowMorphism,
        PathInitialDecomposition.rayArrowNonzeroHom] using h
    have hfigure' : IsRayCoThreeArrowFigure
        beta.toMorphismTo
        (t.sigma (Fin.last m)).toMorphismTo
        delta.toMorphismTo := by
      rw [← hgamma]
      exact isRayCoThreeArrowFigure_cast hTarget rfl hGammaSource rfl
        dq.rayArrowNonzeroHom dp.rayArrowNonzeroHom
          ds.rayArrowNonzeroHom hfigure
    have hbeta : IsIrreducibleRayMorphism beta.1 := by
      exact isIrreducibleMorphism_cast rfl hTarget
        dq.rayArrowNonzeroHom dq.arrow.property
    have hdelta : IsIrreducibleRayMorphism delta.1 := by
      exact isIrreducibleMorphism_cast rfl hTarget
        ds.rayArrowNonzeroHom ds.arrow.property
    let betaCode : OutgoingQuiverArrow p.source :=
      ⟨dq.middle, dq.arrow⟩
    let gammaCode : OutgoingQuiverArrow p.source :=
      ⟨dp.middle, dp.arrow⟩
    let deltaCode : OutgoingQuiverArrow p.source :=
      ⟨ds.middle, ds.arrow⟩
    have hbetaGammaCode : betaCode ≠ gammaCode := by
      intro h
      exact hbetaGamma (congrArg
        (fun c : OutgoingQuiverArrow p.source =>
          bundledQuiverArrow c.2) h)
    have hbetaDeltaCode : betaCode ≠ deltaCode :=
      otherInitialArrow_ne_of_principal_survivor hpqEssential hrsEssential
        hrSurvives dp dq dr ds hshared
    have hgammaDeltaCode : gammaCode ≠ deltaCode := by
      intro h
      apply hrsNot
      apply rayPaths_interlaced_of_initialDecomposition_code_eq dr ds hrs
      exact hshared.symm.trans h
    have hgammaDelta : bundledQuiverArrow dp.arrow ≠
        bundledQuiverArrow ds.arrow := by
      intro h
      exact hgammaDeltaCode
        (bundledQuiverArrow_injective_on_outgoing h)
    have hbetaDelta : bundledQuiverArrow dq.arrow ≠
        bundledQuiverArrow ds.arrow := by
      intro h
      exact hbetaDeltaCode
        (bundledQuiverArrow_injective_on_outgoing h)
    have hcover : ∀ e : OutgoingQuiverArrow p.source,
        e = betaCode ∨ e = gammaCode ∨ e = deltaCode := fun e =>
      eq_first_or_eq_second_or_eq_third_of_natCard_le_three
        houtgoingCard hbetaGammaCode hbetaDeltaCode hgammaDeltaCode
    have hpairBalance :
        J.InitialArrowPairBalanceOnSurvivingEssentialContours
          (bundledQuiverArrow dp.arrow)
          (bundledQuiverArrow ds.arrow) := by
      dsimp [J]
      exact
        ZeroHomIdeal.initialArrowPairBalance_principal_of_sharedSurvivingContour
          hpqEssential hrsEssential hrSurvives dp dq dr ds hshared
            houtgoingCard
    apply
      ZeroHomIdeal.hasInvisibleCorrectionClingingOnIdeal_principal_of_maximal
        p hp
    rcases t.exists_efficient_replacement_of_figure
        ht beta delta hbeta hdelta hfigure' with
      ⟨hbetaCompatible, hbetaEfficient⟩ |
        ⟨hdeltaCompatible, hdeltaEfficient⟩
    · have hbetaReplaceArrow : bundledQuiverArrow
          (t.replaceLast beta hbeta hbetaCompatible).lastArrow =
          bundledQuiverArrow dq.arrow := by
        exact bundledQuiverArrow_replaceLast_lastArrow_eq_of_cast
          t dq.arrow hTarget hbeta hbetaCompatible
      have hbetaPrefix : EssentialContourArrowPrefixTrivial R PI
          (bundledQuiverArrow dq.arrow) := by
        rw [← hbetaReplaceArrow]
        exact
          Figure55CohookRhoStage.essentialContourArrowPrefixTrivial_of_isEfficientAt
            (t.replaceLast beta hbeta hbetaCompatible) hbetaEfficient
      have hbetaAbsent :
          J.BundledArrowAbsentFromSurvivingEssentialContours
            (bundledQuiverArrow dq.arrow) := by
        apply J.bundledArrowAbsent_of_initialArrowPairBalance_of_cover
          betaCode gammaCode deltaCode hbetaGammaCode hbetaDeltaCode
            hcover hbetaPrefix
        exact hpairBalance
      exact
        J.hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass_initialArrow_of_absent_zero_one
          p.path q hpp hpq hpqNot hcard dp dq hbetaGamma
            hbetaPrefix hbetaAbsent
    · have hdeltaReplaceArrow : bundledQuiverArrow
          (t.replaceLast delta hdelta hdeltaCompatible).lastArrow =
          bundledQuiverArrow ds.arrow := by
        exact bundledQuiverArrow_replaceLast_lastArrow_eq_of_cast
          t ds.arrow hTarget hdelta hdeltaCompatible
      have hdeltaPrefix : EssentialContourArrowPrefixTrivial R PI
          (bundledQuiverArrow ds.arrow) := by
        rw [← hdeltaReplaceArrow]
        exact
          Figure55CohookRhoStage.essentialContourArrowPrefixTrivial_of_isEfficientAt
            (t.replaceLast delta hdelta hdeltaCompatible) hdeltaEfficient
      apply
        J.hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterTwoClass_initialArrow_of_pairBalanced
          p.path q hpp hpq hpqNot hcard dp dq deltaCode
            hbetaGamma hgammaDelta hbetaDelta hgammaPrefix hdeltaPrefix
      exact hpairBalance

/-- The complete Figure-59 `N = 3` correction for an efficient cohook. -/
theorem hasInvisibleCorrectionClingingOnIdeal_principal_of_card_eq_three
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [HasRayLongPathEndpointValencyAtMostThree C] [IsRayCocrownFree C]
    {m : ℕ} (t : RayCohookTackle (C := C) m) {y : C}
    (ht : (RayTackle.cohook m t).IsEfficientAt y)
    (p : NonzeroRayPathThroughArrow
      (C := C) (bundledQuiverArrow t.lastArrow))
    (hp : p.IsMaximal)
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p.path) = 3) :
    ZeroHomIdeal.HasInvisibleCorrectionClingingOnIdeal (k := k)
      (principalZeroHomIdeal (rayPathMap p.path)) := by
  let R := rayPathContourRelation (C := C)
  let PI := properWhiskerInterlacementRelation R
  let J := principalZeroHomIdeal (rayPathMap p.path)
  have hpp : R.related p.path p.path := ⟨p.map_ne_zero, rfl⟩
  have hpLengthTwo : 2 ≤ p.path.length := by
    have hpNotOne : p.path.length ≠ 1 := by
      intro hpOne
      have hOne :=
        relatedRayPathInterlacementClass_card_eq_one_of_length_eq_one
          p.path hpOne hpp
      have hOne' : Nat.card (RelatedPathInterlacementClass
          (properWhiskerInterlacementRelation
            (rayPathContourRelation (C := C))) p.path) = 1 := by
        simpa [R] using hOne
      have : (3 : ℕ) = 1 := hcard.symm.trans hOne'
      simp at this
    have hpNotZero : p.path.length ≠ 0 := p.length_ne_zero
    omega
  have houtgoingCard : Nat.card (OutgoingQuiverArrow p.source) ≤ 3 :=
    HasRayLongPathEndpointValencyAtMostThree.outgoing_card_le
      p.path p.map_ne_zero hpLengthTwo
  letI : Finite (OutgoingQuiverArrow p.source) :=
    outgoingQuiverArrow_finite p.source
  letI : Finite (RelatedPathInterlacementClass PI p.path) :=
    relatedRayPathInterlacementClass_finite_of_initial
      p.path p.map_not_isIso
  obtain ⟨q, r, hpq, hpr, hpqNot, hprNot, hqrNot⟩ :=
    exists_two_pairwise_noninterlaced_related_of_ray_card_eq_three
      p.path p.length_ne_zero hpp hcard
  have hqLength : q.length ≠ 0 :=
    rayPath_length_ne_zero_of_related_of_not_isIso p.map_not_isIso hpq
  have hrLength : r.length ≠ 0 :=
    rayPath_length_ne_zero_of_related_of_not_isIso p.map_not_isIso hpr
  have hqr : R.related q r := R.trans (R.symm hpq) hpr
  have hpqEssential : IsEssentialPathContour R PI p.path q :=
    ⟨hpq, hpqNot⟩
  have hprEssential : IsEssentialPathContour R PI p.path r :=
    ⟨hpr, hprNot⟩
  have hqrEssential : IsEssentialPathContour R PI q r :=
    ⟨hqr, hqrNot⟩
  have hbefore : p.occurrence.before.length = 0 :=
    Figure55CohookRhoStage.before_length_eq_zero_of_occurrence
      t ht hpqEssential p.occurrence
  obtain ⟨dp, hdpArrow⟩ :=
    p.occurrence.exists_initialDecomposition_of_beforeLengthZero hbefore
  let dq := chosenPathInitialDecomposition q hqLength
  let dr := chosenPathInitialDecomposition r hrLength
  have hpqArrow : bundledQuiverArrow dp.arrow ≠
      bundledQuiverArrow dq.arrow := by
    intro h
    apply hpqNot
    apply rayPaths_interlaced_of_initialDecomposition_code_eq dp dq hpq
    exact bundledQuiverArrow_injective_on_outgoing h
  have hprArrow : bundledQuiverArrow dp.arrow ≠
      bundledQuiverArrow dr.arrow := by
    intro h
    apply hprNot
    apply rayPaths_interlaced_of_initialDecomposition_code_eq dp dr hpr
    exact bundledQuiverArrow_injective_on_outgoing h
  have hqrArrow : bundledQuiverArrow dq.arrow ≠
      bundledQuiverArrow dr.arrow := by
    intro h
    apply hqrNot
    apply rayPaths_interlaced_of_initialDecomposition_code_eq dq dr hqr
    exact bundledQuiverArrow_injective_on_outgoing h
  have hprefix : EssentialContourArrowPrefixTrivial R PI
      (bundledQuiverArrow t.lastArrow) :=
    Figure55CohookRhoStage.essentialContourArrowPrefixTrivial_of_isEfficientAt
      t ht
  have hgammaPrefix : EssentialContourArrowPrefixTrivial R PI
      (bundledQuiverArrow dp.arrow) := by
    rw [hdpArrow]
    exact hprefix
  have hgammaAbsent :
      J.BundledArrowAbsentFromSurvivingEssentialContours
        (bundledQuiverArrow dp.arrow) := by
    dsimp [J]
    exact ZeroHomIdeal.bundledArrowAbsent_principal_of_three_essential_initialContours
      hpqEssential hprEssential hqrEssential dp dq dr houtgoingCard
        hgammaPrefix
  have hgammaBalanced :
      J.ArrowSelectorBalancedOnSurvivingEssentialContours
        (singleArrowSelector (bundledQuiverArrow dp.arrow)) :=
    J.arrowSelectorBalancedOnSurvivingEssentialContours_single_of_absent
      (bundledQuiverArrow dp.arrow) hgammaAbsent
  have hfigure : IsRayCoThreeArrowFigure
      dq.rayArrowNonzeroHom.toMorphismTo
      dp.rayArrowNonzeroHom.toMorphismTo
      dr.rayArrowNonzeroHom.toMorphismTo := by
    have hqrInf :=
      isRayPairInfimum_rayPathMorphismTo_of_essential_initialDecompositions
        dq dr hqr hqrNot
    have hpqInf :=
      isRayPairInfimum_rayPathMorphismTo_of_essential_initialDecompositions
        dp dq hpq hpqNot
    refine Or.inl ⟨rayPathMorphismTo q hqr.1, hqrInf, ?_⟩
    rw [← rayPathMorphismTo_eq_of_related p.path q hpq]
    exact hpqInf.1
  let hTarget : p.source.obj = t.z (Fin.last m) :=
    congrArg
      (fun e : BundledQuiverArrow (RayVertex C) => e.1.obj)
      hdpArrow
  let hGammaSource : dp.middle.obj = t.x (Fin.last m).succ :=
    congrArg
      (fun e : BundledQuiverArrow (RayVertex C) => e.2.1.obj)
      hdpArrow
  let beta : NonzeroHom dq.middle.obj (t.z (Fin.last m)) :=
    NonzeroHom.cast rfl hTarget dq.rayArrowNonzeroHom
  let gamma : NonzeroHom (t.x (Fin.last m).succ) (t.z (Fin.last m)) :=
    NonzeroHom.cast hGammaSource hTarget dp.rayArrowNonzeroHom
  let delta : NonzeroHom dr.middle.obj (t.z (Fin.last m)) :=
    NonzeroHom.cast rfl hTarget dr.rayArrowNonzeroHom
  have hgamma : gamma = t.sigma (Fin.last m) := by
    apply Subtype.ext
    have h := congrArg Subtype.val
      (rayArrowNonzeroHom_cast_eq_of_bundledQuiverArrow_eq
        dp.arrow t.lastArrow hdpArrow)
    simpa [gamma, hTarget, hGammaSource, bundledQuiverArrow,
      RayCohookTackle.lastArrow, rayArrowMorphism,
      PathInitialDecomposition.rayArrowNonzeroHom] using h
  have hfigure' : IsRayCoThreeArrowFigure
      beta.toMorphismTo
      (t.sigma (Fin.last m)).toMorphismTo
      delta.toMorphismTo := by
    rw [← hgamma]
    exact isRayCoThreeArrowFigure_cast hTarget rfl hGammaSource rfl
      dq.rayArrowNonzeroHom dp.rayArrowNonzeroHom
        dr.rayArrowNonzeroHom hfigure
  have hbeta : IsIrreducibleRayMorphism beta.1 :=
    isIrreducibleMorphism_cast rfl hTarget
      dq.rayArrowNonzeroHom dq.arrow.property
  have hdelta : IsIrreducibleRayMorphism delta.1 :=
    isIrreducibleMorphism_cast rfl hTarget
      dr.rayArrowNonzeroHom dr.arrow.property
  apply ZeroHomIdeal.hasInvisibleCorrectionClingingOnIdeal_principal_of_maximal
    p hp
  rcases t.exists_efficient_replacement_of_figure
      ht beta delta hbeta hdelta hfigure' with
    ⟨hbetaCompatible, hbetaEfficient⟩ |
      ⟨hdeltaCompatible, hdeltaEfficient⟩
  · have hbetaReplaceArrow : bundledQuiverArrow
        (t.replaceLast beta hbeta hbetaCompatible).lastArrow =
        bundledQuiverArrow dq.arrow := by
      exact bundledQuiverArrow_replaceLast_lastArrow_eq_of_cast
        t dq.arrow hTarget hbeta hbetaCompatible
    have hbetaPrefix : EssentialContourArrowPrefixTrivial R PI
        (bundledQuiverArrow dq.arrow) := by
      rw [← hbetaReplaceArrow]
      exact
        Figure55CohookRhoStage.essentialContourArrowPrefixTrivial_of_isEfficientAt
          (t.replaceLast beta hbeta hbetaCompatible) hbetaEfficient
    have hbetaAbsentQ :
        (principalZeroHomIdeal (rayPathMap q)).BundledArrowAbsentFromSurvivingEssentialContours
          (bundledQuiverArrow dq.arrow) := by
      exact ZeroHomIdeal.bundledArrowAbsent_principal_of_three_essential_initialContours
        hpqEssential.symm hqrEssential hprEssential dq dp dr
          houtgoingCard hbetaPrefix
    have hbetaAbsent :
        J.BundledArrowAbsentFromSurvivingEssentialContours
          (bundledQuiverArrow dq.arrow) := by
      dsimp [J]
      rw [hpq.2]
      exact hbetaAbsentQ
    have hbetaBalanced :
        J.ArrowSelectorBalancedOnSurvivingEssentialContours
          (singleArrowSelector (bundledQuiverArrow dq.arrow)) :=
      J.arrowSelectorBalancedOnSurvivingEssentialContours_single_of_absent
        (bundledQuiverArrow dq.arrow) hbetaAbsent
    exact
      J.hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterThreeClass_initialArrow_of_balanced
        p.path q r hpqEssential hqrEssential hprEssential hcard
          dp dq dr hpqArrow hprArrow hqrArrow hbetaPrefix hgammaPrefix
            hbetaBalanced hgammaBalanced
  · have hdeltaReplaceArrow : bundledQuiverArrow
        (t.replaceLast delta hdelta hdeltaCompatible).lastArrow =
        bundledQuiverArrow dr.arrow := by
      exact bundledQuiverArrow_replaceLast_lastArrow_eq_of_cast
        t dr.arrow hTarget hdelta hdeltaCompatible
    have hdeltaPrefix : EssentialContourArrowPrefixTrivial R PI
        (bundledQuiverArrow dr.arrow) := by
      rw [← hdeltaReplaceArrow]
      exact
        Figure55CohookRhoStage.essentialContourArrowPrefixTrivial_of_isEfficientAt
          (t.replaceLast delta hdelta hdeltaCompatible) hdeltaEfficient
    have hdeltaAbsentR :
        (principalZeroHomIdeal (rayPathMap r)).BundledArrowAbsentFromSurvivingEssentialContours
          (bundledQuiverArrow dr.arrow) := by
      exact ZeroHomIdeal.bundledArrowAbsent_principal_of_three_essential_initialContours
        hprEssential.symm hqrEssential.symm hpqEssential dr dp dq
          houtgoingCard hdeltaPrefix
    have hdeltaAbsent :
        J.BundledArrowAbsentFromSurvivingEssentialContours
          (bundledQuiverArrow dr.arrow) := by
      dsimp [J]
      rw [hpr.2]
      exact hdeltaAbsentR
    have hdeltaBalanced :
        J.ArrowSelectorBalancedOnSurvivingEssentialContours
          (singleArrowSelector (bundledQuiverArrow dr.arrow)) :=
      J.arrowSelectorBalancedOnSurvivingEssentialContours_single_of_absent
        (bundledQuiverArrow dr.arrow) hdeltaAbsent
    exact
      J.hasInvisibleCorrectionClingingOnRelatedPaths_of_roiterThreeClass_initialArrow_of_balanced
        p.path r q hprEssential hqrEssential.symm hpqEssential hcard
          dp dr dq hprArrow hpqArrow hqrArrow.symm hdeltaPrefix
            hgammaPrefix hdeltaBalanced hgammaBalanced

end RayCohookTackle

/-- Package the automatic hard `N = 2` branches with a supplied uniform
cardinal-three efficient-tackle correction. -/
theorem hasHardInvisibleCorrectionsOnEfficientMaximalRays_of_card_eq_three
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [HasRayLongPathEndpointValencyAtMostThree C]
    [IsRayCrownFree C] [IsRayCocrownFree C]
    (hThree : ∀ (t : RayTackle C) (y : C), t.IsEfficientAt y →
      ∀ (p : NonzeroRayPathThroughArrow (C := C) t.lastBundledArrow),
        p.IsMaximal →
          Nat.card (RelatedPathInterlacementClass
            (properWhiskerInterlacementRelation
              (rayPathContourRelation (C := C))) p.path) = 3 →
            ZeroHomIdeal.HasInvisibleCorrectionClingingOnIdeal (k := k)
              (principalZeroHomIdeal (rayPathMap p.path))) :
    HasHardInvisibleCorrectionsOnEfficientMaximalRays k C := by
  intro t y ht p hp
  refine ⟨?_, hThree t y ht p hp⟩
  cases t with
  | hook m t =>
      exact t.hasInvisibleCorrectionClingingOnIdeal_principal_of_card_eq_two
        ht p hp
  | cohook m t =>
      exact t.hasInvisibleCorrectionClingingOnIdeal_principal_of_card_eq_two
        ht p hp

/-- The hard local correction obligations are automatic for every efficient
maximal ray under the source-faithful long-path endpoint valency bound. -/
theorem hasHardInvisibleCorrectionsOnEfficientMaximalRays
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [HasRayLongPathEndpointValencyAtMostThree C]
    [IsRayCrownFree C] [IsRayCocrownFree C] :
    HasHardInvisibleCorrectionsOnEfficientMaximalRays k C := by
  apply hasHardInvisibleCorrectionsOnEfficientMaximalRays_of_card_eq_three
  intro t y ht p hp hcard
  cases t with
  | hook m t =>
      exact t.hasInvisibleCorrectionClingingOnIdeal_principal_of_card_eq_three
        ht p hp hcard
  | cohook m t =>
      exact t.hasInvisibleCorrectionClingingOnIdeal_principal_of_card_eq_three
        ht p hp hcard

/-- Exact contour cohomology vanishing for a finite ray category satisfying
the cancellation, chain, and source-faithful long-path valency hypotheses. -/
theorem contourFunctionCohomologyVanishes_of_noInfiniteRayChain
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [HasNoInfiniteRayChain C]
    [HasRayLongPathEndpointValencyAtMostThree C] :
    ContourFunctionCohomologyVanishes (k := k)
      (rayPathContourRelation (C := C)) := by
  apply
    contourFunctionCohomologyVanishes_of_hardEfficientMaximalRayResidueInduction
  intro D _ _ _ _ _ _ _ hbound
  exact hasHardInvisibleCorrectionsOnEfficientMaximalRays (k := k) (C := D)

end LargeIndecomposable
