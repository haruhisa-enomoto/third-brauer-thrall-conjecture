module

public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalTransitSandwich

@[expose] public section

/-!
# Propagating BGRS critical-path radical sandwiches

Fix one occurrence-by-occurrence representative of a singular path whose
ordinary composite is zero.  At a cut, property `P_i` is then exactly the
assertion that inserting some middle Jacobson-radical endomorphism gives a
nonzero composite: membership of the zero full composite in the sandwich is
automatic.

This file proves the rightward one-arrow induction step from BGRS 4.2.  The
zero composite and nonzero sandwich prohibit cotransit/transit for the two cut
pieces.  Roiter's one-dimensional middle-sandwich conclusion and stability of
the enlarged prefix force cotransit across the next arrow, after which the
radical coefficient transfers to the next cut.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable

universe u v w

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable [HasWellDefinedBGRSRayProduct C]

/-- One cut of a fixed zero occurrence-by-occurrence path representative,
together with the nonzero radical sandwich `P_i` at that cut. -/
structure BGRSZeroRepresentativeCut
    {i x j : RayVertex (BGRSRayCategory C)}
    (left : Quiver.Path i x) (right : Quiver.Path x j) where
  leftRep : BGRSPathRepresentative left
  rightRep : BGRSPathRepresentative right
  comp_eq_zero : rightRep.composite ≫ leftRep.composite = 0
  nonzero_sandwich :
    HasNonzeroJacobsonSandwich rightRep.composite leftRep.composite

namespace BGRSZeroRepresentativeCut

/-- A cut is the special zero-pair radical-sandwich configuration with no
change of representatives. -/
def zeroPair
    {i x j : RayVertex (BGRSRayCategory C)}
    {left : Quiver.Path i x} {right : Quiver.Path x j}
    (D : BGRSZeroRepresentativeCut left right) :
    BGRSZeroPairRadicalSandwich D.rightRep.composite D.leftRep.composite where
  left := D.rightRep.composite
  right := D.leftRep.composite
  left_unitRayEquivalent := ⟨Iso.refl _, Iso.refl _, by simp⟩
  right_unitRayEquivalent := ⟨Iso.refl _, Iso.refl _, by simp⟩
  comp_eq_zero := D.comp_eq_zero
  nonzero_sandwich := D.nonzero_sandwich

/-- The ordinary representative of the right path at a `P_i` cut prohibits
cotransit. -/
theorem rightRep_not_allowsCotransit
    {i x j : RayVertex (BGRSRayCategory C)}
    {left : Quiver.Path i x} {right : Quiver.Path x j}
    (D : BGRSZeroRepresentativeCut left right) :
    ¬AllowsCotransit D.rightRep.composite :=
  D.zeroPair.left_not_allowsCotransit

/-- The ordinary representative of the left path at a `P_i` cut prohibits
transit. -/
theorem leftRep_not_allowsTransit
    {i x j : RayVertex (BGRSRayCategory C)}
    {left : Quiver.Path i x} {right : Quiver.Path x j}
    (D : BGRSZeroRepresentativeCut left right) :
    ¬AllowsTransit D.leftRep.composite :=
  D.zeroPair.right_not_allowsTransit

/-- The representative of the next arrow selected by splitting the right
piece of a `P_i` cut allows cotransit.  This is the arrow-behaviour half of the
rightward BGRS induction step. -/
theorem nextRep_allowsCotransit
    [∀ X Y : C, Module.Finite k (X ⟶ Y)]
    [∀ X : C, IsLocalRing (End X)]
    [∀ X : C, IsArtinianRing (End X)]
    [HasRoiterTransitRankBound k C]
    {i x y j : RayVertex (BGRSRayCategory C)}
    {left : Quiver.Path i x} (next : x ⟶ y)
    (tail : Quiver.Path y j)
    (D : BGRSZeroRepresentativeCut left (next.toPath.comp tail))
    (hprefix : rayPathMap (left.comp next.toPath) ≠ 0) :
    AllowsCotransit
      (BGRSPathRepresentative.splitComp next.toPath tail D.rightRep).1.composite := by
  let pieces := BGRSPathRepresentative.splitComp next.toPath tail D.rightRep
  let nextRep : BGRSPathRepresentative next.toPath := pieces.1
  let tailRep : BGRSPathRepresentative tail := pieces.2
  have hrightFactor :
      D.rightRep.composite =
        tailRep.composite ≫ nextRep.composite := by
    simpa only [pieces, nextRep, tailRep] using
      BGRSPathRepresentative.composite_splitComp
        next.toPath tail D.rightRep
  obtain ⟨ρ, hρ⟩ := D.nonzero_sandwich
  have hlocalSandwich :
      HasNonzeroJacobsonSandwich nextRep.composite D.leftRep.composite := by
    refine ⟨ρ, ?_⟩
    intro hzero
    apply hρ
    rw [hrightFactor]
    calc
      ((tailRep.composite ≫ nextRep.composite) ≫ ρ.1.asHom) ≫
          D.leftRep.composite =
          tailRep.composite ≫
            ((nextRep.composite ≫ ρ.1.asHom) ≫
              D.leftRep.composite) := by
        simp only [Category.assoc]
      _ = 0 := by rw [hzero]; simp
  have hunit : ∀ u : End x.obj.as, IsUnit u →
      (nextRep.composite ≫ u.asHom) ≫
        D.leftRep.composite ≠ 0 := by
    intro u hu
    exact
      BGRSPathRepresentative.middleUnitComposite_ne_zero_of_rayPathMap_comp_ne_zero
        D.leftRep nextRep hprefix u hu
  letI : Module.Finite k (End x.obj.as) := by
    change Module.Finite k (x.obj.as ⟶ x.obj.as)
    infer_instance
  rcases allowsCotransit_or_allowsTransit_of_roiter
      (k := k) nextRep.composite D.leftRep.composite
      hlocalSandwich hunit with hC | hT
  · exact hC
  · exact (D.leftRep_not_allowsTransit hT).elim

/-- Rightward BGRS `P_i → P_{i+1}` propagation across one arrow. -/
theorem advanceRight
    [∀ X Y : C, Module.Finite k (X ⟶ Y)]
    [∀ X : C, IsLocalRing (End X)]
    [∀ X : C, IsArtinianRing (End X)]
    [HasRoiterTransitRankBound k C]
    {i x y j : RayVertex (BGRSRayCategory C)}
    {left : Quiver.Path i x} (next : x ⟶ y)
    (tail : Quiver.Path y j)
    (D : BGRSZeroRepresentativeCut left (next.toPath.comp tail))
    (hprefix : rayPathMap (left.comp next.toPath) ≠ 0) :
    Nonempty (BGRSZeroRepresentativeCut
      (left.comp next.toPath) tail) := by
  let pieces := BGRSPathRepresentative.splitComp next.toPath tail D.rightRep
  let nextRep : BGRSPathRepresentative next.toPath := pieces.1
  let tailRep : BGRSPathRepresentative tail := pieces.2
  have hrightFactor :
      D.rightRep.composite =
        tailRep.composite ≫ nextRep.composite := by
    simpa only [pieces, nextRep, tailRep] using
      BGRSPathRepresentative.composite_splitComp
        next.toPath tail D.rightRep
  have hnextNonzero : nextRep.composite ≠ 0 := by
    exact nextRep.composite_ne_zero_of_rayPathMap_ne_zero
      (rayPathMap_isIrreducible_of_length_eq_one
        next.toPath (by simp)).1
  obtain ⟨ρ, hρ⟩ := D.nonzero_sandwich
  have hnextC : AllowsCotransit nextRep.composite := by
    exact D.nextRep_allowsCotransit (k := k) next tail hprefix
  obtain ⟨ρ', hρ'⟩ :=
    exists_jacobson_left_of_allowsCotransit
      (C := C) hnextNonzero hnextC ρ
  let newLeftRep : BGRSPathRepresentative
      (left.comp next.toPath) := D.leftRep.comp nextRep
  have hnewLeftComposite :
      newLeftRep.composite =
        nextRep.composite ≫ D.leftRep.composite := by
    exact BGRSPathRepresentative.composite_comp _ _
  have hnewZero :
      tailRep.composite ≫ newLeftRep.composite = 0 := by
    rw [hnewLeftComposite, ← Category.assoc, ← hrightFactor]
    exact D.comp_eq_zero
  have hnewSandwich :
      HasNonzeroJacobsonSandwich tailRep.composite
        newLeftRep.composite := by
    refine ⟨ρ', ?_⟩
    intro hzero
    apply hρ
    rw [hrightFactor]
    calc
      ((tailRep.composite ≫ nextRep.composite) ≫ ρ.1.asHom) ≫
          D.leftRep.composite =
          tailRep.composite ≫
            ((nextRep.composite ≫ ρ.1.asHom) ≫
              D.leftRep.composite) := by
        simp only [Category.assoc]
      _ = tailRep.composite ≫
          ((ρ'.1.asHom ≫ nextRep.composite) ≫
            D.leftRep.composite) := by rw [hρ']
      _ =
          (tailRep.composite ≫ ρ'.1.asHom) ≫
            (nextRep.composite ≫ D.leftRep.composite) := by
        simp only [Category.assoc]
      _ = (tailRep.composite ≫ ρ'.1.asHom) ≫
          newLeftRep.composite := by rw [hnewLeftComposite]
      _ = 0 := hzero
  exact ⟨
    { leftRep := newLeftRep
      rightRep := tailRep
      comp_eq_zero := hnewZero
      nonzero_sandwich := hnewSandwich }⟩

/-- The representative of the previous arrow selected by splitting the left
piece of a `P_i` cut allows transit.  This is the arrow-behaviour half of the
leftward BGRS induction step. -/
theorem prevRep_allowsTransit
    [∀ X Y : C, Module.Finite k (X ⟶ Y)]
    [∀ X : C, IsLocalRing (End X)]
    [∀ X : C, IsArtinianRing (End X)]
    [HasRoiterTransitRankBound k C]
    {i y x j : RayVertex (BGRSRayCategory C)}
    (head : Quiver.Path i y) (prev : y ⟶ x)
    {right : Quiver.Path x j}
    (D : BGRSZeroRepresentativeCut
      (head.comp prev.toPath) right)
    (hsuffix : rayPathMap (prev.toPath.comp right) ≠ 0) :
    AllowsTransit
      (BGRSPathRepresentative.splitComp head prev.toPath D.leftRep).2.composite := by
  let pieces :=
    BGRSPathRepresentative.splitComp head prev.toPath D.leftRep
  let headRep : BGRSPathRepresentative head := pieces.1
  let prevRep : BGRSPathRepresentative prev.toPath := pieces.2
  have hleftFactor :
      D.leftRep.composite =
        prevRep.composite ≫ headRep.composite := by
    simpa only [pieces, headRep, prevRep] using
      BGRSPathRepresentative.composite_splitComp
        head prev.toPath D.leftRep
  obtain ⟨ρ, hρ⟩ := D.nonzero_sandwich
  have hlocalSandwich :
      HasNonzeroJacobsonSandwich D.rightRep.composite
        prevRep.composite := by
    refine ⟨ρ, ?_⟩
    intro hzero
    apply hρ
    rw [hleftFactor]
    calc
      (D.rightRep.composite ≫ ρ.1.asHom) ≫
          (prevRep.composite ≫ headRep.composite) =
          ((D.rightRep.composite ≫ ρ.1.asHom) ≫
            prevRep.composite) ≫ headRep.composite := by
        simp only [Category.assoc]
      _ = 0 := by rw [hzero]; simp
  have hunit : ∀ u : End x.obj.as, IsUnit u →
      (D.rightRep.composite ≫ u.asHom) ≫
        prevRep.composite ≠ 0 := by
    intro u hu
    exact
      BGRSPathRepresentative.middleUnitComposite_ne_zero_of_rayPathMap_comp_ne_zero
        prevRep D.rightRep hsuffix u hu
  letI : Module.Finite k (End x.obj.as) := by
    change Module.Finite k (x.obj.as ⟶ x.obj.as)
    infer_instance
  rcases allowsCotransit_or_allowsTransit_of_roiter
      (k := k) D.rightRep.composite prevRep.composite
      hlocalSandwich hunit with hC | hT
  · exact (D.rightRep_not_allowsCotransit hC).elim
  · exact hT

/-- Leftward BGRS `P_i → P_{i-1}` propagation across one arrow. -/
theorem retreatLeft
    [∀ X Y : C, Module.Finite k (X ⟶ Y)]
    [∀ X : C, IsLocalRing (End X)]
    [∀ X : C, IsArtinianRing (End X)]
    [HasRoiterTransitRankBound k C]
    {i y x j : RayVertex (BGRSRayCategory C)}
    (head : Quiver.Path i y) (prev : y ⟶ x)
    {right : Quiver.Path x j}
    (D : BGRSZeroRepresentativeCut
      (head.comp prev.toPath) right)
    (hsuffix : rayPathMap (prev.toPath.comp right) ≠ 0) :
    Nonempty (BGRSZeroRepresentativeCut head
      (prev.toPath.comp right)) := by
  let pieces :=
    BGRSPathRepresentative.splitComp head prev.toPath D.leftRep
  let headRep : BGRSPathRepresentative head := pieces.1
  let prevRep : BGRSPathRepresentative prev.toPath := pieces.2
  have hleftFactor :
      D.leftRep.composite =
        prevRep.composite ≫ headRep.composite := by
    simpa only [pieces, headRep, prevRep] using
      BGRSPathRepresentative.composite_splitComp
        head prev.toPath D.leftRep
  have hprevNonzero : prevRep.composite ≠ 0 := by
    exact prevRep.composite_ne_zero_of_rayPathMap_ne_zero
      (rayPathMap_isIrreducible_of_length_eq_one
        prev.toPath (by simp)).1
  obtain ⟨ρ, hρ⟩ := D.nonzero_sandwich
  have hprevT : AllowsTransit prevRep.composite := by
    exact D.prevRep_allowsTransit (k := k) head prev hsuffix
  obtain ⟨ρ', hρ'⟩ :=
    exists_jacobson_right_of_allowsTransit
      (C := C) hprevNonzero hprevT ρ
  let newRightRep : BGRSPathRepresentative
      (prev.toPath.comp right) := prevRep.comp D.rightRep
  have hnewRightComposite :
      newRightRep.composite =
        D.rightRep.composite ≫ prevRep.composite := by
    exact BGRSPathRepresentative.composite_comp _ _
  have hnewZero :
      newRightRep.composite ≫ headRep.composite = 0 := by
    rw [hnewRightComposite, Category.assoc, ← hleftFactor]
    exact D.comp_eq_zero
  have hnewSandwich :
      HasNonzeroJacobsonSandwich newRightRep.composite
        headRep.composite := by
    refine ⟨ρ', ?_⟩
    intro hzero
    apply hρ
    rw [hleftFactor]
    calc
      (D.rightRep.composite ≫ ρ.1.asHom) ≫
          (prevRep.composite ≫ headRep.composite) =
          D.rightRep.composite ≫
            ((ρ.1.asHom ≫ prevRep.composite) ≫
              headRep.composite) := by
        simp only [Category.assoc]
      _ = D.rightRep.composite ≫
          ((prevRep.composite ≫ ρ'.1.asHom) ≫
            headRep.composite) := by rw [hρ']
      _ = (newRightRep.composite ≫ ρ'.1.asHom) ≫
          headRep.composite := by
        rw [hnewRightComposite]
        simp only [Category.assoc]
      _ = 0 := hzero
  exact ⟨
    { leftRep := headRep
      rightRep := newRightRep
      comp_eq_zero := hnewZero
      nonzero_sandwich := hnewSandwich }⟩

/-- Iterate `advanceRight` along an arbitrary finite path.  Nonvanishing of
the final enlarged prefix implies nonvanishing at every intermediate prefix,
so no separate stability callback is required. -/
theorem advanceAlong
    [∀ X Y : C, Module.Finite k (X ⟶ Y)]
    [∀ X : C, IsLocalRing (End X)]
    [∀ X : C, IsArtinianRing (End X)]
    [HasRoiterTransitRankBound k C]
    {i x y j : RayVertex (BGRSRayCategory C)}
    {left : Quiver.Path i x}
    (segment : Quiver.Path x y) (tail : Quiver.Path y j)
    (D : BGRSZeroRepresentativeCut left (segment.comp tail))
    (hfinal : rayPathMap (left.comp segment) ≠ 0) :
    Nonempty (BGRSZeroRepresentativeCut
      (left.comp segment) tail) := by
  induction segment with
  | nil =>
      exact ⟨by simpa using D⟩
  | @cons z y segment next ih =>
      have hright :
          (segment.cons next).comp tail =
            segment.comp (next.toPath.comp tail) := by
        rw [show segment.cons next = segment.comp next.toPath by
          simp [Quiver.Hom.toPath]]
        exact Quiver.Path.comp_assoc _ _ _
      have Dprefix : BGRSZeroRepresentativeCut left
          (segment.comp (next.toPath.comp tail)) := by
        simpa only [hright] using D
      have hpathFinal :
          left.comp (segment.cons next) =
            (left.comp segment).comp next.toPath := by
        rw [show segment.cons next = segment.comp next.toPath by
          simp [Quiver.Hom.toPath]]
        exact (Quiver.Path.comp_assoc _ _ _).symm
      have hprefix : rayPathMap (left.comp segment) ≠ 0 := by
        intro hzero
        apply hfinal
        rw [hpathFinal]
        calc
          rayPathMap ((left.comp segment).comp next.toPath) =
              rayPathMap next.toPath ≫
                rayPathMap (left.comp segment) := by
            simp only [rayPathMap, LinearPathCategory.pathMap_comp]
          _ = 0 := by rw [hzero]; simp
      obtain ⟨Dmiddle⟩ :=
        ih (next.toPath.comp tail) Dprefix hprefix
      have hnext :
          rayPathMap ((left.comp segment).comp next.toPath) ≠ 0 := by
        rw [← hpathFinal]
        exact hfinal
      obtain ⟨Dnext⟩ :=
        Dmiddle.advanceRight (k := k) next tail hnext
      exact ⟨by
        simpa [Quiver.Hom.toPath, Quiver.Path.comp_assoc] using Dnext⟩

end BGRSZeroRepresentativeCut

end LargeIndecomposable

namespace LargeIndecomposable.BGRSCriticalPathSpine

universe u v w

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable [HasWellDefinedBGRSRayProduct C]

/-- The endpoint `P₁` sandwich transferred to the two pieces of one literal
zero occurrence-by-occurrence representative of the critical path. -/
theorem initialZeroRepresentativeCut
    [HasBGRSPairDichotomy C]
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    Nonempty (BGRSZeroRepresentativeCut spine.first.toPath
      (spine.middle.comp spine.last.toPath)) := by
  have hpath :
      p = spine.first.toPath.comp
        (spine.middle.comp spine.last.toPath) := by
    simpa only [Quiver.Path.comp_assoc] using spine.path_eq
  have hrayZero : rayPathMap
      (spine.first.toPath.comp
        (spine.middle.comp spine.last.toPath)) = 0 := by
    rw [← hpath]
    exact spine.ray_path_eq_zero
  obtain ⟨R, hR⟩ :=
    BGRSPathRepresentative.exists_composite_eq_zero_of_rayPathMap_eq_zero
      (spine.first.toPath.comp
        (spine.middle.comp spine.last.toPath)) hrayZero
  let pieces := BGRSPathRepresentative.splitComp
    spine.first.toPath (spine.middle.comp spine.last.toPath) R
  let leftRep : BGRSPathRepresentative spine.first.toPath := pieces.1
  let rightRep : BGRSPathRepresentative
      (spine.middle.comp spine.last.toPath) := pieces.2
  have hzero : rightRep.composite ≫ leftRep.composite = 0 := by
    rw [← BGRSPathRepresentative.composite_splitComp
      spine.first.toPath (spine.middle.comp spine.last.toPath) R]
    exact hR
  have hbase : HasNonzeroJacobsonSandwich
      (spine.lift.pathMap (spine.middle.comp spine.last.toPath))
      (spine.lift.representative spine.first) := by
    obtain ⟨ρ, -, hρ⟩ := spine.exists_initial_radical_sandwich
    exact ⟨ρ, hρ⟩
  let liftLeft := BGRSPathRepresentative.ofArrowLift
    spine.lift spine.first.toPath
  let liftRight := BGRSPathRepresentative.ofArrowLift
    spine.lift (spine.middle.comp spine.last.toPath)
  have hfirstRay : rayPathMap spine.first.toPath ≠ 0 :=
    (rayPathMap_isIrreducible_of_length_eq_one
      spine.first.toPath (by simp)).1
  have hleftEq : UnitRayEquivalent
      (spine.lift.representative spine.first) leftRep.composite := by
    simpa only [liftLeft,
      BGRSPathRepresentative.composite_ofArrowLift,
      BGRSRayArrowLift.pathMap, Quiver.Hom.toPath,
      LinearPathCategory.pathMap_cons,
      LinearPathCategory.pathMap_nil, Category.comp_id] using
      liftLeft.unitRayEquivalent_of_rayPathMap_ne_zero leftRep hfirstRay
  have hrightEq : UnitRayEquivalent
      (spine.lift.pathMap (spine.middle.comp spine.last.toPath))
      rightRep.composite := by
    simpa only [liftRight,
      BGRSPathRepresentative.composite_ofArrowLift] using
      liftRight.unitRayEquivalent_of_rayPathMap_ne_zero
        rightRep spine.suffix_ray_ne_zero
  exact ⟨
    { leftRep := leftRep
      rightRep := rightRep
      comp_eq_zero := hzero
      nonzero_sandwich :=
        hasNonzeroJacobsonSandwich_of_unitRayEquivalent
          hrightEq hleftEq hbase }⟩

/-- The endpoint `Pₙ₋₁` sandwich transferred to the two pieces of one literal
zero occurrence-by-occurrence representative of the critical path. -/
theorem terminalZeroRepresentativeCut
    [HasBGRSPairDichotomy C]
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    Nonempty (BGRSZeroRepresentativeCut
      (spine.first.toPath.comp spine.middle) spine.last.toPath) := by
  have hrayZero : rayPathMap
      ((spine.first.toPath.comp spine.middle).comp
        spine.last.toPath) = 0 := by
    rw [← spine.path_eq]
    exact spine.ray_path_eq_zero
  obtain ⟨R, hR⟩ :=
    BGRSPathRepresentative.exists_composite_eq_zero_of_rayPathMap_eq_zero
      ((spine.first.toPath.comp spine.middle).comp
        spine.last.toPath) hrayZero
  let pieces := BGRSPathRepresentative.splitComp
    (spine.first.toPath.comp spine.middle) spine.last.toPath R
  let leftRep : BGRSPathRepresentative
      (spine.first.toPath.comp spine.middle) := pieces.1
  let rightRep : BGRSPathRepresentative spine.last.toPath := pieces.2
  have hzero : rightRep.composite ≫ leftRep.composite = 0 := by
    rw [← BGRSPathRepresentative.composite_splitComp
      (spine.first.toPath.comp spine.middle) spine.last.toPath R]
    exact hR
  have hbase : HasNonzeroJacobsonSandwich
      (spine.lift.representative spine.last)
      (spine.lift.pathMap (spine.first.toPath.comp spine.middle)) := by
    obtain ⟨ρ, -, hρ⟩ := spine.exists_terminal_radical_sandwich
    exact ⟨ρ, hρ⟩
  let liftLeft := BGRSPathRepresentative.ofArrowLift
    spine.lift (spine.first.toPath.comp spine.middle)
  let liftRight := BGRSPathRepresentative.ofArrowLift
    spine.lift spine.last.toPath
  have hlastRay : rayPathMap spine.last.toPath ≠ 0 :=
    (rayPathMap_isIrreducible_of_length_eq_one
      spine.last.toPath (by simp)).1
  have hleftEq : UnitRayEquivalent
      (spine.lift.pathMap (spine.first.toPath.comp spine.middle))
      leftRep.composite := by
    simpa only [liftLeft,
      BGRSPathRepresentative.composite_ofArrowLift] using
      liftLeft.unitRayEquivalent_of_rayPathMap_ne_zero
        leftRep spine.prefix_ray_ne_zero
  have hrightEq : UnitRayEquivalent
      (spine.lift.representative spine.last) rightRep.composite := by
    simpa only [liftRight,
      BGRSPathRepresentative.composite_ofArrowLift,
      BGRSRayArrowLift.pathMap, Quiver.Hom.toPath,
      LinearPathCategory.pathMap_cons,
      LinearPathCategory.pathMap_nil, Category.comp_id] using
      liftRight.unitRayEquivalent_of_rayPathMap_ne_zero rightRep hlastRay
  exact ⟨
    { leftRep := leftRep
      rightRep := rightRep
      comp_eq_zero := hzero
      nonzero_sandwich :=
        hasNonzeroJacobsonSandwich_of_unitRayEquivalent
          hrightEq hleftEq hbase }⟩

/-- Conditional on Roiter's transit lemma, every split of the middle of a
critical spine carries the exact `P_i` zero-representative cut.  This is the
all-internal-cuts conclusion of BGRS 4.2; the sole unproved source input is the
`HasRoiterTransitRankBound` instance. -/
theorem zeroRepresentativeCut_at_middle_split
    [HasBGRSPairDichotomy C]
    [∀ X Y : C, Module.Finite k (X ⟶ Y)]
    [∀ X : C, IsLocalRing (End X)]
    [∀ X : C, IsArtinianRing (End X)]
    [HasRoiterTransitRankBound k C]
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    {x : RayVertex (BGRSRayCategory C)}
    (midLeft : Quiver.Path spine.leftInner x)
    (midRight : Quiver.Path x spine.rightInner)
    (hmiddle : spine.middle = midLeft.comp midRight) :
    Nonempty (BGRSZeroRepresentativeCut
      (spine.first.toPath.comp midLeft)
      (midRight.comp spine.last.toPath)) := by
  obtain ⟨Dinitial⟩ := spine.initialZeroRepresentativeCut
  have hright :
      spine.middle.comp spine.last.toPath =
        midLeft.comp (midRight.comp spine.last.toPath) := by
    rw [hmiddle]
    exact Quiver.Path.comp_assoc _ _ _
  have Dstart : BGRSZeroRepresentativeCut spine.first.toPath
      (midLeft.comp (midRight.comp spine.last.toPath)) := by
    simpa only [hright] using Dinitial
  have hfull :
      spine.first.toPath.comp spine.middle =
        (spine.first.toPath.comp midLeft).comp midRight := by
    rw [hmiddle]
    exact (Quiver.Path.comp_assoc _ _ _).symm
  have hprefix :
      rayPathMap (spine.first.toPath.comp midLeft) ≠ 0 := by
    intro hzero
    apply spine.prefix_ray_ne_zero
    rw [hfull]
    calc
      rayPathMap
          ((spine.first.toPath.comp midLeft).comp midRight) =
          rayPathMap midRight ≫
            rayPathMap (spine.first.toPath.comp midLeft) := by
        simp only [rayPathMap, LinearPathCategory.pathMap_comp]
      _ = 0 := by rw [hzero]; simp
  exact Dstart.advanceAlong (k := k) midLeft
    (midRight.comp spine.last.toPath) hprefix

/-- Conditional on Roiter's rank-one transit consequence, every arrow
strictly inside a critical path allows both transit and cotransit.  This is the
bitransit conclusion in BGRS 4.2, stated for the quotient-chosen ordinary
representative of the displayed ray arrow. -/
theorem internalArrow_allowsBitransit
    [HasBGRSPairDichotomy C]
    [∀ X Y : C, Module.Finite k (X ⟶ Y)]
    [∀ X : C, IsLocalRing (End X)]
    [∀ X : C, IsArtinianRing (End X)]
    [HasRoiterTransitRankBound k C]
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p)
    {x y : RayVertex (BGRSRayCategory C)}
    (head : Quiver.Path spine.leftInner x) (a : x ⟶ y)
    (tail : Quiver.Path y spine.rightInner)
    (hmiddle : spine.middle = head.comp (a.toPath.comp tail)) :
    AllowsTransit a.1.out ∧ AllowsCotransit a.1.out := by
  let outRep : BGRSPathRepresentative a.toPath :=
    .cons (.nil _) a.1.out (unitRay_out a.1)
  have haRay : rayPathMap a.toPath ≠ 0 :=
    (rayPathMap_isIrreducible_of_length_eq_one
      a.toPath (by simp)).1
  have hprefixPath :
      spine.first.toPath.comp spine.middle =
        ((spine.first.toPath.comp head).comp a.toPath).comp tail := by
    rw [hmiddle]
    simp only [Quiver.Path.comp_assoc]
  have hprefix :
      rayPathMap ((spine.first.toPath.comp head).comp a.toPath) ≠ 0 := by
    intro hzero
    apply spine.prefix_ray_ne_zero
    rw [hprefixPath]
    calc
      rayPathMap
          (((spine.first.toPath.comp head).comp a.toPath).comp tail) =
          rayPathMap tail ≫
            rayPathMap ((spine.first.toPath.comp head).comp a.toPath) := by
        simp only [rayPathMap, LinearPathCategory.pathMap_comp]
      _ = 0 := by rw [hzero]; simp
  have hsuffixPath :
      spine.middle.comp spine.last.toPath =
        head.comp
          (a.toPath.comp (tail.comp spine.last.toPath)) := by
    rw [hmiddle]
    simp only [Quiver.Path.comp_assoc]
  have hsuffix :
      rayPathMap (a.toPath.comp (tail.comp spine.last.toPath)) ≠ 0 := by
    intro hzero
    apply spine.suffix_ray_ne_zero
    rw [hsuffixPath]
    calc
      rayPathMap
          (head.comp (a.toPath.comp (tail.comp spine.last.toPath))) =
          rayPathMap (a.toPath.comp (tail.comp spine.last.toPath)) ≫
            rayPathMap head := by
        simp only [rayPathMap, LinearPathCategory.pathMap_comp]
      _ = 0 := by rw [hzero]; simp
  constructor
  · have hmiddlePost :
        spine.middle = (head.comp a.toPath).comp tail := by
      rw [hmiddle]
      exact (Quiver.Path.comp_assoc _ _ _).symm
    obtain ⟨Dpost⟩ := spine.zeroRepresentativeCut_at_middle_split
      (k := k) (head.comp a.toPath) tail hmiddlePost
    have Dpost' : BGRSZeroRepresentativeCut
        ((spine.first.toPath.comp head).comp a.toPath)
        (tail.comp spine.last.toPath) := by
      simpa only [Quiver.Path.comp_assoc] using Dpost
    let prevRep : BGRSPathRepresentative a.toPath :=
      (BGRSPathRepresentative.splitComp
        (spine.first.toPath.comp head) a.toPath Dpost'.leftRep).2
    have hprevT : AllowsTransit prevRep.composite := by
      exact Dpost'.prevRep_allowsTransit (k := k)
        (spine.first.toPath.comp head) a hsuffix
    have heq : UnitRayEquivalent prevRep.composite outRep.composite :=
      prevRep.unitRayEquivalent_of_rayPathMap_ne_zero outRep haRay
    have hout : outRep.composite = a.1.out := by
      change a.1.out ≫ 𝟙 _ = a.1.out
      simp
    rw [hout] at heq
    exact AllowsTransit.of_unitRayEquivalent hprevT heq
  · obtain ⟨Dpre⟩ := spine.zeroRepresentativeCut_at_middle_split
      (k := k) head (a.toPath.comp tail) hmiddle
    have Dpre' : BGRSZeroRepresentativeCut
        (spine.first.toPath.comp head)
        (a.toPath.comp (tail.comp spine.last.toPath)) := by
      simpa only [Quiver.Path.comp_assoc] using Dpre
    let nextRep : BGRSPathRepresentative a.toPath :=
      (BGRSPathRepresentative.splitComp a.toPath
        (tail.comp spine.last.toPath) Dpre'.rightRep).1
    have hnextC : AllowsCotransit nextRep.composite := by
      exact Dpre'.nextRep_allowsCotransit (k := k) a
        (tail.comp spine.last.toPath) hprefix
    have heq : UnitRayEquivalent nextRep.composite outRep.composite :=
      nextRep.unitRayEquivalent_of_rayPathMap_ne_zero outRep haRay
    have hout : outRep.composite = a.1.out := by
      change a.1.out ≫ 𝟙 _ = a.1.out
      simp
    rw [hout] at heq
    exact AllowsCotransit.of_unitRayEquivalent hnextC heq

end LargeIndecomposable.BGRSCriticalPathSpine
