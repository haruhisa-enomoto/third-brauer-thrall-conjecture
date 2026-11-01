module

public import LargeIndecomposable.RayCategories.Distributive.BGRSRayPathLift

@[expose] public section

/-!
# Stable paths in the BGRS ray category

BGRS stability is occurrence-sensitive: every occurrence of an arrow in a
path may be represented independently inside its unit ray.  This file records
those representative sequences and proves the source's fundamental
characterization: a path is stable exactly when its composite ray is nonzero.

The reverse implication uses the BGRS pair dichotomy.  In the exceptional
product branch, its zero representatives can be absorbed into the last arrow
occurrence, so no global consistency assumption on repeated arrows is needed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasWellDefinedBGRSRayProduct C]

/-- A nonzero ordinary composite whose two unit rays have zero BGRS product
is necessarily in the exceptional radical-insertion branch. -/
theorem isBGRSSpecialZero_of_comp_ne_zero_of_unitRay_comp_eq_zero
    {X Y Z : BGRSRayCategory C}
    {f : X.as ⟶ Y.as} {g : Y.as ⟶ Z.as}
    (hcomp : f ≫ g ≠ 0)
    (hray :
      (show X ⟶ Y from unitRay f) ≫
        (show Y ⟶ Z from unitRay g) = 0) :
    IsBGRSSpecialZero f g := by
  by_contra hspecial
  have hproductRay : unitRay (bgrsRayRepresentativeProduct f g) =
      (0 : UnitRayOrbit X.as Z.as) := by
    calc
      unitRay (bgrsRayRepresentativeProduct f g) =
          (show X ⟶ Z from
            (show X ⟶ Y from
              unitRay f) ≫
              (show Y ⟶ Z from
                unitRay g)) :=
        (BGRSRayCategory.comp_unitRay f g).symm
      _ = 0 := hray
  have hproduct : bgrsRayRepresentativeProduct f g = 0 :=
    (unitRay_eq_zero_iff _).1 hproductRay
  rw [bgrsRayRepresentativeProduct_eq_comp_of_not_special hspecial] at hproduct
  exact hcomp hproduct

/-- An occurrence-by-occurrence choice of ordinary representatives for a
reversed irreducible path in the BGRS ray category. -/
inductive BGRSPathRepresentative :
    {i j : RayVertex (BGRSRayCategory C)} →
      Quiver.Path i j → Type (max u v)
  | nil (i : RayVertex (BGRSRayCategory C)) :
      BGRSPathRepresentative (Quiver.Path.nil : Quiver.Path i i)
  | cons {i j l : RayVertex (BGRSRayCategory C)}
      {p : Quiver.Path i j} {a : j ⟶ l}
      (initial : BGRSPathRepresentative p)
      (last : l.obj.as ⟶ j.obj.as)
      (unitRay_last : unitRay last = a.1) :
      BGRSPathRepresentative (p.cons a)

namespace BGRSPathRepresentative

/-- Ordinary composite of an occurrence-by-occurrence path representative. -/
def composite {i j : RayVertex (BGRSRayCategory C)}
    {p : Quiver.Path i j} (R : BGRSPathRepresentative p) :
    j.obj.as ⟶ i.obj.as :=
  match R with
  | .nil _ => 𝟙 _
  | .cons initial last _ => last ≫ initial.composite

@[simp]
theorem composite_nil (i : RayVertex (BGRSRayCategory C)) :
    (BGRSPathRepresentative.nil i).composite = 𝟙 i.obj.as :=
  rfl

@[simp]
theorem composite_cons
    {i j l : RayVertex (BGRSRayCategory C)}
    {p : Quiver.Path i j} {a : j ⟶ l}
    (initial : BGRSPathRepresentative p)
    (last : l.obj.as ⟶ j.obj.as)
    (hlast : unitRay last = a.1) :
    (BGRSPathRepresentative.cons initial last hlast).composite =
      last ≫ initial.composite :=
  rfl

/-- Concatenate independent representative choices for two composable ray
paths.  Because ordinary representatives reverse the ray-path orientation,
the composite of the second representative sequence occurs first. -/
def comp
    {i j l : RayVertex (BGRSRayCategory C)}
    {p : Quiver.Path i j} {q : Quiver.Path j l}
    (P : BGRSPathRepresentative p)
    (Q : BGRSPathRepresentative q) :
    BGRSPathRepresentative (p.comp q) :=
  match q, Q with
  | .nil, .nil _ => P
  | .cons _ _, .cons initial last hlast =>
      .cons (comp P initial) last hlast

@[simp]
theorem composite_comp
    {i j l : RayVertex (BGRSRayCategory C)}
    {p : Quiver.Path i j} {q : Quiver.Path j l}
    (P : BGRSPathRepresentative p)
    (Q : BGRSPathRepresentative q) :
    (P.comp Q).composite = Q.composite ≫ P.composite := by
  induction q with
  | nil =>
      cases Q
      simp [comp]
  | cons q a ih =>
      cases Q with
      | cons initial last hlast =>
          change last ≫ (P.comp initial).composite =
            (last ≫ initial.composite) ≫ P.composite
          rw [ih initial, Category.assoc]

/-- Split an occurrence-by-occurrence representative sequence at a specified
path concatenation. -/
def splitComp
    {i j l : RayVertex (BGRSRayCategory C)}
    (p : Quiver.Path i j) (q : Quiver.Path j l)
    (R : BGRSPathRepresentative (p.comp q)) :
    BGRSPathRepresentative p × BGRSPathRepresentative q :=
  match q with
  | .nil => (R, .nil _)
  | .cons q a =>
      match R with
      | .cons initial last hlast =>
          let pieces := splitComp p q initial
          (pieces.1, .cons pieces.2 last hlast)

@[simp]
theorem comp_splitComp
    {i j l : RayVertex (BGRSRayCategory C)}
    (p : Quiver.Path i j) (q : Quiver.Path j l)
    (R : BGRSPathRepresentative (p.comp q)) :
    (splitComp p q R).1.comp (splitComp p q R).2 = R := by
  induction q with
  | nil =>
      simp [splitComp, comp]
  | cons q a ih =>
      cases R with
      | cons initial last hlast =>
          change
            (splitComp p q initial).1.comp
                (.cons (splitComp p q initial).2 last hlast) =
              .cons initial last hlast
          simp only [comp]
          rw [ih initial]

/-- The ordinary composite of a split representative sequence factors in
the reverse order of the two ray subpaths. -/
theorem composite_splitComp
    {i j l : RayVertex (BGRSRayCategory C)}
    (p : Quiver.Path i j) (q : Quiver.Path j l)
    (R : BGRSPathRepresentative (p.comp q)) :
    R.composite =
      (splitComp p q R).2.composite ≫
        (splitComp p q R).1.composite := by
  calc
    R.composite =
        ((splitComp p q R).1.comp
          (splitComp p q R).2).composite :=
      congrArg composite (comp_splitComp p q R).symm
    _ = (splitComp p q R).2.composite ≫
        (splitComp p q R).1.composite := composite_comp _ _

/-- A global ray-arrow lift gives an occurrence-by-occurrence representative
sequence for every path. -/
def ofArrowLift (L : BGRSRayArrowLift (C := C)) :
    {i j : RayVertex (BGRSRayCategory C)} →
      (p : Quiver.Path i j) → BGRSPathRepresentative p
  | _, _, .nil => .nil _
  | _, _, .cons p a =>
      .cons (ofArrowLift L p) (L.representative a)
        (L.unitRay_representative a)

@[simp]
theorem composite_ofArrowLift (L : BGRSRayArrowLift (C := C))
    {i j : RayVertex (BGRSRayCategory C)} (p : Quiver.Path i j) :
    (ofArrowLift L p).composite = L.pathMap p := by
  induction p with
  | nil => simp [ofArrowLift, BGRSRayArrowLift.pathMap]
  | cons p a ih =>
      simp [ofArrowLift, BGRSRayArrowLift.pathMap, ih]

/-- If the ray value of a path is nonzero, every occurrence-by-occurrence
ordinary representative has that exact unit ray. -/
theorem unitRay_composite_eq_rayPathMap_of_ne_zero
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (R : BGRSPathRepresentative p) (hp : rayPathMap p ≠ 0) :
    unitRay R.composite = rayPathMap p := by
  induction p with
  | nil =>
      cases R
      simp [composite, rayPathMap]
  | @cons j l p a ih =>
      cases R with
      | cons initial last hlast =>
          have hpPrefix : rayPathMap p ≠ 0 := by
            intro hzero
            apply hp
            simp only [rayPathMap, LinearPathCategory.pathMap_cons]
            change a.1 ≫ rayPathMap p = 0
            rw [hzero]
            simp
          have ih' := ih initial hpPrefix
          have hcompRay : a.1 ≫ rayPathMap p ≠ 0 := by
            change rayArrowMorphism a ≫ rayPathMap p ≠ 0
            simpa only [rayPathMap, LinearPathCategory.pathMap_cons] using hp
          rw [← hlast, ← ih', BGRSRayCategory.comp_unitRay] at hcompRay
          have hprod :
              bgrsRayRepresentativeProduct last initial.composite ≠ 0 :=
            (unitRay_ne_zero_iff _).1 hcompRay
          have hns : ¬IsBGRSSpecialZero last initial.composite := by
            intro hs
            exact hprod (bgrsRayRepresentativeProduct_eq_zero_of_special hs)
          simp only [composite_cons, rayPathMap,
            LinearPathCategory.pathMap_cons]
          change unitRay (last ≫ initial.composite) =
            a.1 ≫ rayPathMap p
          rw [← hlast, ← ih', BGRSRayCategory.comp_unitRay,
            bgrsRayRepresentativeProduct_eq_comp_of_not_special hns]

/-- On a nonzero ray path, any two independent representative sequences
belong to the same ordinary unit ray. -/
theorem unitRayEquivalent_of_rayPathMap_ne_zero
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (R S : BGRSPathRepresentative p) (hp : rayPathMap p ≠ 0) :
    UnitRayEquivalent R.composite S.composite := by
  apply (unitRay_eq_iff _ _).1
  rw [R.unitRay_composite_eq_rayPathMap_of_ne_zero hp,
    S.unitRay_composite_eq_rayPathMap_of_ne_zero hp]

/-- If a concatenated ray path is nonzero, inserting an arbitrary unit
between any representative sequences for its two pieces leaves the ordinary
composite nonzero.  This is the cutwise stability input in the BGRS `P_i`
induction. -/
theorem middleUnitComposite_ne_zero_of_rayPathMap_comp_ne_zero
    {i j l : RayVertex (BGRSRayCategory C)}
    {p : Quiver.Path i j} {q : Quiver.Path j l}
    (P : BGRSPathRepresentative p)
    (Q : BGRSPathRepresentative q)
    (hpq : rayPathMap (p.comp q) ≠ 0)
    (m : End j.obj.as) (hm : IsUnit m) :
    (Q.composite ≫ m.asHom) ≫ P.composite ≠ 0 := by
  have hp : rayPathMap p ≠ 0 := by
    intro hzero
    apply hpq
    simp only [rayPathMap, LinearPathCategory.pathMap_comp]
    change rayPathMap q ≫ rayPathMap p = 0
    rw [hzero]
    simp
  have hq : rayPathMap q ≠ 0 := by
    intro hzero
    apply hpq
    simp only [rayPathMap, LinearPathCategory.pathMap_comp]
    change rayPathMap q ≫ rayPathMap p = 0
    rw [hzero]
    simp
  haveI : IsIso m.asHom := (isUnit_iff_isIso _).1 hm
  have hQmEq :
      unitRay (Q.composite ≫ m.asHom) = unitRay Q.composite := by
    symm
    apply (unitRay_eq_iff _ _).2
    exact ⟨Iso.refl _, asIso m.asHom, by simp⟩
  have hQm :
      unitRay (Q.composite ≫ m.asHom) = rayPathMap q := by
    rw [hQmEq, Q.unitRay_composite_eq_rayPathMap_of_ne_zero hq]
  have hP : unitRay P.composite = rayPathMap p :=
    P.unitRay_composite_eq_rayPathMap_of_ne_zero hp
  have hray :
      (show l.obj ⟶ j.obj from unitRay (Q.composite ≫ m.asHom)) ≫
        (show j.obj ⟶ i.obj from unitRay P.composite) ≠ 0 := by
    rw [hQm, hP]
    simpa only [rayPathMap, LinearPathCategory.pathMap_comp] using hpq
  have hproductRay :
      unitRay (bgrsRayRepresentativeProduct
        (Q.composite ≫ m.asHom) P.composite) ≠ 0 := by
    intro hzero
    apply hray
    exact (BGRSRayCategory.comp_unitRay
      (Q.composite ≫ m.asHom) P.composite).trans hzero
  have hproduct :
      bgrsRayRepresentativeProduct
        (Q.composite ≫ m.asHom) P.composite ≠ 0 :=
    (unitRay_ne_zero_iff _).1 hproductRay
  have hnotSpecial :
      ¬IsBGRSSpecialZero (Q.composite ≫ m.asHom) P.composite := by
    intro hspecial
    exact hproduct
      (bgrsRayRepresentativeProduct_eq_zero_of_special hspecial)
  rw [bgrsRayRepresentativeProduct_eq_comp_of_not_special hnotSpecial]
    at hproduct
  exact hproduct

/-- A nonzero ray path has nonzero ordinary composite for every independent
choice of representatives at its arrow occurrences. -/
theorem composite_ne_zero_of_rayPathMap_ne_zero
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (R : BGRSPathRepresentative p) (hp : rayPathMap p ≠ 0) :
    R.composite ≠ 0 := by
  rw [← unitRay_ne_zero_iff]
  rw [R.unitRay_composite_eq_rayPathMap_of_ne_zero hp]
  exact hp

/-- A zero ray path admits an occurrence-by-occurrence representative with
zero ordinary composite. -/
theorem exists_composite_eq_zero_of_rayPathMap_eq_zero
    [HasBGRSPairDichotomy C]
    {i j : RayVertex (BGRSRayCategory C)} (p : Quiver.Path i j)
    (hp : rayPathMap p = 0) :
    ∃ R : BGRSPathRepresentative p, R.composite = 0 := by
  induction p with
  | nil =>
      refine ⟨.nil i, ?_⟩
      have hp' : (𝟙 i.obj : i.obj ⟶ i.obj) = 0 := by
        simpa only [rayPathMap, LinearPathCategory.pathMap_nil] using hp
      apply (unitRay_eq_zero_iff (𝟙 i.obj.as)).1
      exact hp'
  | @cons j l p a ih =>
      by_cases hpPrefix : rayPathMap p = 0
      · obtain ⟨initial, hinitial⟩ := ih hpPrefix
        refine ⟨.cons initial a.1.out (unitRay_out a.1), ?_⟩
        simp [hinitial]
      · let initial : BGRSPathRepresentative p :=
          ofArrowLift BGRSRayArrowLift.quotientOut p
        have hinitialRay : unitRay initial.composite = rayPathMap p :=
          initial.unitRay_composite_eq_rayPathMap_of_ne_zero hpPrefix
        let last : l.obj.as ⟶ j.obj.as := a.1.out
        have hlastRay : unitRay last = a.1 := unitRay_out a.1
        have hrayComp :
            (show l.obj ⟶ j.obj from unitRay last) ≫
              (show j.obj ⟶ i.obj from unitRay initial.composite) = 0 := by
          rw [hlastRay, hinitialRay]
          change rayArrowMorphism a ≫ rayPathMap p = 0
          simpa only [rayPathMap, LinearPathCategory.pathMap_cons] using hp
        have hproductRay :
            unitRay (bgrsRayRepresentativeProduct last initial.composite) = 0 := by
          calc
            unitRay (bgrsRayRepresentativeProduct last initial.composite) =
                (show l.obj ⟶ i.obj from
                  (show l.obj ⟶ j.obj from unitRay last) ≫
                    (show j.obj ⟶ i.obj from
                      unitRay initial.composite)) :=
              (BGRSRayCategory.comp_unitRay
                last initial.composite).symm
            _ = 0 := hrayComp
        have hproduct :
            bgrsRayRepresentativeProduct last initial.composite = 0 :=
          (unitRay_eq_zero_iff _).1 hproductRay
        by_cases hspecial : IsBGRSSpecialZero last initial.composite
        · obtain ⟨last', tail', hlast', htail', hzero⟩ :=
            (HasBGRSPairDichotomy.pair last initial.composite)
              |>.zero_representatives_of_special hspecial
          rcases htail' with ⟨leftUnit, rightUnit, htailEq⟩
          let adjustedLast : l.obj.as ⟶ j.obj.as :=
            last' ≫ leftUnit.hom
          have hadjustedRay : unitRay adjustedLast = a.1 := by
            calc
              unitRay adjustedLast = unitRay last' := by
                apply (unitRay_eq_iff _ _).2
                exact ⟨Iso.refl _, leftUnit.symm, by simp [adjustedLast]⟩
              _ = unitRay last := ((unitRay_eq_iff _ _).2 hlast').symm
              _ = a.1 := hlastRay
          have hadjustedZero : adjustedLast ≫ initial.composite = 0 := by
            haveI : IsIso rightUnit.hom := by infer_instance
            apply (cancel_mono rightUnit.hom).1
            calc
              (adjustedLast ≫ initial.composite) ≫ rightUnit.hom =
                  last' ≫ tail' := by
                    rw [htailEq]
                    simp only [adjustedLast, Category.assoc]
              _ = 0 := hzero
              _ = 0 ≫ rightUnit.hom := by simp
          exact ⟨.cons initial adjustedLast hadjustedRay, by
            simpa only [composite_cons] using hadjustedZero⟩
        · refine ⟨.cons initial last hlastRay, ?_⟩
          simp only [composite_cons]
          rw [← bgrsRayRepresentativeProduct_eq_comp_of_not_special hspecial]
          exact hproduct

end BGRSPathRepresentative

/-- BGRS stability with independent representative choices at repeated arrow
occurrences. -/
def IsBGRSStablePath
    {i j : RayVertex (BGRSRayCategory C)} (p : Quiver.Path i j) : Prop :=
  ∀ R : BGRSPathRepresentative p, R.composite ≠ 0

/-- BGRS Proposition 2.1, easy direction: a nonzero composed ray makes the
path stable. -/
theorem isBGRSStablePath_of_rayPathMap_ne_zero
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (hp : rayPathMap p ≠ 0) : IsBGRSStablePath p :=
  fun R ↦ R.composite_ne_zero_of_rayPathMap_ne_zero hp

/-- BGRS Proposition 2.1: stability is equivalent to nonvanishing of the
composed ray. -/
theorem isBGRSStablePath_iff_rayPathMap_ne_zero
    [HasBGRSPairDichotomy C]
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j} :
    IsBGRSStablePath p ↔ rayPathMap p ≠ 0 := by
  constructor
  · intro hstable hzero
    obtain ⟨R, hR⟩ :=
      BGRSPathRepresentative.exists_composite_eq_zero_of_rayPathMap_eq_zero
        p hzero
    exact hstable R hR
  · exact isBGRSStablePath_of_rayPathMap_ne_zero

/-- The exact source notion of a singular path: some independent
representative sequence composes nontrivially and another composes to zero. -/
def IsBGRSSourceSingularPath
    {i j : RayVertex (BGRSRayCategory C)} (p : Quiver.Path i j) : Prop :=
  (∃ R : BGRSPathRepresentative p, R.composite ≠ 0) ∧
    ∃ R : BGRSPathRepresentative p, R.composite = 0

/-- Source singularity is exactly a zero composed ray together with one
nonzero occurrence-by-occurrence representative. -/
theorem isBGRSSourceSingularPath_iff
    [HasBGRSPairDichotomy C]
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j} :
    IsBGRSSourceSingularPath p ↔
      rayPathMap p = 0 ∧
        ∃ R : BGRSPathRepresentative p, R.composite ≠ 0 := by
  constructor
  · rintro ⟨hnonzero, R, hzero⟩
    refine ⟨?_, hnonzero⟩
    by_contra hray
    exact R.composite_ne_zero_of_rayPathMap_ne_zero hray hzero
  · rintro ⟨hray, hnonzero⟩
    exact ⟨hnonzero,
      BGRSPathRepresentative.exists_composite_eq_zero_of_rayPathMap_eq_zero
        p hray⟩

end LargeIndecomposable
