module

public import LargeIndecomposable.RayCategories.RoiterVanishing.RoiterTransit
public import LargeIndecomposable.Cleaving.ClosedChains.PowerAssembly
public import LargeIndecomposable.Cleaving.ClosedChains.RadicalPowerParameter
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalFigure16
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.NormalizedLift

@[expose] public section

/-!
# Singular-pair orientation for BGRS Figure 16

A singular length-two ray path has representatives with nonzero ordinary
composite, but its special BGRS product is zero.  The special relation
therefore gives a nonzero middle-Jacobson sandwich.  Transferring that
sandwich to any zero representative pair shows that the ordinary left factor
allows transit and the ordinary right factor allows cotransit.

Because the ray quiver is reversed, this says that the packaged second arrow
allows transit while the packaged first arrow does not.  Consequently two
singular pairs cannot share an arrow in opposite positions.  Figure 16 only
has to exclude sharing in the same position (up to duality, one case).
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.CriticalSingularFigure16Pairs

open LargeIndecomposable.SingularPairNormalization

universe u v w

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable [HasBGRSPairDichotomy C]
variable [HasWellDefinedBGRSRayProduct C]
variable [HasBGRSDistributiveHomStructure k C]

/-- The transit property of a packaged reversed-ray arrow, evaluated on its
canonical ordinary representative. -/
def ArrowAllowsTransit (a : Arrow (C := C)) : Prop :=
  AllowsTransit (defaultRepresentative a).hom

omit k [Field k] [Linear k C] [HasBGRSPairDichotomy C]
  [HasWellDefinedBGRSRayProduct C]
  [HasBGRSDistributiveHomStructure k C] in
/-- If `f ≫ g = 0` and `g'` lies in the unit ray of `g`, one can adjust
`f` inside its own unit ray so that `f' ≫ g' = 0`. -/
theorem exists_comp_eq_zero_of_right_unitRayEquivalent
    {X Y Z : C} (f : X ⟶ Y) (g g' : Y ⟶ Z)
    (hzero : f ≫ g = 0) (hgg' : UnitRayEquivalent g g') :
    ∃ f' : X ⟶ Y, UnitRayEquivalent f f' ∧ f' ≫ g' = 0 := by
  rcases hgg' with ⟨a, b, rfl⟩
  refine ⟨f ≫ a.inv, ?_, ?_⟩
  · exact ⟨Iso.refl X, a.symm, by simp⟩
  · simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hzero]
    simp

omit [HasWellDefinedBGRSRayProduct C] in
/-- Replace the first zero representative of a singular pair by any chosen
representative in that ray, compensating on the second representative. -/
theorem exists_zeroSecond_for_first
    (p : SingularPair (C := C))
    (first : Representative p.1.firstArrow) :
    ∃ second : Representative p.1.secondArrow,
      second.hom ≫ first.hom = 0 := by
  let R := chosenZeroRepresentatives p
  have hfirst : UnitRayEquivalent R.first.hom first.hom :=
    (unitRay_eq_iff _ _).1
      (R.first.unitRay_hom.trans first.unitRay_hom.symm)
  obtain ⟨secondHom, hsecond, hzero⟩ :=
    exists_comp_eq_zero_of_right_unitRayEquivalent
      R.second.hom R.first.hom first.hom R.comp_zero hfirst
  refine ⟨
    { hom := secondHom
      unitRay_hom := ?_ }, hzero⟩
  exact ((unitRay_eq_iff _ _).2 hsecond).symm.trans
    R.second.unitRay_hom

/-- Transport a representative along equality of packaged ray arrows. -/
def castRepresentative {a b : Arrow (C := C)} (h : a = b)
    (r : Representative a) : Representative b :=
  h ▸ r

omit k [Field k] [Linear k C] [HasBGRSPairDichotomy C]
  [HasWellDefinedBGRSRayProduct C]
  [HasBGRSDistributiveHomStructure k C] in
/-- A nonzero Jacobson sandwich transports along literal equalities of its
three objects. -/
theorem hasNonzeroJacobsonSandwich_transport_eq
    {X Y Z X' Y' Z' : C}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    {f : X ⟶ Y} {g : Y ⟶ Z}
    (H : HasNonzeroJacobsonSandwich f g) :
    HasNonzeroJacobsonSandwich
      (eqToHom hX.symm ≫ f ≫ eqToHom hY)
      (eqToHom hY.symm ≫ g ≫ eqToHom hZ) := by
  subst X'
  subst Y'
  subst Z'
  simpa using H

omit k [Field k] [Linear k C]
  [HasWellDefinedBGRSRayProduct C]
  [HasBGRSDistributiveHomStructure k C] in
/-- The ordinary morphism underlying a cast representative, written with
the two equality isomorphisms made explicit. -/
theorem castRepresentative_hom
    {a b : Arrow (C := C)} (h : a = b) (r : Representative a) :
    (castRepresentative h r).hom =
      eqToHom (congrArg (fun x : Arrow (C := C) ↦ x.target.obj.as) h).symm ≫
        r.hom ≫
          eqToHom (congrArg
            (fun x : Arrow (C := C) ↦ x.source.obj.as) h) := by
  subst b
  simp [castRepresentative]

omit k [Field k] [Linear k C]
  [HasWellDefinedBGRSRayProduct C]
  [HasBGRSDistributiveHomStructure k C] in
/-- Transporting a cast representative back across the same object
equalities recovers its original ordinary morphism. -/
theorem uncastRepresentative_hom
    {a b : Arrow (C := C)} (h : a = b) (r : Representative a) :
    eqToHom (congrArg
        (fun x : Arrow (C := C) ↦ x.target.obj.as) h) ≫
      (castRepresentative h r).hom ≫
        eqToHom (congrArg
          (fun x : Arrow (C := C) ↦ x.source.obj.as) h).symm =
      r.hom := by
  subst b
  simp [castRepresentative]

/-- Two singular pairs sharing their first arrow, with one common ordinary
representative `alpha` and adjusted branch representatives satisfying the two
literal zero relations used in BGRS 4.5. -/
structure CommonFirstZeroRepresentatives
    (p q : SingularPair (C := C))
    (hfirst : p.1.firstArrow = q.1.firstArrow) where
  alpha : Representative p.1.firstArrow
  beta : Representative p.1.secondArrow
  gamma : Representative q.1.secondArrow
  beta_alpha_zero : beta.hom ≫ alpha.hom = 0
  gamma_alpha_zero :
    gamma.hom ≫ (castRepresentative hfirst alpha).hom = 0

/-- Transport the second branch to the first pair's literal middle object.
This removes the dependent equality hidden in the common packaged arrow. -/
def CommonFirstZeroRepresentatives.alignedGamma
    {p q : SingularPair (C := C)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst) :
    q.1.secondArrow.target.obj.as ⟶ p.1.firstArrow.target.obj.as :=
  D.gamma.hom ≫
    eqToHom (congrArg
      (fun x : Arrow (C := C) ↦ x.target.obj.as) hfirst).symm

omit k [Field k] [Linear k C]
  [HasWellDefinedBGRSRayProduct C]
  [HasBGRSDistributiveHomStructure k C] in
/-- The aligned second branch still has literal zero composite with the
chosen common representative. -/
theorem CommonFirstZeroRepresentatives.alignedGamma_alpha_zero
    {p q : SingularPair (C := C)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst) :
    D.alignedGamma ≫ D.alpha.hom = 0 := by
  have hcast := castRepresentative_hom hfirst D.alpha
  apply (cancel_mono (eqToHom (congrArg
    (fun x : Arrow (C := C) ↦ x.source.obj.as) hfirst))).1
  calc
    (D.alignedGamma ≫ D.alpha.hom) ≫
          eqToHom (congrArg
            (fun x : Arrow (C := C) ↦ x.source.obj.as) hfirst) =
        D.gamma.hom ≫ (castRepresentative hfirst D.alpha).hom := by
      rw [hcast]
      simp only [CommonFirstZeroRepresentatives.alignedGamma,
        Category.assoc]
      congr 1
    _ = 0 := D.gamma_alpha_zero
    _ = 0 ≫ eqToHom (congrArg
          (fun x : Arrow (C := C) ↦ x.source.obj.as) hfirst) := by simp

omit [HasWellDefinedBGRSRayProduct C] in
/-- The simultaneous choice `beta * alpha = 0 = gamma * alpha` always
exists for two singular pairs sharing their first packaged ray arrow. -/
theorem nonempty_commonFirstZeroRepresentatives
    (p q : SingularPair (C := C))
    (hfirst : p.1.firstArrow = q.1.firstArrow) :
    Nonempty (CommonFirstZeroRepresentatives p q hfirst) := by
  let alpha := (chosenZeroRepresentatives p).first
  obtain ⟨beta, hbeta⟩ := exists_zeroSecond_for_first p alpha
  obtain ⟨gamma, hgamma⟩ := exists_zeroSecond_for_first q
    (castRepresentative hfirst alpha)
  exact ⟨
    { alpha := alpha
      beta := beta
      gamma := gamma
      beta_alpha_zero := hbeta
      gamma_alpha_zero := hgamma }⟩

def CommonFirstZeroRepresentatives.pZero
    {p q : SingularPair (C := C)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst) :
    ZeroRepresentatives p where
  first := D.alpha
  second := D.beta
  comp_zero := D.beta_alpha_zero

def CommonFirstZeroRepresentatives.qZero
    {p q : SingularPair (C := C)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst) :
    ZeroRepresentatives q where
  first := castRepresentative hfirst D.alpha
  second := D.gamma
  comp_zero := D.gamma_alpha_zero

/-- Every zero representative pair of a singular pair carries the nonzero
middle-radical sandwich hidden by the exceptional BGRS product.  The ordinary
composition order is `second` followed by `first` because the ray quiver is
reversed. -/
theorem nonempty_zeroPairRadicalSandwich
    (p : SingularPair (C := C)) (R : ZeroRepresentatives p) :
    Nonempty (BGRSZeroPairRadicalSandwich R.second.hom R.first.hom) := by
  obtain ⟨first, second, hnonzero⟩ := p.2.2
  let secondHom : p.1.target.obj.as ⟶ p.1.middle.obj.as := second.hom
  let firstHom : p.1.middle.obj.as ⟶ p.1.source.obj.as := first.hom
  have hsecondRay : unitRay second.hom = p.1.second.1 := by
    simpa only [ComposablePair.secondArrow] using second.unitRay_hom
  have hfirstRay : unitRay first.hom = p.1.first.1 := by
    simpa only [ComposablePair.firstArrow] using first.unitRay_hom
  have hsecond : UnitRayEquivalent second.hom R.second.hom :=
    (unitRay_eq_iff _ _).1
      (hsecondRay.trans (by
        simpa only [ComposablePair.secondArrow] using
          R.second.unitRay_hom.symm))
  have hfirst : UnitRayEquivalent first.hom R.first.hom :=
    (unitRay_eq_iff _ _).1
      (hfirstRay.trans (by
        simpa only [ComposablePair.firstArrow] using
          R.first.unitRay_hom.symm))
  have hrayComp : p.1.second.1 ≫ p.1.first.1 = 0 := by
    simpa only [ComposablePair.path, rayPathMap,
      LinearPathCategory.pathMap_comp, rayPathMap_toPath,
      rayArrowMorphism] using p.2.1
  have hspecialHom : IsBGRSSpecialZero secondHom firstHom := by
    apply isBGRSSpecialZero_of_comp_ne_zero_of_unitRay_comp_eq_zero
    · change secondHom ≫ firstHom ≠ 0 at hnonzero
      exact hnonzero
    · have hsecondHomRay : unitRay secondHom = p.1.second.1 := by
        change unitRay secondHom = p.1.second.1 at hsecondRay
        exact hsecondRay
      have hfirstHomRay : unitRay firstHom = p.1.first.1 := by
        change unitRay firstHom = p.1.first.1 at hfirstRay
        exact hfirstRay
      rw [hsecondHomRay, hfirstHomRay]
      exact hrayComp
  have hspecial : IsBGRSSpecialZero second.hom first.hom := by
    change IsBGRSSpecialZero secondHom firstHom
    exact hspecialHom
  rcases hspecial with ⟨rho, hrho⟩
  have hsandwich : HasNonzeroJacobsonSandwich second.hom first.hom := by
    refine ⟨rho, ?_⟩
    intro hzero
    exact hnonzero (hrho.trans hzero)
  refine ⟨
    { left := R.second.hom
      right := R.first.hom
      left_unitRayEquivalent := (unitRay_eq_iff _ _).1 rfl
      right_unitRayEquivalent := (unitRay_eq_iff _ _).1 rfl
      comp_eq_zero := R.comp_zero
      nonzero_sandwich := ?_ }⟩
  exact hasNonzeroJacobsonSandwich_of_unitRayEquivalent
    hsecond hfirst hsandwich

omit [HasBGRSDistributiveHomStructure k C] in
/-- The second singular pair's radical sandwich transports to the literal
common middle object and the aligned `gamma` branch. -/
theorem CommonFirstZeroRepresentatives.nonempty_alignedGammaAlphaRadicalSandwich
    {p q : SingularPair (C := C)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst) :
    Nonempty (BGRSZeroPairRadicalSandwich D.alignedGamma D.alpha.hom) := by
  obtain ⟨S⟩ := nonempty_zeroPairRadicalSandwich q D.qZero
  have Hq : HasNonzeroJacobsonSandwich D.gamma.hom
      (castRepresentative hfirst D.alpha).hom :=
    hasNonzeroJacobsonSandwich_of_unitRayEquivalent
      ((unitRaySetoid _ _).symm S.left_unitRayEquivalent)
      ((unitRaySetoid _ _).symm S.right_unitRayEquivalent)
      S.nonzero_sandwich
  let gamma : q.1.secondArrow.target.obj.as ⟶
      q.1.firstArrow.target.obj.as := D.gamma.hom
  let alphaQ : q.1.firstArrow.target.obj.as ⟶
      q.1.firstArrow.source.obj.as :=
    (castRepresentative hfirst D.alpha).hom
  have Hq' : HasNonzeroJacobsonSandwich gamma alphaQ := Hq
  let hm := congrArg
    (fun x : Arrow (C := C) ↦ x.target.obj.as) hfirst
  let hs := congrArg
    (fun x : Arrow (C := C) ↦ x.source.obj.as) hfirst
  have Htransport : HasNonzeroJacobsonSandwich
      (eqToHom (rfl : q.1.secondArrow.target.obj.as =
          q.1.secondArrow.target.obj.as) ≫ gamma ≫ eqToHom hm.symm)
      (eqToHom hm ≫ alphaQ ≫ eqToHom hs.symm) :=
    hasNonzeroJacobsonSandwich_transport_eq
      (rfl : q.1.secondArrow.target.obj.as =
        q.1.secondArrow.target.obj.as) hm.symm hs.symm Hq'
  have H : HasNonzeroJacobsonSandwich D.alignedGamma D.alpha.hom := by
    have hsecond : eqToHom hm ≫ alphaQ ≫ eqToHom hs.symm =
        D.alpha.hom := by
      exact uncastRepresentative_hom hfirst D.alpha
    have haligned : D.alignedGamma = gamma ≫ eqToHom hm.symm := by
      rfl
    rw [← haligned, hsecond] at Htransport
    simpa using Htransport
  exact ⟨
    { left := D.alignedGamma
      right := D.alpha.hom
      left_unitRayEquivalent := ⟨Iso.refl _, Iso.refl _, by simp⟩
      right_unitRayEquivalent := ⟨Iso.refl _, Iso.refl _, by simp⟩
      comp_eq_zero := D.alignedGamma_alpha_zero
      nonzero_sandwich := H }⟩

section RadicalParameter

variable [∀ X : C, IsLocalRing (End X)]
variable [∀ X : C, IsArtinianRing (End X)]
variable [∀ X : C, Module.Finite k (X ⟶ X)]

/-- The radical sandwich hidden by either singular pair supplies the
nonzero radical element needed to choose the source's parameter
`tau = pi(m,m)` at the common middle object. -/
theorem CommonFirstZeroRepresentatives.nonempty_middleRadicalPowerParameter
    {p q : SingularPair (C := C)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst) :
    Nonempty
      (LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
        (k := k) p.1.middle.obj.as) := by
  obtain ⟨Z⟩ := nonempty_zeroPairRadicalSandwich p D.pZero
  rcases Z.nonzero_sandwich with ⟨rho, hrho⟩
  have hrho0 : rho.1 ≠ 0 := by
    intro hzero
    apply hrho
    rw [hzero]
    change (Z.left ≫
      (0 : p.1.middle.obj.as ⟶ p.1.middle.obj.as)) ≫ Z.right = 0
    have hleftZero : Z.left ≫
        (0 : p.1.middle.obj.as ⟶ p.1.middle.obj.as) = 0 :=
      CategoryTheory.Limits.comp_zero
    rw [hleftZero]
    exact CategoryTheory.Limits.zero_comp
  exact
    LargeIndecomposable.ClosedZigzagTransfer.nonempty_orientedRadicalPowerParameter_of_nonzero_radical
      (k := k) (C := C) p.1.middle.obj.as rho.1 rho.2 hrho0

end RadicalParameter

section TauNoFactor

variable [IsAlgClosed k]
variable [HasRoiterTransitSquareAlternative k C]

omit [HasBGRSPairDichotomy C] [HasWellDefinedBGRSRayProduct C]
  [HasBGRSDistributiveHomStructure k C] in
/-- The load-bearing Roiter step in BGRS 4.5.  If a literal zero pair
`f * g = 0` retains the exceptional nonzero middle-radical sandwich, then
inserting a radical parameter `tau = pi(Y,Y)` makes the composite nonzero.

Indeed, if both the constant and linear `tau` sandwiches vanished, polynomial
generation of `End(Y)` and Roiter's square alternative would kill every
middle-endomorphism sandwich: degrees at least two lie in `Jac(End Y)^2`.
This contradicts the retained nonzero radical sandwich. -/
theorem tau_sandwich_ne_zero_of_zeroPairRadicalSandwich
    {X Y Z : C}
    [Module.Finite k (End Y)] [IsLocalRing (End Y)]
    [IsArtinianRing (End Y)]
    {f : X ⟶ Y} {g : Y ⟶ Z}
    (D : BGRSZeroPairRadicalSandwich f g)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) Y)
    (hzero : f ≫ g = 0) :
    (f ≫ P.tau.asHom) ≫ g ≠ 0 := by
  let E : BGRSZeroPairRadicalSandwich f g :=
    { left := f
      right := g
      left_unitRayEquivalent := ⟨Iso.refl X, Iso.refl Y, by simp⟩
      right_unitRayEquivalent := ⟨Iso.refl Y, Iso.refl Z, by simp⟩
      comp_eq_zero := hzero
      nonzero_sandwich :=
        hasNonzeroJacobsonSandwich_of_unitRayEquivalent
          ((unitRaySetoid X Y).symm D.left_unitRayEquivalent)
          ((unitRaySetoid Y Z).symm D.right_unitRayEquivalent)
          D.nonzero_sandwich }
  change (E.left ≫ P.tau.asHom) ≫ E.right ≠ 0
  intro htau
  have hsquare : LeftJacobsonSquareAnnihilates E.left ∨
      RightJacobsonSquareAnnihilates E.right :=
    HasRoiterTransitSquareAlternative.square_alternative
      (k := k) (C := C) E.left E.right
        E.left_not_allowsCotransit E.right_not_allowsTransit
  have hpoly : ∀ p : Polynomial k,
      (E.left ≫ (Polynomial.aeval P.tau p).asHom) ≫ E.right = 0 := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        rw [map_add]
        change (E.left ≫
          ((Polynomial.aeval P.tau p).asHom +
            (Polynomial.aeval P.tau q).asHom)) ≫ E.right = 0
        rw [Preadditive.comp_add, Preadditive.add_comp, hp, hq, add_zero]
    | monomial n c =>
        rcases n with _ | n
        · have hscalarHom : (algebraMap k (End Y) c).asHom =
              c • (𝟙 Y) := by
            change (c • (1 : End Y)).asHom = c • (𝟙 Y)
            rfl
          rw [Polynomial.aeval_monomial, pow_zero, mul_one, hscalarHom]
          simp [E.comp_eq_zero]
        · rcases n with _ | n
          · have hscalarHom : (algebraMap k (End Y) c).asHom =
                c • (𝟙 Y) := by
              change (c • (1 : End Y)).asHom = c • (𝟙 Y)
              rfl
            rw [Polynomial.aeval_monomial, zero_add, pow_one]
            change (E.left ≫
              (P.tau.asHom ≫ (algebraMap k (End Y) c).asHom)) ≫
                E.right = 0
            rw [hscalarHom]
            simpa [Category.assoc] using
              congrArg (fun z : (X ⟶ Z) ↦ c • z) htau
          · let J : Ideal (End Y) := Ring.jacobson (End Y)
            have hpow : P.tau ^ (Nat.succ (Nat.succ n)) ∈ J ^ 2 := by
              have htau2 : P.tau ^ 2 ∈ J ^ 2 :=
                Ideal.pow_mem_pow P.mem_jacobson 2
              have hmul : P.tau ^ n * P.tau ^ 2 ∈ J ^ 2 :=
                (J ^ 2).mul_mem_left (P.tau ^ n) htau2
              simpa only [J, ← pow_add, Nat.add_eq, Nat.add_comm,
                Nat.add_left_comm, Nat.add_assoc] using hmul
            have hmonomial : Polynomial.aeval P.tau
                ((Polynomial.monomial (Nat.succ (Nat.succ n))) c) ∈
                  J ^ 2 := by
              rw [Polynomial.aeval_monomial]
              exact (J ^ 2).mul_mem_left
                (algebraMap k (End Y) c) hpow
            rcases hsquare with hleft | hright
            · rw [hleft _ hmonomial]
              exact CategoryTheory.Limits.zero_comp
            · rw [Category.assoc, hright _ hmonomial]
              exact CategoryTheory.Limits.comp_zero
  rcases E.nonzero_sandwich with ⟨rho, hrho⟩
  obtain ⟨p, hp⟩ := P.exists_aeval_eq rho.1
  apply hrho
  rw [← hp]
  exact hpoly p

omit [HasBGRSPairDichotomy C] [HasWellDefinedBGRSRayProduct C]
  [HasBGRSDistributiveHomStructure k C] in
/-- The nonzero first-radical sandwich is unchanged by inserting a
`1 - Jacobson` factor immediately after `tau`.  The correction contains two
middle-radical factors and is therefore killed by Roiter's square
alternative. -/
theorem tau_one_sub_jacobson_sandwich_ne_zero_of_zeroPairRadicalSandwich
    {X Y Z : C}
    [Module.Finite k (End Y)] [IsLocalRing (End Y)]
    [IsArtinianRing (End Y)]
    {f : X ⟶ Y} {g : Y ⟶ Z}
    (D : BGRSZeroPairRadicalSandwich f g)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) Y)
    (hzero : f ≫ g = 0)
    (j : End Y) (hj : j ∈ Ring.jacobson (End Y)) :
    ((f ≫ P.tau.asHom) ≫ (1 - j).asHom) ≫ g ≠ 0 := by
  let E : BGRSZeroPairRadicalSandwich f g :=
    { left := f
      right := g
      left_unitRayEquivalent := ⟨Iso.refl X, Iso.refl Y, by simp⟩
      right_unitRayEquivalent := ⟨Iso.refl Y, Iso.refl Z, by simp⟩
      comp_eq_zero := hzero
      nonzero_sandwich :=
        hasNonzeroJacobsonSandwich_of_unitRayEquivalent
          ((unitRaySetoid X Y).symm D.left_unitRayEquivalent)
          ((unitRaySetoid Y Z).symm D.right_unitRayEquivalent)
          D.nonzero_sandwich }
  have hsquare : LeftJacobsonSquareAnnihilates E.left ∨
      RightJacobsonSquareAnnihilates E.right :=
    HasRoiterTransitSquareAlternative.square_alternative
      (k := k) (C := C) E.left E.right
        E.left_not_allowsCotransit E.right_not_allowsTransit
  have htauj : End.of (P.tau.asHom ≫ j.asHom) ∈
      (Ring.jacobson (End Y)) ^ 2 := by
    rw [show (2 : ℕ) = 1 + 1 by omega,
      Ideal.IsTwoSided.pow_add, Submodule.pow_one]
    change j * P.tau ∈
      Ring.jacobson (End Y) * Ring.jacobson (End Y)
    exact Ideal.mul_mem_mul hj P.mem_jacobson
  have hcorrection : (f ≫ (P.tau.asHom ≫ j.asHom)) ≫ g = 0 := by
    change (f ≫ (End.of (P.tau.asHom ≫ j.asHom)).asHom) ≫ g = 0
    rcases hsquare with hleft | hright
    · rw [hleft _ htauj]
      exact CategoryTheory.Limits.zero_comp
    · rw [Category.assoc, hright _ htauj]
      exact CategoryTheory.Limits.comp_zero
  have hbase : (f ≫ P.tau.asHom) ≫ g ≠ 0 :=
    tau_sandwich_ne_zero_of_zeroPairRadicalSandwich D P hzero
  intro htwist
  apply hbase
  have hcorrection' : ((f ≫ P.tau.asHom) ≫ j.asHom) ≫ g = 0 := by
    simpa only [Category.assoc] using hcorrection
  change ((f ≫ P.tau.asHom) ≫ ((𝟙 Y) - j.asHom)) ≫ g = 0 at htwist
  rw [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp,
    hcorrection', sub_zero] at htwist
  exact htwist

omit [HasBGRSPairDichotomy C] [HasWellDefinedBGRSRayProduct C]
  [HasBGRSDistributiveHomStructure k C] in
/-- An endpoint-radical perturbation, a term through a second zero branch,
and an error one `tau`-degree deeper cannot sum to the first-radical branch
path.  This is the linear separation form of the Figure-16 no-factor
argument needed after lifting from the exact quotient. -/
theorem branch_tau_not_endpoint_cross_add_deeper
    {X W Y Z : C}
    [IsLocalRing (End X)] [IsArtinianRing (End X)]
    [Module.Finite k (End Y)] [IsLocalRing (End Y)]
    [IsArtinianRing (End Y)]
    {f : X ⟶ Y} {h : W ⟶ Y} {g : Y ⟶ Z}
    (D : BGRSZeroPairRadicalSandwich f g)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) Y)
    (hfT : LargeIndecomposable.AllowsTransit f)
    (hfg : f ≫ g = 0) (hhg : h ≫ g = 0)
    (c : End X) (hc : c ∈ Ring.jacobson (End X))
    (d : End Y) (hd : d ∈ Ring.jacobson (End Y))
    (a : End X) (mu : X ⟶ W) (z : X ⟶ Y)
    (hz : z ∈ twoSidedEndomorphismSpan k
      (f ≫ (P.tau ^ 2).asHom)) :
    (c.asHom ≫ (f ≫ P.tau.asHom) +
        (f ≫ P.tau.asHom) ≫ d.asHom) +
          a.asHom ≫ f + mu ≫ h + z ≠
      f ≫ P.tau.asHom := by
  have hfTau : f ≫ P.tau.asHom ≠ 0 := by
    intro hzero
    exact (tau_sandwich_ne_zero_of_zeroPairRadicalSandwich D P hfg)
      (by rw [hzero]; exact CategoryTheory.Limits.zero_comp)
  have hf : f ≠ 0 := by
    intro hzero
    apply hfTau
    rw [hzero]
    exact CategoryTheory.Limits.zero_comp
  obtain ⟨q, hcq⟩ := hfT c
  have hq : q ∈ Ring.jacobson (End Y) :=
    LargeIndecomposable.ClosedZigzagTransfer.target_mem_jacobson_of_source_mem_and_transfer
      hf c q hc hcq
  have hdeepT : LargeIndecomposable.AllowsTransit
      (f ≫ (P.tau ^ 2).asHom) :=
    hfT.comp (P.power_allowsTransit 2)
  obtain ⟨b, hzb⟩ :=
    LargeIndecomposable.exists_comp_of_mem_span_of_allowsTransit hdeepT hz
  let j : End Y := q + d + b * P.tau
  have hj : j ∈ Ring.jacobson (End Y) := by
    exact (Ring.jacobson (End Y)).add_mem
      ((Ring.jacobson (End Y)).add_mem hq hd)
      ((Ring.jacobson (End Y)).mul_mem_left b P.mem_jacobson)
  have hcLanding : c.asHom ≫ (f ≫ P.tau.asHom) =
      (f ≫ P.tau.asHom) ≫ q.asHom := by
    have hcomm := congrArg End.asHom (P.mul_comm q P.tau)
    calc
      c.asHom ≫ (f ≫ P.tau.asHom) =
          (c.asHom ≫ f) ≫ P.tau.asHom := by rw [Category.assoc]
      _ = (f ≫ q.asHom) ≫ P.tau.asHom := by rw [hcq]
      _ = (f ≫ P.tau.asHom) ≫ q.asHom := by
        simpa only [End.mul_def, Category.assoc] using
          congrArg (fun r : End Y ↦ f ≫ r.asHom) hcomm.symm
  have hzLanding : z =
      (f ≫ P.tau.asHom) ≫ (b * P.tau).asHom := by
    calc
      z = (f ≫ (P.tau ^ 2).asHom) ≫ b.asHom := hzb
      _ = (f ≫ P.tau.asHom) ≫ (b * P.tau).asHom := by
        simp only [pow_two, End.mul_def, Category.assoc]
  intro heq
  have hcrossEq : a.asHom ≫ f + mu ≫ h =
      (f ≫ P.tau.asHom) ≫ (1 - j).asHom := by
    have hsum :
        (c.asHom ≫ (f ≫ P.tau.asHom) +
            (f ≫ P.tau.asHom) ≫ d.asHom) + z =
          (f ≫ P.tau.asHom) ≫ j.asHom := by
      rw [hcLanding, hzLanding]
      dsimp only [j]
      change ((f ≫ P.tau.asHom) ≫ q.asHom +
          (f ≫ P.tau.asHom) ≫ d.asHom) +
            (f ≫ P.tau.asHom) ≫ (b * P.tau).asHom =
        (f ≫ P.tau.asHom) ≫
          (q.asHom + d.asHom + (b * P.tau).asHom)
      rw [Preadditive.comp_add, Preadditive.comp_add]
    change ((c.asHom ≫ (f ≫ P.tau.asHom) +
        (f ≫ P.tau.asHom) ≫ d.asHom) +
          a.asHom ≫ f + mu ≫ h) + z =
      f ≫ P.tau.asHom at heq
    rw [show ((c.asHom ≫ (f ≫ P.tau.asHom) +
        (f ≫ P.tau.asHom) ≫ d.asHom) +
          a.asHom ≫ f + mu ≫ h) + z =
        ((c.asHom ≫ (f ≫ P.tau.asHom) +
          (f ≫ P.tau.asHom) ≫ d.asHom) + z) +
            (a.asHom ≫ f + mu ≫ h) by abel,
      hsum] at heq
    rw [show (1 - j).asHom = (𝟙 Y) - j.asHom by rfl,
      Preadditive.comp_sub, Category.comp_id]
    change a.asHom ≫ f + mu ≫ h =
      f ≫ P.tau.asHom - (f ≫ P.tau.asHom) ≫ j.asHom
    apply (eq_sub_iff_add_eq).2
    rw [add_comm]
    exact heq
  have hleftZero : (a.asHom ≫ f + mu ≫ h) ≫ g = 0 := by
    rw [Preadditive.add_comp, Category.assoc, hfg, Category.assoc, hhg]
    simp
  apply tau_one_sub_jacobson_sandwich_ne_zero_of_zeroPairRadicalSandwich
    D P hfg j hj
  rw [← hcrossEq, hleftZero]

omit [HasBGRSPairDichotomy C] [HasWellDefinedBGRSRayProduct C]
  [HasBGRSDistributiveHomStructure k C] in
/-- First no-factor consequence used by Figure 16: if both branches compose
to zero with `alpha`, then `beta * tau` cannot factor through `gamma`.
This is the ordinary-projective-category translation of BGRS's assertion
that `gamma` is not a left factor of `tau beta`. -/
theorem postcompose_tau_not_factors_through_zeroBranch
    {B G M A : C}
    [Module.Finite k (End M)] [IsLocalRing (End M)]
    [IsArtinianRing (End M)]
    (beta : B ⟶ M) (gamma : G ⟶ M) (alpha : M ⟶ A)
    (D : BGRSZeroPairRadicalSandwich beta alpha)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) M)
    (hbeta : beta ≫ alpha = 0) (hgamma : gamma ≫ alpha = 0) :
    ¬∃ mu : B ⟶ G, beta ≫ P.tau.asHom = mu ≫ gamma := by
  rintro ⟨mu, hmu⟩
  apply tau_sandwich_ne_zero_of_zeroPairRadicalSandwich D P hbeta
  calc
    (beta ≫ P.tau.asHom) ≫ alpha = (mu ≫ gamma) ≫ alpha := by
      rw [hmu]
    _ = mu ≫ (gamma ≫ alpha) := by rw [Category.assoc]
    _ = 0 := by rw [hgamma]; exact CategoryTheory.Limits.comp_zero

omit [HasBGRSDistributiveHomStructure k C] in
/-- The first printed Figure-16 no-factor statement for common-first
singular pairs, with the second branch transported to the common literal
middle object. -/
theorem CommonFirstZeroRepresentatives.beta_tau_not_factorsThrough_gamma
    {p q : SingularPair (C := C)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    [Module.Finite k (End p.1.middle.obj.as)]
    [IsLocalRing (End p.1.middle.obj.as)]
    [IsArtinianRing (End p.1.middle.obj.as)]
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) p.1.firstArrow.target.obj.as) :
    ¬∃ mu : p.1.secondArrow.target.obj.as ⟶
        q.1.secondArrow.target.obj.as,
      D.beta.hom ≫ P.tau.asHom = mu ≫ D.alignedGamma := by
  obtain ⟨S⟩ := nonempty_zeroPairRadicalSandwich p D.pZero
  apply postcompose_tau_not_factors_through_zeroBranch
    (M := p.1.middle.obj.as)
    D.beta.hom D.alignedGamma D.alpha.hom S P
      D.beta_alpha_zero D.alignedGamma_alpha_zero

omit [HasBGRSDistributiveHomStructure k C] in
/-- The symmetric printed Figure-16 no-factor statement: the aligned
`gamma * tau` cannot factor through `beta`. -/
theorem CommonFirstZeroRepresentatives.gamma_tau_not_factorsThrough_beta
    {p q : SingularPair (C := C)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    [Module.Finite k (End p.1.middle.obj.as)]
    [IsLocalRing (End p.1.middle.obj.as)]
    [IsArtinianRing (End p.1.middle.obj.as)]
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) p.1.firstArrow.target.obj.as) :
    ¬∃ mu : q.1.secondArrow.target.obj.as ⟶
        p.1.secondArrow.target.obj.as,
      D.alignedGamma ≫ P.tau.asHom = mu ≫ D.beta.hom := by
  obtain ⟨S⟩ := D.nonempty_alignedGammaAlphaRadicalSandwich
  apply postcompose_tau_not_factors_through_zeroBranch
    (M := p.1.middle.obj.as)
    D.alignedGamma D.beta.hom D.alpha.hom S P
      D.alignedGamma_alpha_zero D.beta_alpha_zero

/-- The first nonzero threefold composite killed by the Figure-16 quotient. -/
def CommonFirstZeroRepresentatives.betaTauAlpha
    {p q : SingularPair (C := C)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) p.1.firstArrow.target.obj.as) :
    p.1.secondArrow.target.obj.as ⟶ p.1.firstArrow.source.obj.as :=
  (D.beta.hom ≫ P.tau.asHom) ≫ D.alpha.hom

/-- The second nonzero threefold composite killed by the Figure-16 quotient. -/
def CommonFirstZeroRepresentatives.gammaTauAlpha
    {p q : SingularPair (C := C)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) p.1.firstArrow.target.obj.as) :
    q.1.secondArrow.target.obj.as ⟶ p.1.firstArrow.source.obj.as :=
  (D.alignedGamma ≫ P.tau.asHom) ≫ D.alpha.hom

omit [HasBGRSDistributiveHomStructure k C] in
theorem CommonFirstZeroRepresentatives.betaTauAlpha_ne_zero
    {p q : SingularPair (C := C)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    [Module.Finite k (End p.1.middle.obj.as)]
    [IsLocalRing (End p.1.middle.obj.as)]
    [IsArtinianRing (End p.1.middle.obj.as)]
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) p.1.firstArrow.target.obj.as) :
    D.betaTauAlpha P ≠ 0 := by
  obtain ⟨S⟩ := nonempty_zeroPairRadicalSandwich p D.pZero
  exact tau_sandwich_ne_zero_of_zeroPairRadicalSandwich
    (Y := p.1.middle.obj.as) S P D.beta_alpha_zero

omit [HasBGRSDistributiveHomStructure k C] in
theorem CommonFirstZeroRepresentatives.gammaTauAlpha_ne_zero
    {p q : SingularPair (C := C)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    [Module.Finite k (End p.1.middle.obj.as)]
    [IsLocalRing (End p.1.middle.obj.as)]
    [IsArtinianRing (End p.1.middle.obj.as)]
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) p.1.firstArrow.target.obj.as) :
    D.gammaTauAlpha P ≠ 0 := by
  obtain ⟨S⟩ := D.nonempty_alignedGammaAlphaRadicalSandwich
  exact tau_sandwich_ne_zero_of_zeroPairRadicalSandwich
    (Y := p.1.middle.obj.as) S P D.alignedGamma_alpha_zero

end TauNoFactor

omit [HasBGRSDistributiveHomStructure k C] in
/-- Occurrence-sensitive ambient Figure-16 diagram attached to a common-first
singular-pair configuration.  Both center occurrences map to the common
middle object, both beta leaves use `beta`, both gamma leaves use the aligned
`gamma`, and the central edge is the radical parameter `tau`. -/
def CommonFirstZeroRepresentatives.figure16AmbientData
    {p q : SingularPair (C := C)}
    {hfirst : p.1.firstArrow = q.1.firstArrow}
    (D : CommonFirstZeroRepresentatives p q hfirst)
    (P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) p.1.firstArrow.target.obj.as) :
    LargeIndecomposable.CriticalSingularFigure16.DiagramData (C := C) where
  object
    | .upperCenter | .lowerCenter => p.1.firstArrow.target.obj.as
    | .upperBeta | .lowerBeta => p.1.secondArrow.target.obj.as
    | .upperGamma | .lowerGamma => q.1.secondArrow.target.obj.as
  arrow := by
    intro a b e
    cases e with
    | tau => exact P.tau.asHom
    | betaUpper => exact D.beta.hom
    | gammaUpper => exact D.alignedGamma
    | betaLower => exact D.beta.hom
    | gammaLower => exact D.alignedGamma

theorem zeroRepresentatives_second_not_allowsCotransit
    {p : SingularPair (C := C)} (R : ZeroRepresentatives p) :
    ¬AllowsCotransit R.second.hom := by
  obtain ⟨D⟩ := nonempty_zeroPairRadicalSandwich p R
  intro hR
  exact D.left_not_allowsCotransit
    (hR.of_unitRayEquivalent D.left_unitRayEquivalent)

theorem zeroRepresentatives_first_not_allowsTransit
    {p : SingularPair (C := C)} (R : ZeroRepresentatives p) :
    ¬AllowsTransit R.first.hom := by
  obtain ⟨D⟩ := nonempty_zeroPairRadicalSandwich p R
  intro hR
  exact D.right_not_allowsTransit
    (hR.of_unitRayEquivalent D.right_unitRayEquivalent)

include k

theorem zeroRepresentatives_second_allowsTransit
    {p : SingularPair (C := C)} (R : ZeroRepresentatives p) :
    AllowsTransit R.second.hom :=
  (HasBGRSDistributiveHomStructure.transit_or_cotransit
    (k := k) (C := C) R.second.hom).resolve_right
      (zeroRepresentatives_second_not_allowsCotransit R)

theorem zeroRepresentatives_first_allowsCotransit
    {p : SingularPair (C := C)} (R : ZeroRepresentatives p) :
    AllowsCotransit R.first.hom :=
  (HasBGRSDistributiveHomStructure.transit_or_cotransit
    (k := k) (C := C) R.first.hom).resolve_left
      (zeroRepresentatives_first_not_allowsTransit R)

theorem singularPair_secondArrow_allowsTransit
    (p : SingularPair (C := C)) :
    ArrowAllowsTransit p.1.secondArrow := by
  let R := chosenZeroRepresentatives p
  have hR : AllowsTransit R.second.hom :=
    zeroRepresentatives_second_allowsTransit (k := k) R
  apply hR.of_unitRayEquivalent
  exact (unitRay_eq_iff _ _).1
    (R.second.unitRay_hom.trans
      (defaultRepresentative p.1.secondArrow).unitRay_hom.symm)

omit k [Field k] [Linear k C] [HasBGRSDistributiveHomStructure k C] in
theorem singularPair_firstArrow_not_allowsTransit
    (p : SingularPair (C := C)) :
    ¬ArrowAllowsTransit p.1.firstArrow := by
  let R := chosenZeroRepresentatives p
  intro htransit
  apply zeroRepresentatives_first_not_allowsTransit R
  apply htransit.of_unitRayEquivalent
  exact (unitRay_eq_iff _ _).1
    ((defaultRepresentative p.1.firstArrow).unitRay_hom.trans
      R.first.unitRay_hom.symm)

/-- Opposite-position sharing is impossible: the first arrow of a singular
pair cannot be the second arrow of another singular pair. -/
theorem singularPair_firstArrow_ne_secondArrow
    (p q : SingularPair (C := C)) :
    p.1.firstArrow ≠ q.1.secondArrow := by
  intro h
  apply singularPair_firstArrow_not_allowsTransit p
  have hproperty : ArrowAllowsTransit p.1.firstArrow =
      ArrowAllowsTransit q.1.secondArrow :=
    congrArg (fun a : Arrow (C := C) ↦ ArrowAllowsTransit a) h
  exact hproperty.mpr (singularPair_secondArrow_allowsTransit (k := k) q)

/-- The symmetric opposite-position exclusion. -/
theorem singularPair_secondArrow_ne_firstArrow
    (p q : SingularPair (C := C)) :
    p.1.secondArrow ≠ q.1.firstArrow := by
  intro h
  exact singularPair_firstArrow_ne_secondArrow (k := k) q p h.symm

/-- After the orientation lemma, Figure-16 disjointness reduces exactly to
the two same-position sharing cases. -/
theorem singularPair_eq_of_samePosition_disjoint
    (hfirst : ∀ p q : SingularPair (C := C),
      p.1.firstArrow = q.1.firstArrow → p = q)
    (hsecond : ∀ p q : SingularPair (C := C),
      p.1.secondArrow = q.1.secondArrow → p = q)
    (p q : SingularPair (C := C))
    (hshare : p.1.firstArrow = q.1.firstArrow ∨
      p.1.firstArrow = q.1.secondArrow ∨
      p.1.secondArrow = q.1.firstArrow ∨
      p.1.secondArrow = q.1.secondArrow) :
    p = q := by
  rcases hshare with h | h | h | h
  · exact hfirst p q h
  · exact False.elim (singularPair_firstArrow_ne_secondArrow
      (k := k) p q h)
  · exact False.elim (singularPair_secondArrow_ne_firstArrow
      (k := k) p q h)
  · exact hsecond p q h

end LargeIndecomposable.CriticalSingularFigure16Pairs
