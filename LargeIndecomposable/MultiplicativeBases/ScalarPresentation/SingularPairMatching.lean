module

public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.SingularPath

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace LargeIndecomposable
namespace SingularPairNormalization
namespace MatchingChoice

attribute [local instance] Classical.propDecidable

universe u v w

variable {E : Type u} {P : Type v} (R : E → Type w)
variable (left right : P → E)

/-- Pairs incident with an element of the ground type. -/
def At (e : E) := {p : P // left p = e ∨ right p = e}

/-- A disjoint family of pairs has at most one pair incident with each ground
element. -/
theorem at_subsingleton
    (hdisjoint : ∀ p q : P,
      left p = left q ∨ left p = right q ∨
        right p = left q ∨ right p = right q → p = q)
    (e : E) : Subsingleton (At left right e) where
  allEq p q := by
    apply Subtype.ext
    apply hdisjoint p.1 q.1
    rcases p.2 with hp | hp <;> rcases q.2 with hq | hq
    · exact Or.inl (hp.trans hq.symm)
    · exact Or.inr (Or.inl (hp.trans hq.symm))
    · exact Or.inr (Or.inr (Or.inl (hp.trans hq.symm)))
    · exact Or.inr (Or.inr (Or.inr (hp.trans hq.symm)))

/-- The prescribed value of the unique incident pair at a ground element. -/
def atValue
    (leftValue : ∀ p : P, R (left p))
    (rightValue : ∀ p : P, R (right p))
    (e : E) (p : At left right e) : R e :=
  if h : left p.1 = e then
    h ▸ leftValue p.1
  else
    (Or.resolve_left p.2 h) ▸ rightValue p.1

/-- Extend compatible prescriptions on a matching to a total dependent
choice, using the supplied default off the matching. -/
def choose
    (default : ∀ e : E, R e)
    (leftValue : ∀ p : P, R (left p))
    (rightValue : ∀ p : P, R (right p))
    (e : E) : R e :=
  if h : Nonempty (At left right e) then
    atValue R left right leftValue rightValue e (Classical.choice h)
  else
    default e

theorem choose_left
    (default : ∀ e : E, R e)
    (leftValue : ∀ p : P, R (left p))
    (rightValue : ∀ p : P, R (right p))
    (hdisjoint : ∀ p q : P,
      left p = left q ∨ left p = right q ∨
        right p = left q ∨ right p = right q → p = q)
    (p : P) :
    choose R left right default leftValue rightValue (left p) =
      leftValue p := by
  let pe : At left right (left p) := ⟨p, Or.inl rfl⟩
  have hnonempty : Nonempty (At left right (left p)) := ⟨pe⟩
  rw [choose, dif_pos hnonempty]
  haveI := at_subsingleton left right hdisjoint (left p)
  have heq : Classical.choice hnonempty = pe := Subsingleton.elim _ _
  rw [heq]
  simp [atValue, pe]

theorem choose_right
    (default : ∀ e : E, R e)
    (leftValue : ∀ p : P, R (left p))
    (rightValue : ∀ p : P, R (right p))
    (hne : ∀ p : P, left p ≠ right p)
    (hdisjoint : ∀ p q : P,
      left p = left q ∨ left p = right q ∨
        right p = left q ∨ right p = right q → p = q)
    (p : P) :
    choose R left right default leftValue rightValue (right p) =
      rightValue p := by
  let pe : At left right (right p) := ⟨p, Or.inr rfl⟩
  have hnonempty : Nonempty (At left right (right p)) := ⟨pe⟩
  rw [choose, dif_pos hnonempty]
  haveI := at_subsingleton left right hdisjoint (right p)
  have heq : Classical.choice hnonempty = pe := Subsingleton.elim _ _
  rw [heq]
  simp [atValue, pe, hne p]

end MatchingChoice
end SingularPairNormalization
end LargeIndecomposable

open CategoryTheory

namespace LargeIndecomposable.SingularPairNormalization

universe u' v'

variable {C : Type u'} [Category.{v'} C] [Preadditive C]
variable [HasBGRSPairDichotomy C]

abbrev Vertex := RayVertex (BGRSRayCategory C)

/-- A dependent package for one arrow of the reversed irreducible ray
quiver. -/
structure Arrow where
  source : Vertex (C := C)
  target : Vertex (C := C)
  hom : source ⟶ target

/-- An ordinary source-category representative of a packaged ray arrow. -/
structure Representative (a : Arrow (C := C)) where
  hom : a.target.obj.as ⟶ a.source.obj.as
  unitRay_hom : unitRay hom = a.hom.1

/-- The quotient's arbitrary representative supplies a default at every
arrow. -/
def defaultRepresentative (a : Arrow (C := C)) : Representative a where
  hom := a.hom.1.out
  unitRay_hom := unitRay_out a.hom.1

/-- Two consecutive arrows of the reversed ray quiver. -/
structure ComposablePair where
  source : Vertex (C := C)
  middle : Vertex (C := C)
  target : Vertex (C := C)
  first : source ⟶ middle
  second : middle ⟶ target

def ComposablePair.firstArrow (p : ComposablePair (C := C)) :
    Arrow (C := C) :=
  ⟨p.source, p.middle, p.first⟩

def ComposablePair.secondArrow (p : ComposablePair (C := C)) :
    Arrow (C := C) :=
  ⟨p.middle, p.target, p.second⟩

def ComposablePair.path (p : ComposablePair (C := C)) :
    Quiver.Path p.source p.target :=
  p.first.toPath.comp p.second.toPath

/-- A length-two BGRS singular path: its ray product is zero, while some
ordinary choices of representatives have nonzero composite. -/
def ComposablePair.IsSingular (p : ComposablePair (C := C)) : Prop :=
  rayPathMap p.path = 0 ∧
    ∃ (rfirst : Representative p.firstArrow)
      (rsecond : Representative p.secondArrow),
      rsecond.hom ≫ rfirst.hom ≠ 0

abbrev SingularPair :=
  {p : ComposablePair (C := C) // p.IsSingular}

/-- Local zero representatives supplied by the BGRS pair dichotomy. -/
structure ZeroRepresentatives (p : SingularPair (C := C)) where
  first : Representative p.1.firstArrow
  second : Representative p.1.secondArrow
  comp_zero : second.hom ≫ first.hom = 0

private theorem bgrsRayComp_eq_zero_iff_exists_representatives_comp_eq_zero
    {X Y Z : C} (r : UnitRayOrbit X Y) (s : UnitRayOrbit Y Z) :
    bgrsRayComp r s = 0 ↔
      ∃ f : X ⟶ Y, ∃ g : Y ⟶ Z,
        unitRay f = r ∧ unitRay g = s ∧ f ≫ g = 0 := by
  constructor
  · intro hrs
    induction r using Quotient.inductionOn with
    | _ f =>
      induction s using Quotient.inductionOn with
      | _ g =>
        have hspecial : IsBGRSSpecialZero f g := by
          by_contra hnot
          have hfg : f ≫ g ≠ 0 :=
            (HasBGRSPairDichotomy.pair f g).nonzero_common_ray_of_not_special
              hnot f g
              ((unitRay_eq_iff f f).1 rfl)
              ((unitRay_eq_iff g g).1 rfl) |>.1
          have hproductZero : bgrsRayRepresentativeProduct f g = 0 := by
            exact (unitRay_eq_zero_iff _).1 hrs
          rw [bgrsRayRepresentativeProduct_eq_comp_of_not_special hnot]
            at hproductZero
          exact hfg hproductZero
        obtain ⟨f', g', hf', hg', hzero⟩ :=
          (HasBGRSPairDichotomy.pair f g).zero_representatives_of_special
            hspecial
        exact ⟨f', g', ((unitRay_eq_iff f f').2 hf').symm,
          ((unitRay_eq_iff g g').2 hg').symm, hzero⟩
  · rintro ⟨f, g, hf, hg, hzero⟩
    rw [← hf, ← hg]
    have hspecial : IsBGRSSpecialZero f g := by
      refine ⟨⟨0, (Ring.jacobson (End Y)).zero_mem⟩, ?_⟩
      change f ≫ g = (f ≫ (0 : Y ⟶ Y)) ≫ g
      simp [hzero]
    change unitRay (bgrsRayRepresentativeProduct f g) = unitRay 0
    rw [bgrsRayRepresentativeProduct_eq_zero_of_special hspecial]

theorem exists_zeroRepresentatives (p : SingularPair (C := C)) :
    Nonempty (ZeroRepresentatives p) := by
  have hcomp : p.1.second.1 ≫ p.1.first.1 = 0 := by
    simpa only [ComposablePair.path, rayPathMap,
      LinearPathCategory.pathMap_comp, rayPathMap_toPath,
      rayArrowMorphism] using p.2.1
  change bgrsRayComp p.1.second.1 p.1.first.1 = 0 at hcomp
  obtain ⟨second, first, hsecond, hfirst, hzero⟩ :=
    (bgrsRayComp_eq_zero_iff_exists_representatives_comp_eq_zero
      p.1.second.1 p.1.first.1).1 hcomp
  exact ⟨⟨⟨first, hfirst⟩, ⟨second, hsecond⟩, hzero⟩⟩

def chosenZeroRepresentatives (p : SingularPair (C := C)) :
    ZeroRepresentatives p :=
  Classical.choice (exists_zeroRepresentatives p)

/-- The representative assignment obtained by gluing the zero choices along
a matching of singular pairs. -/
def normalizedRepresentative
    (_hdistinct : ∀ p : SingularPair (C := C),
      p.1.firstArrow ≠ p.1.secondArrow)
    (_hdisjoint : ∀ p q : SingularPair (C := C),
      p.1.firstArrow = q.1.firstArrow ∨
      p.1.firstArrow = q.1.secondArrow ∨
      p.1.secondArrow = q.1.firstArrow ∨
      p.1.secondArrow = q.1.secondArrow → p = q)
    (a : Arrow (C := C)) : Representative a :=
  MatchingChoice.choose Representative
    (fun p : SingularPair (C := C) ↦ p.1.firstArrow)
    (fun p : SingularPair (C := C) ↦ p.1.secondArrow)
    defaultRepresentative
    (fun p ↦ (chosenZeroRepresentatives p).first)
    (fun p ↦ (chosenZeroRepresentatives p).second) a

/-- The concrete global arrow lift selected by the matching construction. -/
def normalizedLift
    (hdistinct : ∀ p : SingularPair (C := C),
      p.1.firstArrow ≠ p.1.secondArrow)
    (hdisjoint : ∀ p q : SingularPair (C := C),
      p.1.firstArrow = q.1.firstArrow ∨
      p.1.firstArrow = q.1.secondArrow ∨
      p.1.secondArrow = q.1.firstArrow ∨
      p.1.secondArrow = q.1.secondArrow → p = q) :
    BGRSRayArrowLift (C := C) where
  representative {i j} a :=
    (normalizedRepresentative hdistinct hdisjoint ⟨i, j, a⟩).hom
  unitRay_representative {i j} a :=
    (normalizedRepresentative hdistinct hdisjoint ⟨i, j, a⟩).unitRay_hom

theorem normalizedRepresentative_first
    (hdistinct : ∀ p : SingularPair (C := C),
      p.1.firstArrow ≠ p.1.secondArrow)
    (hdisjoint : ∀ p q : SingularPair (C := C),
      p.1.firstArrow = q.1.firstArrow ∨
      p.1.firstArrow = q.1.secondArrow ∨
      p.1.secondArrow = q.1.firstArrow ∨
      p.1.secondArrow = q.1.secondArrow → p = q)
    (p : SingularPair (C := C)) :
    normalizedRepresentative hdistinct hdisjoint p.1.firstArrow =
      (chosenZeroRepresentatives p).first := by
  exact MatchingChoice.choose_left Representative
    (fun q : SingularPair (C := C) ↦ q.1.firstArrow)
    (fun q : SingularPair (C := C) ↦ q.1.secondArrow)
    defaultRepresentative
    (fun q ↦ (chosenZeroRepresentatives q).first)
    (fun q ↦ (chosenZeroRepresentatives q).second)
    hdisjoint p

theorem normalizedRepresentative_second
    (hdistinct : ∀ p : SingularPair (C := C),
      p.1.firstArrow ≠ p.1.secondArrow)
    (hdisjoint : ∀ p q : SingularPair (C := C),
      p.1.firstArrow = q.1.firstArrow ∨
      p.1.firstArrow = q.1.secondArrow ∨
      p.1.secondArrow = q.1.firstArrow ∨
      p.1.secondArrow = q.1.secondArrow → p = q)
    (p : SingularPair (C := C)) :
    normalizedRepresentative hdistinct hdisjoint p.1.secondArrow =
      (chosenZeroRepresentatives p).second := by
  exact MatchingChoice.choose_right Representative
    (fun q : SingularPair (C := C) ↦ q.1.firstArrow)
    (fun q : SingularPair (C := C) ↦ q.1.secondArrow)
    defaultRepresentative
    (fun q ↦ (chosenZeroRepresentatives q).first)
    (fun q ↦ (chosenZeroRepresentatives q).second)
    hdistinct hdisjoint p

/-- The concrete matching lift annihilates every singular length-two path. -/
theorem normalizedLift_path_eq_zero
    (hdistinct : ∀ p : SingularPair (C := C),
      p.1.firstArrow ≠ p.1.secondArrow)
    (hdisjoint : ∀ p q : SingularPair (C := C),
      p.1.firstArrow = q.1.firstArrow ∨
      p.1.firstArrow = q.1.secondArrow ∨
      p.1.secondArrow = q.1.firstArrow ∨
      p.1.secondArrow = q.1.secondArrow → p = q)
    (p : SingularPair (C := C)) :
    (normalizedLift hdistinct hdisjoint).pathMap p.1.path = 0 := by
  simp only [BGRSRayArrowLift.pathMap, ComposablePair.path,
    LinearPathCategory.pathMap_comp, Quiver.Hom.toPath,
    LinearPathCategory.pathMap_cons, LinearPathCategory.pathMap_nil,
    Category.comp_id, normalizedLift]
  have hfirst := congrArg Representative.hom
    (normalizedRepresentative_first hdistinct hdisjoint p)
  have hsecond := congrArg Representative.hom
    (normalizedRepresentative_second hdistinct hdisjoint p)
  simp only [ComposablePair.firstArrow] at hfirst
  simp only [ComposablePair.secondArrow] at hsecond
  rw [hfirst, hsecond]
  exact (chosenZeroRepresentatives p).comp_zero

theorem exists_normalizedLift
    (hdistinct : ∀ p : SingularPair (C := C),
      p.1.firstArrow ≠ p.1.secondArrow)
    (hdisjoint : ∀ p q : SingularPair (C := C),
      p.1.firstArrow = q.1.firstArrow ∨
      p.1.firstArrow = q.1.secondArrow ∨
      p.1.secondArrow = q.1.firstArrow ∨
      p.1.secondArrow = q.1.secondArrow → p = q) :
    ∃ L : BGRSRayArrowLift (C := C),
      ∀ p : SingularPair (C := C), L.pathMap p.1.path = 0 :=
  ⟨normalizedLift hdistinct hdisjoint,
    normalizedLift_path_eq_zero hdistinct hdisjoint⟩

/-- The existence part of the BGRS structure theorem, stated directly with
the packaged length-two singular pairs used by the matching construction. -/
def HasSingularPairFactorization : Prop :=
  ∀ {i j : Vertex (C := C)} (p : Quiver.Path i j),
    IsBGRSLiftSingularPath p →
      ∃ (q : SingularPair (C := C))
        (left : Quiver.Path i q.1.source)
        (right : Quiver.Path q.1.target j),
        p = (left.comp q.1.path).comp right

/-- The concrete matching lift annihilates every singular path once every
such path is known to contain a singular pair. -/
theorem normalizedLift_path_eq_zero_of_isLiftSingular
    (hdistinct : ∀ p : SingularPair (C := C),
      p.1.firstArrow ≠ p.1.secondArrow)
    (hdisjoint : ∀ p q : SingularPair (C := C),
      p.1.firstArrow = q.1.firstArrow ∨
      p.1.firstArrow = q.1.secondArrow ∨
      p.1.secondArrow = q.1.firstArrow ∨
      p.1.secondArrow = q.1.secondArrow → p = q)
    (hstructure : HasSingularPairFactorization (C := C))
    {i j : Vertex (C := C)} (p : Quiver.Path i j)
    (hp : IsBGRSLiftSingularPath p) :
    (normalizedLift hdistinct hdisjoint).pathMap p = 0 := by
  obtain ⟨q, left, right, rfl⟩ := hstructure p hp
  have hzero := normalizedLift_path_eq_zero hdistinct hdisjoint q
  change LinearPathCategory.pathMap (fun x ↦ x.obj.as)
    (fun {i j} (a : i ⟶ j) ↦
      (normalizedLift hdistinct hdisjoint).representative a) q.1.path = 0
    at hzero
  simp only [BGRSRayArrowLift.pathMap,
    LinearPathCategory.pathMap_comp]
  rw [hzero]
  simp

/-- The BGRS structure and disjointness theorems turn the explicit matching
lift into a presentation detecting exactly the zero paths of the ray
category. -/
theorem normalizedLift_pathMap_eq_zero_iff_rayPathMap_eq_zero
    (hdistinct : ∀ p : SingularPair (C := C),
      p.1.firstArrow ≠ p.1.secondArrow)
    (hdisjoint : ∀ p q : SingularPair (C := C),
      p.1.firstArrow = q.1.firstArrow ∨
      p.1.firstArrow = q.1.secondArrow ∨
      p.1.secondArrow = q.1.firstArrow ∨
      p.1.secondArrow = q.1.secondArrow → p = q)
    (hstructure : HasSingularPairFactorization (C := C))
    {i j : Vertex (C := C)} (p : Quiver.Path i j) :
    (normalizedLift hdistinct hdisjoint).pathMap p = 0 ↔
      rayPathMap p = 0 := by
  constructor
  · contrapose!
    exact (normalizedLift hdistinct hdisjoint).pathMap_ne_zero_of_rayPathMap_ne_zero p
  · intro hp
    by_contra hnonzero
    exact hnonzero
      (normalizedLift_path_eq_zero_of_isLiftSingular
        hdistinct hdisjoint hstructure p
        ⟨hp, normalizedLift hdistinct hdisjoint, hnonzero⟩)

theorem exists_zeroDetectingNormalizedLift
    (hdistinct : ∀ p : SingularPair (C := C),
      p.1.firstArrow ≠ p.1.secondArrow)
    (hdisjoint : ∀ p q : SingularPair (C := C),
      p.1.firstArrow = q.1.firstArrow ∨
      p.1.firstArrow = q.1.secondArrow ∨
      p.1.secondArrow = q.1.firstArrow ∨
      p.1.secondArrow = q.1.secondArrow → p = q)
    (hstructure : HasSingularPairFactorization (C := C)) :
    ∃ L : BGRSRayArrowLift (C := C),
      ∀ {i j : Vertex (C := C)} (p : Quiver.Path i j),
        L.pathMap p = 0 ↔ rayPathMap p = 0 :=
  ⟨normalizedLift hdistinct hdisjoint,
    normalizedLift_pathMap_eq_zero_iff_rayPathMap_eq_zero
      hdistinct hdisjoint hstructure⟩

end LargeIndecomposable.SingularPairNormalization
