module

public import LargeIndecomposable.RayCategories.Contours.ProperPathInterlacement
public import LargeIndecomposable.RayCategories.ClosedChains.RayCrownClosedChain
public import Mathlib.Data.Finite.Sigma

@[expose] public section

/-!
# Cancellation and ray-path interlacement

Use BGRS cancellation to show that two equal nonzero ray paths with a common
initial or final irreducible arrow are interlaced.  This is the key injection
behind the bound on the number of interlacement classes by local arrow
valency in Roiter's theorem.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v w

variable {Q : Type u} [Quiver.{v} Q]

/-- Interlacement restricted to all paths representing the same selected
nonzero contour ray as `p`. -/
def PathInterlacementRelation.relatedPathSetoid
    {R : PathContourRelation Q} (I : PathInterlacementRelation R)
    {i j : Q} (p : Quiver.Path i j) :
    Setoid {q : Quiver.Path i j // R.related p q} where
  r q r := I.interlaced q.1 r.1
  iseqv := by
    constructor
    · intro q
      exact I.refl q.1
    · intro q r hqr
      exact I.symm hqr
    · intro q r s hqr hrs
      exact I.trans hqr hrs

/-- The interlacement classes of paths representing the same selected ray. -/
abbrev RelatedPathInterlacementClass
    {R : PathContourRelation Q} (I : PathInterlacementRelation R)
    {i j : Q} (p : Quiver.Path i j) :=
  Quotient (I.relatedPathSetoid p)

/-- If a code has the property that equal codes force two representatives to
be interlaced, the number of interlacement classes is bounded by the number
of codes.  Choosing the first arrow as the code gives Roiter's local valency
bound once common-first-arrow interlacement is available. -/
theorem relatedPathInterlacementClass_card_le_of_code
    {R : PathContourRelation Q} (I : PathInterlacementRelation R)
    {i j : Q} (p : Quiver.Path i j) {A : Type w} [Finite A]
    (code : {q : Quiver.Path i j // R.related p q} → A)
    (hcode : ∀ q r, code q = code r → I.interlaced q.1 r.1) :
    Nat.card (RelatedPathInterlacementClass I p) ≤ Nat.card A := by
  let f : RelatedPathInterlacementClass I p → A := fun q ↦ code q.out
  apply Nat.card_le_card_of_injective f
  intro q r hqr
  rw [← Quotient.out_eq q, ← Quotient.out_eq r]
  exact Quotient.sound (hcode q.out r.out hqr)

/-- The same separating code proves that the interlacement quotient is a
finite type. -/
theorem relatedPathInterlacementClass_finite_of_code
    {R : PathContourRelation Q} (I : PathInterlacementRelation R)
    {i j : Q} (p : Quiver.Path i j) {A : Type w} [Finite A]
    (code : {q : Quiver.Path i j // R.related p q} → A)
    (hcode : ∀ q r, code q = code r → I.interlaced q.1 r.1) :
    Finite (RelatedPathInterlacementClass I p) := by
  let f : RelatedPathInterlacementClass I p → A := fun q ↦ code q.out
  apply Finite.of_injective f
  intro q r hqr
  rw [← Quotient.out_eq q, ← Quotient.out_eq r]
  exact Quotient.sound (hcode q.out r.out hqr)

/-- If the interlacement quotient has more than one class, a selected
self-related path has a related representative outside its class. -/
theorem exists_related_not_interlaced_of_one_lt_card
    {R : PathContourRelation Q} (I : PathInterlacementRelation R)
    {i j : Q} (p : Quiver.Path i j) (hpp : R.related p p)
    [Finite (RelatedPathInterlacementClass I p)]
    (hcard : 1 < Nat.card (RelatedPathInterlacementClass I p)) :
    ∃ q : Quiver.Path i j, R.related p q ∧ ¬I.interlaced p q := by
  let K := RelatedPathInterlacementClass I p
  let base : K := Quotient.mk'' ⟨p, hpp⟩
  letI : Fintype K := Fintype.ofFinite K
  have hcard' : 1 < Fintype.card K := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  obtain ⟨qClass, hqClass⟩ :=
    Fintype.exists_ne_of_one_lt_card hcard' base
  let q := qClass.out
  refine ⟨q.1, q.2, ?_⟩
  intro hpq
  apply hqClass
  calc
    qClass = Quotient.mk'' q := (Quotient.out_eq qClass).symm
    _ = base := Quotient.sound (I.symm hpq)

/-- An inhabited finite interlacement quotient has cardinal one exactly when
every related representative lies in the class of the selected path. -/
theorem relatedPathInterlacementClass_card_eq_one_iff
    {R : PathContourRelation Q} (I : PathInterlacementRelation R)
    {i j : Q} (p : Quiver.Path i j) (hpp : R.related p p)
    [Finite (RelatedPathInterlacementClass I p)] :
    Nat.card (RelatedPathInterlacementClass I p) = 1 ↔
      ∀ (q : Quiver.Path i j), R.related p q → I.interlaced p q := by
  constructor
  · intro hcard q hpq
    have hsub : Subsingleton (RelatedPathInterlacementClass I p) :=
      (Nat.card_eq_one_iff_unique.mp hcard).1
    exact Quotient.exact (hsub.elim
      (Quotient.mk'' ⟨p, hpp⟩) (Quotient.mk'' ⟨q, hpq⟩))
  · intro hone
    apply Nat.card_eq_one_iff_unique.mpr
    constructor
    · constructor
      intro q r
      rw [← Quotient.out_eq q, ← Quotient.out_eq r]
      apply Quotient.sound
      exact I.trans (I.symm (hone q.out.1 q.out.2))
        (hone r.out.1 r.out.2)
    · exact ⟨Quotient.mk'' ⟨p, hpp⟩⟩

/-- If a related-path quotient has exactly two interlacement classes and
`p,q` represent the two distinct classes, every related path is interlaced
with `p` or with `q`. -/
theorem interlaced_with_first_or_second_of_card_eq_two
    {R : PathContourRelation Q} (I : PathInterlacementRelation R)
    {i j : Q} (p : Quiver.Path i j) (hpp : R.related p p)
    [Finite (RelatedPathInterlacementClass I p)]
    (hcard : Nat.card (RelatedPathInterlacementClass I p) = 2)
    (q : Quiver.Path i j) (hpq : R.related p q)
    (hpqNot : ¬I.interlaced p q)
    (r : Quiver.Path i j) (hpr : R.related p r) :
    I.interlaced p r ∨ I.interlaced q r := by
  let K := RelatedPathInterlacementClass I p
  let base : K := Quotient.mk'' ⟨p, hpp⟩
  let qClass : K := Quotient.mk'' ⟨q, hpq⟩
  let rClass : K := Quotient.mk'' ⟨r, hpr⟩
  have hqNe : qClass ≠ base := by
    intro hqb
    apply hpqNot
    exact I.symm (Quotient.exact hqb)
  obtain ⟨other, hother, hunique⟩ :=
    (Nat.card_eq_two_iff' base).1 hcard
  have hqOther : qClass = other := hunique qClass hqNe
  by_cases hrBase : rClass = base
  · exact Or.inl (I.symm (Quotient.exact hrBase))
  · have hrOther : rClass = other := hunique rClass hrBase
    exact Or.inr (Quotient.exact (hqOther.trans hrOther.symm))

/-- If a related-path quotient has exactly three interlacement classes and
`p,q,r` represent three pairwise distinct classes, every related path is
interlaced with one of those representatives. -/
theorem interlaced_with_first_or_second_or_third_of_card_eq_three
    {R : PathContourRelation Q} (I : PathInterlacementRelation R)
    {i j : Q} (p : Quiver.Path i j) (hpp : R.related p p)
    [Finite (RelatedPathInterlacementClass I p)]
    (hcard : Nat.card (RelatedPathInterlacementClass I p) = 3)
    (q r : Quiver.Path i j) (hpq : R.related p q)
    (hpr : R.related p r)
    (hpqNot : ¬I.interlaced p q) (hprNot : ¬I.interlaced p r)
    (hqrNot : ¬I.interlaced q r)
    (s : Quiver.Path i j) (hps : R.related p s) :
    I.interlaced p s ∨ I.interlaced q s ∨ I.interlaced r s := by
  classical
  let K := RelatedPathInterlacementClass I p
  let base : K := Quotient.mk'' ⟨p, hpp⟩
  let qClass : K := Quotient.mk'' ⟨q, hpq⟩
  let rClass : K := Quotient.mk'' ⟨r, hpr⟩
  let sClass : K := Quotient.mk'' ⟨s, hps⟩
  have hqNeBase : qClass ≠ base := by
    intro hqb
    exact hpqNot (I.symm (Quotient.exact hqb))
  have hrNeBase : rClass ≠ base := by
    intro hrb
    exact hprNot (I.symm (Quotient.exact hrb))
  have hqNeR : qClass ≠ rClass := by
    intro hqr
    exact hqrNot (Quotient.exact hqr)
  letI : Fintype K := Fintype.ofFinite K
  have hcard' : Fintype.card K = 3 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have htripleCard : ({base, qClass, rClass} : Finset K).card = 3 :=
    Finset.card_triple_eq_three_iff.mpr
      ⟨hqNeBase.symm, hrNeBase.symm, hqNeR⟩
  have hcover : ({base, qClass, rClass} : Finset K) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (by simp)
    rw [htripleCard, Finset.card_univ, hcard']
  have hsMember : sClass ∈ ({base, qClass, rClass} : Finset K) := by
    rw [hcover]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsMember
  rcases hsMember with hsBase | hsQ | hsR
  · exact Or.inl (I.symm (Quotient.exact hsBase))
  · exact Or.inr (Or.inl (I.symm (Quotient.exact hsQ)))
  · exact Or.inr (Or.inr (I.symm (Quotient.exact hsR)))

/-- If the interlacement quotient has three classes, one may choose two
representatives which, together with `p`, lie in three pairwise distinct
interlacement classes. -/
theorem exists_two_pairwise_noninterlaced_related_of_card_eq_three
    {R : PathContourRelation Q} (I : PathInterlacementRelation R)
    {i j : Q} (p : Quiver.Path i j) (hpp : R.related p p)
    [Finite (RelatedPathInterlacementClass I p)]
    (hcard : Nat.card (RelatedPathInterlacementClass I p) = 3) :
    ∃ q r : Quiver.Path i j,
      R.related p q ∧ R.related p r ∧
        ¬I.interlaced p q ∧ ¬I.interlaced p r ∧
          ¬I.interlaced q r := by
  let K := RelatedPathInterlacementClass I p
  let base : K := Quotient.mk'' ⟨p, hpp⟩
  letI : Fintype K := Fintype.ofFinite K
  have hcard' : Fintype.card K = 3 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hone : 1 < Fintype.card K := by omega
  obtain ⟨qClass, hqClass⟩ :=
    Fintype.exists_ne_of_one_lt_card hone base
  have hthree : 3 ≤ ENat.card K := by
    simp only [ENat.card_eq_coe_fintype_card, hcard']
    exact le_rfl
  obtain ⟨rClass, hrBase, hrQ⟩ :=
    ENat.exists_ne_ne_of_three_le hthree base qClass
  let q := qClass.out
  let r := rClass.out
  refine ⟨q.1, r.1, q.2, r.2, ?_, ?_, ?_⟩
  · intro hpq
    apply hqClass
    calc
      qClass = Quotient.mk'' q := (Quotient.out_eq qClass).symm
      _ = base := Quotient.sound (I.symm hpq)
  · intro hpr
    apply hrBase
    calc
      rClass = Quotient.mk'' r := (Quotient.out_eq rClass).symm
      _ = base := Quotient.sound (I.symm hpr)
  · intro hqr
    apply hrQ
    calc
      rClass = Quotient.mk'' r := (Quotient.out_eq rClass).symm
      _ = Quotient.mk'' q := Quotient.sound (I.symm hqr)
      _ = qClass := Quotient.out_eq qClass

/-- A bundled arrow starting at one fixed quiver vertex. -/
abbrev OutgoingQuiverArrow (x : Q) := Σ y : Q, x ⟶ y

/-- A bundled arrow ending at one fixed quiver vertex. -/
abbrev IncomingQuiverArrow (z : Q) := Σ y : Q, y ⟶ z

/-- A decomposition of a nonempty path into its initial arrow and remaining
tail. -/
structure PathInitialDecomposition {x z : Q} (p : Quiver.Path x z) where
  middle : Q
  arrow : x ⟶ middle
  tail : Quiver.Path middle z
  path_eq : p = arrow.toPath.comp tail

/-- Two parallel paths have an explicitly displayed common initial segment
and then leave its endpoint through distinct bundled arrows.  This is the
dependent-path form of a maximal common prefix: maximality is encoded by the
inequality of the two next arrows, so no numerical choice of a prefix length
is retained. -/
structure PathInitialDivergence {x z : Q}
    (p q : Quiver.Path x z) where
  middle : Q
  common : Quiver.Path x middle
  leftTarget : Q
  rightTarget : Q
  leftArrow : middle ⟶ leftTarget
  rightArrow : middle ⟶ rightTarget
  leftTail : Quiver.Path leftTarget z
  rightTail : Quiver.Path rightTarget z
  left_eq : p = common.comp (leftArrow.toPath.comp leftTail)
  right_eq : q = common.comp (rightArrow.toPath.comp rightTail)
  arrows_ne :
    (⟨leftTarget, leftArrow⟩ : OutgoingQuiverArrow middle) ≠
      ⟨rightTarget, rightArrow⟩

/-- Choose the initial-arrow decomposition of a nonempty path. -/
def chosenPathInitialDecomposition {x z : Q} (p : Quiver.Path x z)
    (hp : p.length ≠ 0) : PathInitialDecomposition p := by
  let h := (Quiver.Path.length_ne_zero_iff_eq_comp p).1 hp
  let middle := Classical.choose h
  let hmiddle := Classical.choose_spec h
  let arrow := Classical.choose hmiddle
  let harrow := Classical.choose_spec hmiddle
  let tail := Classical.choose harrow
  let htail := Classical.choose_spec harrow
  exact ⟨middle, arrow, tail, htail.1⟩

/-- The bundled initial arrow selected from a nonempty path. -/
def chosenInitialArrow {x z : Q} (p : Quiver.Path x z)
    (hp : p.length ≠ 0) : OutgoingQuiverArrow x :=
  let d := chosenPathInitialDecomposition p hp
  ⟨d.middle, d.arrow⟩

/-- A decomposition of a nonempty path into its initial segment and final
arrow. -/
structure PathFinalDecomposition {x z : Q} (p : Quiver.Path x z) where
  middle : Q
  head : Quiver.Path x middle
  arrow : middle ⟶ z
  path_eq : p = head.comp arrow.toPath

/-- Choose the final-arrow decomposition of a nonempty path. -/
def chosenPathFinalDecomposition {x z : Q} (p : Quiver.Path x z)
    (hp : p.length ≠ 0) : PathFinalDecomposition p := by
  let h := (Quiver.Path.length_ne_zero_iff_eq_cons (p := p)).1 hp
  let middle := Classical.choose h
  let hmiddle := Classical.choose_spec h
  let head := Classical.choose hmiddle
  let hhead := Classical.choose_spec hmiddle
  let arrow := Classical.choose hhead
  let harrow := Classical.choose_spec hhead
  exact ⟨middle, head, arrow, by simpa using harrow⟩

/-- The bundled final arrow selected from a nonempty path. -/
def chosenFinalArrow {x z : Q} (p : Quiver.Path x z)
    (hp : p.length ≠ 0) : IncomingQuiverArrow z :=
  let d := chosenPathFinalDecomposition p hp
  ⟨d.middle, d.arrow⟩

/-- A path of length at least two decomposed into its first arrow, an
intermediate path, and its last arrow. -/
structure PathEndpointDecomposition {x z : Q} (p : Quiver.Path x z) where
  initialMiddle : Q
  finalMiddle : Q
  initial : x ⟶ initialMiddle
  middle : Quiver.Path initialMiddle finalMiddle
  final : finalMiddle ⟶ z
  path_eq : p = initial.toPath.comp (middle.comp final.toPath)

/-- Choose the first and last arrows of a path of length at least two. -/
def chosenPathEndpointDecomposition {x z : Q} (p : Quiver.Path x z)
    (hp : 2 ≤ p.length) : PathEndpointDecomposition p := by
  let di := chosenPathInitialDecomposition p (by omega)
  have htail : di.tail.length ≠ 0 := by
    have hlength := congrArg Quiver.Path.length di.path_eq
    simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at hlength
    omega
  let df := chosenPathFinalDecomposition di.tail htail
  exact
    { initialMiddle := di.middle
      finalMiddle := df.middle
      initial := di.arrow
      middle := df.head
      final := df.arrow
      path_eq := by
        calc
          p = di.arrow.toPath.comp di.tail := di.path_eq
          _ = di.arrow.toPath.comp (df.head.comp df.arrow.toPath) :=
            congrArg (fun r => di.arrow.toPath.comp r) df.path_eq }

namespace PathEndpointDecomposition

/-- Forget the final arrow and retain the initial-arrow decomposition. -/
def toInitial {x z : Q} {p : Quiver.Path x z}
    (d : PathEndpointDecomposition p) : PathInitialDecomposition p where
  middle := d.initialMiddle
  arrow := d.initial
  tail := d.middle.comp d.final.toPath
  path_eq := d.path_eq

/-- Forget the initial arrow and retain the final-arrow decomposition. -/
def toFinal {x z : Q} {p : Quiver.Path x z}
    (d : PathEndpointDecomposition p) : PathFinalDecomposition p where
  middle := d.finalMiddle
  head := d.initial.toPath.comp d.middle
  arrow := d.final
  path_eq := by
    calc
      p = d.initial.toPath.comp (d.middle.comp d.final.toPath) := d.path_eq
      _ = (d.initial.toPath.comp d.middle).comp d.final.toPath :=
        (Quiver.Path.comp_assoc _ _ _).symm

end PathEndpointDecomposition

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace PathInitialDivergence

/-- The common-prefix-plus-left-arrow branch of a divergence survives
whenever the whole left path survives. -/
theorem leftBranch_rayPathMap_ne_zero
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (d : PathInitialDivergence p q) (hp : rayPathMap p ≠ 0) :
    rayPathMap (d.common.comp d.leftArrow.toPath) ≠ 0 := by
  intro hzero
  apply hp
  rw [d.left_eq, ← Quiver.Path.comp_assoc]
  simp only [rayPathMap, LinearPathCategory.pathMap_comp, hzero,
    CategoryTheory.Limits.comp_zero]

/-- The symmetric branch-survival consequence. -/
theorem rightBranch_rayPathMap_ne_zero
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (d : PathInitialDivergence p q) (hq : rayPathMap q ≠ 0) :
    rayPathMap (d.common.comp d.rightArrow.toPath) ≠ 0 := by
  intro hzero
  apply hq
  rw [d.right_eq, ← Quiver.Path.comp_assoc]
  simp only [rayPathMap, LinearPathCategory.pathMap_comp, hzero,
    CategoryTheory.Limits.comp_zero]

end PathInitialDivergence

/-- The nonzero category morphism represented by a bundled arrow ending at
`z`. -/
def incomingQuiverArrowNonzeroHom {z : RayVertex C}
    (a : IncomingQuiverArrow z) : NonzeroHom z.obj a.1.obj :=
  ⟨rayArrowMorphism a.2, a.2.property.1⟩

/-- Distinct arrows ending at the same vertex are incomparable in the
fixed-source ray factorization order. -/
theorem incomingQuiverArrow_raySourceIncomparable_of_ne
    [IsFiniteRayCategory C] {z : RayVertex C}
    {a b : IncomingQuiverArrow z} (hab : a ≠ b) :
    RaySourceIncomparable
      (incomingQuiverArrowNonzeroHom (C := C) a)
      (incomingQuiverArrowNonzeroHom (C := C) b) := by
  rcases a with ⟨ya, a⟩
  rcases b with ⟨yb, b⟩
  constructor
  · rintro ⟨h, hh⟩
    have hIso : IsIso h := by
      rcases b.property.2.2 ya.obj
          (incomingQuiverArrowNonzeroHom (C := C) ⟨ya, a⟩).1 h hh with
        hfIso | hhIso
      · exact (a.property.2.1 hfIso).elim
      · exact hhIso
    letI : IsIso h := hIso
    obtain ⟨htarget, heq⟩ := ray_isIso_eq_eqToHom h
    have hv : ya = yb := RayVertex.ext htarget
    subst yb
    have hhId : h = 𝟙 ya.obj := by simpa using heq
    apply hab
    have harrow : a = b := by
      apply Subtype.ext
      change a.1 ≫ h = b.1 at hh
      simpa [hhId] using hh
    subst b
    rfl
  · rintro ⟨h, hh⟩
    have hIso : IsIso h := by
      rcases a.property.2.2 yb.obj
          (incomingQuiverArrowNonzeroHom (C := C) ⟨yb, b⟩).1 h hh with
        hgIso | hhIso
      · exact (b.property.2.1 hgIso).elim
      · exact hhIso
    letI : IsIso h := hIso
    obtain ⟨htarget, heq⟩ := ray_isIso_eq_eqToHom h
    have hv : yb = ya := RayVertex.ext htarget
    subst ya
    have hhId : h = 𝟙 yb.obj := by simpa using heq
    apply hab
    have harrow : a = b := by
      apply Subtype.ext
      change b.1 ≫ h = a.1 at hh
      simpa [hhId] using hh.symm
    subst b
    rfl

/-- The nonzero category morphism represented by a bundled arrow starting at
`x`. -/
def outgoingQuiverArrowNonzeroHom {x : RayVertex C}
    (a : OutgoingQuiverArrow x) : NonzeroHom a.1.obj x.obj :=
  ⟨rayArrowMorphism a.2, a.2.property.1⟩

/-- Distinct arrows starting at the same vertex are incomparable in the
fixed-target ray factorization order. -/
theorem outgoingQuiverArrow_rayTargetIncomparable_of_ne
    [IsFiniteRayCategory C] {x : RayVertex C}
    {a b : OutgoingQuiverArrow x} (hab : a ≠ b) :
    RayTargetIncomparable
      (outgoingQuiverArrowNonzeroHom (C := C) a)
      (outgoingQuiverArrowNonzeroHom (C := C) b) := by
  rcases a with ⟨ya, a⟩
  rcases b with ⟨yb, b⟩
  constructor
  · rintro ⟨h, hh⟩
    have hIso : IsIso h := by
      rcases a.property.2.2 yb.obj h
          (outgoingQuiverArrowNonzeroHom (C := C) ⟨yb, b⟩).1 hh with
        hhIso | hgIso
      · exact hhIso
      · exact (b.property.2.1 hgIso).elim
    letI : IsIso h := hIso
    obtain ⟨htarget, heq⟩ := ray_isIso_eq_eqToHom h
    have hv : ya = yb := RayVertex.ext htarget
    subst yb
    have hhId : h = 𝟙 ya.obj := by simpa using heq
    apply hab
    have harrow : a = b := by
      apply Subtype.ext
      change h ≫ b.1 = a.1 at hh
      simpa [hhId] using hh.symm
    subst b
    rfl
  · rintro ⟨h, hh⟩
    have hIso : IsIso h := by
      rcases b.property.2.2 ya.obj h
          (outgoingQuiverArrowNonzeroHom (C := C) ⟨ya, a⟩).1 hh with
        hhIso | hfIso
      · exact hhIso
      · exact (a.property.2.1 hfIso).elim
    letI : IsIso h := hIso
    obtain ⟨htarget, heq⟩ := ray_isIso_eq_eqToHom h
    have hv : yb = ya := RayVertex.ext htarget
    subst ya
    have hhId : h = 𝟙 yb.obj := by simpa using heq
    apply hab
    have harrow : a = b := by
      apply Subtype.ext
      change h ≫ a.1 = b.1 at hh
      simpa [hhId] using hh
    subst b
    rfl

namespace PathInitialDecomposition

/-- The category morphism underlying the initial arrow of a path in the
reversed irreducible ray quiver. -/
def rayArrowNonzeroHom {x z : RayVertex C} {p : Quiver.Path x z}
    (d : PathInitialDecomposition p) : NonzeroHom d.middle.obj x.obj :=
  ⟨rayArrowMorphism d.arrow, d.arrow.property.1⟩

@[simp]
theorem coe_rayArrowNonzeroHom {x z : RayVertex C}
    {p : Quiver.Path x z} (d : PathInitialDecomposition p) :
    (d.rayArrowNonzeroHom).1 = rayArrowMorphism d.arrow :=
  rfl

/-- In the fixed-target factorization order, the whole path ray lies below
its initial arrow. -/
theorem rayPathMorphismTo_le_rayArrow
    {x z : RayVertex C} {p : Quiver.Path x z}
    (d : PathInitialDecomposition p) (hp : rayPathMap p ≠ 0) :
    rayPathMorphismTo p hp ≤ d.rayArrowNonzeroHom.toMorphismTo := by
  refine ⟨rayPathMap d.tail, ?_⟩
  change rayPathMap d.tail ≫ rayArrowMorphism d.arrow = rayPathMap p
  calc
    rayPathMap d.tail ≫ rayArrowMorphism d.arrow =
        rayPathMap d.tail ≫ rayPathMap d.arrow.toPath := by
      rw [rayPathMap_toPath]
    _ = rayPathMap (d.arrow.toPath.comp d.tail) := by
      exact (LinearPathCategory.pathMap_comp
        RayVertex.obj rayArrowMorphism d.arrow.toPath d.tail).symm
    _ = rayPathMap p := congrArg rayPathMap d.path_eq.symm

/-- Initial arrows of two related paths admit the whole path ray as a common
lower bound in the fixed-target factorization order. -/
theorem exists_commonLower_rayArrows_of_related
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (dp : PathInitialDecomposition p) (dq : PathInitialDecomposition q)
    (hpq : (rayPathContourRelation (C := C)).related p q) :
    ∃ s : NonzeroMorphismTo x.obj,
      s ≤ dp.rayArrowNonzeroHom.toMorphismTo ∧
        s ≤ dq.rayArrowNonzeroHom.toMorphismTo := by
  let hq : rayPathMap q ≠ 0 := by
    rw [← hpq.2]
    exact hpq.1
  refine ⟨rayPathMorphismTo p hpq.1,
    dp.rayPathMorphismTo_le_rayArrow hpq.1, ?_⟩
  rw [rayPathMorphismTo_eq_of_related p q hpq]
  exact dq.rayPathMorphismTo_le_rayArrow hq

end PathInitialDecomposition

namespace PathFinalDecomposition

/-- The category morphism underlying the final arrow of a path in the
reversed irreducible ray quiver. -/
def rayArrowNonzeroHom {x z : RayVertex C} {p : Quiver.Path x z}
    (d : PathFinalDecomposition p) : NonzeroHom z.obj d.middle.obj :=
  ⟨rayArrowMorphism d.arrow, d.arrow.property.1⟩

@[simp]
theorem coe_rayArrowNonzeroHom {x z : RayVertex C}
    {p : Quiver.Path x z} (d : PathFinalDecomposition p) :
    (d.rayArrowNonzeroHom).1 = rayArrowMorphism d.arrow :=
  rfl

/-- In the fixed-source factorization order, the final arrow lies below the
whole path ray. -/
theorem rayArrow_le_rayPathMorphism
    {x z : RayVertex C} {p : Quiver.Path x z}
    (d : PathFinalDecomposition p) (hp : rayPathMap p ≠ 0) :
    d.rayArrowNonzeroHom.toMorphismFrom ≤ rayPathMorphism p hp := by
  refine ⟨rayPathMap d.head, ?_⟩
  change rayArrowMorphism d.arrow ≫ rayPathMap d.head = rayPathMap p
  calc
    rayArrowMorphism d.arrow ≫ rayPathMap d.head =
        rayPathMap d.arrow.toPath ≫ rayPathMap d.head := by
      rw [rayPathMap_toPath]
    _ = rayPathMap (d.head.comp d.arrow.toPath) := by
      exact (LinearPathCategory.pathMap_comp
        RayVertex.obj rayArrowMorphism d.head d.arrow.toPath).symm
    _ = rayPathMap p := congrArg rayPathMap d.path_eq.symm

/-- Final arrows of two related paths admit the whole path ray as a common
upper bound in the fixed-source factorization order. -/
theorem exists_commonUpper_rayArrows_of_related
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (dp : PathFinalDecomposition p) (dq : PathFinalDecomposition q)
    (hpq : (rayPathContourRelation (C := C)).related p q) :
    ∃ s : NonzeroMorphismFrom z.obj,
      dp.rayArrowNonzeroHom.toMorphismFrom ≤ s ∧
        dq.rayArrowNonzeroHom.toMorphismFrom ≤ s := by
  let hq : rayPathMap q ≠ 0 := by
    rw [← hpq.2]
    exact hpq.1
  refine ⟨rayPathMorphism p hpq.1,
    dp.rayArrow_le_rayPathMorphism hpq.1, ?_⟩
  rw [rayPathMorphism_eq_of_related p q hpq]
  exact dq.rayArrow_le_rayPathMorphism hq

end PathFinalDecomposition

/-- The strong global ray-valency hypothesis: in the reversed irreducible
quiver, at most three arrows leave and at most three arrows enter each vertex. -/
class HasRayValencyAtMostThree (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] : Prop where
  outgoing_card_le : ∀ x : RayVertex C,
    Nat.card (OutgoingQuiverArrow x) ≤ 3
  incoming_card_le : ∀ z : RayVertex C,
    Nat.card (IncomingQuiverArrow z) ≤ 3

/-- The source-faithful valency consequence used by Roiter vanishing:
the endpoints of a nonzero irreducible path of length at least two have at
most three outgoing and incoming arrows, respectively. -/
class HasRayLongPathEndpointValencyAtMostThree
    (C : Type u) [Category.{v} C] [HasZeroMorphisms C] : Prop where
  outgoing_card_le : ∀ {x z : RayVertex C} (p : Quiver.Path x z),
    rayPathMap p ≠ 0 → 2 ≤ p.length →
      Nat.card (OutgoingQuiverArrow x) ≤ 3
  incoming_card_le : ∀ {x z : RayVertex C} (p : Quiver.Path x z),
    rayPathMap p ≠ 0 → 2 ≤ p.length →
      Nat.card (IncomingQuiverArrow z) ≤ 3

/-- The source four-arrow reduction: at an endpoint with at least four
irreducible arrows, every incident two-arrow path evaluates to zero. -/
class HasRayFourArrowZeroCompositions
    (C : Type u) [Category.{v} C] [HasZeroMorphisms C] : Prop where
  outgoing_zero : ∀ {x y z : RayVertex C}
      (a : x ⟶ y) (b : y ⟶ z),
    4 ≤ Nat.card (OutgoingQuiverArrow x) →
      rayPathMap (a.toPath.comp b.toPath) = 0
  incoming_zero : ∀ {x y z : RayVertex C}
      (a : x ⟶ y) (b : y ⟶ z),
    4 ≤ Nat.card (IncomingQuiverArrow z) →
      rayPathMap (a.toPath.comp b.toPath) = 0

/-- Global three-valency implies the source-faithful long-path endpoint
condition. -/
instance HasRayValencyAtMostThree.toHasRayLongPathEndpointValencyAtMostThree
    [HasRayValencyAtMostThree C] :
    HasRayLongPathEndpointValencyAtMostThree C where
  outgoing_card_le _ _ _ :=
    HasRayValencyAtMostThree.outgoing_card_le _
  incoming_card_le _ _ _ :=
    HasRayValencyAtMostThree.incoming_card_le _

/-- Four-arrow zero-composition gives the source-faithful endpoint valency
bound on every nonzero irreducible path of length at least two. -/
instance HasRayFourArrowZeroCompositions.toHasRayLongPathEndpointValencyAtMostThree
    [HasRayFourArrowZeroCompositions C] :
    HasRayLongPathEndpointValencyAtMostThree C where
  outgoing_card_le := by
    intro x z p hp hlength
    by_contra hcard
    have hfour : 4 ≤ Nat.card (OutgoingQuiverArrow x) := by omega
    let d₁ := chosenPathInitialDecomposition p (by omega)
    have htail : d₁.tail.length ≠ 0 := by
      have h := congrArg Quiver.Path.length d₁.path_eq
      simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at h
      omega
    let d₂ := chosenPathInitialDecomposition d₁.tail htail
    have hpair :
        rayPathMap (d₁.arrow.toPath.comp d₂.arrow.toPath) = 0 :=
      HasRayFourArrowZeroCompositions.outgoing_zero
        d₁.arrow d₂.arrow hfour
    have hpath :
        p = (d₁.arrow.toPath.comp d₂.arrow.toPath).comp d₂.tail := by
      calc
        p = d₁.arrow.toPath.comp d₁.tail := d₁.path_eq
        _ = d₁.arrow.toPath.comp (d₂.arrow.toPath.comp d₂.tail) :=
          congrArg (fun q => d₁.arrow.toPath.comp q) d₂.path_eq
        _ = (d₁.arrow.toPath.comp d₂.arrow.toPath).comp d₂.tail :=
          (Quiver.Path.comp_assoc _ _ _).symm
    apply hp
    calc
      rayPathMap p = rayPathMap
          ((d₁.arrow.toPath.comp d₂.arrow.toPath).comp d₂.tail) :=
        congrArg (fun q => rayPathMap q) hpath
      _ = rayPathMap d₂.tail ≫
          rayPathMap (d₁.arrow.toPath.comp d₂.arrow.toPath) :=
        LinearPathCategory.pathMap_comp _ _ _ _
      _ = 0 := by rw [hpair]; simp
  incoming_card_le := by
    intro x z p hp hlength
    by_contra hcard
    have hfour : 4 ≤ Nat.card (IncomingQuiverArrow z) := by omega
    let d₁ := chosenPathFinalDecomposition p (by omega)
    have hhead : d₁.head.length ≠ 0 := by
      have h := congrArg Quiver.Path.length d₁.path_eq
      simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at h
      omega
    let d₂ := chosenPathFinalDecomposition d₁.head hhead
    have hpair :
        rayPathMap (d₂.arrow.toPath.comp d₁.arrow.toPath) = 0 :=
      HasRayFourArrowZeroCompositions.incoming_zero
        d₂.arrow d₁.arrow hfour
    have hpath :
        p = d₂.head.comp (d₂.arrow.toPath.comp d₁.arrow.toPath) := by
      calc
        p = d₁.head.comp d₁.arrow.toPath := d₁.path_eq
        _ = (d₂.head.comp d₂.arrow.toPath).comp d₁.arrow.toPath :=
          congrArg (fun q => q.comp d₁.arrow.toPath) d₂.path_eq
        _ = d₂.head.comp (d₂.arrow.toPath.comp d₁.arrow.toPath) :=
          Quiver.Path.comp_assoc _ _ _
    apply hp
    calc
      rayPathMap p = rayPathMap
          (d₂.head.comp (d₂.arrow.toPath.comp d₁.arrow.toPath)) :=
        congrArg (fun q => rayPathMap q) hpath
      _ = rayPathMap (d₂.arrow.toPath.comp d₁.arrow.toPath) ≫
          rayPathMap d₂.head :=
        LinearPathCategory.pathMap_comp _ _ _ _
      _ = 0 := by rw [hpair]; simp

/-- In a finite type of cardinality at most three, three pairwise distinct
elements exhaust the type. -/
theorem eq_first_or_eq_second_or_eq_third_of_natCard_le_three
    {α : Type w} [Finite α]
    (hcard : Nat.card α ≤ 3) {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    d = a ∨ d = b ∨ d = c := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  by_contra hd
  push Not at hd
  let s : Finset α := {a, b, c, d}
  have ha : a ∉ ({b, c, d} : Finset α) := by
    simp [hab, hac, hd.1.symm]
  have hb : b ∉ ({c, d} : Finset α) := by
    simp [hbc, hd.2.1.symm]
  have hc : c ∉ ({d} : Finset α) := by
    simp [hd.2.2.symm]
  have hsCard : s.card = 4 := by
    change ({a, b, c, d} : Finset α).card = 4
    rw [Finset.card_insert_of_notMem ha,
      Finset.card_insert_of_notMem hb,
      Finset.card_insert_of_notMem hc]
    simp
  have hsLe : s.card ≤ Fintype.card α := Finset.card_le_univ s
  have hcard' : Fintype.card α ≤ 3 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  omega

/-- Finiteness of the objects and Hom sets of a finite ray category makes the
dependent type of arrows leaving any fixed ray-quiver vertex finite. -/
theorem outgoingQuiverArrow_finite [Finite C] [IsFiniteRayCategory C]
    (x : RayVertex C) : Finite (OutgoingQuiverArrow x) := by
  letI : Finite (RayVertex C) :=
    Finite.of_equiv C rayVertexEquiv.symm
  letI (X Y : C) : Finite (X ⟶ Y) :=
    IsFiniteRayCategory.hom_finite X Y
  letI (y : RayVertex C) : Finite (x ⟶ y) := by
    apply Finite.of_injective Subtype.val
    exact Subtype.val_injective
  infer_instance

/-- The dual finiteness statement for arrows entering a fixed ray-quiver
vertex. -/
theorem incomingQuiverArrow_finite [Finite C] [IsFiniteRayCategory C]
    (z : RayVertex C) : Finite (IncomingQuiverArrow z) := by
  letI : Finite (RayVertex C) :=
    Finite.of_equiv C rayVertexEquiv.symm
  letI (X Y : C) : Finite (X ⟶ Y) :=
    IsFiniteRayCategory.hom_finite X Y
  letI (y : RayVertex C) : Finite (y ⟶ z) := by
    apply Finite.of_injective Subtype.val
    exact Subtype.val_injective
  infer_instance

/-- Three pairwise distinct arrows leaving a ray-quiver vertex exhaust all
outgoing arrows at that vertex. -/
theorem outgoingQuiverArrow_eq_first_or_eq_second_or_eq_third
    [Finite C] [IsFiniteRayCategory C] [HasRayValencyAtMostThree C]
    {x : RayVertex C} {a b c d : OutgoingQuiverArrow x}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    d = a ∨ d = b ∨ d = c := by
  letI : Finite (OutgoingQuiverArrow x) :=
    outgoingQuiverArrow_finite x
  exact eq_first_or_eq_second_or_eq_third_of_natCard_le_three
    (HasRayValencyAtMostThree.outgoing_card_le x) hab hac hbc

/-- Three pairwise distinct arrows entering a ray-quiver vertex exhaust all
incoming arrows at that vertex. -/
theorem incomingQuiverArrow_eq_first_or_eq_second_or_eq_third
    [Finite C] [IsFiniteRayCategory C] [HasRayValencyAtMostThree C]
    {z : RayVertex C} {a b c d : IncomingQuiverArrow z}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    d = a ∨ d = b ∨ d = c := by
  letI : Finite (IncomingQuiverArrow z) :=
    incomingQuiverArrow_finite z
  exact eq_first_or_eq_second_or_eq_third_of_natCard_le_three
    (HasRayValencyAtMostThree.incoming_card_le z) hab hac hbc

/-- Equal nonzero ray paths with a common initial quiver arrow are related by
one proper-whisker interlacement step. -/
theorem rayPaths_interlaced_of_commonInitialArrow
    [HasRayCancellation C]
    {x y z : RayVertex C} (a : x ⟶ y)
    (p q : Quiver.Path y z)
    (houter : (rayPathContourRelation (C := C)).related
      (a.toPath.comp p) (a.toPath.comp q)) :
    (properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced
        (a.toPath.comp p) (a.toPath.comp q) := by
  let R := rayPathContourRelation (C := C)
  have hpne : rayPathMap p ≠ 0 := by
    intro hpzero
    apply houter.1
    simp only [rayPathMap, LinearPathCategory.pathMap_comp,
      hpzero, zero_comp]
  have hpq : R.related p q := by
    refine ⟨hpne, ?_⟩
    apply HasRayCancellation.cancel_right
      (rayPathMap p) (rayPathMap q) (rayPathMap a.toPath)
    · simpa only [rayPathMap, LinearPathCategory.pathMap_comp] using houter.2
    · simpa only [rayPathMap, LinearPathCategory.pathMap_comp] using houter.1
  apply properWhiskerInterlaced_of_step R
  refine ⟨y, z, a.toPath, p, q, Quiver.Path.nil,
    hpq, ?_, ?_, ?_, ?_⟩
  · simpa using houter
  · simp
  · simp
  · simp

/-- Equal nonzero ray paths with a common final quiver arrow are related by
one proper-whisker interlacement step. -/
theorem rayPaths_interlaced_of_commonFinalArrow
    [HasRayCancellation C]
    {x y z : RayVertex C} (p q : Quiver.Path x y)
    (a : y ⟶ z)
    (houter : (rayPathContourRelation (C := C)).related
      (p.comp a.toPath) (q.comp a.toPath)) :
    (properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced
        (p.comp a.toPath) (q.comp a.toPath) := by
  let R := rayPathContourRelation (C := C)
  have hpne : rayPathMap p ≠ 0 := by
    intro hpzero
    apply houter.1
    simp only [rayPathMap, LinearPathCategory.pathMap_comp,
      hpzero, comp_zero]
  have hpq : R.related p q := by
    refine ⟨hpne, ?_⟩
    apply HasRayCancellation.cancel_left
      (rayPathMap a.toPath) (rayPathMap p) (rayPathMap q)
    · simpa only [rayPathMap, LinearPathCategory.pathMap_comp] using houter.2
    · simpa only [rayPathMap, LinearPathCategory.pathMap_comp] using houter.1
  apply properWhiskerInterlaced_of_step R
  refine ⟨x, y, Quiver.Path.nil, p, q, a.toPath,
    hpq, ?_, ?_, ?_, ?_⟩
  · simpa using houter
  · simp
  · simp
  · simp

/-- Initial decompositions with the same bundled arrow give interlaced ray
paths.  Equality of the dependent arrow codes identifies both the middle
vertex and the arrow itself. -/
theorem rayPaths_interlaced_of_initialDecomposition_code_eq
    [HasRayCancellation C]
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (dp : PathInitialDecomposition p) (dq : PathInitialDecomposition q)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (hcode : (⟨dp.middle, dp.arrow⟩ : OutgoingQuiverArrow x) =
      ⟨dq.middle, dq.arrow⟩) :
    (properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p q := by
  rcases dp with ⟨y, a, p', rfl⟩
  rcases dq with ⟨y', a', q', rfl⟩
  dsimp at hcode
  cases hcode
  exact rayPaths_interlaced_of_commonInitialArrow a p' q' hpq

/-- Final decompositions with the same bundled arrow give interlaced ray
paths. -/
theorem rayPaths_interlaced_of_finalDecomposition_code_eq
    [HasRayCancellation C]
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (dp : PathFinalDecomposition p) (dq : PathFinalDecomposition q)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (hcode : (⟨dp.middle, dp.arrow⟩ : IncomingQuiverArrow z) =
      ⟨dq.middle, dq.arrow⟩) :
    (properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p q := by
  rcases dp with ⟨y, p', a, rfl⟩
  rcases dq with ⟨y', q', a', rfl⟩
  dsimp at hcode
  cases hcode
  exact rayPaths_interlaced_of_commonFinalArrow p' q' a hpq

/-- Noninterlaced related paths have distinct chosen initial arrows. -/
theorem chosenInitialArrow_ne_of_not_interlaced
    [HasRayCancellation C]
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (hp : p.length ≠ 0) (hq : q.length ≠ 0)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (hnot : ¬(properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p q) :
    chosenInitialArrow p hp ≠ chosenInitialArrow q hq := by
  intro hcode
  apply hnot
  exact rayPaths_interlaced_of_initialDecomposition_code_eq
    (chosenPathInitialDecomposition p hp)
    (chosenPathInitialDecomposition q hq) hpq
    (by simpa only [chosenInitialArrow] using hcode)

/-- The dual distinct-final-arrow consequence. -/
theorem chosenFinalArrow_ne_of_not_interlaced
    [HasRayCancellation C]
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (hp : p.length ≠ 0) (hq : q.length ≠ 0)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (hnot : ¬(properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p q) :
    chosenFinalArrow p hp ≠ chosenFinalArrow q hq := by
  intro hcode
  apply hnot
  exact rayPaths_interlaced_of_finalDecomposition_code_eq
    (chosenPathFinalDecomposition p hp)
    (chosenPathFinalDecomposition q hq) hpq
    (by simpa only [chosenFinalArrow] using hcode)

/-- Every path representing the same noninvertible nonzero ray as `p` is
nonempty. -/
theorem rayPath_length_ne_zero_of_related_of_not_isIso
    [IsFiniteRayCategory C]
    {x z : RayVertex C} {p q : Quiver.Path x z}
    (hp : ¬IsIso (rayPathMap p))
    (hpq : (rayPathContourRelation (C := C)).related p q) :
    q.length ≠ 0 := by
  intro hq
  have hqIso : IsIso (rayPathMap q) := by
    cases q with
    | nil =>
        simp only [rayPathMap, LinearPathCategory.pathMap_nil]
        infer_instance
    | cons p a => simp at hq
  apply hp
  rw [hpq.2]
  exact hqIso

/-- A length-one path in the irreducible ray quiver evaluates to an
irreducible category morphism. -/
theorem rayPathMap_isIrreducible_of_length_eq_one
    {x z : RayVertex C} (p : Quiver.Path x z) (hp : p.length = 1) :
    IsIrreducibleRayMorphism (rayPathMap p) := by
  cases p with
  | nil => simp at hp
  | @cons y z p a =>
      have hpZero : p.length = 0 := by
        simpa using hp
      obtain rfl := Quiver.Path.eq_of_length_zero p hpZero
      obtain rfl := Quiver.Path.eq_nil_of_length_zero p hpZero
      simpa [rayPathMap, LinearPathCategory.pathMap,
        rayArrowMorphism] using a.property

/-- A path related to a one-arrow ray path also has one arrow. -/
theorem rayPath_length_eq_one_of_related_of_length_eq_one
    [IsFiniteRayCategory C]
    {x z : RayVertex C} (p q : Quiver.Path x z)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (hpOne : p.length = 1) : q.length = 1 := by
  have hpIrreducible : IsIrreducibleRayMorphism (rayPathMap p) :=
    rayPathMap_isIrreducible_of_length_eq_one p hpOne
  have hqNeZero : q.length ≠ 0 :=
    rayPath_length_ne_zero_of_related_of_not_isIso
      hpIrreducible.2.1 hpq
  by_contra hqOne
  have hqTwo : 2 ≤ q.length := by omega
  let dq := chosenPathInitialDecomposition q hqNeZero
  have htail : dq.tail.length ≠ 0 := by
    have hlength := congrArg Quiver.Path.length dq.path_eq
    simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at hlength
    omega
  have hfactor : rayPathMap dq.tail ≫ rayArrowMorphism dq.arrow =
      rayPathMap p := by
    calc
      rayPathMap dq.tail ≫ rayArrowMorphism dq.arrow =
          rayPathMap dq.tail ≫ rayPathMap dq.arrow.toPath := by
        rw [rayPathMap_toPath]
      _ = rayPathMap (dq.arrow.toPath.comp dq.tail) := by
        exact (LinearPathCategory.pathMap_comp
          RayVertex.obj rayArrowMorphism dq.arrow.toPath dq.tail).symm
      _ = rayPathMap q := congrArg rayPathMap dq.path_eq.symm
      _ = rayPathMap p := hpq.2.symm
  rcases hpIrreducible.2.2 dq.middle.obj
      (rayPathMap dq.tail) (rayArrowMorphism dq.arrow)
      hfactor with htailIso | harrowIso
  · exact rayPathMap_not_isIso_of_length_ne_zero
      dq.tail htail htailIso
  · exact dq.arrow.property.2.1 harrowIso

/-- Parallel one-arrow ray paths with equal evaluations are equal. -/
theorem rayPath_eq_of_length_eq_one_of_rayPathMap_eq
    {x z : RayVertex C} (p q : Quiver.Path x z)
    (hpOne : p.length = 1) (hqOne : q.length = 1)
    (hpq : rayPathMap p = rayPathMap q) : p = q := by
  cases p with
  | nil => simp at hpOne
  | @cons y _ p a =>
      have hpZero : p.length = 0 := by simpa using hpOne
      obtain rfl := Quiver.Path.eq_of_length_zero p hpZero
      obtain rfl := Quiver.Path.eq_nil_of_length_zero p hpZero
      cases q with
      | nil => simp at hqOne
      | @cons y' _ q b =>
          have hqZero : q.length = 0 := by simpa using hqOne
          obtain rfl := Quiver.Path.eq_of_length_zero q hqZero
          obtain rfl := Quiver.Path.eq_nil_of_length_zero q hqZero
          change rayPathMap a.toPath = rayPathMap b.toPath at hpq
          have hab : rayArrowMorphism a = rayArrowMorphism b := by
            simpa only [rayPathMap_toPath] using hpq
          have : a = b := Subtype.ext hab
          subst b
          rfl

/-- Related one-arrow ray paths are equal. -/
theorem rayPath_eq_of_related_of_length_eq_one
    [IsFiniteRayCategory C]
    {x z : RayVertex C} (p q : Quiver.Path x z)
    (hpq : (rayPathContourRelation (C := C)).related p q)
    (hpOne : p.length = 1) : p = q := by
  exact rayPath_eq_of_length_eq_one_of_rayPathMap_eq p q hpOne
    (rayPath_length_eq_one_of_related_of_length_eq_one p q hpq hpOne)
    hpq.2

/-- A nonzero one-arrow ray has exactly one proper-whisker interlacement
class. -/
theorem relatedRayPathInterlacementClass_card_eq_one_of_length_eq_one
    [IsFiniteRayCategory C]
    {x z : RayVertex C} (p : Quiver.Path x z)
    (hpOne : p.length = 1)
    (hpp : (rayPathContourRelation (C := C)).related p p) :
    Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 1 := by
  let R := rayPathContourRelation (C := C)
  let I := properWhiskerInterlacementRelation R
  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  · constructor
    intro q r
    rw [← Quotient.out_eq q, ← Quotient.out_eq r]
    apply Quotient.sound
    have hqp := rayPath_eq_of_related_of_length_eq_one
      p q.out.1 q.out.2 hpOne
    have hrp := rayPath_eq_of_related_of_length_eq_one
      p r.out.1 r.out.2 hpOne
    change I.interlaced q.out.1 r.out.1
    rw [← hqp, ← hrp]
    exact I.refl p
  · exact ⟨Quotient.mk'' ⟨p, hpp⟩⟩

/-- For a fixed noninvertible ray path, initial arrows inject its
interlacement classes into the arrows leaving the initial quiver vertex. -/
theorem relatedRayPathInterlacementClass_card_le_outgoing
    [IsFiniteRayCategory C] [HasRayCancellation C]
    {x z : RayVertex C} (p : Quiver.Path x z)
    (hp : ¬IsIso (rayPathMap p)) [Finite (OutgoingQuiverArrow x)] :
    Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) ≤
      Nat.card (OutgoingQuiverArrow x) := by
  let R := rayPathContourRelation (C := C)
  let I := properWhiskerInterlacementRelation R
  apply relatedPathInterlacementClass_card_le_of_code I p
    (fun q ↦ chosenInitialArrow q.1
      (rayPath_length_ne_zero_of_related_of_not_isIso hp q.2))
  intro q r hcode
  apply rayPaths_interlaced_of_initialDecomposition_code_eq
    (chosenPathInitialDecomposition q.1
      (rayPath_length_ne_zero_of_related_of_not_isIso hp q.2))
    (chosenPathInitialDecomposition r.1
      (rayPath_length_ne_zero_of_related_of_not_isIso hp r.2))
  · exact R.trans (R.symm q.2) r.2
  · simpa only [chosenInitialArrow] using hcode

/-- The initial-arrow code makes the interlacement quotient finite. -/
theorem relatedRayPathInterlacementClass_finite_of_initial
    [IsFiniteRayCategory C] [HasRayCancellation C]
    {x z : RayVertex C} (p : Quiver.Path x z)
    (hp : ¬IsIso (rayPathMap p)) [Finite (OutgoingQuiverArrow x)] :
    Finite (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) := by
  let R := rayPathContourRelation (C := C)
  let I := properWhiskerInterlacementRelation R
  apply relatedPathInterlacementClass_finite_of_code I p
    (fun q ↦ chosenInitialArrow q.1
      (rayPath_length_ne_zero_of_related_of_not_isIso hp q.2))
  intro q r hcode
  apply rayPaths_interlaced_of_initialDecomposition_code_eq
    (chosenPathInitialDecomposition q.1
      (rayPath_length_ne_zero_of_related_of_not_isIso hp q.2))
    (chosenPathInitialDecomposition r.1
      (rayPath_length_ne_zero_of_related_of_not_isIso hp r.2))
  · exact R.trans (R.symm q.2) r.2
  · simpa only [chosenInitialArrow] using hcode

/-- Dually, final arrows inject the interlacement classes of a fixed
noninvertible ray path into the arrows entering its final quiver vertex. -/
theorem relatedRayPathInterlacementClass_card_le_incoming
    [IsFiniteRayCategory C] [HasRayCancellation C]
    {x z : RayVertex C} (p : Quiver.Path x z)
    (hp : ¬IsIso (rayPathMap p)) [Finite (IncomingQuiverArrow z)] :
    Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) ≤
      Nat.card (IncomingQuiverArrow z) := by
  let R := rayPathContourRelation (C := C)
  let I := properWhiskerInterlacementRelation R
  apply relatedPathInterlacementClass_card_le_of_code I p
    (fun q ↦ chosenFinalArrow q.1
      (rayPath_length_ne_zero_of_related_of_not_isIso hp q.2))
  intro q r hcode
  apply rayPaths_interlaced_of_finalDecomposition_code_eq
    (chosenPathFinalDecomposition q.1
      (rayPath_length_ne_zero_of_related_of_not_isIso hp q.2))
    (chosenPathFinalDecomposition r.1
      (rayPath_length_ne_zero_of_related_of_not_isIso hp r.2))
  · exact R.trans (R.symm q.2) r.2
  · simpa only [chosenFinalArrow] using hcode

/-- The final-arrow code gives the dual finiteness proof. -/
theorem relatedRayPathInterlacementClass_finite_of_final
    [IsFiniteRayCategory C] [HasRayCancellation C]
    {x z : RayVertex C} (p : Quiver.Path x z)
    (hp : ¬IsIso (rayPathMap p)) [Finite (IncomingQuiverArrow z)] :
    Finite (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) := by
  let R := rayPathContourRelation (C := C)
  let I := properWhiskerInterlacementRelation R
  apply relatedPathInterlacementClass_finite_of_code I p
    (fun q ↦ chosenFinalArrow q.1
      (rayPath_length_ne_zero_of_related_of_not_isIso hp q.2))
  intro q r hcode
  apply rayPaths_interlaced_of_finalDecomposition_code_eq
    (chosenPathFinalDecomposition q.1
      (rayPath_length_ne_zero_of_related_of_not_isIso hp q.2))
    (chosenPathFinalDecomposition r.1
      (rayPath_length_ne_zero_of_related_of_not_isIso hp r.2))
  · exact R.trans (R.symm q.2) r.2
  · simpa only [chosenFinalArrow] using hcode

/-- Under the BGRS local valency hypothesis, the interlacement quotient of a
noninvertible ray path has at most three classes, using its initial arrow. -/
theorem relatedRayPathInterlacementClass_card_le_three_of_initial
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [HasRayValencyAtMostThree C]
    {x z : RayVertex C} (p : Quiver.Path x z)
    (hp : ¬IsIso (rayPathMap p)) :
    Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) ≤ 3 := by
  letI : Finite (OutgoingQuiverArrow x) :=
    outgoingQuiverArrow_finite x
  exact (relatedRayPathInterlacementClass_card_le_outgoing p hp).trans
    (HasRayValencyAtMostThree.outgoing_card_le x)

/-- The dual at-most-three bound obtained by coding a path by its final
arrow. -/
theorem relatedRayPathInterlacementClass_card_le_three_of_final
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [HasRayValencyAtMostThree C]
    {x z : RayVertex C} (p : Quiver.Path x z)
    (hp : ¬IsIso (rayPathMap p)) :
    Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) ≤ 3 := by
  letI : Finite (IncomingQuiverArrow z) :=
    incomingQuiverArrow_finite z
  exact (relatedRayPathInterlacementClass_card_le_incoming p hp).trans
    (HasRayValencyAtMostThree.incoming_card_le z)

/-- A nonzero path of length at least two has at most three related-path
interlacement classes, using its initial-arrow code. -/
theorem relatedRayPathInterlacementClass_card_le_three_of_initial_of_length_two_le
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [HasRayLongPathEndpointValencyAtMostThree C]
    {x z : RayVertex C} (p : Quiver.Path x z)
    (hp : rayPathMap p ≠ 0) (hpLength : 2 ≤ p.length) :
    Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) ≤ 3 := by
  letI : Finite (OutgoingQuiverArrow x) :=
    outgoingQuiverArrow_finite x
  exact (relatedRayPathInterlacementClass_card_le_outgoing p
      (rayPathMap_not_isIso_of_length_ne_zero p (by omega))).trans
    (HasRayLongPathEndpointValencyAtMostThree.outgoing_card_le
      p hp hpLength)

/-- The final-arrow dual of the long-path interlacement-class bound. -/
theorem relatedRayPathInterlacementClass_card_le_three_of_final_of_length_two_le
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [HasRayLongPathEndpointValencyAtMostThree C]
    {x z : RayVertex C} (p : Quiver.Path x z)
    (hp : rayPathMap p ≠ 0) (hpLength : 2 ≤ p.length) :
    Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) ≤ 3 := by
  letI : Finite (IncomingQuiverArrow z) :=
    incomingQuiverArrow_finite z
  exact (relatedRayPathInterlacementClass_card_le_incoming p
      (rayPathMap_not_isIso_of_length_ne_zero p (by omega))).trans
    (HasRayLongPathEndpointValencyAtMostThree.incoming_card_le
      p hp hpLength)

/-- The exact BGRS local case split: a nonempty nonzero ray path has one,
two, or three proper-whisker interlacement classes. -/
theorem relatedRayPathInterlacementClass_card_eq_one_or_two_or_three
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [HasRayLongPathEndpointValencyAtMostThree C]
    {x z : RayVertex C} (p : Quiver.Path x z)
    (hp : p.length ≠ 0)
    (hpp : (rayPathContourRelation (C := C)).related p p) :
    Nat.card (RelatedPathInterlacementClass
        (properWhiskerInterlacementRelation
          (rayPathContourRelation (C := C))) p) = 1 ∨
      Nat.card (RelatedPathInterlacementClass
        (properWhiskerInterlacementRelation
          (rayPathContourRelation (C := C))) p) = 2 ∨
      Nat.card (RelatedPathInterlacementClass
        (properWhiskerInterlacementRelation
          (rayPathContourRelation (C := C))) p) = 3 := by
  by_cases hpOne : p.length = 1
  · exact Or.inl
      (relatedRayPathInterlacementClass_card_eq_one_of_length_eq_one
        p hpOne hpp)
  have hpLength : 2 ≤ p.length := by omega
  let R := rayPathContourRelation (C := C)
  let I := properWhiskerInterlacementRelation R
  letI : Finite (OutgoingQuiverArrow x) :=
    outgoingQuiverArrow_finite x
  letI : Finite (RelatedPathInterlacementClass I p) :=
    relatedRayPathInterlacementClass_finite_of_initial p
      (rayPathMap_not_isIso_of_length_ne_zero p hp)
  letI : Nonempty (RelatedPathInterlacementClass I p) :=
    ⟨Quotient.mk'' ⟨p, hpp⟩⟩
  have hpos : 0 < Nat.card (RelatedPathInterlacementClass I p) :=
    Nat.card_pos
  have hle : Nat.card (RelatedPathInterlacementClass I p) ≤ 3 :=
    relatedRayPathInterlacementClass_card_le_three_of_initial_of_length_two_le
      p hpp.1 hpLength
  have hpos' : 0 < Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) := by
    simpa only [I, R] using hpos
  have hle' : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) ≤ 3 := by
    simpa only [I, R] using hle
  by_cases hOne : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 1
  · exact Or.inl hOne
  by_cases hTwo : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 2
  · exact Or.inr (Or.inl hTwo)
  · exact Or.inr (Or.inr (by omega))

/-- In the `N = 2` ray case, choose an actual representative outside the
interlacement class of the selected path. -/
theorem exists_related_not_interlaced_of_ray_card_eq_two
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    {x z : RayVertex C} (p : Quiver.Path x z)
    (hp : p.length ≠ 0)
    (hpp : (rayPathContourRelation (C := C)).related p p)
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 2) :
    ∃ q : Quiver.Path x z,
      (rayPathContourRelation (C := C)).related p q ∧
        ¬(properWhiskerInterlacementRelation
          (rayPathContourRelation (C := C))).interlaced p q := by
  let R := rayPathContourRelation (C := C)
  let I := properWhiskerInterlacementRelation R
  letI : Finite (OutgoingQuiverArrow x) :=
    outgoingQuiverArrow_finite x
  letI : Finite (RelatedPathInterlacementClass I p) :=
    relatedRayPathInterlacementClass_finite_of_initial p
      (rayPathMap_not_isIso_of_length_ne_zero p hp)
  apply exists_related_not_interlaced_of_one_lt_card I p hpp
  have hcard' : Nat.card (RelatedPathInterlacementClass I p) = 2 := by
    simpa only [I, R] using hcard
  omega

/-- In the `N = 1` ray case, every path representing the selected nonzero
ray lies in the selected path's interlacement class. -/
theorem rayPaths_interlaced_of_card_eq_one
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    {x z : RayVertex C} (p : Quiver.Path x z)
    (hp : p.length ≠ 0)
    (hpp : (rayPathContourRelation (C := C)).related p p)
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 1)
    (q : Quiver.Path x z)
    (hpq : (rayPathContourRelation (C := C)).related p q) :
    (properWhiskerInterlacementRelation
      (rayPathContourRelation (C := C))).interlaced p q := by
  let R := rayPathContourRelation (C := C)
  let I := properWhiskerInterlacementRelation R
  letI : Finite (OutgoingQuiverArrow x) :=
    outgoingQuiverArrow_finite x
  letI : Finite (RelatedPathInterlacementClass I p) :=
    relatedRayPathInterlacementClass_finite_of_initial p
      (rayPathMap_not_isIso_of_length_ne_zero p hp)
  exact (relatedPathInterlacementClass_card_eq_one_iff I p hpp).1
    hcard q hpq

/-- In the `N = 3` ray case, choose the `q,r` representatives used in the
three-class correction, with all three classes pairwise distinct. -/
theorem exists_two_pairwise_noninterlaced_related_of_ray_card_eq_three
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    {x z : RayVertex C} (p : Quiver.Path x z)
    (hp : p.length ≠ 0)
    (hpp : (rayPathContourRelation (C := C)).related p p)
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 3) :
    ∃ q r : Quiver.Path x z,
      (rayPathContourRelation (C := C)).related p q ∧
        (rayPathContourRelation (C := C)).related p r ∧
          ¬(properWhiskerInterlacementRelation
            (rayPathContourRelation (C := C))).interlaced p q ∧
          ¬(properWhiskerInterlacementRelation
            (rayPathContourRelation (C := C))).interlaced p r ∧
          ¬(properWhiskerInterlacementRelation
            (rayPathContourRelation (C := C))).interlaced q r := by
  let R := rayPathContourRelation (C := C)
  let I := properWhiskerInterlacementRelation R
  letI : Finite (OutgoingQuiverArrow x) :=
    outgoingQuiverArrow_finite x
  letI : Finite (RelatedPathInterlacementClass I p) :=
    relatedRayPathInterlacementClass_finite_of_initial p
      (rayPathMap_not_isIso_of_length_ne_zero p hp)
  exact exists_two_pairwise_noninterlaced_related_of_card_eq_three
    I p hpp hcard

/-- The `N = 2` representative can be chosen with an explicitly distinct
initial-arrow code. -/
theorem exists_related_with_distinct_initialArrow_of_ray_card_eq_two
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    {x z : RayVertex C} (p : Quiver.Path x z)
    (hp : p.length ≠ 0)
    (hpp : (rayPathContourRelation (C := C)).related p p)
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 2) :
    ∃ (q : Quiver.Path x z) (hq : q.length ≠ 0),
      (rayPathContourRelation (C := C)).related p q ∧
        chosenInitialArrow p hp ≠ chosenInitialArrow q hq := by
  obtain ⟨q, hpq, hnot⟩ :=
    exists_related_not_interlaced_of_ray_card_eq_two p hp hpp hcard
  have hq : q.length ≠ 0 :=
    rayPath_length_ne_zero_of_related_of_not_isIso
      (rayPathMap_not_isIso_of_length_ne_zero p hp) hpq
  exact ⟨q, hq, hpq,
    chosenInitialArrow_ne_of_not_interlaced hp hq hpq hnot⟩

/-- The `N = 2` representative can dually be chosen with an explicitly
distinct final-arrow code. -/
theorem exists_related_with_distinct_finalArrow_of_ray_card_eq_two
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    {x z : RayVertex C} (p : Quiver.Path x z)
    (hp : p.length ≠ 0)
    (hpp : (rayPathContourRelation (C := C)).related p p)
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 2) :
    ∃ (q : Quiver.Path x z) (hq : q.length ≠ 0),
      (rayPathContourRelation (C := C)).related p q ∧
        chosenFinalArrow p hp ≠ chosenFinalArrow q hq := by
  obtain ⟨q, hpq, hnot⟩ :=
    exists_related_not_interlaced_of_ray_card_eq_two p hp hpp hcard
  have hq : q.length ≠ 0 :=
    rayPath_length_ne_zero_of_related_of_not_isIso
      (rayPathMap_not_isIso_of_length_ne_zero p hp) hpq
  exact ⟨q, hq, hpq,
    chosenFinalArrow_ne_of_not_interlaced hp hq hpq hnot⟩

/-- The `N = 3` representatives have three pairwise distinct initial-arrow
codes, exactly as in the three-arrow figure of BGRS 8.6(d). -/
theorem exists_two_related_with_pairwise_distinct_initialArrows_of_ray_card_eq_three
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    {x z : RayVertex C} (p : Quiver.Path x z)
    (hp : p.length ≠ 0)
    (hpp : (rayPathContourRelation (C := C)).related p p)
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 3) :
    ∃ (q r : Quiver.Path x z) (hq : q.length ≠ 0) (hr : r.length ≠ 0),
      (rayPathContourRelation (C := C)).related p q ∧
        (rayPathContourRelation (C := C)).related p r ∧
        chosenInitialArrow p hp ≠ chosenInitialArrow q hq ∧
        chosenInitialArrow p hp ≠ chosenInitialArrow r hr ∧
        chosenInitialArrow q hq ≠ chosenInitialArrow r hr := by
  obtain ⟨q, r, hpq, hpr, hpqNot, hprNot, hqrNot⟩ :=
    exists_two_pairwise_noninterlaced_related_of_ray_card_eq_three
      p hp hpp hcard
  have hq : q.length ≠ 0 :=
    rayPath_length_ne_zero_of_related_of_not_isIso
      (rayPathMap_not_isIso_of_length_ne_zero p hp) hpq
  have hr : r.length ≠ 0 :=
    rayPath_length_ne_zero_of_related_of_not_isIso
      (rayPathMap_not_isIso_of_length_ne_zero p hp) hpr
  have hqr : (rayPathContourRelation (C := C)).related q r :=
    (rayPathContourRelation (C := C)).trans
      ((rayPathContourRelation (C := C)).symm hpq) hpr
  exact ⟨q, r, hq, hr, hpq, hpr,
    chosenInitialArrow_ne_of_not_interlaced hp hq hpq hpqNot,
    chosenInitialArrow_ne_of_not_interlaced hp hr hpr hprNot,
    chosenInitialArrow_ne_of_not_interlaced hq hr hqr hqrNot⟩

/-- The `N = 3` representatives dually have three pairwise distinct
final-arrow codes. -/
theorem exists_two_related_with_pairwise_distinct_finalArrows_of_ray_card_eq_three
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    {x z : RayVertex C} (p : Quiver.Path x z)
    (hp : p.length ≠ 0)
    (hpp : (rayPathContourRelation (C := C)).related p p)
    (hcard : Nat.card (RelatedPathInterlacementClass
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) p) = 3) :
    ∃ (q r : Quiver.Path x z) (hq : q.length ≠ 0) (hr : r.length ≠ 0),
      (rayPathContourRelation (C := C)).related p q ∧
        (rayPathContourRelation (C := C)).related p r ∧
        chosenFinalArrow p hp ≠ chosenFinalArrow q hq ∧
        chosenFinalArrow p hp ≠ chosenFinalArrow r hr ∧
        chosenFinalArrow q hq ≠ chosenFinalArrow r hr := by
  obtain ⟨q, r, hpq, hpr, hpqNot, hprNot, hqrNot⟩ :=
    exists_two_pairwise_noninterlaced_related_of_ray_card_eq_three
      p hp hpp hcard
  have hq : q.length ≠ 0 :=
    rayPath_length_ne_zero_of_related_of_not_isIso
      (rayPathMap_not_isIso_of_length_ne_zero p hp) hpq
  have hr : r.length ≠ 0 :=
    rayPath_length_ne_zero_of_related_of_not_isIso
      (rayPathMap_not_isIso_of_length_ne_zero p hp) hpr
  have hqr : (rayPathContourRelation (C := C)).related q r :=
    (rayPathContourRelation (C := C)).trans
      ((rayPathContourRelation (C := C)).symm hpq) hpr
  exact ⟨q, r, hq, hr, hpq, hpr,
    chosenFinalArrow_ne_of_not_interlaced hp hq hpq hpqNot,
    chosenFinalArrow_ne_of_not_interlaced hp hr hpr hprNot,
    chosenFinalArrow_ne_of_not_interlaced hq hr hqr hqrNot⟩

end LargeIndecomposable
