module

public import LargeIndecomposable.RayCategories.Contours.ContourSparseCorrection

@[expose] public section

/-!
# Essential path contours and arrow occurrences

Package the occurrence conditions used around BGRS Lemma 8.4.  An essential
contour is a related pair outside one interlacement class.  Prefix triviality
in a quiver prevents an initial occurrence from recurring in the remaining
tail.  For the reversed ray quiver, the direct translation of the source's
left-to-right path prefix is instead the suffix-triviality predicate below.
-/

set_option autoImplicit false
noncomputable section

namespace LargeIndecomposable

universe u v

variable {Q : Type u} [Quiver.{v} Q]

/-- A related path pair which is not interlaced. -/
def IsEssentialPathContour
    (R : PathContourRelation Q) (I : PathInterlacementRelation R)
    {x y : Q} (p q : Quiver.Path x y) : Prop :=
  R.related p q ∧ ¬I.interlaced p q

namespace IsEssentialPathContour

/-- Essentiality is symmetric in the two paths. -/
theorem symm {R : PathContourRelation Q} {I : PathInterlacementRelation R}
    {x y : Q} {p q : Quiver.Path x y}
    (h : IsEssentialPathContour R I p q) :
    IsEssentialPathContour R I q p := by
  exact ⟨R.symm h.1, fun hqp => h.2 (I.symm hqp)⟩

end IsEssentialPathContour

/-- An occurrence of one bundled arrow in a path, with the prefix and suffix
on either side exposed. -/
structure BundledArrowOccurrence (a : BundledQuiverArrow Q)
    {x y : Q} (p : Quiver.Path x y) where
  before : Quiver.Path x (a.1)
  after : Quiver.Path (a.2.1) y
  path_eq : p = (before.comp (a.2.2).toPath).comp after

namespace BundledArrowOccurrence

/-- Prepending a path preserves an arrow occurrence and extends its prefix. -/
def prepend {a : BundledQuiverArrow Q} {w x y : Q}
    {p : Quiver.Path x y} (o : BundledArrowOccurrence a p)
    (r : Quiver.Path w x) : BundledArrowOccurrence a (r.comp p) where
  before := r.comp o.before
  after := o.after
  path_eq := by
    calc
      r.comp p =
          r.comp ((o.before.comp (a.2.2).toPath).comp o.after) :=
        congrArg (fun s => r.comp s) o.path_eq
      _ = ((r.comp o.before).comp (a.2.2).toPath).comp o.after := by
        simp only [← Quiver.Path.comp_assoc]

@[simp]
theorem prepend_before_length {a : BundledQuiverArrow Q} {w x y : Q}
    {p : Quiver.Path x y} (o : BundledArrowOccurrence a p)
    (r : Quiver.Path w x) :
    (o.prepend r).before.length = r.length + o.before.length := by
  simp [prepend]

/-- Appending a path preserves an arrow occurrence and extends its suffix. -/
def append {a : BundledQuiverArrow Q} {x y z : Q}
    {p : Quiver.Path x y} (o : BundledArrowOccurrence a p)
    (r : Quiver.Path y z) : BundledArrowOccurrence a (p.comp r) where
  before := o.before
  after := o.after.comp r
  path_eq := by
    calc
      p.comp r =
          ((o.before.comp (a.2.2).toPath).comp o.after).comp r :=
        congrArg (fun s => s.comp r) o.path_eq
      _ = (o.before.comp (a.2.2).toPath).comp (o.after.comp r) := by
        exact Quiver.Path.comp_assoc _ _ _

@[simp]
theorem append_after_length {a : BundledQuiverArrow Q} {x y z : Q}
    {p : Quiver.Path x y} (o : BundledArrowOccurrence a p)
    (r : Quiver.Path y z) :
    (o.append r).after.length = o.after.length + r.length := by
  simp [append]

end BundledArrowOccurrence

/-- A positive singleton-selector count exposes an occurrence of the selected
arrow in the path. -/
theorem exists_bundledArrowOccurrence_of_selectedArrowCount_ne_zero
    (a : BundledQuiverArrow Q) {x y : Q} (p : Quiver.Path x y)
    (hcount : selectedArrowCount (singleArrowSelector a) p ≠ 0) :
    Nonempty (BundledArrowOccurrence a p) := by
  induction p with
  | nil => simp [selectedArrowCount] at hcount
  | @cons z y p b ih =>
      by_cases hb : bundledQuiverArrow b = a
      · subst a
        refine ⟨⟨p, Quiver.Path.nil, ?_⟩⟩
        simp [bundledQuiverArrow, Quiver.Path.comp_toPath_eq_cons]
      · have hpCount :
            selectedArrowCount
                (singleArrowSelector a) p ≠ 0 := by
          simpa [selectedArrowCount, singleArrowSelector, hb] using hcount
        obtain ⟨o⟩ := ih hpCount
        refine ⟨⟨o.before, o.after.cons b, ?_⟩⟩
        calc
          p.cons b =
              ((o.before.comp (a.2.2).toPath).comp o.after).cons b :=
            congrArg (fun s => s.cons b) o.path_eq
          _ = (o.before.comp (a.2.2).toPath).comp (o.after.cons b) := by
            simp

/-- Quiver-prefix triviality isolated for one arrow: whenever that arrow
occurs in the left side of an essential contour, the prefix before the
occurrence is an identity path. -/
def EssentialContourArrowPrefixTrivial
    (R : PathContourRelation Q) (I : PathInterlacementRelation R)
    (a : BundledQuiverArrow Q) : Prop :=
  ∀ {x y : Q} (p q : Quiver.Path x y),
    IsEssentialPathContour R I p q →
      ∀ o : BundledArrowOccurrence a p, o.before.length = 0

/-- The orientation-dual occurrence condition: the path after the selected
arrow is an identity in every essential contour.  For the reversed ray quiver
this is the direct translation of BGRS 8.4, because BGRS composes paths from
left to right in the underlying ray category. -/
def EssentialContourArrowSuffixTrivial
    (R : PathContourRelation Q) (I : PathInterlacementRelation R)
    (a : BundledQuiverArrow Q) : Prop :=
  ∀ {x y : Q} (p q : Quiver.Path x y),
    IsEssentialPathContour R I p q →
      ∀ o : BundledArrowOccurrence a p, o.after.length = 0

/-- Prefix triviality prevents the selected arrow from occurring in the tail
after any initial arrow of an essential contour. -/
theorem selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
    (R : PathContourRelation Q) (I : PathInterlacementRelation R)
    (selected : BundledQuiverArrow Q)
    {x y z : Q} (a : x ⟶ y) (tail : Quiver.Path y z)
    (q : Quiver.Path x z)
    (hessential : IsEssentialPathContour R I (a.toPath.comp tail) q)
    (hprefix : EssentialContourArrowPrefixTrivial R I selected) :
    selectedArrowCount (singleArrowSelector selected) tail = 0 := by
  by_contra hcount
  obtain ⟨o⟩ :=
    exists_bundledArrowOccurrence_of_selectedArrowCount_ne_zero
      selected tail hcount
  let o' := o.prepend a.toPath
  have hzero : o'.before.length = 0 :=
    hprefix (a.toPath.comp tail) q hessential o'
  have hpos : 0 < o'.before.length := by
    simp [o', BundledArrowOccurrence.prepend]
  omega

/-- In particular, an initial arrow satisfying prefix triviality does not
recur in its own tail. -/
theorem selectedInitialArrowCount_tail_eq_zero_of_essential_prefixTrivial
    (R : PathContourRelation Q) (I : PathInterlacementRelation R)
    {x y z : Q} (a : x ⟶ y) (tail : Quiver.Path y z)
    (q : Quiver.Path x z)
    (hessential : IsEssentialPathContour R I (a.toPath.comp tail) q)
    (hprefix : EssentialContourArrowPrefixTrivial R I
      (bundledQuiverArrow a)) :
    selectedArrowCount (singleArrowSelector (bundledQuiverArrow a))
      tail = 0 :=
  selectedArrowCount_tail_eq_zero_of_essential_prefixTrivial
    R I (bundledQuiverArrow a) a tail q hessential hprefix

/-- Suffix triviality prevents the selected arrow from occurring in the head
before any final arrow of an essential contour. -/
theorem selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
    (R : PathContourRelation Q) (I : PathInterlacementRelation R)
    (selected : BundledQuiverArrow Q)
    {x y z : Q} (head : Quiver.Path x y) (a : y ⟶ z)
    (q : Quiver.Path x z)
    (hessential : IsEssentialPathContour R I (head.comp a.toPath) q)
    (hsuffix : EssentialContourArrowSuffixTrivial R I selected) :
    selectedArrowCount (singleArrowSelector selected) head = 0 := by
  by_contra hcount
  obtain ⟨o⟩ :=
    exists_bundledArrowOccurrence_of_selectedArrowCount_ne_zero
      selected head hcount
  let o' := o.append a.toPath
  have hzero : o'.after.length = 0 :=
    hsuffix (head.comp a.toPath) q hessential o'
  have hpos : 0 < o'.after.length := by
    simp [o', BundledArrowOccurrence.append]
  omega

/-- In particular, a final arrow satisfying suffix triviality does not recur
in its own head. -/
theorem selectedFinalArrowCount_head_eq_zero_of_essential_suffixTrivial
    (R : PathContourRelation Q) (I : PathInterlacementRelation R)
    {x y z : Q} (head : Quiver.Path x y) (a : y ⟶ z)
    (q : Quiver.Path x z)
    (hessential : IsEssentialPathContour R I (head.comp a.toPath) q)
    (hsuffix : EssentialContourArrowSuffixTrivial R I
      (bundledQuiverArrow a)) :
    selectedArrowCount (singleArrowSelector (bundledQuiverArrow a))
      head = 0 :=
  selectedArrowCount_head_eq_zero_of_essential_suffixTrivial
    R I (bundledQuiverArrow a) head a q hessential hsuffix

end LargeIndecomposable
