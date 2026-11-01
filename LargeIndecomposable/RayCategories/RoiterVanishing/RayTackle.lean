module

public import LargeIndecomposable.RayCategories.Basic.RayMorphismDepth
public import Mathlib.Order.Preorder.Finite

@[expose] public section

/-!
# BGRS chains, tackles, and efficiency

Definition 1.9 of BGRS has two alternating nonfactorization shapes.  A tackle
is such a chain whose last morphism is irreducible; Section 8.4 orders tackles
from one starting object by the lexicographic word of component depths.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace NonzeroHom

/-- Postcompose a nonzero morphism by an isomorphism. -/
def compIsIso {X Y Z : C} (f : NonzeroHom X Y)
    (e : Y ⟶ Z) [IsIso e] : NonzeroHom X Z :=
  ⟨f.1 ≫ e, by
    intro hzero
    apply f.2
    have hcomp := congrArg (fun q ↦ q ≫ inv e) hzero
    simpa [Category.assoc] using hcomp⟩

@[simp]
theorem coe_compIsIso {X Y Z : C} (f : NonzeroHom X Y)
    (e : Y ⟶ Z) [IsIso e] :
    (f.compIsIso e).1 = f.1 ≫ e :=
  rfl

end NonzeroHom

/-- Two nonzero morphisms with a common source do not factor through one
another. -/
def RaySourceIncomparable {X Y Z : C}
    (f : NonzeroHom X Y) (g : NonzeroHom X Z) : Prop :=
  (¬ ∃ h : Y ⟶ Z, f.1 ≫ h = g.1) ∧
  (¬ ∃ h : Z ⟶ Y, g.1 ≫ h = f.1)

/-- Source incomparability is preserved when the two targets are changed by
isomorphisms. -/
theorem RaySourceIncomparable.compIsIso
    {X Y Z Y' Z' : C}
    {f : NonzeroHom X Y} {g : NonzeroHom X Z}
    (hfg : RaySourceIncomparable f g)
    (e : Y ⟶ Y') (d : Z ⟶ Z') [IsIso e] [IsIso d] :
    RaySourceIncomparable (f.compIsIso e) (g.compIsIso d) := by
  constructor
  · rintro ⟨a, ha⟩
    apply hfg.1
    refine ⟨e ≫ a ≫ inv d, ?_⟩
    have hcomp := congrArg (fun q ↦ q ≫ inv d) ha
    simpa [NonzeroHom.compIsIso, Category.assoc] using hcomp
  · rintro ⟨a, ha⟩
    apply hfg.2
    refine ⟨d ≫ a ≫ inv e, ?_⟩
    have hcomp := congrArg (fun q ↦ q ≫ inv e) ha
    simpa [NonzeroHom.compIsIso, Category.assoc] using hcomp

/-- Source incomparability is exactly incomparability in the fixed-source
factorization order. -/
theorem raySourceIncomparable_iff [IsFiniteRayCategory C]
    {X Y Z : C} (f : NonzeroHom X Y) (g : NonzeroHom X Z) :
    RaySourceIncomparable f g ↔
      (¬f.toMorphismFrom ≤ g.toMorphismFrom) ∧
        (¬g.toMorphismFrom ≤ f.toMorphismFrom) := by
  rfl

/-- If `g` is irreducible and `f` is noninvertible, failure of source
incomparability forces `g` to factor through `f`. -/
theorem le_of_not_raySourceIncomparable_of_right_irreducible
    [IsFiniteRayCategory C]
    {X Y Z : C} (f : NonzeroHom X Y) (g : NonzeroHom X Z)
    (hg : IsIrreducibleRayMorphism g.1) (hf : ¬IsIso f.1)
    (hfg : ¬RaySourceIncomparable f g) :
    g.toMorphismFrom ≤ f.toMorphismFrom := by
  by_cases hgf : g.toMorphismFrom ≤ f.toMorphismFrom
  · exact hgf
  have hfle : f.toMorphismFrom ≤ g.toMorphismFrom := by
    by_contra hfg'
    exact hfg ((raySourceIncomparable_iff f g).2 ⟨hfg', hgf⟩)
  exact NonzeroMorphismFrom.reverse_le_of_le_irreducible_of_noniso
    hfle hg hf

/-- Two nonzero morphisms with a common target do not factor through one
another. -/
def RayTargetIncomparable {X Y Z : C}
    (f : NonzeroHom X Z) (g : NonzeroHom Y Z) : Prop :=
  (¬ ∃ h : X ⟶ Y, h ≫ g.1 = f.1) ∧
  (¬ ∃ h : Y ⟶ X, h ≫ f.1 = g.1)

/-- Target incomparability is preserved when the common target is changed by
an isomorphism. -/
theorem RayTargetIncomparable.compIsIso
    {X Y Z Z' : C}
    {f : NonzeroHom X Z} {g : NonzeroHom Y Z}
    (hfg : RayTargetIncomparable f g)
    (e : Z ⟶ Z') [IsIso e] :
    RayTargetIncomparable (f.compIsIso e) (g.compIsIso e) := by
  constructor
  · rintro ⟨a, ha⟩
    apply hfg.1
    refine ⟨a, ?_⟩
    have hcomp := congrArg (fun q ↦ q ≫ inv e) ha
    simpa [NonzeroHom.compIsIso, Category.assoc] using hcomp
  · rintro ⟨a, ha⟩
    apply hfg.2
    refine ⟨a, ?_⟩
    have hcomp := congrArg (fun q ↦ q ≫ inv e) ha
    simpa [NonzeroHom.compIsIso, Category.assoc] using hcomp

/-- The first chain shape of BGRS 1.9.  It has `m+1` morphisms `rho`,
`m` morphisms `sigma`, and ends with `rho_m`; the associated tackle is a hook
tackle. -/
structure RayHookChain (m : ℕ) where
  x : Fin (m + 1) → C
  z : Fin (m + 1) → C
  rho : ∀ i : Fin (m + 1), NonzeroHom (x i) (z i)
  sigma : ∀ i : Fin m, NonzeroHom (x i.succ) (z i.castSucc)
  peak_incomparable : ∀ i : Fin m,
    RayTargetIncomparable (rho i.castSucc) (sigma i)
  valley_incomparable : ∀ i : Fin m,
    RaySourceIncomparable (sigma i) (rho i.succ)

/-- The second chain shape of BGRS 1.9.  It has `m+1` morphisms of each kind
and ends with `sigma_m`; the associated tackle is a cohook tackle. -/
structure RayCohookChain (m : ℕ) where
  x : Fin (m + 2) → C
  z : Fin (m + 1) → C
  rho : ∀ i : Fin (m + 1), NonzeroHom (x i.castSucc) (z i)
  sigma : ∀ i : Fin (m + 1), NonzeroHom (x i.succ) (z i)
  peak_incomparable : ∀ i : Fin (m + 1),
    RayTargetIncomparable (rho i) (sigma i)
  valley_incomparable : ∀ i : Fin m,
    RaySourceIncomparable (sigma i.castSucc) (rho i.succ)

/-- A hook tackle: a first-shape chain whose last `rho` is irreducible. -/
structure RayHookTackle (m : ℕ) extends RayHookChain (C := C) m where
  last_irreducible :
    IsIrreducibleRayMorphism (rho (Fin.last m)).1

/-- A cohook tackle: a second-shape chain whose last `sigma` is irreducible. -/
structure RayCohookTackle (m : ℕ) extends RayCohookChain (C := C) m where
  last_irreducible :
    IsIrreducibleRayMorphism (sigma (Fin.last m)).1

/-- Alternate two lists, beginning with the first.  For the BGRS depth words
the lists have equal lengths or the first has one additional entry. -/
def alternateLists {α : Type*} : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => x :: y :: alternateLists xs ys

@[simp]
theorem length_alternateLists {alpha : Type*} (xs ys : List alpha) :
    (alternateLists xs ys).length = xs.length + ys.length := by
  induction xs generalizing ys with
  | nil => simp [alternateLists]
  | cons x xs ih =>
      cases ys with
      | nil => simp [alternateLists]
      | cons y ys =>
          simp [alternateLists, ih]
          omega

/-- Efficiency word of a hook tackle, in the source order
`d(rho_0), d(sigma_0), ..., d(rho_m)`. -/
def RayHookTackle.efficiency [HasFiniteRayPathDepth C]
    {m : ℕ} (t : RayHookTackle (C := C) m) : List ℕ :=
  alternateLists
    (List.ofFn fun i => (t.rho i).depth)
    (List.ofFn fun i => (t.sigma i).depth)

/-- Efficiency word of a cohook tackle, in the source order
`d(rho_0), d(sigma_0), ..., d(rho_m), d(sigma_m)`. -/
def RayCohookTackle.efficiency [HasFiniteRayPathDepth C]
    {m : ℕ} (t : RayCohookTackle (C := C) m) : List ℕ :=
  alternateLists
    (List.ofFn fun i => (t.rho i).depth)
    (List.ofFn fun i => (t.sigma i).depth)

@[simp]
theorem RayHookTackle.length_efficiency [HasFiniteRayPathDepth C]
    {m : ℕ} (t : RayHookTackle (C := C) m) :
    t.efficiency.length = 2 * m + 1 := by
  simp [RayHookTackle.efficiency]
  omega

@[simp]
theorem RayCohookTackle.length_efficiency [HasFiniteRayPathDepth C]
    {m : ℕ} (t : RayCohookTackle (C := C) m) :
    t.efficiency.length = 2 * (m + 1) := by
  simp [RayCohookTackle.efficiency]
  omega

/-- The hook of a tackle has depth one. -/
theorem RayHookTackle.last_depth_eq_one
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    {m : ℕ} (t : RayHookTackle (C := C) m) :
    (t.rho (Fin.last m)).depth = 1 :=
  rayMorphismDepth_eq_one_of_irreducible _ t.last_irreducible

/-- Compatibility needed to replace the last hook of a hook tackle.  There is
no condition for a one-morphism tackle; otherwise the replacement must remain
incomparable with the preceding `sigma`. -/
def RayHookTackle.LastReplacementCompatible
    {m : ℕ} (t : RayHookTackle (C := C) m)
    {Z : C} (f : NonzeroHom (t.x (Fin.last m)) Z) : Prop :=
  match m with
  | 0 => True
  | n + 1 => RaySourceIncomparable (t.sigma (Fin.last n)) f

/-- `s` is a chosen supremum of two elements in a fixed-source ray
factorization order. -/
def IsRayPairSupremum {X : C} (f g s : NonzeroMorphismFrom X) : Prop :=
  f ≤ s ∧ g ≤ s ∧
    ∀ u : NonzeroMorphismFrom X, f ≤ u → g ≤ u → s ≤ u

/-- The middle-arrow condition extracted from the four BGRS 8.5 poset
figures: every common upper bound of the two outer arrows also bounds the
middle arrow. -/
def RayThreeArrowMiddleCondition {X B G D : C}
    (beta : NonzeroHom X B) (gamma : NonzeroHom X G)
    (delta : NonzeroHom X D) : Prop :=
  ∀ u : NonzeroMorphismFrom X,
    beta.toMorphismFrom ≤ u → delta.toMorphismFrom ≤ u →
      gamma.toMorphismFrom ≤ u

/-- A middle arrow below the supremum of the two outer arrows satisfies the
three-arrow middle condition. -/
theorem rayThreeArrowMiddleCondition_of_le_supremum
    {X B G D : C}
    (beta : NonzeroHom X B) (gamma : NonzeroHom X G)
    (delta : NonzeroHom X D) (s : NonzeroMorphismFrom X)
    (hs : IsRayPairSupremum beta.toMorphismFrom delta.toMorphismFrom s)
    (hgamma : gamma.toMorphismFrom ≤ s) :
    RayThreeArrowMiddleCondition beta gamma delta := by
  intro u hbeta hdelta
  exact hgamma.trans (hs.2.2 u hbeta hdelta)

/-- The order-theoretic core of BGRS 8.5 for a hook tackle.  If the current
hook lies below every common upper bound of two alternative irreducible
arrows, then at least one alternative is compatible with the preceding
`sigma` and can serve as a replacement last hook. -/
theorem RayHookTackle.lastReplacementCompatible_or
    [IsFiniteRayCategory C]
    {m : ℕ} (t : RayHookTackle (C := C) m)
    {B D : C}
    (beta : NonzeroHom (t.x (Fin.last m)) B)
    (delta : NonzeroHom (t.x (Fin.last m)) D)
    (hbeta : IsIrreducibleRayMorphism beta.1)
    (hdelta : IsIrreducibleRayMorphism delta.1)
    (hforced : RayThreeArrowMiddleCondition beta
      (t.rho (Fin.last m)) delta) :
    t.LastReplacementCompatible beta ∨
      t.LastReplacementCompatible delta := by
  cases m with
  | zero => simp [LastReplacementCompatible]
  | succ n =>
      let sigma := t.sigma (Fin.last n)
      let gamma := t.rho (Fin.last (n + 1))
      have hvalley : RaySourceIncomparable sigma gamma := by
        simpa [sigma, gamma] using t.valley_incomparable (Fin.last n)
      have hsigmaIso : ¬IsIso sigma.1 := by
        intro hsigma
        apply hvalley.1
        letI : IsIso sigma.1 := hsigma
        refine ⟨inv sigma.1 ≫ gamma.1, ?_⟩
        rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
      by_contra hcompat
      push Not at hcompat
      have hbetaSigma : beta.toMorphismFrom ≤ sigma.toMorphismFrom :=
        le_of_not_raySourceIncomparable_of_right_irreducible
          sigma beta hbeta hsigmaIso (by
            simpa [LastReplacementCompatible, sigma] using hcompat.1)
      have hdeltaSigma : delta.toMorphismFrom ≤ sigma.toMorphismFrom :=
        le_of_not_raySourceIncomparable_of_right_irreducible
          sigma delta hdelta hsigmaIso (by
            simpa [LastReplacementCompatible, sigma] using hcompat.2)
      have hgammaSigma : gamma.toMorphismFrom ≤ sigma.toMorphismFrom := by
        simpa [gamma] using hforced sigma.toMorphismFrom
          hbetaSigma hdeltaSigma
      exact hvalley.2 hgammaSigma

/-- The cohook of a tackle has depth one. -/
theorem RayCohookTackle.last_depth_eq_one
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    {m : ℕ} (t : RayCohookTackle (C := C) m) :
    (t.sigma (Fin.last m)).depth = 1 :=
  rayMorphismDepth_eq_one_of_irreducible _ t.last_irreducible

/-- Compatibility needed to replace the last cohook while retaining the last
old peak. -/
def RayCohookTackle.LastReplacementCompatible {m : ℕ}
    (t : RayCohookTackle (C := C) m)
    {X : C} (f : NonzeroHom X (t.z (Fin.last m))) : Prop :=
  RayTargetIncomparable (t.rho (Fin.last m)) f

/-- The fixed-target dual of the BGRS three-arrow middle condition: every
common lower bound of the two outer arrows also lies below the middle arrow. -/
def RayCoThreeArrowMiddleCondition {X B G D : C}
    (beta : NonzeroHom B X) (gamma : NonzeroHom G X)
    (delta : NonzeroHom D X) : Prop :=
  ∀ u : NonzeroMorphismTo X,
    u ≤ beta.toMorphismTo → u ≤ delta.toMorphismTo →
      u ≤ gamma.toMorphismTo

/-- `s` is a chosen infimum of two elements in a fixed-target ray
factorization order. -/
def IsRayPairInfimum {X : C} (f g s : NonzeroMorphismTo X) : Prop :=
  s ≤ f ∧ s ≤ g ∧
    ∀ u : NonzeroMorphismTo X, u ≤ f → u ≤ g → u ≤ s

/-- A middle arrow above the infimum of the two outer arrows satisfies the
cohook-dual three-arrow middle condition. -/
theorem rayCoThreeArrowMiddleCondition_of_infimum_le
    {X B G D : C}
    (beta : NonzeroHom B X) (gamma : NonzeroHom G X)
    (delta : NonzeroHom D X) (s : NonzeroMorphismTo X)
    (hs : IsRayPairInfimum beta.toMorphismTo delta.toMorphismTo s)
    (hgamma : s ≤ gamma.toMorphismTo) :
    RayCoThreeArrowMiddleCondition beta gamma delta := by
  intro u hbeta hdelta
  exact (hs.2.2 u hbeta hdelta).trans hgamma

/-- If `g` is irreducible and `f` is noninvertible, failure of target
incomparability forces `f` below `g` in the fixed-target order. -/
theorem le_of_not_rayTargetIncomparable_of_right_irreducible
    [IsFiniteRayCategory C]
    {X Y Z : C} (f : NonzeroHom X Z) (g : NonzeroHom Y Z)
    (hg : IsIrreducibleRayMorphism g.1) (hf : ¬IsIso f.1)
    (hfg : ¬RayTargetIncomparable f g) :
    f.toMorphismTo ≤ g.toMorphismTo := by
  by_cases hfle : f.toMorphismTo ≤ g.toMorphismTo
  · exact hfle
  have hgfle : g.toMorphismTo ≤ f.toMorphismTo := by
    by_contra hgf
    exact hfg ⟨hfle, hgf⟩
  exact NonzeroMorphismTo.reverse_le_of_le_irreducible_of_noniso
    hgfle hg hf

/-- The fixed-target order-theoretic core of the cohook-dual BGRS 8.5
replacement. -/
theorem RayCohookTackle.lastReplacementCompatible_or
    [IsFiniteRayCategory C]
    {m : ℕ} (t : RayCohookTackle (C := C) m)
    {B D : C}
    (beta : NonzeroHom B (t.z (Fin.last m)))
    (delta : NonzeroHom D (t.z (Fin.last m)))
    (hbeta : IsIrreducibleRayMorphism beta.1)
    (hdelta : IsIrreducibleRayMorphism delta.1)
    (hforced : RayCoThreeArrowMiddleCondition beta
      (t.sigma (Fin.last m)) delta) :
    t.LastReplacementCompatible beta ∨
      t.LastReplacementCompatible delta := by
  let rho := t.rho (Fin.last m)
  let gamma := t.sigma (Fin.last m)
  have hpeak : RayTargetIncomparable rho gamma := by
    simpa [rho, gamma] using t.peak_incomparable (Fin.last m)
  have hrhoIso : ¬IsIso rho.1 := by
    intro hrho
    apply hpeak.2
    letI : IsIso rho.1 := hrho
    refine ⟨gamma.1 ≫ inv rho.1, ?_⟩
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  by_contra hcompat
  push Not at hcompat
  have hrhoBeta : rho.toMorphismTo ≤ beta.toMorphismTo :=
    le_of_not_rayTargetIncomparable_of_right_irreducible
      rho beta hbeta hrhoIso (by
        simpa [LastReplacementCompatible, rho] using hcompat.1)
  have hrhoDelta : rho.toMorphismTo ≤ delta.toMorphismTo :=
    le_of_not_rayTargetIncomparable_of_right_irreducible
      rho delta hdelta hrhoIso (by
        simpa [LastReplacementCompatible, rho] using hcompat.2)
  have hrhoGamma : rho.toMorphismTo ≤ gamma.toMorphismTo := by
    simpa [gamma] using hforced rho.toMorphismTo hrhoBeta hrhoDelta
  exact hpeak.1 hrhoGamma

/-- A tackle is one of the two chain shapes from BGRS 1.9 with irreducible
last morphism. -/
inductive RayTackle (C : Type u) [Category.{v} C] [HasZeroMorphisms C] :
    Type (max u v)
  | hook (m : ℕ) (t : RayHookTackle (C := C) m)
  | cohook (m : ℕ) (t : RayCohookTackle (C := C) m)

namespace RayTackle

/-- The point `x_0` at which a tackle starts. -/
def start : RayTackle C → C
  | .hook _ t => t.x 0
  | .cohook _ t => t.x 0

/-- The lexicographic depth word of a tackle. -/
def efficiency [HasFiniteRayPathDepth C] : RayTackle C → List ℕ
  | .hook _ t => t.efficiency
  | .cohook _ t => t.efficiency

/-- A tackle is efficient at `y` when it starts at `y` and no tackle starting
there has a strictly larger lexicographic depth word. -/
def IsEfficientAt [HasFiniteRayPathDepth C] (y : C)
    (t : RayTackle C) : Prop :=
  t.start = y ∧
    ∀ s : RayTackle C, s.start = y →
      ¬ List.Lex (fun a b : ℕ => a < b) t.efficiency s.efficiency

/-- If only finitely many tackles exist, every start which supports a tackle
supports an efficient one.  In BGRS this finiteness is obtained from local
finiteness and the no-infinite-chain hypothesis by König's theorem. -/
theorem exists_isEfficientAt_of_exists_start
    [HasFiniteRayPathDepth C] [Finite (RayTackle C)]
    (y : C) (hy : ∃ t : RayTackle C, t.start = y) :
    ∃ t : RayTackle C, t.IsEfficientAt y := by
  classical
  let S : Set (RayTackle C) := {t | t.start = y}
  have hSfinite : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := by
    obtain ⟨t, ht⟩ := hy
    exact ⟨t, ht⟩
  obtain ⟨t, htS, htmax⟩ :=
    hSfinite.exists_maximalFor RayTackle.efficiency S hSne
  refine ⟨t, htS, ?_⟩
  intro s hs hlex
  have hlt : t.efficiency < s.efficiency :=
    (List.lt_iff_lex_lt _ _).2 hlex
  exact (not_le_of_gt hlt) (htmax hs (le_of_lt hlt))

end RayTackle

end LargeIndecomposable
