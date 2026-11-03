module

public import LargeIndecomposable.Coverings.UniversalCover.CoverIrr
public import LargeIndecomposable.RayCategories.Basic.RayQuiver
public import LargeIndecomposable.RepresentationEmbeddings.CoveringConstruction.Datum
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

/-!
# Finite pieces of the universal cover as covering data

For a finite ray category `P` and a finite set `S` of objects of its universal
cover, the irreducible morphisms of the cover between objects of `S` form a
finite quiver `D_S`, the projection gives a locally injective morphism of
quivers `D_S → Q_P`, and the deck action of `Π(P, x₀)` makes this covering
data in the sense of Definition 3.5 of the paper (`RayCat.coverPieceData`),
given that `Π(P, x₀)` is torsion-free (it is free by Bongartz's Theorem 2).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits FinQuiver

namespace RayCat

open Cover

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} (S : Finset (Cover x₀))

/-- The arrows of the piece: irreducible morphisms of the cover inside `S`. -/
def PieceArr : Type := Σ (a b : S), {f : (a : Cover x₀) ⟶ b // IsIrreducible f}

open Classical in
noncomputable instance : Fintype (PieceArr S) := by
  haveI : ∀ a b : Cover x₀, Finite (a ⟶ b) := IsRayCategory.finite_hom
  haveI : ∀ a b : Cover x₀, Fintype (a ⟶ b) := fun _ _ ↦ Fintype.ofFinite _
  unfold PieceArr; infer_instance

open Classical in
noncomputable instance : DecidableEq (PieceArr S) := Classical.decEq _

open Classical in
/-- The finite quiver `D_S`. -/
noncomputable def pieceQuiver : FinQuiver where
  V := S
  A := PieceArr S
  src α := α.1
  tgt α := α.2.1

/-- The projection `D_S → Q_P`. -/
def pieceProj : FinQuiver.Hom (pieceQuiver S) (RayQuiver.quiver P) where
  vert a := (show S from a).1.y
  arr α := ⟨_, _, val α.2.2.1, isIrreducible_val α.2.2.2⟩
  map_src _ := rfl
  map_tgt _ := rfl

omit [Fintype P] [DecidableEq P] in
/-- Two nonzero morphisms from `a` with the same value have the same target. -/
lemma target_eq {a b b' : Cover x₀} (f : NZHom a b) (f' : NZHom a b') (hy : b.y = b'.y)
    (hv : HEq f.1 f'.1) : b = b' := by
  obtain ⟨y, u⟩ := b
  obtain ⟨y', u'⟩ := b'
  change y = y' at hy
  subst hy
  have hv' : f.1 = f'.1 := eq_of_heq hv
  obtain ⟨g, hg0, hgu⟩ := f
  obtain ⟨g', hg0', hgu'⟩ := f'
  change g = g' at hv'
  subst hv'
  change u = a.u ≫ cls g hg0 at hgu
  change u' = a.u ≫ cls g hg0' at hgu'
  rw [hgu, hgu']

omit [Fintype P] [DecidableEq P] in
/-- Two nonzero morphisms into `b` with the same value have the same source. -/
lemma source_eq {a a' b : Cover x₀} (f : NZHom a b) (f' : NZHom a' b) (hy : a.y = a'.y)
    (hv : HEq f.1 f'.1) : a = a' := by
  obtain ⟨y, u⟩ := a
  obtain ⟨y', u'⟩ := a'
  change y = y' at hy
  subst hy
  have hv' : f.1 = f'.1 := eq_of_heq hv
  obtain ⟨g, hg0, hgu⟩ := f
  obtain ⟨g', hg0', hgu'⟩ := f'
  change g = g' at hv'
  subst hv'
  change b.u = u ≫ cls g hg0 at hgu
  change b.u = u' ≫ cls g hg0' at hgu'
  have : u ≫ cls g hg0 = u' ≫ cls g hg0 := hgu.symm.trans hgu'
  rw [cancel_mono] at this
  rw [this]

/-- The label of an arrow as a morphism of `P`. -/
def labelMor (t : RayQuiver.Arr P) : RayMor P := ⟨t.1, t.2.1, t.2.2.1⟩

/-- The label of an arrow, indexed by target first. -/
def labelMorOp (t : RayQuiver.Arr P) : Σ (y x : P), x ⟶ y := ⟨t.2.1, t.1, t.2.2.1⟩

lemma pieceProj_locInj : (pieceProj S).LocallyInjective := by
  constructor
  · rintro ⟨a, b, f, hf⟩ ⟨a', b', f', hf'⟩ hs hl
    change a = a' at hs
    subst hs
    rcases f with _ | f
    · exact absurd rfl hf.1
    rcases f' with _ | f'
    · exact absurd rfl hf'.1
    have hm := congrArg labelMor hl
    obtain ⟨-, h1⟩ := Sigma.mk.inj hm
    obtain ⟨hy, hv⟩ := Sigma.mk.inj (eq_of_heq h1)
    have hb : (b : Cover x₀) = b' := target_eq f f' hy hv
    obtain ⟨b, hbS⟩ := b
    obtain ⟨b', hbS'⟩ := b'
    change b = b' at hb
    subst hb
    have hff : f = f' := Subtype.ext (eq_of_heq hv)
    subst hff
    rfl
  · rintro ⟨a, b, f, hf⟩ ⟨a', b', f', hf'⟩ ht hl
    change b = b' at ht
    subst ht
    rcases f with _ | f
    · exact absurd rfl hf.1
    rcases f' with _ | f'
    · exact absurd rfl hf'.1
    have hm := congrArg labelMorOp hl
    obtain ⟨-, h1⟩ := Sigma.mk.inj hm
    obtain ⟨hy, hv⟩ := Sigma.mk.inj (eq_of_heq h1)
    have ha : (a : Cover x₀) = a' := source_eq f f' hy hv
    obtain ⟨a, haS⟩ := a
    obtain ⟨a', haS'⟩ := a'
    change a = a' at ha
    subst ha
    have hff : f = f' := Subtype.ext (eq_of_heq hv)
    subst hff
    rfl

omit [Fintype P] [DecidableEq P] in
lemma target_eq' {a a' b b' : Cover x₀} (f : NZHom a b) (f' : NZHom a' b') (ha : a = a')
    (hy : b.y = b'.y) (hv : HEq f.1 f'.1) : b = b' := by
  subst ha
  exact target_eq f f' hy hv

omit [IsRayCategory P] [Fintype P] [DecidableEq P] in
lemma sigma_heq {A A' : P} (hA : A = A') (s : Σ y, A ⟶ y) (s' : Σ y, A' ⟶ y) (h : HEq s s') :
    s.1 = s'.1 ∧ HEq s.2 s'.2 := by
  subst hA
  have := eq_of_heq h
  subst this
  exact ⟨rfl, HEq.rfl⟩

/-- A finite piece of the universal cover as covering data, given that the
fundamental group is torsion-free. -/
def coverPieceData (htf : ∀ g : Pi1 x₀, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1) :
    Covering.CoverData (pieceProj S) where
  G := Pi1 x₀
  torsionFree := htf
  R₀ := Cover x₀
  free _ _ h := smul_eq_self h
  ι a := (show S from a).1
  ι_inj _ _ h := Subtype.ext h
  fibre x y h := by
    obtain ⟨g, hg⟩ := exists_smul_eq (a := (show S from x).1) (b := (show S from y).1) h
    exact ⟨g, hg.symm⟩
  arrows α β h := by
    obtain ⟨a, b, f, hf⟩ := α
    obtain ⟨a', b', f', hf'⟩ := β
    rcases f with _ | f
    · exact absurd rfl hf.1
    rcases f' with _ | f'
    · exact absurd rfl hf'.1
    have hm := congrArg labelMor h
    obtain ⟨hay, h1⟩ := Sigma.mk.inj hm
    obtain ⟨g, hg⟩ := exists_smul_eq (a := a.1) (b := a'.1) hay
    refine ⟨g, hg.symm, ?_⟩
    change b'.1 = g • b.1
    obtain ⟨hby, hv⟩ := sigma_heq hay _ _ h1
    exact (target_eq' (deckNZ g f) f' hg hby hv).symm
omit [IsRayCategory P] [Fintype P] [DecidableEq P] in
/-- A free group is torsion-free in the form used by covering data. -/
lemma torsionFree_of_isFreeGroup {G : Type} [Group G] [IsFreeGroup G] (g : G) (hg : g ≠ 1)
    (n : ℕ) (hn : 0 < n) : g ^ n ≠ 1 := by
  intro h
  let e := IsFreeGroup.toFreeGroup G
  have h1 : (e g) ^ n = (1 : FreeGroup (IsFreeGroup.Generators G)) ^ n := by
    rw [← map_pow, h, map_one, one_pow]
  have := IsMulTorsionFree.pow_left_injective (Nat.pos_iff_ne_zero.1 hn) h1
  exact hg (e.injective (this.trans (map_one e).symm))

end RayCat

end LargeIndecomposable
