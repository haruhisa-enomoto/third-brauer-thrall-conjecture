module

public import LargeIndecomposable.BongartzTheorem.SimplyConnectedCover.HullCocycle
public import LargeIndecomposable.FundamentalGroups.Fischbacher.Lemma42

/-!
# Good universal covers

The universal cover of `P` at `x₀` is *good* when it has no oriented cycles and all its
intervals are finite (`CoverGood`). A good cover gives `HullFinite` (`hullFinite_of_coverGood`).
Without essential contours, paths with the same nonzero value are equal in the free groupoid,
so the length is a positive cocycle and the cover is good (`coverGood_of_noEss`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- The universal cover is cycle-free and interval-finite. -/
def CoverGood (x₀ : P) : Prop :=
  (∀ (c : RayVert (Cover x₀)) (p : Quiver.Path c c), p.length = 0) ∧
    ∀ a b : Cover x₀, (interval a b).Finite

lemma reaches_of_reach {x₀ : P} {a b : Cover x₀} (h : Reach a b) : Reaches a b := by
  induction h with
  | refl a => exact Reaches.refl _
  | @step a b c f hf _ ih =>
    exact Reaches.trans ⟨(Quiver.Path.nil.cons
      (⟨f, hf⟩ : (RayVert.mk a : RayVert (Cover x₀)) ⟶ RayVert.mk b))⟩ ih

variable [Fintype P] [DecidableEq P]

lemma reach_of_path {x₀ : P} {a : RayVert (Cover x₀)} :
    ∀ {b : RayVert (Cover x₀)} (_ : Quiver.Path a b), Reach a.out b.out
  | _, .nil => Reach.refl _
  | _, .cons p e => (reach_of_path p).trans (Reach.step e.1 e.2 (Reach.refl _))


/-- **A good cover is interval-finite in the sense of `HullFinite`.** -/
theorem hullFinite_of_coverGood {x₀ : P} (h : CoverGood x₀) : HullFinite x₀ := by
  intro T
  let H : Set (Cover x₀) := {b | ∃ a ∈ T, ∃ d ∈ T, Reaches a b ∧ Reaches b d}
  have hH : H.Finite := by
    refine (T.finite_toSet.biUnion fun a _ ↦ T.finite_toSet.biUnion fun d _ ↦ h.2 a d).subset
      fun b ⟨a, ha, d, hd, hab, hbd⟩ ↦ ?_
    exact Set.mem_biUnion ha (Set.mem_biUnion hd ⟨hab, hbd⟩)
  refine ⟨hH.toFinset, fun t ht ↦ ?_, fun a b d ha hd hab hbd ↦ ?_⟩
  · exact hH.mem_toFinset.2 ⟨t, ht, t, ht, Reaches.refl t, Reaches.refl t⟩
  · obtain ⟨a', ha', -, -, ha'a, -⟩ := hH.mem_toFinset.1 ha
    obtain ⟨-, -, d', hd', -, hdd'⟩ := hH.mem_toFinset.1 hd
    exact hH.mem_toFinset.2 ⟨a', ha', d', hd', ha'a.trans (reaches_of_reach hab),
      (reaches_of_reach hbd).trans hdd'⟩

lemma coverHt_path (c : ArrowWeight P) (hc : IsCocycle c)
    (hpos : ∀ {x y : RayVert P} (e : x ⟶ y), 1 ≤ c e) {x₀ : P} {a : RayVert (Cover x₀)} :
    ∀ {b : RayVert (Cover x₀)} (p : Quiver.Path a b),
      coverHt c hc a.out + p.length ≤ coverHt c hc b.out
  | _, .nil => by simp
  | _, .cons p e => by
    have := coverHt_path c hc hpos p
    have h2 := coverHt_lt c hc hpos e.2
    rw [Quiver.Path.length_cons]
    push_cast
    omega

/-- **Without essential contours the universal cover is good.** -/
theorem coverGood_of_noEss [LargeIndecomposable.IsFiniteRayCategory0 P]
    (hP : NoEssContour (P := P)) (x₀ : P) : CoverGood x₀ := by
  have hc : IsCocycle (oneWeight (P := P)) := by
    intro x y s t hst h0
    have h1 := congrArg (freeWeight oneWeight).map (pathFG_eq_of_noEss hP _ s t hst h0 le_rfl)
    rw [freeWeight_pathFG, freeWeight_pathFG] at h1
    exact Multiplicative.ofAdd.injective h1
  have hpos : ∀ {x y : RayVert P} (e : x ⟶ y), 1 ≤ oneWeight e := fun _ ↦ le_rfl
  refine ⟨fun c p ↦ ?_, fun a b ↦ ?_⟩
  · have := coverHt_path oneWeight hc hpos p
    omega
  · refine (finite_interval_of_posCocycle oneWeight hc hpos b
      ((coverHt oneWeight hc b - coverHt oneWeight hc a).toNat + 1) a (by omega)).subset
      fun d ⟨⟨p⟩, ⟨q⟩⟩ ↦ ⟨reach_of_path p, reach_of_path q⟩

end LargeIndecomposable.RayCat
