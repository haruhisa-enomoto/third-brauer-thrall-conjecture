module

public import LargeIndecomposable.RayCategories.Distributive.DistributiveHomStructure
public import LargeIndecomposable.RayCategories.Basic.UnitRayOrbit

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.ClosedZigzagTransfer

universe u v w

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- Comparable principal spans in a finite-dimensional Hom space have a
largest member, and that member is the whole Hom space.  This is the
operational maximal Hom generator denoted `pi(x,y)` in BGRS 1.3/3.7. -/
theorem exists_full_twoSidedEndomorphismSpan
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [HasBGRSDistributiveHomStructure k C]
    (X Y : C) [Module.Finite k (X ⟶ Y)] :
    ∃ f : X ⟶ Y, twoSidedEndomorphismSpan k f = ⊤ := by
  letI : Finite (UnitRayOrbit X Y) :=
    finite_unitRayOrbit_of_classifyingComparableSpans k X Y
  letI : Fintype (UnitRayOrbit X Y) := Fintype.ofFinite _
  obtain ⟨r, _, hr⟩ := Finset.exists_max_image
    (Finset.univ : Finset (UnitRayOrbit X Y))
    (fun s ↦ Module.finrank k (s.twoSidedEndomorphismSpan k))
    (by exact ⟨0, Finset.mem_univ _⟩)
  refine ⟨r.out, ?_⟩
  have hrspan : twoSidedEndomorphismSpan k r.out =
      r.twoSidedEndomorphismSpan k := by
    rw [← UnitRayOrbit.twoSidedEndomorphismSpan_unitRay]
    rw [unitRay_out]
  rw [hrspan]
  apply top_unique
  intro g _
  rcases HasClassifyingComparableUnitRaySpans.span_comparable
      (k := k) (C := C) (unitRay g) r with hgr | hrg
  · exact hgr (mem_twoSidedEndomorphismSpan k g)
  · have hdim : Module.finrank k
        ((unitRay g).twoSidedEndomorphismSpan k) ≤
        Module.finrank k (r.twoSidedEndomorphismSpan k) := by
      exact hr (unitRay g) (Finset.mem_univ _)
    have heq : r.twoSidedEndomorphismSpan k =
        (unitRay g).twoSidedEndomorphismSpan k := by
      apply Submodule.eq_of_le_of_finrank_eq hrg
      exact le_antisymm
        (by
          exact LinearMap.finrank_le_finrank_of_injective
            (Submodule.inclusion_injective hrg))
        hdim
    rw [heq]
    exact mem_twoSidedEndomorphismSpan k g

/-- The Jacobson radical of one endomorphism ring, viewed as a `k`-linear
subspace of the corresponding endomorphism Hom. -/
def endRadicalSubmodule (X : C) : Submodule k (End X) :=
  (Ring.jacobson (End X)).restrictScalars k

private theorem endRadicalSubmodule_isHomSubbimodule (X : C) :
    IsHomSubbimodule (endRadicalSubmodule (k := k) X) := by
  constructor
  · intro a f hf
    change (show End X from f) * a ∈ Ring.jacobson (End X)
    exact (Ring.jacobson (End X)).mul_mem_right a hf
  · intro b f hf
    change b * (show End X from f) ∈ Ring.jacobson (End X)
    exact (Ring.jacobson (End X)).mul_mem_left b hf

private theorem endRadical_mem_of_unitRayEquivalent
    (k : Type w) [Field k] [Linear k C]
    {X : C} {f g : End X} (hf : f ∈ Ring.jacobson (End X))
    (hfg : UnitRayEquivalent f g) : g ∈ Ring.jacobson (End X) := by
  rcases hfg with ⟨a, b, rfl⟩
  have hmul : (show End X from b.hom) *
      ((show End X from f) * (show End X from a.hom)) ∈
        Ring.jacobson (End X) :=
    (Ring.jacobson (End X)).mul_mem_left (show End X from b.hom)
      ((Ring.jacobson (End X)).mul_mem_right
        (show End X from a.hom) hf)
  simpa only [End.mul_def, Category.assoc] using hmul

/-- In a finite-dimensional distributive Hom category, every nonzero
endomorphism radical has a single morphism whose principal two-sided span is
the whole radical.  This is the first operational part of the BGRS local
parameter `pi(X,X)`. -/
theorem exists_radical_twoSidedEndomorphismSpan_eq
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [HasBGRSDistributiveHomStructure k C]
    (X : C) [Module.Finite k (X ⟶ X)]
    (f0 : End X) (hf0J : f0 ∈ Ring.jacobson (End X)) (hf0 : f0 ≠ 0) :
    ∃ tau : End X, tau ∈ Ring.jacobson (End X) ∧ tau ≠ 0 ∧
      twoSidedEndomorphismSpan k tau = endRadicalSubmodule (k := k) X := by
  classical
  letI : Finite (UnitRayOrbit X X) :=
    finite_unitRayOrbit_of_classifyingComparableSpans k X X
  letI : Fintype (UnitRayOrbit X X) := Fintype.ofFinite _
  let rays : Finset (UnitRayOrbit X X) :=
    Finset.univ.filter (fun r ↦ r.out ∈ Ring.jacobson (End X))
  have hout_mem (f : End X) (hfJ : f ∈ Ring.jacobson (End X)) :
      (unitRay f).out ∈ Ring.jacobson (End X) := by
    apply endRadical_mem_of_unitRayEquivalent k hfJ
    apply (unitRay_eq_iff f (unitRay f).out).1
    exact (unitRay_out (unitRay f)).symm
  have hrays : rays.Nonempty := by
    refine ⟨unitRay f0, ?_⟩
    simpa [rays] using hout_mem f0 hf0J
  obtain ⟨r, hr, hrmax⟩ := Finset.exists_max_image rays
    (fun s ↦ Module.finrank k (s.twoSidedEndomorphismSpan k)) hrays
  have hrJ : r.out ∈ Ring.jacobson (End X) := by
    simpa [rays] using hr
  have hr0 : r.out ≠ 0 := by
    intro hrzero
    have hzeroSpan : r.twoSidedEndomorphismSpan k = ⊥ := by
      apply (UnitRayOrbit.twoSidedEndomorphismSpan_eq_bot_iff (k := k) r).2
      rw [← unitRay_out r, hrzero]
      rfl
    have hf0ray : unitRay f0 ∈ rays := by
      simpa [rays] using hout_mem f0 hf0J
    have hdim := hrmax (unitRay f0) hf0ray
    rw [hzeroSpan, finrank_bot] at hdim
    have hfspan : twoSidedEndomorphismSpan k f0 = ⊥ :=
      Submodule.finrank_eq_zero.1 (Nat.eq_zero_of_le_zero hdim)
    exact hf0 ((twoSidedEndomorphismSpan_eq_bot_iff k f0).1 hfspan)
  have hrspan : twoSidedEndomorphismSpan k r.out =
      r.twoSidedEndomorphismSpan k := by
    rw [← UnitRayOrbit.twoSidedEndomorphismSpan_unitRay (k := k) r.out,
      unitRay_out]
  have hradspan : r.twoSidedEndomorphismSpan k =
      endRadicalSubmodule (k := k) X := by
    apply le_antisymm
    · rw [← hrspan]
      apply Submodule.span_le.2
      rintro g ⟨a, b, rfl⟩
      exact (endRadicalSubmodule_isHomSubbimodule (k := k) X).2 b
        ((endRadicalSubmodule_isHomSubbimodule (k := k) X).1 a hrJ)
    · intro g hg
      have hgJ : g ∈ Ring.jacobson (End X) := hg
      have hgray : unitRay g ∈ rays := by
        simpa [rays] using hout_mem g hgJ
      rcases HasClassifyingComparableUnitRaySpans.span_comparable
          (k := k) (C := C) (unitRay g) r with hgr | hrg
      · exact hgr (mem_twoSidedEndomorphismSpan k g)
      · have hdim : Module.finrank k
            ((unitRay g).twoSidedEndomorphismSpan k) ≤
            Module.finrank k (r.twoSidedEndomorphismSpan k) :=
          hrmax (unitRay g) hgray
        have heq : r.twoSidedEndomorphismSpan k =
            (unitRay g).twoSidedEndomorphismSpan k := by
          apply Submodule.eq_of_le_of_finrank_eq hrg
          exact le_antisymm
            (LinearMap.finrank_le_finrank_of_injective
              (Submodule.inclusion_injective hrg))
            hdim
        rw [heq]
        exact mem_twoSidedEndomorphismSpan k g
  exact ⟨r.out, hrJ, hr0, hrspan.trans hradspan⟩


end LargeIndecomposable.ClosedZigzagTransfer
