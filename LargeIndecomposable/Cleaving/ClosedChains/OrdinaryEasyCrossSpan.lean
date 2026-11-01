module

public import LargeIndecomposable.RayCategories.Distributive.DistributiveHomStructure
public import LargeIndecomposable.RayCategories.RoiterVanishing.RayTackle
public import LargeIndecomposable.RayCategories.RoiterVanishing.RayResidueCategory

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.ClosedZigzagTransfer

universe u v w

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- In a Hom space whose endpoint-stable submodules are comparable, every
element of a generated linear span is either zero or has principal two-sided
span bounded by the span of one of the displayed generators.  This is the
finite-sum collapse needed to pass from an algebra ideal corner back to one
categorical factorization ray. -/
theorem exists_generator_span_ge_of_mem_span
    [HasBGRSDistributiveHomStructure k C]
    {X Y : C} (s : Set (X ⟶ Y)) {f : X ⟶ Y}
    (hf : f ∈ Submodule.span k s) :
    f = 0 ∨ ∃ g ∈ s,
      twoSidedEndomorphismSpan k f ≤
        twoSidedEndomorphismSpan k g := by
  induction hf using Submodule.span_induction with
  | mem f hf => exact Or.inr ⟨f, hf, le_rfl⟩
  | zero => exact Or.inl rfl
  | add f g _ _ hf hg =>
      rcases hf with rfl | ⟨f₀, hf₀, hff₀⟩
      · simpa using hg
      rcases hg with rfl | ⟨g₀, hg₀, hgg₀⟩
      · exact Or.inr ⟨f₀, hf₀, by simpa using hff₀⟩
      rcases HasBGRSDistributiveHomStructure.homSubbimodule_comparable
          (k := k) (C := C)
          (twoSidedEndomorphismSpan k f₀)
          (twoSidedEndomorphismSpan k g₀)
          (isHomSubbimodule_twoSidedEndomorphismSpan f₀)
          (isHomSubbimodule_twoSidedEndomorphismSpan g₀) with hfg | hgf
      · refine Or.inr ⟨g₀, hg₀, ?_⟩
        apply twoSidedEndomorphismSpan_le_of_mem
        exact (twoSidedEndomorphismSpan k g₀).add_mem
          (hfg (hff₀ (mem_twoSidedEndomorphismSpan k f)))
          (hgg₀ (mem_twoSidedEndomorphismSpan k g))
      · refine Or.inr ⟨f₀, hf₀, ?_⟩
        apply twoSidedEndomorphismSpan_le_of_mem
        exact (twoSidedEndomorphismSpan k f₀).add_mem
          (hff₀ (mem_twoSidedEndomorphismSpan k f))
          (hgf (hgg₀ (mem_twoSidedEndomorphismSpan k g)))
  | smul c f _ hf =>
      rcases hf with rfl | ⟨g, hg, hfg⟩
      · exact Or.inl (smul_zero c)
      · refine Or.inr ⟨g, hg, ?_⟩
        apply twoSidedEndomorphismSpan_le_of_mem
        exact (twoSidedEndomorphismSpan k g).smul_mem c
          (hfg (mem_twoSidedEndomorphismSpan k f))

/-- Subtracting a scalar multiple from a strictly lower principal span does
not change the larger generator's principal span. -/
theorem twoSidedEndomorphismSpan_sub_smul_eq_of_lt
    [HasBGRSDistributiveHomStructure k C]
    {X Y : C} (f h : X ⟶ Y) (c : k)
    (hlt : twoSidedEndomorphismSpan k h <
      twoSidedEndomorphismSpan k f) :
    twoSidedEndomorphismSpan k (f - c • h) =
      twoSidedEndomorphismSpan k f := by
  have hhf : h ∈ twoSidedEndomorphismSpan k f :=
    hlt.le (mem_twoSidedEndomorphismSpan k h)
  have hdiffF : f - c • h ∈ twoSidedEndomorphismSpan k f :=
    (twoSidedEndomorphismSpan k f).sub_mem
      (mem_twoSidedEndomorphismSpan k f)
      ((twoSidedEndomorphismSpan k f).smul_mem c hhf)
  have hle := twoSidedEndomorphismSpan_le_of_mem hdiffF
  have hnot : ¬twoSidedEndomorphismSpan k f ≤
      twoSidedEndomorphismSpan k h := not_le_of_gt hlt
  have hhDiff : twoSidedEndomorphismSpan k h ≤
      twoSidedEndomorphismSpan k (f - c • h) := by
    rcases HasBGRSDistributiveHomStructure.homSubbimodule_comparable
        (k := k) (C := C)
        (twoSidedEndomorphismSpan k h)
        (twoSidedEndomorphismSpan k (f - c • h))
        (isHomSubbimodule_twoSidedEndomorphismSpan h)
        (isHomSubbimodule_twoSidedEndomorphismSpan (f - c • h)) with
      hhDiff | hdiffH
    · exact hhDiff
    · exfalso
      apply hnot
      apply twoSidedEndomorphismSpan_le_of_mem
      have hdiffMem : f - c • h ∈ twoSidedEndomorphismSpan k h :=
        hdiffH (mem_twoSidedEndomorphismSpan k (f - c • h))
      have hsmul : c • h ∈ twoSidedEndomorphismSpan k h :=
        (twoSidedEndomorphismSpan k h).smul_mem c
          (mem_twoSidedEndomorphismSpan k h)
      have hadd := (twoSidedEndomorphismSpan k h).add_mem hdiffMem hsmul
      simpa only [sub_add_cancel] using hadd
  apply le_antisymm hle
  apply twoSidedEndomorphismSpan_le_of_mem
  have hdiffMem := mem_twoSidedEndomorphismSpan k (f - c • h)
  have hhMem : h ∈ twoSidedEndomorphismSpan k (f - c • h) :=
    hhDiff (mem_twoSidedEndomorphismSpan k h)
  have hsmul :=
    (twoSidedEndomorphismSpan k (f - c • h)).smul_mem c hhMem
  have hadd :=
    (twoSidedEndomorphismSpan k (f - c • h)).add_mem hdiffMem hsmul
  simpa only [sub_add_cancel] using hadd

/-- Under transit, membership in a principal two-sided span collapses to one
target-endomorphism factor. -/
theorem exists_comp_right_of_mem_twoSidedSpan_of_allowsTransit
    {X Y : C} {f g : X ⟶ Y} (ht : AllowsTransit f)
    (hg : g ∈ twoSidedEndomorphismSpan k f) :
    ∃ b : End Y, g = f ≫ b.asHom := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨a, b, rfl⟩
      obtain ⟨c, hc⟩ := ht a
      refine ⟨b * c, ?_⟩
      change (a.asHom ≫ f) ≫ b.asHom = f ≫ (b * c).asHom
      rw [hc, End.mul_def, Category.assoc]
  | zero =>
      refine ⟨0, ?_⟩
      change (0 : X ⟶ Y) = f ≫ (0 : Y ⟶ Y)
      simp
  | add g h _ _ hg hh =>
      rcases hg with ⟨a, rfl⟩
      rcases hh with ⟨b, rfl⟩
      refine ⟨a + b, ?_⟩
      change (f ≫ a.asHom) + (f ≫ b.asHom) =
        f ≫ (a.asHom + b.asHom)
      rw [Preadditive.comp_add]
  | smul c g _ hg =>
      rcases hg with ⟨a, rfl⟩
      refine ⟨c • a, ?_⟩
      change c • (f ≫ a.asHom) = f ≫ (c • a.asHom)
      rw [Linear.comp_smul]

/-- Under cotransit, membership in a principal two-sided span collapses to
one source-endomorphism factor. -/
theorem exists_comp_left_of_mem_twoSidedSpan_of_allowsCotransit
    {X Y : C} {f g : X ⟶ Y} (ht : AllowsCotransit f)
    (hg : g ∈ twoSidedEndomorphismSpan k f) :
    ∃ a : End X, g = a.asHom ≫ f := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨a, b, rfl⟩
      obtain ⟨c, hc⟩ := ht b
      refine ⟨a.asHom ≫ c.asHom, ?_⟩
      change (a.asHom ≫ f) ≫ b.asHom =
        (a.asHom ≫ c.asHom) ≫ f
      rw [Category.assoc, hc]
      simp only [Category.assoc]
  | zero =>
      refine ⟨0, ?_⟩
      change (0 : X ⟶ Y) = (0 : X ⟶ X) ≫ f
      simp
  | add g h _ _ hg hh =>
      rcases hg with ⟨a, rfl⟩
      rcases hh with ⟨b, rfl⟩
      refine ⟨a + b, ?_⟩
      change (a.asHom ≫ f) + (b.asHom ≫ f) =
        (a.asHom + b.asHom) ≫ f
      rw [Preadditive.add_comp]
  | smul c g _ hg =>
      rcases hg with ⟨a, rfl⟩
      refine ⟨c • a, ?_⟩
      change c • (a.asHom ≫ f) = (c • a.asHom) ≫ f
      rw [Linear.smul_comp]

/-- Principal-span domination is an actual two-sided factorization.  The
outer endpoint endomorphism supplied by transit or cotransit is absorbed into
the corresponding outer factor. -/
theorem factorsThroughMorphism_of_twoSidedEndomorphismSpan_le
    [HasBGRSDistributiveHomStructure k C]
    {A B X Y : C} (r : A ⟶ B) {f g : X ⟶ Y}
    (hg : FactorsThroughMorphism r g)
    (hfg : twoSidedEndomorphismSpan k f ≤
      twoSidedEndomorphismSpan k g) :
    FactorsThroughMorphism r f := by
  rcases hg with ⟨a, b, rfl⟩
  have hfmem := hfg (mem_twoSidedEndomorphismSpan k f)
  rcases HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := C) (a ≫ r ≫ b) with hT | hC
  · obtain ⟨d, hfd⟩ :=
      exists_comp_right_of_mem_twoSidedSpan_of_allowsTransit hT hfmem
    refine ⟨a, b ≫ d.asHom, ?_⟩
    simpa only [Category.assoc] using hfd
  · obtain ⟨c, hfc⟩ :=
      exists_comp_left_of_mem_twoSidedSpan_of_allowsCotransit hC hfmem
    refine ⟨c.asHom ≫ a, b, ?_⟩
    simpa only [Category.assoc] using hfc

/-- In particular, domination by the principal span of `g` says literally
that the tested morphism factors through `g`. -/
theorem factorsThroughMorphism_of_twoSidedEndomorphismSpan_le_self
    [HasBGRSDistributiveHomStructure k C]
    {X Y : C} {f g : X ⟶ Y}
    (hfg : twoSidedEndomorphismSpan k f ≤
      twoSidedEndomorphismSpan k g) :
    FactorsThroughMorphism g f := by
  apply factorsThroughMorphism_of_twoSidedEndomorphismSpan_le
    (k := k) (r := g) (g := g)
  · exact ⟨𝟙 X, 𝟙 Y, by simp⟩
  · exact hfg

/-- Easy common-source BGRS case at the ordinary representative level.  If
the cross composite or its first factor allows transit, source
incomparability forces the cross composite's principal span strictly below
the landing generator's span. -/
theorem sourceCross_span_lt_of_allowsTransit
    [HasBGRSDistributiveHomStructure k C]
    {X Y Z : C} (a : NonzeroHom X Z) (f : NonzeroHom X Y)
    (g : Z ⟶ Y) (hinc : RaySourceIncomparable a f)
    (heasy : AllowsTransit (a.1 ≫ g) ∨ AllowsTransit a.1) :
    twoSidedEndomorphismSpan k (a.1 ≫ g) <
      twoSidedEndomorphismSpan k f.1 := by
  have hnot : ¬twoSidedEndomorphismSpan k f.1 ≤
      twoSidedEndomorphismSpan k (a.1 ≫ g) := by
    intro hle
    have hfmem := hle (mem_twoSidedEndomorphismSpan k f.1)
    rcases heasy with hcrossT | haT
    · obtain ⟨b, hfb⟩ :=
        exists_comp_right_of_mem_twoSidedSpan_of_allowsTransit hcrossT hfmem
      apply hinc.1
      refine ⟨g ≫ b.asHom, ?_⟩
      simpa [Category.assoc] using hfb.symm
    · rcases HasBGRSDistributiveHomStructure.transit_or_cotransit
          (k := k) (C := C) (a.1 ≫ g) with hcrossT | hcrossC
      · obtain ⟨b, hfb⟩ :=
          exists_comp_right_of_mem_twoSidedSpan_of_allowsTransit hcrossT hfmem
        apply hinc.1
        refine ⟨g ≫ b.asHom, ?_⟩
        simpa [Category.assoc] using hfb.symm
      · obtain ⟨c, hfc⟩ :=
          exists_comp_left_of_mem_twoSidedSpan_of_allowsCotransit hcrossC hfmem
        obtain ⟨d, hca⟩ := haT c
        apply hinc.1
        refine ⟨d.asHom ≫ g, ?_⟩
        calc
          a.1 ≫ (d.asHom ≫ g) = (a.1 ≫ d.asHom) ≫ g := by
            rw [Category.assoc]
          _ = (c.asHom ≫ a.1) ≫ g := by rw [← hca]
          _ = c.asHom ≫ (a.1 ≫ g) := by rw [Category.assoc]
          _ = f.1 := hfc.symm
  rcases HasBGRSDistributiveHomStructure.homSubbimodule_comparable
      (k := k) (C := C)
      (twoSidedEndomorphismSpan k (a.1 ≫ g))
      (twoSidedEndomorphismSpan k f.1)
      (isHomSubbimodule_twoSidedEndomorphismSpan (a.1 ≫ g))
      (isHomSubbimodule_twoSidedEndomorphismSpan f.1) with hle | hle
  · apply lt_of_le_of_ne hle
    intro heq
    apply hnot
    simp [heq]
  · exact (hnot hle).elim

/-- Easy common-target BGRS case, dual to
`sourceCross_span_lt_of_allowsTransit`. -/
theorem targetCross_span_lt_of_allowsCotransit
    [HasBGRSDistributiveHomStructure k C]
    {X Y Z : C} (f : NonzeroHom X Z) (q : NonzeroHom Y Z)
    (g : X ⟶ Y) (hinc : RayTargetIncomparable f q)
    (heasy : AllowsCotransit (g ≫ q.1) ∨ AllowsCotransit q.1) :
    twoSidedEndomorphismSpan k (g ≫ q.1) <
      twoSidedEndomorphismSpan k f.1 := by
  have hnot : ¬twoSidedEndomorphismSpan k f.1 ≤
      twoSidedEndomorphismSpan k (g ≫ q.1) := by
    intro hle
    have hfmem := hle (mem_twoSidedEndomorphismSpan k f.1)
    rcases heasy with hcrossC | hqC
    · obtain ⟨a, hfa⟩ :=
        exists_comp_left_of_mem_twoSidedSpan_of_allowsCotransit hcrossC hfmem
      apply hinc.1
      refine ⟨a.asHom ≫ g, ?_⟩
      simpa [Category.assoc] using hfa.symm
    · rcases HasBGRSDistributiveHomStructure.transit_or_cotransit
          (k := k) (C := C) (g ≫ q.1) with hcrossT | hcrossC
      · obtain ⟨b, hfb⟩ :=
          exists_comp_right_of_mem_twoSidedSpan_of_allowsTransit hcrossT hfmem
        obtain ⟨a, hqb⟩ := hqC b
        apply hinc.1
        refine ⟨g ≫ a.asHom, ?_⟩
        calc
          (g ≫ a.asHom) ≫ q.1 = g ≫ (a.asHom ≫ q.1) := by
            rw [Category.assoc]
          _ = g ≫ (q.1 ≫ b.asHom) := by rw [← hqb]
          _ = (g ≫ q.1) ≫ b.asHom := by rw [Category.assoc]
          _ = f.1 := hfb.symm
      · obtain ⟨a, hfa⟩ :=
          exists_comp_left_of_mem_twoSidedSpan_of_allowsCotransit hcrossC hfmem
        apply hinc.1
        refine ⟨a.asHom ≫ g, ?_⟩
        simpa [Category.assoc] using hfa.symm
  rcases HasBGRSDistributiveHomStructure.homSubbimodule_comparable
      (k := k) (C := C)
      (twoSidedEndomorphismSpan k (g ≫ q.1))
      (twoSidedEndomorphismSpan k f.1)
      (isHomSubbimodule_twoSidedEndomorphismSpan (g ≫ q.1))
      (isHomSubbimodule_twoSidedEndomorphismSpan f.1) with hle | hle
  · apply lt_of_le_of_ne hle
    intro heq
    apply hnot
    simp [heq]
  · exact (hnot hle).elim

/-- In the hard crossed orientation, inserting a middle radical factor into
a nonexceptional composite strictly lowers its principal two-sided span.
Indeed, a reverse span inclusion lets transit or cotransit collapse the outer
endpoint factors and produces exactly a BGRS exceptional-zero witness. -/
theorem middleRadical_span_lt_of_not_special
    [HasBGRSDistributiveHomStructure k C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfT : AllowsTransit f) (hgC : AllowsCotransit g)
    (m : End Y) (hm : m ∈ Ring.jacobson (End Y))
    (hns : ¬ IsBGRSSpecialZero f g) :
    twoSidedEndomorphismSpan k ((f ≫ m.asHom) ≫ g) <
      twoSidedEndomorphismSpan k (f ≫ g) := by
  have hnot : ¬twoSidedEndomorphismSpan k (f ≫ g) ≤
      twoSidedEndomorphismSpan k ((f ≫ m.asHom) ≫ g) := by
    intro hle
    have hmem := hle (mem_twoSidedEndomorphismSpan k (f ≫ g))
    rcases HasBGRSDistributiveHomStructure.transit_or_cotransit
        (k := k) (C := C) ((f ≫ m.asHom) ≫ g) with hT | hC
    · obtain ⟨b, hb⟩ :=
        exists_comp_right_of_mem_twoSidedSpan_of_allowsTransit hT hmem
      obtain ⟨c, hc⟩ := hgC b
      let rho : End Y := c * m
      have hrho : rho ∈ Ring.jacobson (End Y) :=
        (Ring.jacobson (End Y)).mul_mem_left c hm
      apply hns
      refine ⟨⟨rho, hrho⟩, ?_⟩
      calc
        f ≫ g = ((f ≫ m.asHom) ≫ g) ≫ b.asHom := hb
        _ = (f ≫ m.asHom) ≫ (g ≫ b.asHom) := by
          rw [Category.assoc]
        _ = (f ≫ m.asHom) ≫ (c.asHom ≫ g) := by rw [hc]
        _ = (f ≫ rho.asHom) ≫ g := by
          dsimp [rho]
          simp only [Category.assoc]
    · obtain ⟨a, ha⟩ :=
        exists_comp_left_of_mem_twoSidedSpan_of_allowsCotransit hC hmem
      obtain ⟨d, hd⟩ := hfT a
      let rho : End Y := m * d
      have hrho : rho ∈ Ring.jacobson (End Y) :=
        (Ring.jacobson (End Y)).mul_mem_right d hm
      apply hns
      refine ⟨⟨rho, hrho⟩, ?_⟩
      calc
        f ≫ g = a.asHom ≫ ((f ≫ m.asHom) ≫ g) := ha
        _ = ((a.asHom ≫ f) ≫ m.asHom) ≫ g := by
          simp only [Category.assoc]
        _ = ((f ≫ d.asHom) ≫ m.asHom) ≫ g := by rw [hd]
        _ = (f ≫ rho.asHom) ≫ g := by
          dsimp [rho]
          simp only [Category.assoc]
  rcases HasBGRSDistributiveHomStructure.homSubbimodule_comparable
      (k := k) (C := C)
      (twoSidedEndomorphismSpan k ((f ≫ m.asHom) ≫ g))
      (twoSidedEndomorphismSpan k (f ≫ g))
      (isHomSubbimodule_twoSidedEndomorphismSpan
        ((f ≫ m.asHom) ≫ g))
      (isHomSubbimodule_twoSidedEndomorphismSpan (f ≫ g)) with hle | hle
  · apply lt_of_le_of_ne hle
    intro heq
    apply hnot
    rw [heq]
  · exact (hnot hle).elim

end LargeIndecomposable.ClosedZigzagTransfer
