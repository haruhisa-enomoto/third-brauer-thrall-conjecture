module

public import LargeIndecomposable.RayCategories.Distributive.SplitBasicRayCategory
public import LargeIndecomposable.RayCategories.Distributive.BGRSRayPathLift
public import LargeIndecomposable.RayCategories.Contours.ContourDiscrepancy

@[expose] public section

/-!
# Endpoint socles and scalar unit rays

For chosen primitive projectives over a split-basic algebra, an endpoint unit
acts on a bimodule-socle morphism through its scalar residue.  Consequently,
two endpoint-unit-equivalent morphisms differ by multiplication by a nonzero
scalar as soon as one of them is annihilated by both endpoint Jacobson
radicals.  This is the linear-algebra bridge used for the deep-contour half of
the BGRS semi-normalization argument.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.SplitBasicIdempotents

universe u v x

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

/-- A morphism between chosen primitive projectives lies in the endpoint
bimodule socle when both endpoint Jacobson radicals annihilate it. -/
def IsEndpointSocleMorphism
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    {i j : S.ProjectiveCategory} (f : i ⟶ j) : Prop :=
  (∀ a : End i, a ∈ Ring.jacobson (End i) → a.asHom ≫ f = 0) ∧
  (∀ b : End j, b ∈ Ring.jacobson (End j) → f ≫ b.asHom = 0)

/-- The endpoint bimodule socle as a linear subspace of a primitive-projective
Hom space. -/
def endpointSocleSubmodule
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    (i j : S.ProjectiveCategory) : Submodule k (i ⟶ j) where
  carrier := {f | S.IsEndpointSocleMorphism f}
  zero_mem' := by
    constructor <;> intro a ha <;> simp
  add_mem' := by
    rintro f g ⟨hfL, hfR⟩ ⟨hgL, hgR⟩
    constructor
    · intro a ha
      rw [Preadditive.comp_add, hfL a ha, hgL a ha, add_zero]
    · intro b hb
      rw [Preadditive.add_comp, hfR b hb, hgR b hb, add_zero]
  smul_mem' := by
    rintro c f ⟨hfL, hfR⟩
    constructor
    · intro a ha
      rw [Linear.comp_smul, hfL a ha, smul_zero]
    · intro b hb
      rw [Linear.smul_comp, hfR b hb, smul_zero]

@[simp]
theorem mem_endpointSocleSubmodule
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    {i j : S.ProjectiveCategory} (f : i ⟶ j) :
    f ∈ S.endpointSocleSubmodule i j ↔ S.IsEndpointSocleMorphism f :=
  Iff.rfl

/-- On the endpoint bimodule socle, a source endomorphism acts through its
split-basic scalar residue. -/
theorem left_comp_eq_projectiveEndResidue_smul_of_isEndpointSocleMorphism
    [Module.Finite k A]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    {i j : S.ProjectiveCategory} {f : i ⟶ j}
    (hf : S.IsEndpointSocleMorphism f) (a : End i) :
    a.asHom ≫ f = S.projectiveEndResidue i a • f := by
  let c : k := S.projectiveEndResidue i a
  let n : End i := a - c • (1 : End i)
  have hnResidue : S.projectiveEndResidue i n = 0 := by
    have hscalar :
        S.projectiveEndResidue i (c • (1 : End i)) = c := by
      exact (S.projectiveEndResidue i).commutes c
    calc
      S.projectiveEndResidue i n =
          S.projectiveEndResidue i a -
            S.projectiveEndResidue i (c • (1 : End i)) := by
        exact map_sub (S.projectiveEndResidue i) _ _
      _ = c - c := by rw [hscalar]
      _ = 0 := sub_self c
  have hn : n ∈ Ring.jacobson (End i) := by
    rw [S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson,
      ← S.projectiveEndResidue_eq_zero_iff_val_mem_jacobson]
    exact hnResidue
  have hzero : n.asHom ≫ f = 0 := hf.1 n hn
  change (a.asHom - c • (𝟙 i)) ≫ f = 0 at hzero
  rw [Preadditive.sub_comp, Linear.smul_comp, Category.id_comp] at hzero
  exact sub_eq_zero.mp hzero

/-- On the endpoint bimodule socle, a target endomorphism acts through its
split-basic scalar residue. -/
theorem comp_right_eq_projectiveEndResidue_smul_of_isEndpointSocleMorphism
    [Module.Finite k A]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    {i j : S.ProjectiveCategory} {f : i ⟶ j}
    (hf : S.IsEndpointSocleMorphism f) (b : End j) :
    f ≫ b.asHom = S.projectiveEndResidue j b • f := by
  let c : k := S.projectiveEndResidue j b
  let n : End j := b - c • (1 : End j)
  have hnResidue : S.projectiveEndResidue j n = 0 := by
    have hscalar :
        S.projectiveEndResidue j (c • (1 : End j)) = c := by
      exact (S.projectiveEndResidue j).commutes c
    calc
      S.projectiveEndResidue j n =
          S.projectiveEndResidue j b -
            S.projectiveEndResidue j (c • (1 : End j)) := by
        exact map_sub (S.projectiveEndResidue j) _ _
      _ = c - c := by rw [hscalar]
      _ = 0 := sub_self c
  have hn : n ∈ Ring.jacobson (End j) := by
    rw [S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson,
      ← S.projectiveEndResidue_eq_zero_iff_val_mem_jacobson]
    exact hnResidue
  have hzero : f ≫ n.asHom = 0 := hf.2 n hn
  change f ≫ (b.asHom - c • (𝟙 j)) = 0 at hzero
  rw [Preadditive.comp_sub, Linear.comp_smul, Category.comp_id] at hzero
  exact sub_eq_zero.mp hzero

/-- Every element of the principal two-sided span of an endpoint-socle
morphism is a ground-field scalar multiple of that morphism. -/
theorem exists_eq_smul_of_mem_twoSidedEndomorphismSpan_of_endpointSocle
    [Module.Finite k A]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    {i j : S.ProjectiveCategory} {f g : i ⟶ j}
    (hf : S.IsEndpointSocleMorphism f)
    (hg : g ∈ LargeIndecomposable.twoSidedEndomorphismSpan k f) :
    ∃ c : k, g = c • f := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨a, b, rfl⟩
      refine ⟨S.projectiveEndResidue i a *
        S.projectiveEndResidue j b, ?_⟩
      rw [S.left_comp_eq_projectiveEndResidue_smul_of_isEndpointSocleMorphism
        hf a, Linear.smul_comp,
        S.comp_right_eq_projectiveEndResidue_smul_of_isEndpointSocleMorphism
          hf b, smul_smul]
  | zero => exact ⟨0, by simp⟩
  | add g h _ _ hg hh =>
      obtain ⟨c, rfl⟩ := hg
      obtain ⟨d, rfl⟩ := hh
      exact ⟨c + d, by rw [add_smul]⟩
  | smul c g _ hg =>
      obtain ⟨d, rfl⟩ := hg
      exact ⟨c * d, by rw [smul_smul]⟩

/-- In a split-basic distributive category, every endpoint bimodule socle has
dimension at most one.  This is the formal form of BGRS 1.3 used after
Roiter's square-annihilation alternative. -/
theorem endpointSocleSubmodule_finrank_le_one
    [Module.Finite k A]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [LargeIndecomposable.HasBGRSDistributiveHomStructure
      k S.ProjectiveCategory]
    (i j : S.ProjectiveCategory) :
    Module.finrank k (S.endpointSocleSubmodule i j) ≤ 1 := by
  classical
  let V := S.endpointSocleSubmodule i j
  by_cases hV : V = ⊥
  · change Module.finrank k V ≤ 1
    rw [hV]
    simp
  obtain ⟨f, hfV, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
  let v : V := ⟨f, hfV⟩
  apply finrank_le_one v
  intro w
  have hwSocle : S.IsEndpointSocleMorphism w.1 := w.2
  have hfSocle : S.IsEndpointSocleMorphism f := hfV
  rcases
      LargeIndecomposable.HasBGRSDistributiveHomStructure.homSubbimodule_comparable
        (k := k) (C := S.ProjectiveCategory)
        (LargeIndecomposable.twoSidedEndomorphismSpan k w.1)
        (LargeIndecomposable.twoSidedEndomorphismSpan k f)
        (LargeIndecomposable.isHomSubbimodule_twoSidedEndomorphismSpan w.1)
        (LargeIndecomposable.isHomSubbimodule_twoSidedEndomorphismSpan f) with
    hwf | hfw
  · obtain ⟨c, hc⟩ :=
      S.exists_eq_smul_of_mem_twoSidedEndomorphismSpan_of_endpointSocle
        hfSocle (hwf (LargeIndecomposable.mem_twoSidedEndomorphismSpan k w.1))
    refine ⟨c, ?_⟩
    apply Subtype.ext
    exact hc.symm
  · obtain ⟨c, hc⟩ :=
      S.exists_eq_smul_of_mem_twoSidedEndomorphismSpan_of_endpointSocle
        hwSocle (hfw (LargeIndecomposable.mem_twoSidedEndomorphismSpan k f))
    have hc0 : c ≠ 0 := by
      intro hzero
      apply hf0
      rw [hc, hzero, zero_smul]
    refine ⟨c⁻¹, ?_⟩
    apply Subtype.ext
    change c⁻¹ • f = w.1
    rw [hc, ← mul_smul]
    simp [hc0]

/-- Vanishing against one generator at each endpoint implies membership in
the endpoint bimodule socle, provided those generators generate the endpoint
Jacobson radicals on the sides adjacent to the morphism. -/
theorem isEndpointSocleMorphism_of_radical_generators
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    {i j : S.ProjectiveCategory} (f : i ⟶ j)
    (tauSource : End i) (tauTarget : End j)
    (hsource : ∀ a : End i, a ∈ Ring.jacobson (End i) →
      ∃ q : End i, a.asHom = q.asHom ≫ tauSource.asHom)
    (htarget : ∀ b : End j, b ∈ Ring.jacobson (End j) →
      ∃ q : End j, b.asHom = tauTarget.asHom ≫ q.asHom)
    (hleft : tauSource.asHom ≫ f = 0)
    (hright : f ≫ tauTarget.asHom = 0) :
    S.IsEndpointSocleMorphism f := by
  constructor
  · intro a ha
    obtain ⟨q, hq⟩ := hsource a ha
    rw [hq, Category.assoc, hleft]
    simp
  · intro b hb
    obtain ⟨q, hq⟩ := htarget b hb
    rw [hq, ← Category.assoc, hright]
    simp

/-- Endpoint units act on an endpoint-socle morphism through their
split-basic scalar residues. -/
theorem unitRayEquivalent_eq_unit_smul_of_isEndpointSocleMorphism
    [Module.Finite k A]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    {i j : S.ProjectiveCategory} {f g : i ⟶ j}
    (hf : S.IsEndpointSocleMorphism f)
    (hfg : LargeIndecomposable.UnitRayEquivalent f g) :
    ∃ c : kˣ, g = (c : k) • f := by
  rcases hfg with ⟨a, b, rfl⟩
  let ca : k := S.projectiveEndResidue i (End.of a.hom)
  let cb : k := S.projectiveEndResidue j (End.of b.hom)
  have hau : IsUnit (End.of a.hom) :=
    (isUnit_iff_isIso (End.of a.hom)).2 inferInstance
  have hbu : IsUnit (End.of b.hom) :=
    (isUnit_iff_isIso (End.of b.hom)).2 inferInstance
  have hca : ca ≠ 0 := by
    have hmap : IsUnit ca :=
      hau.map (S.projectiveEndResidue i).toRingHom
    exact fun hzero ↦ not_isUnit_zero (hzero ▸ hmap)
  have hcb : cb ≠ 0 := by
    have hmap : IsUnit cb :=
      hbu.map (S.projectiveEndResidue j).toRingHom
    exact fun hzero ↦ not_isUnit_zero (hzero ▸ hmap)
  let na : End i := End.of a.hom - ca • (1 : End i)
  let nb : End j := End.of b.hom - cb • (1 : End j)
  have hnaResidue : S.projectiveEndResidue i na = 0 := by
    have hscalar :
        S.projectiveEndResidue i (ca • (1 : End i)) = ca := by
      exact (S.projectiveEndResidue i).commutes ca
    calc
      S.projectiveEndResidue i na =
          S.projectiveEndResidue i (End.of a.hom) -
            S.projectiveEndResidue i (ca • (1 : End i)) := by
        exact map_sub (S.projectiveEndResidue i) _ _
      _ = ca - ca := by rw [hscalar]
      _ = 0 := sub_self ca
  have hnbResidue : S.projectiveEndResidue j nb = 0 := by
    have hscalar :
        S.projectiveEndResidue j (cb • (1 : End j)) = cb := by
      exact (S.projectiveEndResidue j).commutes cb
    calc
      S.projectiveEndResidue j nb =
          S.projectiveEndResidue j (End.of b.hom) -
            S.projectiveEndResidue j (cb • (1 : End j)) := by
        exact map_sub (S.projectiveEndResidue j) _ _
      _ = cb - cb := by rw [hscalar]
      _ = 0 := sub_self cb
  have hna : na ∈ Ring.jacobson (End i) := by
    rw [S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson,
      ← S.projectiveEndResidue_eq_zero_iff_val_mem_jacobson]
    exact hnaResidue
  have hnb : nb ∈ Ring.jacobson (End j) := by
    rw [S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson,
      ← S.projectiveEndResidue_eq_zero_iff_val_mem_jacobson]
    exact hnbResidue
  have hleftZero : na.asHom ≫ f = 0 := hf.1 na hna
  have hrightZero : f ≫ nb.asHom = 0 := hf.2 nb hnb
  have hleft : a.hom ≫ f = ca • f := by
    change (a.hom - ca • (𝟙 i)) ≫ f = 0 at hleftZero
    rw [Preadditive.sub_comp, Linear.smul_comp, Category.id_comp] at hleftZero
    exact sub_eq_zero.mp hleftZero
  have hright : f ≫ b.hom = cb • f := by
    change f ≫ (b.hom - cb • (𝟙 j)) = 0 at hrightZero
    rw [Preadditive.comp_sub, Linear.comp_smul, Category.comp_id] at hrightZero
    exact sub_eq_zero.mp hrightZero
  let c : kˣ := Units.mk0 (ca * cb) (mul_ne_zero hca hcb)
  refine ⟨c, ?_⟩
  rw [← Category.assoc, hleft, Linear.smul_comp, hright, smul_smul]
  rfl

/-- In the orientation used by contour functions, a nonzero
endpoint-socle morphism and an endpoint-unit-equivalent morphism are related
by a nonzero ground-field scalar. -/
theorem unitRayEquivalent_isEndpointSocleMorphism_scalar_relation
    [Module.Finite k A]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    {i j : S.ProjectiveCategory} {f g : i ⟶ j}
    (hf0 : f ≠ 0)
    (hf : S.IsEndpointSocleMorphism f)
    (hfg : LargeIndecomposable.UnitRayEquivalent f g) :
    f ≠ 0 ∧ ∃ c : kˣ, f = (c : k) • g := by
  obtain ⟨c, hc⟩ :=
    S.unitRayEquivalent_eq_unit_smul_of_isEndpointSocleMorphism hf hfg
  refine ⟨hf0, c⁻¹, ?_⟩
  rw [hc, smul_smul]
  simp

section RayPaths

variable [Module.Finite k A]

/-- If one chosen composite of a related nonzero pair of ray paths lies in
the endpoint bimodule socle, then the two chosen composites are nonzero scalar
multiples. -/
theorem BGRSRayArrowLift.rayPathContourRelation_related_implies_scalar_of_endpointSocle
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [LargeIndecomposable.HasWellDefinedBGRSRayProduct S.ProjectiveCategory]
    (L : LargeIndecomposable.BGRSRayArrowLift
      (C := S.ProjectiveCategory))
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p q : Quiver.Path i j}
    (hpq : (LargeIndecomposable.rayPathContourRelation
      (C := S.RayCategory)).related p q)
    (hsocle : S.IsEndpointSocleMorphism (L.pathMap p)) :
    (LargeIndecomposable.LinearPathCategory.nonzeroScalarMultiplePathRelation
      (k := k) (fun x : LargeIndecomposable.RayVertex S.RayCategory ↦ x.obj.as)
      (fun {i j} (a : i ⟶ j) ↦ L.representative a)).related p q := by
  have hdata :=
    (L.rayPathContourRelation_related_iff_unitRayEquivalent_pathMap p q).1 hpq
  change L.pathMap p ≠ 0 ∧
    ∃ c : kˣ, L.pathMap p = (c : k) • L.pathMap q
  exact S.unitRayEquivalent_isEndpointSocleMorphism_scalar_relation
    (L.pathMap_ne_zero_of_rayPathMap_ne_zero p hdata.1)
    hsocle hdata.2.2

/-- For a related pair of nonzero ray paths, vanishing against radical
generators at the endpoints is enough to obtain the required nonzero scalar
relation between the chosen composites.  Ray-path orientation reverses the
displayed quiver endpoints, so `j` supplies the source endomorphism ring and
`i` the target endomorphism ring. -/
theorem BGRSRayArrowLift.rayPathContourRelation_related_implies_scalar_of_radical_generators
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [LargeIndecomposable.HasWellDefinedBGRSRayProduct S.ProjectiveCategory]
    (L : LargeIndecomposable.BGRSRayArrowLift
      (C := S.ProjectiveCategory))
    {i j : LargeIndecomposable.RayVertex S.RayCategory}
    {p q : Quiver.Path i j}
    (hpq : (LargeIndecomposable.rayPathContourRelation
      (C := S.RayCategory)).related p q)
    (tauSource : End j.obj.as) (tauTarget : End i.obj.as)
    (hsource : ∀ a : End j.obj.as, a ∈ Ring.jacobson (End j.obj.as) →
      ∃ r : End j.obj.as,
        a.asHom = r.asHom ≫ tauSource.asHom)
    (htarget : ∀ b : End i.obj.as, b ∈ Ring.jacobson (End i.obj.as) →
      ∃ r : End i.obj.as,
        b.asHom = tauTarget.asHom ≫ r.asHom)
    (hleft : tauSource.asHom ≫ L.pathMap p = 0)
    (hright : L.pathMap p ≫ tauTarget.asHom = 0) :
    (LargeIndecomposable.LinearPathCategory.nonzeroScalarMultiplePathRelation
      (k := k) (fun x : LargeIndecomposable.RayVertex S.RayCategory ↦ x.obj.as)
      (fun {i j} (a : i ⟶ j) ↦ L.representative a)).related p q := by
  apply
    LargeIndecomposable.SplitBasicIdempotents.BGRSRayArrowLift.rayPathContourRelation_related_implies_scalar_of_endpointSocle
      S L hpq
  exact S.isEndpointSocleMorphism_of_radical_generators
    (L.pathMap p) tauSource tauTarget hsource htarget hleft hright

end RayPaths

end LargeIndecomposable.SplitBasicIdempotents
