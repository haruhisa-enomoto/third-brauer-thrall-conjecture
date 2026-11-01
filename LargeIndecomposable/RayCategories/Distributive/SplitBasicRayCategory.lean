module

public import LargeIndecomposable.RayCategories.Distributive.BGRSRayCategory
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.BGRSPairDichotomyReduction
public import LargeIndecomposable.RayCategories.Distributive.BGRSRayFinite
public import LargeIndecomposable.RayCategories.Distributive.DistributiveHomStructure
public import LargeIndecomposable.Modules.Idempotents.IdempotentProjectiveCategory
public import LargeIndecomposable.Foundations.Ring.LocalRingJacobson
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Nilpotent.Basic

@[expose] public section

/-!
# The ray-category front end of a split-basic algebra

Attach the BGRS unit-ray construction to the concrete category of chosen
primitive projectives.  For a finite-dimensional split-basic algebra, the
single distributive-Hom package supplies the special product laws, finite ray
Hom sets, span factorization, cancellation, and hence every finite-ray-category
axiom.  Deriving that package from representation-finiteness remains the
concrete algebraic bridge.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable.SplitBasicIdempotents

universe u v x

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

/-- The BGRS ray-category object wrapper attached to the chosen primitive
projectives of a split-basic algebra. -/
abbrev RayCategory
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι)) :=
  LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory

/-- An off-diagonal primitive-projective morphism lies in the ambient
Jacobson radical. -/
theorem ProjectiveCategory.offDiagonal_val_mem_jacobson
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    {i j : S.ProjectiveCategory} (hij : i ≠ j) (f : i ⟶ j) :
    f.1 ∈ Ring.jacobson A := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply S.quotientEquiv.injective
  ext l
  simp only [map_zero, Pi.zero_apply]
  obtain ⟨a, ha⟩ := f.2
  change S.idempotent (S.projectiveVertex j) * a *
    S.idempotent (S.projectiveVertex i) = f.1 at ha
  rw [← ha]
  simp only [map_mul, Pi.mul_apply]
  rw [S.quotientEquiv_mk_idempotent,
    S.quotientEquiv_mk_idempotent]
  by_cases hjl : S.projectiveVertex j = l
  · subst l
    have hil : S.projectiveVertex i ≠ S.projectiveVertex j := by
      intro h
      exact hij (S.projectiveVertex_injective h)
    simp [hil]
  · simp [hjl]

/-- The chosen primitive-projective category is skeletal. -/
theorem ProjectiveCategory.skeletal
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι)) :
    Skeletal S.ProjectiveCategory := by
  intro i j h
  rcases h with ⟨e⟩
  by_contra hij
  have hfJ : e.hom.1 ∈ Ring.jacobson A :=
    ProjectiveCategory.offDiagonal_val_mem_jacobson S hij e.hom
  have hcompJ : (e.hom ≫ e.inv).1 ∈ Ring.jacobson A := by
    change e.inv.1 * e.hom.1 ∈ Ring.jacobson A
    exact (Ring.jacobson A).mul_mem_left e.inv.1 hfJ
  have hidJ : (𝟙 i : End i).1 ∈ Ring.jacobson A := by
    have hidVal := congrArg (fun f : End i => f.1) e.hom_inv_id.symm
    rw [hidVal]
    exact hcompJ
  have hquotzero : Ideal.Quotient.mk (Ring.jacobson A)
      ((𝟙 i : End i).1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hidJ
  have hcoord := congrArg
    (fun q ↦ S.quotientEquiv q (S.projectiveVertex i)) hquotzero
  rw [ProjectiveCategory.id_val,
    S.quotientEquiv_mk_idempotent] at hcoord
  simp at hcoord

/-- The residue of a diagonal primitive-projective endomorphism at its
distinguished split-basic coordinate. -/
def projectiveEndResidue
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    (i : S.ProjectiveCategory) : End i →ₐ[k] k where
  toFun f := S.quotientEquiv
    (Ideal.Quotient.mk (Ring.jacobson A) f.1)
      (S.projectiveVertex i)
  map_one' := by
    change S.quotientEquiv
      (Ideal.Quotient.mk (Ring.jacobson A)
        (S.idempotent (S.projectiveVertex i)))
      (S.projectiveVertex i) = 1
    simpa using S.quotientEquiv_mk_idempotent
      (S.projectiveVertex i) (S.projectiveVertex i)
  map_mul' f g := by
    change S.quotientEquiv
      (Ideal.Quotient.mk (Ring.jacobson A) (f.1 * g.1))
      (S.projectiveVertex i) =
      S.quotientEquiv
          (Ideal.Quotient.mk (Ring.jacobson A) f.1)
          (S.projectiveVertex i) *
        S.quotientEquiv
          (Ideal.Quotient.mk (Ring.jacobson A) g.1)
          (S.projectiveVertex i)
    simp
  map_zero' := by
    change S.quotientEquiv
      (Ideal.Quotient.mk (Ring.jacobson A) (0 : A))
      (S.projectiveVertex i) = 0
    simp
  map_add' f g := by
    change S.quotientEquiv
      (Ideal.Quotient.mk (Ring.jacobson A) (f.1 + g.1))
      (S.projectiveVertex i) =
      S.quotientEquiv
          (Ideal.Quotient.mk (Ring.jacobson A) f.1)
          (S.projectiveVertex i) +
        S.quotientEquiv
          (Ideal.Quotient.mk (Ring.jacobson A) g.1)
          (S.projectiveVertex i)
    simp
  commutes' c := by
    change S.quotientEquiv
      ((Ideal.Quotient.mkₐ k (Ring.jacobson A))
        (c • S.idempotent (S.projectiveVertex i)))
      (S.projectiveVertex i) = c
    rw [map_smul, map_smul]
    simp [S.quotientEquiv_mk_idempotent]

/-- The primitive-projective residue vanishes exactly on elements whose
ambient algebra value belongs to the Jacobson radical. -/
theorem projectiveEndResidue_eq_zero_iff_val_mem_jacobson
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    (i : S.ProjectiveCategory) (f : End i) :
    S.projectiveEndResidue i f = 0 ↔
      f.1 ∈ Ring.jacobson A := by
  constructor
  · intro hf
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply S.quotientEquiv.injective
    ext j
    simp only [map_zero, Pi.zero_apply]
    by_cases hij : S.projectiveVertex i = j
    · subst j
      exact hf
    · obtain ⟨a, ha⟩ := f.2
      change S.idempotent (S.projectiveVertex i) * a *
        S.idempotent (S.projectiveVertex i) = f.1 at ha
      rw [← ha]
      simp only [map_mul, Pi.mul_apply]
      rw [S.quotientEquiv_mk_idempotent]
      simp [hij]
  · intro hf
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hf
    change S.quotientEquiv
      (Ideal.Quotient.mk (Ring.jacobson A) f.1)
        (S.projectiveVertex i) = 0
    rw [hf]
    simp

/-- A primitive-projective endomorphism with zero residue is nilpotent. -/
theorem projectiveEnd_isNilpotent_of_residue_eq_zero
    [Module.Finite k A]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    (i : S.ProjectiveCategory) (f : End i)
    (hf : S.projectiveEndResidue i f = 0) : IsNilpotent f := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  have hfJ : f.1 ∈ Ring.jacobson A :=
    (S.projectiveEndResidue_eq_zero_iff_val_mem_jacobson i f).1 hf
  obtain ⟨m, hm⟩ :=
    IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [Ideal.jacobson_bot] at hm
  refine ⟨Nat.succ m, ?_⟩
  apply Subtype.ext
  have hpow (n : ℕ) :
      ((f ^ Nat.succ n : End i) : i ⟶ i).1 =
        f.1 ^ Nat.succ n := by
    induction n with
    | zero => simp only [pow_one]
    | succ n ih =>
        calc
          ((f ^ Nat.succ (Nat.succ n) : End i) : i ⟶ i).1 =
              (((f ^ Nat.succ n : End i) * f : End i) : i ⟶ i).1 := by
            rw [show Nat.succ (Nat.succ n) =
                Nat.succ n + 1 by omega,
              pow_succ]
          _ = (f ^ Nat.succ n : End i).1 * f.1 := rfl
          _ = f.1 ^ Nat.succ n * f.1 := by rw [ih]
          _ = f.1 ^ Nat.succ (Nat.succ n) :=
            (pow_succ f.1 (Nat.succ n)).symm
  rw [hpow]
  change f.1 ^ Nat.succ m = (0 : A)
  have hmem : f.1 ^ Nat.succ m ∈
      (Ring.jacobson A) ^ Nat.succ m :=
    Ideal.pow_mem_pow hfJ (Nat.succ m)
  rw [show Nat.succ m = m + 1 by omega,
    Ideal.IsTwoSided.pow_succ, hm, mul_zero] at hmem
  simpa using hmem

/-- Every primitive-projective endomorphism ring is nontrivial. -/
noncomputable instance ProjectiveCategory.categoryEndNontrivial
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    (i : S.ProjectiveCategory) : Nontrivial (End i) :=
  ⟨⟨1, 0, ProjectiveCategory.id_ne_zero S i⟩⟩

/-- A primitive-projective endomorphism is a unit exactly when its scalar
residue is nonzero. -/
theorem projectiveEnd_isUnit_iff_residue_ne_zero
    [Module.Finite k A]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    (i : S.ProjectiveCategory) (f : End i) :
    IsUnit f ↔ S.projectiveEndResidue i f ≠ 0 := by
  constructor
  · intro hf hzero
    have hmap : IsUnit (S.projectiveEndResidue i f) :=
      hf.map (S.projectiveEndResidue i).toRingHom
    rw [hzero] at hmap
    exact not_isUnit_zero hmap
  · intro hf
    let c : k := S.projectiveEndResidue i f
    let u : End i := c • (1 : End i)
    let n : End i := f - u
    have huimage : S.projectiveEndResidue i u = c := by
      dsimp [u]
      exact (S.projectiveEndResidue i).commutes c
    have hnres : S.projectiveEndResidue i n = 0 := by
      rw [show n = f - u by rfl, map_sub, huimage]
      exact sub_self c
    have hn : IsNilpotent n :=
      S.projectiveEnd_isNilpotent_of_residue_eq_zero i n hnres
    have hc : c ≠ 0 := hf
    have hu : IsUnit u := by
      dsimp [u]
      simpa [Algebra.smul_def] using
        (isUnit_iff_ne_zero.mpr hc).map (algebraMap k (End i))
    have hu_eq : u = algebraMap k (End i) c := by
      change c • (1 : End i) = algebraMap k (End i) c
      rw [Algebra.smul_def, mul_one]
    have hcomm : Commute n u := by
      rw [hu_eq]
      exact (Algebra.commutes c n).symm
    have hsum : u + n = f := by
      dsimp [n]
      abel
    rw [← hsum]
    exact hn.isUnit_add_left_of_commute hu hcomm

/-- Every diagonal primitive-projective endomorphism ring is local. -/
noncomputable instance ProjectiveCategory.categoryEndIsLocal
    [Module.Finite k A]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    (i : S.ProjectiveCategory) : IsLocalRing (End i) := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro f
  by_cases hf : S.projectiveEndResidue i f = 0
  · right
    rw [S.projectiveEnd_isUnit_iff_residue_ne_zero]
    have hres : S.projectiveEndResidue i (1 - f) = 1 := by
      calc
        S.projectiveEndResidue i (1 - f) =
            S.projectiveEndResidue i (1 : End i) -
              S.projectiveEndResidue i f :=
          map_sub (S.projectiveEndResidue i) (1 : End i) f
        _ = 1 - 0 := by rw [map_one, hf]
        _ = 1 := sub_zero 1
    rw [hres]
    exact one_ne_zero
  · left
    exact (S.projectiveEnd_isUnit_iff_residue_ne_zero i f).2 hf

/-- Every diagonal primitive-projective endomorphism ring is Artinian. -/
noncomputable instance ProjectiveCategory.categoryEndIsArtinian
    [Module.Finite k A]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    (i : S.ProjectiveCategory) : IsArtinianRing (End i) := by
  letI : Module.Finite k (End i) := by
    change Module.Finite k (i ⟶ i)
    infer_instance
  exact IsArtinianRing.of_finite k (End i)

/-- The Jacobson radical of a primitive-projective endomorphism ring is the
intersection of its corner with the ambient Jacobson radical. -/
theorem projectiveEnd_mem_jacobson_iff_val_mem_jacobson
    [Module.Finite k A]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    (i : S.ProjectiveCategory) (f : End i) :
    f ∈ Ring.jacobson (End i) ↔ f.1 ∈ Ring.jacobson A := by
  rw [LargeIndecomposable.mem_ringJacobson_iff_not_isUnit]
  rw [← S.projectiveEndResidue_eq_zero_iff_val_mem_jacobson i f]
  simpa using not_congr
    (S.projectiveEnd_isUnit_iff_residue_ne_zero i f)

/-- A nonexceptional primitive-projective composite remains nonzero after
inserting an invertible endomorphism at its intermediate object. -/
theorem projective_middleUnitComposite_ne_zero_of_not_bgrsSpecial
    [Module.Finite k A]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (m : End Y) (hm : IsUnit m)
    (hns : ¬LargeIndecomposable.IsBGRSSpecialZero f g) :
    (f ≫ m.asHom) ≫ g ≠ 0 := by
  apply LargeIndecomposable.middleUnitComposite_ne_zero_of_not_bgrsSpecial
    f g (S.projectiveEndResidue Y) (fun q ↦ ?_) m hm hns
  rw [S.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
    S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]

/-- Distributivity supplies the remaining middle-unit common-ray law for the
chosen primitive-projective category. -/
noncomputable instance ProjectiveCategory.hasBGRSMiddleUnitCommonRay
    [Module.Finite k A]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [LargeIndecomposable.HasBGRSDistributiveHomStructure
      k S.ProjectiveCategory] :
    LargeIndecomposable.HasBGRSMiddleUnitCommonRay
      S.ProjectiveCategory where
  common_ray_of_not_special f g m hns hm :=
    LargeIndecomposable.unitRayEquivalent_middleUnit_of_bgrsDistributiveHomStructure
      (k := k) (C := S.ProjectiveCategory) f g
      (fun u hu ↦
        projective_middleUnitComposite_ne_zero_of_not_bgrsSpecial
          S f g u hu hns)
      m hm

/-- Distributivity supplies representative-level nonzero cancellation for the
chosen primitive-projective category. -/
noncomputable instance ProjectiveCategory.hasBGRSRayRepresentativeCancellation
    [Module.Finite k A]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [LargeIndecomposable.HasBGRSDistributiveHomStructure
      k S.ProjectiveCategory] :
    LargeIndecomposable.HasBGRSRayRepresentativeCancellation
      S.ProjectiveCategory :=
  LargeIndecomposable.hasBGRSRayRepresentativeCancellation_of_bgrsDistributiveHomStructure
    (k := k) (C := S.ProjectiveCategory)

/-- Finite-dimensionality and the source's distributive Hom structure supply
all finite-ray-category axioms for the concrete BGRS ray category. -/
noncomputable instance
    RayCategory.isFiniteRayCategory_of_bgrsDistributiveHomStructure
    [Module.Finite k A]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [LargeIndecomposable.HasBGRSDistributiveHomStructure
      k S.ProjectiveCategory] :
    LargeIndecomposable.IsFiniteRayCategory S.RayCategory := by
  apply LargeIndecomposable.BGRSRayCategory.isFiniteRayCategory (k := k)
  · exact ProjectiveCategory.id_ne_zero S
  · intro X Y
    exact
      LargeIndecomposable.finite_unitRayOrbit_of_classifyingComparableSpans
        k X Y
  · exact ProjectiveCategory.skeletal S

namespace RayCategory

variable
  (S : LargeIndecomposable.SplitBasicIdempotents
    (k := k) (A := A) (ι := ι))

/-- A primitive-projective vertex regarded as an object of the ray category. -/
abbrev obj (i : S.ProjectiveCategory) : S.RayCategory :=
  LargeIndecomposable.BGRSRayCategory.mk i

variable [LargeIndecomposable.HasWellDefinedBGRSRayProduct S.ProjectiveCategory]

/-- The ray represented by a concrete primitive-projective morphism. -/
abbrev ray {i j : S.ProjectiveCategory} (f : i ⟶ j) :
    obj S i ⟶ obj S j :=
  LargeIndecomposable.unitRay f

@[simp]
theorem ray_eq_zero_iff {i j : S.ProjectiveCategory} (f : i ⟶ j) :
    ray S f = 0 ↔ f = 0 :=
  LargeIndecomposable.unitRay_eq_zero_iff f

/-- Identities in the concrete split-basic ray category are nonzero. -/
theorem id_ne_zero (X : S.RayCategory) :
    (𝟙 X : X ⟶ X) ≠ 0 := by
  change LargeIndecomposable.unitRay (𝟙 X.as) ≠
    (0 : LargeIndecomposable.UnitRayOrbit X.as X.as)
  rw [LargeIndecomposable.unitRay_ne_zero_iff]
  exact ProjectiveCategory.id_ne_zero S X.as

/-- Under the source's classification and chain properties for principal
subbimodules, finite-dimensionality of `A` makes every ray Hom set finite. -/
noncomputable instance homFinite [Module.Finite k A]
    [LargeIndecomposable.HasClassifyingComparableUnitRaySpans
      k S.ProjectiveCategory]
    (X Y : S.RayCategory) : Finite (X ⟶ Y) := by
  change Finite (LargeIndecomposable.UnitRayOrbit X.as Y.as)
  exact
    LargeIndecomposable.finite_unitRayOrbit_of_classifyingComparableSpans
      k X.as Y.as

@[simp]
theorem ray_comp {i j l : S.ProjectiveCategory}
    (f : i ⟶ j) (g : j ⟶ l) :
    ray S f ≫ ray S g =
      ray S (LargeIndecomposable.bgrsRayRepresentativeProduct f g) :=
  LargeIndecomposable.BGRSRayCategory.comp_unitRay f g

end RayCategory

end LargeIndecomposable.SplitBasicIdempotents
