module

public import LargeIndecomposable.Modules.SplitBasic.SplitBasic
public import LargeIndecomposable.Foundations.CategoryTheory.LinearMat
public import Mathlib.Data.Fintype.Shrink

@[expose] public section

/-!
# The category of primitive idempotent projectives

For a chosen complete family `e i` in a split-basic algebra `A`, the
`k`-linear category of primitive left projectives has morphism spaces
`e j * A * e i` from `i` to `j`.  Taking one copy of every object in the
additive envelope recovers `A` as the endomorphism algebra of that generator.

This is the algebraic side of the standard mesh-presentation boundary.  It is
deliberately concrete: it is the full subcategory of the Karoubi envelope of
the one-object category of `A`, written directly in terms of idempotent
corners.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.SplitBasicIdempotents

universe u v x

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

/-- The chosen primitive-projective labels, kept opaque so the category type
retains the chosen split-basic presentation as an inferable parameter. -/
def ProjectiveLabel
    (_S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι)) :=
  ι

instance projectiveLabelFinite
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι)) :
    Finite S.ProjectiveLabel := by
  change Finite ι
  infer_instance

/-- The labels are canonically equivalent to the original idempotent index. -/
def projectiveLabelEquiv
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι)) :
    S.ProjectiveLabel ≃ ι :=
  Equiv.refl ι

/-- A universe-small index for the chosen primitive projectives. -/
abbrev ProjectiveIndex
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι)) :=
  Shrink.{0} S.ProjectiveLabel

noncomputable instance projectiveIndexFintype
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι)) :
    Fintype S.ProjectiveIndex :=
  Fintype.ofFinite S.ProjectiveIndex

noncomputable instance projectiveIndexDecidableEq
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι)) :
    DecidableEq S.ProjectiveIndex :=
  Classical.decEq S.ProjectiveIndex

/-- The small projective index is canonically equivalent to the original
idempotent index. -/
def projectiveVertexEquiv
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι)) :
    S.ProjectiveIndex ≃ ι :=
  (equivShrink.{0} S.ProjectiveLabel).symm.trans S.projectiveLabelEquiv

/-- The original idempotent index represented by a small projective index. -/
abbrev projectiveVertex
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    (i : S.ProjectiveIndex) : ι :=
  S.projectiveVertexEquiv i

theorem projectiveVertex_injective
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι)) :
    Function.Injective S.projectiveVertex :=
  S.projectiveVertexEquiv.injective

/-- The concrete `k`-linear category of chosen primitive left projectives.
Morphisms `i ⟶ j` are elements of `e_j A e_i`. -/
abbrev ProjectiveCategory
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι)) :=
  S.ProjectiveIndex

namespace ProjectiveCategory

instance category
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι)) :
    Category S.ProjectiveCategory where
  Hom i j := idempotentCorner (k := k) S.idempotent
    (S.projectiveVertex j) (S.projectiveVertex i)
  id i := by
    refine ⟨S.idempotent (S.projectiveVertex i), ?_⟩
    refine ⟨1, ?_⟩
    change S.idempotent (S.projectiveVertex i) * 1 *
      S.idempotent (S.projectiveVertex i) =
        S.idempotent (S.projectiveVertex i)
    simpa using S.complete.toOrthogonalIdempotents.idem
      (S.projectiveVertex i) |>.eq
  comp {i j l} f g := by
    refine ⟨g.1 * f.1, ?_⟩
    obtain ⟨a, ha⟩ := f.2
    obtain ⟨b, hb⟩ := g.2
    change S.idempotent (S.projectiveVertex j) * a *
      S.idempotent (S.projectiveVertex i) = f.1 at ha
    change S.idempotent (S.projectiveVertex l) * b *
      S.idempotent (S.projectiveVertex j) = g.1 at hb
    refine ⟨b * S.idempotent (S.projectiveVertex j) * a, ?_⟩
    change S.idempotent (S.projectiveVertex l) *
        (b * S.idempotent (S.projectiveVertex j) * a) *
          S.idempotent (S.projectiveVertex i) = g.1 * f.1
    rw [← ha, ← hb]
    have hj := S.complete.toOrthogonalIdempotents.idem
      (S.projectiveVertex j) |>.eq
    simp only [← mul_assoc]
    rw [mul_assoc
      (S.idempotent (S.projectiveVertex l) * b)
      (S.idempotent (S.projectiveVertex j))
      (S.idempotent (S.projectiveVertex j)), hj]
  comp_id {i j} f := by
    apply Subtype.ext
    obtain ⟨a, ha⟩ := f.2
    change S.idempotent (S.projectiveVertex j) * a *
      S.idempotent (S.projectiveVertex i) = f.1 at ha
    change S.idempotent (S.projectiveVertex j) * f.1 = f.1
    rw [← ha]
    rw [mul_assoc (S.idempotent (S.projectiveVertex j)) a
        (S.idempotent (S.projectiveVertex i)),
      ← mul_assoc (S.idempotent (S.projectiveVertex j))
        (S.idempotent (S.projectiveVertex j))
        (a * S.idempotent (S.projectiveVertex i)),
      S.complete.toOrthogonalIdempotents.idem (S.projectiveVertex j) |>.eq]
  id_comp {i j} f := by
    apply Subtype.ext
    obtain ⟨a, ha⟩ := f.2
    change S.idempotent (S.projectiveVertex j) * a *
      S.idempotent (S.projectiveVertex i) = f.1 at ha
    change f.1 * S.idempotent (S.projectiveVertex i) = f.1
    rw [← ha]
    rw [mul_assoc,
      S.complete.toOrthogonalIdempotents.idem (S.projectiveVertex i) |>.eq]
  assoc f g h := by
    apply Subtype.ext
    exact (mul_assoc h.1 g.1 f.1).symm

@[simp]
theorem id_val
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    (i : S.ProjectiveCategory) :
    (𝟙 i : i ⟶ i).1 = S.idempotent (S.projectiveVertex i) :=
  rfl

@[simp]
theorem comp_val
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    {i j l : S.ProjectiveCategory} (f : i ⟶ j) (g : j ⟶ l) :
    (f ≫ g : i ⟶ l).1 = g.1 * f.1 :=
  rfl

theorem idempotent_mul_val
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    {i j : S.ProjectiveCategory} (f : i ⟶ j) :
    S.idempotent (S.projectiveVertex j) * f.1 = f.1 := by
  obtain ⟨a, ha⟩ := f.2
  change S.idempotent (S.projectiveVertex j) * a *
    S.idempotent (S.projectiveVertex i) = f.1 at ha
  rw [← ha, mul_assoc (S.idempotent (S.projectiveVertex j)) a
      (S.idempotent (S.projectiveVertex i)),
    ← mul_assoc (S.idempotent (S.projectiveVertex j))
      (S.idempotent (S.projectiveVertex j))
      (a * S.idempotent (S.projectiveVertex i)),
    S.complete.toOrthogonalIdempotents.idem (S.projectiveVertex j) |>.eq]

theorem val_mul_idempotent
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    {i j : S.ProjectiveCategory} (f : i ⟶ j) :
    f.1 * S.idempotent (S.projectiveVertex i) = f.1 := by
  obtain ⟨a, ha⟩ := f.2
  change S.idempotent (S.projectiveVertex j) * a *
    S.idempotent (S.projectiveVertex i) = f.1 at ha
  rw [← ha, mul_assoc,
    S.complete.toOrthogonalIdempotents.idem (S.projectiveVertex i) |>.eq]

theorem idempotent_mul_val_eq_zero_of_ne
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    {i j l : S.ProjectiveCategory} (h : l ≠ j) (f : i ⟶ j) :
    S.idempotent (S.projectiveVertex l) * f.1 = 0 := by
  obtain ⟨a, ha⟩ := f.2
  change S.idempotent (S.projectiveVertex j) * a *
    S.idempotent (S.projectiveVertex i) = f.1 at ha
  rw [← ha, mul_assoc (S.idempotent (S.projectiveVertex j)) a
      (S.idempotent (S.projectiveVertex i)),
    ← mul_assoc (S.idempotent (S.projectiveVertex l))
      (S.idempotent (S.projectiveVertex j))
      (a * S.idempotent (S.projectiveVertex i)),
    S.complete.toOrthogonalIdempotents.ortho
      (fun hlj ↦ h (S.projectiveVertex_injective hlj)),
    zero_mul]

theorem val_mul_idempotent_eq_zero_of_ne
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    {i j l : S.ProjectiveCategory} (h : i ≠ l) (f : i ⟶ j) :
    f.1 * S.idempotent (S.projectiveVertex l) = 0 := by
  obtain ⟨a, ha⟩ := f.2
  change S.idempotent (S.projectiveVertex j) * a *
    S.idempotent (S.projectiveVertex i) = f.1 at ha
  rw [← ha, mul_assoc,
    S.complete.toOrthogonalIdempotents.ortho
      (fun hil ↦ h (S.projectiveVertex_injective hil)), mul_zero]

instance preadditive
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι)) :
    Preadditive S.ProjectiveCategory where
  homGroup i j := by
    change AddCommGroup (idempotentCorner (k := k) S.idempotent
      (S.projectiveVertex j) (S.projectiveVertex i))
    infer_instance
  add_comp _ _ _ f f' g := by
    apply Subtype.ext
    exact mul_add g.1 f.1 f'.1
  comp_add _ _ _ f g g' := by
    apply Subtype.ext
    exact add_mul g.1 g'.1 f.1

/-- Scalar multiplication on corners makes the primitive-projective category
`k`-linear. -/
instance linear
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι)) :
    Linear k S.ProjectiveCategory where
  homModule i j := by
    change Module k (idempotentCorner (k := k) S.idempotent
      (S.projectiveVertex j) (S.projectiveVertex i))
    infer_instance
  smul_comp _ _ _ r f g := by
    apply Subtype.ext
    exact Algebra.mul_smul_comm r g.1 f.1
  comp_smul _ _ _ f r g := by
    apply Subtype.ext
    exact Algebra.smul_mul_assoc r g.1 f.1

/-- Finite-dimensionality of the algebra descends to every primitive-
projective Hom space. -/
noncomputable instance homFinite [Module.Finite k A]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    (i j : S.ProjectiveCategory) :
    Module.Finite k (i ⟶ j) := by
  apply Module.Finite.of_injective
    (idempotentCorner (k := k) S.idempotent
      (S.projectiveVertex j) (S.projectiveVertex i)).subtype
  exact Subtype.val_injective

/-- Every chosen primitive-projective identity is nonzero. -/
theorem id_ne_zero
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    (i : S.ProjectiveCategory) :
    (𝟙 i : i ⟶ i) ≠ 0 := by
  intro h
  have hval := congrArg Subtype.val h
  change S.idempotent (S.projectiveVertex i) = (0 : A) at hval
  have hcoord := S.quotientEquiv_mk_idempotent
    (S.projectiveVertex i) (S.projectiveVertex i)
  rw [hval] at hcoord
  simp at hcoord

end ProjectiveCategory

/-- One copy of every chosen primitive projective in the additive envelope. -/
abbrev projectiveGenerator
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι)) :
    Mat_ S.ProjectiveCategory where
  ι := S.ProjectiveIndex
  fintype := Fintype.ofFinite S.ProjectiveIndex
  X i := i

/-- The endomorphism algebra of the additive generator of chosen primitive
projectives. -/
abbrev ProjectiveEndAlgebra
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι)) :=
  CategoryTheory.End (S.projectiveGenerator)

/-- The complete idempotent-component matrix of an algebra element. -/
def projectiveComponentMatrix
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι)) (a : A) :
    S.ProjectiveEndAlgebra :=
  fun i j ↦
    ⟨S.idempotent (S.projectiveVertex j) * a *
      S.idempotent (S.projectiveVertex i), ⟨a, rfl⟩⟩

@[simp]
theorem projectiveComponentMatrix_apply_val
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι)) (a : A)
    (i j : S.ProjectiveIndex) :
    (S.projectiveComponentMatrix a i j).1 =
      S.idempotent (S.projectiveVertex j) * a *
        S.idempotent (S.projectiveVertex i) :=
  rfl

/-- An algebra element acts on the additive generator by its complete matrix
of two-sided idempotent components. -/
def toProjectiveEndAlgHom
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι)) :
    A →ₐ[k] S.ProjectiveEndAlgebra where
  toFun := S.projectiveComponentMatrix
  map_zero' := by
    apply CategoryTheory.Mat_.hom_ext
    intro i j
    apply Subtype.ext
    change S.idempotent (S.projectiveVertex j) * 0 *
      S.idempotent (S.projectiveVertex i) =
        ((0 : idempotentCorner (k := k) S.idempotent
          (S.projectiveVertex j) (S.projectiveVertex i)) : A)
    simp
  map_one' := by
    classical
    rw [CategoryTheory.End.one_def]
    apply CategoryTheory.Mat_.hom_ext
    intro i j
    by_cases hij : i = j
    · subst j
      apply Subtype.ext
      rw [projectiveComponentMatrix_apply_val,
        CategoryTheory.Mat_.id_apply_self, ProjectiveCategory.id_val]
      simp only [mul_one]
      exact S.complete.toOrthogonalIdempotents.idem _ |>.eq
    · apply Subtype.ext
      change S.idempotent (S.projectiveVertex j) * 1 *
          S.idempotent (S.projectiveVertex i) =
        ((𝟙 S.projectiveGenerator : S.ProjectiveEndAlgebra) i j).1
      rw [CategoryTheory.Mat_.id_apply_of_ne _ _ _ hij]
      change S.idempotent (S.projectiveVertex j) * 1 *
          S.idempotent (S.projectiveVertex i) = 0
      rw [mul_one]
      exact S.complete.toOrthogonalIdempotents.ortho
        (fun h ↦ hij (S.projectiveVertex_injective h).symm)
  map_add' a b := by
    apply CategoryTheory.Mat_.hom_ext
    intro i j
    apply Subtype.ext
    change S.idempotent (S.projectiveVertex j) * (a + b) *
        S.idempotent (S.projectiveVertex i) =
      ((S.projectiveComponentMatrix a +
        S.projectiveComponentMatrix b) i j).1
    change S.idempotent (S.projectiveVertex j) * (a + b) *
        S.idempotent (S.projectiveVertex i) =
      S.idempotent (S.projectiveVertex j) * a *
          S.idempotent (S.projectiveVertex i) +
        S.idempotent (S.projectiveVertex j) * b *
          S.idempotent (S.projectiveVertex i)
    rw [mul_add, add_mul]
  map_mul' a b := by
    apply CategoryTheory.Mat_.hom_ext
    intro i j
    apply Subtype.ext
    change S.idempotent (S.projectiveVertex j) * (a * b) *
        S.idempotent (S.projectiveVertex i) =
      ((S.projectiveComponentMatrix b ≫
        S.projectiveComponentMatrix a) i j).1
    rw [CategoryTheory.Mat_.comp_apply]
    have hsum :
        ((∑ z : S.ProjectiveIndex,
            S.projectiveComponentMatrix b i z ≫
              S.projectiveComponentMatrix a z j) :
          i ⟶ j).1 =
        ∑ z : S.ProjectiveIndex,
          (S.projectiveComponentMatrix b i z ≫
            S.projectiveComponentMatrix a z j).1 := by
      exact map_sum
        (idempotentCorner (k := k) S.idempotent
          (S.projectiveVertex j) (S.projectiveVertex i)).subtype
        (fun z : S.ProjectiveIndex ↦
          S.projectiveComponentMatrix b i z ≫
            S.projectiveComponentMatrix a z j) Finset.univ
    rw [hsum]
    simp only [ProjectiveCategory.comp_val,
      projectiveComponentMatrix_apply_val]
    change S.idempotent (S.projectiveVertex j) * (a * b) *
        S.idempotent (S.projectiveVertex i) =
      ∑ z : S.ProjectiveIndex,
        (S.idempotent (S.projectiveVertex j) * a *
            S.idempotent (S.projectiveVertex z)) *
          (S.idempotent (S.projectiveVertex z) * b *
            S.idempotent (S.projectiveVertex i))
    have hterm (z : S.ProjectiveIndex) :
        (S.idempotent (S.projectiveVertex j) * a *
            S.idempotent (S.projectiveVertex z)) *
          (S.idempotent (S.projectiveVertex z) * b *
            S.idempotent (S.projectiveVertex i)) =
        S.idempotent (S.projectiveVertex j) *
          (a * (S.idempotent (S.projectiveVertex z) *
            (b * S.idempotent (S.projectiveVertex i)))) := by
      simp only [mul_assoc]
      rw [← mul_assoc (S.idempotent (S.projectiveVertex z))
        (S.idempotent (S.projectiveVertex z))
        (b * S.idempotent (S.projectiveVertex i)),
        S.complete.toOrthogonalIdempotents.idem
          (S.projectiveVertex z) |>.eq]
    simp_rw [hterm]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [Fintype.sum_equiv S.projectiveVertexEquiv _ S.idempotent
      (fun _ ↦ rfl)]
    rw [S.complete.complete]
    simp only [one_mul, mul_assoc]
  commutes' r := by
    apply CategoryTheory.Mat_.hom_ext
    intro i j
    apply Subtype.ext
    change S.idempotent (S.projectiveVertex j) * algebraMap k A r *
        S.idempotent (S.projectiveVertex i) =
      r • ((𝟙 S.projectiveGenerator : S.ProjectiveEndAlgebra) i j).1
    by_cases hij : i = j
    · subst j
      rw [CategoryTheory.Mat_.id_apply_self, ProjectiveCategory.id_val]
      change S.idempotent (S.projectiveVertex i) * algebraMap k A r *
          S.idempotent (S.projectiveVertex i) =
        r • S.idempotent (S.projectiveVertex i)
      rw [← Algebra.commutes]
      simp only [Algebra.smul_def, mul_assoc]
      rw [S.complete.toOrthogonalIdempotents.idem _ |>.eq]
    · rw [CategoryTheory.Mat_.id_apply_of_ne _ _ _ hij]
      change S.idempotent (S.projectiveVertex j) * algebraMap k A r *
          S.idempotent (S.projectiveVertex i) = r • (0 : A)
      rw [smul_zero]
      rw [← Algebra.commutes]
      simp only [mul_assoc]
      rw [S.complete.toOrthogonalIdempotents.ortho
        (fun h ↦ hij (S.projectiveVertex_injective h).symm), mul_zero]

/-- The selected idempotents still sum to one after passage to the small
projective index. -/
theorem sum_idempotent_projectiveVertex
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι)) :
    ∑ i : S.ProjectiveIndex, S.idempotent (S.projectiveVertex i) = 1 := by
  rw [Fintype.sum_equiv S.projectiveVertexEquiv _ S.idempotent
    (fun _ ↦ rfl)]
  exact S.complete.complete

/-- Sum all entries of an endomorphism matrix back into the algebra. -/
def fromProjectiveEnd
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    (f : S.ProjectiveEndAlgebra) : A :=
  ∑ i : S.ProjectiveIndex, ∑ j : S.ProjectiveIndex, (f i j).1

@[simp]
theorem fromProjectiveEnd_projectiveComponentMatrix
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι)) (a : A) :
    S.fromProjectiveEnd (S.projectiveComponentMatrix a) = a := by
  unfold fromProjectiveEnd
  simp only [projectiveComponentMatrix_apply_val]
  calc
    (∑ i : S.ProjectiveIndex, ∑ j : S.ProjectiveIndex,
        S.idempotent (S.projectiveVertex j) * a *
          S.idempotent (S.projectiveVertex i)) =
        ∑ i : S.ProjectiveIndex,
          (∑ j : S.ProjectiveIndex,
            S.idempotent (S.projectiveVertex j)) * a *
              S.idempotent (S.projectiveVertex i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul, Finset.sum_mul]
    _ = ∑ i : S.ProjectiveIndex,
          a * S.idempotent (S.projectiveVertex i) := by
        rw [S.sum_idempotent_projectiveVertex]
        simp only [one_mul]
    _ = a * ∑ i : S.ProjectiveIndex,
          S.idempotent (S.projectiveVertex i) := by
        rw [Finset.mul_sum]
    _ = a := by
        rw [S.sum_idempotent_projectiveVertex, mul_one]

@[simp]
theorem projectiveComponentMatrix_fromProjectiveEnd
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    (f : S.ProjectiveEndAlgebra) :
    S.projectiveComponentMatrix (S.fromProjectiveEnd f) = f := by
  apply CategoryTheory.Mat_.hom_ext
  intro i j
  apply Subtype.ext
  change S.idempotent (S.projectiveVertex j) *
      (∑ x : S.ProjectiveIndex, ∑ y : S.ProjectiveIndex, (f x y).1) *
        S.idempotent (S.projectiveVertex i) = (f i j).1
  rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_eq_single i]
  · rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_eq_single j]
    · rw [ProjectiveCategory.idempotent_mul_val,
        ProjectiveCategory.val_mul_idempotent]
    · intro y hy hyj
      rw [ProjectiveCategory.idempotent_mul_val_eq_zero_of_ne
        S (Ne.symm hyj), zero_mul]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · intro x hx hxi
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro y hy
    rw [mul_assoc, ProjectiveCategory.val_mul_idempotent_eq_zero_of_ne
      S hxi, mul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- A complete family of primitive idempotents identifies the split-basic
algebra with the endomorphism algebra of the additive generator of its
primitive-projective category. -/
def projectiveEndAlgEquiv
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι)) :
    A ≃ₐ[k] S.ProjectiveEndAlgebra :=
  AlgEquiv.ofBijective S.toProjectiveEndAlgHom ⟨
    (fun a b hab ↦ by
      apply_fun S.fromProjectiveEnd at hab
      change S.fromProjectiveEnd (S.projectiveComponentMatrix a) =
        S.fromProjectiveEnd (S.projectiveComponentMatrix b) at hab
      simpa using hab),
    (fun f ↦ ⟨S.fromProjectiveEnd f,
      S.projectiveComponentMatrix_fromProjectiveEnd f⟩)⟩

@[simp]
theorem projectiveEndAlgEquiv_apply
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι)) (a : A) :
    S.projectiveEndAlgEquiv a = S.projectiveComponentMatrix a :=
  rfl

end LargeIndecomposable.SplitBasicIdempotents
