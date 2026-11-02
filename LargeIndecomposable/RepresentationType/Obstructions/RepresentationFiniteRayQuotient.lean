module

public import LargeIndecomposable.RayCategories.Distributive.RayIrreducibleRadicalLayer
public import LargeIndecomposable.RepresentationType.Basic.RepresentationFiniteUniverse
public import LargeIndecomposable.RepresentationType.Basic.RepresentationFiniteIdeals
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Tactic
public import LargeIndecomposable.RayCategories.Basic.RayQuiverArrowRigidity
public import Mathlib.SetTheory.Cardinal.Embedding
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

/-!
# Quotient extraction from incoming four-ray forks

Coefficient functionals on primitive corners modulo `Jac(A)^2` assemble
surjective algebra maps onto the outward affine-`D₄` star or the one-loop
three-leaf star.  Thus every incoming four-arrow fork gives a
representation-infinite quotient.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.SplitBasicIdempotents

universe u v x

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

variable [Module.Finite k A]

/-- The scalar residue of an ambient algebra element at a chosen primitive
projective. -/
def ambientVertexResidue (p : S.ProjectiveCategory) : A →ₐ[k] k :=
  (Pi.evalAlgHom k (fun _ : ι ↦ k) (S.projectiveVertex p)).comp
    (S.quotientEquiv.toAlgHom.comp
      (Ideal.Quotient.mkₐ k (Ring.jacobson A)))

/-- Projection of the ambient algebra to a primitive two-sided corner. -/
def ambientCornerLinearMap (p q : S.ProjectiveCategory) : A →ₗ[k] A where
  toFun a := S.idempotent (S.projectiveVertex p) * a *
    S.idempotent (S.projectiveVertex q)
  map_add' a b := by rw [mul_add, add_mul]
  map_smul' c a := by
    simp only [RingHom.id_apply]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

omit [Module.Finite k A] in
@[simp]
theorem ambientCornerLinearMap_apply (p q : S.ProjectiveCategory) (a : A) :
    S.ambientCornerLinearMap p q a =
      S.idempotent (S.projectiveVertex p) * a *
        S.idempotent (S.projectiveVertex q) :=
  rfl

omit [Module.Finite k A] in
/-- Every off-diagonal primitive corner is radical. -/
theorem ambientCorner_mem_jacobson_of_ne
    {p q : S.ProjectiveCategory} (hpq : p ≠ q) (a : A) :
    S.ambientCornerLinearMap p q a ∈ Ring.jacobson A := by
  let f : q ⟶ p :=
    ⟨S.ambientCornerLinearMap p q a, ⟨a, rfl⟩⟩
  exact ProjectiveCategory.offDiagonal_val_mem_jacobson S hpq.symm f

omit [Module.Finite k A] in
/-- The diagonal primitive corner of an element differs from its scalar
residue by a radical element. -/
theorem ambientDiagonal_sub_residue_mem_jacobson
    (p : S.ProjectiveCategory) (a : A) :
    S.ambientCornerLinearMap p p a -
        S.ambientVertexResidue p a •
          S.idempotent (S.projectiveVertex p) ∈ Ring.jacobson A := by
  let f : End p :=
    ⟨S.ambientCornerLinearMap p p a, ⟨a, rfl⟩⟩
  have hfres : S.projectiveEndResidue p f =
      S.ambientVertexResidue p a := by
    dsimp [f, projectiveEndResidue, ambientVertexResidue,
      ambientCornerLinearMap]
    simp only [map_mul, Pi.mul_apply]
    simp [S.quotientEquiv_mk_idempotent]
  let g : End p := f - S.ambientVertexResidue p a • (1 : End p)
  have hgres : S.projectiveEndResidue p g = 0 := by
    have hscalar : S.projectiveEndResidue p
        (S.ambientVertexResidue p a • (1 : End p)) =
          S.ambientVertexResidue p a := by
      simp [Algebra.smul_def, (S.projectiveEndResidue p).commutes]
    calc
      S.projectiveEndResidue p g =
          S.projectiveEndResidue p f -
            S.projectiveEndResidue p
              (S.ambientVertexResidue p a • (1 : End p)) := by
        exact map_sub (S.projectiveEndResidue p) f _
      _ = S.ambientVertexResidue p a - S.ambientVertexResidue p a := by
        rw [hfres, hscalar]
      _ = 0 := sub_self _
  have hgJ : g.1 ∈ Ring.jacobson A :=
    (S.projectiveEndResidue_eq_zero_iff_val_mem_jacobson p g).1 hgres
  change S.ambientCornerLinearMap p p a -
      S.ambientVertexResidue p a •
        S.idempotent (S.projectiveVertex p) ∈ Ring.jacobson A at hgJ
  exact hgJ

omit [Module.Finite k A] in
/-- Primitive-corner projection preserves the square of the ambient
Jacobson radical. -/
theorem ambientCorner_mem_jacobson_sq
    (p q : S.ProjectiveCategory) {a : A}
    (ha : a ∈ Ring.jacobson A * Ring.jacobson A) :
    S.ambientCornerLinearMap p q a ∈
      Ring.jacobson A * Ring.jacobson A := by
  exact (Ring.jacobson A * Ring.jacobson A).mul_mem_right
    (S.idempotent (S.projectiveVertex q))
    ((Ring.jacobson A * Ring.jacobson A).mul_mem_left
      (S.idempotent (S.projectiveVertex p)) ha)

omit [Module.Finite k A] in
/-- Ambient vertex residue vanishes on the Jacobson radical. -/
theorem ambientVertexResidue_eq_zero_of_mem_jacobson
    (p : S.ProjectiveCategory) {a : A} (ha : a ∈ Ring.jacobson A) :
    S.ambientVertexResidue p a = 0 := by
  change S.quotientEquiv
    (Ideal.Quotient.mk (Ring.jacobson A) a) (S.projectiveVertex p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  simp

omit [Module.Finite k A] in
@[simp]
theorem ambientVertexResidue_idempotent
    (p q : S.ProjectiveCategory) :
    S.ambientVertexResidue p
        (S.idempotent (S.projectiveVertex q)) =
      if q = p then 1 else 0 := by
  change S.quotientEquiv
    (Ideal.Quotient.mk (Ring.jacobson A)
      (S.idempotent (S.projectiveVertex q)))
        (S.projectiveVertex p) = if q = p then 1 else 0
  rw [S.quotientEquiv_mk_idempotent]
  by_cases hqp : q = p
  · subst q
    simp
  · have hv : S.projectiveVertex q ≠ S.projectiveVertex p :=
      fun h ↦ hqp (S.projectiveVertex_injective h)
    simp [hqp, hv]

omit [Module.Finite k A] in
/-- An off-diagonal corner projection kills every primitive idempotent. -/
theorem ambientCornerLinearMap_idempotent_eq_zero
    {p q : S.ProjectiveCategory} (hpq : p ≠ q)
    (r : S.ProjectiveCategory) :
    S.ambientCornerLinearMap p q
      (S.idempotent (S.projectiveVertex r)) = 0 := by
  dsimp [ambientCornerLinearMap]
  by_cases hpr : p = r
  · subst r
    rw [S.complete.toOrthogonalIdempotents.idem
      (S.projectiveVertex p) |>.eq]
    exact S.complete.toOrthogonalIdempotents.ortho (fun h ↦
      hpq (S.projectiveVertex_injective h))
  · have hv : S.projectiveVertex p ≠ S.projectiveVertex r :=
      fun h ↦ hpr (S.projectiveVertex_injective h)
    rw [S.complete.toOrthogonalIdempotents.ortho hv, zero_mul]

omit [Module.Finite k A] in
/-- Modulo `Jac(A)^2`, an off-diagonal primitive corner obeys the expected
left/right scalar-residue Leibniz rule. -/
theorem ambientCorner_mul_sub_residues_mem_jacobson_sq
    {p q : S.ProjectiveCategory} (hpq : p ≠ q) (a b : A) :
    S.ambientCornerLinearMap p q (a * b) -
        S.ambientVertexResidue p a • S.ambientCornerLinearMap p q b -
          S.ambientVertexResidue q b • S.ambientCornerLinearMap p q a ∈
      Ring.jacobson A * Ring.jacobson A := by
  classical
  let J := Ring.jacobson A
  let J2 := J * J
  let term : S.ProjectiveIndex → A := fun r ↦
    S.ambientCornerLinearMap p r a * S.ambientCornerLinearMap r q b
  have hdecomp : S.ambientCornerLinearMap p q (a * b) = ∑ r, term r := by
    dsimp [term, ambientCornerLinearMap]
    calc
      S.idempotent (S.projectiveVertex p) * (a * b) *
          S.idempotent (S.projectiveVertex q) =
          S.idempotent (S.projectiveVertex p) *
            (a * (∑ r : S.ProjectiveIndex,
              S.idempotent (S.projectiveVertex r)) * b) *
                S.idempotent (S.projectiveVertex q) := by
            rw [S.sum_idempotent_projectiveVertex]
            simp only [mul_one]
      _ = ∑ r : S.ProjectiveIndex,
          (S.idempotent (S.projectiveVertex p) * a *
            S.idempotent (S.projectiveVertex r)) *
              (S.idempotent (S.projectiveVertex r) * b *
                S.idempotent (S.projectiveVertex q)) := by
            simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
            apply Finset.sum_congr rfl
            intro r hr
            rw [← mul_assoc (S.idempotent (S.projectiveVertex r))
              (S.idempotent (S.projectiveVertex r))]
            rw [S.complete.toOrthogonalIdempotents.idem
              (S.projectiveVertex r) |>.eq]
  have hterm_other (r : S.ProjectiveIndex) (hrp : r ≠ p) (hrq : r ≠ q) :
      term r ∈ J2 := by
    exact Ideal.mul_mem_mul
      (S.ambientCorner_mem_jacobson_of_ne (Ne.symm hrp) a)
      (S.ambientCorner_mem_jacobson_of_ne hrq b)
  have hterm_p :
      term p - S.ambientVertexResidue p a •
          S.ambientCornerLinearMap p q b ∈ J2 := by
    have hleft := S.ambientDiagonal_sub_residue_mem_jacobson p a
    have hright := S.ambientCorner_mem_jacobson_of_ne hpq b
    have hmul :
        (S.ambientCornerLinearMap p p a -
            S.ambientVertexResidue p a •
              S.idempotent (S.projectiveVertex p)) *
              S.ambientCornerLinearMap p q b ∈ J2 :=
      Ideal.mul_mem_mul hleft hright
    convert hmul using 1
    dsimp [term]
    have hep : S.idempotent (S.projectiveVertex p) *
        S.idempotent (S.projectiveVertex p) =
          S.idempotent (S.projectiveVertex p) :=
      S.complete.toOrthogonalIdempotents.idem (S.projectiveVertex p) |>.eq
    simp only [sub_mul, Algebra.smul_mul_assoc, ← mul_assoc, hep]
  have hterm_q :
      term q - S.ambientVertexResidue q b •
          S.ambientCornerLinearMap p q a ∈ J2 := by
    have hleft := S.ambientCorner_mem_jacobson_of_ne hpq a
    have hright := S.ambientDiagonal_sub_residue_mem_jacobson q b
    have hmul :
        S.ambientCornerLinearMap p q a *
          (S.ambientCornerLinearMap q q b -
            S.ambientVertexResidue q b •
              S.idempotent (S.projectiveVertex q)) ∈ J2 :=
      Ideal.mul_mem_mul hleft hright
    convert hmul using 1
    dsimp [term]
    have heq : S.idempotent (S.projectiveVertex q) *
        S.idempotent (S.projectiveVertex q) =
          S.idempotent (S.projectiveVertex q) :=
      S.complete.toOrthogonalIdempotents.idem (S.projectiveVertex q) |>.eq
    have hraw :
        S.idempotent (S.projectiveVertex p) * a *
            S.idempotent (S.projectiveVertex q) *
              S.idempotent (S.projectiveVertex q) =
          S.idempotent (S.projectiveVertex p) * a *
            S.idempotent (S.projectiveVertex q) := by
      rw [mul_assoc, heq]
    simp only [mul_sub, Algebra.mul_smul_comm, hraw]
  rw [hdecomp]
  let rest := Finset.univ.erase p |>.erase q
  have hsum : (∑ r : S.ProjectiveIndex, term r) =
      term p + term q + ∑ r ∈ rest, term r := by
    calc
      (∑ r : S.ProjectiveIndex, term r) =
          (∑ r ∈ (Finset.univ : Finset S.ProjectiveIndex).erase p, term r) +
            term p :=
        (Finset.sum_erase_add Finset.univ term (Finset.mem_univ p)).symm
      _ = ((∑ r ∈ rest, term r) + term q) + term p := by
        rw [Finset.sum_erase_add
          ((Finset.univ : Finset S.ProjectiveIndex).erase p) term]
        simp [hpq.symm]
      _ = term p + term q + ∑ r ∈ rest, term r := by abel
  rw [hsum]
  have hrest : ∑ r ∈ rest, term r ∈ J2 := by
    apply Submodule.sum_mem
    intro r hr
    have hrs : r ≠ q ∧ r ≠ p := by simpa [rest] using hr
    have hrp : r ≠ p := hrs.2
    have hrq : r ≠ q := hrs.1
    exact hterm_other r hrp hrq
  have hadd := J2.add_mem (J2.add_mem hterm_p hterm_q) hrest
  convert hadd using 1
  abel

/-- A nonzero class in an off-diagonal primitive corner admits a normalized
coefficient functional.  It kills `Jac(A)^2` and is a derivation with respect
to the two endpoint residue characters. -/
theorem exists_ambientCornerCoefficient
    {p q : S.ProjectiveCategory} (hpq : p ≠ q)
    (r : q ⟶ p)
    (hr : r.1 ∉ Ring.jacobson A * Ring.jacobson A) :
    ∃ phi : A →ₗ[k] k,
      phi r.1 = 1 ∧
      (∀ {a : A}, a ∈ Ring.jacobson A * Ring.jacobson A → phi a = 0) ∧
      (∀ {a : A}, S.ambientCornerLinearMap p q a = 0 → phi a = 0) ∧
      ∀ a b : A,
        phi (a * b) =
          S.ambientVertexResidue p a * phi b +
            phi a * S.ambientVertexResidue q b := by
  let J2k : Submodule k A :=
    (Ring.jacobson A * Ring.jacobson A : Ideal A).restrictScalars k
  obtain ⟨f, hfr, hfJ2⟩ :=
    J2k.exists_dual_map_eq_bot_of_notMem hr inferInstance
  let corner := S.ambientCornerLinearMap p q
  let phi : A →ₗ[k] k := ((f r.1)⁻¹ • f).comp corner
  have hcorner_r : corner r.1 = r.1 := by
    dsimp [corner, ambientCornerLinearMap]
    rw [ProjectiveCategory.idempotent_mul_val,
      ProjectiveCategory.val_mul_idempotent]
  have hkill_f {a : A} (ha : a ∈ Ring.jacobson A * Ring.jacobson A) :
      f a = 0 := by
    have ha' : a ∈ J2k := ha
    have hmem : f a ∈ J2k.map f := ⟨a, ha', rfl⟩
    rw [hfJ2] at hmem
    simpa using hmem
  have hkill {a : A} (ha : a ∈ Ring.jacobson A * Ring.jacobson A) :
      phi a = 0 := by
    dsimp [phi]
    change (f r.1)⁻¹ * f (corner a) = 0
    rw [hkill_f (S.ambientCorner_mem_jacobson_sq p q ha)]
    exact mul_zero _
  refine ⟨phi, ?_, hkill, ?_, ?_⟩
  · dsimp [phi]
    change (f r.1)⁻¹ * f (corner r.1) = 1
    rw [hcorner_r]
    exact inv_mul_cancel₀ hfr
  · intro a ha
    dsimp [phi]
    change (f r.1)⁻¹ * f (corner a) = 0
    rw [show corner a = 0 by exact ha, map_zero, mul_zero]
  · intro a b
    have hd := S.ambientCorner_mul_sub_residues_mem_jacobson_sq hpq a b
    have hz := hkill_f hd
    have heq :
        f (S.ambientCornerLinearMap p q (a * b)) =
          S.ambientVertexResidue p a *
              f (S.ambientCornerLinearMap p q b) +
            S.ambientVertexResidue q b *
              f (S.ambientCornerLinearMap p q a) := by
      simp only [map_sub, map_smul, smul_eq_mul] at hz
      linear_combination hz
    dsimp [phi]
    change (f r.1)⁻¹ * f (corner (a * b)) =
      S.ambientVertexResidue p a * ((f r.1)⁻¹ * f (corner b)) +
        ((f r.1)⁻¹ * f (corner a)) * S.ambientVertexResidue q b
    rw [heq]
    ring

/-- A chosen normalized coefficient functional for a nonzero first-radical
corner class. -/
noncomputable def ambientCornerCoefficient
    {p q : S.ProjectiveCategory} (hpq : p ≠ q)
    (r : q ⟶ p)
    (hr : r.1 ∉ Ring.jacobson A * Ring.jacobson A) : A →ₗ[k] k :=
  Classical.choose (S.exists_ambientCornerCoefficient hpq r hr)

@[simp]
theorem ambientCornerCoefficient_rep
    {p q : S.ProjectiveCategory} (hpq : p ≠ q)
    (r : q ⟶ p)
    (hr : r.1 ∉ Ring.jacobson A * Ring.jacobson A) :
    S.ambientCornerCoefficient hpq r hr r.1 = 1 :=
  (Classical.choose_spec
    (S.exists_ambientCornerCoefficient hpq r hr)).1

/-- The normalized primitive-corner coefficient kills the ambient radical
square. -/
theorem ambientCornerCoefficient_eq_zero_of_mem_jacobson_sq
    {p q : S.ProjectiveCategory} (hpq : p ≠ q)
    (r : q ⟶ p)
    (hr : r.1 ∉ Ring.jacobson A * Ring.jacobson A)
    {a : A} (ha : a ∈ Ring.jacobson A * Ring.jacobson A) :
    S.ambientCornerCoefficient hpq r hr a = 0 :=
  (Classical.choose_spec
    (S.exists_ambientCornerCoefficient hpq r hr)).2.1 ha

theorem ambientCornerCoefficient_eq_zero_of_corner_eq_zero
    {p q : S.ProjectiveCategory} (hpq : p ≠ q)
    (r : q ⟶ p)
    (hr : r.1 ∉ Ring.jacobson A * Ring.jacobson A)
    {a : A} (ha : S.ambientCornerLinearMap p q a = 0) :
    S.ambientCornerCoefficient hpq r hr a = 0 :=
  (Classical.choose_spec
    (S.exists_ambientCornerCoefficient hpq r hr)).2.2.1 ha

theorem ambientCornerCoefficient_mul
    {p q : S.ProjectiveCategory} (hpq : p ≠ q)
    (r : q ⟶ p)
    (hr : r.1 ∉ Ring.jacobson A * Ring.jacobson A)
    (a b : A) :
    S.ambientCornerCoefficient hpq r hr (a * b) =
      S.ambientVertexResidue p a *
          S.ambientCornerCoefficient hpq r hr b +
        S.ambientCornerCoefficient hpq r hr a *
          S.ambientVertexResidue q b :=
  (Classical.choose_spec
    (S.exists_ambientCornerCoefficient hpq r hr)).2.2.2 a b

/-- Restrict an ambient first-radical-layer coefficient to its primitive
projective Hom space. -/
def projectiveHomFirstRadicalCoefficient
    {p q : S.ProjectiveCategory} (hpq : p ≠ q)
    (r : q ⟶ p)
    (hr : r.1 ∉ Ring.jacobson A * Ring.jacobson A) :
    (q ⟶ p) →ₗ[k] k where
  toFun g := S.ambientCornerCoefficient hpq r hr g.1
  map_add' g h := map_add (S.ambientCornerCoefficient hpq r hr) g.1 h.1
  map_smul' c g := map_smul (S.ambientCornerCoefficient hpq r hr) c g.1

@[simp]
theorem projectiveHomFirstRadicalCoefficient_rep
    {p q : S.ProjectiveCategory} (hpq : p ≠ q)
    (r : q ⟶ p)
    (hr : r.1 ∉ Ring.jacobson A * Ring.jacobson A) :
    S.projectiveHomFirstRadicalCoefficient hpq r hr r = 1 :=
  S.ambientCornerCoefficient_rep hpq r hr

/-- The restricted first-radical coefficient vanishes on every morphism
whose ambient algebra value lies in the radical square. -/
theorem projectiveHomFirstRadicalCoefficient_eq_zero_of_mem_jacobson_sq
    {p q : S.ProjectiveCategory} (hpq : p ≠ q)
    (r : q ⟶ p)
    (hr : r.1 ∉ Ring.jacobson A * Ring.jacobson A)
    (g : q ⟶ p) (hg : g.1 ∈ Ring.jacobson A * Ring.jacobson A) :
    S.projectiveHomFirstRadicalCoefficient hpq r hr g = 0 :=
  S.ambientCornerCoefficient_eq_zero_of_mem_jacobson_sq hpq r hr hg

/-- Source-residue covariance of the restricted first-radical coefficient. -/
theorem projectiveHomFirstRadicalCoefficient_comp_left
    {p q : S.ProjectiveCategory} (hpq : p ≠ q)
    (r : q ⟶ p)
    (hr : r.1 ∉ Ring.jacobson A * Ring.jacobson A)
    (a : End q) :
    S.projectiveHomFirstRadicalCoefficient hpq r hr
        (a.asHom ≫ r) = S.projectiveEndResidue q a := by
  have hrJ : r.1 ∈ Ring.jacobson A :=
    ProjectiveCategory.offDiagonal_val_mem_jacobson S hpq.symm r
  change S.ambientCornerCoefficient hpq r hr (r.1 * a.1) = _
  rw [S.ambientCornerCoefficient_mul hpq r hr,
    S.ambientVertexResidue_eq_zero_of_mem_jacobson p hrJ,
    zero_mul, S.ambientCornerCoefficient_rep, zero_add, one_mul]
  rfl

/-- Target-residue covariance of the restricted first-radical coefficient. -/
theorem projectiveHomFirstRadicalCoefficient_comp_right
    {p q : S.ProjectiveCategory} (hpq : p ≠ q)
    (r : q ⟶ p)
    (hr : r.1 ∉ Ring.jacobson A * Ring.jacobson A)
    (b : End p) :
    S.projectiveHomFirstRadicalCoefficient hpq r hr
        (r ≫ b.asHom) = S.projectiveEndResidue p b := by
  have hrJ : r.1 ∈ Ring.jacobson A :=
    ProjectiveCategory.offDiagonal_val_mem_jacobson S hpq.symm r
  change S.ambientCornerCoefficient hpq r hr (b.1 * r.1) = _
  rw [S.ambientCornerCoefficient_mul hpq r hr,
    S.ambientCornerCoefficient_rep,
    S.ambientVertexResidue_eq_zero_of_mem_jacobson q hrJ,
    mul_one, mul_zero, add_zero]
  rfl

/-- The radical part of the diagonal primitive corner at `p`. -/
def ambientDiagonalRadicalPart (p : S.ProjectiveCategory) : A →ₗ[k] A where
  toFun a := S.ambientCornerLinearMap p p a -
    S.ambientVertexResidue p a • S.idempotent (S.projectiveVertex p)
  map_add' a b := by
    rw [map_add, map_add, add_smul]
    abel
  map_smul' c a := by
    rw [map_smul, map_smul]
    simp only [RingHom.id_apply, smul_sub, smul_smul]
    rw [smul_eq_mul]

omit [Module.Finite k A] in
@[simp]
theorem ambientDiagonalRadicalPart_apply
    (p : S.ProjectiveCategory) (a : A) :
    S.ambientDiagonalRadicalPart p a =
      S.ambientCornerLinearMap p p a -
        S.ambientVertexResidue p a •
          S.idempotent (S.projectiveVertex p) :=
  rfl

omit [Module.Finite k A] in
theorem ambientDiagonalRadicalPart_mem_jacobson
    (p : S.ProjectiveCategory) (a : A) :
    S.ambientDiagonalRadicalPart p a ∈ Ring.jacobson A :=
  S.ambientDiagonal_sub_residue_mem_jacobson p a

omit [Module.Finite k A] in
theorem idempotent_mul_ambientDiagonalRadicalPart
    (p : S.ProjectiveCategory) (a : A) :
    S.idempotent (S.projectiveVertex p) *
        S.ambientDiagonalRadicalPart p a =
      S.ambientDiagonalRadicalPart p a := by
  have he : S.idempotent (S.projectiveVertex p) *
      S.idempotent (S.projectiveVertex p) =
        S.idempotent (S.projectiveVertex p) :=
    S.complete.toOrthogonalIdempotents.idem (S.projectiveVertex p) |>.eq
  dsimp [ambientDiagonalRadicalPart, ambientCornerLinearMap]
  rw [mul_sub, Algebra.mul_smul_comm]
  simp only [← mul_assoc, he]

omit [Module.Finite k A] in
theorem ambientDiagonalRadicalPart_mul_idempotent
    (p : S.ProjectiveCategory) (a : A) :
    S.ambientDiagonalRadicalPart p a *
        S.idempotent (S.projectiveVertex p) =
      S.ambientDiagonalRadicalPart p a := by
  have he : S.idempotent (S.projectiveVertex p) *
      S.idempotent (S.projectiveVertex p) =
        S.idempotent (S.projectiveVertex p) :=
    S.complete.toOrthogonalIdempotents.idem (S.projectiveVertex p) |>.eq
  dsimp [ambientDiagonalRadicalPart, ambientCornerLinearMap]
  rw [sub_mul, Algebra.smul_mul_assoc]
  simp only [mul_assoc, he]

omit [Module.Finite k A] in
/-- Exact first-order expansion of the product of two diagonal primitive
corners, with quadratic remainder equal to the product of their radical
parts. -/
theorem ambientDiagonalCorner_product_expansion
    (p : S.ProjectiveCategory) (a b : A) :
    S.ambientCornerLinearMap p p a * S.ambientCornerLinearMap p p b -
        (S.ambientVertexResidue p a * S.ambientVertexResidue p b) •
          S.idempotent (S.projectiveVertex p) -
        S.ambientVertexResidue p a • S.ambientDiagonalRadicalPart p b -
        S.ambientVertexResidue p b • S.ambientDiagonalRadicalPart p a =
      S.ambientDiagonalRadicalPart p a *
        S.ambientDiagonalRadicalPart p b := by
  let ca := S.ambientVertexResidue p a
  let cb := S.ambientVertexResidue p b
  let e := S.idempotent (S.projectiveVertex p)
  let da := S.ambientDiagonalRadicalPart p a
  let db := S.ambientDiagonalRadicalPart p b
  have hua : S.ambientCornerLinearMap p p a = ca • e + da := by
    dsimp [ca, da, ambientDiagonalRadicalPart]
    abel
  have hub : S.ambientCornerLinearMap p p b = cb • e + db := by
    dsimp [cb, db, ambientDiagonalRadicalPart]
    abel
  have he : e * e = e :=
    S.complete.toOrthogonalIdempotents.idem (S.projectiveVertex p) |>.eq
  have heda : e * da = da :=
    S.idempotent_mul_ambientDiagonalRadicalPart p a
  have hedb : e * db = db :=
    S.idempotent_mul_ambientDiagonalRadicalPart p b
  have hdae : da * e = da :=
    S.ambientDiagonalRadicalPart_mul_idempotent p a
  have hda_cb_e : da * (cb • e) = cb • da := by
    rw [Algebra.mul_smul_comm, hdae]
  rw [hua, hub, add_mul, mul_add, mul_add]
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc]
  rw [he, hedb, hda_cb_e]
  rw [smul_smul]
  change (ca * cb) • e + ca • db + (cb • da + da * db) -
      (ca * cb) • e - ca • db - cb • da = da * db
  abel

omit [Module.Finite k A] in
/-- Modulo `Jac(A)^2`, the radical part of a diagonal primitive corner is
a derivation with respect to the corresponding scalar-residue character. -/
theorem ambientDiagonalRadicalPart_mul_sub_residues_mem_jacobson_sq
    (p : S.ProjectiveCategory) (a b : A) :
    S.ambientDiagonalRadicalPart p (a * b) -
        S.ambientVertexResidue p a •
          S.ambientDiagonalRadicalPart p b -
        S.ambientVertexResidue p b •
          S.ambientDiagonalRadicalPart p a ∈
      Ring.jacobson A * Ring.jacobson A := by
  classical
  let J := Ring.jacobson A
  let J2 := J * J
  let term : S.ProjectiveIndex → A := fun r ↦
    S.ambientCornerLinearMap p r a * S.ambientCornerLinearMap r p b
  have hdecomp : S.ambientCornerLinearMap p p (a * b) = ∑ r, term r := by
    dsimp [term, ambientCornerLinearMap]
    calc
      S.idempotent (S.projectiveVertex p) * (a * b) *
          S.idempotent (S.projectiveVertex p) =
          S.idempotent (S.projectiveVertex p) *
            (a * (∑ r : S.ProjectiveIndex,
              S.idempotent (S.projectiveVertex r)) * b) *
                S.idempotent (S.projectiveVertex p) := by
            rw [S.sum_idempotent_projectiveVertex]
            simp only [mul_one]
      _ = ∑ r : S.ProjectiveIndex,
          (S.idempotent (S.projectiveVertex p) * a *
            S.idempotent (S.projectiveVertex r)) *
              (S.idempotent (S.projectiveVertex r) * b *
                S.idempotent (S.projectiveVertex p)) := by
            simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
            apply Finset.sum_congr rfl
            intro r hr
            rw [← mul_assoc (S.idempotent (S.projectiveVertex r))
              (S.idempotent (S.projectiveVertex r))]
            rw [S.complete.toOrthogonalIdempotents.idem
              (S.projectiveVertex r) |>.eq]
  have hterm_other (r : S.ProjectiveIndex) (hrp : r ≠ p) :
      term r ∈ J2 := by
    exact Ideal.mul_mem_mul
      (S.ambientCorner_mem_jacobson_of_ne (Ne.symm hrp) a)
      (S.ambientCorner_mem_jacobson_of_ne hrp b)
  have hterm_p :
      term p -
          (S.ambientVertexResidue p a * S.ambientVertexResidue p b) •
            S.idempotent (S.projectiveVertex p) -
          S.ambientVertexResidue p a •
            S.ambientDiagonalRadicalPart p b -
          S.ambientVertexResidue p b •
            S.ambientDiagonalRadicalPart p a ∈ J2 := by
    have hquad :
        S.ambientDiagonalRadicalPart p a *
            S.ambientDiagonalRadicalPart p b ∈ J2 :=
      Ideal.mul_mem_mul
        (S.ambientDiagonalRadicalPart_mem_jacobson p a)
        (S.ambientDiagonalRadicalPart_mem_jacobson p b)
    rw [← S.ambientDiagonalCorner_product_expansion p a b] at hquad
    simpa [term] using hquad
  rw [ambientDiagonalRadicalPart_apply, hdecomp]
  have hsum : (∑ r : S.ProjectiveIndex, term r) =
      term p + ∑ r ∈ (Finset.univ : Finset S.ProjectiveIndex).erase p,
        term r := by
    calc
      (∑ r : S.ProjectiveIndex, term r) =
          (∑ r ∈ (Finset.univ : Finset S.ProjectiveIndex).erase p,
            term r) + term p :=
        (Finset.sum_erase_add Finset.univ term (Finset.mem_univ p)).symm
      _ = term p + ∑ r ∈
          (Finset.univ : Finset S.ProjectiveIndex).erase p, term r := by
        abel
  rw [hsum, map_mul]
  have hrest :
      ∑ r ∈ (Finset.univ : Finset S.ProjectiveIndex).erase p,
          term r ∈ J2 := by
    apply Submodule.sum_mem
    intro r hr
    exact hterm_other r (by simpa using hr)
  have hadd := J2.add_mem hterm_p hrest
  dsimp [ambientDiagonalRadicalPart]
  convert hadd using 1
  abel

/-- A nonzero first-radical class in a diagonal primitive corner admits a
normalized coefficient functional.  It kills `Jac(A)^2` and is a derivation
with respect to the endpoint residue character. -/
theorem exists_ambientDiagonalCoefficient
    (p : S.ProjectiveCategory) (r : End p)
    (hrJ : r.1 ∈ Ring.jacobson A)
    (hr : r.1 ∉ Ring.jacobson A * Ring.jacobson A) :
    ∃ phi : A →ₗ[k] k,
      phi r.1 = 1 ∧
      (∀ {a : A}, a ∈ Ring.jacobson A * Ring.jacobson A → phi a = 0) ∧
      (∀ {a : A}, S.ambientDiagonalRadicalPart p a = 0 → phi a = 0) ∧
      ∀ a b : A,
        phi (a * b) =
          S.ambientVertexResidue p a * phi b +
            phi a * S.ambientVertexResidue p b := by
  let J2k : Submodule k A :=
    (Ring.jacobson A * Ring.jacobson A : Ideal A).restrictScalars k
  obtain ⟨f, hfr, hfJ2⟩ :=
    J2k.exists_dual_map_eq_bot_of_notMem hr inferInstance
  let radPart := S.ambientDiagonalRadicalPart p
  let phi : A →ₗ[k] k := ((f r.1)⁻¹ • f).comp radPart
  have hrad_r : radPart r.1 = r.1 := by
    dsimp [radPart, ambientDiagonalRadicalPart, ambientCornerLinearMap]
    rw [ProjectiveCategory.idempotent_mul_val,
      ProjectiveCategory.val_mul_idempotent]
    rw [S.ambientVertexResidue_eq_zero_of_mem_jacobson p hrJ,
      zero_smul, sub_zero]
  have hkill_f {a : A} (ha : a ∈ Ring.jacobson A * Ring.jacobson A) :
      f a = 0 := by
    have ha' : a ∈ J2k := ha
    have hmem : f a ∈ J2k.map f := ⟨a, ha', rfl⟩
    rw [hfJ2] at hmem
    simpa using hmem
  have hrad_mem {a : A}
      (ha : a ∈ Ring.jacobson A * Ring.jacobson A) :
      radPart a ∈ Ring.jacobson A * Ring.jacobson A := by
    have haJ : a ∈ Ring.jacobson A := Ideal.mul_le_left ha
    dsimp [radPart, ambientDiagonalRadicalPart]
    rw [S.ambientVertexResidue_eq_zero_of_mem_jacobson p haJ,
      zero_smul, sub_zero]
    exact S.ambientCorner_mem_jacobson_sq p p ha
  have hkill {a : A} (ha : a ∈ Ring.jacobson A * Ring.jacobson A) :
      phi a = 0 := by
    dsimp [phi]
    change (f r.1)⁻¹ * f (radPart a) = 0
    rw [hkill_f (hrad_mem ha), mul_zero]
  refine ⟨phi, ?_, hkill, ?_, ?_⟩
  · dsimp [phi]
    change (f r.1)⁻¹ * f (radPart r.1) = 1
    rw [hrad_r]
    exact inv_mul_cancel₀ hfr
  · intro a ha
    dsimp [phi]
    change (f r.1)⁻¹ * f (radPart a) = 0
    rw [show radPart a = 0 by exact ha, map_zero, mul_zero]
  · intro a b
    have hd :=
      S.ambientDiagonalRadicalPart_mul_sub_residues_mem_jacobson_sq p a b
    have hz := hkill_f hd
    have heq :
        f (S.ambientDiagonalRadicalPart p (a * b)) =
          S.ambientVertexResidue p a *
              f (S.ambientDiagonalRadicalPart p b) +
            S.ambientVertexResidue p b *
              f (S.ambientDiagonalRadicalPart p a) := by
      simp only [map_sub, map_smul, smul_eq_mul] at hz
      linear_combination hz
    dsimp [phi]
    change (f r.1)⁻¹ * f (radPart (a * b)) =
      S.ambientVertexResidue p a * ((f r.1)⁻¹ * f (radPart b)) +
        ((f r.1)⁻¹ * f (radPart a)) * S.ambientVertexResidue p b
    rw [heq]
    ring

/-- A chosen normalized coefficient functional for a nonzero diagonal
first-radical class. -/
noncomputable def ambientDiagonalCoefficient
    (p : S.ProjectiveCategory) (r : End p)
    (hrJ : r.1 ∈ Ring.jacobson A)
    (hr : r.1 ∉ Ring.jacobson A * Ring.jacobson A) : A →ₗ[k] k :=
  Classical.choose (S.exists_ambientDiagonalCoefficient p r hrJ hr)

@[simp]
theorem ambientDiagonalCoefficient_rep
    (p : S.ProjectiveCategory) (r : End p)
    (hrJ : r.1 ∈ Ring.jacobson A)
    (hr : r.1 ∉ Ring.jacobson A * Ring.jacobson A) :
    S.ambientDiagonalCoefficient p r hrJ hr r.1 = 1 :=
  (Classical.choose_spec
    (S.exists_ambientDiagonalCoefficient p r hrJ hr)).1

theorem ambientDiagonalCoefficient_eq_zero_of_radicalPart_eq_zero
    (p : S.ProjectiveCategory) (r : End p)
    (hrJ : r.1 ∈ Ring.jacobson A)
    (hr : r.1 ∉ Ring.jacobson A * Ring.jacobson A)
    {a : A} (ha : S.ambientDiagonalRadicalPart p a = 0) :
    S.ambientDiagonalCoefficient p r hrJ hr a = 0 :=
  (Classical.choose_spec
    (S.exists_ambientDiagonalCoefficient p r hrJ hr)).2.2.1 ha

theorem ambientDiagonalCoefficient_mul
    (p : S.ProjectiveCategory) (r : End p)
    (hrJ : r.1 ∈ Ring.jacobson A)
    (hr : r.1 ∉ Ring.jacobson A * Ring.jacobson A)
    (a b : A) :
    S.ambientDiagonalCoefficient p r hrJ hr (a * b) =
      S.ambientVertexResidue p a *
          S.ambientDiagonalCoefficient p r hrJ hr b +
        S.ambientDiagonalCoefficient p r hrJ hr a *
          S.ambientVertexResidue p b :=
  (Classical.choose_spec
    (S.exists_ambientDiagonalCoefficient p r hrJ hr)).2.2.2 a b

end LargeIndecomposable.SplitBasicIdempotents
