module

public import LargeIndecomposable.Modules.SplitBasic.SplitBasic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
public import Mathlib.RingTheory.TwoSidedIdeal.BigOperators
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

@[expose] public section

/-!
# Split-basic full-corner reduction

This file constructs a full idempotent corner of a finite-dimensional
algebra over an algebraically closed field and equips that corner with a
chosen split-basic presentation.  The construction is characteristic-free:
it uses Wedderburn--Artin for the semisimple quotient, lifting of orthogonal
idempotents through the nilpotent Jacobson radical, and the first isomorphism
theorem for the selected corner.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LargeIndecomposable

universe u v

variable {k : Type u} [Field k]

section FullElements

variable {R S : Type*} [Ring R] [Ring S]

/-- An element is full if it generates the unit two-sided ideal. -/
def IsFull (a : R) : Prop :=
  TwoSidedIdeal.span ({a} : Set R) = ⊤

/-- Fullness lifts along a surjective ring homomorphism with nil kernel. -/
theorem IsFull.of_surjective_of_ker_isNilpotent (f : R →+* S)
    (hf : Function.Surjective f)
    (hker : ∀ x ∈ RingHom.ker f, IsNilpotent x) {a : R}
    (ha : IsFull (f a)) : IsFull a := by
  rw [IsFull, ← TwoSidedIdeal.one_mem_iff]
  let I : TwoSidedIdeal R := TwoSidedIdeal.span {a}
  have hone : (1 : S) ∈ TwoSidedIdeal.span ({f a} : Set S) := by
    rw [ha]
    exact Set.mem_univ 1
  have hpreimage {y : S}
      (hy : y ∈ TwoSidedIdeal.span ({f a} : Set S)) :
      ∃ x : R, x ∈ I ∧ f x = y := by
    induction hy using TwoSidedIdeal.span_induction with
    | mem y hy =>
        rw [Set.mem_singleton_iff] at hy
        subst y
        exact ⟨a, TwoSidedIdeal.subset_span (Set.mem_singleton a), rfl⟩
    | zero => exact ⟨0, I.zero_mem, map_zero f⟩
    | add x y hx hy ihx ihy =>
        obtain ⟨x', hx'I, rfl⟩ := ihx
        obtain ⟨y', hy'I, rfl⟩ := ihy
        exact ⟨x' + y', I.add_mem hx'I hy'I, map_add f x' y'⟩
    | neg x hx ihx =>
        obtain ⟨x', hx'I, rfl⟩ := ihx
        exact ⟨-x', I.neg_mem hx'I, map_neg f x'⟩
    | left_absorb b x hx ihx =>
        obtain ⟨b', rfl⟩ := hf b
        obtain ⟨x', hx'I, rfl⟩ := ihx
        exact ⟨b' * x', I.mul_mem_left b' x' hx'I, map_mul f b' x'⟩
    | right_absorb b x hx ihx =>
        obtain ⟨b', rfl⟩ := hf b
        obtain ⟨x', hx'I, rfl⟩ := ihx
        exact ⟨x' * b', I.mul_mem_right x' b' hx'I, map_mul f x' b'⟩
  obtain ⟨x, hxI, hx⟩ := hpreimage hone
  have hxker : x - 1 ∈ RingHom.ker f := by
    simp [RingHom.mem_ker, hx]
  have hxunit : IsUnit x := by
    simpa using (hker (x - 1) hxker).isUnit_add_one
  obtain ⟨xunit, rfl⟩ := hxunit
  change (1 : R) ∈ I
  simpa using I.mul_mem_left (↑xunit⁻¹) (↑xunit) hxI

/-- A two-sided nil kernel lies in the Jacobson radical. -/
theorem RingHom.ker_le_jacobson_of_isNilpotent (f : R →+* S)
    (hker : ∀ x ∈ RingHom.ker f, IsNilpotent x) :
    RingHom.ker f ≤ Ring.jacobson R := by
  intro x hx
  rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff]
  intro y
  have hyx : y * x ∈ RingHom.ker f := by
    rw [RingHom.mem_ker] at hx ⊢
    rw [map_mul, hx, mul_zero]
  obtain ⟨z, hz⟩ := (hker (y * x) hyx).isUnit_add_one.exists_left_inv
  refine ⟨z, ?_⟩
  rw [Ideal.mem_bot]
  have hz' := congrArg (fun t : R ↦ t - 1) hz
  simpa [mul_add, mul_assoc] using hz'

/-- A surjection onto a semisimple ring whose kernel is nil has kernel
equal to the Jacobson radical. -/
theorem RingHom.ker_eq_jacobson_of_surjective_of_isNilpotent
    (f : R →+* S) (hf : Function.Surjective f)
    (hker : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    [IsSemisimpleRing S] :
    RingHom.ker f = Ring.jacobson R := by
  letI : RingHomSurjective f := ⟨hf⟩
  apply le_antisymm (RingHom.ker_le_jacobson_of_isNilpotent f hker)
  intro x hx
  rw [RingHom.mem_ker]
  have hfx : f x ∈ Submodule.map f.toSemilinearMap (Ring.jacobson R) :=
    ⟨x, hx, rfl⟩
  rw [Ring.map_jacobson_of_ker_le
      (RingHom.ker_le_jacobson_of_isNilpotent f hker),
    IsSemisimpleRing.jacobson_eq_bot] at hfx
  simpa using hfx

end FullElements

section CornerAlgebra

variable {R S : Type*} [Ring R] [Ring S]

/-- A ring homomorphism restricts to a homomorphism of idempotent
corners. -/
def IsIdempotentElem.cornerRingHom (f : R →+* S) {e : R}
    (he : IsIdempotentElem e) : he.Corner →+* (he.map f).Corner where
  toFun x := ⟨f x.1, by
    obtain ⟨r, hr⟩ := x.2
    refine ⟨f r, ?_⟩
    rw [← hr]
    simp⟩
  map_one' := Subtype.ext rfl
  map_mul' x y := Subtype.ext (map_mul f x.1 y.1)
  map_zero' := Subtype.ext (map_zero f)
  map_add' x y := Subtype.ext (map_add f x.1 y.1)

variable {k : Type*} [CommRing k] [Algebra k R] [Algebra k S]

/-- The scalar map into an idempotent corner of a `k`-algebra. -/
def IsIdempotentElem.cornerAlgebraMap {e : R} (he : IsIdempotentElem e) :
    k →+* he.Corner where
  toFun c := ⟨algebraMap k R c * e, by
    refine ⟨algebraMap k R c, ?_⟩
    change e * algebraMap k R c * e = algebraMap k R c * e
    rw [← (Algebra.commutes c e), mul_assoc, he]
  ⟩
  map_one' := by
    apply Subtype.ext
    change algebraMap k R 1 * e = e
    simp
  map_mul' c d := by
    apply Subtype.ext
    change algebraMap k R (c * d) * e =
      (algebraMap k R c * e) * (algebraMap k R d * e)
    calc
      algebraMap k R (c * d) * e =
          algebraMap k R c * (algebraMap k R d * e) := by
        rw [map_mul, mul_assoc]
      _ = algebraMap k R c * ((e * algebraMap k R d) * e) := by
        congr 1
        rw [← (Algebra.commutes d e), mul_assoc, he]
      _ = (algebraMap k R c * e) * (algebraMap k R d * e) := by
        simp only [mul_assoc]
  map_zero' := by
    apply Subtype.ext
    change algebraMap k R 0 * e = 0
    simp
  map_add' c d := by
    apply Subtype.ext
    change algebraMap k R (c + d) * e =
      algebraMap k R c * e + algebraMap k R d * e
    simp [add_mul]

theorem IsIdempotentElem.cornerAlgebraMap_commutes {e : R}
    (he : IsIdempotentElem e) (c : k) (x : he.Corner) :
    IsIdempotentElem.cornerAlgebraMap he c * x =
      x * IsIdempotentElem.cornerAlgebraMap he c := by
  apply Subtype.ext
  obtain ⟨hex, hxe⟩ := (Subsemigroup.mem_corner_iff he).mp x.2
  change (algebraMap k R c * e) * x.1 = x.1 * (algebraMap k R c * e)
  calc
    (algebraMap k R c * e) * x.1 = algebraMap k R c * x.1 := by
      rw [mul_assoc, hex]
    _ = x.1 * algebraMap k R c := Algebra.commutes c x.1
    _ = x.1 * (algebraMap k R c * e) := by
      rw [(Algebra.commutes c e), ← mul_assoc, hxe]

/-- The natural `k`-algebra structure on an idempotent corner of a
`k`-algebra. This is a definition rather than a global instance, so it
does not create typeclass diamonds. -/
abbrev IsIdempotentElem.cornerAlgebra {e : R} (he : IsIdempotentElem e) :
    Algebra k he.Corner :=
  (IsIdempotentElem.cornerAlgebraMap he).toAlgebra'
    (IsIdempotentElem.cornerAlgebraMap_commutes he)

/-- An algebra equivalence restricts to an algebra equivalence between
corresponding idempotent corners. -/
noncomputable def IsIdempotentElem.cornerAlgEquiv (f : R ≃ₐ[k] S)
    {e : R} (he : IsIdempotentElem e) :
    let _ : Algebra k he.Corner := IsIdempotentElem.cornerAlgebra he
    let hf : IsIdempotentElem (f e) := he.map f.toRingHom
    let _ : Algebra k hf.Corner := IsIdempotentElem.cornerAlgebra hf
    he.Corner ≃ₐ[k] hf.Corner := by
  letI : Algebra k he.Corner := IsIdempotentElem.cornerAlgebra he
  let hf : IsIdempotentElem (f e) := he.map f.toRingHom
  letI : Algebra k hf.Corner := IsIdempotentElem.cornerAlgebra hf
  let cornerHom : he.Corner →ₐ[k] hf.Corner := {
    toRingHom := IsIdempotentElem.cornerRingHom f.toRingHom he
    commutes' := fun c ↦ by
      apply Subtype.ext
      change f (algebraMap k R c * e) = algebraMap k S c * f e
      rw [map_mul, f.commutes] }
  apply AlgEquiv.ofBijective cornerHom
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply f.injective
    exact congrArg Subtype.val hxy
  · intro y
    obtain ⟨s, hs⟩ := y.2
    let x : he.Corner := ⟨f.symm y.1, by
      refine ⟨f.symm s, ?_⟩
      rw [← hs]
      simp⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change f (f.symm y.1) = y.1
    simp

end CornerAlgebra

section MatrixBlocks

variable {n : ℕ} (d : Fin n → ℕ) [∀ i, NeZero (d i)]

abbrev MatrixBlocks := ∀ i, Matrix (Fin (d i)) (Fin (d i)) k

/-- One selected diagonal matrix unit in each simple matrix block. -/
def selectedMatrixUnit (i : Fin n) : MatrixBlocks (k := k) d :=
  Pi.single i (Matrix.single default default 1)

/-- The sum of one selected diagonal matrix unit in every block. -/
def selectedMatrixIdempotent : MatrixBlocks (k := k) d :=
  ∑ i, selectedMatrixUnit (k := k) d i

@[simp]
theorem selectedMatrixIdempotent_apply (i : Fin n) :
    selectedMatrixIdempotent (k := k) d i =
      Matrix.single default default 1 := by
  simp [selectedMatrixIdempotent, selectedMatrixUnit]

/-- The selected rank-one matrix units form an orthogonal family. -/
theorem selectedMatrixUnits_orthogonal :
    OrthogonalIdempotents (selectedMatrixUnit (k := k) d) := by
  rw [OrthogonalIdempotents.iff_mul_eq]
  intro i j
  by_cases hij : i = j
  · subst j
    simp [selectedMatrixUnit, ← Pi.single_mul]
  · rw [if_neg hij]
    ext q a b
    by_cases hiq : i = q
    · subst q
      simp [selectedMatrixUnit, hij]
    · simp [selectedMatrixUnit, hiq]

/-- The sum of the selected matrix units is an idempotent. -/
theorem selectedMatrixIdempotent_isIdempotentElem :
    IsIdempotentElem (selectedMatrixIdempotent (k := k) d) :=
  (selectedMatrixUnits_orthogonal (k := k) d).isIdempotentElem_sum

local instance instAlgebraSelectedMatrixCorner :
    Algebra k (selectedMatrixIdempotent_isIdempotentElem (k := k) d).Corner :=
  IsIdempotentElem.cornerAlgebra
    (selectedMatrixIdempotent_isIdempotentElem (k := k) d)

/-- The corner cut out by the selected rank-one idempotents is the
product of one copy of the ground field for every matrix block. -/
noncomputable def selectedMatrixCornerAlgEquiv :
    (selectedMatrixIdempotent_isIdempotentElem (k := k) d).Corner ≃ₐ[k]
      (Fin n → k) := by
  let he := selectedMatrixIdempotent_isIdempotentElem (k := k) d
  let diagonal : (Fin n → k) →+* he.Corner := {
    toFun := fun c ↦ ⟨fun i ↦ Matrix.single default default (c i), by
      refine ⟨fun i ↦ Matrix.single default default (c i), ?_⟩
      funext i
      simp only [Pi.mul_apply, selectedMatrixIdempotent_apply]
      rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same]
      simp⟩
    map_one' := by
      apply Subtype.ext
      change (fun i ↦ Matrix.single default default (1 : k)) =
        selectedMatrixIdempotent (k := k) d
      funext i
      simp
    map_mul' := fun c c' ↦ by
      apply Subtype.ext
      change (fun i ↦ Matrix.single default default (c i * c' i)) =
        (fun i ↦ Matrix.single default default (c i)) *
          (fun i ↦ Matrix.single default default (c' i))
      funext i
      simp only [Pi.mul_apply]
      rw [Matrix.single_mul_single_same]
    map_zero' := by
      apply Subtype.ext
      change (fun i ↦ Matrix.single default default (0 : k)) = 0
      funext i
      simp
    map_add' := fun c c' ↦ by
      apply Subtype.ext
      change (fun i ↦ Matrix.single default default (c i + c' i)) =
        (fun i ↦ Matrix.single default default (c i)) +
          (fun i ↦ Matrix.single default default (c' i))
      funext i
      exact Matrix.single_add default default (c i) (c' i) }
  have hdiagonal : Function.Bijective diagonal := by
    constructor
    · intro c c' hcc'
      funext i
      have hi := congrFun (congrArg Subtype.val hcc') i
      exact congr_fun₂ hi default default
    · intro x
      obtain ⟨r, hr⟩ := x.2
      refine ⟨fun i ↦ r i default default, ?_⟩
      apply Subtype.ext
      change (fun i ↦ Matrix.single default default (r i default default)) = x.1
      rw [← hr]
      funext i
      simp only [Pi.mul_apply, selectedMatrixIdempotent_apply]
      rw [Matrix.single_mul_mul_single]
      simp
  let diagonalAlgHom : (Fin n → k) →ₐ[k] he.Corner := {
    toRingHom := diagonal
    commutes' := fun c ↦ by
      apply Subtype.ext
      change
        (fun i ↦ Matrix.single default default c) =
          algebraMap k (MatrixBlocks (k := k) d) c *
            selectedMatrixIdempotent (k := k) d
      funext i
      simp only [Pi.algebraMap_def, Pi.mul_apply,
        selectedMatrixIdempotent_apply]
      rw [Matrix.algebraMap_eq_diagonal]
      ext a b
      rw [Matrix.diagonal_mul]
      simp [Matrix.single_apply] }
  exact (AlgEquiv.ofBijective diagonalAlgHom hdiagonal).symm

/-- A selected matrix unit as an element of the selected corner. -/
def selectedMatrixUnitCorner (i : Fin n) :
    (selectedMatrixIdempotent_isIdempotentElem (k := k) d).Corner :=
  ⟨selectedMatrixUnit (k := k) d i, by
    refine ⟨selectedMatrixUnit (k := k) d i, ?_⟩
    funext q
    simp only [Pi.mul_apply, selectedMatrixIdempotent_apply]
    by_cases hiq : i = q
    · subst q
      simp only [selectedMatrixUnit, Pi.single_eq_same]
      rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same]
      simp
    · simp [selectedMatrixUnit, hiq]⟩

@[simp]
theorem selectedMatrixCornerAlgEquiv_selectedMatrixUnitCorner (i : Fin n) :
    selectedMatrixCornerAlgEquiv (k := k) d
        (selectedMatrixUnitCorner (k := k) d i) =
      Pi.single i 1 := by
  apply (selectedMatrixCornerAlgEquiv (k := k) d).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  apply Subtype.ext
  ext q a b
  by_cases hiq : i = q
  · subst q
    simp [selectedMatrixCornerAlgEquiv, selectedMatrixUnitCorner,
      selectedMatrixUnit]
  · simp [selectedMatrixCornerAlgEquiv, selectedMatrixUnitCorner,
      selectedMatrixUnit, hiq]

/-- The selected matrix idempotent is full in the product of matrix
algebras. -/
theorem span_selectedMatrixIdempotent_eq_top :
    TwoSidedIdeal.span ({selectedMatrixIdempotent (k := k) d} :
      Set (MatrixBlocks (k := k) d)) = ⊤ := by
  rw [← TwoSidedIdeal.one_mem_iff]
  let I : TwoSidedIdeal (MatrixBlocks (k := k) d) :=
    TwoSidedIdeal.span {selectedMatrixIdempotent (k := k) d}
  let left (q : Σ i, Fin (d i)) : MatrixBlocks (k := k) d :=
    Pi.single q.1 (Matrix.single q.2 default 1)
  let right (q : Σ i, Fin (d i)) : MatrixBlocks (k := k) d :=
    Pi.single q.1 (Matrix.single default q.2 1)
  have hterm (q : Σ i, Fin (d i)) :
      left q * selectedMatrixIdempotent (k := k) d * right q ∈ I := by
    exact I.mul_mem_right _ _ <| I.mul_mem_left _ _ <|
      TwoSidedIdeal.subset_span (Set.mem_singleton _)
  have hproduct (q : Σ i, Fin (d i)) :
      left q * selectedMatrixIdempotent (k := k) d * right q =
        Pi.single q.1 (Matrix.single q.2 q.2 1) := by
    ext i a b
    by_cases hqi : q.1 = i
    · subst i
      simp [left, right, selectedMatrixIdempotent, selectedMatrixUnit]
    · simp [left, right, selectedMatrixIdempotent, selectedMatrixUnit,
        hqi]
  have hsum :
      ∑ q : Σ i, Fin (d i),
          left q * selectedMatrixIdempotent (k := k) d * right q = 1 := by
    simp_rw [hproduct]
    rw [Fintype.sum_sigma]
    funext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simpa using (Matrix.sum_single_one (m := Fin (d i)) (α := k))
    · intro j hj hji
      simp [hji]
    · simp
  rw [← hsum]
  exact I.finsetSum_mem Finset.univ _ fun q _ ↦ hterm q

end MatrixBlocks

section BasicReduction

variable (k : Type u) [Field k] [IsAlgClosed k]
variable (A : Type v) [Ring A] [Algebra k A]

/-- Wedderburn--Artin data lifted from the semisimple quotient: one
orthogonal idempotent above a rank-one diagonal matrix unit in each
simple block. Their sum is full. -/
structure BasicIdempotentData where
  n : ℕ
  d : Fin n → ℕ
  nonzero : ∀ i, NeZero (d i)
  quotientEquiv :
    (A ⧸ Ring.jacobson A) ≃ₐ[k] MatrixBlocks (k := k) d
  idempotent : Fin n → A
  orthogonal : OrthogonalIdempotents idempotent
  quotientEquiv_mk_idempotent : ∀ i,
    quotientEquiv (Ideal.Quotient.mk (Ring.jacobson A) (idempotent i)) =
      @selectedMatrixUnit k _ n d nonzero i
  full : IsFull (∑ i, idempotent i)

namespace BasicIdempotentData

/-- The full idempotent obtained by summing the lifted family. -/
def sumIdempotent (D : BasicIdempotentData k A) : A :=
  ∑ i, D.idempotent i

omit [IsAlgClosed k] in
theorem sumIdempotent_isIdempotentElem (D : BasicIdempotentData k A) :
    IsIdempotentElem D.sumIdempotent :=
  D.orthogonal.isIdempotentElem_sum

/-- The full corner selected by the lifted rank-one idempotents. -/
abbrev Corner (D : BasicIdempotentData k A) :=
  D.sumIdempotent_isIdempotentElem.Corner

instance instAlgebraCorner (D : BasicIdempotentData k A) :
    Algebra k D.Corner :=
  IsIdempotentElem.cornerAlgebra D.sumIdempotent_isIdempotentElem

/-- The corresponding rank-one corner in the Wedderburn--Artin matrix
product. -/
abbrev MatrixCorner (D : BasicIdempotentData k A) :=
  (@selectedMatrixIdempotent_isIdempotentElem k _ D.n D.d D.nonzero).Corner

instance instAlgebraMatrixCorner (D : BasicIdempotentData k A) :
    Algebra k D.MatrixCorner :=
  IsIdempotentElem.cornerAlgebra
    (@selectedMatrixIdempotent_isIdempotentElem k _ D.n D.d D.nonzero)

/-- The quotient map followed by the Wedderburn--Artin equivalence. -/
def quotientToMatrixBlocks (D : BasicIdempotentData k A) :
    A →ₐ[k] MatrixBlocks (k := k) D.d :=
  D.quotientEquiv.toAlgHom.comp
    (Ideal.Quotient.mkₐ k (Ring.jacobson A))

omit [IsAlgClosed k] in
theorem quotientToMatrixBlocks_idempotent (D : BasicIdempotentData k A)
    (i : Fin D.n) :
    quotientToMatrixBlocks k A D (D.idempotent i) =
      @selectedMatrixUnit k _ D.n D.d D.nonzero i := by
  exact D.quotientEquiv_mk_idempotent i

omit [IsAlgClosed k] in
theorem quotientToMatrixBlocks_sumIdempotent
    (D : BasicIdempotentData k A) :
    quotientToMatrixBlocks k A D D.sumIdempotent =
      @selectedMatrixIdempotent k _ D.n D.d D.nonzero := by
  rw [sumIdempotent, map_sum, selectedMatrixIdempotent]
  exact Finset.sum_congr rfl fun i _ ↦
    quotientToMatrixBlocks_idempotent k A D i

/-- The quotient-to-Wedderburn map restricted to the full corner. -/
def cornerToMatrixCorner (D : BasicIdempotentData k A) :
    D.Corner →ₐ[k] D.MatrixCorner where
  toFun x := ⟨quotientToMatrixBlocks k A D x.1, by
    obtain ⟨r, hr⟩ := x.2
    refine ⟨quotientToMatrixBlocks k A D r, ?_⟩
    calc
      @selectedMatrixIdempotent k _ D.n D.d D.nonzero *
            quotientToMatrixBlocks k A D r *
            @selectedMatrixIdempotent k _ D.n D.d D.nonzero =
          quotientToMatrixBlocks k A D D.sumIdempotent *
            quotientToMatrixBlocks k A D r *
            quotientToMatrixBlocks k A D D.sumIdempotent := by
              rw [quotientToMatrixBlocks_sumIdempotent k A D]
      _ = quotientToMatrixBlocks k A D
          (D.sumIdempotent * r * D.sumIdempotent) := by rw [map_mul, map_mul]
      _ = quotientToMatrixBlocks k A D x.1 :=
        congrArg (quotientToMatrixBlocks k A D) hr⟩
  map_one' := by
    apply Subtype.ext
    exact quotientToMatrixBlocks_sumIdempotent k A D
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (quotientToMatrixBlocks k A D) x.1 y.1
  map_zero' := by
    apply Subtype.ext
    exact map_zero (quotientToMatrixBlocks k A D)
  map_add' x y := by
    apply Subtype.ext
    exact map_add (quotientToMatrixBlocks k A D) x.1 y.1
  commutes' c := by
    apply Subtype.ext
    change quotientToMatrixBlocks k A D
        (algebraMap k A c * D.sumIdempotent) =
      algebraMap k (MatrixBlocks (k := k) D.d) c *
        @selectedMatrixIdempotent k _ D.n D.d D.nonzero
    rw [map_mul, (quotientToMatrixBlocks k A D).commutes,
      quotientToMatrixBlocks_sumIdempotent k A D]

omit [IsAlgClosed k] in
theorem cornerToMatrixCorner_surjective (D : BasicIdempotentData k A) :
    Function.Surjective (cornerToMatrixCorner k A D) := by
  intro y
  obtain ⟨s, hs⟩ := y.2
  obtain ⟨r, hr⟩ : ∃ r : A, quotientToMatrixBlocks k A D r = s := by
    obtain ⟨q, rfl⟩ := D.quotientEquiv.surjective s
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨r, rfl⟩
  let x : D.Corner := ⟨D.sumIdempotent * r * D.sumIdempotent,
    ⟨r, rfl⟩⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  change quotientToMatrixBlocks k A D
      (D.sumIdempotent * r * D.sumIdempotent) = y.1
  rw [map_mul, map_mul, quotientToMatrixBlocks_sumIdempotent k A D, hr]
  exact hs

omit [IsAlgClosed k] in
theorem cornerToMatrixCorner_ker_isNilpotent [FiniteDimensional k A]
    (D : BasicIdempotentData k A) :
    ∀ x ∈ RingHom.ker (cornerToMatrixCorner k A D).toRingHom,
      IsNilpotent x := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  intro x hx
  rw [RingHom.mem_ker] at hx
  have hg : quotientToMatrixBlocks k A D x.1 = 0 := by
    have := congrArg Subtype.val hx
    exact this
  have hq : Ideal.Quotient.mk (Ring.jacobson A) x.1 = 0 := by
    apply D.quotientEquiv.injective
    simpa [quotientToMatrixBlocks] using hg
  have hxJ : x.1 ∈ Ring.jacobson A :=
    Ideal.Quotient.eq_zero_iff_mem.mp hq
  obtain ⟨m, hm⟩ := IsSemiprimaryRing.isNilpotent (R := A)
  refine ⟨Nat.succ m, ?_⟩
  have hpow (n : ℕ) :
      (x ^ Nat.succ n).1 = x.1 ^ Nat.succ n := by
    induction n with
    | zero => simp only [pow_one]
    | succ n ih =>
        calc
          (x ^ Nat.succ (Nat.succ n)).1 =
              ((x ^ Nat.succ n) * x).1 := by
            rw [show Nat.succ (Nat.succ n) = Nat.succ n + 1 by omega,
              pow_succ]
          _ = (x ^ Nat.succ n).1 * x.1 := rfl
          _ = x.1 ^ Nat.succ n * x.1 := by rw [ih]
          _ = x.1 ^ Nat.succ (Nat.succ n) := by
            exact (pow_succ x.1 (Nat.succ n)).symm
  apply Subtype.ext
  rw [hpow]
  change x.1 ^ Nat.succ m = 0
  have hxpow : x.1 ^ Nat.succ m ∈ (Ring.jacobson A) ^ Nat.succ m :=
    Ideal.pow_mem_pow hxJ (Nat.succ m)
  rw [show Nat.succ m = m + 1 by omega,
    Ideal.IsTwoSided.pow_succ, hm, mul_zero] at hxpow
  simpa using hxpow

omit [IsAlgClosed k] in
theorem cornerToMatrixCorner_ker_eq_jacobson [FiniteDimensional k A]
    (D : BasicIdempotentData k A) :
    RingHom.ker (cornerToMatrixCorner k A D).toRingHom =
      Ring.jacobson D.Corner := by
  letI : ∀ i, NeZero (D.d i) := D.nonzero
  letI : IsSemisimpleRing D.MatrixCorner :=
    (selectedMatrixCornerAlgEquiv (k := k) D.d).symm.toRingEquiv.isSemisimpleRing
  exact RingHom.ker_eq_jacobson_of_surjective_of_isNilpotent
    (cornerToMatrixCorner k A D).toRingHom
    (cornerToMatrixCorner_surjective k A D)
    (cornerToMatrixCorner_ker_isNilpotent k A D)

/-- The semisimple quotient of the full corner is its selected
Wedderburn--Artin corner. -/
noncomputable def cornerQuotientEquivMatrixCorner [FiniteDimensional k A]
    (D : BasicIdempotentData k A) :
    (D.Corner ⧸ Ring.jacobson D.Corner) ≃ₐ[k] D.MatrixCorner := by
  let f := cornerToMatrixCorner k A D
  let lift : (D.Corner ⧸ Ring.jacobson D.Corner) →ₐ[k] D.MatrixCorner :=
    Ideal.Quotient.liftₐ (Ring.jacobson D.Corner) f (by
      intro a ha
      have hker : a ∈ RingHom.ker f.toRingHom := by
        rw [cornerToMatrixCorner_ker_eq_jacobson k A D]
        exact ha
      rwa [RingHom.mem_ker] at hker)
  apply AlgEquiv.ofBijective lift
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    have hfxy : f (x - y) = 0 := by
      change f x = f y at hxy
      rw [map_sub, hxy, sub_self]
    have hker : x - y ∈ RingHom.ker f.toRingHom := by
      rw [RingHom.mem_ker]
      exact hfxy
    rw [cornerToMatrixCorner_ker_eq_jacobson k A D] at hker
    exact hker
  · intro y
    obtain ⟨x, rfl⟩ := cornerToMatrixCorner_surjective k A D y
    exact ⟨Ideal.Quotient.mk (Ring.jacobson D.Corner) x, rfl⟩

/-- The semisimple quotient of the full corner is split basic. -/
noncomputable def cornerQuotientEquivPi [FiniteDimensional k A]
    (D : BasicIdempotentData k A) :
    (D.Corner ⧸ Ring.jacobson D.Corner) ≃ₐ[k] (Fin D.n → k) := by
  letI : ∀ i, NeZero (D.d i) := D.nonzero
  exact (cornerQuotientEquivMatrixCorner k A D).trans
    (selectedMatrixCornerAlgEquiv (k := k) D.d)

/-- The lifted block idempotents, regarded as elements of the full
corner. -/
def cornerIdempotent (D : BasicIdempotentData k A) (i : Fin D.n) :
    D.Corner := ⟨D.idempotent i, by
  refine ⟨D.idempotent i, ?_⟩
  simp [sumIdempotent, Finset.sum_mul, Finset.mul_sum,
    D.orthogonal.mul_eq]⟩

omit [IsAlgClosed k] in
theorem cornerIdempotents_complete (D : BasicIdempotentData k A) :
    CompleteOrthogonalIdempotents D.cornerIdempotent where
  idem i := by
    apply Subtype.ext
    exact D.orthogonal.idem i
  ortho i j hij := by
    apply Subtype.ext
    exact D.orthogonal.ortho hij
  complete := by
    apply Subtype.ext
    let valHom : D.Corner →+ A := {
      toFun := Subtype.val
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
    change valHom (∑ i, cornerIdempotent k A D i) = valHom 1
    rw [map_sum]
    change (∑ i, D.idempotent i) = D.sumIdempotent
    rfl

omit [IsAlgClosed k] in
@[simp]
theorem cornerToMatrixCorner_cornerIdempotent
    (D : BasicIdempotentData k A) (i : Fin D.n) :
    cornerToMatrixCorner k A D (cornerIdempotent k A D i) =
      @selectedMatrixUnitCorner k _ D.n D.d D.nonzero i := by
  apply Subtype.ext
  exact quotientToMatrixBlocks_idempotent k A D i

omit [IsAlgClosed k] in
@[simp]
theorem cornerQuotientEquivPi_mk_cornerIdempotent
    [FiniteDimensional k A] (D : BasicIdempotentData k A) (i : Fin D.n) :
    cornerQuotientEquivPi k A D
        (Ideal.Quotient.mk (Ring.jacobson D.Corner)
          (cornerIdempotent k A D i)) =
      Pi.single i 1 := by
  letI : ∀ j, NeZero (D.d j) := D.nonzero
  have hmatrix :
      cornerQuotientEquivMatrixCorner k A D
          (Ideal.Quotient.mk (Ring.jacobson D.Corner)
            (cornerIdempotent k A D i)) =
        cornerToMatrixCorner k A D (cornerIdempotent k A D i) := by
    dsimp [cornerQuotientEquivMatrixCorner]
  change selectedMatrixCornerAlgEquiv (k := k) D.d
      (cornerQuotientEquivMatrixCorner k A D
        (Ideal.Quotient.mk (Ring.jacobson D.Corner)
          (cornerIdempotent k A D i))) = Pi.single i 1
  rw [hmatrix, cornerToMatrixCorner_cornerIdempotent,
    selectedMatrixCornerAlgEquiv_selectedMatrixUnitCorner]

/-- The lifted family supplies a chosen split-basic presentation of the
full corner. -/
noncomputable def splitBasicIdempotents [FiniteDimensional k A]
    (D : BasicIdempotentData k A) :
    SplitBasicIdempotents (k := k) (A := D.Corner) (ι := Fin D.n) where
  idempotent := cornerIdempotent k A D
  complete := cornerIdempotents_complete k A D
  quotientEquiv := cornerQuotientEquivPi k A D
  quotientEquiv_mk_idempotent i j := by
    rw [cornerQuotientEquivPi_mk_cornerIdempotent]
    simp [Pi.single_apply, eq_comm]

end BasicIdempotentData

/-- A finite-dimensional algebra over an algebraically closed field has
a full orthogonal family lifting one rank-one diagonal idempotent from
each Wedderburn--Artin block. -/
theorem exists_basicIdempotentData [FiniteDimensional k A] :
    Nonempty (BasicIdempotentData k A) := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  let J : Ideal A := Ring.jacobson A
  let q : A →+* A ⧸ J := Ideal.Quotient.mk J
  obtain ⟨n, d, hd, ⟨equiv⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k (A ⧸ J)
  letI : ∀ i, NeZero (d i) := hd
  let p : Fin n → A ⧸ J :=
    fun i ↦ equiv.symm (selectedMatrixUnit (k := k) d i)
  have hp : OrthogonalIdempotents p := by
    exact (selectedMatrixUnits_orthogonal (k := k) d).map equiv.symm.toRingHom
  have hker : ∀ x ∈ RingHom.ker q, IsNilpotent x := by
    intro x hx
    obtain ⟨m, hm⟩ := IsSemiprimaryRing.isNilpotent (R := A)
    refine ⟨m, ?_⟩
    have hxJ : x ∈ J := by
      simpa [q, RingHom.mem_ker] using hx
    have hxpow : x ^ m ∈ J ^ m := Ideal.pow_mem_pow hxJ m
    rw [hm] at hxpow
    simpa using hxpow
  obtain ⟨e, he, heq⟩ :=
    hp.lift_of_isNilpotent_ker q hker (fun i ↦ Ideal.Quotient.mk_surjective (p i))
  have hqsum : q (∑ i, e i) = ∑ i, p i := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ congr_fun heq i
  have hpsum : IsFull (∑ i, p i) := by
    have hequivker : ∀ x ∈ RingHom.ker equiv.toRingHom, IsNilpotent x := by
      intro x hx
      rw [RingHom.mem_ker] at hx
      have hx0 : x = 0 := equiv.injective (by simpa using hx)
      exact hx0 ▸ IsNilpotent.zero
    apply IsFull.of_surjective_of_ker_isNilpotent equiv.toRingHom equiv.surjective
      hequivker
    simpa [IsFull, p, ← map_sum, selectedMatrixIdempotent] using
      (span_selectedMatrixIdempotent_eq_top (k := k) d)
  have hesum : IsFull (∑ i, e i) := by
    apply IsFull.of_surjective_of_ker_isNilpotent q Ideal.Quotient.mk_surjective hker
    simpa [hqsum] using hpsum
  refine ⟨{
    n := n
    d := d
    nonzero := hd
    quotientEquiv := ?_
    idempotent := e
    orthogonal := he
    quotientEquiv_mk_idempotent := ?_
    full := hesum }⟩
  · simpa [J] using equiv
  · intro i
    have hi := congr_fun heq i
    simpa [q, p, J] using congrArg equiv hi

end BasicReduction

end LargeIndecomposable
