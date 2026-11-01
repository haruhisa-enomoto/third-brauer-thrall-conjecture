module

public import LargeIndecomposable.RepresentationType.Basic.RepresentationFiniteCorners
public import LargeIndecomposable.Modules.SplitBasic.SplitBasicQuotient
public import Mathlib.RingTheory.Jacobson.Artinian

@[expose] public section

/-!
# Selected split-basic idempotent corners

A finite injective subfamily of the chosen primitive idempotents of a
split-basic algebra sums to an idempotent. Its corner inherits a chosen
split-basic presentation, and its primitive-projective category identifies
fully faithfully with the corresponding full subcategory of the ambient
primitive-projective category.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped BigOperators

namespace LargeIndecomposable.SplitBasicIdempotents

universe u v x y

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]
variable {κ : Type y} [Fintype κ] [DecidableEq κ]

/-- A canonical injective enumeration of every chosen primitive idempotent. -/
def fullPrimitiveEmbedding : Fin (Fintype.card ι) ↪ ι :=
  (Fintype.equivFin ι).symm.toEmbedding

/-- The canonical duplicate-free enumeration of a finite set of primitive
vertex indices. -/
def finsetPrimitiveEmbedding (t : Finset ι) : Fin (Fintype.card ↑t) ↪ ι :=
  (Fintype.equivFin ↑t).symm.toEmbedding.trans
    (Function.Embedding.subtype (fun a : ι ↦ a ∈ t))

/-- The coordinate of a member in the canonical enumeration of a finite set
of primitive vertex indices. -/
def finsetPrimitiveIndex (t : Finset ι) (a : ι) (ha : a ∈ t) :
    Fin (Fintype.card ↑t) :=
  Fintype.equivFin ↑t ⟨a, ha⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem finsetPrimitiveEmbedding_index (t : Finset ι) (a : ι)
    (ha : a ∈ t) :
    finsetPrimitiveEmbedding t (finsetPrimitiveIndex t a ha) = a := by
  simp [finsetPrimitiveEmbedding, finsetPrimitiveIndex]

omit [DecidableEq ι] in
/-- The canonical full primitive enumeration is surjective. -/
theorem fullPrimitiveEmbedding_surjective :
    Function.Surjective (fullPrimitiveEmbedding (ι := ι)) :=
  (Fintype.equivFin ι).symm.surjective

/-- The sum of a selected injective family of primitive idempotents. -/
def selectedIdempotent
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    (r : κ ↪ ι) : A :=
  ∑ j : κ, S.idempotent (r j)

omit [DecidableEq κ] in
theorem selectedIdempotent_isIdempotentElem
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    (r : κ ↪ ι) :
    IsIdempotentElem (S.selectedIdempotent r) := by
  let horth : OrthogonalIdempotents (fun j : κ ↦ S.idempotent (r j)) :=
    S.complete.toOrthogonalIdempotents.embedding r
  simpa only [selectedIdempotent, Finset.sum_filter,
    Finset.filter_true_of_mem] using
    (horth.isIdempotentElem_sum (s := Finset.univ))

/-- The algebra cut out by the sum of a selected injective family of chosen
primitive idempotents. -/
abbrev SelectedCorner
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    (r : κ ↪ ι) :=
  (S.selectedIdempotent_isIdempotentElem r).Corner

namespace SelectedCorner

variable
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    (r : κ ↪ ι)

local notation "e" => S.selectedIdempotent r
local notation "he" => S.selectedIdempotent_isIdempotentElem r
local notation "B" => SelectedCorner S r
noncomputable instance selectedCornerAlgebra : Algebra k B :=
  IsIdempotentElem.cornerAlgebra (S.selectedIdempotent_isIdempotentElem r)

/-- The multiplicative inclusion of a selected corner into the ambient
algebra.  It is nonunital unless every primitive vertex was selected. -/
def valNonUnitalRingHom : B →ₙ+* A where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

omit [DecidableEq κ] in
@[simp]
theorem valNonUnitalRingHom_apply (z : B) :
    valNonUnitalRingHom S r z = z.1 :=
  rfl

omit [DecidableEq κ] in
/-- A selected idempotent corner of a finite-dimensional algebra is
finite-dimensional. -/
noncomputable instance selectedCornerModuleFinite [Module.Finite k A] :
    Module.Finite k B := by
  let valLinear : B →ₗ[k] A :=
    { toFun := Subtype.val
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro c z
        obtain ⟨hzleft, _hzright⟩ := (Subsemigroup.mem_corner_iff he).mp z.2
        change (algebraMap k A c * e) * z.1 = c • z.1
        rw [Algebra.smul_def, mul_assoc, hzleft] }
  exact Module.Finite.of_injective valLinear Subtype.val_injective

omit [DecidableEq κ] in
theorem selectedIdempotent_mul_idempotent (j : κ) :
    e * S.idempotent (r j) = S.idempotent (r j) := by
  classical
  let horth : OrthogonalIdempotents (fun q : κ ↦ S.idempotent (r q)) :=
    S.complete.toOrthogonalIdempotents.embedding r
  rw [selectedIdempotent, Finset.sum_mul]
  simp [horth.mul_eq]

omit [DecidableEq κ] in
theorem idempotent_mul_selectedIdempotent (j : κ) :
    S.idempotent (r j) * e = S.idempotent (r j) := by
  classical
  let horth : OrthogonalIdempotents (fun q : κ ↦ S.idempotent (r q)) :=
    S.complete.toOrthogonalIdempotents.embedding r
  rw [selectedIdempotent]
  exact horth.mul_sum_of_mem (Finset.mem_univ j)

/-- The selected primitive idempotents, regarded inside the selected corner. -/
def primitive (j : κ) : B := by
  refine ⟨S.idempotent (r j), ?_⟩
  apply (Subsemigroup.mem_corner_iff he).2
  exact ⟨selectedIdempotent_mul_idempotent S r j,
    idempotent_mul_selectedIdempotent S r j⟩

omit [DecidableEq κ] in
@[simp]
theorem primitive_val (j : κ) : (primitive S r j).1 = S.idempotent (r j) :=
  rfl

omit [DecidableEq κ] in
private theorem val_pow_succ (z : B) (n : ℕ) :
    (z ^ (Nat.succ n) : B).1 = z.1 ^ (Nat.succ n) := by
  induction n with
  | zero => simp only [pow_one]
  | succ n ih =>
      calc
        (z ^ (Nat.succ (Nat.succ n)) : B).1 =
            (z ^ (Nat.succ n) * z : B).1 := by
          exact congrArg Subtype.val (pow_succ z (Nat.succ n))
        _ = (z ^ (Nat.succ n) : B).1 * z.1 := rfl
        _ = z.1 ^ (Nat.succ n) * z.1 := by rw [ih]
        _ = z.1 ^ (Nat.succ (Nat.succ n)) := by
          exact (pow_succ z.1 (Nat.succ n)).symm

omit [DecidableEq κ] in
/-- The selected primitive idempotents are complete and orthogonal in the
selected corner. -/
theorem primitive_complete :
    CompleteOrthogonalIdempotents (primitive S r) := by
  classical
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro j
      apply Subtype.ext
      exact S.complete.toOrthogonalIdempotents.idem (r j) |>.eq
    · intro i j hij
      apply Subtype.ext
      exact S.complete.toOrthogonalIdempotents.ortho
        (fun h ↦ hij (r.injective h))
  · apply Subtype.ext
    let valHom : B →+ A :=
      { toFun := Subtype.val
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    change valHom (∑ j : κ, primitive S r j) = valHom 1
    rw [map_sum]
    change (∑ j : κ, S.idempotent (r j)) = e
    rfl

omit [DecidableEq κ] in
private theorem quotientEquiv_selectedIdempotent_apply (j : κ) :
    S.quotientEquiv
      (Ideal.Quotient.mk (Ring.jacobson A) e) (r j) = 1 := by
  classical
  simp only [selectedIdempotent, map_sum, Finset.sum_apply,
    S.quotientEquiv_mk_idempotent]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _hi hij
    have hrij : r i ≠ r j := fun h ↦ hij (r.injective h)
    simp [hrij]
  · simp

/-- The ambient split residue restricted to the selected corner and selected
coordinates. -/
def residue : B →ₐ[k] (κ → k) where
  toFun z j :=
    S.quotientEquiv
      (Ideal.Quotient.mk (Ring.jacobson A) z.1) (r j)
  map_one' := by
    funext j
    change S.quotientEquiv
      (Ideal.Quotient.mk (Ring.jacobson A) e) (r j) = 1
    exact quotientEquiv_selectedIdempotent_apply S r j
  map_mul' z w := by
    funext j
    exact congrFun (map_mul S.quotientEquiv
      (Ideal.Quotient.mk (Ring.jacobson A) z.1)
      (Ideal.Quotient.mk (Ring.jacobson A) w.1)) (r j)
  map_zero' := by
    funext j
    exact congrFun (map_zero S.quotientEquiv) (r j)
  map_add' z w := by
    funext j
    exact congrFun (map_add S.quotientEquiv
      (Ideal.Quotient.mk (Ring.jacobson A) z.1)
      (Ideal.Quotient.mk (Ring.jacobson A) w.1)) (r j)
  commutes' c := by
    funext j
    change S.quotientEquiv
      (Ideal.Quotient.mk (Ring.jacobson A)
        ((algebraMap k B c).1)) (r j) = algebraMap k (κ → k) c j
    change S.quotientEquiv
      (Ideal.Quotient.mk (Ring.jacobson A)
        ((algebraMap k A c) * e)) (r j) = c
    simp [map_mul, quotientEquiv_selectedIdempotent_apply S r j]

@[simp]
theorem residue_primitive (i j : κ) :
    residue S r (primitive S r i) j = if i = j then 1 else 0 := by
  classical
  change S.quotientEquiv
    (Ideal.Quotient.mk (Ring.jacobson A) (S.idempotent (r i))) (r j) = _
  rw [S.quotientEquiv_mk_idempotent]
  simp only [r.injective.eq_iff]

omit [DecidableEq κ] in
theorem residue_surjective : Function.Surjective (residue S r) := by
  classical
  intro y
  let y' : ι → k := Function.extend r y 0
  obtain ⟨z, hz⟩ := S.quotientEquiv.surjective y'
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  let b : B := ⟨e * a * e, ⟨a, rfl⟩⟩
  refine ⟨b, ?_⟩
  funext j
  change S.quotientEquiv
    (Ideal.Quotient.mk (Ring.jacobson A) (e * a * e)) (r j) = y j
  simp [map_mul, hz, quotientEquiv_selectedIdempotent_apply S r j,
    y', r.injective.extend_apply]

omit [DecidableEq κ] in
private theorem residue_eq_zero_ambient_mem_jacobson
    [Module.Finite k A] {z : B} (hz : residue S r z = 0) :
    z.1 ∈ Ring.jacobson A := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply S.quotientEquiv.injective
  funext i
  by_cases hi : ∃ j, r j = i
  · obtain ⟨j, rfl⟩ := hi
    have hcoord := congrFun hz j
    simpa [residue] using hcoord
  · obtain ⟨hzleft, _hzright⟩ := (Subsemigroup.mem_corner_iff he).mp z.2
    have hecoord : S.quotientEquiv
        (Ideal.Quotient.mk (Ring.jacobson A) e) i = 0 := by
      simp only [selectedIdempotent, map_sum, Finset.sum_apply,
        S.quotientEquiv_mk_idempotent]
      apply Finset.sum_eq_zero
      intro j _hj
      have hrji : r j ≠ i := fun h ↦ hi ⟨j, h⟩
      simp [hrji]
    have hleft := congrArg
      (fun q : A ⧸ Ring.jacobson A ↦ S.quotientEquiv q i)
      (congrArg (Ideal.Quotient.mk (Ring.jacobson A)) hzleft)
    symm
    simpa only [map_mul, Pi.mul_apply, hecoord, zero_mul, map_zero,
      Pi.zero_apply] using hleft

omit [DecidableEq κ] in
theorem residue_ker_le_jacobson [Module.Finite k A] :
    RingHom.ker (residue S r).toRingHom ≤ Ring.jacobson B := by
  intro z hz
  rw [← Ideal.jacobson_bot]
  apply Ideal.mem_jacobson_iff.mpr
  intro w
  have hwzJ : w.1 * z.1 ∈ Ring.jacobson A :=
    (Ring.jacobson A).mul_mem_left w.1
      (residue_eq_zero_ambient_mem_jacobson S r hz)
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  have hnil : IsNilpotent (w * z) := by
    refine ⟨n + 1, ?_⟩
    apply Subtype.ext
    have hp : (w.1 * z.1) ^ n ∈ (Ring.jacobson A) ^ n :=
      Ideal.pow_mem_pow hwzJ n
    have hn' : (Ring.jacobson A) ^ n = 0 := by
      simpa only [Ideal.jacobson_bot] using hn
    rw [hn'] at hp
    have hpzero : (w.1 * z.1) ^ n = 0 :=
      (Submodule.mem_bot A).mp hp
    rw [show n + 1 = Nat.succ n by omega,
      val_pow_succ S r (w * z) n]
    change (w.1 * z.1) ^ (Nat.succ n) = 0
    rw [pow_succ, hpzero, zero_mul]
  let hu := hnil.isUnit_add_one
  refine ⟨↑hu.unit⁻¹, ?_⟩
  calc
    (↑hu.unit⁻¹ : B) * w * z + ↑hu.unit⁻¹ - 1 =
        (↑hu.unit⁻¹ : B) * (w * z) + ↑hu.unit⁻¹ * 1 - 1 := by
      rw [mul_assoc, mul_one]
    _ = (↑hu.unit⁻¹ : B) * (w * z + 1) - 1 := by
      rw [mul_add]
    _ = (↑hu.unit⁻¹ : B) * (↑hu.unit : B) - 1 := by
      rw [hu.unit_spec]
    _ = 0 := by simp

omit [DecidableEq κ] in
theorem residue_ker_eq_jacobson [Module.Finite k A] :
    RingHom.ker (residue S r).toRingHom = Ring.jacobson B := by
  have hle := residue_ker_le_jacobson S r
  letI : RingHomSurjective (residue S r).toRingHom :=
    ⟨residue_surjective S r⟩
  apply le_antisymm hle
  have hmap := Ring.map_jacobson_of_ker_le
    (f := (residue S r).toRingHom) hle
  rw [IsSemisimpleRing.jacobson_eq_bot (κ → k)] at hmap
  intro z hz
  have hzmap : (residue S r).toRingHom z ∈
      Submodule.map (residue S r).toRingHom.toSemilinearMap
        (Ring.jacobson B) :=
    ⟨z, hz, rfl⟩
  rw [hmap] at hzmap
  exact hzmap

omit [DecidableEq κ] in
/-- An element of a finite-dimensional selected idempotent corner is radical
exactly when its ambient algebra value is radical. -/
theorem mem_jacobson_iff_val_mem_jacobson [Module.Finite k A] (z : B) :
    z ∈ Ring.jacobson B ↔ z.1 ∈ Ring.jacobson A := by
  constructor
  · intro hz
    rw [← residue_ker_eq_jacobson S r] at hz
    exact residue_eq_zero_ambient_mem_jacobson S r hz
  · intro hz
    rw [← residue_ker_eq_jacobson S r]
    change residue S r z = 0
    funext j
    change S.quotientEquiv
      (Ideal.Quotient.mk (Ring.jacobson A) z.1) (r j) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz]
    simp

omit [DecidableEq κ] in
/-- The value of a selected-corner element in the corner radical square lies
in the ambient radical square. -/
theorem val_mem_jacobson_sq_of_mem_jacobson_sq
    [Module.Finite k A] (z : B)
    (hz : z ∈ Ring.jacobson B * Ring.jacobson B) :
    z.1 ∈ Ring.jacobson A * Ring.jacobson A := by
  let K : Ideal B := {
    carrier := {a | a.1 ∈ Ring.jacobson A * Ring.jacobson A}
    zero_mem' := (Ring.jacobson A * Ring.jacobson A).zero_mem
    add_mem' := fun ha hb ↦
      (Ring.jacobson A * Ring.jacobson A).add_mem ha hb
    smul_mem' := by
      intro a b hb
      change (a * b).1 ∈ Ring.jacobson A * Ring.jacobson A
      exact (Ring.jacobson A * Ring.jacobson A).mul_mem_left a.1 hb }
  apply (show Ring.jacobson B * Ring.jacobson B ≤ K by
    apply Ideal.mul_le.2
    intro a ha b hb
    change a.1 * b.1 ∈ Ring.jacobson A * Ring.jacobson A
    exact Ideal.mul_mem_mul
      ((mem_jacobson_iff_val_mem_jacobson S r a).1 ha)
      ((mem_jacobson_iff_val_mem_jacobson S r b).1 hb))
  exact hz

/-- A selected injective subfamily of the chosen primitive idempotents gives
a chosen split-basic presentation of its corner. -/
def splitBasic [Module.Finite k A] :
    LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := B) (ι := κ) := by
  classical
  let q := residue S r
  have hq := residue_surjective S r
  have hker := residue_ker_eq_jacobson S r
  let eKer : (B ⧸ RingHom.ker q.toRingHom) ≃ₐ[k] (κ → k) :=
    Ideal.quotientKerAlgEquivOfSurjective hq
  let eJac : (B ⧸ Ring.jacobson B) ≃ₐ[k]
      (B ⧸ RingHom.ker q.toRingHom) :=
    Ideal.quotientEquivAlgOfEq k hker.symm
  refine
    { idempotent := primitive S r
      complete := primitive_complete S r
      quotientEquiv := eJac.trans eKer
      quotientEquiv_mk_idempotent := ?_ }
  intro i j
  dsimp [eJac, eKer, q]
  exact residue_primitive S r i j

omit [DecidableEq κ] in
/-- Representation-finiteness descends to a corner selected by any finite
injective subfamily of the chosen primitive idempotents. -/
theorem isRepresentationFinite [Module.Finite k A]
    (hA : LargeIndecomposable.IsRepresentationFinite k A) :
    LargeIndecomposable.IsRepresentationFinite k B :=
  hA.of_idempotentCorner he

section ProjectiveFunctor

variable [Module.Finite k A]

/-- The ambient primitive projective selected by a primitive projective of the
selected corner. -/
def projectiveObj
    (X : (splitBasic S r).ProjectiveCategory) : S.ProjectiveCategory :=
  S.projectiveVertexEquiv.symm
    (r ((splitBasic S r).projectiveVertex X))

@[simp]
theorem projectiveObj_projectiveVertex
    (X : (splitBasic S r).ProjectiveCategory) :
    S.projectiveVertex (projectiveObj S r X) =
      r ((splitBasic S r).projectiveVertex X) := by
  exact S.projectiveVertexEquiv.apply_symm_apply _

/-- Forgetting the selected-corner subtype embeds its chosen primitive
projectives into the ambient chosen primitive-projective category. -/
def projectiveFunctor :
    (splitBasic S r).ProjectiveCategory ⥤ S.ProjectiveCategory where
  obj := projectiveObj S r
  map {X Y} f := by
    refine ⟨f.1.1, ?_⟩
    rw [mem_idempotentCorner_iff]
    obtain ⟨b, hb⟩ := f.2
    refine ⟨b.1, ?_⟩
    have hv := congrArg Subtype.val hb
    change S.idempotent (r ((splitBasic S r).projectiveVertex Y)) * b.1 *
        S.idempotent (r ((splitBasic S r).projectiveVertex X)) = f.1.1 at hv
    simpa using hv
  map_id X := by
    apply Subtype.ext
    change S.idempotent (r ((splitBasic S r).projectiveVertex X)) =
      S.idempotent (S.projectiveVertex (projectiveObj S r X))
    rw [projectiveObj_projectiveVertex]
  map_comp f g := by
    apply Subtype.ext
    rfl

@[simp]
theorem projectiveFunctor_obj_projectiveVertex
    (X : (splitBasic S r).ProjectiveCategory) :
    S.projectiveVertex ((projectiveFunctor S r).obj X) =
      r ((splitBasic S r).projectiveVertex X) :=
  projectiveObj_projectiveVertex S r X

@[simp]
theorem projectiveFunctor_map_val
    {X Y : (splitBasic S r).ProjectiveCategory} (f : X ⟶ Y) :
    ((projectiveFunctor S r).map f).1 = f.1.1 :=
  rfl

instance projectiveFunctor_additive : (projectiveFunctor S r).Additive where
  map_add := by
    intro X Y f g
    apply Subtype.ext
    rfl

instance projectiveFunctor_linear : (projectiveFunctor S r).Linear k where
  map_smul := by
    intro X Y f c
    apply Subtype.ext
    rw [projectiveFunctor_map_val]
    obtain ⟨hfleft, _hfright⟩ := (Subsemigroup.mem_corner_iff he).mp f.1.2
    change ((algebraMap k A c * e) * f.1.1) = c • f.1.1
    rw [Algebra.smul_def]
    rw [mul_assoc, hfleft]

/-- The selected-projective embedding is faithful. -/
instance projectiveFunctor_faithful : (projectiveFunctor S r).Faithful where
  map_injective {X Y} f g h := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun q : (projectiveFunctor S r).obj X ⟶
        (projectiveFunctor S r).obj Y ↦ q.1) h

/-- Every ambient morphism between selected primitive projectives comes from
the corresponding morphism over the selected corner. -/
instance projectiveFunctor_full : (projectiveFunctor S r).Full where
  map_surjective {X Y} g := by
    have hselY : e * S.idempotent
        (S.projectiveVertex ((projectiveFunctor S r).obj Y)) =
          S.idempotent
            (S.projectiveVertex ((projectiveFunctor S r).obj Y)) := by
      rw [projectiveFunctor_obj_projectiveVertex]
      exact selectedIdempotent_mul_idempotent S r _
    have hselX : S.idempotent
        (S.projectiveVertex ((projectiveFunctor S r).obj X)) * e =
          S.idempotent
            (S.projectiveVertex ((projectiveFunctor S r).obj X)) := by
      rw [projectiveFunctor_obj_projectiveVertex]
      exact idempotent_mul_selectedIdempotent S r _
    have hleft : e * g.1 = g.1 := by
      calc
        e * g.1 = e *
            (S.idempotent (S.projectiveVertex ((projectiveFunctor S r).obj Y)) *
              g.1) := by
                rw [ProjectiveCategory.idempotent_mul_val]
        _ = (e * S.idempotent
              (S.projectiveVertex ((projectiveFunctor S r).obj Y))) * g.1 := by
                rw [mul_assoc]
        _ = S.idempotent
              (S.projectiveVertex ((projectiveFunctor S r).obj Y)) * g.1 := by
                rw [hselY]
        _ = g.1 := ProjectiveCategory.idempotent_mul_val S g
    have hright : g.1 * e = g.1 := by
      calc
        g.1 * e =
            (g.1 * S.idempotent
              (S.projectiveVertex ((projectiveFunctor S r).obj X))) * e := by
                rw [ProjectiveCategory.val_mul_idempotent]
        _ = g.1 * (S.idempotent
              (S.projectiveVertex ((projectiveFunctor S r).obj X)) * e) := by
                rw [mul_assoc]
        _ = g.1 * S.idempotent
              (S.projectiveVertex ((projectiveFunctor S r).obj X)) := by
                rw [hselX]
        _ = g.1 := ProjectiveCategory.val_mul_idempotent S g
    let b : B := ⟨g.1, (Subsemigroup.mem_corner_iff he).2 ⟨hleft, hright⟩⟩
    let f : X ⟶ Y := by
      refine ⟨b, ?_⟩
      rw [mem_idempotentCorner_iff]
      refine ⟨b, ?_⟩
      apply Subtype.ext
      change S.idempotent
          (r ((splitBasic S r).projectiveVertex Y)) * g.1 *
            S.idempotent
              (r ((splitBasic S r).projectiveVertex X)) = g.1
      rw [← projectiveFunctor_obj_projectiveVertex S r X,
        ← projectiveFunctor_obj_projectiveVertex S r Y,
        ProjectiveCategory.idempotent_mul_val,
        ProjectiveCategory.val_mul_idempotent]
    refine ⟨f, ?_⟩
    apply Subtype.ext
    rfl

/-- If the selected family contains every primitive idempotent, the
selected-projective embedding is essentially surjective. -/
theorem projectiveFunctor_essSurj_of_surjective
    (hr : Function.Surjective r) :
    (projectiveFunctor S r).EssSurj := by
  constructor
  intro X
  obtain ⟨j, hj⟩ := hr (S.projectiveVertex X)
  let Y : (splitBasic S r).ProjectiveCategory :=
    (splitBasic S r).projectiveVertexEquiv.symm j
  have hobj : (projectiveFunctor S r).obj Y = X := by
    apply S.projectiveVertexEquiv.injective
    change S.projectiveVertex ((projectiveFunctor S r).obj Y) =
      S.projectiveVertex X
    rw [projectiveFunctor_obj_projectiveVertex]
    change r ((splitBasic S r).projectiveVertexEquiv Y) =
      S.projectiveVertex X
    rw [(splitBasic S r).projectiveVertexEquiv.apply_symm_apply]
    exact hj
  exact ⟨Y, ⟨eqToIso hobj⟩⟩

/-- A corner selected by a surjective embedding has a primitive-projective
category equivalent to the ambient primitive-projective category. -/
theorem projectiveFunctor_isEquivalence_of_surjective
    (hr : Function.Surjective r) :
    (projectiveFunctor S r).IsEquivalence := by
  letI : (projectiveFunctor S r).EssSurj :=
    projectiveFunctor_essSurj_of_surjective S r hr
  exact {}

/-- Selecting the canonical enumeration of all primitive idempotents gives
an equivalence on primitive-projective categories. -/
theorem fullProjectiveFunctor_isEquivalence :
    (projectiveFunctor S (fullPrimitiveEmbedding (ι := ι))).IsEquivalence :=
  projectiveFunctor_isEquivalence_of_surjective S
    (fullPrimitiveEmbedding (ι := ι)) fullPrimitiveEmbedding_surjective

/-- The selected-corner primitive projective corresponding to an ambient
primitive projective whose vertex lies in a specified finite set. -/
def finsetProjectiveObj (t : Finset ι) (X : S.ProjectiveCategory)
    (hX : S.projectiveVertex X ∈ t) :
    (splitBasic S (finsetPrimitiveEmbedding t)).ProjectiveCategory :=
  (splitBasic S (finsetPrimitiveEmbedding t)).projectiveVertexEquiv.symm
    (finsetPrimitiveIndex t (S.projectiveVertex X) hX)

@[simp]
theorem finsetProjectiveObj_projectiveVertex
    (t : Finset ι) (X : S.ProjectiveCategory)
    (hX : S.projectiveVertex X ∈ t) :
    (splitBasic S (finsetPrimitiveEmbedding t)).projectiveVertex
      (finsetProjectiveObj S t X hX) =
        finsetPrimitiveIndex t (S.projectiveVertex X) hX := by
  exact (splitBasic S (finsetPrimitiveEmbedding t)).projectiveVertexEquiv.apply_symm_apply _

/-- The selected-corner projective attached to an ambient projective maps
back to that ambient projective. -/
theorem projectiveFunctor_obj_finsetProjectiveObj_eq
    (t : Finset ι) (X : S.ProjectiveCategory)
    (hX : S.projectiveVertex X ∈ t) :
    (projectiveFunctor S (finsetPrimitiveEmbedding t)).obj
        (finsetProjectiveObj S t X hX) = X := by
  apply S.projectiveVertexEquiv.injective
  simp

omit [Module.Finite k A] in
@[simp]
theorem projectiveEqToHom_val
    {X Y : S.ProjectiveCategory} (h : X = Y) :
    (eqToHom h : X ⟶ Y).1 =
      S.idempotent (S.projectiveVertex X) := by
  subst Y
  rfl

/-- An ambient morphism between selected primitive projectives, with its
endpoints presented using the canonical finite-set enumeration. -/
def finsetAmbientHom
    (t : Finset ι) {X Y : S.ProjectiveCategory}
    (hX : S.projectiveVertex X ∈ t)
    (hY : S.projectiveVertex Y ∈ t) (f : X ⟶ Y) :
    (projectiveFunctor S (finsetPrimitiveEmbedding t)).obj
        (finsetProjectiveObj S t X hX) ⟶
      (projectiveFunctor S (finsetPrimitiveEmbedding t)).obj
        (finsetProjectiveObj S t Y hY) := by
  refine ⟨f.1, ?_⟩
  rw [mem_idempotentCorner_iff]
  refine ⟨f.1, ?_⟩
  rw [projectiveFunctor_obj_projectiveVertex,
    projectiveFunctor_obj_projectiveVertex,
    finsetProjectiveObj_projectiveVertex,
    finsetProjectiveObj_projectiveVertex,
    finsetPrimitiveEmbedding_index,
    finsetPrimitiveEmbedding_index,
    ProjectiveCategory.idempotent_mul_val,
    ProjectiveCategory.val_mul_idempotent]

@[simp]
theorem finsetAmbientHom_val
    (t : Finset ι) {X Y : S.ProjectiveCategory}
    (hX : S.projectiveVertex X ∈ t)
    (hY : S.projectiveVertex Y ∈ t) (f : X ⟶ Y) :
    (finsetAmbientHom S t hX hY f).1 = f.1 :=
  rfl

/-- After transporting the endpoints back along their canonical equalities,
the ambient realization of a lifted finite-corner morphism is the original
morphism. -/
theorem homCongr_finsetAmbientHom
    (t : Finset ι) {X Y : S.ProjectiveCategory}
    (hX : S.projectiveVertex X ∈ t)
    (hY : S.projectiveVertex Y ∈ t) (f : X ⟶ Y) :
    let eX := eqToIso
      (projectiveFunctor_obj_finsetProjectiveObj_eq S t X hX)
    let eY := eqToIso
      (projectiveFunctor_obj_finsetProjectiveObj_eq S t Y hY)
    CategoryTheory.Linear.homCongr k eX eY
      (finsetAmbientHom S t hX hY f) = f := by
  dsimp only
  apply Subtype.ext
  simp [CategoryTheory.Linear.homCongr_apply,
    ProjectiveCategory.idempotent_mul_val,
    ProjectiveCategory.val_mul_idempotent]

/-- Lift an ambient morphism whose endpoints lie in a finite selected set to
the corresponding morphism in the selected corner. -/
def finsetProjectiveHom
    (t : Finset ι) {X Y : S.ProjectiveCategory}
    (hX : S.projectiveVertex X ∈ t)
    (hY : S.projectiveVertex Y ∈ t) (f : X ⟶ Y) :
    finsetProjectiveObj S t X hX ⟶ finsetProjectiveObj S t Y hY :=
  (projectiveFunctor S (finsetPrimitiveEmbedding t)).preimage
    (finsetAmbientHom S t hX hY f)

@[simp]
theorem finsetProjectiveFunctor_map_finsetProjectiveHom
    (t : Finset ι) {X Y : S.ProjectiveCategory}
    (hX : S.projectiveVertex X ∈ t)
    (hY : S.projectiveVertex Y ∈ t) (f : X ⟶ Y) :
    (projectiveFunctor S (finsetPrimitiveEmbedding t)).map
        (finsetProjectiveHom S t hX hY f) =
      finsetAmbientHom S t hX hY f := by
  exact Functor.map_preimage _ _

/-- The ambient value of an arbitrary selected-corner morphism is unchanged
by mapping it to the ambient projective category and transporting its
canonical endpoints. -/
theorem homCongr_projectiveFunctorMap_val
    (t : Finset ι) {X Y : S.ProjectiveCategory}
    (hX : S.projectiveVertex X ∈ t)
    (hY : S.projectiveVertex Y ∈ t)
    (f : finsetProjectiveObj S t X hX ⟶
      finsetProjectiveObj S t Y hY) :
    let E := projectiveFunctor S (finsetPrimitiveEmbedding t)
    let eX := eqToIso
      (projectiveFunctor_obj_finsetProjectiveObj_eq S t X hX)
    let eY := eqToIso
      (projectiveFunctor_obj_finsetProjectiveObj_eq S t Y hY)
    (CategoryTheory.Linear.homCongr k eX eY (E.map f)).1 = f.1.1 := by
  dsimp only
  simp [CategoryTheory.Linear.homCongr_apply]
  let E := projectiveFunctor S (finsetPrimitiveEmbedding t)
  have hleft : S.idempotent (S.projectiveVertex Y) * (E.map f).1 =
      (E.map f).1 := by
    simpa [E] using ProjectiveCategory.idempotent_mul_val S (E.map f)
  have hright : (E.map f).1 * S.idempotent (S.projectiveVertex X) =
      (E.map f).1 := by
    simpa [E] using ProjectiveCategory.val_mul_idempotent S (E.map f)
  change S.idempotent (S.projectiveVertex Y) * (E.map f).1 *
      S.idempotent (S.projectiveVertex X) = (E.map f).1
  rw [hleft, hright]

@[simp]
theorem finsetProjectiveHom_val_val
    (t : Finset ι) {X Y : S.ProjectiveCategory}
    (hX : S.projectiveVertex X ∈ t)
    (hY : S.projectiveVertex Y ∈ t) (f : X ⟶ Y) :
    (finsetProjectiveHom S t hX hY f).1.1 = f.1 := by
  have hmap := finsetProjectiveFunctor_map_finsetProjectiveHom
    S t hX hY f
  exact congrArg (fun g ↦ g.1) hmap

/-- Ambient-radical morphisms remain radical when lifted to a finite selected
corner. -/
theorem finsetProjectiveHom_val_mem_jacobson
    (t : Finset ι) {X Y : S.ProjectiveCategory}
    (hX : S.projectiveVertex X ∈ t)
    (hY : S.projectiveVertex Y ∈ t) (f : X ⟶ Y)
    (hf : f.1 ∈ Ring.jacobson A) :
    (finsetProjectiveHom S t hX hY f).1 ∈
      Ring.jacobson (SelectedCorner S (finsetPrimitiveEmbedding t)) := by
  rw [mem_jacobson_iff_val_mem_jacobson S (finsetPrimitiveEmbedding t)]
  simpa only [finsetProjectiveHom_val_val] using hf

/-- A full Hom-bimodule generator remains full after passage to a finite
selected primitive corner. -/
theorem finsetProjectiveHom_span_eq_top_of_ambient
    (t : Finset ι) {X Y : S.ProjectiveCategory}
    (hX : S.projectiveVertex X ∈ t)
    (hY : S.projectiveVertex Y ∈ t) (f : X ⟶ Y)
    (hf : LargeIndecomposable.twoSidedEndomorphismSpan k f = ⊤) :
    LargeIndecomposable.twoSidedEndomorphismSpan k
      (finsetProjectiveHom S t hX hY f) = ⊤ := by
  let E := projectiveFunctor S (finsetPrimitiveEmbedding t)
  rw [← LargeIndecomposable.fullyFaithfulLinearFunctor_map_span_eq_top_iff E]
  let eX := eqToIso (projectiveFunctor_obj_finsetProjectiveObj_eq S t X hX)
  let eY := eqToIso (projectiveFunctor_obj_finsetProjectiveObj_eq S t Y hY)
  apply (LargeIndecomposable.homCongr_span_eq_top_iff
    (k := k) eX eY
      (E.map (finsetProjectiveHom S t hX hY f))).1
  have hmap : CategoryTheory.Linear.homCongr k eX eY
      (E.map (finsetProjectiveHom S t hX hY f)) = f := by
    simpa [eX, eY, E] using
      (homCongr_finsetAmbientHom (k := k) S t hX hY f)
  rw [hmap]
  exact hf

/-- A radical endomorphism generator retains its exact Jacobson span in a
finite selected primitive corner. -/
theorem finsetProjectiveEnd_span_eq_jacobson_of_ambient
    (t : Finset ι) (X : S.ProjectiveCategory)
    (hX : S.projectiveVertex X ∈ t) (tau : End X)
    (htauSpan : LargeIndecomposable.twoSidedEndomorphismSpan k tau =
      (Ring.jacobson (End X)).restrictScalars k) :
    LargeIndecomposable.twoSidedEndomorphismSpan k
        (End.of (finsetProjectiveHom S t hX hX tau.asHom)) =
      (Ring.jacobson
        (End (finsetProjectiveObj S t X hX))).restrictScalars k := by
  let X' := finsetProjectiveObj S t X hX
  let tau' : End X' := End.of (finsetProjectiveHom S t hX hX tau.asHom)
  let E := projectiveFunctor S (finsetPrimitiveEmbedding t)
  let eX := eqToIso (projectiveFunctor_obj_finsetProjectiveObj_eq S t X hX)
  have htauJ : tau ∈ Ring.jacobson (End X) := by
    have hmem : tau ∈
        (Ring.jacobson (End X)).restrictScalars k := by
      rw [← htauSpan]
      exact LargeIndecomposable.mem_twoSidedEndomorphismSpan k tau
    exact hmem
  have htau'ValJ : tau'.1 ∈
      Ring.jacobson (SelectedCorner S (finsetPrimitiveEmbedding t)) := by
    exact finsetProjectiveHom_val_mem_jacobson S t hX hX tau.asHom
      ((S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson X tau).1 htauJ)
  have htau'J : tau' ∈ Ring.jacobson (End X') := by
    exact ((splitBasic S (finsetPrimitiveEmbedding t))
      |>.projectiveEnd_mem_jacobson_iff_val_mem_jacobson X' tau').2 htau'ValJ
  change LargeIndecomposable.twoSidedEndomorphismSpan k tau' = _
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro z ⟨a, b, rfl⟩
    have hring : b * tau' * a ∈ Ring.jacobson (End X') :=
      (Ring.jacobson (End X')).mul_mem_right a
        ((Ring.jacobson (End X')).mul_mem_left b htau'J)
    change End.of ((a.asHom ≫ tau'.asHom) ≫ b.asHom) ∈
      Ring.jacobson (End X')
    rw [show End.of ((a.asHom ≫ tau'.asHom) ≫ b.asHom) =
        b * tau' * a by
      apply End.ext
      simp only [End.mul_def, Category.assoc]]
    exact hring
  · intro a ha
    let g : End X := End.of
      (CategoryTheory.Linear.homCongr k eX eX (E.map a))
    have haCornerVal : a.1 ∈
        Ring.jacobson (SelectedCorner S (finsetPrimitiveEmbedding t)) :=
      ((splitBasic S (finsetPrimitiveEmbedding t))
        |>.projectiveEnd_mem_jacobson_iff_val_mem_jacobson X' a).1 ha
    have haAmbientVal : a.1.1 ∈ Ring.jacobson A :=
      (mem_jacobson_iff_val_mem_jacobson
        S (finsetPrimitiveEmbedding t) a.1).1 haCornerVal
    have hgVal : g.1 ∈ Ring.jacobson A := by
      change (CategoryTheory.Linear.homCongr k eX eX (E.map a)).1 ∈
        Ring.jacobson A
      rw [homCongr_projectiveFunctorMap_val (k := k) S t hX hX a]
      exact haAmbientVal
    have hgJ : g ∈ Ring.jacobson (End X) :=
      (S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson X g).2 hgVal
    have hgSpan : g.asHom ∈
        LargeIndecomposable.twoSidedEndomorphismSpan k tau.asHom := by
      change g ∈ LargeIndecomposable.twoSidedEndomorphismSpan k tau
      rw [htauSpan]
      exact hgJ
    have htauMap : CategoryTheory.Linear.homCongr k eX eX
        (E.map tau'.asHom) = tau.asHom := by
      simpa [eX, E, tau', X'] using
        (homCongr_finsetAmbientHom (k := k) S t hX hX tau.asHom)
    rw [← htauMap] at hgSpan
    have hback := LargeIndecomposable.homCongr_mem_twoSidedEndomorphismSpan
      (k := k) eX.symm eX.symm hgSpan
    have hmap : E.map a ∈
        LargeIndecomposable.twoSidedEndomorphismSpan k
          (E.map tau'.asHom) := by
      simpa [g, CategoryTheory.Linear.homCongr_apply,
        Category.assoc] using hback
    exact LargeIndecomposable.fullyFaithfulLinearFunctor_mem_span_of_map_mem
      (k := k) E hmap

end ProjectiveFunctor

end SelectedCorner

end LargeIndecomposable.SplitBasicIdempotents
