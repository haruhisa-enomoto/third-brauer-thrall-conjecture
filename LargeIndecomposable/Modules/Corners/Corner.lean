module

public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Jacobson.Semiprimary
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Corner algebras

For an idempotent `e` of a `k`-algebra `A`, Mathlib's corner ring
`IsIdempotentElem.Corner` is `eAe` with identity `e`. This file makes it a
finite-dimensional `k`-algebra and shows that `e (rad A) e` lies in the radical
of `eAe` (`cornerMk_mem_jacobson`).

The value API and the algebra structure are adapted from
`LargeIndecomposable/Foundations/CornerAlgebra.lean` and
`CornerRadical.lean` of `multiplicative-bases-deformations`
(commit 7b9f39f221d8a420a1531f487a3b93ae6d26ce85). The radical statement is
proved here through nilpotence of `rad A`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

universe u

namespace Corner

variable {A : Type u} [Ring A] {e : A} (he : IsIdempotentElem e)

/-- The underlying element of `A` of an element of the corner. -/
def val (x : he.Corner) : A := (show ↥(Subsemigroup.corner e) from x).1

/-- An element of `A` lying in the corner, as an element of the corner. -/
def mk (a : A) (ha : a ∈ Subsemigroup.corner e) : he.Corner :=
  show ↥(Subsemigroup.corner e) from ⟨a, ha⟩

theorem val_mem (x : he.Corner) : val he x ∈ Subsemigroup.corner e :=
  (show ↥(Subsemigroup.corner e) from x).2

theorem ext {x y : he.Corner} (h : val he x = val he y) : x = y :=
  Subtype.ext (p := (· ∈ Subsemigroup.corner e)) h

theorem val_injective : Function.Injective (val he) := fun _ _ h ↦ ext he h

@[simp]
theorem val_mk (a : A) (ha : a ∈ Subsemigroup.corner e) : val he (mk he a ha) = a := rfl

@[simp]
theorem val_one : val he (1 : he.Corner) = e := rfl

@[simp]
theorem val_mul (x y : he.Corner) : val he (x * y) = val he x * val he y := rfl

@[simp]
theorem val_add (x y : he.Corner) : val he (x + y) = val he x + val he y := rfl

@[simp]
theorem val_zero : val he (0 : he.Corner) = 0 := rfl

@[simp]
theorem val_neg (x : he.Corner) : val he (-x) = -val he x := rfl

@[simp]
theorem val_sub (x y : he.Corner) : val he (x - y) = val he x - val he y := by
  rw [sub_eq_add_neg, val_add, val_neg, ← sub_eq_add_neg]

theorem val_pow (x : he.Corner) (n : ℕ) : val he (x ^ (n + 1)) = val he x ^ (n + 1) := by
  induction n with
  | zero => rw [zero_add, pow_one, pow_one]
  | succ n ih => rw [pow_succ, val_mul, ih, ← pow_succ]

theorem mul_val (x : he.Corner) : e * val he x = val he x :=
  ((Subsemigroup.mem_corner_iff he).mp (val_mem he x)).1

theorem val_mul_e (x : he.Corner) : val he x * e = val he x :=
  ((Subsemigroup.mem_corner_iff he).mp (val_mem he x)).2

include he in
theorem mem_iff {a : A} : a ∈ Subsemigroup.corner e ↔ e * a = a ∧ a * e = a :=
  Subsemigroup.mem_corner_iff he

theorem sandwich_mem (a : A) : e * a * e ∈ Subsemigroup.corner e := ⟨a, rfl⟩

/-- `e a e` as an element of the corner. -/
def sandwich (a : A) : he.Corner := mk he (e * a * e) (sandwich_mem (e := e) a)

@[simp]
theorem val_sandwich (a : A) : val he (sandwich he a) = e * a * e := rfl

section Algebra

variable {k : Type*} [CommRing k] [Algebra k A]

theorem smul_mem (c : k) (x : he.Corner) : c • val he x ∈ Subsemigroup.corner e := by
  rw [mem_iff he, mul_smul_comm, mul_val, smul_mul_assoc, val_mul_e]
  exact ⟨rfl, rfl⟩

instance instSMul : SMul k he.Corner where
  smul c x := mk he (c • val he x) (smul_mem he c x)

@[simp]
theorem val_smul (c : k) (x : he.Corner) : val he (c • x) = c • val he x := rfl

/-- The corner `eAe` is a `k`-algebra. -/
instance instAlgebra : Algebra k he.Corner where
  algebraMap :=
    { toFun c := c • (1 : he.Corner)
      map_one' := ext he (by simp)
      map_mul' c d := ext he (by
        simp only [val_smul, val_one, val_mul]
        rw [smul_mul_smul_comm, he.eq, mul_comm])
      map_zero' := ext he (by simp)
      map_add' c d := ext he (by simp [add_smul]) }
  commutes' c x := ext he (by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, val_mul, val_smul, val_one,
      smul_mul_assoc, mul_smul_comm, mul_val, val_mul_e])
  smul_def' c x := ext he (by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, val_mul, val_smul, val_one,
      smul_mul_assoc, mul_val])

/-- The value map of the corner, as a `k`-linear map. -/
def valL (k : Type*) [CommRing k] [Algebra k A] {e : A} (he : IsIdempotentElem e) :
    he.Corner →ₗ[k] A where
  toFun := val he
  map_add' := val_add he
  map_smul' := val_smul he

@[simp]
theorem valL_apply (x : he.Corner) : valL k he x = val he x := rfl

theorem valL_injective : Function.Injective (valL k he) := val_injective he

end Algebra

variable {k : Type*} [Field k] [Algebra k A] [FiniteDimensional k A]

include k in
theorem finiteDimensional : FiniteDimensional k he.Corner :=
  Module.Finite.of_injective (valL k he) (valL_injective he)

/-- An element `x` with `1 - y x` invertible for all `y` lies in the Jacobson
radical. (Adapted from `EndpointChains.lean` of `multiplicative-bases-deformations`.) -/
theorem mem_jacobson_of_forall_isUnit {R : Type*} [Ring R] {x : R}
    (h : ∀ y, IsUnit (1 - y * x)) : x ∈ Ring.jacobson R := by
  rw [Ring.jacobson_eq_sInf_isMaximal, Submodule.mem_sInf]
  intro I hI
  by_contra hx
  have hI' : Ideal.IsMaximal I := hI
  have htop : I ⊔ Submodule.span R {x} = ⊤ := by
    apply hI'.1.2
    refine lt_of_le_of_ne le_sup_left fun he ↦ hx ?_
    rw [he]
    exact le_sup_right (a := I) (Submodule.mem_span_singleton_self x)
  have h1 : (1 : R) ∈ I ⊔ Submodule.span R {x} := htop ▸ Submodule.mem_top
  obtain ⟨i, hi, z, hz, hiz⟩ := Submodule.mem_sup.1 h1
  obtain ⟨y, rfl⟩ := Submodule.mem_span_singleton.1 hz
  have hi1 : i = 1 - y * x := by rw [← hiz, smul_eq_mul]; abel
  exact hI'.ne_top (Ideal.eq_top_of_isUnit_mem I hi (hi1 ▸ h y))

variable (k) in
include k in
/-- Every element of the radical of a finite-dimensional algebra is nilpotent. -/
theorem isNilpotent_of_mem_jacobson {x : A} (hx : x ∈ Ring.jacobson A) : IsNilpotent x := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨N, hN⟩ := IsSemiprimaryRing.isNilpotent (R := A)
  refine ⟨N, ?_⟩
  have := Ideal.pow_mem_pow hx N
  rw [hN] at this
  simpa using this

variable (k) in
include k in
/-- `e (rad A) e ⊆ rad (eAe)`. -/
theorem mk_mem_jacobson {z : A} (hz : z ∈ Ring.jacobson A) (hze : z ∈ Subsemigroup.corner e) :
    mk he z hze ∈ Ring.jacobson he.Corner := by
  refine mem_jacobson_of_forall_isUnit fun y ↦ IsNilpotent.isUnit_one_sub ?_
  obtain ⟨N, hN⟩ := isNilpotent_of_mem_jacobson k ((Ring.jacobson A).mul_mem_left (val he y) hz)
  refine ⟨N + 1, val_injective he ?_⟩
  rw [val_pow, val_mul, val_mk, pow_succ, hN, zero_mul, val_zero]

end Corner

end LargeIndecomposable
