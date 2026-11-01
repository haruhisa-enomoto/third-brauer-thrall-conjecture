module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.Basic

@[expose] public section

/-!
# The Jacobson radical of a noncommutative local ring

In a Dedekind-finite local ring, the nonunits form a two-sided ideal.  This is
the unique maximal left ideal, and therefore agrees with the ring Jacobson
radical.  The Dedekind-finite hypothesis holds in particular for Artinian
rings and for finite-dimensional algebras over a field.
-/

set_option autoImplicit false

namespace LargeIndecomposable

variable (R : Type*) [Ring R] [IsDedekindFiniteMonoid R] [IsLocalRing R]

/-- The ideal of nonunits in a possibly noncommutative Dedekind-finite local
ring. -/
def nonunitsIdeal : Ideal R where
  carrier := nonunits R
  zero_mem' := not_isUnit_zero
  add_mem' := IsLocalRing.nonunits_add
  smul_mem' _ _ hb := fun hab ↦ hb (isUnit_of_mul_isUnit_right hab)

@[simp]
theorem mem_nonunitsIdeal_iff_not_isUnit (x : R) :
    x ∈ nonunitsIdeal R ↔ ¬ IsUnit x :=
  Iff.rfl

instance nonunitsIdeal_isTwoSided : (nonunitsIdeal R).IsTwoSided where
  mul_mem_of_left _ ha := fun hab ↦ ha (isUnit_of_mul_isUnit_left hab)

instance nonunitsIdeal_isMaximal : (nonunitsIdeal R).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  constructor
  · change ¬ ¬ IsUnit (1 : R)
    exact not_not_intro isUnit_one
  · intro I x _ hx hIx
    change ¬ ¬ IsUnit x at hx
    rw [Classical.not_not] at hx
    obtain ⟨u, rfl⟩ := hx
    simpa using I.mul_mem_left (↑u⁻¹) hIx

/-- Every maximal left ideal of a Dedekind-finite local ring is the ideal of
nonunits. -/
theorem Ideal.IsMaximal.eq_nonunitsIdeal {I : Ideal R} (hI : I.IsMaximal) :
    I = nonunitsIdeal R := by
  apply hI.eq_of_le (Ideal.IsMaximal.ne_top (nonunitsIdeal_isMaximal R))
  intro x hx
  exact coe_subset_nonunits hI.ne_top hx

/-- In a possibly noncommutative Dedekind-finite local ring, the Jacobson
radical is the ideal of nonunits. -/
theorem ringJacobson_eq_nonunitsIdeal :
    Ring.jacobson R = nonunitsIdeal R := by
  rw [Ring.jacobson_eq_sInf_isMaximal]
  ext x
  constructor
  · intro hx
    exact Ideal.mem_sInf.mp hx (nonunitsIdeal_isMaximal R)
  · intro hx
    apply Ideal.mem_sInf.mpr
    intro I hI
    rw [LargeIndecomposable.Ideal.IsMaximal.eq_nonunitsIdeal R hI]
    exact hx

/-- Membership in the Jacobson radical of a Dedekind-finite local ring is
equivalent to failure to be a unit. -/
theorem mem_ringJacobson_iff_not_isUnit (x : R) :
    x ∈ Ring.jacobson R ↔ ¬ IsUnit x := by
  rw [ringJacobson_eq_nonunitsIdeal]
  exact mem_nonunitsIdeal_iff_not_isUnit R x

omit [IsDedekindFiniteMonoid R] in
/-- Adding one to a nonunit in a possibly noncommutative local ring produces
a unit. -/
theorem isUnit_one_add_of_not_isUnit (x : R) (hx : ¬ IsUnit x) :
    IsUnit (1 + x) := by
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one
      (a := -x) (b := 1 + x) (by abel) with hneg | h
  · exact (hx (by simpa using hneg.neg)).elim
  · exact h

end LargeIndecomposable
