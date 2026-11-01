module

public import LargeIndecomposable.Cleaving.ClosedChains.RadicalParameter
public import LargeIndecomposable.Foundations.Ring.AlgClosedDivision
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.ClosedZigzagTransfer

universe u v w z

private theorem exists_left_unit_times_power
    {R : Type z} [Ring R] [IsLocalRing R] [IsArtinianRing R]
    (tau : R) (htauJ : tau ∈ Ring.jacobson R)
    (hgen : ∀ x : R, x ∈ Ring.jacobson R → ∃ y : R, x = y * tau)
    {x : R} (hxJ : x ∈ Ring.jacobson R) (hx0 : x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ u : R, IsUnit u ∧ x = u * tau ^ n := by
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rw [Ideal.jacobson_bot] at hN
  have hiter : ∀ n : ℕ,
      (∃ m : ℕ, m ≤ n ∧ ∃ u : R, IsUnit u ∧ x = u * tau ^ m) ∨
      (∃ y : R, y ∈ Ring.jacobson R ∧ x = y * tau ^ n) := by
    intro n
    induction n with
    | zero =>
        right
        exact ⟨x, hxJ, by simp⟩
    | succ n ih =>
        rcases ih with hdone | ⟨y, hyJ, hxy⟩
        · left
          rcases hdone with ⟨m, hmn, u, hu, hxu⟩
          exact ⟨m, hmn.trans (Nat.le_succ n), u, hu, hxu⟩
        · obtain ⟨q, hyq⟩ := hgen y hyJ
          by_cases hq : IsUnit q
          · left
            refine ⟨n + 1, Nat.le_refl _, q, hq, ?_⟩
            rw [hyq] at hxy
            calc
              x = (q * tau) * tau ^ n := hxy
              _ = q * tau ^ (n + 1) := by rw [pow_succ']; exact mul_assoc _ _ _
          · right
            refine ⟨q, (mem_ringJacobson_iff_not_isUnit R q).2 hq, ?_⟩
            rw [hyq] at hxy
            calc
              x = (q * tau) * tau ^ n := hxy
              _ = q * tau ^ (n + 1) := by rw [pow_succ']; exact mul_assoc _ _ _
  rcases hiter N with hdone | ⟨y, hyJ, hxy⟩
  · rcases hdone with ⟨n, hnN, u, hu, hxu⟩
    refine ⟨n, ?_, u, hu, hxu⟩
    cases n with
    | zero =>
        exfalso
        apply (mem_ringJacobson_iff_not_isUnit R x).1 hxJ
        rw [pow_zero, mul_one] at hxu
        rw [hxu]
        exact hu
    | succ n => exact Nat.succ_pos n
  · have htauPow : tau ^ N = 0 := by
      have htauPowMem : tau ^ N ∈ (Ring.jacobson R) ^ N :=
        Ideal.pow_mem_pow htauJ N
      rw [hN] at htauPowMem
      simpa using htauPowMem
    exact (hx0 (by rw [hxy, htauPow, mul_zero])).elim

private theorem exists_power_times_right_unit
    {R : Type z} [Ring R] [IsLocalRing R] [IsArtinianRing R]
    (tau : R) (htauJ : tau ∈ Ring.jacobson R)
    (hgen : ∀ x : R, x ∈ Ring.jacobson R → ∃ y : R, x = tau * y)
    {x : R} (hxJ : x ∈ Ring.jacobson R) (hx0 : x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ u : R, IsUnit u ∧ x = tau ^ n * u := by
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rw [Ideal.jacobson_bot] at hN
  have hiter : ∀ n : ℕ,
      (∃ m : ℕ, m ≤ n ∧ ∃ u : R, IsUnit u ∧ x = tau ^ m * u) ∨
      (∃ y : R, y ∈ Ring.jacobson R ∧ x = tau ^ n * y) := by
    intro n
    induction n with
    | zero =>
        right
        exact ⟨x, hxJ, by simp⟩
    | succ n ih =>
        rcases ih with hdone | ⟨y, hyJ, hxy⟩
        · left
          rcases hdone with ⟨m, hmn, u, hu, hxu⟩
          exact ⟨m, hmn.trans (Nat.le_succ n), u, hu, hxu⟩
        · obtain ⟨q, hyq⟩ := hgen y hyJ
          by_cases hq : IsUnit q
          · left
            refine ⟨n + 1, Nat.le_refl _, q, hq, ?_⟩
            rw [hyq] at hxy
            calc
              x = tau ^ n * (tau * q) := hxy
              _ = tau ^ (n + 1) * q := by rw [pow_succ]; exact (mul_assoc _ _ _).symm
          · right
            refine ⟨q, (mem_ringJacobson_iff_not_isUnit R q).2 hq, ?_⟩
            rw [hyq] at hxy
            calc
              x = tau ^ n * (tau * q) := hxy
              _ = tau ^ (n + 1) * q := by rw [pow_succ]; exact (mul_assoc _ _ _).symm
  rcases hiter N with hdone | ⟨y, hyJ, hxy⟩
  · rcases hdone with ⟨n, hnN, u, hu, hxu⟩
    refine ⟨n, ?_, u, hu, hxu⟩
    cases n with
    | zero =>
        exfalso
        apply (mem_ringJacobson_iff_not_isUnit R x).1 hxJ
        rw [pow_zero, one_mul] at hxu
        rw [hxu]
        exact hu
    | succ n => exact Nat.succ_pos n
  · have htauPow : tau ^ N = 0 := by
      have htauPowMem : tau ^ N ∈ (Ring.jacobson R) ^ N :=
        Ideal.pow_mem_pow htauJ N
      rw [hN] at htauPowMem
      simpa using htauPowMem
    exact (hx0 (by rw [hxy, htauPow, zero_mul])).elim

private theorem isNilpotent_of_mem_jacobson_of_isArtinian
    {R : Type z} [Ring R] [IsArtinianRing R]
    {a : R} (haJ : a ∈ Ring.jacobson R) : IsNilpotent a := by
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rw [Ideal.jacobson_bot] at hN
  refine ⟨N, ?_⟩
  have haPow : a ^ N ∈ (Ring.jacobson R) ^ N :=
    Ideal.pow_mem_pow haJ N
  rw [hN] at haPow
  simpa using haPow

private theorem eq_zero_of_eq_mul_left_of_isNilpotent
    {R : Type z} [Ring R] {a x : R} (ha : IsNilpotent a)
    (h : x = a * x) : x = 0 := by
  have hu : IsUnit (1 - a) := ha.isUnit_one_sub
  apply hu.mul_left_cancel
  rw [mul_zero, sub_mul, one_mul, ← h, sub_self]

private theorem eq_zero_of_eq_mul_right_of_isNilpotent
    {R : Type z} [Ring R] {a x : R} (ha : IsNilpotent a)
    (h : x = x * a) : x = 0 := by
  have hu : IsUnit (1 - a) := ha.isUnit_one_sub
  apply hu.mul_right_cancel
  rw [zero_mul, mul_sub, mul_one, ← h, sub_self]

private theorem le_of_eq_left_unit_times_powers
    {R : Type z} [Ring R] [IsArtinianRing R]
    (tau : R) (htauJ : tau ∈ Ring.jacobson R)
    {x : R} (hx0 : x ≠ 0) {m n : ℕ} {e f : R}
    (_he : IsUnit e) (hf : IsUnit f)
    (hm : x = e * tau ^ m) (hn : x = f * tau ^ n) : m ≤ n := by
  by_contra hmn
  have hnm : n < m := Nat.lt_of_not_ge hmn
  have hdpos : 0 < m - n := Nat.sub_pos_of_lt hnm
  have htauDiffJ : tau ^ (m - n) ∈ Ring.jacobson R :=
    (Ring.jacobson R).pow_mem_of_mem htauJ (m - n) hdpos
  let a : R := (↑(hf.unit⁻¹) : R) * e * tau ^ (m - n)
  have haJ : a ∈ Ring.jacobson R := by
    exact (Ring.jacobson R).mul_mem_left
      ((↑(hf.unit⁻¹) : R) * e) htauDiffJ
  have hinv : (↑(hf.unit⁻¹) : R) * f = 1 := by
    calc
      (↑(hf.unit⁻¹) : R) * f =
          (↑(hf.unit⁻¹) : R) * (↑hf.unit : R) :=
        congrArg (fun q : R ↦ (↑(hf.unit⁻¹) : R) * q) hf.unit_spec.symm
      _ = 1 := Units.inv_mul hf.unit
  have hfixed : tau ^ n = a * tau ^ n := by
    calc
      tau ^ n = (↑(hf.unit⁻¹) : R) * (f * tau ^ n) := by
        rw [← mul_assoc, hinv, one_mul]
      _ = (↑(hf.unit⁻¹) : R) * (e * tau ^ m) := by rw [← hn, hm]
      _ = a * tau ^ n := by
        rw [show m = (m - n) + n by omega, pow_add]
        simp only [a, mul_assoc]
  have htauN0 : tau ^ n = 0 :=
    eq_zero_of_eq_mul_left_of_isNilpotent
      (isNilpotent_of_mem_jacobson_of_isArtinian haJ) hfixed
  exact hx0 (by rw [hn, htauN0, mul_zero])

private theorem le_of_eq_powers_times_right_unit
    {R : Type z} [Ring R] [IsArtinianRing R]
    (tau : R) (htauJ : tau ∈ Ring.jacobson R)
    {x : R} (hx0 : x ≠ 0) {m n : ℕ} {e f : R}
    (_he : IsUnit e) (hf : IsUnit f)
    (hm : x = tau ^ m * e) (hn : x = tau ^ n * f) : m ≤ n := by
  by_contra hmn
  have hnm : n < m := Nat.lt_of_not_ge hmn
  have hdpos : 0 < m - n := Nat.sub_pos_of_lt hnm
  have htauDiffJ : tau ^ (m - n) ∈ Ring.jacobson R :=
    (Ring.jacobson R).pow_mem_of_mem htauJ (m - n) hdpos
  let a : R := tau ^ (m - n) * e * (↑(hf.unit⁻¹) : R)
  have haJ : a ∈ Ring.jacobson R := by
    simpa only [a, mul_assoc] using (Ring.jacobson R).mul_mem_right
      (e * (↑(hf.unit⁻¹) : R)) htauDiffJ
  have hinv : f * (↑(hf.unit⁻¹) : R) = 1 := by
    calc
      f * (↑(hf.unit⁻¹) : R) =
          (↑hf.unit : R) * (↑(hf.unit⁻¹) : R) :=
        congrArg (fun q : R ↦ q * (↑(hf.unit⁻¹) : R)) hf.unit_spec.symm
      _ = 1 := Units.mul_inv hf.unit
  have hfixed : tau ^ n = tau ^ n * a := by
    calc
      tau ^ n = (tau ^ n * f) * (↑(hf.unit⁻¹) : R) := by
        rw [mul_assoc, hinv, mul_one]
      _ = (tau ^ m * e) * (↑(hf.unit⁻¹) : R) := by rw [← hn, hm]
      _ = tau ^ n * a := by
        rw [show m = n + (m - n) by omega, pow_add]
        simp only [a, mul_assoc]
  have htauN0 : tau ^ n = 0 :=
    eq_zero_of_eq_mul_right_of_isNilpotent
      (isNilpotent_of_mem_jacobson_of_isArtinian haJ) hfixed
  exact hx0 (by rw [hm, show m = n + (m - n) by omega, pow_add,
    htauN0, zero_mul, zero_mul])

/-- Over an algebraically closed field, a left generator of the radical of a
finite-dimensional Artinian local algebra generates the whole algebra. -/
theorem algebra_adjoin_singleton_eq_top_of_left_radical_generator
    {k : Type w} [Field k] [IsAlgClosed k]
    {R : Type z} [Ring R] [Algebra k R] [Module.Finite k R]
    [IsLocalRing R] [IsArtinianRing R]
    (tau : R) (htauJ : tau ∈ Ring.jacobson R)
    (hgen : ∀ x : R, x ∈ Ring.jacobson R → ∃ q : R, x = q * tau) :
    Algebra.adjoin k ({tau} : Set R) = ⊤ := by
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rw [Ideal.jacobson_bot] at hN
  have htauN : tau ^ N = 0 := by
    have htauPow : tau ^ N ∈ (Ring.jacobson R) ^ N :=
      Ideal.pow_mem_pow htauJ N
    rw [hN] at htauPow
    simpa using htauPow
  let S : Subalgebra k R := Algebra.adjoin k ({tau} : Set R)
  have htauS : tau ∈ S := Algebra.self_mem_adjoin_singleton k tau
  have hiter : ∀ (n : ℕ) (x : R),
      ∃ s : R, s ∈ S ∧ ∃ q : R, x = s + q * tau ^ n := by
    intro n
    induction n with
    | zero =>
        intro x
        exact ⟨0, S.zero_mem, x, by simp⟩
    | succ n ih =>
        intro x
        obtain ⟨s, hs, q, hx⟩ := ih x
        obtain ⟨c, hcJ⟩ := exists_sub_algebraMap_mem_ringJacobson k R q
        obtain ⟨r, hr⟩ := hgen (q - algebraMap k R c) hcJ
        have hq : q = algebraMap k R c + r * tau := by
          calc
            q = (q - algebraMap k R c) + algebraMap k R c :=
              (sub_add_cancel q (algebraMap k R c)).symm
            _ = r * tau + algebraMap k R c := by rw [hr]
            _ = algebraMap k R c + r * tau := add_comm _ _
        refine ⟨s + algebraMap k R c * tau ^ n,
          S.add_mem hs (S.mul_mem (S.algebraMap_mem c) (S.pow_mem htauS n)),
          r, ?_⟩
        calc
          x = s + q * tau ^ n := hx
          _ = s + (algebraMap k R c + r * tau) * tau ^ n := by rw [hq]
          _ = (s + algebraMap k R c * tau ^ n) +
              r * tau ^ (n + 1) := by
            rw [add_mul, mul_assoc, ← pow_succ']
            exact (add_assoc s (algebraMap k R c * tau ^ n)
              (r * tau ^ (n + 1))).symm
  apply top_unique
  intro x _hx
  obtain ⟨s, hs, q, hx⟩ := hiter N x
  rw [htauN, mul_zero, add_zero] at hx
  simpa [S, hx] using hs

/-- Right-oriented counterpart of
`algebra_adjoin_singleton_eq_top_of_left_radical_generator`. -/
theorem algebra_adjoin_singleton_eq_top_of_right_radical_generator
    {k : Type w} [Field k] [IsAlgClosed k]
    {R : Type z} [Ring R] [Algebra k R] [Module.Finite k R]
    [IsLocalRing R] [IsArtinianRing R]
    (tau : R) (htauJ : tau ∈ Ring.jacobson R)
    (hgen : ∀ x : R, x ∈ Ring.jacobson R → ∃ q : R, x = tau * q) :
    Algebra.adjoin k ({tau} : Set R) = ⊤ := by
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rw [Ideal.jacobson_bot] at hN
  have htauN : tau ^ N = 0 := by
    have htauPow : tau ^ N ∈ (Ring.jacobson R) ^ N :=
      Ideal.pow_mem_pow htauJ N
    rw [hN] at htauPow
    simpa using htauPow
  let S : Subalgebra k R := Algebra.adjoin k ({tau} : Set R)
  have htauS : tau ∈ S := Algebra.self_mem_adjoin_singleton k tau
  have hiter : ∀ (n : ℕ) (x : R),
      ∃ s : R, s ∈ S ∧ ∃ q : R, x = s + tau ^ n * q := by
    intro n
    induction n with
    | zero =>
        intro x
        exact ⟨0, S.zero_mem, x, by simp⟩
    | succ n ih =>
        intro x
        obtain ⟨s, hs, q, hx⟩ := ih x
        obtain ⟨c, hcJ⟩ := exists_sub_algebraMap_mem_ringJacobson k R q
        obtain ⟨r, hr⟩ := hgen (q - algebraMap k R c) hcJ
        have hq : q = algebraMap k R c + tau * r := by
          calc
            q = (q - algebraMap k R c) + algebraMap k R c :=
              (sub_add_cancel q (algebraMap k R c)).symm
            _ = tau * r + algebraMap k R c := by rw [hr]
            _ = algebraMap k R c + tau * r := add_comm _ _
        refine ⟨s + tau ^ n * algebraMap k R c,
          S.add_mem hs (S.mul_mem (S.pow_mem htauS n) (S.algebraMap_mem c)),
          r, ?_⟩
        calc
          x = s + tau ^ n * q := hx
          _ = s + tau ^ n * (algebraMap k R c + tau * r) := by rw [hq]
          _ = (s + tau ^ n * algebraMap k R c) +
              tau ^ (n + 1) * r := by
            rw [mul_add, ← mul_assoc, ← pow_succ]
            exact (add_assoc s (tau ^ n * algebraMap k R c)
              (tau ^ (n + 1) * r)).symm
  apply top_unique
  intro x _hx
  obtain ⟨s, hs, q, hx⟩ := hiter N x
  rw [htauN, zero_mul, add_zero] at hx
  simpa [S, hx] using hs

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

private theorem exists_postcomposition_of_mem_span_of_allowsTransit
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

private theorem exists_precomposition_of_mem_span_of_allowsCotransit
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

/-- Transit-oriented local parameter data: the radical is generated by
postcomposition with `tau`, and every nonzero radical element is exactly a
positive power of `tau` followed by a unit. -/
structure TransitRadicalPowerData {X : C} (tau : End X) : Prop where
  allows_transit : AllowsTransit tau
  generates : ∀ x : End X, x ∈ Ring.jacobson (End X) →
    ∃ q : End X, x.asHom = tau.asHom ≫ q.asHom
  factors : ∀ x : End X, x ∈ Ring.jacobson (End X) → x ≠ 0 →
    ∃ n : ℕ, 0 < n ∧ ∃ e : End X, IsUnit e ∧
      x.asHom = (tau ^ n).asHom ≫ e.asHom

/-- Cotransit-oriented local parameter data: the radical is generated by
precomposition with `tau`, and every nonzero radical element is exactly a unit
followed by a positive power of `tau`. -/
structure CotransitRadicalPowerData {X : C} (tau : End X) : Prop where
  allows_cotransit : AllowsCotransit tau
  generates : ∀ x : End X, x ∈ Ring.jacobson (End X) →
    ∃ q : End X, x.asHom = q.asHom ≫ tau.asHom
  factors : ∀ x : End X, x ∈ Ring.jacobson (End X) → x ≠ 0 →
    ∃ n : ℕ, 0 < n ∧ ∃ e : End X, IsUnit e ∧
      x.asHom = e.asHom ≫ (tau ^ n).asHom

/-- A nonzero endomorphism cannot have two different exponents in
transit-oriented `tau`-power normal form. -/
theorem exponent_unique_of_power_postcomposition_units
    {X : C} [IsArtinianRing (End X)]
    (tau : End X) (htauJ : tau ∈ Ring.jacobson (End X))
    {x : End X} (hx0 : x ≠ 0) {m n : ℕ} {e f : End X}
    (he : IsUnit e) (hf : IsUnit f)
    (hm : x.asHom = (tau ^ m).asHom ≫ e.asHom)
    (hn : x.asHom = (tau ^ n).asHom ≫ f.asHom) : m = n := by
  have hmRing : x = e * tau ^ m := by
    change x.asHom = (e * tau ^ m).asHom
    simpa only [End.mul_def] using hm
  have hnRing : x = f * tau ^ n := by
    change x.asHom = (f * tau ^ n).asHom
    simpa only [End.mul_def] using hn
  exact le_antisymm
    (le_of_eq_left_unit_times_powers tau htauJ hx0 he hf hmRing hnRing)
    (le_of_eq_left_unit_times_powers tau htauJ hx0 hf he hnRing hmRing)

/-- A nonzero endomorphism cannot have two different exponents in
cotransit-oriented `tau`-power normal form. -/
theorem exponent_unique_of_precomposition_power_units
    {X : C} [IsArtinianRing (End X)]
    (tau : End X) (htauJ : tau ∈ Ring.jacobson (End X))
    {x : End X} (hx0 : x ≠ 0) {m n : ℕ} {e f : End X}
    (he : IsUnit e) (hf : IsUnit f)
    (hm : x.asHom = e.asHom ≫ (tau ^ m).asHom)
    (hn : x.asHom = f.asHom ≫ (tau ^ n).asHom) : m = n := by
  have hmRing : x = tau ^ m * e := by
    change x.asHom = (tau ^ m * e).asHom
    simpa only [End.mul_def] using hm
  have hnRing : x = tau ^ n * f := by
    change x.asHom = (tau ^ n * f).asHom
    simpa only [End.mul_def] using hn
  exact le_antisymm
    (le_of_eq_powers_times_right_unit tau htauJ hx0 he hf hmRing hnRing)
    (le_of_eq_powers_times_right_unit tau htauJ hx0 hf he hnRing hmRing)

/-- The operational content of a BGRS local parameter, with its orientation
retained rather than hidden behind two-sided unit equivalence. -/
def HasOrientedRadicalPowerFactorization {X : C} (tau : End X) : Prop :=
  TransitRadicalPowerData tau ∨ CotransitRadicalPowerData tau

/-- A two-sided generator of the endomorphism radical which allows transit or
cotransit is automatically an oriented BGRS radical-power parameter. -/
theorem hasOrientedRadicalPowerFactorization_of_span_eq
    {X : C} [IsLocalRing (End X)] [IsArtinianRing (End X)]
    (tau : End X) (htauJ : tau ∈ Ring.jacobson (End X))
    (htauSpan : twoSidedEndomorphismSpan k tau =
      (Ring.jacobson (End X)).restrictScalars k)
    (horient : AllowsTransit tau ∨ AllowsCotransit tau) :
    HasOrientedRadicalPowerFactorization tau := by
  rcases horient with ht | hc
  · left
    have hgenCat : ∀ y : End X, y ∈ Ring.jacobson (End X) →
        ∃ q : End X, y.asHom = tau.asHom ≫ q.asHom := by
      intro y hyJ
      have hySpan : y ∈ twoSidedEndomorphismSpan k tau := by
        rw [htauSpan]
        exact hyJ
      exact exists_postcomposition_of_mem_span_of_allowsTransit ht hySpan
    have hgenRing : ∀ y : End X, y ∈ Ring.jacobson (End X) →
        ∃ q : End X, y = q * tau := by
      intro y hyJ
      obtain ⟨q, hyq⟩ := hgenCat y hyJ
      refine ⟨q, ?_⟩
      change y.asHom = (q * tau).asHom
      simpa only [End.mul_def] using hyq
    refine ⟨ht, hgenCat, ?_⟩
    intro x hxJ hx0
    obtain ⟨n, hn, e, he, hxe⟩ :=
      exists_left_unit_times_power tau htauJ hgenRing hxJ hx0
    exact ⟨n, hn, e, he, by simpa only [End.mul_def] using congrArg End.asHom hxe⟩
  · right
    have hgenCat : ∀ y : End X, y ∈ Ring.jacobson (End X) →
        ∃ q : End X, y.asHom = q.asHom ≫ tau.asHom := by
      intro y hyJ
      have hySpan : y ∈ twoSidedEndomorphismSpan k tau := by
        rw [htauSpan]
        exact hyJ
      exact exists_precomposition_of_mem_span_of_allowsCotransit hc hySpan
    have hgenRing : ∀ y : End X, y ∈ Ring.jacobson (End X) →
        ∃ q : End X, y = tau * q := by
      intro y hyJ
      obtain ⟨q, hyq⟩ := hgenCat y hyJ
      refine ⟨q, ?_⟩
      change y.asHom = (tau * q).asHom
      simpa only [End.mul_def] using hyq
    refine ⟨hc, hgenCat, ?_⟩
    intro x hxJ hx0
    obtain ⟨n, hn, e, he, hxe⟩ :=
      exists_power_times_right_unit tau htauJ hgenRing hxJ hx0
    exact ⟨n, hn, e, he, by simpa only [End.mul_def] using congrArg End.asHom hxe⟩

/-- Clean data package for the local BGRS radical parameter used in closed-ray
chain calculations. -/
structure OrientedRadicalPowerParameter (X : C) where
  tau : End X
  mem_jacobson : tau ∈ Ring.jacobson (End X)
  ne_zero : tau ≠ 0
  span_eq : twoSidedEndomorphismSpan k tau =
    (Ring.jacobson (End X)).restrictScalars k
  power_factorization : HasOrientedRadicalPowerFactorization tau

/-- Every nonzero radical endomorphism has the same two-sided unit ray as a
positive power of an oriented local parameter. -/
theorem OrientedRadicalPowerParameter.exists_positive_power_unitRay_eq
    {X : C} (P : OrientedRadicalPowerParameter (k := k) X)
    {x : End X} (hxJ : x ∈ Ring.jacobson (End X)) (hx0 : x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧
      unitRay (P.tau ^ n).asHom = unitRay x.asHom := by
  rcases P.power_factorization with hT | hC
  · obtain ⟨n, hn, e, he, hxe⟩ := hT.factors x hxJ hx0
    refine ⟨n, hn, (unitRay_eq_iff _ _).2 ?_⟩
    letI : IsIso e.asHom := (isUnit_iff_isIso e).1 he
    exact ⟨Iso.refl X, asIso e.asHom, by simpa using hxe⟩
  · obtain ⟨n, hn, e, he, hxe⟩ := hC.factors x hxJ hx0
    refine ⟨n, hn, (unitRay_eq_iff _ _).2 ?_⟩
    letI : IsIso e.asHom := (isUnit_iff_isIso e).1 he
    exact ⟨asIso e.asHom, Iso.refl X, by simpa using hxe⟩

/-- An oriented endpoint parameter over an algebraically closed field is an
algebra generator: every endomorphism is a polynomial in `tau`. -/
theorem OrientedRadicalPowerParameter.adjoin_eq_top
    [IsAlgClosed k] {X : C} [Module.Finite k (End X)]
    [IsLocalRing (End X)] [IsArtinianRing (End X)]
    (P : OrientedRadicalPowerParameter (k := k) X) :
    Algebra.adjoin k ({P.tau} : Set (End X)) = ⊤ := by
  rcases P.power_factorization with hT | hC
  · apply algebra_adjoin_singleton_eq_top_of_left_radical_generator
      P.tau P.mem_jacobson
    intro x hxJ
    obtain ⟨q, hxq⟩ := hT.generates x hxJ
    refine ⟨q, ?_⟩
    change x.asHom = (q * P.tau).asHom
    simpa only [End.mul_def] using hxq
  · apply algebra_adjoin_singleton_eq_top_of_right_radical_generator
      P.tau P.mem_jacobson
    intro x hxJ
    obtain ⟨q, hxq⟩ := hC.generates x hxJ
    refine ⟨q, ?_⟩
    change x.asHom = (P.tau * q).asHom
    simpa only [End.mul_def] using hxq

/-- Explicit polynomial normal form supplied by the singleton-adjoin theorem. -/
theorem OrientedRadicalPowerParameter.exists_aeval_eq
    [IsAlgClosed k] {X : C} [Module.Finite k (End X)]
    [IsLocalRing (End X)] [IsArtinianRing (End X)]
    (P : OrientedRadicalPowerParameter (k := k) X) (a : End X) :
    ∃ p : Polynomial k, Polynomial.aeval P.tau p = a := by
  apply Algebra.adjoin_mem_exists_aeval k P.tau
  rw [P.adjoin_eq_top]
  trivial

/-- Consequently the endpoint ring is commutative, stated without installing
a global typeclass instance. -/
theorem OrientedRadicalPowerParameter.commute
    [IsAlgClosed k] {X : C} [Module.Finite k (End X)]
    [IsLocalRing (End X)] [IsArtinianRing (End X)]
    (P : OrientedRadicalPowerParameter (k := k) X) (a b : End X) :
    Commute a b := by
  have ha : a ∈ Algebra.adjoin k ({P.tau} : Set (End X)) := by
    rw [P.adjoin_eq_top]
    trivial
  have hb : b ∈ Algebra.adjoin k ({P.tau} : Set (End X)) := by
    rw [P.adjoin_eq_top]
    trivial
  exact Algebra.commute_of_mem_adjoin_singleton_of_commute hb
    (Algebra.commute_of_mem_adjoin_self ha).symm

theorem OrientedRadicalPowerParameter.mul_comm
    [IsAlgClosed k] {X : C} [Module.Finite k (End X)]
    [IsLocalRing (End X)] [IsArtinianRing (End X)]
    (P : OrientedRadicalPowerParameter (k := k) X) (a b : End X) :
    a * b = b * a :=
  (P.commute a b).eq

/-- Multiplying the radical parameter by a unit gives another algebra
generator. -/
theorem OrientedRadicalPowerParameter.adjoin_mul_unit_eq_top
    [IsAlgClosed k] {X : C} [Module.Finite k (End X)]
    [IsLocalRing (End X)] [IsArtinianRing (End X)]
    (P : OrientedRadicalPowerParameter (k := k) X)
    (e : End X) (he : IsUnit e) :
    Algebra.adjoin k ({P.tau * e} : Set (End X)) = ⊤ := by
  have hbJ : P.tau * e ∈ Ring.jacobson (End X) :=
    (Ring.jacobson (End X)).mul_mem_right e P.mem_jacobson
  apply algebra_adjoin_singleton_eq_top_of_left_radical_generator
    (P.tau * e) hbJ
  intro x hxJ
  have htauT : AllowsTransit P.tau := by
    intro a
    refine ⟨a, ?_⟩
    have h := congrArg End.asHom (P.mul_comm P.tau a)
    simpa only [End.mul_def] using h
  have hxSpan : x ∈ twoSidedEndomorphismSpan k P.tau := by
    rw [P.span_eq]
    exact hxJ
  obtain ⟨q, hxq⟩ :=
    exists_postcomposition_of_mem_span_of_allowsTransit htauT hxSpan
  let einv : End X := ↑(he.unit⁻¹)
  have hinv : einv * e = 1 := by
    dsimp [einv]
    calc
      (↑(he.unit⁻¹) : End X) * e =
          (↑(he.unit⁻¹) : End X) * (↑he.unit : End X) :=
        congrArg (fun z : End X ↦ (↑(he.unit⁻¹) : End X) * z)
          he.unit_spec.symm
      _ = 1 := Units.inv_mul he.unit
  refine ⟨q * einv, ?_⟩
  have hxqRing : x = q * P.tau := by
    change x.asHom = (q * P.tau).asHom
    simpa only [End.mul_def] using hxq
  rw [hxqRing]
  symm
  calc
    (q * einv) * (P.tau * e) = q * (einv * P.tau) * e := by
      simp only [mul_assoc]
    _ = q * (P.tau * einv) * e := by rw [P.mul_comm einv P.tau]
    _ = (q * P.tau) * (einv * e) := by simp only [mul_assoc]
    _ = q * P.tau := by rw [hinv, mul_one]

/-- If one endomorphism transfers across a morphism and generates the target
endomorphism algebra, then every target endomorphism transfers: the morphism
allows cotransit. -/
theorem allowsCotransit_of_transfer_of_adjoin_eq_top
    {X Y : C} (pi : X ⟶ Y) (rho : End X) (b : End Y)
    (hbgen : Algebra.adjoin k ({b} : Set (End Y)) = ⊤)
    (htransfer : rho.asHom ≫ pi = pi ≫ b.asHom) :
    AllowsCotransit pi := by
  intro c
  have hc : c ∈ Algebra.adjoin k ({b} : Set (End Y)) := by
    rw [hbgen]
    trivial
  induction hc using Algebra.adjoin_induction with
  | mem x hx =>
      have hxb : x = b := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨rho, htransfer.symm⟩
  | algebraMap r =>
      refine ⟨algebraMap k (End X) r, ?_⟩
      change pi ≫ (r • (𝟙 Y)) = (r • (𝟙 X)) ≫ pi
      simp
  | add x y _ _ hx hy =>
      obtain ⟨a, hxa⟩ := hx
      obtain ⟨d, hyd⟩ := hy
      refine ⟨a + d, ?_⟩
      change pi ≫ (x.asHom + y.asHom) =
        (a.asHom + d.asHom) ≫ pi
      rw [Preadditive.comp_add, Preadditive.add_comp, hxa, hyd]
  | mul x y _ _ hx hy =>
      obtain ⟨a, hxa⟩ := hx
      obtain ⟨d, hyd⟩ := hy
      refine ⟨a * d, ?_⟩
      change pi ≫ (y.asHom ≫ x.asHom) =
        (d.asHom ≫ a.asHom) ≫ pi
      calc
        pi ≫ (y.asHom ≫ x.asHom) = (pi ≫ y.asHom) ≫ x.asHom := by
          rw [Category.assoc]
        _ = (d.asHom ≫ pi) ≫ x.asHom := by rw [hyd]
        _ = d.asHom ≫ (pi ≫ x.asHom) := by rw [Category.assoc]
        _ = d.asHom ≫ (a.asHom ≫ pi) := by rw [hxa]
        _ = (d.asHom ≫ a.asHom) ≫ pi := by rw [Category.assoc]

/-- Source-dual counterpart of
`allowsCotransit_of_transfer_of_adjoin_eq_top`: if one algebra generator at
the source transfers across a morphism, then every source endomorphism does. -/
theorem allowsTransit_of_transfer_of_adjoin_eq_top
    {X Y : C} (pi : X ⟶ Y) (a : End X) (sigma : End Y)
    (hagen : Algebra.adjoin k ({a} : Set (End X)) = ⊤)
    (htransfer : a.asHom ≫ pi = pi ≫ sigma.asHom) :
    AllowsTransit pi := by
  intro c
  have hc : c ∈ Algebra.adjoin k ({a} : Set (End X)) := by
    rw [hagen]
    trivial
  induction hc using Algebra.adjoin_induction with
  | mem x hx =>
      have hxa : x = a := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨sigma, htransfer⟩
  | algebraMap r =>
      refine ⟨algebraMap k (End Y) r, ?_⟩
      change (r • (𝟙 X)) ≫ pi = pi ≫ (r • (𝟙 Y))
      simp
  | add x y _ _ hx hy =>
      obtain ⟨b, hxb⟩ := hx
      obtain ⟨d, hyd⟩ := hy
      refine ⟨b + d, ?_⟩
      change (x.asHom + y.asHom) ≫ pi =
        pi ≫ (b.asHom + d.asHom)
      rw [Preadditive.add_comp, Preadditive.comp_add, hxb, hyd]
  | mul x y _ _ hx hy =>
      obtain ⟨b, hxb⟩ := hx
      obtain ⟨d, hyd⟩ := hy
      refine ⟨b * d, ?_⟩
      change (y.asHom ≫ x.asHom) ≫ pi =
        pi ≫ (d.asHom ≫ b.asHom)
      calc
        (y.asHom ≫ x.asHom) ≫ pi = y.asHom ≫ (x.asHom ≫ pi) := by
          rw [Category.assoc]
        _ = y.asHom ≫ (pi ≫ b.asHom) := by rw [hxb]
        _ = (y.asHom ≫ pi) ≫ b.asHom := by rw [Category.assoc]
        _ = (pi ≫ d.asHom) ≫ b.asHom := by rw [hyd]
        _ = pi ≫ (d.asHom ≫ b.asHom) := by rw [Category.assoc]

/-- The source's `n ≥ 2` mechanism: an exponent-one transfer through a
unit-twisted endpoint parameter would make `pi` cotransit. -/
theorem two_le_exponent_of_transfer_of_not_allowsCotransit
    [IsAlgClosed k] {X Y : C} [Module.Finite k (End Y)]
    [IsLocalRing (End Y)] [IsArtinianRing (End Y)]
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (pi : X ⟶ Y) (rho : End X) (n : ℕ) (hn : 0 < n)
    (e : End Y) (he : IsUnit e)
    (htransfer : rho.asHom ≫ pi =
      pi ≫ (P.tau ^ n * e).asHom)
    (hnot : ¬ AllowsCotransit pi) : 2 ≤ n := by
  by_contra hn2
  have hn1 : n = 1 := by omega
  subst n
  have hbgen : Algebra.adjoin k ({P.tau ^ 1 * e} : Set (End Y)) = ⊤ := by
    simpa using P.adjoin_mul_unit_eq_top e he
  exact hnot
    (allowsCotransit_of_transfer_of_adjoin_eq_top
      pi rho (P.tau ^ 1 * e) hbgen htransfer)

/-- Source-dual `n ≥ 2` mechanism: an exponent-one transfer through a
unit-twisted source parameter would make `pi` transit. -/
theorem two_le_exponent_of_transfer_of_not_allowsTransit
    [IsAlgClosed k] {X Y : C} [Module.Finite k (End X)]
    [IsLocalRing (End X)] [IsArtinianRing (End X)]
    (P : OrientedRadicalPowerParameter (k := k) X)
    (pi : X ⟶ Y) (sigma : End Y) (n : ℕ) (hn : 0 < n)
    (e : End X) (he : IsUnit e)
    (htransfer : (e * P.tau ^ n).asHom ≫ pi =
      pi ≫ sigma.asHom)
    (hnot : ¬ AllowsTransit pi) : 2 ≤ n := by
  by_contra hn2
  have hn1 : n = 1 := by omega
  subst n
  have heq : e * P.tau ^ 1 = P.tau ^ 1 * e := by
    simpa using P.mul_comm e P.tau
  have hagen :
      Algebra.adjoin k ({e * P.tau ^ 1} : Set (End X)) = ⊤ := by
    rw [heq]
    simpa using P.adjoin_mul_unit_eq_top e he
  exact hnot
    (allowsTransit_of_transfer_of_adjoin_eq_top
      pi (e * P.tau ^ 1) sigma hagen htransfer)

/-- Polynomial generation upgrades the original chosen orientation: `tau`
allows transit in either case. -/
theorem OrientedRadicalPowerParameter.tau_allowsTransit
    [IsAlgClosed k] {X : C} [Module.Finite k (End X)]
    [IsLocalRing (End X)] [IsArtinianRing (End X)]
    (P : OrientedRadicalPowerParameter (k := k) X) :
    AllowsTransit P.tau := by
  intro a
  refine ⟨a, ?_⟩
  have h := congrArg End.asHom (P.mul_comm P.tau a)
  simpa only [End.mul_def] using h

/-- The dual upgrade: `tau` also allows cotransit. -/
theorem OrientedRadicalPowerParameter.tau_allowsCotransit
    [IsAlgClosed k] {X : C} [Module.Finite k (End X)]
    [IsLocalRing (End X)] [IsArtinianRing (End X)]
    (P : OrientedRadicalPowerParameter (k := k) X) :
    AllowsCotransit P.tau := by
  intro b
  refine ⟨b, ?_⟩
  have h := congrArg End.asHom (P.mul_comm b P.tau)
  simpa only [End.mul_def] using h

private theorem eq_zero_of_eq_postcomp_of_isNilpotent
    {X Y : C} {f : X ⟶ Y} {a : End Y} (ha : IsNilpotent a)
    (h : f = f ≫ a.asHom) : f = 0 := by
  have hu : IsUnit (1 - a) := ha.isUnit_one_sub
  haveI : IsIso ((1 - a).asHom) := (isUnit_iff_isIso _).1 hu
  have hz : f ≫ (1 - a).asHom = 0 := by
    change f ≫ ((𝟙 Y) - a.asHom) = 0
    rw [Preadditive.comp_sub, Category.comp_id]
    exact sub_eq_zero.mpr h
  apply (cancel_mono ((1 - a).asHom)).1
  simpa using hz

private theorem eq_zero_of_eq_precomp_of_isNilpotent
    {X Y : C} {f : X ⟶ Y} {a : End X} (ha : IsNilpotent a)
    (h : f = a.asHom ≫ f) : f = 0 := by
  have hu : IsUnit (1 - a) := ha.isUnit_one_sub
  haveI : IsIso ((1 - a).asHom) := (isUnit_iff_isIso _).1 hu
  have hz : (1 - a).asHom ≫ f = 0 := by
    change ((𝟙 X) - a.asHom) ≫ f = 0
    rw [Preadditive.sub_comp, Category.id_comp]
    exact sub_eq_zero.mpr h
  apply (cancel_epi ((1 - a).asHom)).1
  simpa using hz

/-- A nonzero postcomposition by a power of the local parameter is never a
BGRS exceptional zero; its representative-level ray product is the ordinary
composite. -/
theorem OrientedRadicalPowerParameter.bgrsProduct_postcompose_power_eq_comp
    {X Y : C} [IsAlgClosed k] [Module.Finite k (End Y)]
    [IsLocalRing (End Y)] [IsArtinianRing (End Y)]
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (f : X ⟶ Y) (n : ℕ) (hne : f ≫ (P.tau ^ n).asHom ≠ 0) :
    bgrsRayRepresentativeProduct f (P.tau ^ n).asHom =
      f ≫ (P.tau ^ n).asHom := by
  apply bgrsRayRepresentativeProduct_eq_comp_of_not_special
  rintro ⟨rho, hrho⟩
  have hfix : f ≫ (P.tau ^ n).asHom =
      (f ≫ (P.tau ^ n).asHom) ≫ rho.1.asHom := by
    calc
      f ≫ (P.tau ^ n).asHom =
          (f ≫ rho.1.asHom) ≫ (P.tau ^ n).asHom := hrho
      _ = f ≫ (rho.1.asHom ≫ (P.tau ^ n).asHom) := by
        rw [Category.assoc]
      _ = f ≫ ((P.tau ^ n).asHom ≫ rho.1.asHom) := by
        have hcomm := congrArg End.asHom (P.mul_comm rho.1 (P.tau ^ n))
        simpa only [End.mul_def] using
          congrArg (fun q ↦ f ≫ q) hcomm.symm
      _ = (f ≫ (P.tau ^ n).asHom) ≫ rho.1.asHom := by
        rw [Category.assoc]
  exact hne (eq_zero_of_eq_postcomp_of_isNilpotent
    (isNilpotent_of_mem_jacobson_of_isArtinian rho.2) hfix)

/-- Source-dual exceptional-zero exclusion for a nonzero precomposition by a
power of the local parameter. -/
theorem OrientedRadicalPowerParameter.bgrsProduct_precompose_power_eq_comp
    {X Y : C} [IsAlgClosed k] [Module.Finite k (End X)]
    [IsLocalRing (End X)] [IsArtinianRing (End X)]
    (P : OrientedRadicalPowerParameter (k := k) X)
    (g : X ⟶ Y) (n : ℕ) (hne : (P.tau ^ n).asHom ≫ g ≠ 0) :
    bgrsRayRepresentativeProduct (P.tau ^ n).asHom g =
      (P.tau ^ n).asHom ≫ g := by
  apply bgrsRayRepresentativeProduct_eq_comp_of_not_special
  rintro ⟨rho, hrho⟩
  have hfix : (P.tau ^ n).asHom ≫ g =
      rho.1.asHom ≫ ((P.tau ^ n).asHom ≫ g) := by
    calc
      (P.tau ^ n).asHom ≫ g =
          ((P.tau ^ n).asHom ≫ rho.1.asHom) ≫ g := hrho
      _ = (rho.1.asHom ≫ (P.tau ^ n).asHom) ≫ g := by
        have hcomm := congrArg End.asHom (P.mul_comm rho.1 (P.tau ^ n))
        simpa only [End.mul_def] using
          congrArg (fun q ↦ q ≫ g) hcomm
      _ = rho.1.asHom ≫ ((P.tau ^ n).asHom ≫ g) := by
        rw [Category.assoc]
  exact hne (eq_zero_of_eq_precomp_of_isNilpotent
    (isNilpotent_of_mem_jacobson_of_isArtinian rho.2) hfix)

/-- Every power of an oriented radical parameter allows transit; polynomial
generation makes the endpoint ring commutative. -/
theorem OrientedRadicalPowerParameter.power_allowsTransit
    [IsAlgClosed k] {X : C} [Module.Finite k (End X)]
    [IsLocalRing (End X)] [IsArtinianRing (End X)]
    (P : OrientedRadicalPowerParameter (k := k) X) (n : ℕ) :
    AllowsTransit (P.tau ^ n).asHom := by
  intro a
  refine ⟨a, ?_⟩
  have h := congrArg End.asHom (P.mul_comm (P.tau ^ n) a)
  simpa only [End.mul_def] using h

private theorem OrientedRadicalPowerParameter.power_succ_mem_span
    [IsAlgClosed k] {X : C} [Module.Finite k (End X)]
    [IsLocalRing (End X)] [IsArtinianRing (End X)]
    (P : OrientedRadicalPowerParameter (k := k) X) (n : ℕ) :
    (P.tau ^ (n + 1)).asHom ∈
      twoSidedEndomorphismSpan k (P.tau ^ n).asHom := by
  apply Submodule.subset_span
  refine ⟨𝟙 X, P.tau, ?_⟩
  simp only [Category.id_comp]
  have hcomm := P.mul_comm (P.tau ^ n) P.tau
  rw [pow_succ, hcomm]
  rfl

/-- Successive nonzero powers of an oriented radical parameter have strictly
descending principal two-sided spans. -/
theorem OrientedRadicalPowerParameter.power_succ_span_lt
    [IsAlgClosed k] {X : C} [Module.Finite k (End X)]
    [IsLocalRing (End X)] [IsArtinianRing (End X)]
    (P : OrientedRadicalPowerParameter (k := k) X) (n : ℕ)
    (hn : P.tau ^ n ≠ 0) :
    twoSidedEndomorphismSpan k (P.tau ^ (n + 1)).asHom <
      twoSidedEndomorphismSpan k (P.tau ^ n).asHom := by
  have hle := twoSidedEndomorphismSpan_le_of_mem
    (P.power_succ_mem_span n)
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hnmem : (P.tau ^ n).asHom ∈
      twoSidedEndomorphismSpan k (P.tau ^ (n + 1)).asHom := by
    rw [heq]
    exact mem_twoSidedEndomorphismSpan k (P.tau ^ n).asHom
  obtain ⟨b, hb⟩ :=
    exists_postcomposition_of_mem_span_of_allowsTransit
      (P.power_allowsTransit (n + 1)) hnmem
  have hring : P.tau ^ n = b * P.tau ^ (n + 1) := by
    apply End.ext
    simpa only [End.mul_def] using hb
  have hfix : P.tau ^ n = (b * P.tau) * P.tau ^ n := by
    calc
      P.tau ^ n = b * P.tau ^ (n + 1) := hring
      _ = b * (P.tau ^ n * P.tau) := by rw [pow_succ]
      _ = (b * P.tau) * P.tau ^ n := by
        rw [P.mul_comm (P.tau ^ n) P.tau]
        simp only [mul_assoc]
  have hrad : b * P.tau ∈ Ring.jacobson (End X) :=
    (Ring.jacobson (End X)).mul_mem_left b P.mem_jacobson
  have hzero : P.tau ^ n = 0 :=
    eq_zero_of_eq_mul_left_of_isNilpotent
      (isNilpotent_of_mem_jacobson_of_isArtinian hrad) hfix
  exact hn hzero

/-- Stable right extensions by successive powers of a local radical parameter
have strictly descending principal spans.  This is the representative-level
form of the stable-composition rule used in BGRS 3.4(d). -/
theorem OrientedRadicalPowerParameter.postcompose_power_succ_span_lt
    [IsAlgClosed k]
    [∀ T : C, Module.Finite k (End T)]
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [HasBGRSDistributiveHomStructure k C]
    {X Y : C} (f : X ⟶ Y)
    (P : OrientedRadicalPowerParameter (k := k) Y) (n : ℕ)
    (hlong : f ≫ (P.tau ^ (n + 1)).asHom ≠ 0)
    (hshort : f ≫ (P.tau ^ n).asHom ≠ 0) :
    twoSidedEndomorphismSpan k
        (f ≫ (P.tau ^ (n + 1)).asHom) <
      twoSidedEndomorphismSpan k (f ≫ (P.tau ^ n).asHom) := by
  have hmem : f ≫ (P.tau ^ (n + 1)).asHom ∈
      twoSidedEndomorphismSpan k (f ≫ (P.tau ^ n).asHom) := by
    apply Submodule.subset_span
    refine ⟨𝟙 X, P.tau, ?_⟩
    simp only [Category.id_comp, Category.assoc]
    have hcomm := P.mul_comm (P.tau ^ n) P.tau
    rw [pow_succ, hcomm]
    rfl
  have hle := twoSidedEndomorphismSpan_le_of_mem hmem
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hordinary : UnitRayEquivalent
      (f ≫ (P.tau ^ (n + 1)).asHom)
      (f ≫ (P.tau ^ n).asHom) :=
    unitRayEquivalent_of_twoSidedEndomorphismSpan_eq heq
  have hlongEq : bgrsRayRepresentativeProduct
      f (P.tau ^ (n + 1)).asHom =
      f ≫ (P.tau ^ (n + 1)).asHom :=
    P.bgrsProduct_postcompose_power_eq_comp f (n + 1) hlong
  have hshortEq : bgrsRayRepresentativeProduct f (P.tau ^ n).asHom =
      f ≫ (P.tau ^ n).asHom :=
    P.bgrsProduct_postcompose_power_eq_comp f n hshort
  have hlongProduct : bgrsRayRepresentativeProduct
      f (P.tau ^ (n + 1)).asHom ≠ 0 := by
    rw [hlongEq]
    exact hlong
  have hproduct : UnitRayEquivalent
      (bgrsRayRepresentativeProduct f (P.tau ^ (n + 1)).asHom)
      (bgrsRayRepresentativeProduct f (P.tau ^ n).asHom) := by
    rw [hlongEq, hshortEq]
    exact hordinary
  have hpowers : UnitRayEquivalent
      (P.tau ^ (n + 1)).asHom (P.tau ^ n).asHom :=
    bgrsRayRepresentativeProduct_cancel_left_of_bgrsDistributiveHomStructure
      (k := k) (C := C) f (P.tau ^ (n + 1)).asHom
        (P.tau ^ n).asHom hproduct hlongProduct
  have hpowspan : twoSidedEndomorphismSpan k (P.tau ^ (n + 1)).asHom =
      twoSidedEndomorphismSpan k (P.tau ^ n).asHom :=
    twoSidedEndomorphismSpan_eq_of_unitRayEquivalent k hpowers
  have hpown : P.tau ^ n ≠ 0 := by
    intro hzero
    apply hshort
    rw [hzero]
    change f ≫ (0 : Y ⟶ Y) = 0
    simp
  exact (P.power_succ_span_lt n hpown).ne hpowspan

/-- Source-dual stable-composition rule for successive powers of a local
radical parameter. -/
theorem OrientedRadicalPowerParameter.precompose_power_succ_span_lt
    [IsAlgClosed k]
    [∀ T : C, Module.Finite k (End T)]
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [HasBGRSDistributiveHomStructure k C]
    {X Y : C} (g : X ⟶ Y)
    (P : OrientedRadicalPowerParameter (k := k) X) (n : ℕ)
    (hlong : (P.tau ^ (n + 1)).asHom ≫ g ≠ 0)
    (hshort : (P.tau ^ n).asHom ≫ g ≠ 0) :
    twoSidedEndomorphismSpan k
        ((P.tau ^ (n + 1)).asHom ≫ g) <
      twoSidedEndomorphismSpan k ((P.tau ^ n).asHom ≫ g) := by
  have hmem : (P.tau ^ (n + 1)).asHom ≫ g ∈
      twoSidedEndomorphismSpan k ((P.tau ^ n).asHom ≫ g) := by
    apply Submodule.subset_span
    refine ⟨P.tau, 𝟙 Y, ?_⟩
    simp only [Category.comp_id, ← Category.assoc]
    rw [pow_succ, End.mul_def]
  have hle := twoSidedEndomorphismSpan_le_of_mem hmem
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hordinary : UnitRayEquivalent
      ((P.tau ^ (n + 1)).asHom ≫ g)
      ((P.tau ^ n).asHom ≫ g) :=
    unitRayEquivalent_of_twoSidedEndomorphismSpan_eq heq
  have hlongEq : bgrsRayRepresentativeProduct
      (P.tau ^ (n + 1)).asHom g =
      (P.tau ^ (n + 1)).asHom ≫ g :=
    P.bgrsProduct_precompose_power_eq_comp g (n + 1) hlong
  have hshortEq : bgrsRayRepresentativeProduct (P.tau ^ n).asHom g =
      (P.tau ^ n).asHom ≫ g :=
    P.bgrsProduct_precompose_power_eq_comp g n hshort
  have hlongProduct : bgrsRayRepresentativeProduct
      (P.tau ^ (n + 1)).asHom g ≠ 0 := by
    rw [hlongEq]
    exact hlong
  have hproduct : UnitRayEquivalent
      (bgrsRayRepresentativeProduct (P.tau ^ (n + 1)).asHom g)
      (bgrsRayRepresentativeProduct (P.tau ^ n).asHom g) := by
    rw [hlongEq, hshortEq]
    exact hordinary
  have hpowers : UnitRayEquivalent
      (P.tau ^ (n + 1)).asHom (P.tau ^ n).asHom :=
    bgrsRayRepresentativeProduct_cancel_right_of_bgrsDistributiveHomStructure
      (k := k) (C := C) (P.tau ^ (n + 1)).asHom
        (P.tau ^ n).asHom g hproduct hlongProduct
  have hpowspan : twoSidedEndomorphismSpan k (P.tau ^ (n + 1)).asHom =
      twoSidedEndomorphismSpan k (P.tau ^ n).asHom :=
    twoSidedEndomorphismSpan_eq_of_unitRayEquivalent k hpowers
  have hpown : P.tau ^ n ≠ 0 := by
    intro hzero
    apply hshort
    rw [hzero]
    change (0 : X ⟶ X) ≫ g = 0
    simp
  exact (P.power_succ_span_lt n hpown).ne hpowspan

/-- A nonzero parameter which generates the whole endomorphism radical does
not lie in its square.  Otherwise its two-sided span would put the whole
radical in its square; nilpotence would then force the radical, and hence the
parameter, to vanish. -/
theorem OrientedRadicalPowerParameter.tau_not_mem_jacobson_sq
    {X : C} [IsArtinianRing (End X)]
    (P : OrientedRadicalPowerParameter (k := k) X) :
    P.tau ∉ (Ring.jacobson (End X)) ^ 2 := by
  intro htauSq
  let J : Ideal (End X) := Ring.jacobson (End X)
  have hJle : J ≤ J ^ 2 := by
    intro a ha
    have haSpan : a ∈ twoSidedEndomorphismSpan k P.tau := by
      rw [P.span_eq]
      exact ha
    apply (show twoSidedEndomorphismSpan k P.tau ≤
        (J ^ 2).restrictScalars k from ?_) haSpan
    apply Submodule.span_le.2
    rintro a ⟨l, r, rfl⟩
    change (End.of ((l.asHom ≫ P.tau.asHom) ≫ r.asHom)) ∈ J ^ 2
    have hmem : r * (P.tau * l) ∈ J ^ 2 :=
      (J ^ 2).mul_mem_left r ((J ^ 2).mul_mem_right l htauSq)
    simpa only [J, End.mul_def, Category.assoc] using hmem
  have hJ2le : J ^ 2 ≤ J := Ideal.pow_le_self (by omega)
  have hJ : J ^ 2 = J := le_antisymm hJ2le hJle
  have hJmul : J * J = J := by
    simpa only [Submodule.pow_succ, Submodule.pow_zero,
      Submodule.one_mul] using hJ
  have hpow : ∀ n : ℕ, J ^ (Nat.succ n) = J := by
    intro n
    induction n with
    | zero => simpa using Submodule.pow_one J
    | succ n ih =>
        calc
          J ^ (Nat.succ (Nat.succ n)) =
              J ^ (Nat.succ n) * J := by
            simpa only [Nat.succ_eq_add_one] using
              (Submodule.pow_succ (M := J) (n := Nat.succ n))
          _ = J * J := by rw [ih]
          _ = J := hJmul
  obtain ⟨N, hN⟩ :=
    IsArtinianRing.isNilpotent_jacobson_bot (R := End X)
  rw [Ideal.jacobson_bot] at hN
  have hNpos : 0 < N := by
    by_contra hnot
    have hN0 : N = 0 := Nat.eq_zero_of_not_pos hnot
    subst N
    have htopBot : (⊤ : Ideal (End X)) = ⊥ := by
      simpa only [Submodule.pow_zero, Ideal.one_eq_top,
        Ideal.zero_eq_bot] using hN
    have htauBot : P.tau ∈ (⊥ : Ideal (End X)) := by
      rw [← htopBot]
      simp
    exact P.ne_zero (by simpa using htauBot)
  have hJbot : J = ⊥ := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt hNpos)
    have hN' : J ^ (Nat.succ n) = ⊥ := by
      simpa [J] using hN
    exact (hpow n).symm.trans hN'
  have htauBot : P.tau ∈ (⊥ : Ideal (End X)) := by
    rw [← hJbot]
    exact P.mem_jacobson
  exact P.ne_zero (by simpa using htauBot)

/-- A nonzero radical element in transit-oriented power normal form has
exponent at least two as soon as it belongs to the radical square. -/
theorem OrientedRadicalPowerParameter.two_le_transitExponent_of_mem_sq
    {X : C} [IsArtinianRing (End X)]
    (P : OrientedRadicalPowerParameter (k := k) X)
    {a : End X} (haSq : a ∈ (Ring.jacobson (End X)) ^ 2)
    (_ha0 : a ≠ 0) (n : ℕ) (hn : 0 < n)
    (e : End X) (he : IsUnit e)
    (hae : a.asHom = (P.tau ^ n).asHom ≫ e.asHom) :
    2 ≤ n := by
  by_contra hn2
  have hn1 : n = 1 := by omega
  subst n
  have haRing : a = e * P.tau := by
    apply End.ext
    simpa only [End.mul_def, pow_one] using hae
  let ei : End X := ↑(he.unit⁻¹)
  have hei : ei * e = 1 := by
    dsimp [ei]
    calc
      (↑(he.unit⁻¹) : End X) * e =
          (↑(he.unit⁻¹) : End X) * (↑he.unit : End X) := by
        rw [he.unit_spec]
      _ = 1 := Units.inv_mul he.unit
  have hmem : ei * a ∈ (Ring.jacobson (End X)) ^ 2 :=
    (Ring.jacobson (End X) ^ 2).mul_mem_left ei haSq
  have heita : ei * a = P.tau := by
    rw [haRing, ← mul_assoc, hei, one_mul]
  rw [heita] at hmem
  exact P.tau_not_mem_jacobson_sq hmem

/-- Source-dual exponent bound for cotransit-oriented power normal form. -/
theorem OrientedRadicalPowerParameter.two_le_cotransitExponent_of_mem_sq
    {X : C} [IsArtinianRing (End X)]
    (P : OrientedRadicalPowerParameter (k := k) X)
    {a : End X} (haSq : a ∈ (Ring.jacobson (End X)) ^ 2)
    (_ha0 : a ≠ 0) (n : ℕ) (hn : 0 < n)
    (e : End X) (he : IsUnit e)
    (hae : a.asHom = e.asHom ≫ (P.tau ^ n).asHom) :
    2 ≤ n := by
  by_contra hn2
  have hn1 : n = 1 := by omega
  subst n
  have haRing : a = P.tau * e := by
    apply End.ext
    simpa only [End.mul_def, pow_one] using hae
  let ei : End X := ↑(he.unit⁻¹)
  have hei : e * ei = 1 := by
    dsimp [ei]
    calc
      e * (↑(he.unit⁻¹) : End X) =
          (↑he.unit : End X) * (↑(he.unit⁻¹) : End X) := by
        rw [he.unit_spec]
      _ = 1 := Units.mul_inv he.unit
  have hmem : a * ei ∈ (Ring.jacobson (End X)) ^ 2 :=
    (Ring.jacobson (End X) ^ 2).mul_mem_right ei haSq
  have hatei : a * ei = P.tau := by
    rw [haRing, mul_assoc, hei, mul_one]
  rw [hatei] at hmem
  exact P.tau_not_mem_jacobson_sq hmem

/-- Over an algebraically closed field, every endpoint parameter admits the
transit-oriented generator and power factorization, irrespective of which
orientation was initially selected. -/
theorem OrientedRadicalPowerParameter.transitData
    [IsAlgClosed k] {X : C} [Module.Finite k (End X)]
    [IsLocalRing (End X)] [IsArtinianRing (End X)]
    (P : OrientedRadicalPowerParameter (k := k) X) :
    TransitRadicalPowerData P.tau where
  allows_transit := P.tau_allowsTransit
  generates := by
    intro x hxJ
    have hxSpan : x ∈ twoSidedEndomorphismSpan k P.tau := by
      rw [P.span_eq]
      exact hxJ
    exact exists_postcomposition_of_mem_span_of_allowsTransit
      P.tau_allowsTransit hxSpan
  factors := by
    intro x hxJ hx0
    have hgen : ∀ y : End X, y ∈ Ring.jacobson (End X) →
        ∃ q : End X, y = q * P.tau := by
      intro y hyJ
      have hySpan : y ∈ twoSidedEndomorphismSpan k P.tau := by
        rw [P.span_eq]
        exact hyJ
      obtain ⟨q, hyq⟩ :=
        exists_postcomposition_of_mem_span_of_allowsTransit
          P.tau_allowsTransit hySpan
      refine ⟨q, ?_⟩
      change y.asHom = (q * P.tau).asHom
      simpa only [End.mul_def] using hyq
    obtain ⟨n, hn, e, he, hxe⟩ :=
      exists_left_unit_times_power P.tau P.mem_jacobson hgen hxJ hx0
    exact ⟨n, hn, e, he,
      by simpa only [End.mul_def] using congrArg End.asHom hxe⟩

/-- Dual orientation upgrade. -/
theorem OrientedRadicalPowerParameter.cotransitData
    [IsAlgClosed k] {X : C} [Module.Finite k (End X)]
    [IsLocalRing (End X)] [IsArtinianRing (End X)]
    (P : OrientedRadicalPowerParameter (k := k) X) :
    CotransitRadicalPowerData P.tau where
  allows_cotransit := P.tau_allowsCotransit
  generates := by
    intro x hxJ
    have hxSpan : x ∈ twoSidedEndomorphismSpan k P.tau := by
      rw [P.span_eq]
      exact hxJ
    exact exists_precomposition_of_mem_span_of_allowsCotransit
      P.tau_allowsCotransit hxSpan
  factors := by
    intro x hxJ hx0
    have hgen : ∀ y : End X, y ∈ Ring.jacobson (End X) →
        ∃ q : End X, y = P.tau * q := by
      intro y hyJ
      have hySpan : y ∈ twoSidedEndomorphismSpan k P.tau := by
        rw [P.span_eq]
        exact hyJ
      obtain ⟨q, hyq⟩ :=
        exists_precomposition_of_mem_span_of_allowsCotransit
          P.tau_allowsCotransit hySpan
      refine ⟨q, ?_⟩
      change y.asHom = (P.tau * q).asHom
      simpa only [End.mul_def] using hyq
    obtain ⟨n, hn, e, he, hxe⟩ :=
      exists_power_times_right_unit P.tau P.mem_jacobson hgen hxJ hx0
    exact ⟨n, hn, e, he,
      by simpa only [End.mul_def] using congrArg End.asHom hxe⟩

/-- A maximal Hom generator whose target coefficient is in the aligned
transit-oriented power normal form.  Exponent zero is the unit-coefficient
case; positive exponents are precisely the radical-coefficient cases produced
by `TransitRadicalPowerData.factors`. -/
structure TargetPowerHomNormalForm (X Y : C) (tau : End Y) where
  pi : X ⟶ Y
  full_span : twoSidedEndomorphismSpan k pi = ⊤
  allows_transit : AllowsTransit pi
  tau_mem_jacobson : tau ∈ Ring.jacobson (End Y)
  normal_form : ∀ f : X ⟶ Y, f ≠ 0 →
    ∃ n : ℕ, ∃ e : End Y, IsUnit e ∧
      f = (pi ≫ (tau ^ n).asHom) ≫ e.asHom

/-- The source-dual maximal Hom presentation, aligned with cotransit at the
source endpoint. -/
structure SourcePowerHomNormalForm (X Y : C) (tau : End X) where
  pi : X ⟶ Y
  full_span : twoSidedEndomorphismSpan k pi = ⊤
  allows_cotransit : AllowsCotransit pi
  tau_mem_jacobson : tau ∈ Ring.jacobson (End X)
  normal_form : ∀ f : X ⟶ Y, f ≠ 0 →
    ∃ n : ℕ, ∃ e : End X, IsUnit e ∧
      f = e.asHom ≫ ((tau ^ n).asHom ≫ pi)

/-- Build the target-power Hom presentation from an aligned maximal generator
and target radical parameter. -/
def targetPowerHomNormalForm_of_aligned
    {X Y : C} [IsLocalRing (End Y)] [IsArtinianRing (End Y)]
    (pi : X ⟶ Y) (hpiSpan : twoSidedEndomorphismSpan k pi = ⊤)
    (hpiT : AllowsTransit pi)
    (tau : End Y) (htauJ : tau ∈ Ring.jacobson (End Y))
    (htauT : TransitRadicalPowerData tau) :
    TargetPowerHomNormalForm (k := k) X Y tau where
  pi := pi
  full_span := hpiSpan
  allows_transit := hpiT
  tau_mem_jacobson := htauJ
  normal_form := by
    intro f hf0
    have hfSpan : f ∈ twoSidedEndomorphismSpan k pi := by
      rw [hpiSpan]
      trivial
    obtain ⟨b, hfb⟩ :=
      exists_postcomposition_of_mem_span_of_allowsTransit hpiT hfSpan
    by_cases hbU : IsUnit b
    · exact ⟨0, b, hbU, by simpa using hfb⟩
    · have hbJ : b ∈ Ring.jacobson (End Y) :=
        (mem_ringJacobson_iff_not_isUnit (End Y) b).2 hbU
      have hb0 : b ≠ 0 := by
        intro hb
        subst b
        change f = pi ≫ (0 : Y ⟶ Y) at hfb
        exact hf0 (by simpa using hfb)
      obtain ⟨n, _hn, e, he, hbe⟩ := htauT.factors b hbJ hb0
      refine ⟨n, e, he, ?_⟩
      calc
        f = pi ≫ b.asHom := hfb
        _ = pi ≫ ((tau ^ n).asHom ≫ e.asHom) := by rw [hbe]
        _ = (pi ≫ (tau ^ n).asHom) ≫ e.asHom := by
          rw [Category.assoc]

/-- Build the source-power Hom presentation from an aligned maximal generator
and source radical parameter. -/
def sourcePowerHomNormalForm_of_aligned
    {X Y : C} [IsLocalRing (End X)] [IsArtinianRing (End X)]
    (pi : X ⟶ Y) (hpiSpan : twoSidedEndomorphismSpan k pi = ⊤)
    (hpiC : AllowsCotransit pi)
    (tau : End X) (htauJ : tau ∈ Ring.jacobson (End X))
    (htauC : CotransitRadicalPowerData tau) :
    SourcePowerHomNormalForm (k := k) X Y tau where
  pi := pi
  full_span := hpiSpan
  allows_cotransit := hpiC
  tau_mem_jacobson := htauJ
  normal_form := by
    intro f hf0
    have hfSpan : f ∈ twoSidedEndomorphismSpan k pi := by
      rw [hpiSpan]
      trivial
    obtain ⟨a, hfa⟩ :=
      exists_precomposition_of_mem_span_of_allowsCotransit hpiC hfSpan
    by_cases haU : IsUnit a
    · exact ⟨0, a, haU, by simpa using hfa⟩
    · have haJ : a ∈ Ring.jacobson (End X) :=
        (mem_ringJacobson_iff_not_isUnit (End X) a).2 haU
      have ha0 : a ≠ 0 := by
        intro ha
        subst a
        change f = (0 : X ⟶ X) ≫ pi at hfa
        exact hf0 (by simpa using hfa)
      obtain ⟨n, _hn, e, he, hae⟩ := htauC.factors a haJ ha0
      refine ⟨n, e, he, ?_⟩
      calc
        f = a.asHom ≫ pi := hfa
        _ = (e.asHom ≫ (tau ^ n).asHom) ≫ pi := by rw [hae]
        _ = e.asHom ≫ ((tau ^ n).asHom ≫ pi) := by
          rw [Category.assoc]

/-- A maximal Hom space has one of the two source-aligned BGRS power normal
forms.  Polynomial generation of the endpoint rings removes the apparent
orientation mismatch: either endpoint parameter is available in both
orientations. -/
abbrev OrientedHomPowerNormalForm
    (X Y : C)
    (PX : OrientedRadicalPowerParameter (k := k) X)
    (PY : OrientedRadicalPowerParameter (k := k) Y) :=
  TargetPowerHomNormalForm (k := k) X Y PY.tau ⊕
    SourcePowerHomNormalForm (k := k) X Y PX.tau

/-- The endpoint-case orientation used in BGRS Lemma 2.6: take the
target/transit normal form whenever the chosen maximal Hom generator allows
transit; the source/cotransit alternative then records that transit is
genuinely prohibited. -/
abbrev PreferredOrientedHomPowerNormalForm
    (X Y : C)
    (PX : OrientedRadicalPowerParameter (k := k) X)
    (PY : OrientedRadicalPowerParameter (k := k) Y) :=
  TargetPowerHomNormalForm (k := k) X Y PY.tau ⊕
    { H : SourcePowerHomNormalForm (k := k) X Y PX.tau //
      ¬ AllowsTransit H.pi }

/-- Choose a maximal Hom generator and equip it with an exact endpoint-power
normal form. -/
theorem nonempty_orientedHomPowerNormalForm
    [IsAlgClosed k]
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [HasBGRSDistributiveHomStructure k C]
    (X Y : C) [Module.Finite k (End X)] [Module.Finite k (End Y)]
    [Module.Finite k (X ⟶ Y)]
    (PX : OrientedRadicalPowerParameter (k := k) X)
    (PY : OrientedRadicalPowerParameter (k := k) Y) :
    Nonempty (OrientedHomPowerNormalForm (k := k) X Y PX PY) := by
  obtain ⟨pi, hpiSpan⟩ :=
    exists_full_twoSidedEndomorphismSpan (k := k) (C := C) X Y
  rcases HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := C) pi with hpiT | hpiC
  · exact ⟨Sum.inl (targetPowerHomNormalForm_of_aligned
      pi hpiSpan hpiT PY.tau PY.mem_jacobson PY.transitData)⟩
  · exact ⟨Sum.inr (sourcePowerHomNormalForm_of_aligned
      pi hpiSpan hpiC PX.tau PX.mem_jacobson PX.cotransitData)⟩

/-- Choose the BGRS endpoint normal form with a genuine transit prohibition
attached to the source-oriented branch.  This is the precise case split used
when a positive target loop must either remain at the target or transfer to a
source power of exponent at least two. -/
theorem nonempty_preferredOrientedHomPowerNormalForm
    [IsAlgClosed k]
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [HasBGRSDistributiveHomStructure k C]
    (X Y : C) [Module.Finite k (End X)] [Module.Finite k (End Y)]
    [Module.Finite k (X ⟶ Y)]
    (PX : OrientedRadicalPowerParameter (k := k) X)
    (PY : OrientedRadicalPowerParameter (k := k) Y) :
    Nonempty (PreferredOrientedHomPowerNormalForm (k := k) X Y PX PY) := by
  obtain ⟨pi, hpiSpan⟩ :=
    exists_full_twoSidedEndomorphismSpan (k := k) (C := C) X Y
  by_cases hpiT : AllowsTransit pi
  · exact ⟨Sum.inl (targetPowerHomNormalForm_of_aligned
      pi hpiSpan hpiT PY.tau PY.mem_jacobson PY.transitData)⟩
  · have hpiC : AllowsCotransit pi :=
      (HasBGRSDistributiveHomStructure.transit_or_cotransit
        (k := k) (C := C) pi).resolve_left hpiT
    exact ⟨Sum.inr ⟨sourcePowerHomNormalForm_of_aligned
      pi hpiSpan hpiC PX.tau PX.mem_jacobson PX.cotransitData, hpiT⟩⟩

/-- Package the span statement and the BGRS orientation as an operational
radical-power parameter. -/
def orientedRadicalPowerParameter_of_span_eq
    {X : C} [IsLocalRing (End X)] [IsArtinianRing (End X)]
    (tau : End X) (htauJ : tau ∈ Ring.jacobson (End X))
    (htau0 : tau ≠ 0)
    (htauSpan : twoSidedEndomorphismSpan k tau =
      (Ring.jacobson (End X)).restrictScalars k)
    (horient : AllowsTransit tau ∨ AllowsCotransit tau) :
    OrientedRadicalPowerParameter (k := k) X where
  tau := tau
  mem_jacobson := htauJ
  ne_zero := htau0
  span_eq := htauSpan
  power_factorization :=
    hasOrientedRadicalPowerFactorization_of_span_eq tau htauJ htauSpan horient

/-- The maximal-radical-span construction supplies an actual oriented power
parameter as soon as the endomorphism radical is nonzero. -/
theorem nonempty_orientedRadicalPowerParameter_of_nonzero_radical
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [HasBGRSDistributiveHomStructure k C]
    (X : C) [Module.Finite k (X ⟶ X)]
    (f0 : End X) (hf0J : f0 ∈ Ring.jacobson (End X)) (hf0 : f0 ≠ 0) :
    Nonempty (OrientedRadicalPowerParameter (k := k) X) := by
  obtain ⟨tau, htauJ, htau0, htauSpan⟩ :=
    exists_radical_twoSidedEndomorphismSpan_eq
      (k := k) (C := C) X f0 hf0J hf0
  refine ⟨orientedRadicalPowerParameter_of_span_eq tau htauJ htau0 ?_ ?_⟩
  · exact htauSpan
  · exact HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := C) tau


end LargeIndecomposable.ClosedZigzagTransfer
