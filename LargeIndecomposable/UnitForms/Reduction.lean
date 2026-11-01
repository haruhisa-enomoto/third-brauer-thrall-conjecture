module

public import LargeIndecomposable.UnitForms.Inflation

/-!
# Inflating a corank-one nonnegative form to a graph form

`Rad1 q y`: `q` is nonnegative, `y ≫ 0` is a radical vector, and `q` vanishes only on
rational multiples of `y`. Inflations preserve this, with `y ↦ y + y_b e_a`
(`Rad1.inflate`). Since the off-diagonal coefficients of a nonnegative form lie in
`[-2, 2]`, only finitely many forms occur, and the radical vector strictly grows; so
repeated inflation ends at a form with no coefficient `+1` (`exists_terminal`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.Forms

open Finset

namespace UnitForm

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Corank one with a sincere positive radical vector `y`. -/
def Rad1 (q : UnitForm ι) (y : ι → ℤ) : Prop :=
  (∀ x, 0 ≤ q.val x) ∧ (∀ a, 0 < y a) ∧ (∀ x, q.B y x = 0) ∧
    ∀ x, q.val x = 0 → ∀ c d, y c * x d = x c * y d

lemma Rad1.of_exists {q : UnitForm ι} {y : ι → ℤ} (hnn : ∀ x, 0 ≤ q.val x) (hy : ∀ a, 0 < y a)
    (hrad : ∀ x, q.B y x = 0) (hz : ∀ x, q.val x = 0 → ∃ a, y a • x = x a • y) : q.Rad1 y := by
  refine ⟨hnn, hy, hrad, fun x hx c d ↦ ?_⟩
  obtain ⟨a, ha⟩ := hz x hx
  have h1 := congrFun ha d
  have h2 := congrFun ha c
  simp only [Pi.smul_apply, smul_eq_mul] at h1 h2
  have : y a * (y c * x d - x c * y d) = 0 := by
    have e : y a * (y c * x d - x c * y d) = y c * (y a * x d) - y d * (y a * x c) := by ring
    rw [e, h1, h2]; ring
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (hy a).ne'
  · linarith

/-- A critical form in at least three variables has `Rad1`. -/
theorem Critical.rad1 (q : UnitForm ι) (hq : q.Critical) (hn : 3 ≤ Fintype.card ι) :
    ∃ y, q.Rad1 y := by
  obtain ⟨z, hz, hrad, h⟩ := Critical.nonneg q hq hn
  exact ⟨z, Rad1.of_exists (fun x ↦ (h x).1) hz hrad fun x hx ↦ (h x).2 hx⟩

variable {q : UnitForm ι}

lemma Rad1.val_eq_zero {y : ι → ℤ} (h : q.Rad1 y) : q.val y = 0 := by
  have := q.two_mul_val y; rw [h.2.2.1] at this; omega

/-- **Inflation** preserves `Rad1`, with radical vector `y + y_b e_a`. -/
theorem Rad1.inflate {y : ι → ℤ} (h : q.Rad1 y) {a b : ι} (hab : a ≠ b) (hc : q.c a b = 1) :
    (q.inflate hab hc).Rad1 (deflMap a b y) := by
  obtain ⟨hnn, hy, hrad, hz⟩ := h
  refine ⟨fun x ↦ by rw [inflate_val]; exact hnn _, fun u ↦ ?_, q.inflate_radical hab hc y hrad,
    fun x hx u v ↦ ?_⟩
  · simp only [deflMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Pi.single_apply]
    split_ifs
    · have := hy u; have := hy b; linarith
    · simpa using hy u
  · rw [inflate_val] at hx
    have key := hz _ hx
    set w := inflMap a b x with hw
    have hx' : x = deflMap a b w := (deflMap_inflMap hab x).symm
    rw [hx']
    simp only [deflMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Pi.single_apply]
    have k1 := key u v
    have k2 := key u b
    have k3 := key b v
    have k4 := key b b
    split_ifs <;> nlinarith

lemma val_eq_zero_of_radical (q : UnitForm ι) {z : ι → ℤ} (hz : ∀ x, q.B z x = 0) :
    q.val z = 0 := by
  have := q.two_mul_val z; rw [hz] at this; omega

/-- The least sum of a positive radical vector (`0` if there is none). -/
def rsum (q : UnitForm ι) : ℕ := by
  classical
  exact if h : ∃ s : ℕ, ∃ z : ι → ℤ, (∀ a, 0 < z a) ∧ (∀ x, q.B z x = 0) ∧ (∑ a, z a) = s
    then Nat.find h else 0

lemma rsum_spec (q : UnitForm ι) {y : ι → ℤ} (hy : ∀ a, 0 < y a) (hrad : ∀ x, q.B y x = 0) :
    ∃ z : ι → ℤ, (∀ a, 0 < z a) ∧ (∀ x, q.B z x = 0) ∧ (∑ a, z a) = q.rsum := by
  classical
  have h : ∃ s : ℕ, ∃ z : ι → ℤ, (∀ a, 0 < z a) ∧ (∀ x, q.B z x = 0) ∧ (∑ a, z a) = s :=
    ⟨(∑ a, y a).toNat, y, hy, hrad, by
      rw [Int.toNat_of_nonneg (Finset.sum_nonneg fun a _ ↦ (hy a).le)]⟩
  unfold rsum
  rw [dif_pos h]
  exact Nat.find_spec h

lemma rsum_le (q : UnitForm ι) {z : ι → ℤ} (hz : ∀ a, 0 < z a) (hrad : ∀ x, q.B z x = 0) :
    (q.rsum : ℤ) ≤ ∑ a, z a := by
  classical
  have h : ∃ s : ℕ, ∃ z : ι → ℤ, (∀ a, 0 < z a) ∧ (∀ x, q.B z x = 0) ∧ (∑ a, z a) = s :=
    ⟨(∑ a, z a).toNat, z, hz, hrad, by
      rw [Int.toNat_of_nonneg (Finset.sum_nonneg fun a _ ↦ (hz a).le)]⟩
  unfold rsum
  rw [dif_pos h]
  have := Nat.find_min' h ⟨z, hz, hrad, (Int.toNat_of_nonneg
    (Finset.sum_nonneg fun a _ ↦ (hz a).le)).symm⟩
  have h0 : 0 ≤ ∑ a, z a := Finset.sum_nonneg fun a _ ↦ (hz a).le
  omega

/-- A positive radical vector of an inflation maps to a positive radical vector of `q`. -/
lemma Rad1.of_inflate {y : ι → ℤ} (h : q.Rad1 y) {a b : ι} (hab : a ≠ b) (hc : q.c a b = 1)
    {z1 : ι → ℤ} (hz1 : ∀ u, 0 < z1 u) (hrad1 : ∀ x, (q.inflate hab hc).B z1 x = 0) :
    (∀ x, q.B (inflMap a b z1) x = 0) ∧ (∀ u, 0 < inflMap a b z1 u) ∧ z1 b < z1 a := by
  have hprop := (h.inflate hab hc).2.2.2 z1 (val_eq_zero_of_radical _ hrad1)
  have hradT : ∀ x, q.B (inflMap a b z1) x = 0 := by
    intro x
    have := hrad1 (deflMap a b x)
    unfold UnitForm.inflate at this
    rwa [pullback_B, inflMap_deflMap hab] at this
  have hy := h.2.1
  have hab' : z1 b < z1 a := by
    have e := hprop b a
    simp [deflMap, Pi.single_apply, Ne.symm hab] at e
    -- `y_b z1_a = z1_b (y_a + y_b)`
    by_contra hcon
    push Not at hcon
    have h1 : y b * z1 a ≤ y b * z1 b := mul_le_mul_of_nonneg_left hcon (hy b).le
    have h2 := mul_pos (hz1 b) (hy a)
    nlinarith
  refine ⟨hradT, fun u ↦ ?_, hab'⟩
  simp only [inflMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Pi.single_apply]
  split_ifs with hu
  · subst hu; linarith
  · simpa using hz1 u

/-- An inflation strictly increases `rsum`. -/
lemma rsum_lt_inflate {y : ι → ℤ} (h : q.Rad1 y) {a b : ι} (hab : a ≠ b) (hc : q.c a b = 1) :
    q.rsum < (q.inflate hab hc).rsum := by
  have h1 := h.inflate hab hc
  obtain ⟨z1, hz1, hrad1, hsum1⟩ := (q.inflate hab hc).rsum_spec h1.2.1 h1.2.2.1
  obtain ⟨hradT, hposT, -⟩ := h.of_inflate hab hc hz1 hrad1
  have hle := q.rsum_le hposT hradT
  have hsumT : ∑ u, inflMap a b z1 u = (∑ u, z1 u) - z1 b := by
    simp [inflMap, Finset.sum_sub_distrib, Pi.single_apply]
  rw [hsumT, hsum1] at hle
  have := hz1 b
  omega

/-- Nonnegative unit forms are finitely many. -/
lemma finite_nonneg : Set.Finite {q : UnitForm ι | ∀ x, 0 ≤ q.val x} := by
  have hT : Set.Finite (Set.pi Set.univ fun _ : ι ↦ Set.pi Set.univ fun _ : ι ↦
      (Set.Icc (-2 : ℤ) 2)) :=
    Set.Finite.pi fun _ ↦ Set.Finite.pi fun _ ↦ Set.finite_Icc _ _
  refine Set.Finite.of_finite_image (f := UnitForm.c) ?_ ?_
  · refine hT.subset ?_
    rintro _ ⟨q, hq, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
    intro a b
    by_cases hab : a = b
    · subst hab; rw [q.diag]; norm_num
    · exact q.coeff_bound hq hab
  · intro q _ q' _ h
    cases q; cases q'; simp only at h; subst h; rfl

/-- **Repeated inflation ends at a form with no coefficient `+1`**, with a larger radical
vector. -/
theorem exists_terminal {y : ι → ℤ} (h : q.Rad1 y) :
    ∃ (q' : UnitForm ι) (y' : ι → ℤ), q'.Rad1 y' ∧ (∀ a b, a ≠ b → q'.c a b ≠ 1) ∧
      ∀ u, y u ≤ y' u := by
  classical
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ q' ∈ {q : UnitForm ι | ∀ x, 0 ≤ q.val x}, q'.rsum ≤ M := by
    obtain ⟨M, hM⟩ := ((finite_nonneg (ι := ι)).image rsum).bddAbove
    exact ⟨M, fun q' hq' ↦ hM ⟨q', hq', rfl⟩⟩
  suffices H : ∀ n, ∀ (q : UnitForm ι) (y : ι → ℤ), q.Rad1 y → M - q.rsum = n →
      ∃ (q' : UnitForm ι) (y' : ι → ℤ), q'.Rad1 y' ∧ (∀ a b, a ≠ b → q'.c a b ≠ 1) ∧
        ∀ u, y u ≤ y' u from H _ q y h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro q y h hn
  by_cases hterm : ∀ a b, a ≠ b → q.c a b ≠ 1
  · exact ⟨q, y, h, hterm, fun _ ↦ le_rfl⟩
  push Not at hterm
  obtain ⟨a, b, hab, hc⟩ := hterm
  have h1 := h.inflate hab hc
  have hlt := q.rsum_lt_inflate h hab hc
  have hle := hM _ h1.1
  obtain ⟨q', y', h', ht, hy'⟩ := ih (M - (q.inflate hab hc).rsum) (by omega) _ _ h1 rfl
  refine ⟨q', y', h', ht, fun u ↦ le_trans ?_ (hy' u)⟩
  simp only [deflMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Pi.single_apply]
  split_ifs
  · have := h.2.1 b; linarith
  · simp

/-- The terminal form has off-diagonal coefficients `0` or `-1` (at least three points). -/
lemma Rad1.coeff_graph {y : ι → ℤ} (h : q.Rad1 y) (hterm : ∀ a b, a ≠ b → q.c a b ≠ 1)
    (hn : 3 ≤ Fintype.card ι) {a b : ι} (hab : a ≠ b) : q.c a b = 0 ∨ q.c a b = -1 := by
  obtain ⟨h1, h2⟩ := q.coeff_bound h.1 hab
  have h3 := hterm a b hab
  have hc2 : q.c a b ≠ 2 := by
    intro hc
    have hv : q.val (Pi.single a 1 - Pi.single b 1) = 0 := by
      have e := q.two_mul_val (Pi.single a 1 - Pi.single b 1)
      rw [B_sub_left, B_sub_right, B_sub_right, B_single_single, B_single_single,
        B_single_single, B_single_single, q.diag, q.diag, q.symm b a, hc] at e
      omega
    have := h.2.2.2 _ hv a b
    simp [Pi.single_apply, hab, Ne.symm hab] at this
    have := h.2.1 a; have := h.2.1 b; linarith
  have hcm2 : q.c a b ≠ -2 := by
    intro hc
    have hv : q.val (Pi.single a 1 + Pi.single b 1) = 0 := by
      have e := q.two_mul_val (Pi.single a 1 + Pi.single b 1)
      rw [B_add_left, B_add_right, B_add_right, B_single_single, B_single_single,
        B_single_single, B_single_single, q.diag, q.diag, q.symm b a, hc] at e
      omega
    obtain ⟨d, hda, hdb⟩ : ∃ d, d ≠ a ∧ d ≠ b := by
      by_contra hall
      push Not at hall
      have : Fintype.card ι ≤ 2 := by
        have : (Finset.univ : Finset ι) ⊆ {a, b} := fun d _ ↦ by
          by_cases hd : d = a
          · simp [hd]
          · simp [hall d hd]
        calc Fintype.card ι = (Finset.univ : Finset ι).card := rfl
          _ ≤ ({a, b} : Finset ι).card := Finset.card_le_card this
          _ ≤ 2 := Finset.card_le_two
      omega
    have := h.2.2.2 _ hv a d
    simp [Pi.single_apply, hda, hdb, Ne.symm hda, Ne.symm hdb, hab] at this
    have := h.2.1 a; have := h.2.1 d; nlinarith
  omega

/-- **Patterns**: a nonzero `u ≥ 0` with `q(u) ≤ 0` is a rational multiple of the radical
vector; if moreover `u_a = 1` and `y_a ∣` nothing smaller, `y = y_a • u`. -/
lemma Rad1.prop_of_nonpos {y : ι → ℤ} (h : q.Rad1 y) {u : ι → ℤ} (hu : q.val u ≤ 0) :
    ∀ c d, y c * u d = u c * y d :=
  h.2.2.2 u (le_antisymm hu (h.1 u))

/-- A form vector with a coordinate `1` and value `≤ 0` gives `y = y_a • u`. -/
lemma Rad1.eq_smul_of_nonpos {y : ι → ℤ} (h : q.Rad1 y) {u : ι → ℤ} (hu : q.val u ≤ 0)
    {a : ι} (ha : u a = 1) : y = y a • u := by
  funext d
  have := h.prop_of_nonpos hu a d
  rw [ha] at this
  simp only [Pi.smul_apply, smul_eq_mul]
  linarith

end UnitForm

end LargeIndecomposable.Forms
