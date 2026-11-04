module

public import LargeIndecomposable.DirectedAlgebras.EulerForm.EulerUnit
public import LargeIndecomposable.DirectedAlgebras.Directing.CornerSurvive
public import LargeIndecomposable.DirectedAlgebras.Preprojective.MinimalQuot

/-!
# The Euler form on an interval with two points

The inverse Cartan matrix is supported on the path order (`cartan_inv_support`). If `b` is
reached from `a` with `dim e_b A e_a = 1` and no third point lies on a path from `a` to `b`,
then `⟨e_a, e_b⟩ + ⟨e_b, e_a⟩ = -1`, a full edge of the Euler form (`eulerForm_c_interval`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open Module Matrix

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (D : DirData k A)

/-- **The inverse Cartan matrix is supported on the path order.** -/
theorem cartan_inv_support (hT : ∀ x, x ∈ D.T) (i : D.ι) :
    ∀ j, (cartan D)⁻¹ j i ≠ 0 → Relation.ReflTransGen D.Arr i j := by
  classical
  obtain ⟨lo, hmono⟩ := exists_linOrder D
  letI := lo
  have hu : IsUnit (cartan D).det := by rw [det_cartan D hT]; exact isUnit_one
  intro j
  induction j using WellFoundedLT.induction with
  | _ j ih =>
  intro hj
  by_cases hji : j = i
  · subst hji; exact Relation.ReflTransGen.refl
  have h1 := congrFun (congrFun (mul_nonsing_inv _ hu) j) i
  rw [mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), cartan_diag D (hT j), one_mul,
    one_apply_ne hji] at h1
  obtain ⟨y, hy, hyne⟩ : ∃ y ∈ Finset.univ.erase j, cartan D j y * (cartan D)⁻¹ y i ≠ 0 := by
    by_contra hall
    push Not at hall
    rw [Finset.sum_eq_zero hall, add_zero] at h1
    exact hj h1
  have hyj : y ≠ j := Finset.ne_of_mem_erase hy
  have hc : cartan D j y ≠ 0 := fun h0 ↦ hyne (by rw [h0, zero_mul])
  have hci : (cartan D)⁻¹ y i ≠ 0 := fun h0 ↦ hyne (by rw [h0, mul_zero])
  have hpath : Relation.ReflTransGen D.Arr y j := by
    by_contra hn
    exact hc (cartan_eq_zero D hn)
  have hlt : y < j := lt_of_le_of_ne (hmono _ _ hpath) hyj
  exact (ih y hlt hci).trans hpath

/-- **A two-point interval gives a full edge.** -/
theorem eulerForm_c_interval (hT : ∀ x, x ∈ D.T) {a b : D.ι} (hab : a ≠ b)
    (hba : cartan D b a = 1)
    (hint : ∀ y, y ≠ a → y ≠ b → Relation.ReflTransGen D.Arr a y →
      Relation.ReflTransGen D.Arr y b → False) :
    (eulerForm D hT).c a b = -1 := by
  classical
  have hu : IsUnit (cartan D).det := by rw [det_cartan D hT]; exact isUnit_one
  have hab' : Relation.ReflTransGen D.Arr a b := by
    by_contra hn
    rw [cartan_eq_zero D hn] at hba
    exact absurd hba (by norm_num)
  -- no path back
  have h1 : (cartan D)⁻¹ a b = 0 := by
    by_contra h
    have hba' := cartan_inv_support D hT b a h
    have := D.acyc a b (D.transGen_of_ne hab' hab) hba'
    exact this
  -- the entry `(b, a)`
  have h2 : (cartan D)⁻¹ b a = -1 := by
    have e := congrFun (congrFun (mul_nonsing_inv _ hu) b) a
    rw [mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ b), cartan_diag D (hT b), one_mul,
      one_apply_ne (Ne.symm hab), ← Finset.add_sum_erase _ _
        (Finset.mem_erase.2 ⟨hab, Finset.mem_univ a⟩), hba, cartan_inv_diag D hT a] at e
    have hrest : ∑ y ∈ (Finset.univ.erase b).erase a, cartan D b y * (cartan D)⁻¹ y a = 0 := by
      refine Finset.sum_eq_zero fun y hy ↦ ?_
      have hya : y ≠ a := Finset.ne_of_mem_erase hy
      have hyb : y ≠ b := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hy)
      by_cases hc : cartan D b y = 0
      · rw [hc, zero_mul]
      · have hpath : Relation.ReflTransGen D.Arr y b := by
          by_contra hn
          exact hc (cartan_eq_zero D hn)
        by_cases hi : (cartan D)⁻¹ y a = 0
        · rw [hi, mul_zero]
        · exact (hint y hya hyb (cartan_inv_support D hT a y hi) hpath).elim
    rw [hrest, add_zero] at e
    linarith
  change (cartan D)⁻¹ b a + (cartan D)⁻¹ a b = -1
  rw [h1, h2, add_zero]

namespace DirData

variable {D}

/-- Paths of a quotient are paths of the algebra. -/
lemma rtg_of_quot {T' : Set D.ι} (hsub : T' ⊆ D.T) {x y : T'}
    (h : Relation.ReflTransGen (D.quotAny hsub).Arr x y) :
    Relation.ReflTransGen D.Arr x.1 y.1 := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail y z _ hyz ih =>
    obtain ⟨-, a, ha⟩ := hyz
    obtain ⟨a', rfl⟩ := D.qmap_surjective T' a
    have ha' : D.e z.1 * a' * D.e y.1 ≠ 0 := fun h0 ↦ ha (by
      change D.qmap T' _ * D.qmap T' a' * D.qmap T' _ = 0
      rw [← map_mul, ← map_mul, h0, map_zero])
    exact ih.trans (D.hom _ _ a' ha')

/-- **An edge of the quotient**: if `e_b A e_a` is one-dimensional and nonzero, and every
point on a path from `a` to `b` is `a` or `b`, then `a, b` are joined by a full edge of the
Euler form of the quotient by the idempotents outside any `T' ∋ a, b`. -/
theorem eulerForm_c_quot_interval {T' : Set D.ι} (hsub : T' ⊆ D.T) {a b : D.ι} (ha : a ∈ T')
    (hb : b ∈ T') (hab : a ≠ b) {c : A} (hc : D.e b * c * D.e a ≠ 0)
    (hle : cartan D b a ≤ 1)
    (hmid : ∀ v, Relation.ReflTransGen D.Arr a v → Relation.ReflTransGen D.Arr v b →
      v = a ∨ v = b) :
    (eulerForm (D.quotAny hsub) fun _ ↦ Set.mem_univ _).c ⟨a, ha⟩ ⟨b, hb⟩ = -1 := by
  classical
  have hsurv : D.qmap T' (D.e b * c * D.e a) ≠ 0 :=
    D.qmap_corner_ne' ha hb (fun v h1 h2 ↦ by
      rcases hmid v h1 h2 with rfl | rfl
      · exact ha
      · exact hb) hc
  have hcart : cartan (D.quotAny hsub) ⟨b, hb⟩ ⟨a, ha⟩ = 1 := by
    have hle' := (cartan_quotAny_le hsub ⟨a, ha⟩ ⟨b, hb⟩).trans hle
    have hpos : 0 < cartan (D.quotAny hsub) ⟨b, hb⟩ ⟨a, ha⟩ := by
      unfold cartan
      have : (⟨⟨D.qmap T' (D.e b * c * D.e a), by
          change D.qmap T' _ * D.qmap T' (D.e a) = _
          rw [← map_mul, mul_assoc, (D.idem a).eq]⟩, by
          apply Subtype.ext
          change D.qmap T' (D.e b) * D.qmap T' _ = _
          rw [← map_mul, ← mul_assoc, ← mul_assoc, (D.idem b).eq]⟩ :
          eSub (projE (k := k) ((D.quotAny hsub).idem ⟨a, ha⟩))
            ((D.quotAny hsub).e ⟨b, hb⟩)) ≠ 0 := fun h0 ↦
        hsurv (congrArg (fun z : eSub (projE (k := k) ((D.quotAny hsub).idem ⟨a, ha⟩))
          ((D.quotAny hsub).e ⟨b, hb⟩) ↦ (z : projE (k := k) ((D.quotAny hsub).idem ⟨a, ha⟩)).1)
          h0)
      exact_mod_cast Module.finrank_pos_iff_exists_ne_zero.2 ⟨_, this⟩
    omega
  refine eulerForm_c_interval _ _ (fun h : (⟨a, ha⟩ : T') = ⟨b, hb⟩ ↦
    hab (congrArg Subtype.val h)) hcart ?_
  intro y hya hyb h1 h2
  rcases hmid y.1 (rtg_of_quot hsub h1) (rtg_of_quot hsub h2) with h | h
  · exact hya (Subtype.ext h)
  · exact hyb (Subtype.ext h)

end DirData

end LargeIndecomposable.AR
