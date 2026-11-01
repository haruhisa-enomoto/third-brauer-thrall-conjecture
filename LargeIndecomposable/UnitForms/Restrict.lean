module

public import LargeIndecomposable.UnitForms.Ovsienko

/-!
# Restrictions of unit forms and critical restrictions

The restriction of a unit form to a finite set `s` of indices (`UnitForm.restrict`) computes the
form on vectors supported in `s` (`val_restrict`). A form that is not weakly positive has a
critical restriction: one to a set of minimal size on which it is not weakly positive
(`exists_critical_restrict`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.Forms

namespace UnitForm

variable {ι : Type} [Fintype ι] [DecidableEq ι] (q : UnitForm ι)

/-- The restriction to a finite set of indices. -/
def restrict (s : Finset ι) : UnitForm s where
  c a b := q.c a b
  symm a b := q.symm a b
  diag a := q.diag a

/-- Extension by zero of a vector on `s`. -/
def extZ (s : Finset ι) (x : s → ℤ) : ι → ℤ := fun i ↦ if h : i ∈ s then x ⟨i, h⟩ else 0

lemma extZ_mem {s : Finset ι} (x : s → ℤ) (a : s) : extZ s x a = x a := by
  simp [extZ, a.2]

lemma extZ_out {s : Finset ι} (x : s → ℤ) {i : ι} (hi : i ∉ s) : extZ s x i = 0 := by
  simp [extZ, hi]

lemma B_restrict (s : Finset ι) (x y : s → ℤ) :
    (q.restrict s).B x y = q.B (extZ s x) (extZ s y) := by
  let F : ι → ι → ℤ := fun i j ↦ q.c i j * extZ s x i * extZ s y j
  have h1 : (q.restrict s).B x y = ∑ a : s, ∑ b : s, F a b := by
    unfold B
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
    simp only [F, extZ_mem]
    rfl
  rw [h1]
  unfold B
  rw [Finset.sum_coe_sort s (fun i ↦ ∑ b : s, F i b)]
  simp_rw [Finset.sum_coe_sort s (F _)]
  rw [← Finset.sum_subset (Finset.subset_univ s) (fun i _ hi ↦ by
    exact Finset.sum_eq_zero fun j _ ↦ by simp [F, extZ_out x hi])]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_subset (Finset.subset_univ s) (fun j _ hj ↦ by simp [F, extZ_out y hj])]

lemma val_restrict (s : Finset ι) (x : s → ℤ) : (q.restrict s).val x = q.val (extZ s x) := by
  unfold val
  rw [B_restrict]

lemma pos_extZ {s : Finset ι} {x : s → ℤ} (hx : Pos x) : Pos (extZ s x) := by
  refine ⟨fun i ↦ ?_, fun h ↦ hx.2 (funext fun a ↦ ?_)⟩
  · by_cases hi : i ∈ s
    · rw [show i = ((⟨i, hi⟩ : s) : ι) from rfl, extZ_mem]
      exact hx.1 _
    · rw [extZ_out x hi]
  · have := congrFun h a
    rwa [extZ_mem] at this

/-- **A form that is not weakly positive has a critical restriction.** -/
theorem exists_critical_restrict (hq : ¬q.WeaklyPositive) :
    ∃ s : Finset ι, (q.restrict s).Critical := by
  classical
  have hex : ∃ n, ∃ s : Finset ι, s.card = n ∧ ¬(q.restrict s).WeaklyPositive := by
    refine ⟨_, Finset.univ, rfl, fun hwp ↦ hq fun x hx ↦ ?_⟩
    have := hwp (fun a ↦ x a) ⟨fun a ↦ hx.1 a, fun h ↦ hx.2 (funext fun i ↦
      congrFun h ⟨i, Finset.mem_univ i⟩)⟩
    rw [val_restrict] at this
    convert this using 2
    funext i
    simp [extZ]
  obtain ⟨s, hs, hnwp⟩ := Nat.find_spec hex
  refine ⟨s, hnwp, fun a x hx hxa ↦ ?_⟩
  -- the restriction to `s \ {a}` is weakly positive by minimality
  let t : Finset ι := s.erase a
  have hmin : (q.restrict t).WeaklyPositive := by
    by_contra h
    exact Nat.find_min hex (by rw [← hs]; exact Finset.card_erase_lt_of_mem a.2) ⟨t, rfl, h⟩
  let y : t → ℤ := fun b ↦ x ⟨b.1, Finset.mem_of_mem_erase b.2⟩
  have hy : extZ t y = extZ s x := by
    funext i
    by_cases hit : i ∈ t
    · have his : i ∈ s := Finset.mem_of_mem_erase hit
      simp [extZ, hit, his, y]
    · by_cases his : i ∈ s
      · have : i = a := by
          by_contra hne
          exact hit (Finset.mem_erase.2 ⟨hne, his⟩)
        subst this
        simp [extZ, hit, his, hxa]
      · simp [extZ, hit, his]
  have hypos : Pos y := by
    refine ⟨fun b ↦ hx.1 _, fun h ↦ hx.2 (funext fun b ↦ ?_)⟩
    by_cases hb : b = a
    · subst hb; exact hxa
    · have := congrFun h ⟨b.1, Finset.mem_erase.2 ⟨fun e ↦ hb (Subtype.ext e), b.2⟩⟩
      exact this
  have := hmin y hypos
  rw [val_restrict, hy, ← val_restrict] at this
  exact this

end UnitForm

end LargeIndecomposable.Forms
