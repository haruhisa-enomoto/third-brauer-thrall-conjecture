module

public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Data.Finite.Prod

/-!
# Free groups are residually finite

A nontrivial reduced word `L` of length `n` moves the point `n` of `Fin (n + 1)` to `0` under
suitable permutations: the `j`-th letter `(a, ε)` asks `σ_a^ε (j + 1) = j`, and reducedness makes
these partial prescriptions injective (`exists_perm_ne_one`). Hence finitely many nontrivial
elements of a free group survive in one finite quotient (`exists_finite_quotient`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.FreeRF

open Function

variable {α : Type*} (L : List (α × Bool))

/-- `k` is the end `j + 1` of a positive letter `a`. -/
def TrueAt (a : α) (k : ℕ) : Prop := ∃ j, L[j]? = some (a, true) ∧ k = j + 1

/-- `k` is the start `j` of a negative letter `a`. -/
def FalseAt (a : α) (k : ℕ) : Prop := ∃ j, L[j]? = some (a, false) ∧ k = j

open Classical in
/-- The prescribed step of `σ_a`. -/
def stepN (a : α) (k : ℕ) : ℕ := if TrueAt L a k then k - 1 else k + 1

open Classical in
/-- The step on `Fin (L.length + 1)`. -/
def stepF (a : α) (k : Fin (L.length + 1)) : Fin (L.length + 1) :=
  if h : stepN L a k < L.length + 1 then ⟨_, h⟩ else k

/-- Where `σ_a` is prescribed. -/
def dom (a : α) : Set (Fin (L.length + 1)) := {k | TrueAt L a k ∨ FalseAt L a k}

variable {L}

lemma adj (hL : FreeGroup.IsReduced L) {i : ℕ} {a : α} {b c : Bool} (h₁ : L[i]? = some (a, b))
    (h₂ : L[i + 1]? = some (a, c)) : b = c := by
  have hi : i + 1 < L.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at h₂; cases h₂
  rw [FreeGroup.IsReduced, List.isChain_iff_getElem] at hL
  have := hL i hi
  obtain ⟨i₁, e₁⟩ := List.getElem?_eq_some_iff.1 h₁
  obtain ⟨i₂, e₂⟩ := List.getElem?_eq_some_iff.1 h₂
  rw [e₁, e₂] at this
  exact this rfl

lemma not_trueAt_of_falseAt (hL : FreeGroup.IsReduced L) {a : α} {k : ℕ} (hF : FalseAt L a k) :
    ¬TrueAt L a k := by
  rintro ⟨j, hj, rfl⟩
  obtain ⟨j', hj', hk⟩ := hF
  subst hk
  exact Bool.noConfusion (adj hL hj hj')

lemma stepN_lt {a : α} {k : ℕ} (hk : TrueAt L a k ∨ FalseAt L a k) :
    stepN L a k < L.length + 1 := by
  unfold stepN
  split_ifs with h
  · obtain ⟨j, hj, rfl⟩ := h
    have := (List.getElem?_eq_some_iff.1 hj).1
    omega
  · rcases hk with hk | ⟨j, hj, rfl⟩
    · exact absurd hk h
    · have := (List.getElem?_eq_some_iff.1 hj).1
      omega

lemma stepF_val {a : α} {k : Fin (L.length + 1)} (hk : k ∈ dom L a) :
    (stepF L a k).1 = stepN L a k := by
  unfold stepF
  rw [dif_pos (stepN_lt hk)]

lemma injOn (hL : FreeGroup.IsReduced L) (a : α) : Set.InjOn (stepF L a) (dom L a) := by
  intro k₁ h₁ k₂ h₂ he
  have he' := congrArg Fin.val he
  rw [stepF_val h₁, stepF_val h₂] at he'
  unfold stepN at he'
  apply Fin.ext
  split_ifs at he' with t₁ t₂ t₂
  · obtain ⟨j₁, -, hj₁⟩ := t₁; obtain ⟨j₂, -, hj₂⟩ := t₂; omega
  · obtain ⟨j₁, hj₁, e₁⟩ := t₁
    rcases h₂ with h₂ | ⟨j₂, hj₂, e₂⟩
    · exact absurd h₂ t₂
    · have : j₁ = j₂ + 1 := by omega
      subst this
      exact absurd (adj hL hj₂ hj₁) (by decide)
  · obtain ⟨j₂, hj₂, e₂⟩ := t₂
    rcases h₁ with h₁ | ⟨j₁, hj₁, e₁⟩
    · exact absurd h₁ t₁
    · have : j₂ = j₁ + 1 := by omega
      subst this
      exact absurd (adj hL hj₁ hj₂) (by decide)
  · omega

open Classical in
/-- The permutation `σ_a`. -/
def sigma (hL : FreeGroup.IsReduced L) (a : α) : Equiv.Perm (Fin (L.length + 1)) :=
  Equiv.extendSubtype (p := (· ∈ dom L a)) (q := (· ∈ stepF L a '' dom L a))
    (Equiv.Set.imageOfInjOn _ _ (injOn hL a))

lemma sigma_apply (hL : FreeGroup.IsReduced L) {a : α} {k : Fin (L.length + 1)}
    (hk : k ∈ dom L a) : sigma hL a k = stepF L a k := by
  classical
  unfold sigma
  rw [Equiv.extendSubtype_apply_of_mem _ _ hk]
  rfl

lemma letter_step (hL : FreeGroup.IsReduced L) (i : ℕ) (hi : i < L.length) :
    (cond L[i].2 (sigma hL L[i].1) (sigma hL L[i].1)⁻¹) ⟨i + 1, by omega⟩ = ⟨i, by omega⟩ := by
  have hget : L[i]? = some (L[i].1, L[i].2) := by simp [hi]
  cases hb : L[i].2
  · rw [hb] at hget
    change (sigma hL L[i].1).symm _ = _
    rw [Equiv.symm_apply_eq]
    have hF : FalseAt L L[i].1 i := ⟨i, hget, rfl⟩
    have hd : (⟨i, by omega⟩ : Fin (L.length + 1)) ∈ dom L L[i].1 := Or.inr hF
    rw [sigma_apply hL hd]
    apply Fin.ext
    rw [stepF_val hd]
    change _ = stepN L L[i].1 i
    unfold stepN
    rw [if_neg (not_trueAt_of_falseAt hL hF)]
  · rw [hb] at hget
    change sigma hL L[i].1 _ = _
    have hT : TrueAt L L[i].1 (i + 1) := ⟨i, hget, rfl⟩
    have hd : (⟨i + 1, by omega⟩ : Fin (L.length + 1)) ∈ dom L L[i].1 := Or.inl hT
    rw [sigma_apply hL hd]
    apply Fin.ext
    rw [stepF_val hd]
    change stepN L L[i].1 (i + 1) = i
    unfold stepN
    rw [if_pos hT]
    rfl

lemma prod_drop (hL : FreeGroup.IsReduced L) :
    ∀ (m i : ℕ) (_ : i + m = L.length),
      ((L.drop i).map fun x ↦ cond x.2 (sigma hL x.1) (sigma hL x.1)⁻¹).prod
        ⟨L.length, by omega⟩ = ⟨i, by omega⟩
  | 0, i, h => by
    have : L.drop i = [] := List.drop_eq_nil_of_le (by omega)
    rw [this]; simp only [List.map_nil, List.prod_nil, Equiv.Perm.coe_one, id_eq]
    exact Fin.ext (by simp; omega)
  | m + 1, i, h => by
    have hi : i < L.length := by omega
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply,
      prod_drop hL m (i + 1) (by omega)]
    exact letter_step hL i hi

theorem exists_perm_ne_one {x : FreeGroup α} (hx : x ≠ 1) :
    ∃ (n : ℕ) (f : FreeGroup α →* Equiv.Perm (Fin n)), f x ≠ 1 := by
  classical
  set L := x.toWord with hLdef
  have hL : FreeGroup.IsReduced L := FreeGroup.isReduced_toWord
  have hne : L ≠ [] := fun h ↦ hx (FreeGroup.toWord_eq_nil_iff.1 h)
  have hpos : 0 < L.length := List.length_pos_iff.2 hne
  refine ⟨L.length + 1, FreeGroup.lift (sigma hL), fun h ↦ ?_⟩
  have hp := prod_drop hL L.length 0 (by omega)
  rw [List.drop_zero] at hp
  have hx' : FreeGroup.lift (sigma hL) x =
      (L.map fun x ↦ cond x.2 (sigma hL x.1) (sigma hL x.1)⁻¹).prod := by
    conv_lhs => rw [← FreeGroup.mk_toWord (x := x)]
    exact FreeGroup.lift_mk
  rw [← hx', h] at hp
  have := congrArg Fin.val hp
  change L.length = 0 at this
  omega

/-- **Finitely many nontrivial elements of a free group survive in one finite quotient.** -/
theorem exists_finite_quotient {G : Type*} [Group G] [IsFreeGroup G] (s : Finset G)
    (hs : ∀ g ∈ s, g ≠ 1) :
    ∃ (H : Type) (_ : Group H) (_ : Finite H) (f : G →* H), ∀ g ∈ s, f g ≠ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Unit, inferInstance, inferInstance, 1, by simp⟩
  | insert g s hg ih =>
    obtain ⟨H, _, _, f, hf⟩ := ih fun g' h' ↦ hs g' (Finset.mem_insert_of_mem h')
    have hg1 : IsFreeGroup.toFreeGroup G g ≠ 1 := by
      simpa using hs g (Finset.mem_insert_self _ _)
    obtain ⟨n, f', hf'⟩ := exists_perm_ne_one hg1
    refine ⟨H × Equiv.Perm (Fin n), inferInstance, inferInstance,
      f.prod (f'.comp (IsFreeGroup.toFreeGroup G).toMonoidHom), fun g' hg' ↦ ?_⟩
    rcases Finset.mem_insert.1 hg' with rfl | h'
    · intro h
      exact hf' (congrArg Prod.snd h)
    · intro h
      exact hf g' h' (congrArg Prod.fst h)

end LargeIndecomposable.FreeRF
