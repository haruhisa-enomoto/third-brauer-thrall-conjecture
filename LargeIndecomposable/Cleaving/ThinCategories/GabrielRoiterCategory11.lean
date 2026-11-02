module

public import LargeIndecomposable.Cleaving.ThinCategories.CoreFour

/-!
# Category 11 (Gabriel–Roiter 10.7) is representation-infinite

The orientation of BO13a figure 6.7: a commutative square `x → p → s`,
`x → q → s` with an arm `r → p` into the square, and arms `x → t`, `q → c`
out of it. As a core poset: core `x ≤ p, q`, source `r ≤ p`, sinks `s`
(above `p, q`), `t` (above `x`), `c` (above `q`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayQuiver

namespace RayCat

namespace Cat11

/-- The core poset of category 11. -/
abbrev data : CoreData where
  C := Fin 3
  S := Unit
  T := Fin 3
  cle c c' := c = c' ∨ c = 0
  sle _ c := c = 1
  tle c t := t = 0 ∨ (t = 1 ∧ c = 0) ∨ (t = 2 ∧ (c = 0 ∨ c = 2))
  crefl _ := Or.inl rfl
  cantisymm c c' h h' := by rcases h with h | h <;> rcases h' with h' | h' <;> simp_all
  ctrans c c' c'' h h' := by rcases h with h | h <;> rcases h' with h' | h' <;> simp_all
  sle_up s c c' h h' := by subst h; rcases h' with h' | h' <;> simp_all
  tle_down c c' t h h' := by
    rcases h with h | h
    · subst h; exact h'
    · subst h; rcases h' with h' | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp_all

/-- The sink functionals: kernels `⟨e₂⟩`, `⟨e₁⟩`, `⟨(1,1)⟩`. -/
def φ (k : Type*) [Field k] : Fin 3 → Fin 2 → k := ![![1, 0], ![0, 1], ![1, -1]]

/-- **Category 11 is representation-infinite.** -/
theorem not_isRepresentationFinite (k : Type*) [Field k] [Infinite k] :
    ¬Statement.IsRepresentationFinite (Linearization (ThinCat data.thin) k) := by
  refine data.not_isRepresentationFinite (k := k) (0 : Fin 3) (fun _ ↦ Relation.EqvGen.rel _ _ (Or.inr rfl)) ()
    (fun _ ↦ ⟨(1 : Fin 3), rfl⟩) (fun t ↦ ⟨(0 : Fin 3), by fin_cases t <;> simp⟩)
    (fun _ ↦ 0) (φ k) (fun s hs ↦ absurd rfl hs) ?_ ?_
  · intro t h
    fin_cases t <;> simp [φ] at h <;> exact h
  · intro F _ hφ
    obtain ⟨m0, h0⟩ := hφ 0
    obtain ⟨m1, h1⟩ := hφ 1
    obtain ⟨m2, h2⟩ := hφ 2
    simp only [CoreData.fn_apply, φ, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, one_mul, zero_mul, add_zero, zero_add, neg_mul] at h0 h1 h2
    have e := h2 ![1, 1]
    rw [h0, h1] at e
    simp at e
    have hm : m1 = m0 := by linear_combination -e
    refine ⟨m0, LinearMap.ext fun v ↦ funext fun i ↦ ?_⟩
    fin_cases i
    · simpa using h0 v
    · simpa [hm] using h1 v

end Cat11

end RayCat

end LargeIndecomposable
