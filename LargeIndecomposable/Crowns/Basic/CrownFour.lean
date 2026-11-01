module

public import LargeIndecomposable.Crowns.Lemma6.Figure63

/-!
# Crowns of length four and minimality

* `RayCat.Crown.two_le_n`: crowns have length at least four.
* `RayCat.Crown.mk4`: the crown `(f₀, f₁, f₂, f₃)` of length four, with
  `f₀, f₁` and `f₂, f₃` peaks and `f₁, f₂` and `f₃, f₀` valleys;
  `Crown.weight_mk4`.
* `RayCat.Crown.weight_shift`, `Crown.weight_two`: the weight is a sum over
  any period.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

namespace Crown

/-- The weight is a sum over any period. -/
lemma weight_shift (C : Crown P) (k : ℕ) :
    C.weight = ∑ t ∈ Finset.range (2 * C.n), depth (C.f (t + k)).2.2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [ih]
    have h := Finset.sum_range_succ (fun t ↦ depth (C.f (t + k)).2.2) (2 * C.n)
    have h' := Finset.sum_range_succ' (fun t ↦ depth (C.f (t + k)).2.2) (2 * C.n)
    rw [Nat.zero_add] at h'
    rw [show 2 * C.n + k = k + 2 * C.n by ring, C.per] at h
    have e : ∑ t ∈ Finset.range (2 * C.n), depth (C.f (t + 1 + k)).2.2 =
        ∑ t ∈ Finset.range (2 * C.n), depth (C.f (t + (k + 1))).2.2 :=
      Finset.sum_congr rfl (fun t _ ↦ by rw [show t + 1 + k = t + (k + 1) by ring])
    omega

/-- The weight of a crown of length four. -/
lemma weight_two (C : Crown P) (hn : C.n = 2) (k : ℕ) :
    C.weight = depth (C.f k).2.2 + depth (C.f (k + 1)).2.2 + depth (C.f (k + 2)).2.2 +
      depth (C.f (k + 3)).2.2 := by
  rw [C.weight_shift k, hn]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [Nat.zero_add, Nat.zero_add, Nat.add_comm 1 k, Nat.add_comm 2 k, Nat.add_comm 3 k]

section Mk4

variable {a₀ a₁ b₀ b₁ : P} (f₀ : a₀ ⟶ b₀) (f₁ : a₁ ⟶ b₀) (f₂ : a₁ ⟶ b₁) (f₃ : a₀ ⟶ b₁)

/-- The entries of the crown `(f₀, f₁, f₂, f₃)`. -/
def mk4f (t : ℕ) : RayMor P :=
  match t % 4 with
  | 0 => ⟨a₀, b₀, f₀⟩
  | 1 => ⟨a₁, b₀, f₁⟩
  | 2 => ⟨a₁, b₁, f₂⟩
  | _ => ⟨a₀, b₁, f₃⟩

omit [HasZeroMorphisms P] in
lemma mk4f_mod (t : ℕ) : mk4f f₀ f₁ f₂ f₃ t = mk4f f₀ f₁ f₂ f₃ (t % 4) := by
  simp [mk4f]

/-- **The crown `(f₀, f₁, f₂, f₃)` of length four.** -/
def mk4 (p1 : ¬∃ c, c ≫ f₁ = f₀) (p2 : ¬∃ c, c ≫ f₀ = f₁) (v1 : ¬∃ c, f₁ ≫ c = f₂)
    (v2 : ¬∃ c, f₂ ≫ c = f₁) (p3 : ¬∃ c, c ≫ f₃ = f₂) (p4 : ¬∃ c, c ≫ f₂ = f₃)
    (v3 : ¬∃ c, f₃ ≫ c = f₀) (v4 : ¬∃ c, f₀ ≫ c = f₃) (h0 : f₀ ≠ 0) (h1 : f₁ ≠ 0)
    (h2 : f₂ ≠ 0) (h3 : f₃ ≠ 0) : Crown P where
  n := 2
  hn := by norm_num
  f := mk4f f₀ f₁ f₂ f₃
  per t := by rw [mk4f_mod, show (t + 2 * 2) % 4 = t % 4 by omega, ← mk4f_mod]
  peak i := by
    rw [mk4f_mod, mk4f_mod f₀ f₁ f₂ f₃ (2 * i + 1)]
    rcases Nat.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [show 2 * (j + j) % 4 = 0 by omega, show (2 * (j + j) + 1) % 4 = 1 by omega]
      exact (peak_mk_iff f₀ f₁).2 ⟨p1, p2⟩
    · rw [show 2 * (2 * j + 1) % 4 = 2 by omega, show (2 * (2 * j + 1) + 1) % 4 = 3 by omega]
      exact (peak_mk_iff f₂ f₃).2 ⟨p3, p4⟩
  valley i := by
    rw [mk4f_mod, mk4f_mod f₀ f₁ f₂ f₃ (2 * i + 2)]
    rcases Nat.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [show (2 * (j + j) + 1) % 4 = 1 by omega, show (2 * (j + j) + 2) % 4 = 2 by omega]
      exact (valley_mk_iff f₁ f₂).2 ⟨v1, v2⟩
    · rw [show (2 * (2 * j + 1) + 1) % 4 = 3 by omega,
        show (2 * (2 * j + 1) + 2) % 4 = 0 by omega]
      exact (valley_mk_iff f₃ f₀).2 ⟨v3, v4⟩
  ne t := by
    rw [mk4f_mod]
    have : t % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases t % 4 <;> assumption

lemma weight_mk4 (p1 : ¬∃ c, c ≫ f₁ = f₀) (p2 : ¬∃ c, c ≫ f₀ = f₁) (v1 : ¬∃ c, f₁ ≫ c = f₂)
    (v2 : ¬∃ c, f₂ ≫ c = f₁) (p3 : ¬∃ c, c ≫ f₃ = f₂) (p4 : ¬∃ c, c ≫ f₂ = f₃)
    (v3 : ¬∃ c, f₃ ≫ c = f₀) (v4 : ¬∃ c, f₀ ≫ c = f₃) (h0 : f₀ ≠ 0) (h1 : f₁ ≠ 0)
    (h2 : f₂ ≠ 0) (h3 : f₃ ≠ 0) :
    (mk4 f₀ f₁ f₂ f₃ p1 p2 v1 v2 p3 p4 v3 v4 h0 h1 h2 h3).weight =
      depth f₀ + depth f₁ + depth f₂ + depth f₃ := by
  rw [weight_two _ rfl 0]
  rfl

end Mk4

variable [IsRayCategory P] [IsFiniteRayCategory P]

omit [IsRayCategory P] in
/-- **Crowns have length at least four** (parallel neighbours are comparable). -/
lemma two_le_n (hQ : OneSidedCyclic P) (C : Crown P) : 2 ≤ C.n := by
  by_contra h
  have h1 : C.n = 1 := by have := C.hn; omega
  have e : C.f 2 = C.f 0 := by
    have := C.per 0
    rw [h1] at this
    simpa using this
  have hPk := C.peak 0
  have hVl := C.valley 0
  simp only [mul_zero, zero_add] at hPk hVl
  rw [e] at hVl
  have hne0 := C.ne 0
  have hne1 := C.ne 1
  generalize C.f 0 = F at hPk hVl hne0
  generalize C.f 1 = G at hPk hVl hne1
  obtain ⟨a, c, φ⟩ := F
  obtain ⟨a', c', ψ⟩ := G
  obtain ⟨hc, hp1, hp2⟩ := hPk
  obtain ⟨ha, hv1, hv2⟩ := hVl
  simp only at hc ha
  subst hc ha
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hp1 hp2 hv1 hv2
  exact not_parallel hQ φ ψ hne0 hne1 hv2 hv1 hp2 hp1

end Crown

end RayCat

end LargeIndecomposable
