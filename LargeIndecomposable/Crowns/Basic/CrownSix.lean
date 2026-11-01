module

public import LargeIndecomposable.Crowns.Lemma8.Reflecting

/-!
# Crowns of length six

* `RayCat.Crown.mk6`: the crown `(f₀, …, f₅)` of length six (peaks `f₀f₁`, `f₂f₃`,
  `f₄f₅`; valleys `f₁f₂`, `f₃f₄`, `f₅f₀`), `Crown.weight_mk6`.
* `RayCat.Crown.weight_chain3`: the weight of a crown of length six in terms of its
  chain.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

namespace Crown

section Mk6

variable {a₀ a₁ a₂ b₀ b₁ b₂ : P} (f₀ : a₀ ⟶ b₀) (f₁ : a₁ ⟶ b₀) (f₂ : a₁ ⟶ b₁) (f₃ : a₂ ⟶ b₁)
  (f₄ : a₂ ⟶ b₂) (f₅ : a₀ ⟶ b₂)

/-- The entries of the crown `(f₀, …, f₅)`. -/
def mk6f (t : ℕ) : RayMor P :=
  match t % 6 with
  | 0 => ⟨a₀, b₀, f₀⟩
  | 1 => ⟨a₁, b₀, f₁⟩
  | 2 => ⟨a₁, b₁, f₂⟩
  | 3 => ⟨a₂, b₁, f₃⟩
  | 4 => ⟨a₂, b₂, f₄⟩
  | _ => ⟨a₀, b₂, f₅⟩

omit [HasZeroMorphisms P] in
lemma mk6f_mod (t : ℕ) : mk6f f₀ f₁ f₂ f₃ f₄ f₅ t = mk6f f₀ f₁ f₂ f₃ f₄ f₅ (t % 6) := by
  simp [mk6f]

/-- **The crown `(f₀, …, f₅)` of length six.** -/
def mk6 (p1 : ¬∃ c, c ≫ f₁ = f₀) (p2 : ¬∃ c, c ≫ f₀ = f₁) (v1 : ¬∃ c, f₁ ≫ c = f₂)
    (v2 : ¬∃ c, f₂ ≫ c = f₁) (p3 : ¬∃ c, c ≫ f₃ = f₂) (p4 : ¬∃ c, c ≫ f₂ = f₃)
    (v3 : ¬∃ c, f₃ ≫ c = f₄) (v4 : ¬∃ c, f₄ ≫ c = f₃) (p5 : ¬∃ c, c ≫ f₅ = f₄)
    (p6 : ¬∃ c, c ≫ f₄ = f₅) (v5 : ¬∃ c, f₅ ≫ c = f₀) (v6 : ¬∃ c, f₀ ≫ c = f₅)
    (h0 : f₀ ≠ 0) (h1 : f₁ ≠ 0) (h2 : f₂ ≠ 0) (h3 : f₃ ≠ 0) (h4 : f₄ ≠ 0) (h5 : f₅ ≠ 0) :
    Crown P where
  n := 3
  hn := by norm_num
  f := mk6f f₀ f₁ f₂ f₃ f₄ f₅
  per t := by rw [mk6f_mod, show (t + 2 * 3) % 6 = t % 6 by omega, ← mk6f_mod]
  peak i := by
    rw [mk6f_mod, mk6f_mod f₀ f₁ f₂ f₃ f₄ f₅ (2 * i + 1)]
    have h : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have e1 : 2 * i % 6 = 2 * (i % 3) := by omega
    have e2 : (2 * i + 1) % 6 = 2 * (i % 3) + 1 := by omega
    rw [e1, e2]
    interval_cases i % 3
    · exact (peak_mk_iff f₀ f₁).2 ⟨p1, p2⟩
    · exact (peak_mk_iff f₂ f₃).2 ⟨p3, p4⟩
    · exact (peak_mk_iff f₄ f₅).2 ⟨p5, p6⟩
  valley i := by
    rw [mk6f_mod, mk6f_mod f₀ f₁ f₂ f₃ f₄ f₅ (2 * i + 2)]
    have h : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have e1 : (2 * i + 1) % 6 = 2 * (i % 3) + 1 := by omega
    have e2 : (2 * i + 2) % 6 = (2 * (i % 3) + 2) % 6 := by omega
    rw [e1, e2]
    interval_cases i % 3
    · exact (valley_mk_iff f₁ f₂).2 ⟨v1, v2⟩
    · exact (valley_mk_iff f₃ f₄).2 ⟨v3, v4⟩
    · exact (valley_mk_iff f₅ f₀).2 ⟨v5, v6⟩
  ne t := by
    rw [mk6f_mod]
    have : t % 6 < 6 := Nat.mod_lt _ (by norm_num)
    interval_cases t % 6 <;> assumption

lemma weight_mk6 (p1 : ¬∃ c, c ≫ f₁ = f₀) (p2 : ¬∃ c, c ≫ f₀ = f₁) (v1 : ¬∃ c, f₁ ≫ c = f₂)
    (v2 : ¬∃ c, f₂ ≫ c = f₁) (p3 : ¬∃ c, c ≫ f₃ = f₂) (p4 : ¬∃ c, c ≫ f₂ = f₃)
    (v3 : ¬∃ c, f₃ ≫ c = f₄) (v4 : ¬∃ c, f₄ ≫ c = f₃) (p5 : ¬∃ c, c ≫ f₅ = f₄)
    (p6 : ¬∃ c, c ≫ f₄ = f₅) (v5 : ¬∃ c, f₅ ≫ c = f₀) (v6 : ¬∃ c, f₀ ≫ c = f₅)
    (h0 : f₀ ≠ 0) (h1 : f₁ ≠ 0) (h2 : f₂ ≠ 0) (h3 : f₃ ≠ 0) (h4 : f₄ ≠ 0) (h5 : f₅ ≠ 0) :
    (mk6 f₀ f₁ f₂ f₃ f₄ f₅ p1 p2 v1 v2 p3 p4 v3 v4 p5 p6 v5 v6 h0 h1 h2 h3 h4 h5).weight =
      depth f₀ + depth f₁ + depth f₂ + depth f₃ + depth f₄ + depth f₅ := by
  change ∑ t ∈ Finset.range (2 * 3), depth (mk6f f₀ f₁ f₂ f₃ f₄ f₅ t).2.2 = _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add, zero_add]
  rfl

end Mk6

variable [IsRayCategory P]

/-- The weight of a crown of length six in terms of its chain. -/
lemma weight_chain3 (C : Crown P) (hn : C.n = 3) (r : ℕ) :
    C.weight = depth (C.toZChain.ρ (r + 1)) + depth (C.toZChain.σ (r + 1)) +
      depth (C.toZChain.ρ (r + 2)) + depth (C.toZChain.σ (r + 2)) +
        depth (C.toZChain.ρ (r + 3)) + depth (C.toZChain.σ (r + 3)) := by
  rw [C.weight_shift (2 * (r + 1)), hn]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
  have e1 := depth_of_rayMor_eq (C.toZChain_σ (r + 1))
  have e2 := depth_of_rayMor_eq (C.toZChain_σ (r + 2))
  have e3 := depth_of_rayMor_eq (C.toZChain_σ (r + 3))
  have e4 := depth_of_rayMor_eq (C.toZChain_ρ (r + 2))
  have e5 := depth_of_rayMor_eq (C.toZChain_ρ (r + 3))
  have e6 := depth_of_rayMor_eq (C.toZChain_ρ (r + 1))
  simp only at e1 e2 e3 e4 e5 e6
  rw [e1, e2, e3, e4, e5, e6, show 0 + 2 * (r + 1) = 2 * (r + 1) by ring,
    show 1 + 2 * (r + 1) = 2 * (r + 1) + 1 by ring,
    show 2 + 2 * (r + 1) = 2 * (r + 2) by ring, show 3 + 2 * (r + 1) = 2 * (r + 2) + 1 by ring,
    show 4 + 2 * (r + 1) = 2 * (r + 3) by ring, show 5 + 2 * (r + 1) = 2 * (r + 3) + 1 by ring]

end Crown

end RayCat

end LargeIndecomposable
