module

public import LargeIndecomposable.Crowns.Lemma8.Statement

/-!
# Crowns from their first `2n` entries; replacing two entries

* `RayCat.Crown.ofFn`: the crown with entries `G 0, …, G (2n-1)` (repeated), from the
  peak and valley conditions of consecutive entries; `Crown.weight_ofFn`.
* `RayCat.Crown.replace`: `C` with the entries at `2k+1`, `2k+2` replaced by `e₁`, `e₂`;
  `Crown.weight_replace`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

lemma two_mul_add_mod (i n c : ℕ) (hc : 2 * (i % n) + c < 2 * n) :
    (2 * i + c) % (2 * n) = 2 * (i % n) + c := by
  conv_lhs => rw [← Nat.div_add_mod i n]
  rw [show 2 * (n * (i / n) + i % n) + c = 2 * (i % n) + c + 2 * n * (i / n) by ring,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]

lemma two_mul_add_two_mod (i n : ℕ) (h : i % n = n - 1) (hn : 0 < n) :
    (2 * i + 2) % (2 * n) = 0 := by
  conv_lhs => rw [← Nat.div_add_mod i n]
  rw [h, show 2 * (n * (i / n) + (n - 1)) + 2 = 2 * n * (i / n + 1) by
    have : n - 1 + 1 = n := Nat.sub_add_cancel hn
    nlinarith [this], Nat.mul_mod_right]

namespace Crown

/-- **The crown with entries `G 0, …, G (2n-1)`.** -/
def ofFn (n : ℕ) (hn : 0 < n) (G : ℕ → RayMor P)
    (hp : ∀ i < n, Peak (G (2 * i)) (G (2 * i + 1)))
    (hv : ∀ i, i + 1 < n → Valley (G (2 * i + 1)) (G (2 * i + 2)))
    (hv' : Valley (G (2 * n - 1)) (G 0)) (hne : ∀ t < 2 * n, (G t).2.2 ≠ 0) : Crown P where
  n := n
  hn := hn
  f t := G (t % (2 * n))
  per t := by rw [Nat.add_mod_right]
  peak i := by
    have hi := Nat.mod_lt i hn
    rw [show 2 * i = 2 * i + 0 by rfl, two_mul_add_mod i n 0 (by omega),
      two_mul_add_mod i n 1 (by omega)]
    exact hp _ hi
  valley i := by
    have hi := Nat.mod_lt i hn
    by_cases h : i % n = n - 1
    · rw [two_mul_add_mod i n 1 (by omega), two_mul_add_two_mod i n h hn, h,
        show 2 * (n - 1) + 1 = 2 * n - 1 by omega]
      exact hv'
    · rw [two_mul_add_mod i n 1 (by omega), two_mul_add_mod i n 2 (by omega)]
      exact hv _ (by omega)
  ne t := hne _ (Nat.mod_lt _ (by omega))

lemma weight_ofFn (n : ℕ) (hn : 0 < n) (G : ℕ → RayMor P)
    (hp : ∀ i < n, Peak (G (2 * i)) (G (2 * i + 1)))
    (hv : ∀ i, i + 1 < n → Valley (G (2 * i + 1)) (G (2 * i + 2)))
    (hv' : Valley (G (2 * n - 1)) (G 0)) (hne : ∀ t < 2 * n, (G t).2.2 ≠ 0) :
    (ofFn n hn G hp hv hv' hne).weight = ∑ t ∈ Finset.range (2 * n), depth (G t).2.2 :=
  Finset.sum_congr rfl fun t ht ↦ by
    change depth (G (t % (2 * n))).2.2 = _
    rw [Nat.mod_eq_of_lt (Finset.mem_range.1 ht)]

/-- The entries of `C` from `2k` on, with the second and third replaced. -/
def replaceF (C : Crown P) (k : ℕ) (e₁ e₂ : RayMor P) (t : ℕ) : RayMor P :=
  if t = 1 then e₁ else if t = 2 then e₂ else C.f (t + 2 * k)

/-- **`C` with the entries at `2k+1`, `2k+2` replaced by `e₁`, `e₂`** (read from `2k`). -/
def replace (C : Crown P) (hC2 : 2 ≤ C.n) (k : ℕ) (e₁ e₂ : RayMor P)
    (h1 : Peak (C.f (2 * k)) e₁) (h2 : Valley e₁ e₂) (h3 : Peak e₂ (C.f (2 * k + 3)))
    (h01 : e₁.2.2 ≠ 0) (h02 : e₂.2.2 ≠ 0) : Crown P :=
  ofFn C.n C.hn (replaceF C k e₁ e₂)
    (fun i hi ↦ by
      rcases Nat.lt_or_ge i 2 with h | h
      · interval_cases i
        · simpa [replaceF] using h1
        · simpa [replaceF, show 3 + 2 * k = 2 * k + 3 by ring] using h3
      · have := C.peak (i + k)
        simp only [replaceF, show 2 * i ≠ 1 by omega, show 2 * i ≠ 2 by omega,
          show 2 * i + 1 ≠ 1 by omega, show 2 * i + 1 ≠ 2 by omega, ite_false]
        rwa [show 2 * i + 2 * k = 2 * (i + k) by ring,
          show 2 * i + 1 + 2 * k = 2 * (i + k) + 1 by ring])
    (fun i hi ↦ by
      rcases Nat.eq_zero_or_pos i with rfl | h
      · simpa [replaceF] using h2
      · have := C.valley (i + k)
        simp only [replaceF, show 2 * i + 1 ≠ 1 by omega, show 2 * i + 1 ≠ 2 by omega,
          show 2 * i + 2 ≠ 1 by omega, show 2 * i + 2 ≠ 2 by omega, ite_false]
        rwa [show 2 * i + 1 + 2 * k = 2 * (i + k) + 1 by ring,
          show 2 * i + 2 + 2 * k = 2 * (i + k) + 2 by ring])
    (by
      have := C.valley (C.n - 1 + k)
      simp only [replaceF, show 2 * C.n - 1 ≠ 1 by omega, show 2 * C.n - 1 ≠ 2 by omega,
        show (0 : ℕ) ≠ 1 by omega, show (0 : ℕ) ≠ 2 by omega, ite_false, Nat.zero_add]
      rw [show 2 * (C.n - 1 + k) + 1 = 2 * C.n - 1 + 2 * k by omega,
        show 2 * (C.n - 1 + k) + 2 = 2 * k + 2 * C.n by omega, C.per] at this
      exact this)
    (fun t _ ↦ by
      unfold replaceF
      by_cases ht1 : t = 1
      · rw [ite_eq_left ht1]; exact h01
      · rw [ite_eq_right ht1]
        by_cases ht2 : t = 2
        · rw [ite_eq_left ht2]; exact h02
        · rw [ite_eq_right ht2]; exact C.ne _)

lemma weight_replace (C : Crown P) (hC2 : 2 ≤ C.n) (k : ℕ) (e₁ e₂ : RayMor P)
    (h1 : Peak (C.f (2 * k)) e₁) (h2 : Valley e₁ e₂) (h3 : Peak e₂ (C.f (2 * k + 3)))
    (h01 : e₁.2.2 ≠ 0) (h02 : e₂.2.2 ≠ 0) :
    (C.replace hC2 k e₁ e₂ h1 h2 h3 h01 h02).weight + depth (C.f (2 * k + 1)).2.2 +
      depth (C.f (2 * k + 2)).2.2 = C.weight + depth e₁.2.2 + depth e₂.2.2 := by
  rw [replace, weight_ofFn, C.weight_shift (2 * k)]
  have hs : ∀ F : ℕ → ℕ, ∑ t ∈ Finset.range (2 * C.n), F t =
      F 1 + F 2 + ∑ t ∈ (Finset.range (2 * C.n)).erase 1 |>.erase 2, F t := by
    intro F
    rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 (by omega : 1 < 2 * C.n)),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨by omega, Finset.mem_range.2
        (by omega : 2 < 2 * C.n)⟩)]
    ring
  rw [hs, hs (fun t ↦ depth (C.f (t + 2 * k)).2.2)]
  have he : ∑ t ∈ (Finset.range (2 * C.n)).erase 1 |>.erase 2,
      depth (replaceF C k e₁ e₂ t).2.2 =
      ∑ t ∈ (Finset.range (2 * C.n)).erase 1 |>.erase 2, depth (C.f (t + 2 * k)).2.2 :=
    Finset.sum_congr rfl fun t ht ↦ by
      have h2' := Finset.ne_of_mem_erase ht
      have h1' := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht)
      unfold replaceF
      rw [ite_eq_right h1', ite_eq_right h2']
  rw [he]
  unfold replaceF
  rw [ite_eq_left rfl, ite_eq_right (by decide : ¬(2 : ℕ) = 1), ite_eq_left rfl,
    show 1 + 2 * k = 2 * k + 1 by ring, show 2 + 2 * k = 2 * k + 2 by ring]
  ring

end Crown

end RayCat

end LargeIndecomposable
