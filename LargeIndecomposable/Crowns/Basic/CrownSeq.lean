module

public import LargeIndecomposable.RayCategories.ClosedChains.ClosedChainOf
public import LargeIndecomposable.RayCategories.Basic.Op
public import LargeIndecomposable.RayCategories.Basic.MorphismDepth

/-!
# Crowns as periodic sequences

A crown of length `2n` is a `2n`-periodic sequence of nonzero morphisms with
peaks at even and valleys at odd positions (`RayCat.Crown`). This form makes
rotation, reversal and duality (`Crown.shift`, `Crown.rev`, `Crown.op`)
cast-free; `Crown.toClosedChain` returns to `ClosedChain` for the
representation-infinite families. Crowns are compared by `(n, weight)`
lexicographically, where the weight is the sum of the depths (BO13a §2.2).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayQuiver

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

lemma Peak.symm {f g : RayMor P} (h : Peak f g) : Peak g f := by
  obtain ⟨f1, f2, f3⟩ := f
  obtain ⟨g1, g2, g3⟩ := g
  obtain ⟨h0 : f2 = g2, h1, h2⟩ := h
  subst h0
  exact ⟨rfl, fun ⟨c, hc⟩ ↦ h2 ⟨c, by simpa using hc⟩, fun ⟨c, hc⟩ ↦ h1 ⟨c, by simpa using hc⟩⟩

lemma Valley.symm {f g : RayMor P} (h : Valley f g) : Valley g f := by
  obtain ⟨f1, f2, f3⟩ := f
  obtain ⟨g1, g2, g3⟩ := g
  obtain ⟨h0 : f1 = g1, h1, h2⟩ := h
  subst h0
  exact ⟨rfl, fun ⟨c, hc⟩ ↦ h2 ⟨c, by simpa using hc⟩, fun ⟨c, hc⟩ ↦ h1 ⟨c, by simpa using hc⟩⟩

variable (P) in
/-- A crown of length `2n`. -/
structure Crown where
  n : ℕ
  hn : 0 < n
  f : ℕ → RayMor P
  per : ∀ t, f (t + 2 * n) = f t
  peak : ∀ i, Peak (f (2 * i)) (f (2 * i + 1))
  valley : ∀ i, Valley (f (2 * i + 1)) (f (2 * i + 2))
  ne : ∀ t, (f t).2.2 ≠ 0

namespace Crown

variable (C : Crown P)

lemma f_mod (t : ℕ) : C.f t = C.f (t % (2 * C.n)) := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 2 * C.n
    · rw [Nat.mod_eq_of_lt ht]
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 * C.n := ⟨t - 2 * C.n, by omega⟩
      rw [C.per, Nat.add_mod_right]
      exact ih s (by have := C.hn; omega)

lemma two_mul_succ_mod {m : ℕ} (i : Fin (m + 1)) :
    (2 * (i + 1 : Fin (m + 1)).1) % (2 * (m + 1)) = (2 * i.1 + 2) % (2 * (m + 1)) := by
  rw [Fin.val_add_one]
  split_ifs with h
  · subst h
    simp [show 2 * m + 2 = 2 * (m + 1) by ring]
  · rfl

/-- The closed chain of a crown. -/
def toClosedChain [IsRayCategory P] : ClosedChain P (C.n - 1) :=
  ClosedChain.ofSeq (C.n - 1) C.f (fun i ↦ C.peak i) (fun i ↦ by
    have h := C.valley i
    have hn' : C.n - 1 + 1 = C.n := Nat.sub_add_cancel C.hn
    have key : ∀ t s, t % (2 * (C.n - 1 + 1)) = s % (2 * (C.n - 1 + 1)) → C.f t = C.f s := by
      intro t s h'
      rw [C.f_mod t, C.f_mod s]
      rw [hn'] at h'
      exact congrArg _ h'
    have e : C.f (2 * i.1 + 2) = C.f (2 * (i + 1 : Fin (C.n - 1 + 1)).1) :=
      key _ _ (two_mul_succ_mod i).symm
    rwa [e] at h) C.ne

/-- Rotation by two positions. -/
def shift : Crown P where
  n := C.n
  hn := C.hn
  f t := C.f (t + 2)
  per t := by rw [show t + 2 * C.n + 2 = t + 2 + 2 * C.n by ring, C.per]
  peak i := by simpa [show 2 * i + 1 + 2 = 2 * (i + 1) + 1 by ring,
    show 2 * i + 2 = 2 * (i + 1) by ring] using C.peak (i + 1)
  valley i := by simpa [show 2 * i + 1 + 2 = 2 * (i + 1) + 1 by ring,
    show 2 * i + 2 + 2 = 2 * (i + 1) + 2 by ring] using C.valley (i + 1)
  ne t := C.ne _

lemma f_add_mul (t k : ℕ) : C.f (t + 2 * C.n * k) = C.f t := by
  induction k with
  | zero => simp
  | succ k ih => rw [show t + 2 * C.n * (k + 1) = t + 2 * C.n * k + 2 * C.n by ring, C.per, ih]

/-- Reversal: read the crown backwards (`t ↦ 1 - t`). -/
def rev : Crown P where
  n := C.n
  hn := C.hn
  f t := C.f (2 * C.n * (t + 1) + 1 - t)
  per t := by
    have h := C.hn
    rw [show 2 * C.n * (t + 2 * C.n + 1) + 1 - (t + 2 * C.n) =
      2 * C.n * (t + 1) + 1 - t + 2 * C.n * (2 * C.n - 1) by
        have e1 : 2 * C.n * (t + 2 * C.n + 1) = 2 * C.n * (t + 1) + 2 * C.n * (2 * C.n) := by ring
        have e2 : 2 * C.n * (2 * C.n) = 2 * C.n * (2 * C.n - 1) + 2 * C.n := by
          rw [Nat.mul_sub, mul_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ (by omega))]
        have e3 : t < 2 * C.n * (t + 1) := by nlinarith
        omega]
    exact C.f_add_mul _ _
  peak i := by
    have hA : 2 * C.n * (2 * i + 1 + 1) + 1 - (2 * i + 1) + 1 =
        2 * C.n * (2 * i + 1) + 1 - 2 * i + 2 * C.n := by
      have e3 : 2 * i + 1 < 2 * C.n * (2 * i + 1) := by have := C.hn; nlinarith
      have e1 : 2 * C.n * (2 * i + 1 + 1) = 2 * C.n * (2 * i + 1) + 2 * C.n := by ring
      omega
    have hev : 2 * C.n * (2 * i + 1 + 1) + 1 - (2 * i + 1) =
        2 * (C.n * (2 * i + 2) - i) := by
      have e3 : i < C.n * (2 * i + 2) := by have := C.hn; nlinarith
      have e1 : 2 * C.n * (2 * i + 1 + 1) = 2 * (C.n * (2 * i + 2)) := by ring
      omega
    have h := C.peak (C.n * (2 * i + 2) - i)
    rw [← hev] at h
    rw [hA, C.per] at h
    exact h.symm
  valley i := by
    have hev : 2 * C.n * (2 * i + 1 + 1) + 1 - (2 * i + 1) =
        2 * (C.n * (2 * i + 2) - i - 1) + 2 := by
      have e3 : i + 1 < C.n * (2 * i + 2) := by have := C.hn; nlinarith
      have e1 : 2 * C.n * (2 * i + 1 + 1) = 2 * (C.n * (2 * i + 2)) := by ring
      omega
    have hod : 2 * C.n * (2 * i + 2 + 1) + 1 - (2 * i + 2) =
        2 * (C.n * (2 * i + 2) - i - 1) + 1 + 2 * C.n := by
      have e3 : i + 1 < C.n * (2 * i + 2) := by have := C.hn; nlinarith
      have e1 : 2 * C.n * (2 * i + 2 + 1) = 2 * (C.n * (2 * i + 2)) + 2 * C.n := by ring
      omega
    have h := C.valley (C.n * (2 * i + 2) - i - 1)
    rw [← C.per (2 * _ + 1), ← hod, ← hev] at h
    exact h.symm
  ne t := C.ne _

/-- The dual crown in `Pᵒᵖ`. -/
def op : Crown Pᵒᵖ where
  n := C.n
  hn := C.hn
  f t := opRM (C.f (t + 1))
  per t := by rw [show t + 2 * C.n + 1 = t + 1 + 2 * C.n by ring, C.per]
  peak i := by
    have h := C.valley i
    exact (valley_iff_peak_op _ _).1 h
  valley i := by
    have h := C.peak (i + 1)
    have e1 : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
    have e2 : 2 * (i + 1) + 1 = 2 * i + 2 + 1 := by ring
    rw [e2, e1] at h
    exact (peak_iff_valley_op _ _).1 h
  ne t h := C.ne (t + 1) (by
    have := congrArg Quiver.Hom.unop h
    exact this)

/-- The weight: the sum of the depths. -/
def weight : ℕ := ∑ t ∈ Finset.range (2 * C.n), depth (C.f t).2.2

/-- `C` is minimal for the lexicographic order on `(n, weight)`. -/
def IsMin : Prop := ∀ C' : Crown P, C.n < C'.n ∨ (C.n = C'.n ∧ C.weight ≤ C'.weight)

end Crown

open Classical in
/-- **A minimal crown exists** as soon as a crown exists. -/
lemma Crown.exists_isMin (h : Nonempty (Crown P)) : ∃ C : Crown P, C.IsMin := by
  have h1 : ∃ n, ∃ C : Crown P, C.n = n := ⟨_, h.some, rfl⟩
  have h2 : ∃ w, ∃ C : Crown P, C.n = Nat.find h1 ∧ C.weight = w := by
    obtain ⟨C, hC⟩ := Nat.find_spec h1
    exact ⟨_, C, hC, rfl⟩
  obtain ⟨C, hCn, hCw⟩ := Nat.find_spec h2
  refine ⟨C, fun C' ↦ ?_⟩
  have hn : Nat.find h1 ≤ C'.n := Nat.find_min' h1 ⟨C', rfl⟩
  rcases lt_or_eq_of_le hn with hlt | heq
  · exact Or.inl (hCn ▸ hlt)
  · refine Or.inr ⟨hCn.trans heq, ?_⟩
    rw [hCw]
    exact Nat.find_min' h2 ⟨C', heq.symm, rfl⟩

end RayCat

end LargeIndecomposable
