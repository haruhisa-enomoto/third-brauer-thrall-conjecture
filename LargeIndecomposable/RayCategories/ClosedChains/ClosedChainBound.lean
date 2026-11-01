module

public import LargeIndecomposable.RayCategories.ClosedChains.ClosedChainOf

/-!
# A closed chain makes chains unbounded

Going around a closed chain again and again gives chains of every length
(`ClosedChain.not_chainBounded`), the converse of `exists_closedChain`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

variable {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] {m : ℕ}

namespace ClosedChain

variable (C : ClosedChain Q m)

/-- The `i`-th left morphism `ρᵢ`. -/
def rhoM (i : Fin (m + 1)) : RayMor Q := ⟨C.x i, C.z i, C.ρ i⟩

/-- The `i`-th right morphism `σᵢ`. -/
def sigmaM (i : Fin (m + 1)) : RayMor Q := ⟨C.x (i + 1), C.z i, C.σ i⟩

/-- A natural number modulo `m + 1`. -/
def cidx (m t : ℕ) : Fin (m + 1) := ⟨t % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩

omit [Category Q] [HasZeroMorphisms Q] in
lemma cidx_succ (t : ℕ) : cidx m (t + 1) = cidx m t + 1 := by
  rcases m with _ | m
  · exact Fin.ext (by simp [cidx, Fin.val_add, Nat.mod_one])
  · ext
    simp only [cidx, Fin.val_add, Fin.val_one]
    rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < m + 1 + 1 by omega)]

/-- The periodic sequence `ρ₀, σ₀, ρ₁, σ₁, …`. -/
def cseq (t : ℕ) : RayMor Q :=
  if t % 2 = 0 then C.rhoM (cidx m (t / 2)) else C.sigmaM (cidx m (t / 2))

lemma cseq_even (t : ℕ) : C.cseq (2 * t) = C.rhoM (cidx m t) := by
  simp [cseq]

lemma cseq_odd (t : ℕ) : C.cseq (2 * t + 1) = C.sigmaM (cidx m t) := by
  simp only [cseq]
  rw [if_neg (by omega), show (2 * t + 1) / 2 = t by omega]

lemma peak_rho_sigma (i : Fin (m + 1)) : Peak (C.rhoM i) (C.sigmaM i) := by
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨c, hc⟩
    exact C.peak₁ i ⟨c, by simpa [rhoM, sigmaM] using hc⟩
  · rintro ⟨c, hc⟩
    exact C.peak₂ i ⟨c, by simpa [rhoM, sigmaM] using hc⟩

lemma valley_sigma_rho (i : Fin (m + 1)) : Valley (C.sigmaM i) (C.rhoM (i + 1)) := by
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨c, hc⟩
    have hc' : 𝟙 _ ≫ C.σ i ≫ c = C.ρ (i + 1) := hc
    rw [Category.id_comp] at hc'
    exact C.valley₁ i ⟨c, hc'⟩
  · rintro ⟨c, hc⟩
    have hc' : 𝟙 _ ≫ C.ρ (i + 1) ≫ c = C.σ i := hc
    rw [Category.id_comp] at hc'
    exact C.valley₂ i ⟨c, hc'⟩

lemma link_seq (j : ℕ) : Link j (C.cseq j) (C.cseq (j + 1)) := by
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' j
  · rw [cseq_even, cseq_odd]
    simpa [Link] using C.peak_rho_sigma (cidx m t)
  · rw [cseq_odd, show 2 * t + 1 + 1 = 2 * (t + 1) by ring, cseq_even, cidx_succ]
    simp only [Link]
    rw [if_neg (by omega)]
    exact C.valley_sigma_rho _

lemma seq_ne (t : ℕ) : (C.cseq t).2.2 ≠ 0 := by
  obtain ⟨t', rfl | rfl⟩ := Nat.even_or_odd' t
  · rw [cseq_even]
    simp only [rhoM]
    exact C.ρ_ne _
  · rw [cseq_odd]
    simp only [sigmaM]
    exact C.σ_ne _

include C in
/-- **A closed chain makes chains unbounded.** -/
theorem not_chainBounded : ¬ChainBounded Q := by
  rintro ⟨N, hN⟩
  have h := hN (List.ofFn fun k : Fin (N + 1) ↦ C.cseq k) ⟨?_, ?_⟩
  · simp at h
  · intro f hf
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hf
    exact C.seq_ne k
  · intro j hj
    simp only [List.getElem_ofFn, Nat.add_zero]
    exact C.link_seq j

end ClosedChain

/-- **A cyclic sequence with alternating peaks and valleys makes chains unbounded.** The
sequence `f 0, …, f (2m+1)` has peaks `(f (2i), f (2i+1))` and valleys `(f (2i+1), f (2i+2))`,
the last valley closing up with `f 0`. -/
theorem not_chainBounded_of_cyclic [IsRayCategory Q] (m : ℕ) (f : ℕ → RayMor Q) (hne : ∀ t, (f t).2.2 ≠ 0)
    (hP : ∀ i ≤ m, Peak (f (2 * i)) (f (2 * i + 1)))
    (hV : ∀ i < m, Valley (f (2 * i + 1)) (f (2 * i + 2))) (hV' : Valley (f (2 * m + 1)) (f 0)) :
    ¬ChainBounded Q := by
  refine (ClosedChain.ofSeq m f (fun i ↦ hP i.1 (by omega)) (fun i ↦ ?_) hne).not_chainBounded
  rcases Nat.lt_or_ge i.1 m with h | h
  · have : (i + 1 : Fin (m + 1)).1 = i.1 + 1 := Fin.val_add_one_of_lt (by
      rw [Fin.lt_iff_val_lt_val]; simp; omega)
    rw [this, show 2 * (i.1 + 1) = 2 * i.1 + 2 by ring]
    exact hV i.1 h
  · have hi : i.1 = m := by omega
    have : (i + 1 : Fin (m + 1)).1 = 0 := by
      rw [Fin.val_add_one]
      split_ifs with h' <;> [rfl; (exfalso; apply h'; ext; simp [hi])]
    rw [this, hi]
    exact hV'

end LargeIndecomposable.RayCat