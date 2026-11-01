module

public import LargeIndecomposable.Crowns.Section225.Arrow

/-!
# BO13a §2.2.5: the shorter crown

`MulBasis.b2_core`: for long entries `σ₁ = σ (s+2)` and `ρⱼ = ρ (s+3+L+1)` (`j = L+2`),
split at `a` and `c'`, with `ρⱼ = γ ≫ ρ₁ ≫ δ` and `v₁', v₂'` arrows,
`(γ ≫ V₁, r, σₙ, …, ρⱼ₊₁, r'', V₁')` is a crown of length `2(n - j + 1) < 2n` unless
`V₁'` factors as `γ ≫ V₁ ≫ c` (BO13a's last case, "the domains coincide").
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

/-- Two split pieces with the same (transported) source form a valley. -/
lemma valley_pieces {X X' C C' Y Y' Z Z' : P} (r'' : X ⟶ C) (V₂' : C ⟶ Y) (σa : X ⟶ Y)
    (h1 : r'' ≫ V₂' = σa) (ρa : X ⟶ Z) (L8d : ¬∃ c, r'' ≫ c = ρa) (r : X' ⟶ C')
    (V₂ : C' ⟶ Z') (ρb : X' ⟶ Z') (h2 : r ≫ V₂ = ρb) (σb : X' ⟶ Y')
    (L8b : ¬∃ c, r ≫ c = σb) (E1 : (⟨X, Y, σa⟩ : RayMor P) = ⟨X', Y', σb⟩)
    (E2 : (⟨X, Z, ρa⟩ : RayMor P) = ⟨X', Z', ρb⟩) : Valley ⟨X, C, r''⟩ ⟨X', C', r⟩ := by
  cases E1
  cases E2
  refine (valley_mk_iff r'' r).2 ⟨fun ⟨k, hk⟩ ↦ L8d ⟨k ≫ V₂, ?_⟩, fun ⟨k, hk⟩ ↦ L8b ⟨k ≫ V₂', ?_⟩⟩
  · rw [← Category.assoc, hk, h2]
  · rw [← Category.assoc, hk, h1]

end RayCat

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

/-- The entries of the shorter crown: four new entries around a segment of `C`. -/
def Crown.spliceF (C : Crown P) (n' P₀ : ℕ) (e0 e1 e2 e3 : RayMor P) (t : ℕ) : RayMor P :=
  if t = 0 then e0 else if t = 1 then e1 else if t = 2 * n' - 2 then e2 else
    if t = 2 * n' - 1 then e3 else C.f (t + P₀)

section Splice

variable (C : Crown P) (n' P₀ : ℕ) (e0 e1 e2 e3 : RayMor P)

lemma Crown.spliceF_0 : C.spliceF n' P₀ e0 e1 e2 e3 0 = e0 := by simp [Crown.spliceF]

lemma Crown.spliceF_1 (h : 2 ≤ n') : C.spliceF n' P₀ e0 e1 e2 e3 1 = e1 := by
  unfold Crown.spliceF; rw [ite_eq_right (by omega), ite_eq_left rfl]

lemma Crown.spliceF_2 (h : 2 ≤ n') : C.spliceF n' P₀ e0 e1 e2 e3 (2 * n' - 2) = e2 := by
  unfold Crown.spliceF; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]

lemma Crown.spliceF_3 (h : 2 ≤ n') : C.spliceF n' P₀ e0 e1 e2 e3 (2 * n' - 1) = e3 := by
  unfold Crown.spliceF
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]

lemma Crown.spliceF_mid (t : ℕ) (h1 : 2 ≤ t) (h2 : t + 3 ≤ 2 * n') :
    C.spliceF n' P₀ e0 e1 e2 e3 t = C.f (t + P₀) := by
  unfold Crown.spliceF
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega)]

end Splice

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A]

/-- **BO13a §2.2.5, the case `σ₁ … ρⱼ`: the shorter crown.** -/
theorem b2_core (hL : LeftCancel P) (C : Crown P) (hC : C.IsMin) (s L : ℕ)
    (hLn : L + 3 ≤ C.n)
    {a c' : P} (V₁ : C.toZChain.x (s + 3) ⟶ a) (V₂ : a ⟶ C.toZChain.z (s + 2))
    (ρ₁' : a ⟶ C.toZChain.z (s + 3)) (r : C.toZChain.x (s + 2) ⟶ a)
    (hV : V₁ ≫ V₂ = C.toZChain.σ (s + 2)) (hρ₁' : V₁ ≫ ρ₁' = C.toZChain.ρ (s + 3))
    (hr : r ≫ V₂ = C.toZChain.ρ (s + 2)) (hz : r ≫ ρ₁' = 0) (hiV₁ : ¬IsIso V₁)
    (V₁' : C.toZChain.x (s + 3 + L + 1) ⟶ c') (V₂' : c' ⟶ C.toZChain.z (s + 3 + L + 1))
    (r'' : C.toZChain.x (s + 3 + L + 1 + 1) ⟶ c')
    (hV' : V₁' ≫ V₂' = C.toZChain.ρ (s + 3 + L + 1))
    (hr'' : r'' ≫ V₂' = C.toZChain.σ (s + 3 + L + 1))
    (hirr₁ : IsIrreducible V₁') (hirr₂ : IsIrreducible V₂')
    (γ : C.toZChain.x (s + 3 + L + 1) ⟶ C.toZChain.x (s + 3))
    (δ : C.toZChain.z (s + 3) ⟶ C.toZChain.z (s + 3 + L + 1))
    (hγ : γ ≫ C.toZChain.ρ (s + 3) ≫ δ = C.toZChain.ρ (s + 3 + L + 1))
    (L8b : ¬∃ c, r ≫ c = C.toZChain.σ (s + 1))
    (L8d : ¬∃ c, r'' ≫ c = C.toZChain.ρ (s + 3 + L + 1 + 1))
    (hρ₁l : ¬IsLong (C.toZChain.ρ (s + 3)))
    (hlam : IsLong (C.toZChain.ρ (s + 3 + L + 1))) : ∃ c, (γ ≫ V₁) ≫ c = V₁' := by
  by_contra hno
  have hlam0 : C.toZChain.ρ (s + 3 + L + 1) ≠ 0 := hlam.1
  have hγV0 : γ ≫ V₁ ≠ 0 := fun h ↦ hlam0 (by rw [← hγ, ← hρ₁', ← Category.assoc, ← Category.assoc,
    h, zero_comp, zero_comp])
  -- BO13a's third case: `V₁' ≫ k = γ ≫ V₁`
  have hiρ₁' : ¬IsIso ρ₁' := fun _ ↦
    C.toZChain.valley₂ (s + 2) ⟨inv ρ₁' ≫ V₂, by rw [← hρ₁', ← hV]; simp⟩
  have h6a : ¬∃ k, V₁' ≫ k = γ ≫ V₁ := by
    rintro ⟨k, hk⟩
    have e : V₁' ≫ V₂' = V₁' ≫ (k ≫ ρ₁' ≫ δ) := by
      calc V₁' ≫ V₂' = γ ≫ (V₁ ≫ ρ₁') ≫ δ := by rw [hV', hρ₁', hγ]
        _ = (V₁' ≫ k) ≫ ρ₁' ≫ δ := by rw [hk]; simp
        _ = V₁' ≫ (k ≫ ρ₁' ≫ δ) := by simp
    have hV₂' : V₂' = k ≫ ρ₁' ≫ δ := hL _ _ _ e (by rw [hV']; exact hlam0)
    rcases hirr₂.2.2 _ k (ρ₁' ≫ δ) hV₂' with hk' | hk'
    · -- `k` invertible: `γ` and `δ` are invertible, so `ρ₁` is long
      have hV₁'e : V₁' = γ ≫ (V₁ ≫ inv k) := by rw [← Category.assoc, ← hk]; simp
      have hirrρδ : IsIrreducible (ρ₁' ≫ δ) := by
        have e2 : ρ₁' ≫ δ = inv k ≫ V₂' := by rw [hV₂']; simp
        rw [e2]; exact IsIrreducible.isIso_comp hirr₂ (inv k)
      rcases hirrρδ.2.2 _ ρ₁' δ rfl with h | hδi
      · exact hiρ₁' h
      rcases hirr₁.2.2 _ γ (V₁ ≫ inv k) hV₁'e with hγi | hVi
      · apply hρ₁l
        refine hlam.of_factorsThrough (C.toZChain.ρ_ne _) ⟨inv γ, inv δ, ?_⟩
        rw [← hγ]; simp
      · exact hiV₁ (isIso_of_isIso_comp V₁ (inv k) (fun h ↦ hγV0 (by rw [h, comp_zero])) hVi)
    · exact hiρ₁' (isIso_of_isIso_comp ρ₁' δ (fun h ↦ hlam0 (by
        rw [← hγ, ← hρ₁', Category.assoc, h]; simp)) hk')
  -- the shorter crown
  obtain ⟨n', hn'⟩ : ∃ n', n' = C.n - L - 1 := ⟨_, rfl⟩
  have hn2 : 2 ≤ n' := by omega
  have hr0 : r ≠ 0 := fun h ↦ C.toZChain.ρ_ne (s + 2) (by rw [← hr, h, zero_comp])
  have hr''0 : r'' ≠ 0 := fun h ↦ C.toZChain.σ_ne _ (by rw [← hr'', h, zero_comp])
  let e0 : RayMor P := ⟨_, _, V₁'⟩
  let e1 : RayMor P := ⟨_, _, r''⟩
  let e2 : RayMor P := ⟨_, _, r⟩
  let e3 : RayMor P := ⟨_, _, γ ≫ V₁⟩
  have p01 : Peak e0 e1 := (peak_mk_iff V₁' r'').2
    ⟨fun ⟨k, hk⟩ ↦ C.toZChain.peak₁ (s + 3 + L + 1) ⟨k, by rw [← hr'', ← Category.assoc, hk, hV']⟩,
      fun ⟨k, hk⟩ ↦ C.toZChain.peak₂ (s + 3 + L + 1) ⟨k, by rw [← hV', ← Category.assoc, hk, hr'']⟩⟩
  have p23 : Peak e2 e3 := (peak_mk_iff r (γ ≫ V₁)).2
    ⟨fun ⟨k, hk⟩ ↦ C.toZChain.peak₁ (s + 2) ⟨k ≫ γ, by
        rw [← hr, ← hk, ← hV]; simp⟩,
      fun ⟨k, hk⟩ ↦ hlam0 (by
        rw [← hγ, ← hρ₁', ← Category.assoc, ← Category.assoc, ← hk]; simp [hz])⟩
  have v30 : Valley e3 e0 := (valley_mk_iff (γ ≫ V₁) V₁').2 ⟨hno, h6a⟩
  have v1mid : ∀ (h3 : 3 ≤ n'), Valley e1 (C.f (2 * (s + 3 + L + 1 + 1))) := fun _ ↦
    (valley_mk_iff r'' (C.toZChain.ρ (s + 3 + L + 1 + 1))).2
      ⟨L8d, fun ⟨k, hk⟩ ↦ C.toZChain.valley₂ (s + 3 + L + 1)
        ⟨k ≫ V₂', by rw [← Category.assoc, hk, hr'']⟩⟩
  have vmid2 : Valley (C.f (2 * (s + 1) + 1)) e2 := by
    rw [← Crown.toZChain_σ]
    exact (valley_mk_iff (C.toZChain.σ (s + 1)) r).2
      ⟨fun ⟨k, hk⟩ ↦ C.toZChain.valley₁ (s + 1) ⟨k ≫ V₂, by rw [← Category.assoc, hk, hr]⟩, L8b⟩
  have hidx : 2 * n' - 3 + 2 * (s + 3 + L + 1) = 2 * (s + 1) + 1 + 2 * C.n := by omega
  let G := C.spliceF n' (2 * (s + 3 + L + 1)) e0 e1 e2 e3
  have hp : ∀ i < n', Peak (G (2 * i)) (G (2 * i + 1)) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · change Peak (C.spliceF n' _ e0 e1 e2 e3 0) (C.spliceF n' _ e0 e1 e2 e3 1)
      rw [Crown.spliceF_0, Crown.spliceF_1 _ _ _ _ _ _ _ hn2]
      exact p01
    · by_cases hlast : i = n' - 1
      · change Peak (C.spliceF n' _ e0 e1 e2 e3 (2 * i)) (C.spliceF n' _ e0 e1 e2 e3 (2 * i + 1))
        rw [show 2 * i = 2 * n' - 2 by omega, show 2 * n' - 2 + 1 = 2 * n' - 1 by omega,
          Crown.spliceF_2 _ _ _ _ _ _ _ hn2, Crown.spliceF_3 _ _ _ _ _ _ _ hn2]
        exact p23
      · change Peak (C.spliceF n' _ e0 e1 e2 e3 (2 * i)) (C.spliceF n' _ e0 e1 e2 e3 (2 * i + 1))
        rw [Crown.spliceF_mid _ _ _ _ _ _ _ _ (by omega) (by omega),
          Crown.spliceF_mid _ _ _ _ _ _ _ _ (by omega) (by omega)]
        have := C.peak (i + (s + 3 + L + 1))
        rwa [show 2 * i + 2 * (s + 3 + L + 1) = 2 * (i + (s + 3 + L + 1)) by ring,
          show 2 * i + 1 + 2 * (s + 3 + L + 1) = 2 * (i + (s + 3 + L + 1)) + 1 by ring]
  have hv : ∀ i, i + 1 < n' → Valley (G (2 * i + 1)) (G (2 * i + 2)) := by
    intro i hi
    change Valley (C.spliceF n' _ e0 e1 e2 e3 (2 * i + 1)) (C.spliceF n' _ e0 e1 e2 e3 (2 * i + 2))
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [show 2 * 0 + 1 = 1 by rfl, Crown.spliceF_1 _ _ _ _ _ _ _ hn2]
      by_cases h2 : n' = 2
      · subst h2
        rw [show 2 * 0 + 2 = 2 * 2 - 2 by rfl, Crown.spliceF_2 _ _ _ _ _ _ _ le_rfl]
        have hLn' : L + 3 = C.n := by omega
        refine valley_pieces r'' V₂' _ hr'' _ L8d r V₂ _ hr _ L8b ?_ ?_
        · rw [Crown.toZChain_σ, Crown.toZChain_σ, show 2 * (s + 3 + L + 1) + 1 =
            2 * (s + 1) + 1 + 2 * C.n by omega, C.per]
        · rw [Crown.toZChain_ρ, Crown.toZChain_ρ, show 2 * (s + 3 + L + 1 + 1) =
            2 * (s + 2) + 2 * C.n by omega, C.per]
      · rw [Crown.spliceF_mid _ _ _ _ _ _ _ _ (by omega) (by omega),
          show 2 * 0 + 2 + 2 * (s + 3 + L + 1) = 2 * (s + 3 + L + 1 + 1) by ring]
        exact v1mid (by omega)
    · by_cases hlast : i + 2 = n'
      · rw [show 2 * i + 1 = 2 * n' - 3 by omega, show 2 * i + 2 = 2 * n' - 2 by omega,
          Crown.spliceF_mid _ _ _ _ _ _ _ _ (by omega) (by omega),
          Crown.spliceF_2 _ _ _ _ _ _ _ hn2, hidx, C.per]
        exact vmid2
      · rw [Crown.spliceF_mid _ _ _ _ _ _ _ _ (by omega) (by omega),
          Crown.spliceF_mid _ _ _ _ _ _ _ _ (by omega) (by omega)]
        have := C.valley (i + (s + 3 + L + 1))
        rwa [show 2 * i + 1 + 2 * (s + 3 + L + 1) = 2 * (i + (s + 3 + L + 1)) + 1 by ring,
          show 2 * i + 2 + 2 * (s + 3 + L + 1) = 2 * (i + (s + 3 + L + 1)) + 2 by ring]
  have hv' : Valley (G (2 * n' - 1)) (G 0) := by
    change Valley (C.spliceF n' _ e0 e1 e2 e3 (2 * n' - 1)) (C.spliceF n' _ e0 e1 e2 e3 0)
    rw [Crown.spliceF_3 _ _ _ _ _ _ _ hn2, Crown.spliceF_0]
    exact v30
  have hne : ∀ t < 2 * n', (G t).2.2 ≠ 0 := by
    intro t ht
    change (C.spliceF n' _ e0 e1 e2 e3 t).2.2 ≠ 0
    unfold Crown.spliceF
    by_cases h0 : t = 0
    · rw [ite_eq_left h0]; exact hirr₁.1
    rw [ite_eq_right h0]
    by_cases h1 : t = 1
    · rw [ite_eq_left h1]; exact hr''0
    rw [ite_eq_right h1]
    by_cases h2 : t = 2 * n' - 2
    · rw [ite_eq_left h2]; exact hr0
    rw [ite_eq_right h2]
    by_cases h3 : t = 2 * n' - 1
    · rw [ite_eq_left h3]; exact hγV0
    rw [ite_eq_right h3]
    exact C.ne _
  rcases hC (Crown.ofFn n' (by omega) G hp hv hv' hne) with h | h
  · change C.n < n' at h
    omega
  · change C.n = n' ∧ _ at h
    omega

/-- **BO13a §2.2.5, the case `σ₁ … σⱼ`: the shorter crown** `(ρⱼ, σⱼ₊₁, …, σₙ, r, γ ≫ V₁)`
and BO13a's last case: `γ` is invertible. -/
theorem b3_core (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (C : Crown P) (hC : C.IsMin) (s L : ℕ) (hLn : L + 4 ≤ C.n)
    {a : P} (V₁ : C.toZChain.x (s + 3) ⟶ a) (V₂ : a ⟶ C.toZChain.z (s + 2))
    (ρ₁' : a ⟶ C.toZChain.z (s + 3)) (r : C.toZChain.x (s + 2) ⟶ a)
    (hV : V₁ ≫ V₂ = C.toZChain.σ (s + 2)) (hρ₁' : V₁ ≫ ρ₁' = C.toZChain.ρ (s + 3))
    (hr : r ≫ V₂ = C.toZChain.ρ (s + 2)) (hz : r ≫ ρ₁' = 0)
    (hirr₁ : IsIrreducible V₁) (hirr₂ : IsIrreducible V₂)
    (γ : C.toZChain.x (s + 3 + L + 1 + 1) ⟶ C.toZChain.x (s + 3))
    (δ : C.toZChain.z (s + 3) ⟶ C.toZChain.z (s + 3 + L + 1))
    (hγ : γ ≫ C.toZChain.ρ (s + 3) ≫ δ = C.toZChain.σ (s + 3 + L + 1))
    (γ' : C.toZChain.x (s + 3) ⟶ C.toZChain.x (s + 3 + L + 1 + 1))
    (δ' : C.toZChain.z (s + 3 + L + 1 + 1) ⟶ C.toZChain.z (s + 2))
    (hγ' : γ' ≫ C.toZChain.ρ (s + 3 + L + 1 + 1) ≫ δ' = C.toZChain.σ (s + 2))
    (L8b : ¬∃ c, r ≫ c = C.toZChain.σ (s + 1)) : IsIso γ := by
  have hσ0 := C.toZChain.σ_ne (s + 2)
  have hlam0 := C.toZChain.σ_ne (s + 3 + L + 1)
  have hγV0 : γ ≫ V₁ ≠ 0 := fun h ↦ hlam0 (by
    rw [← hγ, ← hρ₁', ← Category.assoc, ← Category.assoc, h, zero_comp, zero_comp])
  have hr0 : r ≠ 0 := fun h ↦ C.toZChain.ρ_ne (s + 2) (by rw [← hr, h, zero_comp])
  -- the shorter crown, unless `ρⱼ = γ ≫ V₁ ≫ k`
  obtain ⟨k, hk⟩ : ∃ k, (γ ≫ V₁) ≫ k = C.toZChain.ρ (s + 3 + L + 1 + 1) := by
    by_contra hno
    obtain ⟨n', hn'⟩ : ∃ n', n' = C.n - L - 2 := ⟨_, rfl⟩
    have hn2 : 2 ≤ n' := by omega
    let e2 : RayMor P := ⟨_, _, r⟩
    let e3 : RayMor P := ⟨_, _, γ ≫ V₁⟩
    let P₀ := 2 * (s + 3 + L + 1 + 1)
    have p23 : Peak e2 e3 := (peak_mk_iff r (γ ≫ V₁)).2
      ⟨fun ⟨k, hk⟩ ↦ C.toZChain.peak₁ (s + 2) ⟨k ≫ γ, by rw [← hr, ← hk, ← hV]; simp⟩,
        fun ⟨k, hk⟩ ↦ hlam0 (by
          rw [← hγ, ← hρ₁', ← Category.assoc, ← Category.assoc, ← hk]; simp [hz])⟩
    have v30 : Valley e3 (C.f P₀) := (valley_mk_iff (γ ≫ V₁)
        (C.toZChain.ρ (s + 3 + L + 1 + 1))).2
      ⟨hno, fun ⟨k, hk⟩ ↦ C.toZChain.valley₂ (s + 3 + L + 1)
        ⟨k ≫ ρ₁' ≫ δ, by rw [← Category.assoc, hk, ← hγ, ← hρ₁']; simp⟩⟩
    have vmid2 : Valley (C.f (2 * (s + 1) + 1)) e2 := by
      rw [← Crown.toZChain_σ]
      exact (valley_mk_iff (C.toZChain.σ (s + 1)) r).2
        ⟨fun ⟨k, hk⟩ ↦ C.toZChain.valley₁ (s + 1) ⟨k ≫ V₂, by rw [← Category.assoc, hk, hr]⟩,
          L8b⟩
    have hidx : 2 * n' - 3 + P₀ = 2 * (s + 1) + 1 + 2 * C.n := by omega
    let G := C.spliceF n' P₀ (C.f (0 + P₀)) (C.f (1 + P₀)) e2 e3
    have hG01 : ∀ t, t + 3 ≤ 2 * n' → G t = C.f (t + P₀) := by
      intro t ht
      rcases Nat.lt_or_ge t 2 with h | h
      · interval_cases t
        · exact Crown.spliceF_0 _ _ _ _ _ _ _
        · exact Crown.spliceF_1 _ _ _ _ _ _ _ hn2
      · exact Crown.spliceF_mid _ _ _ _ _ _ _ _ h ht
    have hp : ∀ i < n', Peak (G (2 * i)) (G (2 * i + 1)) := by
      intro i hi
      by_cases hlast : i = n' - 1
      · change Peak (C.spliceF n' _ _ _ e2 e3 (2 * i)) (C.spliceF n' _ _ _ e2 e3 (2 * i + 1))
        rw [show 2 * i = 2 * n' - 2 by omega, show 2 * n' - 2 + 1 = 2 * n' - 1 by omega,
          Crown.spliceF_2 _ _ _ _ _ _ _ hn2, Crown.spliceF_3 _ _ _ _ _ _ _ hn2]
        exact p23
      · rw [hG01 _ (by omega), hG01 _ (by omega)]
        have := C.peak (i + (s + 3 + L + 1 + 1))
        rwa [show 2 * i + P₀ = 2 * (i + (s + 3 + L + 1 + 1)) by ring,
          show 2 * i + 1 + P₀ = 2 * (i + (s + 3 + L + 1 + 1)) + 1 by ring]
    have hv : ∀ i, i + 1 < n' → Valley (G (2 * i + 1)) (G (2 * i + 2)) := by
      intro i hi
      by_cases hlast : i + 2 = n'
      · rw [hG01 _ (by omega)]
        change Valley (C.f (2 * i + 1 + P₀)) (C.spliceF n' _ _ _ e2 e3 (2 * i + 2))
        rw [show 2 * i + 2 = 2 * n' - 2 by omega, Crown.spliceF_2 _ _ _ _ _ _ _ hn2,
          show 2 * i + 1 + P₀ = 2 * n' - 3 + P₀ by omega, hidx, C.per]
        exact vmid2
      · rw [hG01 _ (by omega), hG01 _ (by omega)]
        have := C.valley (i + (s + 3 + L + 1 + 1))
        rwa [show 2 * i + 1 + P₀ = 2 * (i + (s + 3 + L + 1 + 1)) + 1 by ring,
          show 2 * i + 2 + P₀ = 2 * (i + (s + 3 + L + 1 + 1)) + 2 by ring]
    have hv' : Valley (G (2 * n' - 1)) (G 0) := by
      rw [hG01 0 (by omega), Nat.zero_add]
      change Valley (C.spliceF n' _ _ _ e2 e3 (2 * n' - 1)) _
      rw [Crown.spliceF_3 _ _ _ _ _ _ _ hn2]
      exact v30
    have hne : ∀ t < 2 * n', (G t).2.2 ≠ 0 := by
      intro t ht
      by_cases h2 : t = 2 * n' - 2
      · subst h2
        change (C.spliceF n' _ _ _ e2 e3 (2 * n' - 2)).2.2 ≠ 0
        rw [Crown.spliceF_2 _ _ _ _ _ _ _ hn2]; exact hr0
      by_cases h3 : t = 2 * n' - 1
      · subst h3
        change (C.spliceF n' _ _ _ e2 e3 (2 * n' - 1)).2.2 ≠ 0
        rw [Crown.spliceF_3 _ _ _ _ _ _ _ hn2]; exact hγV0
      rw [hG01 t (by omega)]
      exact C.ne _
    rcases hC (Crown.ofFn n' (by omega) G hp hv hv' hne) with h | h
    · change C.n < n' at h
      omega
    · change C.n = n' ∧ _ at h
      omega
  -- BO13a's last case
  have hk0 : ¬IsIso k := fun _ ↦ C.toZChain.valley₂ (s + 3 + L + 1)
    ⟨inv k ≫ ρ₁' ≫ δ, by rw [← hγ, ← hρ₁', ← hk]; simp⟩
  have hε0 : k ≫ δ' ≠ 0 := fun h ↦ hσ0 (by rw [← hγ', ← hk]; simp [h])
  have hεi : ¬IsIso (k ≫ δ') := fun h ↦ hk0 (isIso_of_isIso_comp k δ'
    (fun h' ↦ hε0 (by rw [h', zero_comp])) h)
  have hσu : (γ' ≫ γ) ≫ V₁ ≫ (k ≫ δ') = C.toZChain.σ (s + 2) := by
    rw [← hγ', ← hk]; simp
  have hV₂0 : V₂ ≠ 0 := hirr₂.1
  suffices hu : γ' ≫ γ = 𝟙 _ by
    have hγ'i : IsIso γ' := isIso_of_isIso_comp γ' γ (fun h ↦ hσ0 (by
      rw [← hσu, h]; simp)) (by rw [hu]; infer_instance)
    haveI : IsIso (γ' ≫ γ) := by rw [hu]; infer_instance
    exact IsIso.of_isIso_comp_left γ' γ
  have key : ∀ V : a ⟶ C.toZChain.z (s + 2), V₂ = V → V = k ≫ δ' → γ' ≫ γ = 𝟙 _ := by
    intro V hV₂V hVe
    subst hV₂V
    refine (IsRayCategory.eq_id_of_two_sided _ hσ0 (γ' ≫ γ) (𝟙 _) ?_).1
    conv_lhs => rw [← hσu, ← hVe, hV]
    simp
  rcases cmp4 hQ (k ≫ δ') V₂ hε0 hV₂0 with ⟨b, hb⟩ | ⟨a', ha⟩ | ⟨b, hb⟩ | ⟨a', ha⟩
  · rcases hirr₂.2.2 _ (k ≫ δ') b hb with h | h
    · exact absurd h hεi
    · obtain ⟨hyy, hb1⟩ := eq_eqToHom_of_isIso (show _ ⟶ _ from b)
      exact key V₂ rfl (by rw [hb]; change _ ≫ (b : _ ⟶ _) = _; rw [hb1]; simp)
  · rcases hirr₂.2.2 _ a' (k ≫ δ') ha with h | h
    · obtain ⟨hyy, ha1⟩ := eq_eqToHom_of_isIso (show _ ⟶ _ from a')
      exact key V₂ rfl (by rw [ha]; change (a' : _ ⟶ _) ≫ _ = _; rw [ha1]; simp)
    · exact absurd h hεi
  · rw [hb] at hσu
    refine (IsRayCategory.eq_id_of_two_sided _ hσ0 (γ' ≫ γ) b ?_).1
    conv_lhs => rw [← hσu]
    rw [← hV]
    simp
  · rw [ha] at hσu
    have e : ((γ' ≫ γ) ≫ V₁ ≫ a') ≫ V₂ = V₁ ≫ V₂ := by rw [hV, ← hσu]; simp
    have e2 := hR _ _ _ e (by rw [e, hV]; exact hσ0)
    exact (IsRayCategory.eq_id_of_two_sided V₁ hirr₁.1 (γ' ≫ γ) a' e2.symm).1

end MulBasis

end RayQuiver

end LargeIndecomposable
