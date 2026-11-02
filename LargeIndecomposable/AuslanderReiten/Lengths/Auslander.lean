module

public import LargeIndecomposable.AuslanderReiten.AlmostSplit.RightAS

/-!
# Chains, Harada–Sai, and an Auslander-type theorem

`Chain P n c`: `c` is a composite of `n` non-bijective maps between objects satisfying
`P`. If `P`-objects are indecomposable of dimension `≤ b`, a chain of length `2ᵇ − 1` is
zero (`Chain.eq_zero`).

`RASFam P X`: a right almost split family into `X` with sources in `P`.

`auslander`: if every `P`-object has such a family and every nonzero module maps nonzero
into some `P`-object, then every indecomposable module is isomorphic to a `P`-object.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- Composites of non-bijective maps between `P`-objects. -/
inductive Chain (P : FDMod k A → Prop) : ∀ {X Y : FDMod k A}, ℕ → (X ⟶ Y) → Prop
  | nil {X : FDMod k A} (hX : P X) : Chain P 0 (𝟙 X)
  | cons {X Y Z : FDMod k A} (g : X ⟶ Y) (hX : P X) (hg : ¬Function.Bijective (FDMod.lin g))
      {n : ℕ} {c : Y ⟶ Z} (hc : Chain P n c) : Chain P (n + 1) (g ≫ c)

namespace Chain

variable {P : FDMod k A → Prop}

lemma source {X Y : FDMod k A} {n : ℕ} {c : X ⟶ Y} (h : Chain P n c) : P X := by
  cases h with
  | nil hX => exact hX
  | cons _ hX _ _ => exact hX

lemma inv_succ {X Z : FDMod k A} {n : ℕ} {c : X ⟶ Z} (h : Chain P (n + 1) c) :
    ∃ (Y : FDMod k A) (g : X ⟶ Y) (c' : Y ⟶ Z), P X ∧ ¬Function.Bijective (FDMod.lin g) ∧
      Chain P n c' ∧ c = g ≫ c' := by
  cases h with
  | cons g hX hg hc => exact ⟨_, g, _, hX, hg, hc, rfl⟩

lemma split {X Z : FDMod k A} (a : ℕ) : ∀ {b' : ℕ} {c : X ⟶ Z}, Chain P (a + b') c →
    ∃ (Y : FDMod k A) (c₁ : X ⟶ Y) (c₂ : Y ⟶ Z), Chain P a c₁ ∧ Chain P b' c₂ ∧ c = c₁ ≫ c₂ := by
  induction a generalizing X with
  | zero =>
    intro b' c h
    rw [zero_add] at h
    exact ⟨X, 𝟙 X, c, nil h.source, h, (Category.id_comp c).symm⟩
  | succ a ih =>
    intro b' c h
    rw [show a + 1 + b' = (a + b') + 1 by omega] at h
    obtain ⟨Y, g, c', hX, hg, hc', rfl⟩ := h.inv_succ
    obtain ⟨M, c₁, c₂, h₁, h₂, rfl⟩ := ih hc'
    exact ⟨M, g ≫ c₁, c₂, cons g hX hg h₁, h₂, (Category.assoc _ _ _).symm⟩

/-- **Harada–Sai for chains**: rank bound. -/
lemma rk_le {b : ℕ} (hind : ∀ X, P X → IsIndecMod A X) (hdim : ∀ X, P X → finrank k X ≤ b) :
    ∀ n ≤ b, ∀ {X Y : FDMod k A} {c : X ⟶ Y}, Chain P (2 ^ n - 1) c →
      rk k (FDMod.lin c) ≤ b - n := by
  intro n
  induction n with
  | zero =>
    intro _ X Y c h
    cases h with
    | nil hX =>
      unfold rk
      rw [FDMod.lin_id, LinearMap.range_id, Submodule.restrictScalars_top, finrank_top]
      exact hdim _ hX
  | succ n ih =>
    intro hn X Y c h
    have h1 := Nat.one_le_two_pow (n := n)
    have e : 2 ^ (n + 1) - 1 = (2 ^ n - 1) + ((2 ^ n - 1) + 1) := by rw [pow_succ]; omega
    rw [e] at h
    obtain ⟨M, c₁, c₂, h₁, h₂, rfl⟩ := h.split (2 ^ n - 1)
    obtain ⟨M', g, c₃, hM, hg, h₃, rfl⟩ := h₂.inv_succ
    have hM' := h₃.source
    have := haradaSai_step (k := k) (hind _ hM) (hind _ hM') (FDMod.lin c₁) (FDMod.lin g)
      (FDMod.lin c₃) hg (c := b - n) (by omega) (ih (by omega) h₁) (ih (by omega) h₃)
    simp only [FDMod.lin_comp]
    exact (by omega : ∀ x, x < b - n → x ≤ b - (n + 1)) _ this

/-- **Harada–Sai for chains.** -/
lemma eq_zero {b : ℕ} (hind : ∀ X, P X → IsIndecMod A X) (hdim : ∀ X, P X → finrank k X ≤ b)
    {X Y : FDMod k A} {c : X ⟶ Y} (h : Chain P (2 ^ b - 1) c) : FDMod.lin c = 0 := by
  have h0 := rk_le hind hdim b le_rfl h
  rw [Nat.sub_self, Nat.le_zero] at h0
  unfold rk at h0
  have := Submodule.finrank_eq_zero.1 h0
  ext x
  have hx : FDMod.lin c x ∈ (LinearMap.range (FDMod.lin c)).restrictScalars k :=
    LinearMap.mem_range_self _ x
  rw [this] at hx
  rw [LinearMap.zero_apply]
  exact (Submodule.mem_bot k).1 hx

end Chain

/-- A right almost split family into `X` with sources in `P`. -/
structure RASFam (P : FDMod k A → Prop) (X : FDMod k A) where
  ι : Type u
  [fin : Fintype ι]
  E : ι → FDMod k A
  hE : ∀ i, P (E i)
  g : ∀ i, E i ⟶ X
  notSplit : ¬∃ h : ∀ i, X ⟶ E i, ∑ i, FDMod.lin (g i) ∘ₗ FDMod.lin (h i) = LinearMap.id
  factor : ∀ (W : FDMod k A) (v : W ⟶ X),
    (¬∃ s : X ⟶ W, FDMod.lin v ∘ₗ FDMod.lin s = LinearMap.id) →
      ∃ h : ∀ i, W ⟶ E i, FDMod.lin v = ∑ i, FDMod.lin (g i) ∘ₗ FDMod.lin (h i)

attribute [instance] RASFam.fin

/-- The maps of a right almost split family are not bijective. -/
lemma RASFam.not_bijective {P : FDMod k A → Prop} {X : FDMod k A} (F : RASFam P X) (i : F.ι) :
    ¬Function.Bijective (FDMod.lin (F.g i)) := by
  classical
  intro hb
  let e := LinearEquiv.ofBijective (FDMod.lin (F.g i)) hb
  apply F.notSplit
  refine ⟨Function.update (fun j ↦ (0 : X ⟶ F.E j)) i (FDMod.ofLin e.symm.toLinearMap), ?_⟩
  rw [Finset.sum_eq_single i]
  · ext x
    simp only [Function.update_self, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe,
      id_eq]
    exact e.apply_symm_apply x
  · intro j _ hj
    simp only [Function.update_of_ne hj]
    exact LinearMap.comp_zero _
  · simp

/-- A split epimorphism from an indecomposable to a nonzero module is bijective. -/
lemma bijective_of_split {N X : FDMod k A} (hN : IsIndecMod A N) (hX : Nontrivial X)
    (f : N ⟶ X) (s : X ⟶ N) (hs : FDMod.lin f ∘ₗ FDMod.lin s = LinearMap.id) :
    Function.Bijective (FDMod.lin f) := by
  have hsurj : Function.Surjective (FDMod.lin f) := fun x ↦
    ⟨FDMod.lin s x, by simpa using LinearMap.congr_fun hs x⟩
  refine ⟨?_, hsurj⟩
  let e : Module.End A N := FDMod.lin s ∘ₗ FDMod.lin f
  have he : IsIdempotentElem e := by
    show e * e = e
    ext x
    simp only [Module.End.mul_apply, e, LinearMap.coe_comp, Function.comp_apply]
    have := LinearMap.congr_fun hs (FDMod.lin f x)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this
    rw [this]
  rcases hN _ _ (LinearMap.IsIdempotentElem.isCompl he) with h | h
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (0 : X)
    apply hx
    have h1 : FDMod.lin s x ∈ LinearMap.range e := by
      have := LinearMap.congr_fun hs x
      refine ⟨FDMod.lin s x, ?_⟩
      simp only [e, LinearMap.coe_comp, Function.comp_apply]
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this
      rw [this]
    rw [h] at h1
    have h2 := LinearMap.congr_fun hs x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at h2
    rw [← h2, (Submodule.mem_bot A).1 h1, map_zero]
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [← h]
    simp [e, LinearMap.mem_ker.1 hx]

/-- **An Auslander-type theorem.** If the indecomposable objects `P` of bounded dimension
have right almost split families inside `P`, and every nonzero module maps nonzero into
some `P`-object, then every indecomposable module is isomorphic to a `P`-object. -/
theorem auslander {P : FDMod k A → Prop} {b : ℕ} (hind : ∀ X, P X → IsIndecMod A X)
    (hdim : ∀ X, P X → finrank k X ≤ b) (hnt : ∀ X, P X → Nontrivial X)
    (fam : ∀ X, P X → Nonempty (RASFam P X))
    (cogen : ∀ N : FDMod k A, Nontrivial N → ∃ X, P X ∧ ∃ f : N ⟶ X, FDMod.lin f ≠ 0)
    (N : FDMod k A) (hN : IsIndecMod A N) (hNnt : Nontrivial N) :
    ∃ X, P X ∧ ∃ f : N ⟶ X, Function.Bijective (FDMod.lin f) := by
  classical
  obtain ⟨X₀, hX₀, f₀, hf₀⟩ := cogen N hNnt
  by_contra hno
  push Not at hno
  have step : ∀ t, ∃ (X : FDMod k A) (c : X ⟶ X₀) (f : N ⟶ X), Chain P t c ∧
      FDMod.lin (f ≫ c) ≠ 0 := by
    intro t
    induction t with
    | zero => exact ⟨X₀, 𝟙 X₀, f₀, Chain.nil hX₀, by simpa using hf₀⟩
    | succ t ih =>
      obtain ⟨X, c, f, hc, hfc⟩ := ih
      have hX := hc.source
      obtain ⟨F⟩ := fam X hX
      have hns : ¬∃ s : X ⟶ N, FDMod.lin f ∘ₗ FDMod.lin s = LinearMap.id := by
        rintro ⟨s, hs⟩
        exact hno X hX f (bijective_of_split hN (hnt X hX) f s hs)
      obtain ⟨h, hh⟩ := F.factor N f hns
      have : ∃ i, FDMod.lin c ∘ₗ FDMod.lin (F.g i) ∘ₗ FDMod.lin (h i) ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hfc
        rw [FDMod.lin_comp, hh]
        ext x
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply, map_sum,
          LinearMap.zero_apply]
        exact Finset.sum_eq_zero fun i _ ↦ by
          simpa using LinearMap.congr_fun (hall i) x
      obtain ⟨i, hi⟩ := this
      exact ⟨F.E i, F.g i ≫ c, h i, Chain.cons (F.g i) (F.hE i) (F.not_bijective i) hc,
        by simpa [FDMod.lin_comp, LinearMap.comp_assoc] using hi⟩
  obtain ⟨X, c, f, hc, hfc⟩ := step (2 ^ b - 1)
  apply hfc
  rw [FDMod.lin_comp, hc.eq_zero hind hdim, LinearMap.zero_comp]

end LargeIndecomposable.AR
