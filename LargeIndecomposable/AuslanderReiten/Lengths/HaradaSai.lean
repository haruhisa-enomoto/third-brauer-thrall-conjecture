module

public import Mathlib

/-!
# The Harada–Sai step

`IsIndecMod A M`: the `A`-module `M` has no decomposition `M = U ⊕ V` into two nonzero
`A`-submodules. `rk φ` is the `k`-dimension of the range of an `A`-linear map.

`haradaSai_step`: if `g : X → M`, `f : M → M'`, `h : M' → Y` with `M, M'` indecomposable,
`f` not bijective, and `rk g ≤ c`, `rk h ≤ c` with `c ≥ 1`, then `rk (h f g) < c`.
Iterating gives the Harada–Sai lemma: a composite of `2ᵇ − 1` non-isomorphisms between
indecomposables of dimension `≤ b` is zero.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open Module

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

variable (A) in
/-- No decomposition into two nonzero `A`-submodules. -/
def IsIndecMod (M : Type*) [AddCommGroup M] [Module A M] : Prop :=
  ∀ U V : Submodule A M, IsCompl U V → U = ⊥ ∨ V = ⊥

variable {X M M' Y : Type*} [AddCommGroup X] [Module A X] [Module k X] [IsScalarTower k A X]
  [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  [AddCommGroup M'] [Module A M'] [Module k M'] [IsScalarTower k A M']
  [AddCommGroup Y] [Module A Y] [Module k Y] [IsScalarTower k A Y]

variable (k) in
/-- The `k`-rank of an `A`-linear map. -/
def rk {P Q : Type*} [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
    [AddCommGroup Q] [Module A Q] [Module k Q] [IsScalarTower k A Q] (φ : P →ₗ[A] Q) : ℕ :=
  finrank k ((LinearMap.range φ).restrictScalars k)

/-- `k`-dimension of an `A`-submodule. -/
abbrev dimk {P : Type*} [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
    (U : Submodule A P) : ℕ := finrank k (U.restrictScalars k)

lemma dimk_mono {P : Type*} [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
    [FiniteDimensional k P] {U V : Submodule A P} (h : U ≤ V) : dimk (k := k) U ≤ dimk (k := k) V :=
  Submodule.finrank_mono (show U.restrictScalars k ≤ V.restrictScalars k from h)

lemma eq_of_le_of_dimk {P : Type*} [AddCommGroup P] [Module A P] [Module k P]
    [IsScalarTower k A P] [FiniteDimensional k P] {U V : Submodule A P} (h : U ≤ V)
    (hd : dimk (k := k) V ≤ dimk (k := k) U) : U = V := by
  have := Submodule.eq_of_le_of_finrank_le (K := k)
    (show U.restrictScalars k ≤ V.restrictScalars k from h) hd
  exact Submodule.restrictScalars_injective k A P this

/-- Two `A`-submodules with trivial meet and complementary dimensions are complements. -/
lemma isCompl_of_dimk {P : Type*} [AddCommGroup P] [Module A P] [Module k P]
    [IsScalarTower k A P] [FiniteDimensional k P] {U V : Submodule A P} (h : U ⊓ V = ⊥)
    (hd : dimk (k := k) U + dimk (k := k) V = finrank k P) : IsCompl U V := by
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (U.restrictScalars k) (V.restrictScalars k)
  have hinf : U.restrictScalars k ⊓ V.restrictScalars k = ⊥ := by
    rw [← Submodule.restrictScalars_inf, h, Submodule.restrictScalars_bot]
  rw [hinf, finrank_bot, add_zero] at hsup
  refine ⟨disjoint_iff.2 h, codisjoint_iff.2 ?_⟩
  have : (U ⊔ V).restrictScalars k = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Submodule.restrictScalars_sup, hsup, ← hd]
  exact Submodule.restrictScalars_injective k A P (by rw [this]; rfl)

lemma dimk_map_le {P Q : Type*} [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
    [AddCommGroup Q] [Module A Q] [Module k Q] [IsScalarTower k A Q] [FiniteDimensional k P]
    (φ : P →ₗ[A] Q) (U : Submodule A P) : dimk (k := k) (U.map φ) ≤ dimk (k := k) U := by
  have : (U.map φ).restrictScalars k = (U.restrictScalars k).map (φ.restrictScalars k) := rfl
  rw [dimk, this]
  exact Submodule.finrank_map_le _ _

/-- Dimension of the image plus the kernel restricted to a submodule. -/
lemma dimk_map_add_ker {P Q : Type*} [AddCommGroup P] [Module A P] [Module k P]
    [IsScalarTower k A P] [AddCommGroup Q] [Module A Q] [Module k Q] [IsScalarTower k A Q]
    [FiniteDimensional k P] (φ : P →ₗ[A] Q) :
    dimk (k := k) (LinearMap.range φ) + dimk (k := k) (LinearMap.ker φ) = finrank k P :=
  LinearMap.finrank_range_add_finrank_ker (φ.restrictScalars k)

/-- **The Harada–Sai step**, with indecomposability needed only for the two decompositions
that occur. -/
theorem haradaSai_step' [FiniteDimensional k X] [FiniteDimensional k M] [FiniteDimensional k M']
    [FiniteDimensional k Y] (g : X →ₗ[A] M) (f : M →ₗ[A] M') (h : M' →ₗ[A] Y)
    (hM : IsCompl (LinearMap.range g) (LinearMap.ker (h ∘ₗ f)) →
      LinearMap.range g = ⊥ ∨ LinearMap.ker (h ∘ₗ f) = ⊥)
    (hM' : IsCompl ((LinearMap.range g).map f) (LinearMap.ker h) →
      (LinearMap.range g).map f = ⊥ ∨ LinearMap.ker h = ⊥)
    (hf : ¬Function.Bijective f) {c : ℕ} (hc : 1 ≤ c) (hg : rk k g ≤ c)
    (hh : rk k h ≤ c) : rk k (h ∘ₗ f ∘ₗ g) < c := by
  classical
  set Xs := LinearMap.range g with hXs
  haveI : FiniteDimensional k Xs := inferInstanceAs (FiniteDimensional k (Xs.restrictScalars k))
  have r1 : rk k (h ∘ₗ f ∘ₗ g) ≤ rk k g := by
    have : LinearMap.range (h ∘ₗ f ∘ₗ g) = Xs.map (h ∘ₗ f) := by
      rw [hXs, ← LinearMap.range_comp]; rfl
    unfold rk; rw [this]; exact dimk_map_le _ _
  have r2 : rk k (h ∘ₗ f ∘ₗ g) ≤ rk k h := by
    unfold rk
    have : LinearMap.range (h ∘ₗ f ∘ₗ g) ≤ LinearMap.range h := LinearMap.range_comp_le_range _ _
    exact Submodule.finrank_mono (show (LinearMap.range (h ∘ₗ f ∘ₗ g)).restrictScalars k ≤
      (LinearMap.range h).restrictScalars k from this)
  by_contra hcon
  push Not at hcon
  have eg : rk k g = c := by omega
  have eh : rk k h = c := by omega
  have ehfg : rk k (h ∘ₗ f ∘ₗ g) = c := by omega
  -- `hf` is injective on `Xs`
  have hdisj : Xs ⊓ LinearMap.ker (h ∘ₗ f) = ⊥ := by
    have e1 := dimk_map_add_ker (k := k) ((h ∘ₗ f).domRestrict Xs)
    have hr : LinearMap.range ((h ∘ₗ f).domRestrict Xs) = LinearMap.range (h ∘ₗ f ∘ₗ g) := by
      rw [LinearMap.range_domRestrict, hXs, ← LinearMap.range_comp]; rfl
    have hXdim : finrank k Xs = c := eg
    rw [hr, show dimk (k := k) (LinearMap.range (h ∘ₗ f ∘ₗ g)) = c from ehfg, hXdim] at e1
    have hk : LinearMap.ker ((h ∘ₗ f).domRestrict Xs) = ⊥ := by
      have : finrank k ((LinearMap.ker ((h ∘ₗ f).domRestrict Xs)).restrictScalars k) = 0 := by
        have e1' : c + finrank k ((LinearMap.ker ((h ∘ₗ f).domRestrict Xs)).restrictScalars k) =
          c := e1
        omega
      have := Submodule.finrank_eq_zero.1 this
      exact Submodule.restrictScalars_injective k A _ (by rw [this]; rfl)
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have : (⟨x, hx1⟩ : Xs) ∈ LinearMap.ker ((h ∘ₗ f).domRestrict Xs) := hx2
    rw [hk] at this
    simpa using congrArg Subtype.val (Submodule.mem_bot A |>.1 this)
  -- ranges
  have hrange : LinearMap.range (h ∘ₗ f) = LinearMap.range h := by
    refine le_antisymm (LinearMap.range_comp_le_range _ _) ?_
    have hle : LinearMap.range (h ∘ₗ f ∘ₗ g) ≤ LinearMap.range (h ∘ₗ f) := by
      rw [← LinearMap.comp_assoc]; exact LinearMap.range_comp_le_range _ _
    have : LinearMap.range (h ∘ₗ f ∘ₗ g) = LinearMap.range h :=
      eq_of_le_of_dimk (LinearMap.range_comp_le_range _ _)
        (by show rk k h ≤ rk k (h ∘ₗ f ∘ₗ g); omega)
    rw [← this]; exact hle
  -- `M = Xs ⊕ ker (h f)`, so `f` is injective
  have hc1 : IsCompl Xs (LinearMap.ker (h ∘ₗ f)) := by
    refine isCompl_of_dimk (k := k) hdisj ?_
    have e := dimk_map_add_ker (k := k) (h ∘ₗ f)
    rw [hrange] at e
    have : dimk (k := k) Xs = c := eg
    have : dimk (k := k) (LinearMap.range h) = c := eh
    omega
  have hXne : Xs ≠ ⊥ := by
    intro h0
    have : rk k g = 0 := by
      unfold rk; rw [← hXs, h0, Submodule.restrictScalars_bot, finrank_bot]
    omega
  have hkerhf : LinearMap.ker (h ∘ₗ f) = ⊥ := (hM hc1).resolve_left hXne
  have finj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact eq_bot_iff.2 fun x hx ↦ by
      rw [← hkerhf]; simp [LinearMap.mem_ker.1 hx]
  -- `M' = f(Xs) ⊕ ker h`, so `f` is surjective
  have hc2 : IsCompl (Xs.map f) (LinearMap.ker h) := by
    refine isCompl_of_dimk (k := k) ?_ ?_
    · rw [eq_bot_iff]
      rintro y ⟨⟨x, hx, rfl⟩, hy⟩
      have : x ∈ Xs ⊓ LinearMap.ker (h ∘ₗ f) := ⟨hx, hy⟩
      rw [hdisj] at this
      simp [(Submodule.mem_bot A).1 this]
    · have e := dimk_map_add_ker (k := k) h
      have : dimk (k := k) (Xs.map f) = c := by
        have hmap : (Xs.map f).restrictScalars k = (Xs.restrictScalars k).map (f.restrictScalars k) :=
          rfl
        rw [dimk, hmap, ← (Submodule.equivMapOfInjective (f.restrictScalars k) finj
          (Xs.restrictScalars k)).finrank_eq]
        exact eg
      have : dimk (k := k) (LinearMap.range h) = c := eh
      omega
  have hfXne : Xs.map f ≠ ⊥ := by
    intro h0
    apply hXne
    rw [eq_bot_iff]; intro x hx
    have : f x ∈ Xs.map f := Submodule.mem_map_of_mem hx
    rw [h0] at this
    exact (Submodule.mem_bot A).2 (finj (by simpa using (Submodule.mem_bot A).1 this))
  have hkerh : LinearMap.ker h = ⊥ := (hM' hc2).resolve_left hfXne
  have hmapTop : Xs.map f = ⊤ := by
    have := hc2.sup_eq_top; rwa [hkerh, sup_bot_eq] at this
  have fsurj : Function.Surjective f := by
    intro y
    have : y ∈ Xs.map f := by rw [hmapTop]; trivial
    obtain ⟨x, -, rfl⟩ := this
    exact ⟨x, rfl⟩
  exact hf ⟨finj, fsurj⟩

/-- **The Harada–Sai step.** -/
theorem haradaSai_step [FiniteDimensional k X] [FiniteDimensional k M] [FiniteDimensional k M']
    [FiniteDimensional k Y]
    (hM : IsIndecMod A M) (hM' : IsIndecMod A M') (g : X →ₗ[A] M) (f : M →ₗ[A] M')
    (h : M' →ₗ[A] Y) (hf : ¬Function.Bijective f) {c : ℕ} (hc : 1 ≤ c) (hg : rk k g ≤ c)
    (hh : rk k h ≤ c) : rk k (h ∘ₗ f ∘ₗ g) < c :=
  haradaSai_step' g f h (hM _ _) (hM' _ _) hf hc hg hh

end LargeIndecomposable.AR
