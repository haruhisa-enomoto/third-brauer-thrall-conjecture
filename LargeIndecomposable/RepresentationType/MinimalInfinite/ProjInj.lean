module

public import LargeIndecomposable.RepresentationType.MinimalInfinite.Split
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# No projective-injective modules over minimal representation-infinite algebras

Let `e, e'` be idempotents and `s ∈ e' B e` nonzero such that every element of
`B e` killed by a nilpotent left ideal `R` (in practice the radical) is a
multiple of `s`, and `dim B e = dim e' B`. Then `B e` is injective in the
following concrete sense: for a module `U` with `s u ≠ 0`, the map
`B e → U`, `b ↦ b u`, has a retraction (it is injective, and composed with
`U → (e'B)^*`, `m ↦ (c ↦ ψ(c m))`, it gives an injective map between spaces of
the same dimension). Hence an indecomposable module not killed by `s` is
`B e`, and `B` is not minimal representation-infinite
(`not_minimal_of_projInj`). This is the classical fact used by Bongartz
([mild] §4, [Standard] §3) that a minimal representation-infinite algebra has
no nonzero projective-injective module.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Statement Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

/-- The left ideal `B e`. -/
def leftIdealOf (e : B) (he : e * e = e) : Submodule B B where
  carrier := {b | b * e = b}
  add_mem' := fun {a b} ha hb ↦ by simp only [Set.mem_setOf_eq] at *; rw [add_mul, ha, hb]
  zero_mem' := zero_mul e
  smul_mem' := fun a b hb ↦ by
    simp only [Set.mem_setOf_eq, smul_eq_mul] at *; rw [mul_assoc, hb]

/-- The right ideal `e' B` as a subspace. -/
def rightIdealOf (k : Type u) [Field k] [Algebra k B] (e' : B) (he' : e' * e' = e') :
    Submodule k B where
  carrier := {c | e' * c = c}
  add_mem' := fun {a b} ha hb ↦ by simp only [Set.mem_setOf_eq] at *; rw [mul_add, ha, hb]
  zero_mem' := mul_zero e'
  smul_mem' := fun a c hc ↦ by
    simp only [Set.mem_setOf_eq] at *; rw [mul_smul_comm, hc]

/-- A nonzero element of a left ideal contained in `B e` has a nonzero left
multiple killed by a nilpotent left ideal `R`. -/
lemma exists_killed {R : Set B} (hR : ∃ n : ℕ, ∀ l : List B, l.length = n → (∀ x ∈ l, x ∈ R) →
    l.prod = 0) {b : B} (hb : b ≠ 0) :
    ∃ l : List B, (∀ x ∈ l, x ∈ R) ∧ l.prod * b ≠ 0 ∧ ∀ j ∈ R, j * (l.prod * b) = 0 := by
  classical
  have hex : ∃ i, ∀ l : List B, l.length = i → (∀ x ∈ l, x ∈ R) → l.prod * b = 0 := by
    obtain ⟨n, hn⟩ := hR
    exact ⟨n, fun l hl hlR ↦ by rw [hn l hl hlR, zero_mul]⟩
  let i := Nat.find hex
  have hi0 : i ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [show Nat.find hex = 0 from h] at this
    exact hb (by simpa using this [] rfl (by simp))
  have hmin := Nat.find_min hex (show i - 1 < i by omega)
  push Not at hmin
  obtain ⟨l, hl, hlR, hne⟩ := hmin
  refine ⟨l, hlR, hne, fun j hj ↦ ?_⟩
  have := Nat.find_spec hex (j :: l) (by simp [hl]; omega) (by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hj
    · exact hlR x hx)
  simpa [mul_assoc] using this

/-- **No projective-injective module** (Bongartz's classical argument): if the
socle of `B e` is `k s` and `dim B e = dim e' B`, then `B` is not minimal
representation-infinite. -/
theorem not_minimal_of_projInj [FiniteDimensional k B] (hB : IsMinimalRepInfinite B)
    {e e' s : B} (he : e * e = e) (he' : e' * e' = e') (hs0 : s ≠ 0) (hse : s * e = s)
    (hes : e' * s = s) {R : Set B}
    (hR : ∃ n : ℕ, ∀ l : List B, l.length = n → (∀ x ∈ l, x ∈ R) → l.prod = 0)
    (hsoc : ∀ b, b * e = b → (∀ j ∈ R, j * b = 0) → ∃ c : k, b = algebraMap k B c * s)
    (hdim : finrank k ((leftIdealOf e he).restrictScalars k) =
      finrank k (rightIdealOf k e' he')) : False := by
  let P := leftIdealOf e he
  let Q := rightIdealOf k e' he'
  let I : TwoSidedIdeal B := TwoSidedIdeal.span {s}
  have hI : I ≠ ⊥ := by
    intro h0
    have : s ∈ I := TwoSidedIdeal.subset_span rfl
    rw [h0] at this
    exact hs0 ((TwoSidedIdeal.mem_bot B).1 this)
  obtain ⟨n, X, hX⟩ := hB.2 I hI
  refine hB.1 ⟨n + 1, Fin.append
    (fun i ↦ (ModuleCat.restrictScalars (Ideal.Quotient.mk _)).obj (X i))
    (fun _ ↦ ModuleCat.of B P), ?_⟩
  intro U _ _ _ hU
  by_cases hk : ∀ m : U, s • m = 0
  · have htor : ∀ x ∈ I, ∀ m : U, x • m = 0 :=
      span_smul_eq_zero _ (by rintro _ rfl m; exact hk m)
    obtain ⟨i, hi⟩ := exists_iso_of_isTorsion _ X hX U hU htor
    exact ⟨Fin.castAdd 1 i, by rwa [Fin.append_left]⟩
  push Not at hk
  obtain ⟨m₀, hm₀⟩ := hk
  refine ⟨Fin.natAdd n 0, ?_⟩
  rw [Fin.append_right]
  letI : Module k U := Module.compHom U (algebraMap k B)
  have hsm : ∀ (c : k) (m : U), c • m = algebraMap k B c • m := fun _ _ ↦ rfl
  let u : U := e • m₀
  have hsu : s • u ≠ 0 := by
    change s • e • m₀ ≠ 0; rwa [smul_smul, hse]
  have heu : e • u = u := by change e • e • m₀ = e • m₀; rw [smul_smul, he]
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_ne_zero k hsu
  -- `p ↦ (c ↦ ψ (c p u))`
  let hfun : B → Module.Dual k Q := fun p ↦
    { toFun := fun c ↦ ψ ((c.1 * p) • u)
      map_add' := fun c c' ↦ by
        change ψ (((c.1 + c'.1) * p) • u) = _; rw [add_mul, add_smul, map_add]
      map_smul' := fun a c ↦ by
        change ψ (((a • c.1) * p) • u) = a • ψ ((c.1 * p) • u)
        rw [Algebra.smul_def, mul_assoc, mul_smul, ← hsm, map_smul] }
  have hfun_apply : ∀ p (c : Q), hfun p c = ψ ((c.1 * p) • u) := fun _ _ ↦ rfl
  have hclosed : ∀ a p, hfun p = 0 → hfun (a * p) = 0 := by
    intro a p hp
    ext c
    have hc : (c.1 * a) ∈ Q := by
      change e' * (c.1 * a) = c.1 * a; rw [← mul_assoc, c.2]
    have := LinearMap.congr_fun hp ⟨c.1 * a, hc⟩
    rw [hfun_apply] at this
    rw [hfun_apply, ← mul_assoc]
    exact this
  let h : P.restrictScalars k →ₗ[k] Module.Dual k Q :=
    { toFun := fun p ↦ hfun p.1
      map_add' := fun p p' ↦ by
        ext c; change ψ ((c.1 * (p.1 + p'.1)) • u) = _
        rw [mul_add, add_smul, map_add]; rfl
      map_smul' := fun a p ↦ by
        ext c; change ψ ((c.1 * (a • p.1)) • u) = a • ψ ((c.1 * p.1) • u)
        rw [Algebra.smul_def, ← mul_assoc, ← Algebra.commutes, mul_assoc, mul_smul, ← hsm,
          map_smul] }
  have he'Q : e' ∈ Q := he'
  have hinj : Function.Injective h := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    by_contra hne
    have hne' : p.1 ≠ 0 := fun h0 ↦ hne (Subtype.ext h0)
    obtain ⟨l, -, hlne, hkill⟩ := exists_killed hR hne'
    have hn' : hfun (l.prod * p.1) = 0 := hclosed _ _ hp
    obtain ⟨c, hc⟩ := hsoc (l.prod * p.1) (by rw [mul_assoc, p.2]) hkill
    have hc0 : c ≠ 0 := by
      rintro rfl; rw [map_zero, zero_mul] at hc; exact hlne hc
    have hs : hfun s = 0 := by
      have : s = algebraMap k B c⁻¹ * (l.prod * p.1) := by
        rw [hc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
      rw [this]; exact hclosed _ _ hn'
    have := LinearMap.congr_fun hs ⟨e', he'Q⟩
    rw [hfun_apply, hes] at this
    exact hψ this
  have hsurj : Function.Surjective h := by
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    rw [Subspace.dual_finrank_eq]; exact hdim
  let hequiv := LinearEquiv.ofBijective h ⟨hinj, hsurj⟩
  let g : U → Module.Dual k Q := fun m ↦
    { toFun := fun c ↦ ψ (c.1 • m)
      map_add' := fun c c' ↦ by change ψ ((c.1 + c'.1) • m) = _; rw [add_smul, map_add]
      map_smul' := fun a c ↦ by
        change ψ ((a • c.1) • m) = a • ψ (c.1 • m)
        rw [Algebra.smul_def, mul_smul, ← hsm, map_smul] }
  have hgf : ∀ p : P, g (p.1 • u) = h p := fun p ↦ by
    ext c; change ψ (c.1 • p.1 • u) = ψ ((c.1 * p.1) • u); rw [smul_smul]
  let fB : P →ₗ[B] U :=
    { toFun := fun p ↦ p.1 • u
      map_add' := fun p p' ↦ add_smul _ _ _
      map_smul' := fun b p ↦ by change (b * p.1) • u = b • p.1 • u; rw [mul_smul] }
  have hgadd : ∀ m m', g (m + m') = g m + g m' := fun m m' ↦ by
    ext c; change ψ (c.1 • (m + m')) = ψ (c.1 • m) + ψ (c.1 • m'); rw [smul_add, map_add]
  let rB : U →ₗ[B] P :=
    { toFun := fun m ↦ hequiv.symm (g m)
      map_add' := fun m m' ↦ by rw [hgadd, map_add]; rfl
      map_smul' := fun b m ↦ by
        apply hequiv.injective
        rw [LinearEquiv.apply_symm_apply]
        ext c
        change ψ (c.1 • b • m) = hfun (b * (hequiv.symm (g m)).1) c
        rw [hfun_apply, ← mul_assoc]
        have hcb : c.1 * b ∈ Q := by
          change e' * (c.1 * b) = c.1 * b; rw [← mul_assoc, c.2]
        have := LinearMap.congr_fun (hequiv.apply_symm_apply (g m)) ⟨c.1 * b, hcb⟩
        change hfun (hequiv.symm (g m)).1 ⟨c.1 * b, hcb⟩ = ψ ((c.1 * b) • m) at this
        rw [hfun_apply] at this
        rw [this, smul_smul] }
  have hrf : ∀ p, rB (fB p) = p := fun p ↦ by
    change hequiv.symm (g (p.1 • u)) = p
    rw [hgf]; exact hequiv.symm_apply_apply p
  let φ : U →ₗ[B] U := fB ∘ₗ rB
  have hφ : IsIdempotentElem φ := by
    ext m; change fB (rB (fB (rB m))) = fB (rB m); rw [hrf]
  have heP : e ∈ P := he
  rcases hU.2 _ _ (LinearMap.IsIdempotentElem.isCompl hφ) with h0 | h0
  · exfalso
    have : φ (fB ⟨e, heP⟩) ∈ LinearMap.range φ := ⟨_, rfl⟩
    rw [h0, Submodule.mem_bot] at this
    change fB (rB (fB ⟨e, heP⟩)) = 0 at this
    rw [hrf] at this
    change e • u = 0 at this
    rw [heu] at this
    exact hsu (by rw [this, smul_zero])
  · have hrinj : Function.Injective rB := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro m hm
      rw [LinearMap.mem_ker] at hm
      have : m ∈ LinearMap.ker φ := by
        rw [LinearMap.mem_ker]; change fB (rB m) = 0; rw [hm, map_zero]
      rwa [h0] at this
    exact ⟨LinearEquiv.ofBijective rB ⟨hrinj, fun p ↦ ⟨fB p, hrf p⟩⟩⟩

end LargeIndecomposable
