module

public import LargeIndecomposable.RepresentationType.MinimalInfinite.ProjInj
public import Mathlib.RingTheory.Jacobson.Semiprimary
public import Mathlib.RingTheory.Artinian.Ring

/-!
# Tiny penny-farthings: an almost projective-injective point

A variant of `not_minimal_of_projInj` used for the open penny-farthing case of
[mild] Theorem 3 (replacing the Auslander–Reiten argument of [Standard] §3.1,
§3.2). Let `e, e'` be idempotents, `s ∈ e' B e` nonzero, and `t ∈ e_b B e` with
`R t = 0`, `e' B t = 0`, such that

* the elements of `B e` whose `R`-multiples lie in `k t` lie in `k s + k t`;
* the elements of `e' B` killed by `R` on the right lie in `k s`;
* every element of `e_b R` is a left multiple `t b'`, and `e_b` is local.

Then for a module `U` with `s u ≠ 0` the map `B e → U`, `b ↦ b u`, composed with
`U → (e'B)^*`, `m ↦ (c ↦ ψ(c m))`, is surjective with kernel inside `k t`, and an
indecomposable `U` not killed by `s` is `B e` or `B e / (t)`: if `t u = 0`,
`B e / (t)` splits off; if `t u` lies in `R V` (`V` the kernel of `U → (e'B)^*`)
one changes `u` so that `t u = 0`; otherwise `B e` splits off modulo a
complement of `k t u` in `V`. Hence `B` is not minimal representation-infinite.
For `t = 0` this is the projective-injective case.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Statement Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

/-- A product of elements of a two-sided ideal lies in the corresponding power. -/
theorem listProd_mem_pow {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided] :
    ∀ l : List R, (∀ a ∈ l, a ∈ I) → l.prod ∈ I ^ l.length
  | [], _ => by rw [List.prod_nil, List.length_nil, Submodule.pow_zero, Ideal.one_eq_top]; trivial
  | a :: l, h => by
    rw [List.prod_cons, List.length_cons, Ideal.IsTwoSided.pow_succ]
    exact Ideal.mul_mem_mul (h a (by simp)) (listProd_mem_pow I l (fun x hx ↦ h x (by simp [hx])))

/-- The radical of an artinian ring is nilpotent, in list form. -/
theorem jacobson_listProd {R : Type*} [Ring R] [IsArtinianRing R] :
    ∃ n : ℕ, ∀ l : List R, l.length = n → (∀ x ∈ l, x ∈ Ring.jacobson R) → l.prod = 0 := by
  obtain ⟨n, hn⟩ := (IsSemiprimaryRing.isNilpotent : IsNilpotent (Ring.jacobson R))
  refine ⟨n, fun l hl h ↦ ?_⟩
  have := listProd_mem_pow _ l h
  rw [hl, hn] at this
  exact this

/-- `exists_killed` modulo a set `N` containing `0`. -/
lemma exists_killed_mem {R : Set B} (N : Set B) (hN : (0 : B) ∈ N)
    (hR : ∃ n : ℕ, ∀ l : List B, l.length = n → (∀ x ∈ l, x ∈ R) → l.prod = 0) {b : B}
    (hb : b ∉ N) :
    ∃ l : List B, (∀ x ∈ l, x ∈ R) ∧ l.prod * b ∉ N ∧ ∀ j ∈ R, j * (l.prod * b) ∈ N := by
  classical
  have hex : ∃ i, ∀ l : List B, l.length = i → (∀ x ∈ l, x ∈ R) → l.prod * b ∈ N := by
    obtain ⟨n, hn⟩ := hR
    exact ⟨n, fun l hl hlR ↦ by rw [hn l hl hlR, zero_mul]; exact hN⟩
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

/-- The right-handed version of `exists_killed`. -/
lemma exists_killed_right {R : Set B}
    (hR : ∃ n : ℕ, ∀ l : List B, l.length = n → (∀ x ∈ l, x ∈ R) → l.prod = 0) {b : B}
    (hb : b ≠ 0) :
    ∃ l : List B, (∀ x ∈ l, x ∈ R) ∧ b * l.prod ≠ 0 ∧ ∀ j ∈ R, (b * l.prod) * j = 0 := by
  classical
  have hex : ∃ i, ∀ l : List B, l.length = i → (∀ x ∈ l, x ∈ R) → b * l.prod = 0 := by
    obtain ⟨n, hn⟩ := hR
    exact ⟨n, fun l hl hlR ↦ by rw [hn l hl hlR, mul_zero]⟩
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
  have := Nat.find_spec hex (l ++ [j]) (by simp [hl]; omega) (by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hlR x hx
    · rw [List.mem_singleton.1 hx]; exact hj)
  simpa [mul_assoc] using this

/-- A module map `F : M → U` that becomes bijective modulo a submodule `W` of an
indecomposable `U` is an isomorphism onto `U` (it splits, `r = (q F)⁻¹ q`). -/
lemma nonempty_equiv_of_retract {M U : Type u} [AddCommGroup M] [Module B M] [AddCommGroup U]
    [Module B U] (hU : IsIndecomposable B U) (F : M →ₗ[B] U) (hF : F ≠ 0) (W : Submodule B U)
    (hbij : Function.Bijective (W.mkQ ∘ₗ F)) : Nonempty (U ≃ₗ[B] M) := by
  let E := LinearEquiv.ofBijective _ hbij
  let r : U →ₗ[B] M := E.symm.toLinearMap ∘ₗ W.mkQ
  have hrf : ∀ m, r (F m) = m := fun m ↦ E.symm_apply_apply m
  let φ : U →ₗ[B] U := F ∘ₗ r
  have hφ : IsIdempotentElem φ := by
    ext m; change F (r (F (r m))) = F (r m); rw [hrf]
  rcases hU.2 _ _ (LinearMap.IsIdempotentElem.isCompl hφ) with h0 | h0
  · exfalso
    apply hF
    ext m
    have : φ (F m) ∈ LinearMap.range φ := ⟨_, rfl⟩
    rw [h0, Submodule.mem_bot] at this
    change F (r (F m)) = 0 at this
    rwa [hrf] at this
  · have hrinj : Function.Injective r := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro m hm
      rw [LinearMap.mem_ker] at hm
      have : m ∈ LinearMap.ker φ := by
        rw [LinearMap.mem_ker]; change F (r m) = 0; rw [hm, map_zero]
      rwa [h0] at this
    exact ⟨LinearEquiv.ofBijective r ⟨hrinj, fun m ↦ ⟨F m, hrf m⟩⟩⟩

/-- **Tiny penny-farthings** (see the module docstring): `B` is not minimal
representation-infinite. -/
theorem not_minimal_of_tiny [FiniteDimensional k B] (hB : IsMinimalRepInfinite B)
    {e e' s t eb : B} (he : e * e = e) (he' : e' * e' = e') (hs0 : s ≠ 0) (hse : s * e = s)
    (hes : e' * s = s) (hte : t * e = t) (hebt : eb * t = t) {R : Set B}
    (hR : ∃ n : ℕ, ∀ l : List B, l.length = n → (∀ x ∈ l, x ∈ R) → l.prod = 0)
    (hRt : ∀ j ∈ R, j * t = 0) (htk : ∀ c, e' * c = c → c * t = 0)
    (hsocL : ∀ b, b * e = b → (∀ j ∈ R, ∃ d : k, j * b = algebraMap k B d * t) →
      ∃ c d : k, b = algebraMap k B c * s + algebraMap k B d * t)
    (hsocR : ∀ c, e' * c = c → (∀ j ∈ R, c * j = 0) → ∃ a : k, c = algebraMap k B a * s)
    (hfac : ∀ j ∈ R, ∃ b', eb * j = t * b')
    (hloc : ∀ b : B, ∃ l : k, eb * b - algebraMap k B l * eb ∈ R ∧
      b * eb - algebraMap k B l * eb ∈ R) : False := by
  classical
  let P := leftIdealOf e he
  let Q := rightIdealOf k e' he'
  have htP : t ∈ P := hte
  have heP : e ∈ P := he
  let T : Submodule B P := Submodule.span B {⟨t, htP⟩}
  have hBt : ∀ b : B, ∃ d : k, b * t = algebraMap k B d * t := by
    intro b
    obtain ⟨l, -, h2⟩ := hloc b
    refine ⟨l, ?_⟩
    have := hRt _ h2
    rw [sub_mul, sub_eq_zero, mul_assoc, hebt, mul_assoc, hebt] at this
    exact this
  have htT : (⟨t, htP⟩ : P) ∈ T := Submodule.subset_span rfl
  obtain ⟨θ, hθ⟩ := Module.Projective.exists_dual_ne_zero k hs0
  let I : TwoSidedIdeal B := TwoSidedIdeal.span {s}
  have hI : I ≠ ⊥ := by
    intro h0
    have : s ∈ I := TwoSidedIdeal.subset_span rfl
    rw [h0] at this
    exact hs0 ((TwoSidedIdeal.mem_bot B).1 this)
  obtain ⟨n, X, hX⟩ := hB.2 I hI
  refine hB.1 ⟨n + 2, Fin.append
    (fun i ↦ (ModuleCat.restrictScalars (Ideal.Quotient.mk _)).obj (X i))
    ![ModuleCat.of B P, ModuleCat.of B (P ⧸ T)], ?_⟩
  intro U _ _ _ hU
  by_cases hk : ∀ m : U, s • m = 0
  · have htor : ∀ x ∈ I, ∀ m : U, x • m = 0 :=
      span_smul_eq_zero _ (by rintro _ rfl m; exact hk m)
    obtain ⟨i, hi⟩ := exists_iso_of_isTorsion _ X hX U hU htor
    exact ⟨Fin.castAdd 2 i, by rwa [Fin.append_left]⟩
  suffices H : Nonempty (U ≃ₗ[B] P) ∨ Nonempty (U ≃ₗ[B] (P ⧸ T)) by
    rcases H with H | H
    · exact ⟨Fin.natAdd n 0, by rw [Fin.append_right]; exact H⟩
    · exact ⟨Fin.natAdd n 1, by rw [Fin.append_right]; exact H⟩
  push Not at hk
  obtain ⟨m₀, hm₀⟩ := hk
  let _ : Module k U := Module.compHom U (algebraMap k B)
  have hsm : ∀ (c : k) (m : U), c • m = algebraMap k B c • m := fun _ _ ↦ rfl
  let u₀ : U := e • m₀
  have hsu₀ : s • u₀ ≠ 0 := by
    change s • e • m₀ ≠ 0; rwa [smul_smul, hse]
  have heu₀ : e • u₀ = u₀ := by change e • e • m₀ = e • m₀; rw [smul_smul, he]
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_ne_zero k hsu₀
  have hQmul : ∀ c a : B, e' * c = c → e' * (c * a) = c * a := fun c a hc ↦ by
    rw [← mul_assoc, hc]
  let V : Submodule B U :=
    { carrier := {m | ∀ c, e' * c = c → ψ (c • m) = 0}
      add_mem' := fun {m m'} hm hm' c hc ↦ by
        change ψ (c • (m + m')) = 0; rw [smul_add, map_add, hm c hc, hm' c hc, add_zero]
      zero_mem' := fun c _ ↦ by change ψ (c • (0 : U)) = 0; rw [smul_zero, map_zero]
      smul_mem' := fun b m hm c hc ↦ by
        change ψ (c • b • m) = 0; rw [smul_smul]; exact hm _ (hQmul c b hc) }
  have hmemV : ∀ m, m ∈ V ↔ ∀ c, e' * c = c → ψ (c • m) = 0 := fun _ ↦ Iff.rfl
  -- the map `p ↦ (c ↦ ψ (c p u))`: kernel inside `k t`, image everything
  have stepB : ∀ u : U, e • u = u → ψ (s • u) ≠ 0 →
      (∀ p : B, p * e = p → p • u ∈ V → ∃ d : k, p = algebraMap k B d * t) ∧
      (∀ m : U, ∃ p : B, p * e = p ∧ m - p • u ∈ V) := by
    intro u heu hsu
    let Z : B → Prop := fun p ↦ ∀ c, e' * c = c → ψ ((c * p) • u) = 0
    have hZV : ∀ p, p • u ∈ V ↔ Z p := fun p ↦ by
      simp only [hmemV, Z, smul_smul]
    have hZmul : ∀ a p, Z p → Z (a * p) := fun a p hp c hc ↦ by
      rw [← mul_assoc]; exact hp _ (hQmul c a hc)
    have hZt : Z t := fun c hc ↦ by rw [htk c hc, zero_smul, map_zero]
    have hker : ∀ p : B, p * e = p → Z p → ∃ d : k, p = algebraMap k B d * t := by
      intro p hpe hp
      by_contra hne
      obtain ⟨l, -, hlN, hlR⟩ := exists_killed_mem {x | ∃ d : k, x = algebraMap k B d * t}
        ⟨0, by simp⟩ hR (b := p) (fun h ↦ hne h)
      obtain ⟨c, d, hcd⟩ := hsocL (l.prod * p) (by rw [mul_assoc, hpe]) hlR
      have hZ := hZmul l.prod p hp e' he'
      rw [hcd, mul_add, add_smul, map_add, ← mul_assoc, ← Algebra.commutes, mul_assoc,
        ← mul_assoc e' (algebraMap k B d), ← Algebra.commutes, mul_assoc, htk e' he', mul_zero,
        zero_smul, map_zero, add_zero, hes, mul_smul, ← hsm, map_smul, smul_eq_mul] at hZ
      rcases mul_eq_zero.1 hZ with h0 | h0
      · exact hlN ⟨d, by rw [hcd, h0, map_zero, zero_mul, zero_add]⟩
      · exact hsu h0
    -- the linear map `h : B e → (e' B)^*`
    let hfun : B → Module.Dual k Q := fun p ↦
      { toFun := fun c ↦ ψ ((c.1 * p) • u)
        map_add' := fun c c' ↦ by
          change ψ (((c.1 + c'.1) * p) • u) = _; rw [add_mul, add_smul, map_add]
        map_smul' := fun a c ↦ by
          change ψ (((a • c.1) * p) • u) = a • ψ ((c.1 * p) • u)
          rw [Algebra.smul_def, mul_assoc, mul_smul, ← hsm, map_smul] }
    let h : P.restrictScalars k →ₗ[k] Module.Dual k Q :=
      { toFun := fun p ↦ hfun p.1
        map_add' := fun p p' ↦ by
          ext c; change ψ ((c.1 * (p.1 + p'.1)) • u) = _
          rw [mul_add, add_smul, map_add]; rfl
        map_smul' := fun a p ↦ by
          ext c; change ψ ((c.1 * (a • p.1)) • u) = a • ψ ((c.1 * p.1) • u)
          rw [Algebra.smul_def, ← mul_assoc, ← Algebra.commutes, mul_assoc, mul_smul, ← hsm,
            map_smul] }
    let K : Submodule k (P.restrictScalars k) := Submodule.span k {⟨t, htP⟩}
    have hkerK : LinearMap.ker h ≤ K := by
      intro p hp
      have hZ : Z p.1 := fun c hc ↦ LinearMap.congr_fun hp ⟨c, hc⟩
      obtain ⟨d, hd⟩ := hker p.1 p.2 hZ
      have : p = d • (⟨t, htP⟩ : P.restrictScalars k) := Subtype.ext (by
        rw [hd]; change _ = d • t; rw [Algebra.smul_def])
      rw [this]; exact K.smul_mem _ (Submodule.subset_span rfl)
    let κ : Q →ₗ[k] Module.Dual k (P.restrictScalars k) :=
      { toFun := fun c ↦
          { toFun := fun p ↦ θ (c.1 * p.1)
            map_add' := fun p p' ↦ by
              change θ (c.1 * (p.1 + p'.1)) = _; rw [mul_add, map_add]
            map_smul' := fun a p ↦ by
              change θ (c.1 * (a • p.1)) = a • θ (c.1 * p.1)
              rw [mul_smul_comm, map_smul] }
        map_add' := fun c c' ↦ by
          ext p; change θ ((c.1 + c'.1) * p.1) = _; rw [add_mul, map_add]; rfl
        map_smul' := fun a c ↦ by
          ext p; change θ ((a • c.1) * p.1) = a • θ (c.1 * p.1)
          rw [smul_mul_assoc, map_smul] }
    have hκK : ∀ c, κ c ∈ K.dualAnnihilator := by
      intro c
      rw [Submodule.mem_dualAnnihilator]
      intro p hp
      rw [Submodule.mem_span_singleton] at hp
      obtain ⟨a, rfl⟩ := hp
      change θ (c.1 * (a • t)) = 0
      rw [mul_smul_comm, htk c.1 c.2, smul_zero, map_zero]
    have hκinj : Function.Injective κ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro c hc
      by_contra hne
      have hne' : c.1 ≠ 0 := fun h0 ↦ hne (Subtype.ext h0)
      obtain ⟨l, -, hlne, hlR⟩ := exists_killed_right hR hne'
      obtain ⟨a, ha⟩ := hsocR (c.1 * l.prod) (hQmul _ _ c.2) hlR
      have ha0 : a ≠ 0 := by rintro rfl; rw [map_zero, zero_mul] at ha; exact hlne ha
      have hlP : l.prod * e ∈ P := by change l.prod * e * e = _; rw [mul_assoc, he]
      have := LinearMap.congr_fun hc ⟨_, hlP⟩
      change θ (c.1 * (l.prod * e)) = 0 at this
      rw [← mul_assoc, ha, mul_assoc, hse, ← Algebra.smul_def, map_smul, smul_eq_mul] at this
      rcases mul_eq_zero.1 this with h0 | h0
      · exact ha0 h0
      · exact hθ h0
    have h1 : finrank k Q ≤ finrank k K.dualAnnihilator :=
      LinearMap.finrank_le_finrank_of_injective (f := κ.codRestrict _ hκK)
        (fun c c' hcc ↦ hκinj (congrArg Subtype.val hcc))
    have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq K
    have h3 := LinearMap.finrank_range_add_finrank_ker h
    have h4 : finrank k (LinearMap.ker h) ≤ finrank k K := Submodule.finrank_mono hkerK
    have h5 : finrank k (Module.Dual k Q) = finrank k Q := Subspace.dual_finrank_eq
    have h6 : finrank k (LinearMap.range h) ≤ finrank k (Module.Dual k Q) :=
      Submodule.finrank_le _
    have hsurj : LinearMap.range h = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
    refine ⟨fun p hpe hp ↦ hker p hpe ((hZV p).1 hp), fun m ↦ ?_⟩
    let gm : Module.Dual k Q :=
      { toFun := fun c ↦ ψ (c.1 • m)
        map_add' := fun c c' ↦ by change ψ ((c.1 + c'.1) • m) = _; rw [add_smul, map_add]
        map_smul' := fun a c ↦ by
          change ψ ((a • c.1) • m) = a • ψ (c.1 • m)
          rw [Algebra.smul_def, mul_smul, ← hsm, map_smul] }
    obtain ⟨p, hp⟩ : gm ∈ LinearMap.range h := by rw [hsurj]; trivial
    refine ⟨p.1, p.2, fun c hc ↦ ?_⟩
    have := LinearMap.congr_fun hp ⟨c, hc⟩
    change ψ ((c * p.1) • u) = ψ (c • m) at this
    rw [smul_sub, map_sub, smul_smul, this, sub_self]
  have hu0 : ∀ u : U, ψ (s • u) ≠ 0 → u ≠ 0 := fun u hsu h0 ↦ hsu (by rw [h0, smul_zero, map_zero])
  let fB : U → (P →ₗ[B] U) := fun u ↦
    { toFun := fun p ↦ p.1 • u
      map_add' := fun p p' ↦ add_smul _ _ _
      map_smul' := fun b p ↦ by change (b * p.1) • u = b • p.1 • u; rw [mul_smul] }
  have hfB0 : ∀ u : U, e • u = u → u ≠ 0 → fB u ≠ 0 := fun u heu hu h0 ↦ by
    have := LinearMap.congr_fun h0 ⟨e, heP⟩
    change e • u = 0 at this
    exact hu (by rw [← heu, this])
  have htV : ∀ u : U, t • u ∈ V := fun u c hc ↦ by
    rw [smul_smul, htk c hc, zero_smul, map_zero]
  -- case `t u = 0`: `B e / (t)` splits off
  have caseC : ∀ u : U, e • u = u → ψ (s • u) ≠ 0 → t • u = 0 →
      Nonempty (U ≃ₗ[B] (P ⧸ T)) := by
    intro u heu hsu htu
    obtain ⟨hk1, hk2⟩ := stepB u heu hsu
    have hTle : T ≤ LinearMap.ker (fB u) := by
      rw [Submodule.span_le, Set.singleton_subset_iff]; exact htu
    refine nonempty_equiv_of_retract hU (T.liftQ (fB u) hTle) ?_ V ⟨?_, ?_⟩
    · intro h0
      have := LinearMap.congr_fun h0 (T.mkQ ⟨e, heP⟩)
      change e • u = 0 at this
      exact hu0 u hsu (by rw [← heu, this])
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      obtain ⟨p, rfl⟩ := T.mkQ_surjective x
      change V.mkQ (p.1 • u) = 0 at hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨d, hd⟩ := hk1 p.1 p.2 hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      have : p = (algebraMap k B d) • (⟨t, htP⟩ : P) := Subtype.ext hd
      rw [this]; exact T.smul_mem _ htT
    · intro y
      obtain ⟨m, rfl⟩ := V.mkQ_surjective y
      obtain ⟨p, hp, hpm⟩ := hk2 m
      refine ⟨T.mkQ ⟨p, hp⟩, ?_⟩
      change V.mkQ (p • u) = V.mkQ m
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      have := V.neg_mem hpm; rwa [neg_sub] at this
  -- `R V` and the factorization of its `e_b`-part through `t`
  let RV : Submodule k U := Submodule.span k {m | ∃ j ∈ R, ∃ v ∈ V, m = j • v}
  have hD : ∀ x ∈ RV, ∃ w ∈ V, eb • x = t • w := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨j, hj, v, hv, rfl⟩ := hx
        obtain ⟨b', hb'⟩ := hfac j hj
        exact ⟨b' • v, V.smul_mem _ hv, by rw [smul_smul, hb', mul_smul]⟩
    | zero => exact ⟨0, V.zero_mem, by rw [smul_zero, smul_zero]⟩
    | add x y _ _ hx hy =>
        obtain ⟨w, hw, hxw⟩ := hx; obtain ⟨w', hw', hyw⟩ := hy
        exact ⟨w + w', V.add_mem hw hw', by rw [smul_add, smul_add, hxw, hyw]⟩
    | smul a x _ hx =>
        obtain ⟨w, hw, hxw⟩ := hx
        refine ⟨algebraMap k B a • w, V.smul_mem _ hw, ?_⟩
        rw [hsm, smul_smul, ← Algebra.commutes, ← smul_smul, hxw, smul_smul, smul_smul,
          Algebra.commutes]
  -- case `t u ∉ R V`: `B e` splits off modulo a complement of `k t u` in `V`
  have caseE : ∀ u : U, e • u = u → ψ (s • u) ≠ 0 → t • u ∉ RV → Nonempty (U ≃ₗ[B] P) := by
    intro u heu hsu htu
    obtain ⟨hk1, hk2⟩ := stepB u heu hsu
    have hq : RV.mkQ (t • u) ≠ 0 := by
      rwa [Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]
    obtain ⟨φ', hφ'⟩ := Module.Projective.exists_dual_ne_zero k hq
    let φ₀ : Module.Dual k U := (φ' (RV.mkQ (t • u)))⁻¹ • (φ' ∘ₗ RV.mkQ)
    have hφt : φ₀ (t • u) = 1 := by
      change (φ' (RV.mkQ (t • u)))⁻¹ * φ' (RV.mkQ (t • u)) = 1
      exact inv_mul_cancel₀ hφ'
    have hφRV : ∀ x ∈ RV, φ₀ x = 0 := fun x hx ↦ by
      change (φ' (RV.mkQ (t • u)))⁻¹ * φ' (RV.mkQ x) = 0
      have : RV.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero RV).2 hx
      rw [this, map_zero, mul_zero]
    let W : Submodule B U :=
      { carrier := {m | m ∈ V ∧ φ₀ (eb • m) = 0}
        add_mem' := fun {m m'} hm hm' ↦ ⟨V.add_mem hm.1 hm'.1, by
          rw [smul_add, map_add, hm.2, hm'.2, add_zero]⟩
        zero_mem' := ⟨V.zero_mem, by rw [smul_zero, map_zero]⟩
        smul_mem' := fun b m hm ↦ ⟨V.smul_mem b hm.1, by
          obtain ⟨l, h1, -⟩ := hloc b
          change φ₀ (eb • b • m) = 0
          have hr : (eb * b - algebraMap k B l * eb) • m ∈ RV :=
            Submodule.subset_span ⟨_, h1, m, hm.1, rfl⟩
          rw [smul_smul, show eb * b = (eb * b - algebraMap k B l * eb) + algebraMap k B l * eb
            by abel, add_smul, map_add, hφRV _ hr, zero_add, mul_smul, ← hsm, map_smul, hm.2,
            smul_zero]⟩ }
    refine nonempty_equiv_of_retract hU (fB u) (hfB0 u heu (hu0 u hsu)) W ⟨?_, ?_⟩
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro p hp
      change W.mkQ (p.1 • u) = 0 at hp
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hp
      obtain ⟨d, hd⟩ := hk1 p.1 p.2 hp.1
      have h2 := hp.2
      rw [hd, smul_smul, ← mul_assoc, ← Algebra.commutes, mul_assoc, hebt, mul_smul, ← hsm,
        map_smul, hφt, smul_eq_mul, mul_one] at h2
      exact Subtype.ext (by rw [hd, h2, map_zero, zero_mul]; rfl)
    · intro y
      obtain ⟨m, rfl⟩ := W.mkQ_surjective y
      obtain ⟨p₀, hp₀, hv⟩ := hk2 m
      set c := φ₀ (eb • (m - p₀ • u))
      have hpP : p₀ + algebraMap k B c * t ∈ P := by
        change (p₀ + algebraMap k B c * t) * e = _; rw [add_mul, mul_assoc, hte, hp₀]
      refine ⟨⟨_, hpP⟩, ?_⟩
      change W.mkQ ((p₀ + algebraMap k B c * t) • u) = W.mkQ m
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      have e1 : (p₀ + algebraMap k B c * t) • u - m = -((m - p₀ • u) - c • (t • u)) := by
        rw [add_smul, mul_smul, ← hsm]; abel
      rw [e1]
      refine W.neg_mem ⟨V.sub_mem hv (V.smul_mem (algebraMap k B c) (htV u)), ?_⟩
      have ht' : eb • c • t • u = c • t • u := by
        rw [hsm, smul_smul, ← Algebra.commutes, mul_smul, smul_smul eb t, hebt]
      rw [smul_sub, map_sub, ht', φ₀.map_smul c (t • u), hφt, smul_eq_mul, mul_one, sub_self]
  -- the three cases
  by_cases htu : t • u₀ = 0
  · exact Or.inr (caseC u₀ heu₀ hψ htu)
  by_cases hRV : t • u₀ ∈ RV
  · obtain ⟨w, hwV, hw⟩ := hD _ hRV
    rw [smul_smul, hebt] at hw
    refine Or.inr (caseC (u₀ - e • w) ?_ ?_ ?_)
    · rw [smul_sub, heu₀, smul_smul, he]
    · rw [smul_sub, map_sub, smul_smul s e w, hse, hwV s hes, sub_zero]; exact hψ
    · rw [smul_sub, hw, smul_smul, hte, sub_self]
  · exact Or.inl (caseE u₀ heu₀ hψ hRV)

end LargeIndecomposable
