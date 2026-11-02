module

public import LargeIndecomposable.Cleaving.ThinCategories.RadSq
public import LargeIndecomposable.Cleaving.Functors.Cleaving

/-!
# Band modules over the crown category

The crown category `Cr m` is the radical-square-zero category of the
alternating cycle with sources `x₀, …, xₘ`, sinks `z₀, …, zₘ` and arrows
`ρᵢ : xᵢ → zᵢ`, `σᵢ : xᵢ₊₁ → zᵢ` (indices mod `m + 1`). For `λ ∈ kˣ` the band
module `k^V` (every arrow acts by `1`, except `σₘ` by `λ`) is indecomposable,
and band modules for different `λ` are not isomorphic. Hence `k(Cr m)` is
representation-infinite over an infinite field (`RayCat.not_isRepresentationFinite_crown`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayQuiver

universe u

namespace RayCat

/-- Sources of the arrows of the alternating cycle. -/
def crSrc (m : ℕ) : Fin (m + 1) ⊕ Fin (m + 1) → Fin (m + 1) ⊕ Fin (m + 1)
  | .inl i => .inl i
  | .inr i => .inl (i + 1)

/-- Targets of the arrows of the alternating cycle. -/
def crTgt (m : ℕ) : Fin (m + 1) ⊕ Fin (m + 1) → Fin (m + 1) ⊕ Fin (m + 1)
  | .inl i => .inr i
  | .inr i => .inr i

lemma crTgt_ne_crSrc (m : ℕ) (e e' : Fin (m + 1) ⊕ Fin (m + 1)) : crTgt m e ≠ crSrc m e' := by
  rcases e with i | i <;> rcases e' with j | j <;> simp [crSrc, crTgt]

/-- The crown category. -/
abbrev Cr (m : ℕ) := RSZ (crSrc m) (crTgt m)

instance (m : ℕ) : IsRayCategory (Cr m) := RSZ.isRayCategory (crTgt_ne_crSrc m)

variable (k : Type u) [Field k] (m : ℕ)

/-- The scalar by which a morphism acts on a band module. -/
def bandCoef (c : Fin (m + 1) ⊕ Fin (m + 1) → k) {X Y : Cr m} : (X ⟶ Y) → k
  | none => 0
  | some (.inl _) => 1
  | some (.inr ⟨e, _, _⟩) => c e

/-- The band module with coefficients `c` (a copy of `k^V`). -/
@[ext]
structure Band (_c : Fin (m + 1) ⊕ Fin (m + 1) → k) where
  /-- The coordinates. -/
  toFun : Fin (m + 1) ⊕ Fin (m + 1) → k

variable (c : Fin (m + 1) ⊕ Fin (m + 1) → k)

namespace Band

variable {k m c}

instance : Zero (Band k m c) := ⟨⟨0⟩⟩
instance : Add (Band k m c) := ⟨fun φ ψ ↦ ⟨φ.toFun + ψ.toFun⟩⟩
instance : Neg (Band k m c) := ⟨fun φ ↦ ⟨-φ.toFun⟩⟩
instance : Sub (Band k m c) := ⟨fun φ ψ ↦ ⟨φ.toFun - ψ.toFun⟩⟩
instance : SMul ℕ (Band k m c) := ⟨fun n φ ↦ ⟨n • φ.toFun⟩⟩
instance : SMul ℤ (Band k m c) := ⟨fun n φ ↦ ⟨n • φ.toFun⟩⟩
instance : SMul k (Band k m c) := ⟨fun a φ ↦ ⟨a • φ.toFun⟩⟩

@[simp] lemma zero_toFun : (0 : Band k m c).toFun = 0 := rfl
@[simp] lemma add_toFun (φ ψ : Band k m c) : (φ + ψ).toFun = φ.toFun + ψ.toFun := rfl
@[simp] lemma smul_toFun (a : k) (φ : Band k m c) : (a • φ).toFun = a • φ.toFun := rfl

lemma toFun_injective : Function.Injective (Band.toFun : Band k m c → _) :=
  fun _ _ h ↦ Band.ext h

instance : AddCommGroup (Band k m c) :=
  toFun_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance : Module k (Band k m c) :=
  toFun_injective.module k (⟨⟨Band.toFun, rfl⟩, fun _ _ ↦ rfl⟩ : Band k m c →+ _) fun _ _ ↦ rfl

end Band

/-- The action of a morphism on `k^V`. -/
def bandAct {X Y : Cr m} (f : X ⟶ Y) : Module.End k (Band k m c) where
  toFun φ := ⟨fun u ↦ if u = Y.as then bandCoef k m c f * φ.toFun X.as else 0⟩
  map_add' φ ψ := by
    ext u
    simp only [Band.add_toFun, Pi.add_apply]
    split_ifs <;> simp [mul_add]
  map_smul' a φ := by
    ext u
    simp only [Band.smul_toFun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp [mul_left_comm]

lemma bandAct_apply {X Y : Cr m} (f : X ⟶ Y) (φ : Band k m c) (u : Fin (m + 1) ⊕ Fin (m + 1)) :
    (bandAct k m c f φ).toFun u = if u = Y.as then bandCoef k m c f * φ.toFun X.as else 0 := rfl

lemma bandCoef_comp {X Y Z : Cr m} (f : X ⟶ Y) (g : Y ⟶ Z) :
    bandCoef k m c (f ≫ g) = bandCoef k m c g * bandCoef k m c f := by
  rw [RSZ.comp_def]
  rcases f with _ | ⟨⟨_, h⟩ | ⟨e, hs, ht⟩⟩ <;> rcases g with _ | ⟨⟨_, h'⟩ | ⟨e', hs', ht'⟩⟩
  all_goals simp only [RHom.comp, bandCoef, mul_one, one_mul, mul_zero, zero_mul]
  exact absurd (ht.trans hs'.symm) (crTgt_ne_crSrc m e e')

lemma bandAct_zero {X Y : Cr m} : bandAct k m c (0 : X ⟶ Y) = 0 := by
  refine LinearMap.ext fun φ ↦ Band.ext (funext fun u ↦ ?_)
  rw [bandAct_apply]
  simp [bandCoef, RSZ.zero_def]

/-- The representation of `k(Cr m)` on `k^V`. -/
def bandRep : Linearization (Cr m) k →ₐ[k] Module.End k (Band k m c) :=
  linLift k (fun f ↦ bandAct k m c f) (bandAct_zero k m c)
    (by
      intro X Y Z f g
      refine LinearMap.ext fun φ ↦ Band.ext (funext fun u ↦ ?_)
      simp only [Module.End.mul_apply, bandAct_apply, bandCoef_comp]
      split_ifs <;> simp [mul_assoc])
    (by
      intro X Y Y' Z f g hY
      refine LinearMap.ext fun φ ↦ Band.ext (funext fun u ↦ ?_)
      have : Y.as ≠ Y'.as := fun h ↦ hY (RSZ.ext_as h)
      simp only [Module.End.mul_apply, bandAct_apply, LinearMap.zero_apply, Band.zero_toFun,
        Pi.zero_apply]
      split_ifs <;> simp_all)
    (by
      refine LinearMap.ext fun φ ↦ Band.ext (funext fun u ↦ ?_)
      rw [LinearMap.sum_apply]
      rw [show (∑ X : Cr m, bandAct k m c (𝟙 X) φ).toFun u =
          ∑ X : Cr m, (bandAct k m c (𝟙 X) φ).toFun u from
        map_sum (⟨⟨fun ψ : Band k m c ↦ ψ.toFun u, rfl⟩, fun _ _ ↦ rfl⟩ : Band k m c →+ k) _ _]
      simp only [bandAct_apply, Module.End.one_apply]
      rw [Finset.sum_eq_single (⟨u⟩ : Cr m) (fun X _ hX ↦ if_neg fun h ↦ hX (RSZ.ext_as h.symm))
        (by simp)]
      simp [bandCoef, RSZ.id_def])

instance : Module (Linearization (Cr m) k) (Band k m c) := Module.compHom _ (bandRep k m c).toRingHom
instance : IsScalarTower k (Linearization (Cr m) k) (Band k m c) where
  smul_assoc a b φ := by
    change bandRep k m c (a • b) φ = a • bandRep k m c b φ
    rw [map_smul]
    rfl

variable {k m c}

lemma morElt_smul_band {X Y : Cr m} (f : X ⟶ Y) (φ : Band k m c) (u : Fin (m + 1) ⊕ Fin (m + 1)) :
    (morElt k f • φ).toFun u = if u = Y.as then bandCoef k m c f * φ.toFun X.as else 0 := by
  change (bandRep k m c (morElt k f) φ).toFun u = _
  rw [show bandRep k m c (morElt k f) = bandAct k m c f from
    linLiftₗ_morElt k _ (bandAct_zero k m c) f]
  rfl

/-- The basis vector at a vertex. -/
def bvec (v : Fin (m + 1) ⊕ Fin (m + 1)) : Band k m c := ⟨Pi.single v 1⟩

lemma id_smul_bvec (v : Fin (m + 1) ⊕ Fin (m + 1)) :
    morElt k (𝟙 (⟨v⟩ : Cr m)) • (bvec v : Band k m c) = bvec v := by
  ext u
  rw [morElt_smul_band]
  simp only [bvec, Pi.single_apply, bandCoef, RSZ.id_def]
  split_ifs <;> simp_all

lemma arr_smul_bvec (e : Fin (m + 1) ⊕ Fin (m + 1)) :
    morElt k (RSZ.arr (src := crSrc m) (tgt := crTgt m) e) • (bvec (crSrc m e) : Band k m c) =
      c e • bvec (crTgt m e) := by
  ext u
  rw [morElt_smul_band]
  simp only [bvec, Pi.single_apply, bandCoef, RSZ.arr, Band.smul_toFun, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

variable {c' : Fin (m + 1) ⊕ Fin (m + 1) → k}

/-- A module map between band modules is diagonal. -/
lemma map_bvec (φ : Band k m c →ₗ[Linearization (Cr m) k] Band k m c')
    (v : Fin (m + 1) ⊕ Fin (m + 1)) : φ (bvec v) = (φ (bvec v)).toFun v • bvec v := by
  have h1 : φ (bvec v) = morElt k (𝟙 (⟨v⟩ : Cr m)) • φ (bvec v) := by
    conv_lhs => rw [← id_smul_bvec (c := c) v]
    rw [map_smul]
  ext u
  conv_lhs => rw [h1]
  rw [morElt_smul_band]
  simp only [bvec, Band.smul_toFun, Pi.smul_apply, Pi.single_apply, bandCoef, RSZ.id_def,
    smul_eq_mul]
  split_ifs with h
  · subst h
    simp
  · simp

/-- The diagonal coefficients of a module map are compatible with the arrows. -/
lemma map_coef (φ : Band k m c →ₗ[Linearization (Cr m) k] Band k m c')
    (e : Fin (m + 1) ⊕ Fin (m + 1)) :
    c e * (φ (bvec (crTgt m e))).toFun (crTgt m e) =
      c' e * (φ (bvec (crSrc m e))).toFun (crSrc m e) := by
  have h := congrArg (fun ψ : Band k m c' ↦ ψ.toFun (crTgt m e))
    (map_smul φ (morElt k (RSZ.arr (src := crSrc m) (tgt := crTgt m) e)) (bvec (crSrc m e)))
  rw [arr_smul_bvec, LinearMap.map_smul_of_tower, map_bvec φ (crSrc m e), smul_comm,
    arr_smul_bvec] at h
  simpa [bvec, mul_comm] using h

/-! ### The band family of the alternating cycle -/

variable (m) in
/-- The coefficients of the band module with parameter `t`: every arrow acts by
`1` except `σₘ`, which acts by `t`. -/
def bandC (t : k) : Fin (m + 1) ⊕ Fin (m + 1) → k
  | .inl _ => 1
  | .inr i => if i = Fin.last m then t else 1

/-- The diagonal coefficients of a map between band modules are all equal. -/
lemma diag_eq {t t' : k} (φ : Band k m (bandC m t) →ₗ[Linearization (Cr m) k] Band k m (bandC m t'))
    (v : Fin (m + 1) ⊕ Fin (m + 1)) :
    (φ (bvec v)).toFun v = (φ (bvec (.inl 0))).toFun (.inl 0) := by
  set d : Fin (m + 1) ⊕ Fin (m + 1) → k := fun v ↦ (φ (bvec v)).toFun v with hd
  have hρ : ∀ i, d (.inr i) = d (.inl i) := fun i ↦ by
    simpa [bandC, crSrc, crTgt] using map_coef φ (.inl i)
  have hσ : ∀ i, i ≠ Fin.last m → d (.inr i) = d (.inl (i + 1)) := fun i hi ↦ by
    simpa [bandC, crSrc, crTgt, hi] using map_coef φ (.inr i)
  have hx : ∀ n (hn : n < m + 1), d (.inl ⟨n, hn⟩) = d (.inl 0) := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      have hj : (⟨n, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
        intro h; rw [Fin.ext_iff] at h; simp at h; omega
      have h1 : (⟨n, by omega⟩ : Fin (m + 1)) + 1 = ⟨n + 1, hn⟩ := by
        ext; rw [Fin.val_add_one_of_lt (by rw [Fin.lt_iff_val_lt_val]; simp; omega)]
      rw [← h1, ← hσ _ hj, hρ, ih]
  change d v = d (.inl 0)
  rcases v with i | i
  · exact hx i.1 i.2
  · rw [hρ]; exact hx i.1 i.2

lemma band_sum (ψ : Band k m c) : ψ = ∑ v, ψ.toFun v • bvec v := by
  ext u
  rw [show (∑ v, ψ.toFun v • (bvec v : Band k m c)).toFun u = ∑ v, (ψ.toFun v • (bvec v : Band k m c)).toFun u from
    map_sum (⟨⟨fun ψ : Band k m c ↦ ψ.toFun u, rfl⟩, fun _ _ ↦ rfl⟩ : Band k m c →+ k) _ _]
  simp [bvec, Pi.single_apply]

/-- A map between band modules is a scalar multiple of the identity on coordinates. -/
lemma map_eq_smul {t t' : k}
    (φ : Band k m (bandC m t) →ₗ[Linearization (Cr m) k] Band k m (bandC m t'))
    (ψ : Band k m (bandC m t)) :
    (φ ψ).toFun = (φ (bvec (.inl 0))).toFun (.inl 0) • ψ.toFun := by
  conv_lhs => rw [band_sum ψ]
  rw [map_sum]
  funext u
  rw [show (∑ v, φ (ψ.toFun v • bvec v)).toFun u = ∑ v, (φ (ψ.toFun v • bvec v)).toFun u from
    map_sum (⟨⟨fun ψ : Band k m (bandC m t') ↦ ψ.toFun u, rfl⟩, fun _ _ ↦ rfl⟩ :
      Band k m (bandC m t') →+ k) _ _]
  simp only [LinearMap.map_smul_of_tower]
  conv_lhs => arg 2; ext v; rw [map_bvec φ v, diag_eq φ v]
  simp [bvec, Pi.single_apply, mul_comm]

/-- Isomorphic band modules have the same parameter. -/
lemma band_param_eq {t t' : k}
    (φ : Band k m (bandC m t) ≃ₗ[Linearization (Cr m) k] Band k m (bandC m t')) : t = t' := by
  have hd : (φ (bvec (.inl 0))).toFun (.inl 0) ≠ 0 := by
    intro h0
    have : φ (bvec (.inl 0)) = 0 := by
      ext u
      have := congrFun (map_eq_smul φ.toLinearMap (bvec (.inl 0))) u
      simp only [LinearEquiv.coe_coe] at this
      rw [this, h0, zero_smul]
      rfl
    have h2 := φ.injective (this.trans φ.map_zero.symm)
    have := congrArg (fun ψ : Band k m (bandC m t) ↦ ψ.toFun (.inl 0)) h2
    simp [bvec] at this
  have h := map_coef φ.toLinearMap (.inr (Fin.last m))
  rw [diag_eq φ.toLinearMap (crTgt m _), diag_eq φ.toLinearMap (crSrc m _)] at h
  simp only [bandC, ite_true, LinearEquiv.coe_coe] at h
  exact mul_right_cancel₀ hd h

/-- Band modules are indecomposable. -/
lemma band_isIndecomposable (t : k) :
    Statement.IsIndecomposable (Linearization (Cr m) k) (Band k m (bandC m t)) := by
  refine ⟨⟨bvec (.inl 0), 0, fun h ↦ ?_⟩, fun N N' hN ↦ ?_⟩
  · have := congrArg (fun ψ : Band k m (bandC m t) ↦ ψ.toFun (.inl 0)) h
    simp [bvec] at this
  let π : Band k m (bandC m t) →ₗ[Linearization (Cr m) k] Band k m (bandC m t) :=
    N.subtype ∘ₗ Submodule.projectionOnto (R := Linearization (Cr m) k) N N' hN
  set d := (π (bvec (.inl 0))).toFun (.inl 0)
  have hπ : ∀ ψ, π ψ = d • ψ := fun ψ ↦ Band.ext (map_eq_smul π ψ)
  have hidem : d * d = d := by
    have h2 : π (π (bvec (.inl 0))) = π (bvec (.inl 0)) := by
      simp only [π, LinearMap.comp_apply, Submodule.coe_subtype]
      rw [Submodule.projectionOnto_apply_left (R := Linearization (Cr m) k) (p := N) (q := N') hN]
    rw [hπ, hπ, smul_smul] at h2
    have := congrArg (fun ψ : Band k m (bandC m t) ↦ ψ.toFun (.inl 0)) h2
    simpa [bvec] using this
  have hd01 : d * (d - 1) = 0 := by rw [mul_sub, mul_one, hidem, sub_self]
  rcases mul_eq_zero.1 hd01 with h0 | h1
  · left
    refine eq_bot_iff.2 fun x hx ↦ ?_
    have : π x = x := by simp [π, Submodule.projectionOnto_apply_left (R := Linearization (Cr m) k) (p := N) (q := N') hN ⟨x, hx⟩]
    rw [hπ, h0, zero_smul] at this
    exact (Submodule.mem_bot _).2 this.symm
  · right
    have h1 : d = 1 := sub_eq_zero.1 h1
    refine eq_bot_iff.2 fun x hx ↦ ?_
    have : π x = 0 := by simp [π, Submodule.projectionOnto_apply_right (R := Linearization (Cr m) k) (p := N) (q := N') hN ⟨x, hx⟩]
    rw [hπ, h1, one_smul] at this
    exact (Submodule.mem_bot _).2 this

instance : Module.Finite k (Band k m c) :=
  Module.Finite.of_injective
    (⟨⟨Band.toFun, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩ : Band k m c →ₗ[k] (Fin (m + 1) ⊕ Fin (m + 1) → k))
    Band.toFun_injective

instance : Module.Finite (Linearization (Cr m) k) (Band k m c) :=
  Module.Finite.of_restrictScalars_finite k _ _

variable (k m) in
/-- **Crowns are representation-infinite**: over an infinite field, the band
modules form an infinite family of pairwise non-isomorphic finite-dimensional
indecomposable `k(Cr m)`-modules. -/
theorem not_isRepresentationFinite_crown [Infinite k] :
    ¬Statement.IsRepresentationFinite (Linearization (Cr m) k) := by
  rintro ⟨n, Bs, hB⟩
  choose i hi using fun t : k ↦ hB (Band k m (bandC m t)) (band_isIndecomposable t)
  obtain ⟨t, t', hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite i
  obtain ⟨e⟩ := hi t
  obtain ⟨e'⟩ := hi t'
  rw [heq] at e
  exact hne (band_param_eq (e.trans e'.symm))

end RayCat

end LargeIndecomposable
