module

public import LargeIndecomposable.AuslanderReiten.Translate.Tau

/-!
# `Ext¹` from a free presentation

For a free presentation `P` of `Z` with generator map `g₀ : Aⁿ⁰ → Z` and syzygy `Ω = ker g₀`,
`Ext¹_P(Z, W) = Hom_A(Ω, W) / {restrictions of maps Aⁿ⁰ → W}` (`Ext1`). When the relation rows
are free generators of `Ω` (`P.Free`, i.e. `pd Z ≤ 1` with this resolution), `Ext¹_P(Z, W)` is
`Wⁿ¹ / F Wⁿ⁰` (`ext1EquivCoker`), and the Auslander–Reiten formula reads
`dim Hom(W, τ_P Z) = dim Ext¹_P(Z, W)` (`finrank_hom_tau_eq_ext1`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open Module

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
variable {Z : Type*} [AddCommGroup Z] [Module A Z]

/-- The generator map `Aⁿ⁰ → Z`. -/
def FreePres.gen (P : FreePres A Z) : (Fin P.n₀ → A) →ₗ[A] Z where
  toFun p := ∑ j, p j • P.z j
  map_add' p q := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a p := by simp [mul_smul, Finset.smul_sum]

/-- The syzygy `Ω = ker(Aⁿ⁰ → Z)`. -/
abbrev FreePres.syz (P : FreePres A Z) : Submodule A (Fin P.n₀ → A) := LinearMap.ker P.gen

/-- The relation rows lie in the syzygy. -/
lemma FreePres.row_mem (P : FreePres A Z) (i : Fin P.n₁) : P.F i ∈ P.syz := P.rel i

/-- The rows generate the syzygy. -/
lemma FreePres.syz_eq_span (P : FreePres A Z) (p : Fin P.n₀ → A) (hp : p ∈ P.syz) :
    ∃ r : Fin P.n₁ → A, p = ∑ i, r i • P.F i := by
  obtain ⟨r, hr⟩ := P.exact p hp
  refine ⟨r, funext fun j ↦ ?_⟩
  rw [hr j, Finset.sum_apply]
  rfl

/-- The relation rows are free generators of the syzygy (projective dimension at most one). -/
def FreePres.Free (P : FreePres A Z) : Prop :=
  ∀ r : Fin P.n₁ → A, ∑ i, r i • P.F i = 0 → r = 0

variable {W : Type*} [AddCommGroup W] [Module A W] [Module k W] [IsScalarTower k A W]

/-- Restriction `Hom(Aⁿ⁰, W) → Hom(Ω, W)`. -/
def FreePres.restr (P : FreePres A Z) :
    ((Fin P.n₀ → A) →ₗ[A] W) →ₗ[k] (P.syz →ₗ[A] W) where
  toFun f := f ∘ₗ P.syz.subtype
  map_add' f g := LinearMap.add_comp _ _ _
  map_smul' c f := rfl

variable (W) in
/-- **`Ext¹` from a free presentation.** -/
abbrev Ext1 (P : FreePres A Z) : Type _ :=
  (P.syz →ₗ[A] W) ⧸ LinearMap.range (P.restr (k := k) (W := W))

/-- `r ↦ Σᵢ rᵢ Fᵢ`, into the syzygy. -/
def FreePres.rowMap (P : FreePres A Z) : (Fin P.n₁ → A) →ₗ[A] P.syz :=
  LinearMap.codRestrict P.syz
    { toFun r := ∑ i, r i • P.F i
      map_add' r r' := by simp [add_smul, Finset.sum_add_distrib]
      map_smul' a r := by simp [mul_smul, Finset.smul_sum] }
    fun r ↦ by
      change P.gen (∑ i, r i • P.F i) = 0
      rw [map_sum]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [map_smul, LinearMap.mem_ker.1 (P.row_mem i), smul_zero]

lemma FreePres.rowMap_apply (P : FreePres A Z) (r : Fin P.n₁ → A) :
    (P.rowMap r : Fin P.n₀ → A) = ∑ i, r i • P.F i := rfl

lemma FreePres.rowMap_eq (P : FreePres A Z) (r : Fin P.n₁ → A) :
    P.rowMap r = ∑ i, r i • (⟨P.F i, P.row_mem i⟩ : P.syz) := by
  apply Subtype.ext
  rw [FreePres.rowMap_apply, Submodule.coe_sum]
  rfl

lemma FreePres.rowMap_single (P : FreePres A Z) (i : Fin P.n₁) :
    P.rowMap (Pi.single i 1) = ⟨P.F i, P.row_mem i⟩ := by
  apply Subtype.ext
  rw [FreePres.rowMap_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp

lemma FreePres.rowMap_surjective (P : FreePres A Z) : Function.Surjective P.rowMap := by
  rintro ⟨p, hp⟩
  obtain ⟨r, hr⟩ := P.syz_eq_span p hp
  exact ⟨r, Subtype.ext (by rw [FreePres.rowMap_apply]; exact hr.symm)⟩

lemma FreePres.rowMap_injective (P : FreePres A Z) (hF : P.Free) :
    Function.Injective P.rowMap := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro r hr
  apply hF r
  have := congrArg Subtype.val (LinearMap.mem_ker.1 hr)
  rw [FreePres.rowMap_apply] at this
  exact this

/-- For a free presentation with free relation rows, the syzygy is free on the rows. -/
def FreePres.rowEquiv (P : FreePres A Z) (hF : P.Free) : (Fin P.n₁ → A) ≃ₗ[A] P.syz :=
  LinearEquiv.ofBijective P.rowMap ⟨P.rowMap_injective hF, P.rowMap_surjective⟩

/-- `Hom(Ω, W) ≅ Wⁿ¹`, `f ↦ (f Fᵢ)ᵢ`. -/
def FreePres.homSyzEquiv (P : FreePres A Z) (hF : P.Free) :
    (P.syz →ₗ[A] W) ≃ₗ[k] (Fin P.n₁ → W) where
  toFun f i := f ⟨P.F i, P.row_mem i⟩
  map_add' f g := rfl
  map_smul' c f := rfl
  invFun w := (LinearEquiv.piRing A W (Fin P.n₁) k).symm w ∘ₗ (P.rowEquiv hF).symm.toLinearMap
  left_inv f := by
    apply LinearMap.ext; intro x
    obtain ⟨r, rfl⟩ := (P.rowEquiv hF).surjective x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.piRing_symm_apply]
    change ∑ i, r i • f ⟨P.F i, P.row_mem i⟩ = f (P.rowMap r)
    rw [FreePres.rowMap_eq, map_sum]
    simp_rw [map_smul]
  right_inv w := by
    funext i
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [← FreePres.rowMap_single]
    change (LinearEquiv.piRing A W (Fin P.n₁) k).symm w ((P.rowEquiv hF).symm
      ((P.rowEquiv hF) (Pi.single i 1))) = w i
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.piRing_symm_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Pi.single_apply, hj]
    · simp

/-- Restriction corresponds to the relation map. -/
lemma FreePres.homSyzEquiv_restr (P : FreePres A Z) (hF : P.Free)
    (f : (Fin P.n₀ → A) →ₗ[A] W) :
    P.homSyzEquiv (k := k) hF (P.restr (k := k) f) = relMapLin (k := k) P.F (fun j ↦ f (Pi.single j 1)) := by
  funext i
  change f (P.F i) = ∑ j, P.F i j • f (Pi.single j 1)
  conv_lhs => rw [show P.F i = ∑ j, P.F i j • (Pi.single j 1 : Fin P.n₀ → A) by
    funext j'; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  simp_rw [map_smul]

lemma FreePres.map_range_restr (P : FreePres A Z) (hF : P.Free) :
    (LinearMap.range (P.restr (k := k) (W := W))).map (P.homSyzEquiv (k := k) hF).toLinearMap =
      LinearMap.range (relMapLin (k := k) (W := W) P.F) := by
  ext v
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨f, rfl⟩, rfl⟩
    exact ⟨_, (P.homSyzEquiv_restr hF f).symm⟩
  · rintro ⟨w, rfl⟩
    refine ⟨_, ⟨(LinearEquiv.piRing A W (Fin P.n₀) k).symm w, rfl⟩, ?_⟩
    rw [P.homSyzEquiv_restr hF]
    congr 1
    funext j
    rw [LinearEquiv.piRing_symm_apply, Finset.sum_eq_single j]
    · simp
    · intro j' _ hj; simp [Pi.single_apply, Ne.symm hj]
    · simp

/-- **`Ext¹` of a projective-dimension-one presentation is `Wⁿ¹ / F Wⁿ⁰`.** -/
def FreePres.ext1EquivCoker (P : FreePres A Z) (hF : P.Free) :
    Ext1 (k := k) W P ≃ₗ[k] (Fin P.n₁ → W) ⧸ LinearMap.range (relMapLin (k := k) (W := W) P.F) :=
  Submodule.Quotient.equiv _ _ (P.homSyzEquiv hF) (P.map_range_restr hF)

/-- **The Auslander–Reiten formula for `pd Z ≤ 1`**: `dim Hom(W, τ_P Z) = dim Ext¹_P(Z, W)`. -/
theorem finrank_hom_tau_eq_ext1 [FiniteDimensional k W] (P : FreePres A Z) (hF : P.Free) :
    finrank k (W →ₗ[A] tauK (k := k) P.F) = finrank k (Ext1 (k := k) W P) := by
  rw [(P.ext1EquivCoker hF).finrank_eq]
  have h1 := finrank_hom_tauK (k := k) (W := W) P.F
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range (relMapLin (k := k) (W := W) P.F))
  omega

end LargeIndecomposable.AR
