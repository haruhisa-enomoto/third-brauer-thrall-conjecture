module

public import LargeIndecomposable.BongartzTheorem.Reduction.ControlledEmbeddings
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Corollaries 1.1 and 5.3

Applying the representation embedding of Theorem A to Kronecker bricks of
every infinite dimension gives indecomposable modules of every infinite
dimension (Corollary 1.1), with local endomorphism algebras whose radicals are
nilpotent of an exponent independent of the dimension (Corollary 5.3, through
the retractions of Proposition 5.2).

The Kronecker bricks are supplied by Göbel–Simson, Corollary 1.3; here this
input is the hypothesis `KroneckerBricks`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair

universe u

variable {k : Type u} [Field k]

/-- A Kronecker brick: a nonzero Kronecker module whose endomorphisms are
scalars. -/
def IsBrickKron (T : Kron k) : Prop :=
  ¬ IsZero T ∧ ∀ f : T ⟶ T, ∃ c : k, f = c • 𝟙 T

/-- Hypothesis (Göbel–Simson, Corollary 1.3): Kronecker bricks of every
infinite dimension. -/
def KroneckerBricks : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (κ : Cardinal.{u}), Cardinal.aleph0 ≤ κ →
    ∃ T : Kron k, T.dim = κ ∧ IsBrickKron T

/-- A linear functional equal to `1` at `x` and vanishing on `p ∌ x`. -/
lemma exists_functional {M : Type u} [AddCommGroup M] [Module k M] {p : Submodule k M} {x : M}
    (hx : x ∉ p) : ∃ φ : M →ₗ[k] k, φ x = 1 ∧ ∀ y ∈ p, φ y = 0 := by
  obtain ⟨φ, hφx, hφp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  refine ⟨(φ x)⁻¹ • φ, by simp [hφx], fun y hy ↦ ?_⟩
  have : φ y ∈ p.map φ := ⟨y, hy, rfl⟩
  rw [hφp, Submodule.mem_bot] at this
  simp [this]

/-- The rank-one map `x ↦ φ(x) v`. -/
def rankOne {M N : Type u} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (φ : M →ₗ[k] k) (v : N) : M →ₗ[k] N :=
  (LinearMap.toSpanSingleton k N v).comp φ

lemma rankOne_apply {M N : Type u} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (φ : M →ₗ[k] k) (v : N) (x : M) : rankOne φ v x = φ x • v := rfl

/-- If `c • x = φ(x) v` for all `x` with `c ≠ 0`, the space has dimension at most one. -/
lemma rank_le_one_of_eq_rankOne {M : Type u} [AddCommGroup M] [Module k M] {c : k} (hc : c ≠ 0)
    (φ : M →ₗ[k] k) (v : M) (h : ∀ x, φ x • v = c • x) : Module.rank k M ≤ 1 := by
  rw [rank_le_one_iff]
  exact ⟨v, fun x ↦ ⟨c⁻¹ * φ x, by rw [mul_smul, h, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩⟩

lemma dim_lt_aleph0 {T : Kron k} (hV : Module.rank k T.V ≤ 1) (hW : Module.rank k T.W ≤ 1) :
    T.dim < Cardinal.aleph0 := by
  unfold Kron.dim
  exact Cardinal.add_lt_aleph0 (hV.trans_lt Cardinal.one_lt_aleph0)
    (hW.trans_lt Cardinal.one_lt_aleph0)

lemma rank_le_one_of_subsingleton {M : Type u} [AddCommGroup M] [Module k M] [Subsingleton M] :
    Module.rank k M ≤ 1 := by
  rw [rank_subsingleton']; exact zero_le_one

/-- An infinite-dimensional Kronecker brick lies in `D`. -/
lemma IsBrickKron.inD {T : Kron k} (hT : IsBrickKron T) (hinf : Cardinal.aleph0 ≤ T.dim) :
    InD T := by
  rw [inD_iff]
  by_contra hcon
  push Not at hcon
  obtain ⟨v, ha, hb, hv⟩ := hcon
  obtain ⟨φ, hφ, -⟩ := exists_functional (k := k) (p := ⊥) (x := v) (by simpa using hv)
  let f : T ⟶ T := Kron.homMk (ModuleCat.ofHom (rankOne φ v)) 0
    (by ext x; simp [rankOne_apply, ha]) (by ext x; simp [rankOne_apply, hb])
  obtain ⟨c, hc⟩ := hT.2 f
  have h0 := congrArg (fun g : T ⟶ T ↦ (g.app zero).hom) hc
  have h1 := congrArg (fun g : T ⟶ T ↦ (g.app one).hom) hc
  simp only [f] at h0 h1
  by_cases hc0 : c = 0
  · have := LinearMap.congr_fun h0 v
    simp [rankOne_apply, hφ, hc0] at this
    exact hv this
  · have hW : Subsingleton T.W := ⟨fun x y ↦ by
      have hx := LinearMap.congr_fun h1 x
      have hy := LinearMap.congr_fun h1 y
      simp at hx hy
      rw [← smul_right_injective _ hc0 |>.eq_iff]
      rw [← hx, ← hy]⟩
    refine absurd hinf (not_le.2 (dim_lt_aleph0 ?_ rank_le_one_of_subsingleton))
    exact rank_le_one_of_eq_rankOne hc0 φ v fun x ↦ by
      have := LinearMap.congr_fun h0 x
      simpa [rankOne_apply] using this

/-- An infinite-dimensional Kronecker brick lies in `C`. -/
lemma IsBrickKron.inC {T : Kron k} (hT : IsBrickKron T) (hinf : Cardinal.aleph0 ≤ T.dim) :
    InC T := by
  refine ⟨hT.inD hinf, ?_⟩
  by_contra hcon
  obtain ⟨w, -, hw⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hcon)
  obtain ⟨ψ, hψ, hψR⟩ := exists_functional hw
  let f : T ⟶ T := Kron.homMk 0 (ModuleCat.ofHom (rankOne ψ w))
    (by ext x; simp [rankOne_apply, hψR _ (Submodule.mem_sup_left ⟨x, rfl⟩)])
    (by ext x; simp [rankOne_apply, hψR _ (Submodule.mem_sup_right ⟨x, rfl⟩)])
  obtain ⟨c, hc⟩ := hT.2 f
  have h0 := congrArg (fun g : T ⟶ T ↦ (g.app zero).hom) hc
  have h1 := congrArg (fun g : T ⟶ T ↦ (g.app one).hom) hc
  simp only [f] at h0 h1
  by_cases hc0 : c = 0
  · have := LinearMap.congr_fun h1 w
    simp [rankOne_apply, hψ, hc0] at this
    exact hw (this ▸ Submodule.zero_mem _)
  · have hV : Subsingleton T.V := ⟨fun x y ↦ by
      have hx := LinearMap.congr_fun h0 x
      have hy := LinearMap.congr_fun h0 y
      simp at hx hy
      rw [← smul_right_injective _ hc0 |>.eq_iff]
      rw [← hx, ← hy]⟩
    refine absurd hinf (not_le.2 (dim_lt_aleph0 rank_le_one_of_subsingleton ?_))
    exact rank_le_one_of_eq_rankOne hc0 ψ w fun x ↦ by
      have := LinearMap.congr_fun h1 x
      simpa [rankOne_apply] using this

/-- A bound for `n` maps gives a bound for `n + 1` maps. -/
lemma Retractions.NilpotentBound.succ {A : Type u} [Ring A] [Algebra k A] {𝒞 : Type*}
    [Category 𝒞] [Preadditive 𝒞] [Linear k 𝒞] {Ψ : 𝒞 ⥤ ModuleCat.{u} A} (R : Retractions k Ψ)
    {n : ℕ} (h : R.NilpotentBound n) : R.NilpotentBound (n + 1) := by
  intro X Y f hf
  cases hf with
  | cons hf' hg => rw [h _ hf', Limits.zero_comp]

/-! ### The modules of Corollaries 1.1 and 5.3 -/

section Modules

variable {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A] (E : ControlledEmbedding k A)
  {T : Kron k} (hT : IsBrickKron T) (hinf : Cardinal.aleph0 ≤ T.dim)

/-- `T` as an object of `C`. -/
def brickC : (InCD (k := k)).FullSubcategory :=
  ⟨⟨T, (hT.inC hinf).1⟩, hT.inC hinf⟩

/-- The retractions of Proposition 5.2 for the extension of `E`. -/
abbrev Rext := Extension.retractions E.Φ E.R E.isRepEmbeddingFin.fin

lemma brickC_scalar (f : brickC hT hinf ⟶ brickC hT hinf) : ∃ c : k, f = c • 𝟙 _ := by
  obtain ⟨c, hc⟩ := hT.2 f.hom.hom
  exact ⟨c, by ext1; ext1; exact hc⟩

lemma brickC_id_ne_zero : (𝟙 (brickC hT hinf) : brickC hT hinf ⟶ brickC hT hinf) ≠ 0 := by
  intro h
  exact hT.1 ((IsZero.iff_id_eq_zero _).2 (congrArg (fun φ ↦ InCD.kh φ) h))

lemma iter_hom {M : ModuleCat.{u} A} (w : M ⟶ M) (m : ℕ) :
    (Retractions.iter w m).hom = w.hom ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Retractions.iter, ModuleCat.hom_comp, ih, pow_succ']; rfl

/-- The module `F(T)`. -/
abbrev FT : ModuleCat.{u} A := ((InCD (k := k)).ι ⋙ Extension.functor E.Φ).obj (brickC hT hinf)

include hinf in
/-- The module `F(T)` is indecomposable. -/
theorem isIndecomposable_brick : IsIndecomposable A (FT E hT hinf) := by
  refine Retractions.isIndecomposable (Rext E) (Extension.nilpotentBound E.Φ E.R
    E.isRepEmbeddingFin.fin E.bound) (brickC_id_ne_zero hT hinf) fun e he ↦ ?_
  obtain ⟨c, rfl⟩ := brickC_scalar hT hinf e
  have hc : c * c = c := by
    have h := he
    rw [Linear.smul_comp, Linear.comp_smul, Category.comp_id, smul_smul] at h
    by_contra hne
    apply brickC_id_ne_zero hT hinf
    have := congrArg (fun φ ↦ φ) ((sub_eq_zero.2 h))
    rw [← sub_smul] at this
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  by_cases h0 : c = 0
  · left; rw [h0, zero_smul]
  · right; rw [show c = 1 by
      have : c * (c - 1) = 0 := by rw [mul_sub, hc, mul_one, sub_self]
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h0), one_smul]

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

/-- The retraction of an endomorphism of `F(T)`. -/
abbrev ρE (x : Module.End A (FT E hT hinf)) : brickC hT hinf ⟶ brickC hT hinf :=
  (Rext E).ρ _ _ (ModuleCat.ofHom x)

lemma ρE_mul (x y : Module.End A (FT E hT hinf)) :
    ρE E hT hinf (x * y) = ρE E hT hinf y ≫ ρE E hT hinf x :=
  (Rext E).map_comp (ModuleCat.ofHom y) (ModuleCat.ofHom x)

lemma ρE_sub (x y : Module.End A (FT E hT hinf)) :
    ρE E hT hinf (x - y) = ρE E hT hinf x - ρE E hT hinf y :=
  map_sub ((Rext E).ρ (brickC hT hinf) (brickC hT hinf)) (ModuleCat.ofHom x) (ModuleCat.ofHom y)

lemma ρE_algebraMap (c : k) : ρE E hT hinf (algebraMap k _ c) = c • 𝟙 _ := by
  have : ModuleCat.ofHom (algebraMap k (Module.End A (FT E hT hinf)) c) = c • 𝟙 _ := by
    ext m; rfl
  have e2 : (Rext E).ρ (brickC hT hinf) (brickC hT hinf) (c • 𝟙 _) = c • 𝟙 _ := by
    rw [map_smul, Retractions.ρ_id]
  exact (congrArg ((Rext E).ρ (brickC hT hinf) (brickC hT hinf)) this).trans e2

lemma ker_mem_jacobson (y : Module.End A (FT E hT hinf)) (hy : ρE E hT hinf y = 0) :
    y ∈ Ring.jacobson (Module.End A (FT E hT hinf)) := by
  refine Corner.mem_jacobson_of_forall_isUnit fun z ↦ IsNilpotent.isUnit_one_sub ⟨E.n, ?_⟩
  have h0 : (Rext E).ρ _ _ (ModuleCat.ofHom (z * y)) = 0 :=
    (ρE_mul E hT hinf z y).trans (by rw [hy, Limits.zero_comp])
  have := Extension.nilpotentBound E.Φ E.R E.isRepEmbeddingFin.fin E.bound _
    ((Rext E).kerChain_iter _ h0 E.n)
  have h := congrArg ModuleCat.Hom.hom this
  exact (iter_hom (ModuleCat.ofHom (z * y)) E.n).symm.trans h

lemma one_not_mem_jacobson : (1 : Module.End A (FT E hT hinf)) ∉
    Ring.jacobson (Module.End A (FT E hT hinf)) := by
  have : Nontrivial (FT E hT hinf) := (isIndecomposable_brick E hT hinf).1
  have : Nontrivial (Module.End A (FT E hT hinf)) := inferInstance
  rw [Ring.jacobson_eq_sInf_isMaximal, Submodule.mem_sInf]
  intro h
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (Module.End A (FT E hT hinf))
  exact hI.ne_top ((Ideal.eq_top_iff_one I).2 (h I hI))

lemma ρE_eq_zero_of_mem {x : Module.End A (FT E hT hinf)}
    (hx : x ∈ Ring.jacobson (Module.End A (FT E hT hinf))) : ρE E hT hinf x = 0 := by
  obtain ⟨c, hc⟩ := brickC_scalar hT hinf (ρE E hT hinf x)
  by_cases h0 : c = 0
  · rw [hc, h0, zero_smul]
  exfalso
  have hy : x - algebraMap k _ c ∈ Ring.jacobson (Module.End A (FT E hT hinf)) :=
    ker_mem_jacobson E hT hinf _ (by rw [ρE_sub, ρE_algebraMap, hc, sub_self])
  have hc' : algebraMap k (Module.End A (FT E hT hinf)) c ∈ Ring.jacobson _ := by
    have := Submodule.sub_mem _ hx hy
    rwa [sub_sub_cancel] at this
  apply one_not_mem_jacobson E hT hinf
  have := (Ring.jacobson (Module.End A (FT E hT hinf))).smul_mem (algebraMap k _ c⁻¹) hc'
  rwa [smul_eq_mul, ← map_mul, inv_mul_cancel₀ h0, map_one] at this

lemma prod_eq_zero (f : Fin (E.n + 1) → Module.End A (FT E hT hinf))
    (hf : ∀ i, f i ∈ Ring.jacobson (Module.End A (FT E hT hinf))) : (List.ofFn f).prod = 0 := by
  have key : ∀ (m : ℕ) (g : Fin m → Module.End A (FT E hT hinf)),
      (∀ i, ρE E hT hinf (g i) = 0) → (Rext E).KerChain m (ModuleCat.ofHom (List.ofFn g).prod) := by
    intro m
    induction m with
    | zero => intro g _; exact Retractions.KerChain.nil _
    | succ m ih =>
      intro g hg
      rw [List.ofFn_succ, List.prod_cons]
      exact Retractions.KerChain.cons (ih _ fun i ↦ hg i.succ) (hg 0)
  have h := key _ f fun i ↦ ρE_eq_zero_of_mem E hT hinf (hf i)
  have hz := Retractions.NilpotentBound.succ _
    (Extension.nilpotentBound E.Φ E.R E.isRepEmbeddingFin.fin E.bound) _ h
  exact congrArg ModuleCat.Hom.hom hz

omit [FiniteDimensional k A] in
lemma rank_FT : Module.rank k (FT E hT hinf) = T.dim :=
  Extension.dim_eq E.Φ E.isRepEmbeddingFin.fin (brickC hT hinf).obj hinf

end Modules

section Main

variable (H : DistributiveControlled.{u}) (G : KroneckerBricks.{u})

include H G in
/-- Corollary 1.1, conditional on the two hypotheses. -/
theorem corollaryDimension_of : CorollaryDimension.{u} := by
  intro k _ _ A _ _ _ hA κ hκ
  obtain ⟨E⟩ := nonempty_controlledEmbedding_of_not_isRepresentationFinite (k := k) H A hA
  obtain ⟨T, hTd, hT⟩ := G k κ hκ
  have hinf : Cardinal.aleph0 ≤ T.dim := hTd ▸ hκ
  exact ⟨FT E hT hinf, inferInstance, inferInstance, ModuleCat.moduleOfAlgebraModule _,
    ModuleCat.isScalarTower_of_algebra_moduleCat _, (rank_FT E hT hinf).trans hTd,
    isIndecomposable_brick E hT hinf⟩

include H G in
/-- Corollary 5.3, conditional on the two hypotheses. -/
theorem corollaryRadical_of : CorollaryRadical.{u} := by
  intro k _ _ A _ _ _ hA
  obtain ⟨E⟩ := nonempty_controlledEmbedding_of_not_isRepresentationFinite (k := k) H A hA
  refine ⟨E.n + 1, Nat.succ_le_succ (Nat.zero_le _), fun κ hκ ↦ ?_⟩
  obtain ⟨T, hTd, hT⟩ := G k κ hκ
  have hinf : Cardinal.aleph0 ≤ T.dim := hTd ▸ hκ
  let _ := ModuleCat.moduleOfAlgebraModule (k := k) (FT E hT hinf)
  have := ModuleCat.isScalarTower_of_algebra_moduleCat (k := k) (FT E hT hinf)
  refine ⟨FT E hT hinf, inferInstance, inferInstance, inferInstance, inferInstance,
    (rank_FT E hT hinf).trans hTd, fun x ↦ ?_, one_not_mem_jacobson E hT hinf,
    prod_eq_zero E hT hinf, isIndecomposable_brick E hT hinf⟩
  obtain ⟨c, hc⟩ := brickC_scalar hT hinf (ρE E hT hinf x)
  exact ⟨c, ker_mem_jacobson E hT hinf _ (by rw [ρE_sub, ρE_algebraMap, hc, sub_self])⟩

end Main

end LargeIndecomposable
