module

public import LargeIndecomposable.Modules.Duality.DualA

/-!
# Free presentations and the Nakayama map

`FreePres A Z`: generators `z : Fin n₀ → Z` and relation rows `F : Fin n₁ → Fin n₀ → A`
presenting `Z`, i.e. an exact sequence `Aⁿ¹ → Aⁿ⁰ → Z → 0`. Every finite-dimensional
module has one (`FreePres.exists`). A tuple `w ∈ Wⁿ⁰` killed by the relations comes from
a unique `A`-linear map `Z → W` (`FreePres.lift`).

`theta` identifies `Hom_A(W, DAⁿ)` with the `k`-dual of `Wⁿ`, and `nu F : DAⁿ¹ → DAⁿ⁰` is
the Nakayama transform of the presentation, with `theta (nu F ∘ ψ) = theta ψ ∘ F`
(`theta_nu_comp`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open Module

/-- A functional vanishing on the kernel of a linear map factors through it. -/
lemma exists_comp_of_ker_le {K V V' : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] (T : V →ₗ[K] V') (l : V →ₗ[K] K)
    (h : LinearMap.ker T ≤ LinearMap.ker l) : ∃ l' : V' →ₗ[K] K, l' ∘ₗ T = l := by
  let l₀ : LinearMap.range T →ₗ[K] K :=
    ((LinearMap.ker T).liftQ l h) ∘ₗ (LinearMap.quotKerEquivRange T).symm.toLinearMap
  obtain ⟨l', hl'⟩ := LinearMap.exists_extend l₀
  refine ⟨l', LinearMap.ext fun v ↦ ?_⟩
  have := congrArg (fun f ↦ f ⟨T v, LinearMap.mem_range_self T v⟩) hl'
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at this
  rw [LinearMap.comp_apply, this]
  simp only [l₀, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [show (LinearMap.quotKerEquivRange T).symm ⟨T v, LinearMap.mem_range_self T v⟩ =
      Submodule.Quotient.mk v from
    (LinearMap.quotKerEquivRange T).symm_apply_eq.2 rfl]
  rfl

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

variable (A) in
/-- A free presentation `Aⁿ¹ → Aⁿ⁰ → Z → 0`. -/
structure FreePres (Z : Type*) [AddCommGroup Z] [Module A Z] where
  n₀ : ℕ
  n₁ : ℕ
  z : Fin n₀ → Z
  F : Fin n₁ → Fin n₀ → A
  rel : ∀ i, ∑ j, F i j • z j = 0
  span : ∀ x : Z, ∃ p : Fin n₀ → A, ∑ j, p j • z j = x
  exact : ∀ p : Fin n₀ → A, ∑ j, p j • z j = 0 → ∃ r : Fin n₁ → A, ∀ j, p j = ∑ i, r i * F i j

section Lift

variable {Z : Type*} [AddCommGroup Z] [Module A Z]
variable {W : Type*} [AddCommGroup W] [Module A W]

/-- The relation map `Wⁿ⁰ → Wⁿ¹`, `w ↦ (Σⱼ Fᵢⱼ wⱼ)ᵢ`. -/
def relMap {n₀ n₁ : ℕ} (F : Fin n₁ → Fin n₀ → A) (w : Fin n₀ → W) : Fin n₁ → W :=
  fun i ↦ ∑ j, F i j • w j

/-- **Lifting**: a tuple killed by the relations comes from a map `Z → W`. -/
theorem FreePres.lift (P : FreePres A Z) (w : Fin P.n₀ → W) (hw : relMap P.F w = 0) :
    ∃ v : Z →ₗ[A] W, ∀ j, v (P.z j) = w j := by
  classical
  let g₀ : (Fin P.n₀ → A) →ₗ[A] Z :=
    { toFun p := ∑ j, p j • P.z j
      map_add' p q := by simp [add_smul, Finset.sum_add_distrib]
      map_smul' a p := by simp [mul_smul, Finset.smul_sum] }
  let h : (Fin P.n₀ → A) →ₗ[A] W :=
    { toFun p := ∑ j, p j • w j
      map_add' p q := by simp [add_smul, Finset.sum_add_distrib]
      map_smul' a p := by simp [mul_smul, Finset.smul_sum] }
  have hsurj : Function.Surjective g₀ := fun x ↦ P.span x
  have hker : LinearMap.ker g₀ ≤ LinearMap.ker h := by
    intro p hp
    obtain ⟨r, hr⟩ := P.exact p hp
    simp only [LinearMap.mem_ker, h, LinearMap.coe_mk, AddHom.coe_mk]
    simp_rw [hr, Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.smul_sum]
    have : ∀ i, ∑ j, P.F i j • w j = 0 := fun i ↦ congrFun hw i
    simp [this]
  let e := LinearMap.quotKerEquivOfSurjective g₀ hsurj
  refine ⟨(LinearMap.ker g₀).liftQ h hker ∘ₗ e.symm.toLinearMap, fun j ↦ ?_⟩
  have hz : g₀ (Pi.single j 1) = P.z j := by
    simp [g₀, Pi.single_apply]
  have : e.symm (P.z j) = Submodule.Quotient.mk (Pi.single j 1) := by
    rw [LinearEquiv.symm_apply_eq, ← hz]; rfl
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this,
    Submodule.liftQ_apply]
  simp [h, Pi.single_apply]

/-- Maps out of `Z` are determined by the generators. -/
lemma FreePres.hom_ext (P : FreePres A Z) {v v' : Z →ₗ[A] W} (h : ∀ j, v (P.z j) = v' (P.z j)) :
    v = v' := by
  ext x
  obtain ⟨p, rfl⟩ := P.span x
  simp [map_sum, h]

/-- The relations kill the images of the generators. -/
lemma FreePres.relMap_hom (P : FreePres A Z) (v : Z →ₗ[A] W) :
    relMap P.F (fun j ↦ v (P.z j)) = 0 := by
  funext i
  simp only [relMap, Pi.zero_apply]
  simp_rw [← map_smul]
  rw [← map_sum, P.rel i, map_zero]

end Lift

section Theta

variable {W : Type*} [AddCommGroup W] [Module A W] [Module k W] [IsScalarTower k A W]

/-- `θ : Hom_A(W, DAⁿ) → D(Wⁿ)`, `θ φ w = Σⱼ φ(wⱼ)ⱼ(1)`. -/
def theta {n : ℕ} (φ : W →ₗ[A] (Fin n → DA k A)) : Module.Dual k (Fin n → W) where
  toFun w := ∑ j, (φ (w j) j).ev 1
  map_add' w w' := by simp [Finset.sum_add_distrib]
  map_smul' c w := by
    simp only [Pi.smul_apply, LinearMap.map_smul_of_tower, DA.ev_smul, RingHom.id_apply,
      smul_eq_mul, Finset.mul_sum]

@[simp] lemma theta_apply {n : ℕ} (φ : W →ₗ[A] (Fin n → DA k A)) (w : Fin n → W) :
    theta φ w = ∑ j, (φ (w j) j).ev 1 := rfl

variable (A) in
/-- The inverse of `θ`. -/
def thetaInv {n : ℕ} (l : Module.Dual k (Fin n → W)) : W →ₗ[A] (Fin n → DA k A) where
  toFun x j := dualToHomDA (A := A) (l ∘ₗ LinearMap.single k (fun _ ↦ W) j) x
  map_add' x y := by funext j; simp
  map_smul' a x := by funext j; simp

lemma theta_thetaInv {n : ℕ} (l : Module.Dual k (Fin n → W)) : theta (thetaInv A l) = l := by
  ext j w
  simp [thetaInv, Finset.sum_apply, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi; simp [hi]
  · simp

lemma thetaInv_theta {n : ℕ} (φ : W →ₗ[A] (Fin n → DA k A)) : thetaInv A (theta φ) = φ := by
  ext x j b
  simp only [thetaInv, LinearMap.coe_mk, AddHom.coe_mk, dualToHomDA_ev, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.coe_single, theta_apply]
  rw [Finset.sum_eq_single j]
  · simp [map_smul, DA.ev_smulA]
  · intro i _ hi
    simp [Pi.single_apply, hi]
  · simp

lemma theta_injective {n : ℕ} : Function.Injective (theta (k := k) (A := A) (W := W) (n := n)) :=
  fun φ ψ h ↦ by rw [← thetaInv_theta φ, ← thetaInv_theta ψ, h]

end Theta

section Nu

variable {n₀ n₁ : ℕ} (F : Fin n₁ → Fin n₀ → A)

/-- **The Nakayama transform** `ν F : DAⁿ¹ → DAⁿ⁰`, `(ν λ)ⱼ(b) = Σᵢ λᵢ(Fᵢⱼ b)`. -/
def nu : (Fin n₁ → DA k A) →ₗ[A] (Fin n₀ → DA k A) where
  toFun l j := ∑ i, DA.mk ((show A →ₗ[k] k from l i) ∘ₗ LinearMap.mulLeft k (F i j))
  map_add' l m := by
    funext j; ext b
    simp only [Pi.add_apply, DA.ev_finset_sum, DA.ev_mk, DA.ev_add, LinearMap.coe_comp,
      Function.comp_apply, ← Finset.sum_add_distrib]
    rfl
  map_smul' a l := by
    funext j; ext b
    simp only [Pi.smul_apply, DA.ev_finset_sum, DA.ev_mk, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.mulLeft_apply, RingHom.id_apply, DA.ev_smulA]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    show (a • l i).ev (F i j * b) = (l i).ev (F i j * (b * a))
    rw [DA.ev_smulA, mul_assoc]

@[simp] lemma nu_ev (l : Fin n₁ → DA k A) (j : Fin n₀) (b : A) :
    (nu F l j).ev b = ∑ i, (l i).ev (F i j * b) := by
  simp [nu]; rfl

variable {W : Type*} [AddCommGroup W] [Module A W] [Module k W] [IsScalarTower k A W]

/-- **Naturality**: `θ (ν F ∘ ψ) = θ ψ ∘ F`. -/
lemma theta_nu_comp (ψ : W →ₗ[A] (Fin n₁ → DA k A)) (w : Fin n₀ → W) :
    theta (nu F ∘ₗ ψ) w = theta ψ (relMap F w) := by
  simp only [theta_apply, LinearMap.coe_comp, Function.comp_apply, nu_ev, mul_one, relMap,
    map_sum, Finset.sum_apply, DA.ev_finset_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smul, Pi.smul_apply, DA.ev_smulA, one_mul]

end Nu

section Exists

variable {Z : Type*} [AddCommGroup Z] [Module A Z] [Module k Z] [IsScalarTower k A Z]

variable (k A Z) in
/-- **Every finite-dimensional module has a free presentation.** -/
theorem FreePres.exists [FiniteDimensional k A] [FiniteDimensional k Z] :
    Nonempty (FreePres A Z) := by
  classical
  let b := Module.finBasis k Z
  let n₀ := Module.finrank k Z
  let g : (Fin n₀ → A) →ₗ[k] Z :=
    { toFun p := ∑ j, p j • b j
      map_add' p q := by simp [add_smul, Finset.sum_add_distrib]
      map_smul' c p := by simp [Finset.smul_sum, smul_assoc] }
  let K := LinearMap.ker g
  let bK := Module.finBasis k K
  refine ⟨FreePres.mk n₀ (Module.finrank k K) b (fun i ↦ (bK i : Fin n₀ → A))
    (fun i ↦ (bK i).2) (fun x ↦ ⟨fun j ↦ algebraMap k A (b.repr x j), ?_⟩)
    (fun p hp ↦ ⟨fun i ↦ algebraMap k A (bK.repr ⟨p, hp⟩ i), fun j ↦ ?_⟩)⟩
  · simp only [algebraMap_smul]
    exact b.sum_repr x
  · have := congrArg (fun q : K ↦ (q : Fin n₀ → A) j) (bK.sum_repr ⟨p, hp⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def]

end Exists

section Range

variable {Z : Type*} [AddCommGroup Z] [Module A Z]

/-- `relMap` over `A` itself, as a `k`-linear map. -/
def relMapK {n₀ n₁ : ℕ} (F : Fin n₁ → Fin n₀ → A) : (Fin n₀ → A) →ₗ[k] (Fin n₁ → A) where
  toFun := relMap F
  map_add' p q := by funext i; simp [relMap, mul_add, Finset.sum_add_distrib]
  map_smul' c p := by
    funext i
    simp [relMap, Finset.smul_sum, Algebra.mul_smul_comm]

/-- **The range of the Nakayama transform**: a tuple in `DAⁿ⁰` lies in the range of `ν F`
when it vanishes on the generator values of every map `Z → A`. -/
theorem FreePres.mem_range_nu (P : FreePres A Z) (l : Fin P.n₀ → DA k A)
    (h : ∀ α : Z →ₗ[A] A, ∑ j, (l j).ev (α (P.z j)) = 0) : l ∈ LinearMap.range (nu P.F) := by
  classical
  let Φ : Module.Dual k (Fin P.n₀ → A) :=
    { toFun β := ∑ j, (l j).ev (β j)
      map_add' β γ := by simp [DA.ev_addB, Finset.sum_add_distrib]
      map_smul' c β := by simp [DA.ev_smulB, Finset.mul_sum] }
  have hker : LinearMap.ker (relMapK (k := k) P.F) ≤ LinearMap.ker Φ := by
    intro β hβ
    obtain ⟨α, hα⟩ := P.lift (W := A) β hβ
    simp only [LinearMap.mem_ker, Φ, LinearMap.coe_mk, AddHom.coe_mk]
    simpa [hα] using h α
  obtain ⟨l', hl'⟩ := exists_comp_of_ker_le _ Φ hker
  refine ⟨fun i ↦ DA.mk (l' ∘ₗ LinearMap.single k (fun _ ↦ A) i), ?_⟩
  funext j; ext b
  rw [nu_ev]
  simp only [DA.ev_mk, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single]
  rw [← map_sum]
  have e : (∑ i, Pi.single i (P.F i j * b) : Fin P.n₁ → A) =
      relMapK (k := k) P.F (Pi.single j b) := by
    funext i
    simp [relMapK, relMap, Pi.single_apply, Finset.sum_apply]
  rw [e, ← LinearMap.comp_apply, hl']
  simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi; simp [hi, DA.ev_zeroB]
  · simp

end Range

end LargeIndecomposable.AR
