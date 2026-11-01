module

public import LargeIndecomposable.Foundations.Gradings.Pres
public import LargeIndecomposable.Modules.KrullSchmidt.Fitting

/-!
# Graded right almost split families

For a nonzero graded-indecomposable module `Z` (torsion-free grading group) that is not a
summand of a free module, the right almost split map of `AuslanderReiten/AlmostSplit/RightAlmostSplit.lean` built
from a graded presentation and a degree-one functional `θ` has a graded source
(`isGrSub_pullbackE`). Decomposing the source gives a right almost split family whose
sources carry graded-indecomposable gradings (`grRASFam`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.Graded

open Module AR

variable {G : Type*} [Group G] [DecidableEq G] {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A] {Γ : GrAlg G k A}
variable {Z : Type*} [AddCommGroup Z] [Module A Z] [Module k Z] [IsScalarTower k A Z]

/-- Products of homogeneous scalars and homogeneous vectors. -/
lemma GrMod.proj_smul_of_mem (μ : GrMod Γ Z) {g : G} {x : Z} (hx : μ.Mem g x) (h : G) (b : A) :
    μ.proj h (b • x) = Γ.proj (h * g⁻¹) b • x := by
  rw [μ.proj_smul']
  by_cases hs : h * g⁻¹ ∈ Γ.supp
  · rw [Finset.sum_eq_single (h * g⁻¹)]
    · rw [show (h * g⁻¹)⁻¹ * h = g by group, hx]
    · intro y _ hy
      rw [μ.proj_of_mem hx (fun e ↦ hy (by rw [← e]; group)), smul_zero]
    · intro h'; exact absurd hs h'
  · rw [Γ.out _ hs, zero_smul]
    refine Finset.sum_eq_zero fun y hy ↦ ?_
    rw [μ.proj_of_mem hx (fun e ↦ hs (by rw [← e]; simpa using hy)), smul_zero]

/-- The component of degree one on a homogeneous vector. -/
lemma comp_apply_of_mem {N : Type*} [AddCommGroup N] [Module A N] [Module k N]
    [IsScalarTower k A N] (μ : GrMod Γ Z) (ν : GrMod Γ N) {g : G} {m : Z} (hm : μ.Mem g m)
    (h : G) (f : Z →ₗ[A] N) : comp μ ν h f m = ν.proj (g * h) (f m) := by
  rw [comp_apply]
  by_cases hg : g ∈ μ.supp
  · rw [Finset.sum_eq_single g]
    · rw [hm]
    · intro g' _ hg'; rw [μ.proj_of_mem hm hg', map_zero, map_zero]
    · intro h'; exact absurd hg h'
  · have : m = 0 := by rw [← hm, μ.out g hg]
    subst this; simp

variable (μ : GrMod Γ Z) (P : GrPres μ)

/-- The grading of `DAⁿ¹` and `DAⁿ⁰` for a graded presentation. -/
abbrev grD₁ : GrMod Γ (Fin P.n₁ → DA k A) := GrMod.pi fun i ↦ grDA Γ (P.e i)
abbrev grD₀ : GrMod Γ (Fin P.n₀ → DA k A) := GrMod.pi fun j ↦ grDA Γ (P.d j)

/-- **The Nakayama transform is homogeneous of degree one.** -/
lemma isHomog_nu : IsHomog (grD₁ μ P) (grD₀ μ P) 1 (nu P.F) := by
  intro g l hl
  rw [mul_one]
  funext j
  have hl' : ∀ i, (grDA Γ (P.e i)).Mem g (l i) := fun i ↦ congrFun hl i
  refine (grDA_mem _ _ _).2 fun b ↦ ?_
  show (nu P.F l j).ev (Γ.proj (P.d j * g⁻¹) b) = (nu P.F l j).ev b
  rw [nu_ev, nu_ev]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h1 := (grDA_mem _ _ _).1 (hl' i) (P.F i j * b)
  rw [← h1, show P.e i * g⁻¹ = (P.e i * (P.d j)⁻¹) * (P.d j * g⁻¹) by group,
    GrAlg.proj_mul_left (P.hF i j)]

variable {μ P}

/-- **For a degree-one `θ`, `θ⁻¹(θ)` is homogeneous of degree one.** -/
lemma isHomog_thetaInv {θ : Module.Dual k (Fin P.n₀ → Z)}
    (hθ : ∀ w, θ w = θ (fun j ↦ μ.proj (P.d j) (w j))) :
    IsHomog μ (grD₀ μ P) 1 (thetaInv A θ) := by
  classical
  intro g x hx
  rw [mul_one]
  funext j
  refine (grDA_mem _ _ _).2 fun b ↦ ?_
  have key : ∀ b', (thetaInv A θ x j).ev b' =
      θ (Pi.single j (Γ.proj (P.d j * g⁻¹) b' • x)) := by
    intro b'
    simp only [thetaInv, LinearMap.coe_mk, AddHom.coe_mk, dualToHomDA_ev, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.coe_single]
    rw [hθ]
    congr 1
    funext j'
    by_cases hj : j' = j
    · subst hj; simp [μ.proj_smul_of_mem hx]
    · simp [Pi.single_apply, hj]
  show (thetaInv A θ x j).ev (Γ.proj (P.d j * g⁻¹) b) = (thetaInv A θ x j).ev b
  rw [key, key, Γ.proj_proj]

/-- `pullbackE` is graded for a degree-one `θ`. -/
lemma isGrSub_pullbackE {θ : Module.Dual k (Fin P.n₀ → Z)}
    (hθ : ∀ w, θ w = θ (fun j ↦ μ.proj (P.d j) (w j))) :
    IsGrSub (μ.prod (grD₁ μ P)) (pullbackE P.toFreePres θ) := by
  refine isGrSub_ker' (ν := grD₀ μ P) (h := 1) ?_
  intro g x hx
  have h1 : μ.Mem g x.1 := congrArg Prod.fst hx
  have h2 : (grD₁ μ P).Mem g x.2 := congrArg Prod.snd hx
  have a1 := isHomog_thetaInv hθ g x.1 h1
  have a2 := isHomog_nu μ P g x.2 h2
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply]
  show (grD₀ μ P).proj (g * 1) _ = _
  rw [map_sub, a1, a2]

section Main

universe u

variable {k' A' : Type u} [Field k'] [Ring A'] [Algebra k' A'] {Γ' : GrAlg G k' A'}

/-- **Graded right almost split families.** -/
theorem grRASFam [FiniteDimensional k' A'] (htf : TorsionFree G) (Z : FDMod k' A')
    (μ : GrMod Γ' Z) (hind : IsGrIndec μ) [Nontrivial Z] (hnp : ¬IsFreeSummand A' Z) :
    Nonempty (RASFam (fun X : FDMod k' A' ↦ ∃ γ : GrMod Γ' X, IsGrIndec γ ∧ Nontrivial X) Z) := by
  classical
  haveI : IsLocalRing (Module.End A' Z) := (isIndecMod htf hind).isLocalRing (k := k')
  obtain ⟨P⟩ := GrPres.exists μ
  obtain ⟨η, hη1, hη0⟩ := exists_eta (k := k') (A := A') (Z := Z)
  obtain ⟨θ₀, hθ₀⟩ := exists_theta_of_eta P.toFreePres η
  let D : (Fin P.n₀ → Z) →ₗ[k'] (Fin P.n₀ → Z) :=
    LinearMap.pi fun j ↦ μ.proj (P.d j) ∘ₗ LinearMap.proj j
  let θ := θ₀ ∘ₗ D
  have hθ : ∀ w, θ w = θ (fun j ↦ μ.proj (P.d j) (w j)) := by
    intro w
    simp only [θ, D, LinearMap.coe_comp, Function.comp_apply]
    congr 1; funext j; simp [Grading.proj_proj]
  have hθe : ∀ e : Module.End A' Z, θ (fun j ↦ e (P.z j)) = η (comp μ μ 1 e) := by
    intro e
    rw [← hθ₀]
    simp only [θ, D, LinearMap.coe_comp, Function.comp_apply]
    congr 1; funext j
    simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
      Function.eval]
    rw [comp_apply_of_mem μ μ (P.hz j), mul_one]
  have hθ1 : θ (fun j ↦ P.z j) ≠ 0 := by
    have := hθe 1
    rw [Module.End.one_eq_id, comp_of_isHomog μ μ isHomog_id, if_pos rfl,
      ← Module.End.one_eq_id] at this
    rw [show (fun j ↦ P.z j) = fun j ↦ (LinearMap.id : Module.End A' Z) (P.z j) from rfl,
      ← Module.End.one_eq_id, this]
    exact hη1
  have hθ0 : ∀ e : Module.End A' Z, ¬IsUnit e → θ (fun j ↦ e (P.z j)) = 0 := by
    intro e he
    rw [hθe]
    refine hη0 _ fun hu ↦ he ?_
    rw [Module.End.isUnit_iff] at hu ⊢
    exact bijective_of_comp_one htf hind e hu
  have hras := rightAlmostSplit_of_theta hnp P.toFreePres θ hθ1 hθ0
  set E := pullbackE P.toFreePres θ with hEdef
  have hE := isGrSub_pullbackE (P := P) hθ
  let Eobj := FDMod.ofSubProd Z (Fin P.n₁ → DA k' A') E
  let γE : GrMod Γ' Eobj := (μ.prod (grD₁ μ P)).sub hE
  obtain ⟨d⟩ := exists_grDecomp Eobj γE
  let gE : E →ₗ[A'] Z := LinearMap.fst A' Z _ ∘ₗ E.subtype
  refine ⟨RASFam.mk d.ι d.obj (fun i ↦ ⟨d.gr i, d.indec i, d.nt i⟩)
    (fun i ↦ show d.obj i →ₗ[A'] Z from gE ∘ₗ d.inc i) ?_ ?_⟩
  · rintro ⟨h, hh⟩
    apply hras.1
    refine ⟨∑ i, d.inc i ∘ₗ FDMod.lin (h i), ?_⟩
    rw [← hh]
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply, map_sum]
    rfl
  · intro W v hv
    obtain ⟨t, ht⟩ := hras.2 W (FDMod.lin v) fun ⟨s, hs⟩ ↦ hv ⟨s, hs⟩
    refine ⟨fun i ↦ show W →ₗ[A'] d.obj i from d.proj i ∘ₗ t, ?_⟩
    rw [← ht]
    ext x
    have := LinearMap.congr_fun d.sum_id (t x)
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe,
      id_eq] at this
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply]
    change _ = ∑ i, gE (d.inc i (d.proj i (t x)))
    rw [← map_sum gE, this]
    rfl

end Main

end LargeIndecomposable.Graded
