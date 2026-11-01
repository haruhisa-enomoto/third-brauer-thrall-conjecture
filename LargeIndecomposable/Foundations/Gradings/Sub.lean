module

public import LargeIndecomposable.Coverings.GradedModules.PushDownIndecomposable

/-!
# Graded submodules and graded decompositions

A graded submodule carries the restricted grading (`GrMod.sub`). Every
finite-dimensional graded module is a finite direct sum of nonzero graded-indecomposable
graded submodules (`GrMod.exists_grDecomp`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.Graded

open Module

variable {G : Type*} [Group G] [DecidableEq G] {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A] {Γ : GrAlg G k A}
variable {M : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]

/-- The grading of a graded submodule. -/
def GrMod.sub (μ : GrMod Γ M) {U : Submodule A M} (hU : IsGrSub μ U) : GrMod Γ U where
  proj g :=
    { toFun u := ⟨μ.proj g u, hU u u.2 g⟩
      map_add' u v := Subtype.ext (by simp)
      map_smul' c u := Subtype.ext (by simp) }
  supp := μ.supp
  orth g h hgh u := Subtype.ext (by simp [μ.orth g h hgh])
  out g hg u := Subtype.ext (by simp [μ.out g hg])
  sum_eq u := Subtype.ext (by simp [μ.sum_eq])
  smul_mem g h a u ha hu := Subtype.ext (by
    have hu' : μ.Mem h (u : M) := congrArg Subtype.val hu
    exact μ.smul_mem g h a u ha hu')

@[simp] lemma GrMod.sub_proj (μ : GrMod Γ M) {U : Submodule A M} (hU : IsGrSub μ U) (g : G)
    (u : U) : ((μ.sub hU).proj g u : M) = μ.proj g u := rfl

variable (μ : GrMod Γ M)

/-- The projection onto a graded complement is homogeneous of degree one. -/
lemma isHomog_projectionOnto {U V : Submodule A M} (hU : IsGrSub μ U) (hV : IsGrSub μ V)
    (hUV : IsCompl U V) : IsHomog μ (μ.sub hU) 1 (Submodule.projectionOnto U V hUV) := by
  intro g m hm
  rw [mul_one]
  apply Subtype.ext
  change μ.proj g (Submodule.projectionOnto U V hUV m : M) = _
  have hdec := Submodule.projection_add_projection_eq_self hUV m
  rw [Submodule.projection_apply, Submodule.projection_apply] at hdec
  set u := (Submodule.projectionOnto U V hUV m : M)
  set v := (Submodule.projectionOnto V U hUV.symm m : M)
  have hu : u ∈ U := (Submodule.projectionOnto U V hUV m).2
  have hv : v ∈ V := (Submodule.projectionOnto V U hUV.symm m).2
  -- `proj g u - u = v - proj g v` lies in `U ∩ V`
  have key : μ.proj g u - u ∈ U ⊓ V := by
    constructor
    · exact U.sub_mem (hU u hu g) hu
    · have : μ.proj g u - u = v - μ.proj g v := by
        have h1 : μ.proj g u + μ.proj g v = μ.proj g m := by rw [← map_add, hdec]
        rw [hm] at h1
        have h2 : u + v = m := hdec
        rw [← h2] at h1
        linear_combination (norm := abel_nf) h1
      rw [this]; exact V.sub_mem hv (hV v hv g)
  rw [hUV.inf_eq_bot, Submodule.mem_bot, sub_eq_zero] at key
  exact key

/-- **Shifted grading**: degree `g` of `μ.shift h` is degree `g h` of `μ`. -/
def GrMod.shift (μ : GrMod Γ M) (h : G) : GrMod Γ M where
  proj g := μ.proj (g * h)
  supp := μ.supp.image fun g ↦ g * h⁻¹
  orth g g' hgg' m := μ.orth _ _ (fun e ↦ hgg' (mul_right_cancel e)) m
  out g hg m := μ.out _ (fun hm ↦ hg (Finset.mem_image.2 ⟨_, hm, by group⟩)) m
  sum_eq m := by
    rw [Finset.sum_image (fun x _ y _ e ↦ mul_right_cancel e)]
    simp only [inv_mul_cancel_right]
    exact μ.sum_eq m
  smul_mem x y a m ha hm := by
    change μ.Mem (x * y * h) (a • m)
    rw [mul_assoc]
    exact μ.smul_mem x (y * h) a m ha hm

lemma GrMod.shift_mem (μ : GrMod Γ M) (h g : G) (m : M) :
    (μ.shift h).Mem g m ↔ μ.Mem (g * h) m := Iff.rfl

/-- Graded submodules do not depend on the shift. -/
lemma isGrSub_shift (μ : GrMod Γ M) (h : G) (U : Submodule A M) :
    IsGrSub (μ.shift h) U ↔ IsGrSub μ U := by
  constructor
  · intro hU m hm g
    have := hU m hm (g * h⁻¹)
    simpa [GrMod.shift, inv_mul_cancel_right] using this
  · intro hU m hm g
    exact hU m hm (g * h)

lemma IsGrIndec.shift {μ : GrMod Γ M} (hμ : IsGrIndec μ) (h : G) : IsGrIndec (μ.shift h) :=
  fun U V hU hV hUV ↦ hμ U V ((isGrSub_shift μ h U).1 hU) ((isGrSub_shift μ h V).1 hV) hUV

section Decomp

open AR

universe u

variable {k' A' : Type u} [Field k'] [Ring A'] [Algebra k' A'] {Γ' : GrAlg G k' A'}

/-- A graded decomposition of a graded object into nonzero graded-indecomposables. -/
structure GrDecomp (E : FDMod k' A') (μ : GrMod Γ' E) where
  ι : Type u
  [fin : Fintype ι]
  obj : ι → FDMod k' A'
  gr : ∀ i, GrMod Γ' (obj i)
  indec : ∀ i, IsGrIndec (gr i)
  nt : ∀ i, Nontrivial (obj i)
  inc : ∀ i, obj i →ₗ[A'] E
  proj : ∀ i, E →ₗ[A'] obj i
  inc_homog : ∀ i, IsHomog (gr i) μ 1 (inc i)
  proj_homog : ∀ i, IsHomog μ (gr i) 1 (proj i)
  sum_id : ∑ i, inc i ∘ₗ proj i = LinearMap.id

attribute [instance] GrDecomp.fin

/-- The inclusion of a graded submodule is homogeneous of degree one. -/
lemma isHomog_subtype {E : FDMod k' A'} (μ : GrMod Γ' E) {U : Submodule A' E}
    (hU : IsGrSub μ U) : IsHomog (μ.sub hU) μ 1 U.subtype := by
  intro g u hu
  rw [mul_one]
  exact congrArg Subtype.val hu

/-- Gluing graded decompositions of two graded complements. -/
def GrDecomp.ofCompl {E : FDMod k' A'} (μ : GrMod Γ' E) (U V : Submodule A' E)
    (hU : IsGrSub μ U) (hV : IsGrSub μ V) (hUV : IsCompl U V)
    (dU : GrDecomp (FDMod.ofSub U) (μ.sub hU)) (dV : GrDecomp (FDMod.ofSub V) (μ.sub hV)) :
    GrDecomp E μ where
  ι := dU.ι ⊕ dV.ι
  obj := Sum.elim dU.obj dV.obj
  gr i := match i with
    | .inl i => dU.gr i
    | .inr i => dV.gr i
  indec i := match i with
    | .inl i => dU.indec i
    | .inr i => dV.indec i
  nt i := match i with
    | .inl i => dU.nt i
    | .inr i => dV.nt i
  inc i := match i with
    | .inl i => U.subtype ∘ₗ dU.inc i
    | .inr i => V.subtype ∘ₗ dV.inc i
  proj i := match i with
    | .inl i => dU.proj i ∘ₗ Submodule.projectionOnto U V hUV
    | .inr i => dV.proj i ∘ₗ Submodule.projectionOnto V U hUV.symm
  inc_homog i := match i with
    | .inl i => by
        have := (dU.inc_homog i).comp (isHomog_subtype μ hU); rwa [mul_one] at this
    | .inr i => by
        have := (dV.inc_homog i).comp (isHomog_subtype μ hV); rwa [mul_one] at this
  proj_homog i := match i with
    | .inl i => by
        have := (isHomog_projectionOnto μ hU hV hUV).comp (dU.proj_homog i)
        rwa [mul_one] at this
    | .inr i => by
        have := (isHomog_projectionOnto μ hV hU hUV.symm).comp (dV.proj_homog i)
        rwa [mul_one] at this
  sum_id := by
    rw [Fintype.sum_sum_type]
    ext x
    have hU' := LinearMap.congr_fun dU.sum_id (Submodule.projectionOnto U V hUV x)
    have hV' := LinearMap.congr_fun dV.sum_id (Submodule.projectionOnto V U hUV.symm x)
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe,
      id_eq] at hU' hV'
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.id_coe, id_eq]
    change ∑ i, U.subtype (dU.inc i (dU.proj i (Submodule.projectionOnto U V hUV x))) +
      ∑ i, V.subtype (dV.inc i (dV.proj i (Submodule.projectionOnto V U hUV.symm x))) = x
    calc _ = U.subtype (∑ i, dU.inc i (dU.proj i (Submodule.projectionOnto U V hUV x))) +
          V.subtype (∑ i, dV.inc i (dV.proj i (Submodule.projectionOnto V U hUV.symm x))) := by
            simp only [map_sum]
      _ = x := by
        rw [hU', hV']
        exact Submodule.projection_add_projection_eq_self hUV x

/-- **Every graded object has a graded decomposition.** -/
theorem exists_grDecomp : ∀ (E : FDMod k' A') (μ : GrMod Γ' E), Nonempty (GrDecomp E μ) := by
  classical
  suffices H : ∀ n, ∀ (E : FDMod k' A') (μ : GrMod Γ' E), finrank k' E = n →
      Nonempty (GrDecomp E μ) from fun E μ ↦ H _ E μ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E μ hn
  by_cases htriv : Subsingleton E
  · refine ⟨GrDecomp.mk PEmpty.{u + 1} (fun i ↦ i.elim) (fun i ↦ i.elim) (fun i ↦ i.elim)
      (fun i ↦ i.elim) (fun i ↦ i.elim) (fun i ↦ i.elim) (fun i ↦ i.elim) (fun i ↦ i.elim) ?_⟩
    ext x; exact Subsingleton.elim _ _
  rw [not_subsingleton_iff_nontrivial] at htriv
  by_cases hind : IsGrIndec μ
  · exact ⟨GrDecomp.mk PUnit.{u + 1} (fun _ ↦ E) (fun _ ↦ μ) (fun _ ↦ hind) (fun _ ↦ htriv)
      (fun _ ↦ LinearMap.id) (fun _ ↦ LinearMap.id) (fun _ ↦ isHomog_id) (fun _ ↦ isHomog_id)
      (by simp)⟩
  simp only [IsGrIndec, not_forall] at hind
  obtain ⟨U, V, hU, hV, hUV, hne⟩ := hind
  push Not at hne
  have hlt : ∀ (W W' : Submodule A' E), IsCompl W W' → W' ≠ ⊥ →
      finrank k' (FDMod.ofSub W) < n := by
    intro W W' hc hW'
    rw [← hn]
    have h1 := Submodule.finrank_add_eq_of_isCompl (K := k') (U := W.restrictScalars k')
      (W := W'.restrictScalars k') (by
        constructor
        · rw [disjoint_iff, ← Submodule.restrictScalars_inf, hc.inf_eq_bot,
            Submodule.restrictScalars_bot]
        · rw [codisjoint_iff, ← Submodule.restrictScalars_sup, hc.sup_eq_top,
            Submodule.restrictScalars_top])
    have h2 : 0 < finrank k' (W'.restrictScalars k') := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW'
      exact ⟨⟨x, hx⟩, fun h ↦ hx0 (congrArg Subtype.val h)⟩
    change finrank k' (W.restrictScalars k') < _
    omega
  obtain ⟨dU⟩ := ih _ (hlt U V hUV hne.2) _ (μ.sub hU) rfl
  obtain ⟨dV⟩ := ih _ (hlt V U hUV.symm hne.1) _ (μ.sub hV) rfl
  exact ⟨GrDecomp.ofCompl μ U V hU hV hUV dU dV⟩

end Decomp

end LargeIndecomposable.Graded
