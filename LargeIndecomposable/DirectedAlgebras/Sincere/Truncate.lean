module

public import LargeIndecomposable.DirectedAlgebras.Sincere.SincereRoots

/-!
# Truncation of a module to a convex set

For a directed algebra, a module `U` and a convex set `T` of points, the part of `U` on `T` is a
subquotient of `U` (`trunc`). A summand of the truncation which vanishes on the boundary of `T`
splits off `U` (`exists_boundary`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

namespace DirData

variable (D : DirData k A)

/-- A convex set of points. -/
def IsConvexSet (T : Set D.ι) : Prop :=
  ∀ x z c, x ∈ T → z ∈ T → Relation.ReflTransGen D.Arr x c → Relation.ReflTransGen D.Arr c z →
    c ∈ T

/-- The up-closure of a set. -/
def upC (T : Set D.ι) : Set D.ι := {c | ∃ x ∈ T, Relation.ReflTransGen D.Arr x c}

variable {D}

lemma upC_closed {T : Set D.ι} {x c : D.ι} (hx : x ∈ D.upC T)
    (h : Relation.ReflTransGen D.Arr x c) : c ∈ D.upC T := by
  obtain ⟨y, hy, hyx⟩ := hx
  exact ⟨y, hy, hyx.trans h⟩

lemma upD_closed {T : Set D.ι} (hT : D.IsConvexSet T) {x c : D.ι} (hx : x ∈ D.upC T \ T)
    (h : Relation.ReflTransGen D.Arr x c) : c ∈ D.upC T \ T := by
  refine ⟨upC_closed hx.1 h, fun hc ↦ hx.2 ?_⟩
  obtain ⟨y, hy, hyx⟩ := hx.1
  exact hT y c x hy hc hyx h

variable (U : FDMod k A)

/-- The submodule of `U` supported in an up-closed set. -/
def upSub (F : Set D.ι) (hF : ∀ x c, x ∈ F → Relation.ReflTransGen D.Arr x c → c ∈ F) :
    Submodule A U where
  carrier := {m | ∀ c, c ∉ F → D.e c • m = 0}
  add_mem' hm hn c hc := by rw [smul_add, hm c hc, hn c hc, add_zero]
  zero_mem' _ _ := smul_zero _
  smul_mem' a m hm c hc := by
    classical
    change D.e c • (a • m) = 0
    have h1 : m = ∑ x, D.e x • m := by rw [← Finset.sum_smul, D.sum, one_smul]
    rw [h1, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    by_cases hx : x ∈ F
    · have h2 : D.e c * a * D.e x = 0 := by
        by_contra h0
        exact hc (hF x c hx (D.hom x c a h0))
      have h3 : D.e c • (a • (D.e x • m)) = (D.e c * a * D.e x) • m := by
        rw [mul_smul, mul_smul]
      rw [h3, h2, zero_smul]
    · rw [hm x hx, smul_zero, smul_zero]

/-- The idempotent of a set of points. -/
def eT (D : DirData k A) (T : Set D.ι) : A := by
  classical
  exact ∑ x ∈ Finset.univ.filter (· ∈ T), D.e x

lemma e_mul_eT_of_mem {T : Set D.ι} {x : D.ι} (hx : x ∈ T) : D.e x * D.eT T = D.e x := by
  classical
  unfold eT
  rw [Finset.mul_sum, Finset.sum_eq_single x]
  · exact (D.idem x).eq
  · intro y _ hy
    exact D.orth x y (Ne.symm hy)
  · intro h
    exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩) h

lemma e_mul_eT_of_not_mem {T : Set D.ι} {x : D.ι} (hx : x ∉ T) : D.e x * D.eT T = 0 := by
  classical
  unfold eT
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun y hy ↦ D.orth x y fun h ↦ hx ?_
  rw [h]
  exact (Finset.mem_filter.1 hy).2

lemma smul_eq_sum_e {M : Type*} [AddCommGroup M] [Module A M] (m : M) :
    m = ∑ x, D.e x • m := by
  rw [← Finset.sum_smul, D.sum, one_smul]

/-- Elements vanishing at every point are zero. -/
lemma eq_zero_of_e {M : Type*} [AddCommGroup M] [Module A M] {m : M} (h : ∀ x, D.e x • m = 0) :
    m = 0 := by
  rw [smul_eq_sum_e (D := D) m]
  exact Finset.sum_eq_zero fun x _ ↦ h x

/-- Equality at every point. -/
lemma ext_e {M : Type*} [AddCommGroup M] [Module A M] {m n : M}
    (h : ∀ x, D.e x • m = D.e x • n) : m = n := by
  rw [smul_eq_sum_e (D := D) m, smul_eq_sum_e (D := D) n]
  exact Finset.sum_congr rfl fun x _ ↦ h x

lemma e_smul_eT_smul {M : Type*} [AddCommGroup M] [Module A M] {T : Set D.ι} {x : D.ι} (hx : x ∈ T)
    (m : M) : D.e x • (D.eT T • m) = D.e x • m := by
  rw [← mul_smul, e_mul_eT_of_mem hx]

lemma e_smul_eT_smul' {M : Type*} [AddCommGroup M] [Module A M] {T : Set D.ι} {x : D.ι}
    (hx : x ∉ T) (m : M) : D.e x • (D.eT T • m) = 0 := by
  rw [← mul_smul, e_mul_eT_of_not_mem hx, zero_smul]

section Trunc

variable {T : Set D.ι} (hT : D.IsConvexSet T)

/-- The submodule on the up-closure. -/
abbrev U₁ (T : Set D.ι) : FDMod k A :=
  FDMod.ofSub (upSub (D := D) U (D.upC T) fun _ _ hx h ↦ upC_closed hx h)

/-- The kernel of the truncation. -/
def truncK : Submodule A (U₁ (D := D) U T) :=
  (upSub (D := D) U (D.upC T \ T) fun _ _ hx h ↦ upD_closed hT hx h).comap
    (Submodule.subtype _)

/-- **The truncation of `U` to a convex set.** -/
abbrev trunc : FDMod k A := FDMod.ofQuot (U₁ (D := D) U T) (truncK U hT)

/-- The element of the up-closure part. -/
def toU₁ : U →ₗ[k] U₁ (D := D) U T where
  toFun m := ⟨D.eT T • m, fun c hc ↦ by
    have h : c ∉ T := fun h ↦ hc ⟨c, h, Relation.ReflTransGen.refl⟩
    exact e_smul_eT_smul' h m⟩
  map_add' m n := Subtype.ext (smul_add _ _ _)
  map_smul' c m := Subtype.ext (smul_algebra_smul_comm c (D.eT T) m)

/-- The projection of `U` to the truncation. -/
def rho : U →ₗ[k] trunc U hT :=
  ((truncK U hT).mkQ.restrictScalars k) ∘ₗ toU₁ U

/-- Multiplication by an element as a `k`-linear map. -/
def smulL (a : A) : U →ₗ[k] U where
  toFun m := a • m
  map_add' := smul_add a
  map_smul' c m := by
    rw [RingHom.id_apply]
    exact smul_algebra_smul_comm c a m

/-- The section of the projection. -/
def sigma : trunc U hT →ₗ[k] U :=
  ((truncK U hT).restrictScalars k).liftQ (smulL U (D.eT T) ∘ₗ
      ((Submodule.subtype _).restrictScalars k)) (by
      intro m hm
      refine LinearMap.mem_ker.2 (eq_zero_of_e (D := D) fun x ↦ ?_)
      change D.e x • (D.eT T • (m : U)) = 0
      by_cases hx : x ∈ T
      · rw [e_smul_eT_smul hx]
        exact hm x fun h ↦ h.2 hx
      · exact e_smul_eT_smul' hx _) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv k (truncK U hT)).symm.toLinearMap

variable {U}

variable {hT} in
lemma sigma_mk (m : U₁ (D := D) U T) :
    sigma U hT ((truncK U hT).mkQ m) = D.eT T • (m : U) := rfl

variable {hT} in
lemma rho_apply (m : U) : rho U hT m = (truncK U hT).mkQ (toU₁ U m) := rfl

lemma coe_toU₁ (m : U) : ((toU₁ (T := T) U m : U₁ (D := D) U T) : U) = D.eT T • m := rfl

lemma eT_idem : D.eT T * D.eT T = D.eT T := by
  classical
  refine ext_e (D := D) fun x ↦ ?_
  simp only [smul_eq_mul]
  by_cases hx : x ∈ T
  · rw [← mul_assoc, e_mul_eT_of_mem hx, e_mul_eT_of_mem hx]
  · rw [← mul_assoc, e_mul_eT_of_not_mem hx, zero_mul]

variable {hT} in
lemma e_smul_sigma_of_not_mem {c : D.ι} (hc : c ∉ T) (n : trunc U hT) :
    D.e c • sigma U hT n = 0 := by
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ n
  rw [sigma_mk]
  exact e_smul_eT_smul' hc _

variable {hT} in
lemma eT_smul_sigma (n : trunc U hT) : D.eT T • sigma U hT n = sigma U hT n := by
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ n
  rw [sigma_mk, ← mul_smul, eT_idem]

variable {hT} in
lemma sigma_rho (m : U) : sigma U hT (rho U hT m) = D.eT T • m := by
  rw [rho_apply, sigma_mk, coe_toU₁, ← mul_smul, eT_idem]

variable {hT} in
lemma rho_sigma (n : trunc U hT) : rho U hT (sigma U hT n) = n := by
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ n
  rw [sigma_mk, rho_apply]
  refine (Submodule.Quotient.eq (truncK U hT)).2 ?_
  intro c hc
  change D.e c • (D.eT T • (D.eT T • (m : U)) - (m : U)) = 0
  rw [← mul_smul (D.eT T), eT_idem, smul_sub]
  by_cases hcT : c ∈ T
  · rw [e_smul_eT_smul hcT, sub_self]
  · have h : c ∉ D.upC T := fun h ↦ hc ⟨h, hcT⟩
    rw [e_smul_eT_smul' hcT, m.2 c h, sub_self]

/-- Morphisms from outside the up-closure part into `T` vanish. -/
lemma e_mul_e_of_upD (hc : D.IsConvexSet T) {x y : D.ι} (hx : x ∈ D.upC T \ T) (hy : y ∈ T)
    (a : A) : D.e y * a * D.e x = 0 := by
  by_contra h0
  exact (upD_closed hc hx (D.hom x y a h0)).2 hy

lemma e_smul_sigma_smul {y : D.ι} (hy : y ∈ T) (a : A) (n : trunc U hT) :
    D.e y • sigma U hT (a • n) = D.e y • (a • sigma U hT n) := by
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ n
  have h0 : a • (truncK U hT).mkQ m = (truncK U hT).mkQ (a • m) := (map_smul _ a m).symm
  rw [h0, sigma_mk, sigma_mk, e_smul_eT_smul hy]
  change D.e y • (a • (m : U)) = D.e y • (a • (D.eT T • (m : U)))
  -- the difference lives outside `T`
  have key : ∀ x, D.e y • (a • (D.e x • (m : U))) =
      D.e y • (a • (D.e x • (D.eT T • (m : U)))) := by
    intro x
    by_cases hx : x ∈ T
    · rw [e_smul_eT_smul hx]
    · rw [e_smul_eT_smul' hx, smul_zero, smul_zero]
      by_cases hu : x ∈ D.upC T
      · have h1 := e_mul_e_of_upD hT ⟨hu, hx⟩ hy a
        rw [← mul_smul, ← mul_smul, h1, zero_smul]
      · rw [m.2 x hu, smul_zero, smul_zero]
  calc D.e y • (a • (m : U)) = ∑ x, D.e y • (a • (D.e x • (m : U))) := by
        conv_lhs => rw [smul_eq_sum_e (D := D) (m : U)]
        rw [Finset.smul_sum, Finset.smul_sum]
    _ = ∑ x, D.e y • (a • (D.e x • (D.eT T • (m : U)))) := Finset.sum_congr rfl fun x _ ↦ key x
    _ = D.e y • (a • (D.eT T • (m : U))) := by
        conv_rhs => rw [smul_eq_sum_e (D := D) (D.eT T • (m : U))]
        rw [Finset.smul_sum, Finset.smul_sum]

lemma sigma_e_smul (x : D.ι) (n : trunc U hT) :
    sigma U hT (D.e x • n) = D.e x • sigma U hT n := by
  by_cases hx : x ∈ T
  · apply ext_e (D := D)
    intro c
    by_cases hc : c ∈ T
    · rw [e_smul_sigma_smul hT hc]
    · rw [e_smul_sigma_of_not_mem hc, ← mul_smul]
      by_cases hcx : c = x
      · exact absurd (hcx ▸ hx) hc
      · rw [D.orth c x hcx, zero_smul]
  · rw [e_smul_sigma_of_not_mem hx]
    have : D.e x • n = 0 := by
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ n
      have h0 : D.e x • (truncK U hT).mkQ m = (truncK U hT).mkQ (D.e x • m) := (map_smul _ _ m).symm
      rw [h0]
      refine (Submodule.Quotient.mk_eq_zero (truncK U hT)).2 ?_
      intro c hc
      change D.e c • (D.e x • (m : U)) = 0
      by_cases hcx : c = x
      · subst hcx
        by_cases hu : c ∈ D.upC T
        · exact absurd ⟨hu, hx⟩ hc
        · rw [m.2 c hu, smul_zero]
      · rw [← mul_smul, D.orth c x hcx, zero_smul]
    rw [this, map_zero]

/-- Elements of `T`-support are compatible with the truncation. -/
lemma rho_smul {m : U} (hm : ∀ c, c ∉ T → D.e c • m = 0) (a : A) :
    rho U hT (a • m) = a • rho U hT m := by
  have hem : D.eT T • m = m := by
    apply ext_e (D := D)
    intro c
    by_cases hc : c ∈ T
    · rw [e_smul_eT_smul hc]
    · rw [e_smul_eT_smul' hc, hm c hc]
  have hmU : m ∈ upSub (D := D) U (D.upC T) (fun _ _ hx h ↦ upC_closed hx h) := fun c hc ↦
    hm c fun h ↦ hc ⟨c, h, Relation.ReflTransGen.refl⟩
  have h0 : a • (truncK U hT).mkQ (toU₁ U m) = (truncK U hT).mkQ (a • toU₁ U m) :=
    (map_smul _ a _).symm
  rw [rho_apply, rho_apply, h0]
  refine (Submodule.Quotient.eq (truncK U hT)).2 ?_
  intro c hc
  change D.e c • (D.eT T • (a • m) - a • (D.eT T • m)) = 0
  rw [hem, smul_sub]
  by_cases hcT : c ∈ T
  · rw [e_smul_eT_smul hcT, sub_self]
  · have h : c ∉ D.upC T := fun h ↦ hc ⟨h, hcT⟩
    have h1 := Submodule.smul_mem _ a hmU
    rw [e_smul_eT_smul' hcT, h1 c h, sub_self]

lemma e_smul_rho {x : D.ι} (m : U) : D.e x • rho U hT m = rho U hT (D.e x • m) := by
  have hs : rho U hT m = rho U hT (D.eT T • m) := by
    rw [← sigma_rho, rho_sigma]
  have hsup : ∀ c, c ∉ T → D.e c • (D.eT T • m) = 0 := fun c hc ↦ e_smul_eT_smul' hc m
  rw [hs, ← rho_smul hT hsup]
  have hr : ∀ w, rho U hT w = rho U hT (D.eT T • w) := fun w ↦ by
    rw [← sigma_rho, rho_sigma]
  rw [hr (D.e x • (D.eT T • m)), hr (D.e x • m)]
  congr 1
  apply ext_e (D := D)
  intro c
  by_cases hc : c ∈ T
  · rw [e_smul_eT_smul hc, e_smul_eT_smul hc]
    by_cases hcx : c = x
    · subst hcx
      have h2 : ∀ w : U, D.e c • (D.e c • w) = D.e c • w := fun w ↦ by
        rw [← mul_smul, (D.idem c).eq]
      rw [h2, h2, e_smul_eT_smul hc]
    · have h3 : ∀ w : U, D.e c • (D.e x • w) = 0 := fun w ↦ by
        rw [← mul_smul, D.orth c x hcx, zero_smul]
      rw [h3, h3]
  · rw [e_smul_eT_smul' hc, e_smul_eT_smul' hc]

/-- The truncation vanishes off `T`. -/
lemma e_smul_trunc_of_not_mem {c : D.ι} (hc : c ∉ T) (n : trunc U hT) : D.e c • n = 0 := by
  have h1 : n = rho U hT (sigma U hT n) := (rho_sigma n).symm
  rw [h1, e_smul_rho, e_smul_sigma_of_not_mem hc, map_zero]

/-- Multiplication by a corner of `T` is compatible with the section. -/
lemma sigma_corner {x y : D.ι} (hy : y ∈ T) (a : A) (n : trunc U hT) :
    sigma U hT ((D.e y * a * D.e x) • n) = (D.e y * a * D.e x) • sigma U hT n := by
  have e1 : (D.e y * a * D.e x) • n = D.e y • (a • (D.e x • n)) := by rw [mul_smul, mul_smul]
  rw [e1, sigma_e_smul, e_smul_sigma_smul hT hy, sigma_e_smul, mul_smul, mul_smul]

/-- First-step induction for morphisms. -/
lemma first_step (P : A → Prop) (h0 : P 0) (hadd : ∀ u v, P u → P v → P (u + v)) {x : D.ι}
    (hgen : ∀ c b r, D.Arr x c → P (r * (D.e c * b * D.e x))) (a : A) :
    P ((1 - D.e x) * a * D.e x) := by
  have key : ∀ z ∈ Submodule.span A {r | ∃ y b, D.Arr x y ∧ r = D.e y * b * D.e x},
      ∀ r, P (r * z) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, b, hy, rfl⟩ := hz
      exact fun r ↦ hgen y b r hy
    | zero => exact fun r ↦ by rw [mul_zero]; exact h0
    | add u v _ _ hu hv => exact fun r ↦ by rw [mul_add]; exact hadd _ _ (hu r) (hv r)
    | smul s z _ hz => exact fun r ↦ by rw [smul_eq_mul, ← mul_assoc]; exact hz _
  have := key _ (D.gen x a) 1
  rwa [one_mul] at this

/-- `e_y a e_x` for `y ≠ x` by first steps. -/
lemma corner_first_step (P : A → Prop) (h0 : P 0) (hadd : ∀ u v, P u → P v → P (u + v)) {x y : D.ι}
    (hxy : y ≠ x) (hgen : ∀ c b r, D.Arr x c → P (D.e y * r * (D.e c * b * D.e x))) (a : A) :
    P (D.e y * a * D.e x) := by
  have h1 : D.e y * ((1 - D.e x) * a * D.e x) = D.e y * a * D.e x := by
    rw [← mul_assoc, ← mul_assoc, mul_sub, mul_one, D.orth y x hxy, sub_zero]
  rw [← h1]
  exact first_step (fun z ↦ P (D.e y * z)) (by rw [mul_zero]; exact h0)
    (fun u v hu hv ↦ by rw [mul_add]; exact hadd _ _ hu hv)
    (fun c b r hc ↦ by rw [← mul_assoc]; exact hgen c b r hc) a


/-- The boundary of a set of points. -/
def bdry (D : DirData k A) (T : Set D.ι) : Set D.ι :=
  {b | b ∈ T ∧ ∃ c, c ∉ T ∧ (D.Arr b c ∨ D.Arr c b)}

/-- Well-foundedness of the order of a directed algebra, forwards. -/
lemma wf_flip (D : DirData k A) : WellFounded (flip (Relation.TransGen D.Arr)) := by
  haveI : IsTrans D.ι (flip (Relation.TransGen D.Arr)) :=
    ⟨fun _ _ _ h1 h2 ↦ Relation.TransGen.trans h2 h1⟩
  haveI : Std.Irrefl (flip (Relation.TransGen D.Arr)) :=
    ⟨fun x h ↦ D.acyc x x h Relation.ReflTransGen.refl⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

section Boundary

variable (π : trunc U hT →ₗ[A] trunc U hT)
  (hπ : ∀ b ∈ D.bdry T, ∀ n, D.e b • π n = 0)
include hπ

/-- Morphisms from outside into `T` die in the image of `π`. -/
lemma pi_rho_in {y : D.ι} (hy : y ∈ T) : ∀ x, x ∉ T → ∀ (a : A) (m : U),
    π (rho U hT ((D.e y * a * D.e x) • m)) = 0 := by
  intro x
  induction x using D.wf_flip.induction with
  | _ x ih =>
    intro hx a m
    have hxy : y ≠ x := fun h ↦ hx (h ▸ hy)
    refine corner_first_step (fun z ↦ π (rho U hT (z • m)) = 0) (by simp)
      (fun u v hu hv ↦ by rw [add_smul, map_add, map_add, hu, hv, add_zero]) hxy
      (fun c b r hc ↦ ?_) a
    by_cases hcT : c ∈ T
    · -- `c` is on the boundary
      have hb : c ∈ D.bdry T := ⟨hcT, x, hx, Or.inr hc⟩
      set v := (D.e c * b * D.e x) • m
      have hv : D.e c • v = v := by
        change D.e c • ((D.e c * b * D.e x) • m) = _
        rw [← mul_smul, ← mul_assoc, ← mul_assoc, (D.idem c).eq]
      have hvs : ∀ c', c' ∉ T → D.e c' • v = 0 := fun c' hc' ↦ by
        rw [← hv, ← mul_smul, D.orth c' c fun h ↦ hc' (h ▸ hcT), zero_smul]
      have h1 : (D.e y * r * (D.e c * b * D.e x)) • m = (D.e y * r) • v := by rw [mul_smul]
      rw [h1, rho_smul hT hvs, map_smul]
      have h2 : π (rho U hT v) = D.e c • π (rho U hT v) := by
        rw [← map_smul, e_smul_rho, hv]
      rw [h2, hπ c hb, smul_zero]
    · have h1 : (D.e y * r * (D.e c * b * D.e x)) • m =
          (D.e y * r * D.e c) • (b • (D.e x • m)) := by
        rw [← mul_smul, ← mul_smul]
        congr 1
        simp only [mul_assoc]
      rw [h1]
      exact ih c (Relation.TransGen.single hc) hcT r _

/-- Morphisms out of `T` die on the image of `π`. -/
lemma sigma_out {y : D.ι} (hy : y ∉ T) : ∀ x, x ∈ T → ∀ (a : A) (n : trunc U hT),
    (D.e y * a * D.e x) • sigma U hT (π n) = 0 := by
  intro x
  induction x using D.wf_flip.induction with
  | _ x ih =>
    intro hx a n
    by_cases hb : x ∈ D.bdry T
    · rw [mul_smul, ← sigma_e_smul, hπ x hb, map_zero, smul_zero]
    · have hin : ∀ c, D.Arr x c → c ∈ T := fun c hc ↦ by
        by_contra h
        exact hb ⟨hx, c, h, Or.inl hc⟩
      have hxy : y ≠ x := fun h ↦ hy (h ▸ hx)
      refine corner_first_step (fun z ↦ z • sigma U hT (π n) = 0) (by simp)
        (fun u v hu hv ↦ by rw [add_smul, hu, hv, add_zero]) hxy (fun c b r hc ↦ ?_) a
      have h1 : (D.e y * r * (D.e c * b * D.e x)) • sigma U hT (π n) =
          (D.e y * r * D.e c) • ((D.e c * b * D.e x) • sigma U hT (π n)) := by
        rw [← mul_smul]
        congr 1
        have : D.e c * (D.e c * b * D.e x) = D.e c * b * D.e x := by
          rw [← mul_assoc, ← mul_assoc, (D.idem c).eq]
        rw [mul_assoc (D.e y * r), this]
      have h2 := sigma_corner (x := x) hT (hin c hc) b (π n)
      have h3 : (D.e c * b * D.e x) • π n = π ((D.e c * b * D.e x) • n) := (map_smul π _ n).symm
      rw [h1, ← h2, h3]
      exact ih c (Relation.TransGen.single hc) (hin c hc) r _

/-- The corner compatibility of the composite. -/
lemma eps_corner (x y : D.ι) (a : A) (m : U) :
    sigma U hT (π (rho U hT ((D.e y * a * D.e x) • m))) =
      (D.e y * a * D.e x) • sigma U hT (π (rho U hT m)) := by
  have hexs : ∀ n, x ∉ T → (D.e y * a * D.e x) • sigma U hT n = 0 := fun n hx ↦ by
    rw [mul_smul, e_smul_sigma_of_not_mem hx, smul_zero]
  by_cases hy : y ∈ T
  · by_cases hx : x ∈ T
    · have hsup : ∀ c, c ∉ T → D.e c • (D.e x • m) = 0 := fun c hc ↦ by
        rw [← mul_smul, D.orth c x fun h ↦ hc (h ▸ hx), zero_smul]
      have h1 : rho U hT ((D.e y * a * D.e x) • m) = (D.e y * a * D.e x) • rho U hT m := by
        rw [mul_smul (D.e y * a) (D.e x) m, rho_smul hT hsup, ← e_smul_rho,
          mul_smul (D.e y * a) (D.e x) (rho U hT m)]
      rw [h1, map_smul, sigma_corner hT hy]
    · rw [hexs _ hx, pi_rho_in hT π hπ hy x hx a m, map_zero]
  · have h0 : rho U hT ((D.e y * a * D.e x) • m) = 0 := by
      have h1 : (D.e y * a * D.e x) • m = D.e y • ((a * D.e x) • m) := by
        rw [← mul_smul, mul_assoc]
      rw [h1, ← e_smul_rho, e_smul_trunc_of_not_mem hT hy]
    rw [h0, map_zero, map_zero]
    by_cases hx : x ∈ T
    · exact (sigma_out hT π hπ hy x hx a _).symm
    · exact (hexs _ hx).symm

/-- **The composite is `A`-linear.** -/
theorem eps_smul (a : A) (m : U) :
    sigma U hT (π (rho U hT (a • m))) = a • sigma U hT (π (rho U hT m)) := by
  have hdec : ∀ b : A, b = ∑ y, ∑ x, D.e y * b * D.e x := fun b ↦ by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, D.sum, one_mul, mul_one]
  conv_lhs => rw [hdec a]
  conv_rhs => rw [hdec a]
  simp only [Finset.sum_smul, map_sum]
  exact Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun x _ ↦ eps_corner hT π hπ x y a m

end Boundary

/-- **A summand of a truncation reaches the boundary.** -/
theorem exists_bdry_of_summand (hind : IsIndecMod A U) {Y : FDMod k A}
    (inc : Y →ₗ[A] trunc U hT) (pr : trunc U hT →ₗ[A] Y) (hretr : ∀ y, pr (inc y) = y)
    (hY : Nontrivial Y) {x₀ : D.ι} {u₀ : U} (hu₀ : D.e x₀ • u₀ ≠ 0)
    (hx₀ : x₀ ∉ T ∨ x₀ ∈ D.bdry T) : ∃ b ∈ D.bdry T, ∃ y : Y, D.e b • y ≠ 0 := by
  by_contra hno
  push Not at hno
  let π : trunc U hT →ₗ[A] trunc U hT := inc ∘ₗ pr
  have hπ : ∀ b ∈ D.bdry T, ∀ n, D.e b • π n = 0 := fun b hb n ↦ by
    change D.e b • inc (pr n) = 0
    rw [← map_smul, hno b hb, map_zero]
  have hππ : ∀ n, π (π n) = π n := fun n ↦ by
    change inc (pr (inc (pr n))) = inc (pr n)
    rw [hretr]
  let ε : U →ₗ[A] U :=
    { toFun := fun m ↦ sigma U hT (π (rho U hT m))
      map_add' := fun m n ↦ by simp only [map_add]
      map_smul' := fun a m ↦ eps_smul hT π hπ a m }
  have hε : ∀ m, ε (ε m) = ε m := fun m ↦ by
    change sigma U hT (π (rho U hT (sigma U hT (π (rho U hT m))))) = sigma U hT (π (rho U hT m))
    rw [rho_sigma, hππ]
  have hcompl : IsCompl (LinearMap.range ε) (LinearMap.ker ε) := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      rintro m ⟨⟨n, rfl⟩, hm⟩
      have h1 : ε (ε n) = 0 := hm
      rw [hε] at h1
      rw [h1]
      exact Submodule.zero_mem _
    · rw [codisjoint_iff, eq_top_iff]
      intro m _
      have hm : m = ε m + (m - ε m) := by abel
      rw [hm]
      refine Submodule.add_mem _ (Submodule.mem_sup_left ⟨m, rfl⟩) (Submodule.mem_sup_right ?_)
      change ε (m - ε m) = 0
      rw [map_sub, hε, sub_self]
  rcases hind _ _ hcompl with h | h
  · -- `ε = 0`
    have h0 : ∀ m, ε m = 0 := fun m ↦ by
      have : ε m ∈ LinearMap.range ε := ⟨m, rfl⟩
      rw [h] at this
      exact (Submodule.mem_bot A).1 this
    obtain ⟨y, hy⟩ := exists_ne (0 : Y)
    apply hy
    have h1 : π (rho U hT (sigma U hT (inc y))) = inc y := by
      rw [rho_sigma]
      change inc (pr (inc y)) = inc y
      rw [hretr]
    have h2 : inc y = 0 := by
      rw [← h1, ← rho_sigma (hT := hT) (π (rho U hT (sigma U hT (inc y))))]
      have := h0 (sigma U hT (inc y))
      change sigma U hT (π (rho U hT (sigma U hT (inc y)))) = 0 at this
      rw [this, map_zero]
    rw [← hretr y, h2, map_zero]
  · -- `ε = 1`
    have h1 : ∀ m, ε m = m := fun m ↦ by
      have : m - ε m ∈ LinearMap.ker ε := by
        change ε (m - ε m) = 0
        rw [map_sub, hε, sub_self]
      rw [h] at this
      exact (sub_eq_zero.1 ((Submodule.mem_bot A).1 this)).symm
    apply hu₀
    have h2 := h1 (D.e x₀ • u₀)
    have h3 : D.e x₀ • ε (D.e x₀ • u₀) = 0 := by
      change D.e x₀ • sigma U hT (π _) = 0
      rcases hx₀ with hx | hx
      · exact e_smul_sigma_of_not_mem hx _
      · rw [← sigma_e_smul, hπ x₀ hx, map_zero]
    rw [h2, ← mul_smul, (D.idem x₀).eq] at h3
    exact h3

/-- **A point of the truncation lies in a summand.** -/
theorem exists_summand {x : D.ι} (hx : x ∈ T) {u : U} (hu : D.e x • u ≠ 0) :
    ∃ (Y : FDMod k A) (inc : Y →ₗ[A] trunc U hT) (pr : trunc U hT →ₗ[A] Y),
      IndNT Y ∧ (∀ y, pr (inc y) = y) ∧ ∃ y : Y, D.e x • y ≠ 0 := by
  classical
  obtain ⟨d⟩ := FDMod.exists_decomp (trunc U hT)
  set n := rho U hT (D.e x • u)
  have hen : D.e x • n = n := by
    rw [e_smul_rho, ← mul_smul, (D.idem x).eq]
  have hn : n ≠ 0 := by
    intro h0
    have h1 := sigma_rho (U := U) (hT := hT) (D.e x • u)
    rw [show rho U hT (D.e x • u) = 0 from h0, map_zero] at h1
    have h2 : D.e x • (D.eT T • (D.e x • u)) = D.e x • u := by
      rw [e_smul_eT_smul hx, ← mul_smul, (D.idem x).eq]
    rw [← h1, smul_zero] at h2
    exact hu h2.symm
  have hsum : n = ∑ j, FDMod.lin (d.inc j) (FDMod.lin (d.proj j) n) := by
    have := LinearMap.congr_fun d.sum_id n
    simpa using this.symm
  obtain ⟨j, hj⟩ : ∃ j, FDMod.lin (d.proj j) n ≠ 0 := by
    by_contra h
    push Not at h
    apply hn
    rw [hsum]
    exact Finset.sum_eq_zero fun j _ ↦ by rw [h j, map_zero]
  refine ⟨d.obj j, FDMod.lin (d.inc j), FDMod.lin (d.proj j), ⟨d.indec j, d.nt j⟩,
    fun y ↦ LinearMap.congr_fun (d.retr j) y, FDMod.lin (d.proj j) n, ?_⟩
  rw [← map_smul, hen]
  exact hj

end Trunc

end DirData

end LargeIndecomposable.AR
