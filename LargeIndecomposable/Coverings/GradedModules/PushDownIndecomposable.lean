module

public import LargeIndecomposable.Foundations.Gradings.Hom
public import LargeIndecomposable.Modules.KrullSchmidt.Fitting

/-!
# Push-downs of graded-indecomposable modules are indecomposable

Let `M` be a finite-dimensional graded module that has no decomposition into two
nonzero graded submodules, over an algebra graded by a torsion-free group. Then:

* a product of `2ᵇ − 1` homogeneous non-bijective endomorphisms is zero (graded
  Harada–Sai, `prod_eq_zero`);
* a homogeneous bijective endomorphism has degree `1` (`eq_one_of_bijective`);
* an endomorphism whose degree-one component is bijective is bijective
  (`bijective_of_comp_one`, Gabriel 3.5);
* `M` is indecomposable as an `A`-module (`isIndecMod`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.Graded

open Module AR

variable {G : Type*} [Group G] [DecidableEq G] {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A] {Γ : GrAlg G k A}
variable {M : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
variable (μ : GrMod Γ M)

/-- A graded submodule. -/
def IsGrSub (U : Submodule A M) : Prop := ∀ m ∈ U, ∀ g, μ.proj g m ∈ U

/-- No decomposition into two nonzero graded submodules. -/
def IsGrIndec : Prop :=
  ∀ U V : Submodule A M, IsGrSub μ U → IsGrSub μ V → IsCompl U V → U = ⊥ ∨ V = ⊥

variable {μ}

lemma isGrSub_range {h : G} {f : M →ₗ[A] M} (hf : IsHomog μ μ h f) :
    IsGrSub μ (LinearMap.range f) := by
  rintro _ ⟨x, rfl⟩ g
  have := hf.proj_apply (g * h⁻¹) x
  rw [inv_mul_cancel_right] at this
  rw [this]; exact LinearMap.mem_range_self _ _

lemma isGrSub_ker {h : G} {f : M →ₗ[A] M} (hf : IsHomog μ μ h f) :
    IsGrSub μ (LinearMap.ker f) := by
  intro m hm g
  rw [LinearMap.mem_ker, ← hf.proj_apply g m, LinearMap.mem_ker.1 hm, map_zero]

lemma isGrSub_map {h : G} {f : M →ₗ[A] M} (hf : IsHomog μ μ h f) {U : Submodule A M}
    (hU : IsGrSub μ U) : IsGrSub μ (U.map f) := by
  rintro _ ⟨x, hx, rfl⟩ g
  have := hf.proj_apply (g * h⁻¹) x
  rw [inv_mul_cancel_right] at this
  rw [this]; exact Submodule.mem_map_of_mem (hU x hx _)

/-- Homogeneous endomorphisms. -/
def Homog (f : Module.End A M) : Prop := ∃ h, IsHomog μ μ h f

lemma homog_mul {f f' : Module.End A M} (hf : Homog (μ := μ) f) (hf' : Homog (μ := μ) f') :
    Homog (μ := μ) (f * f') := by
  obtain ⟨h, hh⟩ := hf; obtain ⟨h', hh'⟩ := hf'
  exact ⟨h' * h, hh'.comp hh⟩

lemma homog_prod (l : List (Module.End A M)) (hl : ∀ x ∈ l, Homog (μ := μ) x) :
    Homog (μ := μ) l.prod := by
  induction l with
  | nil => exact ⟨1, isHomog_id⟩
  | cons x l ih =>
    rw [List.prod_cons]
    exact homog_mul (hl x (List.mem_cons_self ..)) (ih fun y hy ↦ hl y (List.mem_cons_of_mem _ hy))

/-- **Graded Harada–Sai.** -/
theorem prod_eq_zero [FiniteDimensional k M] (hind : IsGrIndec μ) {b : ℕ}
    (hdim : finrank k M ≤ b) {W : Set (Module.End A M)}
    (hW : ∀ w ∈ W, Homog (μ := μ) w ∧ ¬Function.Bijective w)
    (l : List (Module.End A M)) (hl : l.length = 2 ^ b - 1) (hlW : ∀ x ∈ l, x ∈ W) :
    l.prod = 0 := by
  have claim : ∀ n ≤ b, ∀ l : List (Module.End A M), l.length = 2 ^ n - 1 →
      (∀ x ∈ l, x ∈ W) → rk k (l.prod : M →ₗ[A] M) ≤ b - n := by
    intro n
    induction n with
    | zero =>
      intro _ l hl _
      simp only [pow_zero, Nat.sub_self, List.length_eq_zero_iff] at hl
      subst hl
      unfold rk
      rw [List.prod_nil, Module.End.one_eq_id, LinearMap.range_id,
        Submodule.restrictScalars_top, finrank_top]
      simpa using hdim
    | succ n ih =>
      intro hn l hl hlW
      have h1 := Nat.one_le_two_pow (n := n)
      have hlen : l.length = (2 ^ n - 1) + 1 + (2 ^ n - 1) := by rw [hl, pow_succ]; omega
      set l₁ := l.take (2 ^ n - 1) with hl₁
      obtain ⟨x, l₂, hdrop⟩ : ∃ x l₂, l.drop (2 ^ n - 1) = x :: l₂ := by
        cases h : l.drop (2 ^ n - 1) with
        | nil => have := congrArg List.length h; simp at this; omega
        | cons x l₂ => exact ⟨x, l₂, rfl⟩
      have hsplit : l = l₁ ++ x :: l₂ := by rw [hl₁, ← hdrop, List.take_append_drop]
      have hl₁len : l₁.length = 2 ^ n - 1 := by rw [hl₁, List.length_take]; omega
      have hl₂len : l₂.length = 2 ^ n - 1 := by
        have := congrArg List.length hsplit
        simp only [List.length_append, List.length_cons] at this
        omega
      have hW₁ : ∀ y ∈ l₁, y ∈ W := fun y hy ↦ hlW y (hsplit ▸ List.mem_append_left _ hy)
      have hW₂ : ∀ y ∈ l₂, y ∈ W := fun y hy ↦
        hlW y (hsplit ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hy))
      have hxW : x ∈ W := hlW x (hsplit ▸ List.mem_append_right _ (List.mem_cons_self ..))
      have hp : l.prod = l₁.prod * (x * l₂.prod) := by rw [hsplit, List.prod_append, List.prod_cons]
      obtain ⟨d₁, hd₁⟩ := homog_prod l₁ fun y hy ↦ (hW y (hW₁ y hy)).1
      obtain ⟨d₂, hd₂⟩ := homog_prod l₂ fun y hy ↦ (hW y (hW₂ y hy)).1
      obtain ⟨dx, hdx⟩ := (hW x hxW).1
      have step := haradaSai_step' (k := k) (l₂.prod : M →ₗ[A] M) (x : M →ₗ[A] M)
        (l₁.prod : M →ₗ[A] M)
        (fun hc ↦ hind _ _ (isGrSub_range hd₂) (isGrSub_ker (hdx.comp hd₁)) hc)
        (fun hc ↦ hind _ _ (isGrSub_map hdx (isGrSub_range hd₂)) (isGrSub_ker hd₁) hc)
        (hW x hxW).2 (c := b - n) (by omega) (ih (by omega) l₂ hl₂len hW₂)
        (ih (by omega) l₁ hl₁len hW₁)
      rw [hp]
      exact (by omega : ∀ y, y < b - n → y ≤ b - (n + 1)) _ step
  have h0 := claim b le_rfl l hl hlW
  rw [Nat.sub_self, Nat.le_zero] at h0
  unfold rk at h0
  have := Submodule.finrank_eq_zero.1 h0
  ext m
  have hm : (l.prod : M →ₗ[A] M) m ∈ (LinearMap.range (l.prod : M →ₗ[A] M)).restrictScalars k :=
    LinearMap.mem_range_self _ m
  rw [this] at hm
  exact (Submodule.mem_bot k).1 hm

/-- A torsion-free group. -/
def TorsionFree (G : Type*) [Group G] : Prop := ∀ x : G, ∀ n : ℕ, 0 < n → x ^ n = 1 → x = 1

/-- **A bijective homogeneous endomorphism of a nonzero module has degree one.** -/
lemma eq_one_of_bijective (htf : TorsionFree G) [Nontrivial M] {h : G} {f : M →ₗ[A] M}
    (hf : IsHomog μ μ h f) (hb : Function.Bijective f) : h = 1 := by
  classical
  let S := μ.supp.filter fun g ↦ ∃ m, μ.proj g m ≠ 0
  have hstep : ∀ g ∈ S, g * h ∈ S := by
    intro g hg
    obtain ⟨-, m, hm⟩ := Finset.mem_filter.1 hg
    have hne : f (μ.proj g m) ≠ 0 := fun h0 ↦ hm (hb.1 (by rw [h0, map_zero]))
    have hmem := hf g _ (μ.mem_proj g m)
    refine Finset.mem_filter.2 ⟨?_, f (μ.proj g m), by rwa [hmem]⟩
    by_contra hout
    exact hne (by rw [← hmem, μ.out _ hout])
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨s, hs⟩ : ∃ s, μ.proj s m ≠ 0 := by
    by_contra hall; push Not at hall
    exact hm (by rw [← μ.sum_eq m]; exact Finset.sum_eq_zero fun g _ ↦ hall g)
  have hsS : s ∈ S := Finset.mem_filter.2 ⟨by by_contra h'; exact hs (μ.out s h' m), m, hs⟩
  have hpow : ∀ n : ℕ, s * h ^ n ∈ S := by
    intro n
    induction n with
    | zero => simpa using hsS
    | succ n ih => rw [pow_succ, ← mul_assoc]; exact hstep _ ih
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ ↦ (⟨s * h ^ n, hpow n⟩ : S))
  have heq' : h ^ i = h ^ j := mul_left_cancel (congrArg Subtype.val heq)
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · refine htf h (j - i) (by omega) ?_
    have : h ^ j = h ^ i * h ^ (j - i) := by rw [← pow_add]; congr 1; omega
    rw [this] at heq'
    exact (mul_eq_left.1 heq'.symm)
  · refine htf h (i - j) (by omega) ?_
    have : h ^ i = h ^ j * h ^ (i - j) := by rw [← pow_add]; congr 1; omega
    rw [this] at heq'
    exact (mul_eq_left.1 heq')

/-- **Graded Fitting**: a degree-one endomorphism is bijective or nilpotent. -/
lemma bijective_or_nilpotent [FiniteDimensional k M] (hind : IsGrIndec μ) {f : M →ₗ[A] M}
    (hf : IsHomog μ μ 1 f) : Function.Bijective f ∨ IsNilpotent f := by
  haveI : IsNoetherian A M := isNoetherian_of_tower k inferInstance
  haveI : IsArtinian A M := isArtinian_of_tower k inferInstance
  obtain ⟨n, hn, hn1⟩ := ((LinearMap.eventually_isCompl_ker_pow_range_pow f).and
    (Filter.eventually_ge_atTop 1)).exists
  have hpow : ∀ j : ℕ, IsHomog μ μ 1 (f ^ j) := by
    intro j
    induction j with
    | zero => exact isHomog_id
    | succ j ih =>
      rw [pow_succ]
      have := hf.comp ih
      rwa [mul_one] at this
  have hfn := hpow n
  rcases hind _ _ (isGrSub_ker hfn) (isGrSub_range hfn) hn with h | h
  · left
    have hinj : Function.Injective (f ^ n) := LinearMap.ker_eq_bot.1 h
    have hfinj : Function.Injective f := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      intro x y hxy
      apply hinj
      rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, hxy]
    exact ⟨hfinj, (LinearMap.injective_iff_surjective (f := f.restrictScalars k)).1 hfinj⟩
  · right
    refine ⟨n, LinearMap.ext fun x ↦ ?_⟩
    have : (f ^ n) x ∈ LinearMap.range (f ^ n) := LinearMap.mem_range_self _ x
    rw [h] at this
    simpa using this

/-- Powers of an element of the span of `W` lie in the span of products from `W`. -/
lemma pow_mem_span {W : Set (Module.End A M)} {r : Module.End A M}
    (hr : r ∈ Submodule.span k W) (n : ℕ) :
    r ^ n ∈ Submodule.span k {p | ∃ l : List (Module.End A M), l.length = n ∧
      (∀ x ∈ l, x ∈ W) ∧ l.prod = p} := by
  induction n with
  | zero => exact Submodule.subset_span ⟨[], rfl, by simp, by simp⟩
  | succ n ih =>
    rw [pow_succ']
    have := Submodule.mul_mem_mul hr ih
    rw [Submodule.span_mul_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨w, hw, _, ⟨l, hl, hlW, rfl⟩, rfl⟩
    exact ⟨w :: l, by simp [hl], fun x hx ↦ by
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hw
      · exact hlW x hx, by simp⟩

lemma comp_sub {h : G} (f f' : M →ₗ[A] M) :
    comp μ μ h (f - f') = comp μ μ h f - comp μ μ h f' := by
  ext m; simp [comp_apply, Finset.sum_sub_distrib]

/-- **Gabriel 3.5**: an endomorphism whose degree-one component is bijective is bijective. -/
theorem bijective_of_comp_one [FiniteDimensional k M] (htf : TorsionFree G)
    (hind : IsGrIndec μ) (e : M →ₗ[A] M) (he : Function.Bijective (comp μ μ 1 e)) :
    Function.Bijective e := by
  classical
  by_cases hnt : Nontrivial M
  swap
  · rw [not_nontrivial_iff_subsingleton] at hnt
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨y, Subsingleton.elim _ _⟩⟩
  set u := comp μ μ 1 e with hu
  have hu1 : IsHomog μ μ 1 u := isHomog_comp μ μ 1 e
  let uinv := (LinearEquiv.ofBijective u he).symm.toLinearMap
  have huinv : ∀ y, u (uinv y) = y := fun y ↦ (LinearEquiv.ofBijective u he).apply_symm_apply y
  have hv : IsHomog μ μ 1 uinv := by
    intro g m hm
    rw [mul_one]
    apply μ.ext_proj
    intro x
    by_cases hx : x = g
    · subst hx; exact μ.proj_proj x _
    · rw [μ.orth x g hx]
      symm
      apply he.1
      rw [map_zero, ← hu1.proj_apply x (uinv m), huinv m, mul_one, μ.proj_of_mem hm hx]
  set e' := uinv ∘ₗ e with he'
  have hce' : comp μ μ 1 e' = LinearMap.id := by
    rw [he', comp_comp_left μ μ hv]
    ext y; exact (LinearEquiv.ofBijective u he).symm_apply_apply y
  set r : Module.End A M := 1 - e' with hr
  have hcr : comp μ μ 1 r = 0 := by
    rw [hr, Module.End.one_eq_id, comp_sub, hce', comp_of_isHomog μ μ isHomog_id, if_pos rfl,
      sub_self]
  -- `r` is a sum of homogeneous non-bijective endomorphisms
  let W : Set (Module.End A M) := {w | Homog (μ := μ) w ∧ ¬Function.Bijective w}
  have hrW : r ∈ Submodule.span k W := by
    have hsum := sum_comp μ μ r
    rw [← hsum]
    refine Submodule.sum_mem _ fun h _ ↦ ?_
    by_cases h1 : h = 1
    · subst h1; rw [hcr]; exact Submodule.zero_mem _
    · refine Submodule.subset_span ⟨⟨h, isHomog_comp μ μ h r⟩, fun hb ↦ h1 ?_⟩
      exact eq_one_of_bijective htf (isHomog_comp μ μ h r) hb
  have hrn : r ^ (2 ^ finrank k M - 1) = 0 := by
    have := pow_mem_span hrW (2 ^ finrank k M - 1)
    refine (Submodule.span_le (p := ⊥)).2 ?_ this |> fun h ↦ (Submodule.mem_bot k).1 h
    rintro _ ⟨l, hl, hlW, rfl⟩
    exact (prod_eq_zero hind le_rfl (fun w hw ↦ hw) l hl hlW : _)
  have hunit : IsUnit e' := by
    have := IsNilpotent.isUnit_one_sub ⟨_, hrn⟩
    rwa [hr, sub_sub_cancel] at this
  have he'b : Function.Bijective e' := (Module.End.isUnit_iff e').1 hunit
  have heq : e = u ∘ₗ e' := by
    ext y; simp only [he', LinearMap.comp_apply]; exact (huinv (e y)).symm
  rw [heq]
  exact he.comp he'b

/-- **The push-down of a graded-indecomposable module is indecomposable.** -/
theorem isIndecMod [FiniteDimensional k M] (htf : TorsionFree G) (hind : IsGrIndec μ) :
    IsIndecMod A M := by
  intro U V hUV
  let ε : M →ₗ[A] M := U.subtype ∘ₗ Submodule.projectionOnto U V hUV
  have hε : ε * ε = ε := by
    ext m; simp [ε, Module.End.mul_apply, Submodule.projectionOnto_apply_left]
  rcases bijective_or_nilpotent hind (isHomog_comp μ μ 1 ε) with hb | hn
  · -- `ε` is bijective, so it is the identity and `V = 0`
    have hεb := bijective_of_comp_one htf hind ε hb
    right
    rw [eq_bot_iff]; intro v hv
    have h1 : ε v = 0 := by
      simp [ε, Submodule.projectionOnto_apply_eq_zero_iff, hv]
    have := hεb.1 (h1.trans (map_zero ε).symm)
    simp [this]
  · -- `1 - ε` has bijective degree-one component, so `ε = 0` and `U = 0`
    have hcomp : comp μ μ 1 ((1 : Module.End A M) - ε) = 1 - comp μ μ 1 ε := by
      rw [Module.End.one_eq_id, comp_sub, comp_of_isHomog μ μ isHomog_id, if_pos rfl]
    have hb : Function.Bijective (comp μ μ 1 ((1 : Module.End A M) - ε)) := by
      rw [hcomp, ← Module.End.isUnit_iff]
      exact hn.isUnit_one_sub
    have hεb := bijective_of_comp_one htf hind _ hb
    left
    rw [eq_bot_iff]; intro u hu
    have h1 : ((1 : Module.End A M) - ε) u = 0 := by
      simp [ε, Submodule.projectionOnto_apply_left (h := hUV) ⟨u, hu⟩]
    have := hεb.1 (h1.trans (map_zero _).symm)
    simp [this]

end LargeIndecomposable.Graded
