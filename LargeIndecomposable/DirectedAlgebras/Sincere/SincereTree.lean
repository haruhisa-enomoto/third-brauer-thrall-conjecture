module

public import LargeIndecomposable.DirectedAlgebras.Sincere.Truncate

/-!
# Sincere directing modules on trees

* Directed paths of a sincere directing module split into two parts of bounded length
  (`run_bound`), by Vossieck's lemma.
* If a point `t` separates two orthogonal convex parts, then a summand of the truncation to one
  of the parts is a clean line from `t` (`line_of_cut`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

namespace DirData

variable {D : DirData k A} {U : FDMod k A}

/-- A composite of chosen morphisms along a sequence of points. -/
inductive IsChain (D : DirData k A) (x : ℕ → D.ι) (c : ℕ → A) (s : ℕ) : ℕ → A → Prop
  | refl : IsChain D x c s s 1
  | step {t : ℕ} {w : A} : IsChain D x c s t w → IsChain D x c s (t + 1) (c t * D.e (x t) * w)

section Run

variable (hT : ∀ x, x ∈ D.T) (hU : Directing U) (hs : Sincere D U)
  {x : ℕ → D.ι} {r : ℕ} (hArr : ∀ i < r, D.Arr (x i) (x (i + 1)))
  (c : ℕ → A) (hc : ∀ i < r, D.e (x (i + 1)) * c i * D.e (x i) ≠ 0)
include hT hU hs hArr hc

omit hT hU hs hArr hc in
lemma nontrivial_eSub (hs : Sincere D U) (a : D.ι) : Nontrivial (eSub U (D.e a)) := by
  obtain ⟨t, ht⟩ := hs a
  refine ⟨⟨⟨D.e a • t, ?_⟩, 0, fun h ↦ ht (congrArg Subtype.val h)⟩⟩
  change D.e a • D.e a • t = _
  rw [← mul_smul, D.e_mul_e]

omit hT hU hs hArr hc in
lemma actE_eq_zero {a b : D.ι} {w : A} (h : D.e b * w * D.e a = 0) : actE U a b w = 0 := by
  refine LinearMap.ext fun u ↦ Subtype.ext ?_
  rw [actE_coe, h, zero_smul]
  rfl

lemma ne_of_lt_run {s t : ℕ} (hst : s < t) (ht : t ≤ r) : x s ≠ x t := by
  have key : ∀ t, s < t → t ≤ r → Relation.TransGen D.Arr (x s) (x t) := by
    intro t hst
    induction t, hst using Nat.le_induction with
    | base => exact fun _ ↦ Relation.TransGen.single (hArr s (by omega))
    | succ t _ ih => exact fun h ↦ (ih (by omega)).tail (hArr t (by omega))
  intro h
  have h1 := key t hst ht
  rw [← h] at h1
  exact D.acyc _ _ h1 Relation.ReflTransGen.refl

omit hT hU hs hArr in
/-- Composites of injective steps are injective. -/
lemma exists_inj {s : ℕ} : ∀ t, s ≤ t → t ≤ r →
    (∀ m, s ≤ m → m < t → Function.Injective (actE U (x m) (x (m + 1)) (c m))) →
    ∃ w, IsChain D x c s t w ∧ Function.Injective (actE U (x s) (x t) w) := by
  intro t hst
  induction t, hst using Nat.le_induction with
  | base => exact fun _ _ ↦ ⟨1, .refl, (actE_one_bijective _).1⟩
  | succ t hs' ih =>
    intro ht h
    obtain ⟨w, hch, hw⟩ := ih (by omega) fun m h1 h2 ↦ h m h1 (by omega)
    refine ⟨c t * D.e (x t) * w, hch.step, ?_⟩
    have e1 : ⇑(actE U (x s) (x (t + 1)) (c t * D.e (x t) * w)) =
        ⇑(actE U (x t) (x (t + 1)) (c t)) ∘ ⇑(actE U (x s) (x t) w) :=
      funext fun u ↦ (actE_comp _ _ _ _ _ u).symm
    rw [e1]
    exact (h t hs' (by omega)).comp hw

omit hT hU hs hArr in
/-- Composites of surjective steps are surjective. -/
lemma exists_surj {s : ℕ} : ∀ t, s ≤ t → t ≤ r →
    (∀ m, s ≤ m → m < t → Function.Surjective (actE U (x m) (x (m + 1)) (c m))) →
    ∃ w, IsChain D x c s t w ∧ Function.Surjective (actE U (x s) (x t) w) := by
  intro t hst
  induction t, hst using Nat.le_induction with
  | base => exact fun _ _ ↦ ⟨1, .refl, (actE_one_bijective _).2⟩
  | succ t hs' ih =>
    intro ht h
    obtain ⟨w, hch, hw⟩ := ih (by omega) fun m h1 h2 ↦ h m h1 (by omega)
    refine ⟨c t * D.e (x t) * w, hch.step, ?_⟩
    have e1 : ⇑(actE U (x s) (x (t + 1)) (c t * D.e (x t) * w)) =
        ⇑(actE U (x t) (x (t + 1)) (c t)) ∘ ⇑(actE U (x s) (x t) w) :=
      funext fun u ↦ (actE_comp _ _ _ _ _ u).symm
    rw [e1]
    exact (h t hs' (by omega)).comp hw

omit hT hU hs hArr in
/-- Composites of bijective steps are bijective. -/
lemma exists_bij {s : ℕ} : ∀ t, s ≤ t → t ≤ r →
    (∀ m, s ≤ m → m < t → Function.Bijective (actE U (x m) (x (m + 1)) (c m))) →
    ∃ w, Function.Bijective (actE U (x s) (x t) w) := by
  intro t hst
  induction t, hst using Nat.le_induction with
  | base => exact fun _ _ ↦ ⟨1, actE_one_bijective _⟩
  | succ t hs' ih =>
    intro ht h
    obtain ⟨w, hw⟩ := ih (by omega) fun m h1 h2 ↦ h m h1 (by omega)
    refine ⟨c t * D.e (x t) * w, ?_⟩
    have e1 : ⇑(actE U (x s) (x (t + 1)) (c t * D.e (x t) * w)) =
        ⇑(actE U (x t) (x (t + 1)) (c t)) ∘ ⇑(actE U (x s) (x t) w) :=
      funext fun u ↦ (actE_comp _ _ _ _ _ u).symm
    rw [e1]
    exact (h t hs' (by omega)).comp hw

/-- Each step acts injectively or surjectively. -/
lemma step_mono_or_epi {i : ℕ} (hi : i < r) :
    Function.Injective (actE U (x i) (x (i + 1)) (c i)) ∨
      Function.Surjective (actE U (x i) (x (i + 1)) (c i)) :=
  actE_mono_or_epi hT hU hs (ne_of_lt_run hT hU hs hArr c hc (Nat.lt_succ_self i) hi) _ (hc i hi)

/-- No strict drop comes before a strict rise. -/
theorem no_drop_rise : ∀ (n i j : ℕ), j = i + n → 0 < n → j < r →
    ¬Function.Injective (actE U (x i) (x (i + 1)) (c i)) →
    ¬Function.Surjective (actE U (x j) (x (j + 1)) (c j)) → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i j hj hn hjr hi hs'
    have hstep := fun m (hm : m < r) ↦ step_mono_or_epi hT hU hs hArr c hc hm
    by_cases hbet : ∀ m, i + 1 ≤ m → m < j →
        Function.Bijective (actE U (x m) (x (m + 1)) (c m))
    · obtain ⟨w, hw⟩ := exists_bij (U := U) (r := r) c hc (j) (by omega) (by omega) hbet
      have hsi : Function.Surjective (actE U (x i) (x (i + 1)) (c i)) := by
        rcases hstep i (by omega) with h | h
        · exact absurd h hi
        · exact h
      have hij : Function.Injective (actE U (x j) (x (j + 1)) (c j)) := by
        rcases hstep j hjr with h | h
        · exact h
        · exact absurd h hs'
      let W : A := c j * D.e (x j) * w * D.e (x (i + 1)) * c i
      have hcomp : ∀ u, actE U (x i) (x (j + 1)) W u =
          actE U (x j) (x (j + 1)) (c j) (actE U (x (i + 1)) (x j) w
            (actE U (x i) (x (i + 1)) (c i) u)) := fun u ↦ by
        rw [actE_comp, actE_comp]
      have hW : D.e (x (j + 1)) * W * D.e (x i) ≠ 0 := by
        intro h0
        haveI := nontrivial_eSub hs (x (i + 1))
        obtain ⟨t, ht⟩ := exists_ne (0 : eSub U (D.e (x (i + 1))))
        obtain ⟨u, hu⟩ := hsi t
        have h1 : actE U (x i) (x (j + 1)) W u = 0 := by rw [actE_eq_zero h0]; rfl
        rw [hcomp, hu] at h1
        exact ht (hw.1 (hij (h1.trans (map_zero _).symm) |>.trans (map_zero _).symm))
      have hne := ne_of_lt_run hT hU hs hArr c hc (show i < j + 1 by omega) (by omega)
      rcases actE_mono_or_epi hT hU hs hne W hW with h1 | h1
      · exact hi fun p q hpq ↦ h1 (by rw [hcomp, hcomp, hpq])
      · exact hs' fun z ↦ by
          obtain ⟨u, hu⟩ := h1 z
          exact ⟨_, (hcomp u).symm.trans hu⟩
    · push Not at hbet
      obtain ⟨m, hm1, hm2, hm3⟩ := hbet
      by_cases hmi : Function.Injective (actE U (x m) (x (m + 1)) (c m))
      · have hms : ¬Function.Surjective (actE U (x m) (x (m + 1)) (c m)) := fun h ↦ hm3 ⟨hmi, h⟩
        exact ih (m - i) (by omega) i m (by omega) (by omega) (by omega) hi hms
      · exact ih (j - m) (by omega) m j (by omega) (by omega) hjr hmi hs'

/-- **Directed paths have bounded length.** -/
theorem run_bound (N : ℕ) (hN : ∀ s t w, s + N ≤ t → t ≤ r → IsChain D x c s t w →
    D.e (x t) * w * D.e (x s) = 0) : r < 2 * N := by
  by_contra hr
  push Not at hr
  obtain ⟨m, hm1, hm2⟩ : ∃ m, m < N ∧ ¬Function.Injective (actE U (x m) (x (m + 1)) (c m)) := by
    by_contra h
    push Not at h
    obtain ⟨w, hch, hw⟩ := exists_inj (U := U) (r := r) (x := x) (s := 0) c hc N (Nat.zero_le _)
      (by omega) fun m _ hm ↦ h m hm
    haveI := nontrivial_eSub hs (x 0)
    obtain ⟨t, ht⟩ := exists_ne (0 : eSub U (D.e (x 0)))
    have h1 : actE U (x 0) (x N) w t = 0 := by
      rw [actE_eq_zero (hN 0 N w (by omega) (by omega) hch)]
      rfl
    exact ht (hw (h1.trans (map_zero _).symm))
  obtain ⟨j, hj1, hj2, hj3⟩ : ∃ j, r - N ≤ j ∧ j < r ∧
      ¬Function.Surjective (actE U (x j) (x (j + 1)) (c j)) := by
    by_contra h
    push Not at h
    obtain ⟨w, hch, hw⟩ := exists_surj (U := U) (r := r) (x := x) (s := r - N) c hc r (by omega)
      le_rfl fun m h1 h2 ↦ h m h1 h2
    haveI := nontrivial_eSub hs (x r)
    obtain ⟨t, ht⟩ := exists_ne (0 : eSub U (D.e (x r)))
    obtain ⟨u, hu⟩ := hw t
    apply ht
    rw [← hu, actE_eq_zero (hN (r - N) r w (by omega) le_rfl hch)]
    rfl
  exact no_drop_rise hT hU hs hArr c hc (j - m) m j (by omega) (by omega) hj2 hm2 hj3

end Run

section Cut

variable [IsAlgClosed k] (hT : ∀ x, x ∈ D.T) (hDir : ∀ N : FDMod k A, IndNT N → Directing N)
  (hU : Directing U) (hs : Sincere D U)
include hT hDir hU hs

/-- Elements of a summand of a truncation vanish off `T`. -/
lemma e_smul_summand {T : Set D.ι} {hc : D.IsConvexSet T} {Y : FDMod k A}
    {inc : Y →ₗ[A] trunc U hc} {pr : trunc U hc →ₗ[A] Y} (hr : ∀ y, pr (inc y) = y) {b : D.ι}
    (hb : b ∉ T) (y : Y) : D.e b • y = 0 := by
  rw [← hr y, ← map_smul, e_smul_trunc_of_not_mem hc hb, map_zero]

/-- A good end or a line through a boundary point of a convex set. -/
theorem end_or_line_of_trunc {T : Set D.ι} (hc : D.IsConvexSet T) {t v : D.ι}
    (hbd : D.bdry T ⊆ {t}) (ht : t ∈ D.bdry T) (hv : v ∈ T) :
    ∃ Y : FDMod k A, IndNT Y ∧ dimZ D Y v ≠ 0 ∧ (∀ c, c ∉ T → dimZ D Y c = 0) ∧
      ((eulerForm D hT).IsLine t (dimZ D Y) ∨ (eulerForm D hT).GoodEnd (dimZ D Y) t) := by
  have hw := eulerForm_weaklyPositive hT hU hs hDir
  obtain ⟨u, hu⟩ := hs v
  obtain ⟨Y, inc, pr, hY, hr, y, hy⟩ := exists_summand hc hv hu
  obtain ⟨ut, hut⟩ := hs t
  obtain ⟨b, hb, y', hy'⟩ := exists_bdry_of_summand hc hU.1.1 inc pr hr hY.2 hut (Or.inr ht)
  obtain rfl : b = t := hbd hb
  have hroot := isRoot_dimZ hT (hDir Y hY)
  have hc1 : 1 ≤ dimZ D Y b := by
    have h1 := dimZ_ne_zero hy'
    have h2 := dimZ_nonneg (D := D) Y b
    omega
  refine ⟨Y, hY, dimZ_ne_zero hy, fun c hcT ↦ ?_,
    Forms.UnitForm.end_or_line hw _ _ b rfl hroot hc1⟩
  have h0 : eSub Y (D.e c) = ⊥ := eq_bot_iff.2 fun m hm ↦ (Submodule.mem_bot k).2 (by
    have h1 : D.e c • m = m := hm
    rw [← h1]
    exact e_smul_summand hT hDir hU hs hr hcT m)
  change ((finrank k (eSub Y (D.e c)) : ℕ) : ℤ) = 0
  rw [h0, finrank_bot]
  rfl

/-- **A cut gives a line.** -/
theorem line_of_cut {T₁ T₂ : Set D.ι} (h₁ : D.IsConvexSet T₁) (h₂ : D.IsConvexSet T₂) {t v₁ v₂ : D.ι}
    (hb₁ : D.bdry T₁ ⊆ {t}) (hb₂ : D.bdry T₂ ⊆ {t}) (ht₁ : t ∈ D.bdry T₁) (ht₂ : t ∈ D.bdry T₂)
    (hv₁ : v₁ ∈ T₁) (hv₂ : v₂ ∈ T₂)
    (horth : ∀ a ∈ T₁, ∀ b ∈ T₂, a ≠ t → b ≠ t → ¬Relation.ReflTransGen D.Arr a b ∧
      ¬Relation.ReflTransGen D.Arr b a) :
    ∃ Y : FDMod k A, IndNT Y ∧ (eulerForm D hT).IsLine t (dimZ D Y) ∧
      ((dimZ D Y v₁ ≠ 0 ∧ ∀ c, c ∉ T₁ → dimZ D Y c = 0) ∨
        (dimZ D Y v₂ ≠ 0 ∧ ∀ c, c ∉ T₂ → dimZ D Y c = 0)) := by
  obtain ⟨Y₁, hY₁, hv1, hs1, hl1⟩ := end_or_line_of_trunc hT hDir hU hs h₁ hb₁ ht₁ hv₁
  obtain ⟨Y₂, hY₂, hv2, hs2, hl2⟩ := end_or_line_of_trunc hT hDir hU hs h₂ hb₂ ht₂ hv₂
  rcases hl1 with hl1 | hg1
  · exact ⟨Y₁, hY₁, hl1, Or.inl ⟨hv1, hs1⟩⟩
  rcases hl2 with hl2 | hg2
  · exact ⟨Y₂, hY₂, hl2, Or.inr ⟨hv2, hs2⟩⟩
  exfalso
  have hw := eulerForm_weaklyPositive hT hU hs hDir
  obtain ⟨w₁, hp1, ht1, hq1, hsu1⟩ := hg1
  obtain ⟨w₂, hp2, ht2, hq2, hsu2⟩ := hg2
  have hmem : ∀ {Y' : FDMod k A} {T' : Set D.ι}, (∀ c, c ∉ T' → dimZ D Y' c = 0) →
      ∀ c, 0 < dimZ D Y' c → c ∈ T' := fun h c hc ↦ by
    by_contra hcn
    rw [h c hcn] at hc
    exact lt_irrefl _ hc
  have hsub : ∀ (w' : D.ι → ℤ) c, w' t = 2 → (∀ a, 0 ≤ w' a) →
      0 < (w' - (Pi.single t 1 + Pi.single t 1) : D.ι → ℤ) c → c ≠ t ∧ 0 < w' c := fun w' c h1 h2 h3 ↦ by
    have hct : c ≠ t := by
      rintro rfl
      simp only [Pi.sub_apply, Pi.add_apply, Pi.single_eq_same] at h3
      omega
    refine ⟨hct, ?_⟩
    simpa [Pi.single_eq_of_ne hct] using h3
  have hnn : ∀ (w' : D.ι → ℤ), w' t = 2 → (∀ a, 0 ≤ w' a) →
      ∀ c, 0 ≤ (w' - (Pi.single t 1 + Pi.single t 1) : D.ι → ℤ) c := fun w' h1 h2 c ↦ by
    by_cases hct : c = t
    · subst hct
      simp [h1]
    · simpa [Pi.single_eq_of_ne hct] using h2 c
  refine Forms.UnitForm.false_of_glue hw hp1 hp2 ht1 ht2 hq1 hq2 ?_
  refine (eulerForm D hT).B_eq_zero_of_orth (hnn _ ht1 hp1.1) (hnn _ ht2 hp2.1) fun c l hc hl ↦ ?_
  obtain ⟨hct, hc1⟩ := hsub _ c ht1 hp1.1 hc
  obtain ⟨hlt, hl1⟩ := hsub _ l ht2 hp2.1 hl
  have hc2 := hmem hs1 c (hsu1 c hc1)
  have hl2 := hmem hs2 l (hsu2 l hl1)
  exact eulerForm_c_eq_zero hT (horth c hc2 l hl2 hct hlt).1 (horth c hc2 l hl2 hct hlt).2

end Cut

end DirData

end LargeIndecomposable.AR
