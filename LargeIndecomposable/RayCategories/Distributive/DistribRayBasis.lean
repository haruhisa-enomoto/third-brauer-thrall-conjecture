module

public import LargeIndecomposable.RayCategories.RayTables.RayBasis
public import LargeIndecomposable.RayCategories.RayTables.EndpointChains

/-!
# Ray transversals for algebras with finitely many ideals

Copies of the endpoint-chain and ray-transversal results of
`RayCategories/RayTables/EndpointChains.lean` and `RayCategories/RayTables/RayBasis.lean`
whose only use of representation-finiteness was the finiteness of the set of
two-sided ideals. Here that finiteness is the hypothesis, so the results
apply to distributive algebras (`finite_twoSidedIdeal_of_isDistribIdeals`):
one representative of each nonzero ray forms a basis (BGRS 1.7).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

universe u v

namespace PrimitiveIdempotents

variable {k : Type u} [Field k] [IsAlgClosed k] {A : Type v} [Ring A] [Algebra k A]
  [FiniteDimensional k A] (F : PrimitiveIdempotents A)

/-- **Finitely many endpoint subbimodules**: each is recovered from the ideal
it generates. -/
theorem finite_subbimodules_fin (hA : (Set.univ : Set (TwoSidedIdeal A)).Finite) (x y : Fin F.m) :
    {N : Submodule k A | F.IsEndpointSubbimodule x y N}.Finite := by
  apply Set.Finite.of_finite_image (f := genIdeal)
  · exact hA.subset (Set.subset_univ _)
  · intro N hN N' hN' h
    apply le_antisymm
    · intro n hn
      have := F.genIdeal_corner hN' (h ▸ mem_genIdeal hn)
      rwa [(F.corner_mul_mem (hN.1 hn)).1, (F.corner_mul_mem (hN.1 hn)).2] at this
    · intro n hn
      have := F.genIdeal_corner hN (h.symm ▸ mem_genIdeal hn)
      rwa [(F.corner_mul_mem (hN'.1 hn)).1, (F.corner_mul_mem (hN'.1 hn)).2] at this

/-- **Lemma 3.1(3)**: the endpoint subbimodules form a chain. -/
theorem isChain_subbimodules_fin (hA : (Set.univ : Set (TwoSidedIdeal A)).Finite) (x y : Fin F.m) :
    IsChain (· ≤ ·) {N : Submodule k A | F.IsEndpointSubbimodule x y N} := by
  intro N₁ h₁ N₂ h₂ _
  by_contra hcon
  push Not at hcon
  obtain ⟨h12, h21⟩ := hcon
  have hI := F.isEndpoint_inf h₁ h₂
  obtain ⟨P₁, hP₁, hlt₁, hle₁, hr₁⟩ := F.exists_socle_layer hI h₁
    (lt_of_le_of_ne inf_le_left fun h ↦ h12 (h ▸ inf_le_right))
  obtain ⟨P₂, hP₂, hlt₂, hle₂, hr₂⟩ := F.exists_socle_layer hI h₂
    (lt_of_le_of_ne inf_le_right fun h ↦ h21 (h ▸ inf_le_left))
  obtain ⟨s₁, hs₁, hs₁'⟩ := SetLike.exists_of_lt hlt₁
  obtain ⟨s₂, hs₂, hs₂'⟩ := SetLike.exists_of_lt hlt₂
  have hs₁N₂ : s₁ ∉ N₂ := fun h ↦ hs₁' ⟨hle₁ hs₁, h⟩
  have hs₂N₁ : s₂ ∉ N₁ := fun h ↦ hs₂' ⟨h, hle₂ hs₂⟩
  let L : k → Submodule k A := fun t ↦ (N₁ ⊓ N₂) ⊔ Submodule.span k {s₁ + t • s₂}
  have hPP := F.isEndpoint_sup hP₁ hP₂
  have hrad : F.cornerRadical (k := k) x * (P₁ ⊔ P₂) ⊔ (P₁ ⊔ P₂) * F.cornerRadical (k := k) y ≤
      N₁ ⊓ N₂ := by
    rw [Submodule.mul_sup, Submodule.sup_mul]
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · exact le_sup_left.trans hr₁
    · exact le_sup_left.trans hr₂
    · exact le_sup_right.trans hr₁
    · exact le_sup_right.trans hr₂
  have hL : ∀ t, F.IsEndpointSubbimodule x y (L t) := fun t ↦
    F.isEndpoint_between hPP le_sup_left
      (sup_le (hlt₁.le.trans le_sup_left)
        ((Submodule.span_le).2 (Set.singleton_subset_iff.2
          (Submodule.add_mem _ (Submodule.mem_sup_left hs₁)
            (Submodule.smul_mem _ t (Submodule.mem_sup_right hs₂)))))) hrad
  have hinj : Function.Injective L := by
    intro t t' h
    have hmem : s₁ + t • s₂ ∈ L t' := h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    obtain ⟨n, hn, z, hz, hnz⟩ := Submodule.mem_sup.1 hmem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have hn' : n = s₁ + t • s₂ - c • (s₁ + t' • s₂) := by rw [← hnz]; abel
    have key : (1 - c) • s₁ + (t - c * t') • s₂ = n := by
      rw [hn']
      simp only [sub_smul, one_smul, smul_add, mul_smul]
      abel
    have hc : c = 1 := by
      by_contra hc1
      have : (1 - c) • s₁ ∈ N₂ := by
        have h2 : (t - c * t') • s₂ ∈ N₂ := Submodule.smul_mem _ _ (hle₂ hs₂)
        have := Submodule.sub_mem _ hn.2 h2
        rwa [← key, add_sub_cancel_right] at this
      apply hs₁N₂
      have h1c : (1 - c) ≠ 0 := sub_ne_zero.2 (Ne.symm hc1)
      have := Submodule.smul_mem _ (1 - c)⁻¹ this
      rwa [smul_smul, inv_mul_cancel₀ h1c, one_smul] at this
    subst hc
    by_contra htt
    have : (t - 1 * t') • s₂ ∈ N₁ := by
      have := hn.1
      rwa [← key, sub_self, zero_smul, zero_add] at this
    apply hs₂N₁
    have hne : t - 1 * t' ≠ 0 := by rw [one_mul]; exact sub_ne_zero.2 htt
    have := Submodule.smul_mem _ (t - 1 * t')⁻¹ this
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  have hfin := F.finite_subbimodules_fin (k := k) hA x y
  exact Set.infinite_of_injective_forall_mem hinj hL hfin

/-- **Lemma 3.1(3)**, last part: `R_x f R_y = R_x f` or `f R_y`. -/
theorem endpointSpan_one_sided_fin (hA : (Set.univ : Set (TwoSidedIdeal A)).Finite) {x y : Fin F.m} {f : A}
    (hf : f ∈ F.corner (k := k) x y) :
    F.endpointSpan (k := k) x y f =
        Submodule.span k {g | ∃ a ∈ F.corner (k := k) x x, g = a * f} ∨
      F.endpointSpan (k := k) x y f =
        Submodule.span k {g | ∃ b ∈ F.corner (k := k) y y, g = f * b} := by
  classical
  set Cx := F.corner (k := k) x x
  set Cy := F.corner (k := k) y y
  set Rx := F.cornerRadical (k := k) x
  set Ry := F.cornerRadical (k := k) y
  set U := F.endpointSpan (k := k) x y f
  set Lx := Submodule.span k {g | ∃ a ∈ Cx, g = a * f}
  set Ly := Submodule.span k {g | ∃ b ∈ Cy, g = f * b}
  have hfl := (F.corner_mul_mem hf).1
  have hfr := (F.corner_mul_mem hf).2
  have hmulx : ∀ {a a'}, a ∈ Cx → a' ∈ Cx → a * a' ∈ Cx := fun {a a'} ha ha' ↦
    (F.mem_corner_iff' (k := k)).2 (by
      rw [← (F.mem_corner_iff' (k := k)).1 ha, ← (F.mem_corner_iff' (k := k)).1 ha']
      simp only [mul_assoc, (F.complete.idem x).eq]
      rw [← mul_assoc (F.e x) (F.e x), (F.complete.idem x).eq])
  have hmuly : ∀ {b b'}, b ∈ Cy → b' ∈ Cy → b * b' ∈ Cy := fun {b b'} hb hb' ↦
    (F.mem_corner_iff' (k := k)).2 (by
      rw [← (F.mem_corner_iff' (k := k)).1 hb, ← (F.mem_corner_iff' (k := k)).1 hb']
      simp only [mul_assoc, (F.complete.idem y).eq]
      rw [← mul_assoc (F.e y) (F.e y), (F.complete.idem y).eq])
  have hgenU : ∀ {a b}, a ∈ Cx → b ∈ Cy → a * f * b ∈ U := fun ha hb ↦
    Submodule.subset_span ⟨_, ha, _, hb, rfl⟩
  have hfU : f ∈ U := by
    have := hgenU (F.e_mem_corner x) (F.e_mem_corner y)
    rwa [hfl, hfr] at this
  -- `U` is a subbimodule
  have hU : F.IsEndpointSubbimodule x y U := by
    refine ⟨Submodule.span_le.2 ?_, fun a ha z hz ↦ ?_, fun b hb z hz ↦ ?_⟩
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact (F.mem_corner_iff' (k := k)).2 (by
        rw [← (F.mem_corner_iff' (k := k)).1 ha, ← (F.mem_corner_iff' (k := k)).1 hb]
        simp only [mul_assoc, (F.complete.idem x).eq, (F.complete.idem y).eq]
        rw [← mul_assoc (F.e x) (F.e x), (F.complete.idem x).eq])
    · induction hz using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨a', ha', b, hb, rfl⟩ := hg
          rw [← mul_assoc, ← mul_assoc]; exact hgenU (hmulx ha ha') hb
      | zero => simp
      | add g h _ _ hg hh => rw [mul_add]; exact U.add_mem hg hh
      | smul c g _ hg => rw [mul_smul_comm]; exact U.smul_mem c hg
    · induction hz using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨a, ha, b', hb', rfl⟩ := hg
          rw [mul_assoc]; exact hgenU ha (hmuly hb' hb)
      | zero => simp
      | add g h _ _ hg hh => rw [add_mul]; exact U.add_mem hg hh
      | smul c g _ hg => rw [smul_mul_assoc]; exact U.smul_mem c hg
  have hRxU_le : Rx * U ≤ U := Submodule.mul_le.2 fun r hr u hu ↦
    hU.2.1 r (F.cornerRadical_le_corner x hr) u hu
  have hURy_le : U * Ry ≤ U := Submodule.mul_le.2 fun u hu r hr ↦
    hU.2.2 r (F.cornerRadical_le_corner y hr) u hu
  have hRxU : F.IsEndpointSubbimodule x y (Rx * U) := by
    refine ⟨hRxU_le.trans hU.1, fun a ha z hz ↦ ?_, fun b hb z hz ↦ ?_⟩
    · refine Submodule.mul_induction_on hz (fun r hr u hu ↦ ?_) (fun p q hp hq ↦ ?_)
      · rw [← mul_assoc]; exact Submodule.mul_mem_mul (F.radL_mem ha hr) hu
      · rw [mul_add]; exact Submodule.add_mem _ hp hq
    · refine Submodule.mul_induction_on hz (fun r hr u hu ↦ ?_) (fun p q hp hq ↦ ?_)
      · rw [mul_assoc]; exact Submodule.mul_mem_mul hr (hU.2.2 b hb u hu)
      · rw [add_mul]; exact Submodule.add_mem _ hp hq
  have hURy : F.IsEndpointSubbimodule x y (U * Ry) := by
    refine ⟨hURy_le.trans hU.1, fun a ha z hz ↦ ?_, fun b hb z hz ↦ ?_⟩
    · refine Submodule.mul_induction_on hz (fun u hu r hr ↦ ?_) (fun p q hp hq ↦ ?_)
      · rw [← mul_assoc]; exact Submodule.mul_mem_mul (hU.2.1 a ha u hu) hr
      · rw [mul_add]; exact Submodule.add_mem _ hp hq
    · refine Submodule.mul_induction_on hz (fun u hu r hr ↦ ?_) (fun p q hp hq ↦ ?_)
      · rw [mul_assoc]; exact Submodule.mul_mem_mul hu (F.radR_mem hb hr)
      · rw [add_mul]; exact Submodule.add_mem _ hp hq
  obtain ⟨K, hK⟩ := F.cornerRadical_pow_eq_bot (k := k)
  rcases (F.isChain_subbimodules_fin (k := k) hA x y).total hRxU hURy with hPQ | hQP
  · -- `(rad R_x) U ≤ U (rad R_y)`: `U = f R_y`
    right
    have hCyLy : ∀ b ∈ Cy, ∀ z ∈ Ly, z * b ∈ Ly := by
      intro b hb z hz
      induction hz using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨b', hb', rfl⟩ := hg
          rw [mul_assoc]; exact Submodule.subset_span ⟨_, hmuly hb' hb, rfl⟩
      | zero => simp
      | add g h _ _ hg hh => rw [add_mul]; exact Ly.add_mem hg hh
      | smul c g _ hg => rw [smul_mul_assoc]; exact Ly.smul_mem c hg
    have hCypow : ∀ n, ∀ b ∈ Cy, ∀ z ∈ U * Ry ^ n, z * b ∈ U * Ry ^ n := by
      intro n
      induction n with
      | zero => intro b hb z hz; rw [pow_zero, Submodule.mul_one] at hz ⊢; exact hU.2.2 b hb z hz
      | succ n ih =>
          intro b hb z hz
          rw [pow_succ, ← mul_assoc] at hz ⊢
          refine Submodule.mul_induction_on hz (fun w hw r hr ↦ ?_) (fun p q hp hq ↦ ?_)
          · rw [mul_assoc w r b]; exact Submodule.mul_mem_mul hw (F.radR_mem hb hr)
          · rw [add_mul]; exact Submodule.add_mem _ hp hq
    have key : ∀ n, ∀ a ∈ Cx, a * f ∈ Ly ⊔ U * Ry ^ n := by
      intro n
      induction n with
      | zero =>
          intro a ha
          rw [pow_zero, Submodule.mul_one]
          apply Submodule.mem_sup_right
          have := hgenU ha (F.e_mem_corner y); rwa [mul_assoc, hfr] at this
      | succ n ih =>
          intro a ha
          obtain ⟨c, hc⟩ := F.exists_sub_smul_mem_radical k x ha
          have hr : a - c • F.e x ∈ Rx :=
            ⟨Submodule.sub_mem _ ha (Submodule.smul_mem _ c (F.e_mem_corner x)), hc⟩
          have hsplit : a * f = c • f + (a - c • F.e x) * f := by
            rw [sub_mul, smul_mul_assoc, hfl]; abel
          rw [hsplit]
          refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ c ?_)) ?_
          · exact Submodule.subset_span ⟨F.e y, F.e_mem_corner y, hfr.symm⟩
          · have h1 : (a - c • F.e x) * f ∈ Rx * U := Submodule.mul_mem_mul hr hfU
            have hUle : U ≤ Ly ⊔ U * Ry ^ n := by
              refine Submodule.span_le.2 ?_
              rintro _ ⟨a', ha', b, hb, rfl⟩
              obtain ⟨l, hl, w, hw, hlw⟩ := Submodule.mem_sup.1 (ih a' ha')
              rw [← hlw, add_mul]
              exact Submodule.add_mem_sup (hCyLy b hb l hl) (hCypow n b hb w hw)
            have h2 : U * Ry ≤ Ly ⊔ U * Ry ^ (n + 1) := by
              calc U * Ry ≤ (Ly ⊔ U * Ry ^ n) * Ry := _root_.mul_le_mul_left hUle Ry
                _ = Ly * Ry ⊔ U * Ry ^ (n + 1) := by rw [Submodule.sup_mul, pow_succ, mul_assoc]
                _ ≤ Ly ⊔ U * Ry ^ (n + 1) := sup_le_sup_right (Submodule.mul_le.2 fun z hz r hr ↦
                    hCyLy r (F.cornerRadical_le_corner y hr) z hz) _
            exact h2 (hPQ h1)
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, ha, b, hb, rfl⟩
      have := key K a ha
      rw [hK y, Submodule.mul_bot, sup_bot_eq] at this
      exact hCyLy b hb _ this
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨b, hb, rfl⟩
      have := hgenU (F.e_mem_corner x) hb
      rwa [hfl] at this
  · -- `U (rad R_y) ≤ (rad R_x) U`: `U = R_x f`
    left
    have hCxLx : ∀ a ∈ Cx, ∀ z ∈ Lx, a * z ∈ Lx := by
      intro a ha z hz
      induction hz using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨a', ha', rfl⟩ := hg
          rw [← mul_assoc]; exact Submodule.subset_span ⟨_, hmulx ha ha', rfl⟩
      | zero => simp
      | add g h _ _ hg hh => rw [mul_add]; exact Lx.add_mem hg hh
      | smul c g _ hg => rw [mul_smul_comm]; exact Lx.smul_mem c hg
    have hCxpow : ∀ n, ∀ a ∈ Cx, ∀ z ∈ Rx ^ n * U, a * z ∈ Rx ^ n * U := by
      intro n
      induction n with
      | zero => intro a ha z hz; rw [pow_zero, Submodule.one_mul] at hz ⊢; exact hU.2.1 a ha z hz
      | succ n ih =>
          intro a ha z hz
          rw [pow_succ', mul_assoc] at hz ⊢
          refine Submodule.mul_induction_on hz (fun r hr w hw ↦ ?_) (fun p q hp hq ↦ ?_)
          · rw [← mul_assoc a r w]; exact Submodule.mul_mem_mul (F.radL_mem ha hr) hw
          · rw [mul_add]; exact Submodule.add_mem _ hp hq
    have key : ∀ n, ∀ b ∈ Cy, f * b ∈ Lx ⊔ Rx ^ n * U := by
      intro n
      induction n with
      | zero =>
          intro b hb
          rw [pow_zero, Submodule.one_mul]
          apply Submodule.mem_sup_right
          have := hgenU (F.e_mem_corner x) hb; rwa [hfl] at this
      | succ n ih =>
          intro b hb
          obtain ⟨c, hc⟩ := F.exists_sub_smul_mem_radical k y hb
          have hr : b - c • F.e y ∈ Ry :=
            ⟨Submodule.sub_mem _ hb (Submodule.smul_mem _ c (F.e_mem_corner y)), hc⟩
          have hsplit : f * b = c • f + f * (b - c • F.e y) := by
            rw [mul_sub, mul_smul_comm, hfr]; abel
          rw [hsplit]
          refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ c ?_)) ?_
          · exact Submodule.subset_span ⟨F.e x, F.e_mem_corner x, hfl.symm⟩
          · have h1 : f * (b - c • F.e y) ∈ U * Ry := Submodule.mul_mem_mul hfU hr
            have hUle : U ≤ Lx ⊔ Rx ^ n * U := by
              refine Submodule.span_le.2 ?_
              rintro _ ⟨a, ha, b', hb', rfl⟩
              obtain ⟨l, hl, w, hw, hlw⟩ := Submodule.mem_sup.1 (ih b' hb')
              rw [mul_assoc, ← hlw, mul_add]
              exact Submodule.add_mem_sup (hCxLx a ha l hl) (hCxpow n a ha w hw)
            have h2 : Rx * U ≤ Lx ⊔ Rx ^ (n + 1) * U := by
              calc Rx * U ≤ Rx * (Lx ⊔ Rx ^ n * U) := _root_.mul_le_mul_right hUle Rx
                _ = Rx * Lx ⊔ Rx ^ (n + 1) * U := by rw [Submodule.mul_sup, pow_succ', mul_assoc]
                _ ≤ Lx ⊔ Rx ^ (n + 1) * U := sup_le_sup_right (Submodule.mul_le.2 fun r hr z hz ↦
                    hCxLx r (F.cornerRadical_le_corner x hr) z hz) _
            exact h2 (hQP h1)
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, ha, b, hb, rfl⟩
      have := key K b hb
      rw [hK x, Submodule.bot_mul, sup_bot_eq] at this
      rw [mul_assoc]
      exact hCxLx a ha _ this
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, ha, rfl⟩
      have := hgenU ha (F.e_mem_corner y)
      rwa [mul_assoc, hfr] at this

/-- **`R(f)` is the unique maximal subbimodule of `U(f)`.** -/
theorem le_endpointRadical_fin (hA : (Set.univ : Set (TwoSidedIdeal A)).Finite) {x y : Fin F.m} {g : A}
    (hg : g ∈ F.corner (k := k) x y) {N : Submodule k A} (hN : F.IsEndpointSubbimodule x y N)
    (hNU : N ≤ F.endpointSpan (k := k) x y g) (hgN : g ∉ N) :
    N ≤ F.endpointRadical (k := k) x y g := by
  rcases (F.isChain_subbimodules_fin (k := k) hA x y).total hN (F.isEndpoint_endpointRadical hg) with h | h
  · exact h
  · by_contra hle
    obtain ⟨n, hn, hnR⟩ := SetLike.not_le_iff_exists.1 hle
    have hnU := hNU hn
    rw [F.endpointSpan_eq hg] at hnU
    obtain ⟨v, hv, r, hr, hvr⟩ := Submodule.mem_sup.1 hnU
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    have hc : c ≠ 0 := by
      rintro rfl
      rw [zero_smul, zero_add] at hvr
      exact hnR (hvr ▸ hr)
    apply hgN
    have : g = c⁻¹ • n - c⁻¹ • r := by
      rw [← hvr, smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul, add_sub_cancel_right]
    rw [this]
    exact N.sub_mem (N.smul_mem _ hn) (N.smul_mem _ (h hr))

/-- **`[f] = U(f) ∖ R(f)`** (`eq:ray-layer`). -/
theorem mem_ray_iff_fin (hA : (Set.univ : Set (TwoSidedIdeal A)).Finite) {x y : Fin F.m} {f : A}
    (hf : f ∈ F.corner (k := k) x y) (hf0 : f ≠ 0) (g : A) :
    g ∈ F.ray (k := k) x y f ↔
      g ∈ F.endpointSpan (k := k) x y f ∧ g ∉ F.endpointRadical (k := k) x y f := by
  have hR := F.isEndpoint_endpointRadical hf
  constructor
  · rintro ⟨u, w, hu, hw, rfl⟩
    refine ⟨Submodule.subset_span ⟨u, hu.1, w, hw.1, rfl⟩, fun hgR ↦ ?_⟩
    obtain ⟨u', hu', h1, h2⟩ := F.cornerUnit_inv hu
    obtain ⟨w', hw', h3, h4⟩ := F.cornerUnit_inv hw
    apply F.not_mem_endpointRadical hf hf0
    have := hR.2.2 w' hw'.1 _ (hR.2.1 u' hu'.1 _ hgR)
    have hfeq : f = u' * (u * f * w) * w' := by
      calc f = (u' * u) * f * (w * w') := by rw [h2, h3, F.e_mul_of_mem hf, F.mul_e_of_mem hf]
        _ = u' * (u * f * w) * w' := by simp only [mul_assoc]
    rwa [← hfeq] at this
  · rintro ⟨hgU, hgR⟩
    rcases F.endpointSpan_one_sided_fin (k := k) hA hf with h | h
    · obtain ⟨a, ha, rfl⟩ := F.exists_of_mem_span_left (h ▸ hgU)
      have ha' : a ∉ F.cornerRadical (k := k) x := fun haR ↦ hgR (Submodule.subset_span
        (Or.inl ⟨a, haR, F.e y, F.e_mem_corner y, by rw [mul_assoc, F.mul_e_of_mem hf]⟩))
      exact ⟨a, F.e y, F.isCornerUnit_of_not_mem ha ha', F.isCornerUnit_e y, by
        rw [mul_assoc, F.mul_e_of_mem hf]⟩
    · obtain ⟨b, hb, rfl⟩ := F.exists_of_mem_span_right (h ▸ hgU)
      have hb' : b ∉ F.cornerRadical (k := k) y := fun hbR ↦ hgR (Submodule.subset_span
        (Or.inr ⟨F.e x, F.e_mem_corner x, b, hbR, by rw [F.e_mul_of_mem hf]⟩))
      exact ⟨F.e x, b, F.isCornerUnit_e x, F.isCornerUnit_of_not_mem hb hb', by
        rw [F.e_mul_of_mem hf]⟩

/-- **A ray is determined by its subbimodule.** -/
theorem ray_eq_of_endpointSpan_eq_fin (hA : (Set.univ : Set (TwoSidedIdeal A)).Finite) {x y : Fin F.m} {f g : A}
    (hf : f ∈ F.corner (k := k) x y) (hf0 : f ≠ 0) (hg : g ∈ F.corner (k := k) x y)
    (h : F.endpointSpan (k := k) x y g = F.endpointSpan (k := k) x y f) :
    F.ray (k := k) x y g = F.ray (k := k) x y f := by
  refine F.ray_eq_of_mem hf ((F.mem_ray_iff_fin (k := k) hA hf hf0 g).2 ⟨h ▸ F.mem_endpointSpan_self hg, ?_⟩)
  intro hgR
  have := F.endpointSpan_le (F.isEndpoint_endpointRadical hf) hgR
  rw [h] at this
  exact F.not_mem_endpointRadical hf hf0 (this (F.mem_endpointSpan_self hf))

/-- **Every nonzero subbimodule is cyclic**: `N = U(g)`, `g` taken outside the
largest subbimodule below `N`. -/
theorem exists_cyclic_fin (hA : (Set.univ : Set (TwoSidedIdeal A)).Finite) {x y : Fin F.m} {N : Submodule k A}
    (hN : F.IsEndpointSubbimodule x y N) (hN0 : N ≠ ⊥) :
    ∃ g ∈ N, g ≠ 0 ∧ N = F.endpointSpan (k := k) x y g := by
  set S := {M : Submodule k A | F.IsEndpointSubbimodule x y M ∧ M < N}
  have hfin : S.Finite := (F.finite_subbimodules_fin (k := k) hA x y).subset fun M hM ↦ hM.1
  have hbot : F.IsEndpointSubbimodule x y ⊥ :=
    ⟨bot_le, fun _ _ n hn ↦ by rw [(Submodule.mem_bot k).1 hn, mul_zero]; exact Submodule.zero_mem _,
      fun _ _ n hn ↦ by rw [(Submodule.mem_bot k).1 hn, zero_mul]; exact Submodule.zero_mem _⟩
  obtain ⟨M, hM⟩ := hfin.exists_maximal ⟨⊥, hbot, bot_lt_iff_ne_bot.2 hN0⟩
  obtain ⟨g, hgN, hgM⟩ := SetLike.exists_of_lt hM.1.2
  have hg0 : g ≠ 0 := fun h ↦ hgM (h ▸ Submodule.zero_mem _)
  have hgC := hN.1 hgN
  have hU := F.isEndpoint_endpointSpan hgC
  have hUN := F.endpointSpan_le hN hgN
  refine ⟨g, hgN, hg0, (le_antisymm hUN ?_).symm⟩
  by_contra hNU
  have hlt : F.endpointSpan (k := k) x y g < N := lt_of_le_of_ne hUN fun h ↦ hNU (h ▸ le_rfl)
  rcases (F.isChain_subbimodules_fin (k := k) hA x y).total hU hM.1.1 with h | h
  · exact hgM (h (F.mem_endpointSpan_self hgC))
  · have := hM.2 ⟨hU, hlt⟩ h
    exact hgM (this (F.mem_endpointSpan_self hgC))

variable {b : F.NonzeroRay k → A} (hb : F.IsRayTransversal b)

include hb in
/-- **Distinct rays of a corner have distinct subbimodules.** -/
theorem transversal_ext_fin (hA : (Set.univ : Set (TwoSidedIdeal A)).Finite) {x y : Fin F.m} {s s' : F.NonzeroRay k}
    (hs : b s ∈ F.corner (k := k) x y) (hs' : b s' ∈ F.corner (k := k) x y)
    (h : F.endpointSpan (k := k) x y (b s) = F.endpointSpan (k := k) x y (b s')) : s = s' := by
  obtain ⟨-, -, -, hs0, -⟩ := F.transversal_spec hb s'
  apply Subtype.ext
  rw [F.transversal_ray hb s hs, F.transversal_ray hb s' hs']
  exact F.ray_eq_of_endpointSpan_eq_fin (k := k) hA hs' hs0 hs h

include hb in
/-- **The transversal spans every subbimodule of a corner.** -/
theorem le_span_transversal_fin (hA : (Set.univ : Set (TwoSidedIdeal A)).Finite) {x y : Fin F.m} :
    ∀ (n : ℕ) (N : Submodule k A), Module.finrank k N = n → F.IsEndpointSubbimodule x y N →
      N ≤ Submodule.span k (b '' {s | b s ∈ N}) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N hn hN
  by_cases hN0 : N = ⊥
  · rw [hN0]; exact bot_le
  obtain ⟨g, hgN, hg0, hNU⟩ := F.exists_cyclic_fin (k := k) hA hN hN0
  have hgC := hN.1 hgN
  set R := F.endpointRadical (k := k) x y g
  have hRU : R ≤ F.endpointSpan (k := k) x y g := by
    rw [F.endpointSpan_eq hgC]; exact le_sup_right
  have hRN : R < N := by
    rw [hNU]
    exact lt_of_le_of_ne hRU fun h ↦ F.not_mem_endpointRadical hgC hg0
      (by change g ∈ R; rw [h]; exact F.mem_endpointSpan_self hgC)
  have hspanR : R ≤ Submodule.span k (b '' {s | b s ∈ N}) :=
    (ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hRN) R rfl
      (F.isEndpoint_endpointRadical hgC)).trans
      (Submodule.span_mono (Set.image_mono fun s hs ↦ hRN.le hs))
  let s : F.NonzeroRay k := ⟨F.ray (k := k) x y g, x, y, g, hgC, hg0, rfl⟩
  obtain ⟨hbU, hbR⟩ := (F.mem_ray_iff_fin (k := k) hA hgC hg0 (b s)).1 (hb.1 s)
  have hbN : b s ∈ N := hNU ▸ hbU
  have hbU' := hbU
  rw [F.endpointSpan_eq hgC] at hbU'
  obtain ⟨v, hv, r, hr, hvr⟩ := Submodule.mem_sup.1 hbU'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_add] at hvr
    exact hbR (hvr ▸ hr)
  have hg : g ∈ Submodule.span k (b '' {s | b s ∈ N}) := by
    have : g = c⁻¹ • b s - c⁻¹ • r := by
      rw [← hvr, smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul, add_sub_cancel_right]
    rw [this]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, hbN, rfl⟩))
      (Submodule.smul_mem _ _ (hspanR hr))
  calc N = F.endpointSpan (k := k) x y g := hNU
    _ = (k ∙ g) ⊔ R := F.endpointSpan_eq hgC
    _ ≤ _ := sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hg) hspanR

include hb in
theorem span_transversal_fin (hA : (Set.univ : Set (TwoSidedIdeal A)).Finite) :
    Submodule.span k (Set.range b) = ⊤ := by
  refine eq_top_iff.2 fun a _ ↦ ?_
  rw [F.eq_sum_corners a]
  refine Submodule.sum_mem _ fun x _ ↦ Submodule.sum_mem _ fun y _ ↦ ?_
  exact Submodule.span_mono (Set.image_subset_range _ _)
    (F.le_span_transversal_fin (k := k) hb hA _ _ rfl (F.corner_isEndpoint x y) (F.eAe_mem_corner x y a))

include hb in
theorem linearIndependent_transversal_fin (hA : (Set.univ : Set (TwoSidedIdeal A)).Finite) :
    LinearIndependent k b := by
  classical
  refine linearIndependent_iff'.2 fun S g hsum s₀ hs₀ ↦ ?_
  by_contra hg₀
  obtain ⟨x, y, hx, -, -⟩ := F.transversal_spec hb s₀
  set T := S.filter fun s ↦ g s ≠ 0 ∧ b s ∈ F.corner (k := k) x y
  have hT : (T.image fun s ↦ F.endpointSpan (k := k) x y (b s) : Set (Submodule k A)).Nonempty :=
    ⟨_, Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hs₀, hg₀, hx⟩))⟩
  obtain ⟨M, hM⟩ := (T.image fun s ↦ F.endpointSpan (k := k) x y (b s)).finite_toSet.exists_maximal hT
  obtain ⟨s₁, hs₁T, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hM.1)
  obtain ⟨hs₁S, hg₁, hs₁⟩ := Finset.mem_filter.1 hs₁T
  obtain ⟨-, -, -, hs₁0, -⟩ := F.transversal_spec hb s₁
  -- the corner part of the relation
  have hproj : ∑ s ∈ S.filter fun s ↦ b s ∈ F.corner (k := k) x y, g s • b s = 0 := by
    have h2 : ∀ s ∈ S, F.e x * (g s • b s) * F.e y =
        if b s ∈ F.corner (k := k) x y then g s • b s else 0 := by
      intro s _
      obtain ⟨x', y', hs', -, -⟩ := F.transversal_spec hb s
      rw [mul_smul_comm, smul_mul_assoc, F.proj_corner_of_mem hs', smul_ite, smul_zero]
    have := congrArg (fun z ↦ F.e x * z * F.e y) hsum
    rw [Finset.mul_sum, Finset.sum_mul, mul_zero, zero_mul, Finset.sum_congr rfl h2,
      ← Finset.sum_filter] at this
    exact this
  have hmem : s₁ ∈ S.filter fun s ↦ b s ∈ F.corner (k := k) x y := Finset.mem_filter.2 ⟨hs₁S, hs₁⟩
  rw [← Finset.add_sum_erase _ _ hmem] at hproj
  have hrest : ∑ s ∈ (S.filter fun s ↦ b s ∈ F.corner (k := k) x y).erase s₁, g s • b s ∈
      F.endpointRadical (k := k) x y (b s₁) := by
    refine Submodule.sum_mem _ fun s hs ↦ ?_
    obtain ⟨hss₁, hs⟩ := Finset.mem_erase.1 hs
    obtain ⟨hsS, hsC⟩ := Finset.mem_filter.1 hs
    by_cases hgs : g s = 0
    · rw [hgs, zero_smul]; exact Submodule.zero_mem _
    refine Submodule.smul_mem _ _ ?_
    have hsT : s ∈ T := Finset.mem_filter.2 ⟨hsS, hgs, hsC⟩
    have hU := F.isEndpoint_endpointSpan hsC
    have hU₁ := F.isEndpoint_endpointSpan hs₁
    have hle : F.endpointSpan (k := k) x y (b s) ≤ F.endpointSpan (k := k) x y (b s₁) := by
      rcases (F.isChain_subbimodules_fin (k := k) hA x y).total hU hU₁ with h | h
      · exact h
      · exact hM.2 (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hsT)) h
    have hnot : b s₁ ∉ F.endpointSpan (k := k) x y (b s) := fun h ↦
      hss₁ (F.transversal_ext_fin (k := k) hb hA hsC hs₁ (le_antisymm hle (F.endpointSpan_le hU h)))
    exact F.le_endpointRadical_fin (k := k) hA hs₁ hU hle hnot (F.mem_endpointSpan_self hsC)
  have h1 : g s₁ • b s₁ ∈ F.endpointRadical (k := k) x y (b s₁) := by
    have : g s₁ • b s₁ = -∑ s ∈ (S.filter fun s ↦ b s ∈ F.corner (k := k) x y).erase s₁,
        g s • b s := eq_neg_of_add_eq_zero_left hproj
    rw [this]
    exact Submodule.neg_mem _ hrest
  apply F.not_mem_endpointRadical hs₁ hs₁0
  have := Submodule.smul_mem _ (g s₁)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hg₁, one_smul] at this

include hb in
/-- **Corollary 3.3.** -/
theorem rayTransversal_isBasis_fin (hA : (Set.univ : Set (TwoSidedIdeal A)).Finite) :
    LinearIndependent k b ∧ Submodule.span k (Set.range b) = ⊤ ∧
      ∀ I : TwoSidedIdeal A, ∀ a : A, a ∈ I ↔ a ∈ Submodule.span k (b '' {r | b r ∈ I}) := by
  refine ⟨F.linearIndependent_transversal_fin (k := k) hb hA, F.span_transversal_fin (k := k) hb hA, fun I a ↦ ⟨fun ha ↦ ?_,
    fun ha ↦ ?_⟩⟩
  · set Iₛ := idealSubmodule (k := k) I
    rw [F.eq_sum_corners a]
    refine Submodule.sum_mem _ fun x _ ↦ Submodule.sum_mem _ fun y _ ↦ ?_
    have hN : F.IsEndpointSubbimodule x y (F.corner (k := k) x y ⊓ Iₛ) :=
      ⟨inf_le_left, fun c hc n hn ↦ ⟨F.corner_mul_corner hc hn.1, I.mul_mem_left _ _ hn.2⟩,
        fun c hc n hn ↦ ⟨F.corner_mul_corner hn.1 hc, I.mul_mem_right _ _ hn.2⟩⟩
    have hmem : F.e x * a * F.e y ∈ F.corner (k := k) x y ⊓ Iₛ :=
      ⟨F.eAe_mem_corner x y a, I.mul_mem_right _ _ (I.mul_mem_left _ _ ha)⟩
    exact Submodule.span_mono (Set.image_mono fun s hs ↦ hs.2)
      (F.le_span_transversal_fin (k := k) hb hA _ _ rfl hN hmem)
  · have : Submodule.span k (b '' {r | b r ∈ I}) ≤ idealSubmodule (k := k) I :=
      Submodule.span_le.2 (by rintro _ ⟨r, hr, rfl⟩; exact hr)
    exact this ha

end PrimitiveIdempotents

end LargeIndecomposable
