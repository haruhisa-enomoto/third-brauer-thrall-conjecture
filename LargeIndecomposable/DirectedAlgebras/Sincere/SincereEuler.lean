module

public import LargeIndecomposable.DirectedAlgebras.Sincere.SincereDirecting

/-!
# Consequences for a sincere directing module

Let `U` be a sincere directing module over a directed algebra.

* **The minimum of the dimension vector is reached at a source or a sink** (`exists_min_extreme`).
  This replaces the use of homogeneous modules in Bongartz's Lemma 4.
* The kernel of a cover of any module is, up to a projective syzygy, of projective dimension at
  most one (`isProjSummand_syz`). So the global dimension is at most two, and
  `⟨X, Y⟩ ≥ dim Hom(X, Y) - dim Ext¹(X, Y)` (`euler_ge`).
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

/-- The action of `e_b c e_a` from `e_a U` to `e_b U`. -/
def actE (U : FDMod k A) (a b : D.ι) (c : A) : eSub U (D.e a) →ₗ[k] eSub U (D.e b) where
  toFun u := ⟨(D.e b * c * D.e a) • (u : U), by
    change D.e b • (D.e b * c * D.e a) • (u : U) = _
    rw [← mul_smul, ← mul_assoc, ← mul_assoc, D.e_mul_e]⟩
  map_add' x y := Subtype.ext (smul_add _ _ _)
  map_smul' c' x := Subtype.ext (by
    change (D.e b * c * D.e a) • (c' • (x : U)) = c' • ((D.e b * c * D.e a) • (x : U))
    rw [smul_comm])

lemma actE_coe (a b : D.ι) (c : A) (u : eSub U (D.e a)) :
    ((actE U a b c u : eSub U (D.e b)) : U) = (D.e b * c * D.e a) • (u : U) := rfl

lemma actE_comp (a b z : D.ι) (c c' : A) (u : eSub U (D.e a)) :
    actE U b z c' (actE U a b c u) = actE U a z (c' * D.e b * c) u := by
  apply Subtype.ext
  rw [actE_coe, actE_coe, actE_coe, ← mul_smul]
  congr 1
  calc (D.e z * c' * D.e b) * (D.e b * c * D.e a)
      = D.e z * c' * (D.e b * D.e b) * c * D.e a := by simp only [mul_assoc]
    _ = _ := by rw [D.e_mul_e]; simp only [mul_assoc]

lemma actE_one_bijective (a : D.ι) : Function.Bijective (actE U a a 1) := by
  have h : ∀ u, actE U a a 1 u = u := fun u ↦ by
    apply Subtype.ext
    rw [actE_coe, mul_one, D.e_mul_e]
    exact u.2
  exact ⟨fun x y hxy ↦ by rwa [h, h] at hxy, fun u ↦ ⟨u, h u⟩⟩

/-- `x` is a sink: nothing leaves it. -/
def IsSink (D : DirData k A) (x : D.ι) : Prop := ∀ y, y ≠ x → ∀ a, D.e y * a * D.e x = 0

/-- `x` is a source: nothing enters it. -/
def IsSource (D : DirData k A) (x : D.ι) : Prop := ∀ y, y ≠ x → ∀ a, D.e x * a * D.e y = 0

/-- **Lemma 4 for `actE`.** -/
theorem actE_mono_or_epi (hT : ∀ x, x ∈ D.T) (hU : Directing U) (hs : Sincere D U) {x y : D.ι}
    (hxy : x ≠ y) (a : A) (hv : D.e y * a * D.e x ≠ 0) :
    Function.Injective (actE U x y a) ∨ Function.Surjective (actE U x y a) := by
  rcases mono_or_epi (D := D) hT hU hs hxy a hv with h | h
  · refine Or.inl ((injective_iff_map_eq_zero _).2 fun u hu ↦ Subtype.ext ?_)
    exact h u u.2 (congrArg Subtype.val hu)
  · refine Or.inr fun w ↦ ?_
    obtain ⟨u, hu1, hu2⟩ := h w w.2
    exact ⟨⟨u, hu1⟩, Subtype.ext hu2⟩

/-- **Lemma 5: the minimum of the dimension vector is reached at a source or a sink.** -/
theorem exists_min_extreme (hT : ∀ x, x ∈ D.T) (hU : Directing U) (hs : Sincere D U) (m : ℕ)
    (hm : ∀ x, m ≤ finrank k (eSub U (D.e x))) (x₀ : D.ι)
    (hx₀ : finrank k (eSub U (D.e x₀)) = m) :
    ∃ x, finrank k (eSub U (D.e x)) = m ∧ (IsSink D x ∨ IsSource D x) := by
  classical
  let d : D.ι → ℕ := fun x ↦ finrank k (eSub U (D.e x))
  let L : Finset D.ι := Finset.univ.filter fun x ↦ d x = m
  obtain ⟨a₀, ha₀, hmax⟩ := L.exists_max_image D.depth ⟨x₀, by simpa [L, d] using hx₀⟩
  have ha₀m : d a₀ = m := (Finset.mem_filter.1 ha₀).2
  let S : Finset D.ι := L.filter fun z ↦ ∃ c, Function.Bijective (actE U a₀ z c)
  have ha₀S : a₀ ∈ S := Finset.mem_filter.2 ⟨ha₀, 1, actE_one_bijective a₀⟩
  obtain ⟨a₁, ha₁, hmin⟩ := S.exists_min_image D.depth ⟨a₀, ha₀S⟩
  obtain ⟨ha₁L, c₀, hc₀⟩ := Finset.mem_filter.1 ha₁
  have ha₁m : d a₁ = m := (Finset.mem_filter.1 ha₁L).2
  by_contra H
  push Not at H
  have hnsrc : ¬IsSource D a₀ := fun h ↦ (H a₀ ha₀m).2 h
  have hnsnk : ¬IsSink D a₁ := fun h ↦ (H a₁ ha₁m).1 h
  simp only [IsSource, IsSink, not_forall] at hnsrc hnsnk
  obtain ⟨y, hy, c, hc⟩ := hnsrc
  obtain ⟨y', hy', c', hc'⟩ := hnsnk
  -- `y` and `y'` have dimension above the minimum
  have hdy : m < d y := by
    refine lt_of_le_of_ne (hm y) fun h ↦ ?_
    have h1 := hmax y (by simpa [L, d] using h.symm)
    have h2 := D.depth_lt hy c hc
    omega
  have hdy' : m < d y' := by
    refine lt_of_le_of_ne (hm y') fun h ↦ ?_
    have hfr : finrank k (eSub U (D.e a₁)) = finrank k (eSub U (D.e y')) := by
      change d a₁ = d y'
      omega
    have hb : Function.Bijective (actE U a₁ y' c') := by
      rcases actE_mono_or_epi hT hU hs (Ne.symm hy') c' hc' with h1 | h1
      · exact ⟨h1, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 h1⟩
      · exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).2 h1, h1⟩
    have hmem : y' ∈ S := by
      refine Finset.mem_filter.2 ⟨by simpa [L, d] using h.symm, c' * D.e a₁ * c₀, ?_⟩
      have : (actE U a₀ y' (c' * D.e a₁ * c₀)) = (actE U a₁ y' c') ∘ (actE U a₀ a₁ c₀) :=
        funext fun u ↦ (actE_comp a₀ a₁ y' c₀ c' u).symm
      rw [this]
      exact hb.comp hc₀
    have h1 := hmin y' hmem
    have h2 := D.depth_lt (Ne.symm hy') c' hc'
    omega
  have hfin : ∀ {a b : D.ι} (f : eSub U (D.e a) →ₗ[k] eSub U (D.e b)),
      Function.Injective f → d a ≤ d b := fun f hf ↦ LinearMap.finrank_le_finrank_of_injective hf
  have hfsur : ∀ {a b : D.ι} (f : eSub U (D.e a) →ₗ[k] eSub U (D.e b)),
      Function.Surjective f → d b ≤ d a := fun f hf ↦ LinearMap.finrank_le_finrank_of_surjective hf
  -- the first map is onto, the last one is into
  have hsurj : Function.Surjective (actE U y a₀ c) := by
    rcases actE_mono_or_epi hT hU hs hy c hc with h1 | h1
    · have := hfin _ h1
      omega
    · exact h1
  have hinj : Function.Injective (actE U a₁ y' c') := by
    rcases actE_mono_or_epi hT hU hs (Ne.symm hy') c' hc' with h1 | h1
    · exact h1
    · have := hfsur _ h1
      omega
  let w : A := c' * D.e a₁ * c₀ * D.e a₀ * c
  have hcomp : ∀ u, actE U y y' w u = actE U a₁ y' c' (actE U a₀ a₁ c₀ (actE U y a₀ c u)) :=
    fun u ↦ by rw [actE_comp, actE_comp]
  have hw : D.e y' * w * D.e y ≠ 0 := by
    intro h0
    obtain ⟨t, ht⟩ := hs a₀
    let t' : eSub U (D.e a₀) := ⟨D.e a₀ • t, by
      change D.e a₀ • D.e a₀ • t = _
      rw [← mul_smul, D.e_mul_e]⟩
    obtain ⟨u, hu⟩ := hsurj t'
    have h1 : actE U y y' w u = 0 := by
      apply Subtype.ext
      rw [actE_coe, h0, zero_smul]
      rfl
    rw [hcomp, hu] at h1
    have h2 := hc₀.1 (hinj (h1.trans (map_zero _).symm) |>.trans (map_zero _).symm)
    exact ht (congrArg Subtype.val h2)
  have hne : y ≠ y' := by
    rintro rfl
    have h1 := D.depth_lt hy c hc
    have h2 := D.depth_lt (Ne.symm hy') c' hc'
    have h3 := hmin a₀ ha₀S
    omega
  rcases actE_mono_or_epi hT hU hs hne w hw with h1 | h1
  · have hinj1 : Function.Injective (actE U y a₀ c) := fun p q hpq ↦ h1 (by
      rw [hcomp, hcomp, hpq])
    have := hfin _ hinj1
    omega
  · have hsurj1 : Function.Surjective (actE U a₁ y' c') := fun z ↦ by
      obtain ⟨u, hu⟩ := h1 z
      exact ⟨_, (hcomp u).symm.trans hu⟩
    have := hfsur _ hsurj1
    omega

/-! ### Global dimension -/

lemma isProjL_sumProj (D : DirData k A) (l : List D.ι) : IsProjL (sumProj D l) := by
  intro X Y q hq φ
  obtain ⟨g, hg⟩ := sumProj_lift D (show X ⟶ Y from (FDMod.ofLin q)) hq l (show _ ⟶ Y from (FDMod.ofLin φ))
  exact ⟨g, ((FDMod.comp_eq_iff _ _ _).1 hg)⟩

lemma exists_iso_proj (hT : ∀ x, x ∈ D.T) :
    ∀ (l : List D.ι) (t : (decompSumProj D hT l).ι),
      ∃ i, IsoM ((decompSumProj D hT l).obj t) (projE (k := k) (D.idem i))
  | [], t => t.elim
  | i :: _, .inl _ => ⟨i, ⟨𝟙 _, Function.bijective_id⟩⟩
  | _ :: l, .inr t => exists_iso_proj hT l t

lemma exists_proj_hom_ne (hs : Sincere D U) (i : D.ι) :
    ∃ f : projE (k := k) (D.idem i) ⟶ U, FDMod.lin f ≠ 0 := by
  obtain ⟨u, hu⟩ := hs i
  refine ⟨(FDMod.ofLin (show projE (k := k) (D.idem i) →ₗ[A] U from
    { toFun := fun b ↦ (b : A) • u
      map_add' := fun a b ↦ add_smul _ _ _
      map_smul' := fun a b ↦ mul_smul _ _ _ })), fun h0 ↦ hu ?_⟩
  exact LinearMap.congr_fun h0 (genP i)

/-- **Indecomposable submodules of projectives are projective or predecessors of `U`.** -/
theorem dirGood_of_embed (hT : ∀ x, x ∈ D.T) (hU : Directing U) (hs : Sincere D U) {W : FDMod k A}
    (hW : IsInd W) (l : List D.ι) (φ : W →ₗ[A] sumProj D l) (hφ : Function.Injective φ) :
    DirGood D U W := by
  classical
  obtain ⟨t, ht⟩ : ∃ t, FDMod.lin ((decompSumProj D hT l).proj t) ∘ₗ φ ≠ 0 := by
    by_contra hall
    push Not at hall
    haveI := hW.2
    obtain ⟨u, hu⟩ := exists_ne (0 : W)
    apply hu
    apply hφ
    rw [map_zero]
    have hs' := LinearMap.congr_fun (decompSumProj D hT l).sum_id (φ u)
    rw [LinearMap.sum_apply, LinearMap.id_apply] at hs'
    rw [← hs']
    exact Finset.sum_eq_zero fun t _ ↦ by
      have := LinearMap.congr_fun (hall t) u
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this ⊢
      rw [this, map_zero]
  have hZ : IsInd ((decompSumProj D hT l).obj t) :=
    ⟨(decompSumProj D hT l).indec t, (decompSumProj D hT l).nt t⟩
  by_cases hb : Function.Bijective (FDMod.lin ((decompSumProj D hT l).proj t) ∘ₗ φ)
  · left
    let e := LinearEquiv.ofBijective _ hb
    exact (isProjSummand_decompSumProj D hT l t).of_splitMono D
      ((FDMod.ofLin (show W →ₗ[A] (decompSumProj D hT l).obj t from
        FDMod.lin ((decompSumProj D hT l).proj t) ∘ₗ φ)))
      ((FDMod.ofLin (show (decompSumProj D hT l).obj t →ₗ[A] W from e.symm.toLinearMap)))
      (FDMod.hom_ext ((LinearMap.ext fun x ↦ e.symm_apply_apply x)))
  · right
    left
    have h1 : Reach₁ W ((decompSumProj D hT l).obj t) :=
      Reach₁.step hW hZ (FDMod.ofLin ((FDMod.lin ((decompSumProj D hT l).proj t) ∘ₗ φ))) ht hb
    obtain ⟨i, g, hg⟩ := exists_iso_proj hT l t
    obtain ⟨f, hf⟩ := exists_proj_hom_ne hs i
    have hb0 : FDMod.lin (g ≫ f) ≠ 0 := by
      intro h0
      apply hf
      refine LinearMap.ext fun y ↦ ?_
      obtain ⟨x, rfl⟩ := hg.2 y
      exact LinearMap.congr_fun h0 x
    by_cases hb2 : Function.Bijective (FDMod.lin (g ≫ f))
    · exact h1.trans_iso hU.1 ⟨g ≫ f, hb2⟩
    · exact h1.trans (Reach₁.step hZ hU.1 (g ≫ f) hb0 hb2)

/-- Submodules of projectives have no extensions by cosyzygies. -/
theorem extVanish_cosyz_of_embed (hT : ∀ x, x ∈ D.T) (hU : Directing U) (hs : Sincere D U)
    {K : FDMod k A} (l : List D.ι) (f : K →ₗ[A] sumProj D l) (hf : Function.Injective f)
    (Y : FDMod k A) :
    ExtVanish K (FDMod.ofQuot (envJ D Y) (LinearMap.range (envMap (D := D) Y))) := by
  obtain ⟨d⟩ := FDMod.exists_decomp K
  refine extVanish_of_decomp d fun j ↦ ?_
  have hW : IsInd (d.obj j) := ⟨d.indec j, d.nt j⟩
  have hinc : Function.Injective (FDMod.lin (d.inc j)) :=
    Function.LeftInverse.injective fun x ↦ LinearMap.congr_fun (d.retr j) x
  rcases dirGood_of_embed hT hU hs hW l (f ∘ₗ FDMod.lin (d.inc j)) (hf.comp hinc) with h | h | h
  · exact h.extVanish D _
  · exact extVanish_cosyz (D := D) hT hU hs hW (Or.inl h) Y
  · exact extVanish_cosyz (D := D) hT hU hs hW (Or.inr h) Y

/-- **The syzygy of a submodule of a projective is projective.** -/
theorem isProjSummand_syz (hT : ∀ x, x ∈ D.T) (hU : Directing U) (hs : Sincere D U)
    {K : FDMod k A} (l : List D.ι) (f : K →ₗ[A] sumProj D l) (hf : Function.Injective f) :
    IsProjSummand D (syz D K) := by
  let L := syz D K
  have hv : ∀ Y : FDMod k A, ExtVanish L Y := fun Y ↦
    extVanish_syz_of_cosyz (D := D) (LinearMap.ker (sumMap D K (coverList D K))).subtype
      (sumMap D K (coverList D K)) Subtype.val_injective (sumMap_coverList_surjective D K)
      (Submodule.range_subtype _) (isProjL_sumProj D _) Y
      (extVanish_cosyz_of_embed hT hU hs l f hf Y)
  obtain ⟨σ, hσ⟩ := hv (syz D L) (sumProj D ((coverList D L).map Sigma.fst))
    (LinearMap.ker (sumMap D L (coverList D L))).subtype (sumMap D L (coverList D L))
    Subtype.val_injective (sumMap_coverList_surjective D L) (Submodule.range_subtype _)
  exact ⟨(coverList D L).map Sigma.fst, (FDMod.ofLin σ), (FDMod.ofLin (sumMap D L (coverList D L))), ((FDMod.comp_eq_id_iff _ _).2 hσ)⟩

/-- Rank–nullity for restriction along the kernel of a surjection. -/
lemma finrank_hom_exact {K P Z : FDMod k A} (f : K →ₗ[A] P) (g : P →ₗ[A] Z)
    (hg : Function.Surjective g) (hex : LinearMap.range f = LinearMap.ker g) (Y : FDMod k A) :
    finrank k (P →ₗ[A] Y) = finrank k (Z →ₗ[A] Y) +
      finrank k (LinearMap.range (precomp k (Y := Y) f)) := by
  have hinj : Function.Injective (precomp k (Y := Y) g) := by
    intro φ ψ h
    refine LinearMap.ext fun z ↦ ?_
    obtain ⟨p, rfl⟩ := hg z
    exact LinearMap.congr_fun h p
  have hrange : LinearMap.range (precomp k (Y := Y) g) = LinearMap.ker (precomp k (Y := Y) f) := by
    ext φ
    constructor
    · rintro ⟨ψ, rfl⟩
      rw [LinearMap.mem_ker]
      refine LinearMap.ext fun p ↦ ?_
      change ψ (g (f p)) = 0
      rw [mem_ker_of_range hex, map_zero]
    · intro hφ
      obtain ⟨ψ, hψ⟩ := exists_factor f g hg hex φ hφ
      exact ⟨ψ, hψ⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker (precomp k (Y := Y) f)
  rw [← hrange, LinearMap.finrank_range_of_inj hinj] at h1
  omega

/-- `⟨K, Y⟩ ≤ dim Hom(K, Y)` for submodules of projectives. -/
theorem euler_le_hom (hT : ∀ x, x ∈ D.T) (hU : Directing U) (hs : Sincere D U)
    {K : FDMod k A} (l : List D.ι) (f : K →ₗ[A] sumProj D l) (hf : Function.Injective f)
    (Y : FDMod k A) :
    euler D (dimZ D K) (dimZ D Y) ≤ finrank k (K →ₗ[A] Y) := by
  obtain ⟨l', s, r, hsr⟩ := isProjSummand_syz hT hU hs l f hf
  have hLe : EulerProj D (syz D K) := eulerProj_of_summand D hT l' s r hsr
  have hPe := eulerProj_sumProj D hT ((coverList D K).map Sigma.fst)
  have hd := dimZ_exact D (M := syz D K) (N := sumProj D ((coverList D K).map Sigma.fst)) (L := K)
    (LinearMap.ker (sumMap D K (coverList D K))).subtype
    (sumMap D K (coverList D K)) Subtype.val_injective (sumMap_coverList_surjective D K)
    (Submodule.range_subtype _)
  have hK : dimZ D K = dimZ D (sumProj D ((coverList D K).map Sigma.fst)) -
      dimZ D (syz D K) := by rw [hd]; abel
  rw [hK, euler_sub, hPe Y, hLe Y]
  have h1 := finrank_hom_exact (K := syz D K) (P := sumProj D ((coverList D K).map Sigma.fst))
    (Z := K) (LinearMap.ker (sumMap D K (coverList D K))).subtype
    (sumMap D K (coverList D K)) (sumMap_coverList_surjective D K) (Submodule.range_subtype _) Y
  have h2 : finrank k (LinearMap.range (precomp k (Y := Y)
      (LinearMap.ker (sumMap D K (coverList D K))).subtype)) ≤
      finrank k (syz D K →ₗ[A] Y) := by
    haveI : FiniteDimensional k (syz D K) := (syz D K).isFD
    exact Submodule.finrank_le _
  have h3 : finrank k (sumProj D ((coverList D K).map Sigma.fst) →ₗ[A] Y) =
      finrank k (K →ₗ[A] Y) + finrank k (LinearMap.range (precomp k (Y := Y)
      (LinearMap.ker (sumMap D K (coverList D K))).subtype)) := h1
  omega

/-- **The Euler inequality** (`E` of the note): with `f : syz X → P` the cover of `X`,
`dim Hom(X, Y) - dim coker Hom(f, Y) ≤ ⟨X, Y⟩`. -/
theorem euler_ge (hT : ∀ x, x ∈ D.T) (hU : Directing U) (hs : Sincere D U) (X Y : FDMod k A) :
    (finrank k (X →ₗ[A] Y) : ℤ) + finrank k (LinearMap.range (precomp k (Y := Y)
      (LinearMap.ker (sumMap D X (coverList D X))).subtype)) - finrank k (syz D X →ₗ[A] Y) ≤
      euler D (dimZ D X) (dimZ D Y) := by
  have hPe := eulerProj_sumProj D hT ((coverList D X).map Sigma.fst)
  have hd := dimZ_exact D (M := syz D X) (N := sumProj D ((coverList D X).map Sigma.fst)) (L := X)
    (LinearMap.ker (sumMap D X (coverList D X))).subtype
    (sumMap D X (coverList D X)) Subtype.val_injective (sumMap_coverList_surjective D X)
    (Submodule.range_subtype _)
  have hX : dimZ D X = dimZ D (sumProj D ((coverList D X).map Sigma.fst)) -
      dimZ D (syz D X) := by rw [hd]; abel
  have h1 := euler_le_hom (K := syz D X) hT hU hs ((coverList D X).map Sigma.fst)
    (LinearMap.ker (sumMap D X (coverList D X))).subtype Subtype.val_injective Y
  have h2 := finrank_hom_exact (K := syz D X) (P := sumProj D ((coverList D X).map Sigma.fst))
    (Z := X) (LinearMap.ker (sumMap D X (coverList D X))).subtype
    (sumMap D X (coverList D X)) (sumMap_coverList_surjective D X) (Submodule.range_subtype _) Y
  have h3 : finrank k (sumProj D ((coverList D X).map Sigma.fst) →ₗ[A] Y) =
      finrank k (X →ₗ[A] Y) + finrank k (LinearMap.range (precomp k (Y := Y)
      (LinearMap.ker (sumMap D X (coverList D X))).subtype)) := h2
  rw [hX, euler_sub, hPe Y]
  omega

/-- **The Euler form of a rigid pair.** If `Ext¹(X, Y) = 0`, then `dim Hom(X, Y) ≤ ⟨X, Y⟩`. -/
theorem hom_le_euler (hT : ∀ x, x ∈ D.T) (hU : Directing U) (hs : Sincere D U) {X Y : FDMod k A}
    (hv : ExtVanish X Y) : (finrank k (X →ₗ[A] Y) : ℤ) ≤ euler D (dimZ D X) (dimZ D Y) := by
  have h := euler_ge hT hU hs X Y
  have hr : LinearMap.range (precomp k (Y := Y)
      (LinearMap.ker (sumMap D X (coverList D X))).subtype) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro φ
    obtain ⟨ψ, hψ⟩ := extend_of_extVanish (P₀ := sumProj D ((coverList D X).map Sigma.fst))
      (P₁ := syz D X) (Z := X) (LinearMap.ker (sumMap D X (coverList D X))).subtype
      (sumMap D X (coverList D X)) Subtype.val_injective (sumMap_coverList_surjective D X)
      (Submodule.range_subtype _) hv φ
    exact ⟨ψ, hψ⟩
  rw [hr, finrank_top] at h
  have e : finrank k (LinearMap.ker (sumMap D X (coverList D X)) →ₗ[A] Y) =
      finrank k (syz D X →ₗ[A] Y) := rfl
  omega

end DirData

end LargeIndecomposable.AR
