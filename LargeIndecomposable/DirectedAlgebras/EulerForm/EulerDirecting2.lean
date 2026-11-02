module

public import LargeIndecomposable.DirectedAlgebras.EulerForm.EulerDirecting

/-!
# The Euler form of a directing module (main theorem)

Fix a directing module `M`. An indecomposable is good if it is a projective summand, a
predecessor of `M`, or isomorphic to `M`; good modules have no nonsplit extensions by `M`
(`DirGood.extVanish`). The summands of the syzygy of a good module are good (`good_syz`). Covering a
module with good summands summand by summand and inducting on depth gives
`⟨dim Z, dim M⟩ = dim Hom(Z, M)` (`euler_good`), in particular `χ(dim M) = dim End M`
(`euler_directing`; ASS IX.1.4–1.5).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (D : DirData k A)

lemma Reach₁.trans_iso {X Y Z : FDMod k A} (h : Reach₁ X Y) (hZ : IsInd Z) (e : IsoM Y Z) :
    Reach₁ X Z := by
  induction h with
  | step hX hY f hf hnb =>
    obtain ⟨g, hg⟩ := e
    refine Reach₁.step hX hZ (f ≫ g) (fun h0 ↦ hf ?_) (fun hb ↦ hnb ?_)
    · ext x
      apply hg.1
      have := LinearMap.congr_fun h0 x
      simpa using this
    · have hc := (LinearEquiv.ofBijective (FDMod.lin g) hg).symm.bijective.comp hb
      have heq : ⇑(LinearEquiv.ofBijective (FDMod.lin g) hg).symm ∘ ⇑(FDMod.lin (f ≫ g)) =
          ⇑(FDMod.lin f) := funext fun x ↦
        (LinearEquiv.ofBijective (FDMod.lin g) hg).symm_apply_apply (FDMod.lin f x)
      rwa [heq] at hc
  | trans _ _ _ ih2 => exact Reach₁.trans ‹_› (ih2 e)

/-- Vanishing of extensions is invariant under isomorphism of the end term. -/
lemma ExtVanish.of_iso {X X' W : FDMod k A} (e : X ≃ₗ[A] X') (h : ExtVanish X W) :
    ExtVanish X' W := by
  intro E i p hi hp hex
  have hex' : LinearMap.range i = LinearMap.ker (e.symm.toLinearMap ∘ₗ p) := by
    rw [hex]
    ext x
    simp
  obtain ⟨s, hs⟩ := h E i (e.symm.toLinearMap ∘ₗ p) hi (e.symm.surjective.comp hp) hex'
  refine ⟨s ∘ₗ e.symm.toLinearMap, LinearMap.ext fun x ↦ ?_⟩
  have := LinearMap.congr_fun hs (e.symm x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at this ⊢
  exact e.symm.injective this

/-- Good indecomposables for a directing module `M`. -/
def DirGood (M U : FDMod k A) : Prop := IsProjSummand D U ∨ Reach₁ U M ∨ IsoM U M

/-- **DirGood modules have no nonsplit extensions by `M`.** -/
theorem DirGood.extVanish {M U : FDMod k A} (hM : Directing M) (hU : IsInd U) (h : DirGood D M U) :
    ExtVanish U M := by
  rcases h with h | h | ⟨g, hg⟩
  · exact h.extVanish D M
  · exact hM.extVanish_pred hU h
  · exact hM.extVanish.of_iso (LinearEquiv.ofBijective (FDMod.lin g) hg).symm

/-- Every component of the cover by bases is nonzero. -/
lemma sumMap_inc_ne_zero (hT : ∀ x, x ∈ D.T) (V : FDMod k A) :
    ∀ (L : List (Σ i : D.ι, eSub V (D.e i))), (∀ x ∈ L, (x.2 : V) ≠ 0) →
      ∀ t, sumMap D V L ∘ₗ FDMod.lin ((decompSumProj D hT (L.map Sigma.fst)).inc t) ≠ 0
  | [], _, t => t.elim
  | ⟨c, b⟩ :: L, hL, .inl _ => by
    intro h0
    apply hL ⟨c, b⟩ List.mem_cons_self
    have := LinearMap.congr_fun h0 ⟨D.e c, e_mem (D.idem c)⟩
    change (homProjEquiv (D.idem c) V).symm b ⟨D.e c, e_mem (D.idem c)⟩ + sumMap D V L 0 = 0
      at this
    rw [map_zero, add_zero, homProjEquiv_symm_apply] at this
    rw [← this]
    exact b.2.symm
  | ⟨c, b⟩ :: L, hL, .inr t => by
    intro h0
    apply sumMap_inc_ne_zero hT V L (fun x hx ↦ hL x (List.mem_cons_of_mem _ hx)) t
    refine LinearMap.ext fun y ↦ ?_
    have := LinearMap.congr_fun h0 y
    change (homProjEquiv (D.idem c) V).symm b 0 +
      sumMap D V L (FDMod.lin ((decompSumProj D hT (L.map Sigma.fst)).inc t) y) = 0 at this
    rw [map_zero, zero_add] at this
    exact this

lemma coverList_ne_zero (V : FDMod k A) : ∀ x ∈ coverList D V, (x.2 : V) ≠ 0 := by
  classical
  intro x hx
  unfold coverList at hx
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hi
  obtain ⟨t, rfl⟩ := List.mem_ofFn.1 hb
  intro h0
  exact (Module.finBasis k (eSub V (D.e i))).ne_zero t (Subtype.ext h0)

lemma isProjSummand_projE (i : D.ι) : IsProjSummand D (projE (k := k) (D.idem i)) :=
  ⟨[i], (FDMod.ofLin (show projE (k := k) (D.idem i) →ₗ[A] sumProj D [i] from LinearMap.inl A _ _)),
    (FDMod.ofLin (show sumProj D [i] →ₗ[A] projE (k := k) (D.idem i) from LinearMap.fst A _ _)), rfl⟩

lemma IsProjSummand.of_splitMono {U V : FDMod k A} (hV : IsProjSummand D V) (s : U ⟶ V)
    (r : V ⟶ U) (hsr : s ≫ r = 𝟙 U) : IsProjSummand D U := by
  obtain ⟨l, s', r', h'⟩ := hV
  refine ⟨l, s ≫ s', r' ≫ r, ?_⟩
  rw [Category.assoc, ← Category.assoc s' r' r, h', Category.id_comp, hsr]

lemma isProjSummand_decompSumProj (hT : ∀ x, x ∈ D.T) :
    ∀ (l : List D.ι) (t : (decompSumProj D hT l).ι), IsProjSummand D ((decompSumProj D hT l).obj t)
  | [], t => t.elim
  | i :: l, .inl _ => isProjSummand_projE D i
  | i :: l, .inr t => isProjSummand_decompSumProj hT l t

/-- **Summands of the syzygy of a good module are good.** -/
theorem good_syz (hT : ∀ x, x ∈ D.T) {M V : FDMod k A} (hMi : IsInd M) (hV : IsInd V)
    (hg : DirGood D M V)
    (d : Decomp (syz D V)) (j : d.ι) : DirGood D M (d.obj j) := by
  classical
  have hU : IsInd (d.obj j) := ⟨d.indec j, d.nt j⟩
  have hsplitU : d.inc j ≫ d.proj j = 𝟙 _ := ((FDMod.comp_eq_id_iff _ _).2 (d.retr j))
  by_cases hP : IsProjSummand D V
  · -- the cover splits, so the syzygy is a projective summand
    left
    obtain ⟨σ, hσ⟩ := hP.extVanish D (syz D V) (sumProj D ((coverList D V).map Sigma.fst))
      (LinearMap.ker (sumMap D V (coverList D V))).subtype (sumMap D V (coverList D V)) Subtype.val_injective
      (sumMap_coverList_surjective D V) (Submodule.range_subtype _)
    obtain ⟨r, hr⟩ := exists_retr_of_section (L := syz D V)
      (M := sumProj D ((coverList D V).map Sigma.fst)) (N := V)
      (LinearMap.ker (sumMap D V (coverList D V))).subtype
      (sumMap D V (coverList D V)) Subtype.val_injective (Submodule.range_subtype _) σ hσ
    have hK : IsProjSummand D (syz D V) :=
      ⟨(coverList D V).map Sigma.fst, (FDMod.ofLin ((LinearMap.ker (sumMap D V (coverList D V))).subtype)), (FDMod.ofLin (r)), ((FDMod.comp_eq_id_iff _ _).2 (hr))⟩
    exact hK.of_splitMono D (d.inc j) (d.proj j) hsplitU
  · let φ : d.obj j →ₗ[A] sumProj D ((coverList D V).map Sigma.fst) :=
      (LinearMap.ker (sumMap D V (coverList D V))).subtype ∘ₗ FDMod.lin (d.inc j)
    have hφ : Function.Injective φ := Subtype.val_injective.comp
      (Function.LeftInverse.injective fun x ↦ LinearMap.congr_fun (d.retr j) x)
    obtain ⟨t, ht⟩ : ∃ t, FDMod.lin ((decompSumProj D hT ((coverList D V).map Sigma.fst)).proj t) ∘ₗ φ ≠ 0 := by
      by_contra hall
      push Not at hall
      haveI := hU.2
      obtain ⟨u, hu⟩ := exists_ne (0 : d.obj j)
      apply hu
      apply hφ
      rw [map_zero]
      have hs := LinearMap.congr_fun (decompSumProj D hT ((coverList D V).map Sigma.fst)).sum_id (φ u)
      rw [LinearMap.sum_apply, LinearMap.id_apply] at hs
      rw [← hs]
      exact Finset.sum_eq_zero fun t _ ↦ by
        have := LinearMap.congr_fun (hall t) u
        simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this ⊢
        rw [this, map_zero]
    have hT' : IsInd ((decompSumProj D hT ((coverList D V).map Sigma.fst)).obj t) := ⟨(decompSumProj D hT ((coverList D V).map Sigma.fst)).indec t, (decompSumProj D hT ((coverList D V).map Sigma.fst)).nt t⟩
    let g₂ : (decompSumProj D hT ((coverList D V).map Sigma.fst)).obj t →ₗ[A] V := sumMap D V (coverList D V) ∘ₗ FDMod.lin ((decompSumProj D hT ((coverList D V).map Sigma.fst)).inc t)
    have hg₂ : g₂ ≠ 0 := sumMap_inc_ne_zero D hT V (coverList D V) (coverList_ne_zero D V) t
    have hnb₂ : ¬Function.Bijective g₂ := by
      intro hb
      apply hP
      let e := LinearEquiv.ofBijective g₂ hb
      exact (isProjSummand_decompSumProj D hT _ t).of_splitMono D
        ((FDMod.ofLin (show V →ₗ[A] (decompSumProj D hT ((coverList D V).map Sigma.fst)).obj t from e.symm.toLinearMap))) ((FDMod.ofLin (show (decompSumProj D hT ((coverList D V).map Sigma.fst)).obj t →ₗ[A] V from g₂)))
        (FDMod.hom_ext ((LinearMap.ext fun x ↦ e.apply_symm_apply x)))
    have hV2 : Reach₁ ((decompSumProj D hT ((coverList D V).map Sigma.fst)).obj t) V := Reach₁.step hT' hV (FDMod.ofLin (g₂)) hg₂ hnb₂
    by_cases hb₁ : Function.Bijective (FDMod.lin ((decompSumProj D hT ((coverList D V).map Sigma.fst)).proj t) ∘ₗ φ)
    · left
      let e := LinearEquiv.ofBijective _ hb₁
      exact (isProjSummand_decompSumProj D hT _ t).of_splitMono D
        ((FDMod.ofLin (show d.obj j →ₗ[A] (decompSumProj D hT ((coverList D V).map Sigma.fst)).obj t from FDMod.lin ((decompSumProj D hT ((coverList D V).map Sigma.fst)).proj t) ∘ₗ φ)))
        ((FDMod.ofLin (show (decompSumProj D hT ((coverList D V).map Sigma.fst)).obj t →ₗ[A] d.obj j from e.symm.toLinearMap)))
        (FDMod.hom_ext ((LinearMap.ext fun x ↦ e.symm_apply_apply x)))
    · right
      have hUV : Reach₁ (d.obj j) V :=
        Reach₁.trans (Reach₁.step hU hT' (FDMod.ofLin ((FDMod.lin ((decompSumProj D hT ((coverList D V).map Sigma.fst)).proj t) ∘ₗ φ))) ht hb₁) hV2
      rcases hg with h | h | h
      · exact absurd h hP
      · exact Or.inl (Reach₁.trans hUV h)
      · exact Or.inl (hUV.trans_iso hMi h)

omit [FiniteDimensional k A] in
/-- Extensions split if they split for each summand of a decomposition. -/
theorem extVanish_of_decomp {Z W : FDMod k A} (d : Decomp Z) (h : ∀ j, ExtVanish (d.obj j) W) :
    ExtVanish Z W := by
  classical
  intro E i p hi hp hex
  have hs : ∀ j, ∃ s : d.obj j →ₗ[A] E, p ∘ₗ s = FDMod.lin (d.inc j) := fun j ↦
    exists_lift_summand (FDMod.lin (d.inc j)) (FDMod.lin (d.proj j)) (d.retr j) (h j) i p hi hp hex
  choose s hs using hs
  refine ⟨∑ j, s j ∘ₗ FDMod.lin (d.proj j), LinearMap.ext fun x ↦ ?_⟩
  rw [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  simp only [LinearMap.comp_apply]
  have hx := LinearMap.congr_fun d.sum_id x
  rw [LinearMap.sum_apply, LinearMap.id_apply] at hx
  rw [LinearMap.id_apply]
  conv_rhs => rw [← hx]
  exact Finset.sum_congr rfl fun j _ ↦ LinearMap.congr_fun (hs j) _

lemma LivesBelow.of_inj {X Y : FDMod k A} {n : ℕ} (hY : LivesBelow D Y n) (f : X →ₗ[A] Y)
    (hf : Function.Injective f) : LivesBelow D X n := by
  intro x hx
  rw [eq_bot_iff]
  intro m hm
  rw [Submodule.mem_bot]
  apply hf
  rw [map_zero]
  have : f m ∈ eSub Y (D.e x) := by
    change D.e x • f m = f m
    rw [← map_smul, show D.e x • m = m from hm]
  rw [hY x hx] at this
  exact (Submodule.mem_bot k).1 this

lemma eq_zero_of_livesBelow_zero {Z : FDMod k A} (hZ : LivesBelow D Z 0) (z : Z) : z = 0 := by
  have hz : z = ∑ x, D.e x • z := by rw [← Finset.sum_smul, D.sum, one_smul]
  rw [hz]
  refine Finset.sum_eq_zero fun x _ ↦ ?_
  have : D.e x • z ∈ eSub Z (D.e x) := by
    change D.e x • D.e x • z = D.e x • z
    rw [← mul_smul, (D.idem x).eq]
  rw [hZ x (Nat.zero_le _)] at this
  exact (Submodule.mem_bot k).1 this

/-- **The Euler form against a directing module.** -/
theorem euler_good (hT : ∀ x, x ∈ D.T) {M : FDMod k A} (hM : Directing M) :
    ∀ (n : ℕ) (Z : FDMod k A), LivesBelow D Z n → ∀ dZ : Decomp Z,
      (∀ j, DirGood D M (dZ.obj j)) →
        euler D (dimZ D Z) (dimZ D M) = finrank k (Z →ₗ[A] M)
  | 0, Z, hZ, _, _ => by
    have h0 : ∀ z : Z, z = 0 := eq_zero_of_livesBelow_zero D hZ
    have hd : dimZ D Z = 0 := by
      funext x
      simp only [dimZ, Pi.zero_apply, Nat.cast_eq_zero]
      exact (Submodule.finrank_eq_zero (S := eSub Z (D.e x))).2 (hZ x (Nat.zero_le _))
    haveI : Subsingleton (Z →ₗ[A] M) :=
      ⟨fun f g ↦ LinearMap.ext fun z ↦ by rw [h0 z, map_zero, map_zero]⟩
    rw [hd, Module.finrank_zero_of_subsingleton]
    simp [euler]
  | n + 1, Z, hZ, dZ, hgood => by
    classical
    let V := dZ.obj
    let K : FDMod k A := FDMod.pi fun j ↦ syz D (V j)
    let P : FDMod k A := FDMod.pi fun j ↦ sumProj D ((coverList D (V j)).map Sigma.fst)
    let f : K →ₗ[A] P := LinearMap.pi fun j ↦
      (LinearMap.ker (sumMap D (V j) (coverList D (V j)))).subtype ∘ₗ
        LinearMap.proj (R := A) (φ := fun j ↦ syz D (V j)) j
    let g : P →ₗ[A] Z := ∑ j, FDMod.lin (dZ.inc j) ∘ₗ sumMap D (V j) (coverList D (V j)) ∘ₗ
      LinearMap.proj (R := A) (φ := fun j ↦ sumProj D ((coverList D (V j)).map Sigma.fst)) j
    have hprojg : ∀ i (p : P), FDMod.lin (dZ.proj i) (g p) =
        sumMap D (V i) (coverList D (V i)) (p i) := by
      intro i p
      simp only [g, LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
      rw [Finset.sum_eq_single i]
      · exact LinearMap.congr_fun (dZ.retr i) _
      · intro j _ hji
        exact LinearMap.congr_fun (dZ.orth j i hji) _
      · simp
    have hf : Function.Injective f := by
      intro a b h
      funext j
      exact Subtype.val_injective (congrFun h j)
    have hg : Function.Surjective g := by
      intro z
      choose p hp using fun j ↦ sumMap_coverList_surjective D (V j) (FDMod.lin (dZ.proj j) z)
      refine ⟨p, ?_⟩
      have hz := LinearMap.congr_fun dZ.sum_id z
      rw [LinearMap.sum_apply, LinearMap.id_apply] at hz
      conv_rhs => rw [← hz]
      simp only [g, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.coe_proj, Function.eval]
      exact Finset.sum_congr rfl fun j _ ↦ congrArg (FDMod.lin (dZ.inc j)) (hp j)
    have hex : LinearMap.range f = LinearMap.ker g := by
      ext p
      constructor
      · rintro ⟨q, rfl⟩
        rw [LinearMap.mem_ker]
        simp only [g, f, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.pi_apply,
          LinearMap.coe_proj, Function.eval]
        exact Finset.sum_eq_zero fun j _ ↦ by
          have hq : sumMap D (V j) (coverList D (V j)) ((q j : sumProj D _)) = 0 := (q j).2
          exact (congrArg (FDMod.lin (dZ.inc j)) hq).trans (map_zero _)
      · intro hp
        rw [LinearMap.mem_ker] at hp
        refine ⟨fun j ↦ ⟨p j, ?_⟩, rfl⟩
        rw [LinearMap.mem_ker, ← hprojg j p, hp, map_zero]
    have hPe : EulerProj D P := EulerProj.pi D fun j ↦ eulerProj_sumProj D hT _
    have hv : ExtVanish Z M := extVanish_of_decomp dZ fun j ↦
      (hgood j).extVanish D hM ⟨dZ.indec j, dZ.nt j⟩
    have hstep := euler_step D hPe f g hf hg hex hv
    -- the syzygy lives one depth lower and has good summands
    have hK : LivesBelow D K n := LivesBelow.pi D fun j ↦
      livesBelow_syz D hT (V j) n (hZ.of_inj D (FDMod.lin (dZ.inc j))
        (Function.LeftInverse.injective fun x ↦ LinearMap.congr_fun (dZ.retr j) x))
    let dK : ∀ j, Decomp (syz D (V j)) := fun j ↦ (FDMod.exists_decomp (syz D (V j))).some
    have hgK : ∀ c, DirGood D M ((Decomp.pi dK).obj c) := fun c ↦
      good_syz D hT hM.1 ⟨dZ.indec c.1, dZ.nt c.1⟩ (hgood c.1) (dK c.1) c.2
    have ih := euler_good hT hM n K hK (Decomp.pi dK) hgK
    rw [hstep, ih]
    ring

/-- **The Euler form of a directing module** (ASS IX.1.5): `χ(dim M) = dim End M`. -/
theorem euler_directing (hT : ∀ x, x ∈ D.T) {M : FDMod k A} (hM : Directing M) :
    euler D (dimZ D M) (dimZ D M) = finrank k (M →ₗ[A] M) :=
  euler_good D hT hM _ M (livesBelow_card D M) (Decomp.single hM.1)
    fun _ ↦ Or.inr (Or.inr ⟨𝟙 M, Function.bijective_id⟩)

end LargeIndecomposable.AR
