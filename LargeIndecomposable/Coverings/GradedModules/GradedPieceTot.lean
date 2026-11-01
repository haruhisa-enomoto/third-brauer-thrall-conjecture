module

public import LargeIndecomposable.Coverings.GradedModules.GradedPiece

/-!
# The total space of `grRep`

The cover object of a pair `(y, g)` is `cov y g = (y, g ≫ ℓ y)`; every cover object is
`cov a.y (gOf a)` (`cov_gOf`). The projection of `M` onto `W a` is `e_{a.y} ∘ proj_{g(a)}`
(`projW`). If `S` contains every cover object with `W a ≠ 0`, summing the components
identifies the total space of `grRep S` with `M` (`totEquiv`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits LargeIndecomposable.Graded RayQuiver Cover AR Classical FinQuiver

universe u

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} (ℓ : ∀ y : P, vtx x₀ ⟶ vtx y)

/-- The cover object of degree `g` over `y`. -/
def cov (y : P) (g : Pi1 x₀) : Cover x₀ := ⟨y, g.hom ≫ ℓ y⟩

lemma gOf_cov (y : P) (g : Pi1 x₀) : gOf ℓ (cov ℓ y g) = g := by
  apply Iso.ext
  change (g.hom ≫ ℓ y) ≫ inv (ℓ y) = g.hom
  simp

lemma cov_gOf (a : Cover x₀) : cov ℓ a.y (gOf ℓ a) = a := by
  obtain ⟨y, u⟩ := a
  change (⟨y, (u ≫ inv (ℓ y)) ≫ ℓ y⟩ : Cover x₀) = ⟨y, u⟩
  simp

lemma eq_of_y_gOf {a b : Cover x₀} (hy : a.y = b.y) (hg : gOf ℓ a = gOf ℓ b) : a = b := by
  rw [← cov_gOf ℓ a, ← cov_gOf ℓ b, hy, hg]

variable (k : Type u) [Field k]
variable {M : Type u} [AddCommGroup M] [Module (Linearization P k) M] [Module k M]
  [IsScalarTower k (Linearization P k) M] (μ : GrMod (rayGrAlg ℓ k) M)

/-- The projection of `M` onto `W a`. -/
def projW (a : Cover x₀) : M →ₗ[k] M where
  toFun m := morElt k (𝟙 a.y) • μ.proj (gOf ℓ a) m
  map_add' m n := by simp only [map_add, smul_add]
  map_smul' c m := by simp only [map_smul, RingHom.id_apply]; rw [smul_comm]

lemma idem_comm (y : P) (g : Pi1 x₀) (m : M) :
    μ.proj g (morElt k (𝟙 y) • m) = morElt k (𝟙 y) • μ.proj g m := by
  have h1 : (rayGrAlg ℓ k).Mem 1 (morElt k (𝟙 y)) := by
    have := morElt_mem_rayGrAlg ℓ k (𝟙 y) (IsRayCategory.id_ne_zero y)
    have e : rayDeg ℓ ⟨y, y, 𝟙 y, IsRayCategory.id_ne_zero y⟩ = 1 := rayDeg_id ℓ y
    rwa [e] at this
  have := μ.proj_smul h1 g m
  rwa [one_mul] at this

lemma projW_mem (a : Cover x₀) (m : M) : projW ℓ k μ a m ∈ W ℓ k μ a := by
  refine ⟨?_, ?_⟩
  · show morElt k (𝟙 a.y) • (morElt k (𝟙 a.y) • μ.proj (gOf ℓ a) m) =
      morElt k (𝟙 a.y) • μ.proj (gOf ℓ a) m
    rw [← mul_smul, morElt_mul, Category.id_comp]
  · show μ.proj (gOf ℓ a) (morElt k (𝟙 a.y) • μ.proj (gOf ℓ a) m) =
      morElt k (𝟙 a.y) • μ.proj (gOf ℓ a) m
    rw [idem_comm, Grading.proj_proj]

lemma projW_of_mem {a b : Cover x₀} {w : M} (hw : w ∈ W ℓ k μ b) :
    projW ℓ k μ a w = if a = b then w else 0 := by
  obtain ⟨h1, h2⟩ := hw
  change morElt k (𝟙 a.y) • μ.proj (gOf ℓ a) w = _
  split_ifs with hab
  · subst hab; rw [h2, h1]
  · by_cases hy : a.y = b.y
    · have hg : gOf ℓ a ≠ gOf ℓ b := fun hg ↦ hab (eq_of_y_gOf ℓ hy hg)
      rw [μ.proj_of_mem h2 hg, smul_zero]
    · rw [← h1, idem_comm, ← mul_smul, morElt_mul_ne k (𝟙 b.y) (𝟙 a.y) (Ne.symm hy),
        zero_smul]

/-- The cover objects that can carry `M`. -/
def suppSet : Finset (Cover x₀) :=
  (Finset.univ ×ˢ μ.supp).image fun p : P × Pi1 x₀ ↦ cov ℓ p.1 p.2

/-- **`M` is the sum of its pieces.** -/
lemma sum_projW (m : M) : ∑ a ∈ suppSet ℓ k μ, projW ℓ k μ a m = m := by
  have hinj : Set.InjOn (fun p : P × Pi1 x₀ ↦ cov ℓ p.1 p.2)
      ↑(Finset.univ ×ˢ μ.supp : Finset (P × Pi1 x₀)) := by
    rintro ⟨y, g⟩ _ ⟨y', g'⟩ _ h
    have hy : y = y' := congrArg Cover.y h
    have hg : g = g' := by
      have := congrArg (gOf ℓ) h
      simpa [gOf_cov] using this
    rw [hy, hg]
  rw [suppSet, Finset.sum_image hinj, Finset.sum_product_right]
  conv_rhs => rw [← μ.sum_eq m]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  change ∑ y : P, morElt k (𝟙 (cov ℓ y g).y) • μ.proj (gOf ℓ (cov ℓ y g)) m = _
  simp only [gOf_cov]
  rw [← Finset.sum_smul]
  change (∑ y : P, morElt k (𝟙 y)) • μ.proj g m = _
  rw [sum_morElt_id, one_smul]

lemma projW_eq_zero_of_not_mem {a : Cover x₀} (ha : a ∉ suppSet ℓ k μ) (m : M) :
    projW ℓ k μ a m = 0 := by
  have hg : gOf ℓ a ∉ μ.supp := fun hg ↦ ha (Finset.mem_image.2
    ⟨(a.y, gOf ℓ a), Finset.mem_product.2 ⟨Finset.mem_univ _, hg⟩, cov_gOf ℓ a⟩)
  change morElt k (𝟙 a.y) • μ.proj (gOf ℓ a) m = 0
  rw [μ.out _ hg, smul_zero]

variable (S : Finset (Cover x₀))

/-- The map `⊕_{a ∈ S} W a → M`. -/
def totToM : (grRep ℓ k μ S).Tot →ₗ[k] M where
  toFun x := ∑ a, toM (x a)
  map_add' x y := by rw [← Finset.sum_add_distrib]; rfl
  map_smul' c x := by rw [Finset.smul_sum]; rfl

/-- The map `M → ⊕_{a ∈ S} W a`. -/
def mToTot : M →ₗ[k] (grRep ℓ k μ S).Tot where
  toFun m a := (⟨projW ℓ k μ (pt S a) m, projW_mem ℓ k μ _ m⟩ : W ℓ k μ (pt S a))
  map_add' m n := by funext a; exact Subtype.ext (map_add _ _ _)
  map_smul' c m := by funext a; exact Subtype.ext (map_smul _ _ _)

lemma mToTot_totToM (x : (grRep ℓ k μ S).Tot) : mToTot ℓ k μ S (totToM ℓ k μ S x) = x := by
  funext b
  apply toM_injective
  change projW ℓ k μ (pt S b) (∑ a, toM (x a)) = toM (x b)
  have hm : ∀ a, toM (x a) ∈ W ℓ k μ (pt S a) := fun a ↦ (show W ℓ k μ (pt S a) from x a).2
  rw [map_sum, Finset.sum_eq_single b]
  · rw [projW_of_mem ℓ k μ (hm b), if_pos rfl]
  · intro a _ hab
    rw [projW_of_mem ℓ k μ (hm a), if_neg]
    exact fun h ↦ hab (Subtype.ext h).symm
  · simp

/-- If `S` contains all cover objects carrying `M`, the total space is `M`. -/
lemma totToM_mToTot (hS : ∀ a, W ℓ k μ a ≠ ⊥ → a ∈ S) (m : M) :
    totToM ℓ k μ S (mToTot ℓ k μ S m) = m := by
  change ∑ a : S, projW ℓ k μ (a : Cover x₀) m = m
  rw [Finset.sum_coe_sort S (fun a ↦ projW ℓ k μ a m)]
  conv_rhs => rw [← sum_projW ℓ k μ m]
  have h1 : ∀ a ∈ S, a ∉ suppSet ℓ k μ → projW ℓ k μ a m = 0 :=
    fun a _ ha ↦ projW_eq_zero_of_not_mem ℓ k μ ha m
  have h2 : ∀ a ∈ suppSet ℓ k μ, a ∉ S → projW ℓ k μ a m = 0 := by
    intro a _ ha
    by_contra hne
    exact ha (hS a fun h0 ↦ hne (by
      have := projW_mem ℓ k μ a m
      rw [h0] at this; exact (Submodule.mem_bot k).1 this))
  rw [Finset.sum_subset (Finset.subset_union_left (s₂ := suppSet ℓ k μ))
      (fun a ha hna ↦ h2 a ((Finset.mem_union.1 ha).resolve_left hna) hna)]
  exact (Finset.sum_subset (Finset.subset_union_right (s₁ := S))
      (fun a ha hna ↦ h1 a ((Finset.mem_union.1 ha).resolve_right hna) hna)).symm

variable {ℓ k μ S}

variable (k) in
/-- The element of `k(P)` of an arrow of `Q_P`. -/
def arrElt (c : (quiver P).A) : Linearization P k := morElt k c.2.2.1

lemma toM_map_eq (α : (pieceQuiver S).A) (w : (grRep ℓ k μ S).obj ((pieceQuiver S).src α)) :
    toM (((grRep ℓ k μ S).map α).hom w) = arrElt k ((pieceProj S).arr α) • toM w := rfl

lemma toM_sum {a : (pieceQuiver S).V} {ι : Type*} (s : Finset ι)
    (f : ι → (grRep ℓ k μ S).obj a) : toM (∑ i ∈ s, f i) = ∑ i ∈ s, toM (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]; rfl

lemma sum_toM_single (t : (pieceQuiver S).V) (v : (grRep ℓ k μ S).obj t) :
    ∑ j, toM ((Pi.single t v : (grRep ℓ k μ S).Tot) j) = toM v := by
  rw [Finset.sum_eq_single t]
  · rw [Pi.single_eq_same]
  · intro j _ hj; rw [Pi.single_eq_of_ne hj]; rfl
  · simp

lemma idem_smul_toM (q : P) {a : (pieceQuiver S).V} (w : (grRep ℓ k μ S).obj a) :
    morElt k (𝟙 q) • toM w = if (pt S a).y = q then toM w else 0 := by
  have hw : morElt k (𝟙 (pt S a).y) • toM w = toM w := (show W ℓ k μ (pt S a) from w).2.1
  split_ifs with h
  · subst h; exact hw
  · rw [← hw, ← mul_smul, morElt_mul_ne k (𝟙 (pt S a).y) (𝟙 q) h, zero_smul]

/-- `totToM` intertwines the vertex actions. -/
lemma totToM_pdVert (q : P) (x : (grRep ℓ k μ S).Tot) :
    totToM ℓ k μ S ((grRep ℓ k μ S).pdVert (pieceProj S) q x) =
      morElt k (𝟙 q) • totToM ℓ k μ S x := by
  change ∑ a, toM (((grRep ℓ k μ S).pdVert (pieceProj S) q x) a) = _ • ∑ a, toM (x a)
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Rep.pdVert_apply, idem_smul_toM]
  change toM (if (pt S a).y = q then x a else 0) = _
  split_ifs <;> rfl

/-- `totToM` intertwines the arrow actions when `S` contains all cover objects carrying `M`. -/
lemma totToM_pdArr (hS : ∀ a, W ℓ k μ a ≠ ⊥ → a ∈ S) (c : (quiver P).A)
    (x : (grRep ℓ k μ S).Tot) :
    totToM ℓ k μ S ((grRep ℓ k μ S).pdArr (pieceProj S) c x) =
      arrElt k c • totToM ℓ k μ S x := by
  classical
  set E := Finset.univ.filter fun e : (pieceQuiver S).A ↦ (pieceProj S).arr e = c with hE
  -- the left side
  have hL : totToM ℓ k μ S ((grRep ℓ k μ S).pdArr (pieceProj S) c x) =
      ∑ e ∈ E, arrElt k c • toM (x ((pieceQuiver S).src e)) := by
    change ∑ j, toM (((grRep ℓ k μ S).pdArr (pieceProj S) c x) j) = _
    simp_rw [Rep.pdArr_apply, toM_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e he ↦ ?_
    rw [sum_toM_single, toM_map_eq, (Finset.mem_filter.1 he).2]
  -- vertices without an arrow labelled `c` are killed
  have hzero : ∀ a, a ∉ E.image (pieceQuiver S).src → arrElt k c • toM (x a) = 0 := by
    intro a ha
    obtain ⟨x', y', f, hf⟩ := c
    have hw : morElt k (𝟙 (pt S a).y) • toM (x a) = toM (x a) :=
      (show W ℓ k μ (pt S a) from x a).2.1
    change morElt k f • toM (x a) = 0
    by_cases hy : (pt S a).y = x'
    · subst hy
      set b : Cover x₀ := ⟨y', (pt S a).u ≫ cls f hf.1⟩
      have hmem : morElt k f • toM (x a) ∈ W ℓ k μ b := by
        have := smul_mem_W ℓ k μ (liftAt (pt S a) f hf.1) (Option.some_ne_none _) hf.1
          (show W ℓ k μ (pt S a) from x a).2
        exact this
      by_cases hb : b ∈ S
      · exfalso
        apply ha
        refine Finset.mem_image.2 ⟨⟨a, ⟨b, hb⟩, ⟨liftAt (pt S a) f hf.1,
          isIrreducible_liftAt (pt S a) hf⟩⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, rfl⟩
        rfl
      · have hWb : W ℓ k μ b = ⊥ := by
          by_contra h; exact hb (hS b h)
        rw [hWb] at hmem
        exact (Submodule.mem_bot k).1 hmem
    · rw [← hw, ← mul_smul, morElt_mul_ne k (𝟙 (pt S a).y) f hy, zero_smul]
  have hsrc : Set.InjOn (pieceQuiver S).src ↑E := by
    intro e he e' he' h
    exact (pieceProj_locInj S).1 e e' h
      (((Finset.mem_filter.1 he).2).trans ((Finset.mem_filter.1 he').2).symm)
  rw [hL]
  change _ = arrElt k c • ∑ a, toM (x a)
  rw [Finset.smul_sum, ← Finset.sum_subset (Finset.subset_univ (E.image (pieceQuiver S).src))
    (fun a _ ha ↦ hzero a ha), Finset.sum_image hsrc]

end LargeIndecomposable.RayCat
