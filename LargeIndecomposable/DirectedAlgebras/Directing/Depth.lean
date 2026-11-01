module

public import LargeIndecomposable.DirectedAlgebras.EulerForm.ProjSummand

/-!
# Depth of vertices and supports of syzygies

For directed data, the depth of a vertex `x` is the number of its strict successors
(`DirData.depth`); it drops strictly along nonzero `e_y A e_x` with `x ≠ y` (`depth_lt`).
A module `M` lives in depth `< d` if `e_x M = 0` whenever `depth x ≥ d` (`LivesBelow`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (D : DirData k A)

namespace DirData

open Classical in
/-- The number of strict successors of a vertex. -/
def depth (x : D.ι) : ℕ := (Finset.univ.filter fun z ↦ Relation.TransGen D.Arr x z).card

/-- **Depth drops along paths.** -/
lemma depth_lt_of_transGen {x y : D.ι} (h : Relation.TransGen D.Arr x y) : D.depth y < D.depth x := by
  classical
  unfold depth
  refine Finset.card_lt_card ⟨fun z hz ↦ ?_, fun hsub ↦ ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact h.trans hz
  · have : y ∈ Finset.univ.filter fun z ↦ Relation.TransGen D.Arr y z := hsub (by simpa using h)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact D.acyc y y this Relation.ReflTransGen.refl

/-- **Depth drops along nonzero corners.** -/
lemma depth_lt {x y : D.ι} (hxy : x ≠ y) (a : A) (ha : D.e y * a * D.e x ≠ 0) :
    D.depth y < D.depth x :=
  D.depth_lt_of_transGen (D.transGen_of_ne (D.hom x y a ha) hxy)

end DirData

/-- `M` lives in depth `< d`: `e_x M = 0` whenever `depth x ≥ d`. -/
def LivesBelow (M : FDMod k A) (d : ℕ) : Prop :=
  ∀ x, d ≤ D.depth x → eSub M (D.e x) = ⊥

lemma livesBelow_zero_iff_subsingleton (M : FDMod k A) :
    LivesBelow D M 0 ↔ ∀ x, eSub M (D.e x) = ⊥ := by
  simp [LivesBelow]

/-- Every module lives in depth `< card ι + 1`. -/
lemma livesBelow_card (M : FDMod k A) : LivesBelow D M (Fintype.card D.ι + 1) := by
  classical
  intro x hx
  exfalso
  have : D.depth x ≤ Fintype.card D.ι := by
    unfold DirData.depth
    exact Finset.card_le_univ _
  omega

variable [FiniteDimensional k A]

/-- The dimension vector of a sum of indecomposable projectives. -/
lemma dimv_sumProj (x : D.ι) : ∀ l : List D.ι,
    (dimv D.e (sumProj D l) x : ℤ) = (l.map fun c ↦ cartan D x c).sum
  | [] => by
    simp only [List.map_nil, List.sum_nil, Nat.cast_eq_zero]
    haveI : Subsingleton (sumProj D []) := inferInstanceAs (Subsingleton PUnit)
    exact Module.finrank_zero_of_subsingleton
  | c :: l => by
    have h := dimZ_exact D (M := projE (k := k) (D.idem c)) (N := sumProj D (c :: l))
      (L := sumProj D l) (LinearMap.inl A _ _) (LinearMap.snd A _ _) LinearMap.inl_injective
      (fun q ↦ ⟨(0, q), rfl⟩) (LinearMap.range_inl A _ _)
    have h' := congrFun h x
    simp only [dimZ, Pi.add_apply] at h'
    rw [h', dimv_sumProj x l, List.map_cons, List.sum_cons]
    rfl

/-- The cover list: bases of all `eᵢ M`. -/
def coverList (M : FDMod k A) : List (Σ i : D.ι, eSub M (D.e i)) := by
  classical
  exact (Finset.univ.toList).flatMap fun i ↦
    (List.ofFn (Module.finBasis k (eSub M (D.e i)))).map fun b ↦ ⟨i, b⟩

lemma count_coverList (M : FDMod k A) (x : D.ι) :
    ((coverList D M).map Sigma.fst).count x = finrank k (eSub M (D.e x)) := by
  classical
  unfold coverList
  rw [List.map_flatMap, List.count_flatMap]
  have h : ∀ i, List.map Sigma.fst
      ((List.ofFn (Module.finBasis k (eSub M (D.e i)))).map fun b ↦ (⟨i, b⟩ : Σ i : D.ι, eSub M (D.e i))) =
      List.replicate (finrank k (eSub M (D.e i))) i := by
    intro i
    rw [List.map_map, List.map_ofFn]
    exact List.ofFn_const _ i
  simp only [Function.comp_def, h, List.count_replicate, beq_iff_eq]
  rw [Finset.sum_map_toList, Finset.sum_eq_single x]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

lemma sum_map_eq_count {x : D.ι} (f : D.ι → ℤ) :
    ∀ l : List D.ι, (∀ c ∈ l, f c = if c = x then 1 else 0) → (l.map f).sum = l.count x
  | [], _ => by simp
  | c :: l, h => by
    rw [List.map_cons, List.sum_cons, sum_map_eq_count f l fun c hc ↦ h c (List.mem_cons_of_mem _ hc),
      h c List.mem_cons_self, List.count_cons]
    by_cases hc : c = x
    · subst hc; simp; ring
    · simp [hc]

/-- **The cover by bases is onto.** -/
lemma sumMap_coverList_surjective (M : FDMod k A) :
    Function.Surjective (sumMap D M (coverList D M)) := by
  classical
  rw [← LinearMap.range_eq_top]
  have hsub : ∀ i, ∀ m : eSub M (D.e i), (m : M) ∈ LinearMap.range (sumMap D M (coverList D M)) := by
    intro i m
    have hspan : (m : eSub M (D.e i)) ∈ Submodule.span k
        (Set.range (Module.finBasis k (eSub M (D.e i)))) := by
      rw [(Module.finBasis k (eSub M (D.e i))).span_eq]
      trivial
    induction hspan using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨t, rfl⟩ := hb
      refine mem_range_sumMap D M _ ⟨i, _⟩ ?_
      unfold coverList
      refine List.mem_flatMap.2 ⟨i, Finset.mem_toList.2 (Finset.mem_univ i), ?_⟩
      exact List.mem_map.2 ⟨_, List.mem_ofFn.2 ⟨t, rfl⟩, rfl⟩
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have := Submodule.smul_mem _ (algebraMap k A c) ha
      rwa [algebraMap_smul] at this
  rw [eq_top_iff]
  intro m _
  have hm : m = ∑ i, D.e i • m := by rw [← Finset.sum_smul, D.sum, one_smul]
  rw [hm]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  exact hsub i ⟨D.e i • m, by
    change D.e i • D.e i • m = D.e i • m
    rw [← mul_smul, (D.idem i).eq]⟩

/-- The syzygy of the cover by bases. -/
abbrev syz (M : FDMod k A) : FDMod k A := FDMod.ofSub (LinearMap.ker (sumMap D M (coverList D M)))

/-- **The syzygy lives one depth lower.** -/
theorem livesBelow_syz (hT : ∀ x, x ∈ D.T) (M : FDMod k A) (d : ℕ) (hM : LivesBelow D M (d + 1)) :
    LivesBelow D (syz D M) d := by
  classical
  intro x hx
  have hex := dimZ_exact D (M := syz D M) (N := sumProj D ((coverList D M).map Sigma.fst)) (L := M)
    (LinearMap.ker (sumMap D M (coverList D M))).subtype (sumMap D M (coverList D M))
    Subtype.val_injective (sumMap_coverList_surjective D M) (Submodule.range_subtype _)
  have h1 := congrFun hex x
  simp only [dimZ, Pi.add_apply] at h1
  rw [dimv_sumProj] at h1
  -- the terms of the sum
  have hterm : ∀ c ∈ (coverList D M).map Sigma.fst,
      cartan D x c = if c = x then 1 else 0 := by
    intro c hc
    have hpos : 0 < finrank k (eSub M (D.e c)) := by
      rw [← count_coverList]
      exact List.count_pos_iff.2 hc
    have hdc : D.depth c ≤ d := by
      by_contra hlt
      have := hM c (by omega)
      rw [this, finrank_bot] at hpos
      exact absurd hpos (lt_irrefl 0)
    by_cases hcx : c = x
    · subst hcx
      rw [if_pos rfl, cartan_diag D (hT c)]
    · rw [if_neg hcx]
      apply cartan_eq_zero
      intro hpath
      have := D.depth_lt_of_transGen (D.transGen_of_ne hpath hcx)
      omega
  rw [sum_map_eq_count D _ _ hterm, count_coverList] at h1
  have h0 : dimv D.e (syz D M) x = 0 := by
    have : (dimv D.e M x : ℤ) = finrank k (eSub M (D.e x)) := rfl
    omega
  haveI : FiniteDimensional k (syz D M) := (syz D M).isFD
  exact Submodule.finrank_eq_zero.1 h0

end LargeIndecomposable.AR
