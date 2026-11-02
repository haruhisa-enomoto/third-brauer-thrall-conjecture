module

public import LargeIndecomposable.MildContours.Assembly.TinyBridge
public import LargeIndecomposable.RepresentationType.MinimalInfinite.Split

/-!
# From a split point of the ray category to the algebra (bridge)

A `SplitAt V₁ Z` point of the ray category of a split basic distributive
algebra `B` gives a `SplitPoint` of `B` (with `e₁` the sum of the idempotents of
`V₁`, `e_z`, and `e₂` the rest), so a minimal representation-infinite `B` has no
split point (`SplitPoint.not_minimal`). With `RaySmall` this gives `NoSplit` for
the small ray category.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable RayCat

universe u

namespace RayCat.RaySmall

universe w v u'

variable {P : Type u'} [Category.{v} P] [LocallySmall.{w} P] [HasZeroMorphisms P]

/-- **`SplitAt` passes from the small model to `P`.** -/
theorem splitAt_of_small {V₁ : Set (RaySmall.{u'} P)} {Z : RaySmall.{u'} P}
    (h : SplitAt V₁ Z) : SplitAt {p : P | (⟨p⟩ : RaySmall.{u'} P) ∈ V₁} Z.as := by
  obtain ⟨z⟩ := Z
  obtain ⟨hZ, c2, c3, c4, c5, c6, ⟨I, hI, f₁, hf₁⟩, ⟨J, hJ, hJZ, f₂, hf₂⟩⟩ := h
  have ne : ∀ {j : P}, j ≠ z → (⟨j⟩ : RaySmall.{u'} P) ≠ ⟨z⟩ := fun h e ↦ h (congrArg RaySmall.as e)
  refine ⟨hZ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj hjz f
    exact (sh_eq_zero_iff.{w} (X := ⟨i⟩) (Y := ⟨j⟩) f).1 (c2 _ hi _ hj (ne hjz) _)
  · intro i hi hiz j hj f
    exact (sh_eq_zero_iff.{w} (X := ⟨i⟩) (Y := ⟨j⟩) f).1 (c3 _ hi (ne hiz) _ hj _)
  · intro i hi hiz f
    exact (sh_eq_zero_iff.{w} (X := ⟨i⟩) (Y := ⟨z⟩) f).1 (c4 _ hi (ne hiz) _)
  · intro j hj f
    exact (sh_eq_zero_iff.{w} (X := ⟨z⟩) (Y := ⟨j⟩) f).1 (c5 _ hj _)
  · intro f hf
    exact (sh_eq_zero_iff.{w} (X := ⟨z⟩) (Y := ⟨z⟩) f).1 (c6 _ (fun h' ↦ hf
      ((isIso_sh_iff.{w} (X := ⟨z⟩) (Y := ⟨z⟩) f).1 h')))
  · obtain ⟨i⟩ := I
    refine ⟨i, hI, (sh.{w}).symm f₁, fun h0 ↦ hf₁ ?_⟩
    rw [← Equiv.apply_symm_apply sh f₁, h0, sh_zero]
  · obtain ⟨j⟩ := J
    refine ⟨j, hJ, fun h ↦ hJZ (by rw [h]), (sh.{w}).symm f₂, fun h0 ↦ hf₂ ?_⟩
    rw [← Equiv.apply_symm_apply sh f₂, h0, sh_zero]

end RayCat.RaySmall

namespace SplitBasicData

variable {k : Type u} [Field k] [IsAlgClosed k] {B : Type u} [Ring B] [Algebra k B]
  [FiniteDimensional k B] {ι : Type} [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι)
  [HasBGRSDistributiveHomStructure k S.toIdempotents.ProjectiveCategory]

lemma sum_mul_sum (A C : Finset ι) :
    (∑ v ∈ A, S.e v) * (∑ w ∈ C, S.e w) = ∑ v ∈ A ∩ C, S.e v := by
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, S.complete.toOrthogonalIdempotents.mul_eq]
  rw [← Finset.sum_ite_mem]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [Finset.sum_ite_eq]

lemma e_mul_sum (A : Finset ι) (v : ι) :
    S.e v * (∑ w ∈ A, S.e w) = if v ∈ A then S.e v else 0 := by
  have := S.sum_mul_sum {v} A
  rw [Finset.sum_singleton] at this
  rw [this]
  split_ifs with h
  · rw [Finset.singleton_inter_of_mem h, Finset.sum_singleton]
  · rw [Finset.singleton_inter_of_notMem h, Finset.sum_empty]

lemma sum_mul_e (A : Finset ι) (v : ι) :
    (∑ w ∈ A, S.e w) * S.e v = if v ∈ A then S.e v else 0 := by
  have := S.sum_mul_sum A {v}
  rw [Finset.sum_singleton] at this
  rw [this]
  split_ifs with h
  · rw [Finset.inter_singleton_of_mem h, Finset.sum_singleton]
  · rw [Finset.inter_singleton_of_notMem h, Finset.sum_empty]

/-- The ray object of a vertex. -/
abbrev R (v : ι) : S.toIdempotents.RayCategory := ⟨objOf S v⟩

lemma R_vert (X : S.toIdempotents.RayCategory) : S.R (S.toIdempotents.projectiveVertex X.as) = X := by
  obtain ⟨i⟩ := X
  change (⟨S.toIdempotents.projectiveVertexEquiv.symm (S.toIdempotents.projectiveVertex i)⟩ :
    S.toIdempotents.RayCategory) = ⟨i⟩
  congr 1
  exact S.toIdempotents.projectiveVertexEquiv.symm_apply_apply i

lemma R_injective : Function.Injective S.R := by
  intro v w h
  have := congrArg BGRSRayCategory.as h
  exact S.toIdempotents.projectiveVertexEquiv.symm.injective this

lemma zr (v w : ι) (b : B) (h : ∀ f : S.R w ⟶ S.R v, f = 0) : S.e v * b * S.e w = 0 := by
  have h0 := (rayOf_eq_zero_iff (homOf S (objOf S w) (objOf S v) b)).1 (h _)
  have := congrArg Subtype.val h0
  rw [homOf_val, ev_objOf, ev_objOf] at this
  exact this

/-- **No split point** in the ray category of a minimal representation-infinite algebra. -/
theorem not_splitAt (hB : IsMinimalRepInfinite B) (V₁ : Set S.toIdempotents.RayCategory)
    (Z : S.toIdempotents.RayCategory) : ¬SplitAt V₁ Z := by
  classical
  obtain ⟨vz, rfl⟩ : ∃ vz, S.R vz = Z := ⟨_, S.R_vert Z⟩
  rintro ⟨hZ, c2, c3, c4, c5, c6, ⟨I, hI, f₁, hf₁⟩, ⟨J, hJ, hJZ, f₂, hf₂⟩⟩
  obtain ⟨vI, rfl⟩ : ∃ v, S.R v = I := ⟨_, S.R_vert I⟩
  obtain ⟨vJ, rfl⟩ : ∃ v, S.R v = J := ⟨_, S.R_vert J⟩
  let F₁ := Finset.univ.filter fun v ↦ S.R v ∈ V₁
  let F₂ := Finset.univ.filter fun v ↦ S.R v ∉ V₁ ∧ v ≠ vz
  have m1 : ∀ {v}, v ∈ F₁ ↔ S.R v ∈ V₁ := by simp [F₁]
  have m2 : ∀ {v}, v ∈ F₂ ↔ S.R v ∉ V₁ ∧ v ≠ vz := by simp [F₂]
  have hvz1 : vz ∉ F₁ := by rw [m1]; exact hZ
  have hvz2 : vz ∉ F₂ := by rw [m2]; simp
  have h12 : F₁ ∩ F₂ = ∅ := by
    ext v; simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro h1 h2; exact (m2.1 h2).1 (m1.1 h1)
  have ne_z : ∀ {v}, v ≠ vz → S.R v ≠ S.R vz := fun h e ↦ h (S.R_injective e)
  have hsum : (∑ v ∈ F₁, S.e v) + S.e vz + (∑ v ∈ F₂, S.e v) = 1 := by
    rw [← S.sum_e, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v ↦ S.R v ∈ V₁)]
    rw [add_assoc]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun v ↦ S.R v ∉ V₁)
      (fun v ↦ v = vz), Finset.filter_filter, Finset.filter_filter]
    have : Finset.univ.filter (fun v ↦ S.R v ∉ V₁ ∧ v = vz) = {vz} := by
      ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · exact fun h ↦ h.2
      · rintro rfl; exact ⟨hZ, rfl⟩
    rw [this, Finset.sum_singleton]
  have mulsum : ∀ (A C : Finset ι) (b : B), (∀ v ∈ A, ∀ w ∈ C, S.e v * b * S.e w = 0) →
      (∑ v ∈ A, S.e v) * b * (∑ w ∈ C, S.e w) = 0 := by
    intro A C b h
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_eq_zero fun v hv ↦ ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun w hw ↦ h v hv w hw
  let D : SplitPoint k B :=
    { e₁ := ∑ v ∈ F₁, S.e v, ez := S.e vz, e₂ := ∑ v ∈ F₂, S.e v, sum := hsum
      h11 := by rw [S.sum_mul_sum, Finset.inter_self]
      hzz := S.e_mul_e vz
      h22 := by rw [S.sum_mul_sum, Finset.inter_self]
      h1z := by rw [S.sum_mul_e, if_neg hvz1]
      hz1 := by rw [S.e_mul_sum, if_neg hvz1]
      h12 := by rw [S.sum_mul_sum, h12, Finset.sum_empty]
      h21 := by rw [S.sum_mul_sum, Finset.inter_comm, h12, Finset.sum_empty]
      hz2 := by rw [S.e_mul_sum, if_neg hvz2]
      h2z := by rw [S.sum_mul_e, if_neg hvz2]
      b12 := fun b ↦ mulsum _ _ b fun v hv w hw ↦ S.zr v w b fun f ↦
        c3 _ (m2.1 hw).1 (ne_z (m2.1 hw).2) _ (m1.1 hv) f
      b21 := fun b ↦ mulsum _ _ b fun w hw v hv ↦ S.zr w v b fun f ↦
        c2 _ (m1.1 hv) _ (m2.1 hw).1 (ne_z (m2.1 hw).2) f
      b1z := fun b ↦ by
        have := mulsum F₁ {vz} b fun v hv w hw ↦ by
          rw [Finset.mem_singleton] at hw; subst hw
          exact S.zr v _ b fun f ↦ c5 _ (m1.1 hv) f
        rwa [Finset.sum_singleton] at this
      bz2 := fun b ↦ by
        have := mulsum {vz} F₂ b fun v hv w hw ↦ by
          rw [Finset.mem_singleton] at hv; subst hv
          exact S.zr _ w b fun f ↦ c4 _ (m2.1 hw).1 (ne_z (m2.1 hw).2) f
        rwa [Finset.sum_singleton] at this
      bzz := fun b ↦ by
        obtain ⟨c, hc⟩ := S.corner_diag vz b
        refine ⟨c, ?_⟩
        set r := S.e vz * b * S.e vz - c • S.e vz with hr
        let m := homOf S (objOf S vz) (objOf S vz) r
        have hm : m.1 = r := by
          change ev S (objOf S vz) * r * ev S (objOf S vz) = r
          have he := S.e_mul_e vz
          have h1 : S.e vz * (S.e vz * b * S.e vz) * S.e vz = S.e vz * b * S.e vz := by
            rw [← mul_assoc, ← mul_assoc, he, mul_assoc, he]
          have h2 : S.e vz * (c • S.e vz) * S.e vz = c • S.e vz := by
            rw [mul_smul_comm, smul_mul_assoc, he, he]
          rw [ev_objOf, hr, mul_sub, sub_mul, h1, h2]
        have hmJ : m.1 ∈ Ring.jacobson B := by rw [hm]; exact hc
        have h0 := c6 (rayOf m) (not_isIso_rayOf S m hmJ)
        have := congrArg Subtype.val ((rayOf_eq_zero_iff m).1 h0)
        rw [hm] at this
        rw [Algebra.smul_def] at hr
        rw [hr] at this
        exact sub_eq_zero.1 this }
  -- the two nonzero corners
  have rep : ∀ {v w : ι} (f : S.R v ⟶ S.R w), f ≠ 0 →
      ∃ b : B, b ≠ 0 ∧ S.e w * b = b ∧ b * S.e v = b := by
    intro v w f hf
    refine ⟨(Quotient.out f).1, fun h ↦ hf ?_, ?_, ?_⟩
    · rw [← unitRay_out f]
      exact (rayOf_eq_zero_iff _).2 (hom_ext' S h)
    · have := val_left S (Quotient.out f); rwa [ev_objOf] at this
    · have := val_right S (Quotient.out f); rwa [ev_objOf] at this
  obtain ⟨b₁, hb₁, hb₁l, hb₁r⟩ := rep f₁ hf₁
  obtain ⟨b₂, hb₂, hb₂l, hb₂r⟩ := rep f₂ hf₂
  have hvJ : vJ ∈ F₂ := m2.2 ⟨hJ, fun h ↦ hJZ (by rw [h])⟩
  refine D.not_minimal hB ⟨b₁, ?_⟩ ⟨b₂, ?_⟩
  · change S.e vz * b₁ * (∑ v ∈ F₁, S.e v) ≠ 0
    rw [hb₁l, ← hb₁r, mul_assoc, S.e_mul_sum, if_pos (m1.2 hI)]
    rwa [hb₁r]
  · change (∑ v ∈ F₂, S.e v) * b₂ * S.e vz ≠ 0
    rw [mul_assoc, hb₂r, ← hb₂l, ← mul_assoc, S.sum_mul_e, if_pos hvJ]
    rwa [hb₂l]

/-- **`NoSplit` for the small ray category** of a minimal representation-infinite algebra. -/
theorem noSplit_small (hB : IsMinimalRepInfinite B) [LocallySmall.{0} S.toIdempotents.RayCategory] :
    NoSplit (RaySmall.{0} S.toIdempotents.RayCategory) := fun V₁ Z h ↦
  S.not_splitAt hB _ _ (RaySmall.splitAt_of_small h)

end SplitBasicData

end LargeIndecomposable
