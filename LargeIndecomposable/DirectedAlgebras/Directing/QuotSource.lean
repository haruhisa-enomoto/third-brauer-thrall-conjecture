module

public import LargeIndecomposable.DirectedAlgebras.EulerForm.EulerUnit
public import LargeIndecomposable.DirectedAlgebras.Directing.QuotAny

/-!
# Removing a source

Let `w` be a source of a directed algebra `D` with all points live: nothing maps into `w`
(`e_w A e_x = 0` for `x ≠ w`). Then the other points form a convex set, the quotient
`D / ⟨e_w⟩` has the same corners between the other points (`cartan_quotAny_source`), and its
Euler form is the restriction of that of `D` (`euler_quotAny_source`,
`eulerForm_c_quotAny_source`): the Cartan matrix is block triangular.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module Matrix

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

namespace DirData

variable (D : DirData k A) (w : D.ι)
  (hw : ∀ x, x ≠ w → ∀ c : A, D.e w * c * D.e x = 0)

include hw in
/-- The points other than a source form a convex set. -/
lemma convexSet_ne_source (hT : ∀ x, x ∈ D.T) : D.ConvexSet {x | x ≠ w} := by
  refine ⟨fun x _ ↦ hT x, fun x y z hx hz hxy hyz ↦ ?_⟩
  intro hyw
  subst hyw
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hxy with h | h
  · exact hx h.symm
  · -- a path into the source `y`
    obtain ⟨c, hc⟩ : ∃ c, Relation.ReflTransGen D.Arr x c ∧ D.Arr c y := by
      rcases Relation.TransGen.tail'_iff.1 h with ⟨c, h1, h2⟩
      exact ⟨c, h1, h2⟩
    obtain ⟨d, hd⟩ := D.arrNe c y hc.2
    have hcy : c ≠ y := D.ne_of_arr hc.2
    exact hd (hw c hcy d)

lemma ne_subset (hT : ∀ x, x ∈ D.T) : ({x | x ≠ w} : Set D.ι) ⊆ D.T := fun x _ ↦ hT x

/-- The quotient by the source. -/
abbrev qsrc (hT : ∀ x, x ∈ D.T) : DirData k (D.QAlg {x | x ≠ w}) := D.quotAny (D.ne_subset w hT)

/-- The quotient map on corners `e_j A e_i`. -/
def cornerQ (hT : ∀ x, x ∈ D.T) (i j : ({x | x ≠ w} : Set D.ι)) :
    eSub (projE (k := k) (D.idem i)) (D.e j) →ₗ[k]
      eSub (projE (k := k) ((D.qsrc w hT).idem i)) ((D.qsrc w hT).e j) where
  toFun m := ⟨⟨D.qmap _ ((m : projE (k := k) (D.idem i)) : A), by
      change D.qmap _ _ * D.qmap _ (D.e i) = _
      rw [← map_mul, show ((m : projE (k := k) (D.idem i)) : A) * D.e i = _ from
        (m : projE (k := k) (D.idem i)).2]⟩, by
      apply Subtype.ext
      change D.qmap _ (D.e j) * D.qmap _ _ = _
      rw [← map_mul]
      congr 1
      exact congrArg Subtype.val m.2⟩
  map_add' m n := by
    apply Subtype.ext; apply Subtype.ext
    change D.qmap _ (((m + n : eSub _ _) : projE (k := k) (D.idem i)) : A) = _
    simp
  map_smul' c m := by
    apply Subtype.ext; apply Subtype.ext
    change D.qmap _ (((c • m : eSub _ _) : projE (k := k) (D.idem i)) : A) = _
    simp

include hw in
lemma cornerQ_bijective (hT : ∀ x, x ∈ D.T) (i j : ({x | x ≠ w} : Set D.ι)) :
    Function.Bijective (D.cornerQ w hT i j) := by
  have hconv := D.convexSet_ne_source w hw hT
  refine ⟨fun m n hmn ↦ ?_, fun y ↦ ?_⟩
  · have h := congrArg (fun z : eSub (projE (k := k) ((D.qsrc w hT).idem i))
        ((D.qsrc w hT).e j) ↦ (z : projE (k := k) ((D.qsrc w hT).idem i)).1) hmn
    change D.qmap _ _ = D.qmap _ _ at h
    rw [← sub_eq_zero, ← map_sub] at h
    by_contra hne
    set d : A := ((m : projE (k := k) (D.idem i)) : A) - ((n : projE (k := k) (D.idem i)) : A)
    have hd1 : d * D.e i = d := by
      simp only [d, sub_mul, show ((m : projE (k := k) (D.idem i)) : A) * D.e i = _ from
        (m : projE (k := k) (D.idem i)).2, show ((n : projE (k := k) (D.idem i)) : A) * D.e i = _
        from (n : projE (k := k) (D.idem i)).2]
    have hd2 : D.e j * d = d := by
      simp only [d, mul_sub]
      rw [show D.e j * ((m : projE (k := k) (D.idem i)) : A) = _ from congrArg Subtype.val m.2,
        show D.e j * ((n : projE (k := k) (D.idem i)) : A) = _ from congrArg Subtype.val n.2]
    have hd0 : d ≠ 0 := fun h0 ↦ hne (Subtype.ext (Subtype.ext (sub_eq_zero.1 h0)))
    have hc : D.e j * d * D.e i ≠ 0 := by rwa [hd2, hd1]
    exact D.qmap_corner_ne hconv i.2 j.2 hc (by rwa [hd2, hd1])
  · set y0 : D.QAlg {x | x ≠ w} := (y : projE (k := k) ((D.qsrc w hT).idem i)).1
    obtain ⟨z, hz⟩ := D.qmap_surjective {x | x ≠ w} y0
    have hy1 : y0 * D.qmap _ (D.e i) = y0 := (y : projE (k := k) ((D.qsrc w hT).idem i)).2
    have hy2 : D.qmap _ (D.e j) * y0 = y0 := congrArg Subtype.val y.2
    refine ⟨⟨⟨D.e j * z * D.e i, by
      change D.e j * z * D.e i * D.e i = _
      rw [mul_assoc, (D.idem i).eq]⟩, by
      apply Subtype.ext
      change D.e j * (D.e j * z * D.e i) = _
      rw [← mul_assoc, ← mul_assoc, (D.idem j).eq]⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    change D.qmap _ (D.e j * z * D.e i) = _
    rw [map_mul, map_mul, hz, hy2, hy1]

include hw in
/-- **The corners between the other points do not change.** -/
lemma cartan_quotAny_source (hT : ∀ x, x ∈ D.T) (i j : ({x | x ≠ w} : Set D.ι)) :
    cartan (D.qsrc w hT) j i = cartan D j i := by
  unfold cartan
  congr 1
  exact (LinearEquiv.ofBijective _ (D.cornerQ_bijective w hw hT i j)).finrank_eq.symm

include hw in
lemma cartan_source_row (x : D.ι) (hx : x ≠ w) : cartan D w x = 0 := by
  unfold cartan
  have : eSub (projE (k := k) (D.idem x)) (D.e w) = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    rw [Submodule.mem_bot]
    have h1 : D.e w • m = m := hm
    apply Subtype.ext
    have h2 : (m : A) * D.e x = m := m.2
    change (m : A) = 0
    have h3 : D.e w * (m : A) = m := congrArg Subtype.val h1
    rw [← h3, ← h2, ← mul_assoc]
    exact hw x hx m
  rw [this, finrank_bot]; rfl

/-- Extension by zero at the source. -/
def extW (hT : ∀ x, x ∈ D.T) (u : (D.qsrc w hT).ι → ℤ) : D.ι → ℤ :=
  fun x ↦ if h : x ≠ w then u ⟨x, h⟩ else 0

lemma sum_extW (f : D.ι → ℤ) (hf : f w = 0) [inst : Fintype ({x | x ≠ w} : Set D.ι)] :
    ∑ x, f x = ∑ x : ({x | x ≠ w} : Set D.ι), f x := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ≠ w)]
  have h2 : ∑ x ∈ Finset.univ.filter (fun x ↦ ¬x ≠ w), f x = 0 :=
    Finset.sum_eq_zero fun x hx ↦ by
      have : x = w := by simpa using hx
      rw [this, hf]
  rw [h2, add_zero]
  exact Finset.sum_subtype _ (fun x ↦ by simp) f

include hw in
/-- **The Euler form of the quotient by a source is the restriction.** -/
theorem euler_quotAny_source (hT : ∀ x, x ∈ D.T) (u v : (D.qsrc w hT).ι → ℤ) :
    euler (D.qsrc w hT) u v = euler D (D.extW w hT u) (D.extW w hT v) := by
  classical
  have hT' : ∀ x, x ∈ (D.qsrc w hT).T := fun _ ↦ Set.mem_univ _
  have hu' : IsUnit (cartan (D.qsrc w hT)).det := by
    rw [det_cartan (D.qsrc w hT) hT']; exact isUnit_one
  have hu : IsUnit (cartan D).det := by rw [det_cartan D hT]; exact isUnit_one
  obtain ⟨y', hy'⟩ : ∃ y', y' = (cartan (D.qsrc w hT))⁻¹ *ᵥ u := ⟨_, rfl⟩
  have hCy : cartan (D.qsrc w hT) *ᵥ y' = u := by
    rw [hy', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu', Matrix.one_mulVec]
  have hsum : ∀ f : D.ι → ℤ, f w = 0 → ∑ x, f x = ∑ x : (D.qsrc w hT).ι, f x.1 :=
    fun f hf ↦ sum_extW D w f hf (inst := (D.qsrc w hT).fin)
  have hext : ∀ (z : (D.qsrc w hT).ι → ℤ) (x : (D.qsrc w hT).ι), D.extW w hT z x.1 = z x :=
    fun z x ↦ by simp only [extW]; rw [dif_pos (show (x.1 : D.ι) ≠ w from x.2)]; rfl
  have key : cartan D *ᵥ D.extW w hT y' = D.extW w hT u := by
    funext j
    simp only [Matrix.mulVec, dotProduct]
    rw [hsum _ (by simp [extW])]
    simp only [hext]
    by_cases hj : j ≠ w
    · have := congrFun hCy ⟨j, hj⟩
      simp only [Matrix.mulVec, dotProduct] at this
      have hj' : D.extW w hT u j = u ⟨j, hj⟩ := hext u ⟨j, hj⟩
      rw [hj', ← this]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [← D.cartan_quotAny_source w hw hT x ⟨j, hj⟩]
    · have hjw : j = w := by simpa using hj
      subst hjw
      have : D.extW j hT u j = 0 := by simp [extW]
      rw [this]
      refine Finset.sum_eq_zero fun x _ ↦ ?_
      rw [D.cartan_source_row j hw x.1 x.2, zero_mul]
  have hinv : (cartan D)⁻¹ *ᵥ D.extW w hT u = D.extW w hT y' := by
    rw [← key, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  unfold euler
  rw [hinv, ← hy']
  simp only [dotProduct]
  rw [hsum _ (by simp [extW])]
  simp only [hext]

/-- The indicator vector of a point. -/
def ind {α : Type} [DecidableEq α] (a : α) : α → ℤ := fun x ↦ if x = a then 1 else 0

lemma euler_ind (D : DirData k A) (a b : D.ι) : euler D (ind a) (ind b) = (cartan D)⁻¹ b a := by
  unfold euler
  simp [Matrix.mulVec, dotProduct, ind]

lemma extW_ind (hT : ∀ x, x ∈ D.T) (a : (D.qsrc w hT).ι) : D.extW w hT (ind a) = ind a.1 := by
  funext x
  simp only [extW, ind]
  by_cases hx : x ≠ w
  · rw [dif_pos hx]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (congrArg Subtype.val h1) h2
    · exact absurd (Subtype.ext h2) h1
    · rfl
  · rw [dif_neg hx]
    split_ifs with h1
    · exact absurd (h1 ▸ a.2) hx
    · rfl

include hw in
/-- **The coefficients of the Euler form off a source do not change.** -/
theorem eulerForm_c_quotAny_source (hT : ∀ x, x ∈ D.T) (a b : (D.qsrc w hT).ι) :
    (eulerForm (D.qsrc w hT) fun _ ↦ Set.mem_univ _).c a b = (eulerForm D hT).c a.1 b.1 := by
  change (cartan (D.qsrc w hT))⁻¹ b a + (cartan (D.qsrc w hT))⁻¹ a b =
    (cartan D)⁻¹ b.1 a.1 + (cartan D)⁻¹ a.1 b.1
  rw [← euler_ind, ← euler_ind, ← euler_ind, ← euler_ind, D.euler_quotAny_source w hw hT,
    D.euler_quotAny_source w hw hT, D.extW_ind w hT, D.extW_ind w hT]

end DirData

end LargeIndecomposable.AR
