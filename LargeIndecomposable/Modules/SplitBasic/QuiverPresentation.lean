module

public import LargeIndecomposable.Foundations.Ring.NilGen
public import LargeIndecomposable.Quivers.PathAlgebras.FiniteQuiver
public import LargeIndecomposable.Modules.SplitBasic.SplitBasicAlgebras
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import Mathlib.RingTheory.Artinian.Algebra

/-!
# Presentations of split basic algebras by quivers

Gabriel's presentation in the form needed for the data of Theorem 3.10: a
finite-dimensional split basic algebra `B` with idempotents `e_x` is a quotient
of a path algebra `kQ`. The vertices of `Q` are the `x`, the arrows `x → y` are
lifts to `e_y J e_x` of a basis of the corner `e_y (J/J²) e_x` of the first
radical layer, and `π : kQ → B` sends `e_x ↦ e_x` and each arrow to its lift
(`SplitBasicData.presentation`). It is surjective by the nilpotent generation
criterion (`NilGen.surjective_of_nilpotent_ideal`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

universe u v

namespace FinQuiver

variable {k : Type u} [Field k] (Q : FinQuiver) {R : Type v} [Ring R] [Algebra k R]

/-- The algebra map out of `kQ` given by images of the vertices and arrows
satisfying the defining relations. -/
def lift (ev : Q.V → R) (ea : Q.A → R)
    (h_idem : ∀ v w, ev v * ev w = if v = w then ev v else 0) (h_one : ∑ v, ev v = 1)
    (h_src : ∀ a, ea a * ev (Q.src a) = ea a) (h_tgt : ∀ a, ev (Q.tgt a) * ea a = ea a) :
    Q.PathAlgebra k →ₐ[k] R :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k (Sum.elim ev ea), by
    intro x y h
    cases h with
    | idem v w =>
        simp only [map_mul, FreeAlgebra.lift_ι_apply, Sum.elim_inl, h_idem]
        split_ifs <;> simp
    | one => simp [map_sum, h_one]
    | src a => simp [h_src]
    | tgt a => simp [h_tgt]⟩

variable {Q}

@[simp]
lemma lift_vertex (ev : Q.V → R) (ea : Q.A → R) (h₁ h₂ h₃ h₄) (v : Q.V) :
    Q.lift (k := k) ev ea h₁ h₂ h₃ h₄ (vertex k Q v) = ev v := by
  simp [lift, vertex]

@[simp]
lemma lift_arrow (ev : Q.V → R) (ea : Q.A → R) (h₁ h₂ h₃ h₄) (a : Q.A) :
    Q.lift (k := k) ev ea h₁ h₂ h₃ h₄ (arrow k Q a) = ea a := by
  simp [lift, arrow]

end FinQuiver

namespace SplitBasicData

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B] [FiniteDimensional k B]
  {ι : Type} [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι)

/-- The radical `J` as a `k`-subspace. -/
abbrev Jk : Submodule k B := (Ring.jacobson B).restrictScalars k

/-- The radical square `J²` as a `k`-subspace. -/
abbrev J2k : Submodule k B := (Ring.jacobson B ^ 2).restrictScalars k

/-- `b ↦ [e_y b e_x]` into `B / J²`. -/
def cornerMap (x y : ι) : B →ₗ[k] B ⧸ J2k (k := k) (B := B) :=
  (J2k (k := k) (B := B)).mkQ ∘ₗ (LinearMap.mulLeft k (S.e y) ∘ₗ LinearMap.mulRight k (S.e x))

/-- The corner `e_y (J/J²) e_x` of the first radical layer. -/
def firstLayer (x y : ι) : Submodule k (B ⧸ J2k (k := k) (B := B)) := (Jk (k := k) (B := B)).map (S.cornerMap x y)

/-- A basis of the corner of the first layer. -/
def firstLayerBasis (x y : ι) : Module.Basis (Fin (Module.finrank k (S.firstLayer x y))) k (S.firstLayer x y) :=
  Module.finBasis k (S.firstLayer x y)

/-- A lift to `J` of a basis vector of the corner of the first layer. -/
def liftJ (x y : ι) (i : Fin (Module.finrank k (S.firstLayer x y))) : B :=
  ((S.firstLayerBasis x y i).2).choose

omit [DecidableEq ι] in
lemma liftJ_mem (x y : ι) (i) : S.liftJ x y i ∈ Ring.jacobson B :=
  ((S.firstLayerBasis x y i).2).choose_spec.1

omit [DecidableEq ι] in
lemma cornerMap_liftJ (x y : ι) (i) : S.cornerMap x y (S.liftJ x y i) = S.firstLayerBasis x y i :=
  ((S.firstLayerBasis x y i).2).choose_spec.2

/-- The quiver of the presentation: arrows `x → y` index a basis of
`e_y (J/J²) e_x`. -/
abbrev quiver : FinQuiver where
  V := ι
  A := Σ p : ι × ι, Fin (Module.finrank k (S.firstLayer p.1 p.2))
  src a := a.1.1
  tgt a := a.1.2

/-- The image of an arrow: `e_y j e_x` for the chosen lift `j`. -/
def arrVal (a : S.quiver.A) : B := S.e a.1.2 * S.liftJ a.1.1 a.1.2 a.2 * S.e a.1.1

lemma arrVal_mem (a : S.quiver.A) : S.arrVal a ∈ Ring.jacobson B :=
  Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (S.liftJ_mem _ _ _))

/-- The presentation `kQ → B`. -/
def presentation : S.quiver.PathAlgebra k →ₐ[k] B :=
  S.quiver.lift (k := k) S.e S.arrVal
    (fun v w ↦ by
      by_cases h : v = w
      · subst h; rw [ite_eq_left rfl]; exact S.e_mul_e v
      · simp [h, S.complete.ortho h])
    S.sum_eq_one
    (fun a ↦ by simp only [arrVal, mul_assoc, S.e_mul_e])
    (fun a ↦ by simp only [arrVal, ← mul_assoc, S.e_mul_e])

@[simp]
lemma presentation_vertex (x : ι) : S.presentation (FinQuiver.vertex k S.quiver x) = S.e x := by
  simp [presentation]

@[simp]
lemma presentation_arrow (a : S.quiver.A) :
    S.presentation (FinQuiver.arrow k S.quiver a) = S.arrVal a := by
  simp [presentation]

omit [FiniteDimensional k B] [DecidableEq ι] in
lemma cornerMap_corner (x y : ι) (b : B) :
    S.cornerMap x y (S.e y * b * S.e x) = S.cornerMap x y b := by
  simp only [cornerMap, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
    LinearMap.mulLeft_apply]
  congr 1
  calc S.e y * (S.e y * b * S.e x * S.e x) = (S.e y * S.e y) * b * (S.e x * S.e x) := by
        simp only [mul_assoc]
    _ = S.e y * (b * S.e x) := by rw [S.e_mul_e, S.e_mul_e, mul_assoc]

/-- Gabriel's presentation: `kQ → B` is surjective. -/
theorem presentation_surjective : Function.Surjective S.presentation := by
  have hnil : IsNilpotent (Ring.jacobson B) := by
    have : IsArtinianRing B := IsArtinianRing.of_finite k B
    exact IsSemiprimaryRing.isNilpotent
  refine NilGen.surjective_of_nilpotent_ideal S.presentation (Ring.jacobson B) hnil ?_ ?_
  · -- modulo `J`, `B` is spanned by the `e_x`
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    choose c hc using fun x ↦ S.corner_diag x b
    refine ⟨∑ x, c x • FinQuiver.vertex k S.quiver x, ?_⟩
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      show S.presentation (∑ x, c x • FinQuiver.vertex k S.quiver x) = ∑ x, c x • S.e x by simp]
    refine Ideal.Quotient.eq.2 ?_
    have hb : b = ∑ x, ∑ y, S.e x * b * S.e y := (S.sum_corners b).symm
    have : ∑ x, c x • S.e x - b = ∑ x, ∑ y, ((if x = y then c x • S.e x else 0) -
        S.e x * b * S.e y) := by
      conv_lhs => rw [hb]
      simp [Finset.sum_sub_distrib]
    rw [this]
    refine Submodule.sum_mem _ fun x _ ↦ Submodule.sum_mem _ fun y _ ↦ ?_
    by_cases h : x = y
    · subst h
      simp only [ite_true]
      rw [← neg_sub]
      exact (Ideal.neg_mem_iff _).2 (hc x)
    · simp only [h, ite_false, zero_sub]
      exact (Ideal.neg_mem_iff _).2 (S.corner_offdiag x y h b)
  · -- the arrows span the first layer
    intro j hj
    have hj' : j ∈ Ring.jacobson B := (Submodule.restrictScalars_mem k _ _).1 hj
    rw [← S.sum_corners j, Finset.sum_comm]
    refine Submodule.sum_mem _ fun x _ ↦ Submodule.sum_mem _ fun y _ ↦ ?_
    have hm : S.cornerMap x y j ∈ S.firstLayer x y := ⟨j, hj, rfl⟩
    set w : S.firstLayer x y := ⟨_, hm⟩
    have hw := (S.firstLayerBasis x y).sum_repr w
    set r : B := ∑ i, (S.firstLayerBasis x y).repr w i • S.arrVal ⟨(x, y), i⟩
    have hr : r ∈ S.presentation.range.toSubmodule := by
      refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ ?_
      exact ⟨FinQuiver.arrow k S.quiver ⟨(x, y), i⟩, presentation_arrow _ _⟩
    have hcm : ∀ i, S.cornerMap x y (S.arrVal ⟨(x, y), i⟩) = S.firstLayerBasis x y i := fun i ↦
      (S.cornerMap_corner x y _).trans (S.cornerMap_liftJ x y i)
    have hmap : S.cornerMap x y r = (w : B ⧸ J2k (k := k) (B := B)) := by
      calc S.cornerMap x y r
          = ∑ i, (S.firstLayerBasis x y).repr w i • ((S.firstLayerBasis x y i : S.firstLayer x y) :
              B ⧸ J2k (k := k) (B := B)) := by
            simp only [r, map_sum, _root_.map_smul, hcm]
        _ = w := by
            conv_rhs => rw [← hw]
            simp only [Submodule.coe_sum, Submodule.coe_smul]
    have hr' : S.e y * r * S.e x = r := by
      simp only [r, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, arrVal]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      congr 1
      calc S.e y * (S.e y * S.liftJ x y i * S.e x) * S.e x
          = (S.e y * S.e y) * S.liftJ x y i * (S.e x * S.e x) := by simp only [mul_assoc]
        _ = _ := by rw [S.e_mul_e, S.e_mul_e]
    set d := S.e y * j * S.e x - r
    have hd : S.e y * d * S.e x = d := by
      simp only [d, mul_sub, sub_mul, hr']
      congr 1
      calc S.e y * (S.e y * j * S.e x) * S.e x = (S.e y * S.e y) * j * (S.e x * S.e x) := by
            simp only [mul_assoc]
        _ = _ := by rw [S.e_mul_e, S.e_mul_e]
    have h0 : S.cornerMap x y d = 0 := by
      rw [map_sub, S.cornerMap_corner, hmap, sub_eq_zero]
    have hdiff : d ∈ J2k (k := k) (B := B) := by
      have := (Submodule.Quotient.mk_eq_zero _).1 h0
      rw [← hd, mul_assoc]
      exact this
    have : S.e y * j * S.e x = r + d := by simp only [d]; abel
    rw [this]
    exact Submodule.add_mem_sup hr hdiff

end SplitBasicData

end LargeIndecomposable
