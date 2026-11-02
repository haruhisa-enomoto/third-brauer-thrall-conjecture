module

public import LargeIndecomposable.RayCategories.Distributive.Cancel
public import LargeIndecomposable.Coverings.UniversalCover.Cover
public import LargeIndecomposable.RepresentationType.MinimalInfinite.Connected
public import LargeIndecomposable.FundamentalGroups.Basic.FreePi

/-!
# The ray category of a connected algebra is connected

If a split basic algebra `B` has no central idempotent other than `0` and `1`
(for instance if `B` is minimal representation-infinite), the fundamental
groupoid of its ray category is connected (`SplitBasicData.isConnected_fund`):
otherwise the sum of the idempotents of one component would be central.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

namespace RayCat

/-- Objects joined by a zigzag of nonzero morphisms. -/
def NZConnected {Q : Type*} [Category Q] [HasZeroMorphisms Q] (x y : Q) : Prop :=
  Relation.EqvGen (fun a b : Q ↦ ∃ f : a ⟶ b, f ≠ 0) x y

/-- A ray category whose objects are joined by zigzags of nonzero morphisms has
a connected fundamental groupoid. -/
theorem isConnected_fund_of_nzConnected {Q : Type*} [Category Q] [HasZeroMorphisms Q]
    [IsRayCategory Q] [Nonempty Q] (h : ∀ x y : Q, NZConnected x y) :
    IsConnected (FundGroupoid Q) := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty Q)
  have : Nonempty (FundGroupoid Q) := ⟨vtx x₀⟩
  have key : ∀ x y : Q, NZConnected x y → Zigzag (vtx x) (vtx y) := by
    intro x y hxy
    induction hxy with
    | rel a b hab =>
      obtain ⟨f, hf⟩ := hab
      obtain ⟨p, -⟩ := exists_path f hf
      exact Zigzag.of_hom ((CategoryTheory.Quotient.functor homotopy).map (pathFG p))
    | refl => exact Relation.ReflTransGen.refl
    | symm _ _ _ ih => exact zigzag_equivalence.symm ih
    | trans _ _ _ _ _ ih ih' => exact zigzag_equivalence.trans ih ih'
  refine zigzag_isConnected fun X Y ↦ ?_
  let base : FundGroupoid Q → Q := fun X ↦ X.as.as
  exact key (base X) (base Y) (h _ _)

end RayCat

namespace SplitBasicData

universe u v w

variable {k : Type u} [Field k] [Infinite k] {B : Type v} [Ring B] [Algebra k B]
  [FiniteDimensional k B] {ι : Type w} [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι)

open LargeIndecomposable RayCat in
/-- The objects of the ray category of a connected split basic distributive
algebra are joined by zigzags of nonzero morphisms. -/
theorem nzConnected (hd : IsDistribIdeals B) [Nonempty ι]
    (hcon : ∀ e : B, e * e = e → (∀ b, e * b = b * e) → e = 0 ∨ e = 1) :
    letI := S.distribHomStructure hd
    ∀ x y : S.toIdempotents.RayCategory, NZConnected x y := by
  letI := S.distribHomStructure hd
  letI := S.isRayCategory hd
  classical
  -- objects of the ray category indexed by `ι`
  let ob : ι → S.toIdempotents.RayCategory := fun i ↦ ⟨S.toIdempotents.projectiveVertexEquiv.symm i⟩
  have hob : ∀ i, S.toIdempotents.projectiveVertex (ob i).as = i := fun i ↦
    S.toIdempotents.projectiveVertexEquiv.apply_symm_apply i
  -- a nonzero corner element joins the two vertices
  have hzig : ∀ i j (b : B), S.e i * b * S.e j ≠ 0 → NZConnected (ob j) (ob i) := by
    intro i j b hb
    have hmem : S.e i * b * S.e j ∈ idempotentCorner (k := k) S.toIdempotents.idempotent
        (S.toIdempotents.projectiveVertex (ob i).as) (S.toIdempotents.projectiveVertex (ob j).as) := by
      rw [hob, hob, mem_idempotentCorner_iff]
      exact ⟨b, rfl⟩
    let f : (ob j).as ⟶ (ob i).as := ⟨_, hmem⟩
    have hf : (unitRay f : ob j ⟶ ob i) ≠ 0 := by
      intro h
      apply hb
      have := (unitRay_eq_zero_iff f).1 h
      exact congrArg Subtype.val this
    exact Relation.EqvGen.rel _ _ ⟨unitRay f, hf⟩
  -- the component of a base vertex
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  let C : Finset ι := Finset.univ.filter fun i ↦ NZConnected (ob i₀) (ob i)
  have hclosed : ∀ i j (b : B), S.e i * b * S.e j ≠ 0 → (i ∈ C ↔ j ∈ C) := by
    intro i j b hb
    have h := hzig i j b hb
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hi ↦ hi.trans _ _ _ (h.symm _ _), fun hj ↦ hj.trans _ _ _ h⟩
  -- the idempotent of the component
  let eC : B := ∑ i ∈ C, S.e i
  have horth := S.complete.toOrthogonalIdempotents
  have hsum : ∑ i, S.e i = 1 := S.complete.complete
  have hzero : ∀ i j (b : B), (i ∈ C ↔ j ∉ C) → S.e i * b * S.e j = 0 := by
    intro i j b hij
    by_contra hb
    exact absurd (hclosed i j b hb) (by tauto)
  have hleft : ∀ b : B, eC * b = ∑ i ∈ C, ∑ j ∈ C, S.e i * b * S.e j := by
    intro b
    calc eC * b = eC * b * ∑ j, S.e j := by rw [hsum, mul_one]
      _ = ∑ i ∈ C, ∑ j, S.e i * b * S.e j := by
        simp only [eC, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_comm
      _ = ∑ i ∈ C, ∑ j ∈ C, S.e i * b * S.e j := by
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j ↦ j ∈ C)]
        rw [Finset.sum_eq_zero (s := Finset.univ.filter fun j ↦ j ∉ C) fun j hj ↦
          hzero i j b ⟨fun _ ↦ (Finset.mem_filter.1 hj).2, fun _ ↦ hi⟩, add_zero]
        exact Finset.sum_congr (by ext j; simp) fun _ _ ↦ rfl
  have hright : ∀ b : B, b * eC = ∑ i ∈ C, ∑ j ∈ C, S.e i * b * S.e j := by
    intro b
    calc b * eC = (∑ i, S.e i) * b * eC := by rw [hsum, one_mul]
      _ = ∑ j ∈ C, ∑ i, S.e i * b * S.e j := by
        simp only [eC, Finset.sum_mul, Finset.mul_sum]
      _ = ∑ j ∈ C, ∑ i ∈ C, S.e i * b * S.e j := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i ↦ i ∈ C)]
        rw [Finset.sum_eq_zero (s := Finset.univ.filter fun i ↦ i ∉ C) fun i hi ↦
          hzero i j b ⟨fun h ↦ absurd h (Finset.mem_filter.1 hi).2, fun hnj ↦ absurd hj hnj⟩,
          add_zero]
        exact Finset.sum_congr (by ext i; simp) fun _ _ ↦ rfl
      _ = ∑ i ∈ C, ∑ j ∈ C, S.e i * b * S.e j := Finset.sum_comm
  have hidem : eC * eC = eC := by
    simp only [eC, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.sum_eq_single i]
    · exact (horth.idem i).eq
    · intro j _ hji
      exact horth.ortho hji
    · intro h; exact absurd hi h
  rcases hcon eC hidem (fun b ↦ (hleft b).trans (hright b).symm) with h0 | h1
  · -- `eC = 0` is impossible
    exfalso
    have hi₀ : i₀ ∈ C := by simp [C]; exact Relation.EqvGen.refl _
    have : S.e i₀ * eC = S.e i₀ := by
      simp only [eC, Finset.mul_sum]
      rw [Finset.sum_eq_single i₀]
      · exact (horth.idem i₀).eq
      · intro j _ hj
        exact horth.ortho (Ne.symm hj)
      · intro h; exact absurd hi₀ h
    rw [h0, mul_zero] at this
    exact S.ne_zero i₀ this.symm
  · -- `eC = 1`: every vertex lies in the component
    have hall : ∀ i, i ∈ C := by
      intro i
      by_contra hi
      have : S.e i * eC = 0 := by
        simp only [eC, Finset.mul_sum]
        refine Finset.sum_eq_zero fun j hj ↦ horth.ortho fun h ↦ hi (h ▸ hj)
      rw [h1, mul_one] at this
      exact S.ne_zero i this
    have hX : ∀ x : S.toIdempotents.RayCategory, NZConnected (ob i₀) x := by
      intro x
      have hx : x = ob (S.toIdempotents.projectiveVertex x.as) := by
        obtain ⟨y⟩ := x
        change (⟨y⟩ : S.toIdempotents.RayCategory) = ⟨S.toIdempotents.projectiveVertexEquiv.symm
          (S.toIdempotents.projectiveVertexEquiv y)⟩
        rw [Equiv.symm_apply_apply]
      rw [hx]
      have := hall (S.toIdempotents.projectiveVertex x.as)
      simpa [C] using this
    intro x y
    exact ((hX x).symm _ _).trans _ _ _ (hX y)

open LargeIndecomposable RayCat in
/-- The fundamental groupoid of the ray category of a connected split basic
distributive algebra is connected. -/
theorem isConnected_fund (hd : IsDistribIdeals B) [Nonempty ι]
    (hcon : ∀ e : B, e * e = e → (∀ b, e * b = b * e) → e = 0 ∨ e = 1) :
    letI := S.distribHomStructure hd
    letI := S.isRayCategory hd
    IsConnected (FundGroupoid S.toIdempotents.RayCategory) := by
  letI := S.distribHomStructure hd
  letI := S.isRayCategory hd
  have : Nonempty S.toIdempotents.RayCategory := ⟨⟨S.toIdempotents.projectiveVertexEquiv.symm (Classical.arbitrary ι)⟩⟩
  exact isConnected_fund_of_nzConnected (S.nzConnected hd hcon)

open RayCat in
/-- **Fischbacher for distributive minimal representation-infinite algebras**
(no crown): if the ray category is chain-bounded, its fundamental group is free. -/
theorem isFreeGroup_end_of_chainBounded (hd : IsDistribIdeals B) (hB : IsMinimalRepInfinite B)
    [Nonempty ι] :
    letI := S.distribHomStructure hd
    ChainBounded S.toIdempotents.RayCategory →
      ∀ X : FundGroupoid S.toIdempotents.RayCategory, IsFreeGroup (End X) := by
  letI := S.distribHomStructure hd
  have := S.isFiniteRayCategory hd
  intro hCB X
  have hcon := S.isConnected_fund hd fun e he hc ↦ hB.central_idempotent e he hc
  exact isFreeGroup_end_fund _ _ (S.leftCancel hd) (S.rightCancel hd) hCB hcon le_rfl X

end SplitBasicData

end LargeIndecomposable
