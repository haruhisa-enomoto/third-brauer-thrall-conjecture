module

public import LargeIndecomposable.MildContours.Basic.SplitBridge
public import LargeIndecomposable.RepresentationType.MinimalInfinite.Connected

/-!
# The ray category of a minimal representation-infinite algebra is connected

A set `V` of objects with no nonzero morphism between `V` and its complement gives a
central idempotent `Σ_{v ∈ V} e_v` of `B`, which is `0` or `1`
(`IsMinimalRepInfinite.central_idempotent`); so `V` is empty or everything
(`SplitBasicData.isolated_trivial`, and `isolated_trivial_small` for the small model).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable RayCat

namespace RayCat

variable {Q : Type*} [Category Q] [HasZeroMorphisms Q]

/-- `V` is a union of connected components: no nonzero morphism leaves or enters it. -/
def Isolated (V : Set Q) : Prop :=
  (∀ i ∈ V, ∀ j, j ∉ V → ∀ f : i ⟶ j, f = 0) ∧ ∀ i, i ∉ V → ∀ j ∈ V, ∀ f : i ⟶ j, f = 0

end RayCat

namespace RayCat.RaySmall

universe w v u'

variable {P : Type u'} [Category.{v} P] [LocallySmall.{w} P] [HasZeroMorphisms P]

/-- **`Isolated` passes from the small model to `P`.** -/
theorem isolated_of_small {V : Set (RaySmall.{u'} P)} (h : Isolated V) :
    Isolated {p : P | (⟨p⟩ : RaySmall.{u'} P) ∈ V} := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun i hi j hj f ↦ ?_, fun i hi j hj f ↦ ?_⟩
  · exact (sh_eq_zero_iff.{w} (X := ⟨i⟩) (Y := ⟨j⟩) f).1 (h1 _ hi _ hj _)
  · exact (sh_eq_zero_iff.{w} (X := ⟨i⟩) (Y := ⟨j⟩) f).1 (h2 _ hi _ hj _)

end RayCat.RaySmall

universe u

namespace SplitBasicData

variable {k : Type u} [Field k] [IsAlgClosed k] {B : Type u} [Ring B] [Algebra k B]
  [FiniteDimensional k B] {ι : Type} [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι)
  [HasBGRSDistributiveHomStructure k S.toIdempotents.ProjectiveCategory]

/-- **An isolated set of objects is empty or everything.** -/
theorem isolated_trivial (hB : IsMinimalRepInfinite B) (V : Set S.toIdempotents.RayCategory)
    (hV : Isolated V) : (∀ X, X ∉ V) ∨ ∀ X, X ∈ V := by
  classical
  obtain ⟨h1, h2⟩ := hV
  let F := Finset.univ.filter fun v ↦ S.R v ∈ V
  let G := Finset.univ.filter fun v ↦ S.R v ∉ V
  have mF : ∀ {v}, v ∈ F ↔ S.R v ∈ V := by simp [F]
  have mG : ∀ {v}, v ∈ G ↔ S.R v ∉ V := by simp [G]
  set e := ∑ v ∈ F, S.e v with he
  set e' := ∑ v ∈ G, S.e v with he'
  have hsum : e + e' = 1 := by
    rw [he, he', ← S.sum_e]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have mulsum : ∀ (A C : Finset ι) (b : B), (∀ v ∈ A, ∀ w ∈ C, S.e v * b * S.e w = 0) →
      (∑ v ∈ A, S.e v) * b * (∑ w ∈ C, S.e w) = 0 := by
    intro A C b h
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_eq_zero fun v hv ↦ ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun w hw ↦ h v hv w hw
  have z1 : ∀ b, e * b * e' = 0 := fun b ↦ mulsum _ _ b fun v hv w hw ↦
    S.zr v w b fun f ↦ h2 _ (mG.1 hw) _ (mF.1 hv) f
  have z2 : ∀ b, e' * b * e = 0 := fun b ↦ mulsum _ _ b fun w hw v hv ↦
    S.zr w v b fun f ↦ h1 _ (mF.1 hv) _ (mG.1 hw) f
  have hee : e * e = e := by rw [he, S.sum_mul_sum, Finset.inter_self]
  have hc : ∀ b, e * b = b * e := by
    intro b
    have l : e * b = e * b * e := by
      conv_lhs => rw [← mul_one (e * b), ← hsum, mul_add, z1, add_zero]
    have r : b * e = e * b * e := by
      conv_lhs => rw [← one_mul (b * e), ← hsum, add_mul, ← mul_assoc e' b e, z2, add_zero,
        ← mul_assoc]
    rw [l, r]
  rcases hB.central_idempotent e hee hc with h0 | h0
  · left
    intro X hX
    obtain ⟨v, rfl⟩ : ∃ v, S.R v = X := ⟨_, S.R_vert X⟩
    apply S.ne_zero v
    have := S.e_mul_sum F v
    rw [if_pos (mF.2 hX), ← he, h0, mul_zero] at this
    exact this.symm
  · right
    intro X
    obtain ⟨v, rfl⟩ : ∃ v, S.R v = X := ⟨_, S.R_vert X⟩
    by_contra hX
    apply S.ne_zero v
    have := S.e_mul_sum F v
    rw [if_neg (fun h ↦ hX (mF.1 h)), ← he, h0, mul_one] at this
    exact this

/-- **The small ray category is connected.** -/
theorem isolated_trivial_small (hB : IsMinimalRepInfinite B) [LocallySmall.{0} S.toIdempotents.RayCategory]
    (V : Set (RaySmall.{0} S.toIdempotents.RayCategory)) (hV : Isolated V) :
    (∀ X, X ∉ V) ∨ ∀ X, X ∈ V := by
  rcases S.isolated_trivial hB _ (RaySmall.isolated_of_small hV) with h | h
  · exact Or.inl fun X hX ↦ h X.as hX
  · exact Or.inr fun X ↦ h X.as

end SplitBasicData

end LargeIndecomposable
