module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.SinkCount

/-!
# Point–brick data from two independent cocycles

If `V` is a sincere brick off a vertex `x`, vanishing at `x` and respecting the cover, and the
cocycles of a generating family of relations from `V` to the simple representation at `x` have
dimension at least two (that is, `dim Ext¹(V, S_x) ≥ 2`), then `PointBrick` holds
(`pointBrick_of_cocycles`). `pointBrick_of_count` is the special case of a count.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Statement Cover RayQuiver Covering FinQuiver

universe u

variable {k : Type u} [Field k]
  {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)}

/-- **Point–brick data from two independent cocycles.** -/
theorem pointBrick_of_cocycles (F : Ext.RelFam (pieceQuiver S) k)
    (hF : ∀ r, F.ρ r ∈ TwoSidedIdeal.span (relGens k S))
    (hgen : relGens k S ⊆ TwoSidedIdeal.span (Set.range F.ρ))
    (x : (pieceQuiver S).V) (V : Rep k (pieceQuiver S)) (finV : ∀ i, FiniteDimensional k (V.obj i))
    (hVx : Subsingleton (V.obj x))
    (brickV : ∀ f : V ⟶ V, ∃ c : k, ∀ i, (f.app i).hom = c • LinearMap.id)
    (hV : ∃ i, Nontrivial (V.obj i)) (hsinc : ∀ i, i ≠ x → Nontrivial (V.obj i))
    (hVc : RespectsCover V)
    (h2 : 2 ≤ Module.finrank k (Ext.cocycles F (X := V) (Y := Rep.pointRep (k := k) x))) :
    PointBrick (k := k) S := by
  haveI := finV
  haveI : ∀ i, FiniteDimensional k ((Rep.pointRep (k := k) x).obj i) := fun i ↦
    inferInstanceAs (FiniteDimensional k (Fin _ → k))
  obtain ⟨w₁, w₂, hw⟩ := exists_pair h2
  have hind : ∀ c₁ c₂ : k, (∀ α, c₁ • (w₁ : Ext.Data V (Rep.pointRep (k := k) x)) α +
      c₂ • (w₂ : Ext.Data V (Rep.pointRep (k := k) x)) α = 0) → c₁ = 0 ∧ c₂ = 0 := by
    intro c₁ c₂ hc
    apply hw
    apply Subtype.ext
    funext α
    simpa using hc α
  have hK : ∀ w : Ext.cocycles F (X := V) (Y := Rep.pointRep (k := k) x),
      CrossOK (pairAtSink x V finV hVx brickV hV (w₁ : Ext.Data V (Rep.pointRep (k := k) x))
        (w₂ : Ext.Data V (Rep.pointRep (k := k) x)) hind)
        (w : Ext.Data V (Rep.pointRep (k := k) x)) := fun w ↦
    crossOK_of_cocycle _ hVc (respectsCover_pointRep x) F hF hgen _ w.2
  exact ⟨x, V, finV, hVx, brickV, hV, hsinc, hVc,
    Or.inr ⟨(w₁ : Ext.Data V (Rep.pointRep (k := k) x)),
      (w₂ : Ext.Data V (Rep.pointRep (k := k) x)), hind, hK w₁, hK w₂⟩⟩

end LargeIndecomposable.RayCat
