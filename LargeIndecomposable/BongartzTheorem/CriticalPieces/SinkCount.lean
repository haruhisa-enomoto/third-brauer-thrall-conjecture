module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.CriticalPoint
public import LargeIndecomposable.Quivers.Representations.ExtCount

/-!
# Point–brick data from a count of arrows and relations

Let `F` be a finite family of relations generating the relations of the cover of a piece. For a
brick `V` vanishing at `x`, the extensions of `V` by the simple representation at `x` that respect
the cover are the cocycles of `F` (`crossOK_of_cocycle`), and their dimension is at least
`Σ_{α → x} dim V(s α) - Σ_{ρ_r ending at x} dim V(s r)` (`Ext.finrank_data_le`). If this number is
at least `2`, two independent extensions give the data of Bongartz's Lemma 4
(`pointBrick_of_count`).
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

lemma kcross_eq {D : FinQuiver} (K : KroneckerPair k D)
    (z : ∀ α : D.A, K.P.obj (D.src α) →ₗ[k] K.Q₀.obj (D.tgt α)) :
    ∀ le : List D.A, K.cross z le = Ext.cross (X := K.P) (Y := K.Q₀) z le
  | [] => rfl
  | e :: le => by
    change K.Q₀.pathTot le ∘ₗ K.zOp z e + K.cross z le ∘ₗ K.P.arrOp e =
      K.Q₀.pathTot le ∘ₗ Ext.zOp z e + Ext.cross z le ∘ₗ K.P.arrOp e
    rw [kcross_eq K z le]
    rfl

lemma crossA_word {D : FinQuiver} {X Y : Rep k D} (z : Ext.Data X Y) (l : List D.A) :
    Ext.crossA z (FinQuiver.word k D l) = Ext.cross z l := by
  unfold Ext.crossA; rw [Ext.act_word, Ext.cross_eq]

lemma crossA_sub {D : FinQuiver} {X Y : Rep k D} (z : Ext.Data X Y) (a b : D.PathAlgebra k) :
    Ext.crossA z (a - b) = Ext.crossA z a - Ext.crossA z b := by
  simp [Ext.crossA, LinearMap.sub_comp, LinearMap.comp_sub]

/-- Two linearly independent vectors in a space of dimension at least two. -/
lemma exists_pair {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (h : 2 ≤ Module.finrank k W) :
    ∃ w₁ w₂ : W, ∀ c₁ c₂ : k, c₁ • w₁ + c₂ • w₂ = 0 → c₁ = 0 ∧ c₂ = 0 := by
  let b := Module.finBasis k W
  refine ⟨b ⟨0, by omega⟩, b ⟨1, by omega⟩, fun c₁ c₂ hc ↦ ?_⟩
  have hinj : Function.Injective
      (![⟨0, by omega⟩, ⟨1, by omega⟩] : Fin 2 → Fin (Module.finrank k W)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]
  have hli : LinearIndependent k ![b ⟨0, by omega⟩, b ⟨1, by omega⟩] := by
    have := b.linearIndependent.comp _ hinj
    convert this using 1
    funext i; fin_cases i <;> rfl
  exact LinearIndependent.pair_iff.1 hli c₁ c₂ hc

end LargeIndecomposable.RayCat