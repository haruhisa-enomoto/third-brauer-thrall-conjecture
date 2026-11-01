module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.PieceTits
public import LargeIndecomposable.Quivers.Representations.ExtEuler

/-!
# Directing modules with the same dimension vector

For representations `X`, `Y` of a piece killed by a family `F` of relations and with the same
dimension vector `x`, the Euler characteristic of the cocycle complex gives
`dim Hom(X, Y) ≥ q_F(x) - dim H²(X, Y)` (`one_le_finrank_hom`). So if `q_F(x) ≥ 1` and `H²` vanishes
in both directions, there are nonzero morphisms both ways; for a directing module and a
non-isomorphic indecomposable this is a cycle (`not_directing_of_hom_hom`; ASS IX.3.1).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver Module

universe u

section Fam

variable {k : Type u} [Field k] {D : FinQuiver} {X Y : Rep k D}

/-- A family in the kernel of the coboundary map is a morphism. -/
def homOfFam (h : ∀ i, X.obj i →ₗ[k] Y.obj i) (hh : h ∈ LinearMap.ker (Ext.cobL (X := X) (Y := Y))) :
    X ⟶ Y where
  app i := ModuleCat.ofHom (h i)
  comm α := by
    have h0 := congrFun (LinearMap.mem_ker.1 hh) α
    change h (D.tgt α) ∘ₗ (X.map α).hom - (Y.map α).hom ∘ₗ h (D.src α) = 0 at h0
    ext v
    have := LinearMap.congr_fun h0 v
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply, sub_eq_zero] at this
    exact this

lemma homOfFam_app (h : ∀ i, X.obj i →ₗ[k] Y.obj i)
    (hh : h ∈ LinearMap.ker (Ext.cobL (X := X) (Y := Y))) (i : D.V) :
    ((homOfFam h hh).app i).hom = h i := rfl

end Fam

variable {k : Type u} [Field k]
  {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)}

/-- **Morphisms from the Tits form.** -/
theorem one_le_finrank_hom (F : Ext.RelFam (pieceQuiver S) k)
    {X Y : Rep k (pieceQuiver S)} [∀ i, FiniteDimensional k (X.obj i)]
    [∀ i, FiniteDimensional k (Y.obj i)] (hX : ∀ r, Ext.act X (F.ρ r) = 0)
    (hY : ∀ r, Ext.act Y (F.ρ r) = 0) (x : (pieceQuiver S).V → ℕ)
    (hXd : ∀ i, finrank k (X.obj i) = x i) (hYd : ∀ i, finrank k (Y.obj i) = x i)
    (hq : 1 ≤ titsF F (fun i ↦ (x i : ℤ))) (hH2 : Ext.dimH2 F (X := X) (Y := Y) = 0) :
    1 ≤ finrank k (LinearMap.ker (Ext.cobL (X := X) (Y := Y))) := by
  have he := Ext.euler_cocycle_complex F (X := X) (Y := Y)
  have hH1 : 0 ≤ Ext.dimH1 F (X := X) (Y := Y) := by
    unfold Ext.dimH1
    have : LinearMap.range (Ext.cobL (X := X) (Y := Y)) ≤ Ext.cocycles F (X := X) (Y := Y) := by
      rintro _ ⟨h, rfl⟩
      exact Ext.cob_mem_cocycles F hX hY h
    have := Submodule.finrank_mono this
    omega
  simp only [hXd, hYd] at he
  unfold titsF at hq
  push_cast at he
  rw [hH2] at he
  have : (1 : ℤ) ≤ finrank k (LinearMap.ker (Ext.cobL (X := X) (Y := Y))) := by linarith
  exact_mod_cast this

/-- A nonzero family in the kernel gives a nonzero module map. -/
lemma toFDModHom_ne_zero {X Y : Rep k (pieceQuiver S)} (hX : RespectsCover X)
    (hY : RespectsCover Y) [∀ i, FiniteDimensional k (X.obj i)]
    [∀ i, FiniteDimensional k (Y.obj i)] (h : ∀ i, X.obj i →ₗ[k] Y.obj i)
    (hh : h ∈ LinearMap.ker (Ext.cobL (X := X) (Y := Y))) (hne : h ≠ 0) :
    AR.FDMod.lin (toFDModHom hX hY (homOfFam h hh)) ≠ 0 := by
  intro h0
  apply hne
  funext i
  refine LinearMap.ext fun v ↦ ?_
  have := congrFun (show (homOfFam h hh).tot (Pi.single i v) = 0 from
    LinearMap.congr_fun h0 (show X.Tot from Pi.single i v)) i
  rw [Rep.Hom.tot_apply, Pi.single_eq_same, homOfFam_app] at this
  exact this

/-- **Nonzero morphisms both ways between different indecomposables break directedness.** -/
theorem not_directing_of_hom_hom [FiniteDimensional k (PieceAlg k S)]
    {X Y : Rep k (pieceQuiver S)} (hX : RespectsCover X)
    (hY : RespectsCover Y) [∀ i, FiniteDimensional k (X.obj i)]
    [∀ i, FiniteDimensional k (Y.obj i)] (hXi : AR.IsInd (toFDMod X hX))
    (hYi : AR.IsInd (toFDMod Y hY)) (hni : ¬AR.IsoM (toFDMod X hX) (toFDMod Y hY))
    (h₁ : 1 ≤ finrank k (LinearMap.ker (Ext.cobL (X := X) (Y := Y))))
    (h₂ : 1 ≤ finrank k (LinearMap.ker (Ext.cobL (X := Y) (Y := X)))) :
    ¬AR.Directing (toFDMod X hX) := by
  obtain ⟨⟨f, hf⟩, hf0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 h₁
  obtain ⟨⟨g, hg⟩, hg0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 h₂
  have hf' : f ≠ 0 := fun h ↦ hf0 (Subtype.ext h)
  have hg' : g ≠ 0 := fun h ↦ hg0 (Subtype.ext h)
  intro hD
  have hnb : ∀ (φ : toFDMod X hX ⟶ toFDMod Y hY), ¬Function.Bijective (AR.FDMod.lin φ) :=
    fun φ hb ↦ hni ⟨φ, hb⟩
  have hnb' : ∀ (φ : toFDMod Y hY ⟶ toFDMod X hX), ¬Function.Bijective (AR.FDMod.lin φ) := by
    intro φ hb
    exact hni ⟨(LinearEquiv.ofBijective _ hb).symm.toLinearMap, (LinearEquiv.bijective _)⟩
  exact hD.2 (AR.Reach₁.trans
    (AR.Reach₁.step hXi hYi _ (toFDModHom_ne_zero hX hY f hf hf') (hnb _))
    (AR.Reach₁.step hYi hXi _ (toFDModHom_ne_zero hY hX g hg hg') (hnb' _)))

end LargeIndecomposable.RayCat
