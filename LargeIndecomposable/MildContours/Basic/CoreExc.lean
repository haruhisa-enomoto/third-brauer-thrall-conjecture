module

public import LargeIndecomposable.MildContours.PennyFarthings.OpenAssembly
public import LargeIndecomposable.MildContours.PennyFarthings.OpenCase2
public import LargeIndecomposable.MildContours.DumbBells.RemainingFacts
public import LargeIndecomposable.MildContours.Diamonds.Conclusion

/-!
# [mild] Theorem 3, core case: everything but LPF and the exceptional categories

`coreHyp_of_exc`: the core case `CoreHyp P` holds unless `P` (or `Pᵒᵖ`) contains an
exceptional dumb-bell (`DBExc`) or the exceptional penny-farthing `Q₂'` (`PFExc`); the
only remaining ray-level input is [mild] LPF (`LPFStmt`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Opposite RayCat LargeIndecomposable

universe w

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]
  [Fintype P] [DecidableEq P] [IsFiniteRayCategory P] {k : Type w} [Field k] [Infinite k]

/-- **The open penny-farthing** from LPF, unless `P` contains `Q₂'`. -/
theorem pfOpenStmt_of_exc (hLPF : LPFStmt P k) (hNTo : NoTiny Pᵒᵖ) (hNS : NoSplit P)
    (hne : ¬PFExc P) : PFOpenStmt P k := by
  intro x D hq c a₁ w₁ hw hM hMo hE hNT z μ hμ hz
  have hl := hLPF D hq a₁ w₁ hw hM hMo hE μ hμ hz
  cases w₁ with
  | cons _ _ => simp at hl
  | nil =>
    have hw2 : D.w' = Quiver.Path.nil.cons a₁ := by rw [hw]; rfl
    have hzx : z ≠ x := by
      rintro rfl
      exact hz ⟨.nil, D.w'.cons D.β, (Quiver.Path.nil_comp _).symm⟩
    have hzt : z ≠ D.t := by
      rintro rfl
      exact hz ⟨Quiver.Path.nil.cons a₁, Quiver.Path.nil.cons D.β, D.split2 hq a₁ hw2⟩
    by_cases hex : ∃ (y : RayVert P) (_ : y ≠ x) (_ : y ≠ D.t), Nonempty (x ⟶ y)
    · obtain ⟨y, hyx, hyt, ⟨ε⟩⟩ := hex
      exact hNT _ _ (D.tiny_x0 hq a₁ hw2 hM hMo hE ε hyx hyt)
    · have hno : ∀ {y : RayVert P}, y ≠ x → y ≠ D.t → IsEmpty (x ⟶ y) :=
        fun hyx hyt ↦ ⟨fun e ↦ hex ⟨_, hyx, hyt, ⟨e⟩⟩⟩
      obtain ⟨y, hyx, hyt, γ, haγ⟩ := D.exit_t hq a₁ hw2 hM hE hno _
        (pathOf (P := P) (x := x.out) (y := z.out) μ hμ) rfl
        (by rw [pathVal_pathOf]; exact hμ) hzx hzt
      exact hne (D.case2_exc hq a₁ hw2 hM hMo hE hNT hNTo hNS hno γ.1 γ.2 hyx hyt haγ)

/-- **The core case of [mild] Theorem 3** without exceptional categories, from LPF. -/
theorem coreHyp_of_exc (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P)
    (hOS : OneSidedCyclic P) (hNPI : NoProjInj P) (hNS : NoSplit P) (hNT : NoTiny P)
    (hNTo : NoTiny Pᵒᵖ) (hLPF : LPFStmt P k)
    (hLPFo : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); letI : Fintype Pᵒᵖ := Fintype.ofFinite _
      letI : DecidableEq Pᵒᵖ := Classical.decEq _; LPFStmt Pᵒᵖ k)
    (hdb : ¬DBExc P) (hpf : ¬PFExc P)
    (hpfo : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); letI : Fintype Pᵒᵖ := Fintype.ofFinite _
      letI : DecidableEq Pᵒᵖ := Classical.decEq _; ¬PFExc Pᵒᵖ) : CoreHyp P := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  letI : Fintype Pᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq Pᵒᵖ := Classical.decEq _
  have hDB : DBStmt P k := by
    intro x y D hM' hMo' hE' hNPI' _ _
    exact hdb (D.dbExc hM' hMo' hOS hE' hNPI' hNS)
  intro x y C ω' hρ
  exact coreHyp hM hMo hE hNPI hNT hNTo (pfOpenStmt_of_exc hLPF hNTo hNS hpf)
    (pfOpenStmt_of_exc hLPFo hNT.op_op hNS.op hpfo) hDB diamondStmt C ω' hρ

end RayCat

end LargeIndecomposable
