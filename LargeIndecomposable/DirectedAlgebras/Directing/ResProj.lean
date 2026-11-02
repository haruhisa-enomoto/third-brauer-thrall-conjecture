module

public import LargeIndecomposable.AuslanderReiten.AlmostSplit.ARUnique

/-!
# Projectives of a successor-closed quotient

If `P(z)` lives on `T'` (for instance `z ∈ B` with `B` successor-closed), the vertex projective of
the quotient algebra restricts to `P(z)` (`isoM_res_proj`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

namespace DirData

variable {D : DirData k A} {T' : Set D.ι} (hT : D.ConvexSet T')

/-- **The quotient projective at `z` restricts to `P(z)`.** -/
theorem isoM_res_proj (z : D.ι) (hz : LivesOn T' (projE (k := k) (D.idem z))) :
    IsoM (projE (k := k) (D.idem z))
      (resFD (D.qmap T') (projE (k := k) ((D.quot hT).idem z))) := by
  let P := projE (k := k) (D.idem z)
  let ez : P := ⟨D.e z, e_mem (D.idem z)⟩
  -- `Φ : a ↦ qmap a`
  let Φ : P ⟶ resFD (D.qmap T') (projE (k := k) ((D.quot hT).idem z)) :=
    FDMod.ofLin
    { toFun a := ofX (⟨D.qmap T' (a : A), by
        change D.qmap T' (a : A) * D.qmap T' (D.e z) = D.qmap T' (a : A)
        rw [← map_mul, show (a : A) * D.e z = a from a.2]⟩ : leftIdeal ((D.quot hT).idem z))
      map_add' a b := by
        apply toX_injective; apply Subtype.ext
        change D.qmap T' ((a : A) + b) = D.qmap T' a + D.qmap T' b
        rw [map_add]
      map_smul' c a := by
        apply toX_injective; apply Subtype.ext
        change D.qmap T' (c * (a : A)) = D.qmap T' c * D.qmap T' a
        rw [map_mul] }
  -- `Ψ : b' ↦ b' • e_z` in the descent of `P(z)`
  let Ψ : resFD (D.qmap T') (projE (k := k) ((D.quot hT).idem z)) ⟶ P :=
    FDMod.ofLin
    { toFun b := actQ P hz ((toX b : leftIdeal ((D.quot hT).idem z)) : D.QAlg T') ez
      map_add' a b := by
        change actQ P hz (((toX a : leftIdeal _) : D.QAlg T') + (toX b : leftIdeal _)) ez = _
        rw [map_add]; rfl
      map_smul' c b := by
        change actQ P hz (D.qmap T' c * ((toX b : leftIdeal _) : D.QAlg T')) ez = _
        rw [map_mul, Module.End.mul_apply, actQ_qmap]
        rfl }
  have hΨΦ : ∀ a : P, FDMod.lin Ψ (FDMod.lin Φ a) = a := fun a ↦ by
    change actQ P hz (D.qmap T' (a : A)) ez = a
    rw [actQ_qmap]
    apply Subtype.ext
    exact a.2
  refine ⟨Φ, fun a b h ↦ by rw [← hΨΦ a, ← hΨΦ b, h], fun b ↦ ⟨FDMod.lin Ψ b, ?_⟩⟩
  apply toX_injective; apply Subtype.ext
  obtain ⟨a, ha⟩ := D.qmap_surjective T' ((toX b : leftIdeal ((D.quot hT).idem z)) : D.QAlg T')
  have hb : ((toX b : leftIdeal ((D.quot hT).idem z)) : D.QAlg T') * D.qmap T' (D.e z) =
      (toX b : leftIdeal ((D.quot hT).idem z)) := (toX b).2
  change D.qmap T' ((actQ P hz ((toX b : leftIdeal _) : D.QAlg T') ez : P) : A) = _
  rw [← ha, actQ_qmap]
  change D.qmap T' (a * D.e z) = _
  rw [map_mul, ha, hb]

end DirData

end LargeIndecomposable.AR
