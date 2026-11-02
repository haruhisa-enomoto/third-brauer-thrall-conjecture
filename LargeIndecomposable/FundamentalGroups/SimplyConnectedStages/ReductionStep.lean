module

public import LargeIndecomposable.FundamentalGroups.SimplyConnectedStages.ChainHull
public import LargeIndecomposable.FundamentalGroups.SimplyConnectedStages.StageBase

/-!
# The reduction step of Satz 5.1

The base stage is good (`cycleFree_base`, `intervalFinite_base`, `sc_univ`), restoring finitely
many points keeps it good (`good_finite`), and the limit step gives a good universal cover
(`coverGood_limit`). This proves `SimplyConnectedStageStep`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

attribute [local instance] isRayCategory_of_finiteRayCategory

/-- **The reduction step of Fischbacher's Satz 5.1.** -/
theorem simplyConnectedStageStep : SimplyConnectedStageStep := by
  intro Q _ _ _ _ ι b d α hα D hE hL hR hCB hLF hQ' x₀
  letI := (arrowIdeal α).quotientIsFiniteRayCategory0 (arrowIdeal_isProper α hα)
  have hG0 : Stage.Good (x₀ := x₀) (α := α) Set.univ :=
    ⟨Stage.cycleFree_base hα D hE (hQ' _), fun a a' ↦ Stage.intervalFinite_base hα D hE (hQ' _) a a',
      fun c hc ↦ Stage.sc_univ hα D hE c hc⟩
  exact Stage.coverGood_limit hL hR hCB (Stage.good_finite D hα hLF hL hR hCB hG0)

end LargeIndecomposable.RayCat
