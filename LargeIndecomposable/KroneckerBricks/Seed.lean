module

public import LargeIndecomposable.KroneckerBricks.Transport
public import LargeIndecomposable.KroneckerBricks.Medium

/-!
# The `T_Λ` anchored families

Over an infinite field, distinct subsets `X_j ⊆ k` give pairwise orthogonal
bricks `T_{Λ_{X_j}}`, orthogonal to the anchor `T_{Λ₀}`, with explicit
non-split classes (`KroneckerBricks/Medium.lean`, `KroneckerBricks/NonSplit.lean`). This is an
anchored family over any index type `J` with `J ↪ Set k`
(`Bricks.lamAnchored`); for `J` countable it is the `ω`-seed used to transport
rigid `R_ω`-structures.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair

universe u

variable {k : Type u} [Field k] [Infinite k]

namespace Bricks

/-- The `T_Λ` anchored family over `J ↪ Set k`. -/
def lamAnchored {J : Type u} (e : J ↪ Set k) : Anchored k J where
  C := T (Lam0 : Set k)
  B j := T (LamX (e j))
  α _ := 0
  β j := betaExt (LamX (e j)) Lam0 (diff_lam0_infinite (e j)).nonempty.some
  hC := isBrick _ lam0_nonempty
  hB j := isBrick _ ((diff_lam0_infinite (e j)).nonempty.mono Set.sdiff_subset)
  hCB _ := hom_eq_zero (lam0_diff_infinite _)
  hBC _ := hom_eq_zero (diff_lam0_infinite _)
  hBB i j h := hom_eq_zero (diff_infinite fun h' ↦ h (e.injective h'))
  hns j := not_splits (diff_lam0_infinite _) (diff_lam0_infinite (e j)).nonempty.some_mem
  c0 := Finsupp.single ⟨pt0 0, 0, by simp [pt0]⟩ 1
  hc0 := Finsupp.single_ne_zero.2 one_ne_zero
  y j := Finsupp.single ⟨(diff_lam0_infinite (e j)).nonempty.some,
    (diff_lam0_infinite (e j)).nonempty.some_mem.1⟩ 1
  hy _ := Finsupp.single_ne_zero.2 one_ne_zero

variable (k) in
/-- The countable `ω`-seed. -/
def omegaSeed : Anchored k Nu :=
  lamAnchored ⟨fun n ↦ Infinite.natEmbedding (Set k) n.down,
    fun _ _ h ↦ ULift.ext ((Infinite.natEmbedding (Set k)).injective h)⟩

end Bricks

end LargeIndecomposable
