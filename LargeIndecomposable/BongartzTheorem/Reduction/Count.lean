module

public import LargeIndecomposable.KroneckerBricks.RigidFamily
public import LargeIndecomposable.Modules.IsoClassCount

/-!
# `2^κ` modules in every infinite dimension (Corollary 5.6)

Applying the representation embedding of Theorem 5.2 to the Göbel–Simson family
`T_β`, `β ⊆ κ` (Theorem 5.5), gives `2^κ` pairwise non-isomorphic indecomposable
modules of dimension `κ` with local endomorphism rings whose radicals satisfy
the nilpotence bound of the retractions (`EmbeddingData.exists_noniso_family`).
For `β ≠ γ` one of `Hom(T_β, T_γ)`, `Hom(T_γ, T_β)` vanishes, so `T_β ≇ T_γ`,
and the embedding reflects isomorphism classes.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair
open _root_.Cardinal

universe u

variable {k : Type u} [Field k] [Infinite k] {A : Type u} [Ring A] [Algebra k A]
  [FiniteDimensional k A]

namespace EmbeddingData

variable (E : EmbeddingData k A)

/-- `2^κ` Kronecker bricks of dimension `κ` whose images under `F` are pairwise
non-isomorphic. -/
theorem exists_noniso_family (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) :
    ∃ (ι : Type u) (T : ι → Kron k) (hT : ∀ i, IsBrickKron (T i))
      (hinf : ∀ i, ℵ₀ ≤ (T i).dim), #ι = 2 ^ κ ∧ (∀ i, (T i).dim = κ) ∧
      ∀ i j, Nonempty (FT E (hT i) (hinf i) ≃ₗ[A] FT E (hT j) (hinf j)) → i = j := by
  classical
  let X := κ.ord.ToType
  have hX : #X = κ := mk_ord_toType κ
  haveI : Infinite X := Cardinal.infinite_iff.2 (hX ▸ hκ)
  obtain ⟨T, hdims, -, hzero, -, hbrick⟩ := Bricks.rigidFamily (k := k) X
  have hdim : ∀ b, (T b).dim = κ := fun b ↦ by
    change Module.rank k (T b).V + Module.rank k (T b).W = κ
    rw [(hdims b).1, (hdims b).2.1, hX, add_eq_self hκ]
  have hinf : ∀ b, ℵ₀ ≤ (T b).dim := fun b ↦ (hdim b).symm ▸ hκ
  refine ⟨Set X, T, hbrick, hinf, by rw [mk_set, hX], hdim, fun b c ⟨e⟩ ↦ ?_⟩
  obtain ⟨φ⟩ := E.reflects_iso (brickC (hbrick b) (hinf b)).obj (brickC (hbrick c) (hinf c)).obj
    e.toModuleIso
  have hne : ∀ {b c : Set X} (φ : T b ≅ T c), b ⊆ c := fun {b c} φ ↦ by
    by_contra h
    refine (hbrick b).1 ((IsZero.iff_id_eq_zero _).2 ?_)
    rw [← φ.hom_inv_id, hzero b c h φ.hom, Limits.zero_comp]
  let ψ : T b ≅ T c := (InD (k := k)).ι.mapIso φ
  exact Set.Subset.antisymm (hne ψ) (hne ψ.symm)

end EmbeddingData

end LargeIndecomposable
