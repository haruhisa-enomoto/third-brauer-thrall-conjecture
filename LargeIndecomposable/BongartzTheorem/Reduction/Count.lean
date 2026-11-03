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

section Main

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

omit [Infinite k] in
/-- The endomorphism algebra of `F(T)` for a brick `T ∈ C` is local with residue
field `k`, and its radical satisfies the nilpotence bound of the retractions. -/
lemma endLocalBounded_FT (E : EmbeddingData k A) {T : Kron k} (hT : IsBrickKron T)
    (hinf : ℵ₀ ≤ T.dim) : EndLocalBounded k A (E.n + 1) (FT E hT hinf) := by
  refine ⟨fun x ↦ ?_, one_not_mem_jacobson E hT hinf, prod_eq_zero E hT hinf⟩
  obtain ⟨c, hc⟩ := brickC_scalar hT hinf (ρE E hT hinf x)
  exact ⟨c, ker_mem_jacobson E hT hinf _ (by rw [ρE_sub, ρE_algebraMap, hc, sub_self])⟩

end Main

variable (H : DistributiveEmbeddingData.{u})

include H in
/-- Corollary 5.6 without the explicit bound on `n`, conditional on the
distributive case of Theorem 3.14. -/
theorem corollaryCount_of : CorollaryCount.{u} := by
  intro k _ _ A _ _ _ hA
  obtain ⟨E⟩ := nonempty_embeddingData_of_not_isRepresentationFinite (k := k) H A hA
  refine ⟨E.n + 1, Nat.succ_le_succ (Nat.zero_le _), fun κ hκ ↦ ⟨?_, fun hk ι M _ _ _ _ hni hdim ↦
    card_le_two_pow_of_pairwise_not_iso κ hκ hk M hni hdim⟩⟩
  obtain ⟨ι, T, hT, hinf, hι, hdim, hni⟩ := E.exists_noniso_family κ hκ
  exact ⟨ι, fun i ↦ FT E (hT i) (hinf i), fun _ ↦ inferInstance, fun _ ↦ inferInstance,
    fun _ ↦ ModuleCat.moduleOfAlgebraModule _, fun _ ↦ ModuleCat.isScalarTower_of_algebra_moduleCat _,
    hι, hni, fun i ↦ ⟨(rank_FT E (hT i) (hinf i)).trans (hdim i),
      isIndecomposable_brick E (hT i) (hinf i), endLocalBounded_FT E (hT i) (hinf i)⟩⟩

end LargeIndecomposable
