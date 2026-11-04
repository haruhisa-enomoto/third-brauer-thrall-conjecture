module

public import LargeIndecomposable.BongartzTheorem.Reduction.MinimalReduction

/-!
# The reduction of Lemma 3.1 with the nilpotence bound

The nilpotence bound `n` of the data of Theorem 5.2 is unchanged by transport along inflation
and the Morita functor, and the minimal quotient `B` of the basic corner has `dim B ≤ dim A`.
So a bound `n + 1 ≤ max(30, 4 dim B)` for the split basic minimal distributive algebras
(`DistributiveEmbeddingDataBounded`) gives the same bound for every representation-infinite `A`
(`exists_embeddingData_bounded_of`); the nondistributive case has `n ≤ dim B`
(`SplitBasicData.exists_embeddingData_le`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement

universe u

/-- The distributive case of Theorem 3.14 with the explicit bound. -/
def DistributiveEmbeddingDataBounded : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B] [Algebra k B]
    [FiniteDimensional k B] (ι : Type) [Fintype ι], SplitBasicData k B ι →
      IsMinimalRepInfinite B → IsDistribIdeals B →
        ∃ E : EmbeddingData k B, E.n + 1 ≤ max 30 (4 * Module.finrank k B)

/-- **Theorem 3.14 with the explicit bound**, from the bounded distributive case: a
representation-infinite algebra over an algebraically closed field has the data of Theorem 5.2
with `n + 1 ≤ max(30, 4 dim A)`. -/
theorem exists_embeddingData_bounded_of (H : DistributiveEmbeddingDataBounded.{u}) {k : Type u} [Field k]
    [IsAlgClosed k] (A : Type u) [Ring A] [Algebra k A] [FiniteDimensional k A]
    (hA : ¬ Statement.IsRepresentationFinite A) :
    ∃ E : EmbeddingData k A, E.n + 1 ≤ max 30 (4 * Module.finrank k A) := by
  classical
  obtain ⟨e, he, m, hfull, ⟨S⟩⟩ := exists_full_splitBasic k A
  haveI hCfd : FiniteDimensional k he.Corner := Corner.finiteDimensional he (k := k)
  have hA₀ : ¬ Statement.IsRepresentationFinite he.Corner := fun h ↦
    hA (Morita.isRepresentationFinite_of_corner (k := k) he hfull h)
  obtain ⟨K, hK'⟩ := exists_minimalRepInfinite_quotient k hA₀
  haveI hQfd : FiniteDimensional k (he.Corner ⧸ K.asIdeal) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k K.asIdeal).toLinearMap
      Ideal.Quotient.mk_surjective
  have hdim : Module.finrank k (he.Corner ⧸ K.asIdeal) ≤ Module.finrank k A :=
    (LinearMap.finrank_le_finrank_of_surjective
      (f := (Ideal.Quotient.mkₐ k K.asIdeal).toLinearMap) Ideal.Quotient.mk_surjective).trans
      (LinearMap.finrank_le_finrank_of_injective (Corner.valL_injective he (k := k)))
  obtain ⟨E, hE⟩ : ∃ E : EmbeddingData k (he.Corner ⧸ K.asIdeal),
      E.n + 1 ≤ max 30 (4 * Module.finrank k (he.Corner ⧸ K.asIdeal)) := by
    by_cases hd : IsDistribIdeals (he.Corner ⧸ K.asIdeal)
    · exact H k _ _ (S.quotientNZ K) hK' hd
    · obtain ⟨E, hE⟩ := (S.quotientNZ K).exists_embeddingData_le hd
      exact ⟨E, by omega⟩
  let E₀ := E.transport (Inflation.functor K) (Inflation.fullyFaithful K)
    (Inflation.preservesSES K) (Inflation.finite K)
  haveI := Morita.preservesFilteredColimits he hfull
  refine ⟨E₀.transport (Morita.functor he) (Functor.FullyFaithful.ofFullyFaithful _)
    (Morita.preservesSES he hfull) (fun M _ ↦ Morita.finite_obj (k := k) he hfull M), ?_⟩
  change E.n + 1 ≤ _
  omega

end LargeIndecomposable
