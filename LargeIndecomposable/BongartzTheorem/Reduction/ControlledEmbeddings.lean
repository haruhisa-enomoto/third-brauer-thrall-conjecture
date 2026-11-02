module

public import LargeIndecomposable.RepresentationType.MinimalInfinite.Minimal
public import LargeIndecomposable.Modules.Morita.CoindDim
public import LargeIndecomposable.RepresentationType.DistributiveIdeals.NonDistributiveEmbedding

/-!
# Theorem A from controlled embeddings of minimal algebras

The assembly of Section 5. Lemma 3.1 reduces `A` to a split basic minimal
representation-infinite algebra `B` (full corner, then a minimal quotient);
Theorem 3.10 provides a controlled embedding for `B` (proved here in the
nondistributive case; the distributive case enters as the hypothesis
`DistributiveControlled`); it transports to `A` and Theorem 5.1 applies.

`DistributiveControlled` is an intermediate hypothesis of the formalization.
It follows from the data form of Bongartz's Theorem 6 together with
Sections 3.3–3.4 and 4.2–4.5 of the manuscript (`BongartzTheorem/Reduction/DataForm.lean`), and the
final proof in `MainTheorems.lean` removes it.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Statement

universe u

/-- Hypothesis: every distributive split basic minimal
representation-infinite algebra over an algebraically closed field has a
controlled embedding. -/
def DistributiveControlled : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B] [Algebra k B]
    [FiniteDimensional k B] (ι : Type) [Fintype ι], SplitBasicData k B ι →
      IsMinimalRepInfinite B → IsDistribIdeals B → Nonempty (ControlledEmbedding k B)

/-- The Morita functor of a full idempotent preserves short exact sequences. -/
lemma Morita.preservesSES {A : Type u} [Ring A] {e : A} (he : IsIdempotentElem e)
    (hfull : Morita.IsFull e) : ControlledEmbedding.PreservesSES (Morita.functor he) :=
  fun _ _ _ f g h₁ h₂ h₃ ↦ Morita.preservesShortExact (he := he) hfull f g h₁ h₂ h₃

variable (H : DistributiveControlled.{u})

include H in
/-- Theorem 3.10 (in controlled form) for split basic minimal
representation-infinite algebras. -/
theorem nonempty_controlledEmbedding_of_minimal {k : Type u} [Field k] [IsAlgClosed k]
    (B : Type u) [Ring B] [Algebra k B] [FiniteDimensional k B] {ι : Type} [Fintype ι]
    (S : SplitBasicData k B ι) (hB : IsMinimalRepInfinite B) :
    Nonempty (ControlledEmbedding k B) := by
  classical
  by_cases hd : IsDistribIdeals B
  · exact H k B ι S hB hd
  · exact S.nonempty_controlledEmbedding hd

include H in
/-- Lemma 3.1 with Theorem 3.10: a representation-infinite finite-dimensional
algebra over an algebraically closed field has a controlled embedding. -/
theorem nonempty_controlledEmbedding_of_not_isRepresentationFinite {k : Type u} [Field k]
    [IsAlgClosed k] (A : Type u) [Ring A] [Algebra k A] [FiniteDimensional k A]
    (hA : ¬ IsRepresentationFinite A) : Nonempty (ControlledEmbedding k A) := by
  classical
  obtain ⟨e, he, m, hfull, ⟨S⟩⟩ := exists_full_splitBasic k A
  have : FiniteDimensional k he.Corner := Corner.finiteDimensional he (k := k)
  have hA₀ : ¬ IsRepresentationFinite he.Corner := fun h ↦
    hA (Morita.isRepresentationFinite_of_corner (k := k) he hfull h)
  obtain ⟨K, hK⟩ := exists_minimalRepInfinite_quotient k hA₀
  have : FiniteDimensional k (he.Corner ⧸ K.asIdeal) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k K.asIdeal).toLinearMap
      Ideal.Quotient.mk_surjective
  obtain ⟨E⟩ := nonempty_controlledEmbedding_of_minimal H (he.Corner ⧸ K.asIdeal)
    (S.quotientNZ K) hK
  let E₀ := E.transport (Inflation.functor K) (Inflation.fullyFaithful K)
    (Inflation.preservesSES K) (Inflation.finite K)
  exact ⟨E₀.transport (Morita.functor he) (Functor.FullyFaithful.ofFullyFaithful _)
    (Morita.preservesSES he hfull) (fun M _ ↦ Morita.finite_obj (k := k) he hfull M)⟩

include H in
/-- Theorem A, conditional on the distributive case of Theorem 3.10. -/
theorem theoremA_of_distributiveControlled : TheoremA.{u} := by
  intro k _ _ A _ _ _ hA
  obtain ⟨E⟩ := nonempty_controlledEmbedding_of_not_isRepresentationFinite (k := k) H A hA
  exact E.theoremA_conclusion

end LargeIndecomposable
