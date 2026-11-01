module

public import LargeIndecomposable.RepresentationEmbeddings.Control.QuotientRetractions
public import LargeIndecomposable.RepresentationEmbeddings.Control.Consequences
public import LargeIndecomposable.RepresentationEmbeddings.ColimitExtension.Criterion

/-!
# The quotient construction satisfies the hypotheses of Theorem 2.7

For `Q : QuotientData k Λ` with one-dimensional tops at `e_x, e_y` and
`J^n = 0`, the functor `F₁` restricted to `D_fin` is a representation embedding
with finite-dimensional values (part (1) of Theorem 3.10 in data form); its
retractions (Proposition 4.1) restrict
to `C_fin`. Preservation of indecomposability and reflection of isomorphism
classes follow from the retractions on all of `D_fin`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair

universe u

variable {k : Type u} [Field k] {Λ : Type u} [Ring Λ] [Algebra k Λ]

namespace QuotientData

variable {Q : QuotientData k Λ} (hx : TopOneDim k Q.ex) (hy : TopOneDim k Q.ey) {n : ℕ}
  (hJ : ∀ l : List Λ, l.length = n → (∀ j ∈ l, j ∈ Ring.jacobson Λ) → l.prod = 0)

instance : (Φfin Q).Additive := by unfold Φfin; infer_instance

instance : (Φfin Q).Linear k := by unfold Φfin; infer_instance

include hx hy hJ in
/-- `F₁` on `D_fin` satisfies the hypotheses of Theorem 2.7. -/
theorem isRepEmbeddingFin [FiniteDimensional k Λ] : IsRepEmbeddingFin (Φfin Q) where
  fin X := by
    have := X.2.2.2
    exact Q.finite_restrictScalars X.obj
  exact X Y Z f g h :=
    ⟨Q.map_injective_of_shortExact hx h Z.2.1, Q.map_surjective_of_shortExact h,
      Q.range_eq_ker_of_shortExact hx h⟩
  indecS := Retractions.isIndecomposable (retractions hx hy) (nilpotentBound hx hy hJ)
    (fun h ↦ isIndecDfin_SminusFin.1
      ((IsZero.iff_id_eq_zero _).2 (congrArg (fun φ : Extension.SminusFin ⟶ Extension.SminusFin ↦
        φ.hom) h)))
    isIndecDfin_SminusFin.2
  notIsoS X hX := ⟨fun e ↦ by
    obtain ⟨e'⟩ := Retractions.reflects_iso (retractions hx hy) e
    exact not_inC_Sminus (inC_of_iso ((ObjectProperty.ι _).mapIso e'.symm) hX)⟩

/-- The retractions of Proposition 4.1 restricted to `C_fin`. -/
def retractionsCfin : Retractions k (Extension.Ψfin (Φfin Q)) :=
  (retractions hx hy).precomp (G := (InCfin (k := k)).ι) (ObjectProperty.fullyFaithfulι _)

include hJ in
lemma nilpotentBound_Cfin : (retractionsCfin hx hy).NilpotentBound n :=
  Retractions.NilpotentBound.precomp _ _ (nilpotentBound hx hy hJ)

end QuotientData

end LargeIndecomposable
