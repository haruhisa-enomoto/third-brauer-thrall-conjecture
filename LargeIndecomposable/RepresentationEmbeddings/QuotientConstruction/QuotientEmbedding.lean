module

public import LargeIndecomposable.RepresentationEmbeddings.Control.QuotientRetractions
public import LargeIndecomposable.RepresentationEmbeddings.Control.Consequences
public import LargeIndecomposable.RepresentationEmbeddings.EmbeddingTheorem.EmbeddingData
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# The quotient construction satisfies the hypotheses of Theorem 5.2

For `Q : QuotientData k Λ` with one-dimensional tops at `e_x, e_y` and
`J^n = 0`, the functor `F₁ : D → Mod Λ` of Construction 3.3 is exact and
faithful, has finite-dimensional values on `D_fin` and satisfies the colimit
comparison (3.6) (Lemma 3.4); its retractions on `D` (Proposition 4.1) restrict
to `C`. Restricted to `D_fin`, the retractions show that `F₁(S₋)` is
indecomposable and not isomorphic to `F₁(T)` for `T ∈ C_fin`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair TensorProduct

universe u

variable {k : Type u} [Field k] {Λ : Type u} [Ring Λ] [Algebra k Λ]

namespace QuotientData

variable {Q : QuotientData k Λ} (hx : TopOneDim k Q.ex) (hy : TopOneDim k Q.ey) {n : ℕ}
  (hJ : ∀ l : List Λ, l.length = n → (∀ j ∈ l, j ∈ Ring.jacobson Λ) → l.prod = 0)

instance : (ΦD Q).Additive := by unfold ΦD; infer_instance

instance : (ΦD Q).Linear k := by unfold ΦD; infer_instance

lemma tensorMap_comp {W₁ W₂ W₃ : ModuleCat.{u} k} (f : W₁ ⟶ W₂) (g : W₂ ⟶ W₃)
    (x : Q.P ⊗[k] W₁) : Q.tensorMap g (Q.tensorMap f x) = Q.tensorMap (f ≫ g) x := by
  rw [tensorMap_apply, tensorMap_apply, tensorMap_apply, ← LinearMap.comp_apply,
    ← LinearMap.lTensor_comp]
  rfl

include hx in
/-- Lemma 3.4: `F₁` satisfies the colimit comparison (3.6). An element of
`F₁(T)` is the class of an element of `Λe_y ⊗ W₀` for a finite-dimensional
`W₀ ⊆ W`, and a relation `s ⊗ a(v) + t ⊗ b(v)` holds in `F₁(U + ⟨v⟩)`. -/
theorem comparison : Comparison.IsComparison (ΦD Q) := by
  refine Comparison.isComparison_of_elements _ (fun X x ↦ ?_) (fun X U y hy ↦ ?_)
  · obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨N', hN', ht⟩ :=
      TensorProduct.exists_finite_submodule_right_of_setFinite {t} (Set.finite_singleton t)
    obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.1 (Module.Finite.iff_fg.1 hN')
    obtain ⟨U, -, hU⟩ := Kron.FinSub.exists_of_finite (X := X.obj) ∅ s Set.finite_empty hs
    have hle : N' ≤ U.1.W := hspan ▸ Submodule.span_le.2 hU
    obtain ⟨t', ht'⟩ := ht (Set.mem_singleton t)
    refine ⟨U, Q.π U.1.toKron (LinearMap.lTensor Q.P (Submodule.inclusion hle) t'), ?_⟩
    change Q.π X.obj (Q.tensorMap ((Kron.Sub.ι U.1).app one) _) = _
    rw [tensorMap_apply, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    exact congrArg (Q.π X.obj) ht'
  · obtain ⟨t, rfl⟩ : ∃ t : Q.P ⊗[k] U.1.toKron.W, Q.π U.1.toKron t = y :=
      Submodule.Quotient.mk_surjective _ y
    have h0 : Q.π X.obj (Q.tensorMap ((Kron.Sub.ι U.1).app one) t) = 0 := hy
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Q.mem_relSub_iff hx] at h0
    obtain ⟨v, hv⟩ := h0
    let U' : Kron.FinSub X.obj := ⟨max U.1 (Kron.Sub.span {v} ∅),
      U.2.max (Kron.Sub.isFin_span _ _ (Set.finite_singleton v) Set.finite_empty)⟩
    have hUU' : U ≤ U' := Kron.Sub.le_max_left' _ _
    have hv' : v ∈ U'.1.V :=
      (Kron.Sub.le_max_right' _ _).1 (Kron.Sub.subset_span_V _ _ (Set.mem_singleton v))
    refine ⟨U', hUU', ?_⟩
    change Q.π U'.1.toKron (Q.tensorMap ((Kron.Sub.homOfLE hUU').app one) t) = 0
    have key : Q.tensorMap ((Kron.Sub.homOfLE hUU').app one) t =
        Q.relMap U'.1.toKron ⟨v, hv'⟩ := by
      have hinj : Function.Injective (Q.tensorMap ((Kron.Sub.ι U'.1).app one)) := by
        intro a b h
        rw [tensorMap_apply, tensorMap_apply] at h
        exact Module.Flat.lTensor_preserves_injective_linearMap (M := Q.P)
          ((Kron.Sub.ι U'.1).app one).hom Subtype.val_injective h
      apply hinj
      rw [tensorMap_comp, Q.tensorMap_relMap (Kron.Sub.ι U'.1), ← NatTrans.comp_app,
        Kron.Sub.homOfLE_ι]
      exact hv.symm
    rw [key, π_relMap]

/-- The retractions of Proposition 4.1 restricted to `D_fin`. -/
def retractionsFin : Retractions k (DfinToD k ⋙ ΦD Q) :=
  (retractions hx hy).precomp (G := DfinToD k) (ObjectProperty.fullyFaithfulιOfLE _)

include hJ in
lemma nilpotentBound_fin : (retractionsFin hx hy).NilpotentBound n :=
  Retractions.NilpotentBound.precomp _ _ (nilpotentBound hx hy hJ)

include hx hy hJ in
/-- `F₁(S₋)` is indecomposable. -/
lemma isIndecomposable_Sminus : IsIndecomposable Λ ((ΦD Q).obj Extension.Sminus) :=
  Retractions.isIndecomposable (retractionsFin hx hy) (nilpotentBound_fin hx hy hJ)
    (X := Extension.SminusFin)
    (fun h ↦ isIndecDfin_SminusFin.1
      ((IsZero.iff_id_eq_zero _).2 (congrArg (fun φ : Extension.SminusFin ⟶ Extension.SminusFin ↦
        φ.hom) h)))
    isIndecDfin_SminusFin.2

include hx hy in
/-- `F₁(S₋)` is not isomorphic to `F₁(T)` for `T ∈ C_fin`. -/
lemma not_iso_Sminus (X : Dfin k) (hX : InC X.obj) :
    IsEmpty ((ΦD Q).obj Extension.Sminus ≅ (ΦD Q).obj ((DfinToD k).obj X)) :=
  ⟨fun e ↦ by
    obtain ⟨e'⟩ := Retractions.reflects_iso (retractionsFin hx hy) (X := Extension.SminusFin) e
    exact not_inC_Sminus (inC_of_iso ((ObjectProperty.ι _).mapIso e'.symm) hX)⟩

/-- Part (1) of Theorem 3.14 in data form: the quotient construction gives the
data of Theorem 5.2. -/
def embeddingData [FiniteDimensional k Λ] : EmbeddingData k Λ where
  F := ΦD Q
  faithful := ⟨fun h ↦ (retractions hx hy).map_injective h⟩
  exact X Y Z f g h :=
    ⟨Q.map_injective_of_shortExact hx h Z.2, Q.map_surjective_of_shortExact h,
      Q.range_eq_ker_of_shortExact hx h⟩
  fin X := by
    have := X.2.2.2
    exact Q.finite_restrictScalars X.obj
  comparison := comparison hx
  R := (retractions hx hy).precomp (G := (InCD (k := k)).ι) (ObjectProperty.fullyFaithfulι _)
  n := n
  bound := Retractions.NilpotentBound.precomp _ _ (nilpotentBound hx hy hJ)
  indecS := isIndecomposable_Sminus hx hy hJ
  notIsoS := not_iso_Sminus hx hy

end QuotientData

end LargeIndecomposable
