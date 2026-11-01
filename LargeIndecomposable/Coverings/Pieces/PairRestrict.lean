module

public import LargeIndecomposable.RepresentationEmbeddings.CoveringConstruction.KroneckerPair
public import LargeIndecomposable.Quivers.PushDown.FullSub

/-!
# Restricting a Kronecker pair to its support

A Kronecker pair on a quiver `D` need not have every vertex in its support. Restricting it to the
full subquiver on the support `T` gives a Kronecker pair (`KroneckerPair.restrict`) whose
representations `L(T)` are the restrictions of the old ones; since these vanish off `T`, relations
killing the old push-downs kill the new ones (`Rep.pdAct_res_eq_zero`). So covering data with a
pair need no support condition (`PairCoveringData.ofPair`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair TensorProduct FinQuiver

universe u

namespace Covering

variable {k : Type u} [Field k] {D : FinQuiver}

namespace KroneckerPair

variable (K : KroneckerPair k D)

open Classical in
/-- The support of a Kronecker pair. -/
def supp : Finset D.V :=
  Finset.univ.filter fun i ↦ Nontrivial (K.P.obj i) ∨ Nontrivial (K.Q₀.obj i)

lemma mem_supp {i : D.V} : i ∈ K.supp ↔ Nontrivial (K.P.obj i) ∨ Nontrivial (K.Q₀.obj i) := by
  classical
  simp [supp]

lemma subsingleton_P {i : D.V} (h : i ∉ K.supp) : Subsingleton (K.P.obj i) := by
  rw [mem_supp] at h
  exact not_nontrivial_iff_subsingleton.1 fun h' ↦ h (Or.inl h')

lemma subsingleton_Q {i : D.V} (h : i ∉ K.supp) : Subsingleton (K.Q₀.obj i) := by
  rw [mem_supp] at h
  exact not_nontrivial_iff_subsingleton.1 fun h' ↦ h (Or.inr h')

/-- A linear map out of or into a zero space vanishes. -/
lemma linearMap_eq_zero {M N : Type u} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (f : M →ₗ[k] N) (h : Subsingleton M ∨ Subsingleton N) : f = 0 := by
  rcases h with h | h
  · ext x
    rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
  · ext x
    exact Subsingleton.elim _ _

/-- The components of the extension by zero. -/
def extLin (X : Rep k D) (T : Finset D.V) (f : X.res T ⟶ X.res T) (i : D.V) :
    X.obj i →ₗ[k] X.obj i :=
  if h : i ∈ T then (show X.obj i →ₗ[k] X.obj i from (f.app ⟨i, h⟩).hom) else 0

/-- Extension by zero of an endomorphism of the restriction. -/
def extEnd (X : Rep k D) (T : Finset D.V) (hX : ∀ i, i ∉ T → Subsingleton (X.obj i))
    (f : X.res T ⟶ X.res T) : X ⟶ X where
  app i := ModuleCat.ofHom (extLin X T f i)
  comm α := by
    ext v
    change extLin X T f (D.tgt α) ((X.map α).hom v) = (X.map α).hom (extLin X T f (D.src α) v)
    unfold extLin
    by_cases hs : D.src α ∈ T
    · by_cases ht : D.tgt α ∈ T
      · rw [dif_pos hs, dif_pos ht]
        have := congrArg (fun g ↦ (ModuleCat.Hom.hom g) v) (f.comm ⟨α, hs, ht⟩)
        exact this
      · haveI := hX _ ht
        exact Subsingleton.elim _ _
    · haveI := hX _ hs
      rw [Subsingleton.elim v 0, map_zero, map_zero, map_zero, map_zero]

lemma extEnd_app (X : Rep k D) (T : Finset D.V) (hX : ∀ i, i ∉ T → Subsingleton (X.obj i))
    (f : X.res T ⟶ X.res T) (i : (fullSub D T).V) :
    ((extEnd X T hX f).app i.1).hom = (f.app i).hom := by
  change extLin X T f i.1 = _
  unfold extLin
  rw [dif_pos i.2]
  rfl

/-- **The restriction of a Kronecker pair to its support.** -/
def restrict : KroneckerPair k (fullSub D K.supp) where
  P := K.P.res K.supp
  Q₀ := K.Q₀.res K.supp
  finP i := K.finP i.1
  finQ i := K.finQ i.1
  disjoint i := K.disjoint i.1
  brickP f := by
    obtain ⟨c, hc⟩ := K.brickP (extEnd K.P K.supp (fun i h ↦ K.subsingleton_P h) f)
    exact ⟨c, fun i ↦ by rw [← extEnd_app K.P K.supp (fun i h ↦ K.subsingleton_P h) f i]; exact hc i.1⟩
  brickQ f := by
    obtain ⟨c, hc⟩ := K.brickQ (extEnd K.Q₀ K.supp (fun i h ↦ K.subsingleton_Q h) f)
    exact ⟨c, fun i ↦ by rw [← extEnd_app K.Q₀ K.supp (fun i h ↦ K.subsingleton_Q h) f i]; exact hc i.1⟩
  z₁ α := K.z₁ α.1
  z₂ α := K.z₂ α.1
  indep c₁ c₂ h := by
    refine K.indep c₁ c₂ fun α ↦ ?_
    by_cases hα : D.src α ∈ K.supp ∧ D.tgt α ∈ K.supp
    · exact h ⟨α, hα⟩
    · apply linearMap_eq_zero
      by_cases hs : D.src α ∈ K.supp
      · exact Or.inr (K.subsingleton_Q fun ht ↦ hα ⟨hs, ht⟩)
      · exact Or.inl (K.subsingleton_P hs)
  nonzeroP := by
    obtain ⟨i, hi⟩ := K.nonzeroP
    exact ⟨⟨i, K.mem_supp.2 (Or.inl hi)⟩, hi⟩
  nonzeroQ := by
    obtain ⟨i, hi⟩ := K.nonzeroQ
    exact ⟨⟨i, K.mem_supp.2 (Or.inr hi)⟩, hi⟩

lemma restrict_supp (i : (fullSub D K.supp).V) :
    Nontrivial (K.restrict.P.obj i) ∨ Nontrivial (K.restrict.Q₀.obj i) :=
  K.mem_supp.1 i.2

lemma restrict_obj (T : Kfin k) : K.restrict.functor.obj T = (K.functor.obj T).res K.supp := rfl

lemma functor_obj_subsingleton (T : Kfin k) {i : D.V} (h : i ∉ K.supp) :
    Subsingleton ((K.functor.obj T).obj i) := by
  haveI := K.subsingleton_P h
  haveI := K.subsingleton_Q h
  change Subsingleton ((K.Q₀.obj i ⊗[k] T.obj.W) × (K.P.obj i ⊗[k] T.obj.V))
  infer_instance

end KroneckerPair

/-- Covering data restrict to a full subquiver. -/
def CoverData.restrict {Q : FinQuiver} {p : FinQuiver.Hom D Q} (C : CoverData p) (T : Finset D.V) :
    CoverData (fullSubHom T p) where
  G := C.G
  torsionFree := C.torsionFree
  R₀ := C.R₀
  free := C.free
  ι i := C.ι i.1
  ι_inj _ _ h := Subtype.ext (C.ι_inj h)
  fibre x y h := C.fibre x.1 y.1 h
  arrows α β h := C.arrows α.1 β.1 h

variable {A : Type u} [Ring A] [Algebra k A]

/-- **Covering data with a Kronecker pair, without a support condition.** -/
def PairCoveringData.ofPair (D Q : FinQuiver) (p : FinQuiver.Hom D Q) (locInj : p.LocallyInjective)
    (C : CoverData p) (K : KroneckerPair k D) (π : Q.PathAlgebra k →ₐ[k] A)
    (surj : Function.Surjective π)
    (kills : ∀ (T : Dfin k) (z : Q.PathAlgebra k), π z = 0 →
      (K.functor.obj ((DfinToKfin k).obj T)).pdAct p z = 0) : PairCoveringData k A where
  D := fullSub D K.supp
  Q := Q
  p := fullSubHom K.supp p
  locInj := fullSubHom_locallyInjective K.supp locInj
  C := C.restrict K.supp
  K := K.restrict
  supp := K.restrict_supp
  π := π
  surj := surj
  kills T z hz := by
    rw [K.restrict_obj]
    exact Rep.pdAct_res_eq_zero K.supp _ (fun i h ↦ K.functor_obj_subsingleton _ h) p z
      (kills T z hz)

end Covering

end LargeIndecomposable
