module

public import LargeIndecomposable.Quivers.PushDown.PushDown

/-!
# The push-down as a module over the path algebra

For a quiver morphism `p : D → Q` and a representation `X` of `D`, the
push-down `p_*X` (Construction 3.9) is the total space `⊕_i X(i)` with `e_q`
acting as the projection onto `⊕_{p(i)=q} X(i)` and an arrow `c` acting by the
sum of the arrow operators of the arrows labelled `c`. This file builds the
algebra homomorphism `kQ → End_k(⊕_i X(i))`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory

universe u

variable {k : Type u} [Field k] {D Q : FinQuiver} (p : FinQuiver.Hom D Q)

namespace Rep

variable (X : Rep k D)

/-- The action of the vertex idempotent `e_q`: the projection onto
`⊕_{p(i)=q} X(i)`. -/
def pdVert (q : Q.V) : Module.End k X.Tot :=
  LinearMap.pi fun i ↦ if p.vert i = q then LinearMap.proj i else 0

lemma pdVert_apply (q : Q.V) (x : X.Tot) (i : D.V) :
    X.pdVert p q x i = if p.vert i = q then x i else 0 := by
  simp only [pdVert, LinearMap.pi_apply]; split_ifs <;> rfl

/-- The action of an arrow `c`: the sum of the blocks `X(e)` over the arrows
`e` labelled `c`. -/
def pdArr (c : Q.A) : Module.End k X.Tot :=
  ∑ e ∈ Finset.univ.filter (p.arr · = c), X.arrOp e

lemma pdArr_apply (c : Q.A) (x : X.Tot) (j : D.V) :
    X.pdArr p c x j = ∑ e ∈ Finset.univ.filter (p.arr · = c),
      (Pi.single (D.tgt e) ((X.map e).hom (x (D.src e))) : X.Tot) j := by
  simp [pdArr, arrOp_apply, Finset.sum_apply]

lemma pdVert_mul_pdVert (q q' : Q.V) :
    X.pdVert p q * X.pdVert p q' = if q = q' then X.pdVert p q else 0 := by
  refine LinearMap.ext fun x ↦ funext fun i ↦ ?_
  simp only [Module.End.mul_apply, pdVert_apply]
  split_ifs with h1 h2 h3 h3 <;> simp_all [pdVert_apply]

lemma sum_pdVert : ∑ q, X.pdVert p q = 1 := by
  refine LinearMap.ext fun x ↦ funext fun i ↦ ?_
  simp [LinearMap.sum_apply, Finset.sum_apply, pdVert_apply]

lemma pdArr_mul_pdVert_src (c : Q.A) : X.pdArr p c * X.pdVert p (Q.src c) = X.pdArr p c := by
  refine LinearMap.ext fun x ↦ funext fun j ↦ ?_
  simp only [Module.End.mul_apply, pdArr_apply, pdVert_apply]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
  rw [ite_eq_left_iff.2 fun h ↦ absurd (by rw [← p.map_src, he]) h]

lemma pdVert_tgt_mul_pdArr (c : Q.A) : X.pdVert p (Q.tgt c) * X.pdArr p c = X.pdArr p c := by
  refine LinearMap.ext fun x ↦ funext fun j ↦ ?_
  simp only [Module.End.mul_apply, pdVert_apply, pdArr_apply]
  split_ifs with h
  · rfl
  · symm
    refine Finset.sum_eq_zero fun e he ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    rw [Pi.single_eq_of_ne]
    rintro rfl
    exact h (by rw [← p.map_tgt, he])

/-- The push-down action `kQ → End_k(⊕_i X(i))`. -/
def pdAct : Q.PathAlgebra k →ₐ[k] Module.End k X.Tot :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k (Sum.elim (X.pdVert p) (X.pdArr p)), by
    intro x y h
    induction h with
    | idem v w =>
      simp only [map_mul, FreeAlgebra.lift_ι_apply, Sum.elim_inl, pdVert_mul_pdVert]
      split_ifs <;> simp
    | one =>
      simp only [map_sum, FreeAlgebra.lift_ι_apply, Sum.elim_inl, sum_pdVert, map_one]
    | src a =>
      simp only [map_mul, FreeAlgebra.lift_ι_apply, Sum.elim_inl, Sum.elim_inr,
        pdArr_mul_pdVert_src]
    | tgt a =>
      simp only [map_mul, FreeAlgebra.lift_ι_apply, Sum.elim_inl, Sum.elim_inr,
        pdVert_tgt_mul_pdArr]⟩

@[simp]
lemma pdAct_vertex (q : Q.V) : X.pdAct p (FinQuiver.vertex k Q q) = X.pdVert p q := by
  simp [pdAct, FinQuiver.vertex]

@[simp]
lemma pdAct_arrow (c : Q.A) : X.pdAct p (FinQuiver.arrow k Q c) = X.pdArr p c := by
  simp [pdAct, FinQuiver.arrow]

/-- A linear map of total spaces commutes with the push-down action if it
commutes with the vertex and arrow actions. -/
lemma commute_pdAct {Y : Rep k D} (f : X.Tot →ₗ[k] Y.Tot)
    (hv : ∀ q, f ∘ₗ X.pdVert p q = Y.pdVert p q ∘ₗ f)
    (ha : ∀ c, f ∘ₗ X.pdArr p c = Y.pdArr p c ∘ₗ f) (z : Q.PathAlgebra k) :
    f ∘ₗ X.pdAct p z = Y.pdAct p z ∘ₗ f := by
  obtain ⟨x, rfl⟩ := RingQuot.mkAlgHom_surjective k (FinQuiver.PathRel k Q) z
  induction x using FreeAlgebra.induction with
  | grade0 r =>
    simp only [AlgHom.commutes, Module.algebraMap_end_eq_smul_id,
      Module.algebraMap_end_eq_smul_id, LinearMap.comp_smul, LinearMap.smul_comp]
    rfl
  | grade1 g =>
    rcases g with q | c
    · exact (pdAct_vertex p X q) ▸ (pdAct_vertex p Y q) ▸ hv q
    · exact (pdAct_arrow p X c) ▸ (pdAct_arrow p Y c) ▸ ha c
  | mul a b ha' hb' =>
    rw [map_mul, map_mul, map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      ← LinearMap.comp_assoc, ha', LinearMap.comp_assoc, hb', LinearMap.comp_assoc]
  | add a b ha' hb' =>
    rw [map_add, map_add, map_add, LinearMap.comp_add, LinearMap.add_comp, ha', hb']

end Rep

end LargeIndecomposable
