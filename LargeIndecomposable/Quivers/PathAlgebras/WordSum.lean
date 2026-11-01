module

public import LargeIndecomposable.RepresentationEmbeddings.WalkConstruction.Monomial

/-!
# The push-down action of a path as a sum over its lifts

For a quiver morphism `p : D → Q` and a representation `X` of `D`, a word `l`
of `Q` acts on the push-down `p_*X` as the sum of the operators of all lists of
arrows of `D` labelled by `l` (`Rep.pdAct_word_eq_sum`); lists that are not
paths act by zero (`Rep.pathTot_eq_zero`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory

universe u

namespace Rep

variable {k : Type u} [Field k] {D Q : FinQuiver} (p : FinQuiver.Hom D Q) (X : Rep k D)

/-- The operator of a list of arrows on the total space (first arrow first). -/
def pathTot : List D.A → (X.Tot →ₗ[k] X.Tot)
  | [] => LinearMap.id
  | e :: le => pathTot le ∘ₗ X.arrOp e

/-- The lists of arrows of `D` labelled by a word of `Q`. -/
def lab : List Q.A → Finset (List D.A)
  | [] => {[]}
  | c :: l => ((Finset.univ.filter (p.arr · = c)) ×ˢ lab l).image fun x ↦ x.1 :: x.2

lemma mem_lab : ∀ (l : List Q.A) (le : List D.A), le ∈ lab p l ↔ le.map p.arr = l
  | [], le => by cases le <;> simp [lab]
  | c :: l, [] => by simp [lab]
  | c :: l, e :: le => by
    simp only [lab, Finset.mem_image, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
      true_and, Prod.exists, List.cons.injEq, List.map_cons, mem_lab l]
    constructor
    · rintro ⟨e', le', ⟨h1, h2⟩, rfl, rfl⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨e, le, ⟨h1, h2⟩, rfl, rfl⟩

/-- A word acts on push-downs as the sum over its lifts. -/
theorem pdAct_word_eq_sum : ∀ l : List Q.A,
    X.pdAct p (FinQuiver.word k Q l) = ∑ le ∈ lab p l, X.pathTot le
  | [] => by
    simp only [FinQuiver.word, map_one, lab, Finset.sum_singleton, pathTot]
    rfl
  | c :: l => by
    rw [word_cons, map_mul, pdAct_word_eq_sum l, pdAct_arrow, lab,
      Finset.sum_image (fun x _ y _ h ↦ by
        obtain ⟨h1, h2⟩ := List.cons.inj h
        exact Prod.ext h1 h2),
      Finset.sum_product, Module.End.mul_eq_comp, finsetSum_comp]
    simp only [pdArr, comp_finsetSum, pathTot]
    rw [Finset.sum_comm]

lemma pathTot_cons_cons (e e' : D.A) (le : List D.A) (h : D.tgt e ≠ D.src e') :
    X.pathTot (e :: e' :: le) = 0 := by
  have : X.arrOp e' ∘ₗ X.arrOp e = 0 := by
    rw [X.arrOp_eq_idm_comp e, ← LinearMap.comp_assoc]
    have h2 : X.arrOp e' ∘ₗ X.idm (D.tgt e) = 0 := by
      rw [arrOp_comp_idm, if_neg (Ne.symm h)]
    rw [h2, LinearMap.zero_comp]
  simp only [pathTot, LinearMap.comp_assoc, this, LinearMap.comp_zero]

/-- Lists of arrows that are not paths act by zero. -/
theorem pathTot_eq_zero : ∀ (le : List D.A), (∀ i j, ¬FinQuiver.PathFrom i le j) → le ≠ [] →
    X.pathTot le = 0
  | [], _, h => absurd rfl h
  | [e], hn, _ => absurd ⟨rfl, rfl⟩ (hn (D.src e) (D.tgt e))
  | e :: e' :: le, hn, _ => by
    by_cases h : D.tgt e = D.src e'
    · have hn' : ∀ i j, ¬FinQuiver.PathFrom i (e' :: le) j := fun i j hp ↦
        hn (D.src e) j ⟨rfl, h ▸ hp.1 ▸ hp⟩
      have := pathTot_eq_zero (e' :: le) hn' (List.cons_ne_nil _ _)
      simp only [pathTot] at this ⊢
      rw [this, LinearMap.zero_comp]
    · exact X.pathTot_cons_cons e e' le h

end Rep

end LargeIndecomposable
