module

public import LargeIndecomposable.Quivers.PathAlgebras.PathAlgebraLemmas

/-!
# The path algebra is spanned by vertices and paths

Words of non-composable lists vanish (`word_eq_zero_of_not_path`), words multiply by
concatenation (`word_append`), and so the vertex idempotents together with the words of nonempty
paths span the path algebra (`span_vertex_path`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

namespace FinQuiver

universe u

variable (k : Type u) [Field k] {Q : FinQuiver}

lemma word_append : ∀ l l' : List Q.A, word k Q (l ++ l') = word k Q l' * word k Q l
  | [], l' => by simp [word]
  | c :: l, l' => by
    change word k Q (l ++ l') * arrow k Q c = word k Q l' * (word k Q l * arrow k Q c)
    rw [word_append l l', mul_assoc]

lemma word_mul_vertex_src (c : Q.A) (l : List Q.A) :
    word k Q (c :: l) * vertex k Q (Q.src c) = word k Q (c :: l) := by
  change word k Q l * arrow k Q c * vertex k Q (Q.src c) = word k Q l * arrow k Q c
  rw [mul_assoc, arrow_mul_src]

lemma sum_vertex : ∑ v, vertex k Q v = 1 := by
  have := RingQuot.mkAlgHom_rel k (PathRel.one (k := k) (Q := Q))
  rw [map_sum, map_one] at this
  exact this

lemma word_eq_zero_of_not_path : ∀ l : List Q.A, (¬∃ i j, PathFrom i l j) → word k Q l = 0
  | [], h => by
    rcases isEmpty_or_nonempty Q.V with hV | hV
    · rw [word, ← sum_vertex, Finset.univ_eq_empty, Finset.sum_empty]
    · exact absurd ⟨Classical.arbitrary _, _, rfl⟩ h
  | [c], h => absurd ⟨Q.src c, Q.tgt c, rfl, rfl⟩ h
  | c :: d :: l, h => by
    by_cases hp : ∃ i j, PathFrom i (d :: l) j
    · obtain ⟨i, j, hij⟩ := hp
      have hi : Q.src d = i := hij.1
      have hne : Q.src d ≠ Q.tgt c := fun he ↦ h ⟨Q.src c, j, rfl, by rw [← he, hi]; exact hij⟩
      change word k Q (d :: l) * arrow k Q c = 0
      rw [← word_mul_vertex_src, mul_assoc, vertex_mul_arrow, if_neg hne, mul_zero]
    · change word k Q (d :: l) * arrow k Q c = 0
      rw [word_eq_zero_of_not_path (d :: l) hp, zero_mul]
  termination_by l => l.length

/-- The span of the vertex idempotents and all words. -/
def vwSpan : Submodule k (PathAlgebra k Q) :=
  Submodule.span k (Set.range (vertex k Q) ∪ Set.range (word k Q))

lemma word_mem (l : List Q.A) : word k Q l ∈ vwSpan k (Q := Q) :=
  Submodule.subset_span (Or.inr ⟨l, rfl⟩)

lemma vertex_mem (v : Q.V) : vertex k Q v ∈ vwSpan k (Q := Q) :=
  Submodule.subset_span (Or.inl ⟨v, rfl⟩)

lemma vertex_mul_word_mem (v : Q.V) (l : List Q.A) :
    vertex k Q v * word k Q l ∈ vwSpan k (Q := Q) := by
  rcases l with _ | ⟨c, l⟩
  · rw [word, mul_one]; exact vertex_mem k v
  · by_cases hp : ∃ i j, PathFrom i (c :: l) j
    · obtain ⟨i, j, hij⟩ := hp
      by_cases hv : v = j
      · subst hv; rw [vertex_mul_word k c l i v hij]; exact word_mem k _
      · rw [← vertex_mul_word k c l i j hij, ← mul_assoc, vertex_mul_vertex, if_neg hv,
          zero_mul]
        exact Submodule.zero_mem _
    · rw [word_eq_zero_of_not_path k _ hp, mul_zero]; exact Submodule.zero_mem _

lemma word_mul_vertex_mem (l : List Q.A) (v : Q.V) :
    word k Q l * vertex k Q v ∈ vwSpan k (Q := Q) := by
  rcases l with _ | ⟨c, l⟩
  · rw [word, one_mul]; exact vertex_mem k v
  · by_cases hv : v = Q.src c
    · subst hv; rw [word_mul_vertex_src]; exact word_mem k _
    · rw [← word_mul_vertex_src, mul_assoc, vertex_mul_vertex, if_neg (Ne.symm hv), mul_zero]
      exact Submodule.zero_mem _

lemma mul_mem_vwSpan {x y : PathAlgebra k Q} (hx : x ∈ vwSpan k (Q := Q))
    (hy : y ∈ vwSpan k (Q := Q)) : x * y ∈ vwSpan k (Q := Q) := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    induction hy using Submodule.span_induction with
    | mem b hb =>
      rcases ha with ⟨v, rfl⟩ | ⟨l, rfl⟩ <;> rcases hb with ⟨w, rfl⟩ | ⟨l', rfl⟩
      · rw [vertex_mul_vertex]
        split_ifs
        · exact vertex_mem k v
        · exact Submodule.zero_mem _
      · exact vertex_mul_word_mem k v l'
      · exact word_mul_vertex_mem k l w
      · rw [← word_append]; exact word_mem k _
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add b c _ _ hb hc => rw [mul_add]; exact Submodule.add_mem _ hb hc
    | smul r b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hb
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add a c _ _ ha hc => rw [add_mul]; exact Submodule.add_mem _ ha hc
  | smul r a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r ha

/-- **Vertices and words span the path algebra.** -/
theorem vwSpan_eq_top : vwSpan k (Q := Q) = ⊤ := by
  refine eq_top_iff.2 fun z _ ↦ ?_
  obtain ⟨x, rfl⟩ := RingQuot.mkAlgHom_surjective k (PathRel k Q) z
  induction x using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r (word_mem k [])
  | grade1 g =>
    rcases g with v | a
    · exact vertex_mem k v
    · have : word k Q [a] = arrow k Q a := by simp [word]
      change arrow k Q a ∈ _
      rw [← this]; exact word_mem k _
  | mul a b ha hb => rw [map_mul]; exact mul_mem_vwSpan k (ha trivial) (hb trivial)
  | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ (ha trivial) (hb trivial)

end FinQuiver

end LargeIndecomposable
