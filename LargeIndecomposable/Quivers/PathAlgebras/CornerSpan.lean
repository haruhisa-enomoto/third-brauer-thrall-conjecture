module

public import LargeIndecomposable.Quivers.PathAlgebras.PathSpan

/-!
# Corners of path algebras

For a nonempty path `l` from `i` to `j`, `word l · e_x = [x = i] word l` and
`e_y · word l = [y = j] word l`. Hence every corner `e_y p e_x` lies in the `k`-span of `e_x`
(when `x = y`) and the words of nonempty paths from `x` to `y` (`corner_mem_span`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

namespace FinQuiver

universe u

variable (k : Type u) [Field k] {Q : FinQuiver}

lemma word_mul_vertex_path {i j : Q.V} {l : List Q.A} (hl : l ≠ []) (h : PathFrom i l j)
    (x : Q.V) : word k Q l * vertex k Q x = if x = i then word k Q l else 0 := by
  match l, hl, h with
  | c :: l', _, h =>
    obtain ⟨h1, -⟩ := h
    change word k Q l' * arrow k Q c * vertex k Q x = _
    rw [mul_assoc, arrow_mul_vertex, h1]
    split_ifs <;> simp [word]

lemma vertex_mul_word_path : ∀ {i j : Q.V} {l : List Q.A}, l ≠ [] → PathFrom i l j →
    ∀ y : Q.V, vertex k Q y * word k Q l = if y = j then word k Q l else 0
  | i, j, [c], _, h, y => by
    obtain ⟨-, h2⟩ := h
    change Q.tgt c = j at h2
    change vertex k Q y * (1 * arrow k Q c) = if y = j then 1 * arrow k Q c else 0
    rw [one_mul, vertex_mul_arrow, h2]
  | i, j, c :: d :: l, _, h, y => by
    obtain ⟨-, h2⟩ := h
    change vertex k Q y * (word k Q (d :: l) * arrow k Q c) =
      if y = j then word k Q (d :: l) * arrow k Q c else 0
    rw [← mul_assoc, vertex_mul_word_path (List.cons_ne_nil _ _) h2 y]
    split_ifs <;> simp

/-- The corner generators from `x` to `y`. -/
def cornerSet (x y : Q.V) : Set (PathAlgebra k Q) :=
  {r | x = y ∧ r = vertex k Q x} ∪ {r | ∃ l : List Q.A, l ≠ [] ∧ PathFrom x l y ∧ r = word k Q l}

/-- **Corners lie in the span of the corner generators.** -/
theorem corner_mem_span (p : PathAlgebra k Q) (x y : Q.V) :
    vertex k Q y * p * vertex k Q x ∈ Submodule.span k (cornerSet k x y) := by
  classical
  have hp : p ∈ vwSpan k (Q := Q) := by rw [vwSpan_eq_top]; trivial
  induction hp using Submodule.span_induction with
  | mem r hr =>
    rcases hr with ⟨v, rfl⟩ | ⟨l, rfl⟩
    · rw [vertex_mul_vertex, ite_mul, zero_mul, vertex_mul_vertex]
      split_ifs with h1 h2
      · subst h1 h2
        exact Submodule.subset_span (Or.inl ⟨rfl, rfl⟩)
      · exact Submodule.zero_mem _
      · exact Submodule.zero_mem _
    · rcases eq_or_ne l [] with rfl | hl
      · change vertex k Q y * 1 * vertex k Q x ∈ _
        rw [mul_one, vertex_mul_vertex]
        split_ifs with h
        · subst h
          exact Submodule.subset_span (Or.inl ⟨rfl, rfl⟩)
        · exact Submodule.zero_mem _
      · by_cases hpath : ∃ i j, PathFrom i l j
        · obtain ⟨i, j, h⟩ := hpath
          rw [vertex_mul_word_path k hl h y]
          split_ifs with hy
          · rw [word_mul_vertex_path k hl h x]
            split_ifs with hx
            · subst hx hy
              exact Submodule.subset_span (Or.inr ⟨l, hl, h, rfl⟩)
            · exact Submodule.zero_mem _
          · rw [zero_mul]
            exact Submodule.zero_mem _
        · rw [word_eq_zero_of_not_path k l hpath, mul_zero, zero_mul]
          exact Submodule.zero_mem _
  | zero => rw [mul_zero, zero_mul]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [mul_add, add_mul]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ c ha

end FinQuiver

end LargeIndecomposable
