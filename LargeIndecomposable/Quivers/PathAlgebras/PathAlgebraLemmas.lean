module

public import LargeIndecomposable.RepresentationEmbeddings.WalkConstruction.Monomial

/-!
# Products of vertices, arrows and words in a path algebra

The relations of `kQ` as equations: `e_v e_w = δ_{vw} e_v`,
`a e_v = δ_{v, s(a)} a`, `e_v a = δ_{v, t(a)} a`, a word of a nonempty path
ending at `y` is fixed by `e_y` on the left, and `word (l ++ [a]) = a · word l`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

namespace FinQuiver

universe u

variable (k : Type u) [Field k] {Q : FinQuiver}

lemma vertex_mul_vertex (v w : Q.V) :
    vertex k Q v * vertex k Q w = if v = w then vertex k Q v else 0 := by
  have := RingQuot.mkAlgHom_rel k (PathRel.idem (k := k) (Q := Q) v w)
  rw [map_mul] at this
  rw [vertex, vertex, this]
  split_ifs <;> simp

lemma arrow_mul_src (a : Q.A) : arrow k Q a * vertex k Q (Q.src a) = arrow k Q a := by
  have := RingQuot.mkAlgHom_rel k (PathRel.src (k := k) (Q := Q) a)
  rwa [map_mul] at this

lemma tgt_mul_arrow (a : Q.A) : vertex k Q (Q.tgt a) * arrow k Q a = arrow k Q a := by
  have := RingQuot.mkAlgHom_rel k (PathRel.tgt (k := k) (Q := Q) a)
  rwa [map_mul] at this

lemma arrow_mul_vertex (a : Q.A) (v : Q.V) :
    arrow k Q a * vertex k Q v = if v = Q.src a then arrow k Q a else 0 := by
  rw [← arrow_mul_src, mul_assoc, vertex_mul_vertex]
  split_ifs with h h' h'
  · rfl
  · exact absurd h.symm h'
  · exact absurd h'.symm h
  · rw [mul_zero]

lemma vertex_mul_arrow (v : Q.V) (a : Q.A) :
    vertex k Q v * arrow k Q a = if v = Q.tgt a then arrow k Q a else 0 := by
  rw [← tgt_mul_arrow, ← mul_assoc, vertex_mul_vertex]
  split_ifs with h
  · subst h; rfl
  · rw [zero_mul]

lemma word_append_arrow (a : Q.A) : ∀ l : List Q.A,
    word k Q (l ++ [a]) = arrow k Q a * word k Q l
  | [] => by simp [word]
  | c :: l => by
    rw [List.cons_append, Rep.word_cons, Rep.word_cons, word_append_arrow a l, mul_assoc]

lemma vertex_mul_word : ∀ (c : Q.A) (l : List Q.A) (x y : Q.V), PathFrom x (c :: l) y →
    vertex k Q y * word k Q (c :: l) = word k Q (c :: l)
  | c, [], x, y, h => by
    obtain ⟨-, h2⟩ := h
    change Q.tgt c = y at h2
    subst h2
    rw [Rep.word_cons]
    simp only [word, one_mul]
    exact tgt_mul_arrow k c
  | c, d :: l, x, y, h => by
    rw [Rep.word_cons, ← mul_assoc, vertex_mul_word d l _ y h.2]

end FinQuiver

end LargeIndecomposable
