module

public import LargeIndecomposable.RayCategories.Basic.RayQuiver
public import LargeIndecomposable.Quivers.PathAlgebras.PathSpan

/-!
# Ray categories without contours have monomial linearizations

A finite ray category `P` has no contours (`NoContour`) if two directed paths of `Q_P` with the
same nonzero value are equal. Then the kernel of the presentation `kQ_P → k(P)` is spanned by the
words of the paths with zero value (`ker_linPres_le`): the linearization is a zero-relation
algebra.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits FinQuiver

namespace RayQuiver

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P]

variable (P) in
/-- No contours: directed paths with the same nonzero value are equal. -/
def NoContour : Prop :=
  ∀ (l l' : List (quiver P).A) (x y : P) (h : PathFrom (D := quiver P) x l y)
    (h' : PathFrom (D := quiver P) x l' y), pathMor l x y h = pathMor l' x y h' →
      pathMor l x y h ≠ 0 → l = l'

variable (P) in
/-- The directed paths with zero value. -/
def ZeroPaths : Set (List (quiver P).A) :=
  {l | ∃ (x y : P) (h : PathFrom (D := quiver P) x l y), pathMor l x y h = 0}

lemma pathFrom_split : ∀ (l l' : List (quiver P).A) (x z : P),
    PathFrom (D := quiver P) x (l ++ l') z →
      ∃ y, PathFrom (D := quiver P) x l y ∧ PathFrom (D := quiver P) y l' z
  | [], _, x, _, h => ⟨x, rfl, h⟩
  | e :: l, l', x, z, h => by
    obtain ⟨y, h1, h2⟩ := pathFrom_split l l' _ z h.2
    exact ⟨y, ⟨h.1, h1⟩, h2⟩

lemma pathFrom_tgt_unique : ∀ (l : List (quiver P).A) (x y y' : P),
    PathFrom (D := quiver P) x l y → PathFrom (D := quiver P) x l y' → y = y'
  | [], _, _, _, h, h' => (show _ = _ from h).symm.trans h'
  | _ :: l, _, y, y', h, h' => pathFrom_tgt_unique l _ y y' h.2 h'.2

lemma pathFrom_src_unique : ∀ (l : List (quiver P).A) (x x' y y' : P), l ≠ [] →
    PathFrom (D := quiver P) x l y → PathFrom (D := quiver P) x' l y' → x = x'
  | [], _, _, _, _, hl, _, _ => absurd rfl hl
  | _ :: _, _, _, _, _, _, h, h' => h.1.symm.trans h'.1

lemma ne_nil_of_mem_zeroPaths {l : List (quiver P).A} (hl : l ∈ ZeroPaths P) : l ≠ [] := by
  rintro rfl
  obtain ⟨x, y, h, h0⟩ := hl
  change x = y at h
  subst h
  exact IsRayCategory.id_ne_zero x (by simpa [pathMor] using h0)

variable (k : Type*) [Field k]

/-- Appending to a zero path gives a zero path or a vanishing word. -/
lemma append_zero_right {l : List (quiver P).A} (hl : l ∈ ZeroPaths P) (l' : List (quiver P).A) :
    word k (quiver P) (l ++ l') = 0 ∨ l ++ l' ∈ ZeroPaths P := by
  by_cases hp : ∃ x z, PathFrom (D := quiver P) x (l ++ l') z
  · obtain ⟨x, z, h⟩ := hp
    obtain ⟨y, h1, h2⟩ := pathFrom_split l l' x z h
    obtain ⟨x₀, y₀, h0, hz⟩ := hl
    obtain rfl := pathFrom_src_unique l x₀ x y₀ y (ne_nil_of_mem_zeroPaths ⟨x₀, y₀, h0, hz⟩) h0 h1
    obtain rfl := pathFrom_tgt_unique l x₀ y₀ y h0 h1
    refine Or.inr ⟨x₀, z, pathFrom_append l l' x₀ y₀ z h0 h2, ?_⟩
    rw [pathMor_append l l' x₀ y₀ z h0 h2, hz, zero_comp]
  · exact Or.inl (word_eq_zero_of_not_path k _ hp)

lemma append_zero_left {l : List (quiver P).A} (hl : l ∈ ZeroPaths P) (l' : List (quiver P).A) :
    word k (quiver P) (l' ++ l) = 0 ∨ l' ++ l ∈ ZeroPaths P := by
  by_cases hp : ∃ x z, PathFrom (D := quiver P) x (l' ++ l) z
  · obtain ⟨x, z, h⟩ := hp
    obtain ⟨y, h1, h2⟩ := pathFrom_split l' l x z h
    obtain ⟨x₀, y₀, h0, hz⟩ := hl
    have hne := ne_nil_of_mem_zeroPaths ⟨x₀, y₀, h0, hz⟩
    obtain rfl := pathFrom_src_unique l x₀ y y₀ z hne h0 h2
    obtain rfl := pathFrom_tgt_unique l x₀ z y₀ h2 h0
    refine Or.inr ⟨x, z, pathFrom_append l' l x x₀ z h1 h2, ?_⟩
    rw [pathMor_append l' l x x₀ z h1 h2, hz, comp_zero]
  · exact Or.inl (word_eq_zero_of_not_path k _ hp)

variable (P) in
/-- The span of the words of zero paths. -/
def zspan : Submodule k ((quiver P).PathAlgebra k) :=
  Submodule.span k (word k (quiver P) '' ZeroPaths P)

lemma word_mem_zspan {l : List (quiver P).A} (hl : l ∈ ZeroPaths P) :
    word k (quiver P) l ∈ zspan P k :=
  Submodule.subset_span ⟨l, hl, rfl⟩

lemma word_mul_mem (l' : List (quiver P).A) {z : (quiver P).PathAlgebra k}
    (hz : z ∈ zspan P k) : word k (quiver P) l' * z ∈ zspan P k := by
  induction hz using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l, hl, rfl⟩ := ha
    rw [← word_append]
    rcases append_zero_right k hl l' with h | h
    · rw [h]; exact Submodule.zero_mem _
    · exact word_mem_zspan k h
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ r ha

lemma mul_word_mem (l' : List (quiver P).A) {z : (quiver P).PathAlgebra k}
    (hz : z ∈ zspan P k) : z * word k (quiver P) l' ∈ zspan P k := by
  induction hz using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l, hl, rfl⟩ := ha
    rw [← word_append]
    rcases append_zero_left k hl l' with h | h
    · rw [h]; exact Submodule.zero_mem _
    · exact word_mem_zspan k h
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r ha

lemma vertex_mul_mem (v : P) {z : (quiver P).PathAlgebra k} (hz : z ∈ zspan P k) :
    vertex k (quiver P) v * z ∈ zspan P k := by
  induction hz using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l, hl, rfl⟩ := ha
    obtain ⟨x, y, h, h0⟩ := hl
    rcases l with _ | ⟨c, l⟩
    · exact absurd rfl (ne_nil_of_mem_zeroPaths ⟨x, y, h, h0⟩)
    · by_cases hv : v = y
      · subst hv
        rw [vertex_mul_word k c l x v h]
        exact word_mem_zspan k ⟨x, v, h, h0⟩
      · rw [← vertex_mul_word k c l x y h, ← mul_assoc, vertex_mul_vertex, if_neg hv, zero_mul]
        exact Submodule.zero_mem _
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ r ha

lemma mul_vertex_mem (v : P) {z : (quiver P).PathAlgebra k} (hz : z ∈ zspan P k) :
    z * vertex k (quiver P) v ∈ zspan P k := by
  induction hz using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l, hl, rfl⟩ := ha
    obtain ⟨x, y, h, h0⟩ := hl
    rcases l with _ | ⟨c, l⟩
    · exact absurd rfl (ne_nil_of_mem_zeroPaths ⟨x, y, h, h0⟩)
    · by_cases hv : v = (quiver P).src c
      · subst hv
        rw [word_mul_vertex_src]
        exact word_mem_zspan k ⟨x, y, h, h0⟩
      · rw [← word_mul_vertex_src, mul_assoc, vertex_mul_vertex, if_neg (Ne.symm hv), mul_zero]
        exact Submodule.zero_mem _
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r ha

lemma mul_mem_left (a : (quiver P).PathAlgebra k) {z : (quiver P).PathAlgebra k}
    (hz : z ∈ zspan P k) : a * z ∈ zspan P k := by
  have ha : a ∈ vwSpan k (Q := quiver P) := by rw [vwSpan_eq_top]; trivial
  induction ha using Submodule.span_induction with
  | mem b hb =>
    rcases hb with ⟨v, rfl⟩ | ⟨l, rfl⟩
    · exact vertex_mul_mem k v hz
    · exact word_mul_mem k l hz
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add b c _ _ hb hc => rw [add_mul]; exact Submodule.add_mem _ hb hc
  | smul r b _ hb => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hb

lemma mul_mem_right (a : (quiver P).PathAlgebra k) {z : (quiver P).PathAlgebra k}
    (hz : z ∈ zspan P k) : z * a ∈ zspan P k := by
  have ha : a ∈ vwSpan k (Q := quiver P) := by rw [vwSpan_eq_top]; trivial
  induction ha using Submodule.span_induction with
  | mem b hb =>
    rcases hb with ⟨v, rfl⟩ | ⟨l, rfl⟩
    · exact mul_vertex_mem k v hz
    · exact mul_word_mem k l hz
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add b c _ _ hb hc => rw [mul_add]; exact Submodule.add_mem _ hb hc
  | smul r b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hb

/-- **Without contours the linearization is a zero-relation algebra.** -/
theorem ker_linPres_le (hnc : NoContour P) (z : (quiver P).PathAlgebra k)
    (hz : linPres P k z = 0) : z ∈ zspan P k := by
  have hrel : ∀ a b, RingQuot.Rel (LinRel P k) a b → a - b ∈ zspan P k := by
    intro a b h
    induction h with
    | of h =>
      rcases h with ⟨l, x, y, h, h0⟩ | ⟨l, l', x, y, h, h', he⟩
      · rw [sub_zero]; exact word_mem_zspan k ⟨x, y, h, h0⟩
      · by_cases h0 : pathMor l x y h = 0
        · exact Submodule.sub_mem _ (word_mem_zspan k ⟨x, y, h, h0⟩)
            (word_mem_zspan k ⟨x, y, h', he ▸ h0⟩)
        · rw [hnc l l' x y h h' he h0, sub_self]; exact Submodule.zero_mem _
    | add_left _ ih => rwa [add_sub_add_right_eq_sub]
    | mul_left _ ih => rw [← sub_mul]; exact mul_mem_right k _ ih
    | mul_right _ ih => rw [← mul_sub]; exact mul_mem_left k _ ih
  have heq : Relation.EqvGen (RingQuot.Rel (LinRel P k)) z 0 := by
    have h1 : linPres P k z = linPres P k 0 := by rw [hz, map_zero]
    simp only [linPres, RingQuot.mkAlgHom_def, RingQuot.mkRingHom_def] at h1
    exact Quot.eqvGen_exact (congrArg RingQuot.toQuot h1)
  have key : ∀ a b, Relation.EqvGen (RingQuot.Rel (LinRel P k)) a b → a - b ∈ zspan P k := by
    intro a b hab
    induction hab with
    | rel a b h => exact hrel a b h
    | refl a => rw [sub_self]; exact Submodule.zero_mem _
    | symm a b _ ih => rw [← neg_sub]; exact Submodule.neg_mem _ ih
    | trans a b c _ _ iab ibc => rw [← sub_add_sub_cancel a b c]; exact Submodule.add_mem _ iab ibc
  simpa using key z 0 heq

end RayQuiver

end LargeIndecomposable
