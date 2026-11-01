module

public import LargeIndecomposable.RayCategories.Basic.MorphismDepth

/-!
# Chains and tackles of a ray category (BGRS 1.9, 8.4)

A chain is a zigzag `x₀ -ρ₀→ z₀ ←σ₀- x₁ -ρ₁→ z₁ ← … ` of nonzero morphisms in
which no peak `(ρᵢ, σᵢ)` and no valley `(σᵢ, ρᵢ₊₁)` closes to a commutative
triangle. We store it as the list of its morphisms (as ray morphisms), with
alternating peak and valley conditions between consecutive entries
(`RayCat.IsChainFrom`). A tackle is a chain whose last morphism is
irreducible; its efficiency is the word of depths of its morphisms.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe v u

namespace RayCat

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- Two morphisms form a peak: common target, and neither factors through the
other from the left. -/
def Peak (f g : RayMor P) : Prop :=
  ∃ h : f.2.1 = g.2.1,
    (¬∃ c : f.1 ⟶ g.1, c ≫ g.2.2 = f.2.2 ≫ eqToHom h) ∧
      ¬∃ c : g.1 ⟶ f.1, c ≫ f.2.2 ≫ eqToHom h = g.2.2

/-- Two morphisms form a valley: common source, and neither factors through
the other from the right. -/
def Valley (f g : RayMor P) : Prop :=
  ∃ h : f.1 = g.1,
    (¬∃ c : f.2.1 ⟶ g.2.1, eqToHom h.symm ≫ f.2.2 ≫ c = g.2.2) ∧
      ¬∃ c : g.2.1 ⟶ f.2.1, eqToHom h ≫ g.2.2 ≫ c = f.2.2

/-- The relation between the entries at positions `j` and `j + 1`: a peak for
even `j`, a valley for odd `j`. -/
def Link (j : ℕ) (f g : RayMor P) : Prop := if j % 2 = 0 then Peak f g else Valley f g

/-- A chain (BGRS 1.9): nonzero morphisms with alternating peak and valley
conditions; the link after position `j` is `Link (j + o)` (offset `o = 0`:
starting with a peak). -/
def IsChain (o : ℕ) (l : List (RayMor P)) : Prop :=
  (∀ f ∈ l, f.2.2 ≠ 0) ∧ ∀ (j : ℕ) (h : j + 1 < l.length), Link (j + o) l[j] l[j + 1]

/-- The efficiency word: depths of the morphisms. -/
def efficiency (l : List (RayMor P)) : List ℕ := l.map fun f ↦ depth f.2.2

/-- A tackle with offset `o`: a chain whose last morphism is irreducible and
satisfies `adm` (for Fischbacher: lies in an essential contour). The start
point plays no role for finite ray categories and is not fixed. -/
def IsTackle (adm : RayMor P → Prop) (o : ℕ) (l : List (RayMor P)) : Prop :=
  ∃ h : l ≠ [], IsChain o l ∧ IsIrreducible (l.getLast h).2.2 ∧ adm (l.getLast h)

/-- An efficient tackle: no tackle with the same offset has a larger
efficiency word. -/
def IsEfficient (adm : RayMor P → Prop) (o : ℕ) (l : List (RayMor P)) : Prop :=
  IsTackle adm o l ∧ ∀ l', IsTackle adm o l' → ¬List.Lex (· < ·) (efficiency l) (efficiency l')

omit [IsRayCategory P] in
/-- Keeping the first `k` entries of a chain and attaching two new entries. -/
lemma isChain_take_append {o : ℕ} (l : List (RayMor P)) (hl : IsChain o l) (k : ℕ)
    (hk : k ≤ l.length) (a b : RayMor P) (ha : a.2.2 ≠ 0) (hb : b.2.2 ≠ 0)
    (hlink : ∀ (h : 0 < k), Link (k - 1 + o) (l[k - 1]'(by omega)) a) (hab : Link (k + o) a b) :
    IsChain o (l.take k ++ [a, b]) := by
  refine ⟨fun f hf ↦ ?_, fun j hj ↦ ?_⟩
  · rcases List.mem_append.1 hf with hf | hf
    · exact hl.1 f (List.mem_of_mem_take hf)
    · simp at hf
      rcases hf with rfl | rfl
      · exact ha
      · exact hb
  · have hlen : (l.take k ++ [a, b]).length = k + 2 := by simp; omega
    rw [hlen] at hj
    rcases Nat.lt_or_ge (j + 1) k with h1 | h1
    · simp only [List.getElem_append_left (by simp; omega : j < (l.take k).length),
        List.getElem_append_left (by simp; omega : j + 1 < (l.take k).length),
        List.getElem_take]
      exact hl.2 j (by omega)
    · rcases Nat.lt_or_ge j k with h2 | h2
      · have hj1 : j + 1 = k := by omega
        subst hj1
        rw [List.getElem_append_left (by simp; omega : j < (l.take (j + 1)).length),
          List.getElem_append_right (by simp)]
        simp only [List.getElem_take, List.length_take, Nat.min_eq_left hk, Nat.sub_self,
          List.getElem_cons_zero]
        exact hlink (by omega)
      · have hjk : j = k := by omega
        subst hjk
        rw [List.getElem_append_right (by simp), List.getElem_append_right (by simp)]
        simp only [List.length_take, Nat.min_eq_left hk, Nat.sub_self, List.getElem_cons_zero,
          Nat.add_sub_cancel_left, List.getElem_cons_succ]
        exact hab

/-- A word with an equal prefix and a larger next letter is larger. -/
lemma lex_take_append {l : List ℕ} {k : ℕ} (hk : k < l.length) (x : ℕ) (hx : l[k] < x)
    (r : List ℕ) : List.Lex (· < ·) l (l.take k ++ x :: r) := by
  have key : ∀ (p s t : List ℕ) (a b : ℕ), a < b → List.Lex (· < ·) (p ++ a :: s) (p ++ b :: t) := by
    intro p s t a b hab
    induction p with
    | nil => exact List.Lex.rel hab
    | cons c p ih => exact List.Lex.cons ih
  conv_lhs => rw [← List.take_append_drop k l, List.drop_eq_getElem_cons hk]
  exact key _ _ _ _ _ hx

/-- A proper extension is larger. -/
lemma lex_of_prefix (l : List ℕ) (x : ℕ) (r : List ℕ) :
    List.Lex (· < ·) l (l ++ x :: r) := by
  induction l with
  | nil => exact List.Lex.nil
  | cons a l ih => exact List.Lex.cons ih

lemma getLast_append_pair {α : Type*} (L : List α) (f g : α) (h : L ++ [f, g] ≠ []) :
    (L ++ [f, g]).getLast h = g := by
  rw [List.getLast_eq_getElem]
  simp

omit [IsRayCategory P] in
lemma efficiency_take_append (l : List (RayMor P)) (k : ℕ) (f g : RayMor P) :
    efficiency (l.take k ++ [f, g]) = (efficiency l).take k ++ [depth f.2.2, depth g.2.2] := by
  simp [efficiency, List.map_take]

/-- Replacing the `k`-th entry by a deeper one (or extending the word when `k`
is the last position) gives a larger efficiency word. -/
lemma lex_candidate (l : List (RayMor P)) (k : ℕ) (hk : k < l.length) (f g : RayMor P)
    (hdep : depth l[k].2.2 ≤ depth f.2.2)
    (hstr : k + 1 = l.length ∨ depth l[k].2.2 < depth f.2.2) :
    List.Lex (· < ·) (efficiency l) (efficiency (l.take k ++ [f, g])) := by
  rw [efficiency_take_append]
  by_cases hlt : depth l[k].2.2 < depth f.2.2
  · exact lex_take_append (by simp [efficiency]; omega) _ (by simpa [efficiency] using hlt) _
  · have heq : depth l[k].2.2 = depth f.2.2 := by omega
    have hlen : k + 1 = l.length := hstr.resolve_right hlt
    have hl : efficiency l = (efficiency l).take k ++ [depth f.2.2] := by
      rw [← heq]
      conv_lhs => rw [← List.take_append_drop k (efficiency l)]
      congr 1
      rw [List.drop_eq_getElem_cons (by simp [efficiency]; omega)]
      simp [efficiency]
      omega
    conv_lhs => rw [hl]
    rw [show (efficiency l).take k ++ [depth f.2.2, depth g.2.2] =
      ((efficiency l).take k ++ [depth f.2.2]) ++ depth g.2.2 :: [] by simp]
    exact lex_of_prefix _ _ _

end RayCat

end LargeIndecomposable
