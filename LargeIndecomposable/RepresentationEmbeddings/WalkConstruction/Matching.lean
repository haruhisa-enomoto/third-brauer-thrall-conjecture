module

public import LargeIndecomposable.Quivers.PathAlgebras.FiniteQuiver
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Logic.Relation
public import Mathlib.Tactic.LinearCombination

/-!
# The matching quiver of a closed walk

Definition 4.5 and Lemma 4.6. The cycle `D_w` of a closed walk is described
by cycle coordinates (`CycleCoords`): its vertices and arrows are numbered by
`ZMod r`, arrow `x` joining the vertices `x` and `x + 1`, forwards (from `x`
to `x + 1`) or backwards. For a quiver morphism `p : D_w → Q`, the matching
quiver `H` has the pairs `(j, i)` of vertices as vertices, and an edge for each
pair of arrows `α` at `j` and `β` at `i` with the same label, both leaving or
both entering (`Inc`); it joins `(j, i)` to the pair of the other endpoints
(`Adj`). Components are classes of `Conn`, the reflexive transitive closure.

For `p` injective on the arrows with a fixed source and on those with a
fixed target (3.4), we prove the facts of Lemma 4.6 used in Proposition 4.7:

* `diag_iff_of_conn`: the diagonal pairs form a union of components;
* `eq_of_conn_of_snd_eq`: on each component the second coordinate determines
  the first;
* `exists_col_not_conn`: if the walk is primitive (`Primitive`: no nontrivial
  rotation of the cycle preserves the labels and orientations of the arrows),
  every component off the diagonal misses some second coordinate.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

namespace FinQuiver

open Relation

/-- Cycle coordinates on a quiver `D`: vertices and arrows numbered by
`ZMod r`, the arrow `x` joining the vertices `x` and `x + 1`, from `x` to
`x + 1` if `fwd` holds and from `x + 1` to `x` otherwise. -/
structure CycleCoords (D : FinQuiver) (r : ℕ) where
  /-- The position of a vertex. -/
  pos : D.V ≃ ZMod r
  /-- The position of an arrow. -/
  eix : D.A ≃ ZMod r
  /-- The orientation of an arrow. -/
  fwd : D.A → Bool
  pos_src : ∀ e, pos (D.src e) = if fwd e then eix e else eix e + 1
  pos_tgt : ∀ e, pos (D.tgt e) = if fwd e then eix e + 1 else eix e

variable {D Q : FinQuiver} (p : Hom D Q)

/-- `α` at `a.1` and `β` at `a.2` carry the same label and both leave or both
enter: they give an edge of the matching quiver at `a`. -/
def Inc (a : D.V × D.V) (α β : D.A) : Prop :=
  p.arr α = p.arr β ∧ ((D.src α = a.1 ∧ D.src β = a.2) ∨ (D.tgt α = a.1 ∧ D.tgt β = a.2))

/-- The other endpoint of an arrow at a vertex. -/
def other (v : D.V) (α : D.A) : D.V := if D.src α = v then D.tgt α else D.src α

/-- Adjacency in the matching quiver. -/
def Adj (a b : D.V × D.V) : Prop := ∃ α β, Inc p a α β ∧ b = (other a.1 α, other a.2 β)

/-- Being in the same component of the matching quiver. -/
def Conn : D.V × D.V → D.V × D.V → Prop := ReflTransGen (Adj p)

lemma adj_src_tgt {α β : D.A} (h : p.arr α = p.arr β) :
    Adj p (D.src α, D.src β) (D.tgt α, D.tgt β) := by
  refine ⟨α, β, ⟨h, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩
  simp [other]

lemma inc_fst {a : D.V × D.V} {α β : D.A} (h : Inc p a α β) : D.src α = a.1 ∨ D.tgt α = a.1 := by
  rcases h.2 with h | h
  exacts [Or.inl h.1, Or.inr h.1]

lemma inc_snd {a : D.V × D.V} {α β : D.A} (h : Inc p a α β) : D.src β = a.2 ∨ D.tgt β = a.2 := by
  rcases h.2 with h | h
  exacts [Or.inl h.2, Or.inr h.2]

section Coords

variable {r : ℕ} [Fact (1 < r)] (C : CycleCoords D r)

lemma one_ne_zero' : (1 : ZMod r) ≠ 0 := by
  intro h
  have := ZMod.val_one r
  rw [h, ZMod.val_zero] at this
  exact zero_ne_one this

include C

lemma src_ne_tgt (e : D.A) : D.src e ≠ D.tgt e := by
  intro h
  have := congrArg C.pos h
  rw [C.pos_src, C.pos_tgt] at this
  have h1 := one_ne_zero' (r := r)
  split_ifs at this with hf
  · exact h1 (by simpa using this.symm)
  · exact h1 (by simp at this)

/-- The sign of an arrow at an endpoint: `1` if the arrow goes from it to the
next position, `-1` if to the previous one. -/
def sgn (v : D.V) (α : D.A) : ℤ := if C.eix α = C.pos v then 1 else -1

omit [Fact (1 < r)] in
lemma sgn_sq (v : D.V) (α : D.A) : sgn C v α * sgn C v α = 1 := by
  unfold sgn; split_ifs <;> norm_num

/-- An arrow at `v` has position `v` or `v - 1`. -/
lemma eix_of_inc {v : D.V} {α : D.A} (h : D.src α = v ∨ D.tgt α = v) :
    C.eix α = C.pos v ∨ C.eix α = C.pos v - 1 := by
  rcases h with rfl | rfl
  · rw [C.pos_src]; split_ifs <;> simp
  · rw [C.pos_tgt]; split_ifs <;> simp

lemma pos_other {v : D.V} {α : D.A} (h : D.src α = v ∨ D.tgt α = v) :
    C.pos (other v α) = C.pos v + (sgn C v α : ZMod r) := by
  have h1 := one_ne_zero' (r := r)
  unfold other sgn
  by_cases hs : D.src α = v
  · subst hs
    rw [ite_eq_left rfl, C.pos_tgt, C.pos_src]
    cases C.fwd α
    · simp only [Bool.false_eq_true, ite_false]
      rw [ite_eq_right (by intro h'; exact h1 (by simpa using h'.symm))]
      push_cast; ring
    · simp
  · have ht : D.tgt α = v := h.resolve_left hs
    subst ht
    rw [ite_eq_right hs, C.pos_tgt, C.pos_src]
    cases C.fwd α
    · simp
    · simp only [ite_true]
      rw [ite_eq_right (by intro h'; exact h1 (by simp at h'))]
      push_cast; ring

lemma sgn_other {v : D.V} {α : D.A} (h : D.src α = v ∨ D.tgt α = v) :
    sgn C (other v α) α = - sgn C v α := by
  have h1 := one_ne_zero' (r := r)
  have hp := pos_other C h
  rcases eix_of_inc C h with he | he
  · have : sgn C v α = 1 := by simp [sgn, he]
    rw [this, sgn, ite_eq_right (by rw [hp, this, he]; intro h'; exact h1 (by simpa using h'.symm))]
  · have hne : C.eix α ≠ C.pos v := by
      rw [he]; intro h'; exact h1 (by simp at h')
    have : sgn C v α = -1 := by simp [sgn, hne]
    rw [this, sgn, ite_eq_left (by rw [hp, this, he]; push_cast; ring)]
    norm_num

/-- Distinct arrows at a vertex have opposite signs there. -/
lemma sgn_eq_neg {v : D.V} {α α' : D.A} (h : D.src α = v ∨ D.tgt α = v)
    (h' : D.src α' = v ∨ D.tgt α' = v) (hne : α ≠ α') : sgn C v α = - sgn C v α' := by
  rcases eix_of_inc C h with he | he <;> rcases eix_of_inc C h' with he' | he'
  · exact absurd (C.eix.injective (he.trans he'.symm)) hne
  · have : C.eix α' ≠ C.pos v := by
      rw [he']; intro h''; exact one_ne_zero' (r := r) (by simp at h'')
    simp [sgn, he, this]
  · have : C.eix α ≠ C.pos v := by
      rw [he]; intro h''; exact one_ne_zero' (r := r) (by simp at h'')
    simp [sgn, he', this]
  · exact absurd (C.eix.injective (he.trans he'.symm)) hne

variable {p}

/-- The type of an edge of the matching quiver at `a`. -/
def type (a : D.V × D.V) (α β : D.A) : ℤ := sgn C a.1 α * sgn C a.2 β

omit [Fact (1 < r)] in
lemma type_eq_one_or (a : D.V × D.V) (α β : D.A) : type C a α β = 1 ∨ type C a α β = -1 := by
  unfold type sgn; split_ifs <;> norm_num

/-- The edge at the other end is again an edge, with the same type. -/
lemma inc_other_pair {a : D.V × D.V} {α β : D.A} (h : Inc p a α β) :
    Inc p (other a.1 α, other a.2 β) α β := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · right
    simp [other, h1, h2]
  · left
    have n1 : D.src α ≠ a.1 := h1 ▸ src_ne_tgt C α
    have n2 : D.src β ≠ a.2 := h2 ▸ src_ne_tgt C β
    simp [other, n1, n2]

lemma type_other {a : D.V × D.V} {α β : D.A} (h : Inc p a α β) :
    type C (other a.1 α, other a.2 β) α β = type C a α β := by
  simp only [type, sgn_other C (inc_fst p h), sgn_other C (inc_snd p h), neg_mul_neg]

lemma other_other {v : D.V} {α : D.A} (h : D.src α = v ∨ D.tgt α = v) : other (other v α) α = v := by
  unfold other
  by_cases hs : D.src α = v
  · rw [ite_eq_left hs, ite_eq_right (hs ▸ (src_ne_tgt C α)), hs]
  · rw [ite_eq_right hs, ite_eq_left rfl]; exact h.resolve_left hs

variable (hloc : p.LocallyInjective)
include hloc

lemma inc_unique_snd {a : D.V × D.V} {α β β' : D.A} (h : Inc p a α β) (h' : Inc p a α β') :
    β = β' := by
  rcases h.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h'.2 with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · exact hloc.1 β β' (h2.trans h2'.symm) (h.1.symm.trans h'.1)
  · exact absurd (h1.trans h1'.symm) (src_ne_tgt C α)
  · exact absurd (h1'.trans h1.symm) (src_ne_tgt C α)
  · exact hloc.2 β β' (h2.trans h2'.symm) (h.1.symm.trans h'.1)

lemma inc_unique_fst {a : D.V × D.V} {α α' β : D.A} (h : Inc p a α β) (h' : Inc p a α' β) :
    α = α' := by
  rcases h.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h'.2 with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · exact hloc.1 α α' (h1.trans h1'.symm) (h.1.trans h'.1.symm)
  · exact absurd (h2.trans h2'.symm) (src_ne_tgt C β)
  · exact absurd (h2'.trans h2.symm) (src_ne_tgt C β)
  · exact hloc.2 α α' (h1.trans h1'.symm) (h.1.trans h'.1.symm)

/-- All edges of the matching quiver at a vertex have the same type. -/
lemma type_eq {a : D.V × D.V} {α β α' β' : D.A} (h : Inc p a α β) (h' : Inc p a α' β') :
    type C a α β = type C a α' β' := by
  by_cases hα : α = α'
  · subst hα
    rw [inc_unique_snd C hloc h h']
  · have hβ : β ≠ β' := fun hβ ↦ hα (inc_unique_fst C hloc h (hβ ▸ h'))
    simp only [type, sgn_eq_neg C (inc_fst p h) (inc_fst p h') hα,
      sgn_eq_neg C (inc_snd p h) (inc_snd p h') hβ, neg_mul_neg]

omit hloc in
lemma adj_symm {a b : D.V × D.V} (h : Adj p a b) : Adj p b a := by
  obtain ⟨α, β, hi, rfl⟩ := h
  refine ⟨α, β, inc_other_pair C hi, ?_⟩
  simp [other_other C (inc_fst p hi), other_other C (inc_snd p hi)]

omit hloc in
lemma conn_symm {a b : D.V × D.V} (h : Conn p a b) : Conn p b a := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ReflTransGen.head (adj_symm C hbc) ih

omit hloc [Fact (1 < r)] C in
lemma conn_trans {a b c : D.V × D.V} (h : Conn p a b) (h' : Conn p b c) : Conn p a c :=
  ReflTransGen.trans h h'

omit [Fact (1 < r)] C in
/-- A diagonal vertex of the matching quiver is adjacent only to diagonal
vertices. -/
lemma adj_diag {a b : D.V × D.V} (h : Adj p a b) (ha : a.1 = a.2) : b.1 = b.2 := by
  obtain ⟨α, β, hi, rfl⟩ := h
  have : α = β := by
    rcases hi.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hloc.1 α β (h1.trans (ha.trans h2.symm)) hi.1
    · exact hloc.2 α β (h1.trans (ha.trans h2.symm)) hi.1
  subst this
  simp [ha]

/-- Lemma 4.6: the diagonal pairs form a union of components. -/
lemma diag_iff_of_conn {a b : D.V × D.V} (h : Conn p a b) : a.1 = a.2 ↔ b.1 = b.2 := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hbc ih =>
    exact ⟨fun ha ↦ adj_diag hloc hbc (ih.1 ha),
      fun hc ↦ ih.2 (adj_diag hloc (adj_symm C hbc) hc)⟩

/-- A common type of the edges at `a₀`. -/
lemma exists_type (a₀ : D.V × D.V) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ α β, Inc p a₀ α β → type C a₀ α β = s := by
  by_cases h : ∃ α β, Inc p a₀ α β
  · obtain ⟨α, β, hi⟩ := h
    exact ⟨type C a₀ α β, type_eq_one_or C a₀ α β, fun α' β' hi' ↦ type_eq C hloc hi' hi⟩
  · push Not at h
    exact ⟨1, Or.inl rfl, fun α β hi ↦ absurd hi (h α β)⟩

/-- Each component lies on a line `pos j - pos j₀ = s (pos i - pos i₀)`, and all
its edges have type `s`. -/
lemma line {a₀ : D.V × D.V} {s : ℤ} (h₀ : ∀ α β, Inc p a₀ α β → type C a₀ α β = s)
    {a : D.V × D.V} (h : Conn p a₀ a) :
    C.pos a.1 - C.pos a₀.1 = (s : ZMod r) * (C.pos a.2 - C.pos a₀.2) ∧
      ∀ α β, Inc p a α β → type C a α β = s := by
  induction h with
  | refl => exact ⟨by simp, h₀⟩
  | @tail b c _ hbc ih =>
    obtain ⟨α, β, hi, rfl⟩ := hbc
    obtain ⟨ih1, ih2⟩ := ih
    have ht := ih2 α β hi
    refine ⟨?_, fun α' β' hi' ↦ ?_⟩
    · rw [pos_other C (inc_fst p hi), pos_other C (inc_snd p hi)]
      have hs : sgn C b.1 α = s * sgn C b.2 β := by
        rw [← ht, type, mul_assoc, sgn_sq, mul_one]
      rw [hs]
      push_cast
      linear_combination ih1
    · rw [type_eq C hloc hi' (inc_other_pair C hi), type_other C hi, ht]

/-- Lemma 4.6: on a component the second coordinate determines the first. -/
lemma eq_of_conn_of_snd_eq {a₀ a b : D.V × D.V} (ha : Conn p a₀ a) (hb : Conn p a₀ b)
    (h : a.2 = b.2) : a = b := by
  obtain ⟨s, -, hs⟩ := exists_type C hloc a₀
  have h1 := (line C hloc hs ha).1
  have h2 := (line C hloc hs hb).1
  rw [h] at h1
  have : a.1 = b.1 := C.pos.injective (by linear_combination h1 - h2)
  exact Prod.ext this h

end Coords

section Primitive

variable {r : ℕ} [Fact (1 < r)] (C : CycleCoords D r)

/-- The signed label of the arrow at position `x`. -/
def signedLabel (x : ZMod r) : Q.A × Bool := (p.arr (C.eix.symm x), C.fwd (C.eix.symm x))

/-- The walk is primitive: no nontrivial rotation of the cycle preserves the
signed labels. -/
def Primitive : Prop := ∀ τ : ZMod r, τ ≠ 0 → ∃ x, signedLabel p C (x + τ) ≠ signedLabel p C x

/-- If `f (x + τ) = f x` for all `x` but one, then also for that one. -/
lemma rot_of_all_but_one {β : Type*} (f : ZMod r → β) (τ x₀ : ZMod r)
    (h : ∀ x, x ≠ x₀ → f (x + τ) = f x) : f (x₀ + τ) = f x₀ := by
  have hpos := addOrderOf_pos τ
  have key : ∀ k, 1 ≤ k → k ≤ addOrderOf τ → f (x₀ + k • τ) = f (x₀ + τ) := by
    intro k hk1 hk2
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · rw [succ_nsmul, ← add_assoc, h _ ?_, ih hk (by omega)]
        intro he
        exact nsmul_ne_zero_of_lt_addOrderOf (n := k) (x := τ) (by omega) (by omega)
          (by simpa using congrArg (· - x₀) he)
  have := key _ hpos le_rfl
  rw [addOrderOf_nsmul_eq_zero, add_zero] at this
  exact this.symm

omit [Fact (1 < r)] in
lemma two_fixed [Fact (1 < r)] (c : ZMod r) (h : ∀ x, 2 * x ≠ c) :
    ∃ x y : ZMod r, x ≠ y ∧ 2 * x = c - 1 ∧ 2 * y = c - 1 := by
  have hr := (Fact.out : 1 < r)
  have hc : ((c.val : ℕ) : ZMod r) = c := ZMod.natCast_zmod_val c
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' c.val
  · exact absurd (by rw [← hc, hm]; push_cast; ring) (h m)
  · obtain ⟨t, ht | ht⟩ := Nat.even_or_odd' r
    · refine ⟨m, m + t, ?_, ?_, ?_⟩
      · intro he
        have h0 : ((t : ℕ) : ZMod r) = 0 := by simpa using congrArg (· - (m : ZMod r)) he.symm
        rw [ZMod.natCast_eq_zero_iff] at h0
        have := Nat.le_of_dvd (by omega) h0
        omega
      · rw [← hc, hm]; push_cast; ring
      · have hr0 : (2 : ZMod r) * t = 0 := by
          have := (congrArg (Nat.cast : ℕ → ZMod r) ht).symm.trans (ZMod.natCast_self r)
          rw [Nat.cast_mul, Nat.cast_ofNat] at this
          exact this
        rw [← hc, hm]
        push_cast
        linear_combination hr0
    · have hr0 : (2 : ZMod r) * t + 1 = 0 := by
        have := (congrArg (Nat.cast : ℕ → ZMod r) ht).symm.trans (ZMod.natCast_self r)
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at this
        exact this
      refine absurd ?_ (h (m + t + 1))
      rw [← hc, hm]
      push_cast
      linear_combination hr0

variable {p} (hloc : p.LocallyInjective)
include hloc

/-- Lemma 4.6: if the walk is primitive, a component off the diagonal misses
some second coordinate. -/
theorem exists_col_not_conn (hprim : Primitive p C) {a₀ : D.V × D.V} (hoff : a₀.1 ≠ a₀.2) :
    ∃ i, ∀ j, ¬ Conn p a₀ (j, i) := by
  by_contra H
  push Not at H
  obtain ⟨s, hs1, hs⟩ := exists_type C hloc a₀
  -- the points of the component, one for each second coordinate
  let σ : ZMod r → ZMod r := fun x ↦ C.pos a₀.1 + (s : ZMod r) * (x - C.pos a₀.2)
  let pt : ZMod r → D.V × D.V := fun x ↦ (C.pos.symm (σ x), C.pos.symm x)
  have hcls : ∀ a, Conn p a₀ a → a = pt (C.pos a.2) := by
    intro a ha
    have h1 := (line C hloc hs ha).1
    refine Prod.ext (C.pos.injective ?_) (by simp [pt])
    simp only [pt, σ, Equiv.apply_symm_apply]
    linear_combination h1
  have hpt : ∀ x, Conn p a₀ (pt x) := by
    intro x
    obtain ⟨j, hj⟩ := H (C.pos.symm x)
    have := hcls _ hj
    simp only [Equiv.apply_symm_apply] at this
    exact this ▸ hj
  have hoffpt : ∀ x, (pt x).1 ≠ (pt x).2 := fun x hd ↦
    hoff ((diag_iff_of_conn C hloc (hpt x)).2 hd)
  -- links between consecutive points
  let Link : ZMod r → Prop := fun x ↦ ∃ α, Inc p (pt x) α (C.eix.symm x)
  have hstep : ∀ x z, Adj p (pt x) z → (z = pt (x + 1) ∧ Link x) ∨ (z = pt (x - 1) ∧ Link (x - 1)) := by
    intro x z hz
    have hzc : Conn p a₀ z := ReflTransGen.tail (hpt x) hz
    obtain ⟨α, β, hi, rfl⟩ := hz
    have hz2 := pos_other C (inc_snd p hi)
    rcases eix_of_inc C (inc_snd p hi) with he | he
    · have hβ : β = C.eix.symm x := by
        rw [← C.eix.symm_apply_apply β, he]; simp [pt]
      have hsg : sgn C (pt x).2 β = 1 := by simp [sgn, he]
      left
      refine ⟨?_, α, hβ ▸ hi⟩
      rw [hcls _ hzc, hz2, hsg]
      simp [pt]
    · have hne : C.eix β ≠ C.pos (pt x).2 := by
        rw [he]; intro h'; exact one_ne_zero' (r := r) (by simp at h')
      have hsg : sgn C (pt x).2 β = -1 := by simp [sgn, hne]
      have hpz : C.pos (other (pt x).2 β) = x - 1 := by
        rw [hz2, hsg]; simp [pt]; ring
      right
      refine ⟨?_, α, ?_⟩
      · rw [hcls _ hzc, hpz]
      · have hβ : β = C.eix.symm (x - 1) := by
          rw [← C.eix.symm_apply_apply β, he]; simp [pt]
        have := inc_other_pair C hi
        rw [hcls _ hzc, hpz] at this
        exact hβ ▸ this
  -- at most one link is missing
  have hone : ∀ a b, ¬ Link a → ¬ Link b → a = b := by
    intro a b ha hb
    by_contra hab
    let S : ZMod r → Prop := fun x ↦ (x - a - 1).val ≤ (b - a - 1).val
    have hS : ∀ z, Conn p (pt b) z → S (C.pos z.2) := by
      intro z hz
      induction hz with
      | refl => simp [S, pt]
      | tail hyz hzw ih =>
        rename_i y w
        have hyc : Conn p a₀ y := conn_trans (hpt b) hyz
        have hy := hcls _ hyc
        rw [hy] at hzw
        set x := C.pos y.2
        have hSx : S x := ih
        rcases hstep x w hzw with ⟨rfl, hl⟩ | ⟨rfl, hl⟩
        · have hxb : x ≠ b := fun h ↦ hb (h ▸ hl)
          have hlt : (x - a - 1).val < (b - a - 1).val := by
            refine lt_of_le_of_ne hSx fun h ↦ hxb ?_
            have := ZMod.val_injective r h
            linear_combination this
          show ((C.pos (C.pos.symm (x + 1))) - a - 1).val ≤ _
          rw [Equiv.apply_symm_apply, show x + 1 - a - 1 = (x - a - 1) + 1 by ring,
            ZMod.val_add_of_lt (by rw [ZMod.val_one]; have := ZMod.val_lt (b - a - 1); omega),
            ZMod.val_one]
          omega
        · have hxa : x - 1 ≠ a := fun h ↦ ha (h ▸ hl)
          have hne : x - a - 1 ≠ 0 := fun h ↦ hxa (by linear_combination h)
          have hv : 1 ≤ (x - a - 1).val := by
            rw [Nat.one_le_iff_ne_zero]; exact (ZMod.val_ne_zero _).2 hne
          show ((C.pos (C.pos.symm (x - 1))) - a - 1).val ≤ _
          rw [Equiv.apply_symm_apply, show x - 1 - a - 1 = (x - a - 1) - 1 by ring,
            ZMod.val_sub (by rw [ZMod.val_one]; exact hv), ZMod.val_one]
          exact le_trans (Nat.sub_le _ _) hSx
    have := hS (pt a) (conn_trans (conn_symm C (hpt b)) (hpt a))
    simp only [S, pt, Equiv.apply_symm_apply, sub_self, zero_sub] at this
    rw [ZMod.neg_val, ite_eq_right (one_ne_zero' (r := r)), ZMod.val_one] at this
    have hlt := ZMod.val_lt (b - a - 1)
    have hv : (b - a - 1).val = (-1 : ZMod r).val := by
      rw [ZMod.neg_val, ite_eq_right (one_ne_zero' (r := r)), ZMod.val_one]; omega
    exact hab (by linear_combination -(ZMod.val_injective r hv))
  rcases hs1 with rfl | rfl
  · -- a rotation: present links preserve signed labels
    let τ := C.pos a₀.1 - C.pos a₀.2
    have hτ : τ ≠ 0 := fun h ↦ hoff (C.pos.injective (by linear_combination h))
    have hlink : ∀ x, Link x → signedLabel p C (x + τ) = signedLabel p C x := by
      rintro x ⟨α, hi⟩
      have hty := (line C hloc hs (hpt x)).2 α _ hi
      have hsb : sgn C (pt x).2 (C.eix.symm x) = 1 := by simp [sgn, pt]
      have hsa : sgn C (pt x).1 α = 1 := by
        have := hty; rw [type, hsb, mul_one] at this; exact_mod_cast this
      have hea : C.eix α = x + τ := by
        have : C.eix α = C.pos (pt x).1 := by
          by_contra h'; simp [sgn, h'] at hsa
        rw [this]; simp [pt, σ, τ]; ring
      have hα : α = C.eix.symm (x + τ) := by rw [← hea]; simp
      subst hα
      -- orientation: an arrow at its own position leaves the vertex iff it is forward
      have hfw : ∀ (v : D.V) (e : D.A), C.eix e = C.pos v → (D.src e = v ∨ D.tgt e = v) →
          (D.src e = v ↔ C.fwd e = true) := by
        intro v e he hv
        constructor
        · intro hs'
          have := C.pos_src e
          rw [hs', he] at this
          by_contra hf
          simp only [Bool.not_eq_true] at hf
          rw [hf] at this
          exact one_ne_zero' (r := r) (by simp at this)
        · intro hf
          apply C.pos.injective
          rw [C.pos_src, hf, he]; rfl
      have h1 := hfw _ _ (by simp [pt, σ, τ]; ring) (inc_fst p hi)
      have h2 := hfw _ _ (by simp [pt]) (inc_snd p hi)
      have hfeq : C.fwd (C.eix.symm (x + τ)) = C.fwd (C.eix.symm x) := by
        rcases hi.2 with ⟨hs₁, hs₂⟩ | ⟨ht₁, ht₂⟩
        · rw [h1.1 hs₁, h2.1 hs₂]
        · have n1 : D.src (C.eix.symm (x + τ)) ≠ (pt x).1 := ht₁ ▸ src_ne_tgt C _
          have n2 : D.src (C.eix.symm x) ≠ (pt x).2 := ht₂ ▸ src_ne_tgt C _
          rw [Bool.eq_false_iff.2 (fun h ↦ n1 (h1.2 h)), Bool.eq_false_iff.2 (fun h ↦ n2 (h2.2 h))]
      exact Prod.ext hi.1 hfeq
    obtain ⟨x, hx⟩ := hprim τ hτ
    apply hx
    by_cases hall : ∀ y, Link y
    · exact hlink x (hall x)
    · push Not at hall
      obtain ⟨y₀, hy₀⟩ := hall
      have hrest : ∀ y, y ≠ y₀ → signedLabel p C (y + τ) = signedLabel p C y := fun y hy ↦
        hlink y (by by_contra h'; exact hy (hone y y₀ h' hy₀))
      by_cases hxy : x = y₀
      · subst hxy; exact rot_of_all_but_one _ τ x hrest
      · exact hrest x hxy
  · -- a reflection: it fixes no vertex, so it fixes two arrows, whose links are missing
    let c := C.pos a₀.1 + C.pos a₀.2
    have hc : c = C.pos a₀.1 + C.pos a₀.2 := rfl
    have hnofix : ∀ x, 2 * x ≠ c := by
      intro x hx
      apply hoffpt x
      simp only [pt, σ]
      congr 1
      push_cast
      linear_combination -hx + hc
    have hmiss : ∀ x, 2 * x = c - 1 → ¬ Link x := by
      rintro x hx ⟨α, hi⟩
      have hty := (line C hloc hs (hpt x)).2 α _ hi
      have hsb : sgn C (pt x).2 (C.eix.symm x) = 1 := by simp [sgn, pt]
      have hsa : sgn C (pt x).1 α = -1 := by
        have := hty; rw [type, hsb, mul_one] at this; exact_mod_cast this
      have hne : C.eix α ≠ C.pos (pt x).1 := by
        intro h'; simp [sgn, h'] at hsa
      have hea : C.eix α = x := by
        rcases eix_of_inc C (inc_fst p hi) with h' | h'
        · exact absurd h' hne
        · rw [h']; simp only [pt, σ, Equiv.apply_symm_apply]; push_cast
          linear_combination -hx + hc
      have hα : α = C.eix.symm x := by rw [← hea]; simp
      subst hα
      apply hoffpt x
      rcases hi.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h1.symm.trans h2
      · exact h1.symm.trans h2
    obtain ⟨x, y, hxy, hx, hy⟩ := two_fixed c hnofix
    exact hxy (hone x y (hmiss x hx) (hmiss y hy))

end Primitive

end FinQuiver

end LargeIndecomposable
