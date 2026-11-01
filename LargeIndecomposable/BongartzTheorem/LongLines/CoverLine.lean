module

public import LargeIndecomposable.Coverings.UniversalCover.PieceKills
public import Mathlib.Combinatorics.Pigeonhole
public import LargeIndecomposable.FundamentalGroups.Basic.CocycleExtendMax

/-!
# Lines in the universal cover

A line of the cover (BO13b, §1: a full convex subcategory given by a quiver of type `A` without
relations) is recorded by its points `pt 0, …, pt n` and the orientations `fwd i` of the arrows
joining `pt i` and `pt (i + 1)` (`CLine`). Directed runs of a line are bounded by the number of
morphisms of `P` (`run_le_fwd`, `run_le_bwd`), so a long line has many sinks (`exists_sinks`).
Two sinks with the same image in `P` whose outer incoming arrows have different labels form a
*good pair* (`GoodPair`; BO23, proof of Theorem 7); a long enough line contains one
(`exists_goodPair`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] {x₀ : P}

variable (x₀) in
/-- **A line of the universal cover**: a full convex subcategory given by a quiver of type `A`
without relations. The points are `pt 0, …, pt n`, and the `i`-th arrow joins `pt i` and
`pt (i + 1)`, pointing to `pt (i + 1)` iff `fwd i`. -/
structure CLine where
  /-- The number of arrows. -/
  n : ℕ
  /-- The points. -/
  pt : ℕ → Cover x₀
  /-- The orientations. -/
  fwd : ℕ → Bool
  inj : ∀ a b, a ≤ n → b ≤ n → pt a = pt b → a = b
  arrF : ∀ i < n, fwd i = true → ∃ f : pt i ⟶ pt (i + 1), IsIrreducible f
  arrB : ∀ i < n, fwd i = false → ∃ f : pt (i + 1) ⟶ pt i, IsIrreducible f
  uniqF : ∀ i < n, ∀ f g : pt i ⟶ pt (i + 1), IsIrreducible f → IsIrreducible g → f = g
  uniqB : ∀ i < n, ∀ f g : pt (i + 1) ⟶ pt i, IsIrreducible f → IsIrreducible g → f = g
  /-- The only arrows between points of the line are the line arrows. -/
  only : ∀ a b, a ≤ n → b ≤ n → ∀ f : pt a ⟶ pt b, IsIrreducible f →
    (b = a + 1 ∧ fwd a = true) ∨ (a = b + 1 ∧ fwd b = false)
  convex : Convex {c | ∃ a ≤ n, pt a = c}
  /-- No relations: every path inside the line has nonzero value. -/
  nz : ∀ {X Y : RayVert (Cover x₀)} (p : Quiver.Path X Y), PathIn {c | ∃ a ≤ n, pt a = c} p →
    pathVal p ≠ 0

namespace CLine

variable (L : CLine x₀)

/-- The set of points of the line. -/
def pts : Set (Cover x₀) := {c | ∃ a ≤ L.n, L.pt a = c}

/-- The forward path from `pt a` to `pt (a + k)`. -/
def pathF (a : ℕ) : ∀ k, (∀ i, a ≤ i → i < a + k → i < L.n ∧ L.fwd i = true) →
    Quiver.Path (RayVert.mk (L.pt a)) (RayVert.mk (L.pt (a + k)))
  | 0, _ => .nil
  | k + 1, h => (pathF a k fun i h1 h2 ↦ h i h1 (by omega)).cons
      ⟨(L.arrF (a + k) (h (a + k) (by omega) (by omega)).1
        (h (a + k) (by omega) (by omega)).2).choose,
       (L.arrF (a + k) (h (a + k) (by omega) (by omega)).1
        (h (a + k) (by omega) (by omega)).2).choose_spec⟩

lemma pathIn_pathF (a : ℕ) : ∀ k (h : ∀ i, a ≤ i → i < a + k → i < L.n ∧ L.fwd i = true),
    a + k ≤ L.n → PathIn L.pts (L.pathF a k h)
  | 0, _, hk => ⟨a, hk, rfl⟩
  | k + 1, h, hk => ⟨pathIn_pathF a k _ (by omega), a + k + 1, hk, rfl⟩

/-- The backward path from `pt (a + k)` to `pt a`. -/
def pathB (a : ℕ) : ∀ k, (∀ i, a ≤ i → i < a + k → i < L.n ∧ L.fwd i = false) →
    Quiver.Path (RayVert.mk (L.pt (a + k))) (RayVert.mk (L.pt a))
  | 0, _ => .nil
  | k + 1, h => (Quiver.Path.nil.cons
      (⟨(L.arrB (a + k) (h (a + k) (by omega) (by omega)).1
        (h (a + k) (by omega) (by omega)).2).choose,
       (L.arrB (a + k) (h (a + k) (by omega) (by omega)).1
        (h (a + k) (by omega) (by omega)).2).choose_spec⟩ :
          RayVert.mk (L.pt (a + k + 1)) ⟶ RayVert.mk (L.pt (a + k)))).comp
      (pathB a k fun i h1 h2 ↦ h i h1 (by omega))

lemma pathIn_pathB (a : ℕ) : ∀ k (h : ∀ i, a ≤ i → i < a + k → i < L.n ∧ L.fwd i = false),
    a + k ≤ L.n → PathIn L.pts (L.pathB a k h)
  | 0, _, hk => ⟨a, by omega, rfl⟩
  | k + 1, h, hk => by
    rw [pathB, pathIn_comp_iff]
    exact ⟨⟨⟨a + k + 1, hk, rfl⟩, a + k, by omega, rfl⟩, pathIn_pathB a k _ (by omega)⟩

lemma nzF (a b : ℕ) (hab : a ≤ b) (hb : b ≤ L.n) (h : ∀ i, a ≤ i → i < b → L.fwd i = true) :
    ∃ f : L.pt a ⟶ L.pt b, f ≠ 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, b = a + k := ⟨b - a, by omega⟩
  have h' : ∀ i, a ≤ i → i < a + k → i < L.n ∧ L.fwd i = true := fun i h1 h2 ↦
    ⟨by omega, h i h1 h2⟩
  exact ⟨pathVal (L.pathF a k h'), L.nz _ (L.pathIn_pathF a k h' hb)⟩

lemma nzB (a b : ℕ) (hab : a ≤ b) (hb : b ≤ L.n) (h : ∀ i, a ≤ i → i < b → L.fwd i = false) :
    ∃ f : L.pt b ⟶ L.pt a, f ≠ 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, b = a + k := ⟨b - a, by omega⟩
  have h' : ∀ i, a ≤ i → i < a + k → i < L.n ∧ L.fwd i = false := fun i h1 h2 ↦
    ⟨by omega, h i h1 h2⟩
  exact ⟨pathVal (L.pathB a k h'), L.nz _ (L.pathIn_pathB a k h' hb)⟩

lemma tgt_eq_of_val {a b b' : Cover x₀} {f : a ⟶ b} {f' : a ⟶ b'} (hf : f ≠ 0) (hf' : f' ≠ 0)
    (hy : b.y = b'.y) (hv : HEq (val f) (val f')) : b = b' := by
  rcases f with _ | f
  · exact absurd rfl hf
  rcases f' with _ | f'
  · exact absurd rfl hf'
  exact target_eq f f' hy hv

lemma src_eq_of_val {a a' b : Cover x₀} {f : a ⟶ b} {f' : a' ⟶ b} (hf : f ≠ 0) (hf' : f' ≠ 0)
    (hy : a.y = a'.y) (hv : HEq (val f) (val f')) : a = a' := by
  rcases f with _ | f
  · exact absurd rfl hf
  rcases f' with _ | f'
  · exact absurd rfl hf'
  exact source_eq f f' hy hv

section Count

variable [Finite P] [∀ x y : P, Finite (x ⟶ y)]

/-- A bound for the number of morphisms of `P`. -/
abbrev bound (P : Type) [Category.{0} P] : ℕ := Nat.card (Σ x y : P, (x ⟶ y))

include L in
/-- **Forward runs are short.** -/
lemma run_le_fwd {a b : ℕ} (hab : a ≤ b) (hb : b ≤ L.n)
    (h : ∀ i, a ≤ i → i < b → L.fwd i = true) : b - a < bound P := by
  have hf : ∀ j : Fin (b - a + 1), ∃ f : L.pt a ⟶ L.pt (a + j), f ≠ 0 := fun j ↦
    L.nzF a (a + j) (by omega) (by omega) fun i hi hi' ↦ h i hi (by omega)
  let F : Fin (b - a + 1) → Σ y : P, ((L.pt a).y ⟶ y) := fun j ↦
    ⟨(L.pt (a + j)).y, val (hf j).choose⟩
  have hF : Function.Injective F := by
    intro j j' hjj
    obtain ⟨hy, hv⟩ := Sigma.mk.inj hjj
    have := tgt_eq_of_val (hf j).choose_spec (hf j').choose_spec hy hv
    have := L.inj _ _ (by omega) (by omega) this
    exact Fin.ext (by omega)
  have h1 := Nat.card_le_card_of_injective F hF
  have h2 := Nat.card_le_card_of_injective
    (fun s : Σ y : P, ((L.pt a).y ⟶ y) ↦ (⟨(L.pt a).y, s.1, s.2⟩ : Σ x y : P, (x ⟶ y)))
    fun s s' h ↦ by
      obtain ⟨-, h⟩ := Sigma.mk.inj h
      exact eq_of_heq h
  rw [Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at h1
  show b - a < Nat.card _
  omega

include L in
/-- **Backward runs are short.** -/
lemma run_le_bwd {a b : ℕ} (hab : a ≤ b) (hb : b ≤ L.n)
    (h : ∀ i, a ≤ i → i < b → L.fwd i = false) : b - a < bound P := by
  have hf : ∀ j : Fin (b - a + 1), ∃ f : L.pt (a + j) ⟶ L.pt a, f ≠ 0 := fun j ↦
    L.nzB a (a + j) (by omega) (by omega) fun i hi hi' ↦ h i hi (by omega)
  let F : Fin (b - a + 1) → Σ x : P, (x ⟶ (L.pt a).y) := fun j ↦
    ⟨(L.pt (a + j)).y, val (hf j).choose⟩
  have hF : Function.Injective F := by
    intro j j' hjj
    obtain ⟨hy, hv⟩ := Sigma.mk.inj hjj
    have := src_eq_of_val (hf j).choose_spec (hf j').choose_spec hy hv
    have := L.inj _ _ (by omega) (by omega) this
    exact Fin.ext (by omega)
  have h1 := Nat.card_le_card_of_injective F hF
  have h2 := Nat.card_le_card_of_injective
    (fun s : Σ x : P, (x ⟶ (L.pt a).y) ↦ (⟨s.1, (L.pt a).y, s.2⟩ : Σ x y : P, (x ⟶ y)))
    fun s s' h ↦ by
      obtain ⟨h1, h2⟩ := Sigma.mk.inj h
      obtain ⟨x, f⟩ := s
      obtain ⟨x', f'⟩ := s'
      change x = x' at h1
      subst h1
      obtain ⟨-, h3⟩ := Sigma.mk.inj (eq_of_heq h2)
      have h4 : f = f' := eq_of_heq h3
      rw [h4]
  rw [Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at h1
  show b - a < Nat.card _
  omega

end Count

/-- A sink of the line at `t + 1`: arrows `pt t → pt (t + 1) ← pt (t + 2)`. -/
def IsSinkAt (t : ℕ) : Prop := t + 1 < L.n ∧ L.fwd t = true ∧ L.fwd (t + 1) = false

section Count

variable [Finite P] [∀ x y : P, Finite (x ⟶ y)]

/-- **A sink in every window of length `2 bound`.** -/
lemma exists_sink (a : ℕ) (ha : a + 2 * bound P ≤ L.n) :
    ∃ t, a ≤ t ∧ t < a + 2 * bound P ∧ L.IsSinkAt t := by
  set K := bound P
  have hi : ∃ i, a ≤ i ∧ i < a + K ∧ L.fwd i = true := by
    by_contra hno
    push_neg at hno
    have := L.run_le_bwd (a := a) (b := a + K) (by omega) (by omega) fun i h1 h2 ↦ by
      have := hno i h1 h2; simpa using this
    omega
  obtain ⟨i, hai, hiK, hfi⟩ := hi
  have hj : ∃ j, i < j ∧ L.fwd j = false := by
    by_contra hno
    push_neg at hno
    have := L.run_le_fwd (a := i) (b := i + K) (by omega) (by omega) fun j h1 h2 ↦ by
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · exact hfi
      · have := hno j h1; simpa using this
    omega
  classical
  let j := Nat.find hj
  have hjs : i < j ∧ L.fwd j = false := Nat.find_spec hj
  have hjm : ∀ m, i < m → m < j → L.fwd m = true := fun m h1 h2 ↦ by
    have := Nat.find_min hj h2
    push_neg at this
    simpa using this h1
  have hjK : j ≤ i + K := by
    by_contra hlt
    push_neg at hlt
    have := L.run_le_fwd (a := i) (b := i + K) (by omega) (by omega) fun m h1 h2 ↦ by
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · exact hfi
      · exact hjm m h1 (by omega)
    omega
  refine ⟨j - 1, by omega, by omega, by omega, ?_, ?_⟩
  · rcases Nat.eq_or_lt_of_le (show i ≤ j - 1 by omega) with h | h
    · rw [← h]; exact hfi
    · exact hjm _ h (by omega)
  · rw [show j - 1 + 1 = j by omega]; exact hjs.2

/-- **Many sinks**: `m + 1` sinks in increasing order. -/
lemma exists_sinks (m : ℕ) (hm : (m + 1) * (2 * bound P) ≤ L.n) :
    ∃ s : ℕ → ℕ, (∀ j ≤ m, L.IsSinkAt (s j) ∧ s j < (j + 1) * (2 * bound P)) ∧
      ∀ j < m, s j < s (j + 1) := by
  induction m with
  | zero =>
    obtain ⟨t, -, ht, hs⟩ := L.exists_sink 0 (by simpa using hm)
    exact ⟨fun _ ↦ t, fun j hj ↦ by
      obtain rfl : j = 0 := by omega
      exact ⟨hs, by simpa using ht⟩, fun j hj ↦ absurd hj (by omega)⟩
  | succ m ih =>
    obtain ⟨s, hs, hmono⟩ := ih (le_trans (Nat.mul_le_mul_right _ (by omega)) hm)
    obtain ⟨t, ht1, ht2, ht⟩ := L.exists_sink (s m + 1) (by
      have := (hs m le_rfl).2
      have : (m + 1 + 1) * (2 * bound P) = (m + 1) * (2 * bound P) + 2 * bound P := by ring
      omega)
    refine ⟨fun j ↦ if j ≤ m then s j else t, fun j hj ↦ ?_, fun j hj ↦ ?_⟩
    · by_cases hjm : j ≤ m
      · simp only [hjm, ↓reduceIte]; exact hs j hjm
      · obtain rfl : j = m + 1 := by omega
        simp only [show ¬m + 1 ≤ m by omega, ↓reduceIte]
        refine ⟨ht, ?_⟩
        have := (hs m le_rfl).2
        have : (m + 1 + 1) * (2 * bound P) = (m + 1) * (2 * bound P) + 2 * bound P := by ring
        omega
    · by_cases hjm : j + 1 ≤ m
      · simp only [show j ≤ m by omega, hjm, ↓reduceIte]; exact hmono j (by omega)
      · obtain rfl : m = j := by omega
        simp only [le_refl, ↓reduceIte, show ¬m + 1 ≤ m by omega]
        omega

end Count

lemma sigma_heq_snd {X X' : P} (hX : X = X') {s : Σ y : P, (X ⟶ y)} {s' : Σ y : P, (X' ⟶ y)}
    (h : HEq s s') : HEq s.2 s'.2 := by
  subst hX
  obtain rfl := eq_of_heq h
  rfl

/-- The label of the arrow `pt t → pt (t + 1)`. -/
def labL (t : ℕ) : Σ x y : P, (x ⟶ y) :=
  if h : t < L.n ∧ L.fwd t = true then
    ⟨(L.pt t).y, (L.pt (t + 1)).y, val (L.arrF t h.1 h.2).choose⟩
  else ⟨x₀, x₀, 0⟩

/-- The label of the arrow `pt (t + 2) → pt (t + 1)`. -/
def labR (t : ℕ) : Σ x y : P, (x ⟶ y) :=
  if h : t + 1 < L.n ∧ L.fwd (t + 1) = false then
    ⟨(L.pt (t + 1 + 1)).y, (L.pt (t + 1)).y, val (L.arrB (t + 1) h.1 h.2).choose⟩
  else ⟨x₀, x₀, 0⟩

/-- The two arrows into a sink have different labels. -/
lemma labL_ne_labR {t : ℕ} (ht : L.IsSinkAt t) : L.labL t ≠ L.labR t := by
  unfold labL labR
  rw [dif_pos ⟨by have := ht.1; omega, ht.2.1⟩, dif_pos ⟨ht.1, ht.2.2⟩]
  intro h
  obtain ⟨hx, h2⟩ := Sigma.mk.inj h
  have hv := sigma_heq_snd hx h2
  have := src_eq_of_val (L.arrF t (by have := ht.1; omega) ht.2.1).choose_spec.1
    (L.arrB (t + 1) ht.1 ht.2.2).choose_spec.1 hx hv
  have := L.inj _ _ (by have := ht.1; omega) (by have := ht.1; omega) this
  omega

/-- **A good pair of sinks** (BO23, proof of Theorem 7): two sinks at `t + 1 < t' + 1` with the
same image in `P` whose outer incoming arrows have different labels. -/
def GoodPair (t t' : ℕ) : Prop :=
  L.IsSinkAt t ∧ L.IsSinkAt t' ∧ t < t' ∧ (L.pt (t + 1)).y = (L.pt (t' + 1)).y ∧
    L.labR t ≠ L.labL t'

lemma goodPair_of_three {t₁ t₂ t₃ : ℕ} (h₁ : L.IsSinkAt t₁) (h₂ : L.IsSinkAt t₂)
    (h₃ : L.IsSinkAt t₃) (h12 : t₁ < t₂) (h23 : t₂ < t₃) (hy₁ : (L.pt (t₁ + 1)).y = (L.pt (t₂ + 1)).y)
    (hy₂ : (L.pt (t₂ + 1)).y = (L.pt (t₃ + 1)).y) :
    ∃ t t', L.GoodPair t t' := by
  by_cases ha : L.labR t₁ = L.labL t₂
  · by_cases hb : L.labR t₂ = L.labL t₃
    · refine ⟨t₁, t₃, h₁, h₃, h12.trans h23, hy₁.trans hy₂, ?_⟩
      rw [ha, ← hb]
      exact L.labL_ne_labR h₂
    · exact ⟨t₂, t₃, h₂, h₃, h23, hy₂, hb⟩
  · exact ⟨t₁, t₂, h₁, h₂, h12, hy₁, ha⟩

section Count

variable [Fintype P] [∀ x y : P, Finite (x ⟶ y)]

/-- **A long line contains a good pair.** -/
theorem exists_goodPair (hn : (2 * Fintype.card P + 1) * (2 * bound P) ≤ L.n) :
    ∃ t t', L.GoodPair t t' := by
  classical
  obtain ⟨s, hs, hmono⟩ := L.exists_sinks (2 * Fintype.card P) hn
  have hsm' : ∀ i j, i < j → j ≤ 2 * Fintype.card P → s i < s j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
      · exact (ih h (by omega)).trans (hmono j (by omega))
      · exact hmono i (by omega)
  have hsm : StrictMonoOn s (Set.Iic (2 * Fintype.card P)) := fun i _ j hj hij ↦
    hsm' i j hij hj
  have hcard : (Finset.univ : Finset P).card * 2 < (Finset.range (2 * Fintype.card P + 1)).card := by
    simp only [Finset.card_univ, Finset.card_range]; omega
  obtain ⟨y, -, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (f := fun j ↦ (L.pt (s j + 1)).y) (fun _ _ ↦ Finset.mem_univ _) hcard
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 hy
  simp only [Finset.mem_filter, Finset.mem_range] at ha hb hc
  have key : ∀ i j l, i ∈ Finset.range (2 * Fintype.card P + 1) →
      j ∈ Finset.range (2 * Fintype.card P + 1) → l ∈ Finset.range (2 * Fintype.card P + 1) →
      i < j → j < l → (L.pt (s i + 1)).y = y → (L.pt (s j + 1)).y = y → (L.pt (s l + 1)).y = y →
      ∃ t t', L.GoodPair t t' := by
    intro i j l hi hj hl hij hjl hyi hyj hyl
    simp only [Finset.mem_range] at hi hj hl
    exact L.goodPair_of_three (hs i (by omega)).1 (hs j (by omega)).1 (hs l (by omega)).1
      (hsm (by simp; omega) (by simp; omega) hij) (hsm (by simp; omega) (by simp; omega) hjl)
      (hyi.trans hyj.symm) (hyj.trans hyl.symm)
  have hr : ∀ i, i < 2 * Fintype.card P + 1 → i ∈ Finset.range (2 * Fintype.card P + 1) :=
    fun i hi ↦ Finset.mem_range.2 hi
  rcases lt_trichotomy a b with h1 | h1 | h1 <;> rcases lt_trichotomy b c with h2 | h2 | h2 <;>
    rcases lt_trichotomy a c with h3 | h3 | h3 <;> first
    | exact absurd h1 hab | exact absurd h2 hbc | exact absurd h3 hac
    | exact key a b c (hr a ha.1) (hr b hb.1) (hr c hc.1) h1 h2 ha.2 hb.2 hc.2
    | exact key a c b (hr a ha.1) (hr c hc.1) (hr b hb.1) h3 h2 ha.2 hc.2 hb.2
    | exact key b a c (hr b hb.1) (hr a ha.1) (hr c hc.1) h1 h3 hb.2 ha.2 hc.2
    | exact key b c a (hr b hb.1) (hr c hc.1) (hr a ha.1) h2 h3 hb.2 hc.2 ha.2
    | exact key c a b (hr c hc.1) (hr a ha.1) (hr b hb.1) h3 h1 hc.2 ha.2 hb.2
    | exact key c b a (hr c hc.1) (hr b hb.1) (hr a ha.1) h2 h1 hc.2 hb.2 ha.2
    | omega

end Count

/-- **A good pair of minimal length.** -/
lemma exists_minimal_goodPair (h : ∃ t t', L.GoodPair t t') :
    ∃ t t', L.GoodPair t t' ∧ ∀ u u', L.GoodPair u u' → t' - t ≤ u' - u := by
  classical
  have hd : ∃ d, ∃ t t', L.GoodPair t t' ∧ t' - t = d := by
    obtain ⟨t, t', h⟩ := h
    exact ⟨_, t, t', h, rfl⟩
  obtain ⟨t, t', hg, hd'⟩ := Nat.find_spec hd
  refine ⟨t, t', hg, fun u u' hu ↦ ?_⟩
  rw [hd']
  exact Nat.find_min' hd ⟨u, u', hu, rfl⟩

end CLine

end LargeIndecomposable.RayCat
