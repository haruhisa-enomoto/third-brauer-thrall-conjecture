module

public import LargeIndecomposable.UnitForms.Graph

/-!
# The critical diagrams of type `D̃` (von Höhne 1988, Theorem 2.1)

The critical diagrams of type `D̃_n` (von Höhne, Fig. 3) form one family. Its points are an
induced path `p 0, …, p (M - 1)` of full edges and two more points `s`, `t`, with attachment
positions `i < j < M`:

* `s` is joined to `p (i + 1)`; if `i ≥ 1` also to `p 0`, and by a broken edge to `p i`;
* `t` is joined to `p (j - 1)`; if `j + 2 ≤ M` also to `p (M - 1)`, and by a broken edge to
  `p j`;
* `s` and `t` are joined if `j = i + 1`;
* the radical vector is `2` on `p k` for `i < k < j` and `1` elsewhere.

`i = 0` is a fork end (`s` and `p 0` are two leaves at `p 1`), `i ≥ 1` a cycle end
`s, p 0, …, p i` closed by a broken edge. We record the coefficients on the model points
`Pt` (`sc`, `sy`) and show that the family is closed under deflation (`sc_deflA`, `sc_deflB`,
and the reflection `sc_refl`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.Forms

namespace DTilde

/-- The model points: `s`, `t` and the path points `p k`. -/
inductive Pt
  | s
  | t
  | p (k : ℕ)
  deriving DecidableEq

open Pt

/-- The valid model points for a path of `M` points. -/
def Valid (M : ℕ) : Pt → Prop
  | s => True
  | t => True
  | p k => k < M

/-- The coefficients of `s` with the path. -/
def sAdj (i k : ℕ) : ℤ :=
  if k = i + 1 then -1 else if 1 ≤ i ∧ k = 0 then -1 else if 1 ≤ i ∧ k = i then 1 else 0

/-- The coefficients of `t` with the path. -/
def tAdj (M j k : ℕ) : ℤ :=
  if k + 1 = j then -1 else if j + 2 ≤ M ∧ k + 1 = M then -1
  else if j + 2 ≤ M ∧ k = j then 1 else 0

/-- The off-diagonal coefficients of the model. -/
def sc (M i j : ℕ) : Pt → Pt → ℤ
  | p k, p l => if k + 1 = l ∨ l + 1 = k then -1 else 0
  | s, p k => sAdj i k
  | p k, s => sAdj i k
  | t, p k => tAdj M j k
  | p k, t => tAdj M j k
  | s, t => if j = i + 1 then -1 else 0
  | t, s => if j = i + 1 then -1 else 0
  | s, s => 2
  | t, t => 2

/-- The radical vector of the model. -/
def sy (i j : ℕ) : Pt → ℤ
  | p k => if i < k ∧ k < j then 2 else 1
  | _ => 1

/-- The deflation of the model at `(A, B)`, written on the old points. -/
def defl (c : Pt → Pt → ℤ) (A B : Pt) (x y : Pt) : ℤ :=
  if x = B ∧ y = A ∨ x = A ∧ y = B then c A B + 2
  else if x = B then c B y + c A y
  else if y = B then c x B + c x A
  else c x y

/-- Relabelling for the deflation at `(p (i + 1), p i)`: the new path is
`s, p 0, …, p i, p (i + 2), …`, and `p (i + 1)` becomes the new `s`. -/
def relA (i : ℕ) : Pt → Pt
  | s => p 0
  | t => t
  | p k => if k ≤ i then p (k + 1) else if k = i + 1 then s else p k

/-- Relabelling for the deflation at `(p (i + 1), s)`: the new path is
`p i, …, p 0, s, p (i + 2), …`, and `p (i + 1)` becomes the new `s`. -/
def relB (i : ℕ) : Pt → Pt
  | s => p (i + 1)
  | t => t
  | p k => if k ≤ i then p (i - k) else if k = i + 1 then s else p k

lemma relA_s (i : ℕ) : relA i s = p 0 := rfl
lemma relA_t (i : ℕ) : relA i t = t := rfl
lemma relA_le {i k : ℕ} (h : k ≤ i) : relA i (p k) = p (k + 1) := by simp [relA, h]
lemma relA_mid (i : ℕ) : relA i (p (i + 1)) = s := by simp [relA]
lemma relA_gt {i k : ℕ} (h : i + 2 ≤ k) : relA i (p k) = p k := by
  simp only [relA]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The five kinds of model points relative to `i`. -/
lemma cases5 {M : ℕ} (i : ℕ) (x : Pt) (hx : Valid M x) :
    x = s ∨ x = t ∨ (∃ k, k ≤ i ∧ k < M ∧ x = p k) ∨ x = p (i + 1) ∨
      ∃ k, i + 2 ≤ k ∧ k < M ∧ x = p k := by
  rcases x with _ | _ | k
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · simp only [Valid] at hx
    rcases Nat.lt_or_ge i k with h | h
    · rcases Nat.lt_or_ge (i + 1) k with h' | h'
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨k, by omega, hx, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [show k = i + 1 by omega]))))
    · exact Or.inr (Or.inr (Or.inl ⟨k, h, hx, rfl⟩))

/-- Finish a model identity: unfold, decide the conditions that `omega` can decide, split
the rest. -/
macro "model_tac" : tactic => `(tactic| (
  simp only [defl, sc, sy, sAdj, tAdj, reduceCtorEq, false_and, and_false, or_false, false_or,
    Pt.p.injEq, ne_eq, not_true_eq_false] at *
  all_goals
    try simp (disch := omega) only [ite_eq_left, ite_eq_right, and_true, true_and, ite_true,
      ite_false, Nat.add_right_cancel_iff, or_true, true_or]
  all_goals first | omega | (split_ifs <;> omega)))

lemma sc_deflA {M i j : ℕ} (hij : i + 2 ≤ j) (hjM : j < M) (x y : Pt) (hx : Valid M x)
    (hy : Valid M y) (hxy : x ≠ y) :
    sc M (i + 1) j (relA i x) (relA i y) = defl (sc M i j) (p (i + 1)) (p i) x y := by
  rcases cases5 i x hx with rfl | rfl | ⟨k, hk, hkM, rfl⟩ | rfl | ⟨k, hk, hkM, rfl⟩ <;>
  rcases cases5 i y hy with rfl | rfl | ⟨l, hl, hlM, rfl⟩ | rfl | ⟨l, hl, hlM, rfl⟩ <;>
  simp (disch := omega) only [relA_s, relA_t, relA_le, relA_mid, relA_gt] <;>
  model_tac

lemma sy_deflA {i j : ℕ} (hij : i + 2 ≤ j) (x : Pt) :
    sy (i + 1) j (relA i x) =
      if x = p (i + 1) then sy i j (p (i + 1)) - sy i j (p i) else sy i j x := by
  rcases x with _ | _ | k
  · simp [relA, sy]
  · simp [relA, sy]
  · rcases Nat.lt_or_ge i k with h | h
    · rcases Nat.lt_or_ge (i + 1) k with h' | h'
      · rw [relA_gt (by omega)]; model_tac
      · obtain rfl : k = i + 1 := by omega
        rw [relA_mid]; model_tac
    · rw [relA_le h]; model_tac

lemma relB_s (i : ℕ) : relB i s = p (i + 1) := rfl
lemma relB_t (i : ℕ) : relB i t = t := rfl
lemma relB_le {i k : ℕ} (h : k ≤ i) : relB i (p k) = p (i - k) := by simp [relB, h]
lemma relB_mid (i : ℕ) : relB i (p (i + 1)) = s := by simp [relB]
lemma relB_gt {i k : ℕ} (h : i + 2 ≤ k) : relB i (p k) = p k := by
  simp only [relB]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

lemma sc_deflB {M i j : ℕ} (hij : i + 2 ≤ j) (hjM : j < M) (x y : Pt) (hx : Valid M x)
    (hy : Valid M y) (hxy : x ≠ y) :
    sc M (i + 1) j (relB i x) (relB i y) = defl (sc M i j) (p (i + 1)) s x y := by
  rcases cases5 i x hx with rfl | rfl | ⟨k, hk, hkM, rfl⟩ | rfl | ⟨k, hk, hkM, rfl⟩ <;>
  rcases cases5 i y hy with rfl | rfl | ⟨l, hl, hlM, rfl⟩ | rfl | ⟨l, hl, hlM, rfl⟩ <;>
  simp (disch := omega) only [relB_s, relB_t, relB_le, relB_mid, relB_gt] <;>
  model_tac

lemma sy_deflB {i j : ℕ} (hij : i + 2 ≤ j) (x : Pt) :
    sy (i + 1) j (relB i x) =
      if x = p (i + 1) then sy i j (p (i + 1)) - sy i j s else sy i j x := by
  rcases x with _ | _ | k
  · simp [relB, sy]
  · simp [relB, sy]
  · rcases Nat.lt_or_ge i k with h | h
    · rcases Nat.lt_or_ge (i + 1) k with h' | h'
      · rw [relB_gt (by omega)]; model_tac
      · obtain rfl : k = i + 1 := by omega
        rw [relB_mid]; model_tac
    · rw [relB_le h]; model_tac

/-- The reflection of the model: `s ↔ t` and `p k ↔ p (M - 1 - k)`. -/
def reflPt (M : ℕ) : Pt → Pt
  | s => t
  | t => s
  | p k => p (M - 1 - k)

lemma sc_refl {M i j : ℕ} (hij : i < j) (hjM : j < M) (x y : Pt) (hx : Valid M x)
    (hy : Valid M y) (hxy : x ≠ y) :
    sc M (M - 1 - j) (M - 1 - i) (reflPt M x) (reflPt M y) = sc M i j x y := by
  rcases x with _ | _ | k <;> rcases y with _ | _ | l <;>
    simp only [Valid] at hx hy <;> simp only [reflPt] <;> model_tac

lemma sy_refl {M i j : ℕ} (hij : i < j) (hjM : j < M) (x : Pt) (hx : Valid M x) :
    sy (M - 1 - j) (M - 1 - i) (reflPt M x) = sy i j x := by
  rcases x with _ | _ | k <;> simp only [Valid] at hx <;> simp only [reflPt] <;> model_tac

lemma one_le_sy (i j : ℕ) (x : Pt) : 1 ≤ sy i j x := by
  rcases x with _ | _ | k <;> simp only [sy] <;> try split_ifs
  all_goals norm_num

lemma sy_p_of_not {i j k : ℕ} (h : ¬(i < k ∧ k < j)) : sy i j (p k) = 1 := by
  simp only [sy, if_neg h]

lemma valid_relA {M i j : ℕ} (hij : i + 2 ≤ j) (hjM : j < M) {x : Pt} (hx : Valid M x) :
    Valid M (relA i x) := by
  rcases x with _ | _ | k
  · simp only [relA, Valid]; omega
  · trivial
  · simp only [Valid] at hx
    simp only [relA]
    split_ifs <;> simp only [Valid] <;> omega

lemma valid_relB {M i j : ℕ} (hij : i + 2 ≤ j) (hjM : j < M) {x : Pt} (hx : Valid M x) :
    Valid M (relB i x) := by
  rcases x with _ | _ | k
  · simp only [relB, Valid]; omega
  · trivial
  · simp only [Valid] at hx
    simp only [relB]
    split_ifs <;> simp only [Valid] <;> omega

lemma relA_injective {i : ℕ} : Function.Injective (relA i) := by
  intro x y h
  rcases x with _ | _ | k <;> rcases y with _ | _ | l <;> simp only [relA] at h <;>
    (try split_ifs at h) <;> simp_all <;> omega

lemma relB_injective {i : ℕ} : Function.Injective (relB i) := by
  intro x y h
  rcases x with _ | _ | k <;> rcases y with _ | _ | l <;> simp only [relB] at h <;>
    (try split_ifs at h) <;> simp_all <;> omega

lemma relA_surj {M i j : ℕ} (hij : i + 2 ≤ j) (hjM : j < M) (x : Pt) (hx : Valid M x) :
    ∃ y, Valid M y ∧ relA i y = x := by
  rcases x with _ | _ | k
  · exact ⟨p (i + 1), by simp only [Valid]; omega, relA_mid i⟩
  · exact ⟨t, trivial, rfl⟩
  · simp only [Valid] at hx
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨s, trivial, rfl⟩
    · rcases Nat.lt_or_ge (i + 1) k with h | h
      · exact ⟨p k, hx, relA_gt (by omega)⟩
      · exact ⟨p (k - 1), by simp only [Valid]; omega, by
          rw [relA_le (by omega)]; congr 1; omega⟩

lemma relB_surj {M i j : ℕ} (hij : i + 2 ≤ j) (hjM : j < M) (x : Pt) (hx : Valid M x) :
    ∃ y, Valid M y ∧ relB i y = x := by
  rcases x with _ | _ | k
  · exact ⟨p (i + 1), by simp only [Valid]; omega, relB_mid i⟩
  · exact ⟨t, trivial, rfl⟩
  · simp only [Valid] at hx
    rcases Nat.lt_or_ge (i + 1) k with h | h
    · exact ⟨p k, hx, relB_gt (by omega)⟩
    · rcases Nat.eq_or_lt_of_le h with h' | h'
      · exact ⟨s, trivial, by rw [relB_s, h']⟩
      · exact ⟨p (i - k), by simp only [Valid]; omega, by
          rw [relB_le (by omega)]; congr 1; omega⟩

lemma valid_reflPt {M : ℕ} {x : Pt} (hx : Valid M x) : Valid M (reflPt M x) := by
  rcases x with _ | _ | k <;> simp only [Valid, reflPt] at hx ⊢ <;> omega

lemma reflPt_reflPt {M : ℕ} {x : Pt} (hx : Valid M x) : reflPt M (reflPt M x) = x := by
  rcases x with _ | _ | k <;> simp only [Valid, reflPt] at hx ⊢
  congr 1; omega

/-- The neighbours in the model `D̃` with fork ends (`i = 0`, `j = M - 1`, `M = k + 3`). -/
def forkNbrs (k : ℕ) : Pt → Finset Pt
  | s => {p 1}
  | t => {p (k + 1)}
  | p m => if m = 0 then {p 1} else if m = 1 then {p 0, s, p 2} else if m ≤ k then
      {p (m - 1), p (m + 1)} else if m = k + 1 then {p k, p (k + 2), t} else {p (k + 1)}

lemma sc_fork {k : ℕ} (hk : 1 ≤ k) (x x' : Pt) (hx : Valid (k + 3) x) (hx' : Valid (k + 3) x')
    (hne : x ≠ x') : sc (k + 3) 0 (k + 2) x x' = if x' ∈ forkNbrs k x then -1 else 0 := by
  rcases x with _ | _ | m <;> rcases x' with _ | _ | m' <;> simp only [Valid] at hx hx' <;>
    simp only [forkNbrs] <;> (try split_ifs) <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, Pt.p.injEq, or_false,
      false_or] at * <;> model_tac

end DTilde

namespace UnitForm

open DTilde DTilde.Pt

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The critical diagrams of type `D̃`** (von Höhne, Fig. 3): `q` and `y` are the model
coefficients and a positive multiple of the model radical vector, through a bijection of `ι`
with the valid model points. -/
def DShape (q : UnitForm ι) (y : ι → ℤ) : Prop :=
  ∃ (M i j : ℕ) (pos : ι → Pt) (l : ℤ), 0 < l ∧ i < j ∧ j < M ∧ (∀ u, Valid M (pos u)) ∧
    Function.Injective pos ∧ (∀ x, Valid M x → ∃ u, pos u = x) ∧
    (∀ u v, u ≠ v → q.c u v = sc M i j (pos u) (pos v)) ∧ ∀ u, y u = l * sy i j (pos u)

omit [Fintype ι] in
lemma inflMap_single (a b x : ι) :
    inflMap a b (Pi.single x 1) = if x = b then Pi.single b 1 - Pi.single a 1 else Pi.single x 1 := by
  funext v
  by_cases hx : x = b
  · subst hx; simp [inflMap, Pi.single_apply]
  · simp [inflMap, Pi.single_apply, hx]

/-- The coefficients of `q` from those of an inflation. -/
lemma c_eq_defl {q : UnitForm ι} {a b : ι} (hab : a ≠ b) (h : q.c a b = 1) {u v : ι}
    (huv : u ≠ v) :
    q.c u v = (if u = b ∧ v = a ∨ u = a ∧ v = b then (q.inflate hab h).c a b + 2
      else if u = b then (q.inflate hab h).c b v + (q.inflate hab h).c a v
      else if v = b then (q.inflate hab h).c u b + (q.inflate hab h).c u a
      else (q.inflate hab h).c u v) := by
  have key : ∀ x y, (q.inflate hab h).c x y = q.B (inflMap a b (Pi.single x 1))
      (inflMap a b (Pi.single y 1)) := fun _ _ ↦ rfl
  simp only [key, inflMap_single, ite_eq_right (Ne.symm hab), ite_eq_left rfl]
  have hba : q.c b a = 1 := by rw [q.symm]; exact h
  by_cases hu : u = b <;> by_cases hv : v = b <;> by_cases hua : u = a <;> by_cases hva : v = a <;>
    simp_all [B_sub_left, B_sub_right, B_single_single, q.diag] <;> ring

lemma deflMap_apply (a b : ι) (y : ι → ℤ) (u : ι) :
    deflMap a b y u = y u + if u = a then y b else 0 := by
  simp [deflMap, Pi.single_apply]

/-- The end-one step: if the inflation of `q` at `(a, b)` is a shape with `a = p (i + 1)` and
`b = p i` or `b = s`, then `q` is a shape. -/
lemma dshape_of_inflate_end {q : UnitForm ι} {a b : ι} (hab : a ≠ b) (hc : q.c a b = 1)
    {y : ι → ℤ} {M i j : ℕ} {pos : ι → Pt} {l : ℤ} (hl : 0 < l) (hij : i + 2 ≤ j)
    (hjM : j < M) (hval : ∀ u, Valid M (pos u)) (hinj : Function.Injective pos)
    (hsurj : ∀ x, Valid M x → ∃ u, pos u = x)
    (hcoef : ∀ u v, u ≠ v → (q.inflate hab hc).c u v = sc M i j (pos u) (pos v))
    (hyy : ∀ u, deflMap a b y u = l * sy i j (pos u)) (ha : pos a = p (i + 1))
    (hb : pos b = p i ∨ pos b = s) : q.DShape y := by
  have hyb : y b = l * sy i j (pos b) := by
    have := hyy b; rwa [deflMap_apply, if_neg (Ne.symm hab), add_zero] at this
  have hy' : ∀ u, y u = l * (if pos u = pos a then sy i j (pos a) - sy i j (pos b)
      else sy i j (pos u)) := by
    intro u
    have h1 := hyy u
    rw [deflMap_apply] at h1
    by_cases hua : u = a
    · subst hua; rw [if_pos rfl] at h1 ⊢; rw [hyb] at h1; linarith
    · rw [if_neg hua] at h1; rw [if_neg (fun h ↦ hua (hinj h))]; linarith
  -- coefficients of `q` as a deflation of the model
  have hdefl : ∀ u v, u ≠ v → q.c u v = defl (sc M i j) (pos a) (pos b) (pos u) (pos v) := by
    intro u v huv
    rw [c_eq_defl hab hc huv]
    simp only [defl, hinj.eq_iff]
    have hpu : pos u ≠ pos v := fun h ↦ huv (hinj h)
    split_ifs with h1 h2 h3 <;>
      first
      | (rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [hcoef _ _ hab])
      | (subst h2; rw [hcoef _ _ huv, hcoef a v (by tauto)])
      | (subst h3; rw [hcoef _ _ huv, hcoef u a (by tauto)])
      | exact hcoef _ _ huv
  rcases hb with hb | hb
  · refine ⟨M, i + 1, j, relA i ∘ pos, l, hl, by omega, hjM, fun u ↦ valid_relA hij hjM (hval u),
      relA_injective.comp hinj, fun x hx ↦ ?_, fun u v huv ↦ ?_, fun u ↦ ?_⟩
    · obtain ⟨z, hz, rfl⟩ := relA_surj hij hjM x hx
      obtain ⟨u, rfl⟩ := hsurj z hz
      exact ⟨u, rfl⟩
    · rw [hdefl u v huv, ha, hb]
      exact (sc_deflA hij hjM _ _ (hval u) (hval v) fun h ↦ huv (hinj h)).symm
    · rw [hy' u, Function.comp_apply, sy_deflA hij, ha, hb]
  · refine ⟨M, i + 1, j, relB i ∘ pos, l, hl, by omega, hjM, fun u ↦ valid_relB hij hjM (hval u),
      relB_injective.comp hinj, fun x hx ↦ ?_, fun u v huv ↦ ?_, fun u ↦ ?_⟩
    · obtain ⟨z, hz, rfl⟩ := relB_surj hij hjM x hx
      obtain ⟨u, rfl⟩ := hsurj z hz
      exact ⟨u, rfl⟩
    · rw [hdefl u v huv, ha, hb]
      exact (sc_deflB hij hjM _ _ (hval u) (hval v) fun h ↦ huv (hinj h)).symm
    · rw [hy' u, Function.comp_apply, sy_deflB hij, ha, hb]

/-- **Closure under deflation** (von Höhne, proof of Theorem 2.1 (2)): if the inflation of `q`
at `(a, b)` is a critical diagram of type `D̃`, so is `q`. -/
theorem DShape.of_inflate {q : UnitForm ι} {a b : ι} (hab : a ≠ b) (hc : q.c a b = 1)
    {y : ι → ℤ} (hy : ∀ u, 0 < y u) (h : (q.inflate hab hc).DShape (deflMap a b y)) :
    q.DShape y := by
  obtain ⟨M, i, j, pos, l, hl, hij, hjM, hval, hinj, hsurj, hcoef, hyy⟩ := h
  have hcab : sc M i j (pos a) (pos b) = -1 := by
    rw [← hcoef a b hab]
    have := c_eq_defl hab hc hab
    rw [if_pos (Or.inr ⟨rfl, rfl⟩)] at this
    linarith
  have hya := hyy a
  have hyb := hyy b
  rw [deflMap_apply, if_pos rfl] at hya
  rw [deflMap_apply, if_neg (Ne.symm hab), add_zero] at hyb
  have hlt : sy i j (pos b) < sy i j (pos a) := by
    have h2 : 0 < l * (sy i j (pos a) - sy i j (pos b)) := by
      have := hy a; rw [mul_sub]; linarith
    exact sub_pos.1 (pos_of_mul_pos_right h2 hl.le)
  have hpa := hval a
  have hpb := hval b
  -- the four deflatable pairs
  have h1b := one_le_sy i j (pos b)
  rcases hA : pos a with _ | _ | k <;> rw [hA] at hlt hcab hpa
  · rw [show sy i j s = 1 from rfl] at hlt; omega
  · rw [show sy i j t = 1 from rfl] at hlt; omega
  have hk : i < k ∧ k < j := by
    by_contra hk; rw [sy_p_of_not hk] at hlt; omega
  simp only [Valid] at hpa
  -- reflected data for the second end
  have refl_case : (∃ m, pos b = p m ∧ m = j ∧ k + 1 = j) ∨ (pos b = t ∧ k + 1 = j) →
      q.DShape y := by
    intro hend
    refine dshape_of_inflate_end (i := M - 1 - j) (j := M - 1 - i) (M := M)
      (pos := reflPt M ∘ pos) hab hc hl (by omega) (by omega)
      (fun u ↦ valid_reflPt (hval u)) ?_ ?_ ?_ ?_ ?_ ?_
    · intro u v huv
      exact hinj (by
        have := congrArg (reflPt M) huv
        simpa [Function.comp_apply, reflPt_reflPt (hval u), reflPt_reflPt (hval v)] using this)
    · intro x hx
      obtain ⟨u, hu⟩ := hsurj (reflPt M x) (valid_reflPt hx)
      exact ⟨u, by simp [Function.comp_apply, hu, reflPt_reflPt hx]⟩
    · intro u v huv
      rw [hcoef u v huv, Function.comp_apply, Function.comp_apply,
        sc_refl hij hjM _ _ (hval u) (hval v) fun h ↦ huv (hinj h)]
    · intro u
      rw [hyy u, Function.comp_apply, sy_refl hij hjM _ (hval u)]
    · rw [Function.comp_apply, hA]; simp only [reflPt]; congr 1; omega
    · rcases hend with ⟨m, hm, hmj, hkj⟩ | ⟨ht, hkj⟩
      · left; rw [Function.comp_apply, hm, hmj]; rfl
      · right; rw [Function.comp_apply, ht]; rfl
  rcases hB : pos b with _ | _ | m <;> rw [hB] at hlt hcab hpb
  · -- `b = s`
    have hk1 : k = i + 1 := by
      simp only [sc, sAdj] at hcab; split_ifs at hcab <;> omega
    subst hk1
    exact dshape_of_inflate_end hab hc hl (by omega) hjM hval hinj hsurj hcoef hyy hA (Or.inr hB)
  · -- `b = t`
    have hk1 : k + 1 = j := by
      simp only [sc, tAdj] at hcab; split_ifs at hcab <;> omega
    exact refl_case (Or.inr ⟨hB, hk1⟩)
  · simp only [Valid] at hpb
    have hm : m ≤ i ∨ j ≤ m := by
      by_contra hm; push Not at hm
      simp only [sy, if_pos hm, if_pos hk] at hlt; omega
    have hadj : k + 1 = m ∨ m + 1 = k := by
      simp only [sc] at hcab; split_ifs at hcab with h <;> first | exact h | omega
    rcases hm with hm | hm
    · obtain rfl : k = i + 1 := by omega
      obtain rfl : m = i := by omega
      exact dshape_of_inflate_end hab hc hl (by omega) hjM hval hinj hsurj hcoef hyy hA (Or.inl hB)
    · exact refl_case (Or.inl ⟨m, hB, by omega, by omega⟩)

end UnitForm

end LargeIndecomposable.Forms
