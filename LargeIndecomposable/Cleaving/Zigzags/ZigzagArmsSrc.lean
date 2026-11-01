module

public import LargeIndecomposable.Cleaving.Zigzags.ZigzagArms

/-!
# Zigzags with two arms, one at a source: BO13a figure 9.5

The diagram: an arm `x₀ → M₀ → E₀` with `s₀ : M₀ → z p`; the zigzag `σ (p+j)` (`j ≤ L`),
`ρ (p+j+1)` (`j < L`) from `z p` to the source `x (p+L+1)`; `r : x (p+L+1) → M` and an arm
`X'' → M → E`. It is an orientation of `D̃₂ₗ₊₇` (`RayCat.ZAB`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

/-- The vertices. -/
inductive ZAB (L : ℕ) : Type
  | zv (j : Fin (L + 1))
  | xv (j : Fin (L + 1))
  | m0
  | x0
  | e0
  | mv
  | xe
  | ee
  deriving DecidableEq

namespace ZAB

variable {L : ℕ}

instance : Fintype (ZAB L) where
  elems := (Finset.univ.map ⟨zv, fun _ _ h ↦ by cases h; rfl⟩) ∪
    (Finset.univ.map ⟨xv, fun _ _ h ↦ by cases h; rfl⟩) ∪ {m0, x0, e0, mv, xe, ee}
  complete v := by
    cases v
    · simp only [Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and]
      exact Or.inl (Or.inl ⟨_, rfl⟩)
    · simp only [Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and]
      exact Or.inl (Or.inr ⟨_, rfl⟩)
    all_goals simp

/-- The arrows. -/
inductive R : ZAB L → ZAB L → Prop
  | σ (j : Fin (L + 1)) : R (xv j) (zv j)
  | ρ (j : Fin L) : R (xv j.castSucc) (zv j.succ)
  | s0 : R m0 (zv 0)
  | u1 : R x0 m0
  | u2 : R m0 e0
  | rm : R (xv (Fin.last L)) mv
  | v1 : R xe mv
  | v2 : R mv ee

lemma R_asymm {u v : ZAB L} (h : R u v) : ¬R v u := by
  intro h'
  cases h <;> cases h'

lemma R_irrefl {u : ZAB L} (h : R u u) : False := by
  cases h

variable (L) in
/-- The graph. -/
def graph : SimpleGraph (ZAB L) := SimpleGraph.fromRel R

lemma adj_iff {u v : ZAB L} : (graph L).Adj u v ↔ R u v ∨ R v u := by
  rw [graph, SimpleGraph.fromRel_adj]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  rintro rfl
  rcases h with h | h <;> exact R_irrefl h

/-- The parent function towards `m0`. -/
def par : ZAB L → Option (ZAB L)
  | zv j => if h : j.val = 0 then some m0 else some (xv ⟨j.val - 1, by have := j.2; omega⟩)
  | xv j => some (zv j)
  | m0 => none
  | x0 => some m0
  | e0 => some m0
  | mv => some (xv (Fin.last L))
  | xe => some mv
  | ee => some mv

/-- The height. -/
def ht : ZAB L → ℕ
  | zv j => 2 * j.val + 1
  | xv j => 2 * j.val + 2
  | m0 => 0
  | x0 => 1
  | e0 => 1
  | mv => 2 * L + 3
  | xe => 2 * L + 4
  | ee => 2 * L + 4

lemma par_of_R {u v : ZAB L} (h : R u v) : par u = some v ∨ par v = some u := by
  cases h with
  | σ j => exact Or.inl rfl
  | ρ j =>
    right
    simp only [par, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, dite_false,
      Option.some.injEq, xv.injEq]
    ext
    simp
  | s0 => exact Or.inr (by simp [par])
  | u1 => exact Or.inl rfl
  | u2 => exact Or.inr rfl
  | rm => exact Or.inr rfl
  | v1 => exact Or.inl rfl
  | v2 => exact Or.inr rfl

lemma R_of_par {u v : ZAB L} (h : par u = some v) : R u v ∨ R v u := by
  cases u with
  | zv j =>
    simp only [par] at h
    split_ifs at h with h1
    · simp only [Option.some.injEq] at h
      subst h
      right
      obtain rfl : j = 0 := Fin.ext h1
      exact R.s0
    · simp only [Option.some.injEq] at h
      subst h
      right
      have hj : j.val - 1 < L := by have := j.2; omega
      convert R.ρ (L := L) ⟨j.val - 1, hj⟩ using 2
      · ext
        simp
      · ext
        simp
        omega
  | xv j => simp only [par, Option.some.injEq] at h; subst h; exact Or.inl (R.σ j)
  | m0 => simp [par] at h
  | x0 => simp only [par, Option.some.injEq] at h; subst h; exact Or.inl R.u1
  | e0 => simp only [par, Option.some.injEq] at h; subst h; exact Or.inr R.u2
  | mv => simp only [par, Option.some.injEq] at h; subst h; exact Or.inr R.rm
  | xe => simp only [par, Option.some.injEq] at h; subst h; exact Or.inl R.v1
  | ee => simp only [par, Option.some.injEq] at h; subst h; exact Or.inr R.v2

lemma R_iff_par (u v : ZAB L) : R u v ∨ R v u ↔ par u = some v ∨ par v = some u := by
  constructor
  · rintro (h | h)
    · exact par_of_R h
    · exact (par_of_R h).symm
  · rintro (h | h)
    · exact R_of_par h
    · exact (R_of_par h).symm

lemma par_lt (u v : ZAB L) (h : par u = some v) : ht v < ht u := by
  cases u with
  | zv j =>
    simp only [par] at h
    split_ifs at h with h1
    · simp only [Option.some.injEq] at h; subst h; simp [ht]
    · simp only [Option.some.injEq] at h; subst h; simp only [ht]; omega
  | xv j => simp only [par, Option.some.injEq] at h; subst h; simp [ht]
  | m0 => simp [par] at h
  | x0 => simp only [par, Option.some.injEq] at h; subst h; simp [ht]
  | e0 => simp only [par, Option.some.injEq] at h; subst h; simp [ht]
  | mv => simp only [par, Option.some.injEq] at h; subst h; simp [ht]
  | xe => simp only [par, Option.some.injEq] at h; subst h; simp [ht]
  | ee => simp only [par, Option.some.injEq] at h; subst h; simp [ht]

lemma isAcyclic : (graph L).IsAcyclic :=
  isAcyclic_of_parent (graph L) par ht (fun u v ↦ by rw [adj_iff, R_iff_par]) par_lt

lemma R_ρ' {a b : Fin (L + 1)} (h : b.val = a.val + 1) : R (xv a) (zv b) := by
  have ha : a.val < L := by have := b.2; omega
  convert R.ρ (L := L) ⟨a.val, ha⟩ using 2
  · ext; simp
  · ext; simp [h]

lemma R_σ' {a b : Fin (L + 1)} (h : b.val = a.val) : R (xv a) (zv b) := by
  obtain rfl : b = a := Fin.ext h
  exact R.σ b

open LargeIndecomposable.Foundations.Quiver in
/-- The vertex map of the copy of `D̃₂ₗ₊₇`. -/
def dmap : AffineD (2 * L + 3) → ZAB L
  | .spine a => if h0 : a.val = 0 then m0 else if hl : a.val = 2 * L + 3 then mv else
      if h : a.val % 2 = 1 then zv ⟨(a.val - 1) / 2, by have := a.isLt; omega⟩
      else xv ⟨a.val / 2 - 1, by have := a.isLt; omega⟩
  | .leaf i => if i.val = 0 then x0 else if i.val = 1 then e0 else if i.val = 2 then xe else ee

open LargeIndecomposable.Foundations.Quiver in
lemma dmap_adj_of_hom (a b : AffineD (2 * L + 3)) (e : Nonempty (a ⟶ b)) :
    (graph L).Adj (dmap a) (dmap b) := by
  rw [adj_iff]
  rcases a with i | j <;> rcases b with i' | j'
  · exact absurd e (AffineD.not_nonempty_hom_leaf _ _)
  · have hj := (AffineD.nonempty_leaf_spine_iff i j').1 e
    by_cases hi : i.val < 2
    · rw [AffineD.leafTarget_of_lt_two i hi] at hj
      subst hj
      simp only [dmap, Fin.val_zero]
      by_cases h0 : i.val = 0
      · rw [ite_eq_left h0]; exact Or.inl R.u1
      · rw [ite_eq_right h0, ite_eq_left (by omega)]; exact Or.inr R.u2
    · rw [AffineD.leafTarget_of_not_lt_two i hi] at hj
      subst hj
      simp only [dmap, Fin.val_last, dite_true]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      by_cases h2 : i.val = 2
      · rw [ite_eq_left h2]; exact Or.inl R.v1
      · rw [ite_eq_right h2]; exact Or.inr R.v2
  · exact absurd e (AffineD.not_nonempty_hom_leaf _ _)
  · have hj := (AffineD.nonempty_spine_spine_iff j j').1 e
    have hj0 : ¬j'.val = 0 := by omega
    have hjl : j.val ≠ 2 * L + 3 := by have := j'.2; omega
    by_cases h0 : j.val = 0
    · left
      have hl : ¬j'.val = 2 * L + 3 := by omega
      have hod : j'.val % 2 = 1 := by omega
      simp only [dmap, h0, dite_true, hj0, hl, hod, dite_false]
      have e : (⟨(j'.val - 1) / 2, by omega⟩ : Fin (L + 1)) = 0 := Fin.ext (by simp; omega)
      rw [e]
      exact R.s0
    · by_cases hlast : j'.val = 2 * L + 3
      · left
        have hod : ¬j.val % 2 = 1 := by omega
        simp only [dmap, h0, hjl, hod, dite_false, dite_true, hj0, hlast]
        have e : (⟨j.val / 2 - 1, by omega⟩ : Fin (L + 1)) = Fin.last L :=
          Fin.ext (by simp; omega)
        rw [e]
        exact R.rm
      · by_cases hp : j.val % 2 = 1
        · right
          have hq : ¬j'.val % 2 = 1 := by omega
          simp only [dmap, h0, hjl, hp, dite_true, dite_false, hj0, hlast, hq]
          exact R_σ' (by simp; omega)
        · left
          have hq : j'.val % 2 = 1 := by omega
          simp only [dmap, h0, hjl, hp, dite_true, dite_false, hj0, hlast, hq]
          exact R_ρ' (by simp; omega)

open LargeIndecomposable.Foundations.Quiver in
/-- The copy of `D̃₂ₗ₊₇`. -/
def dcopy : (underlyingGraph (AffineD (2 * L + 3))).Copy (graph L) where
  toHom := ⟨dmap, fun {a b} h ↦ by
    rcases (underlyingGraph_adj.1 h).2 with e | e
    · exact dmap_adj_of_hom a b e
    · exact (dmap_adj_of_hom b a e).symm⟩
  injective' a b h := by
    change dmap a = dmap b at h
    rcases a with i | j <;> rcases b with i' | j'
    · simp only [dmap] at h
      split_ifs at h <;> simp only [reduceCtorEq] at h <;> exact congrArg _ (Fin.ext (by omega))
    · simp only [dmap] at h
      split_ifs at h <;> simp only [reduceCtorEq] at h
    · simp only [dmap] at h
      split_ifs at h <;> simp only [reduceCtorEq] at h
    · simp only [dmap] at h
      split_ifs at h <;> simp only [xv.injEq, zv.injEq, Fin.mk.injEq, reduceCtorEq] at h <;>
        exact congrArg _ (Fin.ext (by omega))

lemma zx_val {a b : Fin (L + 1)} (h : R (xv a) (zv b)) (hab : ¬b.val = a.val) :
    b.val = a.val + 1 := by
  cases h with
  | σ j => exact absurd rfl hab
  | ρ j => simp

lemma m0_val {b : Fin (L + 1)} (h : R m0 (zv b)) : b.val = 0 := by cases h; rfl

lemma xm_val {a : Fin (L + 1)} (h : R (xv a) mv) : a.val = L := by cases h; rfl

lemma R_xv {a : Fin (L + 1)} {w : ZAB L} (h : R (xv a) w) :
    (∃ b : Fin (L + 1), w = zv b ∧ b.val = a.val) ∨
      (∃ b : Fin (L + 1), w = zv b ∧ b.val = a.val + 1) ∨ (w = mv ∧ a.val = L) := by
  generalize hu : xv a = u at h
  cases h with
  | σ j => cases hu; exact Or.inl ⟨_, rfl, rfl⟩
  | ρ j =>
    simp only [xv.injEq] at hu
    subst hu
    exact Or.inr (Or.inl ⟨_, rfl, by simp⟩)
  | rm => cases hu; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  | s0 => cases hu
  | u1 => cases hu
  | u2 => cases hu
  | v1 => cases hu
  | v2 => cases hu

lemma R_m0 {w : ZAB L} (h : R m0 w) : (∃ b : Fin (L + 1), w = zv b ∧ b.val = 0) ∨ w = e0 := by
  cases h with
  | s0 => exact Or.inl ⟨_, rfl, rfl⟩
  | u2 => exact Or.inr rfl

lemma R_mv {w : ZAB L} (h : R mv w) : w = ee := by cases h; rfl

lemma R_x0 {w : ZAB L} (h : R x0 w) : w = m0 := by cases h; rfl

lemma R_xe {w : ZAB L} (h : R xe w) : w = mv := by cases h; rfl

lemma R_to_zv {u : ZAB L} {b : Fin (L + 1)} (h : R u (zv b)) :
    (∃ a : Fin (L + 1), u = xv a ∧ b.val = a.val) ∨
      (∃ a : Fin (L + 1), u = xv a ∧ b.val = a.val + 1) ∨ (u = m0 ∧ b.val = 0) := by
  generalize hw : zv b = w at h
  cases h with
  | σ j => cases hw; exact Or.inl ⟨_, rfl, rfl⟩
  | ρ j =>
    simp only [zv.injEq] at hw
    subst hw
    exact Or.inr (Or.inl ⟨_, rfl, by simp⟩)
  | s0 => cases hw; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  | rm => cases hw
  | u1 => cases hw
  | u2 => cases hw
  | v1 => cases hw
  | v2 => cases hw

lemma R_to_m0 {u : ZAB L} (h : R u m0) : u = x0 := by cases h; rfl

lemma R_to_mv {u : ZAB L} (h : R u mv) : (∃ a : Fin (L + 1), u = xv a ∧ a.val = L) ∨ u = xe := by
  cases h with
  | rm => exact Or.inl ⟨_, rfl, rfl⟩
  | v1 => exact Or.inr rfl

lemma R_to_e0 {u : ZAB L} (h : R u e0) : u = m0 := by cases h; rfl

lemma R_to_ee {u : ZAB L} (h : R u ee) : u = mv := by cases h; rfl

lemma R_to_xv {u : ZAB L} {a : Fin (L + 1)} (h : R u (xv a)) : False := by cases h

lemma R_to_x0 {u : ZAB L} (h : R u x0) : False := by cases h

lemma R_to_xe {u : ZAB L} (h : R u xe) : False := by cases h

lemma mid {u b w : ZAB L} (h1 : R u b) (h2 : R b w) :
    (b = m0 ∧ u = x0) ∨ (b = mv ∧ w = ee) := by
  cases h1 <;> cases h2
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

variable {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] (Z : ZChain Q) (p L : ℕ)
  (M₀ X₀ E₀ M X'' E : Q)

/-- The objects. -/
def aobj : ZAB L → Q
  | zv j => Z.z (p + j.val)
  | xv j => Z.x (p + j.val + 1)
  | m0 => M₀
  | x0 => X₀
  | e0 => E₀
  | mv => M
  | xe => X''
  | ee => E

variable {M₀ X₀ E₀ M X'' E} (s₀ : M₀ ⟶ Z.z p) (u₁ : X₀ ⟶ M₀) (u₂ : M₀ ⟶ E₀)
  (r : Z.x (p + L + 1) ⟶ M) (v : X'' ⟶ M) (s'' : M ⟶ E)

/-- The morphisms. -/
def amor : ∀ u w : ZAB L, R u w → (aobj Z p L M₀ X₀ E₀ M X'' E u ⟶ aobj Z p L M₀ X₀ E₀ M X'' E w)
  | xv a, zv b, h =>
    if hab : b.val = a.val then
      Z.σ (p + a.val) ≫ eqToHom (congrArg (fun t ↦ Z.z (p + t)) hab.symm)
    else Z.ρ (p + a.val + 1) ≫ eqToHom (congrArg (fun t ↦ Z.z (p + t)) (zx_val h hab).symm)
  | xv a, mv, h => eqToHom (congrArg (fun t ↦ Z.x (p + t + 1)) (xm_val h)) ≫ r
  | m0, zv b, h => s₀ ≫ eqToHom (congrArg (fun t ↦ Z.z (p + t)) (m0_val h).symm)
  | m0, e0, _ => u₂
  | x0, m0, _ => u₁
  | mv, ee, _ => s''
  | xe, mv, _ => v
  | xv _, xv _, h | xv _, m0, h | xv _, x0, h | xv _, e0, h | xv _, xe, h
  | xv _, ee, h => absurd h (by intro h; cases h)
  | zv _, _, h | e0, _, h | ee, _, h => absurd h (by intro h; cases h)
  | m0, xv _, h | m0, m0, h | m0, x0, h | m0, mv, h | m0, xe, h | m0, ee, h =>
    absurd h (by intro h; cases h)
  | x0, zv _, h | x0, xv _, h | x0, x0, h | x0, e0, h | x0, mv, h | x0, xe, h | x0, ee, h =>
    absurd h (by intro h; cases h)
  | mv, zv _, h | mv, xv _, h | mv, m0, h | mv, x0, h | mv, e0, h | mv, mv, h | mv, xe, h =>
    absurd h (by intro h; cases h)
  | xe, zv _, h | xe, xv _, h | xe, m0, h | xe, x0, h | xe, e0, h | xe, xe, h | xe, ee, h =>
    absurd h (by intro h; cases h)

variable {Z p L s₀ u₁ u₂ r v s''}

lemma amor_σ' (a b : Fin (L + 1)) (hab : b.val = a.val) (h) :
    amor Z p L s₀ u₁ u₂ r v s'' (xv a) (zv b) h =
      Z.σ (p + a.val) ≫ eqToHom (congrArg (fun t ↦ Z.z (p + t)) hab.symm) := by
  simp only [amor, hab, dite_true]
  rfl

lemma amor_ρ' (a b : Fin (L + 1)) (hab : b.val = a.val + 1) (h) :
    amor Z p L s₀ u₁ u₂ r v s'' (xv a) (zv b) h =
      Z.ρ (p + a.val + 1) ≫ eqToHom (congrArg (fun t ↦ Z.z (p + t)) hab.symm) := by
  have : ¬b.val = a.val := by omega
  simp only [amor, this, dite_false]
  rfl

lemma amor_σ (j : Fin (L + 1)) (h) : amor Z p L s₀ u₁ u₂ r v s'' (xv j) (zv j) h =
    Z.σ (p + j.val) := by
  rw [amor_σ' j j rfl]
  exact Category.comp_id _

lemma amor_ρ (j : Fin L) (h) : amor Z p L s₀ u₁ u₂ r v s'' (xv j.castSucc) (zv j.succ) h =
    Z.ρ (p + j.val + 1) := by
  rw [amor_ρ' j.castSucc j.succ (by simp)]
  exact Category.comp_id _

lemma amor_s0 (h) : amor Z p L s₀ u₁ u₂ r v s'' m0 (zv 0) h = s₀ := Category.comp_id _

lemma amor_rm (h) : amor Z p L s₀ u₁ u₂ r v s'' (xv (Fin.last L)) mv h = r := Category.id_comp _

lemma amor_s0v (h0 : 0 < L + 1) (h) : amor Z p L s₀ u₁ u₂ r v s'' m0 (zv ⟨0, h0⟩) h = s₀ :=
  Category.comp_id _

lemma amor_rmv (hc : L < L + 1) (h) : amor Z p L s₀ u₁ u₂ r v s'' (xv ⟨L, hc⟩) mv h = r :=
  Category.id_comp _

lemma amor_u1 (h) : amor Z p L s₀ u₁ u₂ r v s'' x0 m0 h = u₁ := rfl

lemma amor_u2 (h) : amor Z p L s₀ u₁ u₂ r v s'' m0 e0 h = u₂ := rfl

lemma amor_v1 (h) : amor Z p L s₀ u₁ u₂ r v s'' xe mv h = v := rfl

lemma amor_v2 (h) : amor Z p L s₀ u₁ u₂ r v s'' mv ee h = s'' := rfl

end ZAB

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

open ZAB in
include B in
/-- **No zigzag with two arms, one at a source, in `P/τ`** (BO13a figure 9.5). -/
theorem not_zigzag_arms_src
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) (Z : ZChain P) (p L : ℕ) {M₀ X₀ E₀ M X'' E : P}
    (s₀ : M₀ ⟶ Z.z p) (u₁ : X₀ ⟶ M₀) (u₂ : M₀ ⟶ E₀)
    (r : Z.x (p + L + 1) ⟶ M) (v : X'' ⟶ M) (s'' : M ⟶ E)
    (hρ : ∀ j < L, ¬FactorsThroughMorphism τ (Z.ρ (p + j + 1)))
    (hσ : ∀ j ≤ L, ¬FactorsThroughMorphism τ (Z.σ (p + j)))
    (hs₀ : ¬FactorsThroughMorphism τ s₀) (hu₁ : ¬FactorsThroughMorphism τ u₁)
    (hu₂ : ¬FactorsThroughMorphism τ u₂) (hu₁₂ : ¬FactorsThroughMorphism τ (u₁ ≫ u₂))
    (hu₁s : ¬FactorsThroughMorphism τ (u₁ ≫ s₀))
    (hr : ¬FactorsThroughMorphism τ r) (hv : ¬FactorsThroughMorphism τ v)
    (hs : ¬FactorsThroughMorphism τ s'') (hrs : ¬FactorsThroughMorphism τ (r ≫ s''))
    (hvs : ¬FactorsThroughMorphism τ (v ≫ s''))
    (his₀ : ¬IsIso s₀) (hiu₁ : ¬IsIso u₁) (hiu₂ : ¬IsIso u₂) (hir : ¬IsIso r)
    (hiv : ¬IsIso v) (his : ¬IsIso s'')
    (hsu : ¬∃ g, s₀ ≫ g = u₂) (hus : ¬∃ g, u₂ ≫ g = s₀)
    (hσs : ¬∃ g, g ≫ Z.σ p = s₀) (hσus : ¬∃ g, g ≫ Z.σ p = u₁ ≫ s₀)
    (hsσ : ¬∃ g, g ≫ s₀ = Z.σ p)
    (hσr : ¬∃ g, Z.σ (p + L) ≫ g = r) (hσrs : ¬∃ g, Z.σ (p + L) ≫ g = r ≫ s'')
    (hrσ : ¬∃ g, r ≫ g = Z.σ (p + L))
    (hrv : ¬∃ g, g ≫ r = v) (hvr : ¬∃ g, g ≫ v = r) : False := by
  have ho : ∀ u v, R u v → (graph L).Adj u v := fun u v h ↦ adj_iff.2 (Or.inl h)
  haveI : Fact (LargeIndecomposable.Foundations.Quiver.IsAcyclic (OT (graph L) R)) :=
    ⟨OT.isAcyclic ho (fun _ _ h ↦ R_asymm h) isAcyclic⟩
  let φ : OT (graph L) R ⥤q P :=
    { obj := fun u ↦ aobj Z p L M₀ X₀ E₀ M X'' E u.as
      map := fun {u w} e ↦ amor Z p L s₀ u₁ u₂ r v s'' u.as w.as (OT.hom_down e) }
  have harr : ∀ u w (h : R u w), ¬FactorsThroughMorphism τ (amor Z p L s₀ u₁ u₂ r v s'' u w h) ∧
      ¬IsIso (amor Z p L s₀ u₁ u₂ r v s'' u w h) := by
    intro u w h
    cases h with
    | σ j => rw [amor_σ]; exact ⟨hσ j (by omega), Z.σ_not_isIso _⟩
    | ρ j => rw [amor_ρ]; exact ⟨hρ j j.2, Z.ρ_not_isIso _⟩
    | s0 => rw [amor_s0]; exact ⟨hs₀, his₀⟩
    | u1 => exact ⟨hu₁, hiu₁⟩
    | u2 => exact ⟨hu₂, hiu₂⟩
    | rm => rw [amor_rm]; exact ⟨hr, hir⟩
    | v1 => exact ⟨hv, hiv⟩
    | v2 => exact ⟨hs, his⟩
  refine B.not_ot_diagram hmin hL hR τ hτ hτ0 (graph L) R ho (fun _ _ h ↦ R_asymm h) isAcyclic
    (OT.not_isRepresentationFinite_affineD ho (fun _ _ h ↦ adj_iff.1 h) k (2 * L + 3) dcopy) φ
    ?_ ?_ ?_ ?_
  · intro u w q hq
    rcases u with ⟨u⟩
    rcases w with ⟨w⟩
    cases q with
    | nil => simp at hq
    | cons q e =>
      rename_i w1
      rcases w1 with ⟨w1⟩
      have he := OT.hom_down e
      cases q with
      | nil =>
        change ¬FactorsThroughMorphism τ (𝟙 _ ≫ amor Z p L s₀ u₁ u₂ r v s'' u w he)
        rw [Category.id_comp]
        exact (harr u w he).1
      | cons q e' =>
        rename_i w2
        rcases w2 with ⟨w2⟩
        have he' := OT.hom_down e'
        rcases mid he' he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · cases q with
          | nil =>
            change ¬FactorsThroughMorphism τ ((𝟙 _ ≫ amor Z p L s₀ u₁ u₂ r v s'' x0 m0 he') ≫
              amor Z p L s₀ u₁ u₂ r v s'' m0 w he)
            rw [Category.id_comp, amor_u1]
            rcases R_m0 he with ⟨⟨c, hc0⟩, rfl, hc⟩ | rfl
            · simp only at hc
              subst hc
              rw [amor_s0v]
              exact hu₁s
            · rw [amor_u2]; exact hu₁₂
          | cons q e'' => exact (R_to_x0 (OT.hom_down e'')).elim
        · rcases R_to_mv he' with ⟨⟨c, hc0⟩, rfl, hc⟩ | rfl
          · simp only at hc
            have hc' : L = c := hc.symm
            subst hc'
            cases q with
            | nil =>
              change ¬FactorsThroughMorphism τ ((𝟙 _ ≫
                amor Z p L s₀ u₁ u₂ r v s'' (xv ⟨L, hc0⟩) mv he') ≫
                  amor Z p L s₀ u₁ u₂ r v s'' mv ee he)
              rw [Category.id_comp, amor_rmv, amor_v2]
              exact hrs
            | cons q e'' => exact (R_to_xv (OT.hom_down e'')).elim
          · cases q with
            | nil =>
              change ¬FactorsThroughMorphism τ ((𝟙 _ ≫ amor Z p L s₀ u₁ u₂ r v s'' xe mv he') ≫
                amor Z p L s₀ u₁ u₂ r v s'' mv ee he)
              rw [Category.id_comp, amor_v1, amor_v2]
              exact hvs
            | cons q e'' => exact (R_to_xe (OT.hom_down e'')).elim
  · intro u w e
    exact (harr _ _ _).2
  · intro u c c' w e e' q hne ⟨g, hg⟩
    rcases u with ⟨u⟩
    rcases c with ⟨c⟩
    rcases c' with ⟨c'⟩
    rcases w with ⟨w⟩
    have he := OT.hom_down e
    have he' := OT.hom_down e'
    cases q with
    | cons q e2 =>
      obtain ⟨d, f, rest, -, heq⟩ :=
        Quiver.Path.eq_toPath_comp_of_length_eq_succ (q.cons e2) (n := q.length) (by simp)
      rcases d with ⟨d⟩
      have hf := OT.hom_down f
      rcases mid he' hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (hne (congrArg OT.mk (R_x0 he))).elim
      · cases rest with
        | cons rest' e5 =>
          obtain ⟨d2, f2, -, -, -⟩ :=
            Quiver.Path.eq_toPath_comp_of_length_eq_succ (rest'.cons e5) (n := rest'.length)
              (by simp)
          exact (by cases OT.hom_down f2 : False)
        | nil =>
          rw [heq] at hg
          rcases R_to_mv he' with ⟨⟨a', ha0⟩, rfl, ha⟩ | rfl
          · simp only at ha
            have ha' : L = a' := ha.symm
            subst ha'
            rcases R_xv he with ⟨⟨b', hb0⟩, rfl, hb⟩ | ⟨⟨b', hb0⟩, rfl, hb⟩ | ⟨rfl, -⟩
            · simp only at hb
              have hb' : L = b' := hb.symm
              subst hb'
              change amor Z p L s₀ u₁ u₂ r v s'' (xv ⟨L, ha0⟩) (zv ⟨L, hb0⟩) he ≫ g =
                (𝟙 _ ≫ amor Z p L s₀ u₁ u₂ r v s'' (xv ⟨L, ha0⟩) mv he') ≫
                  amor Z p L s₀ u₁ u₂ r v s'' mv ee hf at hg
              rw [Category.id_comp, amor_rmv, amor_v2, amor_σ ⟨L, ha0⟩] at hg
              exact hσrs ⟨g, hg⟩
            · simp only at hb; omega
            · exact (hne rfl).elim
          · exact (hne (congrArg OT.mk (R_xe he))).elim
    | nil =>
      change amor Z p L s₀ u₁ u₂ r v s'' u c he ≫ g = 𝟙 _ ≫ amor Z p L s₀ u₁ u₂ r v s'' u c' he'
        at hg
      rw [Category.id_comp] at hg
      cases he with
      | σ j =>
        rw [amor_σ] at hg
        rcases R_xv he' with ⟨⟨b, hb0⟩, rfl, hb⟩ | ⟨⟨b, hb0⟩, rfl, hb⟩ | ⟨rfl, hb⟩
        · exact hne (congrArg OT.mk (congrArg zv (Fin.ext hb.symm)))
        · rw [amor_ρ' j ⟨b, hb0⟩ hb] at hg
          obtain ⟨j, hj⟩ := j
          simp only at hb hg
          subst hb
          try simp only [eqToHom_refl, Category.comp_id] at hg
          exact Z.valley₁ _ ⟨g, hg⟩
        · obtain ⟨j, hj⟩ := j
          simp only at hb hg
          have hb' : L = j := hb.symm
          subst hb'
          rw [amor_rmv] at hg
          exact hσr ⟨g, hg⟩
      | ρ j =>
        rw [amor_ρ] at hg
        rcases R_xv he' with ⟨⟨b, hb0⟩, rfl, hb⟩ | ⟨⟨b, hb0⟩, rfl, hb⟩ | ⟨rfl, hb⟩
        · rw [amor_σ' j.castSucc ⟨b, hb0⟩ hb] at hg
          obtain ⟨j, hj⟩ := j
          simp only [Fin.val_castSucc] at hb hg
          subst hb
          try simp only [eqToHom_refl, Category.comp_id] at hg
          exact Z.valley₂ _ ⟨g, hg⟩
        · exact hne (congrArg OT.mk (congrArg zv (Fin.ext (by simp at hb ⊢; omega))))
        · simp only [Fin.val_castSucc] at hb
          have := j.2
          omega
      | rm =>
        rw [amor_rm] at hg
        rcases R_xv he' with ⟨⟨b, hb0⟩, rfl, hb⟩ | ⟨⟨b, hb0⟩, rfl, hb⟩ | ⟨rfl, -⟩
        · simp only [Fin.val_last] at hb
          have hb' : L = b := hb.symm
          subst hb'
          rw [amor_σ' (Fin.last L) ⟨L, hb0⟩ rfl] at hg
          change r ≫ g = Z.σ (p + L) ≫ 𝟙 _ at hg
          rw [Category.comp_id] at hg
          exact hrσ ⟨g, hg⟩
        · simp only [Fin.val_last] at hb; omega
        · exact hne rfl
      | s0 =>
        rw [amor_s0] at hg
        rcases R_m0 he' with ⟨⟨b, hb0⟩, rfl, hb⟩ | rfl
        · simp only at hb
          exact hne (congrArg OT.mk (congrArg zv (Fin.ext (by simp only [Fin.val_zero]; omega))))
        · rw [amor_u2] at hg
          exact hsu ⟨g, hg⟩
      | u2 =>
        rw [amor_u2] at hg
        rcases R_m0 he' with ⟨⟨b, hb0⟩, rfl, hb⟩ | rfl
        · simp only at hb
          subst hb
          rw [amor_s0v] at hg
          exact hus ⟨g, hg⟩
        · exact hne rfl
      | u1 => exact hne (congrArg OT.mk (R_x0 he').symm)
      | v1 => exact hne (congrArg OT.mk (R_xe he').symm)
      | v2 => exact hne (congrArg OT.mk (R_mv he').symm)
  · intro u c c' w e e' q hne ⟨g, hg⟩
    rcases u with ⟨u⟩
    rcases c with ⟨c⟩
    rcases c' with ⟨c'⟩
    rcases w with ⟨w⟩
    have he := OT.hom_down e
    have he' := OT.hom_down e'
    cases he with
    | σ j =>
      rcases R_to_zv he' with ⟨⟨a, ha0⟩, rfl, ha⟩ | ⟨⟨a, ha0⟩, rfl, ha⟩ | ⟨rfl, hb⟩
      · exact hne (congrArg OT.mk (congrArg xv (Fin.ext (by simp [ha]))))
      · cases q with
        | cons q e3 => exact (R_to_xv (OT.hom_down e3)).elim
        | nil =>
          change g ≫ amor Z p L s₀ u₁ u₂ r v s'' (xv j) (zv j) e.down =
            𝟙 _ ≫ amor Z p L s₀ u₁ u₂ r v s'' (xv ⟨a, ha0⟩) (zv j) he' at hg
          rw [Category.id_comp, amor_σ, amor_ρ' ⟨a, ha0⟩ j ha] at hg
          obtain ⟨j, hj⟩ := j
          simp only at ha hg
          subst ha
          try simp only [eqToHom_refl, Category.comp_id] at hg
          exact Z.peak₁ _ ⟨g, hg⟩
      · obtain ⟨j, hj⟩ := j
        simp only at hb
        subst hb
        cases q with
        | nil =>
          change g ≫ amor Z p L s₀ u₁ u₂ r v s'' (xv ⟨0, hj⟩) (zv ⟨0, hj⟩) e.down =
            𝟙 _ ≫ amor Z p L s₀ u₁ u₂ r v s'' m0 (zv ⟨0, hj⟩) he' at hg
          rw [Category.id_comp, amor_σ, amor_s0v] at hg
          exact hσs ⟨g, hg⟩
        | cons q e3 =>
          rename_i w3
          rcases w3 with ⟨w3⟩
          obtain rfl := R_to_m0 (OT.hom_down e3)
          cases q with
          | cons q e4 => exact (R_to_x0 (OT.hom_down e4)).elim
          | nil =>
            change g ≫ amor Z p L s₀ u₁ u₂ r v s'' (xv ⟨0, hj⟩) (zv ⟨0, hj⟩) e.down =
              (𝟙 _ ≫ amor Z p L s₀ u₁ u₂ r v s'' x0 m0 (OT.hom_down e3)) ≫
                amor Z p L s₀ u₁ u₂ r v s'' m0 (zv ⟨0, hj⟩) he' at hg
            rw [Category.id_comp, amor_σ, amor_u1, amor_s0v] at hg
            exact hσus ⟨g, hg⟩
    | ρ j =>
      rcases R_to_zv he' with ⟨⟨a, ha0⟩, rfl, ha⟩ | ⟨⟨a, ha0⟩, rfl, ha⟩ | ⟨rfl, hb⟩
      · cases q with
        | cons q e3 => exact (R_to_xv (OT.hom_down e3)).elim
        | nil =>
          change g ≫ amor Z p L s₀ u₁ u₂ r v s'' (xv j.castSucc) (zv j.succ) e.down =
            𝟙 _ ≫ amor Z p L s₀ u₁ u₂ r v s'' (xv ⟨a, ha0⟩) (zv j.succ) he' at hg
          rw [Category.id_comp, amor_ρ, amor_σ' ⟨a, ha0⟩ j.succ ha] at hg
          obtain ⟨j, hj⟩ := j
          simp only [Fin.val_succ] at ha hg
          subst ha
          try simp only [eqToHom_refl, Category.comp_id] at hg
          exact Z.peak₂ _ ⟨g, hg⟩
      · exact hne (congrArg OT.mk (congrArg xv (Fin.ext (by simp at ha ⊢; omega))))
      · simp at hb
    | s0 =>
      rcases R_to_zv he' with ⟨⟨a, ha0⟩, rfl, ha⟩ | ⟨⟨a, ha0⟩, rfl, ha⟩ | ⟨rfl, -⟩
      · simp only [Fin.val_zero] at ha
        subst ha
        cases q with
        | cons q e3 => exact (R_to_xv (OT.hom_down e3)).elim
        | nil =>
          change g ≫ amor Z p L s₀ u₁ u₂ r v s'' m0 (zv 0) e.down =
            𝟙 _ ≫ amor Z p L s₀ u₁ u₂ r v s'' (xv ⟨0, ha0⟩) (zv 0) he' at hg
          rw [Category.id_comp, amor_s0, amor_σ' ⟨0, ha0⟩ 0 rfl] at hg
          change g ≫ s₀ = Z.σ (p + 0) ≫ 𝟙 _ at hg
          rw [Category.comp_id] at hg
          exact hsσ ⟨g, hg⟩
      · simp at ha
      · exact hne rfl
    | rm =>
      rcases R_to_mv he' with ⟨⟨a, ha0⟩, rfl, ha⟩ | rfl
      · simp only at ha
        exact hne (congrArg OT.mk (congrArg xv (Fin.ext (by simp only [Fin.val_last]; omega))))
      · cases q with
        | cons q e3 => exact (R_to_xe (OT.hom_down e3)).elim
        | nil =>
          change g ≫ amor Z p L s₀ u₁ u₂ r v s'' (xv (Fin.last L)) mv e.down =
            𝟙 _ ≫ amor Z p L s₀ u₁ u₂ r v s'' xe mv he' at hg
          rw [Category.id_comp, amor_rm, amor_v1] at hg
          exact hrv ⟨g, hg⟩
    | v1 =>
      rcases R_to_mv he' with ⟨⟨a, ha0⟩, rfl, ha⟩ | rfl
      · simp only at ha
        have ha' : L = a := ha.symm
        subst ha'
        cases q with
        | cons q e3 => exact (R_to_xv (OT.hom_down e3)).elim
        | nil =>
          change g ≫ amor Z p L s₀ u₁ u₂ r v s'' xe mv e.down =
            𝟙 _ ≫ amor Z p L s₀ u₁ u₂ r v s'' (xv ⟨L, ha0⟩) mv he' at hg
          rw [Category.id_comp, amor_v1, amor_rmv] at hg
          exact hvr ⟨g, hg⟩
      · exact hne rfl
    | u1 => exact hne (congrArg OT.mk (R_to_m0 he').symm)
    | u2 => exact hne (congrArg OT.mk (R_to_e0 he').symm)
    | v2 => exact hne (congrArg OT.mk (R_to_ee he').symm)

end MulBasis

end RayQuiver

end LargeIndecomposable
