module

public import LargeIndecomposable.Cleaving.Zigzags.ZigzagArm
public import LargeIndecomposable.Cleaving.Zigzags.ZigzagFork2

/-!
# Zigzags with two arms: BO13a figure 9.4

The diagram: an arm `x₀ → M₀ → E₀` with `s₀ : M₀ → z p`; the zigzag `σ (p+j)`
(`j < L`), `ρ (p+j+1)` (`j < L`) from `z p` to `z (p+L)`; an arm `x (p+L+1) → M → E`
with `s' : M → z (p+L)`. It is an orientation of `D̃₂ₗ₊₆` (`RayCat.ZAA`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

/-- The vertices. -/
inductive ZAA (L : ℕ) : Type
  | zv (j : Fin (L + 1))
  | xv (j : Fin L)
  | m0
  | x0
  | e0
  | mv
  | xe
  | ee
  deriving DecidableEq

namespace ZAA

variable {L : ℕ}

instance : Fintype (ZAA L) where
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
inductive R : ZAA L → ZAA L → Prop
  | ρ (j : Fin L) : R (xv j) (zv j.succ)
  | σ (j : Fin L) : R (xv j) (zv j.castSucc)
  | s0 : R m0 (zv 0)
  | u1 : R x0 m0
  | u2 : R m0 e0
  | sm : R mv (zv (Fin.last L))
  | v1 : R xe mv
  | v2 : R mv ee

lemma R_asymm {u v : ZAA L} (h : R u v) : ¬R v u := by
  intro h'
  cases h <;> cases h'

lemma R_irrefl {u : ZAA L} (h : R u u) : False := by
  cases h

variable (L) in
/-- The graph. -/
def graph : SimpleGraph (ZAA L) := SimpleGraph.fromRel R

lemma adj_iff {u v : ZAA L} : (graph L).Adj u v ↔ R u v ∨ R v u := by
  rw [graph, SimpleGraph.fromRel_adj]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  rintro rfl
  rcases h with h | h <;> exact R_irrefl h

/-- The parent function towards `m0`. -/
def par : ZAA L → Option (ZAA L)
  | zv j => if h : j.val = 0 then some m0 else some (xv ⟨j.val - 1, by have := j.2; omega⟩)
  | xv j => some (zv j.castSucc)
  | m0 => none
  | x0 => some m0
  | e0 => some m0
  | mv => some (zv (Fin.last L))
  | xe => some mv
  | ee => some mv

/-- The height. -/
def ht : ZAA L → ℕ
  | zv j => 2 * j.val + 1
  | xv j => 2 * j.val + 2
  | m0 => 0
  | x0 => 1
  | e0 => 1
  | mv => 2 * L + 2
  | xe => 2 * L + 3
  | ee => 2 * L + 3

lemma par_of_R {u v : ZAA L} (h : R u v) : par u = some v ∨ par v = some u := by
  cases h with
  | ρ j =>
    right
    simp only [par, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, dite_false,
      Option.some.injEq, xv.injEq]
    ext
    simp
  | σ j => exact Or.inl rfl
  | s0 => exact Or.inr (by simp [par])
  | u1 => exact Or.inl rfl
  | u2 => exact Or.inr rfl
  | sm => exact Or.inl rfl
  | v1 => exact Or.inl rfl
  | v2 => exact Or.inr rfl

lemma R_of_par {u v : ZAA L} (h : par u = some v) : R u v ∨ R v u := by
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
      ext
      simp
      omega
  | xv j => simp only [par, Option.some.injEq] at h; subst h; exact Or.inl (R.σ j)
  | m0 => simp [par] at h
  | x0 => simp only [par, Option.some.injEq] at h; subst h; exact Or.inl R.u1
  | e0 => simp only [par, Option.some.injEq] at h; subst h; exact Or.inr R.u2
  | mv => simp only [par, Option.some.injEq] at h; subst h; exact Or.inl R.sm
  | xe => simp only [par, Option.some.injEq] at h; subst h; exact Or.inl R.v1
  | ee => simp only [par, Option.some.injEq] at h; subst h; exact Or.inr R.v2

lemma R_iff_par (u v : ZAA L) : R u v ∨ R v u ↔ par u = some v ∨ par v = some u := by
  constructor
  · rintro (h | h)
    · exact par_of_R h
    · exact (par_of_R h).symm
  · rintro (h | h)
    · exact R_of_par h
    · exact (R_of_par h).symm

lemma par_lt (u v : ZAA L) (h : par u = some v) : ht v < ht u := by
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

lemma R_ρ' {a : Fin L} {b : Fin (L + 1)} (h : b.val = a.val + 1) : R (xv a) (zv b) := by
  convert R.ρ a using 2
  ext; simp [h]

lemma R_σ' {a : Fin L} {b : Fin (L + 1)} (h : b.val = a.val) : R (xv a) (zv b) := by
  convert R.σ a using 2
  ext; simp [h]

open LargeIndecomposable.Foundations.Quiver in
/-- The vertex map of the copy of `D̃₂ₗ₊₆`. -/
def dmap : AffineD (2 * L + 2) → ZAA L
  | .spine a => if h0 : a.val = 0 then m0 else if hl : a.val = 2 * L + 2 then mv else
      if h : a.val % 2 = 1 then zv ⟨(a.val - 1) / 2, by have := a.isLt; omega⟩
      else xv ⟨a.val / 2 - 1, by have := a.isLt; omega⟩
  | .leaf i => if i.val = 0 then x0 else if i.val = 1 then e0 else if i.val = 2 then xe else ee

open LargeIndecomposable.Foundations.Quiver in
lemma dmap_adj_of_hom (a b : AffineD (2 * L + 2)) (e : Nonempty (a ⟶ b)) :
    (graph L).Adj (dmap a) (dmap b) := by
  rw [adj_iff]
  rcases a with i | j <;> rcases b with i' | j'
  · exact absurd e (AffineD.not_nonempty_hom_leaf _ _)
  · have hj := (AffineD.nonempty_leaf_spine_iff i j').1 e
    by_cases hi : i.val < 2
    · rw [AffineD.leafTarget_of_lt_two i hi] at hj
      subst hj
      simp only [dmap, Fin.val_zero, dite_true]
      by_cases h0 : i.val = 0
      · rw [ite_eq_left h0]; exact Or.inl R.u1
      · rw [ite_eq_right h0, ite_eq_left (by omega)]; exact Or.inr R.u2
    · rw [AffineD.leafTarget_of_not_lt_two i hi] at hj
      subst hj
      have h0 : ¬(Fin.last (2 * L + 2)).val = 0 := by simp
      simp only [dmap, h0, dite_false, Fin.val_last, dite_true]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      by_cases h2 : i.val = 2
      · rw [ite_eq_left h2]; exact Or.inl R.v1
      · rw [ite_eq_right h2]; exact Or.inr R.v2
  · exact absurd e (AffineD.not_nonempty_hom_leaf _ _)
  · have hj := (AffineD.nonempty_spine_spine_iff j j').1 e
    have hj0 : ¬j'.val = 0 := by omega
    have hjl : j.val ≠ 2 * L + 2 := by have := j'.2; omega
    by_cases h0 : j.val = 0
    · left
      have hl : ¬j'.val = 2 * L + 2 := by omega
      have hod : j'.val % 2 = 1 := by omega
      simp only [dmap, h0, dite_true, hj0, hl, hod, dite_false]
      have e : (⟨(j'.val - 1) / 2, by omega⟩ : Fin (L + 1)) = 0 := Fin.ext (by simp; omega)
      rw [e]
      exact R.s0
    · by_cases hlast : j'.val = 2 * L + 2
      · right
        have hod : j.val % 2 = 1 := by omega
        simp only [dmap, h0, hjl, hod, dite_false, dite_true, hj0, hlast]
        have e : (⟨(j.val - 1) / 2, by omega⟩ : Fin (L + 1)) = Fin.last L := Fin.ext (by simp; omega)
        rw [e]
        exact R.sm
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
/-- The copy of `D̃₂ₗ₊₆`. -/
def dcopy : (underlyingGraph (AffineD (2 * L + 2))).Copy (graph L) where
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

lemma zx_val {a : Fin L} {b : Fin (L + 1)} (h : R (xv a) (zv b)) (hab : ¬b.val = a.val) :
    b.val = a.val + 1 := by
  cases h with
  | ρ j => simp
  | σ j => exact absurd rfl hab

lemma m0_val {b : Fin (L + 1)} (h : R m0 (zv b)) : b.val = 0 := by cases h; rfl

lemma mv_val {b : Fin (L + 1)} (h : R mv (zv b)) : b.val = L := by cases h; rfl

lemma R_xv {a : Fin L} {w : ZAA L} (h : R (xv a) w) :
    (∃ b : Fin (L + 1), w = zv b ∧ b.val = a.val + 1) ∨ ∃ b : Fin (L + 1), w = zv b ∧ b.val = a.val := by
  generalize hu : xv a = u at h
  cases h with
  | ρ j => cases hu; exact Or.inl ⟨_, rfl, by simp⟩
  | σ j => cases hu; exact Or.inr ⟨_, rfl, by simp⟩
  | s0 => cases hu
  | u1 => cases hu
  | u2 => cases hu
  | sm => cases hu
  | v1 => cases hu
  | v2 => cases hu

lemma R_m0 {w : ZAA L} (h : R m0 w) : (∃ b : Fin (L + 1), w = zv b ∧ b.val = 0) ∨ w = e0 := by
  cases h with
  | s0 => exact Or.inl ⟨_, rfl, rfl⟩
  | u2 => exact Or.inr rfl

lemma R_mv {w : ZAA L} (h : R mv w) : (∃ b : Fin (L + 1), w = zv b ∧ b.val = L) ∨ w = ee := by
  cases h with
  | sm => exact Or.inl ⟨_, rfl, rfl⟩
  | v2 => exact Or.inr rfl

lemma R_x0 {w : ZAA L} (h : R x0 w) : w = m0 := by cases h; rfl

lemma R_xe {w : ZAA L} (h : R xe w) : w = mv := by cases h; rfl

lemma R_to_zv {u : ZAA L} {b : Fin (L + 1)} (h : R u (zv b)) :
    (∃ a : Fin L, u = xv a ∧ b.val = a.val + 1) ∨ (∃ a : Fin L, u = xv a ∧ b.val = a.val) ∨
      (u = m0 ∧ b.val = 0) ∨ (u = mv ∧ b.val = L) := by
  generalize hw : zv b = w at h
  cases h with
  | ρ j => cases hw; exact Or.inl ⟨_, rfl, by simp⟩
  | σ j => cases hw; exact Or.inr (Or.inl ⟨_, rfl, by simp⟩)
  | s0 => cases hw; exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  | sm => cases hw; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  | u1 => cases hw
  | u2 => cases hw
  | v1 => cases hw
  | v2 => cases hw

lemma R_to_m0 {u : ZAA L} (h : R u m0) : u = x0 := by cases h; rfl

lemma R_to_mv {u : ZAA L} (h : R u mv) : u = xe := by cases h; rfl

lemma R_to_e0 {u : ZAA L} (h : R u e0) : u = m0 := by cases h; rfl

lemma R_to_ee {u : ZAA L} (h : R u ee) : u = mv := by cases h; rfl

lemma R_to_xv {u : ZAA L} {a : Fin L} (h : R u (xv a)) : False := by cases h

lemma R_to_x0 {u : ZAA L} (h : R u x0) : False := by cases h

lemma R_to_xe {u : ZAA L} (h : R u xe) : False := by cases h

lemma mid {u b w : ZAA L} (h1 : R u b) (h2 : R b w) : (b = m0 ∧ u = x0) ∨ (b = mv ∧ u = xe) := by
  cases h1 <;> cases h2
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

variable {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] (Z : ZChain Q) (p L : ℕ)
  (M₀ X₀ E₀ M E : Q)

/-- The objects. -/
def aobj : ZAA L → Q
  | zv j => Z.z (p + j.val)
  | xv j => Z.x (p + j.val + 1)
  | m0 => M₀
  | x0 => X₀
  | e0 => E₀
  | mv => M
  | xe => Z.x (p + L + 1)
  | ee => E

variable {M₀ X₀ E₀ M E} (s₀ : M₀ ⟶ Z.z p) (u₁ : X₀ ⟶ M₀) (u₂ : M₀ ⟶ E₀)
  (s' : M ⟶ Z.z (p + L)) (v₁ : Z.x (p + L + 1) ⟶ M) (v₂ : M ⟶ E)

/-- The morphisms. -/
def amor : ∀ u w : ZAA L, R u w → (aobj Z p L M₀ X₀ E₀ M E u ⟶ aobj Z p L M₀ X₀ E₀ M E w)
  | xv a, zv b, h =>
    if hab : b.val = a.val then
      Z.σ (p + a.val) ≫ eqToHom (congrArg (fun t ↦ Z.z (p + t)) hab.symm)
    else Z.ρ (p + a.val + 1) ≫ eqToHom (congrArg (fun t ↦ Z.z (p + t)) (zx_val h hab).symm)
  | m0, zv b, h => s₀ ≫ eqToHom (congrArg (fun t ↦ Z.z (p + t)) (m0_val h).symm)
  | m0, e0, _ => u₂
  | x0, m0, _ => u₁
  | mv, zv b, h => s' ≫ eqToHom (congrArg (fun t ↦ Z.z (p + t)) (mv_val h).symm)
  | mv, ee, _ => v₂
  | xe, mv, _ => v₁
  | xv _, xv _, h | xv _, m0, h | xv _, x0, h | xv _, e0, h | xv _, mv, h | xv _, xe, h
  | xv _, ee, h => absurd h (by intro h; cases h)
  | zv _, _, h | e0, _, h | ee, _, h => absurd h (by intro h; cases h)
  | m0, xv _, h | m0, m0, h | m0, x0, h | m0, mv, h | m0, xe, h | m0, ee, h =>
    absurd h (by intro h; cases h)
  | x0, zv _, h | x0, xv _, h | x0, x0, h | x0, e0, h | x0, mv, h | x0, xe, h | x0, ee, h =>
    absurd h (by intro h; cases h)
  | mv, xv _, h | mv, m0, h | mv, x0, h | mv, e0, h | mv, mv, h | mv, xe, h =>
    absurd h (by intro h; cases h)
  | xe, zv _, h | xe, xv _, h | xe, m0, h | xe, x0, h | xe, e0, h | xe, xe, h | xe, ee, h =>
    absurd h (by intro h; cases h)

variable {Z p L s₀ u₁ u₂ s' v₁ v₂}

lemma amor_σ' (a : Fin L) (b : Fin (L + 1)) (hab : b.val = a.val) (h) :
    amor Z p L s₀ u₁ u₂ s' v₁ v₂ (xv a) (zv b) h =
      Z.σ (p + a.val) ≫ eqToHom (congrArg (fun t ↦ Z.z (p + t)) hab.symm) := by
  simp only [amor, hab, dite_true]
  rfl

lemma amor_ρ' (a : Fin L) (b : Fin (L + 1)) (hab : b.val = a.val + 1) (h) :
    amor Z p L s₀ u₁ u₂ s' v₁ v₂ (xv a) (zv b) h =
      Z.ρ (p + a.val + 1) ≫ eqToHom (congrArg (fun t ↦ Z.z (p + t)) hab.symm) := by
  have : ¬b.val = a.val := by omega
  simp only [amor, this, dite_false]
  rfl

lemma amor_s0' (b : Fin (L + 1)) (hb : b.val = 0) (h) :
    amor Z p L s₀ u₁ u₂ s' v₁ v₂ m0 (zv b) h =
      s₀ ≫ eqToHom (congrArg (fun t ↦ Z.z (p + t)) hb.symm) := rfl

lemma amor_sm' (b : Fin (L + 1)) (hb : b.val = L) (h) :
    amor Z p L s₀ u₁ u₂ s' v₁ v₂ mv (zv b) h =
      s' ≫ eqToHom (congrArg (fun t ↦ Z.z (p + t)) hb.symm) := rfl

lemma amor_s0 (h) : amor Z p L s₀ u₁ u₂ s' v₁ v₂ m0 (zv 0) h = s₀ := Category.comp_id _

lemma amor_sm (h) : amor Z p L s₀ u₁ u₂ s' v₁ v₂ mv (zv (Fin.last L)) h = s' :=
  Category.comp_id _

lemma amor_σ (j : Fin L) (h) : amor Z p L s₀ u₁ u₂ s' v₁ v₂ (xv j) (zv j.castSucc) h =
    Z.σ (p + j.val) := by
  rw [amor_σ' j j.castSucc (by simp)]
  exact Category.comp_id _

lemma amor_ρ (j : Fin L) (h) : amor Z p L s₀ u₁ u₂ s' v₁ v₂ (xv j) (zv j.succ) h =
    Z.ρ (p + j.val + 1) := by
  rw [amor_ρ' j j.succ (by simp)]
  exact Category.comp_id _

lemma amor_u1 (h) : amor Z p L s₀ u₁ u₂ s' v₁ v₂ x0 m0 h = u₁ := rfl

lemma amor_u2 (h) : amor Z p L s₀ u₁ u₂ s' v₁ v₂ m0 e0 h = u₂ := rfl

lemma amor_v1 (h) : amor Z p L s₀ u₁ u₂ s' v₁ v₂ xe mv h = v₁ := rfl

lemma amor_v2 (h) : amor Z p L s₀ u₁ u₂ s' v₁ v₂ mv ee h = v₂ := rfl

end ZAA

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

open ZAA in
include B in
/-- **No zigzag with two arms in `P/τ`** (BO13a figure 9.4). -/
theorem not_zigzag_arms
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) (Z : ZChain P) (p L : ℕ) (hL1 : 1 ≤ L) {M₀ X₀ E₀ M E : P}
    (s₀ : M₀ ⟶ Z.z p) (u₁ : X₀ ⟶ M₀) (u₂ : M₀ ⟶ E₀)
    (s' : M ⟶ Z.z (p + L)) (v₁ : Z.x (p + L + 1) ⟶ M) (v₂ : M ⟶ E)
    (hρ : ∀ j < L, ¬FactorsThroughMorphism τ (Z.ρ (p + j + 1)))
    (hσ : ∀ j < L, ¬FactorsThroughMorphism τ (Z.σ (p + j)))
    (hs₀ : ¬FactorsThroughMorphism τ s₀) (hu₁ : ¬FactorsThroughMorphism τ u₁)
    (hu₂ : ¬FactorsThroughMorphism τ u₂) (hu₁₂ : ¬FactorsThroughMorphism τ (u₁ ≫ u₂))
    (hu₁s : ¬FactorsThroughMorphism τ (u₁ ≫ s₀))
    (hs : ¬FactorsThroughMorphism τ s') (hv₁ : ¬FactorsThroughMorphism τ v₁)
    (hv₂ : ¬FactorsThroughMorphism τ v₂) (hv₁₂ : ¬FactorsThroughMorphism τ (v₁ ≫ v₂))
    (hv₁s : ¬FactorsThroughMorphism τ (v₁ ≫ s'))
    (his₀ : ¬IsIso s₀) (hiu₁ : ¬IsIso u₁) (hiu₂ : ¬IsIso u₂) (his : ¬IsIso s')
    (hiv₁ : ¬IsIso v₁) (hiv₂ : ¬IsIso v₂)
    (hsu : ¬∃ g, s₀ ≫ g = u₂) (hus : ¬∃ g, u₂ ≫ g = s₀)
    (hsv : ¬∃ g, s' ≫ g = v₂) (hvs : ¬∃ g, v₂ ≫ g = s')
    (hσs : ¬∃ g, g ≫ Z.σ p = s₀) (hσus : ¬∃ g, g ≫ Z.σ p = u₁ ≫ s₀)
    (hsσ : ¬∃ g, g ≫ s₀ = Z.σ p)
    (hρs : ¬∃ g, g ≫ Z.ρ (p + L) = s') (hρvs : ¬∃ g, g ≫ Z.ρ (p + L) = v₁ ≫ s')
    (hsρ : ¬∃ g, g ≫ s' = Z.ρ (p + L)) : False := by
  have ho : ∀ u v, R u v → (graph L).Adj u v := fun u v h ↦ adj_iff.2 (Or.inl h)
  haveI : Fact (LargeIndecomposable.Foundations.Quiver.IsAcyclic (OT (graph L) R)) :=
    ⟨OT.isAcyclic ho (fun _ _ h ↦ R_asymm h) isAcyclic⟩
  let φ : OT (graph L) R ⥤q P :=
    { obj := fun u ↦ aobj Z p L M₀ X₀ E₀ M E u.as
      map := fun {u w} e ↦ amor Z p L s₀ u₁ u₂ s' v₁ v₂ u.as w.as (OT.hom_down e) }
  have harr : ∀ u w (h : R u w), ¬FactorsThroughMorphism τ (amor Z p L s₀ u₁ u₂ s' v₁ v₂ u w h) ∧
      ¬IsIso (amor Z p L s₀ u₁ u₂ s' v₁ v₂ u w h) := by
    intro u w h
    cases h with
    | ρ j =>
      rw [amor_ρ]
      exact ⟨hρ j j.2, Z.ρ_not_isIso _⟩
    | σ j =>
      rw [amor_σ]
      exact ⟨hσ j j.2, Z.σ_not_isIso _⟩
    | s0 => rw [amor_s0]; exact ⟨hs₀, his₀⟩
    | u1 => exact ⟨hu₁, hiu₁⟩
    | u2 => exact ⟨hu₂, hiu₂⟩
    | sm => rw [amor_sm]; exact ⟨hs, his⟩
    | v1 => exact ⟨hv₁, hiv₁⟩
    | v2 => exact ⟨hv₂, hiv₂⟩
  refine B.not_ot_diagram hmin hL hR τ hτ hτ0 (graph L) R ho (fun _ _ h ↦ R_asymm h) isAcyclic
    (OT.not_isRepresentationFinite_affineD ho (fun _ _ h ↦ adj_iff.1 h) k (2 * L + 2) dcopy) φ
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
        change ¬FactorsThroughMorphism τ (𝟙 _ ≫ amor Z p L s₀ u₁ u₂ s' v₁ v₂ u w he)
        rw [Category.id_comp]
        exact (harr u w he).1
      | cons q e' =>
        rename_i w2
        rcases w2 with ⟨w2⟩
        have he' := OT.hom_down e'
        rcases mid he' he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · cases q with
          | nil =>
            change ¬FactorsThroughMorphism τ ((𝟙 _ ≫ amor Z p L s₀ u₁ u₂ s' v₁ v₂ x0 m0 he') ≫
              amor Z p L s₀ u₁ u₂ s' v₁ v₂ m0 w he)
            rw [Category.id_comp, amor_u1]
            rcases R_m0 he with ⟨⟨c, hc0⟩, rfl, hc⟩ | rfl
            · simp only at hc
              subst hc
              rw [amor_s0' ⟨0, hc0⟩ rfl, ZChain.comp_eqToHom_self]
              exact hu₁s
            · rw [amor_u2]; exact hu₁₂
          | cons q e'' => exact (R_to_x0 (OT.hom_down e'')).elim
        · cases q with
          | nil =>
            change ¬FactorsThroughMorphism τ ((𝟙 _ ≫ amor Z p L s₀ u₁ u₂ s' v₁ v₂ xe mv he') ≫
              amor Z p L s₀ u₁ u₂ s' v₁ v₂ mv w he)
            rw [Category.id_comp, amor_v1]
            rcases R_mv he with ⟨⟨c, hc0⟩, rfl, hc⟩ | rfl
            · simp only at hc
              subst hc
              rw [amor_sm' ⟨c, hc0⟩ rfl, ZChain.comp_eqToHom_self]
              exact hv₁s
            · rw [amor_v2]; exact hv₁₂
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
      exfalso
      obtain ⟨d, f, -, -, -⟩ :=
        Quiver.Path.eq_toPath_comp_of_length_eq_succ (q.cons e2) (n := q.length) (by simp)
      rcases mid he' (OT.hom_down f) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hne (congrArg OT.mk (R_x0 he))
      · exact hne (congrArg OT.mk (R_xe he))
    | nil =>
      change amor Z p L s₀ u₁ u₂ s' v₁ v₂ u c he ≫ g = 𝟙 _ ≫ amor Z p L s₀ u₁ u₂ s' v₁ v₂ u c' he'
        at hg
      rw [Category.id_comp] at hg
      cases he with
      | ρ j =>
        rw [amor_ρ] at hg
        rcases R_xv he' with ⟨⟨b, hb0⟩, rfl, hb⟩ | ⟨⟨b, hb0⟩, rfl, hb⟩ <;>
          simp only at hb <;> subst hb
        · exact hne (congrArg OT.mk (congrArg zv (Fin.ext (by simp))))
        · rw [amor_σ' j ⟨j.val, hb0⟩ rfl, ZChain.comp_eqToHom_self] at hg
          exact Z.valley₂ (p + j.val) ⟨g, hg⟩
      | σ j =>
        rw [amor_σ] at hg
        rcases R_xv he' with ⟨⟨b, hb0⟩, rfl, hb⟩ | ⟨⟨b, hb0⟩, rfl, hb⟩ <;>
          simp only at hb <;> subst hb
        · rw [amor_ρ' j ⟨j.val + 1, hb0⟩ rfl, ZChain.comp_eqToHom_self] at hg
          exact Z.valley₁ (p + j.val) ⟨g, hg⟩
        · exact hne (congrArg OT.mk (congrArg zv (Fin.ext (by simp))))
      | s0 =>
        rw [amor_s0] at hg
        rcases R_m0 he' with ⟨⟨b, hb0⟩, rfl, hb⟩ | rfl
        · simp only at hb
          subst hb
          exact hne rfl
        · rw [amor_u2] at hg
          exact hsu ⟨g, hg⟩
      | u2 =>
        rw [amor_u2] at hg
        rcases R_m0 he' with ⟨⟨b, hb0⟩, rfl, hb⟩ | rfl
        · simp only at hb
          subst hb
          rw [amor_s0' ⟨0, hb0⟩ rfl, ZChain.comp_eqToHom_self] at hg
          exact hus ⟨g, hg⟩
        · exact hne rfl
      | u1 => exact hne (congrArg OT.mk (R_x0 he').symm)
      | sm =>
        rw [amor_sm] at hg
        rcases R_mv he' with ⟨⟨b, hb0⟩, rfl, hb⟩ | rfl
        · simp only at hb
          subst hb
          exact hne rfl
        · rw [amor_v2] at hg
          exact hsv ⟨g, hg⟩
      | v2 =>
        rw [amor_v2] at hg
        rcases R_mv he' with ⟨⟨b, hb0⟩, rfl, hb⟩ | rfl
        · simp only at hb
          subst hb
          rw [amor_sm' ⟨b, hb0⟩ rfl, ZChain.comp_eqToHom_self] at hg
          exact hvs ⟨g, hg⟩
        · exact hne rfl
      | v1 => exact hne (congrArg OT.mk (R_xe he').symm)
  · intro u c c' w e e' q hne ⟨g, hg⟩
    rcases u with ⟨u⟩
    rcases c with ⟨c⟩
    rcases c' with ⟨c'⟩
    rcases w with ⟨w⟩
    have he := OT.hom_down e
    have he' := OT.hom_down e'
    cases he with
    | ρ j =>
      rcases R_to_zv he' with ⟨⟨a, ha0⟩, rfl, ha⟩ | ⟨⟨a, ha0⟩, rfl, ha⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩
      · simp only [Fin.val_succ] at ha
        exact hne (congrArg OT.mk (congrArg xv (Fin.ext (by simp; omega))))
      · simp only [Fin.val_succ] at ha
        cases q with
        | cons q e3 => exact (R_to_xv (OT.hom_down e3)).elim
        | nil =>
          change g ≫ amor Z p L s₀ u₁ u₂ s' v₁ v₂ (xv j) (zv j.succ) e.down =
            𝟙 _ ≫ amor Z p L s₀ u₁ u₂ s' v₁ v₂ (xv ⟨a, ha0⟩) (zv j.succ) he' at hg
          rw [Category.id_comp, amor_ρ j, amor_σ' ⟨a, ha0⟩ j.succ ha] at hg
          subst ha
          try simp only [eqToHom_refl, Category.comp_id] at hg
          exact Z.peak₂ (p + j.val + 1) ⟨g, hg⟩
      · simp at hb
      · cases q with
        | nil =>
          change g ≫ amor Z p L s₀ u₁ u₂ s' v₁ v₂ (xv j) (zv j.succ) e.down =
            𝟙 _ ≫ amor Z p L s₀ u₁ u₂ s' v₁ v₂ mv (zv j.succ) he' at hg
          rw [Category.id_comp, amor_ρ j, amor_sm' j.succ hb] at hg
          obtain ⟨j, hj⟩ := j
          simp only [Fin.val_succ] at hb hg
          subst hb
          try simp only [eqToHom_refl, Category.comp_id] at hg
          exact hρs ⟨g, hg⟩
        | cons q e3 =>
          rename_i w3
          rcases w3 with ⟨w3⟩
          obtain rfl := R_to_mv (OT.hom_down e3)
          cases q with
          | cons q e4 => exact (R_to_xe (OT.hom_down e4)).elim
          | nil =>
            change g ≫ amor Z p L s₀ u₁ u₂ s' v₁ v₂ (xv j) (zv j.succ) e.down =
              (𝟙 _ ≫ amor Z p L s₀ u₁ u₂ s' v₁ v₂ xe mv (OT.hom_down e3)) ≫
                amor Z p L s₀ u₁ u₂ s' v₁ v₂ mv (zv j.succ) he' at hg
            rw [Category.id_comp, amor_ρ j, amor_v1, amor_sm' j.succ hb] at hg
            obtain ⟨j, hj⟩ := j
            simp only [Fin.val_succ] at hb hg
            subst hb
            try simp only [eqToHom_refl, Category.comp_id] at hg
            exact hρvs ⟨g, hg⟩
    | σ j =>
      rcases R_to_zv he' with ⟨⟨a, ha0⟩, rfl, ha⟩ | ⟨⟨a, ha0⟩, rfl, ha⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩
      · simp only [Fin.val_castSucc] at ha
        cases q with
        | cons q e3 => exact (R_to_xv (OT.hom_down e3)).elim
        | nil =>
          change g ≫ amor Z p L s₀ u₁ u₂ s' v₁ v₂ (xv j) (zv j.castSucc) e.down =
            𝟙 _ ≫ amor Z p L s₀ u₁ u₂ s' v₁ v₂ (xv ⟨a, ha0⟩) (zv j.castSucc) he' at hg
          rw [Category.id_comp, amor_σ j,
            amor_ρ' ⟨a, ha0⟩ j.castSucc ha] at hg
          try simp only [eqToHom_refl, Category.comp_id] at hg
          obtain ⟨j, hj⟩ := j
          simp only [Fin.val_castSucc] at ha hg
          subst ha
          try simp only [eqToHom_refl, Category.comp_id] at hg
          exact Z.peak₁ (p + (a + 1)) ⟨g, hg⟩
      · simp only [Fin.val_castSucc] at ha
        exact hne (congrArg OT.mk (congrArg xv (Fin.ext (by simp [ha]))))
      · simp only [Fin.val_castSucc] at hb
        cases q with
        | nil =>
          change g ≫ amor Z p L s₀ u₁ u₂ s' v₁ v₂ (xv j) (zv j.castSucc) e.down =
            𝟙 _ ≫ amor Z p L s₀ u₁ u₂ s' v₁ v₂ m0 (zv j.castSucc) he' at hg
          rw [Category.id_comp, amor_σ j, amor_s0' j.castSucc
            (by simp [hb])] at hg
          obtain ⟨j, hj⟩ := j
          simp only at hb
          subst hb
          try simp only [eqToHom_refl, Category.comp_id] at hg
          exact hσs ⟨g, hg⟩
        | cons q e3 =>
          rename_i w3
          rcases w3 with ⟨w3⟩
          obtain rfl := R_to_m0 (OT.hom_down e3)
          cases q with
          | cons q e4 => exact (R_to_x0 (OT.hom_down e4)).elim
          | nil =>
            change g ≫ amor Z p L s₀ u₁ u₂ s' v₁ v₂ (xv j) (zv j.castSucc) e.down =
              (𝟙 _ ≫ amor Z p L s₀ u₁ u₂ s' v₁ v₂ x0 m0 (OT.hom_down e3)) ≫
                amor Z p L s₀ u₁ u₂ s' v₁ v₂ m0 (zv j.castSucc) he' at hg
            rw [Category.id_comp, amor_σ j, amor_u1,
              amor_s0' j.castSucc (by simp [hb])] at hg
            obtain ⟨j, hj⟩ := j
            simp only at hb
            subst hb
            try simp only [eqToHom_refl, Category.comp_id] at hg
            exact hσus ⟨g, hg⟩
      · simp only [Fin.val_castSucc] at hb
        have := j.2
        omega
    | s0 =>
      rcases R_to_zv he' with ⟨⟨a, ha0⟩, rfl, ha⟩ | ⟨⟨a, ha0⟩, rfl, ha⟩ | ⟨rfl, -⟩ | ⟨rfl, hb⟩
      · simp at ha
      · simp only [Fin.val_zero] at ha
        subst ha
        cases q with
        | cons q e3 => exact (R_to_xv (OT.hom_down e3)).elim
        | nil =>
          change g ≫ amor Z p L s₀ u₁ u₂ s' v₁ v₂ m0 (zv 0) e.down =
            𝟙 _ ≫ amor Z p L s₀ u₁ u₂ s' v₁ v₂ (xv ⟨0, ha0⟩) (zv 0) he' at hg
          rw [Category.id_comp, amor_s0, amor_σ' ⟨0, ha0⟩ 0 rfl] at hg
          change g ≫ s₀ = Z.σ (p + 0) ≫ 𝟙 _ at hg
          rw [Category.comp_id] at hg
          exact hsσ ⟨g, hg⟩
      · exact hne rfl
      · simp at hb; omega
    | sm =>
      rcases R_to_zv he' with ⟨⟨a, ha0⟩, rfl, ha⟩ | ⟨⟨a, ha0⟩, rfl, ha⟩ | ⟨rfl, hb⟩ | ⟨rfl, -⟩
      · cases q with
        | cons q e3 => exact (R_to_xv (OT.hom_down e3)).elim
        | nil =>
          change g ≫ amor Z p L s₀ u₁ u₂ s' v₁ v₂ mv (zv (Fin.last L)) e.down =
            𝟙 _ ≫ amor Z p L s₀ u₁ u₂ s' v₁ v₂ (xv ⟨a, ha0⟩) (zv (Fin.last L)) he' at hg
          rw [Category.id_comp, amor_sm, amor_ρ' ⟨a, ha0⟩ (Fin.last L) ha] at hg
          simp only [Fin.val_last] at ha hg
          subst ha
          try simp only [eqToHom_refl, Category.comp_id] at hg
          exact hsρ ⟨g, hg⟩
      · simp only [Fin.val_last] at ha
        omega
      · simp at hb; omega
      · exact hne rfl
    | u1 => exact hne (congrArg OT.mk (R_to_m0 he').symm)
    | u2 => exact hne (congrArg OT.mk (R_to_e0 he').symm)
    | v1 => exact hne (congrArg OT.mk (R_to_mv he').symm)
    | v2 => exact hne (congrArg OT.mk (R_to_ee he').symm)

end MulBasis

end RayQuiver

end LargeIndecomposable
