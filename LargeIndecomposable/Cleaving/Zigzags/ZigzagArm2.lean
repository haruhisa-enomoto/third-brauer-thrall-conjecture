module

public import LargeIndecomposable.Cleaving.Zigzags.ZigzagArm

/-!
# Zigzags with a fork and an arm at a source: BO13a figure 5.4

The diagram: two forks out of `x p`; the zigzag `ρ (p+j)`, `σ (p+j)`
(`j ≤ L`) ending at the source `x (p+L+1)`; `r : x (p+L+1) → M`; and two
leaves at `M`: `v : X'' → M` and `s'' : M → E`. It is an orientation of
`D̃₂ₗ₊₇` (`RayCat.ZB`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

/-- The vertices. -/
inductive ZB (L : ℕ) : Type
  | xv (j : Fin (L + 2))
  | zv (j : Fin (L + 1))
  | mv
  | xe
  | ee
  | lf (i : Fin 2)
  deriving DecidableEq

namespace ZB

variable {L : ℕ}

instance : Fintype (ZB L) where
  elems := (Finset.univ.map ⟨xv, fun _ _ h ↦ by cases h; rfl⟩) ∪
    (Finset.univ.map ⟨zv, fun _ _ h ↦ by cases h; rfl⟩) ∪ {mv, xe, ee} ∪
    (Finset.univ.map ⟨lf, fun _ _ h ↦ by cases h; rfl⟩)
  complete v := by
    cases v
    · simp only [Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and]
      exact Or.inl (Or.inl (Or.inl ⟨_, rfl⟩))
    · simp only [Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and]
      exact Or.inl (Or.inl (Or.inr ⟨_, rfl⟩))
    · simp
    · simp
    · simp
    · simp only [Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and]
      exact Or.inr ⟨_, rfl⟩

/-- The arrows. -/
inductive R : ZB L → ZB L → Prop
  | ρ (j : Fin (L + 1)) : R (xv j.castSucc) (zv j)
  | σ (j : Fin (L + 1)) : R (xv j.succ) (zv j)
  | r : R (xv (Fin.last _)) mv
  | v1 : R xe mv
  | v2 : R mv ee
  | a (i : Fin 2) : R (xv 0) (lf i)

lemma R_asymm {u v : ZB L} (h : R u v) : ¬R v u := by
  intro h'
  cases h <;> cases h'

lemma R_irrefl {u : ZB L} (h : R u u) : False := by
  cases h

variable (L) in
/-- The graph. -/
def graph : SimpleGraph (ZB L) := SimpleGraph.fromRel R

lemma adj_iff {u v : ZB L} : (graph L).Adj u v ↔ R u v ∨ R v u := by
  rw [graph, SimpleGraph.fromRel_adj]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  rintro rfl
  rcases h with h | h <;> exact R_irrefl h

/-- The parent function towards `xv 0`. -/
def par : ZB L → Option (ZB L)
  | xv j => if h : j.val = 0 then none else some (zv ⟨j.val - 1, by omega⟩)
  | zv j => some (xv j.castSucc)
  | mv => some (xv (Fin.last _))
  | xe => some mv
  | ee => some mv
  | lf _ => some (xv 0)

/-- The height. -/
def ht : ZB L → ℕ
  | xv j => 2 * j.val
  | zv j => 2 * j.val + 1
  | mv => 2 * L + 3
  | xe => 2 * L + 4
  | ee => 2 * L + 4
  | lf _ => 1

lemma par_of_R {u v : ZB L} (h : R u v) : par u = some v ∨ par v = some u := by
  cases h with
  | ρ j => exact Or.inr (by simp [par])
  | σ j =>
    left
    simp only [par, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, dite_false,
      Option.some.injEq, zv.injEq]
    ext
    simp
  | r => exact Or.inr rfl
  | v1 => exact Or.inl rfl
  | v2 => exact Or.inr rfl
  | a i => exact Or.inr rfl

lemma R_of_par {u v : ZB L} (h : par u = some v) : R u v ∨ R v u := by
  cases u with
  | xv j =>
    simp only [par] at h
    split_ifs at h with h1
    simp only [Option.some.injEq] at h
    subst h
    left
    have hj : j.val - 1 < L + 1 := by have := j.2; omega
    convert R.σ (L := L) ⟨j.val - 1, hj⟩ using 2
    · ext
      simp
      omega
  | zv j => simp only [par, Option.some.injEq] at h; subst h; exact Or.inr (R.ρ j)
  | mv => simp only [par, Option.some.injEq] at h; subst h; exact Or.inr R.r
  | xe => simp only [par, Option.some.injEq] at h; subst h; exact Or.inl R.v1
  | ee => simp only [par, Option.some.injEq] at h; subst h; exact Or.inr R.v2
  | lf i => simp only [par, Option.some.injEq] at h; subst h; exact Or.inr (R.a i)

lemma R_iff_par (u v : ZB L) : R u v ∨ R v u ↔ par u = some v ∨ par v = some u := by
  constructor
  · rintro (h | h)
    · exact par_of_R h
    · exact (par_of_R h).symm
  · rintro (h | h)
    · exact R_of_par h
    · exact (R_of_par h).symm

lemma par_lt (u v : ZB L) (h : par u = some v) : ht v < ht u := by
  cases u with
  | xv j =>
    simp only [par] at h
    split_ifs at h with h1
    simp only [Option.some.injEq] at h
    subst h
    simp only [ht]
    omega
  | zv j => simp only [par, Option.some.injEq] at h; subst h; simp [ht]
  | mv => simp only [par, Option.some.injEq] at h; subst h; simp [ht]; omega
  | xe => simp only [par, Option.some.injEq] at h; subst h; simp [ht]
  | ee => simp only [par, Option.some.injEq] at h; subst h; simp [ht]
  | lf i => simp only [par, Option.some.injEq] at h; subst h; simp [ht]

lemma isAcyclic : (graph L).IsAcyclic :=
  isAcyclic_of_parent (graph L) par ht (fun u v ↦ by rw [adj_iff, R_iff_par]) par_lt

lemma R_ρ' {a : Fin (L + 2)} {b : Fin (L + 1)} (h : a.val = b.val) : R (xv a) (zv b) := by
  obtain rfl : a = b.castSucc := Fin.ext h
  exact R.ρ b

lemma R_σ' {a : Fin (L + 2)} {b : Fin (L + 1)} (h : a.val = b.val + 1) : R (xv a) (zv b) := by
  obtain rfl : a = b.succ := Fin.ext h
  exact R.σ b

lemma R_a' {a : Fin (L + 2)} (h : a.val = 0) (i : Fin 2) : R (xv a) (lf i) := by
  obtain rfl : a = 0 := Fin.ext h
  exact R.a i

lemma R_r' {a : Fin (L + 2)} (h : a.val = L + 1) : R (xv a) mv := by
  obtain rfl : a = Fin.last _ := Fin.ext h
  exact R.r

open LargeIndecomposable.Foundations.Quiver in
/-- The vertex map of the copy of `D̃₂ₗ₊₇`. -/
def dmap : AffineD (2 * L + 3) → ZB L
  | .spine a => if h0 : a.val = 2 * L + 3 then mv else
      if h : a.val % 2 = 0 then xv ⟨a.val / 2, by have := a.isLt; omega⟩
      else zv ⟨a.val / 2, by have := a.isLt; omega⟩
  | .leaf i => if h : i.val < 2 then lf ⟨i.val, h⟩ else if i.val = 2 then xe else ee

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
      right
      have h0 : ¬(0 : ℕ) = 2 * L + 3 := by omega
      simp only [dmap, hi, dite_true, Fin.val_zero, h0, dite_false, Nat.zero_mod, Nat.zero_div]
      exact R_a' rfl _
    · rw [AffineD.leafTarget_of_not_lt_two i hi] at hj
      subst hj
      simp only [dmap, hi, dite_false, Fin.val_last, dite_true]
      by_cases h2 : i.val = 2
      · rw [if_pos h2]; left; exact R.v1
      · rw [if_neg h2]; right; exact R.v2
  · exact absurd e (AffineD.not_nonempty_hom_leaf _ _)
  · have hj := (AffineD.nonempty_spine_spine_iff j j').1 e
    have hjl : j.val ≠ 2 * L + 3 := by have := j'.2; omega
    by_cases hlast : j'.val = 2 * L + 3
    · left
      have hp : j.val % 2 = 0 := by omega
      simp only [dmap, hlast, dite_true, hjl, hp, dite_false]
      exact R_r' (by simp; omega)
    · by_cases hp : j.val % 2 = 0
      · left
        have hq : ¬j'.val % 2 = 0 := by omega
        simp only [dmap, hjl, hlast, hp, hq, dite_true, dite_false]
        exact R_ρ' (by simp; omega)
      · right
        have hq : j'.val % 2 = 0 := by omega
        simp only [dmap, hjl, hlast, hp, hq, dite_true, dite_false]
        exact R_σ' (by simp; omega)

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
      split_ifs at h with h1 h2 h3 h4 <;>
        simp only [lf.injEq, Fin.mk.injEq, reduceCtorEq] at h <;>
        first | exact congrArg _ (Fin.ext h) | exact congrArg _ (Fin.ext (by omega))
    · simp only [dmap] at h
      split_ifs at h <;> simp only [reduceCtorEq] at h
    · simp only [dmap] at h
      split_ifs at h <;> simp only [reduceCtorEq] at h
    · simp only [dmap] at h
      split_ifs at h <;> simp only [xv.injEq, zv.injEq, Fin.mk.injEq, reduceCtorEq] at h <;>
        exact congrArg _ (Fin.ext (by omega))

section Lemmas

lemma R_xv {a : Fin (L + 2)} {w : ZB L} (h : R (xv a) w) :
    (∃ b : Fin (L + 1), w = zv b ∧ a.val = b.val) ∨
      (∃ b : Fin (L + 1), w = zv b ∧ a.val = b.val + 1) ∨ (∃ i, w = lf i ∧ a.val = 0) ∨
        (w = mv ∧ a.val = L + 1) := by
  generalize hu : xv a = u at h
  cases h with
  | ρ j =>
    simp only [xv.injEq] at hu
    subst hu
    exact Or.inl ⟨j, rfl, by simp⟩
  | σ j =>
    simp only [xv.injEq] at hu
    subst hu
    exact Or.inr (Or.inl ⟨j, rfl, by simp⟩)
  | a i => cases hu; exact Or.inr (Or.inr (Or.inl ⟨i, rfl, rfl⟩))
  | r => cases hu; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  | v1 => cases hu
  | v2 => cases hu

lemma R_mv {w : ZB L} (h : R mv w) : w = ee := by cases h; rfl

lemma R_xe {w : ZB L} (h : R xe w) : w = mv := by cases h; rfl

lemma R_to_zv {u : ZB L} {b : Fin (L + 1)} (h : R u (zv b)) :
    (∃ a : Fin (L + 2), u = xv a ∧ a.val = b.val) ∨
      (∃ a : Fin (L + 2), u = xv a ∧ a.val = b.val + 1) := by
  generalize hw : zv b = w at h
  cases h with
  | ρ j =>
    simp only [zv.injEq] at hw
    subst hw
    exact Or.inl ⟨_, rfl, by simp⟩
  | σ j =>
    simp only [zv.injEq] at hw
    subst hw
    exact Or.inr ⟨_, rfl, by simp⟩
  | r => cases hw
  | v1 => cases hw
  | v2 => cases hw
  | a i => cases hw

lemma R_to_mv {u : ZB L} (h : R u mv) : u = xv (Fin.last _) ∨ u = xe := by
  cases h
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma R_to_xv {u : ZB L} {a : Fin (L + 2)} (h : R u (xv a)) : False := by cases h

lemma R_to_xe {u : ZB L} (h : R u xe) : False := by cases h

lemma R_to_ee {u : ZB L} (h : R u ee) : u = mv := by cases h; rfl

lemma R_to_lf {u : ZB L} {i : Fin 2} (h : R u (lf i)) : u = xv 0 := by cases h; rfl

lemma mid {u b w : ZB L} (h1 : R u b) (h2 : R b w) :
    b = mv ∧ (u = xv (Fin.last _) ∨ u = xe) ∧ w = ee := by
  cases h1 <;> cases h2
  · exact ⟨rfl, Or.inl rfl, rfl⟩
  · exact ⟨rfl, Or.inr rfl, rfl⟩

lemma xv_zv_val {a : Fin (L + 2)} {b : Fin (L + 1)} (h : R (xv a) (zv b)) (hab : ¬a.val = b.val) :
    a.val = b.val + 1 := by
  rcases R_xv h with ⟨c, hc, h1⟩ | ⟨c, hc, h1⟩ | ⟨i, hc, -⟩ | ⟨hc, -⟩ <;>
    simp only [zv.injEq, reduceCtorEq] at hc
  · subst hc; exact absurd h1 hab
  · subst hc; exact h1

lemma xv_lf_val {a : Fin (L + 2)} {i : Fin 2} (h : R (xv a) (lf i)) : a.val = 0 := by
  cases h; rfl

lemma xv_mv_val {a : Fin (L + 2)} (h : R (xv a) mv) : a.val = L + 1 := by
  cases h; rfl

lemma R_from_zv {b : Fin (L + 1)} {w : ZB L} (h : R (zv b) w) : False := by cases h

lemma R_from_lf {i : Fin 2} {w : ZB L} (h : R (lf i) w) : False := by cases h

lemma R_from_ee {w : ZB L} (h : R ee w) : False := by cases h

end Lemmas

variable {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] (Z : ZChain Q) (p L : ℕ)
  (F : Fin 2 → BMor (Z.x p)) {M X E : Q} (r : Z.x (p + L + 1) ⟶ M) (v : X ⟶ M) (s : M ⟶ E)

/-- The objects. -/
def bobj : ZB L → Q
  | xv j => Z.x (p + j.val)
  | zv j => Z.z (p + j.val)
  | mv => M
  | xe => X
  | ee => E
  | lf i => (F i).1

/-- The morphisms. -/
def bmor : ∀ u w : ZB L, R u w →
    (bobj Z p L F (M := M) (X := X) (E := E) u ⟶ bobj Z p L F (M := M) (X := X) (E := E) w)
  | xv a, zv b, h =>
    if hab : a.val = b.val then eqToHom (congrArg (fun t ↦ Z.x (p + t)) hab) ≫ Z.ρ (p + b.val)
    else eqToHom (congrArg (fun t ↦ Z.x (p + t)) (xv_zv_val h hab)) ≫ Z.σ (p + b.val)
  | xv a, lf i, h => eqToHom (congrArg (fun t ↦ Z.x (p + t)) (xv_lf_val h)) ≫ (F i).2
  | xv a, mv, h => eqToHom (congrArg (fun t ↦ Z.x (p + t)) (xv_mv_val h)) ≫ r
  | xe, mv, _ => v
  | mv, ee, _ => s
  | xv _, xv _, h | xv _, xe, h | xv _, ee, h => absurd h (by intro h; cases h)
  | zv _, _, h | ee, _, h | lf _, _, h => absurd h (by intro h; cases h)
  | mv, xv _, h | mv, zv _, h | mv, mv, h | mv, xe, h | mv, lf _, h =>
    absurd h (by intro h; cases h)
  | xe, xv _, h | xe, zv _, h | xe, xe, h | xe, ee, h | xe, lf _, h =>
    absurd h (by intro h; cases h)

variable {Z p L F r v s}

lemma bmor_ρ' (a : Fin (L + 2)) (b : Fin (L + 1)) (hab : a.val = b.val) (h) :
    bmor Z p L F r v s (xv a) (zv b) h =
      eqToHom (congrArg (fun t ↦ Z.x (p + t)) hab) ≫ Z.ρ (p + b.val) := by
  simp only [bmor, hab, dite_true]
  rfl

lemma bmor_σ' (a : Fin (L + 2)) (b : Fin (L + 1)) (hab : a.val = b.val + 1) (h) :
    bmor Z p L F r v s (xv a) (zv b) h =
      eqToHom (congrArg (fun t ↦ Z.x (p + t)) hab) ≫ Z.σ (p + b.val) := by
  have : ¬a.val = b.val := by omega
  simp only [bmor, this, dite_false]
  rfl

lemma bmor_ρ (j : Fin (L + 1)) (h) :
    bmor Z p L F r v s (xv j.castSucc) (zv j) h = Z.ρ (p + j.val) := by
  simp only [bmor, Fin.val_castSucc, dite_true]
  exact Category.id_comp _

lemma bmor_σ (j : Fin (L + 1)) (h) :
    bmor Z p L F r v s (xv j.succ) (zv j) h = Z.σ (p + j.val) := by
  simp only [bmor, Fin.val_succ, Nat.succ_ne_self, dite_false]
  exact Category.id_comp _

lemma bmor_a (i : Fin 2) (h) : bmor Z p L F r v s (xv 0) (lf i) h = (F i).2 :=
  Category.id_comp _

lemma bmor_a' (a : Fin (L + 2)) (ha : a.val = 0) (i : Fin 2) (h) :
    bmor Z p L F r v s (xv a) (lf i) h =
      eqToHom (congrArg (fun t ↦ Z.x (p + t)) ha) ≫ (F i).2 := rfl

lemma bmor_r (h) : bmor Z p L F r v s (xv (Fin.last _)) mv h = r :=
  Category.id_comp _

lemma bmor_r' (a : Fin (L + 2)) (ha : a.val = L + 1) (h) :
    bmor Z p L F r v s (xv a) mv h = eqToHom (congrArg (fun t ↦ Z.x (p + t)) ha) ≫ r := rfl

lemma bmor_v1 (h) : bmor Z p L F r v s xe mv h = v := rfl

lemma bmor_v2 (h) : bmor Z p L F r v s mv ee h = s := rfl

end ZB

end RayCat

end LargeIndecomposable

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

open ZB in
include B in
/-- **No zigzag with a fork and an arm at a source in `P/τ`** (BO13a figure 5.4). -/
theorem not_zigzag_arm2
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) (Z : ZChain P) (p L : ℕ) (F : Fin 2 → BMor (Z.x p)) {M X E : P}
    (r : Z.x (p + L + 1) ⟶ M) (v : X ⟶ M) (s : M ⟶ E)
    (hρ : ∀ j ≤ L, ¬FactorsThroughMorphism τ (Z.ρ (p + j)))
    (hσ : ∀ j ≤ L, ¬FactorsThroughMorphism τ (Z.σ (p + j)))
    (hF : ∀ i, ¬FactorsThroughMorphism τ (F i).2) (hr : ¬FactorsThroughMorphism τ r)
    (hv : ¬FactorsThroughMorphism τ v) (hs : ¬FactorsThroughMorphism τ s)
    (hrs : ¬FactorsThroughMorphism τ (r ≫ s)) (hvs : ¬FactorsThroughMorphism τ (v ≫ s))
    (hFi : ∀ i, ¬IsIso (F i).2) (hir : ¬IsIso r) (hiv : ¬IsIso v) (his : ¬IsIso s)
    (hFF : ∀ i i', i ≠ i' → ¬∃ g, (F i).2 ≫ g = (F i').2)
    (hFρ : ∀ i, ¬∃ g, (F i).2 ≫ g = Z.ρ p) (hρF : ∀ i, ¬∃ g, Z.ρ p ≫ g = (F i).2)
    (hσr : ¬∃ g, Z.σ (p + L) ≫ g = r) (hrσ : ¬∃ g, r ≫ g = Z.σ (p + L))
    (hσrs : ¬∃ g, Z.σ (p + L) ≫ g = r ≫ s)
    (hrv : ¬∃ g, g ≫ r = v) (hvr : ¬∃ g, g ≫ v = r) : False := by
  have ho : ∀ u v, R u v → (graph L).Adj u v := fun u v h ↦ adj_iff.2 (Or.inl h)
  haveI : Fact (LargeIndecomposable.Foundations.Quiver.IsAcyclic (OT (graph L) R)) :=
    ⟨OT.isAcyclic ho (fun _ _ h ↦ R_asymm h) isAcyclic⟩
  let φ : OT (graph L) R ⥤q P :=
    { obj := fun u ↦ bobj Z p L F (M := M) (X := X) (E := E) u.as
      map := fun {u w} e ↦ bmor Z p L F r v s u.as w.as (OT.hom_down e) }
  have harr : ∀ u w (h : R u w), ¬FactorsThroughMorphism τ (bmor Z p L F r v s u w h) ∧
      ¬IsIso (bmor Z p L F r v s u w h) := by
    intro u w h
    cases h with
    | ρ j => rw [bmor_ρ]; exact ⟨hρ j (by omega), Z.ρ_not_isIso _⟩
    | σ j => rw [bmor_σ]; exact ⟨hσ j (by omega), Z.σ_not_isIso _⟩
    | r => rw [bmor_r]; exact ⟨hr, hir⟩
    | v1 => exact ⟨hv, hiv⟩
    | v2 => exact ⟨hs, his⟩
    | a i => rw [bmor_a]; exact ⟨hF i, hFi i⟩
  have hnil : ∀ {c' w : ZB L} (q : Quiver.Path (⟨c'⟩ : OT (graph L) R) ⟨w⟩),
      (∀ d, ¬R c' d) → c' = w := by
    intro c' w q hc
    cases q with
    | nil => rfl
    | cons q e2 =>
      exfalso
      obtain ⟨d, f, -, -, -⟩ :=
        Quiver.Path.eq_toPath_comp_of_length_eq_succ (q.cons e2) (n := q.length) (by simp)
      exact hc _ (OT.hom_down f)
  have hfirst : ∀ {c' w : ZB L} (q : Quiver.Path (⟨c'⟩ : OT (graph L) R) ⟨w⟩),
      0 < q.length → ∃ d, R c' d := by
    intro c' w q hq
    obtain ⟨d, f, -, -, -⟩ :=
      Quiver.Path.eq_toPath_comp_of_length_eq_succ q (n := q.length - 1) (by omega)
    exact ⟨_, OT.hom_down f⟩
  have hq0 : ∀ {c' w : ZB L} (q : Quiver.Path (⟨c'⟩ : OT (graph L) R) ⟨w⟩), (∀ d, ¬R c' d) →
      ∃ h : (⟨c'⟩ : OT (graph L) R) = ⟨w⟩, q = h ▸ Quiver.Path.nil := by
    intro c' w q hc
    cases q with
    | nil => exact ⟨rfl, rfl⟩
    | cons q e2 => exact absurd (hfirst (q.cons e2) (by simp)) (by rintro ⟨d, h⟩; exact hc d h)
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
        change ¬FactorsThroughMorphism τ (𝟙 _ ≫ bmor Z p L F r v s u w he)
        rw [Category.id_comp]
        exact (harr u w he).1
      | cons q e' =>
        rename_i w2
        rcases w2 with ⟨w2⟩
        have he' := OT.hom_down e'
        obtain ⟨rfl, hu, rfl⟩ := mid he' he
        cases q with
        | cons q e'' =>
          rcases hu with rfl | rfl
          · exact (R_to_xv (OT.hom_down e'')).elim
          · exact (R_to_xe (OT.hom_down e'')).elim
        | nil =>
          rcases hu with rfl | rfl
          · change ¬FactorsThroughMorphism τ ((𝟙 _ ≫ bmor Z p L F r v s (xv (Fin.last _)) mv he') ≫
              bmor Z p L F r v s mv ee he)
            rw [Category.id_comp, bmor_r, bmor_v2]
            exact hrs
          · change ¬FactorsThroughMorphism τ ((𝟙 _ ≫ bmor Z p L F r v s xe mv he') ≫
              bmor Z p L F r v s mv ee he)
            rw [Category.id_comp, bmor_v1, bmor_v2]
            exact hvs
  · intro u w e
    exact (harr _ _ _).2
  · intro u c c' w e e' q hne ⟨g, hg⟩
    rcases u with ⟨u⟩
    rcases c with ⟨c⟩
    rcases c' with ⟨c'⟩
    rcases w with ⟨w⟩
    have he := OT.hom_down e
    have he' := OT.hom_down e'
    cases he with
    | ρ j =>
      rw [show φ.map e = Z.ρ (p + j.val) from bmor_ρ (Z := Z) (p := p) (F := F) (r := r) (v := v) (s := s) j (OT.hom_down e)] at hg
      rcases R_xv he' with ⟨b, rfl, hb⟩ | ⟨⟨b, hb0⟩, rfl, hb⟩ | ⟨i, rfl, hb⟩ | ⟨rfl, hb⟩
      · exact hne (congrArg OT.mk (congrArg zv (Fin.ext (by simpa using hb))))
      · obtain ⟨hq, rfl⟩ := hq0 q (fun d h ↦ R_from_zv h)
        cases hq
        simp only [Fin.val_castSucc] at hb
        obtain ⟨j, hj⟩ := j
        simp only at hb
        subst hb
        change Z.ρ (p + (b + 1)) ≫ g =
          𝟙 _ ≫ bmor Z p L F r v s (xv (Fin.castSucc ⟨b + 1, hj⟩)) (zv ⟨b, hb0⟩) he' at hg
        rw [Category.id_comp, bmor_σ' _ ⟨b, hb0⟩ rfl] at hg
        exact Z.valley₂ (p + b) ⟨g, hg.trans (ZChain.eqToHom_self_comp _ _)⟩
      · obtain ⟨hq, rfl⟩ := hq0 q (fun d h ↦ R_from_lf h)
        cases hq
        simp only [Fin.val_castSucc] at hb
        obtain ⟨j, hj⟩ := j
        simp only at hb
        subst hb
        change Z.ρ (p + 0) ≫ g =
          𝟙 _ ≫ bmor Z p L F r v s (xv (Fin.castSucc ⟨0, hj⟩)) (lf i) he' at hg
        rw [Category.id_comp, bmor_a' _ rfl] at hg
        exact hρF i ⟨g, hg.trans (ZChain.eqToHom_self_comp _ _)⟩
      · simp only [Fin.val_castSucc] at hb
        have := j.2
        omega
    | σ j =>
      rw [show φ.map e = Z.σ (p + j.val) from bmor_σ (Z := Z) (p := p) (F := F) (r := r) (v := v) (s := s) j (OT.hom_down e)] at hg
      rcases R_xv he' with ⟨⟨b, hb0⟩, rfl, hb⟩ | ⟨b, rfl, hb⟩ | ⟨i, rfl, hb⟩ | ⟨rfl, hb⟩
      · obtain ⟨hq, rfl⟩ := hq0 q (fun d h ↦ R_from_zv h)
        cases hq
        simp only [Fin.val_succ] at hb
        subst hb
        change Z.σ (p + j.val) ≫ g =
          𝟙 _ ≫ bmor Z p L F r v s (xv j.succ) (zv ⟨j.val + 1, hb0⟩) he' at hg
        rw [Category.id_comp, bmor_ρ' _ ⟨j.val + 1, hb0⟩ (by simp)] at hg
        exact Z.valley₁ (p + j) ⟨g, hg.trans (ZChain.eqToHom_self_comp _ _)⟩
      · exact hne (congrArg OT.mk (congrArg zv (Fin.ext (by simp at hb; omega))))
      · simp at hb
      · simp only [Fin.val_succ] at hb
        obtain rfl : j = Fin.last L := Fin.ext (by simp; omega)
        cases q with
        | nil =>
          change Z.σ (p + L) ≫ g = 𝟙 _ ≫ bmor Z p L F r v s (xv (Fin.last L).succ) mv he' at hg
          rw [Category.id_comp, bmor_r' _ (by simp)] at hg
          exact hσr ⟨g, hg.trans (ZChain.eqToHom_self_comp _ _)⟩
        | cons q e2 =>
          rename_i w1
          rcases w1 with ⟨w1⟩
          have h2 := OT.hom_down e2
          cases q with
          | nil =>
            obtain rfl := R_mv h2
            change Z.σ (p + L) ≫ g = (𝟙 _ ≫ bmor Z p L F r v s (xv (Fin.last L).succ) mv he') ≫
              bmor Z p L F r v s mv ee h2 at hg
            rw [Category.id_comp, bmor_r' _ (by simp), bmor_v2, ZChain.eqToHom_self_comp] at hg
            exact hσrs ⟨g, hg⟩
          | cons q e3 =>
            exfalso
            obtain ⟨⟨d⟩, f, q', -, -⟩ :=
              Quiver.Path.eq_toPath_comp_of_length_eq_succ (q.cons e3) (n := q.length) (by simp)
            obtain rfl := R_mv (OT.hom_down f)
            obtain ⟨hq', -⟩ := hq0 q' (fun d h ↦ R_from_ee h)
            cases hq'
            exact R_from_ee h2
    | r =>
      rw [show φ.map e = r from bmor_r (Z := Z) (p := p) (F := F) (r := r) (v := v) (s := s) (OT.hom_down e)] at hg
      rcases R_xv he' with ⟨b, rfl, hb⟩ | ⟨⟨b, hb0⟩, rfl, hb⟩ | ⟨i, rfl, hb⟩ | ⟨rfl, hb⟩
      · simp at hb
        have := b.2
        omega
      · obtain ⟨hq, rfl⟩ := hq0 q (fun d h ↦ R_from_zv h)
        cases hq
        simp only [Fin.val_last] at hb
        obtain rfl : b = L := by omega
        change r ≫ g = 𝟙 _ ≫ bmor Z p b F r v s (xv (Fin.last _)) (zv ⟨b, hb0⟩) he' at hg
        rw [Category.id_comp, bmor_σ' _ ⟨b, hb0⟩ (by simp)] at hg
        exact hrσ ⟨g, hg.trans (ZChain.eqToHom_self_comp _ _)⟩
      · simp at hb
      · exact hne rfl
    | v1 => exact hne (congrArg OT.mk (R_xe he').symm)
    | v2 => exact hne (congrArg OT.mk (R_mv he').symm)
    | a i =>
      rw [show φ.map e = (F i).2 from bmor_a (Z := Z) (p := p) (F := F) (r := r) (v := v) (s := s) i (OT.hom_down e)] at hg
      rcases R_xv he' with ⟨⟨b, hb0⟩, rfl, hb⟩ | ⟨b, rfl, hb⟩ | ⟨i', rfl, hb⟩ | ⟨rfl, hb⟩
      · obtain ⟨hq, rfl⟩ := hq0 q (fun d h ↦ R_from_zv h)
        cases hq
        simp only [Fin.val_zero] at hb
        subst hb
        change (F i).2 ≫ g = 𝟙 _ ≫ bmor Z p L F r v s (xv 0) (zv ⟨0, hb0⟩) he' at hg
        rw [Category.id_comp, bmor_ρ' 0 ⟨0, hb0⟩ rfl] at hg
        exact hFρ i ⟨g, hg.trans (ZChain.eqToHom_self_comp _ _)⟩
      · simp at hb
      · obtain ⟨hq, rfl⟩ := hq0 q (fun d h ↦ R_from_lf h)
        cases hq
        change (F i).2 ≫ g = 𝟙 _ ≫ bmor Z p L F r v s (xv 0) (lf i') he' at hg
        rw [Category.id_comp, bmor_a] at hg
        exact hFF i i' (fun h ↦ hne (by rw [h])) ⟨g, hg⟩
      · simp at hb
  · intro u c c' w e e' q hne ⟨g, hg⟩
    rcases u with ⟨u⟩
    rcases c with ⟨c⟩
    rcases c' with ⟨c'⟩
    rcases w with ⟨w⟩
    have he := OT.hom_down e
    have he' := OT.hom_down e'
    cases he with
    | ρ j =>
      rw [show φ.map e = Z.ρ (p + j.val) from
        bmor_ρ (Z := Z) (p := p) (F := F) (r := r) (v := v) (s := s) j (OT.hom_down e)] at hg
      rcases R_to_zv he' with ⟨⟨a, ha0⟩, rfl, ha⟩ | ⟨⟨a, ha0⟩, rfl, ha⟩
      · exact hne (congrArg OT.mk (congrArg xv (Fin.ext (by simp at ha ⊢; omega))))
      · cases q with
        | cons q e3 => exact (R_to_xv (OT.hom_down e3)).elim
        | nil =>
          simp only at ha
          subst ha
          change g ≫ Z.ρ (p + j.val) =
            𝟙 _ ≫ bmor Z p L F r v s (xv ⟨j.val + 1, ha0⟩) (zv j) he' at hg
          rw [Category.id_comp, bmor_σ' ⟨j.val + 1, ha0⟩ j rfl] at hg
          exact Z.peak₂ (p + j) ⟨g, hg.trans (ZChain.eqToHom_self_comp _ _)⟩
    | σ j =>
      rw [show φ.map e = Z.σ (p + j.val) from
        bmor_σ (Z := Z) (p := p) (F := F) (r := r) (v := v) (s := s) j (OT.hom_down e)] at hg
      rcases R_to_zv he' with ⟨⟨a, ha0⟩, rfl, ha⟩ | ⟨⟨a, ha0⟩, rfl, ha⟩
      · cases q with
        | cons q e3 => exact (R_to_xv (OT.hom_down e3)).elim
        | nil =>
          simp only at ha
          subst ha
          change g ≫ Z.σ (p + j.val) =
            𝟙 _ ≫ bmor Z p L F r v s (xv ⟨j.val, ha0⟩) (zv j) he' at hg
          rw [Category.id_comp, bmor_ρ' ⟨j.val, ha0⟩ j rfl] at hg
          exact Z.peak₁ (p + j) ⟨g, hg.trans (ZChain.eqToHom_self_comp _ _)⟩
      · exact hne (congrArg OT.mk (congrArg xv (Fin.ext (by simp at ha ⊢; omega))))
    | r =>
      rw [show φ.map e = r from
        bmor_r (Z := Z) (p := p) (F := F) (r := r) (v := v) (s := s) (OT.hom_down e)] at hg
      rcases R_to_mv he' with rfl | rfl
      · exact hne rfl
      · cases q with
        | cons q e3 => exact (R_to_xe (OT.hom_down e3)).elim
        | nil =>
          change g ≫ r = 𝟙 _ ≫ bmor Z p L F r v s xe mv he' at hg
          rw [Category.id_comp, bmor_v1] at hg
          exact hrv ⟨g, hg⟩
    | v1 =>
      rcases R_to_mv he' with rfl | rfl
      · cases q with
        | cons q e3 => exact (R_to_xv (OT.hom_down e3)).elim
        | nil =>
          change g ≫ bmor Z p L F r v s xe mv (OT.hom_down e) =
            𝟙 _ ≫ bmor Z p L F r v s (xv (Fin.last _)) mv he' at hg
          rw [Category.id_comp, bmor_v1, bmor_r] at hg
          exact hvr ⟨g, hg⟩
      · exact hne rfl
    | v2 => exact hne (congrArg OT.mk (R_to_ee he').symm)
    | a i => exact hne (congrArg OT.mk (R_to_lf he').symm)

end MulBasis

end RayQuiver

end LargeIndecomposable
