module

public import LargeIndecomposable.Cleaving.Zigzags.ZigzagFork
public import LargeIndecomposable.Cleaving.Diagrams.TreeShapes

/-!
# Zigzags with a fork and an arm: BO13a figures 5.2 and 5.3

The diagram: two forks out of `x p`; the zigzag `ρ (p+j)` (`j ≤ L`),
`σ (p+j)` (`j < L`) ending at `z (p+L)`; a vertex `M` with `s' : M → z (p+L)`;
and two leaves at `M`: `v₁ : x (p+L+1) → M` and `v₂ : M → E`. It is an
orientation of `D̃₂ₗ₊₆` (`RayCat.ZA`). With `v₁ ≫ s' = σ (p+L)` it is the
diagram of BO13a figure 5.2 (and of figure 5.3).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

/-- The vertices. -/
inductive ZA (L : ℕ) : Type
  | xv (j : Fin (L + 1))
  | zv (j : Fin (L + 1))
  | mv
  | xe
  | ee
  | lf (i : Fin 2)
  deriving DecidableEq

namespace ZA

variable {L : ℕ}

instance : Fintype (ZA L) where
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
inductive R : ZA L → ZA L → Prop
  | ρ (j : Fin (L + 1)) : R (xv j) (zv j)
  | σ (j : Fin L) : R (xv j.succ) (zv j.castSucc)
  | sm : R mv (zv (Fin.last L))
  | v1 : R xe mv
  | v2 : R mv ee
  | a (i : Fin 2) : R (xv 0) (lf i)

lemma R_asymm {u v : ZA L} (h : R u v) : ¬R v u := by
  intro h'
  cases h <;> cases h'

lemma R_irrefl {u : ZA L} (h : R u u) : False := by
  cases h

variable (L) in
/-- The graph. -/
def graph : SimpleGraph (ZA L) := SimpleGraph.fromRel R

lemma adj_iff {u v : ZA L} : (graph L).Adj u v ↔ R u v ∨ R v u := by
  rw [graph, SimpleGraph.fromRel_adj]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  rintro rfl
  rcases h with h | h <;> exact R_irrefl h

/-- The parent function towards `xv 0`. -/
def par : ZA L → Option (ZA L)
  | xv j => if h : j.val = 0 then none else some (zv ⟨j.val - 1, by omega⟩)
  | zv j => some (xv j)
  | mv => some (zv (Fin.last L))
  | xe => some mv
  | ee => some mv
  | lf _ => some (xv 0)

/-- The height. -/
def ht : ZA L → ℕ
  | xv j => 2 * j.val
  | zv j => 2 * j.val + 1
  | mv => 2 * L + 2
  | xe => 2 * L + 3
  | ee => 2 * L + 3
  | lf _ => 1

lemma par_of_R {u v : ZA L} (h : R u v) : par u = some v ∨ par v = some u := by
  cases h with
  | ρ j => exact Or.inr (by simp [par])
  | σ j =>
    left
    simp only [par, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, dite_false,
      Option.some.injEq, zv.injEq]
    ext
    simp
  | sm => exact Or.inl rfl
  | v1 => exact Or.inl rfl
  | v2 => exact Or.inr rfl
  | a i => exact Or.inr rfl

lemma R_of_par {u v : ZA L} (h : par u = some v) : R u v ∨ R v u := by
  cases u with
  | xv j =>
    simp only [par] at h
    split_ifs at h with h1
    simp only [Option.some.injEq] at h
    subst h
    left
    have hj : j.val - 1 < L := by have := j.2; omega
    convert R.σ (L := L) ⟨j.val - 1, hj⟩ using 2
    · ext
      simp
      omega
    · rfl
  | zv j => simp only [par, Option.some.injEq] at h; subst h; exact Or.inr (R.ρ j)
  | mv => simp only [par, Option.some.injEq] at h; subst h; exact Or.inl R.sm
  | xe => simp only [par, Option.some.injEq] at h; subst h; exact Or.inl R.v1
  | ee => simp only [par, Option.some.injEq] at h; subst h; exact Or.inr R.v2
  | lf i => simp only [par, Option.some.injEq] at h; subst h; exact Or.inr (R.a i)

lemma R_iff_par (u v : ZA L) : R u v ∨ R v u ↔ par u = some v ∨ par v = some u := by
  constructor
  · rintro (h | h)
    · exact par_of_R h
    · exact (par_of_R h).symm
  · rintro (h | h)
    · exact R_of_par h
    · exact (R_of_par h).symm

lemma par_lt (u v : ZA L) (h : par u = some v) : ht v < ht u := by
  cases u with
  | xv j =>
    simp only [par] at h
    split_ifs at h with h1
    simp only [Option.some.injEq] at h
    subst h
    simp only [ht]
    omega
  | zv j => simp only [par, Option.some.injEq] at h; subst h; simp [ht]
  | mv => simp only [par, Option.some.injEq] at h; subst h; simp [ht]
  | xe => simp only [par, Option.some.injEq] at h; subst h; simp [ht]
  | ee => simp only [par, Option.some.injEq] at h; subst h; simp [ht]
  | lf i => simp only [par, Option.some.injEq] at h; subst h; simp [ht]

lemma isAcyclic : (graph L).IsAcyclic :=
  isAcyclic_of_parent (graph L) par ht (fun u v ↦ by rw [adj_iff, R_iff_par]) par_lt

lemma R_ρ' {a b : Fin (L + 1)} (h : a.val = b.val) : R (xv a) (zv b) := by
  obtain rfl : a = b := Fin.ext h
  exact R.ρ a

lemma R_σ' {a b : Fin (L + 1)} (h : a.val = b.val + 1) : R (xv a) (zv b) := by
  have hb : b.val < L := by have := a.2; omega
  convert R.σ (L := L) ⟨b.val, hb⟩ using 2
  · ext; simp; omega
  · rfl

lemma R_a' {a : Fin (L + 1)} (h : a.val = 0) (i : Fin 2) : R (xv a) (lf i) := by
  obtain rfl : a = 0 := Fin.ext h
  exact R.a i

lemma R_sm' {b : Fin (L + 1)} (h : b.val = L) : R mv (zv b) := by
  obtain rfl : b = Fin.last L := Fin.ext h
  exact R.sm

open LargeIndecomposable.Foundations.Quiver in
/-- The vertex map of the copy of `D̃₂ₗ₊₆`. -/
def dmap : AffineD (2 * L + 2) → ZA L
  | .spine a => if h0 : a.val = 2 * L + 2 then mv else
      if h : a.val % 2 = 0 then xv ⟨a.val / 2, by have := a.isLt; omega⟩
      else zv ⟨a.val / 2, by have := a.isLt; omega⟩
  | .leaf i => if h : i.val < 2 then lf ⟨i.val, h⟩ else if i.val = 2 then xe else ee

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
      right
      have h0 : ¬(0 : ℕ) = 2 * L + 2 := by omega
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
    have hjl : j.val ≠ 2 * L + 2 := by have := j'.2; omega
    by_cases hlast : j'.val = 2 * L + 2
    · right
      have hp : ¬j.val % 2 = 0 := by omega
      simp only [dmap, hlast, dite_true, hjl, hp, dite_false]
      exact R_sm' (by simp; omega)
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

end ZA

end RayCat

end LargeIndecomposable

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

namespace RayCat

namespace ZA

section Lemmas

variable {L : ℕ}

lemma xv_zv_val {a b : Fin (L + 1)} (h : R (xv a) (zv b)) (hab : ¬a.val = b.val) :
    a.val = b.val + 1 := by
  cases h with
  | ρ j => exact absurd rfl hab
  | σ j => simp

lemma xv_lf_val {a : Fin (L + 1)} {i : Fin 2} (h : R (xv a) (lf i)) : a.val = 0 := by
  cases h; rfl

lemma mv_zv_val {b : Fin (L + 1)} (h : R mv (zv b)) : b.val = L := by
  cases h; rfl

lemma R_xv {a : Fin (L + 1)} {w : ZA L} (h : R (xv a) w) :
    (∃ b : Fin (L + 1), w = zv b ∧ a.val = b.val) ∨
      (∃ b : Fin (L + 1), w = zv b ∧ a.val = b.val + 1) ∨ ∃ i, w = lf i ∧ a.val = 0 := by
  generalize hu : xv a = u at h
  cases h with
  | ρ j => cases hu; exact Or.inl ⟨_, rfl, rfl⟩
  | σ j =>
    simp only [xv.injEq] at hu
    subst hu
    exact Or.inr (Or.inl ⟨j.castSucc, rfl, by simp⟩)
  | a i => cases hu; exact Or.inr (Or.inr ⟨i, rfl, rfl⟩)
  | sm => cases hu
  | v1 => cases hu
  | v2 => cases hu

lemma R_mv {w : ZA L} (h : R mv w) : (∃ b : Fin (L + 1), w = zv b ∧ b.val = L) ∨ w = ee := by
  cases h with
  | sm => exact Or.inl ⟨_, rfl, rfl⟩
  | v2 => exact Or.inr rfl

lemma R_xe {w : ZA L} (h : R xe w) : w = mv := by cases h; rfl

lemma R_zv {b : Fin (L + 1)} {w : ZA L} (h : R (zv b) w) : False := by cases h

lemma R_ee {w : ZA L} (h : R ee w) : False := by cases h

lemma R_lf {i : Fin 2} {w : ZA L} (h : R (lf i) w) : False := by cases h

lemma R_to_zv {u : ZA L} {b : Fin (L + 1)} (h : R u (zv b)) :
    (∃ a : Fin (L + 1), u = xv a ∧ a.val = b.val) ∨
      (∃ a : Fin (L + 1), u = xv a ∧ a.val = b.val + 1) ∨ (u = mv ∧ b.val = L) := by
  generalize hw : zv b = w at h
  cases h with
  | ρ j => cases hw; exact Or.inl ⟨_, rfl, rfl⟩
  | σ j =>
    simp only [zv.injEq] at hw
    subst hw
    exact Or.inr (Or.inl ⟨j.succ, rfl, by simp⟩)
  | sm => cases hw; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  | v1 => cases hw
  | v2 => cases hw
  | a i => cases hw

lemma R_to_mv {u : ZA L} (h : R u mv) : u = xe := by cases h; rfl

lemma R_to_xv {u : ZA L} {a : Fin (L + 1)} (h : R u (xv a)) : False := by cases h

lemma R_to_xe {u : ZA L} (h : R u xe) : False := by cases h

lemma R_to_ee {u : ZA L} (h : R u ee) : u = mv := by cases h; rfl

lemma R_to_lf {u : ZA L} {i : Fin 2} (h : R u (lf i)) : u = xv 0 := by cases h; rfl

end Lemmas

variable {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] (Z : ZChain Q) (p L : ℕ)
  (F : Fin 2 → BMor (Z.x p)) {M E : Q} (s' : M ⟶ Z.z (p + L)) (v₁ : Z.x (p + L + 1) ⟶ M)
  (v₂ : M ⟶ E)

/-- The objects. -/
def aobj : ZA L → Q
  | xv j => Z.x (p + j.val)
  | zv j => Z.z (p + j.val)
  | mv => M
  | xe => Z.x (p + L + 1)
  | ee => E
  | lf i => (F i).1

/-- The morphisms. -/
def amor : ∀ u w : ZA L, R u w → (aobj Z p L F (M := M) (E := E) u ⟶ aobj Z p L F (M := M) (E := E) w)
  | xv a, zv b, h =>
    if hab : a.val = b.val then eqToHom (congrArg (fun t ↦ Z.x (p + t)) hab) ≫ Z.ρ (p + b.val)
    else eqToHom (congrArg (fun t ↦ Z.x (p + t)) (xv_zv_val h hab)) ≫ Z.σ (p + b.val)
  | xv a, lf i, h => eqToHom (congrArg (fun t ↦ Z.x (p + t)) (xv_lf_val h)) ≫ (F i).2
  | mv, zv b, h => s' ≫ eqToHom (congrArg (fun t ↦ Z.z (p + t)) (mv_zv_val h).symm)
  | mv, ee, _ => v₂
  | xe, mv, _ => v₁
  | xv _, xv _, h | xv _, mv, h | xv _, xe, h | xv _, ee, h => absurd h (by intro h; cases h)
  | zv _, _, h | ee, _, h | lf _, _, h => absurd h (by intro h; cases h)
  | mv, xv _, h | mv, mv, h | mv, xe, h | mv, lf _, h => absurd h (by intro h; cases h)
  | xe, xv _, h | xe, zv _, h | xe, xe, h | xe, ee, h | xe, lf _, h =>
    absurd h (by intro h; cases h)

variable {Z p L F s' v₁ v₂}

lemma amor_ρ' (a b : Fin (L + 1)) (hab : a.val = b.val) (h) :
    amor Z p L F s' v₁ v₂ (xv a) (zv b) h =
      eqToHom (congrArg (fun t ↦ Z.x (p + t)) hab) ≫ Z.ρ (p + b.val) := by
  simp only [amor, hab, dite_true]
  rfl

lemma amor_σ' (a b : Fin (L + 1)) (hab : a.val = b.val + 1) (h) :
    amor Z p L F s' v₁ v₂ (xv a) (zv b) h =
      eqToHom (congrArg (fun t ↦ Z.x (p + t)) hab) ≫ Z.σ (p + b.val) := by
  have : ¬a.val = b.val := by omega
  simp only [amor, this, dite_false]
  rfl

lemma amor_a' (a : Fin (L + 1)) (ha : a.val = 0) (i : Fin 2) (h) :
    amor Z p L F s' v₁ v₂ (xv a) (lf i) h =
      eqToHom (congrArg (fun t ↦ Z.x (p + t)) ha) ≫ (F i).2 := rfl

lemma amor_sm' (b : Fin (L + 1)) (hb : b.val = L) (h) :
    amor Z p L F s' v₁ v₂ mv (zv b) h = s' ≫ eqToHom (congrArg (fun t ↦ Z.z (p + t)) hb.symm) :=
  rfl

lemma amor_ρ (j : Fin (L + 1)) (h) : amor Z p L F s' v₁ v₂ (xv j) (zv j) h = Z.ρ (p + j.val) := by
  simp only [amor, dite_true]
  exact Category.id_comp _

lemma amor_σ (j : Fin L) (h) :
    amor Z p L F s' v₁ v₂ (xv j.succ) (zv j.castSucc) h = Z.σ (p + j.val) := by
  simp only [amor, Fin.val_succ, Fin.coe_castSucc, Nat.succ_ne_self, dite_false]
  exact Category.id_comp _

lemma amor_a (i : Fin 2) (h) : amor Z p L F s' v₁ v₂ (xv 0) (lf i) h = (F i).2 :=
  Category.id_comp _

lemma amor_sm (h) : amor Z p L F s' v₁ v₂ mv (zv (Fin.last L)) h = s' :=
  Category.comp_id _

lemma mid {u b w : ZA L} (h1 : R u b) (h2 : R b w) : b = mv ∧ u = xe := by
  cases h1 <;> cases h2 <;> exact ⟨rfl, rfl⟩

lemma amor_v1 (h) : amor Z p L F s' v₁ v₂ xe mv h = v₁ := rfl

lemma amor_v2 (h) : amor Z p L F s' v₁ v₂ mv ee h = v₂ := rfl

end ZA

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

open ZA in
include B in
/-- **No zigzag with a fork and an arm in `P/τ`** (BO13a figures 5.2, 5.3). -/
theorem not_zigzag_arm
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) (Z : ZChain P) (p L : ℕ) (F : Fin 2 → BMor (Z.x p)) {M E : P}
    (s' : M ⟶ Z.z (p + L)) (v₁ : Z.x (p + L + 1) ⟶ M) (v₂ : M ⟶ E)
    (hfac : v₁ ≫ s' = Z.σ (p + L))
    (hρ : ∀ j ≤ L, ¬FactorsThroughMorphism τ (Z.ρ (p + j)))
    (hσ : ∀ j < L, ¬FactorsThroughMorphism τ (Z.σ (p + j)))
    (hσL : ¬FactorsThroughMorphism τ (Z.σ (p + L)))
    (hF : ∀ i, ¬FactorsThroughMorphism τ (F i).2) (hs : ¬FactorsThroughMorphism τ s')
    (hv₁ : ¬FactorsThroughMorphism τ v₁) (hv₂ : ¬FactorsThroughMorphism τ v₂)
    (hv₁₂ : ¬FactorsThroughMorphism τ (v₁ ≫ v₂))
    (hFi : ∀ i, ¬IsIso (F i).2) (his : ¬IsIso s') (hiv₁ : ¬IsIso v₁) (hiv₂ : ¬IsIso v₂)
    (hFF : ∀ i i', i ≠ i' → ¬∃ g, (F i).2 ≫ g = (F i').2)
    (hFρ : ∀ i, ¬∃ g, (F i).2 ≫ g = Z.ρ p) (hρF : ∀ i, ¬∃ g, Z.ρ p ≫ g = (F i).2)
    (hsv : ¬∃ g, s' ≫ g = v₂) (hvs : ¬∃ g, v₂ ≫ g = s')
    (hρs : ¬∃ g, g ≫ Z.ρ (p + L) = s') (hsρ : ¬∃ g, g ≫ s' = Z.ρ (p + L)) : False := by
  have ho : ∀ u v, R u v → (graph L).Adj u v := fun u v h ↦ adj_iff.2 (Or.inl h)
  haveI : Fact (LargeIndecomposable.Foundations.Quiver.IsAcyclic (OT (graph L) R)) :=
    ⟨OT.isAcyclic ho (fun _ _ h ↦ R_asymm h) isAcyclic⟩
  let φ : OT (graph L) R ⥤q P :=
    { obj := fun u ↦ aobj Z p L F (M := M) (E := E) u.as
      map := fun {u w} e ↦ amor Z p L F s' v₁ v₂ u.as w.as (OT.hom_down e) }
  have harr : ∀ u w (h : R u w), ¬FactorsThroughMorphism τ (amor Z p L F s' v₁ v₂ u w h) ∧
      ¬IsIso (amor Z p L F s' v₁ v₂ u w h) := by
    intro u w h
    cases h with
    | ρ j => rw [amor_ρ]; exact ⟨hρ j (by omega), Z.ρ_not_isIso _⟩
    | σ j => rw [amor_σ]; exact ⟨hσ j j.2, Z.σ_not_isIso _⟩
    | sm => rw [amor_sm]; exact ⟨hs, his⟩
    | v1 => exact ⟨hv₁, hiv₁⟩
    | v2 => exact ⟨hv₂, hiv₂⟩
    | a i => rw [amor_a]; exact ⟨hF i, hFi i⟩
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
        change ¬FactorsThroughMorphism τ (𝟙 _ ≫ amor Z p L F s' v₁ v₂ u w he)
        rw [Category.id_comp]
        exact (harr u w he).1
      | cons q e' =>
        rename_i w2
        rcases w2 with ⟨w2⟩
        have he' := OT.hom_down e'
        obtain ⟨rfl, rfl⟩ := mid he' he
        cases q with
        | nil =>
          change ¬FactorsThroughMorphism τ ((𝟙 _ ≫ amor Z p L F s' v₁ v₂ xe mv he') ≫
            amor Z p L F s' v₁ v₂ mv w he)
          rw [Category.id_comp, amor_v1]
          rcases R_mv he with ⟨c, rfl, hc⟩ | rfl
          · obtain rfl : c = Fin.last L := Fin.ext hc
            rw [amor_sm]
            change ¬FactorsThroughMorphism τ (v₁ ≫ s')
            rw [hfac]
            exact hσL
          · rw [amor_v2]
            exact hv₁₂
        | cons q e'' =>
          exact (R_to_xe (OT.hom_down e'')).elim
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
      obtain ⟨rfl, rfl⟩ := mid he' (OT.hom_down f)
      exact hne (congrArg OT.mk (R_xe he))
    | nil =>
      change amor Z p L F s' v₁ v₂ u c he ≫ g = 𝟙 _ ≫ amor Z p L F s' v₁ v₂ u c' he' at hg
      rw [Category.id_comp] at hg
      cases he with
      | ρ j =>
        obtain ⟨j, hj⟩ := j
        rw [amor_ρ] at hg
        rcases R_xv he' with ⟨⟨b, hb0⟩, rfl, hb⟩ | ⟨⟨b, hb0⟩, rfl, hb⟩ | ⟨i, rfl, hb⟩ <;>
          simp only at hb <;> subst hb
        · exact hne rfl
        · rw [amor_σ' _ _ rfl, ZChain.eqToHom_self_comp] at hg
          exact Z.valley₂ (p + b) ⟨g, hg⟩
        · rw [amor_a' _ rfl, ZChain.eqToHom_self_comp] at hg
          exact hρF i ⟨g, hg⟩
      | σ j =>
        rw [amor_σ] at hg
        rcases R_xv he' with ⟨⟨b, hb0⟩, rfl, hb⟩ | ⟨⟨b, hb0⟩, rfl, hb⟩ | ⟨i, rfl, hb⟩ <;>
          simp only [Fin.val_succ] at hb
        · subst hb
          rw [amor_ρ' j.succ ⟨j.val + 1, hb0⟩ rfl, ZChain.eqToHom_self_comp] at hg
          exact Z.valley₁ (p + j) ⟨g, hg⟩
        · exact hne (congrArg OT.mk (congrArg zv (Fin.ext (by simp; omega))))
        · omega
      | sm =>
        rw [amor_sm] at hg
        rcases R_mv he' with ⟨b, rfl, hb⟩ | rfl
        · exact hne (congrArg OT.mk (congrArg zv (Fin.ext (by simp [hb]))))
        · rw [amor_v2] at hg
          exact hsv ⟨g, hg⟩
      | v1 =>
        exact hne (congrArg OT.mk (R_xe he').symm)
      | v2 =>
        rw [amor_v2] at hg
        rcases R_mv he' with ⟨b, rfl, hb⟩ | rfl
        · obtain rfl : b = Fin.last L := Fin.ext hb
          rw [amor_sm] at hg
          exact hvs ⟨g, hg⟩
        · exact hne rfl
      | a i =>
        rw [amor_a] at hg
        rcases R_xv he' with ⟨⟨b, hb0⟩, rfl, hb⟩ | ⟨⟨b, hb0⟩, rfl, hb⟩ | ⟨i', rfl, hb⟩ <;>
          simp only [Fin.val_zero] at hb
        · subst hb
          rw [amor_ρ' 0 ⟨0, hb0⟩ rfl] at hg
          exact hFρ i ⟨g, hg.trans (ZChain.eqToHom_self_comp _ _)⟩
        · omega
        · rw [amor_a] at hg
          exact hFF i i' (fun h ↦ hne (by rw [h])) ⟨g, hg⟩
  · intro u c c' w e e' q hne ⟨g, hg⟩
    rcases u with ⟨u⟩
    rcases c with ⟨c⟩
    rcases c' with ⟨c'⟩
    rcases w with ⟨w⟩
    have he := OT.hom_down e
    have he' := OT.hom_down e'
    cases he with
    | ρ j =>
      rcases R_to_zv he' with ⟨⟨a, ha0⟩, rfl, ha⟩ | ⟨⟨a, ha0⟩, rfl, ha⟩ | ⟨rfl, hjL⟩
      · simp only at ha
        exact hne (congrArg OT.mk (congrArg xv (Fin.ext (by simp [ha]))))
      · simp only at ha
        subst a
        cases q with
        | cons q e3 => exact (R_to_xv (OT.hom_down e3)).elim
        | nil =>
          change g ≫ amor Z p L F s' v₁ v₂ (xv j) (zv j) e.down =
            𝟙 _ ≫ amor Z p L F s' v₁ v₂ (xv ⟨j.val + 1, ha0⟩) (zv j) he' at hg
          rw [Category.id_comp, amor_ρ, amor_σ' ⟨j.val + 1, ha0⟩ j rfl] at hg
          exact Z.peak₂ (p + j) ⟨g, hg.trans (ZChain.eqToHom_self_comp _ _)⟩
      · obtain rfl : j = Fin.last L := Fin.ext hjL
        cases q with
        | nil =>
          change g ≫ amor Z p L F s' v₁ v₂ (xv (Fin.last L)) (zv (Fin.last L)) e.down =
            𝟙 _ ≫ amor Z p L F s' v₁ v₂ mv (zv (Fin.last L)) he' at hg
          rw [Category.id_comp, amor_ρ, amor_sm] at hg
          exact hρs ⟨g, hg⟩
        | cons q e3 =>
          rename_i w3
          rcases w3 with ⟨w3⟩
          obtain rfl := R_to_mv (OT.hom_down e3)
          cases q with
          | cons q e4 => exact (R_to_xe (OT.hom_down e4)).elim
          | nil =>
            change g ≫ amor Z p L F s' v₁ v₂ (xv (Fin.last L)) (zv (Fin.last L)) e.down =
              (𝟙 _ ≫ amor Z p L F s' v₁ v₂ xe mv (OT.hom_down e3)) ≫
                amor Z p L F s' v₁ v₂ mv (zv (Fin.last L)) he' at hg
            rw [Category.id_comp, amor_ρ, amor_v1, amor_sm] at hg
            exact Z.peak₂ (p + L) ⟨g, hg.trans hfac⟩
    | σ j =>
      rcases R_to_zv he' with ⟨⟨a, ha0⟩, rfl, ha⟩ | ⟨⟨a, ha0⟩, rfl, ha⟩ | ⟨rfl, hjL⟩
      · simp only [Fin.val_castSucc] at ha
        subst ha
        cases q with
        | cons q e3 => exact (R_to_xv (OT.hom_down e3)).elim
        | nil =>
          change g ≫ amor Z p L F s' v₁ v₂ (xv j.succ) (zv j.castSucc) e.down =
            𝟙 _ ≫ amor Z p L F s' v₁ v₂ (xv ⟨j, ha0⟩) (zv j.castSucc) he' at hg
          rw [Category.id_comp, amor_σ, amor_ρ' ⟨j, ha0⟩ j.castSucc rfl] at hg
          exact Z.peak₁ (p + j) ⟨g, hg.trans (ZChain.eqToHom_self_comp _ _)⟩
      · simp only [Fin.val_castSucc] at ha
        exact hne (congrArg OT.mk (congrArg xv (Fin.ext (by simp [ha]))))
      · simp only [Fin.val_castSucc] at hjL
        have := j.2
        omega
    | sm =>
      rcases R_to_zv he' with ⟨⟨a, ha0⟩, rfl, ha⟩ | ⟨⟨a, ha0⟩, rfl, ha⟩ | ⟨rfl, -⟩
      · simp only [Fin.val_last] at ha
        subst a
        cases q with
        | cons q e3 => exact (R_to_xv (OT.hom_down e3)).elim
        | nil =>
          change g ≫ amor Z p L F s' v₁ v₂ mv (zv (Fin.last L)) e.down =
            𝟙 _ ≫ amor Z p L F s' v₁ v₂ (xv ⟨L, ha0⟩) (zv (Fin.last L)) he' at hg
          rw [Category.id_comp, amor_sm, amor_ρ' ⟨L, ha0⟩ (Fin.last L) rfl] at hg
          exact hsρ ⟨g, hg.trans (ZChain.eqToHom_self_comp _ _)⟩
      · simp only [Fin.val_last] at ha
        omega
      · exact hne rfl
    | v1 => exact hne (congrArg OT.mk (R_to_mv he').symm)
    | v2 => exact hne (congrArg OT.mk (R_to_ee he').symm)
    | a i => exact hne (congrArg OT.mk (R_to_lf he').symm)

end MulBasis

end RayQuiver

end LargeIndecomposable
