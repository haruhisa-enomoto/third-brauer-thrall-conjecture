module

public import LargeIndecomposable.Cleaving.Zigzags.ZigzagFork

/-!
# Zigzags ending at a sink with two in-arrows

The diagram: two arrows out of `x p`; the zigzag `ρ (p+j)` (`j ≤ L`),
`σ (p+j)` (`j < L`) ending at the sink `z (p+L)`; two morphisms into
`z (p+L)`. It is a bipartite orientation of `D̃₂ₗ₊₅` (`RayCat.ZW`); the
contradiction is `RayQuiver.MulBasis.not_zigzag_forks_in` (BO13a Lemma 5 a),
case `τ = σᵢ`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

/-- The vertices. -/
inductive ZW (L : ℕ) : Type
  | xv (j : Fin (L + 1))
  | zv (j : Fin (L + 1))
  | lfA (i : Fin 2)
  | lfB (i : Fin 2)
  deriving DecidableEq

namespace ZW

variable {L : ℕ}

/-- The directed edges (source to sink). -/
inductive R : ZW L → ZW L → Prop
  | ρ (j : Fin (L + 1)) : R (xv j) (zv j)
  | σ (j : Fin L) : R (xv j.succ) (zv j.castSucc)
  | a (i : Fin 2) : R (xv 0) (lfA i)
  | b (i : Fin 2) : R (lfB i) (zv (Fin.last L))

/-- The colouring: sources are the `xv` and `lfB`. -/
def col : ZW L → Bool
  | xv _ => true
  | lfB _ => true
  | _ => false

lemma col_of_R {u v : ZW L} (h : R u v) : col u = true ∧ col v = false := by
  cases h <;> exact ⟨rfl, rfl⟩

variable (L) in
/-- The graph. -/
def graph : SimpleGraph (ZW L) := SimpleGraph.fromRel R

lemma adj_iff {u v : ZW L} : (graph L).Adj u v ↔ R u v ∨ R v u := by
  rw [graph, SimpleGraph.fromRel_adj]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  rintro rfl
  rcases h with h | h <;> have := col_of_R h <;> rw [this.1] at this <;> cases this.2

lemma col_ne (u v : ZW L) (h : (graph L).Adj u v) : col u ≠ col v := by
  rcases adj_iff.1 h with h | h <;> have := col_of_R h <;> rw [this.1, this.2] <;> decide

instance : Fintype (ZW L) where
  elems := (Finset.univ.map ⟨xv, fun _ _ h ↦ by cases h; rfl⟩) ∪
    (Finset.univ.map ⟨zv, fun _ _ h ↦ by cases h; rfl⟩) ∪
    (Finset.univ.map ⟨lfA, fun _ _ h ↦ by cases h; rfl⟩) ∪
    (Finset.univ.map ⟨lfB, fun _ _ h ↦ by cases h; rfl⟩)
  complete v := by
    cases v
    · simp only [Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and]
      exact Or.inl (Or.inl (Or.inl ⟨_, rfl⟩))
    · simp only [Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and]
      exact Or.inl (Or.inl (Or.inr ⟨_, rfl⟩))
    · simp only [Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and]
      exact Or.inl (Or.inr ⟨_, rfl⟩)
    · simp only [Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and]
      exact Or.inr ⟨_, rfl⟩

lemma R_ρ' {a b : Fin (L + 1)} (h : a.val = b.val) : R (xv a) (zv b) := by
  obtain rfl : a = b := Fin.ext h
  exact R.ρ a

lemma R_σ' {a b : Fin (L + 1)} (h : a.val = b.val + 1) : R (xv a) (zv b) := by
  have hb : b.val < L := by have := a.2; omega
  convert R.σ (L := L) ⟨b.val, hb⟩ using 2
  · ext; simp; omega
  · rfl

lemma R_a' {a : Fin (L + 1)} (h : a.val = 0) (i : Fin 2) : R (xv a) (lfA i) := by
  obtain rfl : a = 0 := Fin.ext h
  exact R.a i

lemma R_b' {b : Fin (L + 1)} (h : b.val = L) (i : Fin 2) : R (lfB i) (zv b) := by
  obtain rfl : b = Fin.last L := Fin.ext h
  exact R.b i

open LargeIndecomposable.Foundations.Quiver in
/-- The vertex map of the copy of `D̃₂ₗ₊₅`. -/
def dmap : AffineD (2 * L + 1) → ZW L
  | .spine a => if h : a.val % 2 = 0 then xv ⟨a.val / 2, by have := a.isLt; omega⟩
      else zv ⟨a.val / 2, by have := a.isLt; omega⟩
  | .leaf i => if h : i.val < 2 then lfA ⟨i.val, h⟩ else lfB ⟨i.val - 2, by omega⟩

open LargeIndecomposable.Foundations.Quiver in
lemma dmap_adj_of_hom (a b : AffineD (2 * L + 1)) (e : Nonempty (a ⟶ b)) :
    (graph L).Adj (dmap a) (dmap b) := by
  rw [adj_iff]
  rcases a with i | j <;> rcases b with i' | j'
  · exact absurd e (AffineD.not_nonempty_hom_leaf _ _)
  · have hj := (AffineD.nonempty_leaf_spine_iff i j').1 e
    by_cases hi : i.val < 2
    · rw [AffineD.leafTarget_of_lt_two i hi] at hj
      subst hj
      right
      simp only [dmap, hi, dite_true, Fin.val_zero, Nat.zero_mod, Nat.zero_div]
      exact R_a' rfl _
    · rw [AffineD.leafTarget_of_not_lt_two i hi] at hj
      subst hj
      left
      have h2 : ¬(2 * L + 1) % 2 = 0 := by omega
      simp only [dmap, hi, dite_false, Fin.val_last, h2]
      exact R_b' (by simp; omega) _
  · exact absurd e (AffineD.not_nonempty_hom_leaf _ _)
  · have hj := (AffineD.nonempty_spine_spine_iff j j').1 e
    by_cases hp : j.val % 2 = 0
    · left
      have hq : ¬j'.val % 2 = 0 := by omega
      simp only [dmap, hp, hq, dite_true, dite_false]
      exact R_ρ' (by simp; omega)
    · right
      have hq : j'.val % 2 = 0 := by omega
      simp only [dmap, hp, hq, dite_true, dite_false]
      exact R_σ' (by simp; omega)

open LargeIndecomposable.Foundations.Quiver in
/-- The copy of `D̃₂ₗ₊₅`. -/
def dcopy : (underlyingGraph (AffineD (2 * L + 1))).Copy (graph L) where
  toHom := ⟨dmap, fun {a b} h ↦ by
    rcases (underlyingGraph_adj.1 h).2 with e | e
    · exact dmap_adj_of_hom a b e
    · exact (dmap_adj_of_hom b a e).symm⟩
  injective' a b h := by
    change dmap a = dmap b at h
    rcases a with i | j <;> rcases b with i' | j'
    · simp only [dmap] at h
      split_ifs at h with h1 h2 h2 <;> simp only [lfA.injEq, lfB.injEq, Fin.mk.injEq, reduceCtorEq] at h
      · exact congrArg _ (Fin.ext h)
      · exact congrArg _ (Fin.ext (by omega))
    · simp only [dmap] at h
      split_ifs at h <;> simp only [reduceCtorEq] at h
    · simp only [dmap] at h
      split_ifs at h <;> simp only [reduceCtorEq] at h
    · simp only [dmap] at h
      split_ifs at h with h1 h2 h2 <;> simp only [xv.injEq, zv.injEq, Fin.mk.injEq, reduceCtorEq] at h
      · exact congrArg _ (Fin.ext (by omega))
      · exact congrArg _ (Fin.ext (by omega))

end ZW

end RayCat

end LargeIndecomposable

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

namespace ZW

section Lemmas

variable {L : ℕ}

lemma R_of_adj {v w : ZW L} (h : (graph L).Adj v w) (hv : col v = true) : R v w := by
  rcases adj_iff.1 h with h | h
  · exact h
  · have := (col_of_R h).2
    rw [hv] at this
    cases this

lemma R_xv {a : Fin (L + 1)} {w : ZW L} (h : R (xv a) w) :
    (∃ b : Fin (L + 1), w = zv b ∧ a.val = b.val) ∨
      (∃ b : Fin (L + 1), w = zv b ∧ a.val = b.val + 1) ∨ ∃ i, w = lfA i ∧ a.val = 0 := by
  generalize hu : xv a = u at h
  cases h with
  | ρ j => cases hu; exact Or.inl ⟨_, rfl, rfl⟩
  | σ j =>
    simp only [xv.injEq] at hu
    subst hu
    exact Or.inr (Or.inl ⟨j.castSucc, rfl, by simp⟩)
  | a i => cases hu; exact Or.inr (Or.inr ⟨i, rfl, rfl⟩)
  | b i => cases hu

lemma R_lfB {i : Fin 2} {w : ZW L} (h : R (lfB i) w) : w = zv (Fin.last L) := by
  cases h; rfl

lemma xv_zv_val {a b : Fin (L + 1)} (h : R (xv a) (zv b)) (hab : ¬a.val = b.val) :
    a.val = b.val + 1 := by
  rcases R_xv h with ⟨c, hc, h1⟩ | ⟨c, hc, h1⟩ | ⟨i, hc, -⟩ <;>
    simp only [zv.injEq, reduceCtorEq] at hc
  · subst hc; exact absurd h1 hab
  · subst hc; exact h1

lemma xv_lf_val {a : Fin (L + 1)} {i : Fin 2} (h : R (xv a) (lfA i)) : a.val = 0 := by
  rcases R_xv h with ⟨c, hc, -⟩ | ⟨c, hc, -⟩ | ⟨i', hc, h1⟩ <;>
    simp only [lfA.injEq, reduceCtorEq] at hc
  exact h1

lemma lfB_zv_val {i : Fin 2} {b : Fin (L + 1)} (h : R (lfB i) (zv b)) : b.val = L := by
  have := R_lfB h
  simp only [zv.injEq] at this
  subst this
  rfl

end Lemmas

variable {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] (Z : ZChain Q) (p L : ℕ)
  (F : Fin 2 → BMor (Z.x p)) (G : Fin 2 → Σ y : Q, y ⟶ Z.z (p + L))

/-- The objects. -/
def wobj : ZW L → Q
  | xv j => Z.x (p + j.val)
  | zv j => Z.z (p + j.val)
  | lfA i => (F i).1
  | lfB i => (G i).1

/-- The morphisms. -/
def wmor : ∀ v w : ZW L, (graph L).Adj v w → col v = true → col w = false →
    (wobj Z p L F G v ⟶ wobj Z p L F G w)
  | xv a, zv b, h, hv, _ =>
    if hab : a.val = b.val then
      eqToHom (congrArg (fun t ↦ Z.x (p + t)) hab) ≫ Z.ρ (p + b.val)
    else
      eqToHom (congrArg (fun t ↦ Z.x (p + t)) (xv_zv_val (R_of_adj h hv) hab)) ≫ Z.σ (p + b.val)
  | xv a, lfA i, h, hv, _ =>
    eqToHom (congrArg (fun t ↦ Z.x (p + t)) (xv_lf_val (R_of_adj h hv))) ≫ (F i).2
  | lfB i, zv b, h, hv, _ =>
    (G i).2 ≫ eqToHom (congrArg (fun t ↦ Z.z (p + t)) (lfB_zv_val (R_of_adj h hv)).symm)
  | xv _, xv _, _, _, hw | xv _, lfB _, _, _, hw | lfB _, xv _, _, _, hw
  | lfB _, lfB _, _, _, hw => absurd hw (by simp [col])
  | lfB _, lfA _, h, hv, _ => absurd (R_lfB (R_of_adj h hv)) (by simp)
  | zv _, _, _, hv, _ | lfA _, _, _, hv, _ => absurd hv (by simp [col])

variable {Z p L F G}

lemma wmor_ρ' (a b : Fin (L + 1)) (hab : a.val = b.val) (h hv hw) :
    wmor Z p L F G (xv a) (zv b) h hv hw =
      eqToHom (congrArg (fun t ↦ Z.x (p + t)) hab) ≫ Z.ρ (p + b.val) := by
  simp only [wmor, hab, dite_true]
  rfl

lemma wmor_σ' (a b : Fin (L + 1)) (hab : a.val = b.val + 1) (h hv hw) :
    wmor Z p L F G (xv a) (zv b) h hv hw =
      eqToHom (congrArg (fun t ↦ Z.x (p + t)) hab) ≫ Z.σ (p + b.val) := by
  have : ¬a.val = b.val := by omega
  simp only [wmor, this, dite_false]
  rfl

lemma wmor_a' (a : Fin (L + 1)) (ha : a.val = 0) (i : Fin 2) (h hv hw) :
    wmor Z p L F G (xv a) (lfA i) h hv hw =
      eqToHom (congrArg (fun t ↦ Z.x (p + t)) ha) ≫ (F i).2 := rfl

lemma wmor_b' (b : Fin (L + 1)) (hb : b.val = L) (i : Fin 2) (h hv hw) :
    wmor Z p L F G (lfB i) (zv b) h hv hw =
      (G i).2 ≫ eqToHom (congrArg (fun t ↦ Z.z (p + t)) hb.symm) := rfl

lemma col_true {v : ZW L} (h : col v = true) : (∃ a, v = xv a) ∨ ∃ i, v = lfB i := by
  cases v with
  | xv a => exact Or.inl ⟨a, rfl⟩
  | lfB i => exact Or.inr ⟨i, rfl⟩
  | _ => simp [col] at h

end ZW

end RayCat

end LargeIndecomposable

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat.ZChain

variable {Q : Type} [Category.{0} Q]

lemma comp_eqToHom_self {X Y : Q} (f : X ⟶ Y) (h : Y = Y) : f ≫ eqToHom h = f := by simp

end RayCat.ZChain

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

open ZW in
include B in
/-- **No zigzag ending at a sink with two in-arrows in `P/τ`.** -/
theorem not_zigzag_forks_in
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) (Z : ZChain P) (p L : ℕ)
    (F : Fin 2 → BMor (Z.x p)) (G : Fin 2 → Σ y : P, y ⟶ Z.z (p + L))
    (hρ : ∀ j ≤ L, ¬FactorsThroughMorphism τ (Z.ρ (p + j)))
    (hσ : ∀ j < L, ¬FactorsThroughMorphism τ (Z.σ (p + j)))
    (hF : ∀ i, ¬FactorsThroughMorphism τ (F i).2) (hG : ∀ i, ¬FactorsThroughMorphism τ (G i).2)
    (hFi : ∀ i, ¬IsIso (F i).2) (hGi : ∀ i, ¬IsIso (G i).2)
    (hFF : ∀ i i', i ≠ i' → ¬∃ g, (F i).2 ≫ g = (F i').2)
    (hGG : ∀ i i', i ≠ i' → ¬∃ g, g ≫ (G i).2 = (G i').2)
    (hFρ : ∀ i, ¬∃ g, (F i).2 ≫ g = Z.ρ p) (hρF : ∀ i, ¬∃ g, Z.ρ p ≫ g = (F i).2)
    (hGρ : ∀ i, ¬∃ g, g ≫ (G i).2 = Z.ρ (p + L))
    (hρG : ∀ i, ¬∃ g, g ≫ Z.ρ (p + L) = (G i).2) : False := by
  have hD : ¬Statement.IsRepresentationFinite
      (Linearization (PathCat (BQ (ZW.graph L) ZW.col)) k) :=
    not_isRepresentationFinite_of_copy_affineD (2 * L + 1)
      ((BQ.graphIso ZW.col_ne).symm.toEmbedding.toCopy.comp ZW.dcopy)
  refine B.not_bq_diagram hmin hL hR τ hτ hτ0 (ZW.graph L) ZW.col hD (wobj Z p L F G)
    (wmor Z p L F G) ?_ ?_ ?_ ?_
  · intro v w h hv hw
    rcases col_true hv with ⟨⟨a, ha⟩, rfl⟩ | ⟨i, rfl⟩
    · rcases R_xv (R_of_adj h hv) with ⟨⟨c, hc0⟩, rfl, hc⟩ | ⟨⟨c, hc0⟩, rfl, hc⟩ |
          ⟨i, rfl, hc⟩ <;> simp only at hc <;> subst a
      · rw [wmor_ρ' _ _ rfl, ZChain.eqToHom_self_comp]; exact hρ c (by omega)
      · rw [wmor_σ' _ _ rfl, ZChain.eqToHom_self_comp]; exact hσ c (by omega)
      · rw [wmor_a' _ rfl, ZChain.eqToHom_self_comp]; exact hF i
    · obtain rfl := R_lfB (R_of_adj h hv)
      rw [wmor_b' _ rfl, ZChain.comp_eqToHom_self]; exact hG i
  · intro v w h hv hw
    rcases col_true hv with ⟨⟨a, ha⟩, rfl⟩ | ⟨i, rfl⟩
    · rcases R_xv (R_of_adj h hv) with ⟨⟨c, hc0⟩, rfl, hc⟩ | ⟨⟨c, hc0⟩, rfl, hc⟩ |
          ⟨i, rfl, hc⟩ <;> simp only at hc <;> subst a
      · rw [wmor_ρ' _ _ rfl, ZChain.eqToHom_self_comp]; exact Z.ρ_not_isIso _
      · rw [wmor_σ' _ _ rfl, ZChain.eqToHom_self_comp]; exact Z.σ_not_isIso _
      · rw [wmor_a' _ rfl, ZChain.eqToHom_self_comp]; exact hFi i
    · obtain rfl := R_lfB (R_of_adj h hv)
      rw [wmor_b' _ rfl, ZChain.comp_eqToHom_self]; exact hGi i
  · intro v w w' h h' hv hw hw' hne ⟨g, hg⟩
    rcases col_true hv with ⟨⟨a, ha⟩, rfl⟩ | ⟨i, rfl⟩
    · rcases R_xv (R_of_adj h hv) with ⟨⟨c, hc0⟩, rfl, hc⟩ | ⟨⟨c, hc0⟩, rfl, hc⟩ |
          ⟨i, rfl, hc⟩ <;>
        rcases R_xv (R_of_adj h' hv) with ⟨⟨c', hc0'⟩, rfl, hc'⟩ | ⟨⟨c', hc0'⟩, rfl, hc'⟩ |
          ⟨i', rfl, hc'⟩ <;>
        simp only at hc hc' <;> subst hc
      · exact hne (by subst hc'; rfl)
      · subst hc'
        rw [wmor_ρ' _ _ rfl, wmor_σ' _ _ rfl, ZChain.eqToHom_self_comp,
          ZChain.eqToHom_self_comp] at hg
        exact Z.valley₂ (p + c') ⟨g, hg⟩
      · subst hc'
        rw [wmor_ρ' _ _ rfl, wmor_a' _ rfl, ZChain.eqToHom_self_comp,
          ZChain.eqToHom_self_comp] at hg
        exact hρF i' ⟨g, hg⟩
      · subst hc'
        rw [wmor_σ' _ _ rfl, wmor_ρ' _ _ rfl, ZChain.eqToHom_self_comp,
          ZChain.eqToHom_self_comp] at hg
        exact Z.valley₁ (p + c) ⟨g, hg⟩
      · exact hne (by obtain rfl : c = c' := by omega
                      rfl)
      · omega
      · subst hc'
        rw [wmor_a' _ rfl, wmor_ρ' _ _ rfl, ZChain.eqToHom_self_comp,
          ZChain.eqToHom_self_comp] at hg
        exact hFρ i ⟨g, hg⟩
      · omega
      · rw [wmor_a' _ rfl, wmor_a' _ rfl, ZChain.eqToHom_self_comp,
          ZChain.eqToHom_self_comp] at hg
        exact hFF i i' (fun e ↦ hne (by rw [e])) ⟨g, hg⟩
    · obtain rfl := R_lfB (R_of_adj h hv)
      obtain rfl := R_lfB (R_of_adj h' hv)
      exact hne rfl
  · intro v v' w h h' hv hv' hw hne ⟨g, hg⟩
    rcases col_true hv with ⟨⟨a, ha⟩, rfl⟩ | ⟨i, rfl⟩ <;>
      rcases col_true hv' with ⟨⟨a', ha'⟩, rfl⟩ | ⟨i', rfl⟩
    · rcases R_xv (R_of_adj h hv) with ⟨⟨c, hc0⟩, rfl, hc⟩ | ⟨⟨c, hc0⟩, rfl, hc⟩ |
          ⟨i, rfl, hc⟩ <;>
        rcases R_xv (R_of_adj h' hv') with ⟨⟨c', hc0'⟩, hw', hc'⟩ | ⟨⟨c', hc0'⟩, hw', hc'⟩ |
          ⟨i', hw', hc'⟩ <;>
        simp only [zv.injEq, lfA.injEq, Fin.mk.injEq, reduceCtorEq] at hw' <;>
        simp only at hc hc' <;> subst hc hc'
      · exact hne (by subst hw'; rfl)
      · subst hw'
        rw [wmor_ρ' _ _ rfl, wmor_σ' _ _ rfl, ZChain.eqToHom_self_comp,
          ZChain.eqToHom_self_comp] at hg
        exact Z.peak₂ _ ⟨g, hg⟩
      · subst hw'
        rw [wmor_σ' _ _ rfl, wmor_ρ' _ _ rfl, ZChain.eqToHom_self_comp,
          ZChain.eqToHom_self_comp] at hg
        exact Z.peak₁ _ ⟨g, hg⟩
      · exact hne (by subst hw'; rfl)
      · exact hne rfl
    · obtain rfl := R_lfB (R_of_adj h' hv')
      rcases R_xv (R_of_adj h hv) with ⟨⟨c, hc0⟩, hw, hc⟩ | ⟨⟨c, hc0⟩, hw, hc⟩ |
          ⟨i, hw, hc⟩ <;> simp only [zv.injEq, reduceCtorEq, Fin.ext_iff, Fin.val_last] at hw <;>
        simp only at hc <;> subst a
      · obtain rfl : c = L := hw.symm
        rw [wmor_ρ' ⟨c, ha⟩ (Fin.last c) rfl, wmor_b' (Fin.last c) rfl, ZChain.eqToHom_self_comp,
          ZChain.comp_eqToHom_self] at hg
        exact hρG i' ⟨g, hg⟩
      · omega
    · obtain rfl := R_lfB (R_of_adj h hv)
      rcases R_xv (R_of_adj h' hv') with ⟨⟨c, hc0⟩, hw, hc⟩ | ⟨⟨c, hc0⟩, hw, hc⟩ |
          ⟨i', hw, hc⟩ <;> simp only [zv.injEq, reduceCtorEq, Fin.ext_iff, Fin.val_last] at hw <;>
        simp only at hc <;> subst a'
      · obtain rfl : c = L := hw.symm
        rw [wmor_b' (Fin.last c) rfl, wmor_ρ' ⟨c, ha'⟩ (Fin.last c) rfl, ZChain.eqToHom_self_comp,
          ZChain.comp_eqToHom_self] at hg
        exact hGρ i ⟨g, hg⟩
      · omega
    · obtain rfl := R_lfB (R_of_adj h hv)
      rw [wmor_b' _ rfl, wmor_b' _ rfl, ZChain.comp_eqToHom_self,
        ZChain.comp_eqToHom_self] at hg
      exact hGG i i' (fun e ↦ hne (by rw [e])) ⟨g, hg⟩

end MulBasis

end RayQuiver

end LargeIndecomposable
