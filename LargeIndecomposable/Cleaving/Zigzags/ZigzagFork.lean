module

public import LargeIndecomposable.Cleaving.PathCategories.BipTree

/-!
# Zigzags with forks: `D̃` cleaving diagrams

An `ℕ`-indexed chain (`RayCat.ZChain`) has objects `x t`, `z t` and morphisms
`ρ t : x t ⟶ z t`, `σ t : x (t + 1) ⟶ z t` with the peak and valley
conditions. A segment of length `L + 1` from `x p` to `x (p + L + 1)`, with two
extra morphisms out of each end, is a bipartite diagram of type `D̃`
(`RayCat.ZV`, `RayCat.zgraph`). If it avoids `τ` and the forks satisfy the
zigzag conditions, it contradicts minimality
(`RayQuiver.MulBasis.not_zigzag_forks`; BO13a figure 5.1).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable (Q : Type) [Category.{0} Q] [HasZeroMorphisms Q]

/-- An `ℕ`-indexed chain: peaks `ρ t, σ t` at `z t`, valleys `σ t, ρ (t+1)` at
`x (t+1)`. -/
structure ZChain where
  x : ℕ → Q
  z : ℕ → Q
  ρ : ∀ t, x t ⟶ z t
  σ : ∀ t, x (t + 1) ⟶ z t
  ρ_ne : ∀ t, ρ t ≠ 0
  σ_ne : ∀ t, σ t ≠ 0
  peak₁ : ∀ t, ¬∃ c, c ≫ σ t = ρ t
  peak₂ : ∀ t, ¬∃ c, c ≫ ρ t = σ t
  valley₁ : ∀ t, ¬∃ c, σ t ≫ c = ρ (t + 1)
  valley₂ : ∀ t, ¬∃ c, ρ (t + 1) ≫ c = σ t

/-- The vertices of a zigzag of length `L + 1` with forks: sources `xv`, sinks
`zv`, and two leaves at each end. -/
inductive ZV (L : ℕ) : Type
  | xv (j : Fin (L + 2))
  | zv (j : Fin (L + 1))
  | lfA (i : Fin 2)
  | lfB (i : Fin 2)
  deriving DecidableEq

namespace ZV

variable {L : ℕ}

/-- The directed edges (source to sink). -/
inductive R : ZV L → ZV L → Prop
  | ρ (j : Fin (L + 1)) : R (xv j.castSucc) (zv j)
  | σ (j : Fin (L + 1)) : R (xv j.succ) (zv j)
  | a (i : Fin 2) : R (xv 0) (lfA i)
  | b (i : Fin 2) : R (xv (Fin.last _)) (lfB i)

/-- The colouring: sources are the `xv`. -/
def col : ZV L → Bool
  | xv _ => true
  | _ => false

lemma R_ρ' {a : Fin (L + 2)} {b : Fin (L + 1)} (h : a.val = b.val) : R (xv a) (zv b) := by
  obtain rfl : a = b.castSucc := Fin.ext h
  exact R.ρ b

lemma R_σ' {a : Fin (L + 2)} {b : Fin (L + 1)} (h : a.val = b.val + 1) : R (xv a) (zv b) := by
  obtain rfl : a = b.succ := Fin.ext h
  exact R.σ b

lemma R_a' {a : Fin (L + 2)} (h : a.val = 0) (i : Fin 2) : R (xv a) (lfA i) := by
  obtain rfl : a = 0 := Fin.ext h
  exact R.a i

lemma R_b' {a : Fin (L + 2)} (h : a.val = L + 1) (i : Fin 2) : R (xv a) (lfB i) := by
  obtain rfl : a = Fin.last _ := Fin.ext h
  exact R.b i

lemma col_of_R {u v : ZV L} (h : R u v) : col u = true ∧ col v = false := by
  cases h <;> exact ⟨rfl, rfl⟩

variable (L) in
/-- The graph of the zigzag with forks. -/
def graph : SimpleGraph (ZV L) := SimpleGraph.fromRel R

lemma adj_iff {u v : ZV L} : (graph L).Adj u v ↔ R u v ∨ R v u := by
  rw [graph, SimpleGraph.fromRel_adj]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  rintro rfl
  rcases h with h | h <;> have := col_of_R h <;> rw [this.1] at this <;> cases this.2

lemma col_ne (u v : ZV L) (h : (graph L).Adj u v) : col u ≠ col v := by
  rcases adj_iff.1 h with h | h <;> have := col_of_R h <;> rw [this.1, this.2] <;> decide

instance : Fintype (ZV L) where
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

open LargeIndecomposable.Foundations.Quiver in
/-- The spine of `D̃` runs through the zigzag; the leaves go to the forks. -/
def dmap : AffineD (2 * L + 2) → ZV L
  | .spine a => if h : a.val % 2 = 0 then xv ⟨a.val / 2, by have := a.isLt; omega⟩
      else zv ⟨a.val / 2, by have := a.isLt; omega⟩
  | .leaf i => if h : i.val < 2 then lfA ⟨i.val, h⟩ else lfB ⟨i.val - 2, by omega⟩

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
      simp only [dmap, hi, dite_true, Fin.val_zero, Nat.zero_mod, Nat.zero_div]
      exact R_a' rfl _
    · rw [AffineD.leafTarget_of_not_lt_two i hi] at hj
      subst hj
      right
      have h2 : (2 * L + 2) % 2 = 0 := by omega
      simp only [dmap, hi, dite_false, Fin.val_last, h2, dite_true]
      exact R_b' (by simp) _
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
/-- The copy of `D̃₂ₗ₊₆` in the zigzag graph. -/
def dcopy : (underlyingGraph (AffineD (2 * L + 2))).Copy (graph L) where
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

end ZV

end RayCat

end LargeIndecomposable

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

namespace RayCat

namespace ZV

variable {L : ℕ}

lemma R_cases {v w : ZV L} (h : R v w) :
    (∃ j : Fin (L + 1), v = xv j.castSucc ∧ w = zv j) ∨ (∃ j : Fin (L + 1), v = xv j.succ ∧ w = zv j) ∨
      (∃ i, v = xv 0 ∧ w = lfA i) ∨ ∃ i, v = xv (Fin.last _) ∧ w = lfB i := by
  cases h with
  | ρ j => exact Or.inl ⟨j, rfl, rfl⟩
  | σ j => exact Or.inr (Or.inl ⟨j, rfl, rfl⟩)
  | a i => exact Or.inr (Or.inr (Or.inl ⟨i, rfl, rfl⟩))
  | b i => exact Or.inr (Or.inr (Or.inr ⟨i, rfl, rfl⟩))

lemma R_of_adj {v w : ZV L} (h : (graph L).Adj v w) (hv : col v = true) : R v w := by
  rcases adj_iff.1 h with h | h
  · exact h
  · have := (col_of_R h).2
    rw [hv] at this
    cases this

variable {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] (Z : ZChain Q) (p L : ℕ)
  (F : Fin 2 → BMor (Z.x p)) (G : Fin 2 → BMor (Z.x (p + L + 1)))

/-- The objects of the zigzag diagram. -/
def zobj : ZV L → Q
  | xv j => Z.x (p + j.val)
  | zv j => Z.z (p + j.val)
  | lfA i => (F i).1
  | lfB i => (G i).1

/-- The morphisms of the zigzag diagram. -/
def zmor : ∀ v w : ZV L, (graph L).Adj v w → col v = true → col w = false →
    (zobj Z p L F G v ⟶ zobj Z p L F G w)
  | xv a, zv b, h, _, _ =>
    if hab : a.val = b.val then
      eqToHom (congrArg (fun t ↦ Z.x (p + t)) hab) ≫ Z.ρ (p + b.val)
    else
      eqToHom (congrArg (fun t ↦ Z.x (p + t)) (show a.val = b.val + 1 by
        rcases R_cases (R_of_adj h rfl) with ⟨j, h1, h2⟩ | ⟨j, h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨i, h1, h2⟩
        · cases h1; cases h2; exact absurd rfl hab
        · cases h1; cases h2; rfl
        · cases h2
        · cases h2)) ≫ Z.σ (p + b.val)
  | xv a, lfA i, h, _, _ =>
    eqToHom (congrArg (fun t ↦ Z.x (p + t)) (show a.val = 0 by
      rcases R_cases (R_of_adj h rfl) with ⟨j, h1, h2⟩ | ⟨j, h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨i, h1, h2⟩
      · cases h2
      · cases h2
      · cases h1; rfl
      · cases h2)) ≫ (F i).2
  | xv a, lfB i, h, _, _ =>
    eqToHom (congrArg (fun t ↦ Z.x (p + t)) (show a.val = L + 1 by
      rcases R_cases (R_of_adj h rfl) with ⟨j, h1, h2⟩ | ⟨j, h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨i, h1, h2⟩
      · cases h2
      · cases h2
      · cases h2
      · cases h1; rfl)) ≫ (G i).2
  | xv a, xv b, h, _, hw => absurd hw (by simp [col])
  | zv _, _, _, hv, _ => absurd hv (by simp [col])
  | lfA _, _, _, hv, _ => absurd hv (by simp [col])
  | lfB _, _, _, hv, _ => absurd hv (by simp [col])

variable {Z p L F G}

lemma zmor_ρ (j : Fin (L + 1)) (h hv hw) :
    zmor Z p L F G (xv j.castSucc) (zv j) h hv hw = Z.ρ (p + j.val) := by
  simp only [zmor, Fin.coe_castSucc, dite_true]
  exact Category.id_comp _

lemma zmor_σ (j : Fin (L + 1)) (h hv hw) :
    zmor Z p L F G (xv j.succ) (zv j) h hv hw = Z.σ (p + j.val) := by
  simp only [zmor, Fin.val_succ, Nat.succ_ne_self, dite_false]
  exact Category.id_comp _

lemma zmor_a (i : Fin 2) (h hv hw) : zmor Z p L F G (xv 0) (lfA i) h hv hw = (F i).2 :=
  Category.id_comp _

lemma zmor_b (i : Fin 2) (h hv hw) :
    zmor Z p L F G (xv (Fin.last _)) (lfB i) h hv hw = (G i).2 :=
  Category.id_comp _

lemma zmor_ρ' (a : Fin (L + 2)) (b : Fin (L + 1)) (hab : a.val = b.val) (h hv hw) :
    zmor Z p L F G (xv a) (zv b) h hv hw =
      eqToHom (congrArg (fun t ↦ Z.x (p + t)) hab) ≫ Z.ρ (p + b.val) := by
  simp only [zmor, hab, dite_true]
  rfl

lemma zmor_σ' (a : Fin (L + 2)) (b : Fin (L + 1)) (hab : a.val = b.val + 1) (h hv hw) :
    zmor Z p L F G (xv a) (zv b) h hv hw =
      eqToHom (congrArg (fun t ↦ Z.x (p + t)) hab) ≫ Z.σ (p + b.val) := by
  have : ¬a.val = b.val := by omega
  simp only [zmor, this, dite_false]
  rfl

lemma zmor_a' (a : Fin (L + 2)) (ha : a.val = 0) (i : Fin 2) (h hv hw) :
    zmor Z p L F G (xv a) (lfA i) h hv hw =
      eqToHom (congrArg (fun t ↦ Z.x (p + t)) ha) ≫ (F i).2 := rfl

lemma zmor_b' (a : Fin (L + 2)) (ha : a.val = L + 1) (i : Fin 2) (h hv hw) :
    zmor Z p L F G (xv a) (lfB i) h hv hw =
      eqToHom (congrArg (fun t ↦ Z.x (p + t)) ha) ≫ (G i).2 := rfl

lemma col_true {v : ZV L} (h : col v = true) : ∃ a, v = xv a := by
  cases v with
  | xv a => exact ⟨a, rfl⟩
  | _ => simp [col] at h

lemma R_xv {a : Fin (L + 2)} {w : ZV L} (h : R (xv a) w) :
    (∃ b : Fin (L + 1), w = zv b ∧ a.val = b.val) ∨ (∃ b : Fin (L + 1), w = zv b ∧ a.val = b.val + 1) ∨
      (∃ i, w = lfA i ∧ a.val = 0) ∨ ∃ i, w = lfB i ∧ a.val = L + 1 := by
  rcases R_cases h with ⟨j, h1, rfl⟩ | ⟨j, h1, rfl⟩ | ⟨i, h1, rfl⟩ | ⟨i, h1, rfl⟩ <;>
    simp only [xv.injEq] at h1 <;> subst h1
  · exact Or.inl ⟨j, rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨j, rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨i, rfl, rfl⟩))

end ZV

end RayCat

end LargeIndecomposable

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat.ZChain

variable {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] (Z : ZChain Q)

lemma eqToHom_self_comp {X Y : Q} (h : X = X) (f : X ⟶ Y) : eqToHom h ≫ f = f := by simp

lemma ρ_not_isIso (t : ℕ) : ¬IsIso (Z.ρ t) := fun h ↦ Z.peak₂ t ⟨Z.σ t ≫ inv (Z.ρ t), by simp⟩

lemma σ_not_isIso (t : ℕ) : ¬IsIso (Z.σ t) := fun h ↦ Z.peak₁ t ⟨Z.ρ t ≫ inv (Z.σ t), by simp⟩

end RayCat.ZChain

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

open ZV in
include B in
/-- **No zigzag with forks in `P/τ`** (BO13a figure 5.1). -/
theorem not_zigzag_forks
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) (Z : ZChain P) (p L : ℕ)
    (F : Fin 2 → BMor (Z.x p)) (G : Fin 2 → BMor (Z.x (p + L + 1)))
    (hρ : ∀ j ≤ L, ¬FactorsThroughMorphism τ (Z.ρ (p + j)))
    (hσ : ∀ j ≤ L, ¬FactorsThroughMorphism τ (Z.σ (p + j)))
    (hF : ∀ i, ¬FactorsThroughMorphism τ (F i).2) (hG : ∀ i, ¬FactorsThroughMorphism τ (G i).2)
    (hFi : ∀ i, ¬IsIso (F i).2) (hGi : ∀ i, ¬IsIso (G i).2)
    (hFF : ∀ i i', i ≠ i' → ¬∃ g, (F i).2 ≫ g = (F i').2)
    (hGG : ∀ i i', i ≠ i' → ¬∃ g, (G i).2 ≫ g = (G i').2)
    (hFρ : ∀ i, ¬∃ g, (F i).2 ≫ g = Z.ρ p) (hρF : ∀ i, ¬∃ g, Z.ρ p ≫ g = (F i).2)
    (hGσ : ∀ i, ¬∃ g, (G i).2 ≫ g = Z.σ (p + L))
    (hσG : ∀ i, ¬∃ g, Z.σ (p + L) ≫ g = (G i).2) : False := by
  have hD : ¬Statement.IsRepresentationFinite
      (Linearization (PathCat (BQ (ZV.graph L) ZV.col)) k) :=
    not_isRepresentationFinite_of_copy_affineD (2 * L + 2)
      ((BQ.graphIso ZV.col_ne).symm.toEmbedding.toCopy.comp ZV.dcopy)
  refine B.not_bq_diagram hmin hL hR τ hτ hτ0 (ZV.graph L) ZV.col hD (zobj Z p L F G)
    (zmor Z p L F G) ?_ ?_ ?_ ?_
  · intro v w h hv hw
    obtain ⟨⟨a, ha⟩, rfl⟩ := col_true hv
    rcases R_xv (R_of_adj h hv) with ⟨c, rfl, hc⟩ | ⟨c, rfl, hc⟩ | ⟨i, rfl, hc⟩ | ⟨i, rfl, hc⟩ <;>
      simp only at hc <;> subst hc
    · rw [zmor_ρ' _ _ rfl, ZChain.eqToHom_self_comp]; exact hρ c.val (by omega)
    · rw [zmor_σ' _ _ rfl, ZChain.eqToHom_self_comp]; exact hσ c.val (by omega)
    · rw [zmor_a' _ rfl, ZChain.eqToHom_self_comp]; exact hF i
    · rw [zmor_b' _ rfl, ZChain.eqToHom_self_comp]; exact hG i
  · intro v w h hv hw
    obtain ⟨⟨a, ha⟩, rfl⟩ := col_true hv
    rcases R_xv (R_of_adj h hv) with ⟨c, rfl, hc⟩ | ⟨c, rfl, hc⟩ | ⟨i, rfl, hc⟩ | ⟨i, rfl, hc⟩ <;>
      simp only at hc <;> subst hc
    · rw [zmor_ρ' _ _ rfl, ZChain.eqToHom_self_comp]; exact Z.ρ_not_isIso _
    · rw [zmor_σ' _ _ rfl, ZChain.eqToHom_self_comp]; exact Z.σ_not_isIso _
    · rw [zmor_a' _ rfl, ZChain.eqToHom_self_comp]; exact hFi i
    · rw [zmor_b' _ rfl, ZChain.eqToHom_self_comp]; exact hGi i
  · intro v w w' h h' hv hw hw' hne ⟨g, hg⟩
    obtain ⟨⟨a, ha⟩, rfl⟩ := col_true hv
    rcases R_xv (R_of_adj h hv) with ⟨⟨c, hc0⟩, rfl, hc⟩ | ⟨⟨c, hc0⟩, rfl, hc⟩ | ⟨i, rfl, hc⟩ |
        ⟨i, rfl, hc⟩ <;>
      rcases R_xv (R_of_adj h' hv) with ⟨⟨c', hc0'⟩, rfl, hc'⟩ | ⟨⟨c', hc0'⟩, rfl, hc'⟩ |
        ⟨i', rfl, hc'⟩ | ⟨i', rfl, hc'⟩ <;>
      simp only at hc hc' <;> subst hc
    -- (ρ, ρ)
    · exact hne (by subst hc'; rfl)
    -- (ρ, σ)
    · subst hc'
      rw [zmor_ρ' _ _ rfl, zmor_σ' _ _ rfl, ZChain.eqToHom_self_comp,
        ZChain.eqToHom_self_comp] at hg
      exact Z.valley₂ (p + c') ⟨g, hg⟩
    -- (ρ, lfA)
    · subst hc'
      rw [zmor_ρ' _ _ rfl, zmor_a' _ rfl, ZChain.eqToHom_self_comp,
        ZChain.eqToHom_self_comp] at hg
      exact hρF i' ⟨g, hg⟩
    -- (ρ, lfB)
    · omega
    -- (σ, ρ)
    · subst hc'
      rw [zmor_σ' _ _ rfl, zmor_ρ' _ _ rfl, ZChain.eqToHom_self_comp,
        ZChain.eqToHom_self_comp] at hg
      exact Z.valley₁ (p + c) ⟨g, hg⟩
    -- (σ, σ)
    · exact hne (by obtain rfl : c = c' := by omega
                    rfl)
    -- (σ, lfA)
    · omega
    -- (σ, lfB)
    · obtain rfl : c = L := by omega
      rw [zmor_σ' _ _ rfl, zmor_b' _ rfl, ZChain.eqToHom_self_comp,
        ZChain.eqToHom_self_comp] at hg
      exact hσG i' ⟨g, hg⟩
    -- (lfA, ρ)
    · subst hc'
      rw [zmor_a' _ rfl, zmor_ρ' _ _ rfl, ZChain.eqToHom_self_comp,
        ZChain.eqToHom_self_comp] at hg
      exact hFρ i ⟨g, hg⟩
    -- (lfA, σ)
    · omega
    -- (lfA, lfA)
    · rw [zmor_a' _ rfl, zmor_a' _ rfl, ZChain.eqToHom_self_comp,
        ZChain.eqToHom_self_comp] at hg
      exact hFF i i' (fun e ↦ hne (by rw [e])) ⟨g, hg⟩
    -- (lfA, lfB)
    · omega
    -- (lfB, ρ)
    · omega
    -- (lfB, σ)
    · obtain rfl : c' = L := by omega
      rw [zmor_b' _ rfl, zmor_σ' _ _ rfl, ZChain.eqToHom_self_comp,
        ZChain.eqToHom_self_comp] at hg
      exact hGσ i ⟨g, hg⟩
    -- (lfB, lfA)
    · omega
    -- (lfB, lfB)
    · rw [zmor_b' _ rfl, zmor_b' _ rfl, ZChain.eqToHom_self_comp,
        ZChain.eqToHom_self_comp] at hg
      exact hGG i i' (fun e ↦ hne (by rw [e])) ⟨g, hg⟩
  · intro v v' w h h' hv hv' hw hne ⟨g, hg⟩
    obtain ⟨⟨a, ha⟩, rfl⟩ := col_true hv
    obtain ⟨⟨a', ha'⟩, rfl⟩ := col_true hv'
    rcases R_xv (R_of_adj h hv) with ⟨⟨c, hc0⟩, rfl, hc⟩ | ⟨⟨c, hc0⟩, rfl, hc⟩ | ⟨i, rfl, hc⟩ |
        ⟨i, rfl, hc⟩ <;>
      rcases R_xv (R_of_adj h' hv') with ⟨⟨c', hc0'⟩, hw', hc'⟩ | ⟨⟨c', hc0'⟩, hw', hc'⟩ |
        ⟨i', hw', hc'⟩ | ⟨i', hw', hc'⟩ <;>
      simp only [zv.injEq, lfA.injEq, lfB.injEq, Fin.mk.injEq, reduceCtorEq] at hw' <;>
      simp only at hc hc' <;> subst hc hc'
    -- both into `zv c`
    · exact hne (by subst hw'; rfl)
    · subst hw'
      rw [zmor_ρ' _ _ rfl, zmor_σ' _ _ rfl, ZChain.eqToHom_self_comp,
        ZChain.eqToHom_self_comp] at hg
      exact Z.peak₂ _ ⟨g, hg⟩
    · subst hw'
      rw [zmor_σ' _ _ rfl, zmor_ρ' _ _ rfl, ZChain.eqToHom_self_comp,
        ZChain.eqToHom_self_comp] at hg
      exact Z.peak₁ _ ⟨g, hg⟩
    · exact hne (by subst hw'; rfl)
    -- leaves
    · exact hne rfl
    · exact hne rfl

end MulBasis

end RayQuiver

end LargeIndecomposable
