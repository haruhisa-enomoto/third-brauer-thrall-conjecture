module

public import LargeIndecomposable.Cleaving.PathCategories.OrientedTree

/-!
# Fixed tree shapes for cleaving diagrams

* `RayCat.isAcyclic_of_parent`: a graph whose edges are exactly the pairs
  `{a, par a}` for a parent function lowering a height is a forest.
* `RayCat.D5`: the `D̃₅` shape of BO13a Lemma 5 a) (case `i − 1 = 1`), and
  `RayQuiver.MulBasis.not_d5`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

/-- The in-forest of a parent function. -/
structure ParQ (V : Type) (par : V → Option V) where
  as : V

instance {V : Type} {par : V → Option V} : Quiver (ParQ V par) where
  Hom a b := PLift (par a.as = some b.as)

/-- **A graph given by a parent function is a forest.** -/
theorem isAcyclic_of_parent {V : Type} (G : SimpleGraph V) (par : V → Option V) (ht : V → ℕ)
    (hadj : ∀ a b, G.Adj a b ↔ par a = some b ∨ par b = some a)
    (hlt : ∀ a b, par a = some b → ht b < ht a) : G.IsAcyclic := by
  have hH : (LargeIndecomposable.Foundations.Quiver.underlyingGraph (ParQ V par)).IsAcyclic :=
    LargeIndecomposable.Foundations.Quiver.isAcyclic_underlyingGraph_of_lt (fun a ↦ ht a.as)
      (fun a b e ↦ hlt _ _ e.down) (fun a b b' e e' ↦ by
        have := e.down.symm.trans e'.down
        cases a; cases b; cases b'; simp_all)
  let e : LargeIndecomposable.Foundations.Quiver.underlyingGraph (ParQ V par) ≃g G :=
    { toEquiv := ⟨ParQ.as, ParQ.mk, fun _ ↦ rfl, fun _ ↦ rfl⟩
      map_rel_iff' := fun {a b} ↦ by
        change G.Adj a.as b.as ↔ _
        rw [LargeIndecomposable.Foundations.Quiver.underlyingGraph_adj, hadj]
        constructor
        · rintro (h | h)
          · refine ⟨fun hab ↦ ?_, Or.inl ⟨⟨h⟩⟩⟩
            subst hab
            exact lt_irrefl _ (hlt _ _ h)
          · refine ⟨fun hab ↦ ?_, Or.inr ⟨⟨h⟩⟩⟩
            subst hab
            exact lt_irrefl _ (hlt _ _ h)
        · rintro ⟨-, ⟨e⟩ | ⟨e⟩⟩
          · exact Or.inl e.some.down
          · exact Or.inr e.some.down }
  exact e.isAcyclic_iff.1 hH

/-! ### The `D̃₅` shape: `a ← x → b`, `x → m ← x'`, `m → y` -/

/-- Vertices of the `D̃₅` shape. -/
inductive D5V
  | a | b | x | m | y | x'
  deriving DecidableEq

namespace D5V

instance : Fintype D5V := ⟨{a, b, x, m, y, x'}, by intro v; cases v <;> simp⟩

/-- The orientation. -/
def ob : D5V → D5V → Bool
  | x, a | x, b | x, m | x', m | m, y => true
  | _, _ => false

/-- The orientation as a relation. -/
abbrev o (u v : D5V) : Prop := ob u v = true

/-- The graph. -/
def G : SimpleGraph D5V := SimpleGraph.fromRel o

lemma adj_iff (u v : D5V) : G.Adj u v ↔ o u v ∨ o v u := by
  rw [G, SimpleGraph.fromRel_adj]
  cases u <;> cases v <;> decide

instance : DecidableRel G.Adj := fun u v ↦ decidable_of_iff _ (adj_iff u v).symm

lemma ho (u v : D5V) (h : o u v) : G.Adj u v := (adj_iff u v).2 (Or.inl h)

lemma hcov (u v : D5V) (h : G.Adj u v) : o u v ∨ o v u := (adj_iff u v).1 h

lemma hasym (u v : D5V) (h : o u v) : ¬o v u := by
  revert h; cases u <;> cases v <;> decide

/-- The parent function towards `x`. -/
def par : D5V → Option D5V
  | a | b | m => some x
  | x' | y => some m
  | x => none

/-- The height. -/
def ht : D5V → ℕ
  | x => 0
  | a | b | m => 1
  | x' | y => 2

lemma isAcyclic : G.IsAcyclic :=
  isAcyclic_of_parent G par ht (fun u v ↦ by rw [adj_iff]; cases u <;> cases v <;> decide)
    (fun u v h ↦ by cases u <;> cases v <;> simp_all [par, ht])

open LargeIndecomposable.Foundations.Quiver in
/-- The vertex map of the copy of `D̃₅`. -/
def cmap : AffineD 1 → D5V
  | .spine j => if j = 0 then x else m
  | .leaf i => if i = 0 then a else if i = 1 then b else if i = 2 then y else x'

open LargeIndecomposable.Foundations.Quiver in
/-- The copy of `D̃₅`. -/
def copy : (underlyingGraph (AffineD 1)).Copy G where
  toHom := ⟨cmap, fun {u v} h ↦ by
    rcases (underlyingGraph_adj.1 h).2 with e | e
    · rcases u with i | j <;> rcases v with i' | j'
      · exact absurd e (AffineD.not_nonempty_hom_leaf _ _)
      · have := (AffineD.nonempty_leaf_spine_iff i j').1 e
        subst this
        fin_cases i
        · rw [AffineD.leafTarget_of_lt_two _ (by decide)]; simp [cmap]; decide
        · rw [AffineD.leafTarget_of_lt_two _ (by decide)]; simp [cmap]; decide
        · rw [AffineD.leafTarget_of_not_lt_two _ (by decide)]; simp [cmap]; decide
        · rw [AffineD.leafTarget_of_not_lt_two _ (by decide)]; simp [cmap]; decide
      · exact absurd e (AffineD.not_nonempty_hom_leaf _ _)
      · have := (AffineD.nonempty_spine_spine_iff j j').1 e
        fin_cases j <;> fin_cases j' <;> simp_all [cmap] <;> decide
    · rcases v with i | j <;> rcases u with i' | j'
      · exact absurd e (AffineD.not_nonempty_hom_leaf _ _)
      · have := (AffineD.nonempty_leaf_spine_iff i j').1 e
        subst this
        fin_cases i
        · rw [AffineD.leafTarget_of_lt_two _ (by decide)]; simp [cmap]; decide
        · rw [AffineD.leafTarget_of_lt_two _ (by decide)]; simp [cmap]; decide
        · rw [AffineD.leafTarget_of_not_lt_two _ (by decide)]; simp [cmap]; decide
        · rw [AffineD.leafTarget_of_not_lt_two _ (by decide)]; simp [cmap]; decide
      · exact absurd e (AffineD.not_nonempty_hom_leaf _ _)
      · have := (AffineD.nonempty_spine_spine_iff j j').1 e
        fin_cases j <;> fin_cases j' <;> simp_all [cmap] <;> decide⟩
  injective' := by
    intro u v huv
    change cmap u = cmap v at huv
    rcases u with i | j <;> rcases v with i' | j'
    · fin_cases i <;> fin_cases i' <;> simp_all [cmap]
    · fin_cases i <;> fin_cases j' <;> simp_all [cmap]
    · fin_cases j <;> fin_cases i' <;> simp_all [cmap]
    · fin_cases j <;> fin_cases j' <;> simp_all [cmap]

section Diagram

variable {P : Type} [Category.{0} P] {X M Y X' A B : P} (α : X ⟶ A) (β : X ⟶ B) (r : X ⟶ M)
  (v : X' ⟶ M) (s : M ⟶ Y)

/-- The objects. -/
def obj5 : D5V → P
  | a => A | b => B | x => X | m => M | y => Y | x' => X'

/-- The morphisms. -/
def mor5 : ∀ u w : D5V, o u w → ((obj5 (X := X) (M := M) (Y := Y) (X' := X') (A := A) (B := B) u) ⟶
    obj5 (X := X) (M := M) (Y := Y) (X' := X') (A := A) (B := B) w)
  | x, a, _ => α
  | x, b, _ => β
  | x, m, _ => r
  | x', m, _ => v
  | m, y, _ => s
  | a, _, h | b, _, h | y, _, h => absurd h (by cases ‹D5V› <;> decide)
  | x, x, h | x, y, h | x, x', h => absurd h (by decide)
  | m, a, h | m, b, h | m, x, h | m, m, h | m, x', h => absurd h (by decide)
  | x', a, h | x', b, h | x', x, h | x', y, h | x', x', h => absurd h (by decide)

/-- The diagram as a prefunctor. -/
def phi5 : OT G o ⥤q P where
  obj u := obj5 (X := X) (M := M) (Y := Y) (X' := X') (A := A) (B := B) u.as
  map {u w} e := mor5 α β r v s u.as w.as (OT.hom_down e)

end Diagram

end D5V

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

open D5V in
include B in
/-- **No cleaving `D̃₅` diagram** `A ← X → B`, `X → M ← X'`, `M → Y` in `P/τ`
(BO13a Lemma 5 a), case `i − 1 = 1`). -/
theorem not_d5
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) {X M Y X' A₁ B₁ : P} (α : X ⟶ A₁) (β : X ⟶ B₁) (r : X ⟶ M) (v : X' ⟶ M)
    (s : M ⟶ Y)
    (h0α : ¬FactorsThroughMorphism τ α) (h0β : ¬FactorsThroughMorphism τ β)
    (h0r : ¬FactorsThroughMorphism τ r) (h0v : ¬FactorsThroughMorphism τ v)
    (h0s : ¬FactorsThroughMorphism τ s) (h0rs : ¬FactorsThroughMorphism τ (r ≫ s))
    (h0vs : ¬FactorsThroughMorphism τ (v ≫ s))
    (hiα : ¬IsIso α) (hiβ : ¬IsIso β) (hir : ¬IsIso r) (hiv : ¬IsIso v) (his : ¬IsIso s)
    (hαβ : ¬∃ g, α ≫ g = β) (hβα : ¬∃ g, β ≫ g = α) (hαr : ¬∃ g, α ≫ g = r)
    (hαrs : ¬∃ g, α ≫ g = r ≫ s) (hβr : ¬∃ g, β ≫ g = r) (hβrs : ¬∃ g, β ≫ g = r ≫ s)
    (hrα : ¬∃ g, r ≫ g = α) (hrβ : ¬∃ g, r ≫ g = β)
    (hrv : ¬∃ g, g ≫ r = v) (hvr : ¬∃ g, g ≫ v = r) : False := by
  haveI : Fact (LargeIndecomposable.Foundations.Quiver.IsAcyclic (OT G o)) := ⟨OT.isAcyclic ho hasym isAcyclic⟩
  refine B.not_ot_diagram hmin hL hR τ hτ hτ0 G o ho hasym isAcyclic
    (OT.not_isRepresentationFinite_affineD ho hcov k 1 copy) (phi5 α β r v s) ?_ ?_ ?_ ?_
  · intro u w p hp
    rcases u with ⟨u⟩
    rcases w with ⟨w⟩
    cases p with
    | nil => simp at hp
    | cons p e =>
      rename_i w1
      rcases w1 with ⟨w1⟩
      have h := OT.hom_down e
      cases p with
      | nil =>
        change ¬FactorsThroughMorphism τ (𝟙 _ ≫ mor5 α β r v s u w h)
        rw [Category.id_comp]
        cases u <;> cases w <;> first
          | exact absurd h (by decide)
          | exact h0α | exact h0β | exact h0r | exact h0v | exact h0s
      | cons p e' =>
        rename_i w2
        rcases w2 with ⟨w2⟩
        have h' := OT.hom_down e'
        cases p with
        | nil =>
          change ¬FactorsThroughMorphism τ ((𝟙 _ ≫ mor5 α β r v s u w1 h') ≫ mor5 α β r v s w1 w h)
          rw [Category.id_comp]
          cases u <;> cases w1 <;> cases w <;> first
            | exact absurd h (by decide)
            | exact absurd h' (by decide)
            | exact h0rs | exact h0vs
        | cons p e'' =>
          rename_i w3
          rcases w3 with ⟨w3⟩
          have h'' := OT.hom_down e''
          exfalso
          cases w3 <;> cases w2 <;> cases w1 <;> cases w <;> first
            | exact absurd h (by decide)
            | exact absurd h' (by decide)
            | exact absurd h'' (by decide)
  · intro u w e
    rcases u with ⟨u⟩
    rcases w with ⟨w⟩
    have h := OT.hom_down e
    change ¬IsIso (mor5 α β r v s u w h)
    cases u <;> cases w <;> first
      | exact absurd h (by decide)
      | exact hiα | exact hiβ | exact hir | exact hiv | exact his
  · intro u c c' w e e' q hne ⟨g, hg⟩
    rcases u with ⟨u⟩
    rcases c with ⟨c⟩
    rcases c' with ⟨c'⟩
    rcases w with ⟨w⟩
    have he := OT.hom_down e
    have he' := OT.hom_down e'
    cases q with
    | nil =>
      change mor5 α β r v s u c he ≫ g = 𝟙 _ ≫ mor5 α β r v s u c' he' at hg
      rw [Category.id_comp] at hg
      cases u <;> cases c <;> cases c' <;> first
        | exact absurd he (by decide)
        | exact absurd he' (by decide)
        | exact hne rfl
        | exact hαβ ⟨g, hg⟩ | exact hβα ⟨g, hg⟩ | exact hαr ⟨g, hg⟩ | exact hβr ⟨g, hg⟩
        | exact hrα ⟨g, hg⟩ | exact hrβ ⟨g, hg⟩
    | cons q e2 =>
      rename_i w1
      rcases w1 with ⟨w1⟩
      have h2 := OT.hom_down e2
      cases q with
      | nil =>
        change mor5 α β r v s u c he ≫ g =
          (𝟙 _ ≫ mor5 α β r v s u c' he') ≫ mor5 α β r v s c' w h2 at hg
        rw [Category.id_comp] at hg
        cases u <;> cases c <;> cases c' <;> cases w <;> first
          | exact absurd he (by decide)
          | exact absurd he' (by decide)
          | exact absurd h2 (by decide)
          | exact hne rfl
          | exact hαrs ⟨g, hg⟩ | exact hβrs ⟨g, hg⟩
      | cons q e3 =>
        rename_i w2
        rcases w2 with ⟨w2⟩
        have h3 := OT.hom_down e3
        exfalso
        cases q with
        | nil =>
          cases u <;> cases c' <;> cases w1 <;> cases w <;> first
            | exact absurd he' (by decide)
            | exact absurd h3 (by decide)
            | exact absurd h2 (by decide)
        | cons q e4 =>
          rename_i w3
          rcases w3 with ⟨w3⟩
          have h4 := OT.hom_down e4
          cases w3 <;> cases w2 <;> cases w1 <;> cases w <;> first
            | exact absurd h4 (by decide)
            | exact absurd h3 (by decide)
            | exact absurd h2 (by decide)
  · intro u c c' w e e' q hne ⟨g, hg⟩
    rcases u with ⟨u⟩
    rcases c with ⟨c⟩
    rcases c' with ⟨c'⟩
    rcases w with ⟨w⟩
    have he := OT.hom_down e
    have he' := OT.hom_down e'
    cases q with
    | nil =>
      change g ≫ mor5 α β r v s c w he = 𝟙 _ ≫ mor5 α β r v s u w he' at hg
      rw [Category.id_comp] at hg
      cases c <;> cases u <;> cases w <;> first
        | exact absurd he (by decide)
        | exact absurd he' (by decide)
        | exact hne rfl
        | exact hrv ⟨g, hg⟩ | exact hvr ⟨g, hg⟩
    | cons q e2 =>
      rename_i w1
      rcases w1 with ⟨w1⟩
      have h2 := OT.hom_down e2
      exfalso
      cases c <;> cases w1 <;> cases c' <;> cases w <;> first
        | exact absurd h2 (by decide)
        | exact absurd he' (by decide)
        | exact absurd he (by decide)
        | exact hne rfl

end MulBasis

end RayQuiver

end LargeIndecomposable
