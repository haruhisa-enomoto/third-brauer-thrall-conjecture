module

public import LargeIndecomposable.Cleaving.Basic.BipDiagram

/-!
# Bipartite quivers from a graph and a colouring

For a simple graph `G` and a colouring `c` (`true` = source), `BQ G c` has an
arrow `a → b` for each edge with `c a = true`, `c b = false`. For a proper
colouring its underlying graph is `G`; it has no path of length two and is
acyclic. Every proper colouring of `D̃ₘ₊₄` gives a representation-infinite
path category, and a diagram of morphisms indexed by it which avoids `τ` and
satisfies the zigzag conditions contradicts minimality
(`RayQuiver.MulBasis.not_bq_diagram`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

/-- The bipartite quiver of a graph with a colouring. -/
structure BQ {V : Type} (G : SimpleGraph V) (c : V → Bool) where
  /-- The underlying vertex. -/
  as : V

namespace BQ

variable {V : Type} {G : SimpleGraph V} {c : V → Bool}

instance quiver : Quiver.{0} (BQ G c) where
  Hom a b := PLift (G.Adj a.as b.as ∧ c a.as = true ∧ c b.as = false)

instance (a b : BQ G c) : Subsingleton (a ⟶ b) :=
  inferInstanceAs (Subsingleton (PLift (G.Adj a.as b.as ∧ c a.as = true ∧ c b.as = false)))

lemma hom_down {a b : BQ G c} (e : a ⟶ b) : G.Adj a.as b.as ∧ c a.as = true ∧ c b.as = false :=
  PLift.down e

/-- The vertex equivalence. -/
def equiv : BQ G c ≃ V := ⟨BQ.as, BQ.mk, fun _ ↦ rfl, fun _ ↦ rfl⟩

instance [Fintype V] : Fintype (BQ G c) := Fintype.ofEquiv V equiv.symm

instance [DecidableEq V] : DecidableEq (BQ G c) := equiv.decidableEq

lemma noTwoPaths : PathCat.NoTwoPaths (BQ G c) := fun e e' ↦ by
  have h1 := (hom_down e).2.2
  have h2 := (hom_down e').2.1
  rw [h1] at h2
  cases h2

lemma isAcyclic : LargeIndecomposable.Foundations.Quiver.IsAcyclic (BQ G c) := by
  rw [LargeIndecomposable.Foundations.Quiver.isAcyclic_def]
  intro a p
  cases p with
  | nil => rfl
  | cons q e =>
    cases q with
    | nil => exact absurd (hom_down e).1 G.irrefl
    | cons q' e' => exact (noTwoPaths e' e).elim

instance : Fact (LargeIndecomposable.Foundations.Quiver.IsAcyclic (BQ G c)) := ⟨isAcyclic⟩

/-- For a proper colouring the underlying graph is `G`. -/
def graphIso (hc : ∀ a b, G.Adj a b → c a ≠ c b) :
    LargeIndecomposable.Foundations.Quiver.underlyingGraph (BQ G c) ≃g G where
  toEquiv := equiv
  map_rel_iff' {a b} := by
    change G.Adj a.as b.as ↔ _
    rw [LargeIndecomposable.Foundations.Quiver.underlyingGraph_adj]
    constructor
    · intro h
      refine ⟨fun e ↦ G.irrefl (e ▸ h), ?_⟩
      have := hc _ _ h
      cases ha : c a.as <;> cases hb : c b.as <;> rw [ha, hb] at this
      · exact absurd rfl this
      · exact Or.inr ⟨⟨h.symm, hb, ha⟩⟩
      · exact Or.inl ⟨⟨h, ha, hb⟩⟩
      · exact absurd rfl this
    · rintro ⟨-, ⟨⟨⟨e, -⟩⟩⟩ | ⟨⟨⟨e, -⟩⟩⟩⟩
      · exact e
      · exact e.symm

end BQ

open LargeIndecomposable.Foundations.Quiver in
/-- Every proper colouring of `D̃ₘ₊₄` has a representation-infinite path
category. -/
theorem BQ.not_isRepresentationFinite_affineD (k : Type*) [Field k] (m : ℕ)
    (c : AffineD m → Bool)
    (hc : ∀ a b, (underlyingGraph (AffineD m)).Adj a b → c a ≠ c b) :
    ¬Statement.IsRepresentationFinite
      (RayQuiver.Linearization (PathCat (BQ (underlyingGraph (AffineD m)) c)) k) :=
  not_isRepresentationFinite_of_copy_affineD m (BQ.graphIso hc).symm.toEmbedding.toCopy

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **No bipartite tree diagram in `P/τ`**, in graph-and-colouring form. -/
theorem not_bq_diagram
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (c : V → Bool)
    (hD : ¬Statement.IsRepresentationFinite (Linearization (PathCat (BQ G c)) k))
    (obj : V → P) (mor : ∀ v w, G.Adj v w → c v = true → c w = false → (obj v ⟶ obj w))
    (h0 : ∀ v w h hv hw, ¬FactorsThroughMorphism τ (mor v w h hv hw))
    (hiso : ∀ v w h hv hw, ¬IsIso (mor v w h hv hw))
    (hl : ∀ v w w' h h' hv hw hw', w ≠ w' → ¬∃ g, mor v w h hv hw ≫ g = mor v w' h' hv hw')
    (hr : ∀ v v' w h h' hv hv' hw, v ≠ v' → ¬∃ g, g ≫ mor v w h hv hw = mor v' w h' hv' hw) :
    False := by
  let φ : BQ G c ⥤q P :=
    { obj := fun v ↦ obj v.as
      map := fun {v w} e ↦ mor v.as w.as (BQ.hom_down e).1 (BQ.hom_down e).2.1 (BQ.hom_down e).2.2 }
  refine B.not_bip_diagram hmin hL hR τ hτ hτ0 hD BQ.noTwoPaths φ (fun e ↦ h0 _ _ _ _ _)
    (fun e ↦ hiso _ _ _ _ _) (fun e e' hne ↦ hl _ _ _ _ _ _ _ _ fun h ↦ hne ?_)
    (fun e e' hne ↦ hr _ _ _ _ _ _ _ _ fun h ↦ hne ?_)
  · exact congrArg BQ.mk h
  · exact congrArg BQ.mk h

end MulBasis

end RayQuiver

end LargeIndecomposable
