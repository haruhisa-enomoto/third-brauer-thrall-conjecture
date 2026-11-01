module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.GabrielPieces

/-!
# Interval-finiteness of the cover for an acyclic quiver

If the quiver of the ray category `P` has no oriented cycle, the number of objects reachable
from `x` by arrows strictly decreases along arrows. Hence an object of the universal cover
reaches only finitely many objects, and every finite set of objects of the cover lies in a
finite convex piece (`hullFinite_of_acyclic`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P}

/-- An arrow of the quiver of `P`. -/
def Arr (x y : P) : Prop := ∃ f : x ⟶ y, IsIrreducible f

/-- The quiver of `P` has no oriented cycle. -/
def Acyclic (P : Type) [Category.{0} P] [HasZeroMorphisms P] : Prop :=
  ∀ x : P, ¬Relation.TransGen Arr x x

/-- The number of objects reachable from `x` by a nonempty path of arrows. -/
def reachHt (x : P) : ℕ := {z : P | Relation.TransGen Arr x z}.ncard

lemma reachHt_lt (hac : Acyclic P) {x y : P} (h : Arr x y) : reachHt y < reachHt x := by
  apply Set.ncard_lt_ncard _ (Set.toFinite _)
  refine ⟨fun z hz ↦ Relation.TransGen.head h hz, fun hsub ↦ hac y (hsub ?_)⟩
  exact Relation.TransGen.single h

lemma Cover.Reach.trans {a b c : Cover x₀} (h1 : Reach a b) (h2 : Reach b c) : Reach a c := by
  induction h1 with
  | refl => exact h2
  | step f hf _ ih => exact Reach.step f hf (ih h2)

lemma finite_reach_of_acyclic (hac : Acyclic P) :
    ∀ n : ℕ, ∀ a : Cover x₀, reachHt a.y ≤ n → {c | Reach a c}.Finite := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a ha
  have hsucc : {b : Cover x₀ | ∃ f : a ⟶ b, IsIrreducible f}.Finite :=
    (IsRayCategory.finite_out a).subset fun b ⟨f, hf⟩ ↦ ⟨f, hf.1⟩
  have hsub : {c | Reach a c} ⊆
      {a} ∪ ⋃ b ∈ {b : Cover x₀ | ∃ f : a ⟶ b, IsIrreducible f}, {c | Reach b c} := by
    intro c hc
    cases hc with
    | refl => exact Or.inl rfl
    | step f hf hbc => exact Or.inr (Set.mem_biUnion ⟨f, hf⟩ hbc)
  refine ((Set.finite_singleton a).union (hsucc.biUnion fun b ⟨f, hf⟩ ↦ ?_)).subset hsub
  have hlt := reachHt_lt hac ⟨val f, isIrreducible_val hf⟩
  exact ih (reachHt b.y) (by omega) b le_rfl

/-- **For an acyclic quiver the universal cover is interval-finite.** -/
theorem hullFinite_of_acyclic (hac : Acyclic P) : HullFinite x₀ := by
  intro T
  let H : Set (Cover x₀) := {b | ∃ a ∈ T, ∃ c ∈ T, Reach a b ∧ Reach b c}
  have hH : H.Finite := by
    refine (T.finite_toSet.biUnion fun a _ ↦
      finite_reach_of_acyclic hac _ a le_rfl).subset fun b ⟨a, ha, _, _, hab, _⟩ ↦ ?_
    exact Set.mem_biUnion ha hab
  refine ⟨hH.toFinset, fun t ht ↦ ?_, fun a b c ha hc hab hbc ↦ ?_⟩
  · exact hH.mem_toFinset.2 ⟨t, ht, t, ht, Reach.refl t, Reach.refl t⟩
  · obtain ⟨a', ha', -, -, ha'a, -⟩ := hH.mem_toFinset.1 ha
    obtain ⟨-, -, c', hc', -, hcc'⟩ := hH.mem_toFinset.1 hc
    exact hH.mem_toFinset.2 ⟨a', ha', c', hc', ha'a.trans hab, hbc.trans hcc'⟩

end LargeIndecomposable.RayCat
