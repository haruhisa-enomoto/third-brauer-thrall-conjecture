module

public import LargeIndecomposable.Cleaving.Basic.PathCatRep

/-!
# Reorienting a quiver

`Reo V fl` has the vertices of `V` and reverses the arrows `a ⟶ b` with
`fl a b`. It has the same underlying graph, so Gabriel's theorem for
Euclidean trees applies to every orientation
(`RayCat.Reo.not_isRepresentationFinite_affineD`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory RayQuiver

namespace RayCat

/-- The quiver `V` with the arrows in `fl` reversed. -/
structure Reo (V : Type) (fl : V → V → Prop) where
  /-- The underlying vertex. -/
  as : V

namespace Reo

variable {V : Type} [Quiver.{0} V] {fl : V → V → Prop}

instance quiver : Quiver.{0} (Reo V fl) where
  Hom a b := PLift ((Nonempty (a.as ⟶ b.as) ∧ ¬fl a.as b.as) ∨
    (Nonempty (b.as ⟶ a.as) ∧ fl b.as a.as))

instance (a b : Reo V fl) : Subsingleton (a ⟶ b) :=
  ⟨fun x y ↦ by cases x; cases y; rfl⟩

instance (a b : Reo V fl) : Finite (a ⟶ b) := Finite.of_subsingleton

/-- The vertex equivalence. -/
def equiv : Reo V fl ≃ V := ⟨Reo.as, Reo.mk, fun _ ↦ rfl, fun _ ↦ rfl⟩

instance [Fintype V] : Fintype (Reo V fl) := Fintype.ofEquiv V equiv.symm

instance [DecidableEq V] : DecidableEq (Reo V fl) := equiv.decidableEq

lemma adj_iff {a b : Reo V fl} :
    (LargeIndecomposable.Foundations.Quiver.underlyingGraph (Reo V fl)).Adj a b ↔
      (LargeIndecomposable.Foundations.Quiver.underlyingGraph V).Adj a.as b.as := by
  rw [LargeIndecomposable.Foundations.Quiver.underlyingGraph_adj, LargeIndecomposable.Foundations.Quiver.underlyingGraph_adj]
  constructor
  · rintro ⟨hne, ⟨⟨h | h⟩⟩ | ⟨⟨h | h⟩⟩⟩
    · exact ⟨fun e ↦ hne (congrArg Reo.mk e), Or.inl h.1⟩
    · exact ⟨fun e ↦ hne (congrArg Reo.mk e), Or.inr h.1⟩
    · exact ⟨fun e ↦ hne (congrArg Reo.mk e), Or.inr h.1⟩
    · exact ⟨fun e ↦ hne (congrArg Reo.mk e), Or.inl h.1⟩
  · rintro ⟨hne, h | h⟩
    · refine ⟨fun e ↦ hne (congrArg Reo.as e), ?_⟩
      by_cases hf : fl a.as b.as
      · exact Or.inr ⟨⟨Or.inr ⟨h, hf⟩⟩⟩
      · exact Or.inl ⟨⟨Or.inl ⟨h, hf⟩⟩⟩
    · refine ⟨fun e ↦ hne (congrArg Reo.as e), ?_⟩
      by_cases hf : fl b.as a.as
      · exact Or.inl ⟨⟨Or.inr ⟨h, hf⟩⟩⟩
      · exact Or.inr ⟨⟨Or.inl ⟨h, hf⟩⟩⟩

/-- The underlying graphs agree. -/
def graphIso : LargeIndecomposable.Foundations.Quiver.underlyingGraph (Reo V fl) ≃g LargeIndecomposable.Foundations.Quiver.underlyingGraph V where
  toEquiv := equiv
  map_rel_iff' := adj_iff.symm

lemma isAcyclic (hV : ∀ (a b : V), Nonempty (a ⟶ b) → IsEmpty (b ⟶ a))
    (hG : (LargeIndecomposable.Foundations.Quiver.underlyingGraph V).IsAcyclic) : LargeIndecomposable.Foundations.Quiver.IsAcyclic (Reo V fl) := by
  refine LargeIndecomposable.Foundations.Quiver.isAcyclic_of_isAcyclic_underlyingGraph (fun a b e ↦ ⟨fun e' ↦ ?_⟩)
    ((graphIso).isAcyclic_iff.2 hG)
  rcases e with ⟨⟨h, hf⟩ | ⟨h, hf⟩⟩ <;> rcases e' with ⟨⟨h', hf'⟩ | ⟨h', hf'⟩⟩
  · exact (hV _ _ h).false h'.some
  · exact hf hf'
  · exact hf' hf
  · exact (hV _ _ h).false h'.some

section Affine

variable (k : Type*) [Field k]

open LargeIndecomposable.Foundations.Quiver

lemma affineD_rev (m : ℕ) : ∀ (a b : AffineD m), Nonempty (a ⟶ b) → IsEmpty (b ⟶ a) := by
  rintro (i | j) (i' | j') ⟨e⟩
  · exact (IsEmpty.false e).elim
  · exact ⟨fun e' ↦ IsEmpty.false e'⟩
  · exact (IsEmpty.false e).elim
  · refine ⟨fun e' ↦ ?_⟩
    have h1 : (j' : ℕ) = j + 1 := e.down
    have h2 : (j : ℕ) = j' + 1 := e'.down
    omega

instance (m : ℕ) (fl : AffineD m → AffineD m → Prop) : Fact (IsAcyclic (Reo (AffineD m) fl)) :=
  ⟨Reo.isAcyclic (affineD_rev m) AffineD.isAcyclic_underlyingGraph⟩

/-- Every orientation of `D̃ₘ₊₄` has a representation-infinite path category. -/
theorem not_isRepresentationFinite_affineD (m : ℕ) (fl : AffineD m → AffineD m → Prop) :
    ¬Statement.IsRepresentationFinite (Linearization (PathCat (Reo (AffineD m) fl)) k) :=
  not_isRepresentationFinite_of_copy_affineD m (Reo.graphIso.symm.toEmbedding.toCopy)

end Affine

end Reo

end RayCat

end LargeIndecomposable
