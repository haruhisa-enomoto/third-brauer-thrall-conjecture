module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.RingQuot
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Finite quivers, path algebras and representations

A finite quiver `Q`, its path algebra `kQ` and the representations of `Q`
(of arbitrary dimension), with the manuscript's conventions: modules are left
modules, so representations are covariant, and for arrows `α : i → j` and
`β : j → l` the product `βα` traverses `α` first.

`FinQuiver` and the presentation of `kQ` as a `RingQuot` of a free algebra are
adapted from `BrickAccessibility/Statement.lean` in
`brick-accessibility-special-biserial` (commit
`efae161c558e7545419580026e7e6f3447d1bc4a`), which uses traversal-order
products for right modules; here the source and target relations are swapped.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory

universe u

/-- A finite quiver: finite sets of vertices and arrows with source and target
maps. -/
structure FinQuiver where
  /-- Vertices. -/
  V : Type
  /-- Arrows. -/
  A : Type
  [finV : Fintype V]
  [decV : DecidableEq V]
  [finA : Fintype A]
  [decA : DecidableEq A]
  /-- The source of an arrow. -/
  src : A → V
  /-- The target of an arrow. -/
  tgt : A → V

attribute [instance] FinQuiver.finV FinQuiver.decV FinQuiver.finA FinQuiver.decA

namespace FinQuiver

variable (k : Type u) [Field k] (Q : FinQuiver)

/-- Generators of the path algebra: one per vertex and one per arrow. -/
abbrev Gen := Q.V ⊕ Q.A

/-- The defining relations of the path algebra (left-module convention): the
vertex idempotents are orthogonal and sum to one, and an arrow `c` satisfies
`c e_{s(c)} = c = e_{t(c)} c`. -/
inductive PathRel : FreeAlgebra k Q.Gen → FreeAlgebra k Q.Gen → Prop
  | idem (v w : Q.V) :
      PathRel (FreeAlgebra.ι k (Sum.inl v) * FreeAlgebra.ι k (Sum.inl w))
        (if v = w then FreeAlgebra.ι k (Sum.inl v) else 0)
  | one : PathRel (∑ v, FreeAlgebra.ι k (Sum.inl v)) 1
  | src (a : Q.A) :
      PathRel (FreeAlgebra.ι k (Sum.inr a) * FreeAlgebra.ι k (Sum.inl (Q.src a)))
        (FreeAlgebra.ι k (Sum.inr a))
  | tgt (a : Q.A) :
      PathRel (FreeAlgebra.ι k (Sum.inl (Q.tgt a)) * FreeAlgebra.ι k (Sum.inr a))
        (FreeAlgebra.ι k (Sum.inr a))

/-- The path algebra `kQ`, presented by its vertex idempotents and arrows. -/
abbrev PathAlgebra := RingQuot (PathRel k Q)

/-- The vertex idempotent `e_v` in `kQ`. -/
def vertex (v : Q.V) : PathAlgebra k Q :=
  RingQuot.mkAlgHom k (PathRel k Q) (FreeAlgebra.ι k (Sum.inl v))

/-- The arrow `a` in `kQ`. -/
def arrow (a : Q.A) : PathAlgebra k Q :=
  RingQuot.mkAlgHom k (PathRel k Q) (FreeAlgebra.ι k (Sum.inr a))

/-- The element of `kQ` of a word of arrows `[c₁, …, cₙ]` in traversal order:
`cₙ ⋯ c₁`. A word that is not composable gives zero. -/
def word : List Q.A → PathAlgebra k Q
  | [] => 1
  | c :: l => word l * arrow k Q c

/-- Two algebra homomorphisms out of `kQ` agree if they agree on vertices and
arrows. -/
lemma algHom_ext {B : Type u} [Ring B] [Algebra k B] {f g : PathAlgebra k Q →ₐ[k] B}
    (hv : ∀ v, f (vertex k Q v) = g (vertex k Q v))
    (ha : ∀ a, f (arrow k Q a) = g (arrow k Q a)) : f = g := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext x
  rcases x with v | a
  · exact hv v
  · exact ha a

/-- A morphism of quivers `D → Q`. -/
structure Hom (D Q : FinQuiver) where
  /-- The map on vertices. -/
  vert : D.V → Q.V
  /-- The map on arrows (the label of an arrow). -/
  arr : D.A → Q.A
  map_src : ∀ e, Q.src (arr e) = vert (D.src e)
  map_tgt : ∀ e, Q.tgt (arr e) = vert (D.tgt e)

/-- Property (3.4): `p` is injective on the arrows with a fixed source, and on
those with a fixed target. -/
def Hom.LocallyInjective {D Q : FinQuiver} (p : Hom D Q) : Prop :=
  (∀ e e', D.src e = D.src e' → p.arr e = p.arr e' → e = e') ∧
    (∀ e e', D.tgt e = D.tgt e' → p.arr e = p.arr e' → e = e')

/-- The identity morphism of a quiver. -/
def Hom.id (Q : FinQuiver) : Hom Q Q := ⟨_root_.id, _root_.id, fun _ ↦ rfl, fun _ ↦ rfl⟩

end FinQuiver

/-! ### Representations -/

variable (k : Type u) [Field k]

/-- A representation of a finite quiver `D`: a `k`-vector space of arbitrary
dimension at each vertex and a linear map along each arrow. -/
structure Rep (D : FinQuiver) where
  /-- The space at a vertex. -/
  obj : D.V → ModuleCat.{u} k
  /-- The map along an arrow. -/
  map : ∀ e : D.A, obj (D.src e) ⟶ obj (D.tgt e)

namespace Rep

variable {k} {D : FinQuiver}

/-- A morphism of representations: maps at the vertices commuting with the
arrow maps. -/
@[ext]
structure Hom (X Y : Rep k D) where
  /-- The map at a vertex. -/
  app : ∀ i, X.obj i ⟶ Y.obj i
  comm : ∀ e, X.map e ≫ app (D.tgt e) = app (D.src e) ≫ Y.map e

attribute [reassoc] Hom.comm

instance : Category (Rep k D) where
  Hom := Hom
  id X := ⟨fun _ ↦ 𝟙 _, fun _ ↦ by simp⟩
  comp f g := ⟨fun i ↦ f.app i ≫ g.app i, fun e ↦ by
    rw [f.comm_assoc, g.comm, Category.assoc]⟩

@[ext]
lemma hom_ext {X Y : Rep k D} {f g : X ⟶ Y} (h : ∀ i, f.app i = g.app i) : f = g :=
  Hom.ext (funext h)

@[simp]
lemma id_app (X : Rep k D) (i : D.V) : Hom.app (𝟙 X) i = 𝟙 _ := rfl

@[simp]
lemma comp_app {X Y Z : Rep k D} (f : X ⟶ Y) (g : Y ⟶ Z) (i : D.V) :
    Hom.app (f ≫ g) i = f.app i ≫ g.app i := rfl

instance (X Y : Rep k D) : Zero (X ⟶ Y) := ⟨⟨fun _ ↦ 0, fun _ ↦ by simp⟩⟩
instance (X Y : Rep k D) : Add (X ⟶ Y) :=
  ⟨fun f g ↦ ⟨fun i ↦ f.app i + g.app i, fun e ↦ by
    simp [Preadditive.comp_add, Preadditive.add_comp, f.comm, g.comm]⟩⟩
instance (X Y : Rep k D) : Neg (X ⟶ Y) :=
  ⟨fun f ↦ ⟨fun i ↦ -f.app i, fun e ↦ by simp [f.comm]⟩⟩
instance (X Y : Rep k D) : Sub (X ⟶ Y) :=
  ⟨fun f g ↦ ⟨fun i ↦ f.app i - g.app i, fun e ↦ by
    simp [Preadditive.comp_sub, Preadditive.sub_comp, f.comm, g.comm]⟩⟩
instance (X Y : Rep k D) : SMul ℕ (X ⟶ Y) :=
  ⟨fun n f ↦ ⟨fun i ↦ n • f.app i, fun e ↦ by simp [f.comm]⟩⟩
instance (X Y : Rep k D) : SMul ℤ (X ⟶ Y) :=
  ⟨fun n f ↦ ⟨fun i ↦ n • f.app i, fun e ↦ by simp [f.comm]⟩⟩

@[simp] lemma zero_app (X Y : Rep k D) (i : D.V) : Hom.app (0 : X ⟶ Y) i = 0 := rfl
@[simp] lemma add_app {X Y : Rep k D} (f g : X ⟶ Y) (i : D.V) :
    Hom.app (f + g) i = f.app i + g.app i := rfl
@[simp] lemma neg_app {X Y : Rep k D} (f : X ⟶ Y) (i : D.V) :
    Hom.app (-f) i = -f.app i := rfl
@[simp] lemma sub_app {X Y : Rep k D} (f g : X ⟶ Y) (i : D.V) :
    Hom.app (f - g) i = f.app i - g.app i := rfl

instance (X Y : Rep k D) : AddCommGroup (X ⟶ Y) :=
  Function.Injective.addCommGroup (fun f : X ⟶ Y ↦ f.app) (fun _ _ h ↦ Hom.ext h)
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance : Preadditive (Rep k D) where
  add_comp _ _ _ _ _ _ := by ext i; simp [Preadditive.add_comp]
  comp_add _ _ _ _ _ _ := by ext i; simp [Preadditive.comp_add]

end Rep

end LargeIndecomposable
