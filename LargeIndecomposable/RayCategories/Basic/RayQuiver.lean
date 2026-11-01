module

public import LargeIndecomposable.RayCategories.Basic.Factor
public import LargeIndecomposable.RepresentationEmbeddings.WalkConstruction.Monomial

/-!
# The quiver of a finite ray category

For a ray category `P` with finitely many objects, the quiver `Q_P` has the
objects as vertices and the irreducible morphisms as arrows
(Gabriel–Roiter 13.6). A directed path of `Q_P` evaluates to a morphism of
`P` (`pathMor`), evaluation turns concatenation into composition, and every
nonzero non-isomorphism is the value of a path (`exists_path`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits FinQuiver

namespace RayQuiver

variable (P : Type) [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P]

/-- The arrows of `Q_P`: irreducible morphisms. -/
def Arr : Type := Σ (x y : P), {f : x ⟶ y // IsIrreducible f}

open Classical in
noncomputable instance : Fintype (Arr P) := by
  haveI : ∀ x y : P, Finite (x ⟶ y) := IsRayCategory.finite_hom
  haveI : ∀ x y : P, Fintype (x ⟶ y) := fun _ _ ↦ Fintype.ofFinite _
  unfold Arr; infer_instance

open Classical in
noncomputable instance : DecidableEq (Arr P) := Classical.decEq _

/-- The quiver `Q_P` of a finite ray category. -/
abbrev quiver : FinQuiver where
  V := P
  A := Arr P
  src a := a.1
  tgt a := a.2.1

variable {P}

/-- The morphism of `P` given by a directed path of `Q_P`. -/
def pathMor : ∀ (l : List (quiver P).A) (x y : P), PathFrom (D := quiver P) x l y → (x ⟶ y)
  | [], _, _, h => eqToHom h
  | e :: l, _, y, h => eqToHom h.1.symm ≫ e.2.2.1 ≫ pathMor l e.2.1 y h.2

lemma pathFrom_append : ∀ (l l' : List (quiver P).A) (x y z : P),
    PathFrom (D := quiver P) x l y → PathFrom (D := quiver P) y l' z →
      PathFrom (D := quiver P) x (l ++ l') z
  | [], _, x, y, z, h, h' => by
    change x = y at h
    subst h; exact h'
  | e :: l, l', x, y, z, h, h' => ⟨h.1, pathFrom_append l l' _ y z h.2 h'⟩

lemma pathMor_append : ∀ (l l' : List (quiver P).A) (x y z : P)
    (h : PathFrom (D := quiver P) x l y) (h' : PathFrom (D := quiver P) y l' z),
      pathMor (l ++ l') x z (pathFrom_append l l' x y z h h') = pathMor l x y h ≫ pathMor l' y z h'
  | [], l', x, y, z, h, h' => by
    change x = y at h
    subst h
    simp [pathMor]
  | e :: l, l', x, y, z, h, h' => by
    change eqToHom _ ≫ e.2.2.1 ≫ pathMor (l ++ l') e.2.1 z _ =
      (eqToHom _ ≫ e.2.2.1 ≫ pathMor l e.2.1 y h.2) ≫ pathMor l' y z h'
    rw [pathMor_append l l' e.2.1 y z h.2 h']
    simp

/-- Every nonzero non-isomorphism of `P` is the value of a directed path of
`Q_P`. -/
theorem exists_path {x y : P} (f : x ⟶ y) (hf : f ≠ 0) (hiso : ¬IsIso f) :
    ∃ (l : List (quiver P).A) (h : PathFrom (D := quiver P) x l y), pathMor l x y h = f := by
  have key : ∀ {x y : P} (f : x ⟶ y), IrrComp f →
      ∃ (l : List (quiver P).A) (h : PathFrom (D := quiver P) x l y), pathMor l x y h = f := by
    intro x y f hf
    induction hf with
    | @irr x y f hirr =>
      refine ⟨[⟨x, y, f, hirr⟩], ⟨rfl, rfl⟩, ?_⟩
      change eqToHom rfl ≫ f ≫ eqToHom rfl = f
      simp
    | @comp x y z g h _ _ ihg ihh =>
      obtain ⟨l, hl, rfl⟩ := ihg
      obtain ⟨l', hl', rfl⟩ := ihh
      exact ⟨l ++ l', pathFrom_append l l' x z y hl hl', pathMor_append l l' x z y hl hl'⟩
  exact key f (IsRayCategory.irrComp f hf hiso)

variable (k : Type*) [Field k] (P)

/-- The relations of the linearization: a path whose value is zero is zero,
and two paths with the same value are equal. -/
inductive LinRel : (quiver P).PathAlgebra k → (quiver P).PathAlgebra k → Prop
  | zero (l : List (quiver P).A) (x y : P) (h : PathFrom (D := quiver P) x l y)
      (h0 : pathMor l x y h = 0) : LinRel (word k (quiver P) l) 0
  | eq (l l' : List (quiver P).A) (x y : P) (h : PathFrom (D := quiver P) x l y)
      (h' : PathFrom (D := quiver P) x l' y) (he : pathMor l x y h = pathMor l' x y h') :
      LinRel (word k (quiver P) l) (word k (quiver P) l')

/-- The linearization `k(P)` of a finite ray category (Gabriel–Roiter 13.5),
presented as a quotient of the path algebra of `Q_P`. -/
abbrev Linearization := RingQuot (LinRel P k)

/-- The presentation `kQ_P → k(P)`. -/
def linPres : (quiver P).PathAlgebra k →ₐ[k] Linearization P k := RingQuot.mkAlgHom k (LinRel P k)

lemma linPres_surjective : Function.Surjective (linPres P k) :=
  RingQuot.mkAlgHom_surjective k (LinRel P k)

end RayQuiver

end LargeIndecomposable
