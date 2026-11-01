module

public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalCleavingTransfer

@[expose] public section

/-!
# The BGRS Figure 14 cleaving diagram

The source has two two-dimensional central vertices joined by `lambda`, with
two incoming and two outgoing one-dimensional leaves.  This is the mixed
orientation of affine `D̃₅` displayed in BGRS Figure 14.  The family below
uses the four forms/lines

* `e₀ : k → k²`,
* `e₁ : k → k²`,
* `(1,1) : k² → k`, and
* `(c,1) : k² → k`.

Its endomorphisms are scalar, and an isomorphism between parameters forces
the parameters to agree.  The last theorem leaves only the literal
Hom-bifunctor retraction (the source's cleaving assertion) as an ambient
callback.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace LargeIndecomposable.CriticalSingularFigure14

open LargeIndecomposable.CriticalSingularCleaving
open LargeIndecomposable.ClosedZigzagCrossUniverse

universe u

variable {k : Type u} [Field k]

/-- The six vertex occurrences in Figure 14.  The two occurrences labelled
`c` and the two labelled `d` in the printed diagram are deliberately kept
distinct in the source. -/
inductive Vertex
  | leftCenter
  | rightCenter
  | leftLeaf
  | upperLeaf
  | lowerLeaf
  | rightLeaf
  deriving DecidableEq

def vertexEquiv : Vertex ≃ Fin 6 where
  toFun
    | .leftCenter => 0
    | .rightCenter => 1
    | .leftLeaf => 2
    | .upperLeaf => 3
    | .lowerLeaf => 4
    | .rightLeaf => 5
  invFun
    | ⟨0, _⟩ => .leftCenter
    | ⟨1, _⟩ => .rightCenter
    | ⟨2, _⟩ => .leftLeaf
    | ⟨3, _⟩ => .upperLeaf
    | ⟨4, _⟩ => .lowerLeaf
    | ⟨5, _⟩ => .rightLeaf
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype Vertex := Fintype.ofEquiv (Fin 6) vertexEquiv.symm

/-- The five arrows of the literal Figure-14 source. -/
inductive Arrow : Vertex → Vertex → Type
  | lambda : Arrow .leftCenter .rightCenter
  | alphaLeft : Arrow .leftLeaf .leftCenter
  | deltaUpper : Arrow .upperLeaf .rightCenter
  | deltaLower : Arrow .leftCenter .lowerLeaf
  | alphaRight : Arrow .rightCenter .rightLeaf

instance : Quiver Vertex where Hom := Arrow

private theorem arrow_subsingleton (a b : Vertex) :
    Subsingleton (Arrow a b) := by
  constructor
  intro e f
  cases e <;> cases f <;> rfl

private theorem opposite_eq_op_of_unop_eq
    {a : Vertexᵒᵖ} {b : Vertex} (h : a.unop = b) :
    a = Opposite.op b := by
  apply Opposite.unop_injective
  simpa using h

private theorem arrow_from_leftCenter_target
    {b : Vertex} (e : Arrow .leftCenter b) :
    b = .rightCenter ∨ b = .lowerLeaf := by
  cases e with
  | lambda => exact Or.inl rfl
  | deltaLower => exact Or.inr rfl

private theorem arrow_from_rightCenter_target
    {b : Vertex} (e : Arrow .rightCenter b) :
    b = .rightLeaf := by
  cases e
  rfl

private theorem arrow_from_leftLeaf_target
    {b : Vertex} (e : Arrow .leftLeaf b) :
    b = .leftCenter := by
  cases e
  rfl

private theorem arrow_from_upperLeaf_target
    {b : Vertex} (e : Arrow .upperLeaf b) :
    b = .rightCenter := by
  cases e
  rfl

abbrev TotalArrow := Σ a, Σ b, Arrow a b

def totalArrow {a b : Vertex} (e : Arrow a b) : TotalArrow :=
  ⟨a, b, e⟩

private theorem totalArrow_source_ne_target (e : TotalArrow) :
    e.1 ≠ e.2.1 := by
  rcases e with ⟨a, b, e⟩
  cases e <;> intro h <;> cases h

private theorem opposite_arrow_source_ne_target
    {a b : Vertexᵒᵖ} (e : a ⟶ b) : a ≠ b := by
  intro hab
  apply totalArrow_source_ne_target (totalArrow e.unop)
  exact (congrArg Opposite.unop hab).symm

private theorem no_arrow_from_lowerLeaf (b : Vertex) :
    IsEmpty (Arrow .lowerLeaf b) := by
  constructor
  intro e
  cases e

private theorem no_arrow_from_rightLeaf (b : Vertex) :
    IsEmpty (Arrow .rightLeaf b) := by
  constructor
  intro e
  cases e

private theorem no_arrow_to_leftLeaf (a : Vertex) :
    IsEmpty (Arrow a .leftLeaf) := by
  constructor
  intro e
  cases e

private theorem no_arrow_to_upperLeaf (a : Vertex) :
    IsEmpty (Arrow a .upperLeaf) := by
  constructor
  intro e
  cases e

private theorem opposite_no_arrow_to_lowerLeaf (a : Vertexᵒᵖ) :
    IsEmpty (a ⟶ Opposite.op Vertex.lowerLeaf) := by
  constructor
  intro e
  exact (no_arrow_from_lowerLeaf a.unop).false e.unop

private theorem opposite_no_arrow_to_rightLeaf (a : Vertexᵒᵖ) :
    IsEmpty (a ⟶ Opposite.op Vertex.rightLeaf) := by
  constructor
  intro e
  exact (no_arrow_from_rightLeaf a.unop).false e.unop

private theorem opposite_no_arrow_from_leftLeaf (b : Vertexᵒᵖ) :
    IsEmpty (Opposite.op Vertex.leftLeaf ⟶ b) := by
  constructor
  intro e
  exact (no_arrow_to_leftLeaf b.unop).false e.unop

private theorem opposite_no_arrow_from_upperLeaf (b : Vertexᵒᵖ) :
    IsEmpty (Opposite.op Vertex.upperLeaf ⟶ b) := by
  constructor
  intro e
  exact (no_arrow_to_upperLeaf b.unop).false e.unop

theorem path_length_zero_of_target_lowerLeaf {a : Vertexᵒᵖ}
    (p : Quiver.Path a (Opposite.op Vertex.lowerLeaf)) : p.length = 0 := by
  cases p with
  | nil => rfl
  | cons _ e =>
      exact False.elim ((opposite_no_arrow_to_lowerLeaf _).false e)

theorem path_length_zero_of_target_rightLeaf {a : Vertexᵒᵖ}
    (p : Quiver.Path a (Opposite.op Vertex.rightLeaf)) : p.length = 0 := by
  cases p with
  | nil => rfl
  | cons _ e =>
      exact False.elim ((opposite_no_arrow_to_rightLeaf _).false e)

theorem path_length_zero_of_source_leftLeaf {b : Vertexᵒᵖ}
    (p : Quiver.Path (Opposite.op Vertex.leftLeaf) b) : p.length = 0 := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      have hsource := p.eq_of_length_zero ih
      subst_vars
      exact False.elim ((opposite_no_arrow_from_leftLeaf _).false e)

theorem path_length_zero_of_source_upperLeaf {b : Vertexᵒᵖ}
    (p : Quiver.Path (Opposite.op Vertex.upperLeaf) b) : p.length = 0 := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      have hsource := p.eq_of_length_zero ih
      subst_vars
      exact False.elim ((opposite_no_arrow_from_upperLeaf _).false e)

private theorem arrow_to_rightCenter_source_eq_rightLeaf
    {b : Vertexᵒᵖ} (e : b ⟶ Opposite.op Vertex.rightCenter) :
    b = Opposite.op Vertex.rightLeaf := by
  induction b using Opposite.rec with
  | _ b =>
      cases e.unop
      rfl

private theorem arrow_to_leftCenter_source
    {b : Vertexᵒᵖ} (e : b ⟶ Opposite.op Vertex.leftCenter) :
    b = Opposite.op Vertex.rightCenter ∨
      b = Opposite.op Vertex.lowerLeaf := by
  induction b using Opposite.rec with
  | _ b =>
      cases e.unop with
      | lambda => exact Or.inl rfl
      | deltaLower => exact Or.inr rfl

private theorem arrow_to_leftLeaf_source_eq_leftCenter
    {b : Vertexᵒᵖ} (e : b ⟶ Opposite.op Vertex.leftLeaf) :
    b = Opposite.op Vertex.leftCenter := by
  induction b using Opposite.rec with
  | _ b =>
      cases e.unop
      rfl

private theorem arrow_to_upperLeaf_source_eq_rightCenter
    {b : Vertexᵒᵖ} (e : b ⟶ Opposite.op Vertex.upperLeaf) :
    b = Opposite.op Vertex.rightCenter := by
  induction b using Opposite.rec with
  | _ b =>
      cases e.unop
      rfl

private theorem path_length_zero_before_arrow_to_rightCenter
    {a b : Vertexᵒᵖ} (p : Quiver.Path a b)
    (e : b ⟶ Opposite.op Vertex.rightCenter) : p.length = 0 := by
  have hb := arrow_to_rightCenter_source_eq_rightLeaf e
  subst b
  exact path_length_zero_of_target_rightLeaf p

private theorem path_subsingleton_of_all_length_zero
    (a b : Vertexᵒᵖ) (hzero : ∀ p : Quiver.Path a b, p.length = 0) :
    Subsingleton (Quiver.Path a b) := by
  constructor
  intro p q
  have hp := p.eq_of_length_zero (hzero p)
  subst b
  rw [Quiver.Path.eq_nil_of_length_zero p (hzero p),
    Quiver.Path.eq_nil_of_length_zero q (hzero q)]

private theorem path_rightCenter_subsingleton (a : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a (Opposite.op Vertex.rightCenter)) := by
  constructor
  intro p q
  cases p with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e =>
          have hq0 := path_length_zero_before_arrow_to_rightCenter q e
          have hstart := q.eq_of_length_zero hq0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
  | cons p e =>
      cases q with
      | nil =>
          have hp0 := path_length_zero_before_arrow_to_rightCenter p e
          have hstart := p.eq_of_length_zero hp0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
      | cons q f =>
          have hp0 := path_length_zero_before_arrow_to_rightCenter p e
          have hq0 := path_length_zero_before_arrow_to_rightCenter q f
          have hbc := (p.eq_of_length_zero hp0).symm.trans
            (q.eq_of_length_zero hq0)
          cases hbc
          have hef : e = f := Quiver.Hom.unop_inj
            ((arrow_subsingleton _ _).elim e.unop f.unop)
          subst f
          have hpa := p.eq_of_length_zero hp0
          subst_vars
          rw [Quiver.Path.eq_nil_of_length_zero p hp0,
            Quiver.Path.eq_nil_of_length_zero q hq0]

private theorem no_path_leftCenter_to_rightCenter
    (p : Quiver.Path (Opposite.op Vertex.leftCenter)
      (Opposite.op Vertex.rightCenter)) : False := by
  cases p with
  | cons p e =>
      have hp0 := path_length_zero_before_arrow_to_rightCenter p e
      have hstart := p.eq_of_length_zero hp0
      subst_vars
      have hempty : IsEmpty (Arrow .rightCenter .leftCenter) := by
        constructor
        intro f
        cases f
      exact hempty.false e.unop

private theorem no_path_lowerLeaf_to_rightCenter
    (p : Quiver.Path (Opposite.op Vertex.lowerLeaf)
      (Opposite.op Vertex.rightCenter)) : False := by
  cases p with
  | cons p e =>
      have hp0 := path_length_zero_before_arrow_to_rightCenter p e
      have hstart := p.eq_of_length_zero hp0
      subst_vars
      have hempty : IsEmpty (Arrow .rightCenter .lowerLeaf) := by
        constructor
        intro f
        cases f
      exact hempty.false e.unop

private theorem no_path_leftCenter_to_lowerLeaf
    (p : Quiver.Path (Opposite.op Vertex.leftCenter)
      (Opposite.op Vertex.lowerLeaf)) : False := by
  have hp0 := path_length_zero_of_target_lowerLeaf p
  have h := p.eq_of_length_zero hp0
  cases h

private theorem path_leftCenter_subsingleton (a : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a (Opposite.op Vertex.leftCenter)) := by
  constructor
  intro p q
  cases p with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e =>
          rcases arrow_to_leftCenter_source e with he | he
          · subst_vars
            exact False.elim (no_path_leftCenter_to_rightCenter q)
          · subst_vars
            exact False.elim (no_path_leftCenter_to_lowerLeaf q)
  | cons p e =>
      cases q with
      | nil =>
          rcases arrow_to_leftCenter_source e with he | he
          · subst_vars
            exact False.elim (no_path_leftCenter_to_rightCenter p)
          · subst_vars
            exact False.elim (no_path_leftCenter_to_lowerLeaf p)
      | cons q f =>
          rcases arrow_to_leftCenter_source e with he | he <;>
            rcases arrow_to_leftCenter_source f with hf | hf
          · subst_vars
            have hef : e = f := Quiver.Hom.unop_inj
              ((arrow_subsingleton _ _).elim e.unop f.unop)
            subst f
            congr 1
            exact (path_rightCenter_subsingleton a).elim p q
          · subst_vars
            have hq0 := path_length_zero_of_target_lowerLeaf q
            have ha := q.eq_of_length_zero hq0
            subst a
            exact False.elim (no_path_lowerLeaf_to_rightCenter p)
          · subst_vars
            have hp0 := path_length_zero_of_target_lowerLeaf p
            have ha := p.eq_of_length_zero hp0
            subst a
            exact False.elim (no_path_lowerLeaf_to_rightCenter q)
          · subst_vars
            have hef : e = f := Quiver.Hom.unop_inj
              ((arrow_subsingleton _ _).elim e.unop f.unop)
            subst f
            congr 1
            exact (path_subsingleton_of_all_length_zero a _
              (fun r ↦ path_length_zero_of_target_lowerLeaf r)).elim p q

private theorem path_leftLeaf_subsingleton (a : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a (Opposite.op Vertex.leftLeaf)) := by
  constructor
  intro p q
  cases p with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e =>
          have hq0 := path_length_zero_of_source_leftLeaf q
          have hstart := q.eq_of_length_zero hq0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
  | cons p e =>
      cases q with
      | nil =>
          have hp0 := path_length_zero_of_source_leftLeaf p
          have hstart := p.eq_of_length_zero hp0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
      | cons q f =>
          have he := arrow_to_leftLeaf_source_eq_leftCenter e
          have hf := arrow_to_leftLeaf_source_eq_leftCenter f
          subst_vars
          have hef : e = f := Quiver.Hom.unop_inj
            ((arrow_subsingleton _ _).elim e.unop f.unop)
          subst f
          congr 1
          exact (path_leftCenter_subsingleton a).elim p q

private theorem path_upperLeaf_subsingleton (a : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a (Opposite.op Vertex.upperLeaf)) := by
  constructor
  intro p q
  cases p with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e =>
          have hq0 := path_length_zero_of_source_upperLeaf q
          have hstart := q.eq_of_length_zero hq0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
  | cons p e =>
      cases q with
      | nil =>
          have hp0 := path_length_zero_of_source_upperLeaf p
          have hstart := p.eq_of_length_zero hp0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
      | cons q f =>
          have he := arrow_to_upperLeaf_source_eq_rightCenter e
          have hf := arrow_to_upperLeaf_source_eq_rightCenter f
          subst_vars
          have hef : e = f := Quiver.Hom.unop_inj
            ((arrow_subsingleton _ _).elim e.unop f.unop)
          subst f
          congr 1
          exact (path_rightCenter_subsingleton a).elim p q

/-- The free Figure-14 path category is thin: between any ordered pair of
source occurrences there is at most one directed path. -/
theorem path_subsingleton (a b : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a b) := by
  induction b using Opposite.rec with
  | _ b =>
      cases b with
      | leftCenter => exact path_leftCenter_subsingleton a
      | rightCenter => exact path_rightCenter_subsingleton a
      | leftLeaf => exact path_leftLeaf_subsingleton a
      | upperLeaf => exact path_upperLeaf_subsingleton a
      | lowerLeaf =>
          exact path_subsingleton_of_all_length_zero a _
            (fun p ↦ path_length_zero_of_target_lowerLeaf p)
      | rightLeaf =>
          exact path_subsingleton_of_all_length_zero a _
            (fun p ↦ path_length_zero_of_target_rightLeaf p)

/-- Free linear source, with the opposite correcting the path category's
reversed convention. -/
abbrev LinearSource (k : Type u) [Field k] :=
  LinearPathCategory.Category k Vertexᵒᵖ

def vertexOppositeEquiv : Vertex ≃ Vertexᵒᵖ where
  toFun := Opposite.op
  invFun := Opposite.unop
  left_inv _ := rfl
  right_inv _ := rfl

instance vertexOppositeFintype : Fintype Vertexᵒᵖ :=
  Fintype.ofEquiv Vertex vertexOppositeEquiv

instance linearSourceFintype : Fintype (LinearSource k) :=
  Fintype.ofEquiv Vertexᵒᵖ (Equiv.refl Vertexᵒᵖ)

def vertexObj (a : Vertex) : LinearSource k :=
  LinearPathCategory.obj k Vertexᵒᵖ (Opposite.op a)

def generatorHom {a b : Vertex} (e : a ⟶ b) :
    vertexObj (k := k) a ⟶ vertexObj (k := k) b :=
  LinearPathCategory.pathHom (Quiver.Hom.toPath (Quiver.Hom.op e))

abbrev Center := ModuleCat.of k (Fin 2 → k)
abbrev Leaf := ModuleCat.of k k

abbrev obj : Vertex → ModuleCat k
  | .leftCenter | .rightCenter => Center (k := k)
  | .leftLeaf | .upperLeaf | .lowerLeaf | .rightLeaf => Leaf (k := k)

def basisVec (i : Fin 2) : Center (k := k) := Pi.single i 1

@[simp] private theorem basisVec_apply (i j : Fin 2) :
    basisVec (k := k) i j = if i = j then 1 else 0 := by
  simp [basisVec, Pi.single_apply, eq_comm]

def columnHom (a b : k) : Leaf (k := k) ⟶ Center (k := k) :=
  ModuleCat.ofHom
    { toFun := fun x i ↦ if i = 0 then a * x else b * x
      map_add' := by
        intro x y
        funext i
        fin_cases i <;> simp [mul_add]
      map_smul' := by
        intro c x
        funext i
        fin_cases i <;> simp <;> ring }

@[simp] private theorem columnHom_one_zero (x : k) :
    columnHom (k := k) 1 0 x = x • basisVec (k := k) 0 := by
  funext i
  fin_cases i <;> simp [columnHom, basisVec]

@[simp] private theorem columnHom_zero_one (x : k) :
    columnHom (k := k) 0 1 x = x • basisVec (k := k) 1 := by
  funext i
  fin_cases i <;> simp [columnHom, basisVec]

def rowHom (a b : k) : Center (k := k) ⟶ Leaf (k := k) :=
  ModuleCat.ofHom
    { toFun := fun x ↦ a * x 0 + b * x 1
      map_add' := by intros; simp [mul_add]; abel
      map_smul' := by intros; simp [mul_add]; ring }

def centerId : Center (k := k) ⟶ Center (k := k) := 𝟙 _

/-- Arrow realization for parameter `c`. -/
def arrowMap (c : k) {a b : Vertex} :
    (a ⟶ b) → (obj (k := k) a ⟶ obj (k := k) b)
  | .lambda => centerId (k := k)
  | .alphaLeft => columnHom (k := k) 1 0
  | .deltaUpper => columnHom (k := k) 0 1
  | .deltaLower => rowHom (k := k) 1 1
  | .alphaRight => rowHom (k := k) c 1

/-- Explicit one-parameter representation of the Figure-14 source. -/
def module (c : k) : LinearSource k ⥤ ModuleCat k :=
  LinearPathCategory.lift
    (fun a ↦ obj (k := k) a.unop)
    (fun e ↦ arrowMap (k := k) c e.unop)

instance module_additive (c : k) : (module (k := k) c).Additive := by
  unfold module
  infer_instance

instance module_linear (c : k) : (module (k := k) c).Linear k := by
  unfold module
  infer_instance

@[simp] theorem module_obj (c : k) (a : Vertex) :
    (module (k := k) c).obj (vertexObj (k := k) a) = obj (k := k) a := rfl

@[simp] theorem module_map_generator (c : k) {a b : Vertex} (e : a ⟶ b) :
    (module (k := k) c).map (generatorHom (k := k) e) =
      arrowMap (k := k) c e := by
  unfold module generatorHom
  rw [LinearPathCategory.lift_map_pathHom]
  simp only [Quiver.Hom.toPath, LinearPathCategory.pathMap_cons,
    LinearPathCategory.pathMap_nil, Category.comp_id]
  rfl

def leftComponent {c d : k} (f : module (k := k) c ⟶ module d) :
    Center (k := k) ⟶ Center (k := k) :=
  f.app (vertexObj (k := k) .leftCenter)

def rightComponent {c d : k} (f : module (k := k) c ⟶ module d) :
    Center (k := k) ⟶ Center (k := k) :=
  f.app (vertexObj (k := k) .rightCenter)

def leafComponent {c d : k} (f : module (k := k) c ⟶ module d)
    (a : Vertex) : obj (k := k) a ⟶ obj (k := k) a :=
  f.app (vertexObj (k := k) a)

def coeff {c d : k} (f : module (k := k) c ⟶ module d) : k :=
  leftComponent f (basisVec (k := k) 0) 0

private theorem leaf_map_eq_mul (g : Leaf (k := k) ⟶ Leaf (k := k))
    (x : k) : g x = x * g 1 := by
  simpa using g.hom.map_smul x 1

private theorem naturality_lambda {c d : k}
    (f : module (k := k) c ⟶ module d) :
    leftComponent f = rightComponent f := by
  have h := f.naturality (generatorHom (k := k) Arrow.lambda)
  rw [module_map_generator, module_map_generator] at h
  change centerId (k := k) ≫ rightComponent f =
    leftComponent f ≫ centerId (k := k) at h
  simpa [centerId] using h.symm

private theorem left_basis_zero {c d : k}
    (f : module (k := k) c ⟶ module d) :
    leftComponent f (basisVec (k := k) 0) =
      coeff f • basisVec (k := k) 0 := by
  have h := f.naturality (generatorHom (k := k) Arrow.alphaLeft)
  rw [module_map_generator, module_map_generator] at h
  have h1 := congrArg
    (fun q : Leaf (k := k) ⟶ Center (k := k) ↦ q 1) h
  have hvec : leftComponent f (basisVec (k := k) 0) =
      (leafComponent f .leftLeaf 1) • basisVec (k := k) 0 := by
    change leftComponent f (columnHom (k := k) 1 0 1) =
      columnHom (k := k) 1 0 (leafComponent f .leftLeaf 1) at h1
    rw [columnHom_one_zero, columnHom_one_zero] at h1
    simpa using h1
  have hc : leafComponent f .leftLeaf 1 = coeff f := by
    have h0 := congrArg (fun x : Center (k := k) ↦ x 0) hvec
    simpa [coeff, basisVec, Pi.single_apply] using h0.symm
  simpa [hc] using hvec

private theorem left_basis_one {c d : k}
    (f : module (k := k) c ⟶ module d) :
    leftComponent f (basisVec (k := k) 1) =
      coeff f • basisVec (k := k) 1 := by
  let q : k := leafComponent f .upperLeaf 1
  have hu := f.naturality (generatorHom (k := k) Arrow.deltaUpper)
  rw [module_map_generator, module_map_generator] at hu
  have hu1 := congrArg
    (fun g : Leaf (k := k) ⟶ Center (k := k) ↦ g 1) hu
  have hright : rightComponent f (basisVec (k := k) 1) =
      q • basisVec (k := k) 1 := by
    change rightComponent f (columnHom (k := k) 0 1 1) =
      columnHom (k := k) 0 1 (leafComponent f .upperLeaf 1) at hu1
    rw [columnHom_zero_one, columnHom_zero_one] at hu1
    simpa [q] using hu1
  rw [← naturality_lambda f] at hright
  have hl := f.naturality (generatorHom (k := k) Arrow.deltaLower)
  rw [module_map_generator, module_map_generator] at hl
  have hl0 := congrArg
    (fun g : Center (k := k) ⟶ Leaf (k := k) ↦
      g (basisVec (k := k) 0)) hl
  have hl1 := congrArg
    (fun g : Center (k := k) ⟶ Leaf (k := k) ↦
      g (basisVec (k := k) 1)) hl
  have hzero : leafComponent f .lowerLeaf 1 = coeff f := by
    have hz : leafComponent f .lowerLeaf 1 =
        leftComponent f (basisVec (k := k) 0) 0 +
          leftComponent f (basisVec (k := k) 0) 1 := by
      simpa [arrowMap, rowHom, leafComponent, leftComponent,
        basisVec, Pi.single_apply] using hl0
    rw [left_basis_zero] at hz
    simpa [basisVec, Pi.single_apply] using hz
  have hone : leafComponent f .lowerLeaf 1 = q := by
    have ho : leafComponent f .lowerLeaf 1 =
        leftComponent f (basisVec (k := k) 1) 0 +
          leftComponent f (basisVec (k := k) 1) 1 := by
      simpa [arrowMap, rowHom, leafComponent, leftComponent,
        basisVec, Pi.single_apply] using hl1
    rw [hright] at ho
    simpa [basisVec, Pi.single_apply] using ho
  have hq : q = coeff f := hone.symm.trans hzero
  simpa [hq] using hright

private theorem left_central_scalar {c d : k}
    (f : module (k := k) c ⟶ module d) (x : Center (k := k)) :
    leftComponent f x = coeff f • x := by
  have hx : x = x 0 • basisVec (k := k) 0 +
      x 1 • basisVec (k := k) 1 := by
    funext i
    fin_cases i <;> simp [basisVec]
  rw [hx, map_add, map_smul, map_smul, left_basis_zero, left_basis_one]
  module

/-- Every family morphism is scalar on the two central vertices, and its
scalar intertwines the parameters. -/
theorem hom_central_scalar {c d : k}
    (f : module (k := k) c ⟶ module d) :
    (∀ x : Center (k := k), leftComponent f x = coeff f • x) ∧
    (∀ x : Center (k := k), rightComponent f x = coeff f • x) ∧
    c * coeff f = d * coeff f := by
  have hl (x : Center (k := k)) := left_central_scalar f x
  have hr (x : Center (k := k)) : rightComponent f x = coeff f • x := by
    rw [← naturality_lambda f]
    exact hl x
  have h := f.naturality (generatorHom (k := k) Arrow.alphaRight)
  rw [module_map_generator, module_map_generator] at h
  have h0 := congrArg
    (fun g : Center (k := k) ⟶ Leaf (k := k) ↦
      g (basisVec (k := k) 0)) h
  have h1 := congrArg
    (fun g : Center (k := k) ⟶ Leaf (k := k) ↦
      g (basisVec (k := k) 1)) h
  have h0' : leafComponent f .rightLeaf c = d * coeff f := by
    have hraw : leafComponent f .rightLeaf c =
        d * rightComponent f (basisVec (k := k) 0) 0 +
          rightComponent f (basisVec (k := k) 0) 1 := by
      simpa [arrowMap, rowHom, leafComponent, rightComponent,
        basisVec, Pi.single_apply] using h0
    rw [hr] at hraw
    simpa [basisVec, Pi.single_apply] using hraw
  have h1' : leafComponent f .rightLeaf 1 = coeff f := by
    have hraw : leafComponent f .rightLeaf 1 =
        d * rightComponent f (basisVec (k := k) 1) 0 +
          rightComponent f (basisVec (k := k) 1) 1 := by
      simpa [arrowMap, rowHom, leafComponent, rightComponent,
        basisVec, Pi.single_apply] using h1
    rw [hr] at hraw
    simpa [basisVec, Pi.single_apply] using hraw
  rw [leaf_map_eq_mul, h1'] at h0'
  exact ⟨hl, hr, h0'⟩

theorem parameter_eq_of_iso {c d : k}
    (e : module (k := k) c ≅ module d) : c = d := by
  have h := (hom_central_scalar e.hom).2.2
  have hcoeff : coeff e.hom ≠ 0 := by
    intro hz
    have hl := (hom_central_scalar e.hom).1 (basisVec (k := k) 0)
    rw [hz, zero_smul] at hl
    have hinv := congrArg
      (fun g : module (k := k) c ⟶ module c ↦
        g.app (vertexObj (k := k) .leftCenter)
          (basisVec (k := k) 0)) e.hom_inv_id
    change leftComponent e.inv
      (leftComponent e.hom (basisVec (k := k) 0)) =
        basisVec (k := k) 0 at hinv
    rw [hl, map_zero] at hinv
    have hcoord := congrArg (fun x : Center (k := k) ↦ x 0) hinv
    change (0 : k) = 1 at hcoord
    exact zero_ne_one hcoord
  exact mul_right_cancel₀ hcoeff h

private theorem component_scalar {c : k}
    (f : module (k := k) c ⟶ module c) (a : Vertex)
    (x : obj (k := k) a) :
    leafComponent f a x = coeff f • x := by
  cases a with
  | leftCenter => exact (hom_central_scalar f).1 x
  | rightCenter => exact (hom_central_scalar f).2.1 x
  | leftLeaf =>
      have h := f.naturality (generatorHom (k := k) Arrow.alphaLeft)
      simp only [module_map_generator] at h
      have h1 := congrArg
        (fun g : Leaf (k := k) ⟶ Center (k := k) ↦ g 1) h
      have hone : leafComponent f .leftLeaf 1 = coeff f := by
        have hvec : leftComponent f (basisVec (k := k) 0) =
            leafComponent f .leftLeaf 1 • basisVec (k := k) 0 := by
          change leftComponent f (columnHom (k := k) 1 0 1) =
            columnHom (k := k) 1 0 (leafComponent f .leftLeaf 1) at h1
          rw [columnHom_one_zero, columnHom_one_zero] at h1
          simpa using h1
        have hraw := congrArg (fun y : Center (k := k) ↦ y 0) hvec
        simpa [coeff, basisVec, Pi.single_apply] using hraw.symm
      rw [leaf_map_eq_mul, hone]
      exact mul_comm _ _
  | upperLeaf =>
      have h := f.naturality (generatorHom (k := k) Arrow.deltaUpper)
      simp only [module_map_generator] at h
      have h1 := congrArg
        (fun g : Leaf (k := k) ⟶ Center (k := k) ↦ g 1) h
      have hone : leafComponent f .upperLeaf 1 = coeff f := by
        have hvec : rightComponent f (basisVec (k := k) 1) =
            leafComponent f .upperLeaf 1 • basisVec (k := k) 1 := by
          change rightComponent f (columnHom (k := k) 0 1 1) =
            columnHom (k := k) 0 1 (leafComponent f .upperLeaf 1) at h1
          rw [columnHom_zero_one, columnHom_zero_one] at h1
          simpa using h1
        have hraw := congrArg (fun y : Center (k := k) ↦ y 1) hvec
        have hs := (hom_central_scalar f).1 (basisVec (k := k) 1)
        rw [← naturality_lambda f, hs] at hraw
        simpa [basisVec, Pi.single_apply] using hraw.symm
      rw [leaf_map_eq_mul, hone]
      exact mul_comm _ _
  | lowerLeaf =>
      have h := f.naturality (generatorHom (k := k) Arrow.deltaLower)
      simp only [module_map_generator] at h
      have h0 := congrArg
        (fun g : Center (k := k) ⟶ Leaf (k := k) ↦
          g (basisVec (k := k) 0)) h
      have hone : leafComponent f .lowerLeaf 1 = coeff f := by
        have hraw : leafComponent f .lowerLeaf 1 =
            leftComponent f (basisVec (k := k) 0) 0 +
              leftComponent f (basisVec (k := k) 0) 1 := by
          simpa [arrowMap, rowHom, leafComponent, leftComponent,
            basisVec, Pi.single_apply] using h0
        have hs := (hom_central_scalar f).1 (basisVec (k := k) 0)
        rw [hs] at hraw
        simpa [basisVec, Pi.single_apply] using hraw
      rw [leaf_map_eq_mul, hone]
      exact mul_comm _ _
  | rightLeaf =>
      have h := f.naturality (generatorHom (k := k) Arrow.alphaRight)
      simp only [module_map_generator] at h
      have h1 := congrArg
        (fun g : Center (k := k) ⟶ Leaf (k := k) ↦
          g (basisVec (k := k) 1)) h
      have hone : leafComponent f .rightLeaf 1 = coeff f := by
        have hraw : leafComponent f .rightLeaf 1 =
            c * rightComponent f (basisVec (k := k) 1) 0 +
              rightComponent f (basisVec (k := k) 1) 1 := by
          simpa [arrowMap, rowHom, leafComponent, rightComponent,
            basisVec, Pi.single_apply] using h1
        have hs := (hom_central_scalar f).2.1 (basisVec (k := k) 1)
        rw [hs] at hraw
        simpa [basisVec, Pi.single_apply] using hraw
      rw [leaf_map_eq_mul, hone]
      exact mul_comm _ _

theorem end_eq_zero_or_id_of_idempotent (c : k)
    (f : module (k := k) c ⟶ module c) (hf : f ≫ f = f) :
    f = 0 ∨ f = 𝟙 _ := by
  have hc := congrArg coeff hf
  have hmul : coeff f * coeff f = coeff f := by
    change leftComponent (f ≫ f) (basisVec (k := k) 0) 0 = coeff f at hc
    change leftComponent f (leftComponent f (basisVec (k := k) 0)) 0 =
      coeff f at hc
    rw [(hom_central_scalar f).1, (hom_central_scalar f).1] at hc
    simpa [smul_smul] using hc
  rcases eq_zero_or_one_of_sq_eq_self (by simpa [pow_two] using hmul) with h0 | h1
  · left
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change leafComponent f (LinearPathCategory.vertex X).unop x = 0
    rw [component_scalar, h0, zero_smul]
  · right
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change leafComponent f (LinearPathCategory.vertex X).unop x = x
    rw [component_scalar, h1, one_smul]

theorem module_not_isZero (c : k) : ¬ IsZero (module (k := k) c) := by
  intro hzero
  have hid : (𝟙 (module (k := k) c) : module c ⟶ module c) = 0 :=
    (IsZero.iff_id_eq_zero _).mp hzero
  have h := congrArg
    (fun f : module (k := k) c ⟶ module c ↦
      f.app (vertexObj (k := k) .leftCenter)
        (basisVec (k := k) 0) 0) hid
  change (1 : k) = 0 at h
  exact one_ne_zero h

theorem module_indecomposable (c : k) : Indecomposable (module (k := k) c) := by
  refine ⟨module_not_isZero c, ?_⟩
  intro Y Z e
  let p : module (k := k) c ⟶ module c :=
    e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv
  have hp : p ≫ p = p := by simp [p, Category.assoc]
  rcases end_eq_zero_or_id_of_idempotent c p hp with hp0 | hp1
  · left
    apply (IsZero.iff_id_eq_zero Y).mpr
    calc
      𝟙 Y = (biprod.inl ≫ e.inv) ≫ p ≫ (e.hom ≫ biprod.fst) := by
        dsimp [p]
        simp
      _ = 0 := by rw [hp0]; simp
  · right
    apply (IsZero.iff_id_eq_zero Z).mpr
    calc
      𝟙 Z = (biprod.inr ≫ e.inv) ≫ p ≫ (e.hom ≫ biprod.snd) := by
        rw [hp1]
        simp
      _ = 0 := by
        dsimp [p]
        simp

instance module_obj_finite (c : k) (X : LinearSource k) :
    Module.Finite k ((module (k := k) c).obj X) := by
  change Module.Finite k (obj (k := k) (LinearPathCategory.vertex X).unop)
  unfold obj Center Leaf
  cases (LinearPathCategory.vertex X).unop <;> infer_instance

theorem module_end_isLocalRing (c : k) :
    IsLocalRing (CategoryTheory.End (module (k := k) c)) :=
  LargeIndecomposable.ClosedZigzagTransfer.functor_end_isLocalRing
    (module (k := k) c) (fun X ↦ module_obj_finite c X)
      (module_indecomposable c)

section Infinite

variable [Infinite k]

def family (n : ℕ) : LinearSource k ⥤ ModuleCat k :=
  module (Infinite.natEmbedding k n)

instance family_additive (n : ℕ) : (family (k := k) n).Additive := by
  unfold family
  infer_instance

instance family_linear (n : ℕ) : (family (k := k) n).Linear k := by
  unfold family
  infer_instance

theorem family_obj_finite (n : ℕ) (X : LinearSource k) :
    Module.Finite k ((family (k := k) n).obj X) := by
  unfold family
  infer_instance

theorem family_indecomposable (n : ℕ) :
    Indecomposable (family (k := k) n) := module_indecomposable _

theorem family_eq_of_iso {m n : ℕ}
    (e : family (k := k) m ≅ family n) : m = n := by
  apply (Infinite.natEmbedding k).injective
  exact parameter_eq_of_iso e

theorem family_end_isLocalRing (n : ℕ) :
    IsLocalRing (CategoryTheory.End (family (k := k) n)) := by
  unfold family
  exact module_end_isLocalRing _

/-- The fully explicit source-family package for Figure 14. -/
def sourceFamily : CleavingSourceFamily (k := k) (LinearSource k) where
  anchor := vertexObj (k := k) .leftCenter
  module := family (k := k)
  additive := fun _ ↦ inferInstance
  linear := fun _ ↦ inferInstance
  obj_finite := family_obj_finite
  indecomposable := family_indecomposable
  eq_of_iso := fun h ↦ family_eq_of_iso (Classical.choice h)
  end_isLocalRing := family_end_isLocalRing

end Infinite

section Diagram

universe v w

variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]

/-- Literal ambient data occurring in Figure 14. -/
structure DiagramData where
  c : C
  d : C
  b : C
  cUpper : C
  dLower : C
  a : C
  lambda : c ⟶ d
  alphaLeft : b ⟶ c
  deltaUpper : cUpper ⟶ d
  deltaLower : c ⟶ dLower
  alphaRight : d ⟶ a

namespace DiagramData

def object (G : DiagramData (C := C)) : Vertex → C
  | .leftCenter => G.c
  | .rightCenter => G.d
  | .leftLeaf => G.b
  | .upperLeaf => G.cUpper
  | .lowerLeaf => G.dLower
  | .rightLeaf => G.a

def arrow (G : DiagramData (C := C)) {a b : Vertex} :
    (a ⟶ b) → (G.object a ⟶ G.object b)
  | .lambda => G.lambda
  | .alphaLeft => G.alphaLeft
  | .deltaUpper => G.deltaUpper
  | .deltaLower => G.deltaLower
  | .alphaRight => G.alphaRight

def functor (G : DiagramData (C := C)) : LinearSource k ⥤ C :=
  LinearPathCategory.lift
    (fun a ↦ G.object a.unop)
    (fun e ↦ G.arrow e.unop)

instance functor_additive (G : DiagramData (C := C)) :
    (G.functor (k := k)).Additive := by
  unfold functor
  infer_instance

instance functor_linear (G : DiagramData (C := C)) :
    (G.functor (k := k)).Linear k := by
  unfold functor
  infer_instance

@[simp] theorem functor_obj (G : DiagramData (C := C)) (a : Vertex) :
    (G.functor (k := k)).obj (vertexObj (k := k) a) = G.object a := rfl

@[simp] theorem functor_map_generator (G : DiagramData (C := C))
    {a b : Vertex} (e : a ⟶ b) :
    (G.functor (k := k)).map (generatorHom (k := k) e) = G.arrow e := by
  unfold functor generatorHom
  rw [LinearPathCategory.lift_map_pathHom]
  simp only [Quiver.Hom.toPath, LinearPathCategory.pathMap_cons,
    LinearPathCategory.pathMap_nil, Category.comp_id]
  rfl

private theorem left_ne_zero_of_comp_ne_zero
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (hfg : f ≫ g ≠ 0) :
    f ≠ 0 := by
  intro hf
  apply hfg
  simp [hf]

private theorem right_ne_zero_of_comp_ne_zero
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (hfg : f ≫ g ≠ 0) :
    g ≠ 0 := by
  intro hg
  apply hfg
  simp [hg]

private theorem source_id_ne_zero_of_ne_zero
    {X Y : C} {f : X ⟶ Y} (hf : f ≠ 0) : 𝟙 X ≠ 0 := by
  intro hX
  apply hf
  calc
    f = 𝟙 X ≫ f := by simp
    _ = 0 := by rw [hX]; simp

private theorem target_id_ne_zero_of_ne_zero
    {X Y : C} {f : X ⟶ Y} (hf : f ≠ 0) : 𝟙 Y ≠ 0 := by
  intro hY
  apply hf
  calc
    f = f ≫ 𝟙 Y := by simp
    _ = 0 := by rw [hY]; simp

/-- The Figure-14 source has only its five arrows, four length-two paths, and
one length-three path.  Nonvanishing of the four displayed length-two paths
and the length-three path therefore forces every raw source path to survive. -/
theorem pathMap_ne_zero_of_five_composites
    (G : DiagramData (C := C))
    (hleftLower : G.alphaLeft ≫ G.deltaLower ≠ 0)
    (hleftCenter : G.alphaLeft ≫ G.lambda ≠ 0)
    (hcenterRight : G.lambda ≫ G.alphaRight ≠ 0)
    (hupperRight : G.deltaUpper ≫ G.alphaRight ≠ 0)
    (hthree : G.alphaLeft ≫ G.lambda ≫ G.alphaRight ≠ 0)
    {a b : Vertexᵒᵖ} (p : Quiver.Path a b) :
    LinearPathCategory.pathMap
        (fun x ↦ G.object x.unop)
        (fun e ↦ G.arrow e.unop) p ≠ 0 := by
  have hAlphaLeft : G.alphaLeft ≠ 0 :=
    left_ne_zero_of_comp_ne_zero hleftLower
  have hDeltaLower : G.deltaLower ≠ 0 :=
    right_ne_zero_of_comp_ne_zero hleftLower
  have hLambda : G.lambda ≠ 0 :=
    right_ne_zero_of_comp_ne_zero hleftCenter
  have hAlphaRight : G.alphaRight ≠ 0 :=
    right_ne_zero_of_comp_ne_zero hcenterRight
  have hDeltaUpper : G.deltaUpper ≠ 0 :=
    left_ne_zero_of_comp_ne_zero hupperRight
  have hid : ∀ a : Vertex, 𝟙 (G.object a) ≠ 0 := by
    intro a
    cases a with
    | leftCenter => exact target_id_ne_zero_of_ne_zero hAlphaLeft
    | rightCenter => exact target_id_ne_zero_of_ne_zero hLambda
    | leftLeaf => exact source_id_ne_zero_of_ne_zero hAlphaLeft
    | upperLeaf => exact source_id_ne_zero_of_ne_zero hDeltaUpper
    | lowerLeaf => exact target_id_ne_zero_of_ne_zero hDeltaLower
    | rightLeaf => exact target_id_ne_zero_of_ne_zero hAlphaRight
  induction b using Opposite.rec with
  | _ b =>
    cases b with
    | leftCenter =>
        cases p with
        | nil => simpa using hid Vertex.leftCenter
        | @cons c _ p e =>
            rcases arrow_from_leftCenter_target e.unop with hc | hc
            · have hc' : c = Opposite.op Vertex.rightCenter :=
                opposite_eq_op_of_unop_eq hc
              subst c
              have he : e = Quiver.Hom.op Arrow.lambda :=
                Quiver.Hom.unop_inj ((arrow_subsingleton _ _).elim _ _)
              subst e
              rw [LinearPathCategory.pathMap_cons]
              cases p with
              | nil =>
                  convert hLambda using 1 <;> simp [object, arrow]
                  all_goals rfl
              | @cons d _ p q =>
                  have hd : d = Opposite.op Vertex.rightLeaf :=
                    opposite_eq_op_of_unop_eq
                      (arrow_from_rightCenter_target q.unop)
                  subst d
                  have hq : q = Quiver.Hom.op Arrow.alphaRight :=
                    Quiver.Hom.unop_inj
                      ((arrow_subsingleton _ _).elim _ _)
                  subst q
                  rw [LinearPathCategory.pathMap_cons]
                  cases p with
                  | nil =>
                      convert hcenterRight using 1 <;>
                        simp [object, arrow]
                      all_goals rfl
                  | cons p r => cases r.unop
            · have hc' : c = Opposite.op Vertex.lowerLeaf :=
                opposite_eq_op_of_unop_eq hc
              subst c
              have he : e = Quiver.Hom.op Arrow.deltaLower :=
                Quiver.Hom.unop_inj ((arrow_subsingleton _ _).elim _ _)
              subst e
              rw [LinearPathCategory.pathMap_cons]
              cases p with
              | nil =>
                  convert hDeltaLower using 1 <;> simp [object, arrow]
                  all_goals rfl
              | cons p q => cases q.unop
    | rightCenter =>
        cases p with
        | nil => simpa using hid Vertex.rightCenter
        | @cons c _ p e =>
            have hc : c = Opposite.op Vertex.rightLeaf :=
              opposite_eq_op_of_unop_eq
                (arrow_from_rightCenter_target e.unop)
            subst c
            have he : e = Quiver.Hom.op Arrow.alphaRight :=
              Quiver.Hom.unop_inj ((arrow_subsingleton _ _).elim _ _)
            subst e
            rw [LinearPathCategory.pathMap_cons]
            cases p with
            | nil =>
                convert hAlphaRight using 1 <;> simp [object, arrow]
                all_goals rfl
            | cons p q => cases q.unop
    | leftLeaf =>
        cases p with
        | nil => simpa using hid Vertex.leftLeaf
        | @cons c _ p e =>
            have hc : c = Opposite.op Vertex.leftCenter :=
              opposite_eq_op_of_unop_eq
                (arrow_from_leftLeaf_target e.unop)
            subst c
            have he : e = Quiver.Hom.op Arrow.alphaLeft :=
              Quiver.Hom.unop_inj ((arrow_subsingleton _ _).elim _ _)
            subst e
            rw [LinearPathCategory.pathMap_cons]
            cases p with
            | nil =>
                convert hAlphaLeft using 1 <;> simp [object, arrow]
                all_goals rfl
            | @cons d _ p q =>
                rcases arrow_from_leftCenter_target q.unop with hd | hd
                · have hd' : d = Opposite.op Vertex.rightCenter :=
                    opposite_eq_op_of_unop_eq hd
                  subst d
                  have hq : q = Quiver.Hom.op Arrow.lambda :=
                    Quiver.Hom.unop_inj
                      ((arrow_subsingleton _ _).elim _ _)
                  subst q
                  rw [LinearPathCategory.pathMap_cons]
                  cases p with
                  | nil =>
                      convert hleftCenter using 1 <;>
                        simp [object, arrow]
                      all_goals rfl
                  | @cons z _ p r =>
                      have hz : z = Opposite.op Vertex.rightLeaf :=
                        opposite_eq_op_of_unop_eq
                          (arrow_from_rightCenter_target r.unop)
                      subst z
                      have hr : r = Quiver.Hom.op Arrow.alphaRight :=
                        Quiver.Hom.unop_inj
                          ((arrow_subsingleton _ _).elim _ _)
                      subst r
                      rw [LinearPathCategory.pathMap_cons]
                      cases p with
                      | nil =>
                          convert hthree using 1 <;>
                            simp [object, arrow]
                          all_goals rfl
                      | cons p s => cases s.unop
                · have hd' : d = Opposite.op Vertex.lowerLeaf :=
                    opposite_eq_op_of_unop_eq hd
                  subst d
                  have hq : q = Quiver.Hom.op Arrow.deltaLower :=
                    Quiver.Hom.unop_inj
                      ((arrow_subsingleton _ _).elim _ _)
                  subst q
                  rw [LinearPathCategory.pathMap_cons]
                  cases p with
                  | nil =>
                      convert hleftLower using 1 <;>
                        simp [object, arrow]
                      all_goals rfl
                  | cons p r => cases r.unop
    | upperLeaf =>
        cases p with
        | nil => simpa using hid Vertex.upperLeaf
        | @cons c _ p e =>
            have hc : c = Opposite.op Vertex.rightCenter :=
              opposite_eq_op_of_unop_eq
                (arrow_from_upperLeaf_target e.unop)
            subst c
            have he : e = Quiver.Hom.op Arrow.deltaUpper :=
              Quiver.Hom.unop_inj ((arrow_subsingleton _ _).elim _ _)
            subst e
            rw [LinearPathCategory.pathMap_cons]
            cases p with
            | nil =>
                convert hDeltaUpper using 1 <;> simp [object, arrow]
                all_goals rfl
            | @cons d _ p q =>
                have hd : d = Opposite.op Vertex.rightLeaf :=
                  opposite_eq_op_of_unop_eq
                    (arrow_from_rightCenter_target q.unop)
                subst d
                have hq : q = Quiver.Hom.op Arrow.alphaRight :=
                  Quiver.Hom.unop_inj
                    ((arrow_subsingleton _ _).elim _ _)
                subst q
                rw [LinearPathCategory.pathMap_cons]
                cases p with
                | nil =>
                    convert hupperRight using 1 <;>
                      simp [object, arrow]
                    all_goals rfl
                | cons p r => cases r.unop
    | lowerLeaf =>
        cases p with
        | nil => simpa using hid Vertex.lowerLeaf
        | cons p e => cases e.unop
    | rightLeaf =>
        cases p with
        | nil => simpa using hid Vertex.rightLeaf
        | cons p e => cases e.unop

/-- Functor-level form of the five-composite Figure-14 path-survival
criterion. -/
theorem functor_map_pathHom_ne_zero_of_five_composites
    (G : DiagramData (C := C))
    (hleftLower : G.alphaLeft ≫ G.deltaLower ≠ 0)
    (hleftCenter : G.alphaLeft ≫ G.lambda ≠ 0)
    (hcenterRight : G.lambda ≫ G.alphaRight ≠ 0)
    (hupperRight : G.deltaUpper ≫ G.alphaRight ≠ 0)
    (hthree : G.alphaLeft ≫ G.lambda ≫ G.alphaRight ≠ 0)
    {X Y : LinearSource k}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) :
    (G.functor (k := k)).map (LinearPathCategory.pathHom p) ≠ 0 := by
  unfold functor
  rw [LinearPathCategory.lift_map_pathHom]
  exact pathMap_ne_zero_of_five_composites G hleftLower hleftCenter
    hcenterRight hupperRight hthree p

end DiagramData

end Diagram

section AmbientContradiction

universe uA x

variable [Infinite k]
variable {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]
variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

/-- Exact Figure-14 contradiction boundary.  Everything on the source side,
including its infinite family, is explicit; only the ambient cleaving
retraction remains. -/
theorem not_isRepresentationFinite_of_figure14Data
    (G : DiagramData (C := S.ProjectiveCategory))
    (hG : HomBifunctorRetraction (k := k) (G.functor (k := k))) :
    ¬ LargeIndecomposable.IsRepresentationFinite k A :=
  CriticalSingularCleaving.not_isRepresentationFinite_of_homBifunctorRetraction
    (S := S) (D := G.functor (k := k)) (sourceFamily (k := k)) hG

end AmbientContradiction

end LargeIndecomposable.CriticalSingularFigure14
