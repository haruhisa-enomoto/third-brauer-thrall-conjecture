module

public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalCleavingTransfer

@[expose] public section

/-!
# The BGRS Figure 13 diagram D

Figure 13D is the mixed orientation of affine `D̃₄`: two one-dimensional
leaves enter a two-dimensional center and two one-dimensional leaves leave
it.  The explicit family uses the columns `e₀,e₁` and the rows `(1,1)` and
`(c,1)`.  Naturality forces every endomorphism to be scalar, while an
isomorphism between parameters forces the parameters to agree.

The ambient theorem leaves only the literal Hom-bifunctor retraction—the
source's assertion that the displayed diagram is cleaving—as a callback.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace LargeIndecomposable.RoiterFigure13D

open LargeIndecomposable.CriticalSingularCleaving
open LargeIndecomposable.ClosedZigzagCrossUniverse

universe u

variable {k : Type u} [Field k]

/-- The center and four leaf occurrences in Figure 13D. -/
inductive Vertex
  | center
  | leftLeaf
  | upperLeaf
  | lowerLeaf
  | rightLeaf
  deriving DecidableEq

def vertexEquiv : Vertex ≃ Fin 5 where
  toFun
    | .center => 0
    | .leftLeaf => 1
    | .upperLeaf => 2
    | .lowerLeaf => 3
    | .rightLeaf => 4
  invFun
    | ⟨0, _⟩ => .center
    | ⟨1, _⟩ => .leftLeaf
    | ⟨2, _⟩ => .upperLeaf
    | ⟨3, _⟩ => .lowerLeaf
    | ⟨4, _⟩ => .rightLeaf
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype Vertex := Fintype.ofEquiv (Fin 5) vertexEquiv.symm

/-- The four arrows of the literal Figure-13D source. -/
inductive Arrow : Vertex → Vertex → Type
  | alpha : Arrow .leftLeaf .center
  | tauUpper : Arrow .upperLeaf .center
  | tauLower : Arrow .center .lowerLeaf
  | beta : Arrow .center .rightLeaf

instance : Quiver Vertex where Hom := Arrow

/-- An arrow with its endpoints exposed. -/
abbrev TotalArrow := Σ a, Σ b, Arrow a b

def totalArrow {a b : Vertex} (e : a ⟶ b) : TotalArrow :=
  ⟨a, b, e⟩

def totalArrowEndpoints (e : TotalArrow) : Vertex × Vertex :=
  (e.1, e.2.1)

/-- Every Figure-13D arrow is determined by its ordered endpoints. -/
theorem totalArrowEndpoints_injective :
    Function.Injective totalArrowEndpoints := by
  intro e f hef
  rcases e with ⟨a, b, e⟩
  rcases f with ⟨c, d, f⟩
  cases e <;> cases f <;>
    simp only [totalArrowEndpoints, Prod.mk.injEq] at hef ⊢
  all_goals simp_all

theorem arrow_subsingleton (a b : Vertex) : Subsingleton (a ⟶ b) := by
  constructor
  intro e f
  have htotal : totalArrow e = totalArrow f :=
    totalArrowEndpoints_injective (by rfl)
  cases htotal
  rfl

theorem totalArrow_source_ne_target (e : TotalArrow) :
    e.1 ≠ e.2.1 := by
  rcases e with ⟨a, b, e⟩
  cases e <;> intro h <;> cases h

theorem opposite_arrow_source_ne_target
    {a b : Vertexᵒᵖ} (e : a ⟶ b) : a ≠ b := by
  intro hab
  apply totalArrow_source_ne_target (totalArrow e.unop)
  exact (congrArg Opposite.unop hab).symm

theorem no_arrow_from_lower (b : Vertex) :
    IsEmpty (Vertex.lowerLeaf ⟶ b) := by
  constructor
  intro e
  cases e

theorem no_arrow_from_right (b : Vertex) :
    IsEmpty (Vertex.rightLeaf ⟶ b) := by
  constructor
  intro e
  cases e

theorem no_arrow_to_left (a : Vertex) :
    IsEmpty (a ⟶ Vertex.leftLeaf) := by
  constructor
  intro e
  cases e

theorem no_arrow_to_upper (a : Vertex) :
    IsEmpty (a ⟶ Vertex.upperLeaf) := by
  constructor
  intro e
  cases e

theorem opposite_no_arrow_to_lower (a : Vertexᵒᵖ) :
    IsEmpty (a ⟶ Opposite.op Vertex.lowerLeaf) := by
  constructor
  intro e
  exact (no_arrow_from_lower a.unop).false e.unop

theorem opposite_no_arrow_to_right (a : Vertexᵒᵖ) :
    IsEmpty (a ⟶ Opposite.op Vertex.rightLeaf) := by
  constructor
  intro e
  exact (no_arrow_from_right a.unop).false e.unop

theorem opposite_no_arrow_from_left (b : Vertexᵒᵖ) :
    IsEmpty (Opposite.op Vertex.leftLeaf ⟶ b) := by
  constructor
  intro e
  exact (no_arrow_to_left b.unop).false e.unop

theorem opposite_no_arrow_from_upper (b : Vertexᵒᵖ) :
    IsEmpty (Opposite.op Vertex.upperLeaf ⟶ b) := by
  constructor
  intro e
  exact (no_arrow_to_upper b.unop).false e.unop

private theorem arrow_from_center_target
    {b : Vertex} (e : Vertex.center ⟶ b) :
    b = Vertex.lowerLeaf ∨ b = Vertex.rightLeaf := by
  cases e with
  | tauLower => exact Or.inl rfl
  | beta => exact Or.inr rfl

private theorem arrow_from_left_target
    {b : Vertex} (e : Vertex.leftLeaf ⟶ b) : b = Vertex.center := by
  cases e
  rfl

private theorem arrow_from_upper_target
    {b : Vertex} (e : Vertex.upperLeaf ⟶ b) : b = Vertex.center := by
  cases e
  rfl

private theorem opposite_eq_op_of_unop_eq
    {a : Vertexᵒᵖ} {b : Vertex} (h : a.unop = b) :
    a = Opposite.op b := by
  simpa only [Opposite.op_unop] using congrArg Opposite.op h

theorem path_length_zero_of_target_lower {a : Vertexᵒᵖ}
    (p : Quiver.Path a (Opposite.op Vertex.lowerLeaf)) : p.length = 0 := by
  cases p with
  | nil => rfl
  | cons p e => exact False.elim ((opposite_no_arrow_to_lower _).false e)

theorem path_length_zero_of_target_right {a : Vertexᵒᵖ}
    (p : Quiver.Path a (Opposite.op Vertex.rightLeaf)) : p.length = 0 := by
  cases p with
  | nil => rfl
  | cons p e => exact False.elim ((opposite_no_arrow_to_right _).false e)

theorem path_length_zero_of_source_left {b : Vertexᵒᵖ}
    (p : Quiver.Path (Opposite.op Vertex.leftLeaf) b) : p.length = 0 := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      have hsource := p.eq_of_length_zero ih
      subst_vars
      exact False.elim ((opposite_no_arrow_from_left _).false e)

theorem path_length_zero_of_source_upper {b : Vertexᵒᵖ}
    (p : Quiver.Path (Opposite.op Vertex.upperLeaf) b) : p.length = 0 := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      have hsource := p.eq_of_length_zero ih
      subst_vars
      exact False.elim ((opposite_no_arrow_from_upper _).false e)

theorem arrow_to_left_source_eq_center
    {b : Vertexᵒᵖ} (e : b ⟶ Opposite.op Vertex.leftLeaf) :
    b = Opposite.op Vertex.center := by
  induction b using Opposite.rec with
  | _ b =>
      cases e.unop
      rfl

theorem arrow_to_upper_source_eq_center
    {b : Vertexᵒᵖ} (e : b ⟶ Opposite.op Vertex.upperLeaf) :
    b = Opposite.op Vertex.center := by
  induction b using Opposite.rec with
  | _ b =>
      cases e.unop
      rfl

theorem path_length_zero_before_arrow_to_center
    {a b : Vertexᵒᵖ} (p : Quiver.Path a b)
    (e : b ⟶ Opposite.op Vertex.center) : p.length = 0 := by
  induction b using Opposite.rec with
  | _ b =>
      cases e.unop with
      | tauLower => exact path_length_zero_of_target_lower p
      | beta => exact path_length_zero_of_target_right p

theorem path_center_subsingleton (a : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a (Opposite.op Vertex.center)) := by
  constructor
  intro p q
  cases p with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e =>
          have hq0 := path_length_zero_before_arrow_to_center q e
          have hstart := q.eq_of_length_zero hq0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
  | cons p e =>
      cases q with
      | nil =>
          have hp0 := path_length_zero_before_arrow_to_center p e
          have hstart := p.eq_of_length_zero hp0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
      | cons q f =>
          have hp0 := path_length_zero_before_arrow_to_center p e
          have hq0 := path_length_zero_before_arrow_to_center q f
          have hbc := (p.eq_of_length_zero hp0).symm.trans
            (q.eq_of_length_zero hq0)
          cases hbc
          have heunop : e.unop = f.unop :=
            (arrow_subsingleton _ _).elim _ _
          have hef : e = f := Quiver.Hom.unop_inj heunop
          subst f
          have hpa := p.eq_of_length_zero hp0
          subst_vars
          rw [Quiver.Path.eq_nil_of_length_zero p hp0,
            Quiver.Path.eq_nil_of_length_zero q hq0]

theorem path_left_subsingleton (a : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a (Opposite.op Vertex.leftLeaf)) := by
  constructor
  intro p q
  cases p with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e =>
          have hq0 := path_length_zero_of_source_left q
          have hstart := q.eq_of_length_zero hq0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
  | cons p e =>
      cases q with
      | nil =>
          have hp0 := path_length_zero_of_source_left p
          have hstart := p.eq_of_length_zero hp0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
      | cons q f =>
          have he := arrow_to_left_source_eq_center e
          have hf := arrow_to_left_source_eq_center f
          subst_vars
          have hef : e = f := Quiver.Hom.unop_inj
            ((arrow_subsingleton _ _).elim e.unop f.unop)
          subst f
          congr 1
          exact (path_center_subsingleton a).elim p q

theorem path_upper_subsingleton (a : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a (Opposite.op Vertex.upperLeaf)) := by
  constructor
  intro p q
  cases p with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e =>
          have hq0 := path_length_zero_of_source_upper q
          have hstart := q.eq_of_length_zero hq0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
  | cons p e =>
      cases q with
      | nil =>
          have hp0 := path_length_zero_of_source_upper p
          have hstart := p.eq_of_length_zero hp0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
      | cons q f =>
          have he := arrow_to_upper_source_eq_center e
          have hf := arrow_to_upper_source_eq_center f
          subst_vars
          have hef : e = f := Quiver.Hom.unop_inj
            ((arrow_subsingleton _ _).elim e.unop f.unop)
          subst f
          congr 1
          exact (path_center_subsingleton a).elim p q

private theorem path_subsingleton_of_all_length_zero
    (a b : Vertexᵒᵖ) (hzero : ∀ p : Quiver.Path a b, p.length = 0) :
    Subsingleton (Quiver.Path a b) := by
  constructor
  intro p q
  have hp := p.eq_of_length_zero (hzero p)
  subst b
  rw [Quiver.Path.eq_nil_of_length_zero p (hzero p),
    Quiver.Path.eq_nil_of_length_zero q (hzero q)]

/-- The free Figure-13D path category is thin: there is at most one directed
path between every ordered pair of source occurrences. -/
theorem path_subsingleton (a b : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a b) := by
  induction b using Opposite.rec with
  | _ b =>
      cases b with
      | center => exact path_center_subsingleton a
      | leftLeaf => exact path_left_subsingleton a
      | upperLeaf => exact path_upper_subsingleton a
      | lowerLeaf =>
          exact path_subsingleton_of_all_length_zero a _
            (fun p ↦ path_length_zero_of_target_lower p)
      | rightLeaf =>
          exact path_subsingleton_of_all_length_zero a _
            (fun p ↦ path_length_zero_of_target_right p)

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
  | .center => Center (k := k)
  | .leftLeaf | .upperLeaf | .lowerLeaf | .rightLeaf => Leaf (k := k)

def basisVec (i : Fin 2) : Center (k := k) := Pi.single i 1

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

/-- Arrow realization for parameter `c`. -/
def arrowMap (c : k) {a b : Vertex} :
    (a ⟶ b) → (obj (k := k) a ⟶ obj (k := k) b)
  | .alpha => columnHom (k := k) 1 0
  | .tauUpper => columnHom (k := k) 0 1
  | .tauLower => rowHom (k := k) 1 1
  | .beta => rowHom (k := k) c 1

/-- Explicit one-parameter representation of Figure 13D. -/
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

def centerComponent {c d : k} (f : module (k := k) c ⟶ module d) :
    Center (k := k) ⟶ Center (k := k) :=
  f.app (vertexObj (k := k) .center)

def leafComponent {c d : k} (f : module (k := k) c ⟶ module d)
    (a : Vertex) : obj (k := k) a ⟶ obj (k := k) a :=
  f.app (vertexObj (k := k) a)

def coeff {c d : k} (f : module (k := k) c ⟶ module d) : k :=
  centerComponent f (basisVec (k := k) 0) 0

private theorem leaf_map_eq_mul (g : Leaf (k := k) ⟶ Leaf (k := k))
    (x : k) : g x = x * g 1 := by
  simpa using g.hom.map_smul x 1

private theorem center_basis_zero {c d : k}
    (f : module (k := k) c ⟶ module d) :
    centerComponent f (basisVec (k := k) 0) =
      coeff f • basisVec (k := k) 0 := by
  have h := f.naturality (generatorHom (k := k) Arrow.alpha)
  rw [module_map_generator, module_map_generator] at h
  have h1 := congrArg
    (fun q : Leaf (k := k) ⟶ Center (k := k) ↦ q 1) h
  have hvec : centerComponent f (basisVec (k := k) 0) =
      (leafComponent f .leftLeaf 1) • basisVec (k := k) 0 := by
    change centerComponent f (columnHom (k := k) 1 0 1) =
      columnHom (k := k) 1 0 (leafComponent f .leftLeaf 1) at h1
    rw [columnHom_one_zero, columnHom_one_zero] at h1
    simpa using h1
  have hc : leafComponent f .leftLeaf 1 = coeff f := by
    have h0 := congrArg (fun x : Center (k := k) ↦ x 0) hvec
    simpa [coeff, basisVec, Pi.single_apply] using h0.symm
  simpa [hc] using hvec

private theorem center_basis_one {c d : k}
    (f : module (k := k) c ⟶ module d) :
    centerComponent f (basisVec (k := k) 1) =
      coeff f • basisVec (k := k) 1 := by
  let q : k := leafComponent f .upperLeaf 1
  have hu := f.naturality (generatorHom (k := k) Arrow.tauUpper)
  rw [module_map_generator, module_map_generator] at hu
  have hu1 := congrArg
    (fun g : Leaf (k := k) ⟶ Center (k := k) ↦ g 1) hu
  have honeVec : centerComponent f (basisVec (k := k) 1) =
      q • basisVec (k := k) 1 := by
    change centerComponent f (columnHom (k := k) 0 1 1) =
      columnHom (k := k) 0 1 (leafComponent f .upperLeaf 1) at hu1
    rw [columnHom_zero_one, columnHom_zero_one] at hu1
    simpa [q] using hu1
  have hl := f.naturality (generatorHom (k := k) Arrow.tauLower)
  rw [module_map_generator, module_map_generator] at hl
  have hl0 := congrArg
    (fun g : Center (k := k) ⟶ Leaf (k := k) ↦
      g (basisVec (k := k) 0)) hl
  have hl1 := congrArg
    (fun g : Center (k := k) ⟶ Leaf (k := k) ↦
      g (basisVec (k := k) 1)) hl
  have hzero : leafComponent f .lowerLeaf 1 = coeff f := by
    have hz : leafComponent f .lowerLeaf 1 =
        centerComponent f (basisVec (k := k) 0) 0 +
          centerComponent f (basisVec (k := k) 0) 1 := by
      simpa [arrowMap, rowHom, leafComponent, centerComponent,
        basisVec, Pi.single_apply] using hl0
    rw [center_basis_zero] at hz
    simpa [basisVec, Pi.single_apply] using hz
  have hone : leafComponent f .lowerLeaf 1 = q := by
    have ho : leafComponent f .lowerLeaf 1 =
        centerComponent f (basisVec (k := k) 1) 0 +
          centerComponent f (basisVec (k := k) 1) 1 := by
      simpa [arrowMap, rowHom, leafComponent, centerComponent,
        basisVec, Pi.single_apply] using hl1
    rw [honeVec] at ho
    simpa [q, basisVec, Pi.single_apply] using ho
  have hq : q = coeff f := hone.symm.trans hzero
  simpa [hq] using honeVec

private theorem central_scalar {c d : k}
    (f : module (k := k) c ⟶ module d) (x : Center (k := k)) :
    centerComponent f x = coeff f • x := by
  have hx : x = x 0 • basisVec (k := k) 0 +
      x 1 • basisVec (k := k) 1 := by
    funext i
    fin_cases i <;> simp [basisVec]
  rw [hx, map_add, map_smul, map_smul, center_basis_zero,
    center_basis_one]
  module

/-- Every family morphism is scalar at the center, and that scalar
intertwines the two parameters. -/
theorem hom_central_scalar {c d : k}
    (f : module (k := k) c ⟶ module d) :
    (∀ x : Center (k := k), centerComponent f x = coeff f • x) ∧
      c * coeff f = d * coeff f := by
  have hs (x : Center (k := k)) := central_scalar f x
  have h := f.naturality (generatorHom (k := k) Arrow.beta)
  rw [module_map_generator, module_map_generator] at h
  have h0 := congrArg
    (fun g : Center (k := k) ⟶ Leaf (k := k) ↦
      g (basisVec (k := k) 0)) h
  have h1 := congrArg
    (fun g : Center (k := k) ⟶ Leaf (k := k) ↦
      g (basisVec (k := k) 1)) h
  have h0' : leafComponent f .rightLeaf c = d * coeff f := by
    have hraw : leafComponent f .rightLeaf c =
        d * centerComponent f (basisVec (k := k) 0) 0 +
          centerComponent f (basisVec (k := k) 0) 1 := by
      simpa [arrowMap, rowHom, leafComponent, centerComponent,
        basisVec, Pi.single_apply] using h0
    rw [hs] at hraw
    simpa [basisVec, Pi.single_apply] using hraw
  have h1' : leafComponent f .rightLeaf 1 = coeff f := by
    have hraw : leafComponent f .rightLeaf 1 =
        d * centerComponent f (basisVec (k := k) 1) 0 +
          centerComponent f (basisVec (k := k) 1) 1 := by
      simpa [arrowMap, rowHom, leafComponent, centerComponent,
        basisVec, Pi.single_apply] using h1
    rw [hs] at hraw
    simpa [basisVec, Pi.single_apply] using hraw
  rw [leaf_map_eq_mul, h1'] at h0'
  exact ⟨hs, h0'⟩

theorem parameter_eq_of_iso {c d : k}
    (e : module (k := k) c ≅ module d) : c = d := by
  have h := (hom_central_scalar e.hom).2
  have hcoeff : coeff e.hom ≠ 0 := by
    intro hz
    have hs := (hom_central_scalar e.hom).1 (basisVec (k := k) 0)
    rw [hz, zero_smul] at hs
    have hinv := congrArg
      (fun g : module (k := k) c ⟶ module c ↦
        g.app (vertexObj (k := k) .center)
          (basisVec (k := k) 0)) e.hom_inv_id
    change centerComponent e.inv
      (centerComponent e.hom (basisVec (k := k) 0)) =
        basisVec (k := k) 0 at hinv
    rw [hs, map_zero] at hinv
    have hcoord := congrArg (fun x : Center (k := k) ↦ x 0) hinv
    change (0 : k) = 1 at hcoord
    exact zero_ne_one hcoord
  exact mul_right_cancel₀ hcoeff h

private theorem component_scalar {c : k}
    (f : module (k := k) c ⟶ module c) (a : Vertex)
    (x : obj (k := k) a) :
    leafComponent f a x = coeff f • x := by
  cases a with
  | center => exact (hom_central_scalar f).1 x
  | leftLeaf =>
      have h := f.naturality (generatorHom (k := k) Arrow.alpha)
      simp only [module_map_generator] at h
      have h1 := congrArg
        (fun g : Leaf (k := k) ⟶ Center (k := k) ↦ g 1) h
      have hone : leafComponent f .leftLeaf 1 = coeff f := by
        have hvec : centerComponent f (basisVec (k := k) 0) =
            leafComponent f .leftLeaf 1 • basisVec (k := k) 0 := by
          change centerComponent f (columnHom (k := k) 1 0 1) =
            columnHom (k := k) 1 0 (leafComponent f .leftLeaf 1) at h1
          rw [columnHom_one_zero, columnHom_one_zero] at h1
          simpa using h1
        have hraw := congrArg (fun y : Center (k := k) ↦ y 0) hvec
        simpa [coeff, basisVec, Pi.single_apply] using hraw.symm
      rw [leaf_map_eq_mul, hone]
      exact mul_comm _ _
  | upperLeaf =>
      have h := f.naturality (generatorHom (k := k) Arrow.tauUpper)
      simp only [module_map_generator] at h
      have h1 := congrArg
        (fun g : Leaf (k := k) ⟶ Center (k := k) ↦ g 1) h
      have hone : leafComponent f .upperLeaf 1 = coeff f := by
        have hvec : centerComponent f (basisVec (k := k) 1) =
            leafComponent f .upperLeaf 1 • basisVec (k := k) 1 := by
          change centerComponent f (columnHom (k := k) 0 1 1) =
            columnHom (k := k) 0 1 (leafComponent f .upperLeaf 1) at h1
          rw [columnHom_zero_one, columnHom_zero_one] at h1
          simpa using h1
        have hraw := congrArg (fun y : Center (k := k) ↦ y 1) hvec
        have hs := (hom_central_scalar f).1 (basisVec (k := k) 1)
        rw [hs] at hraw
        simpa [basisVec, Pi.single_apply] using hraw.symm
      rw [leaf_map_eq_mul, hone]
      exact mul_comm _ _
  | lowerLeaf =>
      have h := f.naturality (generatorHom (k := k) Arrow.tauLower)
      simp only [module_map_generator] at h
      have h0 := congrArg
        (fun g : Center (k := k) ⟶ Leaf (k := k) ↦
          g (basisVec (k := k) 0)) h
      have hone : leafComponent f .lowerLeaf 1 = coeff f := by
        have hraw : leafComponent f .lowerLeaf 1 =
            centerComponent f (basisVec (k := k) 0) 0 +
              centerComponent f (basisVec (k := k) 0) 1 := by
          simpa [arrowMap, rowHom, leafComponent, centerComponent,
            basisVec, Pi.single_apply] using h0
        have hs := (hom_central_scalar f).1 (basisVec (k := k) 0)
        rw [hs] at hraw
        simpa [basisVec, Pi.single_apply] using hraw
      rw [leaf_map_eq_mul, hone]
      exact mul_comm _ _
  | rightLeaf =>
      have h := f.naturality (generatorHom (k := k) Arrow.beta)
      simp only [module_map_generator] at h
      have h1 := congrArg
        (fun g : Center (k := k) ⟶ Leaf (k := k) ↦
          g (basisVec (k := k) 1)) h
      have hone : leafComponent f .rightLeaf 1 = coeff f := by
        have hraw : leafComponent f .rightLeaf 1 =
            c * centerComponent f (basisVec (k := k) 1) 0 +
              centerComponent f (basisVec (k := k) 1) 1 := by
          simpa [arrowMap, rowHom, leafComponent, centerComponent,
            basisVec, Pi.single_apply] using h1
        have hs := (hom_central_scalar f).1 (basisVec (k := k) 1)
        rw [hs] at hraw
        simpa [basisVec, Pi.single_apply] using hraw
      rw [leaf_map_eq_mul, hone]
      exact mul_comm _ _

theorem end_eq_zero_or_id_of_idempotent (c : k)
    (f : module (k := k) c ⟶ module c) (hf : f ≫ f = f) :
    f = 0 ∨ f = 𝟙 _ := by
  have hc := congrArg coeff hf
  have hmul : coeff f * coeff f = coeff f := by
    change centerComponent (f ≫ f) (basisVec (k := k) 0) 0 = coeff f at hc
    change centerComponent f
      (centerComponent f (basisVec (k := k) 0)) 0 = coeff f at hc
    rw [(hom_central_scalar f).1, (hom_central_scalar f).1] at hc
    simpa [smul_smul, basisVec, Pi.single_apply] using hc
  rcases eq_zero_or_one_of_sq_eq_self (by simpa [pow_two] using hmul) with
    h0 | h1
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
      f.app (vertexObj (k := k) .center)
        (basisVec (k := k) 0) 0) hid
  change (1 : k) = 0 at h
  exact one_ne_zero h

theorem module_indecomposable (c : k) :
    Indecomposable (module (k := k) c) := by
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

/-- The explicit representation-infinite source-family package for Figure
13D. -/
def sourceFamily : CleavingSourceFamily (k := k) (LinearSource k) where
  anchor := vertexObj (k := k) .center
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

/-- Literal ambient data occurring in Figure 13D.  The upper and lower
occurrences may both be sent to the central object and both `tau` arrows to
one loop when the source diagram is realized. -/
structure DiagramData where
  center : C
  leftLeaf : C
  upperLeaf : C
  lowerLeaf : C
  rightLeaf : C
  alpha : leftLeaf ⟶ center
  tauUpper : upperLeaf ⟶ center
  tauLower : center ⟶ lowerLeaf
  beta : center ⟶ rightLeaf

namespace DiagramData

def object (G : DiagramData (C := C)) : Vertex → C
  | .center => G.center
  | .leftLeaf => G.leftLeaf
  | .upperLeaf => G.upperLeaf
  | .lowerLeaf => G.lowerLeaf
  | .rightLeaf => G.rightLeaf

def arrow (G : DiagramData (C := C)) {a b : Vertex} :
    (a ⟶ b) → (G.object a ⟶ G.object b)
  | .alpha => G.alpha
  | .tauUpper => G.tauUpper
  | .tauLower => G.tauLower
  | .beta => G.beta

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

/-- The only possible nonidentity paths in Figure 13D are its four arrows and
its four displayed length-two paths.  Hence nonvanishing on that finite list
implies nonvanishing on every raw path. -/
theorem pathMap_ne_zero_of_nonzero_arrows_and_composites
    (G : DiagramData (C := C))
    (hid : ∀ a : Vertex, 𝟙 (G.object a) ≠ 0)
    (ha : G.alpha ≠ 0) (hu : G.tauUpper ≠ 0)
    (hl : G.tauLower ≠ 0) (hb : G.beta ≠ 0)
    (hal : G.alpha ≫ G.tauLower ≠ 0)
    (hab : G.alpha ≫ G.beta ≠ 0)
    (hul : G.tauUpper ≫ G.tauLower ≠ 0)
    (hub : G.tauUpper ≫ G.beta ≠ 0)
    {a b : Vertexᵒᵖ} (p : Quiver.Path a b) :
    LinearPathCategory.pathMap
        (fun x ↦ G.object x.unop)
        (fun e ↦ G.arrow e.unop) p ≠ 0 := by
  induction b using Opposite.rec with
  | _ b =>
    cases b with
    | center =>
        cases p with
        | nil => simpa using hid Vertex.center
        | @cons c _ p e =>
            rcases arrow_from_center_target e.unop with hc | hc
            · have hc' : c = Opposite.op Vertex.lowerLeaf :=
                opposite_eq_op_of_unop_eq hc
              subst c
              have he : e = Quiver.Hom.op Arrow.tauLower :=
                Quiver.Hom.unop_inj ((arrow_subsingleton _ _).elim _ _)
              subst e
              rw [LinearPathCategory.pathMap_cons]
              cases p with
              | nil =>
                  convert hl using 1 <;>
                    simp [object, arrow]
                  all_goals rfl
              | cons p d => cases d.unop
            · have hc' : c = Opposite.op Vertex.rightLeaf :=
                opposite_eq_op_of_unop_eq hc
              subst c
              have he : e = Quiver.Hom.op Arrow.beta :=
                Quiver.Hom.unop_inj ((arrow_subsingleton _ _).elim _ _)
              subst e
              rw [LinearPathCategory.pathMap_cons]
              cases p with
              | nil =>
                  convert hb using 1 <;>
                    simp [object, arrow]
                  all_goals rfl
              | cons p d => cases d.unop
    | leftLeaf =>
        cases p with
        | nil => simpa using hid Vertex.leftLeaf
        | @cons c _ p e =>
            have hc : c = Opposite.op Vertex.center :=
              opposite_eq_op_of_unop_eq (arrow_from_left_target e.unop)
            subst c
            have he : e = Quiver.Hom.op Arrow.alpha :=
              Quiver.Hom.unop_inj ((arrow_subsingleton _ _).elim _ _)
            subst e
            rw [LinearPathCategory.pathMap_cons]
            cases p with
            | nil =>
                convert ha using 1 <;>
                  simp [object, arrow]
                all_goals rfl
            | @cons dmid _ p d =>
                rcases arrow_from_center_target d.unop with hd | hd
                · have hd' : dmid = Opposite.op Vertex.lowerLeaf :=
                    opposite_eq_op_of_unop_eq hd
                  subst dmid
                  have hde : d = Quiver.Hom.op Arrow.tauLower :=
                    Quiver.Hom.unop_inj ((arrow_subsingleton _ _).elim _ _)
                  subst d
                  rw [LinearPathCategory.pathMap_cons]
                  cases p with
                  | nil =>
                      convert hal using 1 <;>
                        simp [object, arrow]
                      all_goals rfl
                  | cons p c => cases c.unop
                · have hd' : dmid = Opposite.op Vertex.rightLeaf :=
                    opposite_eq_op_of_unop_eq hd
                  subst dmid
                  have hde : d = Quiver.Hom.op Arrow.beta :=
                    Quiver.Hom.unop_inj ((arrow_subsingleton _ _).elim _ _)
                  subst d
                  rw [LinearPathCategory.pathMap_cons]
                  cases p with
                  | nil =>
                      convert hab using 1 <;>
                        simp [object, arrow]
                      all_goals rfl
                  | cons p c => cases c.unop
    | upperLeaf =>
        cases p with
        | nil => simpa using hid Vertex.upperLeaf
        | @cons c _ p e =>
            have hc : c = Opposite.op Vertex.center :=
              opposite_eq_op_of_unop_eq (arrow_from_upper_target e.unop)
            subst c
            have he : e = Quiver.Hom.op Arrow.tauUpper :=
              Quiver.Hom.unop_inj ((arrow_subsingleton _ _).elim _ _)
            subst e
            rw [LinearPathCategory.pathMap_cons]
            cases p with
            | nil =>
                convert hu using 1 <;>
                  simp [object, arrow]
                all_goals rfl
            | @cons dmid _ p d =>
                rcases arrow_from_center_target d.unop with hd | hd
                · have hd' : dmid = Opposite.op Vertex.lowerLeaf :=
                    opposite_eq_op_of_unop_eq hd
                  subst dmid
                  have hde : d = Quiver.Hom.op Arrow.tauLower :=
                    Quiver.Hom.unop_inj ((arrow_subsingleton _ _).elim _ _)
                  subst d
                  rw [LinearPathCategory.pathMap_cons]
                  cases p with
                  | nil =>
                      convert hul using 1 <;>
                        simp [object, arrow]
                      all_goals rfl
                  | cons p c => cases c.unop
                · have hd' : dmid = Opposite.op Vertex.rightLeaf :=
                    opposite_eq_op_of_unop_eq hd
                  subst dmid
                  have hde : d = Quiver.Hom.op Arrow.beta :=
                    Quiver.Hom.unop_inj ((arrow_subsingleton _ _).elim _ _)
                  subst d
                  rw [LinearPathCategory.pathMap_cons]
                  cases p with
                  | nil =>
                      convert hub using 1 <;>
                        simp [object, arrow]
                      all_goals rfl
                  | cons p c => cases c.unop
    | lowerLeaf =>
        cases p with
        | nil => simpa using hid Vertex.lowerLeaf
        | cons p e => cases e.unop
    | rightLeaf =>
        cases p with
        | nil => simpa using hid Vertex.rightLeaf
        | cons p e => cases e.unop

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

/-- Nonvanishing of the four length-two Figure-13D composites already forces
nonvanishing of every path: the arrow and identity cases follow from their
nonzero factors. -/
theorem pathMap_ne_zero_of_four_composites
    (G : DiagramData (C := C))
    (hal : G.alpha ≫ G.tauLower ≠ 0)
    (hab : G.alpha ≫ G.beta ≠ 0)
    (hul : G.tauUpper ≫ G.tauLower ≠ 0)
    (hub : G.tauUpper ≫ G.beta ≠ 0)
    {a b : Vertexᵒᵖ} (p : Quiver.Path a b) :
    LinearPathCategory.pathMap
        (fun x ↦ G.object x.unop)
        (fun e ↦ G.arrow e.unop) p ≠ 0 := by
  have ha : G.alpha ≠ 0 := left_ne_zero_of_comp_ne_zero hal
  have hl : G.tauLower ≠ 0 := right_ne_zero_of_comp_ne_zero hal
  have hu : G.tauUpper ≠ 0 := left_ne_zero_of_comp_ne_zero hub
  have hb : G.beta ≠ 0 := right_ne_zero_of_comp_ne_zero hub
  have hid : ∀ a : Vertex, 𝟙 (G.object a) ≠ 0 := by
    intro a
    cases a with
    | center => exact target_id_ne_zero_of_ne_zero ha
    | leftLeaf => exact source_id_ne_zero_of_ne_zero ha
    | upperLeaf => exact source_id_ne_zero_of_ne_zero hu
    | lowerLeaf => exact target_id_ne_zero_of_ne_zero hl
    | rightLeaf => exact target_id_ne_zero_of_ne_zero hb
  exact pathMap_ne_zero_of_nonzero_arrows_and_composites
    G hid ha hu hl hb hal hab hul hub p

/-- Functor-level form of the finite Figure-13D path-survival criterion. -/
theorem functor_map_pathHom_ne_zero_of_four_composites
    (G : DiagramData (C := C))
    (hal : G.alpha ≫ G.tauLower ≠ 0)
    (hab : G.alpha ≫ G.beta ≠ 0)
    (hul : G.tauUpper ≫ G.tauLower ≠ 0)
    (hub : G.tauUpper ≫ G.beta ≠ 0)
    {X Y : LinearSource k}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) :
    (G.functor (k := k)).map (LinearPathCategory.pathHom p) ≠ 0 := by
  unfold functor
  rw [LinearPathCategory.lift_map_pathHom]
  exact pathMap_ne_zero_of_four_composites G hal hab hul hub p

end DiagramData

end Diagram

section AmbientContradiction

universe uA x

variable [Infinite k]
variable {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]
variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

/-- Exact Figure-13D contradiction boundary.  The Euclidean source family is
explicit; only the ambient cleaving retraction remains. -/
theorem not_isRepresentationFinite_of_figure13DData
    (G : DiagramData (C := S.ProjectiveCategory))
    (hG : HomBifunctorRetraction (k := k) (G.functor (k := k))) :
    ¬ LargeIndecomposable.IsRepresentationFinite k A :=
  CriticalSingularCleaving.not_isRepresentationFinite_of_homBifunctorRetraction
    (S := S) (D := G.functor (k := k)) (sourceFamily (k := k)) hG

end AmbientContradiction

end LargeIndecomposable.RoiterFigure13D
