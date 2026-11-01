module

public import LargeIndecomposable.Foundations.PathCategories.LinearPathLift
public import LargeIndecomposable.RayCategories.ClosedChains.RayInfiniteChain
public import LargeIndecomposable.RayCategories.Distributive.BGRSRayCategory
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable
namespace ClosedZigzag

universe u v w

/-- The vertices of the alternatingly oriented cycle with `n+1` sources and
`n+1` sinks. -/
inductive Vertex (n : ℕ)
  | source (i : Fin (n + 1))
  | sink (i : Fin (n + 1))
  deriving DecidableEq

def vertexEquiv (n : ℕ) :
    Vertex n ≃ Fin (n + 1) ⊕ Fin (n + 1) where
  toFun
    | .source i => Sum.inl i
    | .sink i => Sum.inr i
  invFun
    | Sum.inl i => .source i
    | Sum.inr i => .sink i
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

instance vertexFintype (n : ℕ) : Fintype (Vertex n) :=
  Fintype.ofEquiv (Fin (n + 1) ⊕ Fin (n + 1)) (vertexEquiv n).symm

/-- The arrows of the alternatingly oriented cycle, displayed linearly with
one closing arrow. -/
inductive Arrow (n : ℕ) : Vertex n → Vertex n → Type
  | rho (i : Fin (n + 1)) : Arrow n (.source i) (.sink i)
  | sigma (i : Fin n) : Arrow n (.source i.succ) (.sink i.castSucc)
  | close : Arrow n (.source 0) (.sink (Fin.last n))

instance quiver (n : ℕ) : Quiver (Vertex n) where
  Hom := Arrow n

/-- An arrow with its endpoints exposed. -/
abbrev TotalArrow (n : ℕ) := Σ a, Σ b, Arrow n a b

def totalArrow {n : ℕ} {a b : Vertex n} (e : a ⟶ b) : TotalArrow n :=
  ⟨a, b, e⟩

def totalArrowEndpoints {n : ℕ} (e : TotalArrow n) :
    Vertex n × Vertex n :=
  (e.1, e.2.1)

/-- Once the cycle has at least three sources, an arrow is determined by its
endpoints.  The lower bound excludes the degenerate one- and two-source
presentations in which constructor endpoints can coincide. -/
theorem totalArrowEndpoints_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (totalArrowEndpoints (n := n)) := by
  intro e f hef
  rcases e with ⟨a, b, e⟩
  rcases f with ⟨c, d, f⟩
  cases e <;> cases f <;>
    simp only [totalArrowEndpoints, Prod.mk.injEq, Vertex.source.injEq,
      Vertex.sink.injEq] at hef ⊢
  case rho.rho =>
    rcases hef with ⟨h, _⟩
    cases h
    rfl
  case rho.sigma | rho.close | sigma.rho | sigma.close |
      close.rho | close.sigma =>
    exfalso
    rcases hef with ⟨h₁, h₂⟩
    have h₁' := congrArg Fin.val h₁
    have h₂' := congrArg Fin.val h₂
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_zero,
      Fin.val_last] at h₁' h₂'
    omega
  case sigma.sigma i j =>
    rcases hef with ⟨h, _⟩
    have hv := congrArg Fin.val h
    have hv' : i.1 + 1 = j.1 + 1 := by
      simpa only [Fin.val_succ] using hv
    have hi : i = j := Fin.ext (Nat.add_right_cancel hv')
    cases hi
    rfl

theorem arrow_subsingleton (n : ℕ) (hn : 2 ≤ n) (a b : Vertex n) :
    Subsingleton (a ⟶ b) := by
  constructor
  intro e f
  have htotal : totalArrow e = totalArrow f :=
    totalArrowEndpoints_injective n hn (by rfl)
  cases htotal
  rfl

theorem no_arrow_from_sink (n : ℕ) (i : Fin (n + 1)) (b : Vertex n) :
    IsEmpty ((.sink i : Vertex n) ⟶ b) := by
  constructor
  intro e
  cases e

theorem no_arrow_to_source (n : ℕ) (a : Vertex n) (i : Fin (n + 1)) :
    IsEmpty (a ⟶ (.source i : Vertex n)) := by
  constructor
  intro e
  cases e

theorem opposite_no_arrow_to_sink (n : ℕ) (a : (Vertex n)ᵒᵖ)
    (i : Fin (n + 1)) : IsEmpty (a ⟶ Opposite.op (.sink i)) := by
  constructor
  intro e
  exact (no_arrow_from_sink n i a.unop).false e.unop

theorem opposite_no_arrow_from_source (n : ℕ) (i : Fin (n + 1))
    (b : (Vertex n)ᵒᵖ) : IsEmpty (Opposite.op (.source i) ⟶ b) := by
  constructor
  intro e
  exact (no_arrow_to_source n b.unop i).false e.unop

theorem opposite_path_length_zero_of_target_sink (n : ℕ)
    {a : (Vertex n)ᵒᵖ} (i : Fin (n + 1))
    (p : Quiver.Path a (Opposite.op (.sink i))) : p.length = 0 := by
  cases p with
  | nil => rfl
  | cons p e =>
      exact False.elim ((opposite_no_arrow_to_sink n _ i).false e)

theorem opposite_path_length_zero_of_source_source (n : ℕ)
    (i : Fin (n + 1)) {b : (Vertex n)ᵒᵖ}
    (p : Quiver.Path (Opposite.op (.source i)) b) : p.length = 0 := by
  induction p with
  | nil => rfl
  | @cons b c p e ih =>
      have hbc : Opposite.op (.source i) = b := p.eq_of_length_zero ih
      subst b
      exact False.elim ((opposite_no_arrow_from_source n i c).false e)

theorem totalArrow_source_ne_target (n : ℕ) (e : TotalArrow n) :
    e.1 ≠ e.2.1 := by
  rcases e with ⟨a, b, e⟩
  cases e <;> intro h <;> cases h

theorem opposite_arrow_source_ne_target (n : ℕ)
    {a b : (Vertex n)ᵒᵖ} (e : a ⟶ b) : a ≠ b := by
  intro hab
  apply totalArrow_source_ne_target n (totalArrow e.unop)
  exact (congrArg Opposite.unop hab).symm

theorem opposite_path_length_zero_before_totalArrow (n : ℕ)
    {a : (Vertex n)ᵒᵖ} (e : TotalArrow n)
    (p : Quiver.Path a (Opposite.op e.2.1)) : p.length = 0 := by
  rcases e with ⟨u, v, e⟩
  cases e with
  | rho i => exact opposite_path_length_zero_of_target_sink n i p
  | sigma i => exact opposite_path_length_zero_of_target_sink n i.castSucc p
  | close => exact opposite_path_length_zero_of_target_sink n (Fin.last n) p

theorem opposite_path_length_zero_before_arrow (n : ℕ)
    {a b c : (Vertex n)ᵒᵖ} (p : Quiver.Path a b) (e : b ⟶ c) :
    p.length = 0 := by
  induction b using Opposite.rec with
  | _ b =>
      exact opposite_path_length_zero_before_totalArrow n
        (totalArrow e.unop) p

/-- The opposite alternating cycle has at most one path between any ordered
pair of vertices. -/
theorem opposite_path_subsingleton (n : ℕ) (hn : 2 ≤ n)
    (a b : (Vertex n)ᵒᵖ) : Subsingleton (Quiver.Path a b) := by
  constructor
  intro p q
  cases p with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e =>
          have hq0 := opposite_path_length_zero_before_arrow n q e
          have hstart := q.eq_of_length_zero hq0
          exact False.elim (opposite_arrow_source_ne_target n e hstart.symm)
  | cons p e =>
      cases q with
      | nil =>
          have hp0 := opposite_path_length_zero_before_arrow n p e
          have hstart := p.eq_of_length_zero hp0
          exact False.elim (opposite_arrow_source_ne_target n e hstart.symm)
      | cons q f =>
          have hp0 := opposite_path_length_zero_before_arrow n p e
          have hq0 := opposite_path_length_zero_before_arrow n q f
          have hcd := (p.eq_of_length_zero hp0).symm.trans
            (q.eq_of_length_zero hq0)
          cases hcd
          have heunop : e.unop = f.unop :=
            (arrow_subsingleton n hn _ _).elim _ _
          have hef : e = f := Quiver.Hom.unop_inj heunop
          subst f
          have hac := p.eq_of_length_zero hp0
          subst_vars
          rw [Quiver.Path.eq_nil_of_length_zero p hp0,
            Quiver.Path.eq_nil_of_length_zero q hq0]

variable {k : Type u} [Field k]

/-- All cycle arrows have weight one except the closing arrow, whose weight
is the parameter. -/
def arrowScalar {n : ℕ} (a : Vertex n) (b : Vertex n) (c : k)
    (e : a ⟶ b) : k :=
  match e with
  | .rho _ => 1
  | .sigma _ => 1
  | .close => c

/-- Multiplication by a scalar as a morphism of one-dimensional modules. -/
def scalarHom (c : k) : ModuleCat.of k k ⟶ ModuleCat.of k k :=
  ModuleCat.ofHom
    { toFun := fun x ↦ c * x
      map_add' := fun x y ↦ mul_add c x y
      map_smul' := fun r x ↦ by simp [mul_left_comm] }

@[simp]
theorem scalarHom_apply (c x : k) : scalarHom c x = c * x :=
  rfl

/-- The thin one-parameter representation of the closed zigzag. -/
abbrev module (n : ℕ) (c : k) :
    LinearPathCategory.QuiverRep k (Vertex n) :=
  Paths.lift
    { obj := fun _ ↦ ModuleCat.of k k
      map := fun {a b} e ↦ scalarHom (arrowScalar a b c e) }

@[simp]
theorem module_map_toPath {n : ℕ} (c : k)
    {a b : Vertex n} (e : a ⟶ b) :
    (module n c).map e.toPath = scalarHom (arrowScalar a b c e) :=
  Paths.lift_toPath _ e

/-- The scalar of a morphism between two thin cycle representations at one
vertex. -/
def componentHom {n : ℕ} {c d : k} (f : module n c ⟶ module n d)
    (a : Vertex n) : ModuleCat.of k k ⟶ ModuleCat.of k k :=
  f.app a

/-- The scalar of a morphism between two thin cycle representations at one
vertex. -/
def homCoeff {n : ℕ} {c d : k} (f : module n c ⟶ module n d)
    (a : Vertex n) : k :=
  componentHom f a 1

theorem hom_app_eq_mul_coeff {n : ℕ} {c d : k}
    (f : module n c ⟶ module n d) (a : Vertex n) (x : k) :
    componentHom f a x = x * homCoeff f a := by
  change componentHom f a x = x * componentHom f a 1
  simpa using (componentHom f a).hom.map_smul x 1

/-- Naturality across a cycle arrow, written as the scalar equation at its
two endpoints. -/
theorem homCoeff_naturality {n : ℕ} {c d : k}
    (f : module n c ⟶ module n d)
    {a b : Vertex n} (e : a ⟶ b) :
    arrowScalar a b c e * homCoeff f b =
      homCoeff f a * arrowScalar a b d e := by
  have h := f.naturality e.toPath
  change scalarHom (arrowScalar a b c e) ≫ componentHom f b =
    componentHom f a ≫ scalarHom (arrowScalar a b d e) at h
  have h := congrArg (fun q : ModuleCat.of k k ⟶ ModuleCat.of k k ↦ q 1) h
  change componentHom f b (arrowScalar a b c e * 1) =
    arrowScalar a b d e * componentHom f a 1 at h
  rw [hom_app_eq_mul_coeff] at h
  simpa [homCoeff, mul_comm] using h

theorem homCoeff_source_eq_sink {n : ℕ} {c d : k}
    (f : module n c ⟶ module n d) (i : Fin (n + 1)) :
    homCoeff f (.source i) = homCoeff f (.sink i) := by
  simpa [arrowScalar] using (homCoeff_naturality f (Arrow.rho i)).symm

theorem homCoeff_nextSource_eq_sink {n : ℕ} {c d : k}
    (f : module n c ⟶ module n d) (i : Fin n) :
    homCoeff f (.source i.succ) = homCoeff f (.sink i.castSucc) := by
  simpa [arrowScalar] using (homCoeff_naturality f (Arrow.sigma i)).symm

theorem homCoeff_close {n : ℕ} {c d : k}
    (f : module n c ⟶ module n d) :
    c * homCoeff f (.sink (Fin.last n)) =
      homCoeff f (.source 0) * d := by
  simpa [arrowScalar] using homCoeff_naturality f (Arrow.close (n := n))

theorem homCoeff_source_eq_source_zero {n : ℕ} {c d : k}
    (f : module n c ⟶ module n d) (i : Fin (n + 1)) :
    homCoeff f (.source i) = homCoeff f (.source 0) := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
      calc
        homCoeff f (.source i.succ) =
            homCoeff f (.sink i.castSucc) :=
          homCoeff_nextSource_eq_sink f i
        _ = homCoeff f (.source i.castSucc) :=
          (homCoeff_source_eq_sink f i.castSucc).symm
        _ = homCoeff f (.source 0) := ih

theorem homCoeff_lastSink_eq_source_zero {n : ℕ} {c d : k}
    (f : module n c ⟶ module n d) :
    homCoeff f (.sink (Fin.last n)) = homCoeff f (.source 0) := by
  calc
    homCoeff f (.sink (Fin.last n)) =
        homCoeff f (.source (Fin.last n)) :=
      (homCoeff_source_eq_sink f (Fin.last n)).symm
    _ = homCoeff f (.source 0) :=
      homCoeff_source_eq_source_zero f (Fin.last n)

theorem homCoeff_ne_zero_of_iso {n : ℕ} {c d : k}
    (e : module n c ≅ module n d) (a : Vertex n) :
    homCoeff e.hom a ≠ 0 := by
  have h := e.hom_inv_id_app a
  change componentHom e.hom a ≫ componentHom e.inv a =
    𝟙 (ModuleCat.of k k) at h
  have h := congrArg
    (fun q : ModuleCat.of k k ⟶ ModuleCat.of k k ↦ q 1) h
  change componentHom e.inv a (componentHom e.hom a 1) = 1 at h
  rw [hom_app_eq_mul_coeff] at h
  change homCoeff e.hom a * homCoeff e.inv a = 1 at h
  intro hzero
  rw [hzero, zero_mul] at h
  exact zero_ne_one h

/-- The closing-arrow parameter is a complete isomorphism invariant of the
thin closed-zigzag family. -/
theorem parameter_eq_of_iso {n : ℕ} {c d : k}
    (e : module n c ≅ module n d) : c = d := by
  have h := homCoeff_close e.hom
  rw [homCoeff_lastSink_eq_source_zero] at h
  apply mul_right_cancel₀ (homCoeff_ne_zero_of_iso e (.source 0))
  simpa [mul_comm] using h

instance module_obj_finite (n : ℕ) (c : k) (a : Vertex n) :
    Module.Finite k ((module n c).obj a) := by
  change Module.Finite k k
  infer_instance

/-- Every member of the family has the same finite dimension vector, namely
one at every cycle vertex. -/
theorem module_obj_finrank (n : ℕ) (c : k) (a : Vertex n) :
    Module.finrank k ((module n c).obj a) = 1 := by
  change Module.finrank k k = 1
  simp

/-- The total dimension of a thin cycle representation is finite and is
twice the number of distinct closed-chain states. -/
theorem module_total_finrank (n : ℕ) (c : k) :
  ∑ a : Vertex n, Module.finrank k ((module n c).obj a) =
      2 * (n + 1) := by
  simp only [module_obj_finrank, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  rw [Fintype.card_congr (vertexEquiv n)]
  simp
  omega

theorem homCoeff_eq_source_zero {n : ℕ} {c d : k}
    (f : module n c ⟶ module n d) (a : Vertex n) :
    homCoeff f a = homCoeff f (.source 0) := by
  cases a with
  | source i => exact homCoeff_source_eq_source_zero f i
  | sink i =>
      calc
        homCoeff f (.sink i) = homCoeff f (.source i) :=
          (homCoeff_source_eq_sink f i).symm
        _ = homCoeff f (.source 0) :=
          homCoeff_source_eq_source_zero f i

/-- A morphism between thin cycle representations is determined by its
scalar at one vertex. -/
theorem hom_ext {n : ℕ} {c d : k}
    {f g : module n c ⟶ module n d}
    (h : homCoeff f (.source 0) = homCoeff g (.source 0)) : f = g := by
  apply NatTrans.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change componentHom f a x = componentHom g a x
  rw [hom_app_eq_mul_coeff, hom_app_eq_mul_coeff,
    homCoeff_eq_source_zero f a, homCoeff_eq_source_zero g a, h]

@[simp]
theorem homCoeff_zero {n : ℕ} {c d : k} (a : Vertex n) :
    homCoeff (0 : module n c ⟶ module n d) a = 0 := by
  rfl

@[simp]
theorem homCoeff_id {n : ℕ} {c : k} (a : Vertex n) :
    homCoeff (𝟙 (module n c)) a = 1 := by
  rfl

@[simp]
theorem homCoeff_comp {n : ℕ} {c d e : k}
    (f : module n c ⟶ module n d) (g : module n d ⟶ module n e)
    (a : Vertex n) :
    homCoeff (f ≫ g) a = homCoeff f a * homCoeff g a := by
  change componentHom g a (componentHom f a 1) = _
  rw [hom_app_eq_mul_coeff]
  rfl

/-- The endomorphism ring of a thin closed-zigzag representation has no
nontrivial idempotents. -/
theorem end_eq_zero_or_id_of_idempotent {n : ℕ} {c : k}
    (p : module n c ⟶ module n c) (hp : p ≫ p = p) :
    p = 0 ∨ p = 𝟙 (module n c) := by
  have hcoeff := congrArg (fun q : module n c ⟶ module n c ↦
    homCoeff q (.source 0)) hp
  rw [homCoeff_comp] at hcoeff
  have hsq : homCoeff p (.source 0) ^ 2 = homCoeff p (.source 0) := by
    simpa [pow_two] using hcoeff
  rcases eq_zero_or_one_of_sq_eq_self hsq with hzero | hone
  · left
    apply hom_ext
    simpa using hzero
  · right
    apply hom_ext
    simpa using hone

theorem module_not_isZero (n : ℕ) (c : k) :
    ¬ IsZero (module n c) := by
  intro hzero
  have hid : (𝟙 (module n c) : module n c ⟶ module n c) = 0 :=
    (IsZero.iff_id_eq_zero _).1 hzero
  have h := congrArg
    (fun q : module n c ⟶ module n c ↦ homCoeff q (.source 0)) hid
  simp at h

/-- Every thin closed-zigzag representation is indecomposable. -/
theorem module_indecomposable (n : ℕ) (c : k) :
    Indecomposable (module n c) := by
  refine ⟨module_not_isZero n c, ?_⟩
  intro Y Z e
  let p : module n c ⟶ module n c :=
    e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv
  have hp : p ≫ p = p := by
    simp [p, Category.assoc]
  rcases end_eq_zero_or_id_of_idempotent p hp with hzero | hone
  · left
    rw [IsZero.iff_id_eq_zero]
    have hproj := congrArg
      (fun q : module n c ⟶ module n c ↦ e.inv ≫ q ≫ e.hom) hzero
    have hproj : biprod.fst ≫ biprod.inl =
        (0 : (Y ⊞ Z) ⟶ (Y ⊞ Z)) := by
      simpa [p, Category.assoc] using hproj
    have h := congrArg
      (fun q : (Y ⊞ Z) ⟶ (Y ⊞ Z) ↦
        biprod.inl ≫ q ≫ biprod.fst) hproj
    simpa only [Category.assoc, Limits.biprod.inl_fst_assoc,
      Limits.biprod.inl_fst, Category.comp_id, comp_zero, zero_comp] using h
  · right
    rw [IsZero.iff_id_eq_zero]
    have hproj := congrArg
      (fun q : module n c ⟶ module n c ↦ e.inv ≫ q ≫ e.hom) hone
    have hproj : biprod.fst ≫ biprod.inl = 𝟙 (Y ⊞ Z) := by
      simpa [p, Category.assoc] using hproj
    have h := congrArg
      (fun q : (Y ⊞ Z) ⟶ (Y ⊞ Z) ↦
        biprod.inr ≫ q ≫ biprod.snd) hproj
    simpa only [Category.assoc, Limits.biprod.inr_fst_assoc,
      zero_comp, Limits.biprod.inr_snd, Category.id_comp,
      Category.comp_id] using h.symm

section InfiniteFamily

variable [Infinite k]

/-- A countably infinite subfamily obtained by choosing distinct field
parameters. -/
def family (n : ℕ) (i : ℕ) :
    LinearPathCategory.QuiverRep k (Vertex n) :=
  module n (Infinite.natEmbedding k i)

theorem family_obj_finrank (n i : ℕ) (a : Vertex n) :
    Module.finrank k ((family (k := k) n i).obj a) = 1 :=
  module_obj_finrank n (Infinite.natEmbedding k i) a

theorem family_indecomposable (n i : ℕ) :
    Indecomposable (family (k := k) n i) :=
  module_indecomposable n (Infinite.natEmbedding k i)

/-- Distinct natural-number indices give nonisomorphic members of the thin
closed-zigzag family. -/
theorem family_eq_of_iso {n i j : ℕ}
    (e : family (k := k) n i ≅ family (k := k) n j) : i = j := by
  apply (Infinite.natEmbedding k).injective
  exact parameter_eq_of_iso e

end InfiniteFamily

section ClosedChainRealization

variable {C : Type v} [Category.{w} C] [Preadditive C]
variable [HasWellDefinedBGRSRayProduct C]

/-- The `i`th distinct state of a closed chain: the repeated final state is
omitted. -/
def chainIndex (t : RayClosedChain (C := BGRSRayCategory C))
    (i : Fin ((t.length - 1) + 1)) : Fin t.length :=
  ⟨i.1, by
    have := t.length_ge_three
    omega⟩

/-- The original primitive-projective object represented by a vertex of the
closed zigzag. -/
def chainVertexObj (t : RayClosedChain (C := BGRSRayCategory C)) :
    Vertex (t.length - 1) → C
  | .source i => (t.chain.x (chainIndex t i).castSucc).as
  | .sink i => (t.chain.z (chainIndex t i).castSucc).as

/-- A chosen original-category representative of a `rho` ray. -/
def chainRhoRepresentative
    (t : RayClosedChain (C := BGRSRayCategory C))
    (i : Fin ((t.length - 1) + 1)) :
    chainVertexObj t (.source i) ⟶ chainVertexObj t (.sink i) :=
  (t.chain.rho (chainIndex t i).castSucc).1.out

/-- The non-closing `sigma` index in the original hook chain. -/
def chainSigmaIndex (t : RayClosedChain (C := BGRSRayCategory C))
    (i : Fin (t.length - 1)) : Fin t.length :=
  ⟨i.1, by
    have hi := i.2
    have := t.length_ge_three
    omega⟩

/-- A chosen original-category representative of a non-closing `sigma` ray. -/
def chainSigmaRepresentative
    (t : RayClosedChain (C := BGRSRayCategory C))
    (i : Fin (t.length - 1)) :
    chainVertexObj t (.source i.succ) ⟶
      chainVertexObj t (.sink i.castSucc) := by
  let j : Fin t.length := chainSigmaIndex t i
  exact Quiver.homOfEq (t.chain.sigma j).1.out
    (congrArg (fun q ↦ (t.chain.x q).as) (by
      apply Fin.ext
      rfl))
    (congrArg (fun q ↦ (t.chain.z q).as) (by
      apply Fin.ext
      rfl))

/-- Closing the ray state identifies the first and final source objects in the
original category. -/
theorem chain_first_source_eq_last_source
    (t : RayClosedChain (C := BGRSRayCategory C)) :
    (t.chain.x 0).as = (t.chain.x (Fin.last t.length)).as := by
  have h := congrArg
    (fun q : NonzeroCategoryMorphism (BGRSRayCategory C) ↦ q.source)
    t.first_eq_last
  exact congrArg BGRSRayCategory.as h

/-- A chosen representative of the final `sigma`, transported across the
closed-chain endpoint equality to become the closing zigzag arrow. -/
def chainCloseRepresentative
    (t : RayClosedChain (C := BGRSRayCategory C)) :
    chainVertexObj t (.source 0) ⟶
      chainVertexObj t (.sink (Fin.last (t.length - 1))) := by
  let j : Fin t.length := chainIndex t (Fin.last (t.length - 1))
  exact Quiver.homOfEq (t.chain.sigma j).1.out
    (calc
      (t.chain.x j.succ).as =
          (t.chain.x (Fin.last t.length)).as := by
        apply congrArg (fun q ↦ (t.chain.x q).as)
        apply Fin.ext
        dsimp [j, chainIndex]
        have := t.length_ge_three
        omega
      _ = (t.chain.x 0).as :=
        (chain_first_source_eq_last_source t).symm
      _ = (t.chain.x (chainIndex t 0).castSucc).as := by
        apply congrArg (fun q ↦ (t.chain.x q).as)
        apply Fin.ext
        rfl)
    (by rfl)

/-- The generator-level realization used for the BGRS functor `D`: every ray
is replaced by a chosen original-category representative, and the final
`sigma` is transported to the first source. -/
def chainRepresentativePrefunctor
    (t : RayClosedChain (C := BGRSRayCategory C)) :
    Vertex (t.length - 1) ⥤q C where
  obj := chainVertexObj t
  map
    | .rho i => chainRhoRepresentative t i
    | .sigma i => chainSigmaRepresentative t i
    | .close => chainCloseRepresentative t

omit [HasWellDefinedBGRSRayProduct C] in
private theorem unitRayOut_ne_zero {X Y : C}
    (r : UnitRayOrbit X Y) (hr : r ≠ 0) : r.out ≠ 0 := by
  rw [← unitRay_ne_zero_iff]
  simpa only [unitRay_out] using hr

omit [HasWellDefinedBGRSRayProduct C] in
private theorem homOfEq_ne_zero
    {X Y X' Y' : C} (f : X ⟶ Y) (hf : f ≠ 0)
    (hX : X = X') (hY : Y = Y') :
    Quiver.homOfEq f hX hY ≠ 0 := by
  subst hX
  subst hY
  exact hf

/-- All generators chosen from a closed ray chain remain nonzero after the
endpoint transports. -/
theorem chainRepresentativePrefunctor_map_ne_zero
    (t : RayClosedChain (C := BGRSRayCategory C))
    {a b : Vertex (t.length - 1)} (e : a ⟶ b) :
    (chainRepresentativePrefunctor t).map e ≠ 0 := by
  cases e with
  | rho i =>
      exact unitRayOut_ne_zero _
        (t.chain.rho (chainIndex t i).castSucc).2
  | sigma i =>
      change chainSigmaRepresentative t i ≠ 0
      unfold chainSigmaRepresentative
      apply homOfEq_ne_zero
      exact unitRayOut_ne_zero _ (t.chain.sigma (chainSigmaIndex t i)).2
  | close =>
      change chainCloseRepresentative t ≠ 0
      unfold chainCloseRepresentative
      apply homOfEq_ne_zero
      exact unitRayOut_ne_zero _
        (t.chain.sigma
          (chainIndex t (Fin.last (t.length - 1)))).2

/-- Every object occurring in the closed zigzag has nonzero identity.  This
is forced already by the nonzero `rho` incident with that vertex. -/
theorem chainVertexObj_id_ne_zero
    (t : RayClosedChain (C := BGRSRayCategory C))
    (a : Vertex (t.length - 1)) :
    𝟙 (chainVertexObj t a) ≠ 0 := by
  cases a with
  | source i =>
      change 𝟙 ((chainRepresentativePrefunctor t).obj (.source i)) ≠ 0
      intro hid
      have hf := chainRepresentativePrefunctor_map_ne_zero t (.rho i)
      apply hf
      calc
        (chainRepresentativePrefunctor t).map (.rho i) =
            𝟙 ((chainRepresentativePrefunctor t).obj (.source i)) ≫
              (chainRepresentativePrefunctor t).map (.rho i) := by simp
        _ = 0 := by rw [hid, zero_comp]
  | sink i =>
      change 𝟙 ((chainRepresentativePrefunctor t).obj (.sink i)) ≠ 0
      intro hid
      have hf := chainRepresentativePrefunctor_map_ne_zero t (.rho i)
      apply hf
      calc
        (chainRepresentativePrefunctor t).map (.rho i) =
            (chainRepresentativePrefunctor t).map (.rho i) ≫
              𝟙 ((chainRepresentativePrefunctor t).obj (.sink i)) := by simp
        _ = 0 := by rw [hid, comp_zero]

/-- The ordinary free-path realization of the chosen closed-chain
representatives.  Linearization and cleavage are separate subsequent steps. -/
def chainRepresentativePathFunctor
    (t : RayClosedChain (C := BGRSRayCategory C)) :
    Paths (Vertex (t.length - 1)) ⥤ C :=
  Paths.lift (chainRepresentativePrefunctor t)

theorem chainRepresentativePathFunctor_map_toPath_ne_zero
    (t : RayClosedChain (C := BGRSRayCategory C))
    {a b : Vertex (t.length - 1)}
    (e : Arrow (t.length - 1) a b) :
    (chainRepresentativePathFunctor t).map
      (Quiver.Hom.toPath (V := Vertex (t.length - 1)) e) ≠ 0 := by
  unfold chainRepresentativePathFunctor
  rw [Paths.lift_toPath]
  exact chainRepresentativePrefunctor_map_ne_zero t e

section LinearRealization

variable [Linear k C]

/-- The BGRS generator functor `D`, as a genuinely `k`-linear functor from
the free linear category.  The opposite quiver compensates for the reversed
path convention in `LinearPathCategory`. -/
def chainRepresentativeLinearFunctor
    (t : RayClosedChain (C := BGRSRayCategory C)) :
    LinearPathCategory.Category k (Vertex (t.length - 1))ᵒᵖ ⥤ C :=
  LinearPathCategory.lift
    (fun a ↦ chainVertexObj t a.unop)
    (fun {_ _} e ↦ (chainRepresentativePrefunctor t).map e.unop)

instance chainRepresentativeLinearFunctor_additive
    (t : RayClosedChain (C := BGRSRayCategory C)) :
    (chainRepresentativeLinearFunctor (k := k) t).Additive :=
  by
    unfold chainRepresentativeLinearFunctor
    infer_instance

instance chainRepresentativeLinearFunctor_linear
    (t : RayClosedChain (C := BGRSRayCategory C)) :
    (chainRepresentativeLinearFunctor (k := k) t).Linear k :=
  by
    unfold chainRepresentativeLinearFunctor
    infer_instance

/-- On a one-arrow path-basis morphism, the linear functor is exactly the
chosen representative of the corresponding ray-chain generator. -/
theorem chainRepresentativeLinearFunctor_map_generator
    (t : RayClosedChain (C := BGRSRayCategory C))
    {a b : Vertex (t.length - 1)}
    (e : Arrow (t.length - 1) a b) :
    (chainRepresentativeLinearFunctor (k := k) t).map
        (LinearPathCategory.pathHom
          (x := LinearPathCategory.obj k
            (Vertex (t.length - 1))ᵒᵖ (Opposite.op a))
          (y := LinearPathCategory.obj k
            (Vertex (t.length - 1))ᵒᵖ (Opposite.op b))
          (Quiver.Hom.toPath (Quiver.homOfEq (Quiver.Hom.op e)
            (by rfl : Opposite.op b = LinearPathCategory.vertex
              (LinearPathCategory.obj k
                (Vertex (t.length - 1))ᵒᵖ (Opposite.op b)))
            (by rfl : Opposite.op a = LinearPathCategory.vertex
              (LinearPathCategory.obj k
                (Vertex (t.length - 1))ᵒᵖ (Opposite.op a)))))) =
      (chainRepresentativePrefunctor t).map e := by
  unfold chainRepresentativeLinearFunctor
  rw [LinearPathCategory.lift_map_pathHom]
  simp only [Quiver.Hom.toPath, LinearPathCategory.pathMap,
    Category.comp_id]
  cases e <;> rfl

theorem chainRepresentativeLinearFunctor_map_generator_ne_zero
    (t : RayClosedChain (C := BGRSRayCategory C))
    {a b : Vertex (t.length - 1)}
    (e : Arrow (t.length - 1) a b) :
    (chainRepresentativeLinearFunctor (k := k) t).map
        (LinearPathCategory.pathHom
          (x := LinearPathCategory.obj k
            (Vertex (t.length - 1))ᵒᵖ (Opposite.op a))
          (y := LinearPathCategory.obj k
            (Vertex (t.length - 1))ᵒᵖ (Opposite.op b))
          (Quiver.Hom.toPath (Quiver.homOfEq (Quiver.Hom.op e)
            (by rfl : Opposite.op b = LinearPathCategory.vertex
              (LinearPathCategory.obj k
                (Vertex (t.length - 1))ᵒᵖ (Opposite.op b)))
            (by rfl : Opposite.op a = LinearPathCategory.vertex
              (LinearPathCategory.obj k
                (Vertex (t.length - 1))ᵒᵖ (Opposite.op a)))))) ≠ 0 := by
  rw [chainRepresentativeLinearFunctor_map_generator]
  exact chainRepresentativePrefunctor_map_ne_zero t e

/-- Every path-basis vector of the alternating free linear category has
nonzero image.  There are only trivial paths and single arrows. -/
theorem chainRepresentativeLinearFunctor_map_pathHom_ne_zero
    (t : RayClosedChain (C := BGRSRayCategory C))
    {x y : LinearPathCategory.Category k
      (Vertex (t.length - 1))ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex y)
      (LinearPathCategory.vertex x)) :
    (chainRepresentativeLinearFunctor (k := k) t).map
        (LinearPathCategory.pathHom p) ≠ 0 := by
  unfold chainRepresentativeLinearFunctor
  rw [LinearPathCategory.lift_map_pathHom]
  cases p with
  | nil =>
      simp only [LinearPathCategory.pathMap_nil]
      exact chainVertexObj_id_ne_zero t
        (LinearPathCategory.vertex x).unop
  | cons p e =>
      have hp0 := opposite_path_length_zero_before_arrow
        (t.length - 1) p e
      have hstart := p.eq_of_length_zero hp0
      subst_vars
      rw [Quiver.Path.eq_nil_of_length_zero p hp0]
      simp only [LinearPathCategory.pathMap_cons,
        LinearPathCategory.pathMap_nil, Category.comp_id]
      exact chainRepresentativePrefunctor_map_ne_zero t e.unop

/-- The BGRS closed-chain generator functor is injective on every Hom space.
This closes the injectivity requirement in BGRS 3.4(a); the remaining
cleaving work is entirely the construction of functorial supplements. -/
theorem chainRepresentativeLinearFunctor_map_injective
    (t : RayClosedChain (C := BGRSRayCategory C))
    (x y : LinearPathCategory.Category k
      (Vertex (t.length - 1))ᵒᵖ) :
    Function.Injective
      ((chainRepresentativeLinearFunctor (k := k) t).mapLinearMap k
        (X := x) (Y := y)) := by
  have hn : 2 ≤ t.length - 1 := by
    have := t.length_ge_three
    omega
  letI : Subsingleton
      (Quiver.Path (LinearPathCategory.vertex y)
        (LinearPathCategory.vertex x)) :=
    opposite_path_subsingleton (t.length - 1) hn _ _
  apply LinearMap.injective_of_linearIndependent
    (LinearPathCategory.homPathBasis x y).span_eq
  rw [linearIndependent_subsingleton_index_iff]
  intro p
  change (chainRepresentativeLinearFunctor (k := k) t).map
      (LinearPathCategory.homPathBasis x y p) ≠ 0
  rw [LinearPathCategory.homPathBasis_apply]
  exact chainRepresentativeLinearFunctor_map_pathHom_ne_zero t p

/-- Faithfulness packaged in the ordinary categorical interface. -/
theorem chainRepresentativeLinearFunctorFaithful
    (t : RayClosedChain (C := BGRSRayCategory C)) :
    (chainRepresentativeLinearFunctor (k := k) t).Faithful where
  map_injective := by
    intro X Y
    change Function.Injective
      ((chainRepresentativeLinearFunctor (k := k) t).mapLinearMap k
        (X := X) (Y := Y))
    exact chainRepresentativeLinearFunctor_map_injective t X Y

end LinearRealization

end ClosedChainRealization

end ClosedZigzag
end LargeIndecomposable
