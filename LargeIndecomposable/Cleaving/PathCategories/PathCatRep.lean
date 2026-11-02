module

public import LargeIndecomposable.Cleaving.PathCategories.PathCat
public import LargeIndecomposable.RayCategories.Linearization.LinMul
public import LargeIndecomposable.Cleaving.Functors.Cleaving
public import LargeIndecomposable.Quivers.RepresentationType.Basic
public import LargeIndecomposable.Modules.KrullSchmidt.IndecomposableFullyFaithful
public import LargeIndecomposable.Quivers.RepresentationType.ExtendedDynkin

/-!
# Quiver representations as modules over the linearization of a path category

For a finite acyclic quiver `Q`, a representation `N` of `Q` gives a module
`⊕ᵥ N(v)` over `k(PathCat Q)` on which a path `p : a → b` acts by `N(p)` from
the `a`-component to the `b`-component (`RayCat.RepTot`). This is a fully
faithful functor (`RayCat.repFunctor`), so representation-finiteness of
`k(PathCat Q)` gives finite representation type of `Q` in the sense of LargeIndecomposable
(`RayCat.isFiniteRepType_of_isRepresentationFinite`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayQuiver

universe u

namespace RayCat

variable (k : Type u) [Field k] {Q : Type} [Quiver.{0} Q] [Fintype Q] [DecidableEq Q]
  [∀ a b : Q, Finite (a ⟶ b)] [hQ : Fact (LargeIndecomposable.Foundations.Quiver.IsAcyclic Q)]

instance : IsRayCategory (PathCat Q) := PathCat.isRayCategory hQ.out

variable {k}

/-- A vertex as an object of `Paths Q`. -/
abbrev pv (a : Q) : Paths Q := a

instance : DecidableEq (Paths Q) := inferInstanceAs (DecidableEq Q)

/-- The total space of a representation. -/
@[ext]
structure RepTot (N : LargeIndecomposable.Foundations.QuiverRep.{u, 0, 0, u} k Q) where
  /-- The components. -/
  val : ∀ v : Paths Q, N.obj v

namespace RepTot

variable {N : LargeIndecomposable.Foundations.QuiverRep.{u, 0, 0, u} k Q}

instance : Zero (RepTot N) := ⟨⟨fun _ ↦ 0⟩⟩
instance : Add (RepTot N) := ⟨fun φ ψ ↦ ⟨fun v ↦ φ.val v + ψ.val v⟩⟩
instance : Neg (RepTot N) := ⟨fun φ ↦ ⟨fun v ↦ -φ.val v⟩⟩
instance : Sub (RepTot N) := ⟨fun φ ψ ↦ ⟨fun v ↦ φ.val v - ψ.val v⟩⟩
instance : SMul ℕ (RepTot N) := ⟨fun n φ ↦ ⟨fun v ↦ n • φ.val v⟩⟩
instance : SMul ℤ (RepTot N) := ⟨fun n φ ↦ ⟨fun v ↦ n • φ.val v⟩⟩
instance : SMul k (RepTot N) := ⟨fun a φ ↦ ⟨fun v ↦ a • φ.val v⟩⟩

@[simp] lemma zero_val (v : Paths Q) : (0 : RepTot N).val v = 0 := rfl
@[simp] lemma add_val (φ ψ : RepTot N) (v : Paths Q) : (φ + ψ).val v = φ.val v + ψ.val v := rfl
@[simp] lemma smul_val (a : k) (φ : RepTot N) (v : Paths Q) : (a • φ).val v = a • φ.val v := rfl

lemma val_injective : Function.Injective (RepTot.val : RepTot N → _) := fun _ _ h ↦ RepTot.ext h

instance : AddCommGroup (RepTot N) :=
  val_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance : Module k (RepTot N) :=
  val_injective.module k (⟨⟨RepTot.val, rfl⟩, fun _ _ ↦ rfl⟩ : RepTot N →+ _) fun _ _ ↦ rfl

end RepTot

variable (N : LargeIndecomposable.Foundations.QuiverRep.{u, 0, 0, u} k Q)

/-- The component of a possibly zero path. -/
def pathMap {a b : Q} : Option (Quiver.Path a b) → (N.obj (pv a) →ₗ[k] N.obj (pv b))
  | none => 0
  | some p => (N.map p).hom

/-- The action of a morphism of `PathCat Q`. -/
def repAct {X Y : PathCat Q} (f : X ⟶ Y) : Module.End k (RepTot N) where
  toFun φ := ⟨Pi.single (pv Y.as) (pathMap N f (φ.val (pv X.as)))⟩
  map_add' φ ψ := by
    ext v
    simp only [RepTot.add_val, map_add, Pi.single_add, Pi.add_apply]
  map_smul' a φ := by
    ext v
    simp only [RepTot.smul_val, map_smul, Pi.single_smul, Pi.smul_apply, RingHom.id_apply]

lemma repAct_val {X Y : PathCat Q} (f : X ⟶ Y) (φ : RepTot N) (v : Paths Q) :
    (repAct N f φ).val v = Pi.single (M := fun v ↦ N.obj v) (pv Y.as) (pathMap N f (φ.val (pv X.as))) v := rfl

lemma pathMap_comp {X Y Z : PathCat Q} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pathMap N (f ≫ g) = pathMap N g ∘ₗ pathMap N f := by
  rw [PathCat.comp_def]
  rcases f with _ | p <;> rcases g with _ | q
  all_goals simp only [pcomp, pathMap, LinearMap.zero_comp, LinearMap.comp_zero]
  have := N.map_comp (X := pv X.as) (Y := pv Y.as) (Z := pv Z.as) p q
  exact (congrArg ModuleCat.Hom.hom this).trans (ModuleCat.hom_comp _ _)

lemma repAct_zero {X Y : PathCat Q} : repAct N (0 : X ⟶ Y) = 0 := by
  refine LinearMap.ext fun φ ↦ RepTot.ext (funext fun v ↦ ?_)
  rw [repAct_val]
  simp [pathMap, PathCat.zero_def]

/-- The representation of `k(PathCat Q)` on the total space. -/
def repRep : Linearization (PathCat Q) k →ₐ[k] Module.End k (RepTot N) :=
  linLift k (fun f ↦ repAct N f) (repAct_zero N)
    (by
      intro X Y Z f g
      refine LinearMap.ext fun φ ↦ RepTot.ext (funext fun v ↦ ?_)
      simp only [Module.End.mul_apply, repAct_val, pathMap_comp, LinearMap.comp_apply,
        Pi.single_eq_same])
    (by
      intro X Y Y' Z f g hY
      refine LinearMap.ext fun φ ↦ RepTot.ext (funext fun v ↦ ?_)
      have : pv Y'.as ≠ pv Y.as := fun h ↦ hY (PathCat.ext_as h.symm)
      simp only [Module.End.mul_apply, repAct_val, Pi.single_eq_of_ne this, map_zero,
        Pi.single_zero, LinearMap.zero_apply, RepTot.zero_val]
      rfl)
    (by
      refine LinearMap.ext fun φ ↦ RepTot.ext (funext fun v ↦ ?_)
      rw [LinearMap.sum_apply]
      rw [show (∑ X : PathCat Q, repAct N (𝟙 X) φ).val v = ∑ X : PathCat Q, (repAct N (𝟙 X) φ).val v
        from map_sum (⟨⟨fun ψ : RepTot N ↦ ψ.val v, rfl⟩, fun _ _ ↦ rfl⟩ : RepTot N →+ N.obj v) _ _]
      simp only [repAct_val, Module.End.one_apply]
      rw [Finset.sum_eq_single (⟨v⟩ : PathCat Q) (fun X _ hX ↦ by
        rw [Pi.single_eq_of_ne]
        exact fun h ↦ hX (PathCat.ext_as h.symm)) (by simp), Pi.single_eq_same]
      simp only [PathCat.id_def, pathMap]
      change (N.map (𝟙 _)).hom (φ.val v) = _
      rw [N.map_id]
      rfl)

instance : Module (Linearization (PathCat Q) k) (RepTot N) := Module.compHom _ (repRep N).toRingHom

instance : IsScalarTower k (Linearization (PathCat Q) k) (RepTot N) where
  smul_assoc a b φ := by
    change repRep N (a • b) φ = a • repRep N b φ
    rw [map_smul]
    rfl

variable {N}

lemma morElt_smul_val {X Y : PathCat Q} (f : X ⟶ Y) (φ : RepTot N) (v : Paths Q) :
    (morElt k f • φ).val v = Pi.single (M := fun v ↦ N.obj v) (pv Y.as) (pathMap N f (φ.val (pv X.as))) v := by
  change (repRep N (morElt k f) φ).val v = _
  rw [show repRep N (morElt k f) = repAct N f from linLiftₗ_morElt k _ (repAct_zero N) f]
  rfl

/-! ### The functor -/

variable {N' N'' : LargeIndecomposable.Foundations.QuiverRep.{u, 0, 0, u} k Q}

/-- The element supported at one vertex. -/
def single (v : Paths Q) (m : N.obj v) : RepTot N := ⟨Pi.single v m⟩

lemma id_smul_eq_single (v : Paths Q) (φ : RepTot N) :
    morElt k (𝟙 (⟨v⟩ : PathCat Q)) • φ = single v (φ.val v) := by
  ext w
  rw [morElt_smul_val]
  simp only [single, PathCat.id_def, pathMap]
  congr 2
  change (N.map (𝟙 v)).hom _ = _
  rw [N.map_id]
  rfl

/-- A morphism of `Paths Q` as a path of `Q`. -/
abbrev toPath {a b : Paths Q} (p : a ⟶ b) : Quiver.Path (V := Q) a b := p

lemma path_smul_single {a b : Paths Q} (p : a ⟶ b) (m : N.obj a) :
    morElt k (PathCat.ofPath (Q := Q) (toPath p)) • single a m = single b ((N.map p).hom m) := by
  ext w
  rw [morElt_smul_val]
  simp only [single, PathCat.ofPath, pathMap, Pi.single_eq_same]

/-- A natural transformation as a `k`-linear map of total spaces. -/
def repMapₗ (η : N ⟶ N') : RepTot N →ₗ[k] RepTot N' where
  toFun φ := ⟨fun v ↦ (η.app v).hom (φ.val v)⟩
  map_add' φ ψ := by ext v; simp
  map_smul' a φ := by ext v; simp

lemma repMapₗ_morElt (η : N ⟶ N') {X Y : PathCat Q} (f : X ⟶ Y) (φ : RepTot N) :
    repMapₗ η (morElt k f • φ) = morElt k f • repMapₗ η φ := by
  ext v
  simp only [repMapₗ, LinearMap.coe_mk, AddHom.coe_mk, morElt_smul_val]
  by_cases h : v = pv Y.as
  · subst h
    simp only [Pi.single_eq_same]
    rcases f with _ | p
    · simp [pathMap]
    · change (η.app _).hom ((N.map p).hom _) = (N'.map p).hom ((η.app _).hom _)
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
        ← ModuleCat.hom_comp]
      exact congrArg (fun f ↦ (ModuleCat.Hom.hom f) _) (η.naturality (X := pv X.as) (Y := pv Y.as) p)
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

/-- A natural transformation as a module map. -/
def repMap (η : N ⟶ N') : RepTot N →ₗ[Linearization (PathCat Q) k] RepTot N' :=
  linOfMorElt k (repMapₗ η) fun f φ ↦ repMapₗ_morElt η f φ

variable (k Q) in
/-- **Representations as modules over the linearization of the path category.** -/
def repFunctor : LargeIndecomposable.Foundations.QuiverRep.{u, 0, 0, u} k Q ⥤ ModuleCat.{u} (Linearization (PathCat Q) k) where
  obj N := ModuleCat.of _ (RepTot N)
  map η := ModuleCat.ofHom (repMap η)
  map_id N := by ext φ v; rfl
  map_comp η θ := by ext φ v; rfl

/-- The natural transformation of a module map. -/
def preimageApp (g : RepTot N →ₗ[Linearization (PathCat Q) k] RepTot N') (v : Paths Q) :
    N.obj v ⟶ N'.obj v :=
  ModuleCat.ofHom
    { toFun m := (g (single v m)).val v
      map_add' m m' := by
        rw [show single v (m + m') = single v m + single v m' by ext w; simp [single, Pi.single_add],
          map_add]; rfl
      map_smul' a m := by
        rw [show single v (a • m) = a • single v m by ext w; simp [single, Pi.single_smul],
          LinearMap.map_smul_of_tower]; rfl }

/-- The preimage of a module map. -/
def preimage (g : RepTot N →ₗ[Linearization (PathCat Q) k] RepTot N') : N ⟶ N' where
  app v := preimageApp g v
  naturality a b p := by
    ext m
    change (g (single b ((N.map p).hom m))).val b = (N'.map p).hom ((g (single a m)).val a)
    rw [← path_smul_single (k := k) p m, map_smul, morElt_smul_val]
    simp [PathCat.ofPath, pathMap]

lemma repMap_preimage (g : RepTot N →ₗ[Linearization (PathCat Q) k] RepTot N') :
    repMap (preimage g) = g := by
  ext φ v
  change (g (single v (φ.val v))).val v = (g φ).val v
  rw [← id_smul_eq_single (k := k) v φ, map_smul, id_smul_eq_single]
  simp [single]

instance : (repFunctor k Q).Full where
  map_surjective {N N'} g := ⟨preimage g.hom, by
    ext1
    exact repMap_preimage g.hom⟩

instance : (repFunctor k Q).Faithful where
  map_injective {N N'} η θ h := by
    ext v m
    have := congrArg (fun g : (repFunctor k Q).obj N ⟶ (repFunctor k Q).obj N' ↦
      (g.hom (single v m)).val v) h
    change (η.app v).hom ((single v m).val v) = (θ.app v).hom ((single v m).val v) at this
    simpa [single] using this

/-! ### Finite representation type -/

instance : Fintype (Paths Q) := inferInstanceAs (Fintype Q)

lemma finite_repTot (N : LargeIndecomposable.Foundations.QuiverRep.{u, 0, 0, u} k Q) (hN : LargeIndecomposable.Foundations.IsFinDim k Q N) :
    Module.Finite (Linearization (PathCat Q) k) (RepTot N) := by
  have : ∀ v : Paths Q, Module.Finite k (N.obj v) := LargeIndecomposable.Foundations.isFinDim_iff.1 hN
  have : Module.Finite k (RepTot N) :=
    Module.Finite.of_injective
      (⟨⟨RepTot.val, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩ : RepTot N →ₗ[k] ∀ v : Paths Q, N.obj v)
      RepTot.val_injective
  exact Module.Finite.of_restrictScalars_finite k _ _

lemma isIndecomposable_repTot (N : LargeIndecomposable.Foundations.QuiverRep.{u, 0, 0, u} k Q)
    (hN : Indecomposable N) :
    Statement.IsIndecomposable (Linearization (PathCat Q) k) (RepTot N) := by
  have := (Reduction.isIndecomposable_iff ((repFunctor k Q).obj N)).2
  refine this ⟨fun hz ↦ hN.1 ?_, fun e he ↦ ?_⟩
  · rw [IsZero.iff_id_eq_zero] at *
    exact (repFunctor k Q).map_injective (by rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]; assumption)
  · have he' : (repFunctor k Q).preimage e ≫ (repFunctor k Q).preimage e =
        (repFunctor k Q).preimage e :=
      (repFunctor k Q).map_injective (by simp [he])
    rcases LargeIndecomposable.Foundations.idempotent_eq_zero_or_id_of_indecomposable hN he' with h0 | h1
    · left
      rw [← (repFunctor k Q).map_preimage e, h0, CategoryTheory.Functor.map_zero]
    · right
      rw [← (repFunctor k Q).map_preimage e, h1, CategoryTheory.Functor.map_id]

/-- **Representation-finiteness of `k(PathCat Q)` gives finite representation type
of `Q`.** -/
theorem isFiniteRepType_of_isRepresentationFinite
    (h : Statement.IsRepresentationFinite (Linearization (PathCat Q) k)) :
    LargeIndecomposable.Foundations.IsFiniteRepType.{u, 0, 0, u} k Q := by
  classical
  obtain ⟨n, B, hB⟩ := h
  rw [LargeIndecomposable.Foundations.isFiniteRepType_iff]
  set P := fun M : LargeIndecomposable.Foundations.QuiverRep.{u, 0, 0, u} k Q ↦ LargeIndecomposable.Foundations.IsFinDim k Q M ∧ Indecomposable M
    with hP
  have key : ∀ X : ObjectProperty.FullSubcategory P, ∃ i,
      Nonempty ((repFunctor k Q).obj X.obj ≅ B i) := fun X ↦ by
    have := finite_repTot X.obj X.property.1
    obtain ⟨i, ⟨e⟩⟩ := hB (RepTot X.obj) (isIndecomposable_repTot X.obj X.property.2)
    exact ⟨i, ⟨e.toModuleIso⟩⟩
  choose idx hidx using key
  refine Finite.of_injective (fun x : Skeleton (ObjectProperty.FullSubcategory P) ↦
    idx ((fromSkeleton _).obj x)) fun x y hxy ↦ ?_
  obtain ⟨e1⟩ := hidx ((fromSkeleton _).obj x)
  obtain ⟨e2⟩ := hidx ((fromSkeleton _).obj y)
  simp only at hxy
  rw [hxy] at e1
  have e : ((fromSkeleton _).obj x).obj ≅ ((fromSkeleton _).obj y).obj :=
    (repFunctor k Q).preimageIso (e1 ≪≫ e2.symm)
  have e' : (fromSkeleton _).obj x ≅ (fromSkeleton _).obj y := (ObjectProperty.ι P).preimageIso e
  rw [← Quotient.out_eq x, ← Quotient.out_eq y]
  exact Quotient.sound ⟨e'⟩

/-! ### Euclidean trees -/

open LargeIndecomposable.Foundations in
/-- A path category whose quiver contains `D̃ₘ₊₄` has a representation-infinite
linearization. -/
theorem not_isRepresentationFinite_of_copy_affineD (m : ℕ)
    (f : (LargeIndecomposable.Foundations.Quiver.underlyingGraph (LargeIndecomposable.Foundations.Quiver.AffineD m)).Copy (LargeIndecomposable.Foundations.Quiver.underlyingGraph Q)) :
    ¬Statement.IsRepresentationFinite (Linearization (PathCat Q) k) := fun h ↦
  LargeIndecomposable.Foundations.not_isFiniteRepType_of_copy_affineD (k := k) m f (isFiniteRepType_of_isRepresentationFinite h)

open LargeIndecomposable.Foundations in
/-- The same for `Ẽ₆`. -/
theorem not_isRepresentationFinite_of_copy_affineE6
    (f : (LargeIndecomposable.Foundations.Quiver.underlyingGraph LargeIndecomposable.Foundations.Quiver.AffineE6).Copy (LargeIndecomposable.Foundations.Quiver.underlyingGraph Q)) :
    ¬Statement.IsRepresentationFinite (Linearization (PathCat Q) k) := fun h ↦
  LargeIndecomposable.Foundations.not_isFiniteRepType_of_copy_affineE6 (k := k) f (isFiniteRepType_of_isRepresentationFinite h)

open LargeIndecomposable.Foundations in
/-- The same for `Ẽ₇`. -/
theorem not_isRepresentationFinite_of_copy_affineE7
    (f : (LargeIndecomposable.Foundations.Quiver.underlyingGraph LargeIndecomposable.Foundations.Quiver.AffineE7).Copy (LargeIndecomposable.Foundations.Quiver.underlyingGraph Q)) :
    ¬Statement.IsRepresentationFinite (Linearization (PathCat Q) k) := fun h ↦
  LargeIndecomposable.Foundations.not_isFiniteRepType_of_copy_affineE7 (k := k) f (isFiniteRepType_of_isRepresentationFinite h)

open LargeIndecomposable.Foundations in
/-- The same for `Ẽ₈`. -/
theorem not_isRepresentationFinite_of_copy_affineE8
    (f : (LargeIndecomposable.Foundations.Quiver.underlyingGraph LargeIndecomposable.Foundations.Quiver.AffineE8).Copy (LargeIndecomposable.Foundations.Quiver.underlyingGraph Q)) :
    ¬Statement.IsRepresentationFinite (Linearization (PathCat Q) k) := fun h ↦
  LargeIndecomposable.Foundations.not_isFiniteRepType_of_copy_affineE8 (k := k) f (isFiniteRepType_of_isRepresentationFinite h)

end RayCat

end LargeIndecomposable
