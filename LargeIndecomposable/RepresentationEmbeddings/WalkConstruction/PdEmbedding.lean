module

public import LargeIndecomposable.RepresentationEmbeddings.WalkConstruction.PdControl
public import LargeIndecomposable.RepresentationEmbeddings.EmbeddingTheorem.EmbeddingData
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Push-down constructions and Theorem 5.2

Alternatives (2) and (3) of Theorem 3.14 share one shape: a fully faithful
exact functor `L : D → Rep D` into representations of a finite quiver `D`,
followed by the push-down along a quiver morphism `p : D → Q` into modules over
`A`, presented as a quotient `π : kQ → A` (Constructions 3.6, 3.7 and 3.12).
A `PdData k A` records these data together with the hypotheses of
`PushDown.bl_self_eq_zero` (a partition of block positions into classes, and
the vanishing of morphisms whose image vanishes at a vertex), the condition
that the kernel of `π` acts by zero on `p_*L(T)`, and the facts behind the
colimit comparison: every vector of `L(T)` comes from `L(U)` for a
finite-dimensional `U ⊆ T`, and `L` keeps inclusions injective.

The functor `F = p_*L : D → Mod A` is additive, `k`-linear, faithful and exact,
has finite-dimensional values on `D_fin`, satisfies the colimit comparison
(3.4), and admits retractions on `C` with a nilpotence bound, the number of
vertices of `D` (Propositions 4.4, 4.7, 4.8). With the two facts about `S₋`
(`PdDatum`) it gives the data of Theorem 5.2. A kernel of `π` acting by zero on
`p_*L(T)` for finite-dimensional `T` acts by zero for every `T`
(`kills_of_fin`, as in the proof of Lemma 3.13).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair FinQuiver Rep

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]

namespace PushDown

section Finitary

variable {D Q : FinQuiver} (L : Statement.D k ⥤ Rep k D)
  (finitary : ∀ (T : Statement.D k) (i : D.V) (x : (L.obj T).obj i),
    ∃ U : Kron.FinSub T.obj, x ∈ Set.range ((L.map (Comparison.incl T U)).app i).hom)

include finitary in
/-- A vector of the total space of `L(T)` comes from `L(U)` for a
finite-dimensional `U ⊆ T`. -/
lemma exists_tot_rep (T : Statement.D k) (x : (L.obj T).Tot) :
    ∃ (U : Kron.FinSub T.obj) (y : (L.obj ((DfinToD k).obj
      ((Extension.finDiagram T).obj U))).Tot), (L.map (Comparison.incl T U)).tot y = x := by
  classical
  choose V y hy using fun i ↦ finitary T i (x i)
  obtain ⟨U, -, hVU⟩ := Extension.exists_ge_of_finite (⟨⊥, Kron.Sub.isFin_bot⟩ : Kron.FinSub T.obj) V
  refine ⟨U, fun i ↦ ((L.map ((DfinToD k).map ((Extension.finDiagram T).map
    (homOfLE (hVU i))))).app i).hom (y i), funext fun i ↦ ?_⟩
  rw [Hom.tot_apply, ← hy i]
  change ((L.map (DfinToD k |>.map _) ≫ L.map (Comparison.incl T U)).app i).hom (y i) = _
  rw [← L.map_comp, Comparison.map_incl]

include finitary in
/-- An element of `kQ` acting by zero on `p_*L(T)` for every finite-dimensional
`T` acts by zero for every `T`, since every vector comes from a
finite-dimensional submodule (as in the proof of Lemma 3.13). -/
lemma kills_of_fin (p : FinQuiver.Hom D Q) (z : Q.PathAlgebra k)
    (h : ∀ T : Dfin k, (L.obj ((DfinToD k).obj T)).pdAct p z = 0) (T : Statement.D k) :
    (L.obj T).pdAct p z = 0 := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨U, y, rfl⟩ := exists_tot_rep L finitary T x
  have hc := commute_pdAct p _ (L.map (Comparison.incl T U)).tot
    (Hom.isPdHom_tot p _).1 (Hom.isPdHom_tot p _).2 z
  have := LinearMap.congr_fun hc y
  simp only [LinearMap.comp_apply] at this
  rw [← this, h ((Extension.finDiagram T).obj U), LinearMap.zero_apply, map_zero,
    LinearMap.zero_apply]

end Finitary

variable (k A) in
/-- The data of a push-down construction, apart from the representation-embedding
property. -/
structure PdData where
  /-- The quiver carrying the representations `L(T)`. -/
  D : FinQuiver
  /-- The quiver of the presentation of `A`. -/
  Q : FinQuiver
  /-- The quiver morphism along which we push down. -/
  p : FinQuiver.Hom D Q
  locInj : p.LocallyInjective
  /-- The classes of block positions. -/
  B : BlockClasses p
  /-- The functor `L`. -/
  L : Statement.D k ⥤ Rep k D
  [additive : L.Additive]
  hL : L.FullyFaithful
  map_smul : ∀ {T U : Statement.D k} (c : k) (f : T ⟶ U) (i : D.V),
    (L.map (c • f)).app i = c • (L.map f).app i
  zero : ZeroAtVertex L
  exact : ∀ (X Y Z : Statement.D k) (f : X ⟶ Y) (g : Y ⟶ Z), Kron.IsShortExact f.hom g.hom →
    ∀ i : D.V, Function.Injective ((L.map f).app i).hom ∧
      Function.Surjective ((L.map g).app i).hom ∧
        LinearMap.range ((L.map f).app i).hom = LinearMap.ker ((L.map g).app i).hom
  fin : ∀ (T : Dfin k) (i : D.V), Module.Finite k ((L.obj ((DfinToD k).obj T)).obj i)
  /-- Every vector of `L(T)` comes from `L(U)` for a finite-dimensional `U ⊆ T`. -/
  finitary : ∀ (T : Statement.D k) (i : D.V) (x : (L.obj T).obj i),
    ∃ U : Kron.FinSub T.obj, x ∈ Set.range ((L.map (Comparison.incl T U)).app i).hom
  /-- `L` keeps the inclusions `U ⊆ T` injective. -/
  incl_injective : ∀ (T : Statement.D k) (U : Kron.FinSub T.obj) (i : D.V),
    Function.Injective ((L.map (Comparison.incl T U)).app i).hom
  /-- The presentation `kQ → A`. -/
  π : Q.PathAlgebra k →ₐ[k] A
  surj : Function.Surjective π
  /-- `p_*L(T)` is an `A`-module. -/
  kills : ∀ (T : Statement.D k) (z : Q.PathAlgebra k), π z = 0 → (L.obj T).pdAct p z = 0

attribute [instance] PdData.additive

namespace PdData

variable (W : PdData k A)

/-- The action of `A` on `p_*L(T)`. -/
def act (T : Statement.D k) : A →ₐ[k] Module.End k (W.L.obj T).Tot :=
  (Ideal.Quotient.liftₐ (RingHom.ker W.π) ((W.L.obj T).pdAct W.p)
    fun z hz ↦ W.kills T z hz).comp (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm.toAlgHom

lemma act_π (T : Statement.D k) (z : W.Q.PathAlgebra k) : W.act T (W.π z) = (W.L.obj T).pdAct W.p z := by
  have : (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π z) =
      Ideal.Quotient.mk (RingHom.ker W.π) z := by
    rw [AlgEquiv.symm_apply_eq]; rfl
  change Ideal.Quotient.liftₐ (RingHom.ker W.π) ((W.L.obj T).pdAct W.p)
    (fun z hz ↦ W.kills T z hz) ((Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π z)) = _
  rw [this]
  rfl

/-- The total space `⊕_i L(T)(i)` with its `A`-module structure. -/
def Carrier (T : Statement.D k) : Type u := (W.L.obj T).Tot

instance (T : Statement.D k) : AddCommGroup (W.Carrier T) := inferInstanceAs (AddCommGroup (W.L.obj T).Tot)

instance (T : Statement.D k) : Module k (W.Carrier T) := inferInstanceAs (Module k (W.L.obj T).Tot)

instance (T : Statement.D k) : Module A (W.Carrier T) :=
  Module.compHom (W.L.obj T).Tot (W.act T).toRingHom

lemma smul_def (T : Statement.D k) (a : A) (x : W.Carrier T) :
    a • x = ((W.act T a : Module.End k (W.L.obj T).Tot) x : W.Carrier T) := rfl

instance (T : Statement.D k) : IsScalarTower k A (W.Carrier T) where
  smul_assoc c a x := by
    rw [smul_def, smul_def, _root_.map_smul]
    rfl

/-- The `A`-module `p_*L(T)`. -/
abbrev obj (T : Statement.D k) : ModuleCat.{u} A := ModuleCat.of A (W.Carrier T)

/-- A map of total spaces commuting with the push-down action, as a morphism of
`A`-modules. -/
def ofPd {T U : Statement.D k} (f : (W.L.obj T).Tot →ₗ[k] (W.L.obj U).Tot) (hf : IsPdHom W.p f) :
    W.obj T ⟶ W.obj U :=
  ModuleCat.ofHom
    { toFun := fun x ↦ (f x : W.Carrier U)
      map_add' := f.map_add
      map_smul' := fun a x ↦ by
        obtain ⟨z, rfl⟩ := W.surj a
        show f ((W.act T (W.π z)) (x : (W.L.obj T).Tot)) = (W.act U (W.π z)) (f x)
        rw [act_π, act_π]
        exact LinearMap.congr_fun (commute_pdAct W.p _ f hf.1 hf.2 z) x }

/-- The underlying map of total spaces of a morphism of `A`-modules. -/
def toTot {T U : Statement.D k} (g : W.obj T ⟶ W.obj U) : (W.L.obj T).Tot →ₗ[k] (W.L.obj U).Tot :=
  let f : W.Carrier T →ₗ[k] W.Carrier U :=
    LinearMap.restrictScalars k (show W.Carrier T →ₗ[A] W.Carrier U from g.hom)
  f

lemma toTot_apply {T U : Statement.D k} (g : W.obj T ⟶ W.obj U) (x : (W.L.obj T).Tot) :
    W.toTot g x = g.hom x := rfl

lemma toTot_ofPd {T U : Statement.D k} (f : (W.L.obj T).Tot →ₗ[k] (W.L.obj U).Tot) (hf : IsPdHom W.p f) :
    W.toTot (W.ofPd f hf) = f := rfl

lemma toTot_comp {T U V : Statement.D k} (f : W.obj T ⟶ W.obj U) (g : W.obj U ⟶ W.obj V) :
    W.toTot (f ≫ g) = W.toTot g ∘ₗ W.toTot f := rfl

lemma toTot_id (T : Statement.D k) : W.toTot (𝟙 (W.obj T)) = LinearMap.id := rfl

lemma toTot_add {T U : Statement.D k} (f g : W.obj T ⟶ W.obj U) : W.toTot (f + g) = W.toTot f + W.toTot g :=
  rfl

lemma toTot_injective {T U : Statement.D k} : Function.Injective (W.toTot : (W.obj T ⟶ W.obj U) → _) := by
  intro f g h
  ext x
  exact LinearMap.congr_fun h (x : (W.L.obj T).Tot)

lemma isPdHom_toTot {T U : Statement.D k} (g : W.obj T ⟶ W.obj U) : IsPdHom W.p (W.toTot g) := by
  have key : ∀ z, W.toTot g ∘ₗ (W.L.obj T).pdAct W.p z = (W.L.obj U).pdAct W.p z ∘ₗ W.toTot g := by
    intro z
    rw [← act_π, ← act_π]
    refine LinearMap.ext fun x ↦ ?_
    change g.hom ((W.act T (W.π z)) x) = (W.act U (W.π z)) (g.hom x)
    exact g.hom.map_smul (W.π z) x
  exact ⟨fun q ↦ by simpa using key (FinQuiver.vertex k W.Q q),
    fun c ↦ by simpa using key (FinQuiver.arrow k W.Q c)⟩

lemma blockEqs_toTot {T U : Statement.D k} (g : W.obj T ⟶ W.obj U) : BlockEqs W.p (W.toTot g) :=
  (isPdHom_iff W.p _).1 (W.isPdHom_toTot g)

/-- The functor `F = p_*L` on `D_fin`. -/
def functor : Statement.D k ⥤ ModuleCat.{u} A where
  obj := W.obj
  map f := W.ofPd (W.L.map f).tot (Hom.isPdHom_tot W.p _)
  map_id T := W.toTot_injective (by
    change (W.L.map (𝟙 T)).tot = LinearMap.id
    rw [CategoryTheory.Functor.map_id, Hom.tot_id])
  map_comp f g := W.toTot_injective (by
    change (W.L.map (f ≫ g)).tot = (W.L.map g).tot ∘ₗ (W.L.map f).tot
    rw [CategoryTheory.Functor.map_comp, Hom.tot_comp])

/-- `toTot` commutes with the `k`-linear structure of `Mod A`. -/
lemma toTot_smul' {T U : Statement.D k} (c : k) (f : W.functor.obj T ⟶ W.functor.obj U) :
    W.toTot (c • f) = c • W.toTot f := by
  refine LinearMap.ext fun x ↦ ?_
  change algebraMap k A c • (show W.Carrier U from f.hom x) = c • (show W.Carrier U from f.hom x)
  rw [algebraMap_smul]

lemma toTot_map {T U : Statement.D k} (f : T ⟶ U) : W.toTot (W.functor.map f) = (W.L.map f).tot := rfl

/-! ### Properties of `F` -/

instance : W.functor.Additive where
  map_add {T U f g} := W.toTot_injective (by
    change (W.L.map (f + g)).tot = (W.L.map f).tot + (W.L.map g).tot
    rw [Functor.map_add]
    rfl)

instance : W.functor.Linear k where
  map_smul {T U} f c := W.toTot_injective (by
    rw [W.toTot_smul' c (W.functor.map f)]
    change (W.L.map (c • f)).tot = c • (W.L.map f).tot
    refine LinearMap.ext fun x ↦ funext fun i ↦ ?_
    simp only [Hom.tot_apply, W.map_smul]
    rfl)

instance : W.functor.Faithful where
  map_injective {T U f g} h := by
    have h' : (W.L.map f).tot = (W.L.map g).tot := congrArg W.toTot h
    refine W.hL.map_injective (Rep.hom_ext fun i ↦ ?_)
    ext v
    have := congrArg (fun φ ↦ φ (Pi.single i v) i) h'
    simpa using this

lemma isExact : IsExactOnD W.functor := by
  intro X Y Z f g h
  have hc := W.exact X Y Z f g h
  refine ⟨fun x y hxy ↦ funext fun i ↦ (hc i).1 (congr_fun hxy i), fun y ↦ ?_, ?_⟩
  · exact ⟨fun i ↦ ((hc i).2.1 (y i)).choose, funext fun i ↦ ((hc i).2.1 (y i)).choose_spec⟩
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine funext fun i ↦ ?_
      have : ((W.L.map f).app i).hom (x i) ∈ LinearMap.ker ((W.L.map g).app i).hom :=
        (hc i).2.2 ▸ ⟨x i, rfl⟩
      exact this
    · intro hy
      have hy' : ∀ i, y i ∈ LinearMap.range ((W.L.map f).app i).hom := by
        intro i; rw [(hc i).2.2]; exact congr_fun hy i
      exact ⟨fun i ↦ (hy' i).choose, funext fun i ↦ (hy' i).choose_spec⟩

lemma finite (X : Dfin k) :
    Module.Finite k (RestrictScalars k A ((DfinToD k ⋙ W.functor).obj X)) := by
  have := W.fin X
  have : Module.Finite k (W.Carrier ((DfinToD k).obj X)) := Module.Finite.pi
  let e : W.Carrier ((DfinToD k).obj X) ≃ₗ[k]
      RestrictScalars k A (W.functor.obj ((DfinToD k).obj X)) :=
    { (RestrictScalars.addEquiv k A (W.functor.obj ((DfinToD k).obj X))).symm with
      map_smul' := fun c m ↦ by
        change (RestrictScalars.addEquiv k A _).symm (c • m) = _
        rw [← algebraMap_smul A c m, RestrictScalars.addEquiv_symm_map_algebraMap_smul]
        rfl }
  exact Module.Finite.equiv e

/-! ### The colimit comparison -/

lemma exists_tot_rep (T : Statement.D k) (x : (W.L.obj T).Tot) :
    ∃ (U : Kron.FinSub T.obj) (y : (W.L.obj ((DfinToD k).obj
      ((Extension.finDiagram T).obj U))).Tot), (W.L.map (Comparison.incl T U)).tot y = x :=
  PushDown.exists_tot_rep W.L W.finitary T x

lemma toTot_map_incl (T : Statement.D k) (U : Kron.FinSub T.obj) :
    W.toTot (W.functor.map (Comparison.incl T U)) = (W.L.map (Comparison.incl T U)).tot := rfl

/-- Constructions 3.7 and 3.12: `p_*L` satisfies the colimit comparison (3.4). -/
theorem comparison : Comparison.IsComparison W.functor := by
  refine Comparison.isComparison_of_elements _ (fun T x ↦ ?_) (fun T U y hy ↦ ?_)
  · obtain ⟨U, y, hy⟩ := W.exists_tot_rep T x
    exact ⟨U, y, hy⟩
  · refine ⟨U, le_rfl, ?_⟩
    have hy0 : y = 0 := funext fun i ↦
      W.incl_injective T U i (by
        have := congrFun (show (W.L.map (Comparison.incl T U)).tot y = 0 from hy) i
        exact this.trans (map_zero _).symm)
    rw [hy0, map_zero]

/-! ### Retractions on `C` (Propositions 4.4, 4.7, 4.8) -/

/-- The diagonal part of a morphism, as a morphism of representations. -/
abbrev δ {T U : Statement.D k} (g : W.obj T ⟶ W.obj U) : W.L.obj T ⟶ W.L.obj U :=
  diagHom W.locInj (W.toTot g) (W.blockEqs_toTot g)

/-- The retraction `ρ(g) = L⁻¹(δ g)`. -/
def ρD {T U : Statement.D k} (g : W.obj T ⟶ W.obj U) : T ⟶ U := W.hL.preimage (W.δ g)

lemma map_ρD {T U : Statement.D k} (g : W.obj T ⟶ W.obj U) : W.L.map (W.ρD g) = W.δ g :=
  W.hL.map_preimage _

lemma δ_app {T U : Statement.D k} (g : W.obj T ⟶ W.obj U) (i : W.D.V) :
    (W.δ g).app i = ModuleCat.ofHom (blk (W.toTot g) i i) := rfl

lemma blk_add {X Y : Rep k W.D} (f g : X.Tot →ₗ[k] Y.Tot) (j i : W.D.V) :
    blk (f + g) j i = blk f j i + blk g j i := by
  ext v; simp [blk]

lemma blk_smul {X Y : Rep k W.D} (c : k) (f : X.Tot →ₗ[k] Y.Tot) (j i : W.D.V) :
    blk (c • f) j i = c • blk f j i := by
  ext v; simp [blk]

lemma blk_comp_of_bl {X Y Z : Rep k W.D} {f : X.Tot →ₗ[k] Y.Tot} {g : Y.Tot →ₗ[k] Z.Tot}
    {i : W.D.V} (h : bl (g ∘ₗ f) i i = bl g i i ∘ₗ bl f i i) :
    blk (g ∘ₗ f) i i = blk g i i ∘ₗ blk f i i := by
  rw [← blk_bl_self, h]
  ext v
  simp [blk, bl, idm_apply]

lemma ρD_add {T U : Statement.D k} (g g' : W.obj T ⟶ W.obj U) : W.ρD (g + g') = W.ρD g + W.ρD g' := by
  refine W.hL.map_injective (Rep.hom_ext fun i ↦ ?_)
  rw [Functor.map_add, map_ρD, map_ρD, map_ρD]
  change ModuleCat.ofHom (blk (W.toTot g + W.toTot g') i i) =
    ModuleCat.ofHom (blk (W.toTot g) i i) + ModuleCat.ofHom (blk (W.toTot g') i i)
  rw [blk_add]; rfl

lemma ρD_smul {T U : Statement.D k} (c : k) (g : W.functor.obj T ⟶ W.functor.obj U) :
    W.ρD (c • g) = c • W.ρD g := by
  refine W.hL.map_injective (Rep.hom_ext fun i ↦ ?_)
  rw [W.map_smul]
  erw [map_ρD, map_ρD]
  change ModuleCat.ofHom (blk (W.toTot (c • g)) i i) = c • ModuleCat.ofHom (blk (W.toTot g) i i)
  rw [W.toTot_smul' c g, blk_smul]; rfl

lemma ρD_comp {T U V : Statement.D k} (hT : InC T.obj) (f : W.obj T ⟶ W.obj U) (g : W.obj U ⟶ W.obj V) :
    W.ρD (f ≫ g) = W.ρD f ≫ W.ρD g := by
  refine W.hL.map_injective (Rep.hom_ext fun i ↦ ?_)
  have hm : blk (W.toTot (f ≫ g)) i i = blk (W.toTot g) i i ∘ₗ blk (W.toTot f) i i :=
    W.blk_comp_of_bl (bl_comp_self W.B W.locInj W.hL W.zero hT (W.blockEqs_toTot f)
      (W.blockEqs_toTot g) i)
  rw [Functor.map_comp, map_ρD, map_ρD, map_ρD, comp_app]
  change ModuleCat.ofHom (blk (W.toTot (f ≫ g)) i i) =
    ModuleCat.ofHom (blk (W.toTot f) i i) ≫ ModuleCat.ofHom (blk (W.toTot g) i i)
  rw [hm]; rfl

lemma ρD_map {T U : Statement.D k} (u : T ⟶ U) : W.ρD (W.functor.map u) = u := by
  refine W.hL.map_injective (Rep.hom_ext fun i ↦ ?_)
  erw [map_ρD]
  change ModuleCat.ofHom (blk (W.L.map u).tot i i) = _
  rw [Hom.blk_tot]; rfl

/-- Proposition 4.8: retractions on `C`. -/
def retractions : Retractions k ((InCD (k := k)).ι ⋙ W.functor) where
  ρ X Y :=
    { toFun g := ObjectProperty.homMk (W.ρD g)
      map_add' g g' := by ext1; exact W.ρD_add g g'
      map_smul' c g := by ext1; exact W.ρD_smul c g }
  map_comp {X Y Z} f g := by ext1; exact W.ρD_comp X.2 f g
  ρ_map {X Y} u := by ext1; exact W.ρD_map u.hom

lemma kerChain_mem {m : ℕ} {X Y : (InCD (k := k)).FullSubcategory}
    {f : ((InCD (k := k)).ι ⋙ W.functor).obj X ⟶ ((InCD (k := k)).ι ⋙ W.functor).obj Y}
    (hf : W.retractions.KerChain m f) :
    W.toTot f ∈ AddSubmonoid.closure
      {g : (W.L.obj X.obj).Tot →ₗ[k] (W.L.obj Y.obj).Tot |
        Chain.Good (p := W.p) (LX W.L) (fun _ _ ↦ True) (o := ⟨X.obj, X.2⟩) (o' := ⟨Y.obj, Y.2⟩)
          m g} := by
  induction hf with
  | nil X =>
    exact AddSubmonoid.subset_closure (Chain.good_id (diagZero_LX W.locInj W.hL W.zero) ⟨X.obj, X.2⟩)
  | @cons m X Y Z _ g _ hg ih =>
    have h0 : W.ρD g = 0 := by
      have := congrArg (fun φ : Y ⟶ Z ↦ φ.hom) hg
      exact this
    have hd : ∀ i, bl (W.toTot g) i i = 0 :=
      diagHom_eq_preimage W.locInj W.hL (W.blockEqs_toTot g) h0
    exact Chain.closure_good_comp W.B W.locInj (diagZero_LX W.locInj W.hL W.zero)
      (colAdm_LX W.B) (o := ⟨X.obj, X.2⟩) (o' := ⟨Y.obj, Y.2⟩) (o'' := ⟨Z.obj, Z.2⟩) ih
      (W.blockEqs_toTot g) hd

/-- Every composite of `|D₀|` maps in the kernels of the retractions vanishes. -/
lemma nilpotentBound : W.retractions.NilpotentBound (Fintype.card W.D.V) := by
  intro X Y f hf
  refine W.toTot_injective ?_
  exact Chain.eq_zero_of_mem_closure_good (Xf := LX W.L) (Adm := fun _ _ ↦ True)
    (o := ⟨X.obj, X.2⟩) (o' := ⟨Y.obj, Y.2⟩) (W.kerChain_mem hf)

/-! ### Facts about the push-down of a brick -/

/-- Isomorphic push-downs have total spaces of equal dimension. -/
lemma finrank_eq_of_iso {T U : Statement.D k} (e : W.functor.obj T ≅ W.functor.obj U) :
    Module.finrank k (W.L.obj T).Tot = Module.finrank k (W.L.obj U).Tot := by
  refine LinearEquiv.finrank_eq (LinearEquiv.ofLinearMap (W.toTot e.hom) (W.toTot e.inv) ?_ ?_)
  · refine LinearMap.ext fun x ↦ ?_
    exact congrArg (fun f ↦ f.hom x) e.inv_hom_id
  · refine LinearMap.ext fun x ↦ ?_
    exact congrArg (fun f ↦ f.hom x) e.hom_inv_id

/-- A push-down whose total space has dimension one is indecomposable. -/
lemma isIndecomposable_of_finrank_eq_one {T : Statement.D k}
    (h : Module.finrank k (W.L.obj T).Tot = 1) : IsIndecomposable A (W.functor.obj T) := by
  have hnt : Nontrivial (W.L.obj T).Tot := Module.nontrivial_of_finrank_eq_succ h
  refine ⟨hnt, fun N N' hc ↦ ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne.1
  obtain ⟨y, hyN', hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne.2
  obtain ⟨c, hc'⟩ := (finrank_eq_one_iff_of_nonzero' (show (W.L.obj T).Tot from x) hx0).1 h
    (show (W.L.obj T).Tot from y)
  have hyN : y ∈ N := by
    have hyx : algebraMap k A c • x = y := by
      change algebraMap k A c • (show W.Carrier T from x) = (show W.Carrier T from y)
      rw [algebraMap_smul]
      exact hc'
    exact hyx ▸ N.smul_mem _ hxN
  have : y ∈ N ⊓ N' := ⟨hyN, hyN'⟩
  rw [hc.inf_eq_bot, Submodule.mem_bot] at this
  exact hy0 this

/-- An idempotent map with zero diagonal blocks vanishes, by the chain
argument on a single object. -/
lemma eq_zero_of_idem {𝒪 : Type*} {Xf : 𝒪 → Rep k W.D} {Adm : 𝒪 → W.D.V → Prop}
    (hZ : Chain.DiagZero (p := W.p) Xf Adm) (hC : Chain.ColAdm W.B Xf Adm) {o : 𝒪}
    {u : (Xf o).Tot →ₗ[k] (Xf o).Tot} (hu : BlockEqs W.p u) (hidem : u ∘ₗ u = u)
    (hdiag : ∀ i, bl u i i = 0) : u = 0 := by
  have key : ∀ m, u ∈ AddSubmonoid.closure {g | Chain.Good (p := W.p) Xf Adm (m + 1) g} := by
    intro m
    induction m with
    | zero =>
      have := Chain.closure_good_comp W.B W.locInj hZ hC
        (AddSubmonoid.subset_closure (Chain.good_id hZ o)) hu hdiag
      simpa using this
    | succ m ih =>
      have := Chain.closure_good_comp W.B W.locInj hZ hC ih hu hdiag
      rwa [hidem] at this
  rcases Nat.eq_zero_or_pos (Fintype.card W.D.V) with h0 | h0
  · have := Fintype.card_eq_zero_iff.1 h0
    exact eq_zero_of_comp_idm fun i ↦ (IsEmpty.false i).elim
  · have := key (Fintype.card W.D.V - 1)
    rw [Nat.sub_add_cancel h0] at this
    exact Chain.eq_zero_of_mem_closure_good this

/-- The push-down of a brick `S` is indecomposable if each class
of block positions has a zero column at which `L(S)` is nonzero. -/
lemma isIndecomposable_of_brick (S : Statement.D k) (Adm : W.D.V → Prop)
    (hbrick : ∀ φ : S ⟶ S, ∃ c : k, φ = c • 𝟙 S)
    (hadm : ∀ c, Adm c → Nontrivial ((W.L.obj S).obj c))
    (hcol : ∀ κ : W.B.ι, ∃ c, Adm c ∧ ∀ f : (W.L.obj S).Tot →ₗ[k] (W.L.obj S).Tot,
      BlockEqs W.p f → restr (W.B.piece κ) f ∘ₗ (W.L.obj S).idm c = 0)
    (hne : ∃ c, Adm c) : IsIndecomposable A (W.functor.obj S) := by
  classical
  let Xf : Unit → Rep k W.D := fun _ ↦ W.L.obj S
  let Ad : Unit → W.D.V → Prop := fun _ c ↦ Adm c
  -- the scalar of the diagonal part
  have hscal : ∀ (h : (W.L.obj S).Tot →ₗ[k] (W.L.obj S).Tot) (hh : BlockEqs W.p h),
      ∃ c₀ : k, ∀ i, bl h i i = c₀ • (W.L.obj S).idm i := by
    intro h hh
    obtain ⟨c₀, hc₀⟩ := hbrick (W.hL.preimage (diagHom W.locInj h hh))
    refine ⟨c₀, fun i ↦ ?_⟩
    have e1 : (diagHom W.locInj h hh).app i = c₀ • 𝟙 _ := by
      rw [← W.hL.map_preimage (diagHom W.locInj h hh), hc₀, W.map_smul, CategoryTheory.Functor.map_id]
      rfl
    have e2 : blk h i i = c₀ • LinearMap.id := congrArg (fun φ ↦ φ.hom) e1
    have key : ∀ v, h (Pi.single i v) i = c₀ • v := fun v ↦ by
      have := congrArg (fun φ ↦ φ v) e2
      simpa [blk] using this
    refine LinearMap.ext fun x ↦ funext fun l ↦ ?_
    by_cases hl : l = i
    · subst hl
      simp [bl, idm_apply, key]
    · simp [bl, idm_apply, Pi.single_eq_of_ne hl]
  have hZ : Chain.DiagZero (p := W.p) Xf Ad := by
    intro _ _ h hh c hc hzero i
    obtain ⟨c₀, hc₀⟩ := hscal h hh
    have hcc := hc₀ c
    have : bl h c c = 0 := by simp [bl, hzero]
    rw [this] at hcc
    have hnt := hadm c hc
    obtain ⟨y, hy⟩ := exists_ne (0 : (W.L.obj S).obj c)
    have hy' := congrArg (fun φ ↦ φ (Pi.single c y) c) hcc
    simp only [LinearMap.zero_apply, Pi.zero_apply, LinearMap.smul_apply, idm_apply,
      Pi.single_eq_same, Pi.smul_apply] at hy'
    have hc0 : c₀ = 0 := by
      by_contra hne'
      exact hy ((smul_eq_zero.1 hy'.symm).resolve_left hne')
    rw [hc₀ i, hc0, zero_smul]
  have hC : Chain.ColAdm W.B Xf Ad := fun _ _ κ ↦ hcol κ
  -- idempotents are trivial
  refine ⟨?_, fun N N' hc ↦ ?_⟩
  · obtain ⟨c, hc⟩ := hne
    have := hadm c hc
    obtain ⟨y, hy⟩ := exists_ne (0 : (W.L.obj S).obj c)
    refine ⟨⟨(Pi.single c y : W.Carrier S), 0, fun h ↦ hy ?_⟩⟩
    have := congrFun h c
    simp only [Pi.single_eq_same] at this
    exact this
  let e : W.obj S ⟶ W.obj S := ModuleCat.ofHom (N.subtype ∘ₗ Submodule.projectionOnto N N' hc)
  have hidem : ∀ y, (N.subtype ∘ₗ Submodule.projectionOnto N N' hc)
      ((N.subtype ∘ₗ Submodule.projectionOnto N N' hc) y) =
        (N.subtype ∘ₗ Submodule.projectionOnto N N' hc) y := by
    intro y
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Submodule.projectionOnto_apply_left]
  have he : e ≫ e = e := by
    ext x
    exact hidem x
  set t := W.toTot e
  have ht : BlockEqs W.p t := W.blockEqs_toTot e
  have htt : t ∘ₗ t = t := by rw [← toTot_comp, he]
  obtain ⟨c₀, hc₀⟩ := hscal t ht
  have hmul := Chain.bl_comp_self W.B W.locInj hZ hC (o := ()) (o' := ()) (o'' := ()) ht ht
  obtain ⟨c, hcA⟩ := hne
  have hsq : c₀ * c₀ = c₀ := by
    have h1 := hmul c
    rw [htt, hc₀ c, LinearMap.smul_comp, LinearMap.comp_smul, idm_idm, smul_smul] at h1
    have := hadm c hcA
    obtain ⟨y, hy⟩ := exists_ne (0 : (W.L.obj S).obj c)
    have h2 := congrArg (fun φ ↦ φ (Pi.single c y) c) h1
    simp only [LinearMap.smul_apply, idm_apply, Pi.single_eq_same, Pi.smul_apply] at h2
    exact (smul_left_injective k hy h2).symm
  rcases (IsIdempotentElem.iff_eq_zero_or_one (p := c₀)).1 hsq with h0 | h1
  · -- `e = 0`, so `N = ⊥`
    have hu : t = 0 := W.eq_zero_of_idem hZ hC (o := ()) ht htt (fun i ↦ by rw [hc₀ i, h0, zero_smul])
    left
    refine (Submodule.eq_bot_iff _).2 fun x hx ↦ ?_
    have := LinearMap.congr_fun hu x
    change (N.subtype ∘ₗ Submodule.projectionOnto N N' hc) x = 0 at this
    simpa [Submodule.projectionOnto_apply_left hc ⟨x, hx⟩] using this
  · -- `1 - e = 0`, so `N' = ⊥`
    set u := LinearMap.id - t
    have hu1 : BlockEqs W.p u := (isPdHom_iff W.p _).1
      ⟨fun q ↦ by simp [u, LinearMap.sub_comp, LinearMap.comp_sub, ((isPdHom_iff W.p t).2 ht).1 q],
       fun c' ↦ by simp [u, LinearMap.sub_comp, LinearMap.comp_sub, ((isPdHom_iff W.p t).2 ht).2 c']⟩
    have hu2 : u ∘ₗ u = u := by
      simp only [u, LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp, LinearMap.comp_id, htt]
      abel
    have hu3 : ∀ i, bl u i i = 0 := fun i ↦ by
      simp only [u, bl, LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp]
      rw [show (W.L.obj S).idm i ∘ₗ t ∘ₗ (W.L.obj S).idm i = bl t i i from rfl, hc₀ i, h1, one_smul,
        idm_idm, sub_self]
    have hu : u = 0 := W.eq_zero_of_idem hZ hC (o := ()) hu1 hu2 hu3
    right
    refine (Submodule.eq_bot_iff _).2 fun x hx ↦ ?_
    have := LinearMap.congr_fun hu x
    change x - (N.subtype ∘ₗ Submodule.projectionOnto N N' hc) x = 0 at this
    simpa [Submodule.projectionOnto_apply_right hc ⟨x, hx⟩] using this

end PdData

variable (k A) in
/-- Push-down data with the two facts about `S₋` used in Theorem 5.2: `F(S₋)` is
indecomposable and not isomorphic to `F(T)` for `T ∈ C_fin`. They hold when `F`
is a representation embedding on `D_fin`. -/
structure PdDatum extends PdData k A where
  indecS : IsIndecomposable A (toPdData.functor.obj Extension.Sminus)
  notIsoS : ∀ X : Dfin k, InC X.obj →
    IsEmpty (toPdData.functor.obj Extension.Sminus ≅ toPdData.functor.obj ((DfinToD k).obj X))

/-- A push-down construction gives the data of Theorem 5.2. -/
def PdDatum.embeddingData (W : PdDatum k A) : EmbeddingData k A where
  F := W.functor
  exact := W.isExact
  fin := W.finite
  comparison := W.comparison
  R := W.retractions
  n := Fintype.card W.D.V
  bound := W.nilpotentBound
  indecS := W.indecS
  notIsoS := W.notIsoS

end PushDown

end LargeIndecomposable
