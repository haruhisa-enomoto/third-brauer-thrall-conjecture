module

public import LargeIndecomposable.RepresentationEmbeddings.WalkConstruction.PdControl
public import LargeIndecomposable.KroneckerModules.Subcategories
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Morphisms vanishing at one vertex (Lemma 4.2)

Let `L : K_fin → Rep D` be a functor from finite-dimensional Kronecker modules
to representations of a finite quiver, sending short exact sequences to
vertexwise short exact sequences, such that every vertex lies in the support
of `L(S₊)` or of `L(S₋)`. If `φ : T → U` is a morphism of `D_fin` with
`T ∈ C` and `L(φ)` vanishes at some vertex, then `φ = 0`.

This is the part of Lemma 4.2 used in Proposition 4.4. Instead of the natural
identifications `L(T)(x) ≅ L(S₊)(x) ⊗ V` we argue with the quotient
`T → (V, 0)` and the subobject `(0, W) → U`: at a vertex in the support of
`L(S₊)`, a nonzero `φ` gives a map `T → S₊` whose image under `L` is
surjective there, and dually at a vertex in the support of `L(S₋)`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair

universe u

variable {k : Type u} [Field k]

/-- Finite-dimensional Kronecker modules. -/
abbrev InKfin : ObjectProperty (Kron k) := fun X ↦ X.IsFiniteDimensional

variable (k) in
/-- The category of finite-dimensional Kronecker modules. -/
abbrev Kfin : Type (u + 1) := (InKfin (k := k)).FullSubcategory

lemma inDfin_le_inKfin : InDfin (k := k) ≤ InKfin := fun _ h ↦ h.2

variable (k) in
/-- The inclusion `D_fin → K_fin`. -/
abbrev DfinToKfin : Dfin k ⥤ Kfin k := ObjectProperty.ιOfLE inDfin_le_inKfin

namespace Covering

/-- `L` sends short exact sequences of `K_fin` to vertexwise short exact
sequences. -/
def ExactOnKfin {D : FinQuiver} (L : Kfin k ⥤ Rep k D) : Prop :=
  ∀ (X Y Z : Kfin k) (f : X ⟶ Y) (g : Y ⟶ Z), Kron.IsShortExact f.hom g.hom → ∀ i : D.V,
    Function.Injective ((L.map f).app i).hom ∧ Function.Surjective ((L.map g).app i).hom ∧
      LinearMap.range ((L.map f).app i).hom = LinearMap.ker ((L.map g).app i).hom

variable (k) in
/-- `S₊` in `K_fin`. -/
def SplusK : Kfin k :=
  ⟨Kron.Splus k, ⟨by change FiniteDimensional k k; infer_instance,
    by change FiniteDimensional k PUnit; infer_instance⟩⟩

variable (k) in
/-- `S₋` in `K_fin`. -/
def SminusK : Kfin k :=
  ⟨Kron.Sminus k, ⟨by change FiniteDimensional k PUnit; infer_instance,
    by change FiniteDimensional k k; infer_instance⟩⟩

/-- The quotient `(V, 0)` of `X = (V, W; a, b)`. -/
def topK (X : Kfin k) : Kfin k :=
  ⟨Kron.mk X.obj.V (ModuleCat.of k PUnit.{u + 1}) 0 0,
    ⟨X.2.1, by change FiniteDimensional k PUnit; infer_instance⟩⟩

/-- The subobject `(0, W)` of `X = (V, W; a, b)`. -/
def socK (X : Kfin k) : Kfin k :=
  ⟨Kron.mk (ModuleCat.of k PUnit.{u + 1}) X.obj.W 0 0,
    ⟨by change FiniteDimensional k PUnit; infer_instance, X.2.2⟩⟩

lemma hom_ext_punit {M : ModuleCat.{u} k} (f g : M ⟶ ModuleCat.of k PUnit.{u + 1}) : f = g :=
  ModuleCat.hom_ext (LinearMap.ext fun _ ↦ Subsingleton.elim _ _)

lemma hom_ext_punit' {M : ModuleCat.{u} k} (f g : ModuleCat.of k PUnit.{u + 1} ⟶ M) : f = g :=
  ModuleCat.hom_ext (LinearMap.ext fun x ↦ by
    rw [show x = 0 from Subsingleton.elim _ _, map_zero, map_zero])

/-- The quotient map `X → (V, 0)`. -/
def toTop (X : Kfin k) : X ⟶ topK X :=
  ObjectProperty.homMk (Kron.homMk (𝟙 _) 0 (hom_ext_punit _ _) (hom_ext_punit _ _))

/-- The inclusion `(0, W) → X`. -/
def fromSoc (X : Kfin k) : socK X ⟶ X :=
  ObjectProperty.homMk (Kron.homMk 0 (𝟙 _) (hom_ext_punit' _ _) (hom_ext_punit' _ _))

/-- The kernel `(0, W) → X → (V, 0)` is a short exact sequence. -/
lemma isShortExact_soc_top (X : Kfin k) : Kron.IsShortExact (fromSoc X).hom (toTop X).hom := by
  intro j
  cases j
  · refine ⟨fun a b _ ↦ Subsingleton.elim (α := PUnit) a b, fun v ↦ ⟨v, rfl⟩, ?_⟩
    change LinearMap.range (0 : PUnit →ₗ[k] X.obj.V) = LinearMap.ker (LinearMap.id)
    rw [LinearMap.range_zero, LinearMap.ker_id]
  · refine ⟨fun _ _ h ↦ h, fun y ↦ ⟨0, Subsingleton.elim (α := PUnit) _ y⟩, ?_⟩
    change LinearMap.range (LinearMap.id) = LinearMap.ker (0 : X.obj.W →ₗ[k] PUnit)
    rw [LinearMap.range_id, LinearMap.ker_zero]

variable {D : FinQuiver} (L : Kfin k ⥤ Rep k D) (hex : ExactOnKfin L)

include hex in
/-- At a vertex in the support of `L(S₊)`, a morphism `φ` of `D_fin` with
`T ∈ C` and `L(φ) = 0` there is zero. -/
lemma eq_zero_of_splus {T U : Dfin k} (hT : InC T.obj) (φ : T ⟶ U) (c : D.V)
    (hc : Nontrivial ((L.obj (SplusK k)).obj c))
    (h : (L.map ((DfinToKfin k).map φ)).app c = 0) : φ = 0 := by
  by_contra hφ
  have hg : φ.hom.app zero ≠ 0 := fun h0 ↦ hφ (by ext1; exact hom_eq_zero_of_app_zero hT _ h0)
  obtain ⟨v, hv⟩ : ∃ v, (φ.hom.app zero).hom v ≠ 0 := by
    by_contra hall; push Not at hall
    exact hg (ModuleCat.hom_ext (LinearMap.ext hall))
  obtain ⟨lam, hlam⟩ := Module.Projective.exists_dual_eq_one k hv
  set T' := (DfinToKfin k).obj T
  set U' := (DfinToKfin k).obj U
  -- `q : U → S₊`
  let q : U' ⟶ SplusK k := ObjectProperty.homMk (Kron.homMk (ModuleCat.ofHom lam) 0
    (hom_ext_punit _ _) (hom_ext_punit _ _))
  -- `μ : (V_T, 0) → S₊` and its section `s`
  let μ : topK T' ⟶ SplusK k := ObjectProperty.homMk (Kron.homMk
    (ModuleCat.ofHom (lam ∘ₗ (φ.hom.app zero).hom)) 0 (hom_ext_punit _ _) (hom_ext_punit _ _))
  let s : SplusK k ⟶ topK T' := ObjectProperty.homMk (Kron.homMk
    (ModuleCat.ofHom (LinearMap.toSpanSingleton k _ v)) 0 (hom_ext_punit _ _) (hom_ext_punit _ _))
  have hsμ : s ≫ μ = 𝟙 _ := by
    ext1
    refine Kron.hom_ext (ModuleCat.hom_ext (LinearMap.ext fun (r : k) ↦ ?_)) (hom_ext_punit _ _)
    change lam ((φ.hom.app zero).hom (r • v)) = r
    rw [map_smul, map_smul, hlam, smul_eq_mul, mul_one]
  have hψ : (DfinToKfin k).map φ ≫ q = toTop T' ≫ μ := by
    ext1
    refine Kron.hom_ext ?_ (hom_ext_punit _ _)
    rfl
  -- `L(μ)` is surjective at `c`, and so is `L(T → (V, 0))`
  have hμ : Function.Surjective ((L.map μ).app c).hom := by
    intro y
    refine ⟨((L.map s).app c).hom y, ?_⟩
    have := congrArg (fun f ↦ (f.app c).hom y) (L.map_comp s μ)
    simp only [hsμ, CategoryTheory.Functor.map_id] at this
    exact this.symm
  have ht : Function.Surjective ((L.map (toTop T')).app c).hom :=
    (hex _ _ _ _ _ (isShortExact_soc_top T') c).2.1
  obtain ⟨y, hy⟩ := exists_ne (0 : (L.obj (SplusK k)).obj c)
  obtain ⟨x, rfl⟩ := hμ y
  obtain ⟨z, rfl⟩ := ht x
  apply hy
  have := congrArg (fun f ↦ (f.app c).hom z) (congrArg L.map hψ)
  simp only [CategoryTheory.Functor.map_comp, Rep.comp_app] at this
  change ((L.map q).app c).hom (((L.map ((DfinToKfin k).map φ)).app c).hom z) =
    ((L.map μ).app c).hom (((L.map (toTop T')).app c).hom z) at this
  rw [← this, h]
  simp

include hex in
/-- At a vertex in the support of `L(S₋)`, a morphism `φ` of `D_fin` with
`L(φ) = 0` there is zero. -/
lemma eq_zero_of_sminus {T U : Dfin k} (φ : T ⟶ U) (c : D.V)
    (hc : Nontrivial ((L.obj (SminusK k)).obj c))
    (h : (L.map ((DfinToKfin k).map φ)).app c = 0) : φ = 0 := by
  by_contra hφ
  have hg : φ.hom.app one ≠ 0 := fun h0 ↦ hφ (by ext1; exact hom_eq_zero_of_app_one U.2.1 _ h0)
  obtain ⟨w, hw⟩ : ∃ w, (φ.hom.app one).hom w ≠ 0 := by
    by_contra hall; push Not at hall
    exact hg (ModuleCat.hom_ext (LinearMap.ext hall))
  obtain ⟨lam, hlam⟩ := Module.Projective.exists_dual_eq_one k hw
  set T' := (DfinToKfin k).obj T
  set U' := (DfinToKfin k).obj U
  -- `j : S₋ → T`
  let j : SminusK k ⟶ T' := ObjectProperty.homMk (Kron.homMk 0
    (ModuleCat.ofHom (LinearMap.toSpanSingleton k _ w)) (hom_ext_punit' _ _) (hom_ext_punit' _ _))
  -- `ν : S₋ → (0, W_U)` and its retraction `r`
  let ν : SminusK k ⟶ socK U' := ObjectProperty.homMk (Kron.homMk 0
    (ModuleCat.ofHom (LinearMap.toSpanSingleton k _ ((φ.hom.app one).hom w)))
    (hom_ext_punit' _ _) (hom_ext_punit' _ _))
  let r : socK U' ⟶ SminusK k := ObjectProperty.homMk (Kron.homMk 0 (ModuleCat.ofHom lam)
    (hom_ext_punit' _ _) (hom_ext_punit' _ _))
  have hνr : ν ≫ r = 𝟙 _ := by
    ext1
    refine Kron.hom_ext (hom_ext_punit' _ _) (ModuleCat.hom_ext (LinearMap.ext fun (t : k) ↦ ?_))
    change lam (t • (φ.hom.app one).hom w) = t
    rw [map_smul, hlam, smul_eq_mul, mul_one]
  have hχ : j ≫ (DfinToKfin k).map φ = ν ≫ fromSoc U' := by
    ext1
    refine Kron.hom_ext (hom_ext_punit' _ _) (ModuleCat.hom_ext (LinearMap.ext fun (t : k) ↦ ?_))
    change (φ.hom.app one).hom (t • w) = t • (φ.hom.app one).hom w
    rw [map_smul]
  -- `L(ν)` is injective at `c`, and so is `L((0, W) → U)`
  have hid : ∀ z, ((L.map r).app c).hom (((L.map ν).app c).hom z) = z := by
    intro z
    have := congrArg (fun f ↦ (f.app c).hom z) (L.map_comp ν r)
    simp only [hνr, CategoryTheory.Functor.map_id] at this
    exact this.symm
  have hν : Function.Injective ((L.map ν).app c).hom := by
    intro x y hxy
    rw [← hid x, ← hid y, hxy]
  have hs : Function.Injective ((L.map (fromSoc U')).app c).hom :=
    (hex _ _ _ _ _ (isShortExact_soc_top U') c).1
  obtain ⟨y, hy⟩ := exists_ne (0 : (L.obj (SminusK k)).obj c)
  apply hy
  apply hν
  apply hs
  have := congrArg (fun f ↦ (f.app c).hom y) (congrArg L.map hχ)
  simp only [CategoryTheory.Functor.map_comp, Rep.comp_app] at this
  change ((L.map ((DfinToKfin k).map φ)).app c).hom (((L.map j).app c).hom y) =
    ((L.map (fromSoc U')).app c).hom (((L.map ν).app c).hom y) at this
  rw [← this, h]
  simp

include hex in
/-- Lemma 4.2, in the form used by Proposition 4.4. -/
theorem zeroAtVertex
    (hsupp : ∀ c, Nontrivial ((L.obj (SplusK k)).obj c) ∨ Nontrivial ((L.obj (SminusK k)).obj c)) :
    PushDown.ZeroAtVertex (DfinToKfin k ⋙ L) := by
  intro T U hT φ c h
  rcases hsupp c with hc | hc
  · exact eq_zero_of_splus L hex hT φ c hc h
  · exact eq_zero_of_sminus L hex φ c hc h

end Covering

end LargeIndecomposable
