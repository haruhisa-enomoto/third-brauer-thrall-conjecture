module

public import LargeIndecomposable.MultiplicativeBases.Normed.A0Normed
public import LargeIndecomposable.StandardForm.ProjectiveAlgebra.A0Graded
public import LargeIndecomposable.MeshCategories.Basic.GradedLocal
public import LargeIndecomposable.StandardForm.Deformations.FilteredNormalForm
public import LargeIndecomposable.StandardForm.Main.StandardAlgebras

/-!
# The converse of Corollary 4.15: `A ≅ A₀` implies that `A` is standard

"Conversely an isomorphism `A ≅ A₀` gives an equivalence
`F : ind(mod A) → C`, possibly permuting labels. Since `C` is generated in degree one with
homogeneous relations, `gr_J C = C`. Thus `gr F` is a graded automorphism of `C` with the same
permutation. Applying `(gr F)⁻¹` after `F` gives the required object-preserving equivalence."

An isomorphism `ψ : A ≅ A₀` makes the evaluated modules `M_x` of `C = k(Γ_A)` into
indecomposable `A`-modules, which identifies `C` with `ind(mod A)` up to a permutation `σ` of the
labels (`Φ`). Under `Φ` the radical powers of `ind(mod A)` are the morphisms of degree at least
`m` of `C` (`gr_J C = C`, `MeshRadical`). Deviation: instead of correcting `F` by `(gr F)⁻¹`, the
degree-one parts of the arrow representatives are taken as lifts; their mesh errors are of degree
two and lie in `J³`, so they vanish, and the filtered normal form (`Lifts.functor`) gives the
object-preserving equivalence (`isStandard_of_algEquiv`).

## References

* *Multiplicative bases and deformations of representation-finite algebras*, <https://github.com/haruhisa-enomoto/multiplicative-bases-deformations>. Numbered statements cited here refer to it.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace LargeIndecomposable.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- The algebra `A₀` of `A`. -/
abbrev A0 := (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ

section Generic

variable {S b} {B : Type w} [Ring B] [Algebra k B] (ψ : B ≃ₐ[k] S.A0 b)

/-- `Bᵐᵒᵖ ≅ Alg F₀`. -/
def eOp : Bᵐᵒᵖ ≃+* CatAlg.Alg (S.arMeshData b).F0 where
  toFun a := (ψ a.unop).unop
  invFun x := MulOpposite.op (ψ.symm (MulOpposite.op x))
  left_inv a := by simp
  right_inv x := by simp
  map_mul' a c := by simp
  map_add' a c := by simp

theorem eOp_algebraMap (t : k) : eOp ψ (algebraMap k Bᵐᵒᵖ t) = algebraMap k _ t := by
  change (ψ (algebraMap k B t)).unop = _
  rw [ψ.commutes]
  rfl

variable (S b) in
/-- The evaluation `C → mod A₀`. -/
def ev : S.ARMeshCategory b ⥤ ModuleCat.{w} (CatAlg.Alg (S.arMeshData b).F0) where
  obj X := ModuleCat.of _ (CatAlg.Rep (S.arMeshData b).F0 X)
  map f := ModuleCat.ofHom (CatAlg.repMap f)
  map_id X := by ext m y; simp
  map_comp f g := by ext m y; simp

/-- The evaluation `C → mod B` through `ψ`. -/
def evA : S.ARMeshCategory b ⥤ RightModuleCat B :=
  ev S b ⋙ ModuleCat.restrictScalars (eOp ψ).toRingHom

theorem evA_map_apply {X Y : S.ARMeshCategory b} (f : X ⟶ Y)
    (m : CatAlg.Rep (S.arMeshData b).F0 X) :
    ((evA ψ).map f).hom m = CatAlg.repMap f m := rfl

/-- The `k`-action on an evaluated `A`-module is the natural one. -/
theorem evA_smul {X : S.ARMeshCategory b} (t : k) (m : CatAlg.Rep (S.arMeshData b).F0 X) :
    (t • (show (evA ψ).obj X from m) : (evA ψ).obj X) =
      (t • m : CatAlg.Rep (S.arMeshData b).F0 X) := by
  change (eOp ψ (algebraMap k Bᵐᵒᵖ t)) • m = _
  rw [eOp_algebraMap, algebraMap_smul]

theorem evA_map_add {X Y : S.ARMeshCategory b} (f g : X ⟶ Y) :
    (evA ψ).map (f + g) = (evA ψ).map f + (evA ψ).map g := by
  ext m
  change CatAlg.repMap (f + g) m = CatAlg.repMap f m + CatAlg.repMap g m
  rw [CatAlg.repMap_add]; rfl

theorem evA_map_sub {X Y : S.ARMeshCategory b} (f g : X ⟶ Y) :
    (evA ψ).map (f - g) = (evA ψ).map f - (evA ψ).map g := by
  rw [eq_sub_iff_add_eq, ← evA_map_add, sub_add_cancel]

theorem evA_map_smul {X Y : S.ARMeshCategory b} (t : k) (f : X ⟶ Y) :
    (evA ψ).map (t • f) = t • (evA ψ).map f := by
  ext m
  change CatAlg.repMap (t • f) m = (t • (show (evA ψ).obj Y from CatAlg.repMap f m) : (evA ψ).obj Y)
  rw [evA_smul, CatAlg.repMap_smul_apply]

theorem evA_map_injective (x y : S.ARVertex) :
    Function.Injective fun f : S.meshObj b x ⟶ S.meshObj b y ↦ (evA ψ).map f := by
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k (S.meshObj b x ⟶ S.meshObj b y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  intro f g h
  rw [← sub_eq_zero]
  refine (S.arMeshData b).repMap_eq_zero x y (f - g) fun m ↦ ?_
  have := congrArg (fun φ ↦ φ.hom m) h
  simp only [evA_map_apply] at this
  have e : CatAlg.repMap (F := (S.arMeshData b).F0) (f - g) m =
      CatAlg.repMap f m - CatAlg.repMap g m := by
    ext z; simp [Preadditive.comp_sub]
  rw [e, this, sub_self]

theorem evA_map_surjective (x y : S.ARVertex)
    (g : (evA ψ).obj (S.meshObj b x) ⟶ (evA ψ).obj (S.meshObj b y)) :
    ∃ f : S.meshObj b x ⟶ S.meshObj b y, (evA ψ).map f = g := by
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k (S.meshObj b x ⟶ S.meshObj b y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  let gl : CatAlg.Rep (S.arMeshData b).F0 (S.meshObj b x) →ₗ[CatAlg.Alg (S.arMeshData b).F0]
      CatAlg.Rep (S.arMeshData b).F0 (S.meshObj b y) :=
    { toFun := g.hom
      map_add' := map_add g.hom
      map_smul' := fun a m ↦ by
        obtain ⟨a', rfl⟩ := (eOp ψ).surjective a
        exact g.hom.map_smul a' m }
  obtain ⟨f, hf⟩ := (S.arMeshData b).hom_eq_repMap x y gl
  exact ⟨f, by ext m; exact (hf m).symm⟩

/-! ### The comparison with a skeleton -/

section Comparison

variable (S' : IndSkeleton k B) (σ : S.ARVertex → Fin S'.n)
  (θ : ∀ x : S.ARVertex, (evA ψ).obj (S.meshObj b x) ≅ S'.obj (σ x))

/-- The comparison `C(x, y) → ind(mod A)(σ x, σ y)`. -/
def Φm {x y : S.ARVertex} (f : S.meshObj b x ⟶ S.meshObj b y) :
    (S'.ind (σ x) : S'.Ind) ⟶ S'.ind (σ y) :=
  InducedCategory.homMk ((θ x).inv ≫ (evA ψ).map f ≫ (θ y).hom)

theorem Φm_hom {x y : S.ARVertex} (f : S.meshObj b x ⟶ S.meshObj b y) :
    (Φm ψ S' σ θ f).hom = (θ x).inv ≫ (evA ψ).map f ≫ (θ y).hom := rfl

theorem Φm_comp {x y z : S.ARVertex} (f : S.meshObj b x ⟶ S.meshObj b y)
    (g : S.meshObj b y ⟶ S.meshObj b z) : Φm ψ S' σ θ (f ≫ g) = Φm ψ S' σ θ f ≫ Φm ψ S' σ θ g := by
  ext1
  simp only [Φm_hom, InducedCategory.comp_hom, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc]

theorem Φm_id (x : S.ARVertex) : Φm ψ S' σ θ (𝟙 (S.meshObj b x)) = 𝟙 _ := by
  ext1
  simp [Φm_hom]
  rfl

theorem Φm_add {x y : S.ARVertex} (f g : S.meshObj b x ⟶ S.meshObj b y) :
    Φm ψ S' σ θ (f + g) = Φm ψ S' σ θ f + Φm ψ S' σ θ g := by
  ext1
  simp only [Φm_hom, evA_map_add, Preadditive.add_comp, Preadditive.comp_add]
  rfl

theorem Φm_sub {x y : S.ARVertex} (f g : S.meshObj b x ⟶ S.meshObj b y) :
    Φm ψ S' σ θ (f - g) = Φm ψ S' σ θ f - Φm ψ S' σ θ g := by
  ext1
  simp only [Φm_hom, evA_map_sub, Preadditive.sub_comp, Preadditive.comp_sub]
  rfl

theorem Φm_smul {x y : S.ARVertex} (t : k) (f : S.meshObj b x ⟶ S.meshObj b y) :
    Φm ψ S' σ θ (t • f) = t • Φm ψ S' σ θ f := by
  ext1
  simp only [Φm_hom, evA_map_smul, Linear.smul_comp, Linear.comp_smul]
  rfl

theorem Φm_zero {x y : S.ARVertex} : Φm ψ S' σ θ (0 : S.meshObj b x ⟶ S.meshObj b y) = 0 := by
  have := Φm_sub ψ S' σ θ (0 : S.meshObj b x ⟶ S.meshObj b y) 0
  rwa [sub_self, sub_self] at this

theorem Φm_sum {x y : S.ARVertex} {ι : Type*} (s : Finset ι) (f : ι → (S.meshObj b x ⟶ S.meshObj b y)) :
    Φm ψ S' σ θ (∑ i ∈ s, f i) = ∑ i ∈ s, Φm ψ S' σ θ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Φm_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Φm_add, ih]

theorem Φm_injective {x y : S.ARVertex} :
    Function.Injective (Φm ψ S' σ θ : (S.meshObj b x ⟶ S.meshObj b y) → _) := by
  intro f g h
  apply evA_map_injective ψ x y
  have := congrArg InducedCategory.Hom.hom h
  simp only [Φm_hom] at this
  have := congrArg (fun u ↦ (θ x).hom ≫ u ≫ (θ y).inv) this
  simpa using this

theorem Φm_surjective {x y : S.ARVertex} (h : (S'.ind (σ x) : S'.Ind) ⟶ S'.ind (σ y)) :
    ∃ f : S.meshObj b x ⟶ S.meshObj b y, Φm ψ S' σ θ f = h := by
  obtain ⟨f, hf⟩ := evA_map_surjective ψ x y ((θ x).hom ≫ h.hom ≫ (θ y).inv)
  refine ⟨f, ?_⟩
  ext1
  rw [Φm_hom, hf]
  simp

theorem isIso_Φm_iff {x : S.ARVertex} (f : S.meshObj b x ⟶ S.meshObj b x) :
    IsIso (Φm ψ S' σ θ f) ↔ IsIso f := by
  constructor
  · intro hi
    obtain ⟨g, hg⟩ := Φm_surjective ψ S' σ θ (inv (Φm ψ S' σ θ f))
    refine ⟨g, Φm_injective ψ S' σ θ ?_, Φm_injective ψ S' σ θ ?_⟩
    · rw [Φm_comp, hg, IsIso.hom_inv_id, Φm_id]
    · rw [Φm_comp, hg, IsIso.inv_hom_id, Φm_id]
  · intro hi
    refine ⟨Φm ψ S' σ θ (inv f), ?_, ?_⟩
    · rw [← Φm_comp, IsIso.hom_inv_id, Φm_id]
    · rw [← Φm_comp, IsIso.inv_hom_id, Φm_id]

variable [Finite S.ARVertex]



/-! ### Radical powers are degrees -/

theorem path_first {V : Type} [Quiver.{0} V] {x y : V} (p : Quiver.Path x y) (hp : 0 < p.length) :
    ∃ (z : V) (a : x ⟶ z) (p' : Quiver.Path z y), p = a.toPath.comp p' ∧ p'.length + 1 = p.length := by
  induction p with
  | nil => simp at hp
  | cons q a ih =>
    by_cases hq : q.length = 0
    · obtain rfl := Quiver.Path.eq_of_length_zero q hq
      cases Quiver.Path.eq_nil_of_length_zero q hq
      exact ⟨_, a, Quiver.Path.nil, rfl, by simp⟩
    · obtain ⟨z, a', p', rfl, hl⟩ := ih (by omega)
      exact ⟨z, a', p'.cons a, by rw [Quiver.Path.comp_cons], by simp [hl]⟩

end Comparison

end Generic

/-! ### The relabelling of `ind(mod A)` -/

section Relabel

variable {S b} (ψ : A ≃ₐ[k] S.A0 b)

variable [Finite S.ARVertex]

/-! ### Degree-one lifts and standardness -/

end Relabel

end LargeIndecomposable.IndSkeleton
