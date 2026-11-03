module

public import LargeIndecomposable.RepresentationEmbeddings.ColimitExtension.Colimit
public import LargeIndecomposable.RepresentationEmbeddings.ColimitExtension.Preserves

/-!
# The colimit comparison

For a functor `G : D → Mod A`, the comparison (3.4) of the manuscript says that
`G(T)` is the filtered colimit of the modules `G(U)` over the finite-dimensional
subrepresentations `U ⊆ T`:
`G(T) ≅ colim_{U ⊆ T, dim U < ∞} G(U)`.

The manuscript obtains this from the fact that its three functors commute with
filtered colimits. Here we argue in the other direction. The comparison is
checked on elements (`isComparison_of_elements`): every element of `G(T)` comes
from some `G(U)`, and an element of `G(U)` that vanishes in `G(T)` already
vanishes in `G(U')` for a larger finite-dimensional `U'`. The comparison
identifies `G` with the extension of its restriction to `D_fin` by filtered
colimits (`isoExtension`), so `G` commutes with filtered colimits and arbitrary
direct sums when it is exact, and preserves the dimension of
infinite-dimensional modules when it is faithful with finite-dimensional values
on `D_fin`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A]

variable (k) in
/-- The inclusion `D_fin → D`. -/
abbrev DfinToD : Dfin k ⥤ D k := ObjectProperty.ιOfLE (fun _ h ↦ h.1)

instance : (DfinToD k).Faithful := inferInstance

instance : (DfinToD k).Additive where
  map_add := rfl

instance : (DfinToD k).Linear k where
  map_smul _ _ := rfl

/-- Exactness of a functor on short exact sequences in `D`. -/
def IsExactOnD (G : D k ⥤ ModuleCat.{u} A) : Prop :=
  ∀ (X Y Z : D k) (f : X ⟶ Y) (g : Y ⟶ Z), Kron.IsShortExact f.hom g.hom →
    Function.Injective (G.map f).hom ∧ Function.Surjective (G.map g).hom ∧
      LinearMap.range (G.map f).hom = LinearMap.ker (G.map g).hom

namespace Comparison

variable (G : D k ⥤ ModuleCat.{u} A)

/-- The restriction of `G` to `D_fin`. -/
abbrev fin : Dfin k ⥤ ModuleCat.{u} A := DfinToD k ⋙ G

lemma isExactOnDfin {G : D k ⥤ ModuleCat.{u} A} (hG : IsExactOnD G) :
    IsExactOnDfin (fin G) :=
  fun X Y Z f g h ↦ hG _ _ _ ((DfinToD k).map f) ((DfinToD k).map g) h

/-- The inclusion of a finite-dimensional subrepresentation `U ⊆ X`, in `D`. -/
def incl (X : D k) (U : Kron.FinSub X.obj) :
    (DfinToD k).obj ((Extension.finDiagram X).obj U) ⟶ X :=
  ObjectProperty.homMk (Kron.Sub.ι U.1)

@[reassoc (attr := simp)]
lemma map_incl (X : D k) {U U' : Kron.FinSub X.obj} (h : U ⟶ U') :
    (DfinToD k).map ((Extension.finDiagram X).map h) ≫ incl X U' = incl X U := by
  ext1; exact Kron.Sub.homOfLE_ι (leOfHom h)

@[reassoc]
lemma incl_comp {X Y : D k} (f : X ⟶ Y) (U : Kron.FinSub X.obj) (U' : Kron.FinSub Y.obj)
    (h : U.1.map f.hom ≤ U'.1) :
    incl X U ≫ f = (DfinToD k).map (Extension.restrict f U U' h) ≫ incl Y U' := by
  ext1; exact (Kron.Sub.restrict_ι f.hom U.1 U'.1 h).symm

/-- The comparison cocone `G(U) → G(X)`. -/
def cocone (X : D k) : Cocone (Extension.diag (fin G) X) where
  pt := G.obj X
  ι :=
    { app U := G.map (incl X U)
      naturality U U' h := by
        change G.map ((DfinToD k).map ((Extension.finDiagram X).map h)) ≫ G.map (incl X U') =
          G.map (incl X U) ≫ 𝟙 _
        rw [← G.map_comp, map_incl, Category.comp_id] }

/-- The colimit comparison (3.4): `G(X)` is the colimit of `G(U)` over the
finite-dimensional subrepresentations `U ⊆ X`. -/
abbrev IsComparison : Prop := ∀ X : D k, Nonempty (IsColimit (cocone G X))

/-- The comparison holds if every element of `G(X)` comes from some `G(U)`,
and an element of `G(U)` vanishing in `G(X)` vanishes in some `G(U')`,
`U ⊆ U'`. -/
theorem isComparison_of_elements
    (h₁ : ∀ (X : D k) (x : G.obj X), ∃ (U : Kron.FinSub X.obj)
      (y : (fin G).obj ((Extension.finDiagram X).obj U)), (G.map (incl X U)).hom y = x)
    (h₂ : ∀ (X : D k) (U : Kron.FinSub X.obj) (y : (fin G).obj ((Extension.finDiagram X).obj U)),
      (G.map (incl X U)).hom y = 0 → ∃ (U' : Kron.FinSub X.obj) (h : U ≤ U'),
        ((Extension.diag (fin G) X).map (homOfLE h)).hom y = 0) :
    IsComparison G := by
  intro X
  let φ := colimit.desc (Extension.diag (fin G) X) (cocone G X)
  have hφ : ∀ U y, φ.hom ((colimit.ι (Extension.diag (fin G) X) U).hom y) =
      (G.map (incl X U)).hom y := fun U y ↦ by
    rw [← ModuleCat.comp_apply, colimit.ι_desc]; rfl
  suffices h : IsIso φ by
    have : IsIso ((colimit.isColimit (Extension.diag (fin G) X)).desc (cocone G X)) := h
    exact ⟨IsColimit.ofPointIso (colimit.isColimit _)⟩
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨?_, fun x ↦ ?_⟩
  · change Function.Injective φ.hom
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨U, y, rfl⟩ := Concrete.colimit_exists_rep _ x
    obtain ⟨U', h, hy⟩ := h₂ X U y ((hφ U y).symm.trans hx)
    have e := congrArg (fun m ↦ m.hom y) (colimit.w (Extension.diag (fin G) X) (homOfLE h))
    change ((colimit.ι (Extension.diag (fin G) X) U').hom
      (((Extension.diag (fin G) X).map (homOfLE h)).hom y)) =
        (colimit.ι (Extension.diag (fin G) X) U).hom y at e
    rw [← e, hy, map_zero]
  · obtain ⟨U, y, rfl⟩ := h₁ X x
    exact ⟨(colimit.ι (Extension.diag (fin G) X) U).hom y, hφ U y⟩

variable {G}

/-- The component `G(X) ≅ colim_U G(U)` of the comparison. -/
def isoApp (hG : IsComparison G) (X : D k) : G.obj X ≅ (Extension.functor (fin G)).obj X :=
  (hG X).some.coconePointUniqueUpToIso (colimit.isColimit _)

@[reassoc (attr := simp)]
lemma incl_isoApp (hG : IsComparison G) (X : D k) (U : Kron.FinSub X.obj) :
    G.map (incl X U) ≫ (isoApp hG X).hom = Extension.ι (fin G) X U :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (hG X).some (colimit.isColimit _) U

/-- The comparison identifies `G` with the extension of its restriction to
`D_fin` by filtered colimits. -/
def isoExtension (hG : IsComparison G) : G ≅ Extension.functor (fin G) :=
  NatIso.ofComponents (isoApp hG) (by
    intro X Y f
    refine (hG X).some.hom_ext fun U ↦ ?_
    change G.map (incl X U) ≫ G.map f ≫ (isoApp hG Y).hom =
      G.map (incl X U) ≫ (isoApp hG X).hom ≫ (Extension.functor (fin G)).map f
    rw [incl_isoApp_assoc, ← G.map_comp_assoc,
      incl_comp f U (Kron.FinSub.map f.hom U) le_rfl, G.map_comp_assoc, incl_isoApp]
    exact (Extension.ι_map (fin G) f U _ le_rfl).symm)

/-! ### Consequences of the comparison -/

/-- A functor satisfying the comparison and exact on `D` commutes with filtered
colimits. -/
theorem preservesFilteredColimits (hG : IsComparison G) (hexact : IsExactOnD G) :
    PreservesFilteredColimitsOfSize.{u, u} G := by
  have h := Extension.preservesFilteredColimits (isExactOnDfin hexact)
  exact ⟨fun J _ _ ↦
    haveI := h.preserves_filtered_colimits J
    preservesColimitsOfShape_of_natIso (isoExtension hG).symm⟩

/-- A functor satisfying the comparison, additive and exact on `D` commutes
with arbitrary direct sums. -/
theorem preservesCoproducts [G.Additive] (hG : IsComparison G) (hexact : IsExactOnD G)
    (ι : Type u) : PreservesColimitsOfShape (Discrete ι) G := by
  have := Extension.preservesCoproducts (isExactOnDfin hexact) ι
  exact preservesColimitsOfShape_of_natIso (isoExtension hG).symm

/-- An isomorphism of `A`-modules is `k`-linear on the restricted scalars. -/
def restrictScalarsEquiv [Algebra k A] {M N : ModuleCat.{u} A} (e : M ≅ N) :
    RestrictScalars k A M ≃ₗ[k] RestrictScalars k A N where
  toFun := e.hom.hom
  invFun := e.inv.hom
  map_add' := e.hom.hom.map_add
  map_smul' c x := e.hom.hom.map_smul (algebraMap k A c) x
  left_inv x := congrArg (fun m : M ⟶ M ↦ m.hom x) e.hom_inv_id
  right_inv x := congrArg (fun m : N ⟶ N ↦ m.hom x) e.inv_hom_id

lemma dim_eq_of_iso [Algebra k A] {M N : ModuleCat.{u} A} (e : M ≅ N) :
    Statement.dim k A M = Statement.dim k A N :=
  (restrictScalarsEquiv e).rank_eq

/-- A faithful `k`-linear functor satisfying the comparison, with
finite-dimensional values on `D_fin`, preserves the dimension of
infinite-dimensional modules. -/
theorem dim_eq [Algebra k A] [G.Faithful] [G.Additive] [G.Linear k] (hG : IsComparison G)
    (hfin : ∀ X : Dfin k, Module.Finite k (RestrictScalars k A ((fin G).obj X)))
    (X : D k) (hX : Cardinal.aleph0 ≤ X.obj.dim) :
    Statement.dim k A (G.obj X) = X.obj.dim :=
  (dim_eq_of_iso ((isoExtension hG).app X)).trans (Extension.dim_eq (fin G) hfin X hX)

end Comparison

end LargeIndecomposable
