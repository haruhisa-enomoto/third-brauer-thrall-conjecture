module

public import LargeIndecomposable.Coverings.UniversalCover.PieceKills
public import LargeIndecomposable.RepresentationEmbeddings.WalkConstruction.PdControl
public import LargeIndecomposable.Modules.KrullSchmidt.Fitting

/-!
# Push-downs from pieces of the cover as finite-dimensional modules

For a finite convex piece `S` of the universal cover of a finite ray category `P`, a
finite-dimensional representation `X` of `D_S` respecting the relations of the cover
pushes down to a module over `k(P)` on its total space (`pdMod`). Morphisms of
representations push down to module maps (`pdHom`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat RayCat.Cover RayQuiver AR

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P}
variable {k : Type u} [Field k] {S : Finset (Cover x₀)}

/-- The action of `k(P)` on a push-down. -/
def linAct (hS : Convex (S : Set (Cover x₀))) {X : Rep k (pieceQuiver S)}
    (hX : RespectsCover X) : Linearization P k →ₐ[k] Module.End k X.Tot :=
  RingQuot.liftAlgHom k ⟨X.pdAct (pieceProj S), fun _ _ h ↦ pdAct_linRel hS hX h⟩

lemma linAct_linPres (hS : Convex (S : Set (Cover x₀))) {X : Rep k (pieceQuiver S)}
    (hX : RespectsCover X) (z : (quiver P).PathAlgebra k) :
    linAct hS hX (linPres P k z) = X.pdAct (pieceProj S) z :=
  RingQuot.liftAlgHom_mkAlgHom_apply k _ _ z

/-- **The push-down** of a finite-dimensional representation respecting the cover. -/
def pdMod (hS : Convex (S : Set (Cover x₀))) (X : Rep k (pieceQuiver S))
    (hX : RespectsCover X) [∀ i, FiniteDimensional k (X.obj i)] :
    FDMod k (Linearization P k) where
  carrier := X.Tot
  isModule := Module.compHom X.Tot (linAct hS hX).toRingHom
  isScalarTower := by
    letI : Module (Linearization P k) X.Tot := Module.compHom X.Tot (linAct hS hX).toRingHom
    exact ⟨fun c b x ↦ by
      change (linAct hS hX (c • b)) x = c • (linAct hS hX b) x
      rw [map_smul]; rfl⟩
  isFD := inferInstance

lemma pdMod_smul (hS : Convex (S : Set (Cover x₀))) (X : Rep k (pieceQuiver S))
    (hX : RespectsCover X) [∀ i, FiniteDimensional k (X.obj i)] (b : Linearization P k)
    (x : X.Tot) : (b • (show pdMod hS X hX from x) : pdMod hS X hX) = linAct hS hX b x := rfl

/-- **Push-down of a morphism.** -/
def pdHom (hS : Convex (S : Set (Cover x₀))) {X Y : Rep k (pieceQuiver S)}
    (hX : RespectsCover X) (hY : RespectsCover Y) [∀ i, FiniteDimensional k (X.obj i)]
    [∀ i, FiniteDimensional k (Y.obj i)] (φ : X ⟶ Y) : pdMod hS X hX ⟶ pdMod hS Y hY :=
  AR.FDMod.ofLin
  { toFun := φ.tot
    map_add' := map_add φ.tot
    map_smul' := fun b x ↦ by
      obtain ⟨z, rfl⟩ := linPres_surjective P k b
      change φ.tot (linAct hS hX (linPres P k z) x) = linAct hS hY (linPres P k z) (φ.tot x)
      rw [linAct_linPres, linAct_linPres]
      have := Rep.commute_pdAct (pieceProj S) X φ.tot (Rep.Hom.isPdHom_tot _ φ).1
        (Rep.Hom.isPdHom_tot _ φ).2 z
      exact LinearMap.congr_fun this x
  }

@[simp] lemma pdHom_lin (hS : Convex (S : Set (Cover x₀))) {X Y : Rep k (pieceQuiver S)}
    (hX : RespectsCover X) (hY : RespectsCover Y) [∀ i, FiniteDimensional k (X.obj i)]
    [∀ i, FiniteDimensional k (Y.obj i)] (φ : X ⟶ Y) (x : X.Tot) :
    FDMod.lin (pdHom hS hX hY φ) x = φ.tot x := rfl

end RayCat

end LargeIndecomposable
