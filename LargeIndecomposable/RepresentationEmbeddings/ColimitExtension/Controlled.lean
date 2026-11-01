module

public import LargeIndecomposable.RepresentationEmbeddings.ColimitExtension.Criterion
public import LargeIndecomposable.Modules.KrullSchmidt.IndecomposableFullyFaithful
public import LargeIndecomposable.Modules.Duality.DimensionBasics

/-!
# Controlled embeddings and Theorem 5.1

A *controlled embedding* of `D_fin` into `mod A` is the input of Theorem 2.7:
a faithful `k`-linear representation embedding `Φ : D_fin → mod A` with
finite-dimensional values and retractions on `C_fin` whose kernels satisfy a
common nilpotence bound. Controlled embeddings transport along fully faithful
exact functors that preserve finite dimension (inflation and Morita
equivalence, Lemma 3.1), and a controlled embedding yields the representation
embedding of Theorem A (Theorem 5.1).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement

universe u

variable (k : Type u) [Field k] (A : Type u) [Ring A] [Algebra k A]

/-- A controlled embedding `D_fin → mod A`: the hypotheses of Theorem 2.7. -/
structure ControlledEmbedding where
  /-- The functor. -/
  Φ : Dfin k ⥤ ModuleCat.{u} A
  [additive : Φ.Additive]
  [linear : Φ.Linear k]
  [faithful : Φ.Faithful]
  isRepEmbeddingFin : IsRepEmbeddingFin Φ
  /-- Retractions on `C_fin`. -/
  R : Retractions k (Extension.Ψfin Φ)
  /-- The nilpotence bound. -/
  n : ℕ
  bound : R.NilpotentBound n

attribute [instance] ControlledEmbedding.additive ControlledEmbedding.linear
  ControlledEmbedding.faithful

variable {k A}

namespace ControlledEmbedding

variable [FiniteDimensional k A] (E : ControlledEmbedding k A)

include E in
/-- Theorem 5.1: a controlled embedding gives the representation embedding of
Theorem A. -/
theorem theoremA_conclusion :
    ∃ F : D k ⥤ ModuleCat.{u} A,
      IsRepresentationEmbedding F ∧
      (∀ T : D k, T.obj.IsFiniteDimensional → Module.Finite k (RestrictScalars k A (F.obj T))) ∧
      (∀ ι : Type u, PreservesColimitsOfShape (Discrete ι) F) ∧
      PreservesFilteredColimitsOfSize.{u, u} F ∧
      (∀ T : D k, Cardinal.aleph0 ≤ T.obj.dim → dim k A (F.obj T) = T.obj.dim) := by
  have hrep := Extension.isRepresentationEmbedding E.Φ E.isRepEmbeddingFin E.R E.bound
  exact ⟨Extension.functor E.Φ, hrep,
    Extension.finite_of_finite E.Φ E.isRepEmbeddingFin,
    Extension.preservesCoproducts E.isRepEmbeddingFin.exact,
    Extension.preservesFilteredColimits E.isRepEmbeddingFin.exact,
    fun T hT ↦ Extension.dim_eq E.Φ E.isRepEmbeddingFin.fin T hT⟩

end ControlledEmbedding

namespace ControlledEmbedding

variable {B : Type u} [Ring B] [Algebra k B]

/-- A functor of module categories preserving short exact sequences, in the
three-part form of `Statement.IsRepresentationEmbedding`. -/
def PreservesSES (G : ModuleCat.{u} B ⥤ ModuleCat.{u} A) : Prop :=
  ∀ (L M N : ModuleCat.{u} B) (f : L ⟶ M) (g : M ⟶ N), Function.Injective f.hom →
    Function.Surjective g.hom → LinearMap.range f.hom = LinearMap.ker g.hom →
    Function.Injective (G.map f).hom ∧ Function.Surjective (G.map g).hom ∧
      LinearMap.range (G.map f).hom = LinearMap.ker (G.map g).hom

/-- Transport of a controlled embedding along a fully faithful exact functor
preserving finite dimension (Lemma 3.1 and the proof of Theorem 5.1). -/
def transport (E : ControlledEmbedding k B) (G : ModuleCat.{u} B ⥤ ModuleCat.{u} A)
    [G.Additive] [G.Linear k] (hG : G.FullyFaithful) (hexact : PreservesSES G)
    (hfin : ∀ M : ModuleCat.{u} B, Module.Finite k (RestrictScalars k B M) →
      Module.Finite k (RestrictScalars k A (G.obj M))) :
    ControlledEmbedding k A :=
  haveI := hG.full
  haveI := hG.faithful
  { Φ := E.Φ ⋙ G
    isRepEmbeddingFin :=
      { fin := fun X ↦ hfin _ (E.isRepEmbeddingFin.fin X)
        exact := fun X Y Z f g h ↦ by
          obtain ⟨h₁, h₂, h₃⟩ := E.isRepEmbeddingFin.exact X Y Z f g h
          exact hexact _ _ _ _ _ h₁ h₂ h₃
        indecS := (Reduction.isIndecomposable_map_iff G _).2 E.isRepEmbeddingFin.indecS
        notIsoS := fun X hX ↦ ⟨fun e ↦ (E.isRepEmbeddingFin.notIsoS X hX).false
          (hG.preimageIso e)⟩ }
    R := E.R.postcomp hG
    n := E.n
    bound := Retractions.NilpotentBound.postcomp _ hG E.bound }

end ControlledEmbedding

end LargeIndecomposable
