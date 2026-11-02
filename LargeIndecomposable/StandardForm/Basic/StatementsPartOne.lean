module

public import LargeIndecomposable.MeshCategories.AuslanderReitenQuiver.ARQuiver
public import LargeIndecomposable.StandardForm.Basic.GradedRealizationIso
public import LargeIndecomposable.Modules.Corners.CornerAlgebra
public import LargeIndecomposable.MeshCategories.Basic.MeshCorrections
public import LargeIndecomposable.RayCategories.RayTables.Rays
public import LargeIndecomposable.PreprojectiveAlgebras.ECase
public import LargeIndecomposable.MeshCategories.Periodic.ComponentGlue
public import LargeIndecomposable.RepresentationType.Basic.CornerRepFinite
public import LargeIndecomposable.StandardForm.Basic.SplitTransfer
public import LargeIndecomposable.RayCategories.RayTables.EndpointChains
public import LargeIndecomposable.StandardForm.Weights.PosetWeights
public import LargeIndecomposable.MultiplicativeBases.Normed.NonbasicBasis
public import LargeIndecomposable.RayCategories.RayTables.RayProduct
public import LargeIndecomposable.MultiplicativeBases.Normed.A0Normed
public import LargeIndecomposable.StandardForm.Weights.UnitCoefficients
public import LargeIndecomposable.MeshCategories.AuslanderReitenQuiver.ARMeshFinite
public import LargeIndecomposable.StandardForm.Basic.StandardAlgebras
public import LargeIndecomposable.StandardForm.Deformations.FilteredA
public import LargeIndecomposable.StandardForm.Basic.A0Graded
/-!
# Part I statements

Statements of Part I results of the source paper (Sections 2--5), with their proofs
from the foundations. The remaining Part I results are proved in the foundation
files listed in `docs/PAPER-CORRESPONDENCE.md`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace LargeIndecomposable

universe u v w

section AnyField

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
  [FiniteDimensional k A]

/-- Lemma 2.1 (`lem:nonbasic-basis`). If the basic algebra of `A` has a normed
multiplicative basis, so does `A`. Over any field. The basic algebra is a
corner `eAe` for a full idempotent `e` (`AeA = A`) with `eAe` basic. -/
theorem nonbasicBasis {e : A} (he : IsIdempotentElem e)
    (hfull : ∀ a : A, a ∈ Submodule.span k {x | ∃ p q : A, x = p * e * q})
    (hbasic : IsBasicAlgebra he.Corner)
    (hB : HasNormedMultiplicativeBasis k he.Corner) :
    HasNormedMultiplicativeBasis k A := by
  obtain ⟨ι, b, hb⟩ := hB
  obtain ⟨E, hE, hp⟩ := hb.idempotents
  have H : Nonbasic.Hyp he b E := ⟨hE, hb.multiplicative, hp, hb.radicalPow⟩
  obtain ⟨M⟩ := H.nonempty_match (hfull 1)
  exact M.hasNormedBasis (hfull 1)

/-- Lemma 4.6 (`lem:split-representation-transfer`). Let `C ⊆ B` be a unital
inclusion, `q : C ↠ D` a quotient, and `π : B → D` a `C`-bimodule map with
`π|_C = q`. If `B` is representation-finite, so is `D`. Over any field. -/
theorem splitRepresentationTransfer {B D : Type v} [Ring B] [Algebra k B]
    [FiniteDimensional k B] [Ring D] [Algebra k D] [FiniteDimensional k D]
    (C : Subalgebra k B) (q : C →ₐ[k] D) (hq : Function.Surjective q)
    (π : B →ₗ[k] D) (hπ : ∀ c : C, π c = q c)
    (hbimod : ∀ (c c' : C) (b : B), π (c * b * c') = q c * π b * q c')
    (hB : IsRepresentationFiniteRight k B) :
    IsRepresentationFiniteRight k D :=
  splitRepresentationTransfer_of π hbimod hq hπ hB

end AnyField

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k] {A : Type v} [Ring A] [Algebra k A]
  [FiniteDimensional k A]

/-- Lemma 3.1(1) (`lem:endpoint-chains`), first part. A representation-finite
algebra has finitely many two-sided ideals. -/
theorem finite_twoSidedIdeals (hA : IsRepresentationFiniteRight k A) :
    (Set.univ : Set (TwoSidedIdeal A)).Finite :=
  finite_twoSidedIdeals_of hA

/-- Lemma 3.1(1) (`lem:endpoint-chains`), second part. Every idempotent corner
`eAe` of a representation-finite algebra is representation-finite. -/
theorem corner_isRepresentationFinite (hA : IsRepresentationFiniteRight k A) {e : A}
    (he : IsIdempotentElem e) :
    IsRepresentationFiniteRight k he.Corner :=
  corner_isRepresentationFinite_of he hA

/-- Lemma 3.1(2) (`lem:endpoint-chains`). For a basic representation-finite
algebra, each local corner `R_x = e_x A e_x` is isomorphic to `k[t]/(t^N)`
with `N ≥ 1`. -/
theorem localCorner_truncatedPolynomial (hbasic : IsBasicAlgebra A)
    (hA : IsRepresentationFiniteRight k A) (F : PrimitiveIdempotents A) (x : Fin F.m) :
    ∃ N : ℕ, 1 ≤ N ∧ Nonempty ((F.complete.idem x).Corner ≃ₐ[k]
      Polynomial k ⧸ Ideal.span {(Polynomial.X : Polynomial k) ^ N}) :=
  F.localCorner_iso k hA x

/-- Lemma 3.1(3) (`lem:endpoint-chains`). The `R_x`--`R_y`-subbimodules of
`A(x, y)` form a chain with one-dimensional successive quotients, and every
nonzero `f` generates its subbimodule from one side. -/
theorem endpointSubbimodules_chain (hbasic : IsBasicAlgebra A)
    (hA : IsRepresentationFiniteRight k A) (F : PrimitiveIdempotents A) (x y : Fin F.m) :
    IsChain (· ≤ ·) {N : Submodule k A | F.IsEndpointSubbimodule x y N} ∧
      (∀ N N' : Submodule k A, F.IsEndpointSubbimodule x y N →
        F.IsEndpointSubbimodule x y N' → N < N' →
        (∀ N'', F.IsEndpointSubbimodule x y N'' → N ≤ N'' → N'' ≤ N' →
          N'' = N ∨ N'' = N') →
        Module.finrank k N' = Module.finrank k N + 1) ∧
      ∀ f ∈ F.corner (k := k) x y, f ≠ 0 →
        F.endpointSpan x y f =
            Submodule.span k {g | ∃ a ∈ F.corner (k := k) x x, g = a * f} ∨
          F.endpointSpan x y f =
            Submodule.span k {g | ∃ b ∈ F.corner (k := k) y y, g = f * b} :=
  ⟨F.isChain_subbimodules hA x y,
    fun _ _ hN hN' hlt hcons ↦ F.finrank_succ_of_consecutive hN hN' hlt hcons,
    fun _ hf _ ↦ F.endpointSpan_one_sided hA hf⟩

/-- Corollary 3.3 (`cor:ray-transversal`). One element from each nonzero ray,
using `e_x` for `[e_x]`, gives a basis of `A` whose intersection with every
two-sided ideal is a basis of that ideal. -/
theorem rayTransversal_basis (hbasic : IsBasicAlgebra A)
    (hA : IsRepresentationFiniteRight k A) (F : PrimitiveIdempotents A)
    (b : F.NonzeroRay k → A) (hb : F.IsRayTransversal b) :
    LinearIndependent k b ∧ Submodule.span k (Set.range b) = ⊤ ∧
      ∀ I : TwoSidedIdeal A, ∀ a : A,
        a ∈ I ↔ a ∈ Submodule.span k (b '' {r | b r ∈ I}) :=
  F.rayTransversal_isBasis hb hA

/-- Lemma 3.6 (`lem:ray-product-independent`). The ray product does not depend
on the representatives, and a nonzero ray product has a nonzero product for
every choice of representatives. -/
theorem rayProduct_independent (hbasic : IsBasicAlgebra A)
    (hA : IsRepresentationFiniteRight k A) (F : PrimitiveIdempotents A) (x y z : Fin F.m)
    (f f' h h' : A) (hf : f ∈ F.corner (k := k) x y) (hf0 : f ≠ 0)
    (hh : h ∈ F.corner (k := k) y z) (hh0 : h ≠ 0)
    (hf' : f' ∈ F.ray (k := k) x y f) (hh' : h' ∈ F.ray (k := k) y z h) :
    (f * h ∈ F.insertionSpan (k := k) x y z f h ↔
        f' * h' ∈ F.insertionSpan (k := k) x y z f' h') ∧
      (f * h ∉ F.insertionSpan (k := k) x y z f h →
        f' * h' ≠ 0 ∧ F.ray (k := k) x z (f * h) = F.ray (k := k) x z (f' * h')) :=
  F.rayProduct_independent_of hA hf hf0 hh hh0 hf' hh'

/-- Lemma 4.9 (`lem:poset-weights`). If the incidence algebra of a finite
poset is representation-finite, every additive weight is a difference of
object values. -/
theorem posetWeights {P : Type v} [PartialOrder P] [Fintype P] [DecidableEq P]
    [LocallyFiniteOrder P]
    (hP : IsRepresentationFiniteRight k (IncidenceAlgebra k P))
    {G : Type w} [AddCommGroup G] (wt : P → P → G)
    (hwt : ∀ x y z : P, x ≤ y → y ≤ z → wt x z = wt x y + wt y z) :
    ∃ ζ : P → G, ∀ x y : P, x ≤ y → wt x y = ζ y - ζ x := by
  classical
  exact posetWeights_of hP wt hwt

/-- Proposition 5.3 (`prop:mesh-correction-spaces`). For a finite-dimensional
scalar mesh category on a finite translation quiver with at most one arrow
between ordered vertices, satisfying the brick hypothesis, and
`char k ≠ 2`, the derivative `D_m` is surjective for every `m ≥ 2`. -/
theorem meshCorrectionSpaces {V : Type v} [Quiver.{w} V] [Fintype V] [DecidableEq V]
    [∀ x y : V, Fintype (x ⟶ y)] (Q : TranslationQuiver V)
    (hQ : HasAtMostOneArrow V) (c : MeshCoefficients k Q)
    (hfin : ∀ x y : V, FiniteDimensional k
      (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y))
    (hchar : ringChar k ≠ 2) (hbrick : ScalarMeshCategory.BrickHypothesis c)
    (m : ℕ) (hm : 2 ≤ m) :
    ScalarMeshCategory.MeshDerivativeSurjective c m := by
  classical
  haveI : ∀ x y : V, Subsingleton (x ⟶ y) := hQ
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  -- Proposition 5.1: restrict to the periodic components
  refine meshDerivativeSurjective_of_components c m fun x hx ↦ ?_
  have hS := TranslationQuiver.isTauClosed_component (Q := Q) x
  have hst := TranslationQuiver.restrict_isStable (Q := Q) x
  -- a periodic component: Appendix A, types `A`, `D` and `E`
  exact StarTrace.connected_surjective hst (c.restrict hS)
    (finiteDimensional_restrict hS c hfin) h2
    (FullSub.mk x (TranslationQuiver.mem_component_self hx))
    (TranslationQuiver.restrict_conn x hx)
    (fun L π hπ hτ hsurj hEL m hm ↦ StarTrace.e_surjective hst (c.restrict hS)
      (brickHypothesis_restrict hS c hbrick) h2 L π hπ hτ hsurj hEL m hm) m hm

end AlgClosed

section ARQuiver

universe u'

variable {k A : Type u'} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- Lemma 2.2 (`lem:square-free`). The Auslander--Reiten quiver of a
representation-finite algebra has no loops and at most one arrow between each
ordered pair of vertices. Proved in `Foundations/SquareFree.lean`. (The
instance `IsNoetherianRing Aᵐᵒᵖ` follows from finite-dimensionality, by
`IsNoetherianRing.of_finite`.) -/
theorem squareFree (S : IndSkeleton k A) (x y : Fin S.n) :
    Module.finrank k (S.Irr (S.ind x) (S.ind y)) ≤ 1 ∧
      Module.finrank k (S.Irr (S.ind x) (S.ind x)) = 0 :=
  ⟨S.finrank_irr_le_one x y, S.finrank_irr_self x⟩

/-- Proposition 2.6(3) (`prop:graded-realization`). The chosen arrow classes
induce an isomorphism of graded categories `k(Γ_A) ≅ gr_J ind(mod A)`, with the
scalar relations of `eq:scalar-mesh`. Formally: the Hom spaces of `k(Γ_A)` are
the internal direct sums of their path-degree parts; in each degree `d` there
is a linear isomorphism `φ_d` onto the radical layer `J^d / J^{d+1}`; `φ_1`
sends each arrow to its chosen basis vector of `Irr`; and the `φ_d` are
compatible with composition, which in `gr_J` is computed on
representatives. -/
theorem gradedRealization (hbasic : IsBasicAlgebra A) (S : IndSkeleton k A)
    (b : S.ArrowBases) :
    (∀ x y : S.ARVertex,
      DirectSum.IsInternal fun d ↦ ScalarMeshCategory.degreePart (S.arCoefficients b) d x y) ∧
    ∃ φ : ∀ (d : ℕ) (x y : S.ARVertex),
        ScalarMeshCategory.degreePart (S.arCoefficients b) d x y ≃ₗ[k]
          S.layer d (S.label x) (S.label y),
      (∀ (x y : S.ARVertex) (a : x ⟶ y)
        (ha : ScalarMeshCategory.arrowMor (S.arCoefficients b) a ∈
          ScalarMeshCategory.degreePart (S.arCoefficients b) 1 x y),
        φ 1 x y ⟨_, ha⟩ = b x y a) ∧
      ∀ (d e : ℕ) (x y z : S.ARVertex)
        (f : ScalarMeshCategory.degreePart (S.arCoefficients b) d x y)
        (g : ScalarMeshCategory.degreePart (S.arCoefficients b) e y z)
        (f' : S.label x ⟶ S.label y) (hf' : f' ∈ S.radPow d _ _)
        (g' : S.label y ⟶ S.label z) (hg' : g' ∈ S.radPow e _ _),
        φ d x y f = S.layerClass f' hf' → φ e y z g = S.layerClass g' hg' →
        ∃ (hfg : (f : S.meshObj b x ⟶ S.meshObj b y) ≫ g ∈
            ScalarMeshCategory.degreePart (S.arCoefficients b) (d + e) x z)
          (hfg' : f' ≫ g' ∈ S.radPow (d + e) _ _),
          φ (d + e) x z ⟨_, hfg⟩ = S.layerClass (f' ≫ g') hfg' :=
  S.gradedRealization_full b

/-- Lemma 4.4 (`lem:unit-mesh-coefficients`). Every coefficient system on `Γ_A`
can be changed to coefficients one by rescaling arrows (`φ`) and entire mesh
relations (`ψ`): `c_{x,a} φ(σa) φ(a) = ψ(x)`. In every characteristic. -/
theorem unitMeshCoefficients (S : IndSkeleton k A)
    (c : MeshCoefficients k S.arTranslationQuiver) :
    ∃ (φ : MeshWalk.Arr S.ARVertex → kˣ) (ψ : S.arTranslationQuiver.nonprojective → kˣ),
      ∀ (x : S.arTranslationQuiver.nonprojective) (y : S.ARVertex) (a : y ⟶ x.1),
        c x y a * φ ⟨(S.arTranslationQuiver.tau x).1, y, S.arTranslationQuiver.mate x y a⟩ *
          φ ⟨y, x.1, a⟩ = ψ x := by
  classical
  obtain ⟨b⟩ := S.nonempty_arrowBases
  haveI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  exact MeshWalk.exists_unit_rescaling (S.arCoefficients b)
    (fun x y ↦ S.finiteDimensional_meshHom b x y) c

/-- Corollary 4.15 (`cor:graded-standard-form`), the parts used outside
characteristic two: `A₀` (for any choice of arrow classes) is
representation-finite, and a standard basic `A` is isomorphic to `A₀`. (The
converse, `A ≅ A₀ ⟹ A` standard, is used only in Part III, Theorem 11.8; here
Theorem B obtains standardness directly from Proposition 5.4.) -/
theorem gradedStandardForm (S : IndSkeleton k A) (hbasic : IsBasicAlgebra A) :
    (∀ b : S.ArrowBases, IsRepresentationFiniteRight k (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ) ∧
      (S.IsStandard → ∃ b : S.ArrowBases,
        Nonempty (A ≃ₐ[k] (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ)) := by
  refine ⟨fun b ↦ ?_, fun hstd ↦ ?_⟩
  · haveI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
    haveI : ∀ x y : S.ARVertex, FiniteDimensional k (S.meshObj b x ⟶ S.meshObj b y) :=
      fun x y ↦ S.finiteDimensional_meshHom b x y
    exact CatAlg.MeshData.isRepresentationFinite_A0 (S.arInjData b)
  obtain ⟨n, e, he, hprim, hb⟩ := hbasic
  obtain ⟨b, Φ0, hEq, hlin, hβ⟩ := hstd
  haveI := hEq
  exact ⟨b, ⟨S.algEquivA0 b he hprim hb Φ0 hlin fun x ↦ (hβ x).some⟩⟩

end ARQuiver

end LargeIndecomposable
