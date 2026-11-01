module

public import LargeIndecomposable.RayCategories.Distributive.RayTablePresentation
public import LargeIndecomposable.StandardForm.Basic.FinalStandardness
public import LargeIndecomposable.RayCategories.RayTables.RayTransport
public import LargeIndecomposable.RepresentationType.Basic.RepresentationFiniteForms
public import LargeIndecomposable.Modules.Duality.OppositeDuality
public import LargeIndecomposable.RepresentationType.MinimalInfinite.Minimal

/-!
# Transfer: representation-finiteness passes to the linearization of the ray category

For split basic data `S` of a distributive representation-finite algebra `B`,
the linearization of the (small) ray category of `B` is representation-finite
(`SplitBasicData.isRepresentationFinite_linearization`). This is
Bretscher–Gabriel's theorem; the proof uses the multiplicative-bases library:
`B` is presented by the ray table of its graded standard form `A₀`
(`rayA_eq_rayA0`), which is representation-finite, and also by the ray table of
its ray category (`isRayPres_linTable`); two presentations have isomorphic
tables.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable RayQuiver RayCat LargeIndecomposable

universe u

namespace PrimitiveIdempotentsTransport

variable {k : Type u} [Field k] [IsAlgClosed k] {A : Type u} [Ring A] [Algebra k A]
  [FiniteDimensional k A] (ψ : A ≃ₐ[k] A) (F F' : PrimitiveIdempotents A)
  (σ : Fin F.m ≃ Fin F'.m) (hψ : ∀ i, ψ (F.e i) = F'.e (σ i))

include hψ

lemma hψ_symm (j : Fin F'.m) : ψ.symm (F'.e j) = F.e (σ.symm j) :=
  PrimitiveIdempotents.symm_e ψ F F' σ hψ j

/-- **Ray presentations move along a conjugation.** -/
theorem isRayPres_transport {V R : Type} {T : RaySys.Mult V R} {ι : V ≃ Fin F.m} {β : R → A}
    (h : F.IsRayPres (k := k) T ι β) : F'.IsRayPres (k := k) T (ι.trans σ) (ψ ∘ β) := by
  have hs : ∀ j, ψ.symm (F'.e j) = F.e (σ.symm j) := hψ_symm ψ F F' σ hψ
  refine ⟨fun r ↦ F.corner_fwd ψ F' σ hψ (h.corner r), fun r h0 ↦ h.ne r ?_,
    fun r s hrs ↦ h.inj r s ?_, fun x y f hf hf0 ↦ ?_, fun r s t hrst ↦ ?_, fun r s hn hmid ↦ ?_⟩
  · exact ψ.injective (h0.trans (map_zero ψ).symm)
  · have := F'.ray_fwd ψ.symm F σ.symm hs hrs
    simpa only [Function.comp_apply, AlgEquiv.symm_apply_apply, Equiv.trans_apply,
      Equiv.symm_apply_apply] using this
  · have hf' : ψ.symm f ∈ F.corner (k := k) (σ.symm x) (σ.symm y) :=
      F'.corner_fwd ψ.symm F σ.symm hs hf
    have hf0' : ψ.symm f ≠ 0 := fun h0 ↦ hf0 (by rw [← ψ.apply_symm_apply f, h0, map_zero])
    obtain ⟨r, h1, h2, h3⟩ := h.surj _ _ _ hf' hf0'
    refine ⟨r, by simp [h1], by simp [h2], ?_⟩
    have := F.ray_fwd ψ F' σ hψ h3
    simpa only [AlgEquiv.apply_symm_apply, Equiv.apply_symm_apply, h1, h2, Function.comp_apply]
      using this
  · obtain ⟨hnot, hray⟩ := h.mul_some r s t hrst
    refine ⟨fun hmem ↦ hnot ?_, ?_⟩
    · have := F'.insertionSpan_fwd ψ.symm F σ.symm hs hmem
      simpa only [Function.comp_apply, ← map_mul, AlgEquiv.symm_apply_apply, Equiv.trans_apply,
        Equiv.symm_apply_apply] using this
    · have := F.ray_fwd ψ F' σ hψ hray
      simpa only [Function.comp_apply, map_mul, Equiv.trans_apply] using this
  · have := F.insertionSpan_fwd ψ F' σ hψ (h.mul_none r s hn hmid)
    simpa only [Function.comp_apply, map_mul, Equiv.trans_apply] using this

end PrimitiveIdempotentsTransport

namespace SplitBasicData

variable {k : Type u} [Field k] [IsAlgClosed k] {B : Type u} [Ring B] [Algebra k B]
  [FiniteDimensional k B] {ι : Type} [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι)

omit [IsAlgClosed k] in
/-- Our representation-finiteness gives that of the multiplicative-bases library
(which counts right modules). -/
lemma primitiveIdempotents_isRepresentationFinite {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
    (h : Statement.IsRepresentationFinite A) :
    LargeIndecomposable.IsRepresentationFiniteRight k A :=
  (isRepresentationFinite_iff_moduleForm k Aᵐᵒᵖ).1 (isRepresentationFinite_mop (k := k) h)

omit [IsAlgClosed k] in
/-- ... and conversely. -/
lemma of_right_isRepresentationFinite {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
    (h : LargeIndecomposable.IsRepresentationFiniteRight k A) :
    Statement.IsRepresentationFinite A := by
  have h1 : Statement.IsRepresentationFinite Aᵐᵒᵖ := (isRepresentationFinite_iff_moduleForm k Aᵐᵒᵖ).2 h
  have h2 := isRepresentationFinite_mop (k := k) h1
  exact isRepresentationFinite_of_ringEquiv (RingEquiv.opOp A).symm h2

set_option maxHeartbeats 2000000 in
/-- **A table presenting a representation-finite basic algebra has a
representation-finite linearization** (compare with the table of `A₀`). -/
theorem lin_isRepresentationFinite_of_isRayPres [Nontrivial B]
    (hfin : Statement.IsRepresentationFinite B) {V R : Type} [Fintype V] [DecidableEq V]
    [Fintype R] [DecidableEq R] (T : RaySys.Mult V R) (ιT : V ≃ Fin S.primitiveIdempotents.m) (βT : R → B)
    (hT : S.primitiveIdempotents.IsRayPres (k := k) T ιT βT) :
    LargeIndecomposable.IsRepresentationFiniteRight k (T.Lin k) := by
  classical
  have hA := primitiveIdempotents_isRepresentationFinite (k := k) hfin
  have hbasic := S.isBasicAlgebra
  let _ : IsNoetherianRing Bᵐᵒᵖ := IsNoetherianRing.of_finite k Bᵐᵒᵖ
  obtain ⟨S'⟩ := exists_indSkeleton hA
  obtain ⟨b, v₀, hF, F, ι', β, hpres⟩ := rayA_eq_rayA0 k B hbasic hA inferInstance S'
  obtain ⟨ψ, σ, hψ⟩ := exists_algEquiv_idempotents (k := k) hbasic F S.primitiveIdempotents
  have hpres' := PrimitiveIdempotentsTransport.isRayPres_transport ψ F S.primitiveIdempotents σ hψ hpres
  have : ∀ x y : S'.ARVertex, Subsingleton (x ⟶ y) := S'.hasAtMostOneArrow
  have : ∀ x y : S'.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S'.arTranslationQuiver (S'.arCoefficients b) x ⟶
        MeshWalk.meshFam S'.arTranslationQuiver (S'.arCoefficients b) y) :=
    fun x y ↦ S'.finiteDimensional_meshHom b x y
  let _ : Fintype (S'.rayA0AR b v₀) :=
    inferInstanceAs (Fintype (MeshWalk.RayA0 (S'.arMeshData b) v₀))
  let _ : DecidableEq (S'.rayA0AR b v₀) :=
    inferInstanceAs (DecidableEq (MeshWalk.RayA0 (S'.arMeshData b) v₀))
  obtain ⟨m, ν, hmul, he⟩ := hT.exists_tableIso hA hpres'
  obtain ⟨φ⟩ := RaySys.nonempty_algEquiv_of_match _ _ m ν hmul he k
  have h0 : LargeIndecomposable.IsRepresentationFiniteRight k
      ((S'.A0MultAR b v₀ hF).Lin k) :=
    MeshWalk.A0Tab_isRepresentationFinite (S'.arMeshData b) v₀ hF
  exact isRepresentationFinite_of_surjective φ.symm.toAlgHom (by exact φ.symm.surjective) h0

variable [HasBGRSDistributiveHomStructure k S.toIdempotents.ProjectiveCategory]
  [LocallySmall.{0} S.toIdempotents.RayCategory]
  [IsRayCategory (RaySmall.{0} S.toIdempotents.RayCategory)]
  [Fintype (RaySmall.{0} S.toIdempotents.RayCategory)] [DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory)]

/-- **Bretscher–Gabriel: the linearization of the ray category of a
representation-finite distributive algebra is representation-finite.** -/
theorem isRepresentationFinite_linearization [Nontrivial B]
    (hfin : Statement.IsRepresentationFinite B) :
    Statement.IsRepresentationFinite (Linearization (RaySmall.{0} S.toIdempotents.RayCategory) k) := by
  have h1 := S.lin_isRepresentationFinite_of_isRayPres hfin _ _ _ (S.isRayPres_linTable (k := k))
  have h2 := isRepresentationFinite_of_surjective
    (B := Linearization (RaySmall.{0} S.toIdempotents.RayCategory) k)
    (linTableEquiv k (RaySmall.{0} S.toIdempotents.RayCategory)).toAlgHom
    (by exact (linTableEquiv k (RaySmall.{0} S.toIdempotents.RayCategory)).surjective) h1
  exact of_right_isRepresentationFinite h2

end SplitBasicData

end LargeIndecomposable
