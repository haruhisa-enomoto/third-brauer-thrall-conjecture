module

public import LargeIndecomposable.RayCategories.Basic.Small
public import LargeIndecomposable.RayCategories.Distributive.AlgConnected

/-!
# Fischbacher's theorem for the small model

Cancellation, chain-boundedness and connectivity by nonzero zigzags pass to the
small model `RaySmall P`; hence its fundamental group is free when that of
the conditions hold for `P` (`RayCat.RaySmall.isFreeGroup_end`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe w v u

namespace RayCat

namespace RaySmall

variable {P : Type u} [Category.{v} P] [LocallySmall.{w} P] [HasZeroMorphisms P]

lemma leftCancel (hL : LeftCancel P) : LeftCancel (RaySmall.{u} P) := by
  intro x y z f g h hfg h0
  obtain ⟨f₀, rfl⟩ := (sh.{w}).surjective f
  obtain ⟨g₀, rfl⟩ := (sh.{w}).surjective g
  obtain ⟨h₀, rfl⟩ := (sh.{w}).surjective h
  rw [← sh_comp, ← sh_comp, (sh.{w}).apply_eq_iff_eq] at hfg
  rw [← sh_comp] at h0
  exact congrArg _ (hL _ _ _ hfg fun h' ↦ h0 (by rw [h']; rfl))

lemma rightCancel (hR : RightCancel P) : RightCancel (RaySmall.{u} P) := by
  intro x y z f g h hfg h0
  obtain ⟨f₀, rfl⟩ := (sh.{w}).surjective f
  obtain ⟨g₀, rfl⟩ := (sh.{w}).surjective g
  obtain ⟨h₀, rfl⟩ := (sh.{w}).surjective h
  rw [← sh_comp, ← sh_comp, (sh.{w}).apply_eq_iff_eq] at hfg
  rw [← sh_comp] at h0
  exact congrArg _ (hR _ _ _ hfg fun h' ↦ h0 (by rw [h']; rfl))

/-- A morphism of the small model as a morphism of `P`. -/
def toRM (F : RayMor (RaySmall.{u} P)) : RayMor P := ⟨F.1.as, F.2.1.as, (sh.{w}).symm F.2.2⟩

omit [HasZeroMorphisms P] in
lemma peak_toRM {F G : RayMor (RaySmall.{u} P)} (h : Peak F G) : Peak (toRM F) (toRM G) := by
  obtain ⟨X, Y, φ⟩ := F
  obtain ⟨X', Y', ψ⟩ := G
  obtain ⟨hY, -⟩ := id h
  change Y = Y' at hY
  subst hY
  rw [peak_mk_iff] at h
  change Peak ⟨X.as, Y.as, (sh.{w}).symm φ⟩ ⟨X'.as, Y.as, (sh.{w}).symm ψ⟩
  rw [peak_mk_iff]
  refine ⟨fun ⟨k, hk⟩ ↦ h.1 ⟨sh k, ?_⟩, fun ⟨k, hk⟩ ↦ h.2 ⟨sh k, ?_⟩⟩
  · rw [← Equiv.apply_symm_apply sh ψ, ← sh_comp, hk, Equiv.apply_symm_apply]
  · rw [← Equiv.apply_symm_apply sh φ, ← sh_comp, hk, Equiv.apply_symm_apply]

omit [HasZeroMorphisms P] in
lemma valley_toRM {F G : RayMor (RaySmall.{u} P)} (h : Valley F G) :
    Valley (toRM F) (toRM G) := by
  obtain ⟨X, Y, φ⟩ := F
  obtain ⟨X', Y', ψ⟩ := G
  obtain ⟨hX, -⟩ := id h
  change X = X' at hX
  subst hX
  rw [valley_mk_iff] at h
  change Valley ⟨X.as, Y.as, (sh.{w}).symm φ⟩ ⟨X.as, Y'.as, (sh.{w}).symm ψ⟩
  rw [valley_mk_iff]
  refine ⟨fun ⟨k, hk⟩ ↦ h.1 ⟨sh k, ?_⟩, fun ⟨k, hk⟩ ↦ h.2 ⟨sh k, ?_⟩⟩
  · rw [← Equiv.apply_symm_apply sh φ, ← sh_comp, hk, Equiv.apply_symm_apply]
  · rw [← Equiv.apply_symm_apply sh ψ, ← sh_comp, hk, Equiv.apply_symm_apply]

lemma chainBounded (hCB : ChainBounded P) : ChainBounded (RaySmall.{u} P) := by
  obtain ⟨N, hN⟩ := hCB
  refine ⟨N, fun L hL ↦ ?_⟩
  have : IsChain 0 (L.map toRM) := by
    refine ⟨fun f hf ↦ ?_, fun j hj ↦ ?_⟩
    · obtain ⟨F, hF, rfl⟩ := List.mem_map.1 hf
      intro h0
      apply hL.1 F hF
      rw [← Equiv.apply_symm_apply sh F.2.2]
      change sh ((sh.{w}).symm F.2.2) = 0
      rw [show (sh.{w}).symm F.2.2 = 0 from h0]
      rfl
    · have := hL.2 j (by simpa using hj)
      simp only [List.getElem_map]
      unfold Link at this ⊢
      split_ifs at this ⊢
      · exact peak_toRM this
      · exact valley_toRM this
  simpa using hN _ this

lemma nzConnected {x y : RaySmall.{u} P} (h : NZConnected x.as y.as) : NZConnected x y := by
  obtain ⟨x⟩ := x
  obtain ⟨y⟩ := y
  change NZConnected x y at h
  induction h with
  | rel a b hab =>
    obtain ⟨f, hf⟩ := hab
    exact Relation.EqvGen.rel _ _ ⟨sh.{w} f, fun h ↦ hf ((sh_eq_zero_iff f).1 h)⟩
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact ih.symm _ _
  | trans _ _ _ _ _ ih ih' => exact ih.trans _ _ _ ih'

attribute [local instance] isRayCategory_of_finiteRayCategory in
/-- Fischbacher's theorem for the small model. -/
theorem isFreeGroup_end [LargeIndecomposable.IsFiniteRayCategory P] [Finite P] [Nonempty P]
    (hL : LeftCancel P) (hR : RightCancel P) (hCB : ChainBounded P)
    (hcon : ∀ x y : P, NZConnected x y) (X : FundGroupoid (RaySmall.{u} P)) :
    IsFreeGroup (End X) := by
  have : Nonempty (RaySmall.{u} P) := ⟨⟨Classical.arbitrary P⟩⟩
  exact isFreeGroup_end_fund _ _ (leftCancel hL) (rightCancel hR) (chainBounded hCB)
    (isConnected_fund_of_nzConnected fun x y ↦ nzConnected (hcon x.as y.as)) le_rfl X

end RaySmall

end RayCat

namespace SplitBasicData

variable {k : Type u} [Field k] [Infinite k] {B : Type v} [Ring B] [Algebra k B]
  [FiniteDimensional k B] {ι : Type w} [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι)

open RayCat in
/-- The ray category of a split basic distributive algebra has finite, hence
small, Hom-types. -/
theorem locallySmall (hd : IsDistribIdeals B) :
    letI := S.distribHomStructure hd
    LocallySmall.{0} S.toIdempotents.RayCategory := by
  letI := S.distribHomStructure hd
  have := S.isFiniteRayCategory hd
  exact ⟨fun X Y ↦ by
    have := LargeIndecomposable.IsFiniteRayCategory.hom_finite X Y
    infer_instance⟩

open RayCat in
/-- **Fischbacher, no-crown case, small model.** For a split basic distributive
minimal representation-infinite algebra whose ray category is chain-bounded,
the vertex groups of the fundamental groupoid of the small model are free. -/
theorem small_isFreeGroup_end (hd : IsDistribIdeals B) (hB : IsMinimalRepInfinite B)
    [Nonempty ι] :
    letI := S.distribHomStructure hd
    letI := S.locallySmall hd
    ChainBounded S.toIdempotents.RayCategory →
      ∀ X : FundGroupoid (RaySmall.{0} S.toIdempotents.RayCategory), IsFreeGroup (End X) := by
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  have := S.isFiniteRayCategory hd
  have : Nonempty S.toIdempotents.RayCategory :=
    ⟨⟨S.toIdempotents.projectiveVertexEquiv.symm (Classical.arbitrary ι)⟩⟩
  intro hCB X
  exact RaySmall.isFreeGroup_end (S.leftCancel hd) (S.rightCancel hd) hCB
    (S.nzConnected hd fun e he hc ↦ hB.central_idempotent e he hc) X

end SplitBasicData

end LargeIndecomposable
