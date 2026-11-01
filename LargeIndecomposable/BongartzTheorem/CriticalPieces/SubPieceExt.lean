module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.SubPiece

/-!
# Representations supported in a subpiece

Let `T ⊆ S`. A representation of the piece of `S` is supported in `T` if it vanishes at the
points outside `T`. Morphisms between restrictions of such representations extend by zero
(`extHomP`). So restriction reflects isomorphism (`iso_of_resP_iso`) and preserves
indecomposability (`isIndec_resP`) for representations supported in `T`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver Module

universe u

variable {k : Type u} [Field k]
  {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S T : Finset (Cover x₀)} (hTS : T ⊆ S)

/-- Supported in `T`: zero at the points outside `T`. -/
def SuppIn (T : Finset (Cover x₀)) (X : Rep k (pieceQuiver S)) : Prop :=
  ∀ s : (pieceQuiver S).V, (show S from s).1 ∉ T → Subsingleton (X.obj s)

open Classical in
/-- The components of the extension by zero of a morphism. -/
def extLinP {X Y : Rep k (pieceQuiver S)} (f : resP hTS X ⟶ resP hTS Y) (s : (pieceQuiver S).V) :
    X.obj s →ₗ[k] Y.obj s :=
  if h : (show S from s).1 ∈ T then
    (show X.obj s →ₗ[k] Y.obj s from (f.app ⟨(show S from s).1, h⟩).hom) else 0

lemma extLinP_inc {X Y : Rep k (pieceQuiver S)} (f : resP hTS X ⟶ resP hTS Y)
    (a : (pieceQuiver T).V) : extLinP hTS f ((incH hTS).vert a) = (f.app a).hom := by
  classical
  exact dif_pos (show T from a).2

lemma extLinP_out {X Y : Rep k (pieceQuiver S)} (f : resP hTS X ⟶ resP hTS Y)
    (s : (pieceQuiver S).V) (hs : (show S from s).1 ∉ T) : extLinP hTS f s = 0 := by
  classical
  exact dif_neg hs

/-- **Extension by zero of a morphism.** -/
def extHomP {X Y : Rep k (pieceQuiver S)} (hX : SuppIn T X) (hY : SuppIn T Y)
    (f : resP hTS X ⟶ resP hTS Y) : X ⟶ Y where
  app s := ModuleCat.ofHom (extLinP hTS f s)
  comm α := by
    ext v
    change extLinP hTS f _ ((X.map α).hom v) = (Y.map α).hom (extLinP hTS f _ v)
    by_cases hs : (show S from (pieceQuiver S).src α).1 ∈ T
    · by_cases ht : (show S from (pieceQuiver S).tgt α).1 ∈ T
      · let α' : (pieceQuiver T).A := ⟨⟨_, hs⟩, ⟨_, ht⟩, α.2.2⟩
        have e1 := extLinP_inc hTS f α'.1
        have e2 := extLinP_inc hTS f α'.2.1
        change extLinP hTS f ((incH hTS).vert α'.2.1) ((X.map ((incH hTS).arr α')).hom v) =
          (Y.map ((incH hTS).arr α')).hom (extLinP hTS f ((incH hTS).vert α'.1) v)
        rw [e1, e2]
        have := congrArg (fun g ↦ (ModuleCat.Hom.hom g) v) (f.comm α')
        exact this
      · haveI := hY _ ht
        exact Subsingleton.elim _ _
    · haveI := hX _ hs
      rw [Subsingleton.elim v 0, map_zero, map_zero, map_zero, map_zero]

lemma extHomP_app_inc {X Y : Rep k (pieceQuiver S)} (hX : SuppIn T X) (hY : SuppIn T Y)
    (f : resP hTS X ⟶ resP hTS Y) (a : (pieceQuiver T).V) :
    ((extHomP hTS hX hY f).app ((incH hTS).vert a)).hom = (f.app a).hom :=
  extLinP_inc hTS f a

lemma extHomP_comp {X Y Z : Rep k (pieceQuiver S)} (hX : SuppIn T X) (hY : SuppIn T Y)
    (hZ : SuppIn T Z) (f : resP hTS X ⟶ resP hTS Y) (g : resP hTS Y ⟶ resP hTS Z) :
    extHomP hTS hX hY f ≫ extHomP hTS hY hZ g = extHomP hTS hX hZ (f ≫ g) := by
  refine Rep.hom_ext fun s ↦ ?_
  ext v
  change extLinP hTS g s (extLinP hTS f s v) = extLinP hTS (f ≫ g) s v
  by_cases hs : (show S from s).1 ∈ T
  · obtain ⟨a, rfl⟩ : ∃ a, (incH hTS).vert a = s := ⟨⟨_, hs⟩, rfl⟩
    rw [extLinP_inc, extLinP_inc, extLinP_inc]
    rfl
  · rw [extLinP_out hTS _ s hs, extLinP_out hTS _ s hs, extLinP_out hTS _ s hs]
    rfl

lemma extHomP_id {X : Rep k (pieceQuiver S)} (hX : SuppIn T X) :
    extHomP hTS hX hX (𝟙 (resP hTS X)) = 𝟙 X := by
  refine Rep.hom_ext fun s ↦ ?_
  ext v
  change extLinP hTS (𝟙 (resP hTS X)) s v = v
  by_cases hs : (show S from s).1 ∈ T
  · obtain ⟨a, rfl⟩ : ∃ a, (incH hTS).vert a = s := ⟨⟨_, hs⟩, rfl⟩
    rw [extLinP_inc]
    rfl
  · haveI := hX _ hs
    exact Subsingleton.elim _ _

/-- **Restriction reflects isomorphism** for representations supported in `T`. -/
theorem iso_of_resP_iso {X Y : Rep k (pieceQuiver S)} (hX : SuppIn T X) (hY : SuppIn T Y)
    (φ : resP hTS X ≅ resP hTS Y) : Nonempty (X ≅ Y) :=
  ⟨⟨extHomP hTS hX hY φ.hom, extHomP hTS hY hX φ.inv,
    by rw [extHomP_comp, φ.hom_inv_id, extHomP_id],
    by rw [extHomP_comp, φ.inv_hom_id, extHomP_id]⟩⟩

/-- **Restriction preserves indecomposability** for representations supported in `T`. -/
theorem isIndec_resP {X : Rep k (pieceQuiver S)} (hX : SuppIn T X) (hind : X.IsIndec) :
    (resP hTS X).IsIndec := by
  obtain ⟨⟨s, hs⟩, hidem⟩ := hind
  refine ⟨?_, fun e he ↦ ?_⟩
  · by_cases hsT : (show S from s).1 ∈ T
    · exact ⟨⟨_, hsT⟩, hs⟩
    · exact absurd (hX s hsT) (not_subsingleton_iff_nontrivial.2 hs)
  · rcases hidem (extHomP hTS hX hX e) (by rw [extHomP_comp, he]) with h0 | h1
    · left
      intro a
      have := h0 ((incH hTS).vert a)
      ext v
      have h' := congrArg (fun g ↦ (ModuleCat.Hom.hom g) v) this
      change ((extHomP hTS hX hX e).app ((incH hTS).vert a)).hom v = 0 at h'
      rw [extHomP_app_inc] at h'
      exact h'
    · right
      refine Rep.hom_ext fun a ↦ ?_
      ext v
      have h' := congrArg (fun g ↦ (ModuleCat.Hom.hom (g.app ((incH hTS).vert a))) v) h1
      change ((extHomP hTS hX hX e).app ((incH hTS).vert a)).hom v = v at h'
      rw [extHomP_app_inc] at h'
      exact h'

end LargeIndecomposable.RayCat
