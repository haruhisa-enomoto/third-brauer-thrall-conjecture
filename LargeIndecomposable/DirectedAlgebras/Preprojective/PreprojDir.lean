module

public import LargeIndecomposable.AuslanderReiten.Lengths.Lemma24b

/-!
# Preprojective components and directedness

A preprojective component contains the summands of minimal right almost split maps into its
members and has left almost split families inside it, so with a global bound it is a closed class
(`PreprojComp.closedClass`). Hence a connected algebra of bounded representation length with a
preprojective component is representation-directed (`directing_of_preproj`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

namespace PreprojComp

variable {𝒞 : FDMod k A → Prop} (h𝒞 : PreprojComp 𝒞)
include h𝒞

lemma pred_chosen (X : FDMod k A) (hX : 𝒞 X) (i : (chosenMin X (h𝒞.indNT X hX)).d.ι) :
    𝒞 ((chosenMin X (h𝒞.indNT X hX)).d.obj i) :=
  h𝒞.pred _ _ hX ⟨(chosenMin X _).d.indec i, (chosenMin X _).d.nt i⟩ _
    (isIrr_summand (chosenMin X _).hg (chosenMin X _).hmin (h𝒞.indNT X hX) (chosenMin X _).d i)

/-- Left almost split families inside a preprojective component. -/
lemma lasFam (X : FDMod k A) (hX : 𝒞 X) : Nonempty (LASFam 𝒞 X) := by
  classical
  have hXi := h𝒞.indNT X hX
  haveI := hXi.2
  haveI := hXi.1.isLocalRing (k := k)
  obtain ⟨E, f, hf, hmin⟩ := exists_minimal_leftAS X
  obtain ⟨d⟩ := FDMod.exists_decomp E
  have hsum : ∀ x : E, ∑ j, FDMod.lin (d.inc j) (FDMod.lin (d.proj j) x) = x := fun x ↦ by
    simpa using LinearMap.congr_fun d.sum_id x
  refine ⟨LASFam.mk d.ι d.obj (fun i ↦ h𝒞.succ X _ hX ⟨d.indec i, d.nt i⟩ _
    (isIrr_summandL hf hmin hXi d i)) (fun i ↦ f ≫ d.proj i) ?_ ?_⟩
  · rintro ⟨h, hh⟩
    apply hf.1
    refine ⟨show E →ₗ[A] X from ∑ i, FDMod.lin (h i) ∘ₗ FDMod.lin (d.proj i), ?_⟩
    apply LinearMap.ext; intro x
    have := LinearMap.congr_fun hh x
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply, FDMod.lin_comp,
      LinearMap.id_coe, id_eq] at this
    change (∑ i, FDMod.lin (h i) ∘ₗ FDMod.lin (d.proj i)) (FDMod.lin f x) = x
    simpa [LinearMap.sum_apply] using this
  · intro W v hv
    obtain ⟨t, ht⟩ := hf.2 W v fun ⟨r, hr⟩ ↦ hv ⟨r, hr⟩
    refine ⟨fun i ↦ d.inc i ≫ t, ?_⟩
    rw [← ht]
    ext x
    simp only [FDMod.lin_comp, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply]
    rw [← map_sum (FDMod.lin t), hsum]

/-- With a global bound, a preprojective component is a closed class. -/
lemma closedClass (hb : ∃ b, ∀ N : FDMod k A, IndNT N → finrank k N ≤ b) : ClosedClass 𝒞 where
  indNT := h𝒞.indNT
  iso := h𝒞.iso
  pred := h𝒞.pred_chosen
  las := h𝒞.lasFam
  bound := by
    obtain ⟨b, hb⟩ := hb
    exact ⟨b, fun X hX ↦ hb X (h𝒞.indNT X hX)⟩

end PreprojComp

/-- **A connected algebra of bounded representation length with a preprojective component is
representation-directed.** -/
theorem directing_of_preproj {ι : Type} [Fintype ι] (e : ι → A) (he : ∀ x, IsIdempotentElem (e x))
    (hsum : ∑ x, e x = 1) (hP : ∀ x, IndNT (projE (k := k) (he x)))
    (hconn : ∀ S : Set ι, S.Nonempty →
      (∀ x y, x ∈ S → (∃ a, e x * a * e y ≠ 0) ∨ (∃ a, e y * a * e x ≠ 0) → y ∈ S) →
        S = Set.univ)
    (hb : ∃ b, ∀ N : FDMod k A, IndNT N → finrank k N ≤ b)
    {𝒞 : FDMod k A → Prop} (h𝒞 : PreprojComp 𝒞) (N : FDMod k A) (hN : IndNT N) :
    Directing N := by
  obtain ⟨M, hM⟩ := h𝒞.nonempty
  exact h𝒞.directing (all_of_closed e he hsum hP hconn (h𝒞.closedClass hb) hM N hN)

end LargeIndecomposable.AR
