module

public import LargeIndecomposable.Modules.Idempotents.IdemProj

/-!
# Auslander's argument for successors

The dual of `auslander'`: if the objects of a class `P` (indecomposable, nonzero, of bounded
dimension) have left almost split families inside `P`, any indecomposable `N` receiving a nonzero
map from a `P`-object is isomorphic to a `P`-object (`auslanderL`). Left almost split families
into nonzero indecomposables exist (`exists_lasFam`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- Appending a non-bijective map at the end of a chain. -/
lemma Chain.snoc {P : FDMod k A → Prop} {X Z : FDMod k A} {n : ℕ} {c : X ⟶ Z}
    (h : Chain P n c) {W : FDMod k A} (hW : P W) (g : Z ⟶ W)
    (hg : ¬Function.Bijective (FDMod.lin g)) : Chain P (n + 1) (c ≫ g) := by
  induction h with
  | nil hX =>
    rw [Category.id_comp, ← Category.comp_id g]
    exact Chain.cons g hX hg (Chain.nil hW)
  | cons g' hX' hg' hc ih =>
    rw [Category.assoc]
    exact Chain.cons g' hX' hg' (ih g hg)

lemma Chain.target {P : FDMod k A → Prop} {X Z : FDMod k A} {n : ℕ} {c : X ⟶ Z}
    (h : Chain P n c) : P Z := by
  induction h with
  | nil hX => exact hX
  | cons _ _ _ _ ih => exact ih

/-- A left almost split family out of `X` with targets in `P`. -/
structure LASFam (P : FDMod k A → Prop) (X : FDMod k A) where
  ι : Type u
  [fin : Fintype ι]
  E : ι → FDMod k A
  hE : ∀ i, P (E i)
  f : ∀ i, X ⟶ E i
  notSplit : ¬∃ h : ∀ i, E i ⟶ X, ∑ i, FDMod.lin (h i) ∘ₗ FDMod.lin (f i) = LinearMap.id
  factor : ∀ (W : FDMod k A) (v : X ⟶ W),
    (¬∃ r : W ⟶ X, FDMod.lin r ∘ₗ FDMod.lin v = LinearMap.id) →
      ∃ h : ∀ i, E i ⟶ W, FDMod.lin v = ∑ i, FDMod.lin (h i) ∘ₗ FDMod.lin (f i)

attribute [instance] LASFam.fin

lemma LASFam.not_bijective {P : FDMod k A → Prop} {X : FDMod k A} (F : LASFam P X) (i : F.ι) :
    ¬Function.Bijective (FDMod.lin (F.f i)) := by
  classical
  intro hb
  let e := LinearEquiv.ofBijective (FDMod.lin (F.f i)) hb
  apply F.notSplit
  refine ⟨Function.update (fun j ↦ (FDMod.ofLin ((0 : F.E j →ₗ[A] X)))) i (FDMod.ofLin e.symm.toLinearMap), ?_⟩
  rw [Finset.sum_eq_single i]
  · ext x
    simp only [Function.update_self, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe,
      id_eq]
    exact e.symm_apply_apply x
  · intro j _ hj
    simp only [Function.update_of_ne hj]
    exact LinearMap.zero_comp _
  · simp

/-- A split monomorphism from a nonzero module into an indecomposable is bijective. -/
lemma bijective_of_splitMono {X N : FDMod k A} (hN : IsIndecMod A N) (hX : Nontrivial X)
    (f : X ⟶ N) (r : N ⟶ X) (hr : FDMod.lin r ∘ₗ FDMod.lin f = LinearMap.id) :
    Function.Bijective (FDMod.lin f) := by
  have hrb := bijective_of_split hN hX r f hr
  have hl : Function.LeftInverse (FDMod.lin r) (FDMod.lin f) := fun x ↦ LinearMap.congr_fun hr x
  refine ⟨hl.injective, fun y ↦ ⟨FDMod.lin r y, hrb.1 ?_⟩⟩
  rw [hl]

/-- **Auslander's argument for successors.** -/
theorem auslanderL {P : FDMod k A → Prop} {b : ℕ} (hind : ∀ X, P X → IsIndecMod A X)
    (hdim : ∀ X, P X → finrank k X ≤ b) (hnt : ∀ X, P X → Nontrivial X)
    (fam : ∀ X, P X → Nonempty (LASFam P X))
    (N : FDMod k A) (hN : IsIndecMod A N) (X₀ : FDMod k A) (hX₀ : P X₀) (f₀ : X₀ ⟶ N)
    (hf₀ : FDMod.lin f₀ ≠ 0) :
    ∃ X, P X ∧ ∃ f : X ⟶ N, Function.Bijective (FDMod.lin f) := by
  classical
  by_contra hno
  push Not at hno
  have step : ∀ t, ∃ (X : FDMod k A) (c : X₀ ⟶ X) (f : X ⟶ N), Chain P t c ∧
      FDMod.lin (c ≫ f) ≠ 0 := by
    intro t
    induction t with
    | zero => exact ⟨X₀, 𝟙 X₀, f₀, Chain.nil hX₀, by simpa using hf₀⟩
    | succ t ih =>
      obtain ⟨X, c, f, hc, hfc⟩ := ih
      have hX : P X := hc.target
      obtain ⟨F⟩ := fam X hX
      have hns : ¬∃ r : N ⟶ X, FDMod.lin r ∘ₗ FDMod.lin f = LinearMap.id := by
        rintro ⟨r, hr⟩
        exact hno X hX f (bijective_of_splitMono hN (hnt X hX) f r hr)
      obtain ⟨h, hh⟩ := F.factor N f hns
      have : ∃ i, FDMod.lin (h i) ∘ₗ FDMod.lin (F.f i) ∘ₗ FDMod.lin c ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hfc
        rw [FDMod.lin_comp, hh]
        ext x
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply,
          LinearMap.zero_apply]
        exact Finset.sum_eq_zero fun i _ ↦ by
          simpa using LinearMap.congr_fun (hall i) x
      obtain ⟨i, hi⟩ := this
      exact ⟨F.E i, c ≫ F.f i, h i, hc.snoc (F.hE i) (F.f i) (F.not_bijective i),
        by simpa [FDMod.lin_comp, LinearMap.comp_assoc] using hi⟩
  obtain ⟨X, c, f, hc, hfc⟩ := step (2 ^ b - 1)
  apply hfc
  rw [FDMod.lin_comp, hc.eq_zero hind hdim, LinearMap.comp_zero]

/-- **Left almost split families out of nonzero indecomposables**, with nonzero indecomposable
targets. -/
theorem exists_lasFam [FiniteDimensional k A] (X : FDMod k A) (hX : IndNT X) :
    Nonempty (LASFam IndNT X) := by
  classical
  haveI := hX.2
  haveI := hX.1.isLocalRing (k := k)
  obtain ⟨E, f, hf⟩ := FDMod.exists_leftAS X
  obtain ⟨d⟩ := FDMod.exists_decomp E
  have hsum : ∀ x : E, ∑ j, FDMod.lin (d.inc j) (FDMod.lin (d.proj j) x) = x := fun x ↦ by
    simpa using LinearMap.congr_fun d.sum_id x
  refine ⟨LASFam.mk d.ι d.obj (fun i ↦ ⟨d.indec i, d.nt i⟩) (fun i ↦ f ≫ d.proj i) ?_ ?_⟩
  · rintro ⟨h, hh⟩
    apply hf.1
    refine ⟨(FDMod.ofLin (show E →ₗ[A] X from ∑ i, FDMod.lin (h i) ∘ₗ FDMod.lin (d.proj i))), ?_⟩
    apply FDMod.hom_ext; apply LinearMap.ext; intro x
    have := LinearMap.congr_fun hh x
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply, FDMod.lin_comp,
      LinearMap.id_coe, id_eq] at this
    change (∑ i, FDMod.lin (h i) ∘ₗ FDMod.lin (d.proj i)) (FDMod.lin f x) = x
    simpa [LinearMap.sum_apply] using this
  · intro W v hv
    obtain ⟨t, ht⟩ := hf.2 W v fun ⟨r, hr⟩ ↦ hv ⟨r, ((FDMod.comp_eq_id_iff _ _).1 hr)⟩
    refine ⟨fun i ↦ d.inc i ≫ t, ?_⟩
    rw [← ht]
    ext x
    simp only [FDMod.lin_comp, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply]
    rw [← map_sum (FDMod.lin t), hsum]

end LargeIndecomposable.AR
