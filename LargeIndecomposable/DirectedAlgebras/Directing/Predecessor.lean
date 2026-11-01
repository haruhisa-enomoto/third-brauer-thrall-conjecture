module

public import LargeIndecomposable.AuslanderReiten.Irreducible.Irreducible
public import LargeIndecomposable.Modules.KrullSchmidt.Fitting

/-!
# Predecessors

`auslander'` is Auslander's argument started from a given nonzero map: if the objects of a class
`P` (indecomposable, nonzero, of bounded dimension) have right almost split families inside `P`,
any indecomposable `N` with a nonzero map into a `P`-object is isomorphic to a `P`-object.

For each nonzero indecomposable we choose the family given by a decomposition of a minimal right
almost split map (`minRASFam`); the predecessors of `U` (`PredC U`) are `U` and, recursively, the
sources of these families. If the predecessors of `U` have bounded dimension, every indecomposable
with a nonzero map into `U` is isomorphic to a predecessor (`iso_pred_of_hom`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- **Auslander's argument from a given nonzero map.** -/
theorem auslander' {P : FDMod k A → Prop} {b : ℕ} (hind : ∀ X, P X → IsIndecMod A X)
    (hdim : ∀ X, P X → finrank k X ≤ b) (hnt : ∀ X, P X → Nontrivial X)
    (fam : ∀ X, P X → Nonempty (RASFam P X))
    (N : FDMod k A) (hN : IsIndecMod A N) (X₀ : FDMod k A) (hX₀ : P X₀) (f₀ : N ⟶ X₀)
    (hf₀ : FDMod.lin f₀ ≠ 0) :
    ∃ X, P X ∧ ∃ f : N ⟶ X, Function.Bijective (FDMod.lin f) := by
  classical
  by_contra hno
  push Not at hno
  have step : ∀ t, ∃ (X : FDMod k A) (c : X ⟶ X₀) (f : N ⟶ X), Chain P t c ∧
      FDMod.lin (f ≫ c) ≠ 0 := by
    intro t
    induction t with
    | zero => exact ⟨X₀, 𝟙 X₀, f₀, Chain.nil hX₀, by simpa using hf₀⟩
    | succ t ih =>
      obtain ⟨X, c, f, hc, hfc⟩ := ih
      have hX := hc.source
      obtain ⟨F⟩ := fam X hX
      have hns : ¬∃ s : X ⟶ N, FDMod.lin f ∘ₗ FDMod.lin s = LinearMap.id := by
        rintro ⟨s, hs⟩
        exact hno X hX f (bijective_of_split hN (hnt X hX) f s hs)
      obtain ⟨h, hh⟩ := F.factor N f hns
      have : ∃ i, FDMod.lin c ∘ₗ FDMod.lin (F.g i) ∘ₗ FDMod.lin (h i) ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hfc
        rw [FDMod.lin_comp, hh]
        ext x
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply, map_sum,
          LinearMap.zero_apply]
        exact Finset.sum_eq_zero fun i _ ↦ by
          simpa using LinearMap.congr_fun (hall i) x
      obtain ⟨i, hi⟩ := this
      exact ⟨F.E i, F.g i ≫ c, h i, Chain.cons (F.g i) (F.hE i) (F.not_bijective i) hc,
        by simpa [FDMod.lin_comp, LinearMap.comp_assoc] using hi⟩
  obtain ⟨X, c, f, hc, hfc⟩ := step (2 ^ b - 1)
  apply hfc
  rw [FDMod.lin_comp, hc.eq_zero hind hdim, LinearMap.zero_comp]

/-- Nonzero indecomposable objects. -/
def IndNT (X : FDMod k A) : Prop := IsIndecMod A X ∧ Nontrivial X

/-- A minimal right almost split map with a decomposition of its source. -/
structure MinRAS (Z : FDMod k A) where
  E : FDMod k A
  g : E ⟶ Z
  d : Decomp E
  hg : IsRightAS g
  hmin : ∀ φ : E ⟶ E, φ ≫ g = g → Function.Bijective (FDMod.lin φ)

lemma exists_minRAS [FiniteDimensional k A] (Z : FDMod k A) (hZ : IndNT Z) :
    Nonempty (MinRAS Z) := by
  haveI := hZ.2
  haveI := hZ.1.isLocalRing (k := k)
  obtain ⟨E, g, hg, hmin⟩ := exists_minimal_rightAS Z
  obtain ⟨d⟩ := FDMod.exists_decomp E
  exact ⟨⟨E, g, d, hg, hmin⟩⟩

/-- **The right almost split family of a minimal right almost split map**, with sources in any
class containing the summands. -/
def MinRAS.fam {Z : FDMod k A} (M : MinRAS Z) (P : FDMod k A → Prop) (hP : ∀ i, P (M.d.obj i)) :
    RASFam P Z := by
  classical
  refine RASFam.mk M.d.ι M.d.obj hP (fun i ↦ M.d.inc i ≫ M.g) ?_ ?_
  · rintro ⟨h, hh⟩
    apply M.hg.1
    refine ⟨show Z →ₗ[A] M.E from ∑ i, FDMod.lin (M.d.inc i) ∘ₗ FDMod.lin (h i), ?_⟩
    show FDMod.lin M.g ∘ₗ (∑ i, FDMod.lin (M.d.inc i) ∘ₗ FDMod.lin (h i)) = LinearMap.id
    rw [← hh]
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply, map_sum,
      FDMod.lin_comp]
  · intro W v hv
    obtain ⟨t, ht⟩ := M.hg.2 W v fun ⟨s, hs⟩ ↦ hv ⟨s, hs⟩
    refine ⟨fun i ↦ t ≫ M.d.proj i, ?_⟩
    have hid := M.d.sum_id
    rw [← ht]
    ext x
    have := LinearMap.congr_fun hid (FDMod.lin t x)
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe,
      id_eq] at this
    simp only [FDMod.lin_comp, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply]
    rw [← map_sum (FDMod.lin M.g), this]

variable [FiniteDimensional k A]

/-- The chosen minimal right almost split map into a nonzero indecomposable. -/
def chosenMin (Z : FDMod k A) (hZ : IndNT Z) : MinRAS Z := Classical.choice (exists_minRAS Z hZ)

/-- The predecessors of `U`: `U` and, recursively, the summands of the chosen minimal right almost
split maps. -/
inductive PredC (U : FDMod k A) : FDMod k A → Prop
  | self (hU : IndNT U) : PredC U U
  | step {X : FDMod k A} (h : PredC U X) (hX : IndNT X) (i : (chosenMin X hX).d.ι) :
      PredC U ((chosenMin X hX).d.obj i)

lemma PredC.indNT {U X : FDMod k A} (h : PredC U X) : IndNT X := by
  cases h with
  | self hU => exact hU
  | step _ hX i => exact ⟨(chosenMin _ hX).d.indec i, (chosenMin _ hX).d.nt i⟩

/-- **A nonzero map into `U` comes from a predecessor**: if the predecessors of `U` have bounded
dimension, every indecomposable with a nonzero map into `U` is isomorphic to a predecessor. -/
theorem iso_pred_of_hom {U : FDMod k A} (hU : IndNT U) {b : ℕ}
    (hb : ∀ X, PredC U X → finrank k X ≤ b) (N : FDMod k A) (hN : IsIndecMod A N)
    (f : N ⟶ U) (hf : FDMod.lin f ≠ 0) :
    ∃ X, PredC U X ∧ ∃ e : N ⟶ X, Function.Bijective (FDMod.lin e) :=
  auslander' (P := PredC U) (fun X h ↦ h.indNT.1) hb (fun X h ↦ h.indNT.2)
    (fun X h ↦ ⟨(chosenMin X h.indNT).fam (PredC U) fun i ↦ PredC.step h h.indNT i⟩)
    N hN U (PredC.self hU) f hf

end LargeIndecomposable.AR
