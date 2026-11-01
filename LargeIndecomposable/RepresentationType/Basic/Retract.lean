module

public import LargeIndecomposable.Modules.KrullSchmidt.KrullSchmidt
public import LargeIndecomposable.Modules.KrullSchmidt.IndecomposableFullyFaithful
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Representation-finiteness through retracts

Let `R : Mod S ⥤ Mod T` be an additive functor between module categories of
finite-dimensional algebras that sends finite modules to finite modules. If
every finite indecomposable `T`-module is a retract of `R L` for a finite
`S`-module `L`, then `T` is representation-finite when `S` is: each such
module is isomorphic to an indecomposable summand of one of the finitely many
modules `R (B i)`, where the `B i` represent the indecomposable `S`-modules
(Krull–Schmidt). This is the counting step of the cleaving lemma
(Gabriel–Roiter 13.8).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement

universe u

namespace Reduction

variable (k : Type u) [Field k]

attribute [local instance] RestrictScalars.moduleOrig in
lemma finite_restrictScalars {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
    (M : Type u) [AddCommGroup M] [Module A M] [hM : Module.Finite A M] :
    Module.Finite k (RestrictScalars k A M) := by
  have : Module.Finite A (RestrictScalars k A M) := hM
  exact Module.Finite.trans A _

variable {S T : Type u} [Ring S] [Algebra k S] [FiniteDimensional k S]
  [Ring T] [Algebra k T] [FiniteDimensional k T]

/-- A retract of a finite module is finite. -/
lemma finite_of_retract {A : Type u} [Ring A] {N L : ModuleCat.{u} A} [Module.Finite A L]
    (s : N ⟶ L) (p : L ⟶ N) (h : s ≫ p = 𝟙 N) : Module.Finite A N := by
  refine Module.Finite.of_surjective p.hom fun n ↦ ⟨s.hom n, ?_⟩
  change (s ≫ p).hom n = n
  rw [h]
  rfl

include k in
/-- **Representation-finiteness through retracts.** -/
theorem isRepresentationFinite_of_retract (R : ModuleCat.{u} S ⥤ ModuleCat.{u} T) [R.Additive]
    (hfin : ∀ L : ModuleCat.{u} S, Module.Finite S L → Module.Finite T (R.obj L))
    (hret : ∀ N : ModuleCat.{u} T, Module.Finite T N → IsIndecomposable T N →
      ∃ (L : ModuleCat.{u} S) (_ : Module.Finite S L) (s : N ⟶ R.obj L) (p : R.obj L ⟶ N),
        s ≫ p = 𝟙 N)
    (hS : IsRepresentationFinite S) : IsRepresentationFinite T := by
  classical
  obtain ⟨n, B, hB⟩ := hS
  -- decompose each `R (B i)` when it is finite
  have hdec : ∀ i : Fin n, ∃ (m : ℕ) (Y : Fin m → ModuleCat.{u} T),
      (∀ j, IsIndecomposable T (Y j)) ∧
        (Module.Finite T (R.obj (B i)) → Nonempty (R.obj (B i) ≅ ⨁ Y)) := by
    intro i
    by_cases hf : Module.Finite T (R.obj (B i))
    · have := finite_restrictScalars k (A := T) (R.obj (B i))
      obtain ⟨m, Y, hY, e⟩ := KrullSchmidt.exists_iso_biproduct' k (R.obj (B i))
      exact ⟨m, Y, hY, fun _ ↦ e⟩
    · exact ⟨0, Fin.elim0, fun j ↦ j.elim0, fun h ↦ absurd h hf⟩
  choose m Y hY e using hdec
  let Z : (Σ i : Fin n, Fin (m i)) → ModuleCat.{u} T := fun q ↦ Y q.1 q.2
  let ε := finSigmaFinEquiv (m := n) (n := m)
  refine Reduction.isRepresentationFinite_of_cover _ (fun q ↦ Z (ε.symm q)) fun N _ hN ↦ ?_
  obtain ⟨L, _, s, p, hsp⟩ := hret N inferInstance hN
  have := finite_restrictScalars k (A := S) L
  obtain ⟨r, X, hX, ⟨eL⟩⟩ := KrullSchmidt.exists_iso_biproduct' k L
  -- each summand of `L` is a finite indecomposable `S`-module
  have hXfin : ∀ j, Module.Finite S (X j) := fun j ↦
    finite_of_retract (biproduct.ι X j ≫ eL.inv) (eL.hom ≫ biproduct.π X j) (by simp)
  have hσ : ∀ j, ∃ i, Nonempty (X j ≅ B i) := fun j ↦ by
    obtain ⟨i, ⟨φ⟩⟩ := hB (X j) (hX j)
    exact ⟨i, ⟨φ.toModuleIso⟩⟩
  choose σ hσ using hσ
  have hRfin : ∀ j, Module.Finite T (R.obj (B (σ j))) := fun j ↦ by
    have := hfin (X j) (hXfin j)
    obtain ⟨φ⟩ := hσ j
    exact Module.Finite.equiv (R.mapIso φ).toLinearEquiv
  -- `R L ≅ ⨁ⱼ ⨁ₗ Y (σ j) l`
  let eR : R.obj L ≅ ⨁ fun j ↦ ⨁ Y (σ j) :=
    R.mapIso eL ≪≫ R.mapBiproduct X ≪≫
      biproduct.mapIso fun j ↦ R.mapIso (hσ j).some ≪≫ (e (σ j) (hRfin j)).some
  let eR' : R.obj L ≅ ⨁ fun q : Σ j : Fin r, Fin (m (σ j)) ↦ Y (σ q.1) q.2 :=
    eR ≪≫ biproductBiproductIso _ _
  have := finite_restrictScalars k (A := T) N
  obtain ⟨q, ⟨φ⟩⟩ := KrullSchmidt.exists_iso_of_comp_eq_id' k hN (fun q ↦ hY _ _) eR' s p hsp
  refine ⟨ε ⟨σ q.1, q.2⟩, ⟨φ ≪≫ eqToIso ?_⟩⟩
  simp [Z]

end Reduction

end LargeIndecomposable
