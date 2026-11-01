module

public import LargeIndecomposable.Modules.KrullSchmidt.IndecomposableFullyFaithful
public import LargeIndecomposable.RepresentationType.Basic.RepresentationFinite
public import LargeIndecomposable.Foundations.CategoryTheory.PreadditiveIndecomposable

/-!
# Two forms of representation-finiteness agree

For a finite-dimensional algebra, `Statement.IsRepresentationFinite` (finitely
generated modules, complements of submodules) agrees with the form of the
ported Cartan-determinant library (finite-dimensional objects of `ModuleCat`,
categorical indecomposability).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

open scoped ModuleCat.Algebra

universe u

variable (k : Type u) [Field k] (A : Type u) [Ring A] [Algebra k A] [FiniteDimensional k A]

lemma isIndecomposable_iff_indecomposable (M : ModuleCat.{u} A) :
    Statement.IsIndecomposable A M ↔ Indecomposable M := by
  rw [Reduction.isIndecomposable_iff, LargeIndecomposable.Foundations.indecomposable_iff_idempotent_eq_zero_or_id]

lemma finite_iff_finite (M : ModuleCat.{u} A) : Module.Finite A M ↔ Module.Finite k M :=
  ⟨fun _ ↦ Module.Finite.trans A M, fun _ ↦ Module.Finite.of_restrictScalars_finite k A M⟩

/-- **The two notions of representation-finiteness agree.** -/
theorem isRepresentationFinite_iff_moduleForm :
    Statement.IsRepresentationFinite A ↔ LargeIndecomposable.IsRepresentationFinite k A := by
  classical
  constructor
  · rintro ⟨n, X, hX⟩
    let good : Finset (Fin n) := Finset.univ.filter fun i ↦
      Module.Finite k (X i) ∧ Indecomposable (X i)
    let e := good.equivFin
    refine ⟨good.card, fun j ↦ X (e.symm j).1, fun j ↦ ?_, fun M hM ↦ ?_⟩
    · exact (Finset.mem_filter.1 (e.symm j).2).2
    · obtain ⟨hfin, hind⟩ := hM
      have : Module.Finite A M := (finite_iff_finite k A M).2 hfin
      obtain ⟨i, ⟨φ⟩⟩ := hX M ((isIndecomposable_iff_indecomposable A M).2 hind)
      have hφ : M ≅ X i := φ.toModuleIso
      have hi : i ∈ good := Finset.mem_filter.2 ⟨Finset.mem_univ _,
        Module.Finite.equiv (φ.restrictScalars k),
        hind.of_iso hφ⟩
      refine ⟨e ⟨i, hi⟩, ⟨hφ.trans (eqToIso ?_)⟩⟩
      simp
  · rintro ⟨n, X, -, hX⟩
    refine Reduction.isRepresentationFinite_of_cover n X fun M _ hM ↦ ?_
    exact hX M ⟨(finite_iff_finite k A M).1 inferInstance,
      (isIndecomposable_iff_indecomposable A M).1 hM⟩

end LargeIndecomposable
