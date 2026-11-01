module

public import Mathlib

/-!
# Potentials on hyperforests

Let `T` be a finite set of hyperedges `E M ⊆ α`, each with a function `r M : α → ℤ`. We look
for `w : α → ℤ` such that `w e + r M e` is constant on each hyperedge. If two points of a
hyperedge `M` are never joined by a walk through the other hyperedges (Berge-acyclicity),
such `w` exists (`exists_potential`): add the hyperedges one at a time and shift each
component of the previous ones independently.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

variable {α ι : Type*} (E : ι → Set α) (r : ι → α → ℤ)

/-- Two points lie in a common hyperedge from `X`. -/
def HAdj (X : Set ι) (e e' : α) : Prop := ∃ M ∈ X, e ∈ E M ∧ e' ∈ E M

/-- Berge-acyclicity: points of a hyperedge are not joined through the other hyperedges. -/
def HAcyclic (T : Set ι) : Prop :=
  ∀ M ∈ T, ∀ e ∈ E M, ∀ e' ∈ E M, Relation.EqvGen (HAdj E (T \ {M})) e e' → e = e'

variable {E}

lemma HAcyclic.mono {T T' : Set ι} (h : HAcyclic E T) (hT : T' ⊆ T) : HAcyclic E T' := by
  intro M hM e he e' he' hc
  refine h M (hT hM) e he e' he' ?_
  refine Relation.EqvGen.mono (r := HAdj E (T' \ {M})) (fun a b ⟨M', hM', ha, hb⟩ ↦
    ⟨M', ⟨hT hM'.1, hM'.2⟩, ha, hb⟩) _ _ hc

/-- **Potentials on a finite hyperforest.** -/
theorem exists_potential [DecidableEq ι] (T : Finset ι) (hT : HAcyclic E (T : Set ι)) :
    ∃ w : α → ℤ, ∀ M ∈ T, ∀ e ∈ E M, ∀ e' ∈ E M, w e + r M e = w e' + r M e' := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, fun M hM ↦ absurd hM (Finset.notMem_empty M)⟩
  | @insert M T hMT ih =>
    obtain ⟨w, hw⟩ := ih (hT.mono (by simp))
    -- components of the old hyperedges
    let C : α → α → Prop := Relation.EqvGen (HAdj E (T : Set ι))
    have hCM : ∀ e₀ ∈ E M, ∀ e₁ ∈ E M, C e₀ e₁ → e₀ = e₁ := by
      intro e₀ h₀ e₁ h₁ hc
      refine hT M (by simp) e₀ h₀ e₁ h₁ ?_
      have hsub : ∀ a b, HAdj E (T : Set ι) a b →
          HAdj E (((insert M T : Finset ι) : Set ι) \ {M}) a b := by
        rintro a b ⟨M', hM', ha, hb⟩
        refine ⟨M', ⟨by simp [Finset.mem_coe.1 hM'], ?_⟩, ha, hb⟩
        rintro h
        rw [Set.mem_singleton_iff.1 h] at hM'
        exact hMT hM'
      exact Relation.EqvGen.mono (r := HAdj E (T : Set ι)) hsub _ _ hc
    let shift : α → ℤ := fun e ↦
      if h : ∃ e₀ ∈ E M, C e₀ e then -r M h.choose - w h.choose else 0
    have hshift : ∀ e e', C e e' → shift e = shift e' := by
      intro e e' hee'
      have hiff : (∃ e₀ ∈ E M, C e₀ e) ↔ (∃ e₀ ∈ E M, C e₀ e') :=
        ⟨fun ⟨e₀, h₀, hc⟩ ↦ ⟨e₀, h₀, hc.trans _ _ _ hee'⟩,
          fun ⟨e₀, h₀, hc⟩ ↦ ⟨e₀, h₀, hc.trans _ _ _ hee'.symm⟩⟩
      by_cases h : ∃ e₀ ∈ E M, C e₀ e
      · have h' := hiff.1 h
        simp only [shift, dif_pos h, dif_pos h']
        have := hCM _ h.choose_spec.1 _ h'.choose_spec.1
          (h.choose_spec.2.trans _ _ _ (hee'.trans _ _ _ h'.choose_spec.2.symm))
        rw [this]
      · have h' : ¬∃ e₀ ∈ E M, C e₀ e' := fun h' ↦ h (hiff.2 h')
        simp only [shift, dif_neg h, dif_neg h']
    refine ⟨fun e ↦ w e + shift e, fun M' hM' e he e' he' ↦ ?_⟩
    rcases Finset.mem_insert.1 hM' with rfl | hM'
    · have hself : ∀ e ∈ E M', shift e = -r M' e - w e := by
        intro e he
        have h : ∃ e₀ ∈ E M', C e₀ e := ⟨e, he, Relation.EqvGen.refl _⟩
        simp only [shift, dif_pos h]
        rw [hCM _ h.choose_spec.1 _ he h.choose_spec.2]
      simp only [hself e he, hself e' he']
      ring
    · have hc : C e e' := Relation.EqvGen.rel _ _ ⟨M', hM', he, he'⟩
      have := hw M' hM' e he e' he'
      simp only [hshift e e' hc]
      linarith

end LargeIndecomposable.RayCat
