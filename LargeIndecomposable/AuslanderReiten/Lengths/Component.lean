module

public import LargeIndecomposable.AuslanderReiten.Lengths.AuslanderL

/-!
# Closed classes of bounded length are everything

A class `𝒦` of nonzero indecomposables, closed under isomorphism, containing the summands of the
chosen minimal right almost split maps into its members, with left almost split families inside
`𝒦`, and of bounded dimension, contains every nonzero indecomposable when `A` is connected
(`all_of_closed`). Connected means: for a complete set of orthogonal idempotents `e x`, every
nonempty set of points closed under `e x A e y ≠ 0` in both directions is everything.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- A class closed under predecessors and successors, of bounded dimension. -/
structure ClosedClass (𝒦 : FDMod k A → Prop) : Prop where
  indNT : ∀ X, 𝒦 X → IndNT X
  iso : ∀ X Y, 𝒦 X → IsoM X Y → 𝒦 Y
  pred : ∀ X (hX : 𝒦 X) i, 𝒦 ((chosenMin X (indNT X hX)).d.obj i)
  las : ∀ X, 𝒦 X → Nonempty (LASFam 𝒦 X)
  bound : ∃ b, ∀ X, 𝒦 X → finrank k X ≤ b

namespace ClosedClass

variable {𝒦 : FDMod k A → Prop} (h𝒦 : ClosedClass 𝒦)
include h𝒦

/-- A nonzero map into a member comes from a member. -/
lemma mem_of_hom_to {N X : FDMod k A} (hN : IsIndecMod A N) (hX : 𝒦 X) (f : N ⟶ X)
    (hf : FDMod.lin f ≠ 0) : 𝒦 N := by
  obtain ⟨b, hb⟩ := h𝒦.bound
  obtain ⟨Y, hY, g, hg⟩ := auslander' (P := 𝒦) (b := b) (fun X h ↦ (h𝒦.indNT X h).1) hb
    (fun X h ↦ (h𝒦.indNT X h).2)
    (fun X h ↦ ⟨(chosenMin X (h𝒦.indNT X h)).fam 𝒦 (h𝒦.pred X h)⟩) N hN X hX f hf
  exact h𝒦.iso Y N hY (IsoM.symm ⟨g, hg⟩)

/-- A nonzero map from a member goes to a member. -/
lemma mem_of_hom_from {N X : FDMod k A} (hN : IsIndecMod A N) (hX : 𝒦 X) (f : X ⟶ N)
    (hf : FDMod.lin f ≠ 0) : 𝒦 N := by
  obtain ⟨b, hb⟩ := h𝒦.bound
  obtain ⟨Y, hY, g, hg⟩ := auslanderL (P := 𝒦) (b := b) (fun X h ↦ (h𝒦.indNT X h).1) hb
    (fun X h ↦ (h𝒦.indNT X h).2) h𝒦.las N hN X hX f hf
  exact h𝒦.iso Y N hY ⟨g, hg⟩

end ClosedClass

/-- A nonzero element of `eM` gives a nonzero map `Ae → M`. -/
lemma hom_ne_zero_of_eSub {e : A} (he : IsIdempotentElem e) {M : FDMod k A} (m : M)
    (hm : e • m = m) (hm0 : m ≠ 0) :
    ∃ f : projE (k := k) he ⟶ M, FDMod.lin f ≠ 0 := by
  refine ⟨(homProjEquiv (k := k) he M).symm ⟨m, hm⟩, fun h ↦ hm0 ?_⟩
  have := LinearMap.congr_fun h ⟨e, e_mem he⟩
  change e • m = 0 at this
  rwa [hm] at this

/-- **Closed classes of bounded length are everything.** -/
theorem all_of_closed {ι : Type} [Fintype ι] (e : ι → A) (he : ∀ x, IsIdempotentElem (e x))
    (hsum : ∑ x, e x = 1)
    (hP : ∀ x, IndNT (projE (k := k) (he x)))
    (hconn : ∀ S : Set ι, S.Nonempty →
      (∀ x y, x ∈ S → (∃ a, e x * a * e y ≠ 0) ∨ (∃ a, e y * a * e x ≠ 0) → y ∈ S) →
        S = Set.univ)
    {𝒦 : FDMod k A → Prop} (h𝒦 : ClosedClass 𝒦) {M : FDMod k A} (hM : 𝒦 M)
    (N : FDMod k A) (hN : IndNT N) : 𝒦 N := by
  classical
  -- every nonzero module is reached from some `P(x)`
  have hreach : ∀ L : FDMod k A, Nontrivial L →
      ∃ x, ∃ f : projE (k := k) (he x) ⟶ L, FDMod.lin f ≠ 0 := by
    intro L hL
    obtain ⟨l, hl⟩ := exists_ne (0 : L)
    by_contra hall
    push Not at hall
    apply hl
    have hl1 : l = ∑ x, e x • l := by rw [← Finset.sum_smul, hsum, one_smul]
    rw [hl1]
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    by_contra hx
    obtain ⟨f, hf⟩ := hom_ne_zero_of_eSub (he x) (e x • l) (by rw [← mul_smul, (he x).eq]) hx
    exact hf (hall x f)
  -- a nonzero `e x a e y` gives a nonzero map `P(x) → P(y)`
  have hmap : ∀ x y, (∃ a, e x * a * e y ≠ 0) →
      ∃ f : projE (k := k) (he x) ⟶ projE (he y), FDMod.lin f ≠ 0 := by
    rintro x y ⟨a, ha⟩
    have hmem : e x * a * e y ∈ leftIdeal (he y) := by
      change e x * a * e y * e y = e x * a * e y
      rw [mul_assoc, (he y).eq]
    refine hom_ne_zero_of_eSub (he x) (M := projE (he y)) ⟨_, hmem⟩ ?_ ?_
    · apply Subtype.ext
      change e x * (e x * a * e y) = e x * a * e y
      rw [← mul_assoc, ← mul_assoc, (he x).eq]
    · intro h
      exact ha (congrArg Subtype.val h)
  let S : Set ι := {x | 𝒦 (projE (k := k) (he x))}
  have hS : S = Set.univ := by
    apply hconn
    · obtain ⟨x, f, hf⟩ := hreach M (h𝒦.indNT M hM).2
      exact ⟨x, h𝒦.mem_of_hom_to (hP x).1 hM f hf⟩
    · intro x y hx hxy
      rcases hxy with h | h
      · obtain ⟨f, hf⟩ := hmap x y h
        exact h𝒦.mem_of_hom_from (hP y).1 hx f hf
      · obtain ⟨f, hf⟩ := hmap y x h
        exact h𝒦.mem_of_hom_to (hP y).1 hx f hf
  obtain ⟨x, f, hf⟩ := hreach N hN.2
  have hx : x ∈ S := hS ▸ Set.mem_univ x
  exact h𝒦.mem_of_hom_from hN.1 hx f hf

end LargeIndecomposable.AR
