module

public import LargeIndecomposable.Crowns.Basic.CrownFunctor
public import LargeIndecomposable.RayCategories.Basic.Prefix

/-!
# Unbounded chains contain closed chains

In a finite ray category, a chain longer than twice the number of morphisms
repeats one of its peak entries; the segment between two occurrences is a
closed chain (`RayCat.exists_closedChain`). Hence an algebra with a twisted
multiplicative basis over a finite ray category with unbounded chains is
representation-infinite (`RayCat.chainBounded_of_isRepresentationFinite`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayQuiver

universe u

namespace RayCat

variable {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] [IsRayCategory Q]

section Triple

variable {a g b : RayMor Q} (hP : Peak a g) (hV : Valley g b)

/-- The middle morphism of a peak followed by a valley, transported to the
endpoints of the neighbours. -/
def midMor : b.1 ⟶ a.2.1 := eqToHom hV.fst.symm ≫ g.2.2 ≫ eqToHom hP.fst.symm

include hP hV

lemma midMor_ne (hg : g.2.2 ≠ 0) : midMor hP hV ≠ 0 := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨g1, g2, g3⟩ := g
  obtain ⟨b1, b2, b3⟩ := b
  obtain ⟨h1 : a2 = g2, -⟩ := hP
  obtain ⟨h2 : g1 = b1, -⟩ := hV
  subst h1 h2
  simpa [midMor] using hg

lemma midMor_peak₁ : ¬∃ c : a.1 ⟶ b.1, c ≫ midMor hP hV = a.2.2 := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨g1, g2, g3⟩ := g
  obtain ⟨b1, b2, b3⟩ := b
  obtain ⟨h1 : a2 = g2, hp1, -⟩ := id hP
  obtain ⟨h2 : g1 = b1, -⟩ := id hV
  subst h1 h2
  rintro ⟨c, hc⟩
  exact hp1 ⟨c, by simpa [midMor] using hc⟩

lemma midMor_peak₂ : ¬∃ c : b.1 ⟶ a.1, c ≫ a.2.2 = midMor hP hV := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨g1, g2, g3⟩ := g
  obtain ⟨b1, b2, b3⟩ := b
  obtain ⟨h1 : a2 = g2, -, hp2⟩ := id hP
  obtain ⟨h2 : g1 = b1, -⟩ := id hV
  subst h1 h2
  rintro ⟨c, hc⟩
  exact hp2 ⟨c, by simpa [midMor] using hc⟩

lemma midMor_valley₁ : ¬∃ c : a.2.1 ⟶ b.2.1, midMor hP hV ≫ c = b.2.2 := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨g1, g2, g3⟩ := g
  obtain ⟨b1, b2, b3⟩ := b
  obtain ⟨h1 : a2 = g2, -⟩ := id hP
  obtain ⟨h2 : g1 = b1, hv1, -⟩ := id hV
  subst h1 h2
  rintro ⟨c, hc⟩
  exact hv1 ⟨c, by simpa [midMor] using hc⟩

lemma midMor_valley₂ : ¬∃ c : b.2.1 ⟶ a.2.1, b.2.2 ≫ c = midMor hP hV := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨g1, g2, g3⟩ := g
  obtain ⟨b1, b2, b3⟩ := b
  obtain ⟨h1 : a2 = g2, -⟩ := id hP
  obtain ⟨h2 : g1 = b1, -, hv2⟩ := id hV
  subst h1 h2
  rintro ⟨c, hc⟩
  exact hv2 ⟨c, by simpa [midMor] using hc⟩

end Triple

/-- A closed chain from a sequence of morphisms with peaks at even and valleys
at odd positions. -/
def ClosedChain.ofSeq (m : ℕ) (f : ℕ → RayMor Q)
    (hP : ∀ i : Fin (m + 1), Peak (f (2 * i.1)) (f (2 * i.1 + 1)))
    (hV : ∀ i : Fin (m + 1), Valley (f (2 * i.1 + 1)) (f (2 * (i + 1).1)))
    (hne : ∀ t, (f t).2.2 ≠ 0) : ClosedChain Q m where
  x i := (f (2 * i.1)).1
  z i := (f (2 * i.1)).2.1
  ρ i := (f (2 * i.1)).2.2
  σ i := midMor (hP i) (hV i)
  ρ_ne i := hne _
  σ_ne i := midMor_ne (hP i) (hV i) (hne _)
  peak₁ i := midMor_peak₁ (hP i) (hV i)
  peak₂ i := midMor_peak₂ (hP i) (hV i)
  valley₁ i := midMor_valley₁ (hP i) (hV i)
  valley₂ i := midMor_valley₂ (hP i) (hV i)

lemma link_even {a b : RayMor Q} (t : ℕ) (h : Link (2 * t) a b) : Peak a b := by
  simpa [Link] using h

lemma link_odd {a b : RayMor Q} (t : ℕ) (h : Link (2 * t + 1) a b) : Valley a b := by
  simp only [Link] at h
  rwa [if_neg (by omega)] at h

instance [Finite Q] : Finite (RayMor Q) := by
  have := fun x y : Q ↦ IsRayCategory.finite_hom x y
  infer_instance

/-- **A finite ray category with unbounded chains contains a closed chain.** -/
theorem exists_closedChain [Finite Q] (h : ¬ChainBounded Q) : ∃ m, Nonempty (ClosedChain Q m) := by
  set K := Nat.card (RayMor Q)
  obtain ⟨l, hl, hlen⟩ : ∃ l : List (RayMor Q), IsChain 0 l ∧ 2 * K + 2 < l.length := by
    by_contra hc
    push_neg at hc
    exact h ⟨2 * K + 2, hc⟩
  have : Fintype (RayMor Q) := Fintype.ofFinite _
  obtain ⟨j₁, j₂, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun j : Fin (K + 1) ↦ l[2 * j.1]'(by omega)) (by simp [K, Nat.card_eq_fintype_card])
  -- order the two indices
  obtain ⟨j, j', hjj, hl'⟩ : ∃ j j' : ℕ, ∃ _ : j < j' ∧ j' ≤ K,
      l[2 * j]'(by omega) = l[2 * j']'(by omega) := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h12 | h21
    · exact ⟨j₁, j₂, ⟨h12, by omega⟩, heq⟩
    · exact ⟨j₂, j₁, ⟨h21, by omega⟩, heq.symm⟩
  obtain ⟨hjj, hj'K⟩ := hjj
  set p := j' - j with hp
  have hp0 : 0 < p := by omega
  let f : ℕ → RayMor Q := fun t ↦ l[2 * j + t % (2 * p)]'(by
    have := Nat.mod_lt t (show 0 < 2 * p by omega); omega)
  have hf : ∀ t (ht : t < 2 * p), f t = l[2 * j + t]'(by omega) := fun t ht ↦ by
    simp only [f, Nat.mod_eq_of_lt ht]
  have hlink : ∀ t (ht : t + 1 < 2 * p), Link (2 * j + t) (f t) (f (t + 1)) := fun t ht ↦ by
    rw [hf t (by omega), hf (t + 1) ht]
    have := hl.2 (2 * j + t) (by omega)
    simp only [Nat.add_zero] at this
    simp only [← Nat.add_assoc]
    exact this
  refine ⟨p - 1, ⟨ClosedChain.ofSeq (p - 1) f (fun i ↦ ?_) (fun i ↦ ?_) (fun t ↦ ?_)⟩⟩
  · have hi : i.1 < p := by have := i.2; omega
    have := hlink (2 * i.1) (by omega)
    exact link_even (j + i.1) (by rwa [show 2 * (j + i.1) = 2 * j + 2 * i.1 by ring])
  · have hi : i.1 < p := by have := i.2; omega
    by_cases hlast : i.1 + 1 < p
    · have hsucc : (i + 1).1 = i.1 + 1 := by
        rw [Fin.val_add_one_of_lt]; rw [Fin.lt_def]; simp; omega
      rw [hsucc]
      have := hlink (2 * i.1 + 1) (by omega)
      exact link_odd (j + i.1) (by
        rw [show 2 * (j + i.1) + 1 = 2 * j + (2 * i.1 + 1) by ring]
        rwa [show 2 * (i.1 + 1) = 2 * i.1 + 1 + 1 by ring])
    · have hi' : i.1 = p - 1 := by omega
      have hsucc : (i + 1).1 = 0 := by
        have : i = Fin.last (p - 1) := Fin.ext (by simp [hi'])
        rw [this, Fin.last_add_one]; rfl
      rw [hsucc]
      have h0 : f (2 * 0) = l[2 * j']'(by omega) := by
        rw [Nat.mul_zero, hf 0 (by omega), ← hl']
        simp
      have h1 : f (2 * i.1 + 1) = l[2 * j' - 1]'(by omega) := by
        rw [hf _ (by omega)]
        congr 1
        omega
      rw [h0, h1]
      have := hl.2 (2 * j' - 1) (by omega)
      have h2 : 2 * j' - 1 + 1 = 2 * j' := by omega
      simp only [h2, Nat.add_zero] at this
      exact link_odd (j' - 1) (by rwa [show 2 * (j' - 1) + 1 = 2 * j' - 1 by omega])
  · exact hl.1 _ (List.getElem_mem _)

/-- **Representation-finite algebras with twisted multiplicative bases have
bounded chains.** -/
theorem chainBounded_of_isRepresentationFinite [Fintype Q] [DecidableEq Q] {k : Type u} [Field k]
    [Infinite k] {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k Q A)
    (hA : Statement.IsRepresentationFinite A) : ChainBounded Q := by
  by_contra h
  obtain ⟨m, ⟨C⟩⟩ := exists_closedChain h
  exact C.not_isRepresentationFinite B hA

end RayCat

end LargeIndecomposable
