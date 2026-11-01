module

public import LargeIndecomposable.BongartzTheorem.LongLines.LineBand

/-!
# Paths inside a line of the cover

The points of a line form a finite convex piece `S_L` (`CLine.finset`). Arrows between points of
the line are unique (`arrow_unique`), directed paths of `D_{S_L}` are monotone along the line
(`path_dir`), and so two paths of `D_{S_L}` with the same ends are equal (`path_unique`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover FinQuiver RayQuiver Classical

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P}

namespace CLine

variable (L : CLine x₀)

/-- The points of the line as a finite set. -/
def finset : Finset (Cover x₀) := (Finset.range (L.n + 1)).image L.pt

lemma mem_finset {c : Cover x₀} : c ∈ L.finset ↔ ∃ a ≤ L.n, L.pt a = c := by
  simp only [finset, Finset.mem_image, Finset.mem_range]
  exact ⟨fun ⟨a, ha, h⟩ ↦ ⟨a, by omega, h⟩, fun ⟨a, ha, h⟩ ↦ ⟨a, by omega, h⟩⟩

lemma coe_finset : (L.finset : Set (Cover x₀)) = L.pts := by
  ext c; exact L.mem_finset

lemma convex_finset : Convex (L.finset : Set (Cover x₀)) := by
  rw [coe_finset]; exact L.convex

/-- The index of a point of the line. -/
def idx (c : Cover x₀) : ℕ := if h : ∃ a ≤ L.n, L.pt a = c then Nat.find h else 0

lemma idx_spec {c : Cover x₀} (hc : ∃ a ≤ L.n, L.pt a = c) : L.idx c ≤ L.n ∧ L.pt (L.idx c) = c := by
  unfold idx
  rw [dif_pos hc]
  exact Nat.find_spec hc

lemma idx_pt {a : ℕ} (ha : a ≤ L.n) : L.idx (L.pt a) = a :=
  L.inj _ _ (L.idx_spec ⟨a, ha, rfl⟩).1 ha (L.idx_spec ⟨a, ha, rfl⟩).2

/-- **Arrows between points of the line are unique.** -/
lemma arrow_unique {c d : Cover x₀} (hc : ∃ a ≤ L.n, L.pt a = c) (hd : ∃ a ≤ L.n, L.pt a = d)
    (f g : c ⟶ d) (hf : IsIrreducible f) (hg : IsIrreducible g) : f = g := by
  obtain ⟨a, ha, rfl⟩ := hc
  obtain ⟨b, hb, rfl⟩ := hd
  rcases L.only a b ha hb f hf with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact L.uniqF a (by omega) f g hf hg
  · exact L.uniqB b (by omega) f g hf hg

/-- **The direction of an arrow between points of the line.** -/
lemma arrow_dir {c d : Cover x₀} (hc : ∃ a ≤ L.n, L.pt a = c) (hd : ∃ a ≤ L.n, L.pt a = d)
    (f : c ⟶ d) (hf : IsIrreducible f) :
    (L.idx d = L.idx c + 1 ∧ L.fwd (L.idx c) = true) ∨
      (L.idx c = L.idx d + 1 ∧ L.fwd (L.idx d) = false) := by
  obtain ⟨a, ha, rfl⟩ := hc
  obtain ⟨b, hb, rfl⟩ := hd
  rw [L.idx_pt ha, L.idx_pt hb]
  exact L.only a b ha hb f hf

/-- The point of a vertex of `D_{S_L}`. -/
abbrev vpt (i : (pieceQuiver L.finset).V) : Cover x₀ := RayCat.pt L.finset i

lemma mem_of_V (i : (pieceQuiver L.finset).V) : ∃ a ≤ L.n, L.pt a = L.vpt i :=
  L.mem_finset.1 i.2

/-- **Directed paths inside the line are monotone.** -/
lemma path_dir : ∀ (le : List (pieceQuiver L.finset).A) (i j : (pieceQuiver L.finset).V),
    PathFrom i le j → le ≠ [] →
      (L.idx (L.vpt j) = L.idx (L.vpt i) + le.length ∧
        L.fwd (L.idx (L.vpt i)) = true) ∨
      (L.idx (L.vpt i) = L.idx (L.vpt j) + le.length ∧
        L.fwd (L.idx (L.vpt i) - 1) = false ∧ 0 < L.idx (L.vpt i))
  | [], _, _, _, h => absurd rfl h
  | α :: le, i, j, h, _ => by
    obtain ⟨h1, h2⟩ := h
    change α.1 = i at h1
    subst h1
    have hd := L.arrow_dir (L.mem_of_V α.1) (L.mem_of_V α.2.1) α.2.2.1 α.2.2.2
    rcases le with _ | ⟨β, le'⟩
    · change α.2.1 = j at h2
      subst h2
      rcases hd with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · left; exact ⟨by simp [e1], e2⟩
      · right; refine ⟨by simp [e1], ?_, by omega⟩
        rw [e1, Nat.add_sub_cancel]; exact e2
    · have ih := path_dir (β :: le') α.2.1 j h2 (List.cons_ne_nil _ _)
      rcases hd with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases ih with ⟨f1, f2⟩ | ⟨f1, f2, f3⟩
      · left; refine ⟨?_, e2⟩; simp only [List.length_cons] at f1 ⊢; omega
      · exfalso; rw [e1, Nat.add_sub_cancel, e2] at f2; exact absurd f2 (by simp)
      · exfalso; rw [e2] at f2; exact absurd f2 (by simp)
      · right; refine ⟨?_, ?_, by omega⟩
        · simp only [List.length_cons] at f1 ⊢; omega
        · rw [e1, Nat.add_sub_cancel]; exact e2

lemma path_fwd (α : (pieceQuiver L.finset).A) (le : List (pieceQuiver L.finset).A)
    (i j : (pieceQuiver L.finset).V) (h : PathFrom i (α :: le) j)
    (hα : L.idx (L.vpt α.2.1) = L.idx (L.vpt i) + 1) (hf : L.fwd (L.idx (L.vpt i)) = true) :
    L.idx (L.vpt j) = L.idx (L.vpt i) + 1 + le.length := by
  obtain ⟨h1, h2⟩ := h
  change α.1 = i at h1
  subst h1
  rcases le with _ | ⟨β, le'⟩
  · change α.2.1 = j at h2
    subst h2
    simpa using hα
  · rcases L.path_dir (β :: le') α.2.1 j h2 (List.cons_ne_nil _ _) with ⟨f1, -⟩ | ⟨-, f2, -⟩
    · rw [f1, hα]
    · rw [hα, Nat.add_sub_cancel, hf] at f2; exact absurd f2 (by simp)

lemma path_bwd (α : (pieceQuiver L.finset).A) (le : List (pieceQuiver L.finset).A)
    (i j : (pieceQuiver L.finset).V) (h : PathFrom i (α :: le) j)
    (hα : L.idx (L.vpt i) = L.idx (L.vpt α.2.1) + 1) (hb : L.fwd (L.idx (L.vpt α.2.1)) = false) :
    L.idx (L.vpt i) = L.idx (L.vpt j) + 1 + le.length := by
  obtain ⟨h1, h2⟩ := h
  change α.1 = i at h1
  subst h1
  rcases le with _ | ⟨β, le'⟩
  · change α.2.1 = j at h2
    subst h2
    simpa using hα
  · rcases L.path_dir (β :: le') α.2.1 j h2 (List.cons_ne_nil _ _) with ⟨-, f2⟩ | ⟨f1, -, -⟩
    · rw [hb] at f2; exact absurd f2 (by simp)
    · rw [hα, f1]; simp only [List.length_cons]; omega

lemma V_eq {i j : (pieceQuiver L.finset).V} (h : L.idx (L.vpt i) = L.idx (L.vpt j)) :
    i = j := by
  apply Subtype.ext
  show L.vpt i = L.vpt j
  rw [← (L.idx_spec (L.mem_of_V i)).2, ← (L.idx_spec (L.mem_of_V j)).2, h]

/-- **Two directed paths inside the line with the same ends are equal.** -/
lemma path_unique : ∀ (le le' : List (pieceQuiver L.finset).A) (i j : (pieceQuiver L.finset).V),
    PathFrom i le j → PathFrom i le' j → le = le'
  | [], [], _, _, _, _ => rfl
  | [], β :: le', i, j, h, h' => by
    exfalso
    change i = j at h
    subst h
    rcases L.path_dir (β :: le') i i h' (List.cons_ne_nil _ _) with ⟨f1, -⟩ | ⟨f1, -⟩ <;>
      simp at f1
  | α :: le, [], i, j, h, h' => by
    exfalso
    change i = j at h'
    subst h'
    rcases L.path_dir (α :: le) i i h (List.cons_ne_nil _ _) with ⟨f1, -⟩ | ⟨f1, -⟩ <;>
      simp at f1
  | α :: le, β :: le', i, j, h, h' => by
    have hsrc : α.1 = β.1 := h.1.trans h'.1.symm
    have dα := L.arrow_dir (L.mem_of_V α.1) (L.mem_of_V α.2.1) α.2.2.1 α.2.2.2
    have dβ := L.arrow_dir (L.mem_of_V β.1) (L.mem_of_V β.2.1) β.2.2.1 β.2.2.2
    have eα : L.idx (L.vpt α.1) = L.idx (L.vpt i) :=
      congrArg (fun v ↦ L.idx (L.vpt v)) (show α.1 = i from h.1)
    have eβ : L.idx (L.vpt β.1) = L.idx (L.vpt i) :=
      congrArg (fun v ↦ L.idx (L.vpt v)) (show β.1 = i from h'.1)
    have htgt : α.2.1 = β.2.1 := by
      apply L.V_eq
      rcases dα with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases dβ with ⟨b1, b2⟩ | ⟨b1, b2⟩
      · omega
      · have := L.path_fwd α le i j h (by rw [← eα]; exact a1) (by rw [← eα]; exact a2)
        have := L.path_bwd β le' i j h' (by rw [← eβ]; exact b1) b2
        omega
      · have := L.path_bwd α le i j h (by rw [← eα]; exact a1) a2
        have := L.path_fwd β le' i j h' (by rw [← eβ]; exact b1) (by rw [← eβ]; exact b2)
        omega
      · omega
    have hαβ : α = β := by
      obtain ⟨a, b, f, hf⟩ := α
      obtain ⟨a', b', g, hg⟩ := β
      change a = a' at hsrc
      change b = b' at htgt
      subst hsrc htgt
      obtain rfl := L.arrow_unique (L.mem_of_V a) (L.mem_of_V b) f g hf hg
      rfl
    subst hαβ
    rw [path_unique le le' α.2.1 j h.2 h'.2]

end CLine

end LargeIndecomposable.RayCat
