module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.SubPieceExt
public import LargeIndecomposable.BongartzTheorem.LongLines.ConvexClosed

/-!
# Critical pieces are connected

If the quiver of a convex piece `C` splits into two arrow-closed parts, an indecomposable
representation lives on one of them (`suppIn_or_suppIn`), and both parts are convex
(`convex_of_closed`). So if all smaller convex pieces are representation-finite, so is `C`
(`connected_of_critical`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver Module

universe u

variable {k : Type u} [Field k]
  {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {C : Finset (Cover x₀)}

/-- The points of a set of vertices of a piece. -/
def ptsOf (T' : Set (pieceQuiver C).V) : Finset (Cover x₀) := by
  classical
  exact C.filter fun c ↦ ∃ h : c ∈ C, (⟨c, h⟩ : (pieceQuiver C).V) ∈ T'

lemma mem_ptsOf {T' : Set (pieceQuiver C).V} (s : (pieceQuiver C).V) :
    (show C from s).1 ∈ ptsOf T' ↔ s ∈ T' := by
  classical
  simp only [ptsOf, Finset.mem_filter]
  exact ⟨fun ⟨_, _, h⟩ ↦ h, fun h ↦ ⟨(show C from s).2, (show C from s).2, h⟩⟩

lemma ptsOf_subset (T' : Set (pieceQuiver C).V) : ptsOf T' ⊆ C := by
  classical
  intro c hc
  simp only [ptsOf, Finset.mem_filter] at hc
  exact hc.1

open Classical in
/-- The projection onto the part of a representation on an arrow-closed set. -/
def partEnd (X : Rep k (pieceQuiver C)) (T' : Set (pieceQuiver C).V)
    (hcl : ∀ α : (pieceQuiver C).A, (pieceQuiver C).src α ∈ T' ↔ (pieceQuiver C).tgt α ∈ T') :
    X ⟶ X where
  app s := if s ∈ T' then 𝟙 _ else 0
  comm α := by
    by_cases hs : (pieceQuiver C).src α ∈ T'
    · rw [if_pos hs, if_pos ((hcl α).1 hs)]
      simp
    · rw [if_neg hs, if_neg fun ht ↦ hs ((hcl α).2 ht)]
      simp

/-- **An indecomposable lives on one side of an arrow-closed splitting.** -/
theorem suppIn_or_suppIn {X : Rep k (pieceQuiver C)} (hind : X.IsIndec)
    (T' : Set (pieceQuiver C).V)
    (hcl : ∀ α : (pieceQuiver C).A, (pieceQuiver C).src α ∈ T' ↔ (pieceQuiver C).tgt α ∈ T') :
    SuppIn (ptsOf T') X ∨ SuppIn (ptsOf T'ᶜ) X := by
  classical
  rcases hind.2 (partEnd X T' hcl) (by
      refine Rep.hom_ext fun s ↦ ?_
      change (if s ∈ T' then 𝟙 _ else 0) ≫ (if s ∈ T' then 𝟙 _ else 0) = if s ∈ T' then 𝟙 _ else 0
      split_ifs <;> simp) with h0 | h1
  · right
    intro s hs
    rw [mem_ptsOf] at hs
    have hsT : s ∈ T' := by simpa using hs
    have := h0 s
    change (if s ∈ T' then 𝟙 _ else 0) = 0 at this
    rw [if_pos hsT] at this
    refine ⟨fun a b ↦ ?_⟩
    have ha := congrArg (fun g ↦ (ModuleCat.Hom.hom g) a) this
    have hb := congrArg (fun g ↦ (ModuleCat.Hom.hom g) b) this
    simp only [ModuleCat.hom_id, LinearMap.id_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at ha hb
    rw [ha, hb]
  · left
    intro s hs
    rw [mem_ptsOf] at hs
    have := congrArg (fun g : X ⟶ X ↦ g.app s) h1
    change (if s ∈ T' then 𝟙 _ else 0) = 𝟙 _ at this
    rw [if_neg hs] at this
    refine ⟨fun a b ↦ ?_⟩
    have ha := congrArg (fun g ↦ (ModuleCat.Hom.hom g) a) this
    have hb := congrArg (fun g ↦ (ModuleCat.Hom.hom g) b) this
    simp only [ModuleCat.hom_id, LinearMap.id_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at ha hb
    rw [← ha, ← hb]

lemma convex_ptsOf (hC : Convex (C : Set (Cover x₀))) (R : Set (pieceQuiver C).V)
    (hR : ∀ α : (pieceQuiver C).A, (pieceQuiver C).src α ∈ R ↔ (pieceQuiver C).tgt α ∈ R) :
    Convex ((ptsOf R : Finset (Cover x₀)) : Set (Cover x₀)) :=
  convex_of_closed hC (fun c hc ↦ ptsOf_subset R hc) fun a b f hf ha hb ↦
    (mem_ptsOf (⟨a, ha⟩ : (pieceQuiver C).V)).trans
      ((hR ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨f, hf⟩⟩).trans (mem_ptsOf (⟨b, hb⟩ : (pieceQuiver C).V)).symm)

open Classical in
/-- A representation of `C` supported in `ptsOf R` restricting to `Y`, if there is one. -/
def pickRep (R : Set (pieceQuiver C).V) (Y : Rep k (pieceQuiver (ptsOf R))) :
    Rep k (pieceQuiver C) :=
  if h : ∃ X : Rep k (pieceQuiver C), (∀ i, FiniteDimensional k (X.obj i)) ∧
      SuppIn (ptsOf R) X ∧ Nonempty (resP (ptsOf_subset R) X ≅ Y) then h.choose
  else zeroRep k C fun _ ↦ 0

lemma iso_pickRep (R : Set (pieceQuiver C).V) (Y : Rep k (pieceQuiver (ptsOf R)))
    {X : Rep k (pieceQuiver C)} (hfin : ∀ i, FiniteDimensional k (X.obj i))
    (hs : SuppIn (ptsOf R) X) (φ : resP (ptsOf_subset R) X ≅ Y) : Nonempty (X ≅ pickRep R Y) := by
  classical
  have h : ∃ X : Rep k (pieceQuiver C), (∀ i, FiniteDimensional k (X.obj i)) ∧
      SuppIn (ptsOf R) X ∧ Nonempty (resP (ptsOf_subset R) X ≅ Y) := ⟨X, hfin, hs, ⟨φ⟩⟩
  obtain ⟨-, hs', ⟨ψ⟩⟩ := h.choose_spec
  have hp : pickRep R Y = h.choose := dif_pos h
  rw [hp]
  exact iso_of_resP_iso (ptsOf_subset R) hs hs' (φ ≪≫ ψ.symm)

/-- **Critical pieces are connected.** -/
theorem connected_of_critical (hC : Convex (C : Set (Cover x₀))) (hrep : ¬PieceRepFin k C)
    (hmin : ∀ C' : Finset (Cover x₀), Convex (C' : Set (Cover x₀)) → C'.card < C.card →
      PieceRepFin k C') :
    ∀ T' : Set (pieceQuiver C).V, T'.Nonempty →
      (∀ α : (pieceQuiver C).A, (pieceQuiver C).src α ∈ T' ↔ (pieceQuiver C).tgt α ∈ T') →
        T' = Set.univ := by
  classical
  intro T' ⟨t, ht⟩ hcl
  by_contra hT
  obtain ⟨u, hu⟩ : ∃ u, u ∉ T' := by
    by_contra h
    push Not at h
    exact hT (Set.eq_univ_of_forall h)
  have hclc : ∀ α : (pieceQuiver C).A, (pieceQuiver C).src α ∈ T'ᶜ ↔ (pieceQuiver C).tgt α ∈ T'ᶜ :=
    fun α ↦ not_congr (hcl α)
  have hlt : ∀ R : Set (pieceQuiver C).V, ∀ v, v ∉ R → (ptsOf R).card < C.card := by
    intro R v hv
    refine Finset.card_lt_card ⟨ptsOf_subset R, fun h ↦ hv ?_⟩
    exact (mem_ptsOf v).1 (h (show C from v).2)
  obtain ⟨nT, YT, hYT⟩ := hmin _ (convex_ptsOf hC T' hcl) (hlt T' u hu)
  obtain ⟨nU, YU, hYU⟩ := hmin _ (convex_ptsOf hC T'ᶜ hclc) (hlt T'ᶜ t (by simpa using ht))
  apply hrep
  refine ⟨nT + nU, Fin.append (fun j ↦ pickRep T' (YT j)) (fun j ↦ pickRep T'ᶜ (YU j)),
    fun X hfin hX hind ↦ ?_⟩
  haveI := hfin
  rcases suppIn_or_suppIn hind T' hcl with hs | hs
  · obtain ⟨j, ⟨φ⟩⟩ := hYT _ inferInstance (respectsCover_resP (ptsOf_subset T') X hX)
      (isIndec_resP (ptsOf_subset T') hs hind)
    refine ⟨Fin.castAdd nU j, ?_⟩
    rw [Fin.append_left]
    exact iso_pickRep T' (YT j) hfin hs φ
  · obtain ⟨j, ⟨φ⟩⟩ := hYU _ inferInstance (respectsCover_resP (ptsOf_subset T'ᶜ) X hX)
      (isIndec_resP (ptsOf_subset T'ᶜ) hs hind)
    refine ⟨Fin.natAdd nT j, ?_⟩
    rw [Fin.append_right]
    exact iso_pickRep T'ᶜ (YU j) hfin hs φ

end LargeIndecomposable.RayCat
