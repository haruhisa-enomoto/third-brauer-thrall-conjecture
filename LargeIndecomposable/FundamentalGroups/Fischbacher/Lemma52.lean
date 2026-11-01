module

public import LargeIndecomposable.FundamentalGroups.Fischbacher.Lemma54E

/-!
# Fischbacher's Lemma 5.2

In a chain-bounded ray category with cancellation that is cycle-free, interval-finite, and in
which every cocycle on a finite convex set is a coboundary there: for paths `v, w : a ⇝ b` and a
point `d` on `v`, a chain joins `d` to a point of `w` (`lemma52`).

The hull-shrinking step (`ZWalk.Good.step`) splits a zero `t`-path into its first arrow, takes a
minimal chain of links between the first arrows of `t` and `s` (separation criterion at the
valley), and applies the case analysis of §5.3–5.4.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

universe v u

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [IsRayCategory A]

variable (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)), p.length = 0)
  (hint : ∀ a b : A, (interval a b).Finite)
  (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
    IsCoboundaryOn D c)
  (hL : LeftCancel A) (hR : RightCancel A) (hCB : ChainBounded A)
include hcf hint hsc hL hR hCB

/-- **The hull-shrinking step** (Fischbacher §5.3–5.4). -/
theorem ZWalk.Good.step {b a₀ : A} {w : Quiver.Path (RayVert.mk a₀) (RayVert.mk b)}
    {z : ZWalk b} (hz : z.Good w) (h0 : ∃ σ ∈ z.segs, pathVal σ.t = 0) :
    ∃ z' : ZWalk b, z'.d₀ = z.d₀ ∧ z'.Good w ∧ z'.hull ⊂ z.hull := by
  obtain ⟨σ, hσ, ht0⟩ := h0
  obtain ⟨L₁, L₂, hsplit⟩ := List.append_of_mem hσ
  obtain ⟨c, dl, d, t, s⟩ := σ
  have htpos := hz.tpos _ hσ
  have hspos := hz.spos _ hσ
  change 0 < t.length at htpos
  change 0 < s.length at hspos
  obtain ⟨ct, γt, t'', -, rfl⟩ := Quiver.Path.eq_toPath_comp_of_length_eq_succ t
    (n := t.length - 1) (by omega)
  obtain ⟨cs, γs, s'', -, rfl⟩ := Quiver.Path.eq_toPath_comp_of_length_eq_succ s
    (n := s.length - 1) (by omega)
  change pathVal (γt.toPath.comp t'') = 0 at ht0
  have ht''pos : 0 < t''.length := by
    by_contra h0
    have hct : ct = RayVert.mk dl := Quiver.Path.eq_of_length_zero t'' (by omega)
    subst hct
    rw [Quiver.Path.eq_nil_of_length_zero t'' (by omega)] at ht0
    apply γt.2.1
    rw [← ht0]
    change γt.1 = 𝟙 _ ≫ γt.1
    rw [Category.id_comp]
  obtain ⟨y₁, t₀, a₁, rfl⟩ := exists_cons_of_pos t'' ht''pos
  obtain ⟨W, hW⟩ := hz.exists_minChain (ct := ct.out) (cs := cs.out) hcf hint hsc hsplit
  exact hz.caseB_core hcf hint hsc hL hR hCB hsplit ht0 hW
    fun α' K₀ hK₀ hKb hne hde _ vL₀ a₂ hjL hvV hvb ↦
      hz.caseB_end hcf hint hsc hL hR hCB hsplit α' K₀ hK₀ hKb hne hde vL₀ a₂ hjL hvV hvb

/-- **Fischbacher's Lemma 5.2.** -/
theorem lemma52 {a b : A} (v w : Quiver.Path (RayVert.mk a) (RayVert.mk b)) {d : A}
    (hd : d ∈ pathVerts v) : ChainFromTo d (pathVerts w) :=
  lemma52_of_step hcf hint hsc (fun _ _ hz h0 ↦ hz.step hcf hint hsc hL hR hCB h0) v w hd

end LargeIndecomposable.RayCat
