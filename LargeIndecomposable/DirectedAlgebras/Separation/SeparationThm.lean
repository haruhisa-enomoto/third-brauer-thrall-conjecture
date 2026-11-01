module

public import LargeIndecomposable.DirectedAlgebras.Separation.SepDescend

/-!
# The separation theorem

**Theorem** (Bongartz, *A criterion for finite representation type*, 2.5). A directed algebra
with vertex idempotents, at least one live point, and a separating decomposition of every radical
`rad P(z)` has a preprojective component (`exists_preprojComp`).

Proof: if every radical summand `Rⱼ(y)` is good, the good modules form a preprojective component
(`preprojComp_of_good_R`). Otherwise take `Rⱼ(y)` not good and `B = Bⱼ(y)`, which has fewer points
and inherits separating decompositions (`sepDecomp_descend`); by induction its quotient algebra
has a preprojective component `C`. If some member of `C` restricted `Rⱼ(y)`, then `Rⱼ(y)` would be
good (`good_res`); so none does, and `C` restricts to a preprojective component of `A`
(`preprojComp_transport`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k : Type u} [Field k]

namespace DirData

/-- **The separation theorem.** -/
theorem exists_preprojComp : ∀ (N : ℕ) {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
    (D : DirData k A) (sd : ∀ z, Decomp (D.RadP z)),
    (∀ z, z ∈ D.T → D.SepDecomp z (sd z)) → D.T.ncard ≤ N → D.T.Nonempty →
      ∃ 𝒞 : FDMod k A → Prop, PreprojComp 𝒞 := by
  intro N
  induction N with
  | zero =>
    intro A _ _ _ D sd hsd hN hne
    exfalso
    have := Set.ncard_pos (Set.toFinite D.T) |>.2 hne
    omega
  | succ N ih =>
    intro A _ _ _ D sd hsd hN hne
    classical
    by_cases hgood : ∀ y, y ∈ D.T → ∀ j, Good ((sd y).obj j)
    · exact ⟨_, preprojComp_of_good_R sd hne hgood⟩
    push Not at hgood
    obtain ⟨y, hy, j, hnot⟩ := hgood
    have hB := Bset_convex y (sd y) j
    let B := Bset y (sd y) j
    -- separating decompositions of the quotient
    have hPB : ∀ z, z ∈ B → LivesOn B (projE (k := k) (D.idem z)) := fun z hz ↦
      livesOn_proj y (sd y) j hz
    let gz : ∀ z, z ∈ B → (D.RadP z ⟶ resFD (D.qmap B) ((D.quot hB).RadP z)) := fun z hz ↦
      (isoM_res_radP hB z hz (hPB z hz)).choose
    have hgz : ∀ z (hz : z ∈ B), Function.Bijective (FDMod.lin (gz z hz)) := fun z hz ↦
      (isoM_res_radP hB z hz (hPB z hz)).choose_spec
    have hdz : ∀ z, z ∈ B → ∀ i, LivesOn B ((sd z).obj i) := fun z hz i ↦
      livesOn_of_inj _ (decomp_inc_inj (sd z) i)
        (livesOn_of_inj (D.radInc z) Subtype.val_injective (hPB z hz))
    let sd' : ∀ z, Decomp ((D.quot hB).RadP z) := fun z ↦
      if hz : z ∈ B then decompDescend (gz z hz) (hgz z hz) (sd z) (hdz z hz)
      else Classical.choice (FDMod.exists_decomp _)
    have hsd' : ∀ z, z ∈ (D.quot hB).T → (D.quot hB).SepDecomp z (sd' z) := by
      intro z hz
      have hz' : z ∈ B := hz
      simp only [sd', dif_pos hz']
      exact sepDecomp_descend hB hz' (hsd z (hB.1 hz')) (hdz z hz') (gz z hz') (hgz z hz')
    -- `B` is smaller and nonempty
    have hBT : B ⊂ D.T := by
      refine ⟨fun b hb ↦ hB.1 hb, fun h ↦ ?_⟩
      have hyB : y ∈ B := h hy
      exact (Bset_sub y (sd y) j hyB).2 Relation.ReflTransGen.refl
    have hBcard : B.ncard ≤ N := by
      have := Set.ncard_lt_ncard hBT (Set.toFinite D.T)
      omega
    have hBne : B.Nonempty := by
      haveI := (sd y).nt j
      obtain ⟨u, hu⟩ := supp_nonempty (D := D) ((sd y).obj j)
      exact ⟨u, (livesOn_iff_supp _ _).1 (livesOn_R y (sd y) j) hu⟩
    obtain ⟨𝒞, h𝒞⟩ := ih (D.quot hB) sd' hsd' hBcard hBne
    by_cases hin : ∃ V, 𝒞 V ∧ IsoM (resFD (D.qmap B) V) ((sd y).obj j)
    · exfalso
      obtain ⟨V, hV, hVR⟩ := hin
      have habove : ∀ m W, 0 < m → PredN V m W →
          ¬IsoM (resFD (D.qmap B) W) ((sd y).obj j) := fun m W hm hW hWR ↦
        h𝒞.noCycle V hV m W hm hW (IsoM.unres (D.qmap_surjective B) (hWR.trans hVR.symm))
      exact hnot ((good_res sd hsd j h𝒞 hV habove).of_iso hVR)
    · push Not at hin
      exact ⟨_, preprojComp_transport sd hsd j h𝒞 hin⟩

end DirData

end LargeIndecomposable.AR
