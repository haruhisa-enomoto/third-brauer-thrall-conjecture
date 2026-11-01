module

public import LargeIndecomposable.MultiplicativeBases.Twisted.LoopEndomorphismKill

/-!
# Exact commutation of an exceptional contour by twisting

At the level of a split basic distributive algebra: a contour `χ μ ~ μ α`
(dumb-bell, with loops `χ`, `α`) or `ρ ρ ~ a β` (`Q₂'`) has lifted values that
agree up to units on both ends. Twisting the lifts of `χ` and `α` (dumb-bell), or of
`β` (or `a`) (`Q₂'`), makes the two values equal, and the new lift is still
zero-detecting when the twisted loops kill the other arrows (`ray conditions`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits LargeIndecomposable

namespace LargeIndecomposable.ExceptionalContourCommutation

open RadicalLoopKill

universe u v w

variable {k : Type u} [Field k] [IsAlgClosed k] {A : Type v} [Ring A] [Algebra k A]
  [Module.Finite k A] {ι : Type w} [Fintype ι] [DecidableEq ι]
  (S : SplitBasicIdempotents (k := k) (A := A) (ι := ι))
  [HasBGRSDistributiveHomStructure k S.ProjectiveCategory]

/-- Zero-detecting lifts. -/
def ZD (L : BGRSRayArrowLift (C := S.ProjectiveCategory)) : Prop :=
  ∀ {i j : RayVertex S.RayCategory} (p : Quiver.Path i j),
    L.pathMap p = 0 ↔ rayPathMap p = 0

/-- Every non-invertible endomorphism ray of `j` is a power of `ℓ`. -/
def LoopGen {j : RayVertex S.RayCategory} (ℓ : j ⟶ j) : Prop :=
  ∀ f : j.obj ⟶ j.obj, ¬IsIso f → ∃ n, 0 < n ∧ f = (End.of ℓ.1 ^ n).asHom

lemma pathMap_cons_comp_loop (L : BGRSRayArrowLift (C := S.ProjectiveCategory))
    {i j m : RayVertex S.RayCategory} (a : i ⟶ j) (ℓ : j ⟶ j) (e : j ⟶ m) (n : ℕ) :
    L.pathMap (((Quiver.Path.nil.cons a).comp (loopPath ℓ n)).cons e) =
      L.representative e ≫ (End.of (L.representative ℓ) ^ n).asHom ≫ L.representative a := by
  simp only [BGRSRayArrowLift.pathMap, LinearPathCategory.pathMap_cons,
    LinearPathCategory.pathMap_comp, pathMap_loopPath, LinearPathCategory.pathMap_nil,
    Category.comp_id]

/-- **Kill on the target side from the rays.** -/
lemma kill_tgt (L : BGRSRayArrowLift (C := S.ProjectiveCategory)) (hz : ZD S L)
    {i j : RayVertex S.RayCategory} (a : i ⟶ j) (ℓ : j ⟶ j) (hEC : LoopGen S ℓ)
    {m : RayVertex S.RayCategory} (e : j ⟶ m)
    (hr : ∀ n, rayPathMap (((Quiver.Path.nil.cons a).comp (loopPath ℓ n)).cons e) = 0)
    (u : j.obj.as ⟶ j.obj.as) : L.representative e ≫ u ≫ L.representative a = 0 :=
  comp_end_comp_eq_zero S L ℓ hEC _ _ (fun n ↦ by
    rw [← pathMap_cons_comp_loop]; exact (hz _).2 (hr n)) u

/-- **Kill on the source side from the rays.** -/
lemma kill_src (L : BGRSRayArrowLift (C := S.ProjectiveCategory)) (hz : ZD S L)
    {i j : RayVertex S.RayCategory} (a : i ⟶ j) (ℓ : i ⟶ i) (hEC : LoopGen S ℓ)
    {m : RayVertex S.RayCategory} (e : m ⟶ i)
    (hr : ∀ n, rayPathMap (((Quiver.Path.nil.cons e).comp (loopPath ℓ n)).cons a) = 0)
    (u : i.obj.as ⟶ i.obj.as) : L.representative a ≫ u ≫ L.representative e = 0 :=
  comp_end_comp_eq_zero S L ℓ hEC _ _ (fun n ↦ by
    rw [← pathMap_cons_comp_loop]; exact (hz _).2 (hr n)) u

/-- Two parallel paths with the same nonzero ray have lifted values in the same
unit orbit. -/
lemma unitRay_eq_of_related (L : BGRSRayArrowLift (C := S.ProjectiveCategory))
    {i j : RayVertex S.RayCategory} {p q : Quiver.Path i j}
    (hpq : (rayPathContourRelation (C := S.RayCategory)).related p q) :
    unitRay (L.pathMap p) = unitRay (L.pathMap q) := by
  rw [L.unitRay_pathMap_eq_rayPathMap_of_ne_zero p hpq.1,
    L.unitRay_pathMap_eq_rayPathMap_of_ne_zero q (hpq.2 ▸ hpq.1), hpq.2]

open BGRSRayArrowLift TwistLift in
/-- **Dumb-bell twist**: `χ μ ~ μ α` becomes an exact equality. -/
theorem db_twist (L₀ : BGRSRayArrowLift (C := S.ProjectiveCategory)) (hz₀ : ZD S L₀)
    {X Y : RayVertex S.RayCategory} (hXY : X ≠ Y) (χ : X ⟶ X) (μ : Y ⟶ X) (α : Y ⟶ Y)
    (hrel : (rayPathContourRelation (C := S.RayCategory)).related
      ((Quiver.Path.nil.cons μ).cons χ) ((Quiver.Path.nil.cons α).cons μ))
    (hECx : LoopGen S χ) (hECy : LoopGen S α)
    (hLx : ∀ {m : RayVertex S.RayCategory} (e : X ⟶ m), ¬(∃ _ : m = X, HEq e χ) →
      ∀ n, rayPathMap (((Quiver.Path.nil.cons χ).comp (loopPath χ n)).cons e) = 0)
    (hRy : ∀ {m : RayVertex S.RayCategory} (e : m ⟶ Y), ¬(∃ _ : m = Y, HEq e α) →
      ∀ n, rayPathMap (((Quiver.Path.nil.cons e).comp (loopPath α n)).cons α) = 0) :
    ∃ L : BGRSRayArrowLift (C := S.ProjectiveCategory), ZD S L ∧
      L.pathMap ((Quiver.Path.nil.cons μ).cons χ) = L.pathMap ((Quiver.Path.nil.cons α).cons μ) := by
  obtain ⟨s, t, hst⟩ := (unitRay_eq_iff _ _).1 (unitRay_eq_of_related S L₀ hrel)
  simp only [BGRSRayArrowLift.pathMap, LinearPathCategory.pathMap_cons,
    LinearPathCategory.pathMap_nil, Category.comp_id] at hst
  -- twist `χ` on its target side by `s`
  set L₁ := L₀.twistTgt χ (unitAt X s.hom) (unitAt_isIso X s.hom) with hL₁
  have hz₁ : ZD S L₁ := fun p ↦ by
    rw [hL₁, twistTgt_zero L₀ χ χ s.hom (projEnd_comp_comm S (End.of s.hom) (End.of _))
      (fun e he u ↦ kill_tgt S L₀ hz₀ χ χ hECx e (hLx e he) u) p]
    exact hz₀ p
  -- twist `α` on its source side by `t⁻¹`
  set L₂ := L₁.twistSrc α (unitAt Y (inv t.hom)) (unitAt_isIso Y (inv t.hom)) with hL₂
  have hz₂ : ZD S L₂ := fun p ↦ by
    rw [hL₂, twistSrc_zero L₁ α α (inv t.hom) (projEnd_comp_comm S (End.of (inv t.hom)) (End.of _))
      (fun e he u ↦ kill_src S L₁ hz₁ α α hECy e (hRy e he) u) p]
    exact hz₁ p
  have nχα : ¬IsA χ α := fun ⟨h, _, _⟩ ↦ hXY h.symm
  have nαχ : ¬IsA α χ := fun ⟨h, _, _⟩ ↦ hXY h
  have nχμ : ¬IsA χ μ := fun ⟨h, _, _⟩ ↦ hXY h.symm
  have nαμ : ¬IsA α μ := fun ⟨_, h, _⟩ ↦ hXY h
  have r1 : L₂.representative χ = s.hom ≫ L₀.representative χ := by
    rw [hL₂, twistSrc_rep_of_not _ α _ _ χ nαχ, hL₁, twistTgt_rep_a]
  have r2 : L₂.representative μ = L₀.representative μ := by
    rw [hL₂, twistSrc_rep_of_not _ α _ _ μ nαμ, hL₁, twistTgt_rep_of_not _ χ _ _ μ nχμ]
  have r3 : L₂.representative α = L₀.representative α ≫ inv t.hom := by
    rw [hL₂, twistSrc_rep_a, hL₁, twistTgt_rep_of_not _ χ _ _ α nχα]
  refine ⟨L₂, hz₂, ?_⟩
  simp only [BGRSRayArrowLift.pathMap, LinearPathCategory.pathMap_cons,
    LinearPathCategory.pathMap_nil, Category.comp_id]
  change L₂.representative χ ≫ L₂.representative μ = L₂.representative μ ≫ L₂.representative α
  rw [r1, r2, r3, ← Category.assoc, hst]
  simp

open BGRSRayArrowLift TwistLift in
/-- **`Q₂'` twist at `β`**: `ρ ρ ~ a β` becomes an exact equality. -/
theorem q2_twist_src (L₀ : BGRSRayArrowLift (C := S.ProjectiveCategory)) (hz₀ : ZD S L₀)
    {X T : RayVertex S.RayCategory} (hXT : X ≠ T) (ρ : X ⟶ X) (a : T ⟶ X) (β : X ⟶ T)
    (hrel : (rayPathContourRelation (C := S.RayCategory)).related
      ((Quiver.Path.nil.cons ρ).cons ρ) ((Quiver.Path.nil.cons β).cons a))
    (hEC : LoopGen S ρ)
    (hRb : ∀ {m : RayVertex S.RayCategory} (e : m ⟶ X), ¬(∃ _ : m = X, HEq e ρ) →
      ∀ n, rayPathMap (((Quiver.Path.nil.cons e).comp (loopPath ρ n)).cons β) = 0) :
    ∃ L : BGRSRayArrowLift (C := S.ProjectiveCategory), ZD S L ∧
      L.pathMap ((Quiver.Path.nil.cons ρ).cons ρ) = L.pathMap ((Quiver.Path.nil.cons β).cons a) ∧
      ∀ {i j : RayVertex S.RayCategory} (e : i ⟶ j), ¬IsA β e →
        L.representative e = L₀.representative e := by
  obtain ⟨s, t, hst⟩ := (unitRay_eq_iff _ _).1 (unitRay_eq_of_related S L₀ hrel)
  simp only [BGRSRayArrowLift.pathMap, LinearPathCategory.pathMap_cons,
    LinearPathCategory.pathMap_nil, Category.comp_id] at hst
  set w := inv (s.hom ≫ t.hom)
  set L₁ := L₀.twistSrc β (unitAt X w) (unitAt_isIso X w) with hL₁
  have hz₁ : ZD S L₁ := fun p ↦ by
    rw [hL₁, twistSrc_zero L₀ β ρ w (projEnd_comp_comm S (End.of w) (End.of _))
      (fun e he u ↦ kill_src S L₀ hz₀ β ρ hEC e (hRb e he) u) p]
    exact hz₀ p
  have nβρ : ¬IsA β ρ := fun ⟨_, h, _⟩ ↦ hXT h
  have nβa : ¬IsA β a := fun ⟨h, _, _⟩ ↦ hXT h.symm
  have r1 : L₁.representative ρ = L₀.representative ρ := by
    rw [hL₁, twistSrc_rep_of_not _ β _ _ ρ nβρ]
  have r2 : L₁.representative a = L₀.representative a := by
    rw [hL₁, twistSrc_rep_of_not _ β _ _ a nβa]
  have r3 : L₁.representative β = L₀.representative β ≫ w := by
    rw [hL₁, twistSrc_rep_a]
  refine ⟨L₁, hz₁, ?_, fun e he ↦ by rw [hL₁, twistSrc_rep_of_not _ β _ _ e he]⟩
  simp only [BGRSRayArrowLift.pathMap, LinearPathCategory.pathMap_cons,
    LinearPathCategory.pathMap_nil, Category.comp_id]
  change L₁.representative ρ ≫ L₁.representative ρ = L₁.representative a ≫ L₁.representative β
  rw [r1, r2, r3, ← Category.assoc, hst]
  have hc : s.hom ≫ (L₀.representative ρ ≫ L₀.representative ρ) =
      (L₀.representative ρ ≫ L₀.representative ρ) ≫ s.hom :=
    projEnd_comp_comm S (End.of s.hom) (End.of _)
  rw [← Category.assoc, hc]
  simp [w]

open BGRSRayArrowLift TwistLift in
/-- **`Q₂'` twist at `a`** (the dual case). -/
theorem q2_twist_tgt (L₀ : BGRSRayArrowLift (C := S.ProjectiveCategory)) (hz₀ : ZD S L₀)
    {X T : RayVertex S.RayCategory} (hXT : X ≠ T) (ρ : X ⟶ X) (a : T ⟶ X) (β : X ⟶ T)
    (hrel : (rayPathContourRelation (C := S.RayCategory)).related
      ((Quiver.Path.nil.cons ρ).cons ρ) ((Quiver.Path.nil.cons β).cons a))
    (hEC : LoopGen S ρ)
    (hLa : ∀ {m : RayVertex S.RayCategory} (e : X ⟶ m), ¬(∃ _ : m = X, HEq e ρ) →
      ∀ n, rayPathMap (((Quiver.Path.nil.cons a).comp (loopPath ρ n)).cons e) = 0) :
    ∃ L : BGRSRayArrowLift (C := S.ProjectiveCategory), ZD S L ∧
      L.pathMap ((Quiver.Path.nil.cons ρ).cons ρ) = L.pathMap ((Quiver.Path.nil.cons β).cons a) ∧
      ∀ {i j : RayVertex S.RayCategory} (e : i ⟶ j), ¬IsA a e →
        L.representative e = L₀.representative e := by
  obtain ⟨s, t, hst⟩ := (unitRay_eq_iff _ _).1 (unitRay_eq_of_related S L₀ hrel)
  simp only [BGRSRayArrowLift.pathMap, LinearPathCategory.pathMap_cons,
    LinearPathCategory.pathMap_nil, Category.comp_id] at hst
  set w := inv (s.hom ≫ t.hom)
  set L₁ := L₀.twistTgt a (unitAt X w) (unitAt_isIso X w) with hL₁
  have hz₁ : ZD S L₁ := fun p ↦ by
    rw [hL₁, twistTgt_zero L₀ a ρ w (projEnd_comp_comm S (End.of w) (End.of _))
      (fun e he u ↦ kill_tgt S L₀ hz₀ a ρ hEC e (hLa e he) u) p]
    exact hz₀ p
  have naρ : ¬IsA a ρ := fun ⟨h, _, _⟩ ↦ hXT h
  have naβ : ¬IsA a β := fun ⟨h, _, _⟩ ↦ hXT h
  have r1 : L₁.representative ρ = L₀.representative ρ := by
    rw [hL₁, twistTgt_rep_of_not _ a _ _ ρ naρ]
  have r2 : L₁.representative β = L₀.representative β := by
    rw [hL₁, twistTgt_rep_of_not _ a _ _ β naβ]
  have r3 : L₁.representative a = w ≫ L₀.representative a := by
    rw [hL₁, twistTgt_rep_a]
  refine ⟨L₁, hz₁, ?_, fun e he ↦ by rw [hL₁, twistTgt_rep_of_not _ a _ _ e he]⟩
  simp only [BGRSRayArrowLift.pathMap, LinearPathCategory.pathMap_cons,
    LinearPathCategory.pathMap_nil, Category.comp_id]
  change L₁.representative ρ ≫ L₁.representative ρ = L₁.representative a ≫ L₁.representative β
  rw [r1, r2, r3, Category.assoc, hst]
  have ht : (L₀.representative ρ ≫ L₀.representative ρ) ≫ t.hom =
      t.hom ≫ (L₀.representative ρ ≫ L₀.representative ρ) :=
    projEnd_comp_comm S (End.of _) (End.of t.hom)
  simp only [Category.assoc] at ht ⊢
  rw [ht]
  simp [w]

end LargeIndecomposable.ExceptionalContourCommutation
