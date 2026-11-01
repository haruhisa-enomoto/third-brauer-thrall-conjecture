module

public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.DeepRayPath
public import LargeIndecomposable.RayCategories.Contours.ProperPathInterlacement
public import LargeIndecomposable.RayCategories.Basic.MorphismDepth
public import LargeIndecomposable.RayCategories.Basic.FromDistributive

/-!
# Proportional values of parallel paths

For a zero-detecting lift of the arrows of the ray category of a split basic
distributive algebra, if every non-interlaced pair of paths with the same
nonzero value is deep, then any two paths with the same nonzero value have
proportional values (`scalar_of_related_of_deep`). The induction is on the
depth of the common value: an interlacing step replaces an inner pair whose
value has strictly smaller depth (BGRS 2.9).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace LargeIndecomposable.RayCat

variable {P : Type*} [Category P] [Limits.HasZeroMorphisms P] [IsRayCategory P]

lemma depth_le_comp_left' {x y z : P} (f : x ⟶ y) (g : y ⟶ z) (h : f ≫ g ≠ 0) :
    depth g ≤ depth (f ≫ g) := by
  have hf0 : f ≠ 0 := fun h0 ↦ h (by rw [h0, Limits.zero_comp])
  have hg : g ≠ 0 := fun h0 ↦ h (by rw [h0, Limits.comp_zero])
  obtain ⟨q, hql, hq⟩ := exists_path_depth hg
  obtain ⟨p, hp⟩ := exists_path f hf0
  have := length_le_depth' (p.comp q) (f := f ≫ g) (by rw [pathVal_comp, hp, hq]) h
  rw [Quiver.Path.length_comp] at this
  omega

end LargeIndecomposable.RayCat

namespace LargeIndecomposable.SplitBasicIdempotents

universe u v x

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]
variable (S : LargeIndecomposable.SplitBasicIdempotents (k := k) (A := A) (ι := ι))
variable [LargeIndecomposable.HasBGRSPairDichotomy S.ProjectiveCategory]
variable [LargeIndecomposable.HasBGRSDistributiveHomStructure k S.ProjectiveCategory]
variable [LargeIndecomposable.IsFiniteRayCategory S.RayCategory] [Finite S.RayCategory]

/-- The relation "proportional nonzero values" for a lift. -/
abbrev scalarRel (L : LargeIndecomposable.BGRSRayArrowLift (C := S.ProjectiveCategory)) :=
  LargeIndecomposable.LinearPathCategory.nonzeroScalarMultiplePathRelation
    (k := k) (fun x : LargeIndecomposable.RayVertex S.RayCategory ↦ x.obj.as)
    (fun {i j} (a : i ⟶ j) ↦ L.representative a)

/-- **BGRS 2.9, generalized**: if each non-interlaced pair of paths with the same
nonzero value is deep or already has proportional values, then all such pairs have
proportional values. -/
theorem scalar_of_related_of_deep_or_scalar
    (L : LargeIndecomposable.BGRSRayArrowLift (C := S.ProjectiveCategory))
    (hzero : ∀ {i j : LargeIndecomposable.RayVertex S.RayCategory} (p : Quiver.Path i j),
      L.pathMap p = 0 ↔ LargeIndecomposable.rayPathMap p = 0)
    (hdeep : ∀ {i j : LargeIndecomposable.RayVertex S.RayCategory} {p q : Quiver.Path i j},
      (LargeIndecomposable.rayPathContourRelation (C := S.RayCategory)).related p q →
      ¬(LargeIndecomposable.properWhiskerInterlacementRelation
        (LargeIndecomposable.rayPathContourRelation (C := S.RayCategory))).interlaced p q →
      S.IsBGRSDeepRayPath p ∨ (scalarRel S L).related p q)
    {i j : LargeIndecomposable.RayVertex S.RayCategory} {p q : Quiver.Path i j}
    (hpq : (LargeIndecomposable.rayPathContourRelation (C := S.RayCategory)).related p q) :
    (scalarRel S L).related p q := by
  letI : LargeIndecomposable.IsRayCategory S.RayCategory :=
    LargeIndecomposable.isRayCategory_of_finiteRayCategory
  set R := LargeIndecomposable.rayPathContourRelation (C := S.RayCategory)
  suffices H : ∀ n : ℕ, ∀ {i j : LargeIndecomposable.RayVertex S.RayCategory}
      (p q : Quiver.Path i j), R.related p q →
      LargeIndecomposable.RayCat.depth (LargeIndecomposable.rayPathMap p) ≤ n →
      (scalarRel S L).related p q from H _ p q hpq le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i j p q hpq hn
  by_cases hint : (LargeIndecomposable.properWhiskerInterlacementRelation R).interlaced p q
  swap
  · rcases hdeep hpq hint with hd | hs
    · exact BGRSRayArrowLift.rayPathContourRelation_related_implies_scalar_of_deep S L hzero hpq hd
    · exact hs
  set μ := LargeIndecomposable.rayPathMap p
  have hμ : μ ≠ 0 := hpq.1
  have hnz : ∀ x : Quiver.Path i j, LargeIndecomposable.rayPathMap x = μ → L.pathMap x ≠ 0 :=
    fun x hx h0 ↦ hμ (hx ▸ (hzero x).1 h0)
  have key : ∀ x y : Quiver.Path i j,
      Relation.EqvGen (LargeIndecomposable.ProperWhiskerInterlacementStep R) x y →
      LargeIndecomposable.rayPathMap x = μ → (scalarRel S L).related x y := by
    intro x y hxy
    induction hxy with
    | rel x y hstep =>
        intro hx
        obtain ⟨a', b', s, v, w, t, hvw, houter, hproper, rfl, rfl⟩ := hstep
        have hcompv : LargeIndecomposable.rayPathMap ((s.comp v).comp t) =
            LargeIndecomposable.rayPathMap t ≫ LargeIndecomposable.rayPathMap v ≫
              LargeIndecomposable.rayPathMap s := by
          simp only [LargeIndecomposable.rayPathMap, LargeIndecomposable.LinearPathCategory.pathMap_comp]
        have hout0 : LargeIndecomposable.rayPathMap t ≫ LargeIndecomposable.rayPathMap v ≫
            LargeIndecomposable.rayPathMap s ≠ 0 := by
          rw [← hcompv, hx]; exact hμ
        have hlt : LargeIndecomposable.RayCat.depth (LargeIndecomposable.rayPathMap v) <
            LargeIndecomposable.RayCat.depth μ := by
          rw [← hx, hcompv]
          have hvs0 : LargeIndecomposable.rayPathMap v ≫ LargeIndecomposable.rayPathMap s ≠ 0 :=
            fun h0 ↦ hout0 (by rw [h0, Limits.comp_zero])
          rcases Nat.eq_zero_or_pos t.length with ht | ht
          · have hs : s.length ≠ 0 := by omega
            have h1 := LargeIndecomposable.RayCat.depth_lt_comp_right
              (LargeIndecomposable.rayPathMap v) (LargeIndecomposable.rayPathMap s) hvs0
              (LargeIndecomposable.rayPathMap_not_isIso_of_length_ne_zero s hs)
            have h2 := LargeIndecomposable.RayCat.depth_le_comp_left'
              (LargeIndecomposable.rayPathMap t) _ hout0
            omega
          · have h1 := LargeIndecomposable.RayCat.depth_lt_comp_left
              (LargeIndecomposable.rayPathMap t) _ hout0
              (LargeIndecomposable.rayPathMap_not_isIso_of_length_ne_zero t (by omega))
            have h2 := LargeIndecomposable.RayCat.depth_le_comp_right
              (LargeIndecomposable.rayPathMap v) _ hvs0
            omega
        obtain ⟨hv0, c, hc⟩ := ih _ (lt_of_lt_of_le hlt hn) v w hvw le_rfl
        refine ⟨hnz _ hx, c, ?_⟩
        have e1 : L.pathMap ((s.comp v).comp t) = L.pathMap t ≫ L.pathMap v ≫ L.pathMap s := by
          simp only [LargeIndecomposable.BGRSRayArrowLift.pathMap,
            LargeIndecomposable.LinearPathCategory.pathMap_comp, Category.assoc]
        have e2 : L.pathMap ((s.comp w).comp t) = L.pathMap t ≫ L.pathMap w ≫ L.pathMap s := by
          simp only [LargeIndecomposable.BGRSRayArrowLift.pathMap,
            LargeIndecomposable.LinearPathCategory.pathMap_comp, Category.assoc]
        change L.pathMap ((s.comp v).comp t) = (c : k) • L.pathMap ((s.comp w).comp t)
        have hc' : L.pathMap v = (c : k) • L.pathMap w := hc
        rw [e1, e2, hc', Linear.smul_comp, Linear.comp_smul]
    | refl x =>
        intro hx
        exact ⟨hnz x hx, 1, by rw [Units.val_one, one_smul]⟩
    | symm x y hxy ih' =>
        intro hy
        have hyy : R.related y y := ⟨by rw [hy]; exact hμ, rfl⟩
        have hyx := LargeIndecomposable.related_of_properWhiskerInterlaced R
          (Relation.EqvGen.symm _ _ hxy) hyy
        exact (scalarRel S L).symm (ih' (hyx.2.symm.trans hy))
    | trans x y z hxy hyz ih1 ih2 =>
        intro hx
        have hxx : R.related x x := ⟨by rw [hx]; exact hμ, rfl⟩
        have hxyR := LargeIndecomposable.related_of_properWhiskerInterlaced R hxy hxx
        exact (scalarRel S L).trans (ih1 hx) (ih2 (hxyR.2.symm.trans hx))
  exact key p q hint rfl


/-- **BGRS 2.9**: if non-interlaced pairs of paths with the same nonzero value
are deep, then all such pairs have proportional values. -/
theorem scalar_of_related_of_deep
    (L : LargeIndecomposable.BGRSRayArrowLift (C := S.ProjectiveCategory))
    (hzero : ∀ {i j : LargeIndecomposable.RayVertex S.RayCategory} (p : Quiver.Path i j),
      L.pathMap p = 0 ↔ LargeIndecomposable.rayPathMap p = 0)
    (hdeep : ∀ {i j : LargeIndecomposable.RayVertex S.RayCategory} {p q : Quiver.Path i j},
      (LargeIndecomposable.rayPathContourRelation (C := S.RayCategory)).related p q →
      ¬(LargeIndecomposable.properWhiskerInterlacementRelation
        (LargeIndecomposable.rayPathContourRelation (C := S.RayCategory))).interlaced p q →
      S.IsBGRSDeepRayPath p)
    {i j : LargeIndecomposable.RayVertex S.RayCategory} {p q : Quiver.Path i j}
    (hpq : (LargeIndecomposable.rayPathContourRelation (C := S.RayCategory)).related p q) :
    (scalarRel S L).related p q :=
  scalar_of_related_of_deep_or_scalar S L hzero (fun h h' ↦ Or.inl (hdeep h h')) hpq

end LargeIndecomposable.SplitBasicIdempotents
