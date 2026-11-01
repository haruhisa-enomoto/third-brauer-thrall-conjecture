module

public import LargeIndecomposable.RayCategories.Distributive.ProperQuotientCorners
public import LargeIndecomposable.Cleaving.ClosedChains.Figure13EPrintedSeparation
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.RoiterFigure13EAmbient

@[expose] public section

/-!
# Positive Figure 13E supplement reduction

This file proves the first source-facing part of the positive Figure 13E
argument.  The quotient by the two square relations cannot create the transit
direction prohibited by either outer arrow: a hypothetical transfer of the
image of `tau` lifts with an error in the corresponding relation-ideal
corner, and that error is absorbed into a unit multiple of `tau`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.RoiterFigure13EAmbient

open LargeIndecomposable.ClosedZigzagTransfer
open LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory

universe u v x

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

variable [LargeIndecomposable.HasBGRSDistributiveHomStructure
  k S.ProjectiveCategory]

/-- The Figure-13 quotient preserves the prohibited cotransit direction of
the left outer arrow. -/
theorem quotientFunctor_map_not_allowsCotransit
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (hfspan : twoSidedEndomorphismSpan k f = ⊤)
    (hfNotC : ¬ LargeIndecomposable.AllowsCotransit f) :
    ¬ LargeIndecomposable.AllowsCotransit
      ((figure13QuotientFunctor S f g P).map f) := by
  letI : ∀ T : S.ProjectiveCategory, Module.Finite k (End T) := fun T ↦ by
    change Module.Finite k (T ⟶ T)
    infer_instance
  let F := figure13QuotientFunctor S f g P
  intro hbarC
  let tauBar : End (F.obj Y) := End.of (F.map P.tau.asHom)
  obtain ⟨abar, hbarTransfer⟩ := hbarC tauBar
  let a : End X := End.of (F.preimage abar.asHom)
  have hmapa : F.map a.asHom = abar.asHom := by
    simpa only [a] using F.map_preimage abar.asHom
  have hmapzero : F.map
      (f ≫ P.tau.asHom - a.asHom ≫ f) = 0 := by
    rw [F.map_sub, F.map_comp, F.map_comp, hmapa]
    change F.map f ≫ tauBar.asHom - abar.asHom ≫ F.map f = 0
    exact sub_eq_zero.mpr hbarTransfer
  have hmem : (f ≫ P.tau.asHom - a.asHom ≫ f).1 ∈
      (LargeIndecomposable.RoiterFigure13Quotient.relationIdeal
        S f g P).asIdeal :=
    (S.projectiveQuotientFunctor_map_eq_zero_iff
      (LargeIndecomposable.RoiterFigure13Quotient.relationIdeal S f g P)
      (LargeIndecomposable.RoiterFigure13Quotient.relationIdeal_le_jacobson
        S f g P)
      (f ≫ P.tau.asHom - a.asHom ≫ f)).1 hmapzero
  have hcorner : f ≫ P.tau.asHom - a.asHom ≫ f ∈
      finiteIdealCorner S
        (LargeIndecomposable.RoiterFigure13Quotient.relationIdeal S f g P)
        X Y := hmem
  have hspan :=
    LargeIndecomposable.RoiterFigure13Quotient.relationIdeal_corner_left_le
      S f g P hfspan hcorner
  have hfT : LargeIndecomposable.AllowsTransit f :=
    (LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := S.ProjectiveCategory) f).resolve_right hfNotC
  have hftauSqT : LargeIndecomposable.AllowsTransit
      (f ≫ (P.tau ^ 2).asHom) := by
    intro c
    obtain ⟨d, hcd⟩ := hfT c
    refine ⟨d, ?_⟩
    have hcomm := congrArg End.asHom (P.mul_comm d (P.tau ^ 2))
    calc
      c.asHom ≫ (f ≫ (P.tau ^ 2).asHom) =
          (c.asHom ≫ f) ≫ (P.tau ^ 2).asHom := by
            simp only [Category.assoc]
      _ = (f ≫ d.asHom) ≫ (P.tau ^ 2).asHom := by rw [hcd]
      _ = f ≫ ((P.tau ^ 2).asHom ≫ d.asHom) := by
            simpa only [End.mul_def, Category.assoc] using
              congrArg (fun z : Y ⟶ Y ↦ f ≫ z) hcomm.symm
      _ = (f ≫ (P.tau ^ 2).asHom) ≫ d.asHom := by
            simp only [Category.assoc]
  obtain ⟨b, hb⟩ :=
    exists_comp_right_of_mem_twoSidedSpan_of_allowsTransit
      (k := k) hftauSqT hspan
  let e : End Y := 1 - b * P.tau
  have hbtauJ : b * P.tau ∈ Ring.jacobson (End Y) :=
    (Ring.jacobson (End Y)).mul_mem_left b P.mem_jacobson
  have he : IsUnit e := isUnit_one_sub_of_mem_jacobson hbtauJ
  have htransfer : a.asHom ≫ f =
      f ≫ (P.tau * e).asHom := by
    calc
      a.asHom ≫ f = f ≫ P.tau.asHom -
          (f ≫ P.tau.asHom - a.asHom ≫ f) := by module
      _ = f ≫ P.tau.asHom -
          (f ≫ (P.tau ^ 2).asHom) ≫ b.asHom := by rw [hb]
      _ = f ≫ (P.tau * e).asHom := by
        have hcoef : P.tau * e = P.tau - b * P.tau ^ 2 := by
          calc
            P.tau * e = e * P.tau := P.mul_comm P.tau e
            _ = (1 - b * P.tau) * P.tau := by rfl
            _ = 1 * P.tau - (b * P.tau) * P.tau := by rw [sub_mul]
            _ = P.tau - b * (P.tau * P.tau) := by
              rw [one_mul, mul_assoc]
            _ = P.tau - b * P.tau ^ 2 := by rw [pow_two]
        rw [hcoef]
        change f ≫ P.tau.asHom -
            (f ≫ (P.tau ^ 2).asHom) ≫ b.asHom =
          f ≫ (P.tau.asHom - (b * P.tau ^ 2).asHom)
        rw [Preadditive.comp_sub, End.mul_def]
        simp only [Category.assoc]
  apply hfNotC
  exact allowsCotransit_of_transfer_of_adjoin_eq_top
    f a (P.tau * e) (P.adjoin_mul_unit_eq_top e he) htransfer

/-- Source-dually, the Figure-13 quotient preserves the prohibited transit
direction of the right outer arrow. -/
theorem quotientFunctor_map_not_allowsTransit
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (hgspan : twoSidedEndomorphismSpan k g = ⊤)
    (hgNotT : ¬ LargeIndecomposable.AllowsTransit g) :
    ¬ LargeIndecomposable.AllowsTransit
      ((figure13QuotientFunctor S f g P).map g) := by
  letI : ∀ T : S.ProjectiveCategory, Module.Finite k (End T) := fun T ↦ by
    change Module.Finite k (T ⟶ T)
    infer_instance
  let F := figure13QuotientFunctor S f g P
  intro hbarT
  let tauBar : End (F.obj Y) := End.of (F.map P.tau.asHom)
  obtain ⟨bbar, hbarTransfer⟩ := hbarT tauBar
  let b : End Z := End.of (F.preimage bbar.asHom)
  have hmapb : F.map b.asHom = bbar.asHom := by
    simpa only [b] using F.map_preimage bbar.asHom
  have hmapzero : F.map
      (P.tau.asHom ≫ g - g ≫ b.asHom) = 0 := by
    rw [F.map_sub, F.map_comp, F.map_comp, hmapb]
    change tauBar.asHom ≫ F.map g - F.map g ≫ bbar.asHom = 0
    exact sub_eq_zero.mpr hbarTransfer
  have hmem : (P.tau.asHom ≫ g - g ≫ b.asHom).1 ∈
      (LargeIndecomposable.RoiterFigure13Quotient.relationIdeal
        S f g P).asIdeal :=
    (S.projectiveQuotientFunctor_map_eq_zero_iff
      (LargeIndecomposable.RoiterFigure13Quotient.relationIdeal S f g P)
      (LargeIndecomposable.RoiterFigure13Quotient.relationIdeal_le_jacobson
        S f g P)
      (P.tau.asHom ≫ g - g ≫ b.asHom)).1 hmapzero
  have hcorner : P.tau.asHom ≫ g - g ≫ b.asHom ∈
      finiteIdealCorner S
        (LargeIndecomposable.RoiterFigure13Quotient.relationIdeal S f g P)
        Y Z := hmem
  have hspan :=
    LargeIndecomposable.RoiterFigure13Quotient.relationIdeal_corner_right_le
      S f g P hgspan hcorner
  have hgC : LargeIndecomposable.AllowsCotransit g :=
    (LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := S.ProjectiveCategory) g).resolve_left hgNotT
  have htauSqgC : LargeIndecomposable.AllowsCotransit
      ((P.tau ^ 2).asHom ≫ g) := by
    intro d
    obtain ⟨c, hdc⟩ := hgC d
    refine ⟨c, ?_⟩
    have hcomm := congrArg End.asHom (P.mul_comm c (P.tau ^ 2))
    calc
      ((P.tau ^ 2).asHom ≫ g) ≫ d.asHom =
          (P.tau ^ 2).asHom ≫ (g ≫ d.asHom) := by
            simp only [Category.assoc]
      _ = (P.tau ^ 2).asHom ≫ (c.asHom ≫ g) := by rw [hdc]
      _ = c.asHom ≫ ((P.tau ^ 2).asHom ≫ g) := by
            simpa only [End.mul_def, Category.assoc] using
              congrArg (fun z : Y ⟶ Y ↦ z ≫ g) hcomm
  obtain ⟨a, ha⟩ :=
    exists_comp_left_of_mem_twoSidedSpan_of_allowsCotransit
      (k := k) htauSqgC hspan
  let e : End Y := 1 - P.tau * a
  have htauaJ : P.tau * a ∈ Ring.jacobson (End Y) :=
    (Ring.jacobson (End Y)).mul_mem_right a P.mem_jacobson
  have he : IsUnit e := isUnit_one_sub_of_mem_jacobson htauaJ
  have htransfer : (P.tau * e).asHom ≫ g =
      g ≫ b.asHom := by
    calc
      (P.tau * e).asHom ≫ g =
          P.tau.asHom ≫ g -
            a.asHom ≫ ((P.tau ^ 2).asHom ≫ g) := by
        rw [End.mul_def]
        dsimp only [e]
        change (((𝟙 Y) - (a.asHom ≫ P.tau.asHom)) ≫
            P.tau.asHom) ≫ g = _
        rw [Preadditive.sub_comp, Category.id_comp, Preadditive.sub_comp,
          pow_two, End.mul_def]
        simp only [Category.assoc]
      _ = P.tau.asHom ≫ g -
          (P.tau.asHom ≫ g - g ≫ b.asHom) := by rw [ha]
      _ = g ≫ b.asHom := by module
  apply hgNotT
  exact allowsTransit_of_transfer_of_adjoin_eq_top
    g (P.tau * e) b (P.adjoin_mul_unit_eq_top e he) htransfer

private theorem unitRayEquivalent_map
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} {f g : X ⟶ Y}
    (hfg : LargeIndecomposable.UnitRayEquivalent f g) :
    LargeIndecomposable.UnitRayEquivalent (F.map f) (F.map g) := by
  rcases hfg with ⟨a, b, rfl⟩
  refine ⟨F.mapIso a, F.mapIso b, ?_⟩
  simp only [Functor.map_comp]
  rfl

omit [IsAlgClosed k] in
private theorem exists_dominating_factorization_of_mem_throughObjectSubmodule
    {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [LargeIndecomposable.HasBGRSDistributiveHomStructure k C]
    {X Y : C} {q : Y ⟶ Y}
    (hq : q ∈ LargeIndecomposable.RoiterFigure13E.throughObjectSubmodule
      (k := k) X Y) (hq0 : q ≠ 0) :
    ∃ (l : Y ⟶ X) (r : X ⟶ Y),
      q ∈ twoSidedEndomorphismSpan k (l ≫ r) := by
  revert hq0
  induction hq using Submodule.span_induction with
  | mem q hq =>
      intro _
      rcases hq with ⟨l, r, rfl⟩
      exact ⟨l, r, mem_twoSidedEndomorphismSpan k (l ≫ r)⟩
  | zero =>
      intro hzero
      exact (hzero rfl).elim
  | add p q _ _ hp hq =>
      intro hpq0
      by_cases hp0 : p = 0
      · subst p
        obtain ⟨l, r, hmem⟩ := hq (by simpa using hpq0)
        exact ⟨l, r, by simpa using hmem⟩
      by_cases hq0 : q = 0
      · subst q
        obtain ⟨l, r, hmem⟩ := hp (by simpa using hpq0)
        exact ⟨l, r, by simpa using hmem⟩
      obtain ⟨lp, rp, hpSpan⟩ := hp hp0
      obtain ⟨lq, rq, hqSpan⟩ := hq hq0
      have hcomp :=
        LargeIndecomposable.HasBGRSDistributiveHomStructure.homSubbimodule_comparable
          (k := k) (C := C)
          (twoSidedEndomorphismSpan k (lp ≫ rp))
          (twoSidedEndomorphismSpan k (lq ≫ rq))
          (LargeIndecomposable.isHomSubbimodule_twoSidedEndomorphismSpan
            (lp ≫ rp))
          (LargeIndecomposable.isHomSubbimodule_twoSidedEndomorphismSpan
            (lq ≫ rq))
      rcases hcomp with hpq | hqp
      · exact ⟨lq, rq,
          (twoSidedEndomorphismSpan k (lq ≫ rq)).add_mem
            (hpq hpSpan) hqSpan⟩
      · exact ⟨lp, rp,
          (twoSidedEndomorphismSpan k (lp ≫ rp)).add_mem
            hpSpan (hqp hqSpan)⟩
  | smul c q _ hq =>
      intro hcq0
      have hq0 : q ≠ 0 := by
        intro hzero
        subst q
        simp at hcq0
      obtain ⟨l, r, hqSpan⟩ := hq hq0
      exact ⟨l, r,
        (twoSidedEndomorphismSpan k (l ≫ r)).smul_mem c hqSpan⟩

omit [IsAlgClosed k] in
private theorem exists_preimage_mem_twoSidedEndomorphismSpan_of_full
    {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear k C] [Linear k D]
    (F : C ⥤ D) [F.Additive] [F.Linear k] [F.Full]
    {X Y : C} {q : F.obj X ⟶ F.obj Y} {generator : X ⟶ Y}
    (hq : q ∈ twoSidedEndomorphismSpan k (F.map generator)) :
    ∃ q₀ : X ⟶ Y,
      q₀ ∈ twoSidedEndomorphismSpan k generator ∧ F.map q₀ = q := by
  induction hq using Submodule.span_induction with
  | mem q hq =>
      rcases hq with ⟨a, b, rfl⟩
      obtain ⟨a₀, ha₀⟩ := F.map_surjective a.asHom
      obtain ⟨b₀, hb₀⟩ := F.map_surjective b.asHom
      refine ⟨(a₀ ≫ generator) ≫ b₀, ?_, ?_⟩
      · apply Submodule.subset_span
        exact ⟨End.of a₀, End.of b₀, rfl⟩
      · simp only [Functor.map_comp, ha₀, hb₀]
  | zero =>
      exact ⟨0, by simp, by simp⟩
  | add p q _ _ hp hq =>
      obtain ⟨p₀, hp₀, hpMap⟩ := hp
      obtain ⟨q₀, hq₀, hqMap⟩ := hq
      refine ⟨p₀ + q₀,
        (twoSidedEndomorphismSpan k generator).add_mem hp₀ hq₀, ?_⟩
      rw [F.map_add, hpMap, hqMap]
  | smul c q _ hq =>
      obtain ⟨q₀, hq₀, hqMap⟩ := hq
      refine ⟨c • q₀,
        (twoSidedEndomorphismSpan k generator).smul_mem c hq₀, ?_⟩
      rw [F.map_smul, hqMap]

private theorem mem_tau_square_span_of_mem_jacobson_sq
    {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {Y : C} [Module.Finite k (End Y)] [IsLocalRing (End Y)]
    [IsArtinianRing (End Y)]
    (P : OrientedRadicalPowerParameter (k := k) Y) {a : End Y}
    (haSq : a ∈ (Ring.jacobson (End Y)) ^ 2) :
    a.asHom ∈ twoSidedEndomorphismSpan k (P.tau ^ 2).asHom := by
  by_cases ha0 : a = 0
  · subst a
    exact (twoSidedEndomorphismSpan k (P.tau ^ 2).asHom).zero_mem
  have haJ : a ∈ Ring.jacobson (End Y) :=
    Ideal.pow_le_self (by omega) haSq
  obtain ⟨n, hn, e, he, hae⟩ := P.transitData.factors a haJ ha0
  have hn2 : 2 ≤ n :=
    P.two_le_transitExponent_of_mem_sq haSq ha0 n hn e he hae
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn2
  apply Submodule.subset_span
  refine ⟨P.tau ^ m, e, ?_⟩
  simpa only [End.mul_def, pow_add, Category.assoc] using hae

private theorem postcompose_tau_square_ne_zero_of_unitRayEquivalent
    {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {X Y : C} [Module.Finite k (End Y)] [IsLocalRing (End Y)]
    [IsArtinianRing (End Y)]
    (P : OrientedRadicalPowerParameter (k := k) Y)
    {f alpha : X ⟶ Y} (hfa : LargeIndecomposable.UnitRayEquivalent f alpha)
    (hleft : f ≫ (P.tau ^ 2).asHom ≠ 0) :
    alpha ≫ (P.tau ^ 2).asHom ≠ 0 := by
  rcases hfa with ⟨a, b, hab⟩
  intro hzero
  have hcomm : b.hom ≫ (P.tau ^ 2).asHom =
      (P.tau ^ 2).asHom ≫ b.hom := by
    simpa only [End.mul_def] using congrArg End.asHom
      (P.mul_comm (End.of b.hom) (P.tau ^ 2)).symm
  have hzero' : a.hom ≫
      ((f ≫ (P.tau ^ 2).asHom) ≫ b.hom) = 0 := by
    calc
      a.hom ≫ ((f ≫ (P.tau ^ 2).asHom) ≫ b.hom) =
          (a.hom ≫ f ≫ b.hom) ≫ (P.tau ^ 2).asHom := by
            simp only [Category.assoc]
            rw [hcomm]
      _ = 0 := by rw [← hab]; exact hzero
  apply hleft
  have hcancelLeft : (f ≫ (P.tau ^ 2).asHom) ≫ b.hom = 0 := by
    calc
      (f ≫ (P.tau ^ 2).asHom) ≫ b.hom =
          a.inv ≫ (a.hom ≫ ((f ≫ (P.tau ^ 2).asHom) ≫ b.hom)) := by
            rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      _ = 0 := by rw [hzero']; exact Limits.comp_zero
  calc
    f ≫ (P.tau ^ 2).asHom =
        ((f ≫ (P.tau ^ 2).asHom) ≫ b.hom) ≫ b.inv := by
          rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = 0 := by rw [hcancelLeft]; exact Limits.zero_comp

private theorem precompose_tau_square_ne_zero_of_unitRayEquivalent
    {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {Y Z : C} [Module.Finite k (End Y)] [IsLocalRing (End Y)]
    [IsArtinianRing (End Y)]
    (P : OrientedRadicalPowerParameter (k := k) Y)
    {g beta : Y ⟶ Z} (hgb : LargeIndecomposable.UnitRayEquivalent g beta)
    (hright : (P.tau ^ 2).asHom ≫ g ≠ 0) :
    (P.tau ^ 2).asHom ≫ beta ≠ 0 := by
  rcases hgb with ⟨a, b, hab⟩
  intro hzero
  have hcomm : (P.tau ^ 2).asHom ≫ a.hom =
      a.hom ≫ (P.tau ^ 2).asHom := by
    simpa only [End.mul_def] using congrArg End.asHom
      (P.mul_comm (End.of a.hom) (P.tau ^ 2))
  rw [hab] at hzero
  have hzero' :
      (a.hom ≫ ((P.tau ^ 2).asHom ≫ g)) ≫ b.hom = 0 := by
    calc
      (a.hom ≫ ((P.tau ^ 2).asHom ≫ g)) ≫ b.hom =
          (((P.tau ^ 2).asHom ≫ a.hom) ≫ g) ≫ b.hom := by
            rw [hcomm]
            simp only [Category.assoc]
      _ = 0 := by simpa only [Category.assoc] using hzero
  have hcancelRight : a.hom ≫
      ((P.tau ^ 2).asHom ≫ g) = 0 := by
    calc
      a.hom ≫ ((P.tau ^ 2).asHom ≫ g) =
          (a.hom ≫ ((P.tau ^ 2).asHom ≫ g)) ≫ b.hom ≫ b.inv := by
            rw [Category.assoc, Category.assoc, Iso.hom_inv_id,
              Category.comp_id]
      _ = 0 := by
        simpa only [Category.assoc, Limits.zero_comp] using
          congrArg (fun z ↦ z ≫ b.inv) hzero'
  apply hright
  calc
    (P.tau ^ 2).asHom ≫ g =
        a.inv ≫ (a.hom ≫ ((P.tau ^ 2).asHom ≫ g)) := by
          rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = 0 := by rw [hcancelRight]; exact Limits.comp_zero

private theorem ambient_middle_square_span_le_of_quotient_mem_span
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (hXY : X ≠ Y) (hYZ : Y ≠ Z)
    (hleft : f ≫ (P.tau ^ 2).asHom ≠ 0)
    {cycle : Y ⟶ Y}
    (hmem :
      let F := figure13QuotientFunctor S f g P
      let Pbar :=
        LargeIndecomposable.RoiterFigure13Quotient.quotientMiddlePowerParameter
          S f g P hXY hYZ hleft
      (Pbar.tau ^ 2).asHom ∈
        twoSidedEndomorphismSpan k (F.map cycle)) :
    twoSidedEndomorphismSpan k (P.tau ^ 2).asHom ≤
      twoSidedEndomorphismSpan k cycle := by
  dsimp only at hmem
  let F := figure13QuotientFunctor S f g P
  let Pbar :=
    LargeIndecomposable.RoiterFigure13Quotient.quotientMiddlePowerParameter
      S f g P hXY hYZ hleft
  letI : Module.Finite k (End Y) := by
    change Module.Finite k (Y ⟶ Y)
    infer_instance
  obtain ⟨q, hqSpan, hqMap⟩ :=
    exists_preimage_mem_twoSidedEndomorphismSpan_of_full F hmem
  have htauSq : P.tau ^ 2 ≠ 0 := by
    intro hzero
    apply hleft
    rw [hzero]
    change f ≫ (0 : Y ⟶ Y) = 0
    exact Limits.comp_zero
  have hmapTauSq : F.map (P.tau ^ 2).asHom =
      (Pbar.tau ^ 2).asHom := by
    have htauMap : Pbar.tau.asHom = F.map P.tau.asHom := by rfl
    calc
      F.map (P.tau ^ 2).asHom =
          F.map (P.tau.asHom ≫ P.tau.asHom) := by
            rw [pow_two, End.mul_def]
      _ = F.map P.tau.asHom ≫ F.map P.tau.asHom := F.map_comp _ _
      _ = Pbar.tau.asHom ≫ Pbar.tau.asHom := by rw [htauMap]
      _ = (Pbar.tau ^ 2).asHom := by rw [← End.mul_def, ← pow_two]
  let d : Y ⟶ Y := (P.tau ^ 2).asHom - q
  have hdMap : F.map d = 0 := by
    dsimp only [d]
    rw [F.map_sub, hmapTauSq, hqMap, sub_self]
  have hdIdeal : d.1 ∈
      (LargeIndecomposable.RoiterFigure13Quotient.relationIdeal
        S f g P).asIdeal :=
    (S.projectiveQuotientFunctor_map_eq_zero_iff
      (LargeIndecomposable.RoiterFigure13Quotient.relationIdeal S f g P)
      (LargeIndecomposable.RoiterFigure13Quotient.relationIdeal_le_jacobson
        S f g P) d).1 hdMap
  have hdCorner : d ∈ finiteIdealCorner S
      (LargeIndecomposable.RoiterFigure13Quotient.relationIdeal S f g P)
      Y Y := hdIdeal
  have hdTauCube :=
    LargeIndecomposable.RoiterFigure13Quotient.relationIdeal_corner_middle_le
      S f g P hXY hYZ hdCorner
  have hdSpanLe : twoSidedEndomorphismSpan k d ≤
      twoSidedEndomorphismSpan k (P.tau ^ 3).asHom :=
    twoSidedEndomorphismSpan_le_of_mem hdTauCube
  have hdSpanLt : twoSidedEndomorphismSpan k d <
      twoSidedEndomorphismSpan k (P.tau ^ 2).asHom :=
    hdSpanLe.trans_lt (P.power_succ_span_lt 2 htauSq)
  have hperturb := twoSidedEndomorphismSpan_sub_smul_eq_of_lt
    (k := k) (P.tau ^ 2).asHom d 1 hdSpanLt
  have hsub : (P.tau ^ 2).asHom - d = q := by
    dsimp only [d]
    module
  have hqSpanEq : twoSidedEndomorphismSpan k q =
      twoSidedEndomorphismSpan k (P.tau ^ 2).asHom := by
    simpa only [one_smul, hsub] using hperturb
  calc
    twoSidedEndomorphismSpan k (P.tau ^ 2).asHom =
        twoSidedEndomorphismSpan k q := hqSpanEq.symm
    _ ≤ twoSidedEndomorphismSpan k cycle :=
      twoSidedEndomorphismSpan_le_of_mem hqSpan

/-- The middle square in the Figure-13 quotient does not factor through the
left outer object.  A hypothetical factorization has a dominant cycle through
the zero representative `alpha`; lifting it changes the ambient square only
by a `tau^3`-term.  The resulting ambient unit-ray equality contradicts
`alpha beta = 0` and the nonzero right square arm. -/
theorem zeroRepresentativePair_middleSquare_not_mem_through_left
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (R : ZeroRepresentativePair S f g)
    (hfspan : twoSidedEndomorphismSpan k f = ⊤)
    (hXY : X ≠ Y) (hYZ : Y ≠ Z)
    (hfNotC : ¬ LargeIndecomposable.AllowsCotransit f)
    (hleft : f ≫ (P.tau ^ 2).asHom ≠ 0)
    (hright : (P.tau ^ 2).asHom ≫ g ≠ 0) :
    let F := figure13QuotientFunctor S f g P
    let Pbar :=
      LargeIndecomposable.RoiterFigure13Quotient.quotientMiddlePowerParameter
        S f g P hXY hYZ hleft
    (Pbar.tau ^ 2).asHom ∉
      LargeIndecomposable.RoiterFigure13E.throughObjectSubmodule
        (k := k) (F.obj X) (F.obj Y) := by
  dsimp only
  let F := figure13QuotientFunctor S f g P
  let Pbar :=
    LargeIndecomposable.RoiterFigure13Quotient.quotientMiddlePowerParameter
      S f g P hXY hYZ hleft
  let alphaBar := F.map R.alpha
  letI : Module.Finite k (End Y) := by
    change Module.Finite k (Y ⟶ Y)
    infer_instance
  letI : ∀ T : (figure13QuotientSplitBasic S f g P).ProjectiveCategory,
      Module.Finite k (End T) := fun T ↦ by
    change Module.Finite k (T ⟶ T)
    infer_instance
  have htauBarSq : (Pbar.tau ^ 2).asHom ≠ 0 := by
    have hsquare :=
      LargeIndecomposable.RoiterFigure13Quotient.quotientDiagram_middle_square_ne_zero
        S f g P hXY hYZ hleft
    have htauMap : Pbar.tau.asHom = F.map P.tau.asHom := by rfl
    change F.map P.tau.asHom ≫ F.map P.tau.asHom ≠ 0 at hsquare
    rw [← htauMap] at hsquare
    simpa only [pow_two, End.mul_def] using hsquare
  intro hthrough
  obtain ⟨lbar, rbar, hdominates⟩ :=
    exists_dominating_factorization_of_mem_throughObjectSubmodule
      hthrough htauBarSq
  have hfT : LargeIndecomposable.AllowsTransit f :=
    (LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := S.ProjectiveCategory) f).resolve_right hfNotC
  have hAlphaT : LargeIndecomposable.AllowsTransit alphaBar :=
    LargeIndecomposable.RoiterFigure13Quotient.quotientFunctor_map_allowsTransit
      S f g P R.alpha (hfT.of_unitRayEquivalent R.alpha_equivalent)
  have hAlphaSpan : twoSidedEndomorphismSpan k alphaBar = ⊤ := by
    apply LargeIndecomposable.RoiterFigure13Quotient.quotientFunctor_map_span_eq_top
    rw [← LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
      k R.alpha_equivalent, hfspan]
  have hrbarMem : rbar ∈ twoSidedEndomorphismSpan k alphaBar := by
    rw [hAlphaSpan]
    exact Submodule.mem_top
  obtain ⟨a, hrbar⟩ :=
    exists_comp_right_of_mem_twoSidedSpan_of_allowsTransit
      (k := k) hAlphaT hrbarMem
  have hfactorMem : lbar ≫ rbar ∈
      twoSidedEndomorphismSpan k (lbar ≫ alphaBar) := by
    rw [hrbar]
    apply Submodule.subset_span
    refine ⟨1, a, ?_⟩
    change lbar ≫ alphaBar ≫ a.asHom =
      ((𝟙 (F.obj Y)) ≫ (lbar ≫ alphaBar)) ≫ a.asHom
    rw [Category.id_comp]
    exact (Category.assoc lbar alphaBar a.asHom).symm
  have htauCycleBar : (Pbar.tau ^ 2).asHom ∈
      twoSidedEndomorphismSpan k (lbar ≫ alphaBar) :=
    (twoSidedEndomorphismSpan_le_of_mem hfactorMem) hdominates
  obtain ⟨l, hl⟩ := F.map_surjective lbar
  let cycle : Y ⟶ Y := l ≫ R.alpha
  have htauCycleBar' : (Pbar.tau ^ 2).asHom ∈
      twoSidedEndomorphismSpan k (F.map cycle) := by
    simpa only [cycle, Functor.map_comp, hl, alphaBar] using htauCycleBar
  have htauLeCycle : twoSidedEndomorphismSpan k (P.tau ^ 2).asHom ≤
      twoSidedEndomorphismSpan k cycle :=
    ambient_middle_square_span_le_of_quotient_mem_span
      S f g P hXY hYZ hleft htauCycleBar'
  have hAlphaNotC : ¬ LargeIndecomposable.AllowsCotransit R.alpha := by
    intro hAlphaC
    exact hfNotC
      ((LargeIndecomposable.allowsCotransit_iff_of_unitRayEquivalent
        R.alpha_equivalent).2 hAlphaC)
  have hcycleSq : End.of cycle ∈ (Ring.jacobson (End Y)) ^ 2 := by
    dsimp only [cycle]
    exact
      LargeIndecomposable.RoiterFigure13Quotient.reverse_comp_mem_target_jacobson_sq_of_not_allowsCotransit
        S R.alpha P hXY hAlphaNotC l
  have hcycleMem : cycle ∈
      twoSidedEndomorphismSpan k (P.tau ^ 2).asHom := by
    change (End.of cycle).asHom ∈ _
    exact mem_tau_square_span_of_mem_jacobson_sq P hcycleSq
  have hcycleLeTau : twoSidedEndomorphismSpan k cycle ≤
      twoSidedEndomorphismSpan k (P.tau ^ 2).asHom :=
    twoSidedEndomorphismSpan_le_of_mem hcycleMem
  have hspanEq : twoSidedEndomorphismSpan k cycle =
      twoSidedEndomorphismSpan k (P.tau ^ 2).asHom :=
    le_antisymm hcycleLeTau htauLeCycle
  have hray : LargeIndecomposable.UnitRayEquivalent
      cycle (P.tau ^ 2).asHom :=
    LargeIndecomposable.unitRayEquivalent_of_twoSidedEndomorphismSpan_eq hspanEq
  rcases hray with ⟨a₀, b₀, hray⟩
  have htauBeta : (P.tau ^ 2).asHom ≫ R.beta ≠ 0 :=
    precompose_tau_square_ne_zero_of_unitRayEquivalent
      P R.beta_equivalent hright
  apply htauBeta
  have hzero : ((P.tau ^ 2).asHom ≫ b₀.inv) ≫ R.beta = 0 := by
    calc
      ((P.tau ^ 2).asHom ≫ b₀.inv) ≫ R.beta =
          ((a₀.hom ≫ cycle ≫ b₀.hom) ≫ b₀.inv) ≫ R.beta := by
            rw [hray]
      _ = a₀.hom ≫ (l ≫ (R.alpha ≫ R.beta)) := by
            dsimp only [cycle]
            simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = 0 := by rw [R.comp_zero, Limits.comp_zero, Limits.comp_zero]
  have hcomm : (P.tau ^ 2).asHom ≫ b₀.inv =
      b₀.inv ≫ (P.tau ^ 2).asHom := by
    simpa only [End.mul_def] using congrArg End.asHom
      (P.mul_comm (End.of b₀.inv) (P.tau ^ 2))
  have hcancel : b₀.inv ≫ ((P.tau ^ 2).asHom ≫ R.beta) = 0 := by
    calc
      b₀.inv ≫ ((P.tau ^ 2).asHom ≫ R.beta) =
          ((P.tau ^ 2).asHom ≫ b₀.inv) ≫ R.beta := by
            rw [hcomm]
            simp only [Category.assoc]
      _ = 0 := hzero
  calc
    (P.tau ^ 2).asHom ≫ R.beta =
        b₀.hom ≫ (b₀.inv ≫ ((P.tau ^ 2).asHom ≫ R.beta)) := by
          rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    _ = 0 := by rw [hcancel]; exact Limits.comp_zero

/-- Source-dual middle-square exclusion through the right outer object. -/
theorem zeroRepresentativePair_middleSquare_not_mem_through_right
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (R : ZeroRepresentativePair S f g)
    (hgspan : twoSidedEndomorphismSpan k g = ⊤)
    (hXY : X ≠ Y) (hYZ : Y ≠ Z)
    (hgNotT : ¬ LargeIndecomposable.AllowsTransit g)
    (hleft : f ≫ (P.tau ^ 2).asHom ≠ 0) :
    let F := figure13QuotientFunctor S f g P
    let Pbar :=
      LargeIndecomposable.RoiterFigure13Quotient.quotientMiddlePowerParameter
        S f g P hXY hYZ hleft
    (Pbar.tau ^ 2).asHom ∉
      LargeIndecomposable.RoiterFigure13E.throughObjectSubmodule
        (k := k) (F.obj Z) (F.obj Y) := by
  dsimp only
  let F := figure13QuotientFunctor S f g P
  let Pbar :=
    LargeIndecomposable.RoiterFigure13Quotient.quotientMiddlePowerParameter
      S f g P hXY hYZ hleft
  let betaBar := F.map R.beta
  letI : Module.Finite k (End Y) := by
    change Module.Finite k (Y ⟶ Y)
    infer_instance
  letI : ∀ T : (figure13QuotientSplitBasic S f g P).ProjectiveCategory,
      Module.Finite k (End T) := fun T ↦ by
    change Module.Finite k (T ⟶ T)
    infer_instance
  have htauBarSq : (Pbar.tau ^ 2).asHom ≠ 0 := by
    have hsquare :=
      LargeIndecomposable.RoiterFigure13Quotient.quotientDiagram_middle_square_ne_zero
        S f g P hXY hYZ hleft
    have htauMap : Pbar.tau.asHom = F.map P.tau.asHom := by rfl
    change F.map P.tau.asHom ≫ F.map P.tau.asHom ≠ 0 at hsquare
    rw [← htauMap] at hsquare
    simpa only [pow_two, End.mul_def] using hsquare
  intro hthrough
  obtain ⟨lbar, rbar, hdominates⟩ :=
    exists_dominating_factorization_of_mem_throughObjectSubmodule
      hthrough htauBarSq
  have hgC : LargeIndecomposable.AllowsCotransit g :=
    (LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := S.ProjectiveCategory) g).resolve_left hgNotT
  have hBetaC : LargeIndecomposable.AllowsCotransit betaBar :=
    LargeIndecomposable.RoiterFigure13Quotient.quotientFunctor_map_allowsCotransit
      S f g P R.beta (hgC.of_unitRayEquivalent R.beta_equivalent)
  have hBetaSpan : twoSidedEndomorphismSpan k betaBar = ⊤ := by
    apply LargeIndecomposable.RoiterFigure13Quotient.quotientFunctor_map_span_eq_top
    rw [← LargeIndecomposable.twoSidedEndomorphismSpan_eq_of_unitRayEquivalent
      k R.beta_equivalent, hgspan]
  have hlbarMem : lbar ∈ twoSidedEndomorphismSpan k betaBar := by
    rw [hBetaSpan]
    exact Submodule.mem_top
  obtain ⟨a, hlbar⟩ :=
    exists_comp_left_of_mem_twoSidedSpan_of_allowsCotransit
      (k := k) hBetaC hlbarMem
  have hfactorMem : lbar ≫ rbar ∈
      twoSidedEndomorphismSpan k (betaBar ≫ rbar) := by
    rw [hlbar]
    apply Submodule.subset_span
    refine ⟨a, 1, ?_⟩
    change (a.asHom ≫ betaBar) ≫ rbar =
      (a.asHom ≫ (betaBar ≫ rbar)) ≫ 𝟙 (F.obj Y)
    rw [Category.comp_id]
    exact Category.assoc a.asHom betaBar rbar
  have htauCycleBar : (Pbar.tau ^ 2).asHom ∈
      twoSidedEndomorphismSpan k (betaBar ≫ rbar) :=
    (twoSidedEndomorphismSpan_le_of_mem hfactorMem) hdominates
  obtain ⟨r, hr⟩ := F.map_surjective rbar
  let cycle : Y ⟶ Y := R.beta ≫ r
  have htauCycleBar' : (Pbar.tau ^ 2).asHom ∈
      twoSidedEndomorphismSpan k (F.map cycle) := by
    simpa only [cycle, Functor.map_comp, hr, betaBar] using htauCycleBar
  have htauLeCycle : twoSidedEndomorphismSpan k (P.tau ^ 2).asHom ≤
      twoSidedEndomorphismSpan k cycle :=
    ambient_middle_square_span_le_of_quotient_mem_span
      S f g P hXY hYZ hleft htauCycleBar'
  have hBetaNotT : ¬ LargeIndecomposable.AllowsTransit R.beta := by
    intro hBetaT
    exact hgNotT
      ((LargeIndecomposable.allowsTransit_iff_of_unitRayEquivalent
        R.beta_equivalent).2 hBetaT)
  have hcycleSq : End.of cycle ∈ (Ring.jacobson (End Y)) ^ 2 := by
    dsimp only [cycle]
    exact
      LargeIndecomposable.RoiterFigure13Quotient.comp_reverse_mem_source_jacobson_sq_of_not_allowsTransit
        S R.beta P hYZ hBetaNotT r
  have hcycleMem : cycle ∈
      twoSidedEndomorphismSpan k (P.tau ^ 2).asHom := by
    change (End.of cycle).asHom ∈ _
    exact mem_tau_square_span_of_mem_jacobson_sq P hcycleSq
  have hcycleLeTau : twoSidedEndomorphismSpan k cycle ≤
      twoSidedEndomorphismSpan k (P.tau ^ 2).asHom :=
    twoSidedEndomorphismSpan_le_of_mem hcycleMem
  have hspanEq : twoSidedEndomorphismSpan k cycle =
      twoSidedEndomorphismSpan k (P.tau ^ 2).asHom :=
    le_antisymm hcycleLeTau htauLeCycle
  have hray : LargeIndecomposable.UnitRayEquivalent
      cycle (P.tau ^ 2).asHom :=
    LargeIndecomposable.unitRayEquivalent_of_twoSidedEndomorphismSpan_eq hspanEq
  rcases hray with ⟨a₀, b₀, hray⟩
  have hAlphaTau : R.alpha ≫ (P.tau ^ 2).asHom ≠ 0 :=
    postcompose_tau_square_ne_zero_of_unitRayEquivalent
      P R.alpha_equivalent hleft
  apply hAlphaTau
  have hzero : R.alpha ≫ (a₀.inv ≫ (P.tau ^ 2).asHom) = 0 := by
    calc
      R.alpha ≫ (a₀.inv ≫ (P.tau ^ 2).asHom) =
          R.alpha ≫ (a₀.inv ≫ (a₀.hom ≫ cycle ≫ b₀.hom)) := by
            rw [hray]
      _ = (R.alpha ≫ R.beta) ≫ (r ≫ b₀.hom) := by
            dsimp only [cycle]
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = 0 := by rw [R.comp_zero, Limits.zero_comp]
  have hcomm : a₀.inv ≫ (P.tau ^ 2).asHom =
      (P.tau ^ 2).asHom ≫ a₀.inv := by
    simpa only [End.mul_def] using congrArg End.asHom
      (P.mul_comm (End.of a₀.inv) (P.tau ^ 2)).symm
  have hcancel : (R.alpha ≫ (P.tau ^ 2).asHom) ≫ a₀.inv = 0 := by
    calc
      (R.alpha ≫ (P.tau ^ 2).asHom) ≫ a₀.inv =
          R.alpha ≫ (a₀.inv ≫ (P.tau ^ 2).asHom) := by
            rw [hcomm]
            simp only [Category.assoc]
      _ = 0 := hzero
  calc
    R.alpha ≫ (P.tau ^ 2).asHom =
        ((R.alpha ≫ (P.tau ^ 2).asHom) ≫ a₀.inv) ≫ a₀.hom := by
          rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = 0 := by rw [hcancel]; exact Limits.zero_comp

/-- The left source-printed arm supplement holds for every zero
representative pair selected from the two prescribed outer unit rays. -/
theorem zeroRepresentativePair_leftArmSupplement_separated
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (R : ZeroRepresentativePair S f g)
    (hfspan : twoSidedEndomorphismSpan k f = ⊤)
    (hXY : X ≠ Y) (hYZ : Y ≠ Z)
    (hfNotC : ¬ LargeIndecomposable.AllowsCotransit f)
    (hleft : f ≫ (P.tau ^ 2).asHom ≠ 0) :
    let F := figure13QuotientFunctor S f g P
    let Pbar :=
      LargeIndecomposable.RoiterFigure13Quotient.quotientMiddlePowerParameter
        S f g P hXY hYZ hleft
    F.map R.alpha ≫ Pbar.tau.asHom ∉
      LargeIndecomposable.RoiterFigure13E.leftArmSupplementObstruction
        (k := k) (F.map R.alpha) Pbar.tau := by
  dsimp only
  let Q := figure13QuotientSplitBasic S f g P
  let F := figure13QuotientFunctor S f g P
  let Pbar :=
    LargeIndecomposable.RoiterFigure13Quotient.quotientMiddlePowerParameter
      S f g P hXY hYZ hleft
  letI : ∀ T : Q.ProjectiveCategory, Module.Finite k (End T) := fun T ↦ by
    change Module.Finite k (T ⟶ T)
    infer_instance
  have hfT : LargeIndecomposable.AllowsTransit f :=
    (LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := S.ProjectiveCategory) f).resolve_right hfNotC
  have halphaT : LargeIndecomposable.AllowsTransit (F.map R.alpha) :=
    LargeIndecomposable.RoiterFigure13Quotient.quotientFunctor_map_allowsTransit
      S f g P R.alpha (hfT.of_unitRayEquivalent R.alpha_equivalent)
  have hmapRay : LargeIndecomposable.UnitRayEquivalent
      (F.map f) (F.map R.alpha) :=
    unitRayEquivalent_map F R.alpha_equivalent
  have halphaNotC : ¬ LargeIndecomposable.AllowsCotransit
      (F.map R.alpha) := by
    intro halphaC
    exact (quotientFunctor_map_not_allowsCotransit
      S f g P hfspan hfNotC)
        ((LargeIndecomposable.allowsCotransit_iff_of_unitRayEquivalent
          hmapRay).2 halphaC)
  have hfTau : F.map f ≫ Pbar.tau.asHom ≠ 0 := by
    have h :=
      LargeIndecomposable.RoiterFigure13Quotient.quotientDiagram_left_adjacent_ne_zero
        S f g P hfspan hleft
    change F.map f ≫ Pbar.tau.asHom ≠ 0
    exact h
  have halphaTau : F.map R.alpha ≫ Pbar.tau.asHom ≠ 0 := by
    rcases hmapRay with ⟨a, b, hab⟩
    intro hzero
    have hbcomm := congrArg End.asHom
      (Pbar.mul_comm (End.of b.hom) Pbar.tau)
    rw [hab, Category.assoc] at hzero
    have hzero' : a.hom ≫
        ((F.map f ≫ Pbar.tau.asHom) ≫ b.hom) = 0 := by
      calc
        a.hom ≫ ((F.map f ≫ Pbar.tau.asHom) ≫ b.hom) =
            (a.hom ≫ F.map f ≫ b.hom) ≫ Pbar.tau.asHom := by
              simpa only [End.mul_def, Category.assoc] using
                congrArg (fun z : F.obj Y ⟶ F.obj Y ↦
                  a.hom ≫ F.map f ≫ z) hbcomm
        _ = 0 := by simpa only [Category.assoc] using hzero
    apply hfTau
    have hleftCancel :
        (F.map f ≫ Pbar.tau.asHom) ≫ b.hom = 0 := by
      calc
        (F.map f ≫ Pbar.tau.asHom) ≫ b.hom =
            a.inv ≫ (a.hom ≫ ((F.map f ≫ Pbar.tau.asHom) ≫ b.hom)) := by
              rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
        _ = a.inv ≫ 0 := by rw [hzero']
        _ = 0 := Limits.comp_zero
    calc
      F.map f ≫ Pbar.tau.asHom =
          ((F.map f ≫ Pbar.tau.asHom) ≫ b.hom) ≫ b.inv := by
            rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = 0 ≫ b.inv := by rw [hleftCancel]
      _ = 0 := Limits.zero_comp
  exact
    LargeIndecomposable.RoiterFigure13E.leftArmSupplement_separated_of_not_allowsCotransit
      (F.map R.alpha) Pbar halphaT halphaNotC halphaTau

/-- The source-dual right arm supplement holds for every selected zero
representative pair. -/
theorem zeroRepresentativePair_rightArmSupplement_separated
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (R : ZeroRepresentativePair S f g)
    (hgspan : twoSidedEndomorphismSpan k g = ⊤)
    (hXY : X ≠ Y) (hYZ : Y ≠ Z)
    (hgNotT : ¬ LargeIndecomposable.AllowsTransit g)
    (hleft : f ≫ (P.tau ^ 2).asHom ≠ 0)
    (hright : (P.tau ^ 2).asHom ≫ g ≠ 0) :
    let F := figure13QuotientFunctor S f g P
    let Pbar :=
      LargeIndecomposable.RoiterFigure13Quotient.quotientMiddlePowerParameter
        S f g P hXY hYZ hleft
    Pbar.tau.asHom ≫ F.map R.beta ∉
      LargeIndecomposable.RoiterFigure13E.rightArmSupplementObstruction
        (k := k) (F.map R.beta) Pbar.tau := by
  dsimp only
  let Q := figure13QuotientSplitBasic S f g P
  let F := figure13QuotientFunctor S f g P
  let Pbar :=
    LargeIndecomposable.RoiterFigure13Quotient.quotientMiddlePowerParameter
      S f g P hXY hYZ hleft
  letI : ∀ T : Q.ProjectiveCategory, Module.Finite k (End T) := fun T ↦ by
    change Module.Finite k (T ⟶ T)
    infer_instance
  have hgC : LargeIndecomposable.AllowsCotransit g :=
    (LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := S.ProjectiveCategory) g).resolve_left hgNotT
  have hbetaC : LargeIndecomposable.AllowsCotransit (F.map R.beta) :=
    LargeIndecomposable.RoiterFigure13Quotient.quotientFunctor_map_allowsCotransit
      S f g P R.beta (hgC.of_unitRayEquivalent R.beta_equivalent)
  have hmapRay : LargeIndecomposable.UnitRayEquivalent
      (F.map g) (F.map R.beta) :=
    unitRayEquivalent_map F R.beta_equivalent
  have hbetaNotT : ¬ LargeIndecomposable.AllowsTransit
      (F.map R.beta) := by
    intro hbetaT
    exact (quotientFunctor_map_not_allowsTransit
      S f g P hgspan hgNotT)
        ((LargeIndecomposable.allowsTransit_iff_of_unitRayEquivalent
          hmapRay).2 hbetaT)
  have htauG : Pbar.tau.asHom ≫ F.map g ≠ 0 := by
    have h :=
      LargeIndecomposable.RoiterFigure13Quotient.quotientDiagram_right_adjacent_ne_zero
        S f g P hgspan hright
    change Pbar.tau.asHom ≫ F.map g ≠ 0
    exact h
  have htauBeta : Pbar.tau.asHom ≫ F.map R.beta ≠ 0 := by
    rcases hmapRay with ⟨a, b, hab⟩
    intro hzero
    have hacomm := congrArg End.asHom
      (Pbar.mul_comm Pbar.tau (End.of a.hom))
    rw [hab] at hzero
    have hzero' : a.hom ≫
        ((Pbar.tau.asHom ≫ F.map g) ≫ b.hom) = 0 := by
      calc
        a.hom ≫ ((Pbar.tau.asHom ≫ F.map g) ≫ b.hom) =
            Pbar.tau.asHom ≫ (a.hom ≫ F.map g ≫ b.hom) := by
              simpa only [End.mul_def, Category.assoc] using
                congrArg (fun z : F.obj Y ⟶ F.obj Y ↦
                  z ≫ F.map g ≫ b.hom) hacomm
        _ = 0 := hzero
    apply htauG
    have hleftCancel :
        (Pbar.tau.asHom ≫ F.map g) ≫ b.hom = 0 := by
      calc
        (Pbar.tau.asHom ≫ F.map g) ≫ b.hom =
            a.inv ≫ (a.hom ≫ ((Pbar.tau.asHom ≫ F.map g) ≫ b.hom)) := by
              rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
        _ = a.inv ≫ 0 := by rw [hzero']
        _ = 0 := Limits.comp_zero
    calc
      Pbar.tau.asHom ≫ F.map g =
          ((Pbar.tau.asHom ≫ F.map g) ≫ b.hom) ≫ b.inv := by
            rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = 0 ≫ b.inv := by rw [hleftCancel]
      _ = 0 := Limits.zero_comp
  exact
    LargeIndecomposable.RoiterFigure13E.rightArmSupplement_separated_of_not_allowsTransit
      (F.map R.beta) Pbar hbetaC hbetaNotT htauBeta

/-- All four supplement statements printed after BGRS Figure 13 hold for
the zero representatives selected in the exact hard branch. -/
theorem zeroRepresentativePair_figure13EPrintedSupplementData
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (R : ZeroRepresentativePair S f g)
    (hfspan : twoSidedEndomorphismSpan k f = ⊤)
    (hgspan : twoSidedEndomorphismSpan k g = ⊤)
    (hXY : X ≠ Y) (hYZ : Y ≠ Z)
    (hfNotC : ¬ LargeIndecomposable.AllowsCotransit f)
    (hgNotT : ¬ LargeIndecomposable.AllowsTransit g)
    (hleft : f ≫ (P.tau ^ 2).asHom ≠ 0)
    (hright : (P.tau ^ 2).asHom ≫ g ≠ 0) :
    let F := figure13QuotientFunctor S f g P
    let Pbar :=
      LargeIndecomposable.RoiterFigure13Quotient.quotientMiddlePowerParameter
        S f g P hXY hYZ hleft
    LargeIndecomposable.RoiterFigure13E.Figure13EPrintedSupplementData
      (k := k) (F.map R.alpha) (F.map R.beta) Pbar.tau := by
  dsimp only
  let F := figure13QuotientFunctor S f g P
  let Pbar :=
    LargeIndecomposable.RoiterFigure13Quotient.quotientMiddlePowerParameter
      S f g P hXY hYZ hleft
  letI : ∀ T : (figure13QuotientSplitBasic S f g P).ProjectiveCategory,
      Module.Finite k (End T) := fun T ↦ by
    change Module.Finite k (T ⟶ T)
    infer_instance
  have htauBarSq : Pbar.tau ^ 2 ≠ 0 := by
    have hsquare :=
      LargeIndecomposable.RoiterFigure13Quotient.quotientDiagram_middle_square_ne_zero
        S f g P hXY hYZ hleft
    have htauMap : Pbar.tau.asHom = F.map P.tau.asHom := by rfl
    change F.map P.tau.asHom ≫ F.map P.tau.asHom ≠ 0 at hsquare
    rw [← htauMap] at hsquare
    intro hzero
    apply hsquare
    change Pbar.tau.asHom ≫ Pbar.tau.asHom = 0
    rw [← End.mul_def, ← pow_two, hzero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact zeroRepresentativePair_leftArmSupplement_separated
      S f g P R hfspan hXY hYZ hfNotC hleft
  · apply
      LargeIndecomposable.RoiterFigure13E.middleSquareSideSupplement_separated_of_not_mem_throughObject
        Pbar htauBarSq
    exact zeroRepresentativePair_middleSquare_not_mem_through_left
      S f g P R hfspan hXY hYZ hfNotC hleft hright
  · apply
      LargeIndecomposable.RoiterFigure13E.middleSquareSideSupplement_separated_of_not_mem_throughObject
        Pbar htauBarSq
    exact zeroRepresentativePair_middleSquare_not_mem_through_right
      S f g P R hgspan hXY hYZ hgNotT hleft
  · exact zeroRepresentativePair_rightArmSupplement_separated
      S f g P R hgspan hXY hYZ hgNotT hleft hright

/-- The exact hard branch is impossible for a representation-finite algebra:
Figure 13D supplies zero representatives, the four source-printed Figure 13E
supplements hold for them, and Figure 13E forbids those supplements. -/
theorem false_of_figure13_exact_hard_branch
    [Infinite k]
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (R : ZeroRepresentativePair S f g)
    (hfinite : LargeIndecomposable.MildAlg k A)
    (hfspan : twoSidedEndomorphismSpan k f = ⊤)
    (hgspan : twoSidedEndomorphismSpan k g = ⊤)
    (hXY : X ≠ Y) (hYZ : Y ≠ Z)
    (hfNotC : ¬ LargeIndecomposable.AllowsCotransit f)
    (hgNotT : ¬ LargeIndecomposable.AllowsTransit g)
    (hleft : f ≫ (P.tau ^ 2).asHom ≠ 0)
    (hright : (P.tau ^ 2).asHom ≫ g ≠ 0) : False := by
  apply not_zeroRepresentativePair_figure13EPrintedSupplements
    S f g P R hfinite hfspan hgspan hXY hYZ hfNotC hgNotT hleft
  exact zeroRepresentativePair_figure13EPrintedSupplementData
    S f g P R hfspan hgspan hXY hYZ hfNotC hgNotT hleft hright

end LargeIndecomposable.RoiterFigure13EAmbient
