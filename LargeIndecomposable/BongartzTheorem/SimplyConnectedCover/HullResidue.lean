module

public import LargeIndecomposable.BongartzTheorem.SimplyConnectedCover.HullCocycle
public import LargeIndecomposable.Crowns.Basic.CrownReduction

/-!
# Interval-finiteness of the cover passes from `P/μ` to `P`

Let `μ` be a long morphism of a finite ray category `P` that is neither invertible nor
irreducible and occurs in no contour. Then `P` and `P/μ` have the same quiver and the same
homotopy relation (Bongartz, *Indecomposables live in all smaller lengths*, lemma in
Section 3.1). The residue functor induces a functor of fundamental groupoids (`resPhi`) with
a left inverse on morphisms (`resPsi_resPhi`), hence an injective map of universal covers
preserving arrows (`resCoverMap`). So interval-finiteness of the cover of `P/μ` gives
interval-finiteness of the cover of `P` (`hullFinite_of_residue`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover

section Lift

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] {x₀ : P}

/-- An arrow at the base of an object of the cover lifts to an irreducible morphism. -/
lemma exists_irreducible_of_arrow (a : Cover x₀) {z : P} (e : RayVert.mk a.y ⟶ RayVert.mk z) :
    ∃ f : a ⟶ ⟨z, a.u ≫ arrCls e⟩, IsIrreducible f := by
  have h : a.u ≫ cls e.1 e.2.1 = a.u ≫ arrCls e := by
    rw [cls_eq e.1 e.2.1 (Quiver.Path.nil.cons e) (Category.id_comp _)]
    simp [pathFG]
  rw [← h]
  exact ⟨liftAt a e.1 e.2.1, isIrreducible_liftAt a e.2⟩

end Lift

section Residue

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [Fintype P] [DecidableEq P]
  [LargeIndecomposable.IsFiniteRayCategory P] {a b : P} (μ : a ⟶ b) (hμ : ¬IsIso μ)
  (hμr : ¬IsIrreducible μ) (hμ0 : μ ≠ 0)

attribute [local instance] isRayCategory_of_finiteRayCategory

lemma except_sound (hcont : NotInContour μ) {X Y : Quiver.FreeGroupoid (RayVert P)}
    (f g : X ⟶ Y) (h : homotopy f g) :
    (CategoryTheory.Quotient.functor (homotopyExcept μ)).map f =
      (CategoryTheory.Quotient.functor (homotopyExcept μ)).map g := by
  cases h with
  | path p q hpq h0 =>
    by_cases hμp : ∃ (hx : _ = a) (hy : _ = b), pathVal p = eqToHom hx ≫ μ ≫ eqToHom hy.symm
    · obtain ⟨hx, hy, hval⟩ := hμp
      subst hx hy
      have hval' : pathVal p = μ := by
        rw [hval]
        change 𝟙 _ ≫ μ ≫ 𝟙 _ = μ
        rw [Category.id_comp, Category.comp_id]
      exact interlaced_sound μ (hcont p q hval' (hpq ▸ hval')) hval'
    · exact CategoryTheory.Quotient.sound _ (homotopyExcept.path p q hpq h0 hμp)

include hμ hμr hμ0 in
lemma res_sound (hlong : IsLongAt μ) {X Y : Quiver.FreeGroupoid (RayVert P)} (f g : X ⟶ Y)
    (h : homotopyExcept μ f g) :
    (CategoryTheory.Quotient.functor (homotopy (P := Res μ))).map ((resFG μ hμ hμr hμ0).map f) =
      (CategoryTheory.Quotient.functor homotopy).map ((resFG μ hμ hμr hμ0).map g) := by
  cases h with
  | path p q hpq h0 hμp =>
    rw [freeGroupoidFunctor_pathFG, freeGroupoidFunctor_pathFG]
    refine CategoryTheory.Quotient.sound _ (homotopy.path _ _ ?_ ?_)
    · rw [pathVal_mapPath, pathVal_mapPath, hpq]
    · rw [pathVal_mapPath]
      intro h
      exact hμp (hlong _ h0 ((LargeIndecomposable.ZeroHomIdeal.functor_map_eq_zero_iff _ _).1 h))

include hμ hμr hμ0 in
lemma inv_sound {X Y : Quiver.FreeGroupoid (RayVert (Res μ))} (f g : X ⟶ Y)
    (h : homotopy f g) :
    (CategoryTheory.Quotient.functor (homotopy (P := P))).map ((resFGInv μ hμ hμr hμ0).map f) =
      (CategoryTheory.Quotient.functor homotopy).map ((resFGInv μ hμ hμr hμ0).map g) := by
  cases h with
  | path p q hpq h0 =>
    rw [freeGroupoidFunctor_pathFG, freeGroupoidFunctor_pathFG]
    have hp := pathVal_inv_mapPath μ hμ hμr hμ0 p
    have hq := pathVal_inv_mapPath μ hμ hμr hμ0 q
    have hnm : ¬LargeIndecomposable.FactorsThroughMorphism μ
        (pathVal ((residueQuiverInv μ hμ hμr hμ0).mapPath p)) := by
      intro hm
      apply h0
      rw [← hp]
      exact (LargeIndecomposable.ZeroHomIdeal.functor_map_eq_zero_iff _ _).2 hm
    refine CategoryTheory.Quotient.sound _ (homotopy.path _ _ ?_ ?_)
    · exact resF_map_injective μ hnm (by rw [hp, hq, hpq])
    · intro hz
      apply h0
      rw [← hp, hz, Functor.map_zero]
      rfl

variable (hlong : IsLongAt μ) (hcont : NotInContour μ)

include hlong hcont in
/-- The functor of fundamental groupoids induced by the residue functor. -/
def resPhi : FundGroupoid P ⥤ FundGroupoid (Res μ) :=
  CategoryTheory.Quotient.lift homotopy
    (CategoryTheory.Quotient.functor (homotopyExcept μ) ⋙
      CategoryTheory.Quotient.lift _
        (resFG μ hμ hμr hμ0 ⋙ CategoryTheory.Quotient.functor homotopy)
        fun _ _ f g h ↦ res_sound μ hμ hμr hμ0 hlong f g h)
    fun _ _ f g h ↦ by
      simp only [Functor.comp_map]
      rw [except_sound μ hcont f g h]

/-- The inverse direction. -/
def resPsi : FundGroupoid (Res μ) ⥤ FundGroupoid P :=
  CategoryTheory.Quotient.lift homotopy
    (resFGInv μ hμ hμr hμ0 ⋙ CategoryTheory.Quotient.functor homotopy)
    fun _ _ f g h ↦ inv_sound μ hμ hμr hμ0 f g h

lemma resPhi_map {X Y : Quiver.FreeGroupoid (RayVert P)} (w : X ⟶ Y) :
    (resPhi μ hμ hμr hμ0 hlong hcont).map ((CategoryTheory.Quotient.functor homotopy).map w) =
      (CategoryTheory.Quotient.functor homotopy).map ((resFG μ hμ hμr hμ0).map w) := by
  simp only [resPhi, CategoryTheory.Quotient.lift_map_functor_map, Functor.comp_map]

lemma resPsi_resPhi {x y : P} (u : vtx x ⟶ vtx y) :
    (resPsi μ hμ hμr hμ0).map ((resPhi μ hμ hμr hμ0 hlong hcont).map u) = u := by
  obtain ⟨w, rfl⟩ := (CategoryTheory.Quotient.functor homotopy).map_surjective u
  rw [resPhi_map]
  erw [CategoryTheory.Quotient.lift_map_functor_map]
  rw [Functor.comp_map]
  have := Functor.congr_hom (resFG_comp_inv μ hμ hμr hμ0) w
  simp only [Functor.comp_map, Functor.id_map] at this
  rw [this]
  simp only [Functor.map_comp, eqToHom_map]
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

lemma resPhi_arrCls {x y : RayVert P} (e : x ⟶ y) :
    (resPhi μ hμ hμr hμ0 hlong hcont).map (arrCls e) =
      arrCls ((residueQuiverMap μ hμ hμr hμ0).map e) := by
  rw [arrCls, resPhi_map]
  rfl

variable {x₀ : P} [IsRayCategory (Res μ)]

/-- The map of universal covers. -/
def resCoverMap (c : Cover x₀) : Cover ((resF μ).obj x₀) :=
  ⟨(resF μ).obj c.y, (resPhi μ hμ hμr hμ0 hlong hcont).map c.u⟩

lemma resCoverMap_injective : Function.Injective (resCoverMap μ hμ hμr hμ0 hlong hcont (x₀ := x₀)) := by
  rintro ⟨y, u⟩ ⟨y', u'⟩ h
  have hy' : y = y' := congrArg CategoryTheory.Quotient.as (congrArg Cover.y h)
  subst hy'
  change Cover.mk _ _ = Cover.mk _ _ at h
  have hu' := eq_of_heq (Cover.mk.inj h).2
  rw [← resPsi_resPhi μ hμ hμr hμ0 hlong hcont u, hu', resPsi_resPhi]

lemma reach_resCoverMap {c d : Cover x₀} (h : Reach c d) :
    Reach (resCoverMap μ hμ hμr hμ0 hlong hcont c) (resCoverMap μ hμ hμr hμ0 hlong hcont d) := by
  induction h with
  | refl => exact Reach.refl _
  | @step c' d' _ f hf _ ih =>
    obtain ⟨e, he⟩ := exists_arrow_of_irreducible hf
    obtain ⟨f', hf'⟩ := exists_irreducible_of_arrow
      (resCoverMap μ hμ hμr hμ0 hlong hcont c') ((residueQuiverMap μ hμ hμr hμ0).map e)
    have hd : (⟨(resF μ).obj d'.y, (resPhi μ hμ hμr hμ0 hlong hcont).map c'.u ≫
        arrCls ((residueQuiverMap μ hμ hμr hμ0).map e)⟩ : Cover ((resF μ).obj x₀)) =
        resCoverMap μ hμ hμr hμ0 hlong hcont d' := by
      simp only [resCoverMap, he, Functor.map_comp, resPhi_arrCls]
      rfl
    exact Reach.step f' hf' (hd ▸ ih)

include hμ hμr hμ0 hlong hcont in
/-- **Interval-finiteness of the cover passes from `P/μ` to `P`.** -/
theorem hullFinite_of_residue (h : HullFinite ((resF μ).obj x₀)) : HullFinite x₀ := by
  classical
  intro T
  obtain ⟨S', hTS', hS'⟩ := h (T.image (resCoverMap μ hμ hμr hμ0 hlong hcont))
  refine ⟨S'.preimage _ (resCoverMap_injective μ hμ hμr hμ0 hlong hcont).injOn,
    fun t ht ↦ ?_, fun c d e hc he hcd hde ↦ ?_⟩
  · exact Finset.mem_preimage.2 (hTS' (Finset.mem_image_of_mem _ ht))
  · simp only [Finset.coe_preimage, Set.mem_preimage, Finset.mem_coe] at hc he ⊢
    exact hS' _ _ _ hc he (reach_resCoverMap μ hμ hμr hμ0 hlong hcont hcd)
      (reach_resCoverMap μ hμ hμr hμ0 hlong hcont hde)

end Residue

end LargeIndecomposable.RayCat
