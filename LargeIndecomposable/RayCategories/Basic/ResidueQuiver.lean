module

public import LargeIndecomposable.RayCategories.Contours.Interlaced
public import LargeIndecomposable.RayCategories.Basic.FromDistributive
public import LargeIndecomposable.RayCategories.RoiterVanishing.RayResidueCategory

/-!
# The quiver of a residue category `P/μ`

For a nonzero morphism `μ` of a finite ray category that is neither invertible
nor irreducible, no irreducible morphism factors through `μ`, so the residue
functor `P ⥤ P/μ` sends irreducible morphisms to irreducible morphisms. This
gives a morphism of quivers `RayVert P ⥤q RayVert (P/μ)`
(`RayCat.residueQuiverMap`) compatible with values of paths
(`pathVal_mapPath`). Input for part (a) of the lemma in Section 3.1 of
Bongartz, *Indecomposables live in all smaller lengths*.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe v u

namespace RayCat

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P]

lemma isIrreducible_iff_isIrreducibleRayMorphism {x y : P} (f : x ⟶ y) :
    IsIrreducible f ↔ LargeIndecomposable.IsIrreducibleRayMorphism f := by
  refine ⟨fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, fun z g h e ↦ h3 z g h e.symm⟩,
    fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, fun z g h e ↦ h3 z g h e.symm⟩⟩

variable [LargeIndecomposable.IsFiniteRayCategory P]

/-- No irreducible morphism factors through a nonzero, non-invertible,
reducible morphism. -/
lemma not_factors_of_irreducible {a b : P} (μ : a ⟶ b) (hμ : ¬IsIso μ) (hμr : ¬IsIrreducible μ)
    (hμ0 : μ ≠ 0) {x y : P} {f : x ⟶ y} (hf : IsIrreducible f) :
    ¬LargeIndecomposable.FactorsThroughMorphism μ f := by
  rintro ⟨α, β, rfl⟩
  simp only [IsIrreducible, not_and, not_forall, not_or] at hμr
  obtain ⟨z, g, h, rfl, hg, hh⟩ := hμr hμ0 hμ
  rcases hf.2.2 _ (α ≫ g) (h ≫ β) (by simp [Category.assoc]) with h1 | h1
  · exact hg (LargeIndecomposable.ray_isIso_factors α g).2
  · exact hh (LargeIndecomposable.ray_isIso_factors h β).1

variable {a b : P} (μ : a ⟶ b) (hμ : ¬IsIso μ) (hμr : ¬IsIrreducible μ) (hμ0 : μ ≠ 0)

/-- The residue category `P/μ`. -/
abbrev Res := LargeIndecomposable.RayResidueCategory μ

/-- The residue functor `P ⥤ P/μ`. -/
abbrev resF : P ⥤ Res μ := LargeIndecomposable.rayResidueFunctor μ

include hμ hμr hμ0 in
lemma resF_irreducible {x y : P} {f : x ⟶ y} (hf : IsIrreducible f) :
    IsIrreducible ((resF μ).map f) :=
  (isIrreducible_iff_isIrreducibleRayMorphism _).2
    (((LargeIndecomposable.principalZeroHomIdeal μ).functor_map_isIrreducible_iff
      (LargeIndecomposable.principalZeroHomIdeal_isProper_of_not_isIso μ hμ) f).2
      ⟨(isIrreducible_iff_isIrreducibleRayMorphism f).1 hf, not_factors_of_irreducible μ hμ hμr hμ0 hf⟩)

/-- The morphism of quivers `RayVert P ⥤q RayVert (P/μ)`. -/
def residueQuiverMap : RayVert P ⥤q RayVert (Res μ) where
  obj x := RayVert.mk ((resF μ).obj x.out)
  map e := ⟨(resF μ).map e.1, resF_irreducible μ hμ hμr hμ0 e.2⟩

/-- Values of paths are compatible with the residue functor. -/
lemma pathVal_mapPath {x : RayVert P} : ∀ {y : RayVert P} (p : Quiver.Path x y),
    pathVal ((residueQuiverMap μ hμ hμr hμ0).mapPath p) = (resF μ).map (pathVal p)
  | _, .nil => ((resF μ).map_id _).symm
  | _, .cons p e => by
    rw [Prefunctor.mapPath_cons]
    change pathVal ((residueQuiverMap μ hμ hμr hμ0).mapPath p) ≫ (resF μ).map e.1 = _
    rw [pathVal_mapPath p]
    exact ((resF μ).map_comp _ _).symm

omit [LargeIndecomposable.IsFiniteRayCategory P] in
/-- Equal images of a morphism outside the ideal are equal. -/
lemma resF_map_injective {x y : P} {f g : x ⟶ y}
    (hf : ¬LargeIndecomposable.FactorsThroughMorphism μ f) (h : (resF μ).map f = (resF μ).map g) :
    f = g := by
  have := (CategoryTheory.Quotient.functor_map_eq_iff _ f g).1 h
  rcases this with h | h
  · exact h
  · exact absurd h.1 hf

/-- A lift of a morphism of `P/μ`. -/
def lift {x y : P} (g : (resF μ).obj x ⟶ (resF μ).obj y) : x ⟶ y := Quot.out g

omit [LargeIndecomposable.IsFiniteRayCategory P] in
lemma resF_lift {x y : P} (g : (resF μ).obj x ⟶ (resF μ).obj y) : (resF μ).map (lift μ g) = g :=
  Quot.out_eq g

include hμ hμr hμ0 in
lemma lift_irreducible {x y : P} {g : (resF μ).obj x ⟶ (resF μ).obj y} (hg : IsIrreducible g) :
    IsIrreducible (lift μ g) := by
  rw [← resF_lift μ g] at hg
  exact (isIrreducible_iff_isIrreducibleRayMorphism _).2
    (((LargeIndecomposable.principalZeroHomIdeal μ).functor_map_isIrreducible_iff
      (LargeIndecomposable.principalZeroHomIdeal_isProper_of_not_isIso μ hμ) _).1
      ((isIrreducible_iff_isIrreducibleRayMorphism _).1 hg)).1

/-- The inverse morphism of quivers `RayVert (P/μ) ⥤q RayVert P`. -/
def residueQuiverInv : RayVert (Res μ) ⥤q RayVert P where
  obj x := RayVert.mk (x.out.as)
  map e := ⟨lift μ e.1, lift_irreducible μ hμ hμr hμ0 e.2⟩

lemma residueQuiver_comp_inv :
    residueQuiverMap μ hμ hμr hμ0 ⋙q residueQuiverInv μ hμ hμr hμ0 = 𝟭q _ := by
  refine Prefunctor.ext (fun _ ↦ rfl) fun x y e ↦ ?_
  simp only [Prefunctor.comp_map, Prefunctor.id_map, eqToHom_refl]
  refine Subtype.ext ?_
  change lift μ ((resF μ).map e.1) = e.1
  exact resF_map_injective μ (not_factors_of_irreducible μ hμ hμr hμ0
    (lift_irreducible μ hμ hμr hμ0 (resF_irreducible μ hμ hμr hμ0 e.2))) (resF_lift μ _)

lemma residueQuiver_inv_comp :
    residueQuiverInv μ hμ hμr hμ0 ⋙q residueQuiverMap μ hμ hμr hμ0 = 𝟭q _ := by
  refine Prefunctor.ext (fun _ ↦ rfl) fun x y e ↦ ?_
  simp only [Prefunctor.comp_map, Prefunctor.id_map, eqToHom_refl]
  exact Subtype.ext (resF_lift μ e.1)

/-- The induced functor of free groupoids. -/
abbrev resFG : Quiver.FreeGroupoid (RayVert P) ⥤ Quiver.FreeGroupoid (RayVert (Res μ)) :=
  Quiver.freeGroupoidFunctor (residueQuiverMap μ hμ hμr hμ0)

/-- The inverse functor of free groupoids. -/
abbrev resFGInv : Quiver.FreeGroupoid (RayVert (Res μ)) ⥤ Quiver.FreeGroupoid (RayVert P) :=
  Quiver.freeGroupoidFunctor (residueQuiverInv μ hμ hμr hμ0)

lemma resFG_comp_inv : resFG μ hμ hμr hμ0 ⋙ resFGInv μ hμ hμr hμ0 = 𝟭 _ := by
  rw [← Quiver.freeGroupoidFunctor_comp, residueQuiver_comp_inv,
    Quiver.freeGroupoidFunctor_id]

lemma resFG_inv_comp : resFGInv μ hμ hμr hμ0 ⋙ resFG μ hμ hμr hμ0 = 𝟭 _ := by
  rw [← Quiver.freeGroupoidFunctor_comp, residueQuiver_inv_comp,
    Quiver.freeGroupoidFunctor_id]

omit [LargeIndecomposable.IsFiniteRayCategory P] in
lemma freeGroupoidFunctor_pathFG {Q : Type*} [Category Q] [HasZeroMorphisms Q]
    (φ : RayVert P ⥤q RayVert Q) {x : RayVert P} : ∀ {y : RayVert P} (p : Quiver.Path x y),
    (Quiver.freeGroupoidFunctor φ).map (pathFG p) = pathFG (φ.mapPath p)
  | _, .nil => (Quiver.freeGroupoidFunctor φ).map_id _
  | _, .cons p e => by
    rw [Prefunctor.mapPath_cons]
    change (Quiver.freeGroupoidFunctor φ).map
      (pathFG p ≫ (Quiver.FreeGroupoid.of (RayVert P)).map e) =
      pathFG (φ.mapPath p) ≫ (Quiver.FreeGroupoid.of (RayVert Q)).map (φ.map e)
    rw [Functor.map_comp, freeGroupoidFunctor_pathFG φ p]
    congr 1

lemma pathVal_inv_mapPath {x : RayVert (Res μ)} : ∀ {y : RayVert (Res μ)} (r : Quiver.Path x y),
    (resF μ).map (pathVal ((residueQuiverInv μ hμ hμr hμ0).mapPath r)) = pathVal r
  | _, .nil => (resF μ).map_id _
  | _, .cons r e => by
    rw [Prefunctor.mapPath_cons]
    change (resF μ).map (pathVal ((residueQuiverInv μ hμ hμr hμ0).mapPath r) ≫ lift μ e.1) =
      pathVal r ≫ e.1
    rw [Functor.map_comp, pathVal_inv_mapPath r]
    exact congrArg (fun t ↦ pathVal r ≫ t) (resF_lift μ e.1)

/-- `μ` is long: a nonzero morphism factoring through `μ` is `μ`. -/
def IsLongAt : Prop :=
  ∀ {x y : P} (f : x ⟶ y), f ≠ 0 → LargeIndecomposable.FactorsThroughMorphism μ f →
    ∃ (hx : x = a) (hy : y = b), f = eqToHom hx ≫ μ ≫ eqToHom hy.symm

variable [Finite P]

/-- Part (b) of the lemma in Section 3.1 of Bongartz: if `μ` is long, neither
invertible nor irreducible, and occurs in no contour, the fundamental groups
of `P` and `P/μ` agree. -/
def pi1Equiv (hlong : IsLongAt μ)
    (hcont : letI := isRayCategory_of_finiteRayCategory (C := P); NotInContour μ)
    (X : Quiver.FreeGroupoid (RayVert P)) :
    End ((CategoryTheory.Quotient.functor (homotopy (P := P))).obj X) ≃*
      End ((CategoryTheory.Quotient.functor (homotopy (P := Res μ))).obj
        ((resFG μ hμ hμr hμ0).obj X)) := by
  letI := isRayCategory_of_finiteRayCategory (C := P)
  refine (endEquivExcept μ hcont X).symm.trans
    (endEquivOfFunctors (resFG μ hμ hμr hμ0) (resFGInv μ hμ hμr hμ0) (resFG_comp_inv μ hμ hμr hμ0)
      (resFG_inv_comp μ hμ hμr hμ0) ?_ ?_ X)
  · intro _ _ f g h
    cases h with
    | path p q hpq h0 hμp =>
      rw [freeGroupoidFunctor_pathFG, freeGroupoidFunctor_pathFG]
      refine CategoryTheory.Quotient.sound _ (homotopy.path _ _ ?_ ?_)
      · rw [pathVal_mapPath, pathVal_mapPath, hpq]
      · rw [pathVal_mapPath]
        intro h
        exact hμp (hlong _ h0 ((LargeIndecomposable.ZeroHomIdeal.functor_map_eq_zero_iff _ _).1 h))
  · intro _ _ f g h
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
      refine CategoryTheory.Quotient.sound _ (homotopyExcept.path _ _ ?_ ?_ ?_)
      · exact resF_map_injective μ hnm (by rw [hp, hq, hpq])
      · intro hz
        apply h0
        rw [← hp, hz, Functor.map_zero]
        rfl
      · rintro ⟨hx, hy, he⟩
        exact hnm ⟨eqToHom hx, eqToHom hy.symm, he⟩

end RayCat

end LargeIndecomposable
