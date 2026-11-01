module

public import LargeIndecomposable.RayCategories.Basic.Op

/-!
# The fundamental groupoid of the opposite ray category

Reversing paths and inverting gives mutually inverse functors between the
fundamental groupoids of `P` and `Pᵒᵖ` (`RayCat.opEquiv`): an arrow `e` goes
to the inverse of the class of the reversed arrow. Hence `Π(P)` and `Π(Pᵒᵖ)`
are isomorphic (`RayCat.endEquivOp`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Opposite

universe v u

namespace RayCat

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P]

/-- The class of a path in the fundamental groupoid. -/
abbrev pcls {Q : Type u} [Category.{v} Q] [HasZeroMorphisms Q] {x y : RayVert Q}
    (p : Quiver.Path x y) :
    (CategoryTheory.Quotient.functor (homotopy (P := Q))).obj ((Quiver.FreeGroupoid.of _).obj x) ⟶
      (CategoryTheory.Quotient.functor homotopy).obj ((Quiver.FreeGroupoid.of _).obj y) :=
  (CategoryTheory.Quotient.functor homotopy).map (pathFG p)

/-- The prefunctor `e ↦ [rev e]⁻¹`. -/
def opPre : RayVert P ⥤q FundGroupoid Pᵒᵖ where
  obj x := (CategoryTheory.Quotient.functor homotopy).obj
    ((Quiver.FreeGroupoid.of _).obj (RayVert.mk (op x.out)))
  map e := inv (pcls (revArr e).toPath)

/-- The prefunctor `e ↦ [unrev e]⁻¹`. -/
def unopPre : RayVert Pᵒᵖ ⥤q FundGroupoid P where
  obj X := (CategoryTheory.Quotient.functor homotopy).obj
    ((Quiver.FreeGroupoid.of _).obj (RayVert.mk X.out.unop))
  map e := inv (pcls (unrevArr e).toPath)

/-- `e ↦ [rev e]⁻¹` on free groupoids. -/
def opFG : Quiver.FreeGroupoid (RayVert P) ⥤ FundGroupoid Pᵒᵖ :=
  Quiver.FreeGroupoid.lift opPre

/-- `e ↦ [unrev e]⁻¹` on free groupoids. -/
def unopFG : Quiver.FreeGroupoid (RayVert Pᵒᵖ) ⥤ FundGroupoid P :=
  Quiver.FreeGroupoid.lift unopPre

lemma pcls_cons {Q : Type u} [Category.{v} Q] [HasZeroMorphisms Q] {x y z : RayVert Q}
    (p : Quiver.Path x y) (e : y ⟶ z) :
    pcls (p.cons e) = pcls p ≫ pcls e.toPath := by
  change (CategoryTheory.Quotient.functor homotopy).map (pathFG p ≫ _) = _
  rw [Functor.map_comp]
  change _ = _ ≫ (CategoryTheory.Quotient.functor homotopy).map (𝟙 _ ≫ _)
  rw [Category.id_comp]

lemma pcls_comp {Q : Type u} [Category.{v} Q] [HasZeroMorphisms Q] {x y z : RayVert Q}
    (p : Quiver.Path x y) (q : Quiver.Path y z) : pcls (p.comp q) = pcls p ≫ pcls q := by
  change (CategoryTheory.Quotient.functor homotopy).map _ = _
  rw [pathFG_comp, Functor.map_comp]

lemma opFG_map_of {x y : RayVert P} (e : x ⟶ y) :
    opFG.map ((Quiver.FreeGroupoid.of _).map e) = opPre.map e :=
  lift_map_of opPre e

lemma unopFG_map_of {X Y : RayVert Pᵒᵖ} (e : X ⟶ Y) :
    unopFG.map ((Quiver.FreeGroupoid.of _).map e) = unopPre.map e :=
  lift_map_of unopPre e

lemma opFG_map_pathFG {x : RayVert P} : ∀ {y : RayVert P} (p : Quiver.Path x y),
    opFG.map (pathFG p) = inv (pcls (revPath p))
  | _, .nil => by
    change opFG.map (𝟙 _) = inv (𝟙 _)
    rw [CategoryTheory.Functor.map_id, IsIso.inv_id]
  | _, .cons p e => by
    change opFG.map (pathFG p ≫ (Quiver.FreeGroupoid.of _).map e) = _
    rw [CategoryTheory.Functor.map_comp, opFG_map_pathFG p, opFG_map_of]
    change _ = inv (pcls ((revArr e).toPath.comp (revPath p)))
    simp only [pcls_comp, IsIso.inv_comp]
    rfl

lemma unopFG_map_pathFG {X : RayVert Pᵒᵖ} : ∀ {Y : RayVert Pᵒᵖ} (p : Quiver.Path X Y),
    unopFG.map (pathFG p) = inv (pcls (unrevPath p))
  | _, .nil => by
    change unopFG.map (𝟙 _) = inv (𝟙 _)
    rw [CategoryTheory.Functor.map_id, IsIso.inv_id]
  | _, .cons p e => by
    change unopFG.map (pathFG p ≫ (Quiver.FreeGroupoid.of _).map e) = _
    rw [CategoryTheory.Functor.map_comp, unopFG_map_pathFG p, unopFG_map_of]
    change _ = inv (pcls ((unrevArr e).toPath.comp (unrevPath p)))
    simp only [pcls_comp, IsIso.inv_comp]
    rfl

/-- `opFG` on fundamental groupoids. -/
def opBar : FundGroupoid P ⥤ FundGroupoid Pᵒᵖ :=
  CategoryTheory.Quotient.lift homotopy opFG fun _ _ _ _ h ↦ by
    cases h with
    | path p q hpq h0 =>
      rw [opFG_map_pathFG, opFG_map_pathFG]
      congr 1
      refine homotopic_of_pathVal_eq _ _ ?_ ?_
      · rw [pathVal_revPath, pathVal_revPath, hpq]
      · rw [pathVal_revPath]
        exact fun h ↦ h0 (Quiver.Hom.op_inj (by rw [h, op_zero]))

/-- `unopFG` on fundamental groupoids. -/
def unopBar : FundGroupoid Pᵒᵖ ⥤ FundGroupoid P :=
  CategoryTheory.Quotient.lift homotopy unopFG fun _ _ _ _ h ↦ by
    cases h with
    | path p q hpq h0 =>
      rw [unopFG_map_pathFG, unopFG_map_pathFG]
      congr 1
      refine homotopic_of_pathVal_eq _ _ ?_ ?_
      · rw [pathVal_unrevPath, pathVal_unrevPath, hpq]
      · rw [pathVal_unrevPath]
        exact fun h ↦ h0 (Quiver.Hom.unop_inj (by rw [h, unop_zero]))

omit [Category.{v} P] [HasZeroMorphisms P] in
lemma inv_inv_groupoid {G : Type*} [Groupoid G] {X Y : G} (f : X ⟶ Y) : inv (inv f) = f :=
  IsIso.inv_inv

lemma pcls_toPath {Q : Type u} [Category.{v} Q] [HasZeroMorphisms Q] {x y : RayVert Q}
    (e : x ⟶ y) : pcls e.toPath =
      (CategoryTheory.Quotient.functor homotopy).map ((Quiver.FreeGroupoid.of _).map e) := by
  change (CategoryTheory.Quotient.functor homotopy).map (𝟙 _ ≫ _) = _
  rw [Category.id_comp]

lemma opFG_unopBar : opFG ⋙ unopBar = CategoryTheory.Quotient.functor (homotopy (P := P)) := by
  refine RedData.functor_eq_of_gen _ _ (Prefunctor.ext (fun _ ↦ rfl) fun _ _ e ↦ ?_)
  change unopBar.map (opFG.map ((Quiver.FreeGroupoid.of _).map e)) = _
  rw [opFG_map_of]
  change unopBar.map (inv (pcls (revArr e).toPath)) = _
  rw [Functor.map_inv]
  change inv (unopFG.map (pathFG (revArr e).toPath)) = _
  simp only [unopFG_map_pathFG]
  exact (inv_inv_groupoid _).trans (pcls_toPath e)

lemma unopFG_opBar :
    unopFG ⋙ opBar = CategoryTheory.Quotient.functor (homotopy (P := Pᵒᵖ)) := by
  refine RedData.functor_eq_of_gen _ _ (Prefunctor.ext (fun _ ↦ rfl) fun _ _ e ↦ ?_)
  change opBar.map (unopFG.map ((Quiver.FreeGroupoid.of _).map e)) = _
  rw [unopFG_map_of]
  change opBar.map (inv (pcls (unrevArr e).toPath)) = _
  rw [Functor.map_inv]
  change inv (opFG.map (pathFG (unrevArr e).toPath)) = _
  simp only [opFG_map_pathFG]
  exact (inv_inv_groupoid _).trans (pcls_toPath e)

lemma opBar_unopBar : opBar ⋙ unopBar = 𝟭 (FundGroupoid P) := by
  rw [CategoryTheory.Quotient.lift_unique homotopy (CategoryTheory.Quotient.functor homotopy)
      (fun _ _ _ _ h ↦ CategoryTheory.Quotient.sound _ h) (opBar ⋙ unopBar)
      (by rw [← Functor.assoc, opBar, CategoryTheory.Quotient.lift_spec, opFG_unopBar]),
    CategoryTheory.Quotient.lift_unique homotopy (CategoryTheory.Quotient.functor homotopy)
      (fun _ _ _ _ h ↦ CategoryTheory.Quotient.sound _ h) (𝟭 _) (Functor.comp_id _)]

lemma unopBar_opBar : unopBar ⋙ opBar = 𝟭 (FundGroupoid Pᵒᵖ) := by
  rw [CategoryTheory.Quotient.lift_unique homotopy (CategoryTheory.Quotient.functor homotopy)
      (fun _ _ _ _ h ↦ CategoryTheory.Quotient.sound _ h) (unopBar ⋙ opBar)
      (by rw [← Functor.assoc, unopBar, CategoryTheory.Quotient.lift_spec, unopFG_opBar]),
    CategoryTheory.Quotient.lift_unique homotopy (CategoryTheory.Quotient.functor homotopy)
      (fun _ _ _ _ h ↦ CategoryTheory.Quotient.sound _ h) (𝟭 _) (Functor.comp_id _)]

/-- The fundamental groupoids of `P` and `Pᵒᵖ` are equivalent. -/
def opEquivFund : FundGroupoid P ≌ FundGroupoid Pᵒᵖ :=
  CategoryTheory.Equivalence.mk opBar unopBar (eqToIso opBar_unopBar.symm)
    (eqToIso unopBar_opBar)

/-- `Π(P) ≅ Π(Pᵒᵖ)`. -/
def endEquivOp (X : FundGroupoid P) : End X ≃* End (opBar.obj X) :=
  opEquivFund.fullyFaithfulFunctor.mulEquivEnd X

end RayCat

end LargeIndecomposable
