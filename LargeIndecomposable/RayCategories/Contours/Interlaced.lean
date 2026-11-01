module

public import LargeIndecomposable.FundamentalGroups.Basic.Fundamental
public import LargeIndecomposable.RayCategories.Basic.QuotientCompare

/-!
# Interlaced paths and contours

Two paths are interlaced if they are linked by steps `p v' q ~ p w' q` with
`v' = w' ≠ 0` and `p, q` not both trivial (Gabriel–Roiter 13.6); a contour is a
pair of non-interlaced paths with the same nonzero value. If a morphism `μ`
occurs in no contour, the homotopy relation with the pairs of value `μ`
removed (`homotopyExcept μ`) has the same quotient as the full homotopy
relation, so the fundamental groups agree (`RayCat.endEquivExcept`). With `P/μ`
this is part (b) of the lemma in Section 3.1 of Bongartz, *Indecomposables live
in all smaller lengths*.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe v u

namespace RayCat

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- One interlacing step: `p v' q` and `p w' q` with `v' = w' ≠ 0` and `p, q`
not both trivial. -/
def InterStep {x y : RayVert P} (v w : Quiver.Path x y) : Prop :=
  ∃ (a b : RayVert P) (p : Quiver.Path x a) (v' w' : Quiver.Path a b) (q : Quiver.Path b y),
    v = (p.comp v').comp q ∧ w = (p.comp w').comp q ∧ pathVal v' = pathVal w' ∧
      pathVal v' ≠ 0 ∧ (0 < p.length ∨ 0 < q.length)

/-- Interlaced paths. -/
def Interlaced {x y : RayVert P} (v w : Quiver.Path x y) : Prop :=
  Relation.EqvGen InterStep v w

/-- `μ` occurs in no contour: any two paths with value `μ` are interlaced. -/
def NotInContour {a b : P} (μ : a ⟶ b) : Prop :=
  ∀ (v w : Quiver.Path (RayVert.mk a) (RayVert.mk b)), pathVal v = μ → pathVal w = μ →
    Interlaced v w

/-- The homotopy relation without the pairs of value `μ`. -/
inductive homotopyExcept {a b : P} (μ : a ⟶ b) : HomRel (Quiver.FreeGroupoid (RayVert P))
  | path {x y : RayVert P} (p q : Quiver.Path x y) (h : pathVal p = pathVal q) (h0 : pathVal p ≠ 0)
      (hμ : ¬ ∃ (hx : x.out = a) (hy : y.out = b), pathVal p = eqToHom hx ≫ μ ≫ eqToHom hy.symm) :
      homotopyExcept μ (pathFG p) (pathFG q)

/-- A closed nonempty path does not have the identity as value. -/
lemma pathVal_cons_ne_id {x z : RayVert P} (p : Quiver.Path x z) (e : z ⟶ x) :
    pathVal (p.cons e) ≠ 𝟙 x.out := by
  intro he
  change pathVal p ≫ e.1 = 𝟙 _ at he
  have he0 : e.1 ≠ 0 := e.2.1
  have hcomp : e.1 = (e.1 ≫ pathVal p) ≫ e.1 ≫ 𝟙 _ := by
    rw [Category.comp_id, Category.assoc, he, Category.comp_id]
  obtain ⟨h2, -⟩ := IsRayCategory.eq_id_of_two_sided e.1 he0 _ _ hcomp
  exact e.2.2.1 ⟨pathVal p, h2, he⟩

lemma pathVal_ne_id_of_length {x : RayVert P} : ∀ (p : Quiver.Path x x), 0 < p.length →
    pathVal p ≠ 𝟙 x.out
  | .cons p e, _ => pathVal_cons_ne_id p e

omit [IsRayCategory P] in
lemma pathVal_comp3 {x a b y : RayVert P} (p : Quiver.Path x a) (v : Quiver.Path a b)
    (q : Quiver.Path b y) : pathVal ((p.comp v).comp q) = pathVal p ≫ pathVal v ≫ pathVal q := by
  rw [pathVal_comp, pathVal_comp, Category.assoc]

omit [IsRayCategory P] in
lemma pathFG_comp3 {x a b y : RayVert P} (p : Quiver.Path x a) (v : Quiver.Path a b)
    (q : Quiver.Path b y) : pathFG ((p.comp v).comp q) = pathFG p ≫ pathFG v ≫ pathFG q := by
  rw [pathFG_comp, pathFG_comp, Category.assoc]

omit [IsRayCategory P] in
lemma interStep_val {x y : RayVert P} {v w : Quiver.Path x y} (h : InterStep v w) :
    pathVal v = pathVal w := by
  obtain ⟨a, b, p, v', w', q, rfl, rfl, he, -, -⟩ := h
  rw [pathVal_comp3, pathVal_comp3, he]

omit [IsRayCategory P] in
lemma interlaced_val {x y : RayVert P} {v w : Quiver.Path x y} (h : Interlaced v w) :
    pathVal v = pathVal w := by
  induction h with
  | rel _ _ h => exact interStep_val h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

/-- An interlacing step between paths of value `μ` holds modulo `homotopyExcept μ`. -/
lemma interStep_sound {x y : RayVert P} (μ : x.out ⟶ y.out) {v w : Quiver.Path x y}
    (hv : pathVal v = μ) (h : InterStep v w) :
    (CategoryTheory.Quotient.functor (homotopyExcept μ)).map (pathFG v) =
      (CategoryTheory.Quotient.functor (homotopyExcept μ)).map (pathFG w) := by
  obtain ⟨a, b, p, v', w', q, rfl, rfl, he, h0, hlen⟩ := h
  rw [pathFG_comp3, pathFG_comp3, Functor.map_comp, Functor.map_comp, Functor.map_comp,
    Functor.map_comp]
  congr 2
  refine CategoryTheory.Quotient.sound _ (homotopyExcept.path v' w' he h0 ?_)
  rintro ⟨hx, hy, hμ⟩
  -- `μ = p μ q` with `p` or `q` a nonempty closed path, impossible
  change a = x at hx
  change b = y at hy
  subst hx hy
  replace hμ : pathVal v' = μ := by
    rw [hμ]
    change 𝟙 a.out ≫ μ ≫ 𝟙 b.out = μ
    rw [Category.id_comp, Category.comp_id]
  rw [pathVal_comp3, hμ] at hv
  have hμ0 : μ ≠ 0 := hμ ▸ h0
  obtain ⟨h1, h2⟩ := IsRayCategory.eq_id_of_two_sided μ hμ0 (pathVal p) (pathVal q) hv.symm
  rcases hlen with hl | hl
  · exact pathVal_ne_id_of_length p hl h1
  · exact pathVal_ne_id_of_length q hl h2

lemma interlaced_sound {x y : RayVert P} (μ : x.out ⟶ y.out) {v w : Quiver.Path x y}
    (h : Interlaced v w) (hv : pathVal v = μ) :
    (CategoryTheory.Quotient.functor (homotopyExcept μ)).map (pathFG v) =
      (CategoryTheory.Quotient.functor (homotopyExcept μ)).map (pathFG w) := by
  induction h with
  | rel _ _ h => exact interStep_sound μ hv h
  | refl => rfl
  | symm v w h ih => exact (ih ((interlaced_val h).trans hv)).symm
  | trans u v w h h' ih ih' => exact (ih hv).trans (ih' ((interlaced_val h).symm.trans hv))

/-- If `μ` occurs in no contour, removing the pairs of value `μ` does not change
the fundamental group: the vertex groups of the two quotients agree. -/
def endEquivExcept {a b : P} (μ : a ⟶ b) (hμ : NotInContour μ)
    (X : Quiver.FreeGroupoid (RayVert P)) :
    End ((CategoryTheory.Quotient.functor (homotopyExcept μ)).obj X) ≃*
      End ((CategoryTheory.Quotient.functor (homotopy (P := P))).obj X) :=
  endEquivOfRel
    (fun f g h ↦ by
      cases h with
      | path p q hpq h0 =>
        by_cases hμp : ∃ (hx : _ = a) (hy : _ = b), pathVal p = eqToHom hx ≫ μ ≫ eqToHom hy.symm
        · obtain ⟨hx, hy, hval⟩ := hμp
          subst hx hy
          have hval' : pathVal p = μ := by
            rw [hval]
            change 𝟙 _ ≫ μ ≫ 𝟙 _ = μ
            rw [Category.id_comp, Category.comp_id]
          exact interlaced_sound μ (hμ p q hval' (hpq ▸ hval')) hval'
        · exact CategoryTheory.Quotient.sound _ (homotopyExcept.path p q hpq h0 hμp))
    (fun f g h ↦ by
      cases h with
      | path p q hpq h0 _ => exact CategoryTheory.Quotient.sound _ (homotopy.path p q hpq h0))
    X

end RayCat

end LargeIndecomposable
