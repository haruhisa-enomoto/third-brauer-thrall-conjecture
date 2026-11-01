module

public import LargeIndecomposable.FundamentalGroups.Basic.Cocycle
public import LargeIndecomposable.Coverings.UniversalCover.PieceKills

/-!
# Cocycles on the universal cover are coboundaries

Let `c` be an integer cocycle on the quiver of the universal cover `Cover x₀`. Walks of `P`
act on pairs `(u, n)` (a walk class from `x₀` and an integer) by lifting each arrow at the
object `⟨_, u⟩` of the cover and adding its weight (`liftF`). Paths with the same nonzero
value lift to paths of the cover with the same nonzero value, so the action factors through
the fundamental groupoid (`coverAct`). The second component of the action of `a.u` on
`(𝟙, 0)` is a potential for `c` (`isCoboundary_cover`): the cover is simply connected in
the cohomological sense.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover

/-- Types and equivalences, as a groupoid. -/
structure EqvGrpd : Type 1 where
  /-- The underlying type. -/
  carrier : Type

instance : Category.{0} EqvGrpd where
  Hom X Y := X.carrier ≃ Y.carrier
  id X := Equiv.refl X.carrier
  comp f g := f.trans g
  id_comp f := Equiv.refl_trans f
  comp_id f := Equiv.trans_refl f
  assoc f g h := Equiv.trans_assoc f g h

instance : Groupoid EqvGrpd where
  inv f := Equiv.symm f
  inv_comp f := Equiv.symm_trans_self f
  comp_inv f := Equiv.self_trans_symm f

/-- A morphism of `EqvGrpd` as an equivalence. -/
def ev {X Y : EqvGrpd} (f : X ⟶ Y) : X.carrier ≃ Y.carrier := f

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] {x₀ : P}

/-- The lift of an arrow of `P` at an object of the cover. -/
def liftArr (a : Cover x₀) {z : RayVert P} (e : RayVert.mk a.y ⟶ z) :
    RayVert.mk a ⟶ RayVert.mk (⟨z.out, a.u ≫ cls e.1 e.2.1⟩ : Cover x₀) :=
  ⟨liftAt a e.1 e.2.1, isIrreducible_liftAt a e.2⟩

lemma cls_eq_arr {x y : RayVert P} (e : x ⟶ y) :
    cls e.1 e.2.1 = (CategoryTheory.Quotient.functor homotopy).map
      ((Quiver.FreeGroupoid.of (RayVert P)).map e) := by
  rw [cls_eq e.1 e.2.1 (Quiver.Path.nil.cons e) (Category.id_comp _)]
  simp [pathFG]

variable (c : ArrowWeight (Cover x₀))

/-- The weight of the lift of `e` at `⟨x, u⟩`. -/
def liftWt {x y : RayVert P} (e : x ⟶ y) (u : vtx x₀ ⟶ vtx x.out) : ℤ :=
  c (liftArr (⟨x.out, u⟩ : Cover x₀) e)

/-- The action of an arrow. -/
def arrAct {x y : RayVert P} (e : x ⟶ y) :
    ((vtx x₀ ⟶ vtx x.out) × ℤ) ≃ ((vtx x₀ ⟶ vtx y.out) × ℤ) where
  toFun p := (p.1 ≫ cls e.1 e.2.1, p.2 + liftWt c e p.1)
  invFun q := (q.1 ≫ inv (cls e.1 e.2.1), q.2 - liftWt c e (q.1 ≫ inv (cls e.1 e.2.1)))
  left_inv p := by
    obtain ⟨u, n⟩ := p
    have h : (u ≫ cls e.1 e.2.1) ≫ inv (cls e.1 e.2.1) = u := by simp
    simp only [h, add_sub_cancel_right]
  right_inv q := by
    obtain ⟨v, m⟩ := q
    simp

/-- The action of arrows as a prefunctor. -/
def liftPre : RayVert P ⥤q EqvGrpd where
  obj x := ⟨(vtx x₀ ⟶ vtx x.out) × ℤ⟩
  map e := arrAct c e

/-- The action of walks. -/
def liftF : Quiver.FreeGroupoid (RayVert P) ⥤ EqvGrpd := Quiver.FreeGroupoid.lift (liftPre c)

lemma liftF_of {x y : RayVert P} (e : x ⟶ y) :
    (liftF c).map ((Quiver.FreeGroupoid.of (RayVert P)).map e) = arrAct c e := by
  rfl

lemma liftF_comp_apply {X Y Z : Quiver.FreeGroupoid (RayVert P)} (f : X ⟶ Y) (g : Y ⟶ Z)
    (p : ((liftF c).obj X).carrier) :
    ev ((liftF c).map (f ≫ g)) p = ev ((liftF c).map g) (ev ((liftF c).map f) p) := by
  rw [Functor.map_comp]
  rfl

/-- Lifting a path of `P`. -/
lemma liftF_path {x : RayVert P} : ∀ {y : RayVert P} (p : Quiver.Path x y)
    (u : vtx x₀ ⟶ vtx x.out) (n : ℤ),
    ∃ pt : Quiver.Path (RayVert.mk (⟨x.out, u⟩ : Cover x₀))
        (RayVert.mk (⟨y.out, u ≫ (CategoryTheory.Quotient.functor homotopy).map (pathFG p)⟩ :
          Cover x₀)),
      ev ((liftF c).map (pathFG p)) ((u, n) : (vtx x₀ ⟶ vtx x.out) × ℤ) =
          (u ≫ (CategoryTheory.Quotient.functor homotopy).map (pathFG p), n + pathWeight c pt) ∧
        val (pathVal pt) = pathVal p
  | _, .nil, u, n => by
    have h : u ≫ (CategoryTheory.Quotient.functor homotopy).map
        (pathFG (Quiver.Path.nil : Quiver.Path x x)) = u := by
      simp only [pathFG, CategoryTheory.Functor.map_id]
      exact Category.comp_id u
    rw [h]
    refine ⟨Quiver.Path.nil, ?_, rfl⟩
    simp only [pathFG, pathWeight, add_zero, CategoryTheory.Functor.map_id]
    rfl
  | _, .cons p e, u, n => by
    obtain ⟨pt, h1, h2⟩ := liftF_path p u n
    have h : u ≫ (CategoryTheory.Quotient.functor homotopy).map (pathFG (p.cons e)) =
        (u ≫ (CategoryTheory.Quotient.functor homotopy).map (pathFG p)) ≫ cls e.1 e.2.1 := by
      rw [cls_eq_arr]
      simp [pathFG]
    rw [h]
    refine ⟨pt.cons (liftArr (⟨_, u ≫ (CategoryTheory.Quotient.functor homotopy).map (pathFG p)⟩ :
      Cover x₀) e), ?_, ?_⟩
    · change ev ((liftF c).map (pathFG p ≫ (Quiver.FreeGroupoid.of (RayVert P)).map e))
        ((u, n) : (vtx x₀ ⟶ vtx x.out) × ℤ) = _
      erw [liftF_comp_apply, h1, liftF_of]
      exact Prod.ext rfl (add_assoc _ _ _)
    · change val (pathVal pt ≫ (liftArr _ e).1) = pathVal p ≫ e.1
      rw [val_comp, h2]
      rfl

include c in
lemma liftF_sound (hc : IsCocycle c) {X Y : Quiver.FreeGroupoid (RayVert P)} (f g : X ⟶ Y)
    (h : homotopy f g) : (liftF c).map f = (liftF c).map g := by
  cases h with
  | path p q hpq h0 =>
    refine Equiv.ext fun (un : (vtx x₀ ⟶ vtx _) × ℤ) ↦ ?_
    obtain ⟨u, n⟩ := un
    have hQ := homotopic_of_pathVal_eq p q hpq h0
    obtain ⟨pt, h1, h2⟩ := liftF_path c p u n
    have hq := liftF_path c q u n
    rw [← hQ] at hq
    obtain ⟨qt, h1', h2'⟩ := hq
    have hv : pathVal pt = pathVal qt := val_injective (h2.trans (hpq.trans h2'.symm))
    have hv0 : pathVal pt ≠ 0 := fun h ↦ h0 (by rw [← h2, h]; rfl)
    change ev ((liftF c).map (pathFG p)) ((u, n) : (vtx x₀ ⟶ vtx _) × ℤ) =
      ev ((liftF c).map (pathFG q)) ((u, n) : (vtx x₀ ⟶ vtx _) × ℤ)
    erw [h1, h1', hc pt qt hv hv0]

/-- The action of the fundamental groupoid. -/
def coverAct (hc : IsCocycle c) : FundGroupoid P ⥤ EqvGrpd :=
  CategoryTheory.Quotient.lift homotopy (liftF c) fun _ _ f g h ↦ liftF_sound c hc f g h

lemma liftF_fst {X Y : Quiver.FreeGroupoid (RayVert P)} (w : X ⟶ Y) :
    ∀ p : ((liftF c).obj X).carrier,
      (ev ((liftF c).map w) p).1 = p.1 ≫ (CategoryTheory.Quotient.functor homotopy).map w := by
  induction w using Quiver.FreeGroupoid.hom_rec with
  | of_map e =>
    intro p
    exact congrArg (p.1 ≫ ·) (cls_eq_arr e)
  | @inv_of_map x y e =>
    intro p
    have h1 : (liftF c).map (inv ((Quiver.FreeGroupoid.of (RayVert P)).map e)) =
        Groupoid.inv (arrAct c e) := by
      rw [CategoryTheory.Functor.map_inv]
      exact (Groupoid.inv_eq_inv ((liftF c).map ((Quiver.FreeGroupoid.of (RayVert P)).map e))).symm
    have h2 : (CategoryTheory.Quotient.functor homotopy).map
        (inv ((Quiver.FreeGroupoid.of (RayVert P)).map e)) = inv (cls e.1 e.2.1) := by
      rw [CategoryTheory.Functor.map_inv, cls_eq_arr]
    show (ev ((liftF c).map (inv ((Quiver.FreeGroupoid.of (RayVert P)).map e))) p).1 =
      p.1 ≫ (CategoryTheory.Quotient.functor homotopy).map
        (inv ((Quiver.FreeGroupoid.of (RayVert P)).map e))
    rw [h1]
    exact (rfl : (ev (Groupoid.inv (arrAct c e)) p).1 = p.1 ≫ inv (cls e.1 e.2.1)).trans
      (congrArg (p.1 ≫ ·) h2).symm
  | id x =>
    intro p
    simp only [CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  | comp f g hf hg =>
    intro p
    rw [liftF_comp_apply, hg, hf]
    exact (Category.assoc _ _ _).trans
      (congrArg (p.1 ≫ ·) ((CategoryTheory.Quotient.functor homotopy).map_comp f g).symm)

variable (hc : IsCocycle c)

lemma coverAct_map {X Y : Quiver.FreeGroupoid (RayVert P)} (w : X ⟶ Y) :
    (coverAct c hc).map ((CategoryTheory.Quotient.functor homotopy).map w) = (liftF c).map w :=
  CategoryTheory.Quotient.lift_map_functor_map _ _ _ w

lemma coverAct_fst {x y : P} (u : vtx x ⟶ vtx y) (p : ((coverAct c hc).obj (vtx x)).carrier) :
    (ev ((coverAct c hc).map u) p).1 = p.1 ≫ u := by
  obtain ⟨w, rfl⟩ := (CategoryTheory.Quotient.functor homotopy).map_surjective u
  rw [coverAct_map]
  exact liftF_fst c w p

/-- The potential: the weight of the lift of a walk class. -/
def coverPot (a : Cover x₀) : ℤ :=
  (ev ((coverAct c hc).map a.u) ((𝟙 (vtx x₀), 0) : (vtx x₀ ⟶ vtx x₀) × ℤ)).2

lemma coverPot_step {xA y : P} (uA : vtx x₀ ⟶ vtx xA) (g : xA ⟶ y) (hirr : IsIrreducible g) :
    ∀ (v : vtx x₀ ⟶ vtx y) (_ : v = uA ≫ cls g hirr.1)
      (f' : RayVert.mk (⟨xA, uA⟩ : Cover x₀) ⟶ RayVert.mk (⟨y, v⟩ : Cover x₀)), val f'.1 = g →
      c f' = coverPot c hc ⟨y, v⟩ - coverPot c hc ⟨xA, uA⟩ := by
  intro v hv
  subst hv
  intro f' hf'
  let e : RayVert.mk xA ⟶ RayVert.mk y := ⟨g, hirr⟩
  have hfe : f' = liftArr (⟨xA, uA⟩ : Cover x₀) e :=
    Subtype.ext (val_injective (hf'.trans (val_liftAt (⟨xA, uA⟩ : Cover x₀) g hirr.1).symm))
  have hce : c f' = liftWt c e uA := by rw [hfe]; rfl
  rw [hce]
  unfold coverPot
  rw [CategoryTheory.Functor.map_comp]
  change _ = (ev ((coverAct c hc).map (cls e.1 e.2.1))
    (ev ((coverAct c hc).map uA) ((𝟙 (vtx x₀), 0) : (vtx x₀ ⟶ vtx x₀) × ℤ))).2 - _
  rw [cls_eq_arr, coverAct_map, liftF_of]
  have hq' : liftWt c e (ev ((coverAct c hc).map uA)
      ((𝟙 (vtx x₀), 0) : (vtx x₀ ⟶ vtx x₀) × ℤ)).1 = liftWt c e uA := by
    exact congrArg (liftWt c e)
      ((coverAct_fst c hc uA ((𝟙 (vtx x₀), 0) : (vtx x₀ ⟶ vtx x₀) × ℤ)).trans (Category.id_comp uA))
  change _ = ((ev ((coverAct c hc).map uA) ((𝟙 (vtx x₀), 0) : (vtx x₀ ⟶ vtx x₀) × ℤ)).2 +
    liftWt c e (ev ((coverAct c hc).map uA) ((𝟙 (vtx x₀), 0) : (vtx x₀ ⟶ vtx x₀) × ℤ)).1) -
    (ev ((coverAct c hc).map uA) ((𝟙 (vtx x₀), 0) : (vtx x₀ ⟶ vtx x₀) × ℤ)).2
  rw [hq']
  ring

include hc in
/-- **Every cocycle on the universal cover is a coboundary.** -/
theorem isCoboundary_cover : IsCoboundary c := by
  refine ⟨coverPot c hc, fun {A B} et ↦ ?_⟩
  rcases A with ⟨xA, uA⟩
  rcases B with ⟨y, v⟩
  obtain ⟨f, hf⟩ := et
  rcases f with _ | g
  · exact absurd rfl hf.1
  obtain ⟨hg0, hv⟩ := g.2
  exact coverPot_step c hc uA g.1 (isIrreducible_val hf) v hv ⟨some g, hf⟩ rfl

end LargeIndecomposable.RayCat
