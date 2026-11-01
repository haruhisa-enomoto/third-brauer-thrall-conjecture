module

public import LargeIndecomposable.Coverings.UniversalCover.GCoverFund
public import LargeIndecomposable.FundamentalGroups.Fischbacher.Lemma42
public import LargeIndecomposable.Coverings.UniversalCover.CoverChain

/-!
# The universal cover of `P` inside that of a Galois cover

The projection of the Galois cover induces `piBar : FG(GCover V) ⥤ FG(P)`. Lifting walk classes
from the base point `(x₀, 1)` (the action `gAct`) gives a map `coverMap` from the universal cover
of `P` to that of `GCover V`, with left inverse `coverProj` (`coverProj_map`), sending arrows to
arrows (`exists_path_map`). Hence cycle-freeness and interval-finiteness pass from the universal
cover of the Galois cover to that of `P` (`cycleFree_of_gcover`, `intervalFinite_of_gcover`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]
  {H : Type} [Group H] {V : Voltage P H}

/-- Arrows of the Galois cover give classes downstairs. -/
def prePi : RayVert (GCover V) ⥤q FundGroupoid P where
  obj a := vtx a.out.y
  map e := cls (GCover.val e.1) (GCover.val_ne_zero e.2.1)

/-- The projection on walks. -/
def piFG : Quiver.FreeGroupoid (RayVert (GCover V)) ⥤ FundGroupoid P :=
  Quiver.FreeGroupoid.lift prePi

lemma piFG_of {a b : RayVert (GCover V)} (e : a ⟶ b) :
    piFG.map ((Quiver.FreeGroupoid.of (RayVert (GCover V))).map e) = prePi.map e := by
  have := Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec (prePi (V := V))) e
  exact (Quiver.homOfEq_rfl _).symm.trans this

lemma piFG_path {a : RayVert (GCover V)} : ∀ {b : RayVert (GCover V)} (pt : Quiver.Path a b)
    (h0 : pathVal pt ≠ 0),
    piFG.map (pathFG pt) = cls (GCover.val (pathVal pt)) (GCover.val_ne_zero h0)
  | _, .nil, _ => by
    change piFG.map (𝟙 _) = _
    rw [CategoryTheory.Functor.map_id]
    exact (cls_id _).symm
  | _, .cons pt e, h0 => by
    have h1 : pathVal pt ≠ 0 := fun h ↦ h0 (by change pathVal pt ≫ e.1 = 0; rw [h, zero_comp])
    change piFG.map (pathFG pt ≫ (Quiver.FreeGroupoid.of _).map e) = _
    rw [CategoryTheory.Functor.map_comp, piFG_path pt h1, piFG_of]
    have hv : GCover.val (pathVal pt ≫ e.1) = GCover.val (pathVal pt) ≫ GCover.val e.1 :=
      GCover.val_comp _ _
    change _ = cls (GCover.val (pathVal pt ≫ e.1)) _
    rw [cls_congr hv (GCover.val_ne_zero h0) (hv ▸ GCover.val_ne_zero h0), cls_comp]
    rfl

/-- The projection on walk classes. -/
def piBar : FundGroupoid (GCover V) ⥤ FundGroupoid P :=
  CategoryTheory.Quotient.lift homotopy piFG fun _ _ _ _ h ↦ by
    cases h with
    | path p q hpq h0 =>
      rw [piFG_path p h0, piFG_path q (hpq ▸ h0)]
      exact cls_congr (congrArg GCover.val hpq) _ _

lemma piBar_map {X Y : Quiver.FreeGroupoid (RayVert (GCover V))} (w : X ⟶ Y) :
    piBar.map ((CategoryTheory.Quotient.functor homotopy).map w) = piFG.map w :=
  CategoryTheory.Quotient.lift_map_functor_map _ _ _ w

variable (a₀ : GCover V)

/-- The class downstairs of a fibre element. -/
def fibCls {x : RayVert P} (r : Fib a₀ x) : vtx a₀.y ⟶ vtx x.out := piBar.map r.2

lemma fibCls_arr {x y : RayVert P} (e : x ⟶ y) (q : Fib a₀ x) :
    fibCls a₀ (arrActG a₀ e q) = fibCls a₀ q ≫ cls e.1 e.2.1 := by
  change piBar.map (q.2 ≫ clsA (liftArrG (⟨x.out, q.1⟩ : GCover V) e)) = _
  rw [CategoryTheory.Functor.map_comp, piBar_map, piFG_of]
  rfl

lemma fibCls_act {X Y : Quiver.FreeGroupoid (RayVert P)} (w : X ⟶ Y) :
    ∀ r : ((liftFG a₀).obj X).carrier,
      fibCls a₀ (x := Y.as) (ev ((liftFG a₀).map w) r) =
        fibCls a₀ (x := X.as) r ≫ (CategoryTheory.Quotient.functor homotopy).map w := by
  induction w using Quiver.FreeGroupoid.hom_rec with
  | of_map e =>
    intro r
    exact (fibCls_arr a₀ e r).trans (congrArg (fibCls a₀ r ≫ ·) (cls_eq_arr e))
  | @inv_of_map x y e =>
    intro r
    have h1 : (liftFG a₀).map (inv ((Quiver.FreeGroupoid.of (RayVert P)).map e)) =
        Groupoid.inv (arrActG a₀ e) := by
      rw [CategoryTheory.Functor.map_inv]
      exact (Groupoid.inv_eq_inv ((liftFG a₀).map ((Quiver.FreeGroupoid.of (RayVert P)).map e))).symm
    have h2 : (CategoryTheory.Quotient.functor homotopy).map
        (inv ((Quiver.FreeGroupoid.of (RayVert P)).map e)) = inv (cls e.1 e.2.1) := by
      rw [CategoryTheory.Functor.map_inv, cls_eq_arr]
    show fibCls a₀ (ev ((liftFG a₀).map (inv ((Quiver.FreeGroupoid.of (RayVert P)).map e))) r) =
      fibCls a₀ r ≫ (CategoryTheory.Quotient.functor homotopy).map
        (inv ((Quiver.FreeGroupoid.of (RayVert P)).map e))
    rw [h1]
    refine Eq.trans ?_ (congrArg (fibCls a₀ r ≫ ·) h2.symm)
    have hq : arrActG a₀ e ((arrActG a₀ e).symm r) = r := Equiv.apply_symm_apply _ _
    have h3 := fibCls_arr a₀ e ((arrActG a₀ e).symm r)
    rw [hq] at h3
    change fibCls a₀ ((arrActG a₀ e).symm r) = _
    exact (IsIso.eq_comp_inv (cls e.1 e.2.1)).2 h3.symm
  | id x =>
    intro r
    simp only [CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  | comp f g hf hg =>
    intro r
    rw [liftFG_comp_apply, hg, hf]
    exact (Category.assoc _ _ _).trans
      (congrArg (fibCls a₀ r ≫ ·) ((CategoryTheory.Quotient.functor homotopy).map_comp f g).symm)

lemma fibCls_gAct {x y : P} (u : vtx x ⟶ vtx y) (r : Fib a₀ (RayVert.mk x)) :
    fibCls a₀ (ev ((gAct a₀).map u) r) = fibCls a₀ r ≫ u := by
  obtain ⟨w, rfl⟩ := (CategoryTheory.Quotient.functor homotopy).map_surjective u
  rw [gAct_map]
  exact fibCls_act a₀ w r

variable {x₀ : P}

/-- The universal cover of `P` maps to that of the Galois cover. -/
def coverMap (c : Cover x₀) : Cover (⟨x₀, 1⟩ : GCover V) :=
  ⟨⟨c.y, (ev ((gAct (⟨x₀, 1⟩ : GCover V)).map c.u) (⟨1, 𝟙 _⟩ : Fib _ (RayVert.mk x₀))).1⟩,
    (ev ((gAct (⟨x₀, 1⟩ : GCover V)).map c.u) (⟨1, 𝟙 _⟩ : Fib _ (RayVert.mk x₀))).2⟩

/-- The projection back. -/
def coverProj (d : Cover (⟨x₀, 1⟩ : GCover V)) : Cover x₀ := ⟨d.y.y, piBar.map d.u⟩

lemma coverProj_map (c : Cover x₀) : coverProj (coverMap (V := V) c) = c := by
  obtain ⟨y, u⟩ := c
  change (⟨y, fibCls _ (ev ((gAct (⟨x₀, 1⟩ : GCover V)).map u)
    (⟨1, 𝟙 _⟩ : Fib _ (RayVert.mk x₀)))⟩ : Cover x₀) = ⟨y, u⟩
  rw [fibCls_gAct]
  change (⟨y, piBar.map (𝟙 (vtx (⟨x₀, 1⟩ : GCover V))) ≫ u⟩ : Cover x₀) = ⟨y, u⟩
  rw [CategoryTheory.Functor.map_id]
  erw [Category.id_comp]

lemma coverMap_injective : Function.Injective (coverMap (V := V) (x₀ := x₀)) := fun c c' h ↦ by
  rw [← coverProj_map (V := V) c, ← coverProj_map (V := V) c', h]

/-- An arrow of the universal cover of `P` gives one between the images. -/
lemma exists_arr_map {c d : Cover x₀} (e : RayVert.mk c ⟶ RayVert.mk d) :
    Nonempty (RayVert.mk (coverMap (V := V) c) ⟶ RayVert.mk (coverMap (V := V) d)) := by
  obtain ⟨f, hf⟩ := e
  have hfv := Cover.isIrreducible_val hf
  have hu := u_eq f hf.1
  let ε : RayVert.mk c.y ⟶ RayVert.mk d.y := ⟨Cover.val f, hfv⟩
  obtain ⟨g, hg⟩ : ∃ g, g = liftArrG (⟨c.y, (coverMap (V := V) c).y.h⟩ : GCover V) ε := ⟨_, rfl⟩
  have hd : coverMap (V := V) d =
      ⟨⟨d.y, (coverMap (V := V) c).y.h * V.w (Cover.val f)⟩,
        (coverMap (V := V) c).u ≫ (CategoryTheory.Quotient.functor homotopy).map
          ((Quiver.FreeGroupoid.of _).map g)⟩ := by
    rw [hg]
    unfold coverMap
    rw [hu, show cls (Cover.val f) (RayCat.val_ne_zero hf.1) = cls ε.1 ε.2.1 from rfl,
      cls_eq_arr ε, CategoryTheory.Functor.map_comp]
    rfl
  have ht : (⟨⟨d.y, (coverMap (V := V) c).y.h * V.w (Cover.val f)⟩,
      (coverMap (V := V) c).u ≫ cls g.1 g.2.1⟩ : Cover (⟨x₀, 1⟩ : GCover V)) =
      ⟨⟨d.y, (coverMap (V := V) c).y.h * V.w (Cover.val f)⟩,
        (coverMap (V := V) c).u ≫ (CategoryTheory.Quotient.functor homotopy).map
          ((Quiver.FreeGroupoid.of _).map g)⟩ :=
    congrArg (fun t ↦ (⟨⟨d.y, (coverMap (V := V) c).y.h * V.w (Cover.val f)⟩,
      (coverMap (V := V) c).u ≫ t⟩ : Cover (⟨x₀, 1⟩ : GCover V))) (cls_eq_arr g)
  rw [hd, ← ht]
  exact ⟨⟨Cover.liftAt (coverMap c) g.1 g.2.1, Cover.isIrreducible_liftAt (coverMap c) g.2⟩⟩

lemma exists_path_map {c : RayVert (Cover x₀)} : ∀ {d : RayVert (Cover x₀)} (p : Quiver.Path c d),
    ∃ q : Quiver.Path (RayVert.mk (coverMap (V := V) c.out)) (RayVert.mk (coverMap (V := V) d.out)),
      q.length = p.length
  | _, .nil => ⟨.nil, rfl⟩
  | _, .cons p e => by
    obtain ⟨q, hq⟩ := exists_path_map p
    obtain ⟨e'⟩ := exists_arr_map (V := V) e
    exact ⟨q.cons e', by simp [hq]⟩

lemma reaches_map {c d : Cover x₀} (h : Reaches c d) :
    Reaches (coverMap (V := V) c) (coverMap (V := V) d) := by
  obtain ⟨p⟩ := h
  obtain ⟨q, -⟩ := exists_path_map (V := V) p
  exact ⟨q⟩

/-- **Cycle-freeness descends from the Galois cover.** -/
theorem cycleFree_of_gcover
    (h : ∀ (a : RayVert (Cover (⟨x₀, 1⟩ : GCover V))) (p : Quiver.Path a a), p.length = 0) :
    ∀ (c : RayVert (Cover x₀)) (p : Quiver.Path c c), p.length = 0 := fun _ p ↦ by
  obtain ⟨q, hq⟩ := exists_path_map (V := V) p
  rw [← hq]
  exact h _ q

/-- **Interval-finiteness descends from the Galois cover.** -/
theorem intervalFinite_of_gcover
    (h : ∀ a b : Cover (⟨x₀, 1⟩ : GCover V), (interval a b).Finite) :
    ∀ a b : Cover x₀, (interval a b).Finite := fun a b ↦
  ((h (coverMap a) (coverMap b)).preimage coverMap_injective.injOn).subset
    fun _ hz ↦ ⟨reaches_map hz.1, reaches_map hz.2⟩

end LargeIndecomposable.RayCat
