module

public import LargeIndecomposable.Coverings.UniversalCover.GCover
public import LargeIndecomposable.FundamentalGroups.Basic.CoverCocycle

/-!
# Loops in Galois covers

Walks of `P` act on pairs `(h, γ)` (a sheet `h` and a walk class `γ` of the Galois cover from a
base point to `(x, h)`) by lifting each arrow (`liftFG`). Paths of `P` with the same nonzero value
lift to paths of the cover with the same nonzero value, so the action factors through the
fundamental groupoid of `P` (`gAct`). Consequently a nonzero endomorphism of the cover whose image
in `P` has trivial homotopy class has trivial class itself (`cls_eq_id_of_proj`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits GCover

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]
  {H : Type} [Group H] {V : Voltage P H}

/-- The lift of an arrow of `P` at a point of the Galois cover. -/
def liftArrG (a : GCover V) {z : RayVert P} (e : RayVert.mk a.y ⟶ z) :
    RayVert.mk a ⟶ RayVert.mk (⟨z.out, a.h * V.w e.1⟩ : GCover V) :=
  ⟨liftAt a e.1 e.2.1, isIrreducible_liftAt a e.2⟩

/-- The class of an arrow of a ray category. -/
abbrev clsA {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] {x y : RayVert Q} (e : x ⟶ y) :
    (CategoryTheory.Quotient.mk (r := homotopy (P := Q)) ((Quiver.FreeGroupoid.of (RayVert Q)).obj x)) ⟶
      CategoryTheory.Quotient.mk ((Quiver.FreeGroupoid.of (RayVert Q)).obj y) :=
  (CategoryTheory.Quotient.functor homotopy).map ((Quiver.FreeGroupoid.of (RayVert Q)).map e)

variable (a₀ : GCover V)

/-- The fibre data over `x`: a sheet and a walk class of the cover from `a₀`. -/
abbrev Fib (x : RayVert P) : Type := Σ h : H, (vtx a₀ ⟶ vtx (⟨x.out, h⟩ : GCover V))

/-- The forward action of an arrow. -/
def arrFun {x y : RayVert P} (e : x ⟶ y) (p : Fib a₀ x) : Fib a₀ y :=
  ⟨p.1 * V.w e.1, p.2 ≫ clsA (liftArrG (⟨x.out, p.1⟩ : GCover V) e)⟩

lemma arrFun_bijective {x y : RayVert P} (e : x ⟶ y) : Function.Bijective (arrFun a₀ e) := by
  constructor
  · rintro ⟨k, γ⟩ ⟨k', γ'⟩ h
    unfold arrFun at h
    obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 h
    obtain rfl : k = k' := mul_right_cancel h1
    obtain rfl : γ = γ' := (cancel_mono _).1 (eq_of_heq h2)
    rfl
  · rintro ⟨k', δ⟩
    obtain ⟨k, rfl⟩ : ∃ k, k * V.w e.1 = k' := ⟨k' * (V.w e.1)⁻¹, by group⟩
    refine ⟨⟨k, δ ≫ inv (clsA (liftArrG (⟨x.out, k⟩ : GCover V) e))⟩, ?_⟩
    unfold arrFun
    simp

/-- The action of an arrow. -/
def arrActG {x y : RayVert P} (e : x ⟶ y) : Fib a₀ x ≃ Fib a₀ y :=
  Equiv.ofBijective _ (arrFun_bijective a₀ e)

/-- The action of arrows as a prefunctor. -/
def liftPreG : RayVert P ⥤q EqvGrpd where
  obj x := ⟨Fib a₀ x⟩
  map e := arrActG a₀ e

/-- The action of walks. -/
def liftFG : Quiver.FreeGroupoid (RayVert P) ⥤ EqvGrpd := Quiver.FreeGroupoid.lift (liftPreG a₀)

lemma liftFG_of {x y : RayVert P} (e : x ⟶ y) :
    (liftFG a₀).map ((Quiver.FreeGroupoid.of (RayVert P)).map e) = arrActG a₀ e := rfl

lemma liftFG_comp_apply {X Y Z : Quiver.FreeGroupoid (RayVert P)} (f : X ⟶ Y) (g : Y ⟶ Z)
    (p : ((liftFG a₀).obj X).carrier) :
    ev ((liftFG a₀).map (f ≫ g)) p = ev ((liftFG a₀).map g) (ev ((liftFG a₀).map f) p) := by
  rw [Functor.map_comp]
  rfl

/-- Lifting a path of `P` to the Galois cover. -/
lemma liftFG_path {x : RayVert P} : ∀ {y : RayVert P} (p : Quiver.Path x y) (k : H)
    (γ : vtx a₀ ⟶ vtx (⟨x.out, k⟩ : GCover V)),
    ∃ (k' : H) (pt : Quiver.Path (RayVert.mk (⟨x.out, k⟩ : GCover V))
        (RayVert.mk (⟨y.out, k'⟩ : GCover V))),
      ev ((liftFG a₀).map (pathFG p)) (⟨k, γ⟩ : Fib a₀ x) =
          (⟨k', γ ≫ (CategoryTheory.Quotient.functor homotopy).map (pathFG pt)⟩ : Fib a₀ y) ∧
        val (pathVal pt) = pathVal p
  | _, .nil, k, γ => by
    refine ⟨k, Quiver.Path.nil, ?_, rfl⟩
    change ev (𝟙 _) _ = (⟨k, γ ≫ (CategoryTheory.Quotient.functor homotopy).map (𝟙 _)⟩ :
      Fib a₀ x)
    rw [CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
    rfl
  | _, .cons p e, k, γ => by
    obtain ⟨k₁, pt, h1, h2⟩ := liftFG_path p k γ
    refine ⟨k₁ * V.w e.1, pt.cons (liftArrG (⟨_, k₁⟩ : GCover V) e), ?_, ?_⟩
    · change ev ((liftFG a₀).map (pathFG p ≫ (Quiver.FreeGroupoid.of (RayVert P)).map e)) _ = _
      erw [liftFG_comp_apply, h1, liftFG_of]
      change arrFun a₀ e _ = _
      unfold arrFun
      simp only [pathFG, CategoryTheory.Functor.map_comp, Category.assoc]
    · change val (pathVal pt ≫ (liftArrG _ e).1) = pathVal p ≫ e.1
      rw [val_comp, h2]
      rfl

lemma liftFG_sound {X Y : Quiver.FreeGroupoid (RayVert P)} (f g : X ⟶ Y)
    (h : homotopy f g) : (liftFG a₀).map f = (liftFG a₀).map g := by
  cases h with
  | path p q hpq h0 =>
    refine Equiv.ext fun (kγ : Fib a₀ _) ↦ ?_
    obtain ⟨k, γ⟩ := kγ
    obtain ⟨k₁, pt, h1, h2⟩ := liftFG_path a₀ p k γ
    obtain ⟨k₂, qt, h1', h2'⟩ := liftFG_path a₀ q k γ
    have hp0 : pathVal pt ≠ 0 := fun h ↦ h0 (by rw [← h2, h]; rfl)
    have hq0 : pathVal qt ≠ 0 := fun h ↦ h0 (by rw [hpq, ← h2', h]; rfl)
    have e1 := h_eq (pathVal pt) hp0
    have e2 := h_eq (pathVal qt) hq0
    change k₁ = k * V.w (val (pathVal pt)) at e1
    change k₂ = k * V.w (val (pathVal qt)) at e2
    rw [h2] at e1
    rw [h2', ← hpq] at e2
    obtain rfl : k₁ = k₂ := e1.trans e2.symm
    have hv : pathVal pt = pathVal qt := val_injective (h2.trans (hpq.trans h2'.symm))
    refine h1.trans (Eq.trans ?_ h1'.symm)
    rw [homotopic_of_pathVal_eq pt qt hv hp0]

/-- The action of the fundamental groupoid of `P` on the fibres. -/
def gAct : FundGroupoid P ⥤ EqvGrpd :=
  CategoryTheory.Quotient.lift homotopy (liftFG a₀) fun _ _ f g h ↦ liftFG_sound a₀ f g h

lemma gAct_map {X Y : Quiver.FreeGroupoid (RayVert P)} (w : X ⟶ Y) :
    (gAct a₀).map ((CategoryTheory.Quotient.functor homotopy).map w) = (liftFG a₀).map w :=
  CategoryTheory.Quotient.lift_map_functor_map _ _ _ w

/-- **Loops of trivial class downstairs have trivial class in the Galois cover.** -/
theorem cls_eq_id_of_proj {a : GCover V} (e : a ⟶ a) (he : e ≠ 0)
    (hP : cls (val e) (val_ne_zero he) = 𝟙 _) : cls e he = 𝟙 _ := by
  obtain ⟨p, hp⟩ := exists_path (val e) (val_ne_zero he)
  obtain ⟨k₁, pt, h1, h2⟩ := liftFG_path a p a.h (𝟙 _)
  have hc : (CategoryTheory.Quotient.functor homotopy).map (pathFG p) = 𝟙 _ :=
    (cls_eq _ _ p hp).symm.trans hP
  have h3 : ev ((liftFG a).map (pathFG p)) (⟨a.h, 𝟙 _⟩ : Fib a _) = ⟨a.h, 𝟙 _⟩ := by
    rw [← gAct_map, hc, CategoryTheory.Functor.map_id]
    rfl
  rw [h1] at h3
  obtain ⟨h4, h5⟩ := Sigma.mk.inj_iff.1 h3
  subst h4
  have h6 := eq_of_heq h5
  rw [Category.id_comp] at h6
  have hpe : pathVal pt = e := val_injective (h2.trans hp)
  rw [cls_eq e he pt hpe, h6]

end LargeIndecomposable.RayCat
