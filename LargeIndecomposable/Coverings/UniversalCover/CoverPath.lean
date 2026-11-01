module

public import LargeIndecomposable.FundamentalGroups.Basic.CoverCocycle
public import LargeIndecomposable.Coverings.UniversalCover.CoverChain

/-!
# Paths in the universal cover

A path of the universal cover projects to a path of `P` with the same length and value
(`Cover.projPath`, `Cover.pathVal_projPath`); a path of `P` lifts to a path of the cover from any
point over its start (`Cover.exists_liftPath`), and the lift ends at the point given by the
homotopy class of the path.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

namespace Cover

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] {x₀ : P}

/-- The homotopy class of a path of `P`. -/
abbrev pcls {x y : RayVert P} (p : Quiver.Path x y) :
    (CategoryTheory.Quotient.functor (homotopy (P := P))).obj ((Quiver.FreeGroupoid.of _).obj x) ⟶
      (CategoryTheory.Quotient.functor homotopy).obj ((Quiver.FreeGroupoid.of _).obj y) :=
  (CategoryTheory.Quotient.functor homotopy).map (pathFG p)

/-- The projection of an arrow of the cover. -/
def projArr {a b : RayVert (Cover x₀)} (e : a ⟶ b) :
    RayVert.mk a.out.y ⟶ RayVert.mk b.out.y :=
  ⟨val e.1, isIrreducible_val e.2⟩

/-- The projection of quivers. -/
def projQ : RayVert (Cover x₀) ⥤q RayVert P where
  obj a := RayVert.mk a.out.y
  map e := projArr e

/-- The projection of a path. -/
abbrev projPath {a b : RayVert (Cover x₀)} (p : Quiver.Path a b) :
    Quiver.Path (RayVert.mk a.out.y) (RayVert.mk b.out.y) :=
  (projQ (x₀ := x₀)).mapPath p

lemma pathVal_projPath {a : RayVert (Cover x₀)} : ∀ {b : RayVert (Cover x₀)}
    (p : Quiver.Path a b), val (pathVal p) = pathVal (projPath p)
  | _, .nil => rfl
  | _, .cons p e => by
    change val (pathVal p ≫ e.1) = pathVal (projPath p) ≫ val e.1
    rw [val_comp, pathVal_projPath p]

lemma length_projPath {a : RayVert (Cover x₀)} : ∀ {b : RayVert (Cover x₀)}
    (p : Quiver.Path a b), (projPath p).length = p.length
  | _, .nil => rfl
  | _, .cons p e => by
    change ((projPath p).cons (projArr e)).length = _
    rw [Quiver.Path.length_cons, Quiver.Path.length_cons, length_projPath p]

lemma pcls_cons {x y z : RayVert P} (p : Quiver.Path x y) (e : y ⟶ z) :
    pcls (p.cons e) = pcls p ≫ cls e.1 e.2.1 := by
  rw [cls_eq_arr]
  change (CategoryTheory.Quotient.functor homotopy).map (pathFG p ≫ _) = _
  rw [Functor.map_comp]

/-- **Path lifting.** -/
lemma exists_liftPath (a : Cover x₀) : ∀ {y : RayVert P} (p : Quiver.Path (RayVert.mk a.y) y),
    ∃ (b : Cover x₀) (q : Quiver.Path (RayVert.mk a) (RayVert.mk b)),
      b = ⟨y.out, a.u ≫ pcls p⟩ ∧ HEq (projPath q) p
  | _, .nil => ⟨a, .nil, by
      obtain ⟨a₁, a₂⟩ := a
      have h : pcls (Quiver.Path.nil : Quiver.Path (RayVert.mk a₁) (RayVert.mk a₁)) = 𝟙 _ :=
        (CategoryTheory.Quotient.functor _).map_id _
      change _ = (⟨a₁, a₂ ≫ pcls (Quiver.Path.nil : Quiver.Path (RayVert.mk a₁) _)⟩ : Cover x₀)
      rw [h]
      congr 1
      exact (Category.comp_id (obj := FundGroupoid P) a₂).symm, HEq.rfl⟩
  | z, .cons (b := y) p e => by
    obtain ⟨b, q, rfl, hq⟩ := exists_liftPath a p
    refine ⟨_, q.cons (liftArr _ e), ?_, ?_⟩
    · change (⟨z.out, (a.u ≫ pcls p) ≫ cls e.1 e.2.1⟩ : Cover x₀) = _
      rw [pcls_cons, Category.assoc]
    · have h1 : projArr (liftArr (⟨y.out, a.u ≫ pcls p⟩ : Cover x₀) e) = e := Subtype.ext rfl
      change HEq ((projPath q).cons (projArr (liftArr _ e))) (p.cons e)
      rw [h1, eq_of_heq hq]

/-- The end of a path of the cover is given by the class of its projection. -/
lemma u_of_path {a : Cover x₀} : ∀ {b : RayVert (Cover x₀)} (q : Quiver.Path (RayVert.mk a) b),
    b.out.u = a.u ≫ pcls (projPath q)
  | _, .nil => by
    have h : pcls (Quiver.Path.nil : Quiver.Path (RayVert.mk a.y) (RayVert.mk a.y)) = 𝟙 _ :=
      (CategoryTheory.Quotient.functor _).map_id _
    change a.u = a.u ≫ pcls (Quiver.Path.nil : Quiver.Path (RayVert.mk a.y) _)
    rw [h]
    exact (Category.comp_id (obj := FundGroupoid P) a.u).symm
  | b, .cons (b := b') q e => by
    have h1 := u_of_path q
    have h2 := u_eq e.1 e.2.1
    change b.out.u = a.u ≫ pcls ((projPath q).cons (projArr e))
    rw [pcls_cons, h2, h1, Category.assoc]
    rfl

/-- An arrow of the cover is determined by its source and projection. -/
lemma arr_ext {a b b' : Cover x₀} (e : RayVert.mk a ⟶ RayVert.mk b)
    (e' : RayVert.mk a ⟶ RayVert.mk b') (hy : b.y = b'.y) (he : HEq (projArr e) (projArr e')) :
    b = b' ∧ HEq e e' := by
  obtain ⟨b₁, b₂⟩ := b
  obtain ⟨b₁', b₂'⟩ := b'
  change b₁ = b₁' at hy
  subst hy
  have hv : val e.1 = val e'.1 := congrArg Subtype.val (eq_of_heq he)
  have hb : b₂ = b₂' := by
    have h1 : b₂ = a.u ≫ cls (val e.1) (val_ne_zero e.2.1) := u_eq e.1 e.2.1
    have h2 : b₂' = a.u ≫ cls (val e'.1) (val_ne_zero e'.2.1) := u_eq e'.1 e'.2.1
    rw [h1, h2]
    congr 1
    exact cls_congr hv _ _
  subst hb
  exact ⟨rfl, heq_of_eq (Subtype.ext (val_injective hv))⟩

omit [HasZeroMorphisms P] [IsRayCategory P] in
lemma length_eq_of_heq {V : Type*} [Quiver V] {x y y' : V} {p : Quiver.Path x y}
    {q : Quiver.Path x y'} (hy : y = y') (h : HEq p q) : p.length = q.length := by
  subst hy; rw [eq_of_heq h]

/-- **A path of the cover is determined by its start and its projection.** -/
lemma eq_of_projPath {a : Cover x₀} : ∀ {b b' : RayVert (Cover x₀)}
    (q : Quiver.Path (RayVert.mk a) b) (q' : Quiver.Path (RayVert.mk a) b'),
    b.out.y = b'.out.y → HEq (projPath q) (projPath q') → b = b' ∧ HEq q q'
  | _, _, .nil, .nil, _, _ => ⟨rfl, HEq.rfl⟩
  | _, _, .nil, .cons q' e', hy, h => by
    have := length_eq_of_heq (V := RayVert P) hy h
    rw [length_projPath, length_projPath] at this
    simp at this
  | _, _, .cons q e, .nil, hy, h => by
    have := length_eq_of_heq (V := RayVert P) hy h
    rw [length_projPath, length_projPath] at this
    simp at this
  | b, b', .cons (b := c) q e, .cons (b := c') q' e', hy, h => by
    obtain ⟨b₁, b₂⟩ := b
    obtain ⟨b₁', b₂'⟩ := b'
    change b₁ = b₁' at hy
    subst hy
    have h' : (projPath q).cons (projArr e) = (projPath q').cons (projArr e') := eq_of_heq h
    have hc : RayVert.mk c.y = RayVert.mk c'.y := Quiver.Path.obj_eq_of_cons_eq_cons h'
    obtain ⟨rfl, hqq⟩ := eq_of_projPath q q' hc (Quiver.Path.heq_of_cons_eq_cons h')
    obtain rfl := eq_of_heq hqq
    obtain ⟨hb, hee⟩ := arr_ext e e' rfl (Quiver.Path.hom_heq_of_cons_eq_cons h')
    cases hb
    obtain rfl := eq_of_heq hee
    exact ⟨rfl, HEq.rfl⟩

lemma pcls_comp {x y z : RayVert P} (p : Quiver.Path x y) (q : Quiver.Path y z) :
    pcls (p.comp q) = pcls p ≫ pcls q := by
  rw [pcls, pathFG_comp, Functor.map_comp]

lemma pcls_interStep {x y : RayVert P} {v w : Quiver.Path x y} (h : InterStep v w) :
    pcls v = pcls w := by
  obtain ⟨a, b, p, v', w', q, rfl, rfl, hvw, hv0, -⟩ := h
  rw [pcls_comp, pcls_comp, pcls_comp, pcls_comp]
  congr 2
  exact homotopic_of_pathVal_eq v' w' hvw hv0

lemma projPath_comp {a b c : RayVert (Cover x₀)} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    projPath (p.comp q) = (projPath p).comp (projPath q) :=
  Prefunctor.mapPath_comp _ p q

omit [HasZeroMorphisms P] [IsRayCategory P] in
lemma interStep_of_heq {V : Type} [Category.{0} V] [HasZeroMorphisms V] {x y y' : RayVert V}
    (hy : y = y') {s t : Quiver.Path x y} {s' t' : Quiver.Path x y'} (hs : HEq s s')
    (ht : HEq t t') (h : InterStep s t) : InterStep s' t' := by
  subst hy
  rw [← eq_of_heq hs, ← eq_of_heq ht]
  exact h

/-- **Interlacing steps lift to the cover.** -/
lemma interStep_lift {a : Cover x₀} {b : RayVert (Cover x₀)} {s t : Quiver.Path (RayVert.mk a) b}
    (h : InterStep (projPath s) (projPath t)) : InterStep s t := by
  obtain ⟨c, d, p, v', w', q, hs, ht, hvw, hv0, hlen⟩ := h
  obtain ⟨cT, pT, rfl, hpT⟩ := exists_liftPath a p
  obtain ⟨dT, vT, rfl, hvT⟩ := exists_liftPath (⟨c.out, a.u ≫ pcls p⟩ : Cover x₀) v'
  obtain ⟨dT', wT, hd', hwT⟩ := exists_liftPath (⟨c.out, a.u ≫ pcls p⟩ : Cover x₀) w'
  have hvw' : pcls v' = pcls w' := homotopic_of_pathVal_eq v' w' hvw hv0
  rw [← hvw'] at hd'
  subst hd'
  obtain ⟨eT, qT, rfl, hqT⟩ := exists_liftPath
    (⟨d.out, (a.u ≫ pcls p) ≫ pcls v'⟩ : Cover x₀) q
  have hs' := eq_of_projPath ((pT.comp vT).comp qT) s rfl (by
    rw [projPath_comp, projPath_comp, eq_of_heq hpT, eq_of_heq hvT, eq_of_heq hqT, hs])
  have ht' := eq_of_projPath ((pT.comp wT).comp qT) t rfl (by
    rw [projPath_comp, projPath_comp, eq_of_heq hpT, eq_of_heq hwT, eq_of_heq hqT, ht])
  obtain ⟨heb, hs''⟩ := hs'
  obtain ⟨-, ht''⟩ := ht'
  refine interStep_of_heq heb hs'' ht'' ⟨_, _, pT, vT, wT, qT, rfl, rfl, ?_, ?_, ?_⟩
  · apply val_injective
    rw [pathVal_projPath, pathVal_projPath, eq_of_heq hvT, eq_of_heq hwT, hvw]
  · intro h0
    apply hv0
    rw [← eq_of_heq hvT, ← pathVal_projPath, h0]
    rfl
  · rw [← length_projPath pT, ← length_projPath qT, eq_of_heq hpT, eq_of_heq hqT]
    exact hlen

lemma pcls_interlaced {x y : RayVert P} {v w : Quiver.Path x y}
    (h : Relation.EqvGen InterStep v w) : pcls v = pcls w := by
  induction h with
  | rel _ _ h => exact pcls_interStep h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Interlacing lifts to the cover.** -/
lemma interlaced_lift {a : Cover x₀} {b : RayVert (Cover x₀)} {s t : Quiver.Path (RayVert.mk a) b}
    (h : Interlaced (projPath s) (projPath t)) : Interlaced s t := by
  suffices H : ∀ p q : Quiver.Path (RayVert.mk a.y) (RayVert.mk b.out.y),
      Relation.EqvGen InterStep p q → ∀ s t : Quiver.Path (RayVert.mk a) b,
        projPath s = p → projPath t = q → Interlaced s t from H _ _ h s t rfl rfl
  intro p q hpq
  induction hpq with
  | rel p q hstep =>
    intro s t hs ht
    subst hs ht
    exact Relation.EqvGen.rel _ _ (interStep_lift hstep)
  | refl p =>
    intro s t hs ht
    obtain ⟨-, hst⟩ := eq_of_projPath s t rfl (heq_of_eq (hs.trans ht.symm))
    rw [eq_of_heq hst]
    exact Relation.EqvGen.refl _
  | symm p q _ ih =>
    intro s t hs ht
    exact Relation.EqvGen.symm _ _ (ih t s ht hs)
  | trans p r q hpr _ ih₁ ih₂ =>
    intro s t hs ht
    obtain ⟨E, rT, rfl, hrT⟩ := exists_liftPath a r
    have hEb : (RayVert.mk (⟨b.out.y, a.u ≫ pcls r⟩ : Cover x₀) : RayVert (Cover x₀)) = b := by
      have h1 := u_of_path s
      rw [hs, pcls_interlaced hpr] at h1
      obtain ⟨b₁, b₂⟩ := b
      have h1' : b₂ = a.u ≫ pcls r := h1
      change (⟨b₁, a.u ≫ pcls r⟩ : Cover x₀) = ⟨b₁, b₂⟩
      rw [h1']
    have htr : ∀ (E : RayVert (Cover x₀)) (hE : E = b) (rT : Quiver.Path (RayVert.mk a) E),
        HEq (projPath rT) r → ∃ rT' : Quiver.Path (RayVert.mk a) b, projPath rT' = r := by
      intro E' hE rT₀ h₀
      subst hE
      exact ⟨rT₀, eq_of_heq h₀⟩
    obtain ⟨rT', hrT'⟩ := htr _ hEb rT hrT
    exact Relation.EqvGen.trans _ _ _ (ih₁ s rT' hs hrT') (ih₂ rT' t hrT' ht)

end Cover

end LargeIndecomposable.RayCat
