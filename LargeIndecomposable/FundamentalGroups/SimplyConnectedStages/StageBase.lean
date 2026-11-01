module

public import LargeIndecomposable.FundamentalGroups.SimplyConnectedStages.StageLimit

/-!
# The base stage

The stage `Y_univ` kills the lifts of the `αᵢ` at all points. Its arrows are the lifts of the
arrows of `P' = P/⟨αᵢ⟩`, and `Ψ : FG(P) ⥤ FG(P')` (Lemma 2.2) maps it injectively into the
universal cover of `P'` at `x₀`, arrows to arrows (`exists_arr_base`). So a good cover of `P'`
makes `Y_univ` cycle-free and interval-finite. Its simple connectivity comes from the walk-lifting
action of `FG(P')` on the stage (`liftActQ`), as for the universal cover (`sc_univ`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits LargeIndecomposable

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [LargeIndecomposable.IsFiniteRayCategory0 P]
  [Finite P] {x₀ : P} {ι : Type} {b : P} {d : ι → P} {α : ∀ i, b ⟶ d i}
  (hα : ∀ i, ¬IsIso (α i))

attribute [local instance] isRayCategory_of_finiteRayCategory

namespace Stage

variable (D : RedData α) (hE : D.EssHyp (hα := hα)) [IsRayCategory (ArrowQuot α)]

include hE in
lemma phiBar_psiBar_map {x y : P} (u : vtx x ⟶ vtx y) :
    (phiBar α hα).map ((D.psiBar hE).map u) = u := by
  have h := Functor.congr_hom (D.psiBar_phiBar hE) u
  rw [Functor.comp_map, Functor.id_map] at h
  rw [h]
  exact (Category.id_comp _).trans (Category.comp_id _)

lemma psiBar_cls {x y : RayVert P} (ε : x ⟶ y) (h : ¬(arrowIdeal α).mem ε.1) :
    (D.psiBar hE).map (cls ε.1 ε.2.1) = cls (qArr α hα ε h).1 (qArr α hα ε h).2.1 := by
  rw [cls_eq_arr ε, cls_eq_arr (qArr α hα ε h)]
  change (CategoryTheory.Quotient.lift homotopy (D.psiFG (hα := hα)) _).map
    ((CategoryTheory.Quotient.functor homotopy).map _) = _
  rw [CategoryTheory.Quotient.lift_map_functor_map, RedData.psiFG_map_of_not_mem D ε h]

include hα in
lemma killed_univ_of_mem {x y : RayVert (Cover x₀)} (f : x ⟶ y)
    (hm : (arrowIdeal α).mem (Cover.projArr f).1) : killed (α := α) Set.univ f := by
  obtain ⟨i, hx, -, -⟩ := eq_alpha_of_mem α hα (Cover.projArr f).2 hm
  rcases x with ⟨xy, xu⟩
  change xy = b at hx
  subst hx
  exact ⟨xu, trivial, rfl, hm⟩

include hα in
/-- Arrows of the base stage lie over arrows outside the ideal. -/
lemma not_mem_base {a a' : RayVert (Y (x₀ := x₀) (α := α) Set.univ)} (ε : a ⟶ a') :
    ¬(arrowIdeal α).mem (Cover.val (liftArrQ (isProper Set.univ) ε).1) := fun hm ↦
  liftArrQ_not_mem (isProper Set.univ) ε (Or.inr ⟨_, _, liftArrQ (isProper Set.univ) ε,
    killed_univ_of_mem hα _ hm, 𝟙 _, 𝟙 _, by simp⟩)

/-- The base stage inside the universal cover of `P'`. -/
def coverQ (a : Cover x₀) : Cover (⟨x₀⟩ : ArrowQuot α) := ⟨⟨a.y⟩, (D.psiBar hE).map a.u⟩

lemma coverQ_injective : Function.Injective (coverQ hα D hE (x₀ := x₀)) := by
  rintro ⟨y, u⟩ ⟨y', u'⟩ h
  obtain ⟨h1, h2⟩ := Cover.mk.inj h
  obtain rfl : y = y' := congrArg CategoryTheory.Quotient.as h1
  have h3 := congrArg (phiBar α hα).map (eq_of_heq h2)
  change (phiBar α hα).map ((D.psiBar hE).map u) = (phiBar α hα).map ((D.psiBar hE).map u') at h3
  rw [phiBar_psiBar_map hα D hE, phiBar_psiBar_map hα D hE] at h3
  rw [h3]

/-- An arrow of the base stage gives an arrow of the cover of `P'`. -/
lemma exists_arr_base {a a' : Y (x₀ := x₀) (α := α) Set.univ}
    (ε : RayVert.mk a ⟶ RayVert.mk a') :
    Nonempty (RayVert.mk (coverQ hα D hE a.as) ⟶ RayVert.mk (coverQ hα D hE a'.as)) := by
  have hnm := not_mem_base hα ε
  set f := liftArrQ (isProper Set.univ) ε with hf
  have hfv := Cover.isIrreducible_val f.2
  let ε₀ : RayVert.mk a.as.y ⟶ RayVert.mk a'.as.y := ⟨Cover.val f.1, hfv⟩
  have hu := u_eq f.1 f.2.1
  have hd : coverQ hα D hE a'.as = ⟨⟨a'.as.y⟩, (D.psiBar hE).map a.as.u ≫
      cls (qArr α hα ε₀ hnm).1 (qArr α hα ε₀ hnm).2.1⟩ := by
    unfold coverQ
    rw [hu, CategoryTheory.Functor.map_comp,
      show cls (Cover.val f.1) (RayCat.val_ne_zero f.2.1) = cls ε₀.1 ε₀.2.1 from rfl,
      psiBar_cls hα D hE ε₀ hnm]
    rfl
  rw [hd]
  exact ⟨⟨Cover.liftAt (coverQ hα D hE a.as) (qArr α hα ε₀ hnm).1 (qArr α hα ε₀ hnm).2.1,
    Cover.isIrreducible_liftAt (coverQ hα D hE a.as) (qArr α hα ε₀ hnm).2⟩⟩

lemma exists_path_base {a : RayVert (Y (x₀ := x₀) (α := α) Set.univ)} :
    ∀ {a' : RayVert (Y (x₀ := x₀) (α := α) Set.univ)} (p : Quiver.Path a a'),
      ∃ q : Quiver.Path (RayVert.mk (coverQ hα D hE a.out.as))
        (RayVert.mk (coverQ hα D hE a'.out.as)), q.length = p.length
  | _, .nil => ⟨.nil, rfl⟩
  | _, .cons p e => by
    obtain ⟨q, hq⟩ := exists_path_base p
    obtain ⟨e'⟩ := exists_arr_base hα D hE e
    exact ⟨q.cons e', by simp [hq]⟩

include hα D hE in
lemma cycleFree_base (hG : CoverGood (⟨x₀⟩ : ArrowQuot α)) :
    ∀ (x : RayVert (Y (x₀ := x₀) (α := α) Set.univ)) (p : Quiver.Path x x), p.length = 0 :=
  fun _ p ↦ by
    obtain ⟨q, hq⟩ := exists_path_base hα D hE p
    rw [← hq]
    exact hG.1 _ q

include hα D hE in
lemma intervalFinite_base (hG : CoverGood (⟨x₀⟩ : ArrowQuot α))
    (a a' : Y (x₀ := x₀) (α := α) Set.univ) : (interval a a').Finite := by
  have hinj : Function.Injective
      (fun z : Y (x₀ := x₀) (α := α) Set.univ ↦ coverQ hα D hE z.as) := fun z z' h ↦ by
    have := coverQ_injective hα D hE h
    cases z; cases z'; cases this; rfl
  refine ((hG.2 (coverQ hα D hE a.as) (coverQ hα D hE a'.as)).preimage hinj.injOn).subset ?_
  rintro z ⟨⟨p⟩, ⟨q⟩⟩
  obtain ⟨p', -⟩ := exists_path_base hα D hE p
  obtain ⟨q', -⟩ := exists_path_base hα D hE q
  exact ⟨⟨p'⟩, ⟨q'⟩⟩

lemma phiBar_arr {x y : RayVert (ArrowQuot α)} (e : x ⟶ y) :
    (phiBar α hα).map ((CategoryTheory.Quotient.functor homotopy).map
      ((Quiver.FreeGroupoid.of _).map e)) = cls (inclA hα e).1 (inclA hα e).2.1 := by
  rw [cls_eq_arr (inclA hα e)]
  change (CategoryTheory.Quotient.lift homotopy (inclFG α hα ⋙
    CategoryTheory.Quotient.functor homotopy) _).map
      ((CategoryTheory.Quotient.functor homotopy).map _) = _
  rw [CategoryTheory.Quotient.lift_map_functor_map]
  change (CategoryTheory.Quotient.functor homotopy).map ((inclFG α hα).map _) = _
  erw [lift_map_of]
  rfl

variable (c : ArrowWeight (Y (x₀ := x₀) (α := α) Set.univ))

lemma liftAct_fst {X Y' : Quiver.FreeGroupoid (RayVert (ArrowQuot α))} (w : X ⟶ Y') :
    ∀ p : ((liftAct hα Set.univ c).obj X).carrier,
      (ev ((liftAct hα Set.univ c).map w) p).1 =
        p.1 ≫ (phiBar α hα).map ((CategoryTheory.Quotient.functor homotopy).map w) := by
  induction w using Quiver.FreeGroupoid.hom_rec with
  | of_map e =>
    intro p
    exact congrArg (p.1 ≫ ·) (phiBar_arr hα e).symm
  | @inv_of_map x y e =>
    intro p
    have h1 : (liftAct hα Set.univ c).map (inv ((Quiver.FreeGroupoid.of _).map e)) =
        Groupoid.inv (arrActQ hα Set.univ c e) := by
      rw [CategoryTheory.Functor.map_inv]
      exact (Groupoid.inv_eq_inv ((liftAct hα Set.univ c).map
        ((Quiver.FreeGroupoid.of _).map e))).symm
    have h2 : (phiBar α hα).map ((CategoryTheory.Quotient.functor homotopy).map
        (inv ((Quiver.FreeGroupoid.of _).map e))) = inv (cls (inclA hα e).1 (inclA hα e).2.1) := by
      rw [CategoryTheory.Functor.map_inv, CategoryTheory.Functor.map_inv]
      congr 1
      exact phiBar_arr hα e
    show (ev ((liftAct hα Set.univ c).map (inv ((Quiver.FreeGroupoid.of _).map e))) p).1 =
      p.1 ≫ (phiBar α hα).map ((CategoryTheory.Quotient.functor homotopy).map
        (inv ((Quiver.FreeGroupoid.of _).map e)))
    rw [h1]
    exact (rfl : (ev (Groupoid.inv (arrActQ hα Set.univ c e)) p).1 =
      p.1 ≫ inv (cls (inclA hα e).1 (inclA hα e).2.1)).trans (congrArg (p.1 ≫ ·) h2).symm
  | id x =>
    intro p
    simp only [CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  | comp f g hf hg =>
    intro p
    rw [ev_liftAct_comp, hg, hf]
    exact (Category.assoc _ _ _).trans (congrArg (p.1 ≫ ·)
      ((congrArg (phiBar α hα).map ((CategoryTheory.Quotient.functor homotopy).map_comp f g)).trans
        ((phiBar α hα).map_comp _ _)).symm)

variable (hc : IsCocycle c)

lemma liftActQ_fst {x y : ArrowQuot α} (u : vtx x ⟶ vtx y)
    (p : ((liftActQ hα Set.univ c hc).obj (vtx x)).carrier) :
    (ev ((liftActQ hα Set.univ c hc).map u) p).1 = p.1 ≫ (phiBar α hα).map u := by
  obtain ⟨w, rfl⟩ := (CategoryTheory.Quotient.functor homotopy).map_surjective u
  change (ev ((liftAct hα Set.univ c).map w) p).1 = _
  exact liftAct_fst hα c w p

/-- The potential on the base stage. -/
def potB (a : Y (x₀ := x₀) (α := α) Set.univ) : ℤ :=
  (ev ((liftActQ hα Set.univ c hc).map ((D.psiBar hE).map a.as.u))
    ((𝟙 (vtx x₀), 0) : (vtx x₀ ⟶ vtx x₀) × ℤ)).2

lemma qArr_inclA {x y : RayVert (ArrowQuot α)} (e : x ⟶ y)
    (h : ¬(arrowIdeal α).mem (inclA hα e).1) : qArr α hα (inclA hα e) h = e :=
  Subtype.ext (quotF_liftQ α e.1)

lemma potB_step {x' y' : RayVert (ArrowQuot α)} (e' : x' ⟶ y') (ua : vtx x₀ ⟶ vtx x'.out.as) :
    ∀ (v : vtx x₀ ⟶ vtx y'.out.as) (_ : v = ua ≫ cls (inclA hα e').1 (inclA hα e').2.1)
      (ε : RayVert.mk (⟨⟨x'.out.as, ua⟩⟩ : Y (x₀ := x₀) (α := α) Set.univ) ⟶
        RayVert.mk (⟨⟨y'.out.as, v⟩⟩ : Y (x₀ := x₀) (α := α) Set.univ)),
      Cover.val (liftArrQ (isProper Set.univ) ε).1 = (inclA hα e').1 →
      c ε = potB hα D hE c hc ⟨⟨y'.out.as, v⟩⟩ - potB hα D hE c hc ⟨⟨x'.out.as, ua⟩⟩ := by
  intro v hv
  subst hv
  intro ε hε
  have hfe : ε = qArrI (isProper Set.univ) (liftArr (⟨x'.out.as, ua⟩ : Cover x₀) (inclA hα e'))
      (not_mem_lift hα Set.univ e' ua) := by
    apply Subtype.ext
    exact (Quot.out_eq ε.1).symm.trans (congrArg (qF (I := arrSetIdeal
      (killed (x₀ := x₀) (α := α) Set.univ))).map (Cover.val_injective hε))
  have hce : c ε = liftWtQ hα Set.univ c e' ua := by rw [hfe]; rfl
  rw [hce]
  unfold potB
  have hnm : ¬(arrowIdeal α).mem (inclA hα e').1 := liftQ_not_mem α hα e'.2
  have hps : (D.psiBar hE).map (cls (inclA hα e').1 (inclA hα e').2.1) =
      (CategoryTheory.Quotient.functor homotopy).map ((Quiver.FreeGroupoid.of _).map e') := by
    rw [psiBar_cls hα D hE (inclA hα e') hnm, cls_eq_arr]
    congr 2
    exact qArr_inclA hα e' hnm
  change _ = (ev ((liftActQ hα Set.univ c hc).map ((D.psiBar hE).map
    (ua ≫ cls (inclA hα e').1 (inclA hα e').2.1))) ((𝟙 (vtx x₀), 0) : (vtx x₀ ⟶ vtx x₀) × ℤ)).2 - _
  erw [CategoryTheory.Functor.map_comp, hps, CategoryTheory.Functor.map_comp]
  change _ = (arrActQ hα Set.univ c e' (ev ((liftActQ hα Set.univ c hc).map
    ((D.psiBar hE).map ua)) ((𝟙 (vtx x₀), 0) : (vtx x₀ ⟶ vtx x₀) × ℤ))).2 - _
  have hfst : (ev ((liftActQ hα Set.univ c hc).map ((D.psiBar hE).map ua))
      ((𝟙 (vtx x₀), 0) : (vtx x₀ ⟶ vtx x₀) × ℤ)).1 = ua := by
    refine (liftActQ_fst hα c hc _ _).trans ?_
    change 𝟙 _ ≫ _ = _
    exact (Category.id_comp _).trans (phiBar_psiBar_map hα D hE ua)
  change _ = ((ev ((liftActQ hα Set.univ c hc).map ((D.psiBar hE).map ua))
    ((𝟙 (vtx x₀), 0) : (vtx x₀ ⟶ vtx x₀) × ℤ)).2 + liftWtQ hα Set.univ c e'
      (ev ((liftActQ hα Set.univ c hc).map ((D.psiBar hE).map ua))
        ((𝟙 (vtx x₀), 0) : (vtx x₀ ⟶ vtx x₀) × ℤ)).1) - _
  rw [hfst]
  ring

include hα D hE hc in
/-- **The base stage is simply connected.** -/
theorem sc_univ : IsCoboundary c := by
  refine ⟨fun a ↦ potB hα D hE c hc a.out, fun {a a'} ε ↦ ?_⟩
  have hnm := not_mem_base hα ε
  have hfv := Cover.isIrreducible_val (liftArrQ (isProper Set.univ) ε).2
  let ε₀ : RayVert.mk a.out.as.y ⟶ RayVert.mk a'.out.as.y :=
    ⟨Cover.val (liftArrQ (isProper Set.univ) ε).1, hfv⟩
  have hinc : inclA hα (qArr α hα ε₀ hnm) = ε₀ := incl_qArr α hα ε₀ hnm
  have hu := u_eq (liftArrQ (isProper Set.univ) ε).1 (liftArrQ (isProper Set.univ) ε).2.1
  have hv : a'.out.as.u = a.out.as.u ≫ cls (inclA hα (qArr α hα ε₀ hnm)).1
      (inclA hα (qArr α hα ε₀ hnm)).2.1 := by
    refine hu.trans (congrArg (a.out.as.u ≫ ·) (cls_congr ?_ _ _))
    exact (congrArg Subtype.val hinc).symm
  exact potB_step hα D hE c hc (qArr α hα ε₀ hnm) a.out.as.u a'.out.as.u hv ε
    (congrArg Subtype.val hinc).symm

end Stage

end LargeIndecomposable.RayCat
