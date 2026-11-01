module

public import LargeIndecomposable.Coverings.UniversalCover.CoverGood
public import LargeIndecomposable.FundamentalGroups.Basic.OpFund
public import LargeIndecomposable.FundamentalGroups.Basic.CocycleExtendMax
public import LargeIndecomposable.FundamentalGroups.Basic.CoverCocycle
public import LargeIndecomposable.Coverings.UniversalCover.CoverChain

/-!
# Good covers and duality

The functor `opBar : FG(P) ⥤ FG(Pᵒᵖ)` maps the universal cover of `P` at `x₀` injectively to that
of `Pᵒᵖ` at `op x₀` (`opCov`), reversing arrows (`exists_arr_op`). Hence a good cover of `Pᵒᵖ`
gives a good cover of `P` (`coverGood_of_op`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Opposite

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] {x₀ : P}

/-- The universal cover of `P` inside that of `Pᵒᵖ`. -/
def opCov (c : Cover x₀) : Cover (op x₀) := ⟨op c.y, opBar.map c.u⟩

lemma unopBar_opBar_map {x y : P} (u : vtx x ⟶ vtx y) : unopBar.map (opBar.map u) = u := by
  have h := Functor.congr_hom (opBar_unopBar (P := P)) u
  rw [Functor.comp_map, Functor.id_map] at h
  rw [h]
  exact (Category.id_comp _).trans (Category.comp_id _)

lemma opCov_injective : Function.Injective (opCov (x₀ := x₀)) := by
  rintro ⟨y, u⟩ ⟨y', u'⟩ h
  obtain ⟨h1, h2⟩ := Cover.mk.inj h
  obtain rfl : y = y' := op_injective h1
  have h3 := congrArg unopBar.map (eq_of_heq h2)
  change unopBar.map (opBar.map u) = unopBar.map (opBar.map u') at h3
  rw [unopBar_opBar_map, unopBar_opBar_map] at h3
  rw [h3]

lemma opBar_cls_arr {x y : RayVert P} (ε : x ⟶ y) :
    opBar.map (cls ε.1 ε.2.1) = inv (cls (revArr ε).1 (revArr ε).2.1) := by
  rw [cls_eq_arr ε, cls_eq_arr (revArr ε)]
  change (CategoryTheory.Quotient.lift homotopy opFG _).map
    ((CategoryTheory.Quotient.functor homotopy).map _) = _
  rw [CategoryTheory.Quotient.lift_map_functor_map, opFG_map_of]
  change inv (pcls (revArr ε).toPath) = _
  simp only [pcls_toPath]

/-- An arrow of the cover of `P` gives a reversed arrow of the cover of `Pᵒᵖ`. -/
lemma exists_arr_op {c d : Cover x₀} (e : RayVert.mk c ⟶ RayVert.mk d) :
    Nonempty (RayVert.mk (opCov d) ⟶ RayVert.mk (opCov c)) := by
  obtain ⟨f, hf⟩ := e
  have hfv := Cover.isIrreducible_val hf
  have hu := u_eq f hf.1
  let ε : RayVert.mk c.y ⟶ RayVert.mk d.y := ⟨Cover.val f, hfv⟩
  have hc : opCov c = ⟨op c.y, (opCov d).u ≫ cls (revArr ε).1 (revArr ε).2.1⟩ := by
    unfold opCov
    rw [hu, CategoryTheory.Functor.map_comp,
      show cls (Cover.val f) (RayCat.val_ne_zero hf.1) = cls ε.1 ε.2.1 from rfl, opBar_cls_arr]
    dsimp only
    congr 1
    exact ((Category.assoc _ _ _).trans ((congrArg (opBar.map c.u ≫ ·)
      (IsIso.inv_hom_id (cls (revArr ε).1 (revArr ε).2.1))).trans (Category.comp_id _))).symm
  rw [hc]
  exact ⟨⟨Cover.liftAt (opCov d) (revArr ε).1 (revArr ε).2.1,
    Cover.isIrreducible_liftAt (opCov d) (revArr ε).2⟩⟩

lemma exists_path_op {c : RayVert (Cover x₀)} : ∀ {d : RayVert (Cover x₀)} (p : Quiver.Path c d),
    ∃ q : Quiver.Path (RayVert.mk (opCov d.out)) (RayVert.mk (opCov c.out)), q.length = p.length
  | _, .nil => ⟨.nil, rfl⟩
  | _, .cons p e => by
    obtain ⟨q, hq⟩ := exists_path_op p
    obtain ⟨e'⟩ := exists_arr_op e
    exact ⟨e'.toPath.comp q, by simp [hq, add_comm]⟩

/-- **A good cover of the opposite category gives a good cover.** -/
theorem coverGood_of_op (h : CoverGood (op x₀)) : CoverGood x₀ := by
  refine ⟨fun c p ↦ ?_, fun a b ↦ ?_⟩
  · obtain ⟨q, hq⟩ := exists_path_op p
    rw [← hq]
    exact h.1 _ q
  · refine ((h.2 (opCov b) (opCov a)).preimage opCov_injective.injOn).subset
      fun z ⟨⟨p⟩, ⟨q⟩⟩ ↦ ?_
    obtain ⟨p', -⟩ := exists_path_op p
    obtain ⟨q', -⟩ := exists_path_op q
    exact ⟨⟨q'⟩, ⟨p'⟩⟩

end LargeIndecomposable.RayCat
