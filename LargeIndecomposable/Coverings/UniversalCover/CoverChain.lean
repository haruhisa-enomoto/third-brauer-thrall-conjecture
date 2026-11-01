module

public import LargeIndecomposable.RayCategories.Basic.Prefix
public import LargeIndecomposable.Coverings.UniversalCover.CoverIrr

/-!
# Cancellation and chain-boundedness pass to the universal cover

Morphisms of the cover are determined by their values (`val_injective`), so left and right
cancellation pass from `P` to `Cover x₀`. A factorization in `P` between morphisms of the
cover with a common target (or source) lifts to the cover, so peaks and valleys of the cover
project to peaks and valleys of `P`; hence chains project to chains and chain-boundedness
passes to the cover (`chainBounded_cover`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover

universe v u

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P] [IsRayCategory P] {x₀ : P}

lemma leftCancel_cover (hL : LeftCancel P) : LeftCancel (Cover x₀) := by
  intro a b c f g h hfg h0
  apply val_injective
  refine hL (val f) (val g) (val h) ?_ ?_
  · rw [← val_comp, ← val_comp, hfg]
  · rw [← val_comp]
    exact fun h' ↦ h0 ((val_eq_zero_iff _).1 h')

lemma rightCancel_cover (hR : RightCancel P) : RightCancel (Cover x₀) := by
  intro a b c f g h hfg h0
  apply val_injective
  refine hR (val f) (val g) (val h) ?_ ?_
  · rw [← val_comp, ← val_comp, hfg]
  · rw [← val_comp]
    exact fun h' ↦ h0 ((val_eq_zero_iff _).1 h')

lemma val_ne_zero {a b : Cover x₀} {f : a ⟶ b} (hf : f ≠ 0) : val f ≠ 0 :=
  fun h ↦ hf ((val_eq_zero_iff _).1 h)

/-- The walk class of the target of a nonzero morphism of the cover. -/
lemma u_eq {a b : Cover x₀} (f : a ⟶ b) (hf : f ≠ 0) : b.u = a.u ≫ cls (val f) (val_ne_zero hf) := by
  rcases f with _ | f
  · exact absurd rfl hf
  exact f.2.2

/-- A factorization `c ≫ val g = val f` of nonzero morphisms with a common target lifts. -/
lemma exists_lift_left {a a' b : Cover x₀} (f : a ⟶ b) (g : a' ⟶ b) (hf : f ≠ 0) (hg : g ≠ 0)
    (c : a.y ⟶ a'.y) (hc : c ≫ val g = val f) : ∃ C : a ⟶ a', C ≫ g = f := by
  have hfc : c ≫ val g ≠ 0 := hc ▸ val_ne_zero hf
  have hc0 : c ≠ 0 := fun h ↦ hfc (by rw [h, zero_comp])
  have hu : a'.u = a.u ≫ cls c hc0 := by
    have h1 := u_eq f hf
    have h2 := u_eq g hg
    have h3 : cls (val f) (val_ne_zero hf) = cls c hc0 ≫ cls (val g) (val_ne_zero hg) := by
      have := cls_comp c (val g) hfc
      convert this using 2 <;> simp [hc]
    rw [h3, ← Category.assoc, h2] at h1
    exact ((cancel_mono _).1 h1.symm).symm
  refine ⟨some ⟨c, hc0, hu⟩, val_injective ?_⟩
  rw [val_comp]
  exact hc

/-- A factorization `val f ≫ c = val g` of nonzero morphisms with a common source lifts. -/
lemma exists_lift_right {a b b' : Cover x₀} (f : a ⟶ b) (g : a ⟶ b') (hf : f ≠ 0) (hg : g ≠ 0)
    (c : b.y ⟶ b'.y) (hc : val f ≫ c = val g) : ∃ C : b ⟶ b', f ≫ C = g := by
  have hfc : val f ≫ c ≠ 0 := hc ▸ val_ne_zero hg
  have hc0 : c ≠ 0 := fun h ↦ hfc (by rw [h, comp_zero])
  have hu : b'.u = b.u ≫ cls c hc0 := by
    have h1 := u_eq f hf
    have h2 := u_eq g hg
    have h3 : cls (val g) (val_ne_zero hg) = cls (val f) (val_ne_zero hf) ≫ cls c hc0 := by
      have := cls_comp (val f) c hfc
      convert this using 2 <;> simp [hc]
    rw [h2, h3, ← Category.assoc, ← h1]
  refine ⟨some ⟨c, hc0, hu⟩, val_injective ?_⟩
  rw [val_comp]
  exact hc

/-- The projection of a morphism of the cover. -/
def projRM (F : RayMor (Cover x₀)) : RayMor P := ⟨F.1.y, F.2.1.y, val F.2.2⟩

lemma peak_projRM {F G : RayMor (Cover x₀)} (hF : F.2.2 ≠ 0) (hG : G.2.2 ≠ 0) (h : Peak F G) :
    Peak (projRM F) (projRM G) := by
  obtain ⟨a, b, f⟩ := F
  obtain ⟨a', b', g⟩ := G
  obtain ⟨hb, h1, h2⟩ := h
  change b = b' at hb
  subst hb
  simp only [eqToHom_refl, Category.comp_id] at h1 h2
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨c, hc⟩
    change c ≫ val g = val f ≫ eqToHom (rfl : b.y = b.y) at hc
    rw [eqToHom_refl, Category.comp_id] at hc
    obtain ⟨C, hC⟩ := exists_lift_left f g hF hG c hc
    exact h1 ⟨C, hC⟩
  · rintro ⟨c, hc⟩
    change c ≫ val f ≫ eqToHom (rfl : b.y = b.y) = val g at hc
    have hc' : c ≫ val f = val g :=
      (congrArg (c ≫ ·) (Category.comp_id (val f))).symm.trans hc
    obtain ⟨C, hC⟩ := exists_lift_left g f hG hF c hc'
    exact h2 ⟨C, hC⟩

lemma valley_projRM {F G : RayMor (Cover x₀)} (hF : F.2.2 ≠ 0) (hG : G.2.2 ≠ 0) (h : Valley F G) :
    Valley (projRM F) (projRM G) := by
  obtain ⟨a, b, f⟩ := F
  obtain ⟨a', b', g⟩ := G
  obtain ⟨ha, h1, h2⟩ := h
  change a = a' at ha
  subst ha
  simp only [eqToHom_refl, Category.id_comp] at h1 h2
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨c, hc⟩
    change eqToHom (rfl : a.y = a.y) ≫ val f ≫ c = val g at hc
    rw [eqToHom_refl, Category.id_comp] at hc
    obtain ⟨C, hC⟩ := exists_lift_right f g hF hG c hc
    exact h1 ⟨C, hC⟩
  · rintro ⟨c, hc⟩
    change eqToHom (rfl : a.y = a.y) ≫ val g ≫ c = val f at hc
    rw [eqToHom_refl, Category.id_comp] at hc
    obtain ⟨C, hC⟩ := exists_lift_right g f hG hF c hc
    exact h2 ⟨C, hC⟩

lemma isChain_map_projRM {o : ℕ} {l : List (RayMor (Cover x₀))} (hl : IsChain o l) :
    IsChain o (l.map projRM) := by
  refine ⟨fun f hf ↦ ?_, fun j hj ↦ ?_⟩
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact val_ne_zero (hl.1 g hg)
  · rw [List.length_map] at hj
    have hl' := hl.2 j hj
    have h0 := hl.1 _ (List.getElem_mem (show j < l.length by omega))
    have h1 := hl.1 _ (List.getElem_mem hj)
    simp only [List.getElem_map]
    unfold Link at hl' ⊢
    split_ifs at hl' ⊢
    · exact peak_projRM h0 h1 hl'
    · exact valley_projRM h0 h1 hl'

/-- **Chain-boundedness passes to the universal cover.** -/
lemma chainBounded_cover (hCB : ChainBounded P) : ChainBounded (Cover x₀) := by
  obtain ⟨N, hN⟩ := hCB
  refine ⟨N, fun l hl ↦ ?_⟩
  have := hN _ (isChain_map_projRM hl)
  rwa [List.length_map] at this

end LargeIndecomposable.RayCat
