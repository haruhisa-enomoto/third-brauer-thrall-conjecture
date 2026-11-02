module

public import LargeIndecomposable.MildContours.Setup.Global
public import LargeIndecomposable.RayCategories.Basic.Small

/-!
# `TinyAt` and the small model

`TinyAt` in `RaySmall P` gives `TinyAt` in `P` (`TinyAt.of_small`), so `NoTiny`
transfers from `P` to its small model.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe w v u

namespace RayCat

namespace RaySmall

variable {P : Type u} [Category.{v} P] [LocallySmall.{w} P] [HasZeroMorphisms P]

lemma isIso_symm_iff {X Y : RaySmall.{u} P} (f : X ⟶ Y) : IsIso ((sh.{w}).symm f) ↔ IsIso f := by
  rw [← isIso_sh_iff, Equiv.apply_symm_apply]

lemma symm_eq_zero_iff {X Y : RaySmall.{u} P} (f : X ⟶ Y) : (sh.{w}).symm f = 0 ↔ f = 0 := by
  rw [← sh_eq_zero_iff, Equiv.apply_symm_apply]

lemma rightDeep_iff {X Y : RaySmall.{u} P} (μ : X ⟶ Y) : RightDeep ((sh.{w}).symm μ) ↔ RightDeep μ := by
  constructor
  · intro h W ζ hζ
    have := h ((sh.{w}).symm ζ) ((isIso_symm_iff ζ).not.2 hζ)
    rw [← sh_symm_comp, symm_eq_zero_iff] at this
    exact this
  · intro h w ζ hζ
    have := h (sh.{w} (Y := ⟨w⟩) ζ) ((isIso_sh_iff ζ).not.2 hζ)
    rw [← symm_eq_zero_iff, sh_symm_comp, Equiv.symm_apply_apply] at this
    exact this

lemma leftDeep_iff {X Y : RaySmall.{u} P} (μ : X ⟶ Y) : LeftDeep ((sh.{w}).symm μ) ↔ LeftDeep μ := by
  constructor
  · intro h W ζ hζ
    have := h ((sh.{w}).symm ζ) ((isIso_symm_iff ζ).not.2 hζ)
    rw [← sh_symm_comp, symm_eq_zero_iff] at this
    exact this
  · intro h u ζ hζ
    have := h (sh.{w} (X := ⟨u⟩) ζ) ((isIso_sh_iff ζ).not.2 hζ)
    rw [← symm_eq_zero_iff, sh_symm_comp, Equiv.symm_apply_apply] at this
    exact this

/-- **`TinyAt` passes from the small model to `P`.** -/
theorem tinyAt_of_small {X Z Bp : RaySmall.{u} P} {s : X ⟶ Z} {t : X ⟶ Bp} (h : TinyAt s t) :
    TinyAt ((sh.{w}).symm s) ((sh.{w}).symm t) := by
  obtain ⟨hs0, ht0, hzb, hxb, hsR, hsL, htR, hirr, hRu, hLu, hfac⟩ := h
  refine ⟨(symm_eq_zero_iff s).not.2 hs0, (symm_eq_zero_iff t).not.2 ht0,
    fun h ↦ hzb (by cases Z; cases Bp; cases h; rfl), fun h ↦ hxb (by cases X; cases Bp; cases h; rfl),
    (rightDeep_iff s).2 hsR, (leftDeep_iff s).2 hsL, (rightDeep_iff t).2 htR, ?_, ?_, ?_, ?_⟩
  · intro y a c hac
    have := hirr (sh.{w} (Y := ⟨y⟩) a) (sh.{w} c)
      (by rw [← sh_comp, hac, Equiv.apply_symm_apply])
    rcases this with h | h
    · exact Or.inl ((isIso_sh_iff a).1 h)
    · exact Or.inr ((isIso_sh_iff c).1 h)
  · intro y μ hμ0 hμ
    have hμs : sh.{w} (Y := ⟨y⟩) μ ≠ 0 := (sh_eq_zero_iff μ).not.2 hμ0
    have hμR : RightDeep (sh.{w} (Y := ⟨y⟩) μ) := by
      rw [← rightDeep_iff, Equiv.symm_apply_apply]; exact hμ
    rcases hRu (sh.{w} (Y := ⟨y⟩) μ) hμs hμR with ⟨h, he⟩ | ⟨h, he⟩
    · left
      cases Z
      cases h
      refine ⟨rfl, ?_⟩
      rw [eqToHom_refl, Category.comp_id] at he ⊢
      rw [← he, Equiv.symm_apply_apply]
    · right
      cases Bp
      cases h
      refine ⟨rfl, ?_⟩
      rw [eqToHom_refl, Category.comp_id] at he ⊢
      rw [← he, Equiv.symm_apply_apply]
  · intro u ν hν0 hν
    have hνs : sh.{w} (X := ⟨u⟩) ν ≠ 0 := (sh_eq_zero_iff ν).not.2 hν0
    have hνL : LeftDeep (sh.{w} (X := ⟨u⟩) ν) := by
      rw [← leftDeep_iff, Equiv.symm_apply_apply]; exact hν
    obtain ⟨h, he⟩ := hLu (sh.{w} (X := ⟨u⟩) ν) hνs hνL
    cases X
    cases h
    refine ⟨rfl, ?_⟩
    rw [eqToHom_refl, Category.id_comp] at he ⊢
    rw [← he, Equiv.symm_apply_apply]
  · intro y ν hν
    obtain ⟨ν', hν'⟩ := hfac (sh.{w} (X := ⟨y⟩) ν) ((isIso_sh_iff ν).not.2 hν)
    refine ⟨(sh.{w}).symm ν', ?_⟩
    rw [← sh_symm_comp, ← hν', Equiv.symm_apply_apply]

/-- **`ProjInjAt` passes from the small model to `P`.** -/
theorem projInjAt_of_small {X Z : RaySmall.{u} P} {s : X ⟶ Z} (h : ProjInjAt s) :
    ProjInjAt ((sh.{w}).symm s) := by
  obtain ⟨hs0, hsR, hsL, hRu, hLu⟩ := h
  refine ⟨(symm_eq_zero_iff s).not.2 hs0, (rightDeep_iff s).2 hsR, (leftDeep_iff s).2 hsL, ?_, ?_⟩
  · intro y μ hμ0 hμ
    have hμs : sh.{w} (Y := ⟨y⟩) μ ≠ 0 := (sh_eq_zero_iff μ).not.2 hμ0
    have hμR : RightDeep (sh.{w} (Y := ⟨y⟩) μ) := by
      rw [← rightDeep_iff, Equiv.symm_apply_apply]; exact hμ
    obtain ⟨h, he⟩ := hRu (sh.{w} (Y := ⟨y⟩) μ) hμs hμR
    cases Z
    cases h
    refine ⟨rfl, ?_⟩
    rw [eqToHom_refl, Category.comp_id] at he ⊢
    rw [← he, Equiv.symm_apply_apply]
  · intro u ν hν0 hν
    have hνs : sh.{w} (X := ⟨u⟩) ν ≠ 0 := (sh_eq_zero_iff ν).not.2 hν0
    have hνL : LeftDeep (sh.{w} (X := ⟨u⟩) ν) := by
      rw [← leftDeep_iff, Equiv.symm_apply_apply]; exact hν
    obtain ⟨h, he⟩ := hLu (sh.{w} (X := ⟨u⟩) ν) hνs hνL
    cases X
    cases h
    refine ⟨rfl, ?_⟩
    rw [eqToHom_refl, Category.id_comp] at he ⊢
    rw [← he, Equiv.symm_apply_apply]

/-- **`TinyAtDual` passes from the small model to `P`.** -/
theorem tinyAtDual_of_small {X Z Bp : RaySmall.{u} P} {s : Z ⟶ X} {t : Bp ⟶ X}
    (h : TinyAtDual s t) : TinyAtDual ((sh.{w}).symm s) ((sh.{w}).symm t) := by
  obtain ⟨hs0, ht0, hzb, hxb, hsL, hsR, htL, hirr, hLu, hRu, hfac⟩ := h
  refine ⟨(symm_eq_zero_iff s).not.2 hs0, (symm_eq_zero_iff t).not.2 ht0,
    fun h ↦ hzb (by cases Z; cases Bp; cases h; rfl), fun h ↦ hxb (by cases X; cases Bp; cases h; rfl),
    (leftDeep_iff s).2 hsL, (rightDeep_iff s).2 hsR, (leftDeep_iff t).2 htL, ?_, ?_, ?_, ?_⟩
  · intro y c a hca
    rcases hirr (sh.{w} (Y := ⟨y⟩) c) (sh.{w} a)
      (by rw [← sh_comp, hca, Equiv.apply_symm_apply]) with h | h
    · exact Or.inl ((isIso_sh_iff c).1 h)
    · exact Or.inr ((isIso_sh_iff a).1 h)
  · intro y ν hν0 hν
    have hνs : sh.{w} (X := ⟨y⟩) ν ≠ 0 := (sh_eq_zero_iff ν).not.2 hν0
    have hνL : LeftDeep (sh.{w} (X := ⟨y⟩) ν) := by
      rw [← leftDeep_iff, Equiv.symm_apply_apply]; exact hν
    rcases hLu (sh.{w} (X := ⟨y⟩) ν) hνs hνL with ⟨h, he⟩ | ⟨h, he⟩
    · left
      cases Z
      cases h
      refine ⟨rfl, ?_⟩
      rw [eqToHom_refl, Category.id_comp] at he ⊢
      rw [← he, Equiv.symm_apply_apply]
    · right
      cases Bp
      cases h
      refine ⟨rfl, ?_⟩
      rw [eqToHom_refl, Category.id_comp] at he ⊢
      rw [← he, Equiv.symm_apply_apply]
  · intro w μ hμ0 hμ
    have hμs : sh.{w} (Y := ⟨w⟩) μ ≠ 0 := (sh_eq_zero_iff μ).not.2 hμ0
    have hμR : RightDeep (sh.{w} (Y := ⟨w⟩) μ) := by
      rw [← rightDeep_iff, Equiv.symm_apply_apply]; exact hμ
    obtain ⟨h, he⟩ := hRu (sh.{w} (Y := ⟨w⟩) μ) hμs hμR
    cases X
    cases h
    refine ⟨rfl, ?_⟩
    rw [eqToHom_refl, Category.comp_id] at he ⊢
    rw [← he, Equiv.symm_apply_apply]
  · intro y μ hμ
    obtain ⟨μ', hμ'⟩ := hfac (sh.{w} (Y := ⟨y⟩) μ) ((isIso_sh_iff μ).not.2 hμ)
    refine ⟨(sh.{w}).symm μ', ?_⟩
    rw [← sh_symm_comp, ← hμ', Equiv.symm_apply_apply]

end RaySmall

end RayCat

end LargeIndecomposable
