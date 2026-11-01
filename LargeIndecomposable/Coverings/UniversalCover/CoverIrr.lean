module

public import LargeIndecomposable.RayCategories.Basic.Long
public import LargeIndecomposable.Coverings.UniversalCover.Cover

/-!
# The covering functor and irreducible morphisms

Nonzero morphisms of `P` lift to the universal cover at any object over their
source (`Cover.liftAt`), and lifts compose. Hence a morphism of the cover is
irreducible exactly when its image in `P` is (`Cover.isIrreducible_iff`):
factorizations in `P` lift. So the projection maps the quiver of the cover to
the quiver of `P`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe v u

namespace RayCat

namespace Cover

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P] [IsRayCategory P] {x₀ : P}

/-- The lift of a nonzero morphism starting at `a`. -/
def liftAt (a : Cover x₀) {z : P} (f : a.y ⟶ z) (hf : f ≠ 0) :
    a ⟶ (⟨z, a.u ≫ cls f hf⟩ : Cover x₀) :=
  some ⟨f, hf, rfl⟩

lemma val_liftAt (a : Cover x₀) {z : P} (f : a.y ⟶ z) (hf : f ≠ 0) :
    val (liftAt a f hf) = f := rfl

lemma isIso_val {a b : Cover x₀} (f : a ⟶ b) [IsIso f] : IsIso (val f) :=
  inferInstanceAs (IsIso ((proj x₀).map f))

/-- The image of an irreducible morphism of the cover is irreducible. -/
theorem isIrreducible_val {a b : Cover x₀} {f : a ⟶ b} (hf : IsIrreducible f) :
    IsIrreducible (val f) := by
  rcases f with _ | f
  · exact absurd rfl hf.1
  obtain ⟨hf0, hfu⟩ := f.2
  refine ⟨hf0, fun hiso ↦ ?_, fun z g h hgh ↦ ?_⟩
  · have : IsIso f.1 := hiso
    obtain ⟨hy, he⟩ := eq_eqToHom_of_isIso f.1
    obtain ⟨y, u⟩ := a
    obtain ⟨y', u'⟩ := b
    change y = y' at hy
    subst hy
    have h1 : f.1 = 𝟙 y := he
    have hu : u' = u := by
      have : u' = u ≫ cls f.1 hf0 := hfu
      rw [this, show cls f.1 hf0 = cls (𝟙 y) (IsRayCategory.id_ne_zero y) by congr 1, cls_id,
        Category.comp_id]
    subst hu
    apply hf.2.1
    have hf1 : (some f : (⟨y, u'⟩ : Cover x₀) ⟶ ⟨y, u'⟩) = 𝟙 (⟨y, u'⟩ : Cover x₀) :=
      val_injective (h1.trans (val_id (⟨y, u'⟩ : Cover x₀)).symm)
    rw [hf1]
    infer_instance
  · change f.1 = g ≫ h at hgh
    have hg : g ≠ 0 := fun h0 ↦ hf0 (by rw [hgh, h0, zero_comp])
    have hh : h ≠ 0 := fun h0 ↦ hf0 (by rw [hgh, h0, comp_zero])
    let g' := liftAt a g hg
    let h' : (⟨z, a.u ≫ cls g hg⟩ : Cover x₀) ⟶ b := some ⟨h, hh, by
      rw [Category.assoc, ← cls_comp g h (by rw [← hgh]; exact hf0)]
      refine hfu.trans ?_
      congr 2⟩
    have hfac : (some f : a ⟶ b) = g' ≫ h' := val_injective (by
      rw [val_comp]; exact hgh)
    rcases hf.2.2 _ g' h' hfac with h1 | h1
    · exact Or.inl (isIso_val g')
    · exact Or.inr (isIso_val h')

end Cover

end RayCat

end LargeIndecomposable
