module

public import LargeIndecomposable.FundamentalGroups.Fischbacher.Lemma43
public import LargeIndecomposable.FundamentalGroups.Fischbacher.SeparationCocycle

/-!
# Separation from Lemma 4.3

Two arrows into `a` that end an essential contour with value `μ` lie in different components of
the morphisms into `a` from a set `D` none of whose nonzero morphisms into `a` factors through `μ`
(`not_sepComp_of_essCfg`): a joining sequence of comparabilities gives a walk of common upper
bounds avoiding `μ` (`upWalk_of_sepComp`), which Lemma 4.3 excludes.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

universe v u

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P] [IsRayCategory P] {a s : P}

/-- A nonzero morphism into `a` from another point ends with an arrow. -/
lemma exists_last {y : P} (g : y ⟶ a) (hg : g ≠ 0) (hy : y ≠ a) :
    ∃ (L : AIn a) (r : y ⟶ L.1), IsIrreducible L.2 ∧ g = r ≫ L.2 := by
  have hl : 0 < (pathOf g hg).length := by
    refine length_pathOf_pos g hg fun hiso ↦ hy ?_
    obtain ⟨h, -⟩ := eq_eqToHom_of_isIso g
    exact h
  have h := pathVal_pathOf g hg
  rcases hp : pathOf g hg with _ | ⟨p, lam⟩
  · rw [hp] at hl; simp at hl
  · rw [hp] at h
    exact ⟨⟨_, lam.1⟩, pathVal p, lam.2, h.symm⟩

/-- A last arrow of a nonzero morphism into `a` from another point. -/
def la (g : Σ y : P, y ⟶ a) (h : g.2 ≠ 0 ∧ g.1 ≠ a) : AIn a :=
  (exists_last g.2 h.1 h.2).choose

def laR (g : Σ y : P, y ⟶ a) (h : g.2 ≠ 0 ∧ g.1 ≠ a) : g.1 ⟶ (la g h).1 :=
  (exists_last g.2 h.1 h.2).choose_spec.choose

lemma la_irr (g : Σ y : P, y ⟶ a) (h : g.2 ≠ 0 ∧ g.1 ≠ a) : IsIrreducible (la g h).2 :=
  (exists_last g.2 h.1 h.2).choose_spec.choose_spec.1

lemma la_spec (g : Σ y : P, y ⟶ a) (h : g.2 ≠ 0 ∧ g.1 ≠ a) : g.2 = laR g h ≫ (la g h).2 :=
  (exists_last g.2 h.1 h.2).choose_spec.choose_spec.2

variable {μ : s ⟶ a} {D : Set P}

lemma upWalk_la (hD : ∀ g : Σ y : P, y ⟶ a, g.1 ∈ D → g.2 ≠ 0 → ¬Thr μ g.2)
    {f g : Σ y : P, y ⟶ a} (h : Relation.ReflTransGen (Relation.SymmGen (SepLe D a)) f g)
    (hf : f.2 ≠ 0 ∧ f.1 ≠ a) (hg : g.2 ≠ 0 ∧ g.1 ≠ a) :
    Nonempty (UpWalk μ (la f hf) (la g hg)) := by
  induction h with
  | refl => exact ⟨UpWalk.nil _⟩
  | @tail y g _ hyg ih =>
    have hy : y.2 ≠ 0 ∧ y.1 ≠ a := by
      rcases hyg with ⟨h1, -, -, -, h5, -⟩ | ⟨-, h2, -, -, -, h6, -⟩
      · exact ⟨h1, h5⟩
      · exact ⟨h2, h6⟩
    obtain ⟨W⟩ := ih hy
    rcases hyg with ⟨-, -, -, hgD, -, -, k, hk⟩ | ⟨-, -, -, hyD, -, -, k, hk⟩
    · -- `g = k ≫ y`
      refine ⟨W.snoc ⟨g.1, k ≫ laR y hy, laR g hg, ?_, ?_, ?_, la_irr y hy, la_irr g hg⟩⟩
      · rw [Category.assoc, ← la_spec, ← la_spec, hk]
      · rw [Category.assoc, ← la_spec, ← hk]; exact hg.1
      · rw [Category.assoc, ← la_spec, ← hk]; exact hD g hgD hg.1
    · -- `y = k ≫ g`
      refine ⟨W.snoc ⟨y.1, laR y hy, k ≫ laR g hg, ?_, ?_, ?_, la_irr y hy, la_irr g hg⟩⟩
      · rw [Category.assoc, ← la_spec, ← la_spec, hk]
      · rw [← la_spec]; exact hy.1
      · rw [← la_spec]; exact hD y hyD hy.1

/-- **Joined arrows give a walk of upper bounds avoiding `μ`.** -/
theorem upWalk_of_sepComp (hD : ∀ g : Σ y : P, y ⟶ a, g.1 ∈ D → g.2 ≠ 0 → ¬Thr μ g.2)
    {x₁ x₂ : P} (α : x₁ ⟶ a) (β : x₂ ⟶ a) (hα : IsIrreducible α) (hβ : IsIrreducible β)
    (hx₁ : x₁ ∈ D) (hx₂ : x₂ ∈ D) (h₁ : x₁ ≠ a) (h₂ : x₂ ≠ a)
    (h : SepComp D a ⟨x₁, α⟩ ⟨x₂, β⟩) : Nonempty (UpWalk μ ⟨x₁, α⟩ ⟨x₂, β⟩) := by
  have hv₁ : (⟨x₁, α⟩ : Σ y : P, y ⟶ a).2 ≠ 0 ∧ x₁ ≠ a := ⟨hα.1, h₁⟩
  have hv₂ : (⟨x₂, β⟩ : Σ y : P, y ⟶ a).2 ≠ 0 ∧ x₂ ≠ a := ⟨hβ.1, h₂⟩
  rw [SepComp, ← Relation.EqvGen.reflTransGen_symmGen] at h
  obtain ⟨W⟩ := upWalk_la hD h hv₁ hv₂
  have st₁ : UpStep μ ⟨x₁, α⟩ (la ⟨x₁, α⟩ hv₁) :=
    ⟨x₁, 𝟙 _, laR ⟨x₁, α⟩ hv₁, by rw [Category.id_comp]; exact la_spec ⟨x₁, α⟩ hv₁,
      by rw [Category.id_comp]; exact hα.1, by rw [Category.id_comp]; exact hD _ hx₁ hα.1,
      hα, la_irr _ _⟩
  have st₂ : UpStep μ (la ⟨x₂, β⟩ hv₂) ⟨x₂, β⟩ :=
    ⟨x₂, laR ⟨x₂, β⟩ hv₂, 𝟙 _, by rw [Category.id_comp]; exact (la_spec ⟨x₂, β⟩ hv₂).symm,
      by rw [← la_spec]; exact hβ.1, by rw [← la_spec]; exact hD _ hx₂ hβ.1, la_irr _ _, hβ⟩
  exact ⟨UpWalk.cons st₁ (W.snoc st₂)⟩

/-- **Lemma 4.3, separation form**: the two last arrows of an essential contour are not joined
inside a set avoiding its value. -/
theorem not_sepComp_of_essCfg (hL : LeftCancel P) (hR : RightCancel P) (hCB : ChainBounded P)
    (hμ : μ ≠ 0) (C : EssCfg μ)
    (hD : ∀ g : Σ y : P, y ⟶ a, g.1 ∈ D → g.2 ≠ 0 → ¬Thr μ g.2) (hx : C.x ∈ D)
    (hy : C.y ∈ D) (hxa : C.x ≠ a) (hya : C.y ≠ a) :
    ¬SepComp D a ⟨C.x, C.α.1⟩ ⟨C.y, C.β.1⟩ := by
  intro h
  obtain ⟨W⟩ := upWalk_of_sepComp hD C.α.1 C.β.1 C.α.2 C.β.2 hx hy hxa hya h
  exact lemma43 hL hR hCB hμ _ C W rfl rfl rfl

end LargeIndecomposable.RayCat
