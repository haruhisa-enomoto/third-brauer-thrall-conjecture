module

public import LargeIndecomposable.FundamentalGroups.Fischbacher.SepDual
public import LargeIndecomposable.FundamentalGroups.Fischbacher.Lemma52Init

/-!
# Walks of arrows out of a point with common upper bounds (Fischbacher §5.3)

An arrow walk out of `c` is a list of steps; a step joins two arrows `ε₁, ε₂` out of `c` by a
nonzero common upper bound `ε₁ x = ε₂ y` whose target satisfies a predicate `P`. The separation
criterion at a minimal point (`outComp_of_coboundary`) gives such a walk between two arrows
(`exists_bwalk_of_outComp`). A walk minimal for the Dershowitz–Manna order on the depths of its
bounds has no trivial step, satisfies the valley conditions, has essential contours and distinct
bound targets; these are the properties Fischbacher uses in §5.3.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

universe v u

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [IsRayCategory A]

/-- Arrows out of `c`. -/
abbrev OutA (c : A) : Type (max u v) := Σ f : A, (RayVert.mk c ⟶ RayVert.mk f)

/-- A step between two arrows out of `c`: a nonzero common upper bound with target in `P`. -/
structure BStep (c : A) (P : A → Prop) where
  a₁ : OutA c
  a₂ : OutA c
  e : A
  x : a₁.1 ⟶ e
  y : a₂.1 ⟶ e
  eq : a₁.2.1 ≫ x = a₂.2.1 ≫ y
  ne : a₁.2.1 ≫ x ≠ 0
  he : P e

variable {c : A} {P : A → Prop}

/-- The depth of the bound of a step. -/
def BStep.dep (s : BStep c P) : ℕ := depth (s.a₁.2.1 ≫ s.x)

/-- A walk of steps from `α` to `β`. -/
def IsBWalk : OutA c → OutA c → List (BStep c P) → Prop
  | α, β, [] => α = β
  | α, β, s :: L => s.a₁ = α ∧ IsBWalk s.a₂ β L

/-- The multiset of depths of the bounds. -/
def bms (L : List (BStep c P)) : Multiset ℕ := (L.map BStep.dep : Multiset ℕ)

lemma isBWalk_append : ∀ {α β : OutA c} (L L' : List (BStep c P)),
    IsBWalk α β (L ++ L') ↔ ∃ γ, IsBWalk α γ L ∧ IsBWalk γ β L'
  | α, β, [], L' => ⟨fun h ↦ ⟨α, rfl, h⟩, fun ⟨γ, h₁, h₂⟩ ↦ by
      change α = γ at h₁; subst h₁; exact h₂⟩
  | α, β, s :: L, L' => by
    change s.a₁ = α ∧ IsBWalk s.a₂ β (L ++ L') ↔ ∃ γ, (s.a₁ = α ∧ IsBWalk s.a₂ γ L) ∧ _
    rw [isBWalk_append L L']
    constructor
    · rintro ⟨h₁, γ, h₂, h₃⟩; exact ⟨γ, ⟨h₁, h₂⟩, h₃⟩
    · rintro ⟨γ, ⟨h₁, h₂⟩, h₃⟩; exact ⟨h₁, γ, h₂, h₃⟩

lemma bms_append (L L' : List (BStep c P)) : bms (L ++ L') = bms L + bms L' := by
  simp [bms]

lemma bms_cons (s : BStep c P) (L : List (BStep c P)) : bms (s :: L) = s.dep ::ₘ bms L := by
  simp [bms]

/-- A nonzero morphism out of `c` to another point starts with an arrow. -/
lemma exists_first {y : A} (μ : c ⟶ y) (hμ : μ ≠ 0) (hy : y ≠ c) :
    ∃ (α : OutA c) (r : α.1 ⟶ y), μ = α.2.1 ≫ r := by
  have hl : 0 < (pathOf μ hμ).length := by
    refine length_pathOf_pos μ hμ fun hiso ↦ hy ?_
    obtain ⟨h, -⟩ := eq_eqToHom_of_isIso μ
    exact h.symm
  obtain ⟨z, α, q, -, hq⟩ := Quiver.Path.eq_toPath_comp_of_length_eq_succ (pathOf μ hμ)
    (n := (pathOf μ hμ).length - 1) (by omega)
  refine ⟨⟨z.out, α⟩, pathVal q, ?_⟩
  have := pathVal_pathOf μ hμ
  rw [hq, pathVal_comp] at this
  rw [← this]
  change (𝟙 _ ≫ α.1) ≫ pathVal q = α.1 ≫ pathVal q
  rw [Category.id_comp]

/-- A first arrow of a nonzero morphism out of `c` to another point. -/
def fa (μ : Σ y : A, c ⟶ y) (h : μ.2 ≠ 0 ∧ μ.1 ≠ c) : OutA c :=
  (exists_first μ.2 h.1 h.2).choose

/-- The rest after the first arrow. -/
def faR (μ : Σ y : A, c ⟶ y) (h : μ.2 ≠ 0 ∧ μ.1 ≠ c) : (fa μ h).1 ⟶ μ.1 :=
  (exists_first μ.2 h.1 h.2).choose_spec.choose

lemma fa_spec (μ : Σ y : A, c ⟶ y) (h : μ.2 ≠ 0 ∧ μ.1 ≠ c) : μ.2 = (fa μ h).2.1 ≫ faR μ h :=
  (exists_first μ.2 h.1 h.2).choose_spec.choose_spec

/-- The step given by a comparability `g = f ≫ h`, between first arrows. -/
def stepOfLe {D : Set A} (f g : Σ y : A, c ⟶ y) (hf : f.2 ≠ 0 ∧ f.1 ≠ c)
    (hg : g.2 ≠ 0 ∧ g.1 ≠ c) (hgD : g.1 ∈ D) (h : f.1 ⟶ g.1) (hh : g.2 = f.2 ≫ h) :
    BStep c (fun e ↦ e ∈ D ∧ e ≠ c) where
  a₁ := fa f hf
  a₂ := fa g hg
  e := g.1
  x := faR f hf ≫ h
  y := faR g hg
  eq := by rw [← Category.assoc, ← fa_spec, ← fa_spec, hh]
  ne := by rw [← Category.assoc, ← fa_spec, ← hh]; exact hg.1
  he := ⟨hgD, hg.2⟩

/-- The step given by a comparability `f = g ≫ h`, between first arrows. -/
def stepOfGe {D : Set A} (f g : Σ y : A, c ⟶ y) (hf : f.2 ≠ 0 ∧ f.1 ≠ c)
    (hg : g.2 ≠ 0 ∧ g.1 ≠ c) (hfD : f.1 ∈ D) (h : g.1 ⟶ f.1) (hh : f.2 = g.2 ≫ h) :
    BStep c (fun e ↦ e ∈ D ∧ e ≠ c) where
  a₁ := fa f hf
  a₂ := fa g hg
  e := f.1
  x := faR f hf
  y := faR g hg ≫ h
  eq := by rw [← Category.assoc, ← fa_spec, ← fa_spec, hh]
  ne := by rw [← fa_spec]; exact hf.1
  he := ⟨hfD, hf.2⟩

lemma exists_bwalk_fa {D : Set A} {f g : Σ y : A, c ⟶ y}
    (h : Relation.ReflTransGen (Relation.SymmGen (OutLe D c)) f g) (hf : f.2 ≠ 0 ∧ f.1 ≠ c)
    (hg : g.2 ≠ 0 ∧ g.1 ≠ c) :
    ∃ L : List (BStep c (fun e ↦ e ∈ D ∧ e ≠ c)), IsBWalk (fa f hf) (fa g hg) L := by
  induction h with
  | refl => exact ⟨[], rfl⟩
  | @tail y g _ hyg ih =>
    have hy : y.2 ≠ 0 ∧ y.1 ≠ c := by
      rcases hyg with ⟨h1, -, -, -, h5, -⟩ | ⟨-, h2, -, -, -, h6, -⟩
      · exact ⟨h1, h5⟩
      · exact ⟨h2, h6⟩
    obtain ⟨L, hL⟩ := ih hy
    rcases hyg with ⟨-, -, -, hgD, -, -, k, hk⟩ | ⟨-, -, -, hyD, -, -, k, hk⟩
    · refine ⟨L ++ [stepOfLe y g hy hg hgD k hk], ?_⟩
      rw [isBWalk_append]
      exact ⟨_, hL, rfl, rfl⟩
    · refine ⟨L ++ [stepOfGe y g hy hg hyD k hk], ?_⟩
      rw [isBWalk_append]
      exact ⟨_, hL, rfl, rfl⟩

/-- **An arrow walk from the separation criterion at a minimal point.** -/
theorem exists_bwalk_of_outComp {D : Set A} {t₁ t₂ : A} (e₁ : RayVert.mk c ⟶ RayVert.mk t₁)
    (e₂ : RayVert.mk c ⟶ RayVert.mk t₂) (ht₁ : t₁ ∈ D) (ht₂ : t₂ ∈ D) (h₁ : t₁ ≠ c)
    (h₂ : t₂ ≠ c) (h : OutComp D c ⟨t₁, e₁.1⟩ ⟨t₂, e₂.1⟩) :
    ∃ L : List (BStep c (fun e ↦ e ∈ D ∧ e ≠ c)), IsBWalk ⟨t₁, e₁⟩ ⟨t₂, e₂⟩ L := by
  have hv₁ : (⟨t₁, e₁.1⟩ : Σ y : A, c ⟶ y).2 ≠ 0 ∧ t₁ ≠ c := ⟨e₁.2.1, h₁⟩
  have hv₂ : (⟨t₂, e₂.1⟩ : Σ y : A, c ⟶ y).2 ≠ 0 ∧ t₂ ≠ c := ⟨e₂.2.1, h₂⟩
  rw [OutComp, ← Relation.EqvGen.reflTransGen_symmGen] at h
  obtain ⟨L, hL⟩ := exists_bwalk_fa h hv₁ hv₂
  let s₁ : BStep c (fun e ↦ e ∈ D ∧ e ≠ c) :=
    ⟨⟨t₁, e₁⟩, fa ⟨t₁, e₁.1⟩ hv₁, t₁, 𝟙 _, faR ⟨t₁, e₁.1⟩ hv₁,
      by rw [Category.comp_id]; exact fa_spec ⟨t₁, e₁.1⟩ hv₁,
      by rw [Category.comp_id]; exact e₁.2.1, ⟨ht₁, h₁⟩⟩
  let s₂ : BStep c (fun e ↦ e ∈ D ∧ e ≠ c) :=
    ⟨fa ⟨t₂, e₂.1⟩ hv₂, ⟨t₂, e₂⟩, t₂, faR ⟨t₂, e₂.1⟩ hv₂, 𝟙 _,
      by rw [Category.comp_id]; exact (fa_spec ⟨t₂, e₂.1⟩ hv₂).symm,
      by rw [← fa_spec ⟨t₂, e₂.1⟩ hv₂]; exact e₂.2.1, ⟨ht₂, h₂⟩⟩
  refine ⟨s₁ :: (L ++ [s₂]), rfl, ?_⟩
  rw [isBWalk_append]
  exact ⟨_, hL, rfl, rfl⟩

end LargeIndecomposable.RayCat
