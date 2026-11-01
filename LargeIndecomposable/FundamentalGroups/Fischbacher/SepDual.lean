module

public import LargeIndecomposable.FundamentalGroups.Basic.CocycleExtendMax

/-!
# The separation criterion at a minimal point

The dual of `sepComp_of_coboundary`, via the opposite category: if `c` is minimal in a set `D`
on which every cocycle is a coboundary, two arrows out of `c` whose targets are joined inside
`D \ {c}` lie in one component of the prefix order on nonzero morphisms out of `c` with targets
in `D \ {c}` (`outComp_of_coboundary`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Opposite

universe v u

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

/-- Comparability of nonzero morphisms out of `c` with target in `D \ {c}`: `g = f ≫ h`. -/
def OutLe (D : Set A) (c : A) (f g : Σ y : A, c ⟶ y) : Prop :=
  f.2 ≠ 0 ∧ g.2 ≠ 0 ∧ f.1 ∈ D ∧ g.1 ∈ D ∧ f.1 ≠ c ∧ g.1 ≠ c ∧ ∃ h : f.1 ⟶ g.1, g.2 = f.2 ≫ h

/-- The components of the prefix order on nonzero morphisms out of `c`. -/
def OutComp (D : Set A) (c : A) (f g : Σ y : A, c ⟶ y) : Prop := Relation.EqvGen (OutLe D c) f g

lemma eqvGen_map {α β : Type*} {R : α → α → Prop} {S : β → β → Prop} (F : α → β)
    (hF : ∀ a b, R a b → S (F a) (F b)) {a b : α} (h : Relation.EqvGen R a b) :
    Relation.EqvGen S (F a) (F b) := by
  induction h with
  | rel _ _ h => exact .rel _ _ (hF _ _ h)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

variable [IsRayCategory A]

/-- **The separation criterion at a minimal point.** -/
theorem outComp_of_coboundary {D : Set A} {c : A} (hc : c ∈ D)
    (hmin : ∀ {y : RayVert A} (_ : y ⟶ RayVert.mk c), y.out ∉ D)
    (hcob : ∀ c' : ArrowWeight A, IsCocycleOn D c' → IsCoboundaryOn D c') {t₁ t₂ : A}
    (e₁ : RayVert.mk c ⟶ RayVert.mk t₁) (e₂ : RayVert.mk c ⟶ RayVert.mk t₂) (ht₁ : t₁ ∈ D)
    (ht₂ : t₂ ∈ D) (h₁ : t₁ ≠ c) (h₂ : t₂ ≠ c) (hconn : Relation.EqvGen (AdjOff D c) t₁ t₂) :
    OutComp D c ⟨t₁, e₁.1⟩ ⟨t₂, e₂.1⟩ := by
  have hb : op c ∈ opSet D := hc
  have hmax : ∀ {Y : RayVert Aᵒᵖ} (_ : RayVert.mk (op c) ⟶ Y), Y.out ∉ opSet D :=
    fun E ↦ hmin (unrevArr E)
  have hcob' : ∀ cop : ArrowWeight Aᵒᵖ, IsCocycleOn (opSet D) cop →
      IsCoboundaryOn (opSet D) cop := by
    intro cop hcop
    let c' : ArrowWeight A := fun e ↦ cop (revArr e)
    have hc' : IsCocycleOn D c' := by
      intro x y p q hp hq hpq h0
      rw [← pathIn_revPath] at hp hq
      have h := hcop (revPath p) (revPath q) hp hq
        (by rw [pathVal_revPath, pathVal_revPath, hpq])
        (by rw [pathVal_revPath]; exact fun h ↦ h0 (Quiver.Hom.op_inj h))
      rwa [pathWeight_revPath, pathWeight_revPath] at h
    obtain ⟨φ, hφ⟩ := hcob c' hc'
    refine ⟨fun X ↦ -φ X.unop, fun {X Y} E hX hY ↦ ?_⟩
    have := hφ (unrevArr E) hY hX
    change cop E = -φ Y.out.unop - -φ X.out.unop
    have hE : cop E = c' (unrevArr E) := rfl
    have h2 : c' (unrevArr E) = φ X.out.unop - φ Y.out.unop := this
    rw [hE, h2]
    ring
  have hconn' : Relation.EqvGen (AdjOff (opSet D) (op c)) (op t₁) (op t₂) := by
    refine eqvGen_map (fun s : A ↦ op s) (fun s t h ↦ ?_) hconn
    obtain ⟨hs, ht, hsc, htc, harr⟩ := h
    refine ⟨hs, ht, fun h ↦ hsc (op_injective h), fun h ↦ htc (op_injective h), ?_⟩
    rcases harr with h | h
    · obtain ⟨e⟩ := h
      exact Or.inr ⟨revArr e⟩
    · obtain ⟨e⟩ := h
      exact Or.inl ⟨revArr e⟩
  have hsep := sepComp_of_coboundary hb hmax hcob' (revArr e₁) (revArr e₂) ht₁ ht₂
    (fun h ↦ h₁ (op_injective h)) (fun h ↦ h₂ (op_injective h)) hconn'
  refine eqvGen_map (fun F : (Σ X : Aᵒᵖ, X ⟶ op c) ↦ (⟨F.1.unop, F.2.unop⟩ : Σ y : A, c ⟶ y))
    (fun f g h ↦ ?_) hsep
  obtain ⟨hf, hg, hfD, hgD, hfc, hgc, k, hk⟩ := h
  refine ⟨fun h ↦ hf (Quiver.Hom.unop_inj (by rw [unop_zero]; exact h)),
    fun h ↦ hg (Quiver.Hom.unop_inj (by rw [unop_zero]; exact h)), hfD, hgD,
    fun h ↦ hfc (unop_injective h), fun h ↦ hgc (unop_injective h), k.unop, ?_⟩
  change g.2.unop = f.2.unop ≫ k.unop
  rw [hk, unop_comp]

end LargeIndecomposable.RayCat
