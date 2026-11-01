module

public import LargeIndecomposable.Coverings.UniversalCover.GCoverFund
public import LargeIndecomposable.FundamentalGroups.Basic.FreePi
public import LargeIndecomposable.Foundations.Group.FreeResFin
public import LargeIndecomposable.RayCategories.Basic.LoopFree

/-!
# Loop-free finite covers

A ray category is *loop-free* when every nonzero endomorphism has trivial homotopy class. A
finite connected chain-bounded ray category with cancellation has a free fundamental group
(`isFreeGroup_end_fund`), free groups are residually finite (`FreeRF.exists_finite_quotient`),
so some finite quotient `φ` of `π₁(P, x₀)` is nontrivial on the finitely many nontrivial classes
of nonzero endomorphisms. The Galois cover for the voltage `f ↦ φ([ℓ_y f ℓ_z⁻¹])⁻¹` is then a
finite loop-free ray category (`exists_loopFree_gcover`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits GCover

/-- A ray category satisfies the basic finite ray axioms. -/
theorem isFiniteRayCategory0_of_ray {C : Type*} [Category C] [HasZeroMorphisms C]
    [IsRayCategory C] : LargeIndecomposable.IsFiniteRayCategory0 C where
  id_ne_zero := IsRayCategory.id_ne_zero
  hom_finite := IsRayCategory.finite_hom
  endomorphism_nilpotent {x} f hf := by
    obtain ⟨n, hn⟩ := IsRayCategory.nil x f hf
    refine ⟨n, Nat.pos_of_ne_zero fun h0 ↦ ?_, (rpow_eq_pow f n).symm.trans hn⟩
    subst h0
    exact IsRayCategory.id_ne_zero x hn
  skeletal h := IsRayCategory.skeletal h

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

section Volt

variable {x₀ : P} (ℓ : ∀ y : P, vtx x₀ ⟶ vtx y) {H : Type} [Group H] (φ : End (vtx x₀) →* H)

/-- The class of a nonzero morphism, conjugated to a loop at `x₀`. -/
def loopCls {y z : P} (f : y ⟶ z) (hf : f ≠ 0) : End (vtx x₀) :=
  ℓ y ≫ cls f hf ≫ inv (ℓ z)

lemma loopCls_comp {y z t : P} (f : y ⟶ z) (g : z ⟶ t) (hfg : f ≫ g ≠ 0) (hf : f ≠ 0)
    (hg : g ≠ 0) : loopCls ℓ (f ≫ g) hfg = loopCls ℓ g hg * loopCls ℓ f hf := by
  rw [End.mul_def]
  unfold loopCls
  rw [cls_comp f g hfg]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]

open Classical in
/-- The voltage of a finite quotient of the fundamental group. -/
def volt : Voltage P H where
  w f := if hf : f = 0 then 1 else (φ (loopCls ℓ f hf))⁻¹
  w_id x := by
    rw [dif_neg (IsRayCategory.id_ne_zero x)]
    have : loopCls ℓ (𝟙 x) (IsRayCategory.id_ne_zero x) = 1 := by
      unfold loopCls
      rw [cls_id, Category.id_comp, IsIso.hom_inv_id]
      rfl
    rw [this, map_one, inv_one]
  w_comp f g hfg := by
    have hf : f ≠ 0 := fun h ↦ hfg (by rw [h, zero_comp])
    have hg : g ≠ 0 := fun h ↦ hfg (by rw [h, comp_zero])
    rw [dif_neg hfg, dif_neg hf, dif_neg hg, loopCls_comp ℓ f g hfg hf hg, map_mul, mul_inv_rev]

open Classical in
lemma volt_w {y z : P} (f : y ⟶ z) (hf : f ≠ 0) :
    (volt ℓ φ).w f = (φ (loopCls ℓ f hf))⁻¹ := by
  change (if hf : f = 0 then 1 else _) = _
  rw [dif_neg hf]

/-- **The Galois cover is loop-free** when `φ` detects the nontrivial loop classes. -/
theorem loopFree_gcover {s : Finset (End (vtx x₀))}
    (hs : ∀ (y : P) (f : y ⟶ y) (hf : f ≠ 0), loopCls ℓ f hf ≠ 1 → loopCls ℓ f hf ∈ s)
    (hφ : ∀ g ∈ s, φ g ≠ 1) : LoopFree (GCover (volt ℓ φ)) := by
  intro a e he
  apply cls_eq_id_of_proj e he
  have hne := val_ne_zero he
  have h1 := h_eq e he
  rw [volt_w ℓ φ _ hne] at h1
  have hw : φ (loopCls ℓ (val e) hne) = 1 := by
    have := left_eq_mul.1 h1
    exact inv_eq_one.1 this
  by_contra hc
  have hl : loopCls ℓ (val e) hne ≠ 1 := by
    intro h2
    apply hc
    unfold loopCls at h2
    have h3 : ℓ a.y ≫ cls (val e) hne ≫ inv (ℓ a.y) = 𝟙 _ := h2
    have h4 := congrArg (fun t ↦ inv (ℓ a.y) ≫ t ≫ ℓ a.y) h3
    simpa using h4
  exact hφ _ (hs _ _ _ hl) hw

end Volt

/-- **Loop-free finite covers exist.** -/
theorem exists_loopFree_gcover [Finite P] (x₀ : P) (hfree : IsFreeGroup (End (vtx x₀)))
    (ℓ : ∀ y : P, vtx x₀ ⟶ vtx y) :
    ∃ (H : Type) (_ : Group H) (_ : Finite H) (φ : End (vtx x₀) →* H),
      LoopFree (GCover (volt ℓ φ)) := by
  classical
  let T : Set (End (vtx x₀)) :=
    {g | g ≠ 1 ∧ ∃ (y : P) (f : y ⟶ y) (hf : f ≠ 0), g = loopCls ℓ f hf}
  have hT : T.Finite := by
    have : ∀ y : P, Finite {f : y ⟶ y // f ≠ 0} := fun y ↦
      have := IsRayCategory.finite_hom y y
      Subtype.finite
    refine (Set.finite_range fun p : (Σ y : P, {f : y ⟶ y // f ≠ 0}) ↦
      loopCls ℓ p.2.1 p.2.2).subset ?_
    rintro g ⟨-, y, f, hf, rfl⟩
    exact ⟨⟨y, f, hf⟩, rfl⟩
  obtain ⟨H, _, _, φ, hφ⟩ := FreeRF.exists_finite_quotient hT.toFinset
    fun g hg ↦ ((Set.Finite.mem_toFinset hT).1 hg).1
  exact ⟨H, inferInstance, inferInstance, φ, loopFree_gcover ℓ φ
    (fun y f hf hne ↦ (Set.Finite.mem_toFinset hT).2 ⟨hne, y, f, hf, rfl⟩) hφ⟩

end LargeIndecomposable.RayCat
