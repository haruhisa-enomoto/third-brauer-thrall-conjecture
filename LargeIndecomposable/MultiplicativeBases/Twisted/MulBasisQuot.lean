module

public import LargeIndecomposable.RayCategories.ClosedChains.ClosedChainOf
public import LargeIndecomposable.RayCategories.Quotients.ResidueQuiver

/-!
# Quotients of algebras with twisted multiplicative bases

Let `B` be a twisted multiplicative basis of `A` over a finite ray category
`P`, and `μ` a non-invertible morphism. The span of the basis elements of the
morphisms factoring through `μ` is a two-sided ideal (`RayQuiver.MulBasis.ideal`),
and `A` modulo it has a twisted multiplicative basis over the residue category
`P/μ` (`RayQuiver.MulBasis.quot`). Consequently, if that quotient is
representation-finite, `P/μ` has bounded chains
(`RayQuiver.MulBasis.chainBounded_res`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat

universe u

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]
  (B : MulBasis k P A) {a b : P} (μ : a ⟶ b)

/-- The span of the basis elements of morphisms factoring through `μ`. -/
def idealSub : Submodule k A :=
  Submodule.span k {x | ∃ (s t : P) (ν : s ⟶ t), LargeIndecomposable.FactorsThroughMorphism μ ν ∧
    x = B.elt ν}

variable {B μ}

lemma elt_mem_idealSub {s t : P} {ν : s ⟶ t} (hν : LargeIndecomposable.FactorsThroughMorphism μ ν) :
    B.elt ν ∈ B.idealSub μ :=
  Submodule.subset_span ⟨s, t, ν, hν, rfl⟩

lemma mem_top_span (x : A) : x ∈ Submodule.span k (Set.range fun ρ : NZ P ↦ B.elt ρ.2.2.1) := by
  rw [B.span]; trivial

lemma mul_mem_idealSub_left (x : A) {y : A} (hy : y ∈ B.idealSub μ) : x * y ∈ B.idealSub μ := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨s, t, ν, hν, rfl⟩ := hy
    induction mem_top_span (B := B) x using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨s', t', ρ, -⟩, rfl⟩ := hx
      by_cases h : t = s'
      · subst h
        rw [B.elt_mul]
        refine Submodule.smul_mem _ _ (elt_mem_idealSub ?_)
        obtain ⟨α, β, rfl⟩ := hν
        exact ⟨α, β ≫ ρ, by simp⟩
      · rw [B.elt_mul_ne ν ρ h]; exact Submodule.zero_mem _
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add x x' _ _ hx hx' => rw [add_mul]; exact Submodule.add_mem _ hx hx'
    | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add y y' _ _ hy hy' => rw [mul_add]; exact Submodule.add_mem _ hy hy'
  | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy

lemma mul_mem_idealSub_right {x : A} (hx : x ∈ B.idealSub μ) (y : A) : x * y ∈ B.idealSub μ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, t, ν, hν, rfl⟩ := hx
    induction mem_top_span (B := B) y using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨s', t', ρ, -⟩, rfl⟩ := hy
      by_cases h : t' = s
      · subst h
        rw [B.elt_mul]
        refine Submodule.smul_mem _ _ (elt_mem_idealSub ?_)
        obtain ⟨α, β, rfl⟩ := hν
        exact ⟨ρ ≫ α, β, by simp⟩
      · rw [B.elt_mul_ne ρ ν h]; exact Submodule.zero_mem _
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y y' _ _ hy hy' => rw [mul_add]; exact Submodule.add_mem _ hy hy'
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x x' _ _ hx hx' => rw [add_mul]; exact Submodule.add_mem _ hx hx'
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

variable (B μ) in
/-- The two-sided ideal of the morphisms factoring through `μ`. -/
def ideal : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' (B.idealSub μ) (Submodule.zero_mem _) (Submodule.add_mem _)
    (Submodule.neg_mem _) (fun {x _} hy ↦ mul_mem_idealSub_left x hy)
    (fun {_ y} hx ↦ mul_mem_idealSub_right hx y)

lemma mem_ideal {x : A} : x ∈ B.ideal μ ↔ x ∈ B.idealSub μ := TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _

lemma elt_mem_ideal {s t : P} {ν : s ⟶ t} (hν : LargeIndecomposable.FactorsThroughMorphism μ ν) :
    B.elt ν ∈ B.ideal μ :=
  mem_ideal.2 (elt_mem_idealSub hν)

lemma elt_ne_zero {s t : P} {ν : s ⟶ t} (hν : ν ≠ 0) : B.elt ν ≠ 0 := by
  have := B.basis.ne_zero ⟨s, t, ν, hν⟩
  rwa [B.basis_apply] at this

lemma ideal_ne_bot (hμ0 : μ ≠ 0) : B.ideal μ ≠ ⊥ := by
  intro h
  have := elt_mem_ideal (B := B) (μ := μ) (ν := μ) ⟨𝟙 _, 𝟙 _, by simp⟩
  rw [h, TwoSidedIdeal.mem_bot] at this
  exact elt_ne_zero hμ0 this

/-- Coordinates of elements of the ideal vanish off the morphisms factoring
through `μ`. -/
lemma coord_eq_zero {x : A} (hx : x ∈ B.ideal μ) (ν : NZ P)
    (hν : ¬LargeIndecomposable.FactorsThroughMorphism μ ν.2.2.1) : B.basis.coord ν x = 0 := by
  rw [mem_ideal] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, t, ν', hν', rfl⟩ := hx
    by_cases h0 : ν' = 0
    · subst h0; rw [B.elt_zero, map_zero]
    · classical
      rw [show B.elt ν' = B.basis ⟨s, t, ν', h0⟩ by rw [B.basis_apply], Module.Basis.coord_apply,
        Module.Basis.repr_self, Finsupp.single_apply, if_neg]
      rintro rfl
      exact hν hν'
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

/-! ### The quotient basis -/

section Quot

variable [LargeIndecomposable.IsFiniteRayCategory P]

/-- The quotient map `A → A/I`. -/
abbrev mkq (B : MulBasis k P A) (μ : a ⟶ b) : A →ₐ[k] A ⧸ (B.ideal μ).asIdeal :=
  Ideal.Quotient.mkₐ k (B.ideal μ).asIdeal

lemma mkq_eq_zero {x : A} (hx : x ∈ B.ideal μ) : mkq B μ x = 0 :=
  (Ideal.Quotient.eq_zero_iff_mem).2 (TwoSidedIdeal.mem_asIdeal.2 hx)

lemma mkq_eq_zero_iff {x : A} : mkq B μ x = 0 ↔ x ∈ B.ideal μ :=
  (Ideal.Quotient.eq_zero_iff_mem).trans TwoSidedIdeal.mem_asIdeal

/-- The lift of a morphism of `P/μ`. -/
abbrev rlift {X Y : RayCat.Res μ} (f : X ⟶ Y) : X.as ⟶ Y.as := RayCat.lift μ (x := X.as) (y := Y.as) f

lemma resF_rlift {X Y : RayCat.Res μ} (f : X ⟶ Y) : (resF μ).map (rlift f) = f := resF_lift μ f

lemma factors_rlift_iff {X Y : RayCat.Res μ} (f : X ⟶ Y) :
    LargeIndecomposable.FactorsThroughMorphism μ (rlift f) ↔ f = 0 := by
  rw [← LargeIndecomposable.rayResidueFunctor_map_eq_zero_iff]
  exact Iff.of_eq (congrArg (· = 0) (resF_rlift f))

lemma rlift_map {x y : P} (ν : x ⟶ y) (hν : ¬LargeIndecomposable.FactorsThroughMorphism μ ν) :
    rlift ((resF μ).map ν) = ν :=
  (resF_map_injective μ hν (resF_rlift _).symm).symm

variable (hμ : ¬IsIso μ)

include hμ in
lemma rlift_id (X : RayCat.Res μ) : rlift (𝟙 X) = 𝟙 X.as := by
  have h1 : ¬LargeIndecomposable.FactorsThroughMorphism μ (𝟙 X.as) :=
    LargeIndecomposable.principalZeroHomIdeal_isProper_of_not_isIso μ hμ X.as
  exact (resF_map_injective μ h1 (((resF_rlift (𝟙 X)).trans ((resF μ).map_id X.as).symm)).symm).symm

include hμ in
lemma mkq_elt_comp {X Y Z : RayCat.Res μ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    mkq B μ (B.elt (rlift f ≫ rlift g)) = mkq B μ (B.elt (rlift (f ≫ g))) := by
  have hres : (resF μ).map (rlift f ≫ rlift g) = f ≫ g := by
    rw [Functor.map_comp, resF_rlift, resF_rlift]
  by_cases hf : LargeIndecomposable.FactorsThroughMorphism μ (rlift f ≫ rlift g)
  · have h0 : f ≫ g = 0 := by
      rw [← hres]; exact (LargeIndecomposable.rayResidueFunctor_map_eq_zero_iff μ _).2 hf
    rw [mkq_eq_zero (elt_mem_ideal hf), mkq_eq_zero (elt_mem_ideal ((factors_rlift_iff _).2 h0))]
  · rw [resF_map_injective μ hf (hres.trans (resF_rlift _).symm)]

/-- The lift of a nonzero morphism of `P/μ` as a nonzero morphism of `P`. -/
def liftNZ (ν : NZ (RayCat.Res μ)) : NZ P :=
  ⟨ν.1.as, ν.2.1.as, rlift ν.2.2.1, fun h ↦ ν.2.2.2 (by
    rw [← resF_rlift ν.2.2.1, h, Functor.map_zero])⟩

lemma liftNZ_not_factors (ν : NZ (RayCat.Res μ)) :
    ¬LargeIndecomposable.FactorsThroughMorphism μ (liftNZ ν).2.2.1 :=
  fun h ↦ ν.2.2.2 ((factors_rlift_iff _).1 h)

lemma liftNZ_injective : Function.Injective (liftNZ (μ := μ)) := by
  rintro ⟨⟨x⟩, ⟨y⟩, f, hf⟩ ⟨⟨x'⟩, ⟨y'⟩, f', hf'⟩ h
  simp only [liftNZ, Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  obtain ⟨rfl, h⟩ := (Sigma.mk.inj_iff.1 (eq_of_heq h))
  have h' := congrArg Subtype.val (eq_of_heq h)
  have : f = f' := by
    have := congrArg (resF μ).map h'
    rwa [resF_rlift, resF_rlift] at this
  subst this
  rfl

variable (B μ) in
/-- **The quotient basis**: `A/I` has a twisted multiplicative basis over
`P/μ`. -/
def quot :
    letI := LargeIndecomposable.rayResidueCategory_isFiniteRayCategory μ hμ
    letI : IsRayCategory (RayCat.Res μ) := isRayCategory_of_finiteRayCategory
    letI : Fintype (RayCat.Res μ) := Fintype.ofFinite _
    letI : DecidableEq (RayCat.Res μ) := Classical.decEq _
    MulBasis k (RayCat.Res μ) (A ⧸ (B.ideal μ).asIdeal) :=
  letI := LargeIndecomposable.rayResidueCategory_isFiniteRayCategory μ hμ
  letI : IsRayCategory (RayCat.Res μ) := isRayCategory_of_finiteRayCategory
  letI : Fintype (RayCat.Res μ) := Fintype.ofFinite _
  letI : DecidableEq (RayCat.Res μ) := Classical.decEq _
  { elt f := mkq B μ (B.elt (rlift f))
    tw f g := B.tw (rlift f) (rlift g)
    elt_zero := mkq_eq_zero (elt_mem_ideal ((factors_rlift_iff 0).2 rfl))
    elt_mul f g := by
      rw [← map_mul, B.elt_mul, map_smul, mkq_elt_comp hμ]
    elt_mul_ne {X Y Y' Z} f g h := by
      rw [← map_mul, B.elt_mul_ne _ _ (fun h' ↦ h (by cases Y; cases Y'; cases h'; rfl)), map_zero]
    sum_id := by
      simp_rw [rlift_id hμ]
      rw [← map_sum]
      rw [show ∑ X : RayCat.Res μ, B.elt (𝟙 X.as) = ∑ p : P, B.elt (𝟙 p) from
        Fintype.sum_equiv ⟨fun X ↦ X.as, fun p ↦ ⟨p⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩ _ _ (fun _ ↦ rfl),
        B.sum_id, map_one]
    tw_id_left f := by rw [rlift_id hμ, B.tw_id_left]
    tw_id_right f := by rw [rlift_id hμ, B.tw_id_right]
    linearIndependent := by
      classical
      have := Fintype.ofFinite (NZ (RayCat.Res μ))
      rw [Fintype.linearIndependent_iff]
      intro g hg ν
      set y := ∑ i, g i • B.elt (rlift i.2.2.1) with hy
      have hmem : y ∈ B.ideal μ := by
        rw [← mkq_eq_zero_iff, hy, map_sum]
        simpa only [map_smul] using hg
      have hc := coord_eq_zero hmem (liftNZ ν) (liftNZ_not_factors ν)
      rw [hy, map_sum, Finset.sum_eq_single ν] at hc
      · rw [map_smul, show B.elt (rlift ν.2.2.1) = B.basis (liftNZ ν) by rw [B.basis_apply]; rfl,
          Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul,
          mul_one] at hc
        exact hc
      · intro i _ hi
        rw [map_smul, show B.elt (rlift i.2.2.1) = B.basis (liftNZ i) by rw [B.basis_apply]; rfl,
          Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
          if_neg (fun h ↦ hi (liftNZ_injective h)), smul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    span := by
      refine eq_top_iff.2 fun x hx ↦ ?_
      clear hx
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      change mkq B μ x ∈ _
      induction mem_top_span (B := B) x using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨ν, rfl⟩ := hx
        by_cases hν : LargeIndecomposable.FactorsThroughMorphism μ ν.2.2.1
        · rw [mkq_eq_zero (elt_mem_ideal hν)]; exact Submodule.zero_mem _
        · refine Submodule.subset_span ⟨⟨⟨ν.1⟩, ⟨ν.2.1⟩, (resF μ).map ν.2.2.1, fun h ↦ hν
            ((LargeIndecomposable.rayResidueFunctor_map_eq_zero_iff μ _).1 h)⟩, ?_⟩
          change mkq B μ (B.elt (rlift ((resF μ).map ν.2.2.1))) = _
          rw [rlift_map ν.2.2.1 hν]
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx }

variable (B) in
include hμ in
/-- **Bounded chains in `P/μ`** when `A/I` is representation-finite. -/
theorem chainBounded_res [Infinite k] (hfin : Statement.IsRepresentationFinite (A ⧸ (B.ideal μ).asIdeal)) :
    letI := LargeIndecomposable.rayResidueCategory_isFiniteRayCategory μ hμ
    letI : IsRayCategory (RayCat.Res μ) := isRayCategory_of_finiteRayCategory
    ChainBounded (RayCat.Res μ) := by
  letI := LargeIndecomposable.rayResidueCategory_isFiniteRayCategory μ hμ
  letI : IsRayCategory (RayCat.Res μ) := isRayCategory_of_finiteRayCategory
  letI : Fintype (RayCat.Res μ) := Fintype.ofFinite _
  letI : DecidableEq (RayCat.Res μ) := Classical.decEq _
  exact RayCat.chainBounded_of_isRepresentationFinite (B.quot μ hμ) hfin

end Quot

end MulBasis

end RayQuiver

end LargeIndecomposable
