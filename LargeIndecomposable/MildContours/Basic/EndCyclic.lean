module

public import LargeIndecomposable.MildContours.Basic.Setup
public import LargeIndecomposable.Cleaving.ClosedChains.RadicalPowerParameter

/-!
# Cyclic endomorphism monoids (ray category axiom (d))

`EndCyclic P`: at each object the non-invertible endomorphisms are the positive
powers of one endomorphism `π(x)`. This holds for the ray category of a split
basic distributive algebra (`SplitBasicData.endCyclic`), with `π(x)` the ray
of a radical parameter (`OrientedRadicalPowerParameter`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

/-- Ray category axiom (d): cyclic endomorphism monoids. -/
def EndCyclic (P : Type*) [Category P] : Prop :=
  ∀ x : P, ∃ π : x ⟶ x, ∀ e : x ⟶ x, ¬IsIso e → ∃ n, 0 < n ∧ e = rpow π n

/-- Axiom (d) passes to the small model. -/
theorem EndCyclic.small {P : Type} [Category P] [HasZeroMorphisms P] [LocallySmall.{0} P]
    (h : EndCyclic P) : EndCyclic (RaySmall.{0} P) := by
  intro X
  obtain ⟨π, hπ⟩ := h X.as
  refine ⟨RaySmall.sh.{0} π, fun e he ↦ ?_⟩
  have he' : ¬IsIso ((RaySmall.sh.{0}).symm e) := fun hi ↦ he (by
    rw [← (RaySmall.sh.{0}).apply_symm_apply e]; exact (RaySmall.isIso_sh_iff _).2 hi)
  obtain ⟨n, hn, hen⟩ := hπ _ he'
  refine ⟨n, hn, ?_⟩
  rw [RaySmall.sh_rpow, ← hen, Equiv.apply_symm_apply]

end RayCat

namespace SplitBasicData

variable {k : Type u} [Field k] [IsAlgClosed k] {B : Type u} [Ring B] [Algebra k B]
  [FiniteDimensional k B] {ι : Type} [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι)
  [HasBGRSDistributiveHomStructure k S.toIdempotents.ProjectiveCategory]

/-- An endomorphism ray that is not invertible has a radical representative. -/
lemma mem_jacobson_of_not_isIso {X : S.toIdempotents.ProjectiveCategory} (a : End X)
    (ha : ¬IsIso (show (BGRSRayCategory.mk X) ⟶ (BGRSRayCategory.mk X) from unitRay a.asHom)) :
    a ∈ Ring.jacobson (End X) := by
  rw [mem_ringJacobson_iff_not_isUnit]
  rintro ⟨u, rfl⟩
  apply ha
  have h1 : (show (BGRSRayCategory.mk X) ⟶ (BGRSRayCategory.mk X) from unitRay (u : End X).asHom) =
      unitRay (𝟙 X) := by
    rw [unitRay_eq_iff]
    refine ⟨Iso.refl X, Aut.unitsEndEquivAut X u⁻¹, ?_⟩
    change 𝟙 X = 𝟙 X ≫ (u : End X).asHom ≫ ((u⁻¹ : (End X)ˣ) : End X).asHom
    rw [Category.id_comp, ← End.mul_def, Units.inv_mul]
    rfl
  rw [h1]
  exact (inferInstance : IsIso (𝟙 (BGRSRayCategory.mk X)))

/-- Powers of the ray of a radical parameter are the rays of the powers. -/
lemma rpow_unitRay {X : S.toIdempotents.ProjectiveCategory} (P : ClosedZigzagTransfer.OrientedRadicalPowerParameter (k := k) X) :
    ∀ n, rpow (show (BGRSRayCategory.mk X) ⟶ (BGRSRayCategory.mk X) from unitRay P.tau.asHom) n =
      unitRay (P.tau ^ n).asHom := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rpow_succ, ih, BGRSRayCategory.comp_unitRay]
    letI : Module.Finite k (End X) := by
      change Module.Finite k (X ⟶ X)
      infer_instance
    have hpow : (P.tau ^ (n + 1)).asHom = (P.tau ^ n).asHom ≫ P.tau.asHom := by
      rw [pow_succ', End.mul_def]
    by_cases h : (P.tau ^ n).asHom ≫ P.tau.asHom = 0
    · have h0 : bgrsRayRepresentativeProduct (P.tau ^ n).asHom P.tau.asHom = 0 := by
        unfold bgrsRayRepresentativeProduct
        split_ifs
        · rfl
        · exact h
      rw [h0, hpow, h]
    · have := ClosedZigzagTransfer.OrientedRadicalPowerParameter.bgrsProduct_postcompose_power_eq_comp
        P (P.tau ^ n).asHom 1 (by rw [pow_one]; exact h)
      rw [pow_one] at this
      rw [this, hpow]

variable [IsFiniteRayCategory S.toIdempotents.RayCategory] [Finite S.toIdempotents.RayCategory]

/-- **Axiom (d) for the ray category of a distributive algebra.** -/
theorem endCyclic_ray : EndCyclic S.toIdempotents.RayCategory := by
  letI : IsRayCategory S.toIdempotents.RayCategory := isRayCategory_of_finiteRayCategory
  rintro ⟨X⟩
  have hz : (show (BGRSRayCategory.mk X) ⟶ (BGRSRayCategory.mk X) from unitRay (0 : X ⟶ X)) = 0 :=
    rfl
  by_cases hJ : ∃ f0 : End X, f0 ∈ Ring.jacobson (End X) ∧ f0 ≠ 0
  · obtain ⟨f0, hf0J, hf0⟩ := hJ
    letI : Module.Finite k (X ⟶ X) := inferInstance
    obtain ⟨P⟩ := ClosedZigzagTransfer.nonempty_orientedRadicalPowerParameter_of_nonzero_radical
      (k := k) X f0 hf0J hf0
    refine ⟨unitRay P.tau.asHom, fun e he ↦ ?_⟩
    obtain ⟨a, rfl⟩ := unitRay_surjective _ _ e
    have haJ := S.mem_jacobson_of_not_isIso (show End X from a) he
    by_cases ha0 : (show End X from a) = 0
    · have hπ : (show (BGRSRayCategory.mk X) ⟶ (BGRSRayCategory.mk X) from unitRay P.tau.asHom) ≠
          𝟙 _ := by
        intro h
        obtain ⟨a', b', hab⟩ := (unitRay_eq_iff _ _).1 (show unitRay P.tau.asHom = unitRay (𝟙 X) from h)
        have hiso : IsIso P.tau.asHom := by
          have e1 : P.tau.asHom = a'.inv ≫ b'.inv := by
            calc P.tau.asHom = a'.inv ≫ (a'.hom ≫ P.tau.asHom ≫ b'.hom) ≫ b'.inv := by simp
              _ = a'.inv ≫ 𝟙 X ≫ b'.inv := by rw [← hab]
              _ = a'.inv ≫ b'.inv := by simp
          rw [e1]; infer_instance
        exact (mem_ringJacobson_iff_not_isUnit (R := End X) P.tau).1 P.mem_jacobson ((isUnit_iff_isIso _).2 hiso)
      obtain ⟨N, hN⟩ := IsRayCategory.nil _ _ hπ
      have hN0 : N ≠ 0 := by
        rintro rfl
        exact IsRayCategory.id_ne_zero _ hN
      refine ⟨N, Nat.pos_of_ne_zero hN0, ?_⟩
      rw [hN]
      change unitRay (show X ⟶ X from a) = _
      rw [show (show X ⟶ X from a) = 0 from ha0]
      exact hz
    · obtain ⟨n, hn, hn'⟩ := P.exists_positive_power_unitRay_eq haJ ha0
      exact ⟨n, hn, by rw [S.rpow_unitRay P, hn']⟩
  · push Not at hJ
    refine ⟨0, fun e he ↦ ⟨1, one_pos, ?_⟩⟩
    obtain ⟨a, rfl⟩ := unitRay_surjective _ _ e
    have haJ := S.mem_jacobson_of_not_isIso (show End X from a) he
    have ha0 := hJ _ haJ
    rw [rpow_succ, rpow_zero, Category.id_comp]
    change unitRay (show X ⟶ X from a) = 0
    rw [show (show X ⟶ X from a) = 0 from ha0]
    exact hz

/-- **Axiom (d) for the small ray category.** -/
theorem endCyclic [LocallySmall.{0} S.toIdempotents.RayCategory] :
    EndCyclic (RaySmall.{0} S.toIdempotents.RayCategory) :=
  (S.endCyclic_ray).small

end SplitBasicData

end LargeIndecomposable
