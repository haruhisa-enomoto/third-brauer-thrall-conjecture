module

public import LargeIndecomposable.Cleaving.ClosedChains.Figure13ESupplementCompiler
public import LargeIndecomposable.Cleaving.ClosedChains.IrreducibleRepresentativeIncomparability
public import LargeIndecomposable.Cleaving.ClosedChains.OrdinaryEasyCrossSpan
public import LargeIndecomposable.Cleaving.ClosedChains.PowerAssembly

@[expose] public section

/-!
# Separation lemmas for the four BGRS Figure 13E statements

This file isolates the local algebra behind the four nonmemberships printed
after BGRS Figure 13.  On an arm, an endpoint-radical error can be absorbed
into a unit multiple of the radical generator; a transfer of that generator
would force the prohibited transit direction.  In the middle, any proper
factor-through Hom subbimodule below the `tau^2` ray is already contained in
the endpoint-radical layer, while the line through `tau` is separated by the
strict power-span drop.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.RoiterFigure13E

open LargeIndecomposable.ClosedZigzagTransfer

universe u v w

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
variable [∀ T : C, Module.Finite k (End T)]
variable [∀ T : C, IsLocalRing (End T)]
variable [∀ T : C, IsArtinianRing (End T)]

omit [IsAlgClosed k] [∀ T : C, Module.Finite k (End T)]
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)] in
private theorem twoSidedEndomorphismSpan_le_of_mem_homSubbimodule
    {X Y : C} {S : Submodule k (X ⟶ Y)}
    (hS : LargeIndecomposable.IsHomSubbimodule S)
    {f : X ⟶ Y} (hf : f ∈ S) :
    twoSidedEndomorphismSpan k f ≤ S := by
  apply Submodule.span_le.2
  rintro q ⟨a, b, rfl⟩
  exact hS.2 b (hS.1 a hf)

/-- If `alpha` allows transit but prohibits cotransit, its first composition
with the middle radical generator is separated from the full left-arm
obstruction, including endpoint-radical errors. -/
theorem leftArmSupplement_separated_of_not_allowsCotransit
    [LargeIndecomposable.HasBGRSDistributiveHomStructure k C]
    {X Y : C} (alpha : X ⟶ Y)
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (halphaT : LargeIndecomposable.AllowsTransit alpha)
    (halphaNotC : ¬ LargeIndecomposable.AllowsCotransit alpha)
    (halphaTau : alpha ≫ P.tau.asHom ≠ 0) :
    alpha ≫ P.tau.asHom ∉
      leftArmSupplementObstruction (k := k) alpha P.tau := by
  intro hmem
  rcases Submodule.mem_sup.mp hmem with ⟨r, hr, s, hs, hrs⟩
  rcases hr with ⟨c, hc, d, hd, hr⟩
  rcases hs with ⟨a, rfl⟩
  change r + a.asHom ≫ alpha = alpha ≫ P.tau.asHom at hrs
  obtain ⟨q, hcq⟩ := halphaT c
  have halpha : alpha ≠ 0 := by
    intro hzero
    apply halphaTau
    rw [hzero]
    simp
  have hq : q ∈ Ring.jacobson (End Y) :=
    target_mem_jacobson_of_source_mem_and_transfer
      halpha c q hc hcq
  let e : End Y := 1 - (q + d)
  have heJ : q + d ∈ Ring.jacobson (End Y) :=
    (Ring.jacobson (End Y)).add_mem hq hd
  have he : IsUnit e :=
    isUnit_one_sub_of_mem_jacobson heJ
  have hlanding : alpha ≫ P.tau.asHom =
      (c.asHom ≫ (alpha ≫ P.tau.asHom) +
        (alpha ≫ P.tau.asHom) ≫ d.asHom) +
          a.asHom ≫ alpha := by
    calc
      alpha ≫ P.tau.asHom = r + a.asHom ≫ alpha := hrs.symm
      _ = (c.asHom ≫ (alpha ≫ P.tau.asHom) +
          (alpha ≫ P.tau.asHom) ≫ d.asHom) +
            a.asHom ≫ alpha := by rw [hr]
  have hcqTau : c.asHom ≫ (alpha ≫ P.tau.asHom) =
      (alpha ≫ q.asHom) ≫ P.tau.asHom := by
    simpa only [Category.assoc] using
      congrArg (fun z : X ⟶ Y ↦ z ≫ P.tau.asHom) hcq
  have htransfer : a.asHom ≫ alpha =
      alpha ≫ (P.tau * e).asHom := by
    have hqcomm := congrArg End.asHom (P.mul_comm q P.tau)
    have hqTau : (alpha ≫ q.asHom) ≫ P.tau.asHom =
        (alpha ≫ P.tau.asHom) ≫ q.asHom := by
      simpa only [End.mul_def, Category.assoc] using
        congrArg (fun z : Y ⟶ Y ↦ alpha ≫ z) hqcomm.symm
    calc
      a.asHom ≫ alpha =
          alpha ≫ P.tau.asHom -
            (c.asHom ≫ (alpha ≫ P.tau.asHom) +
              (alpha ≫ P.tau.asHom) ≫ d.asHom) := by
                apply (eq_sub_iff_add_eq).2
                calc
                  a.asHom ≫ alpha +
                      (c.asHom ≫ (alpha ≫ P.tau.asHom) +
                        (alpha ≫ P.tau.asHom) ≫ d.asHom) =
                    (c.asHom ≫ (alpha ≫ P.tau.asHom) +
                        (alpha ≫ P.tau.asHom) ≫ d.asHom) +
                      a.asHom ≫ alpha := add_comm _ _
                  _ = alpha ≫ P.tau.asHom := hlanding.symm
      _ = alpha ≫ P.tau.asHom -
            ((alpha ≫ q.asHom) ≫ P.tau.asHom +
              (alpha ≫ P.tau.asHom) ≫ d.asHom) := by
                rw [hcqTau]
      _ = alpha ≫ P.tau.asHom -
            ((alpha ≫ P.tau.asHom) ≫ q.asHom +
              (alpha ≫ P.tau.asHom) ≫ d.asHom) := by
                rw [hqTau]
      _ = (alpha ≫ P.tau.asHom) ≫ e.asHom := by
                dsimp [e]
                change alpha ≫ P.tau.asHom -
                    ((alpha ≫ P.tau.asHom) ≫ q.asHom +
                      (alpha ≫ P.tau.asHom) ≫ d.asHom) =
                  (alpha ≫ P.tau.asHom) ≫
                    ((𝟙 Y) - (q.asHom + d.asHom))
                rw [Preadditive.comp_sub, Preadditive.comp_add,
                  Category.comp_id]
      _ = alpha ≫ (P.tau * e).asHom := by
                rw [P.mul_comm P.tau e, End.mul_def]
                simp only [Category.assoc]
  apply halphaNotC
  exact allowsCotransit_of_transfer_of_adjoin_eq_top
    alpha a (P.tau * e) (P.adjoin_mul_unit_eq_top e he) htransfer

/-- Source-dual arm separation: if `beta` allows cotransit but prohibits
transit, its first precomposition by the radical generator is outside the
full right-arm obstruction. -/
theorem rightArmSupplement_separated_of_not_allowsTransit
    [LargeIndecomposable.HasBGRSDistributiveHomStructure k C]
    {Y Z : C} (beta : Y ⟶ Z)
    (P : OrientedRadicalPowerParameter (k := k) Y)
    (hbetaC : LargeIndecomposable.AllowsCotransit beta)
    (hbetaNotT : ¬ LargeIndecomposable.AllowsTransit beta)
    (htauBeta : P.tau.asHom ≫ beta ≠ 0) :
    P.tau.asHom ≫ beta ∉
      rightArmSupplementObstruction (k := k) beta P.tau := by
  intro hmem
  rcases Submodule.mem_sup.mp hmem with ⟨r, hr, s, hs, hrs⟩
  rcases hr with ⟨c, hc, d, hd, hr⟩
  rcases hs with ⟨a, rfl⟩
  change r + beta ≫ a.asHom = P.tau.asHom ≫ beta at hrs
  obtain ⟨q, hdq⟩ := hbetaC d
  have hbeta : beta ≠ 0 := by
    intro hzero
    apply htauBeta
    rw [hzero]
    simp
  have hq : q ∈ Ring.jacobson (End Y) :=
    source_mem_jacobson_of_target_mem_and_transfer
      hbeta q d hd hdq
  let e : End Y := 1 - (c + q)
  have heJ : c + q ∈ Ring.jacobson (End Y) :=
    (Ring.jacobson (End Y)).add_mem hc hq
  have he : IsUnit e :=
    isUnit_one_sub_of_mem_jacobson heJ
  have hlanding : P.tau.asHom ≫ beta =
      (c.asHom ≫ (P.tau.asHom ≫ beta) +
        (P.tau.asHom ≫ beta) ≫ d.asHom) +
          beta ≫ a.asHom := by
    calc
      P.tau.asHom ≫ beta = r + beta ≫ a.asHom := hrs.symm
      _ = (c.asHom ≫ (P.tau.asHom ≫ beta) +
          (P.tau.asHom ≫ beta) ≫ d.asHom) +
            beta ≫ a.asHom := by rw [hr]
  have htransfer : (P.tau * e).asHom ≫ beta =
      beta ≫ a.asHom := by
    have hqcomm := congrArg End.asHom (P.mul_comm P.tau q)
    have hqTau : q.asHom ≫ P.tau.asHom =
        P.tau.asHom ≫ q.asHom := by
      simpa only [End.mul_def] using hqcomm
    calc
      (P.tau * e).asHom ≫ beta =
          e.asHom ≫ (P.tau.asHom ≫ beta) := by
            simp only [End.mul_def, Category.assoc]
      _ = P.tau.asHom ≫ beta -
            ((c.asHom ≫ P.tau.asHom) ≫ beta +
              (q.asHom ≫ P.tau.asHom) ≫ beta) := by
                dsimp [e]
                change ((𝟙 Y) - (c.asHom + q.asHom)) ≫
                    (P.tau.asHom ≫ beta) = _
                rw [Preadditive.sub_comp, Preadditive.add_comp,
                  Category.id_comp]
                simp only [Category.assoc]
      _ = P.tau.asHom ≫ beta -
            (c.asHom ≫ (P.tau.asHom ≫ beta) +
              P.tau.asHom ≫ (q.asHom ≫ beta)) := by
                rw [hqTau]
                simp only [Category.assoc]
      _ = P.tau.asHom ≫ beta -
            (c.asHom ≫ (P.tau.asHom ≫ beta) +
              P.tau.asHom ≫ (beta ≫ d.asHom)) := by
                rw [hdq]
      _ = beta ≫ a.asHom := by
                apply (sub_eq_iff_eq_add).2
                simpa only [Category.assoc, add_comm] using hlanding
  apply hbetaNotT
  exact allowsTransit_of_transfer_of_adjoin_eq_top
    beta (P.tau * e) a (P.adjoin_mul_unit_eq_top e he) htransfer

/-- A direct exclusion of `tau^2` from one factor-through subbimodule implies
the stronger one-sided middle supplement used by the Figure 13E coefficient
compiler. -/
theorem middleSquareSideSupplement_separated_of_not_mem_throughObject
    [LargeIndecomposable.HasBGRSDistributiveHomStructure k C]
    {X Y : C} (P : OrientedRadicalPowerParameter (k := k) Y)
    (htauSq : P.tau ^ 2 ≠ 0)
    (hnot : (P.tau ^ 2).asHom ∉
      throughObjectSubmodule (k := k) X Y) :
    (P.tau ^ 2).asHom ∉
      middleSquareSideSupplementObstruction (k := k) X Y P.tau := by
  let S : Submodule k (Y ⟶ Y) :=
    throughObjectSubmodule (k := k) X Y
  let E : Submodule k (Y ⟶ Y) :=
    endpointRadicalSubmodule (k := k) (P.tau ^ 2).asHom
  have hcomp :=
    LargeIndecomposable.HasBGRSDistributiveHomStructure.homSubbimodule_comparable
      (k := k) (C := C) S
      (twoSidedEndomorphismSpan k (P.tau ^ 2).asHom)
      (isHomSubbimodule_throughObjectSubmodule (k := k) X Y)
      (LargeIndecomposable.isHomSubbimodule_twoSidedEndomorphismSpan
        (P.tau ^ 2).asHom)
  have hSle : S ≤ twoSidedEndomorphismSpan k (P.tau ^ 2).asHom := by
    rcases hcomp with hle | hle
    · exact hle
    · exfalso
      apply hnot
      exact hle (mem_twoSidedEndomorphismSpan k (P.tau ^ 2).asHom)
  have hSlt : S < twoSidedEndomorphismSpan k (P.tau ^ 2).asHom := by
    apply lt_of_le_of_ne hSle
    intro heq
    apply hnot
    change (P.tau ^ 2).asHom ∈ S
    rw [heq]
    exact mem_twoSidedEndomorphismSpan k (P.tau ^ 2).asHom
  have hSE : S ≤ E := by
    intro q hq
    apply mem_endpointRadicalSubmodule_of_span_lt
    exact lt_of_le_of_lt
      (twoSidedEndomorphismSpan_le_of_mem_homSubbimodule
        (isHomSubbimodule_throughObjectSubmodule (k := k) X Y) hq)
      hSlt
  have hreduce : middleSquareSideSupplementObstruction
      (k := k) X Y P.tau ≤
      E ⊔ Submodule.span k ({P.tau.asHom} : Set (Y ⟶ Y)) := by
    exact sup_le le_rfl (hSE.trans le_sup_left)
  have htauSqHom : (P.tau ^ 2).asHom ≠ 0 := by
    intro hzero
    apply htauSq
    exact End.ext hzero
  intro hmem
  have hsmall : (P.tau ^ 2).asHom ∈
      E ⊔ Submodule.span k ({P.tau.asHom} : Set (Y ⟶ Y)) :=
    hreduce hmem
  obtain ⟨q : Y ⟶ Y, hq, r : Y ⟶ Y, hr, hqr⟩ :=
    Submodule.mem_sup.mp hsmall
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hr
  by_cases hc : c = 0
  · subst c
    have heq : (P.tau ^ 2).asHom = q := by
      calc
        (P.tau ^ 2).asHom = q + (0 : k) • P.tau.asHom := hqr.symm
        _ = q := by rw [zero_smul, add_zero]
    have htauE : (P.tau ^ 2).asHom ∈ E := by
      rw [heq]
      exact hq
    exact (not_mem_endpointRadicalSubmodule (k := k)
      (P.tau ^ 2).asHom htauSqHom) htauE
  · have hqspan : twoSidedEndomorphismSpan k q <
        twoSidedEndomorphismSpan k (P.tau ^ 2).asHom :=
      span_lt_of_mem_endpointRadicalSubmodule
        (k := k) htauSqHom hq
    have hsubspan :=
      twoSidedEndomorphismSpan_sub_smul_eq_of_lt
        (k := k) (P.tau ^ 2).asHom q 1 hqspan
    have hsubspan' :
        twoSidedEndomorphismSpan k ((P.tau ^ 2).asHom - q) =
          twoSidedEndomorphismSpan k (P.tau ^ 2).asHom := by
      simpa only [one_smul] using hsubspan
    have hsub : (P.tau ^ 2).asHom - q = c • P.tau.asHom := by
      rw [← hqr]
      module
    have hscalar : twoSidedEndomorphismSpan k (c • P.tau.asHom) =
        twoSidedEndomorphismSpan k P.tau.asHom := by
      apply le_antisymm
      · apply twoSidedEndomorphismSpan_le_of_mem
        exact (twoSidedEndomorphismSpan k P.tau.asHom).smul_mem c
          (mem_twoSidedEndomorphismSpan k P.tau.asHom)
      · apply twoSidedEndomorphismSpan_le_of_mem
        let T := twoSidedEndomorphismSpan k (c • P.tau.asHom)
        have hmemc : c⁻¹ • (c • P.tau.asHom) ∈ T :=
          T.smul_mem c⁻¹
            (mem_twoSidedEndomorphismSpan k (c • P.tau.asHom))
        have hrescale : c⁻¹ • (c • P.tau.asHom) = P.tau.asHom := by
          rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
        have htauT : P.tau.asHom ∈ T := hrescale ▸ hmemc
        exact htauT
    have hpowers : twoSidedEndomorphismSpan k (P.tau ^ 2).asHom <
        twoSidedEndomorphismSpan k P.tau.asHom := by
      simpa only [pow_one] using P.power_succ_span_lt 1
        (by simpa only [pow_one] using P.ne_zero)
    have heq : twoSidedEndomorphismSpan k (P.tau ^ 2).asHom =
        twoSidedEndomorphismSpan k P.tau.asHom := by
      rw [← hsubspan', hsub, hscalar]
    exact hpowers.ne heq

end LargeIndecomposable.RoiterFigure13E
