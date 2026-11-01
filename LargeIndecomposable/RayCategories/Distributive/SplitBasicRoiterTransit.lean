module

public import LargeIndecomposable.RayCategories.Distributive.SplitBasicRaySocle
public import LargeIndecomposable.RayCategories.RoiterVanishing.RoiterTransit
public import LargeIndecomposable.Cleaving.ClosedChains.RadicalPowerParameter

@[expose] public section

/-!
# Roiter's rank consequence for split-basic projective categories

BGRS 1.5 deduces the one-dimensional middle-sandwich conclusion from the
literal square-annihilation alternative.  A morphism which prohibits
cotransit transfers source-radical coefficients into the square of the target
radical; dually, a morphism which prohibits transit transfers target-radical
coefficients into the square of the source radical.  Thus either square
alternative puts the entire middle-sandwich range in an endpoint bimodule
socle, whose dimension is at most one by distributivity.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory

universe u v x

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

variable [LargeIndecomposable.HasBGRSDistributiveHomStructure
  k S.ProjectiveCategory]

/-- A morphism which prohibits cotransit sends every source-radical
coefficient across to the square of the target radical.  This is the
source-to-target half of the strict inclusion displayed in BGRS 1.5. -/
theorem exists_target_jacobson_sq_transfer_of_not_allowsCotransit
    {i j : S.ProjectiveCategory} (f : i ⟶ j)
    (hnot : ¬ LargeIndecomposable.AllowsCotransit f)
    (a : Ring.jacobson (End i)) :
    ∃ b : End j, b ∈ (Ring.jacobson (End j)) ^ 2 ∧
      a.1.asHom ≫ f = f ≫ b.asHom := by
  letI : Module.Finite k (End j) := by
    change Module.Finite k (j ⟶ j)
    infer_instance
  have hf0 : f ≠ 0 := by
    intro hzero
    apply hnot
    subst f
    intro b
    exact ⟨0, by simp⟩
  have hfT : LargeIndecomposable.AllowsTransit f := by
    rcases
        LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
          (k := k) (C := S.ProjectiveCategory) f with hfT | hfC
    · exact hfT
    · exact (hnot hfC).elim
  obtain ⟨b, hab⟩ :=
    LargeIndecomposable.exists_jacobson_right_of_allowsTransit
      hf0 hfT a
  by_cases hb0 : b.1 = 0
  · refine ⟨0, (Ring.jacobson (End j) ^ 2).zero_mem, ?_⟩
    simpa [hb0] using hab
  let P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) j :=
    Classical.choice
      (LargeIndecomposable.ClosedZigzagTransfer.nonempty_orientedRadicalPowerParameter_of_nonzero_radical
        (k := k) (C := S.ProjectiveCategory) j b.1 b.2 hb0)
  obtain ⟨n, hn, e, he, hbe⟩ :=
    P.cotransitData.factors b.1 b.2 hb0
  have hbEq : b.1 = P.tau ^ n * e := by
    change b.1.asHom = (P.tau ^ n * e).asHom
    simpa only [End.mul_def] using hbe
  have htransfer :
      a.1.asHom ≫ f = f ≫ (P.tau ^ n * e).asHom := by
    rw [← hbEq]
    exact hab
  have hn2 : 2 ≤ n :=
    LargeIndecomposable.ClosedZigzagTransfer.two_le_exponent_of_transfer_of_not_allowsCotransit
      P f a.1 n hn e he htransfer hnot
  have hpow : P.tau ^ n ∈ (Ring.jacobson (End j)) ^ 2 :=
    Ideal.pow_le_pow_right hn2 (Ideal.pow_mem_pow P.mem_jacobson n)
  refine ⟨b.1, ?_, hab⟩
  rw [hbEq]
  exact (Ring.jacobson (End j) ^ 2).mul_mem_right e hpow

/-- A morphism which prohibits transit sends every target-radical
coefficient across to the square of the source radical.  This is the dual
strict inclusion displayed in BGRS 1.5. -/
theorem exists_source_jacobson_sq_transfer_of_not_allowsTransit
    {i j : S.ProjectiveCategory} (f : i ⟶ j)
    (hnot : ¬ LargeIndecomposable.AllowsTransit f)
    (b : Ring.jacobson (End j)) :
    ∃ a : End i, a ∈ (Ring.jacobson (End i)) ^ 2 ∧
      f ≫ b.1.asHom = a.asHom ≫ f := by
  letI : Module.Finite k (End i) := by
    change Module.Finite k (i ⟶ i)
    infer_instance
  have hf0 : f ≠ 0 := by
    intro hzero
    apply hnot
    subst f
    intro a
    exact ⟨0, by simp⟩
  have hfC : LargeIndecomposable.AllowsCotransit f := by
    rcases
        LargeIndecomposable.HasBGRSDistributiveHomStructure.transit_or_cotransit
          (k := k) (C := S.ProjectiveCategory) f with hfT | hfC
    · exact (hnot hfT).elim
    · exact hfC
  obtain ⟨a, hba⟩ :=
    LargeIndecomposable.exists_jacobson_left_of_allowsCotransit
      hf0 hfC b
  by_cases ha0 : a.1 = 0
  · refine ⟨0, (Ring.jacobson (End i) ^ 2).zero_mem, ?_⟩
    simpa [ha0] using hba
  let P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) i :=
    Classical.choice
      (LargeIndecomposable.ClosedZigzagTransfer.nonempty_orientedRadicalPowerParameter_of_nonzero_radical
        (k := k) (C := S.ProjectiveCategory) i a.1 a.2 ha0)
  obtain ⟨n, hn, e, he, hae⟩ :=
    P.transitData.factors a.1 a.2 ha0
  have haEq : a.1 = e * P.tau ^ n := by
    change a.1.asHom = (e * P.tau ^ n).asHom
    simpa only [End.mul_def] using hae
  have htransfer :
      (e * P.tau ^ n).asHom ≫ f = f ≫ b.1.asHom := by
    rw [← haEq]
    exact hba.symm
  have hn2 : 2 ≤ n :=
    LargeIndecomposable.ClosedZigzagTransfer.two_le_exponent_of_transfer_of_not_allowsTransit
      P f b.1 n hn e he htransfer hnot
  have hpow : P.tau ^ n ∈ (Ring.jacobson (End i)) ^ 2 :=
    Ideal.pow_le_pow_right hn2 (Ideal.pow_mem_pow P.mem_jacobson n)
  refine ⟨a.1, ?_, hba⟩
  rw [haEq]
  exact (Ring.jacobson (End i) ^ 2).mul_mem_left e hpow

/-- The exact radical-parameter reduction at the start of BGRS Section 4.1.
If neither half of Roiter's square alternative holds, one may choose a single
generator `tau` of the middle endomorphism radical for which both displayed
square composites are nonzero. -/
theorem exists_radicalPowerParameter_sq_nonzero_of_not_squareAlternative
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hleft : ¬ LargeIndecomposable.LeftJacobsonSquareAnnihilates f)
    (hright : ¬ LargeIndecomposable.RightJacobsonSquareAnnihilates g) :
    ∃ P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
        (k := k) Y,
      f ≫ (P.tau ^ 2).asHom ≠ 0 ∧
        (P.tau ^ 2).asHom ≫ g ≠ 0 := by
  rw [LargeIndecomposable.LeftJacobsonSquareAnnihilates] at hleft
  push Not at hleft
  obtain ⟨a, haSq, hfa⟩ := hleft
  rw [LargeIndecomposable.RightJacobsonSquareAnnihilates] at hright
  push Not at hright
  obtain ⟨b, hbSq, hbg⟩ := hright
  have haJ : a ∈ Ring.jacobson (End Y) :=
    Ideal.pow_le_self (by omega) haSq
  have hbJ : b ∈ Ring.jacobson (End Y) :=
    Ideal.pow_le_self (by omega) hbSq
  have ha0 : a ≠ 0 := by
    intro ha
    apply hfa
    rw [ha]
    change f ≫ (0 : Y ⟶ Y) = 0
    exact CategoryTheory.Limits.comp_zero
  have hb0 : b ≠ 0 := by
    intro hb
    apply hbg
    rw [hb]
    change (0 : Y ⟶ Y) ≫ g = 0
    exact CategoryTheory.Limits.zero_comp
  letI : Module.Finite k (End Y) := by
    change Module.Finite k (Y ⟶ Y)
    infer_instance
  let P : LargeIndecomposable.ClosedZigzagTransfer.OrientedRadicalPowerParameter
      (k := k) Y :=
    Classical.choice
      (LargeIndecomposable.ClosedZigzagTransfer.nonempty_orientedRadicalPowerParameter_of_nonzero_radical
        (k := k) (C := S.ProjectiveCategory) Y a haJ ha0)
  obtain ⟨m, hm, e, he, hae⟩ := P.transitData.factors a haJ ha0
  have hm2 : 2 ≤ m :=
    P.two_le_transitExponent_of_mem_sq haSq ha0 m hm e he hae
  obtain ⟨n, hn, d, hd, hbd⟩ := P.cotransitData.factors b hbJ hb0
  have hn2 : 2 ≤ n :=
    P.two_le_cotransitExponent_of_mem_sq hbSq hb0 n hn d hd hbd
  refine ⟨P, ?_, ?_⟩
  · intro hzero
    apply hfa
    have hpow : (P.tau ^ m).asHom =
        (P.tau ^ 2).asHom ≫ (P.tau ^ (m - 2)).asHom := by
      have hmEq : m = (m - 2) + 2 := by omega
      calc
        (P.tau ^ m).asHom = (P.tau ^ ((m - 2) + 2)).asHom := by
          exact congrArg (fun q : ℕ ↦ (P.tau ^ q).asHom) hmEq
        _ = (P.tau ^ 2).asHom ≫
            (P.tau ^ (m - 2)).asHom := by rw [pow_add, End.mul_def]
    calc
      f ≫ a.asHom = f ≫ ((P.tau ^ m).asHom ≫ e.asHom) := by rw [hae]
      _ = ((f ≫ (P.tau ^ 2).asHom) ≫
            (P.tau ^ (m - 2)).asHom) ≫ e.asHom := by
          rw [hpow]
          simp only [Category.assoc]
      _ = 0 := by rw [hzero]; simp
  · intro hzero
    apply hbg
    have hpow : (P.tau ^ n).asHom =
        (P.tau ^ (n - 2)).asHom ≫ (P.tau ^ 2).asHom := by
      have hnEq : n = 2 + (n - 2) := by omega
      calc
        (P.tau ^ n).asHom = (P.tau ^ (2 + (n - 2))).asHom := by
          exact congrArg (fun q : ℕ ↦ (P.tau ^ q).asHom) hnEq
        _ = (P.tau ^ (n - 2)).asHom ≫
            (P.tau ^ 2).asHom := by rw [pow_add, End.mul_def]
    calc
      b.asHom ≫ g = (d.asHom ≫ (P.tau ^ n).asHom) ≫ g := by rw [hbd]
      _ = (d.asHom ≫ (P.tau ^ (n - 2)).asHom) ≫
            ((P.tau ^ 2).asHom ≫ g) := by
          rw [hpow]
          simp only [Category.assoc]
      _ = 0 := by rw [hzero]; simp

/-- Under either half of Roiter's square alternative, every middle
endomorphism sandwich lies in the endpoint bimodule socle. -/
theorem middleEndomorphismSandwich_isEndpointSocleMorphism
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ¬ LargeIndecomposable.AllowsCotransit f)
    (hg : ¬ LargeIndecomposable.AllowsTransit g)
    (hsquare : LargeIndecomposable.LeftJacobsonSquareAnnihilates f ∨
      LargeIndecomposable.RightJacobsonSquareAnnihilates g)
    (m : End Y) :
    S.IsEndpointSocleMorphism
      (LargeIndecomposable.middleEndomorphismSandwich (k := k) f g m) := by
  rcases hsquare with hleft | hright
  · constructor
    · intro a ha
      obtain ⟨q, hqJ, haq⟩ :=
        exists_target_jacobson_sq_transfer_of_not_allowsCotransit
          S f hf ⟨a, ha⟩
      let qm : End Y := End.of (q.asHom ≫ m.asHom)
      have hqmJ : qm ∈ (Ring.jacobson (End Y)) ^ 2 := by
        change m * q ∈ (Ring.jacobson (End Y)) ^ 2
        exact (Ring.jacobson (End Y) ^ 2).mul_mem_left m hqJ
      have hkill : f ≫ qm.asHom = 0 := hleft qm hqmJ
      change a.asHom ≫ ((f ≫ m.asHom) ≫ g) = 0
      calc
        a.asHom ≫ ((f ≫ m.asHom) ≫ g) =
            (((a.asHom ≫ f) ≫ m.asHom) ≫ g) := by
          simp only [Category.assoc]
        _ = (((f ≫ q.asHom) ≫ m.asHom) ≫ g) := by rw [haq]
        _ = (f ≫ qm.asHom) ≫ g := by
          simp only [qm, Category.assoc]
        _ = 0 := by rw [hkill]; simp
    · intro b hb
      obtain ⟨q, hqJ, hbq⟩ :=
        exists_source_jacobson_sq_transfer_of_not_allowsTransit
          S g hg ⟨b, hb⟩
      let mq : End Y := End.of (m.asHom ≫ q.asHom)
      have hmqJ : mq ∈ (Ring.jacobson (End Y)) ^ 2 := by
        change q * m ∈ (Ring.jacobson (End Y)) ^ 2
        exact (Ring.jacobson (End Y) ^ 2).mul_mem_right m hqJ
      have hkill : f ≫ mq.asHom = 0 := hleft mq hmqJ
      change ((f ≫ m.asHom) ≫ g) ≫ b.asHom = 0
      calc
        ((f ≫ m.asHom) ≫ g) ≫ b.asHom =
            (f ≫ m.asHom) ≫ (g ≫ b.asHom) := by
          rw [Category.assoc]
        _ = (f ≫ m.asHom) ≫ (q.asHom ≫ g) := by rw [hbq]
        _ = (f ≫ mq.asHom) ≫ g := by
          simp only [mq, Category.assoc]
        _ = 0 := by rw [hkill]; simp
  · constructor
    · intro a ha
      obtain ⟨q, hqJ, haq⟩ :=
        exists_target_jacobson_sq_transfer_of_not_allowsCotransit
          S f hf ⟨a, ha⟩
      let qm : End Y := End.of (q.asHom ≫ m.asHom)
      have hqmJ : qm ∈ (Ring.jacobson (End Y)) ^ 2 := by
        change m * q ∈ (Ring.jacobson (End Y)) ^ 2
        exact (Ring.jacobson (End Y) ^ 2).mul_mem_left m hqJ
      have hkill : qm.asHom ≫ g = 0 := hright qm hqmJ
      change a.asHom ≫ ((f ≫ m.asHom) ≫ g) = 0
      calc
        a.asHom ≫ ((f ≫ m.asHom) ≫ g) =
            (((a.asHom ≫ f) ≫ m.asHom) ≫ g) := by
          simp only [Category.assoc]
        _ = (((f ≫ q.asHom) ≫ m.asHom) ≫ g) := by rw [haq]
        _ = f ≫ (qm.asHom ≫ g) := by
          simp only [qm, Category.assoc]
        _ = 0 := by rw [hkill]; simp
    · intro b hb
      obtain ⟨q, hqJ, hbq⟩ :=
        exists_source_jacobson_sq_transfer_of_not_allowsTransit
          S g hg ⟨b, hb⟩
      let mq : End Y := End.of (m.asHom ≫ q.asHom)
      have hmqJ : mq ∈ (Ring.jacobson (End Y)) ^ 2 := by
        change q * m ∈ (Ring.jacobson (End Y)) ^ 2
        exact (Ring.jacobson (End Y) ^ 2).mul_mem_right m hqJ
      have hkill : mq.asHom ≫ g = 0 := hright mq hmqJ
      change ((f ≫ m.asHom) ≫ g) ≫ b.asHom = 0
      calc
        ((f ≫ m.asHom) ≫ g) ≫ b.asHom =
            (f ≫ m.asHom) ≫ (g ≫ b.asHom) := by
          rw [Category.assoc]
        _ = (f ≫ m.asHom) ≫ (q.asHom ≫ g) := by rw [hbq]
        _ = f ≫ (mq.asHom ≫ g) := by
          simp only [mq, Category.assoc]
        _ = 0 := by rw [hkill]; simp

/-- BGRS 1.5's stated rank consequence, derived from its literal square
alternative in a split-basic distributive primitive-projective category. -/
theorem middleEndomorphismSandwich_finrank_le_one_of_squareAlternative
    {X Y Z : S.ProjectiveCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ¬ LargeIndecomposable.AllowsCotransit f)
    (hg : ¬ LargeIndecomposable.AllowsTransit g)
    (hsquare : LargeIndecomposable.LeftJacobsonSquareAnnihilates f ∨
      LargeIndecomposable.RightJacobsonSquareAnnihilates g) :
    Module.finrank k (LinearMap.range
      (LargeIndecomposable.middleEndomorphismSandwich (k := k) f g)) ≤ 1 := by
  let R := LinearMap.range
    (LargeIndecomposable.middleEndomorphismSandwich (k := k) f g)
  have hle : R ≤ S.endpointSocleSubmodule X Z := by
    rintro h ⟨m, rfl⟩
    exact middleEndomorphismSandwich_isEndpointSocleMorphism
      S f g hf hg hsquare m
  exact (Submodule.finrank_mono hle).trans
    (S.endpointSocleSubmodule_finrank_le_one X Z)

/-- For split-basic primitive projectives, the literal square alternative is
enough to install exactly the rank-only Roiter interface used by BGRS 4.2. -/
theorem hasRoiterTransitRankBoundOfSquareAlternative
    (hsquare : ∀ {X Y Z : S.ProjectiveCategory}
      (f : X ⟶ Y) (g : Y ⟶ Z),
      ¬ LargeIndecomposable.AllowsCotransit f →
      ¬ LargeIndecomposable.AllowsTransit g →
      LargeIndecomposable.LeftJacobsonSquareAnnihilates f ∨
        LargeIndecomposable.RightJacobsonSquareAnnihilates g) :
    LargeIndecomposable.HasRoiterTransitRankBound
      k S.ProjectiveCategory where
  middle_finrank_le_one f g hf hg :=
    middleEndomorphismSandwich_finrank_le_one_of_squareAlternative
      S f g hf hg (hsquare f g hf hg)

/-- The class-form bridge: once Figure 13 supplies Roiter's literal square
alternative, the rank interface used by critical-path propagation is
automatic. -/
noncomputable instance hasRoiterTransitRankBound_of_squareAlternative
    [LargeIndecomposable.HasRoiterTransitSquareAlternative
      k S.ProjectiveCategory] :
    LargeIndecomposable.HasRoiterTransitRankBound
      k S.ProjectiveCategory :=
  hasRoiterTransitRankBoundOfSquareAlternative S
    (fun f g hf hg ↦
      LargeIndecomposable.HasRoiterTransitSquareAlternative.square_alternative
        (k := k) (C := S.ProjectiveCategory) f g hf hg)

end LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory
