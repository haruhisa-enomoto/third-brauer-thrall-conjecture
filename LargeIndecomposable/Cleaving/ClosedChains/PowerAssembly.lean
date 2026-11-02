module

public import LargeIndecomposable.Cleaving.ClosedChains.SupplementRetraction
public import LargeIndecomposable.Cleaving.ClosedChains.RadicalPowerParameter
@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.ClosedZigzagTransfer

universe u x

variable {k : Type u} [Field k]
variable {C : Type x} [Category.{u} C] [Preadditive C] [Linear k C]

private theorem radicalElement_isNilpotent_agent
    {R : Type*} [Ring R] [IsArtinianRing R]
    {a : R} (ha : a ∈ Ring.jacobson R) : IsNilpotent a := by
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rw [Ideal.jacobson_bot] at hN
  refine ⟨N, ?_⟩
  have haPow : a ^ N ∈ (Ring.jacobson R) ^ N :=
    Ideal.pow_mem_pow ha N
  rw [hN] at haPow
  simpa using haPow

private theorem eq_zero_of_eq_comp_radical_agent
    {X Y : C} [IsArtinianRing (End Y)]
    {f : X ⟶ Y} {b : End Y} (hb : b ∈ Ring.jacobson (End Y))
    (h : f = f ≫ b.asHom) : f = 0 := by
  have hu : IsUnit (1 - b) :=
    (radicalElement_isNilpotent_agent hb).isUnit_one_sub
  letI : IsIso (1 - b).asHom := (isUnit_iff_isIso _).1 hu
  have hz : f ≫ (1 - b).asHom = 0 := by
    change f ≫ ((𝟙 Y) - b.asHom) = 0
    rw [Preadditive.comp_sub, Category.comp_id]
    exact sub_eq_zero.mpr h
  apply (cancel_mono (1 - b).asHom).1
  simpa using hz

private theorem eq_zero_of_eq_radical_comp_agent
    {X Y : C} [IsArtinianRing (End X)]
    {f : X ⟶ Y} {a : End X} (ha : a ∈ Ring.jacobson (End X))
    (h : f = a.asHom ≫ f) : f = 0 := by
  have hu : IsUnit (1 - a) :=
    (radicalElement_isNilpotent_agent ha).isUnit_one_sub
  letI : IsIso (1 - a).asHom := (isUnit_iff_isIso _).1 hu
  have hz : (1 - a).asHom ≫ f = 0 := by
    change ((𝟙 X) - a.asHom) ≫ f = 0
    rw [Preadditive.sub_comp, Category.id_comp]
    exact sub_eq_zero.mpr h
  apply (cancel_epi (1 - a).asHom).1
  simpa using hz

private theorem eq_zero_of_eq_comp_comp_of_isNilpotent_right_agent
    {X Y : C} {f : X ⟶ Y} (a : End X) (b : End Y)
    (hb : IsNilpotent b)
    (h : f = (a.asHom ≫ f) ≫ b.asHom) : f = 0 := by
  obtain ⟨n, hn⟩ := hb
  have hp : ∀ m : ℕ,
      f = ((a ^ m).asHom ≫ f) ≫ (b ^ m).asHom := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        calc
          f = (a.asHom ≫ f) ≫ b.asHom := h
          _ = (a.asHom ≫ (((a ^ m).asHom ≫ f) ≫
                (b ^ m).asHom)) ≫ b.asHom := by rw [← ih]
          _ = ((a ^ Nat.succ m).asHom ≫ f) ≫
                (b ^ Nat.succ m).asHom := by
              rw [pow_succ a m, pow_succ' b m, End.mul_def, End.mul_def]
              simp only [Category.assoc]
  have hz : (b ^ n).asHom = (0 : Y ⟶ Y) := congrArg End.asHom hn
  rw [hp n, hz]
  simp

private theorem eq_zero_of_eq_comp_comp_of_isNilpotent_left_agent
    {X Y : C} {f : X ⟶ Y} (a : End X) (b : End Y)
    (ha : IsNilpotent a)
    (h : f = (a.asHom ≫ f) ≫ b.asHom) : f = 0 := by
  obtain ⟨n, hn⟩ := ha
  have hp : ∀ m : ℕ,
      f = ((a ^ m).asHom ≫ f) ≫ (b ^ m).asHom := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        calc
          f = (a.asHom ≫ f) ≫ b.asHom := h
          _ = (a.asHom ≫ (((a ^ m).asHom ≫ f) ≫
                (b ^ m).asHom)) ≫ b.asHom := by rw [← ih]
          _ = ((a ^ Nat.succ m).asHom ≫ f) ≫
                (b ^ Nat.succ m).asHom := by
              rw [pow_succ a m, pow_succ' b m, End.mul_def, End.mul_def]
              simp only [Category.assoc]
  have hz : (a ^ n).asHom = (0 : X ⟶ X) := congrArg End.asHom hn
  rw [hp n, hz]
  simp

/-- A radical source coefficient which transfers across a nonzero morphism
remains radical at the target. -/
theorem target_mem_jacobson_of_source_mem_and_transfer
    {X Y : C} [IsLocalRing (End Y)]
    [IsArtinianRing (End X)] [IsArtinianRing (End Y)]
    {f : X ⟶ Y} (hf : f ≠ 0)
    (a : End X) (b : End Y) (ha : a ∈ Ring.jacobson (End X))
    (hab : a.asHom ≫ f = f ≫ b.asHom) :
    b ∈ Ring.jacobson (End Y) := by
  by_contra hb
  have hbUnit : IsUnit b := by
    by_contra hbUnit
    exact hb ((mem_ringJacobson_iff_not_isUnit (End Y) b).2 hbUnit)
  letI : IsIso b.asHom := (isUnit_iff_isIso _).1 hbUnit
  let bi : End Y := End.of (inv b.asHom)
  have hfixed : f = (a.asHom ≫ f) ≫ bi.asHom := by
    dsimp [bi]
    rw [hab, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  exact hf (eq_zero_of_eq_comp_comp_of_isNilpotent_left_agent a bi
    (radicalElement_isNilpotent_agent ha) hfixed)

/-- Target-dual transfer of Jacobson-radical membership. -/
theorem source_mem_jacobson_of_target_mem_and_transfer
    {X Y : C} [IsLocalRing (End X)]
    [IsArtinianRing (End X)] [IsArtinianRing (End Y)]
    {f : X ⟶ Y} (hf : f ≠ 0)
    (a : End X) (b : End Y) (hb : b ∈ Ring.jacobson (End Y))
    (hab : f ≫ b.asHom = a.asHom ≫ f) :
    a ∈ Ring.jacobson (End X) := by
  by_contra ha
  have haUnit : IsUnit a := by
    by_contra haUnit
    exact ha ((mem_ringJacobson_iff_not_isUnit (End X) a).2 haUnit)
  letI : IsIso a.asHom := (isUnit_iff_isIso _).1 haUnit
  let ai : End X := End.of (inv a.asHom)
  have hfixed : f = (ai.asHom ≫ f) ≫ b.asHom := by
    dsimp [ai]
    calc
      f = inv a.asHom ≫ (a.asHom ≫ f) := by simp
      _ = inv a.asHom ≫ (f ≫ b.asHom) := by rw [← hab]
      _ = (inv a.asHom ≫ f) ≫ b.asHom := by rw [Category.assoc]
  exact hf (eq_zero_of_eq_comp_comp_of_isNilpotent_right_agent ai b
    (radicalElement_isNilpotent_agent hb) hfixed)

/-- The zero endomorphism is a valid transit-oriented radical parameter when
the Jacobson radical vanishes. -/
theorem transitRadicalPowerData_zero_of_jacobson_eq_bot
    {X : C} (hJ : Ring.jacobson (End X) = ⊥) :
    TransitRadicalPowerData (0 : End X) where
  allows_transit := by
    intro a
    refine ⟨0, ?_⟩
    change a.asHom ≫ (0 : X ⟶ X) =
      (0 : X ⟶ X) ≫ (0 : X ⟶ X)
    simp
  generates := by
    intro a ha
    have ha0 : a = 0 := by
      have haBot : a ∈ (⊥ : Ideal (End X)) := by simpa [hJ] using ha
      exact (Submodule.mem_bot (R := End X)).1 haBot
    subst a
    refine ⟨0, ?_⟩
    change (0 : X ⟶ X) = (0 : X ⟶ X) ≫ (0 : X ⟶ X)
    simp
  factors := by
    intro a ha ha0
    have : a = 0 := by
      have haBot : a ∈ (⊥ : Ideal (End X)) := by simpa [hJ] using ha
      exact (Submodule.mem_bot (R := End X)).1 haBot
    exact (ha0 this).elim

/-- Cotransit-oriented zero-radical parameter. -/
theorem cotransitRadicalPowerData_zero_of_jacobson_eq_bot
    {X : C} (hJ : Ring.jacobson (End X) = ⊥) :
    CotransitRadicalPowerData (0 : End X) where
  allows_cotransit := by
    intro b
    refine ⟨0, ?_⟩
    change (0 : X ⟶ X) ≫ b.asHom =
      (0 : X ⟶ X) ≫ (0 : X ⟶ X)
    simp
  generates := by
    intro a ha
    have ha0 : a = 0 := by
      have haBot : a ∈ (⊥ : Ideal (End X)) := by simpa [hJ] using ha
      exact (Submodule.mem_bot (R := End X)).1 haBot
    subst a
    refine ⟨0, ?_⟩
    change (0 : X ⟶ X) = (0 : X ⟶ X) ≫ (0 : X ⟶ X)
    simp
  factors := by
    intro a ha ha0
    have : a = 0 := by
      have haBot : a ∈ (⊥ : Ideal (End X)) := by simpa [hJ] using ha
      exact (Submodule.mem_bot (R := End X)).1 haBot
    exact (ha0 this).elim

/-- Every endpoint has a transit-oriented radical-power generator.  A zero
radical uses `tau = 0`; otherwise the maximal-radical-span construction and
algebraic closedness provide the usual nonzero BGRS parameter. -/
theorem exists_transitRadicalPowerGenerator
    [IsAlgClosed k]
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [HasBGRSDistributiveHomStructure k C]
    (X : C) [Module.Finite k (X ⟶ X)]
    [Module.Finite k (End X)] :
    ∃ tau : End X, tau ∈ Ring.jacobson (End X) ∧
      TransitRadicalPowerData tau := by
  classical
  by_cases hJ : Ring.jacobson (End X) = ⊥
  · exact ⟨0, (Ring.jacobson (End X)).zero_mem,
      transitRadicalPowerData_zero_of_jacobson_eq_bot hJ⟩
  · have hlt : (⊥ : Ideal (End X)) < Ring.jacobson (End X) :=
      bot_lt_iff_ne_bot.mpr hJ
    obtain ⟨a, haJ, ha0⟩ := SetLike.exists_of_lt hlt
    have ha0' : a ≠ 0 := by
      intro hzero
      subst a
      exact ha0 (Ideal.zero_mem _)
    let P := Classical.choice
      (nonempty_orientedRadicalPowerParameter_of_nonzero_radical
        (k := k) (C := C) X a haJ ha0')
    exact ⟨P.tau, P.mem_jacobson, P.transitData⟩

/-- Source-dual endpoint-generator existence, with the same zero-radical
case split. -/
theorem exists_cotransitRadicalPowerGenerator
    [IsAlgClosed k]
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [HasBGRSDistributiveHomStructure k C]
    (X : C) [Module.Finite k (X ⟶ X)]
    [Module.Finite k (End X)] :
    ∃ tau : End X, tau ∈ Ring.jacobson (End X) ∧
      CotransitRadicalPowerData tau := by
  classical
  by_cases hJ : Ring.jacobson (End X) = ⊥
  · exact ⟨0, (Ring.jacobson (End X)).zero_mem,
      cotransitRadicalPowerData_zero_of_jacobson_eq_bot hJ⟩
  · have hlt : (⊥ : Ideal (End X)) < Ring.jacobson (End X) :=
      bot_lt_iff_ne_bot.mpr hJ
    obtain ⟨a, haJ, ha0⟩ := SetLike.exists_of_lt hlt
    have ha0' : a ≠ 0 := by
      intro hzero
      subst a
      exact ha0 (Ideal.zero_mem _)
    let P := Classical.choice
      (nonempty_orientedRadicalPowerParameter_of_nonzero_radical
        (k := k) (C := C) X a haJ ha0')
    exact ⟨P.tau, P.mem_jacobson, P.cotransitData⟩

/-! ## Exact classification of forbidden crosses for one arrow

For a length-one landing in the opposite closed zigzag, a forbidden cross
cannot have both outer paths equal to identities: the landing itself would
then be a path through the supposedly empty middle Hom.  Since all paths have
length at most one, every cross therefore has an outgoing arrow on its left or
an incoming arrow on its right.  The following two submodules make that
source-level dichotomy explicit. -/


end LargeIndecomposable.ClosedZigzagTransfer
