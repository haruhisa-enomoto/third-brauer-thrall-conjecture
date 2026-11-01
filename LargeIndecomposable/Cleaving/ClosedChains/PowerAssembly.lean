module

public import LargeIndecomposable.Cleaving.ClosedChains.PowerAlignedSupplementSeparation

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.ClosedZigzagTransfer

universe u x

variable {k : Type u} [Field k]
variable {C : Type x} [Category.{u} C] [Preadditive C] [Linear k C]

open LargeIndecomposable.ClosedZigzag

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

/-- Every element of the first target-power tail is one postmultiple of
`f ≫ tau`.  This is the linear collapse used implicitly in BGRS 3.7. -/
theorem exists_postcomposition_of_mem_targetPowerTail_one
    {X Y : C} (f : X ⟶ Y) (tau : End Y) {g : X ⟶ Y}
    (hg : g ∈ targetPowerTail (k := k) f tau 1) :
    ∃ q : End Y, g = (f ≫ tau.asHom) ≫ q.asHom := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨m, hm, e, rfl⟩
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      refine ⟨e * tau ^ r, ?_⟩
      rw [pow_succ, End.mul_def, End.mul_def]
      simp only [Category.assoc]
  | zero =>
      refine ⟨0, ?_⟩
      change (0 : X ⟶ Y) = (f ≫ tau.asHom) ≫ (0 : Y ⟶ Y)
      simp
  | add g h _ _ hg hh =>
      rcases hg with ⟨a, rfl⟩
      rcases hh with ⟨b, rfl⟩
      refine ⟨a + b, ?_⟩
      change ((f ≫ tau.asHom) ≫ a.asHom) +
          ((f ≫ tau.asHom) ≫ b.asHom) =
        (f ≫ tau.asHom) ≫ (a.asHom + b.asHom)
      rw [Preadditive.comp_add]
  | smul c g _ hg =>
      rcases hg with ⟨a, rfl⟩
      refine ⟨c • a, ?_⟩
      change c • ((f ≫ tau.asHom) ≫ a.asHom) =
        (f ≫ tau.asHom) ≫ (c • a.asHom)
      rw [Linear.comp_smul]

/-- Source-dual collapse of the first power tail. -/
theorem exists_precomposition_of_mem_sourcePowerTail_one
    {X Y : C} (f : X ⟶ Y) (tau : End X) {g : X ⟶ Y}
    (hg : g ∈ sourcePowerTail (k := k) f tau 1) :
    ∃ q : End X, g = q.asHom ≫ (tau.asHom ≫ f) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨m, hm, e, rfl⟩
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      refine ⟨tau ^ r * e, ?_⟩
      rw [pow_succ', End.mul_def, End.mul_def]
      simp only [Category.assoc]
  | zero =>
      refine ⟨0, ?_⟩
      change (0 : X ⟶ Y) = (0 : X ⟶ X) ≫ (tau.asHom ≫ f)
      simp
  | add g h _ _ hg hh =>
      rcases hg with ⟨a, rfl⟩
      rcases hh with ⟨b, rfl⟩
      refine ⟨a + b, ?_⟩
      change (a.asHom ≫ (tau.asHom ≫ f)) +
          (b.asHom ≫ (tau.asHom ≫ f)) =
        (a.asHom + b.asHom) ≫ (tau.asHom ≫ f)
      rw [Preadditive.add_comp]
  | smul c g _ hg =>
      rcases hg with ⟨a, rfl⟩
      refine ⟨c • a, ?_⟩
      change c • (a.asHom ≫ (tau.asHom ≫ f)) =
        (c • a.asHom) ≫ (tau.asHom ≫ f)
      rw [Linear.smul_comp]

/-- A nonzero morphism is never in its own first target-power tail when the
parameter is radical. -/
theorem not_mem_targetPowerTail_one
    {X Y : C} [IsArtinianRing (End Y)]
    (f : X ⟶ Y) (hf : f ≠ 0) (tau : End Y)
    (htau : tau ∈ Ring.jacobson (End Y)) :
    f ∉ targetPowerTail (k := k) f tau 1 := by
  intro hfTail
  obtain ⟨q, hfq⟩ :=
    exists_postcomposition_of_mem_targetPowerTail_one
      (k := k) f tau hfTail
  let b : End Y := q * tau
  have hbJ : b ∈ Ring.jacobson (End Y) :=
    (Ring.jacobson (End Y)).mul_mem_left q htau
  apply hf
  apply eq_zero_of_eq_comp_radical_agent hbJ
  simpa only [b, End.mul_def, Category.assoc] using hfq

/-- Source-dual exactness of the first power layer. -/
theorem not_mem_sourcePowerTail_one
    {X Y : C} [IsArtinianRing (End X)]
    (f : X ⟶ Y) (hf : f ≠ 0) (tau : End X)
    (htau : tau ∈ Ring.jacobson (End X)) :
    f ∉ sourcePowerTail (k := k) f tau 1 := by
  intro hfTail
  obtain ⟨q, hfq⟩ :=
    exists_precomposition_of_mem_sourcePowerTail_one
      (k := k) f tau hfTail
  let a : End X := tau * q
  have haJ : a ∈ Ring.jacobson (End X) :=
    (Ring.jacobson (End X)).mul_mem_right q htau
  apply hf
  apply eq_zero_of_eq_radical_comp_agent haJ
  simpa only [a, End.mul_def, Category.assoc] using hfq

/-- Set `pi := landing` and `degree := 0`.  Transit and a target radical
generator then make every field of the target power-alignment package
automatic except the source-specific cross-tail inclusion.  The statement
also works with `tau = 0`, so it covers a zero target Jacobson radical. -/
def targetPowerAlignedPathData_of_landing
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    {n : ℕ}
    (D : LinearPathCategory.Category k (Vertex n)ᵒᵖ ⥤ C)
    [D.Additive] [D.Linear k]
    {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X))
    (tau : End (D.obj Y))
    (htau : tau ∈ Ring.jacobson (End (D.obj Y)))
    (tauData : TransitRadicalPowerData tau)
    (hf : D.map (LinearPathCategory.pathHom p) ≠ 0)
    (htransit : AllowsTransit
      (D.map (LinearPathCategory.pathHom p)))
    (cross_raises : forbiddenCrossSubmodule (k := k) D X Y ≤
      targetPowerTail (k := k)
        (D.map (LinearPathCategory.pathHom p)) tau 1) :
    TargetPowerAlignedPathData (k := k) D p where
  pi := D.map (LinearPathCategory.pathHom p)
  tau := tau
  tau_mem_jacobson := htau
  tauData := tauData
  degree := 0
  landing_eq := by simp
  landing_exact := by
    simpa using not_mem_targetPowerTail_one (k := k)
      (D.map (LinearPathCategory.pathHom p)) hf tau htau
  source_radical_raises := by
    intro a ha
    obtain ⟨b, hab⟩ := htransit a
    have hb := target_mem_jacobson_of_source_mem_and_transfer
      hf a b ha hab
    obtain ⟨q, hbq⟩ := tauData.generates b hb
    rw [hab, hbq]
    simpa only [pow_one, zero_add, Category.assoc] using
      (targetPowerTail_generator_mem (k := k)
        (D.map (LinearPathCategory.pathHom p)) tau
        (N := 1) (m := 1) (by omega) q)
  cross_raises := by simpa using cross_raises

/-- Cotransit/source-dual automatic power-alignment constructor. -/
def sourcePowerAlignedPathData_of_landing
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    {n : ℕ}
    (D : LinearPathCategory.Category k (Vertex n)ᵒᵖ ⥤ C)
    [D.Additive] [D.Linear k]
    {X Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X))
    (tau : End (D.obj X))
    (htau : tau ∈ Ring.jacobson (End (D.obj X)))
    (tauData : CotransitRadicalPowerData tau)
    (hf : D.map (LinearPathCategory.pathHom p) ≠ 0)
    (hcotransit : AllowsCotransit
      (D.map (LinearPathCategory.pathHom p)))
    (cross_raises : forbiddenCrossSubmodule (k := k) D X Y ≤
      sourcePowerTail (k := k)
        (D.map (LinearPathCategory.pathHom p)) tau 1) :
    SourcePowerAlignedPathData (k := k) D p where
  pi := D.map (LinearPathCategory.pathHom p)
  tau := tau
  tau_mem_jacobson := htau
  tauData := tauData
  degree := 0
  landing_eq := by simp
  landing_exact := by
    simpa using not_mem_sourcePowerTail_one (k := k)
      (D.map (LinearPathCategory.pathHom p)) hf tau htau
  target_radical_raises := by
    intro b hb
    obtain ⟨a, hba⟩ := hcotransit b
    have ha := source_mem_jacobson_of_target_mem_and_transfer
      hf a b hb hba
    obtain ⟨q, haq⟩ := tauData.generates a ha
    rw [hba, haq]
    simpa only [pow_one, zero_add, Category.assoc] using
      (sourcePowerTail_generator_mem (k := k)
        (D.map (LinearPathCategory.pathHom p)) tau
        (N := 1) (m := 1) (by omega) q)
  cross_raises := by simpa using cross_raises

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

/-- Composites which start with a genuine source arrow out of the landing
source.  No claim is made here that the arrow differs from the landing; that
finer distinction belongs to the ray-incomparability step. -/
def outgoingArrowCrossSubmodule
    {n : ℕ}
    (D : LinearPathCategory.Category k (Vertex n)ᵒᵖ ⥤ C)
    [D.Additive] [D.Linear k]
    (X' Y' : LinearPathCategory.Category k (Vertex n)ᵒᵖ) :
    Submodule k (D.obj X' ⟶ D.obj Y') :=
  Submodule.span k {h | ∃
    (X : LinearPathCategory.Category k (Vertex n)ᵒᵖ)
    (p : Quiver.Path (LinearPathCategory.vertex X)
      (LinearPathCategory.vertex X')),
    p.length = 1 ∧ ∃ g : D.obj X ⟶ D.obj Y',
      h = D.map (LinearPathCategory.pathHom p) ≫ g}

/-- Composites which end with a genuine target arrow into the landing
target. -/
def incomingArrowCrossSubmodule
    {n : ℕ}
    (D : LinearPathCategory.Category k (Vertex n)ᵒᵖ ⥤ C)
    [D.Additive] [D.Linear k]
    (X' Y' : LinearPathCategory.Category k (Vertex n)ᵒᵖ) :
    Submodule k (D.obj X' ⟶ D.obj Y') :=
  Submodule.span k {h | ∃
    (Y : LinearPathCategory.Category k (Vertex n)ᵒᵖ)
    (q : Quiver.Path (LinearPathCategory.vertex Y')
      (LinearPathCategory.vertex Y)),
    q.length = 1 ∧ ∃ g : D.obj X' ⟶ D.obj Y,
      h = g ≫ D.map (LinearPathCategory.pathHom q)}

/-- The forbidden cross space for a length-one landing is generated by the
two BGRS p.240 cross types: a competing outgoing arrow followed by an
ambient map, or an ambient map followed by a competing incoming arrow.

This theorem records only the exact path-shape classification.  Removing
the cases where an outer arrow is the landing itself uses endpoint-radical
factorization; identifying the remaining arrow with the adjacent closed-chain
ray uses the concrete chain indexing. -/
theorem forbiddenCrossSubmodule_le_outgoing_sup_incoming
    {n : ℕ}
    (D : LinearPathCategory.Category k (Vertex n)ᵒᵖ ⥤ C)
    [D.Additive] [D.Linear k]
    {X' Y' : LinearPathCategory.Category k (Vertex n)ᵒᵖ}
    (r : Quiver.Path (LinearPathCategory.vertex Y')
      (LinearPathCategory.vertex X'))
    (_hr : r.length = 1) :
    forbiddenCrossSubmodule (k := k) D X' Y' ≤
      outgoingArrowCrossSubmodule (k := k) D X' Y' ⊔
        incomingArrowCrossSubmodule (k := k) D X' Y' := by
  apply Submodule.span_le.2
  rintro h ⟨X, Y, p, g, q, hm, rfl⟩
  have hp_le := closedZigzagOpposite_path_length_le_one n p
  have hq_le := closedZigzagOpposite_path_length_le_one n q
  by_cases hp0 : p.length = 0
  · have hq0 : q.length ≠ 0 := by
      intro hq0
      have hpEq := p.eq_of_length_zero hp0
      have hqEq := q.eq_of_length_zero hq0
      apply hm.false
      simpa only [hpEq, hqEq] using r
    have hq1 : q.length = 1 := by omega
    apply (show incomingArrowCrossSubmodule (k := k) D X' Y' ≤
      outgoingArrowCrossSubmodule (k := k) D X' Y' ⊔
        incomingArrowCrossSubmodule (k := k) D X' Y' from le_sup_right)
    apply Submodule.subset_span
    refine ⟨Y, q, hq1,
      D.map (LinearPathCategory.pathHom p) ≫ g, ?_⟩
    simp only [Category.assoc]
  · have hp1 : p.length = 1 := by omega
    apply (show outgoingArrowCrossSubmodule (k := k) D X' Y' ≤
      outgoingArrowCrossSubmodule (k := k) D X' Y' ⊔
        incomingArrowCrossSubmodule (k := k) D X' Y' from le_sup_left)
    apply Submodule.subset_span
    refine ⟨X, p, hp1,
      g ≫ D.map (LinearPathCategory.pathHom q), ?_⟩
    rfl


end LargeIndecomposable.ClosedZigzagTransfer
