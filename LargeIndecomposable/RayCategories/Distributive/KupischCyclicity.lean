module

public import LargeIndecomposable.RayCategories.Distributive.SplitBasicRayCategory

@[expose] public section

/-!
# Kupisch cyclicity for distributive Hom spaces

If endpoint-stable subspaces of one Hom space are linearly ordered, compare
the source-radical and target-radical parts of the principal bimodule.  Split
residue maps and nilpotence of the endpoint Jacobson radicals then show that
the principal bimodule is cyclic on one side.  Equivalently, the morphism
allows transit or cotransit in the sense used by BGRS.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable

universe u v w

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- Right-endomorphism multiples of one morphism, as a linear subspace. -/
private def rightEndomorphismSpan {X Y : C} (f : X ⟶ Y) :
    Submodule k (X ⟶ Y) where
  carrier := {g | ∃ b : End Y, g = f ≫ b.asHom}
  zero_mem' := ⟨0, by change (0 : X ⟶ Y) = f ≫ (0 : Y ⟶ Y); simp⟩
  add_mem' := by
    rintro g h ⟨b, rfl⟩ ⟨c, rfl⟩
    refine ⟨b + c, ?_⟩
    change (f ≫ b.asHom) + (f ≫ c.asHom) =
      f ≫ (b.asHom + c.asHom)
    rw [Preadditive.comp_add]
  smul_mem' := by
    rintro c g ⟨b, rfl⟩
    refine ⟨c • b, ?_⟩
    change c • (f ≫ b.asHom) = f ≫ (c • b.asHom)
    rw [Linear.comp_smul]

/-- Left-endomorphism multiples of one morphism, as a linear subspace. -/
private def leftEndomorphismSpan {X Y : C} (f : X ⟶ Y) :
    Submodule k (X ⟶ Y) where
  carrier := {g | ∃ a : End X, g = a.asHom ≫ f}
  zero_mem' := ⟨0, by change (0 : X ⟶ Y) = (0 : X ⟶ X) ≫ f; simp⟩
  add_mem' := by
    rintro g h ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨a + b, ?_⟩
    change (a.asHom ≫ f) + (b.asHom ≫ f) =
      (a.asHom + b.asHom) ≫ f
    rw [Preadditive.add_comp]
  smul_mem' := by
    rintro c g ⟨a, rfl⟩
    refine ⟨c • a, ?_⟩
    change c • (a.asHom ≫ f) = (c • a.asHom) ≫ f
    rw [Linear.smul_comp]

/-- The part of the principal bimodule whose right coefficient belongs to
the `n`th power of the target radical. -/
private def targetRadicalPowerSpan {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    Submodule k (X ⟶ Y) :=
  Submodule.span k {g | ∃ (a : End X) (b : End Y),
    b ∈ (Ring.jacobson (End Y)) ^ n ∧ g = (a.asHom ≫ f) ≫ b.asHom}

/-- The part of the principal bimodule whose left coefficient belongs to
the `n`th power of the source radical. -/
private def sourceRadicalPowerSpan {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    Submodule k (X ⟶ Y) :=
  Submodule.span k {g | ∃ (a : End X) (b : End Y),
    a ∈ (Ring.jacobson (End X)) ^ n ∧ g = (a.asHom ≫ f) ≫ b.asHom}

private theorem targetRadicalPowerSpan_isHomSubbimodule
    {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    IsHomSubbimodule (targetRadicalPowerSpan (k := k) f n) := by
  constructor
  · intro c g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
        rcases hg with ⟨a, b, hb, rfl⟩
        apply Submodule.subset_span
        refine ⟨c.asHom ≫ a.asHom, b, hb, ?_⟩
        simp [Category.assoc]
    | zero => simp
    | add g h _ _ hg hh =>
        simpa [Preadditive.comp_add] using
          (targetRadicalPowerSpan (k := k) f n).add_mem hg hh
    | smul c g _ hg =>
        simpa using (targetRadicalPowerSpan (k := k) f n).smul_mem c hg
  · intro d g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
        rcases hg with ⟨a, b, hb, rfl⟩
        apply Submodule.subset_span
        refine ⟨a, b.asHom ≫ d.asHom, ?_, by simp [Category.assoc]⟩
        change d * b ∈ (Ring.jacobson (End Y)) ^ n
        exact Ideal.mul_mem_left _ d hb
    | zero => simp
    | add g h _ _ hg hh =>
        simpa [Preadditive.add_comp] using
          (targetRadicalPowerSpan (k := k) f n).add_mem hg hh
    | smul c g _ hg =>
        simpa using (targetRadicalPowerSpan (k := k) f n).smul_mem c hg

private theorem sourceRadicalPowerSpan_isHomSubbimodule
    {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    IsHomSubbimodule (sourceRadicalPowerSpan (k := k) f n) := by
  constructor
  · intro c g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
        rcases hg with ⟨a, b, ha, rfl⟩
        apply Submodule.subset_span
        refine ⟨c.asHom ≫ a.asHom, b, ?_, by simp [Category.assoc]⟩
        change a * c ∈ (Ring.jacobson (End X)) ^ n
        exact Ideal.mul_mem_right c _ ha
    | zero => simp
    | add g h _ _ hg hh =>
        simpa [Preadditive.comp_add] using
          (sourceRadicalPowerSpan (k := k) f n).add_mem hg hh
    | smul c g _ hg =>
        simpa using (sourceRadicalPowerSpan (k := k) f n).smul_mem c hg
  · intro d g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
        rcases hg with ⟨a, b, ha, rfl⟩
        apply Submodule.subset_span
        exact ⟨a, b.asHom ≫ d.asHom, ha, by simp [Category.assoc]⟩
    | zero => simp
    | add g h _ _ hg hh =>
        simpa [Preadditive.add_comp] using
          (sourceRadicalPowerSpan (k := k) f n).add_mem hg hh
    | smul c g _ hg =>
        simpa using (sourceRadicalPowerSpan (k := k) f n).smul_mem c hg

private theorem targetRadicalPowerSpan_right_comp
    {X Y : C} (f : X ⟶ Y) {m n : ℕ}
    {g : X ⟶ Y} (hg : g ∈ targetRadicalPowerSpan (k := k) f m)
    (b : End Y) (hb : b ∈ (Ring.jacobson (End Y)) ^ n) :
    g ≫ b.asHom ∈ targetRadicalPowerSpan (k := k) f (n + m) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨a, c, hc, rfl⟩
      apply Submodule.subset_span
      refine ⟨a, c.asHom ≫ b.asHom, ?_, by simp [Category.assoc]⟩
      change b * c ∈ (Ring.jacobson (End Y)) ^ (n + m)
      rw [Ideal.IsTwoSided.pow_add]
      exact Ideal.mul_mem_mul hb hc
  | zero => simp
  | add g h _ _ hg hh =>
      simpa [Preadditive.add_comp] using
        (targetRadicalPowerSpan (k := k) f (n + m)).add_mem hg hh
  | smul c g _ hg =>
      simpa using
        (targetRadicalPowerSpan (k := k) f (n + m)).smul_mem c hg

private theorem sourceRadicalPowerSpan_left_comp
    {X Y : C} (f : X ⟶ Y) {m n : ℕ}
    {g : X ⟶ Y} (hg : g ∈ sourceRadicalPowerSpan (k := k) f m)
    (a : End X) (ha : a ∈ (Ring.jacobson (End X)) ^ n) :
    a.asHom ≫ g ∈ sourceRadicalPowerSpan (k := k) f (m + n) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨c, b, hc, rfl⟩
      apply Submodule.subset_span
      refine ⟨a.asHom ≫ c.asHom, b, ?_, by simp [Category.assoc]⟩
      change c * a ∈ (Ring.jacobson (End X)) ^ (m + n)
      rw [Ideal.IsTwoSided.pow_add]
      exact Ideal.mul_mem_mul hc ha
  | zero => simp
  | add g h _ _ hg hh =>
      simpa [Preadditive.comp_add] using
        (sourceRadicalPowerSpan (k := k) f (m + n)).add_mem hg hh
  | smul c g _ hg =>
      simpa using
        (sourceRadicalPowerSpan (k := k) f (m + n)).smul_mem c hg

private theorem targetRadicalPowerSpan_eq_bot_of_pow_eq_bot
    {X Y : C} (f : X ⟶ Y) (n : ℕ)
    (hn : (Ring.jacobson (End Y)) ^ n = ⊥) :
    targetRadicalPowerSpan (k := k) f n = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro g ⟨a, b, hb, rfl⟩
    rw [hn] at hb
    have hb0 : b.asHom = (0 : Y ⟶ Y) := by
      change b = (0 : End Y)
      exact (Submodule.mem_bot (R := End Y)).1 hb
    rw [hb0]
    simp
  · exact bot_le

private theorem sourceRadicalPowerSpan_eq_bot_of_pow_eq_bot
    {X Y : C} (f : X ⟶ Y) (n : ℕ)
    (hn : (Ring.jacobson (End X)) ^ n = ⊥) :
    sourceRadicalPowerSpan (k := k) f n = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro g ⟨a, b, ha, rfl⟩
    rw [hn] at ha
    have ha0 : a.asHom = (0 : X ⟶ X) := by
      change a = (0 : End X)
      exact (Submodule.mem_bot (R := End X)).1 ha
    rw [ha0]
    simp
  · exact bot_le

private theorem targetRadicalPowerSpan_le_right_sup_succ
    {X Y : C} (f : X ⟶ Y)
    (residue : End X →ₐ[k] k)
    (residue_zero : ∀ a : End X,
      residue a = 0 ↔ a ∈ Ring.jacobson (End X))
    (hmove : sourceRadicalPowerSpan (k := k) f 1 ≤
      targetRadicalPowerSpan (k := k) f 1)
    (n : ℕ) :
    targetRadicalPowerSpan (k := k) f n ≤
      rightEndomorphismSpan (k := k) f ⊔
        targetRadicalPowerSpan (k := k) f (n + 1) := by
  apply Submodule.span_le.2
  rintro g ⟨a, b, hb, rfl⟩
  let c : k := residue a
  let r : End X := a - algebraMap k (End X) c
  have hrzero : residue r = 0 := by
    dsimp [r, c]
    rw [map_sub, residue.commutes]
    exact sub_self _
  have hrJ : r ∈ Ring.jacobson (End X) :=
    (residue_zero r).1 hrzero
  have hrfS : r.asHom ≫ f ∈
      sourceRadicalPowerSpan (k := k) f 1 := by
    apply Submodule.subset_span
    refine ⟨r, 1, ?_, by simp⟩
    rw [Submodule.pow_one]
    exact hrJ
  have hrad : (r.asHom ≫ f) ≫ b.asHom ∈
      targetRadicalPowerSpan (k := k) f (n + 1) :=
    targetRadicalPowerSpan_right_comp (k := k) f (hmove hrfS) b hb
  have hscalar :
      ((((algebraMap k (End X)) c).asHom ≫ f) ≫ b.asHom) ∈
      rightEndomorphismSpan (k := k) f := by
    refine ⟨c • b, ?_⟩
    change ((c • (𝟙 X)) ≫ f) ≫ b.asHom =
      f ≫ (c • b.asHom)
    simp
  have ha : a = algebraMap k (End X) c + r := by
    dsimp [r]
    abel
  have haHom : a.asHom = ((algebraMap k (End X)) c).asHom + r.asHom :=
    congrArg End.asHom ha
  rw [haHom]
  rw [Preadditive.add_comp, Preadditive.add_comp]
  exact (Submodule.mem_sup).2
    ⟨_, hscalar, _, hrad, rfl⟩

private theorem sourceRadicalPowerSpan_le_left_sup_succ
    {X Y : C} (f : X ⟶ Y)
    (residue : End Y →ₐ[k] k)
    (residue_zero : ∀ b : End Y,
      residue b = 0 ↔ b ∈ Ring.jacobson (End Y))
    (hmove : targetRadicalPowerSpan (k := k) f 1 ≤
      sourceRadicalPowerSpan (k := k) f 1)
    (n : ℕ) :
    sourceRadicalPowerSpan (k := k) f n ≤
      leftEndomorphismSpan (k := k) f ⊔
        sourceRadicalPowerSpan (k := k) f (n + 1) := by
  apply Submodule.span_le.2
  rintro g ⟨a, b, ha, rfl⟩
  let c : k := residue b
  let r : End Y := b - algebraMap k (End Y) c
  have hrzero : residue r = 0 := by
    dsimp [r, c]
    rw [map_sub, residue.commutes]
    exact sub_self _
  have hrJ : r ∈ Ring.jacobson (End Y) :=
    (residue_zero r).1 hrzero
  have hfrT : f ≫ r.asHom ∈
      targetRadicalPowerSpan (k := k) f 1 := by
    apply Submodule.subset_span
    refine ⟨1, r, ?_, by simp⟩
    rw [Submodule.pow_one]
    exact hrJ
  have hrad : a.asHom ≫ (f ≫ r.asHom) ∈
      sourceRadicalPowerSpan (k := k) f (n + 1) := by
    simpa [Nat.add_comm] using
      sourceRadicalPowerSpan_left_comp (k := k) f (hmove hfrT) a ha
  have hscalar :
      ((a.asHom ≫ f) ≫ ((algebraMap k (End Y)) c).asHom) ∈
        leftEndomorphismSpan (k := k) f := by
    refine ⟨c • a, ?_⟩
    change (a.asHom ≫ f) ≫ (c • (𝟙 Y)) =
      (c • a.asHom) ≫ f
    simp
  have hbdecomp : b = algebraMap k (End Y) c + r := by
    dsimp [r]
    abel
  have hbHom : b.asHom = ((algebraMap k (End Y)) c).asHom + r.asHom :=
    congrArg End.asHom hbdecomp
  rw [hbHom, Preadditive.comp_add]
  exact (Submodule.mem_sup).2
    ⟨_, hscalar, _, by simpa [Category.assoc] using hrad, rfl⟩

private theorem powerSpan_le_sup_iterate
    {M : Type*} [AddCommMonoid M] [Module k M]
    (F : Submodule k M) (T : ℕ → Submodule k M)
    (hstep : ∀ n, T n ≤ F ⊔ T (n + 1)) :
    ∀ n, T 0 ≤ F ⊔ T n := by
  intro n
  induction n with
  | zero => exact le_sup_right
  | succ n ih =>
      exact ih.trans (sup_le le_sup_left (hstep n))

private theorem allowsTransit_of_radicalSpan_le
    {X Y : C} (f : X ⟶ Y)
    (residue : End X →ₐ[k] k)
    (residue_zero : ∀ a : End X,
      residue a = 0 ↔ a ∈ Ring.jacobson (End X))
    (hmove : sourceRadicalPowerSpan (k := k) f 1 ≤
      targetRadicalPowerSpan (k := k) f 1)
    (N : ℕ) (hN : (Ring.jacobson (End Y)) ^ N = ⊥) :
    AllowsTransit f := by
  have hiter : targetRadicalPowerSpan (k := k) f 0 ≤
      rightEndomorphismSpan (k := k) f ⊔
        targetRadicalPowerSpan (k := k) f N :=
    powerSpan_le_sup_iterate (k := k)
      (rightEndomorphismSpan (k := k) f)
      (targetRadicalPowerSpan (k := k) f)
      (targetRadicalPowerSpan_le_right_sup_succ
        (k := k) f residue residue_zero hmove) N
  rw [targetRadicalPowerSpan_eq_bot_of_pow_eq_bot
    (k := k) f N hN, sup_bot_eq] at hiter
  intro a
  have haf : a.asHom ≫ f ∈
      targetRadicalPowerSpan (k := k) f 0 := by
    apply Submodule.subset_span
    refine ⟨a, 1, ?_, by simp⟩
    rw [Submodule.pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  exact hiter haf

private theorem allowsCotransit_of_radicalSpan_le
    {X Y : C} (f : X ⟶ Y)
    (residue : End Y →ₐ[k] k)
    (residue_zero : ∀ b : End Y,
      residue b = 0 ↔ b ∈ Ring.jacobson (End Y))
    (hmove : targetRadicalPowerSpan (k := k) f 1 ≤
      sourceRadicalPowerSpan (k := k) f 1)
    (N : ℕ) (hN : (Ring.jacobson (End X)) ^ N = ⊥) :
    AllowsCotransit f := by
  have hiter : sourceRadicalPowerSpan (k := k) f 0 ≤
      leftEndomorphismSpan (k := k) f ⊔
        sourceRadicalPowerSpan (k := k) f N :=
    powerSpan_le_sup_iterate (k := k)
      (leftEndomorphismSpan (k := k) f)
      (sourceRadicalPowerSpan (k := k) f)
      (sourceRadicalPowerSpan_le_left_sup_succ
        (k := k) f residue residue_zero hmove) N
  rw [sourceRadicalPowerSpan_eq_bot_of_pow_eq_bot
    (k := k) f N hN, sup_bot_eq] at hiter
  intro b
  have hfb : f ≫ b.asHom ∈
      sourceRadicalPowerSpan (k := k) f 0 := by
    apply Submodule.subset_span
    refine ⟨1, b, ?_, by simp⟩
    rw [Submodule.pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  exact hiter hfb

/-- Kupisch's cyclicity argument: linearly ordered endpoint-stable subspaces,
split residue maps, and nilpotent endpoint radicals force every morphism to
allow transit or cotransit. -/
theorem transit_or_cotransit_of_homSubbimodule_comparable
    {X Y : C} (f : X ⟶ Y)
    [IsArtinianRing (End X)] [IsArtinianRing (End Y)]
    (sourceResidue : End X →ₐ[k] k)
    (targetResidue : End Y →ₐ[k] k)
    (sourceResidue_zero : ∀ a : End X,
      sourceResidue a = 0 ↔ a ∈ Ring.jacobson (End X))
    (targetResidue_zero : ∀ b : End Y,
      targetResidue b = 0 ↔ b ∈ Ring.jacobson (End Y))
    (hcomparable : ∀ (S T : Submodule k (X ⟶ Y)),
      IsHomSubbimodule S → IsHomSubbimodule T → S ≤ T ∨ T ≤ S) :
    AllowsTransit f ∨ AllowsCotransit f := by
  obtain ⟨NX, hNX⟩ :=
    IsArtinianRing.isNilpotent_jacobson_bot (R := End X)
  rw [Ideal.jacobson_bot] at hNX
  obtain ⟨NY, hNY⟩ :=
    IsArtinianRing.isNilpotent_jacobson_bot (R := End Y)
  rw [Ideal.jacobson_bot] at hNY
  rcases hcomparable
      (sourceRadicalPowerSpan (k := k) f 1)
      (targetRadicalPowerSpan (k := k) f 1)
      (sourceRadicalPowerSpan_isHomSubbimodule (k := k) f 1)
      (targetRadicalPowerSpan_isHomSubbimodule (k := k) f 1) with hST | hTS
  · exact Or.inl <| allowsTransit_of_radicalSpan_le
      (k := k) f sourceResidue sourceResidue_zero hST NY hNY
  · exact Or.inr <| allowsCotransit_of_radicalSpan_le
      (k := k) f targetResidue targetResidue_zero hTS NX hNX

end LargeIndecomposable

namespace LargeIndecomposable.SplitBasicIdempotents

universe u v x

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {iota : Type x} [Fintype iota] [DecidableEq iota]

theorem ProjectiveCategory.transit_or_cotransit_of_homSubbimodule_comparable
    [Module.Finite k A]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := iota))
    (hcomparable : ∀ {X Y : S.ProjectiveCategory}
      (U V : Submodule k (X ⟶ Y)),
      LargeIndecomposable.IsHomSubbimodule U →
      LargeIndecomposable.IsHomSubbimodule V → U ≤ V ∨ V ≤ U)
    {X Y : S.ProjectiveCategory} (f : X ⟶ Y) :
    LargeIndecomposable.AllowsTransit f ∨
      LargeIndecomposable.AllowsCotransit f := by
  apply LargeIndecomposable.transit_or_cotransit_of_homSubbimodule_comparable
    (k := k) f (S.projectiveEndResidue X) (S.projectiveEndResidue Y)
  · intro a
    rw [S.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  · intro b
    rw [S.projectiveEndResidue_eq_zero_iff_val_mem_jacobson,
      ← S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  · exact hcomparable

/-- Once endpoint-stable Hom subspaces are known to be linearly ordered, the
split-basic residue maps supply the entire BGRS distributive-Hom package. -/
theorem ProjectiveCategory.bgrsDistributiveHomStructureOfComparable
    [Module.Finite k A]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := iota))
    (hcomparable : ∀ {X Y : S.ProjectiveCategory}
      (U V : Submodule k (X ⟶ Y)),
      LargeIndecomposable.IsHomSubbimodule U →
      LargeIndecomposable.IsHomSubbimodule V → U ≤ V ∨ V ≤ U) :
    LargeIndecomposable.HasBGRSDistributiveHomStructure
      k S.ProjectiveCategory where
  homSubbimodule_comparable := hcomparable
  transit_or_cotransit f :=
    ProjectiveCategory.transit_or_cotransit_of_homSubbimodule_comparable
      S hcomparable f


end LargeIndecomposable.SplitBasicIdempotents
