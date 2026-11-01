module

public import LargeIndecomposable.RayCategories.Distributive.BGRSRayCategory
public import LargeIndecomposable.Foundations.Ring.LocalRingJacobson
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Nilpotent.Basic

@[expose] public section

/-!
# Distributive Hom spaces and unit rays

Package the local Hom-subbimodule form of distributivity used by BGRS.  If
endpoint-stable submodules form chains and every morphism allows transit or
cotransit, local Artinian endpoint rings force principal two-sided spans to
classify two-sided unit rays.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable

universe u v w z

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- A linear subspace of one Hom space stable under both endpoint
endomorphism rings. -/
def IsHomSubbimodule {X Y : C} (S : Submodule k (X ⟶ Y)) : Prop :=
  (∀ (a : End X) {f : X ⟶ Y}, f ∈ S → a.asHom ≫ f ∈ S) ∧
  (∀ (b : End Y) {f : X ⟶ Y}, f ∈ S → f ≫ b.asHom ∈ S)

/-- A principal two-sided endomorphism span is a Hom subbimodule. -/
theorem isHomSubbimodule_twoSidedEndomorphismSpan
    {X Y : C} (f : X ⟶ Y) :
    IsHomSubbimodule (twoSidedEndomorphismSpan k f) := by
  constructor
  · intro a g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
        rcases hg with ⟨c, d, rfl⟩
        apply Submodule.subset_span
        exact ⟨a.asHom ≫ c.asHom, d, by simp [Category.assoc]⟩
    | zero => simp
    | add g h _ _ hg hh =>
        simpa using (twoSidedEndomorphismSpan k f).add_mem hg hh
    | smul c g _ hg =>
        simpa using (twoSidedEndomorphismSpan k f).smul_mem c hg
  · intro b g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
        rcases hg with ⟨a, c, rfl⟩
        apply Submodule.subset_span
        exact ⟨a, c.asHom ≫ b.asHom, by simp [Category.assoc]⟩
    | zero => simp
    | add g h _ _ hg hh =>
        simpa using (twoSidedEndomorphismSpan k f).add_mem hg hh
    | smul c g _ hg =>
        simpa using (twoSidedEndomorphismSpan k f).smul_mem c hg

/-- Membership of one morphism in another's principal two-sided span implies
inclusion of the corresponding principal spans. -/
theorem twoSidedEndomorphismSpan_le_of_mem
    {X Y : C} {f g : X ⟶ Y}
    (hg : g ∈ twoSidedEndomorphismSpan k f) :
    twoSidedEndomorphismSpan k g ≤ twoSidedEndomorphismSpan k f := by
  apply Submodule.span_le.2
  rintro h ⟨a, b, rfl⟩
  exact (isHomSubbimodule_twoSidedEndomorphismSpan f).2 b
    ((isHomSubbimodule_twoSidedEndomorphismSpan f).1 a hg)

/-- Every source endomorphism can transit across the selected morphism. -/
def AllowsTransit {X Y : C} (f : X ⟶ Y) : Prop :=
  ∀ a : End X, ∃ b : End Y, a.asHom ≫ f = f ≫ b.asHom

/-- Every target endomorphism can cotransit across the selected morphism. -/
def AllowsCotransit {X Y : C} (f : X ⟶ Y) : Prop :=
  ∀ b : End Y, ∃ a : End X, f ≫ b.asHom = a.asHom ≫ f

omit [Preadditive C] in
/-- Every endomorphism allows transit when its endomorphism ring is
commutative. -/
theorem allowsTransit_end_of_end_comm
    {X : C} (f : End X)
    (hcomm : ∀ a b : End X,
      a.asHom ≫ b.asHom = b.asHom ≫ a.asHom) :
    AllowsTransit f.asHom := by
  intro a
  exact ⟨a, hcomm a f⟩

omit [Preadditive C] in
/-- Every endomorphism allows cotransit when its endomorphism ring is
commutative. -/
theorem allowsCotransit_end_of_end_comm
    {X : C} (f : End X)
    (hcomm : ∀ a b : End X,
      a.asHom ≫ b.asHom = b.asHom ≫ a.asHom) :
    AllowsCotransit f.asHom := by
  intro b
  exact ⟨b, hcomm f b⟩

omit [Preadditive C] in
/-- Transit is preserved by categorical composition. -/
theorem AllowsTransit.comp
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : AllowsTransit f) (hg : AllowsTransit g) :
    AllowsTransit (f ≫ g) := by
  intro a
  obtain ⟨b, hab⟩ := hf a
  obtain ⟨c, hbc⟩ := hg b
  refine ⟨c, ?_⟩
  calc
    a.asHom ≫ (f ≫ g) = (a.asHom ≫ f) ≫ g := by
      rw [Category.assoc]
    _ = (f ≫ b.asHom) ≫ g := by rw [hab]
    _ = f ≫ (b.asHom ≫ g) := Category.assoc _ _ _
    _ = f ≫ (g ≫ c.asHom) := by rw [hbc]
    _ = (f ≫ g) ≫ c.asHom := by rw [Category.assoc]

omit [Preadditive C] in
/-- Cotransit is preserved by categorical composition. -/
theorem AllowsCotransit.comp
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : AllowsCotransit f) (hg : AllowsCotransit g) :
    AllowsCotransit (f ≫ g) := by
  intro c
  obtain ⟨b, hbc⟩ := hg c
  obtain ⟨a, hab⟩ := hf b
  refine ⟨a, ?_⟩
  calc
    (f ≫ g) ≫ c.asHom = f ≫ (g ≫ c.asHom) :=
      Category.assoc _ _ _
    _ = f ≫ (b.asHom ≫ g) := by rw [hbc]
    _ = (f ≫ b.asHom) ≫ g := by rw [Category.assoc]
    _ = (a.asHom ≫ f) ≫ g := by rw [hab]
    _ = a.asHom ≫ (f ≫ g) := Category.assoc _ _ _

omit [Preadditive C] in
/-- Transit is invariant under changing a morphism by invertible endpoint
factors. -/
theorem AllowsTransit.of_unitRayEquivalent
    {X Y : C} {f f' : X ⟶ Y}
    (hf : AllowsTransit f) (hff' : UnitRayEquivalent f f') :
    AllowsTransit f' := by
  rcases hff' with ⟨a, b, rfl⟩
  intro s
  let q : End X := End.of (a.inv ≫ s.asHom ≫ a.hom)
  obtain ⟨r, hr⟩ := hf q
  let t : End Y := End.of (b.inv ≫ r.asHom ≫ b.hom)
  refine ⟨t, ?_⟩
  calc
    s.asHom ≫ (a.hom ≫ f ≫ b.hom) =
        (a.hom ≫ (q.asHom ≫ f)) ≫ b.hom := by
      simp [q, Category.assoc]
    _ = (a.hom ≫ (f ≫ r.asHom)) ≫ b.hom := by rw [hr]
    _ = (a.hom ≫ f ≫ b.hom) ≫ t.asHom := by
      simp [t, Category.assoc]

omit [Preadditive C] in
/-- Cotransit is invariant under changing a morphism by invertible endpoint
factors. -/
theorem AllowsCotransit.of_unitRayEquivalent
    {X Y : C} {f f' : X ⟶ Y}
    (hf : AllowsCotransit f) (hff' : UnitRayEquivalent f f') :
    AllowsCotransit f' := by
  rcases hff' with ⟨a, b, rfl⟩
  intro s
  let q : End Y := End.of (b.hom ≫ s.asHom ≫ b.inv)
  obtain ⟨r, hr⟩ := hf q
  let t : End X := End.of (a.hom ≫ r.asHom ≫ a.inv)
  refine ⟨t, ?_⟩
  calc
    (a.hom ≫ f ≫ b.hom) ≫ s.asHom =
        a.hom ≫ (f ≫ q.asHom) ≫ b.hom := by
      simp [q, Category.assoc]
    _ = a.hom ≫ (r.asHom ≫ f) ≫ b.hom := by rw [hr]
    _ = t.asHom ≫ (a.hom ≫ f ≫ b.hom) := by
      simp [t, Category.assoc]

omit [Preadditive C] in
/-- Transit depends only on the unit ray of a morphism. -/
theorem allowsTransit_iff_of_unitRayEquivalent
    {X Y : C} {f f' : X ⟶ Y}
    (hff' : UnitRayEquivalent f f') :
    AllowsTransit f ↔ AllowsTransit f' := by
  constructor
  · exact fun hf ↦ hf.of_unitRayEquivalent hff'
  · exact fun hf' ↦ hf'.of_unitRayEquivalent
      ((unitRaySetoid X Y).symm hff')

omit [Preadditive C] in
/-- Cotransit depends only on the unit ray of a morphism. -/
theorem allowsCotransit_iff_of_unitRayEquivalent
    {X Y : C} {f f' : X ⟶ Y}
    (hff' : UnitRayEquivalent f f') :
    AllowsCotransit f ↔ AllowsCotransit f' := by
  constructor
  · exact fun hf ↦ hf.of_unitRayEquivalent hff'
  · exact fun hf' ↦ hf'.of_unitRayEquivalent
      ((unitRaySetoid X Y).symm hff')

/-- The two local consequences of categorical distributivity used to
classify unit rays by principal Hom subbimodules. -/
class HasBGRSDistributiveHomStructure
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C] : Prop where
  homSubbimodule_comparable : ∀ {X Y : C}
    (S T : Submodule k (X ⟶ Y)),
    IsHomSubbimodule S → IsHomSubbimodule T → S ≤ T ∨ T ≤ S
  transit_or_cotransit : ∀ {X Y : C} (f : X ⟶ Y),
    AllowsTransit f ∨ AllowsCotransit f

/-- If the generator allows transit, every element of its principal
two-sided span is a target-endomorphism multiple of the generator. -/
theorem exists_comp_of_mem_span_of_allowsTransit
    {X Y : C} {f g : X ⟶ Y} (ht : AllowsTransit f)
    (hg : g ∈ twoSidedEndomorphismSpan k f) :
    ∃ b : End Y, g = f ≫ b.asHom := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨a, b, rfl⟩
      obtain ⟨c, hc⟩ := ht a
      refine ⟨b * c, ?_⟩
      change (a.asHom ≫ f) ≫ b.asHom = f ≫ (b * c).asHom
      rw [hc, End.mul_def, Category.assoc]
  | zero =>
      refine ⟨0, ?_⟩
      change (0 : X ⟶ Y) = f ≫ (0 : Y ⟶ Y)
      simp
  | add g h _ _ hg hh =>
      rcases hg with ⟨a, rfl⟩
      rcases hh with ⟨b, rfl⟩
      refine ⟨a + b, ?_⟩
      change (f ≫ a.asHom) + (f ≫ b.asHom) =
        f ≫ (a.asHom + b.asHom)
      rw [Preadditive.comp_add]
  | smul c g _ hg =>
      rcases hg with ⟨a, rfl⟩
      refine ⟨c • a, ?_⟩
      change c • (f ≫ a.asHom) = f ≫ (c • a.asHom)
      rw [Linear.comp_smul]

/-- If the generator allows cotransit, every element of its principal
two-sided span is a source-endomorphism multiple of the generator. -/
theorem exists_comp_of_mem_span_of_allowsCotransit
    {X Y : C} {f g : X ⟶ Y} (ht : AllowsCotransit f)
    (hg : g ∈ twoSidedEndomorphismSpan k f) :
    ∃ a : End X, g = a.asHom ≫ f := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨a, b, rfl⟩
      obtain ⟨c, hc⟩ := ht b
      refine ⟨a.asHom ≫ c.asHom, ?_⟩
      change (a.asHom ≫ f) ≫ b.asHom =
        (a.asHom ≫ c.asHom) ≫ f
      rw [Category.assoc, hc]
      simp only [Category.assoc]
  | zero =>
      refine ⟨0, ?_⟩
      change (0 : X ⟶ Y) = (0 : X ⟶ X) ≫ f
      simp
  | add g h _ _ hg hh =>
      rcases hg with ⟨a, rfl⟩
      rcases hh with ⟨b, rfl⟩
      refine ⟨a + b, ?_⟩
      change (a.asHom ≫ f) + (b.asHom ≫ f) =
        (a.asHom + b.asHom) ≫ f
      rw [Preadditive.add_comp]
  | smul c g _ hg =>
      rcases hg with ⟨a, rfl⟩
      refine ⟨c • a, ?_⟩
      change c • (a.asHom ≫ f) = (c • a.asHom) ≫ f
      rw [Linear.smul_comp]

/-- Over a commutative source endomorphism ring, cotransit passes from a
generator to every morphism in its principal two-sided span. -/
theorem AllowsCotransit.of_mem_twoSidedEndomorphismSpan
    {X Y : C} {f g : X ⟶ Y}
    (hf : AllowsCotransit f)
    (hcomm : ∀ a b : End X, a * b = b * a)
    (hg : g ∈ twoSidedEndomorphismSpan k f) :
    AllowsCotransit g := by
  obtain ⟨a, rfl⟩ :=
    exists_comp_of_mem_span_of_allowsCotransit hf hg
  intro b
  obtain ⟨c, hc⟩ := hf b
  refine ⟨c, ?_⟩
  calc
    (a.asHom ≫ f) ≫ b.asHom = a.asHom ≫ (f ≫ b.asHom) :=
      Category.assoc _ _ _
    _ = a.asHom ≫ (c.asHom ≫ f) := by rw [hc]
    _ = c.asHom ≫ (a.asHom ≫ f) := by
      simpa only [End.mul_def, Category.assoc] using
        congrArg (fun q : End X ↦ q.asHom ≫ f) (hcomm c a)

/-- Over a commutative target endomorphism ring, transit passes from a
generator to every morphism in its principal two-sided span. -/
theorem AllowsTransit.of_mem_twoSidedEndomorphismSpan
    {X Y : C} {f g : X ⟶ Y}
    (hf : AllowsTransit f)
    (hcomm : ∀ a b : End Y, a * b = b * a)
    (hg : g ∈ twoSidedEndomorphismSpan k f) :
    AllowsTransit g := by
  obtain ⟨b, rfl⟩ :=
    exists_comp_of_mem_span_of_allowsTransit hf hg
  intro a
  obtain ⟨c, hc⟩ := hf a
  refine ⟨c, ?_⟩
  calc
    a.asHom ≫ (f ≫ b.asHom) = (a.asHom ≫ f) ≫ b.asHom := by
      rw [Category.assoc]
    _ = (f ≫ c.asHom) ≫ b.asHom := by rw [hc]
    _ = (f ≫ b.asHom) ≫ c.asHom := by
      simpa only [End.mul_def, Category.assoc] using
        congrArg (fun q : End Y ↦ f ≫ q.asHom) (hcomm b c)

private theorem isNilpotent_of_not_isUnit_of_isArtinian_isLocal
    {R : Type z} [Ring R] [IsLocalRing R] [IsArtinianRing R]
    (x : R) (hx : ¬IsUnit x) : IsNilpotent x := by
  have hxJ : x ∈ Ring.jacobson R :=
    (mem_ringJacobson_iff_not_isUnit R x).2 hx
  obtain ⟨n, hn⟩ :=
    IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rw [Ideal.jacobson_bot] at hn
  refine ⟨n, ?_⟩
  have hpow : x ^ n ∈ (Ring.jacobson R) ^ n :=
    Ideal.pow_mem_pow hxJ n
  rw [hn] at hpow
  simpa using hpow

/-- Every element of the Jacobson radical of an Artinian ring is
nilpotent. -/
theorem isNilpotent_of_mem_jacobson_of_isArtinian
    {R : Type z} [Ring R] [IsArtinianRing R]
    {x : R} (hx : x ∈ Ring.jacobson R) : IsNilpotent x := by
  obtain ⟨n, hn⟩ :=
    IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rw [Ideal.jacobson_bot] at hn
  refine ⟨n, ?_⟩
  have hpow : x ^ n ∈ (Ring.jacobson R) ^ n :=
    Ideal.pow_mem_pow hx n
  rw [hn] at hpow
  simpa using hpow

private theorem eq_zero_of_eq_comp_of_isNilpotent
    {X Y : C} {f : X ⟶ Y} (b : End Y) (hb : IsNilpotent b)
    (h : f = f ≫ b.asHom) : f = 0 := by
  have hu : IsUnit (1 - b) := hb.isUnit_one_sub
  haveI : IsIso ((1 - b).asHom) := (isUnit_iff_isIso _).1 hu
  have hz : f ≫ (1 - b).asHom = 0 := by
    change f ≫ ((𝟙 Y) - b.asHom) = 0
    rw [Preadditive.comp_sub, Category.comp_id]
    exact sub_eq_zero.mpr h
  apply (cancel_mono ((1 - b).asHom)).1
  simpa using hz

private theorem eq_zero_of_eq_comp_left_of_isNilpotent
    {X Y : C} {f : X ⟶ Y} (a : End X) (ha : IsNilpotent a)
    (h : f = a.asHom ≫ f) : f = 0 := by
  have hu : IsUnit (1 - a) := ha.isUnit_one_sub
  haveI : IsIso ((1 - a).asHom) := (isUnit_iff_isIso _).1 hu
  have hz : (1 - a).asHom ≫ f = 0 := by
    change ((𝟙 X) - a.asHom) ≫ f = 0
    rw [Preadditive.sub_comp, Category.id_comp]
    exact sub_eq_zero.mpr h
  apply (cancel_epi ((1 - a).asHom)).1
  simpa using hz

/-- A morphism fixed by multiplication on both sides is zero when the target
endomorphism is nilpotent. -/
theorem eq_zero_of_eq_comp_comp_of_isNilpotent_right
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
              change (a.asHom ≫ (((a ^ m).asHom ≫ f) ≫
                  (b ^ m).asHom)) ≫ b.asHom =
                ((a.asHom ≫ (a ^ m).asHom) ≫ f) ≫
                  ((b ^ m).asHom ≫ b.asHom)
              simp only [Category.assoc]
  have hz : (b ^ n).asHom = (0 : Y ⟶ Y) :=
    congrArg End.asHom hn
  rw [hp n, hz]
  simp

/-- A morphism fixed by multiplication on both sides is zero when the source
endomorphism is nilpotent. -/
theorem eq_zero_of_eq_comp_comp_of_isNilpotent_left
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
              change (a.asHom ≫ (((a ^ m).asHom ≫ f) ≫
                  (b ^ m).asHom)) ≫ b.asHom =
                ((a.asHom ≫ (a ^ m).asHom) ≫ f) ≫
                  ((b ^ m).asHom ≫ b.asHom)
              simp only [Category.assoc]
  have hz : (a ^ n).asHom = (0 : X ⟶ X) :=
    congrArg End.asHom hn
  rw [hp n, hz]
  simp

/-- In a distributive Hom structure with local Artinian endpoint rings,
equality of principal two-sided spans forces equality up to endpoint units. -/
theorem unitRayEquivalent_of_twoSidedEndomorphismSpan_eq
    [∀ X : C, IsLocalRing (End X)]
    [∀ X : C, IsArtinianRing (End X)]
    [HasBGRSDistributiveHomStructure k C]
    {X Y : C} {f g : X ⟶ Y}
    (hspan : twoSidedEndomorphismSpan k f =
      twoSidedEndomorphismSpan k g) :
    UnitRayEquivalent f g := by
  by_cases hf0 : f = 0
  · subst f
    have hg0 : g = 0 := by
      apply (twoSidedEndomorphismSpan_eq_bot_iff k g).1
      rw [← hspan, twoSidedEndomorphismSpan_zero]
    subst g
    exact ⟨Iso.refl X, Iso.refl Y, by simp⟩
  have hgmem : g ∈ twoSidedEndomorphismSpan k f := by
    rw [hspan]
    exact mem_twoSidedEndomorphismSpan k g
  have hfmem : f ∈ twoSidedEndomorphismSpan k g := by
    rw [← hspan]
    exact mem_twoSidedEndomorphismSpan k f
  rcases
      HasBGRSDistributiveHomStructure.transit_or_cotransit
        (k := k) (C := C) f with hfT | hfC <;>
    rcases
      HasBGRSDistributiveHomStructure.transit_or_cotransit
        (k := k) (C := C) g with hgT | hgC
  · obtain ⟨b, hgb⟩ :=
      exists_comp_of_mem_span_of_allowsTransit hfT hgmem
    obtain ⟨d, hfd⟩ :=
      exists_comp_of_mem_span_of_allowsTransit hgT hfmem
    have hb : IsUnit b := by
      by_contra hb
      let e : End Y := d * b
      have he : ¬IsUnit e := by
        intro he
        exact hb (isUnit_of_mul_isUnit_right he)
      have hen :=
        isNilpotent_of_not_isUnit_of_isArtinian_isLocal e he
      have hfix : f = f ≫ e.asHom := by
        calc
          f = g ≫ d.asHom := hfd
          _ = (f ≫ b.asHom) ≫ d.asHom := by rw [hgb]
          _ = f ≫ e.asHom := by
            dsimp [e]
            change (f ≫ b.asHom) ≫ d.asHom =
              f ≫ (b.asHom ≫ d.asHom)
            rw [Category.assoc]
      exact hf0 (eq_zero_of_eq_comp_of_isNilpotent e hen hfix)
    haveI : IsIso b.asHom := (isUnit_iff_isIso _).1 hb
    exact ⟨Iso.refl X, asIso b.asHom, by simpa using hgb⟩
  · obtain ⟨b, hgb⟩ :=
      exists_comp_of_mem_span_of_allowsTransit hfT hgmem
    obtain ⟨c, hfc⟩ :=
      exists_comp_of_mem_span_of_allowsCotransit hgC hfmem
    have hb : IsUnit b := by
      by_contra hb
      have hbn :=
        isNilpotent_of_not_isUnit_of_isArtinian_isLocal b hb
      have hfix : f = (c.asHom ≫ f) ≫ b.asHom := by
        calc
          f = c.asHom ≫ g := hfc
          _ = c.asHom ≫ (f ≫ b.asHom) := by rw [hgb]
          _ = (c.asHom ≫ f) ≫ b.asHom := by rw [Category.assoc]
      exact hf0
        (eq_zero_of_eq_comp_comp_of_isNilpotent_right c b hbn hfix)
    haveI : IsIso b.asHom := (isUnit_iff_isIso _).1 hb
    exact ⟨Iso.refl X, asIso b.asHom, by simpa using hgb⟩
  · obtain ⟨a, hga⟩ :=
      exists_comp_of_mem_span_of_allowsCotransit hfC hgmem
    obtain ⟨d, hfd⟩ :=
      exists_comp_of_mem_span_of_allowsTransit hgT hfmem
    have ha : IsUnit a := by
      by_contra ha
      have han :=
        isNilpotent_of_not_isUnit_of_isArtinian_isLocal a ha
      have hfix : f = (a.asHom ≫ f) ≫ d.asHom := by
        calc
          f = g ≫ d.asHom := hfd
          _ = (a.asHom ≫ f) ≫ d.asHom := by rw [hga]
      exact hf0
        (eq_zero_of_eq_comp_comp_of_isNilpotent_left a d han hfix)
    haveI : IsIso a.asHom := (isUnit_iff_isIso _).1 ha
    exact ⟨asIso a.asHom, Iso.refl Y, by simpa using hga⟩
  · obtain ⟨a, hga⟩ :=
      exists_comp_of_mem_span_of_allowsCotransit hfC hgmem
    obtain ⟨c, hfc⟩ :=
      exists_comp_of_mem_span_of_allowsCotransit hgC hfmem
    have ha : IsUnit a := by
      by_contra ha
      let e : End X := a * c
      have he : ¬IsUnit e := by
        intro he
        exact ha (isUnit_of_mul_isUnit_left he)
      have hen :=
        isNilpotent_of_not_isUnit_of_isArtinian_isLocal e he
      have hfix : f = e.asHom ≫ f := by
        calc
          f = c.asHom ≫ g := hfc
          _ = c.asHom ≫ (a.asHom ≫ f) := by rw [hga]
          _ = e.asHom ≫ f := by
            dsimp [e]
            change c.asHom ≫ (a.asHom ≫ f) =
              (c.asHom ≫ a.asHom) ≫ f
            rw [Category.assoc]
      exact hf0
        (eq_zero_of_eq_comp_left_of_isNilpotent e hen hfix)
    haveI : IsIso a.asHom := (isUnit_iff_isIso _).1 ha
    exact ⟨asIso a.asHom, Iso.refl Y, by simpa using hga⟩

/-- A nonzero morphism cannot acquire full principal two-sided span by
postcomposition with a nonunit endomorphism.  This is the local-Artinian
Nakayama step used when a full composite is cancelled back to one factor. -/
theorem isUnit_of_twoSidedEndomorphismSpan_comp_right_eq_top
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [HasBGRSDistributiveHomStructure k C]
    {X Y : C} (f : X ⟶ Y) (b : End Y)
    (hf : f ≠ 0)
    (hfull : twoSidedEndomorphismSpan k (f ≫ b.asHom) = ⊤) :
    IsUnit b := by
  by_contra hb
  have hbn :=
    isNilpotent_of_not_isUnit_of_isArtinian_isLocal b hb
  have hfmem : f ∈ twoSidedEndomorphismSpan k (f ≫ b.asHom) := by
    rw [hfull]
    exact Submodule.mem_top
  rcases HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := C) (f ≫ b.asHom) with hT | hC
  · obtain ⟨c, hfc⟩ :=
      exists_comp_of_mem_span_of_allowsTransit hT hfmem
    let e : End Y := c * b
    have he : ¬ IsUnit e := by
      intro he
      apply hb
      apply isUnit_of_mul_isUnit_right
      simpa [e]
    have hen :=
      isNilpotent_of_not_isUnit_of_isArtinian_isLocal e he
    have hfix : f = f ≫ e.asHom := by
      calc
        f = (f ≫ b.asHom) ≫ c.asHom := hfc
        _ = f ≫ e.asHom := by
          simp only [e, End.mul_def, Category.assoc]
    exact hf (eq_zero_of_eq_comp_of_isNilpotent e hen hfix)
  · obtain ⟨a, hfa⟩ :=
      exists_comp_of_mem_span_of_allowsCotransit hC hfmem
    have hfix : f = (a.asHom ≫ f) ≫ b.asHom := by
      calc
        f = a.asHom ≫ (f ≫ b.asHom) := hfa
        _ = (a.asHom ≫ f) ≫ b.asHom := by
          rw [Category.assoc]
    exact hf
      (eq_zero_of_eq_comp_comp_of_isNilpotent_right a b hbn hfix)

/-- A nonzero morphism cannot acquire full principal two-sided span by
precomposition with a nonunit endomorphism.  This is the source-end dual of
`isUnit_of_twoSidedEndomorphismSpan_comp_right_eq_top`. -/
theorem isUnit_of_twoSidedEndomorphismSpan_comp_left_eq_top
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [HasBGRSDistributiveHomStructure k C]
    {X Y : C} (a : End X) (f : X ⟶ Y)
    (hf : f ≠ 0)
    (hfull : twoSidedEndomorphismSpan k (a.asHom ≫ f) = ⊤) :
    IsUnit a := by
  by_contra ha
  have han :=
    isNilpotent_of_not_isUnit_of_isArtinian_isLocal a ha
  have hfmem : f ∈ twoSidedEndomorphismSpan k (a.asHom ≫ f) := by
    rw [hfull]
    exact Submodule.mem_top
  rcases HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := C) (a.asHom ≫ f) with hT | hC
  · obtain ⟨b, hfb⟩ :=
      exists_comp_of_mem_span_of_allowsTransit hT hfmem
    have hfix : f = (a.asHom ≫ f) ≫ b.asHom := hfb
    exact hf
      (eq_zero_of_eq_comp_comp_of_isNilpotent_left a b han hfix)
  · obtain ⟨c, hfc⟩ :=
      exists_comp_of_mem_span_of_allowsCotransit hC hfmem
    let e : End X := a * c
    have he : ¬ IsUnit e := by
      intro he
      apply ha
      apply isUnit_of_mul_isUnit_left
      simpa [e]
    have hen :=
      isNilpotent_of_not_isUnit_of_isArtinian_isLocal e he
    have hfix : f = e.asHom ≫ f := by
      calc
        f = c.asHom ≫ (a.asHom ≫ f) := hfc
        _ = e.asHom ≫ f := by
          simp only [e, End.mul_def, Category.assoc]
    exact hf (eq_zero_of_eq_comp_left_of_isNilpotent e hen hfix)

/-- BGRS distributive Hom structure makes principal two-sided spans a
comparable, ray-classifying family. -/
instance hasClassifyingComparableUnitRaySpans_of_bgrsDistributiveHomStructure
    [∀ X : C, IsLocalRing (End X)]
    [∀ X : C, IsArtinianRing (End X)]
    [HasBGRSDistributiveHomStructure k C] :
    HasClassifyingComparableUnitRaySpans k C where
  span_injective X Y r s hrs := by
    induction r using Quotient.inductionOn' with
    | _ f =>
        induction s using Quotient.inductionOn' with
        | _ g =>
            apply (unitRay_eq_iff f g).2
            exact unitRayEquivalent_of_twoSidedEndomorphismSpan_eq hrs
  span_comparable r s :=
    HasBGRSDistributiveHomStructure.homSubbimodule_comparable
      (k := k) (C := C)
      (r.twoSidedEndomorphismSpan k) (s.twoSidedEndomorphismSpan k)
      (by
        induction r using Quotient.inductionOn' with
        | _ f => exact isHomSubbimodule_twoSidedEndomorphismSpan f)
      (by
        induction s using Quotient.inductionOn' with
        | _ f => exact isHomSubbimodule_twoSidedEndomorphismSpan f)

/-- If a nonunit source endomorphism transfers across a nonzero morphism,
then the transferred target endomorphism is again a nonunit. -/
theorem not_isUnit_right_of_transfer
    {X Y : C}
    [IsLocalRing (End X)] [IsArtinianRing (End X)]
    {f : X ⟶ Y} (hf : f ≠ 0)
    (a : End X) (b : End Y) (ha : ¬ IsUnit a)
    (hab : a.asHom ≫ f = f ≫ b.asHom) :
    ¬ IsUnit b := by
  intro hb
  have han := isNilpotent_of_not_isUnit_of_isArtinian_isLocal a ha
  haveI : IsIso b.asHom := (isUnit_iff_isIso _).1 hb
  have hfix :
      f = (a.asHom ≫ f) ≫ inv b.asHom := by
    rw [hab]
    simp [Category.assoc]
  exact hf
    (eq_zero_of_eq_comp_comp_of_isNilpotent_left
      a (inv b.asHom) han hfix)

/-- If a nonunit target endomorphism transfers across a nonzero morphism,
then the transferred source endomorphism is again a nonunit. -/
theorem not_isUnit_left_of_transfer
    {X Y : C}
    [IsLocalRing (End Y)] [IsArtinianRing (End Y)]
    {f : X ⟶ Y} (hf : f ≠ 0)
    (a : End X) (b : End Y) (hb : ¬ IsUnit b)
    (hab : a.asHom ≫ f = f ≫ b.asHom) :
    ¬ IsUnit a := by
  intro ha
  have hbn := isNilpotent_of_not_isUnit_of_isArtinian_isLocal b hb
  haveI : IsIso a.asHom := (isUnit_iff_isIso _).1 ha
  have hfix :
      f = (inv a.asHom ≫ f) ≫ b.asHom := by
    calc
      f = inv a.asHom ≫ (a.asHom ≫ f) := by simp
      _ = inv a.asHom ≫ (f ≫ b.asHom) := by rw [hab]
      _ = (inv a.asHom ≫ f) ≫ b.asHom := by
            rw [Category.assoc]
  exact hf
    (eq_zero_of_eq_comp_comp_of_isNilpotent_right
      (inv a.asHom) b hbn hfix)

/-- Precomposition by a nonzero cotransit morphism preserves two-sided unit
ray equivalence.  Cotransit moves the intervening source unit to an endpoint
unit. -/
theorem unitRayEquivalent_precomp_of_allowsCotransit
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    {X Y Z : C} (p : X ⟶ Y) {f g : Y ⟶ Z}
    (hp0 : p ≠ 0) (hpC : AllowsCotransit p)
    (hfg : UnitRayEquivalent f g) :
    UnitRayEquivalent (p ≫ f) (p ≫ g) := by
  rcases hfg with ⟨a, b, rfl⟩
  obtain ⟨c, hc⟩ := hpC (End.of a.hom)
  have hcUnit : IsUnit c := by
    by_contra hcNonunit
    have haNonunit : ¬IsUnit (End.of a.hom) :=
      not_isUnit_right_of_transfer hp0 c (End.of a.hom) hcNonunit hc.symm
    exact haNonunit ((isUnit_iff_isIso _).2 inferInstance)
  letI : IsIso c.asHom := (isUnit_iff_isIso _).1 hcUnit
  refine ⟨asIso c.asHom, b, ?_⟩
  calc
    p ≫ (a.hom ≫ f ≫ b.hom) = (p ≫ a.hom) ≫ f ≫ b.hom := by
      simp only [Category.assoc]
    _ = (c.asHom ≫ p) ≫ f ≫ b.hom := by rw [hc]
    _ = (asIso c.asHom).hom ≫ (p ≫ f) ≫ b.hom := by
      simp only [asIso_hom, Category.assoc]

/-- Postcomposition by a nonzero transit morphism preserves two-sided unit
ray equivalence.  Transit moves the intervening target unit to an endpoint
unit. -/
theorem unitRayEquivalent_postcomp_of_allowsTransit
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    {X Y Z : C} {f g : X ⟶ Y} (q : Y ⟶ Z)
    (hq0 : q ≠ 0) (hqT : AllowsTransit q)
    (hfg : UnitRayEquivalent f g) :
    UnitRayEquivalent (f ≫ q) (g ≫ q) := by
  rcases hfg with ⟨a, b, rfl⟩
  obtain ⟨c, hc⟩ := hqT (End.of b.hom)
  have hcUnit : IsUnit c := by
    by_contra hcNonunit
    have hbNonunit : ¬IsUnit (End.of b.hom) :=
      not_isUnit_left_of_transfer hq0 (End.of b.hom) c hcNonunit hc
    exact hbNonunit ((isUnit_iff_isIso _).2 inferInstance)
  letI : IsIso c.asHom := (isUnit_iff_isIso _).1 hcUnit
  refine ⟨a, asIso c.asHom, ?_⟩
  calc
    (a.hom ≫ f ≫ b.hom) ≫ q = a.hom ≫ f ≫ (b.hom ≫ q) := by
      simp only [Category.assoc]
    _ = a.hom ≫ f ≫ (q ≫ c.asHom) := by rw [hc]
    _ = a.hom ≫ (f ≫ q) ≫ (asIso c.asHom).hom := by
      simp only [asIso_hom, Category.assoc]

/-- A nonzero composite starting in an endomorphism which commutes with its
endpoint ring is not a BGRS exceptional-zero pair. -/
theorem not_isBGRSSpecialZero_of_left_end_comm_of_comp_ne_zero
    {X Y : C} [IsArtinianRing (End X)] (a : End X) (f : X ⟶ Y)
    (hcomm : ∀ b : End X,
      a.asHom ≫ b.asHom = b.asHom ≫ a.asHom)
    (haf0 : a.asHom ≫ f ≠ 0) :
    ¬IsBGRSSpecialZero a.asHom f := by
  rintro ⟨rho, hrho⟩
  have hfix : a.asHom ≫ f =
      rho.1.asHom ≫ (a.asHom ≫ f) := by
    calc
      a.asHom ≫ f = (a.asHom ≫ rho.1.asHom) ≫ f := hrho
      _ = (rho.1.asHom ≫ a.asHom) ≫ f := by rw [hcomm rho.1]
      _ = rho.1.asHom ≫ (a.asHom ≫ f) := by
        simp only [Category.assoc]
  have hu : IsUnit (1 - rho.1) :=
    (isNilpotent_of_mem_jacobson_of_isArtinian rho.2).isUnit_one_sub
  letI : IsIso (1 - rho.1).asHom := (isUnit_iff_isIso _).1 hu
  have hz : (1 - rho.1).asHom ≫ (a.asHom ≫ f) = 0 := by
    change ((𝟙 X) - rho.1.asHom) ≫ (a.asHom ≫ f) = 0
    rw [Preadditive.sub_comp, Category.id_comp]
    exact sub_eq_zero.mpr hfix
  apply haf0
  apply (cancel_epi (1 - rho.1).asHom).1
  simpa using hz

/-- Target-end dual of
`not_isBGRSSpecialZero_of_left_end_comm_of_comp_ne_zero`. -/
theorem not_isBGRSSpecialZero_of_right_end_comm_of_comp_ne_zero
    {X Y : C} [IsArtinianRing (End Y)] (f : X ⟶ Y) (a : End Y)
    (hcomm : ∀ b : End Y,
      a.asHom ≫ b.asHom = b.asHom ≫ a.asHom)
    (hfa0 : f ≫ a.asHom ≠ 0) :
    ¬IsBGRSSpecialZero f a.asHom := by
  rintro ⟨rho, hrho⟩
  have hfix : f ≫ a.asHom =
      (f ≫ a.asHom) ≫ rho.1.asHom := by
    calc
      f ≫ a.asHom = (f ≫ rho.1.asHom) ≫ a.asHom := hrho
      _ = f ≫ (rho.1.asHom ≫ a.asHom) := by
        simp only [Category.assoc]
      _ = f ≫ (a.asHom ≫ rho.1.asHom) := by rw [hcomm rho.1]
      _ = (f ≫ a.asHom) ≫ rho.1.asHom := by
        simp only [Category.assoc]
  have hu : IsUnit (1 - rho.1) :=
    (isNilpotent_of_mem_jacobson_of_isArtinian rho.2).isUnit_one_sub
  letI : IsIso (1 - rho.1).asHom := (isUnit_iff_isIso _).1 hu
  have hz : (f ≫ a.asHom) ≫ (1 - rho.1).asHom = 0 := by
    change (f ≫ a.asHom) ≫ ((𝟙 Y) - rho.1.asHom) = 0
    rw [Preadditive.comp_sub, Category.comp_id]
    exact sub_eq_zero.mpr hfix
  apply hfa0
  apply (cancel_mono (1 - rho.1).asHom).1
  simpa using hz

/-- A nonzero composite ending in a nonzero transit morphism is not a BGRS
exceptional-zero pair.  Transit moves a hypothetical radical middle factor to
a nonunit target endomorphism; Artinian local nilpotence then forces the
composite to vanish. -/
theorem not_isBGRSSpecialZero_of_allowsTransit_right_of_comp_ne_zero
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg0 : g ≠ 0) (hgT : AllowsTransit g)
    (hfg0 : f ≫ g ≠ 0) : ¬IsBGRSSpecialZero f g := by
  rintro ⟨rho, hrho⟩
  obtain ⟨b, hb⟩ := hgT rho.1
  have hrhoNonunit : ¬IsUnit rho.1 :=
    (mem_ringJacobson_iff_not_isUnit (End Y) rho.1).1 rho.2
  have hbNonunit : ¬IsUnit b :=
    not_isUnit_right_of_transfer hg0 rho.1 b hrhoNonunit hb
  have hbJ : b ∈ Ring.jacobson (End Z) :=
    (mem_ringJacobson_iff_not_isUnit (End Z) b).2 hbNonunit
  have hbNil : IsNilpotent b :=
    isNilpotent_of_mem_jacobson_of_isArtinian hbJ
  have hfixed : f ≫ g =
      ((1 : End X).asHom ≫ (f ≫ g)) ≫ b.asHom := by
    calc
      f ≫ g = (f ≫ rho.1.asHom) ≫ g := hrho
      _ = f ≫ (rho.1.asHom ≫ g) := Category.assoc _ _ _
      _ = f ≫ (g ≫ b.asHom) := by rw [hb]
      _ = (f ≫ g) ≫ b.asHom := by rw [Category.assoc]
      _ = ((1 : End X).asHom ≫ (f ≫ g)) ≫ b.asHom := by simp
  exact hfg0
    (eq_zero_of_eq_comp_comp_of_isNilpotent_right
      (1 : End X) b hbNil hfixed)

private theorem isUnit_sub_of_isUnit_of_not_isUnit
    {R : Type z} [Ring R] [IsLocalRing R]
    (a b : R) (ha : IsUnit a) (hb : ¬ IsUnit b) :
    IsUnit (a - b) := by
  by_contra hab
  have hsum : ¬ IsUnit ((a - b) + b) :=
    IsLocalRing.nonunits_add hab hb
  exact hsum (by simpa using ha)

/-- A unit inserted at the target of a cotransit morphism can be moved to a
source unit without changing the composite's unit ray. -/
theorem unitRayEquivalent_middleUnit_of_allowsCotransit_left
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf0 : f ≠ 0) (hfC : AllowsCotransit f)
    (m : End Y) (hm : IsUnit m) :
    UnitRayEquivalent (f ≫ g) ((f ≫ m.asHom) ≫ g) := by
  obtain ⟨a, ha⟩ := hfC m
  have hau : IsUnit a := by
    by_contra hna
    exact
      (not_isUnit_right_of_transfer hf0 a m hna ha.symm) hm
  haveI : IsIso a.asHom := (isUnit_iff_isIso _).1 hau
  refine ⟨asIso a.asHom, Iso.refl Z, ?_⟩
  calc
    (f ≫ m.asHom) ≫ g = (a.asHom ≫ f) ≫ g := by rw [ha]
    _ = (asIso a.asHom).hom ≫ (f ≫ g) ≫ (Iso.refl Z).hom := by
      simp [Category.assoc]

/-- A unit inserted at the source of a transit morphism can be moved to a
target unit without changing the composite's unit ray. -/
theorem unitRayEquivalent_middleUnit_of_allowsTransit_right
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hg0 : g ≠ 0) (hgT : AllowsTransit g)
    (m : End Y) (hm : IsUnit m) :
    UnitRayEquivalent (f ≫ g) ((f ≫ m.asHom) ≫ g) := by
  obtain ⟨b, hb⟩ := hgT m
  have hbu : IsUnit b := by
    by_contra hnb
    exact
      (not_isUnit_left_of_transfer hg0 m b hnb hb) hm
  haveI : IsIso b.asHom := (isUnit_iff_isIso _).1 hbu
  refine ⟨Iso.refl X, asIso b.asHom, ?_⟩
  calc
    (f ≫ m.asHom) ≫ g = f ≫ (m.asHom ≫ g) := by
      rw [Category.assoc]
    _ = f ≫ (g ≫ b.asHom) := by rw [hb]
    _ = (Iso.refl X).hom ≫ (f ≫ g) ≫ (asIso b.asHom).hom := by
      simp [Category.assoc]

/-- In the crossed transit/cotransit case, comparability of principal Hom
subbimodules forces every nonzero middle-unit twist into the original unit
ray. -/
theorem unitRayEquivalent_middleUnit_of_allowsTransit_cotransit
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [HasBGRSDistributiveHomStructure k C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfT : AllowsTransit f) (hgC : AllowsCotransit g)
    (hnz : ∀ u : End Y, IsUnit u → (f ≫ u.asHom) ≫ g ≠ 0)
    (m : End Y) (hm : IsUnit m) :
    UnitRayEquivalent (f ≫ g) ((f ≫ m.asHom) ≫ g) := by
  have hbase : f ≫ g ≠ 0 := by
    simpa using hnz (1 : End Y) isUnit_one
  have hf0 : f ≠ 0 := by
    intro hf
    exact hbase (by simp [hf])
  have hg0 : g ≠ 0 := by
    intro hg
    exact hbase (by simp [hg])
  rcases
      HasBGRSDistributiveHomStructure.homSubbimodule_comparable
        (k := k) (C := C)
        (twoSidedEndomorphismSpan k (f ≫ g))
        (twoSidedEndomorphismSpan k ((f ≫ m.asHom) ≫ g))
        (isHomSubbimodule_twoSidedEndomorphismSpan (f ≫ g))
        (isHomSubbimodule_twoSidedEndomorphismSpan
          ((f ≫ m.asHom) ≫ g)) with hle | hle
  · by_cases hrev :
        twoSidedEndomorphismSpan k ((f ≫ m.asHom) ≫ g) ≤
          twoSidedEndomorphismSpan k (f ≫ g)
    · exact unitRayEquivalent_of_twoSidedEndomorphismSpan_eq
        (le_antisymm hle hrev)
    · have hmem :
          f ≫ g ∈
            twoSidedEndomorphismSpan k ((f ≫ m.asHom) ≫ g) :=
        hle (mem_twoSidedEndomorphismSpan k (f ≫ g))
      rcases
          HasBGRSDistributiveHomStructure.transit_or_cotransit
            (k := k) (C := C) ((f ≫ m.asHom) ≫ g) with hT | hC
      · obtain ⟨b, hb⟩ :=
          exists_comp_of_mem_span_of_allowsTransit hT hmem
        have hbnu : ¬ IsUnit b := by
          intro hbu
          haveI : IsIso b.asHom := (isUnit_iff_isIso _).1 hbu
          have hre :
              UnitRayEquivalent ((f ≫ m.asHom) ≫ g) (f ≫ g) :=
            ⟨Iso.refl X, asIso b.asHom, by simpa using hb⟩
          exact hrev
            (twoSidedEndomorphismSpan_eq_of_unitRayEquivalent k hre).le
        obtain ⟨c, hc⟩ := hgC b
        have hcnu : ¬ IsUnit c :=
          not_isUnit_left_of_transfer hg0 c b hbnu hc.symm
        have hcmnu : ¬ IsUnit (c * m) := by
          intro hcm
          exact hcnu (isUnit_of_mul_isUnit_left hcm)
        have hu : IsUnit (1 - c * m) :=
          isUnit_sub_of_isUnit_of_not_isUnit
            (1 : End Y) (c * m) isUnit_one hcmnu
        exfalso
        apply (hnz (1 - c * m) hu)
        change (f ≫ (((𝟙 Y) - (c * m).asHom))) ≫ g = 0
        rw [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp]
        apply sub_eq_zero.mpr
        calc
          f ≫ g = ((f ≫ m.asHom) ≫ g) ≫ b.asHom := hb
          _ = (f ≫ m.asHom) ≫ (g ≫ b.asHom) := by
                rw [Category.assoc]
          _ = (f ≫ m.asHom) ≫ (c.asHom ≫ g) := by rw [hc]
          _ = (f ≫ (c * m).asHom) ≫ g := by
                rw [End.mul_def]
                simp only [Category.assoc]
      · obtain ⟨a, ha⟩ :=
          exists_comp_of_mem_span_of_allowsCotransit hC hmem
        have hanu : ¬ IsUnit a := by
          intro hau
          haveI : IsIso a.asHom := (isUnit_iff_isIso _).1 hau
          have hre :
              UnitRayEquivalent ((f ≫ m.asHom) ≫ g) (f ≫ g) :=
            ⟨asIso a.asHom, Iso.refl Z, by simpa using ha⟩
          exact hrev
            (twoSidedEndomorphismSpan_eq_of_unitRayEquivalent k hre).le
        obtain ⟨c, hc⟩ := hfT a
        have hcnu : ¬ IsUnit c :=
          not_isUnit_right_of_transfer hf0 a c hanu hc
        have hmcnu : ¬ IsUnit (m * c) := by
          intro hmc
          exact hcnu (isUnit_of_mul_isUnit_right hmc)
        have hu : IsUnit (1 - m * c) :=
          isUnit_sub_of_isUnit_of_not_isUnit
            (1 : End Y) (m * c) isUnit_one hmcnu
        exfalso
        apply (hnz (1 - m * c) hu)
        change (f ≫ (((𝟙 Y) - (m * c).asHom))) ≫ g = 0
        rw [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp]
        apply sub_eq_zero.mpr
        calc
          f ≫ g = a.asHom ≫ ((f ≫ m.asHom) ≫ g) := ha
          _ = ((a.asHom ≫ f) ≫ m.asHom) ≫ g := by
                simp only [Category.assoc]
          _ = ((f ≫ c.asHom) ≫ m.asHom) ≫ g := by rw [hc]
          _ = (f ≫ (m * c).asHom) ≫ g := by
                rw [End.mul_def]
                simp only [Category.assoc]
  · by_cases hrev :
        twoSidedEndomorphismSpan k (f ≫ g) ≤
          twoSidedEndomorphismSpan k ((f ≫ m.asHom) ≫ g)
    · exact unitRayEquivalent_of_twoSidedEndomorphismSpan_eq
        (le_antisymm hrev hle)
    · have hmem :
          (f ≫ m.asHom) ≫ g ∈
            twoSidedEndomorphismSpan k (f ≫ g) :=
        hle (mem_twoSidedEndomorphismSpan k ((f ≫ m.asHom) ≫ g))
      rcases
          HasBGRSDistributiveHomStructure.transit_or_cotransit
            (k := k) (C := C) (f ≫ g) with hT | hC
      · obtain ⟨b, hb⟩ :=
          exists_comp_of_mem_span_of_allowsTransit hT hmem
        have hbnu : ¬ IsUnit b := by
          intro hbu
          haveI : IsIso b.asHom := (isUnit_iff_isIso _).1 hbu
          have hre :
              UnitRayEquivalent (f ≫ g) ((f ≫ m.asHom) ≫ g) :=
            ⟨Iso.refl X, asIso b.asHom, by simpa using hb⟩
          exact hrev
            (twoSidedEndomorphismSpan_eq_of_unitRayEquivalent k hre).le
        obtain ⟨c, hc⟩ := hgC b
        have hcnu : ¬ IsUnit c :=
          not_isUnit_left_of_transfer hg0 c b hbnu hc.symm
        have hu : IsUnit (m - c) :=
          isUnit_sub_of_isUnit_of_not_isUnit m c hm hcnu
        exfalso
        apply (hnz (m - c) hu)
        change (f ≫ (m.asHom - c.asHom)) ≫ g = 0
        rw [Preadditive.comp_sub, Preadditive.sub_comp]
        apply sub_eq_zero.mpr
        calc
          (f ≫ m.asHom) ≫ g = (f ≫ g) ≫ b.asHom := hb
          _ = f ≫ (g ≫ b.asHom) := by rw [Category.assoc]
          _ = f ≫ (c.asHom ≫ g) := by rw [hc]
          _ = (f ≫ c.asHom) ≫ g := by rw [Category.assoc]
      · obtain ⟨a, ha⟩ :=
          exists_comp_of_mem_span_of_allowsCotransit hC hmem
        have hanu : ¬ IsUnit a := by
          intro hau
          haveI : IsIso a.asHom := (isUnit_iff_isIso _).1 hau
          have hre :
              UnitRayEquivalent (f ≫ g) ((f ≫ m.asHom) ≫ g) :=
            ⟨asIso a.asHom, Iso.refl Z, by simpa using ha⟩
          exact hrev
            (twoSidedEndomorphismSpan_eq_of_unitRayEquivalent k hre).le
        obtain ⟨c, hc⟩ := hfT a
        have hcnu : ¬ IsUnit c :=
          not_isUnit_right_of_transfer hf0 a c hanu hc
        have hu : IsUnit (m - c) :=
          isUnit_sub_of_isUnit_of_not_isUnit m c hm hcnu
        exfalso
        apply (hnz (m - c) hu)
        change (f ≫ (m.asHom - c.asHom)) ≫ g = 0
        rw [Preadditive.comp_sub, Preadditive.sub_comp]
        apply sub_eq_zero.mpr
        calc
          (f ≫ m.asHom) ≫ g = a.asHom ≫ (f ≫ g) := ha
          _ = (a.asHom ≫ f) ≫ g := by rw [Category.assoc]
          _ = (f ≫ c.asHom) ≫ g := by rw [hc]

/-- Distributive Hom structure turns nonvanishing of all middle-unit twists
into the BGRS common-ray conclusion. -/
theorem unitRayEquivalent_middleUnit_of_bgrsDistributiveHomStructure
    [∀ T : C, IsLocalRing (End T)]
    [∀ T : C, IsArtinianRing (End T)]
    [HasBGRSDistributiveHomStructure k C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hnz : ∀ u : End Y, IsUnit u → (f ≫ u.asHom) ≫ g ≠ 0)
    (m : End Y) (hm : IsUnit m) :
    UnitRayEquivalent (f ≫ g) ((f ≫ m.asHom) ≫ g) := by
  have hbase : f ≫ g ≠ 0 := by
    simpa using hnz (1 : End Y) isUnit_one
  have hf0 : f ≠ 0 := by
    intro hf
    exact hbase (by simp [hf])
  have hg0 : g ≠ 0 := by
    intro hg
    exact hbase (by simp [hg])
  rcases
      HasBGRSDistributiveHomStructure.transit_or_cotransit
        (k := k) (C := C) f with hfT | hfC
  · rcases
        HasBGRSDistributiveHomStructure.transit_or_cotransit
          (k := k) (C := C) g with hgT | hgC
    · exact unitRayEquivalent_middleUnit_of_allowsTransit_right
        (C := C) hg0 hgT m hm
    · exact unitRayEquivalent_middleUnit_of_allowsTransit_cotransit
        (k := k) (C := C) f g hfT hgC hnz m hm
  · exact unitRayEquivalent_middleUnit_of_allowsCotransit_left
      (C := C) hf0 hfC m hm

omit [Preadditive C] in
private theorem bgrsCancellation_unitRayEquivalent_symm
    {X Y : C} {f g : X ⟶ Y}
    (h : UnitRayEquivalent f g) : UnitRayEquivalent g f := by
  apply (unitRay_eq_iff g f).mp
  exact ((unitRay_eq_iff f g).mpr h).symm

private theorem bgrsCancellation_ne_zero_of_unitRayEquivalent
    {X Y : C} {f g : X ⟶ Y}
    (h : UnitRayEquivalent f g) (hf : f ≠ 0) : g ≠ 0 := by
  intro hg
  subst g
  apply hf
  exact (unitRay_eq_zero_iff f).mp ((unitRay_eq_iff f 0).mpr h)

omit [Preadditive C] in
private theorem bgrsCancellation_unitRayEquivalent_of_eq_comp_right_of_isUnit
    {X Y : C} {f g : X ⟶ Y} (b : End Y) (hb : IsUnit b)
    (h : f = g ≫ b.asHom) : UnitRayEquivalent f g := by
  haveI : IsIso b.asHom := (isUnit_iff_isIso _).1 hb
  refine ⟨Iso.refl X, (asIso b.asHom).symm, ?_⟩
  rw [h]
  simp

omit [Preadditive C] in
private theorem bgrsCancellation_unitRayEquivalent_of_eq_comp_left_of_isUnit
    {X Y : C} {f g : X ⟶ Y} (a : End X) (ha : IsUnit a)
    (h : f = a.asHom ≫ g) : UnitRayEquivalent f g := by
  haveI : IsIso a.asHom := (isUnit_iff_isIso _).1 ha
  refine ⟨(asIso a.asHom).symm, Iso.refl Y, ?_⟩
  rw [h]
  simp

private theorem bgrsCancellation_cancel_right_of_span_le
    [∀ X : C, IsLocalRing (End X)]
    [∀ X : C, IsArtinianRing (End X)]
    [HasBGRSDistributiveHomStructure k C]
    {X Y Z : C} (f g : X ⟶ Y) (h : Y ⟶ Z)
    (hspan : twoSidedEndomorphismSpan k f ≤
      twoSidedEndomorphismSpan k g)
    (heq : UnitRayEquivalent
      (bgrsRayRepresentativeProduct f h)
      (bgrsRayRepresentativeProduct g h))
    (hn : bgrsRayRepresentativeProduct f h ≠ 0) :
    UnitRayEquivalent f g := by
  have hfns : ¬ IsBGRSSpecialZero f h := by
    intro hs
    exact hn (bgrsRayRepresentativeProduct_eq_zero_of_special hs)
  have hgnProd : bgrsRayRepresentativeProduct g h ≠ 0 :=
    bgrsCancellation_ne_zero_of_unitRayEquivalent heq hn
  have hgns : ¬ IsBGRSSpecialZero g h := by
    intro hs
    exact hgnProd (bgrsRayRepresentativeProduct_eq_zero_of_special hs)
  have hgn : g ≫ h ≠ 0 := by
    simpa [bgrsRayRepresentativeProduct_eq_comp_of_not_special hgns] using
      hgnProd
  have heqComp : UnitRayEquivalent (f ≫ h) (g ≫ h) := by
    simpa [bgrsRayRepresentativeProduct_eq_comp_of_not_special hfns,
      bgrsRayRepresentativeProduct_eq_comp_of_not_special hgns] using heq
  rcases heqComp with ⟨u, v, huv⟩
  let uEnd : End X := u.hom
  let vEnd : End Z := v.hom
  have hfmem : f ∈ twoSidedEndomorphismSpan k g :=
    hspan (mem_twoSidedEndomorphismSpan k f)
  rcases HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := C) g with hgT | hgC
  · obtain ⟨b, hfb⟩ :=
      exists_comp_of_mem_span_of_allowsTransit hgT hfmem
    by_cases hb : IsUnit b
    · exact
        bgrsCancellation_unitRayEquivalent_of_eq_comp_right_of_isUnit
          b hb hfb
    · have hbn :=
        isNilpotent_of_not_isUnit_of_isArtinian_isLocal b hb
      rcases HasBGRSDistributiveHomStructure.transit_or_cotransit
          (k := k) (C := C) h with hhT | hhC
      · obtain ⟨c, hbc⟩ := hhT b
        have hc : ¬ IsUnit c := by
          intro hc
          haveI : IsIso c.asHom := (isUnit_iff_isIso _).1 hc
          have hh0 : h = 0 :=
            eq_zero_of_eq_comp_comp_of_isNilpotent_left
              b (inv c.asHom) hbn (by
                calc
                  h = (h ≫ c.asHom) ≫ inv c.asHom := by simp
                  _ = (b.asHom ≫ h) ≫ inv c.asHom := by rw [hbc])
          exact hgn (by simp [hh0])
        let e : End Z := vEnd * c
        have he : ¬ IsUnit e := by
          intro he
          apply hc
          apply isUnit_of_mul_isUnit_right
          simpa [e]
        have hen :=
          isNilpotent_of_not_isUnit_of_isArtinian_isLocal e he
        have hfix : g ≫ h =
            ((uEnd.asHom ≫ (g ≫ h)) ≫ e.asHom) := by
          calc
            g ≫ h = u.hom ≫ (f ≫ h) ≫ v.hom := huv
            _ = u.hom ≫ ((g ≫ b.asHom) ≫ h) ≫ v.hom := by
              rw [hfb]
            _ = u.hom ≫ (g ≫ (h ≫ c.asHom)) ≫ v.hom := by
              rw [← hbc]
              simp only [Category.assoc]
            _ = ((uEnd.asHom ≫ (g ≫ h)) ≫ e.asHom) := by
              change u.hom ≫ (g ≫ (h ≫ c.asHom)) ≫ v.hom =
                (u.hom ≫ (g ≫ h)) ≫ (c.asHom ≫ v.hom)
              simp only [Category.assoc]
        exact (hgn
          (eq_zero_of_eq_comp_comp_of_isNilpotent_right
            uEnd e hen hfix)).elim
      · obtain ⟨d, hud⟩ := hgT uEnd
        obtain ⟨c, hvc⟩ := hhC vEnd
        have hud' : u.hom ≫ g = g ≫ d.asHom := by
          simpa [uEnd] using hud
        have hvc' : h ≫ v.hom = c.asHom ≫ h := by
          simpa [vEnd] using hvc
        let ρ : End Y := (c * b) * d
        have hρnot : ¬ IsUnit ρ := by
          intro hρ
          have hcb : IsUnit (c * b) := isUnit_of_mul_isUnit_left hρ
          exact hb (isUnit_of_mul_isUnit_right hcb)
        have hρJ : ρ ∈ Ring.jacobson (End Y) :=
          (mem_ringJacobson_iff_not_isUnit (End Y) ρ).2 hρnot
        have hs : IsBGRSSpecialZero g h := by
          refine ⟨⟨ρ, hρJ⟩, ?_⟩
          calc
            g ≫ h = u.hom ≫ (f ≫ h) ≫ v.hom := huv
            _ = u.hom ≫ ((g ≫ b.asHom) ≫ h) ≫ v.hom := by
              rw [hfb]
            _ = ((u.hom ≫ g) ≫ b.asHom) ≫ (h ≫ v.hom) := by
              simp only [Category.assoc]
            _ = ((g ≫ d.asHom) ≫ b.asHom) ≫ (c.asHom ≫ h) := by
              rw [hud', hvc']
            _ = (g ≫ ρ.asHom) ≫ h := by
              change ((g ≫ d.asHom) ≫ b.asHom) ≫ (c.asHom ≫ h) =
                (g ≫ (d.asHom ≫ b.asHom ≫ c.asHom)) ≫ h
              simp only [Category.assoc]
        exact (hgns hs).elim
  · obtain ⟨a, hfa⟩ :=
      exists_comp_of_mem_span_of_allowsCotransit hgC hfmem
    by_cases ha : IsUnit a
    · exact
        bgrsCancellation_unitRayEquivalent_of_eq_comp_left_of_isUnit
          a ha hfa
    · let e : End X := a * uEnd
      have he : ¬ IsUnit e := by
        intro he
        apply ha
        apply isUnit_of_mul_isUnit_left
        simpa [e]
      have hen :=
        isNilpotent_of_not_isUnit_of_isArtinian_isLocal e he
      have hfix : g ≫ h =
          ((e.asHom ≫ (g ≫ h)) ≫ vEnd.asHom) := by
        calc
          g ≫ h = u.hom ≫ (f ≫ h) ≫ v.hom := huv
          _ = u.hom ≫ ((a.asHom ≫ g) ≫ h) ≫ v.hom := by
            rw [hfa]
          _ = ((e.asHom ≫ (g ≫ h)) ≫ vEnd.asHom) := by
            change u.hom ≫ ((a.asHom ≫ g) ≫ h) ≫ v.hom =
              ((u.hom ≫ a.asHom) ≫ (g ≫ h)) ≫ v.hom
            simp only [Category.assoc]
      exact (hgn
        (eq_zero_of_eq_comp_comp_of_isNilpotent_left
          e vEnd hen hfix)).elim

/-- Right cancellation for the representative-level BGRS product follows
from distributive Hom structure and local Artinian endomorphism rings. -/
theorem bgrsRayRepresentativeProduct_cancel_right_of_bgrsDistributiveHomStructure
    [∀ X : C, IsLocalRing (End X)]
    [∀ X : C, IsArtinianRing (End X)]
    [HasBGRSDistributiveHomStructure k C]
    {X Y Z : C} (f g : X ⟶ Y) (h : Y ⟶ Z)
    (heq : UnitRayEquivalent
      (bgrsRayRepresentativeProduct f h)
      (bgrsRayRepresentativeProduct g h))
    (hn : bgrsRayRepresentativeProduct f h ≠ 0) :
    UnitRayEquivalent f g := by
  rcases HasBGRSDistributiveHomStructure.homSubbimodule_comparable
      (k := k) (C := C)
      (twoSidedEndomorphismSpan k f) (twoSidedEndomorphismSpan k g)
      (isHomSubbimodule_twoSidedEndomorphismSpan f)
      (isHomSubbimodule_twoSidedEndomorphismSpan g) with hfg | hgf
  · exact bgrsCancellation_cancel_right_of_span_le f g h hfg heq hn
  · have hgn : bgrsRayRepresentativeProduct g h ≠ 0 :=
      bgrsCancellation_ne_zero_of_unitRayEquivalent heq hn
    have heq' : UnitRayEquivalent
        (bgrsRayRepresentativeProduct g h)
        (bgrsRayRepresentativeProduct f h) :=
      bgrsCancellation_unitRayEquivalent_symm heq
    exact bgrsCancellation_unitRayEquivalent_symm
      (bgrsCancellation_cancel_right_of_span_le g f h hgf heq' hgn)

private theorem bgrsCancellation_cancel_left_of_span_le
    [∀ X : C, IsLocalRing (End X)]
    [∀ X : C, IsArtinianRing (End X)]
    [HasBGRSDistributiveHomStructure k C]
    {X Y Z : C} (h : X ⟶ Y) (f g : Y ⟶ Z)
    (hspan : twoSidedEndomorphismSpan k f ≤
      twoSidedEndomorphismSpan k g)
    (heq : UnitRayEquivalent
      (bgrsRayRepresentativeProduct h f)
      (bgrsRayRepresentativeProduct h g))
    (hn : bgrsRayRepresentativeProduct h f ≠ 0) :
    UnitRayEquivalent f g := by
  have hfns : ¬ IsBGRSSpecialZero h f := by
    intro hs
    exact hn (bgrsRayRepresentativeProduct_eq_zero_of_special hs)
  have hgnProd : bgrsRayRepresentativeProduct h g ≠ 0 :=
    bgrsCancellation_ne_zero_of_unitRayEquivalent heq hn
  have hgns : ¬ IsBGRSSpecialZero h g := by
    intro hs
    exact hgnProd (bgrsRayRepresentativeProduct_eq_zero_of_special hs)
  have hgn : h ≫ g ≠ 0 := by
    simpa [bgrsRayRepresentativeProduct_eq_comp_of_not_special hgns] using
      hgnProd
  have heqComp : UnitRayEquivalent (h ≫ f) (h ≫ g) := by
    simpa [bgrsRayRepresentativeProduct_eq_comp_of_not_special hfns,
      bgrsRayRepresentativeProduct_eq_comp_of_not_special hgns] using heq
  rcases heqComp with ⟨u, v, huv⟩
  let uEnd : End X := u.hom
  let vEnd : End Z := v.hom
  have hfmem : f ∈ twoSidedEndomorphismSpan k g :=
    hspan (mem_twoSidedEndomorphismSpan k f)
  rcases HasBGRSDistributiveHomStructure.transit_or_cotransit
      (k := k) (C := C) g with hgT | hgC
  · obtain ⟨b, hfb⟩ :=
      exists_comp_of_mem_span_of_allowsTransit hgT hfmem
    by_cases hb : IsUnit b
    · exact
        bgrsCancellation_unitRayEquivalent_of_eq_comp_right_of_isUnit
          b hb hfb
    · let e : End Z := vEnd * b
      have he : ¬ IsUnit e := by
        intro he
        apply hb
        apply isUnit_of_mul_isUnit_right
        simpa [e]
      have hen :=
        isNilpotent_of_not_isUnit_of_isArtinian_isLocal e he
      have hfix : h ≫ g =
          ((uEnd.asHom ≫ (h ≫ g)) ≫ e.asHom) := by
        calc
          h ≫ g = u.hom ≫ (h ≫ f) ≫ v.hom := huv
          _ = u.hom ≫ (h ≫ (g ≫ b.asHom)) ≫ v.hom := by
            rw [hfb]
          _ = ((uEnd.asHom ≫ (h ≫ g)) ≫ e.asHom) := by
            change u.hom ≫ (h ≫ (g ≫ b.asHom)) ≫ v.hom =
              (u.hom ≫ (h ≫ g)) ≫ (b.asHom ≫ v.hom)
            simp only [Category.assoc]
      exact (hgn
        (eq_zero_of_eq_comp_comp_of_isNilpotent_right
          uEnd e hen hfix)).elim
  · obtain ⟨a, hfa⟩ :=
      exists_comp_of_mem_span_of_allowsCotransit hgC hfmem
    by_cases ha : IsUnit a
    · exact
        bgrsCancellation_unitRayEquivalent_of_eq_comp_left_of_isUnit
          a ha hfa
    · have han :=
        isNilpotent_of_not_isUnit_of_isArtinian_isLocal a ha
      rcases HasBGRSDistributiveHomStructure.transit_or_cotransit
          (k := k) (C := C) h with hhT | hhC
      · obtain ⟨d, hud⟩ := hhT uEnd
        obtain ⟨c, hvc⟩ := hgC vEnd
        have hud' : u.hom ≫ h = h ≫ d.asHom := by
          simpa [uEnd] using hud
        have hvc' : g ≫ v.hom = c.asHom ≫ g := by
          simpa [vEnd] using hvc
        let ρ : End Y := (c * a) * d
        have hρnot : ¬ IsUnit ρ := by
          intro hρ
          have hca : IsUnit (c * a) := isUnit_of_mul_isUnit_left hρ
          exact ha (isUnit_of_mul_isUnit_right hca)
        have hρJ : ρ ∈ Ring.jacobson (End Y) :=
          (mem_ringJacobson_iff_not_isUnit (End Y) ρ).2 hρnot
        have hs : IsBGRSSpecialZero h g := by
          refine ⟨⟨ρ, hρJ⟩, ?_⟩
          calc
            h ≫ g = u.hom ≫ (h ≫ f) ≫ v.hom := huv
            _ = u.hom ≫ (h ≫ (a.asHom ≫ g)) ≫ v.hom := by
              rw [hfa]
            _ = ((u.hom ≫ h) ≫ a.asHom) ≫ (g ≫ v.hom) := by
              simp only [Category.assoc]
            _ = ((h ≫ d.asHom) ≫ a.asHom) ≫ (c.asHom ≫ g) := by
              rw [hud', hvc']
            _ = (h ≫ ρ.asHom) ≫ g := by
              change ((h ≫ d.asHom) ≫ a.asHom) ≫ (c.asHom ≫ g) =
                (h ≫ (d.asHom ≫ a.asHom ≫ c.asHom)) ≫ g
              simp only [Category.assoc]
        exact (hgns hs).elim
      · obtain ⟨c, hac⟩ := hhC a
        have hc : ¬ IsUnit c := by
          intro hc
          haveI : IsIso c.asHom := (isUnit_iff_isIso _).1 hc
          have hh0 : h = 0 :=
            eq_zero_of_eq_comp_comp_of_isNilpotent_right
              (inv c.asHom) a han (by
                calc
                  h = inv c.asHom ≫ (c.asHom ≫ h) := by simp
                  _ = inv c.asHom ≫ (h ≫ a.asHom) := by rw [← hac]
                  _ = (inv c.asHom ≫ h) ≫ a.asHom := by
                    simp only [Category.assoc])
          exact hgn (by simp [hh0])
        let e : End X := c * uEnd
        have he : ¬ IsUnit e := by
          intro he
          apply hc
          apply isUnit_of_mul_isUnit_left
          simpa [e]
        have hen :=
          isNilpotent_of_not_isUnit_of_isArtinian_isLocal e he
        have hfix : h ≫ g =
            ((e.asHom ≫ (h ≫ g)) ≫ vEnd.asHom) := by
          calc
            h ≫ g = u.hom ≫ (h ≫ f) ≫ v.hom := huv
            _ = u.hom ≫ (h ≫ (a.asHom ≫ g)) ≫ v.hom := by
              rw [hfa]
            _ = u.hom ≫ ((c.asHom ≫ h) ≫ g) ≫ v.hom := by
              rw [← hac]
              simp only [Category.assoc]
            _ = ((e.asHom ≫ (h ≫ g)) ≫ vEnd.asHom) := by
              change u.hom ≫ ((c.asHom ≫ h) ≫ g) ≫ v.hom =
                ((u.hom ≫ c.asHom) ≫ (h ≫ g)) ≫ v.hom
              simp only [Category.assoc]
        exact (hgn
          (eq_zero_of_eq_comp_comp_of_isNilpotent_left
            e vEnd hen hfix)).elim

/-- Left cancellation for the representative-level BGRS product follows from
distributive Hom structure and local Artinian endomorphism rings. -/
theorem bgrsRayRepresentativeProduct_cancel_left_of_bgrsDistributiveHomStructure
    [∀ X : C, IsLocalRing (End X)]
    [∀ X : C, IsArtinianRing (End X)]
    [HasBGRSDistributiveHomStructure k C]
    {X Y Z : C} (h : X ⟶ Y) (f g : Y ⟶ Z)
    (heq : UnitRayEquivalent
      (bgrsRayRepresentativeProduct h f)
      (bgrsRayRepresentativeProduct h g))
    (hn : bgrsRayRepresentativeProduct h f ≠ 0) :
    UnitRayEquivalent f g := by
  rcases HasBGRSDistributiveHomStructure.homSubbimodule_comparable
      (k := k) (C := C)
      (twoSidedEndomorphismSpan k f) (twoSidedEndomorphismSpan k g)
      (isHomSubbimodule_twoSidedEndomorphismSpan f)
      (isHomSubbimodule_twoSidedEndomorphismSpan g) with hfg | hgf
  · exact bgrsCancellation_cancel_left_of_span_le h f g hfg heq hn
  · have hgn : bgrsRayRepresentativeProduct h g ≠ 0 :=
      bgrsCancellation_ne_zero_of_unitRayEquivalent heq hn
    have heq' : UnitRayEquivalent
        (bgrsRayRepresentativeProduct h g)
        (bgrsRayRepresentativeProduct h f) :=
      bgrsCancellation_unitRayEquivalent_symm heq
    exact bgrsCancellation_unitRayEquivalent_symm
      (bgrsCancellation_cancel_left_of_span_le h g f hgf heq' hgn)

end LargeIndecomposable
