module

public import LargeIndecomposable.RayCategories.Distributive.FromDistributive
public import LargeIndecomposable.RayCategories.Basic.Factor
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# A small model of a ray category

For a category `P` whose Hom-types are `w`-small (for instance finite),
`RaySmall.{w} P` has the same objects (wrapped) and Hom-types
`Shrink.{w} (X ⟶ Y)`; zero morphisms and the ray axioms transfer along
`equivShrink`. This gives a model of the ray category of an algebra in
`Category.{0}`, as required by the covering data.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe w v u

namespace RayCat

/-- The small model of `P`. -/
structure RaySmall (P : Type u) where
  /-- The underlying object. -/
  as : P

namespace RaySmall

variable {P : Type u} [Category.{v} P] [LocallySmall.{w} P]

noncomputable instance category : Category.{w} (RaySmall.{u} P) where
  Hom X Y := Shrink.{w} (X.as ⟶ Y.as)
  id X := equivShrink _ (𝟙 X.as)
  comp f g := equivShrink _ ((equivShrink _).symm f ≫ (equivShrink _).symm g)
  id_comp f := by simp
  comp_id f := by simp
  assoc f g h := by simp

/-- The Hom-equivalence. -/
def sh {X Y : RaySmall.{u} P} : (X.as ⟶ Y.as) ≃ (X ⟶ Y) := equivShrink.{w} (X.as ⟶ Y.as)

lemma sh_comp {X Y Z : RaySmall.{u} P} (f : X.as ⟶ Y.as) (g : Y.as ⟶ Z.as) :
    sh.{w} (f ≫ g) = sh f ≫ sh g := by
  change _ = equivShrink _ ((equivShrink _).symm (equivShrink _ f) ≫
    (equivShrink _).symm (equivShrink _ g))
  simp only [Equiv.symm_apply_apply]
  rfl

lemma sh_symm_comp {X Y Z : RaySmall.{u} P} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (sh.{w}).symm (f ≫ g) = (sh.{w}).symm f ≫ (sh.{w}).symm g := by
  rw [Equiv.symm_apply_eq, sh_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

lemma sh_id (X : RaySmall.{u} P) : sh.{w} (𝟙 X.as) = 𝟙 X := rfl

variable [HasZeroMorphisms P]

noncomputable instance hasZeroMorphisms : HasZeroMorphisms (RaySmall.{u} P) where
  zero X Y := ⟨sh.{w} (0 : X.as ⟶ Y.as)⟩
  comp_zero {X Y} f Z := by
    change sh ((sh).symm f ≫ (sh).symm (sh (0 : Y.as ⟶ Z.as))) = sh 0
    rw [Equiv.symm_apply_apply, comp_zero]
  zero_comp X {Y Z} f := by
    change sh ((sh).symm (sh (0 : X.as ⟶ Y.as)) ≫ (sh).symm f) = sh 0
    rw [Equiv.symm_apply_apply, zero_comp]

lemma sh_zero (X Y : RaySmall.{u} P) : sh.{w} (0 : X.as ⟶ Y.as) = 0 := rfl

lemma sh_eq_zero_iff {X Y : RaySmall.{u} P} (f : X.as ⟶ Y.as) : sh.{w} f = 0 ↔ f = 0 := by
  rw [← sh_zero, (sh.{w}).apply_eq_iff_eq]

omit [HasZeroMorphisms P] in
/-- `P ⥤ RaySmall P`. -/
@[simps]
def toSmall : P ⥤ RaySmall.{u} P where
  obj x := ⟨x⟩
  map f := sh.{w} f
  map_comp f g := sh_comp f g

omit [HasZeroMorphisms P] in
/-- `RaySmall P ⥤ P`. -/
@[simps]
def fromSmall : RaySmall.{u} P ⥤ P where
  obj X := X.as
  map f := (sh.{w}).symm f
  map_id X := by rw [← sh_id, Equiv.symm_apply_apply]
  map_comp f g := sh_symm_comp f g

omit [HasZeroMorphisms P] in
lemma isIso_sh_iff {X Y : RaySmall.{u} P} (f : X.as ⟶ Y.as) : IsIso (sh.{w} f) ↔ IsIso f := by
  constructor
  · intro h
    have := (fromSmall.{w}).map_isIso (sh.{w} f)
    simp only [fromSmall_map, Equiv.symm_apply_apply] at this
    exact this
  · intro h
    exact (toSmall.{w}).map_isIso f

lemma isIrreducible_sh_iff {X Y : RaySmall.{u} P} (f : X.as ⟶ Y.as) :
    IsIrreducible (sh.{w} f) ↔ IsIrreducible f := by
  constructor
  · rintro ⟨h0, hi, hf⟩
    refine ⟨fun h ↦ h0 ((sh_eq_zero_iff f).2 h), fun h ↦ hi ((isIso_sh_iff f).2 h),
      fun z g h hgh ↦ ?_⟩
    rcases hf ⟨z⟩ (sh g) (sh h) (by rw [hgh, sh_comp]) with h1 | h1
    · exact Or.inl ((isIso_sh_iff g).1 h1)
    · exact Or.inr ((isIso_sh_iff h).1 h1)
  · rintro ⟨h0, hi, hf⟩
    refine ⟨fun h ↦ h0 ((sh_eq_zero_iff f).1 h), fun h ↦ hi ((isIso_sh_iff f).1 h),
      fun z g h hgh ↦ ?_⟩
    rcases hf z.as ((sh.{w}).symm g) ((sh.{w}).symm h)
      (by rw [← sh_symm_comp, ← hgh, Equiv.symm_apply_apply]) with h1 | h1
    · left
      rw [← Equiv.apply_symm_apply sh g]
      exact (isIso_sh_iff _).2 h1
    · right
      rw [← Equiv.apply_symm_apply sh h]
      exact (isIso_sh_iff _).2 h1

instance finite [Finite P] : Finite (RaySmall.{u} P) :=
  Finite.of_injective RaySmall.as fun X Y h ↦ by cases X; cases Y; cases h; rfl

omit [HasZeroMorphisms P] in
lemma sh_rpow [HasZeroMorphisms P] {X : RaySmall.{u} P} (e : X.as ⟶ X.as) :
    ∀ n, rpow (sh.{w} e) n = sh.{w} (rpow e n)
  | 0 => rfl
  | n + 1 => by rw [rpow_succ, rpow_succ, sh_rpow e n, sh_comp]

/-- The ray axioms transfer to the small model. -/
instance isRayCategory [IsRayCategory P] : IsRayCategory (RaySmall.{u} P) where
  skeletal X Y h := by
    obtain ⟨e⟩ := h
    have := IsRayCategory.skeletal ⟨(fromSmall.{w}).mapIso e⟩
    cases X; cases Y
    simp only [fromSmall_obj] at this
    rw [this]
  finite_out X := by
    refine (Set.Finite.image (fun y : P ↦ (⟨y⟩ : RaySmall.{u} P))
      (IsRayCategory.finite_out X.as)).subset ?_
    rintro ⟨y⟩ ⟨f, hf⟩
    refine ⟨y, ⟨(sh.{w}).symm f, fun h ↦ hf ?_⟩, rfl⟩
    rw [← Equiv.apply_symm_apply sh f, h, sh_zero]
  finite_in X := by
    refine (Set.Finite.image (fun y : P ↦ (⟨y⟩ : RaySmall.{u} P))
      (IsRayCategory.finite_in X.as)).subset ?_
    rintro ⟨y⟩ ⟨f, hf⟩
    refine ⟨y, ⟨(sh.{w}).symm f, fun h ↦ hf ?_⟩, rfl⟩
    rw [← Equiv.apply_symm_apply sh f, h, sh_zero]
  finite_hom X Y := by
    have := IsRayCategory.finite_hom X.as Y.as
    exact Finite.of_equiv _ sh
  id_ne_zero X h := IsRayCategory.id_ne_zero X.as ((sh_eq_zero_iff _).1 h)
  nil X e he := by
    obtain ⟨n, hn⟩ := IsRayCategory.nil X.as ((sh.{w}).symm e) fun h ↦ he (by
      rw [← Equiv.apply_symm_apply sh e, h]; rfl)
    refine ⟨n, ?_⟩
    rw [← Equiv.apply_symm_apply sh e, sh_rpow, hn, sh_zero]

omit [HasZeroMorphisms P] in
lemma sh_pow {X : RaySmall.{u} P} (e : End X.as) (n : ℕ) :
    ((End.of (sh.{w} e)) ^ n : End X) = sh.{w} ((e ^ n : End X.as) : X.as ⟶ X.as) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, End.mul_def, End.mul_def, ih]
    exact (sh_comp _ _).symm

/-- The ray axioms transfer to the small model. -/
instance isFiniteRayCategory [LargeIndecomposable.IsFiniteRayCategory P] :
    LargeIndecomposable.IsFiniteRayCategory (RaySmall.{u} P) where
  id_ne_zero X h := LargeIndecomposable.IsFiniteRayCategory.id_ne_zero X.as ((sh_eq_zero_iff _).1 h)
  hom_finite X Y := by
    have := LargeIndecomposable.IsFiniteRayCategory.hom_finite X.as Y.as
    exact Finite.of_equiv _ sh
  endomorphism_nilpotent {X} f hf := by
    have hf' : ((sh.{w}).symm f : End X.as) ≠ 𝟙 X.as := fun h ↦ hf (by
      rw [← Equiv.apply_symm_apply sh f]
      exact (congrArg sh h).trans (sh_id X))
    obtain ⟨n, hn, hfn⟩ := LargeIndecomposable.IsFiniteRayCategory.endomorphism_nilpotent _ hf'
    refine ⟨n, hn, ?_⟩
    have := sh_pow (X := X) ((sh.{w}).symm f) n
    rw [Equiv.apply_symm_apply] at this
    change End.of f ^ n = 0
    rw [this, hfn]
    rfl
  skeletal {X Y} h := by
    obtain ⟨e⟩ := h
    have := LargeIndecomposable.IsFiniteRayCategory.skeletal ⟨(fromSmall.{w}).mapIso e⟩
    cases X; cases Y
    simp only [fromSmall_obj] at this
    rw [this]
  factorization_comparable f g := by
    rcases LargeIndecomposable.IsFiniteRayCategory.factorization_comparable
      ((sh.{w}).symm f) ((sh.{w}).symm g) with ⟨a, b, h⟩ | ⟨a, b, h⟩
    · refine Or.inl ⟨End.of (sh a), End.of (sh b), ?_⟩
      rw [← Equiv.apply_symm_apply sh g, h]
      change sh ((a ≫ _) ≫ b) = (sh a ≫ f) ≫ sh b
      rw [sh_comp, sh_comp, Equiv.apply_symm_apply]
    · refine Or.inr ⟨End.of (sh a), End.of (sh b), ?_⟩
      rw [← Equiv.apply_symm_apply sh f, h]
      change sh ((a ≫ _) ≫ b) = (sh a ≫ g) ≫ sh b
      rw [sh_comp, sh_comp, Equiv.apply_symm_apply]
  source_stabilizer_trivial {X Y Z} f g a h0 h := by
    have h0' : (sh.{w}).symm f ≫ (sh.{w}).symm g ≠ 0 := by
      rw [← sh_symm_comp]
      intro h'
      apply h0
      rw [← Equiv.apply_symm_apply sh (f ≫ g), h']
      rfl
    have h' : ((sh.{w}).symm a ≫ (sh.{w}).symm f) ≫ (sh.{w}).symm g =
        (sh.{w}).symm f ≫ (sh.{w}).symm g := by
      rw [← sh_symm_comp, ← sh_symm_comp, ← sh_symm_comp]
      exact congrArg _ h
    have := LargeIndecomposable.IsFiniteRayCategory.source_stabilizer_trivial _ _
      ((sh.{w}).symm a : End X.as) h0' h'
    rw [← Equiv.apply_symm_apply sh a]
    exact (congrArg sh this).trans (sh_id X)

end RaySmall

end RayCat

end LargeIndecomposable
