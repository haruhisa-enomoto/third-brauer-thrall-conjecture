module

public import LargeIndecomposable.MultiplicativeBases.Twisted.AssemblyScalar
public import LargeIndecomposable.RayCategories.Distributive.RayTablePresentation
public import LargeIndecomposable.RayCategories.Distributive.DistribRayBasis
public import LargeIndecomposable.MultiplicativeBases.Twisted.MulBasis

/-!
# A twisted multiplicative basis from a zero-detecting lift

Let `L` be a lift of the arrows of the ray category of a split basic
distributive algebra `B` whose path values vanish exactly on zero ray paths,
and such that parallel paths with the same nonzero value have proportional
values. Choosing one path for each nonzero ray, the values form a twisted
multiplicative basis of `B` over the (small model of the) ray category
(`SplitBasicData.mulBasisOfLift`; BGRS 2.9–2.10).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable RayQuiver RayCat RayCat.RaySmall
  LargeIndecomposable

namespace SplitBasicData

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {B : Type u} [Ring B] [Algebra k B]
  [FiniteDimensional k B] {ι : Type} [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι)
  [HasBGRSDistributiveHomStructure k S.toIdempotents.ProjectiveCategory]
  [LocallySmall.{0} S.toIdempotents.RayCategory]
  [IsFiniteRayCategory S.toIdempotents.RayCategory] [Finite S.toIdempotents.RayCategory]
  (L : BGRSRayArrowLift (C := S.toIdempotents.ProjectiveCategory))

lemma exists_rayPath {a b : S.toIdempotents.RayCategory} (μ : a ⟶ b) (hμ : μ ≠ 0) :
    ∃ p : Quiver.Path (RayVertex.mk b) (RayVertex.mk a), rayPathMap p = μ := by
  let fNonzero : NonzeroHom a b := ⟨μ, hμ⟩
  obtain ⟨p⟩ := rayPathPresentation_nonempty_of_finite fNonzero
  exact ⟨p.path, p.map_eq⟩

open Classical in
/-- The representative of a ray: the value of a chosen path. -/
def rval {a b : S.toIdempotents.RayCategory} (μ : a ⟶ b) : a.as ⟶ b.as :=
  if hμ : μ = 0 then 0 else L.pathMap (S.exists_rayPath μ hμ).choose

lemma rval_zero {a b : S.toIdempotents.RayCategory} : S.rval L (0 : a ⟶ b) = 0 := by
  simp [rval]

lemma rval_of_ne {a b : S.toIdempotents.RayCategory} (μ : a ⟶ b) (hμ : μ ≠ 0) :
    S.rval L μ = L.pathMap (S.exists_rayPath μ hμ).choose := by
  simp [rval, hμ]

variable {S L}

variable (hzero : ∀ {i j : RayVertex S.toIdempotents.RayCategory} (p : Quiver.Path i j),
      L.pathMap p = 0 ↔ rayPathMap p = 0)
  (hscalar : ∀ {i j : RayVertex S.toIdempotents.RayCategory} {p q : Quiver.Path i j},
      (rayPathContourRelation (C := S.toIdempotents.RayCategory)).related p q →
      (S.toIdempotents.scalarRel L).related p q)

include hzero in
lemma rval_ne_zero {a b : S.toIdempotents.RayCategory} (μ : a ⟶ b) (hμ : μ ≠ 0) : S.rval L μ ≠ 0 := by
  rw [S.rval_of_ne L μ hμ]
  intro h0
  exact hμ ((S.exists_rayPath μ hμ).choose_spec ▸ (hzero _).1 h0)

include hzero hscalar in
/-- **Multiplicativity up to scalars**: the representatives of composable rays
multiply to a nonzero multiple of the representative of the product, or to
zero. -/
lemma rval_comp {a b c : S.toIdempotents.RayCategory} (μ : a ⟶ b) (ν : b ⟶ c) :
    (μ ≫ ν ≠ 0 → ∃ t : kˣ, S.rval L μ ≫ S.rval L ν = (t : k) • S.rval L (μ ≫ ν)) ∧
      (μ ≫ ν = 0 → S.rval L μ ≫ S.rval L ν = 0) := by
  by_cases hμ : μ = 0
  · subst hμ
    refine ⟨fun h ↦ absurd (zero_comp) h, fun _ ↦ ?_⟩
    rw [S.rval_zero L, zero_comp]
  by_cases hν : ν = 0
  · subst hν
    refine ⟨fun h ↦ absurd (comp_zero) h, fun _ ↦ ?_⟩
    rw [S.rval_zero L, comp_zero]
  set p := (S.exists_rayPath ν hν).choose
  set q := (S.exists_rayPath μ hμ).choose
  have hp : rayPathMap p = ν := (S.exists_rayPath ν hν).choose_spec
  have hq : rayPathMap q = μ := (S.exists_rayPath μ hμ).choose_spec
  have hpq : rayPathMap (p.comp q) = μ ≫ ν := by
    simp only [rayPathMap, LinearPathCategory.pathMap_comp]
    change rayPathMap q ≫ rayPathMap p = _
    rw [hp, hq]
  have hL : L.pathMap (p.comp q) = S.rval L μ ≫ S.rval L ν := by
    rw [S.rval_of_ne L μ hμ, S.rval_of_ne L ν hν]
    simp only [BGRSRayArrowLift.pathMap, LinearPathCategory.pathMap_comp]
    rfl
  refine ⟨fun hne ↦ ?_, fun h0 ↦ ?_⟩
  · set r := (S.exists_rayPath (μ ≫ ν) hne).choose
    have hr : rayPathMap r = μ ≫ ν := (S.exists_rayPath (μ ≫ ν) hne).choose_spec
    obtain ⟨-, t, ht⟩ := hscalar (p := p.comp q) (q := r) ⟨by rw [hpq]; exact hne, hpq.trans hr.symm⟩
    refine ⟨t, ?_⟩
    rw [← hL, S.rval_of_ne L (μ ≫ ν) hne]
    exact ht
  · rw [← hL]
    exact (hzero _).2 (hpq.trans h0)

lemma rval_id (a : S.toIdempotents.RayCategory) : S.rval L (𝟙 a) = 𝟙 a.as := by
  have h1 : (𝟙 a : a ⟶ a) ≠ 0 := IsFiniteRayCategory.id_ne_zero a
  rw [S.rval_of_ne L _ h1]
  have key : ∀ p : Quiver.Path (RayVertex.mk a) (RayVertex.mk a), rayPathMap p = 𝟙 a →
      L.pathMap p = 𝟙 _ := by
    intro p hp
    cases p with
    | nil => exact LinearPathCategory.pathMap_nil _ _ _
    | cons p e =>
        exact absurd (hp ▸ (inferInstance : IsIso (𝟙 a)))
          (rayPathMap_not_isIso_of_length_ne_zero _ (by simp))
  exact key _ (S.exists_rayPath (𝟙 a) h1).choose_spec

lemma eq_one_of_smul_self {X Y : S.toIdempotents.ProjectiveCategory} {x : X ⟶ Y} (hx : x ≠ 0) {t : kˣ}
    (h : x = (t : k) • x) : t = 1 := by
  have h2 : ((t : k) - 1) • x = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact Units.ext (sub_eq_zero.1 h3)
  · exact absurd h3 hx

variable [IsRayCategory (RaySmall.{0} S.toIdempotents.RayCategory)]
  [Fintype (RaySmall.{0} S.toIdempotents.RayCategory)] [DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory)]

include hzero in
/-- The chosen value of a nonzero ray lies in the ray of its representative. -/
lemma elt_mem_ray (r : NZ (RaySmall.{0} S.toIdempotents.RayCategory)) :
    (S.rval L ((sh.{0}).symm r.2.2.1)).1 ∈
      S.primitiveIdempotents.ray (k := k) (S.labelP r.2.1) (S.labelP r.1) (S.betaP r) := by
  obtain ⟨X, Y, f, hf⟩ := r
  have hμ : (sh.{0}).symm f ≠ 0 := S.sh_symm_ne_zero hf
  have hspec := (S.exists_rayPath ((sh.{0}).symm f) hμ).choose_spec
  have hu : (unitRay (S.rval L ((sh.{0}).symm f)) : X.as ⟶ Y.as) = (sh.{0}).symm f := by
    rw [S.rval_of_ne L _ hμ]
    exact (L.unitRay_pathMap_eq_rayPathMap_of_ne_zero _ (by rw [hspec]; exact hμ)).trans hspec
  have hequiv : UnitRayEquivalent (S.repP f) (S.rval L ((sh.{0}).symm f)) :=
    (unitRay_eq_iff _ _).1 ((S.unitRay_repP f).trans hu.symm)
  exact (S.unitRayEquivalent_iff _ _).1 hequiv

/-- The ray of the representative of a nonzero morphism. -/
def rayOf (r : NZ (RaySmall.{0} S.toIdempotents.RayCategory)) : S.primitiveIdempotents.NonzeroRay k :=
  ⟨S.primitiveIdempotents.ray (k := k) (S.labelP r.2.1) (S.labelP r.1) (S.betaP r),
    _, _, _, S.betaP_mem_corner r, S.betaP_ne_zero r, rfl⟩

lemma rayOf_bijective : Function.Bijective (rayOf (S := S) (k := k)) := by
  constructor
  · intro r s h
    apply S.betaP_inj r s
    have h1 := congrArg Subtype.val h
    change S.primitiveIdempotents.ray (k := k) (S.labelP r.2.1) (S.labelP r.1) (S.betaP r) =
      S.primitiveIdempotents.ray (k := k) (S.labelP s.2.1) (S.labelP s.1) (S.betaP s) at h1
    rw [← h1]
    exact S.primitiveIdempotents.mem_ray_self (S.betaP_mem_corner r)
  · rintro ⟨_, x, y, f, hf, hf0, rfl⟩
    obtain ⟨r, hx, hy, hr⟩ := S.betaP_surj x y f hf hf0
    refine ⟨r, Subtype.ext ?_⟩
    change S.primitiveIdempotents.ray (k := k) (S.labelP r.2.1) (S.labelP r.1) (S.betaP r) = S.primitiveIdempotents.ray (k := k) x y f
    rw [hx, hy]
    have hc := S.betaP_mem_corner r
    rw [hx, hy] at hc
    exact (S.primitiveIdempotents.ray_eq_of_mem hc hr).symm

include hzero in
/-- **The chosen values form a basis** (one per nonzero ray; BGRS 1.7). -/
theorem elt_basis (hfinI : (Set.univ : Set (TwoSidedIdeal B)).Finite) :
    LinearIndependent k (fun μ : NZ (RaySmall.{0} S.toIdempotents.RayCategory) ↦
      (S.rval L ((sh.{0}).symm μ.2.2.1)).1) ∧
    Submodule.span k (Set.range fun μ : NZ (RaySmall.{0} S.toIdempotents.RayCategory) ↦
      (S.rval L ((sh.{0}).symm μ.2.2.1)).1) = ⊤ := by
  let φ := Equiv.ofBijective _ (rayOf_bijective (S := S) (k := k))
  let b : S.primitiveIdempotents.NonzeroRay k → B := fun s ↦ (S.rval L ((sh.{0}).symm (φ.symm s).2.2.1)).1
  have hb : S.primitiveIdempotents.IsRayTransversal (k := k) b := by
    refine ⟨fun s ↦ ?_, fun s x hx ↦ ?_⟩
    · have hs : s.1 = (rayOf (φ.symm s)).1 := congrArg Subtype.val (φ.apply_symm_apply s).symm
      rw [hs]
      exact elt_mem_ray hzero (φ.symm s)
    · have hs : s.1 = (rayOf (φ.symm s)).1 := congrArg Subtype.val (φ.apply_symm_apply s).symm
      change b s = _
      simp only [b]
      generalize φ.symm s = r at hs
      rw [hs] at hx
      obtain ⟨X, Y, f, hf⟩ := r
      change S.primitiveIdempotents.e x ∈ S.primitiveIdempotents.ray (k := k) (S.labelP Y) (S.labelP X) (S.betaP ⟨X, Y, f, hf⟩) at hx
      have hc := S.primitiveIdempotents.ray_subset_corner (S.betaP_mem_corner ⟨X, Y, f, hf⟩) hx
      have hex : S.primitiveIdempotents.e x ≠ 0 := fun h ↦
        S.primitiveIdempotents.e_not_mem_radical (k := k) x (h ▸ zero_mem _)
      obtain ⟨h1, h2⟩ := S.primitiveIdempotents.corner_unique (S.primitiveIdempotents.e_mem_corner x) hc hex
      have hXY : X = Y := S.labelEquiv.injective (h2.symm.trans h1)
      subst hXY h2
      have hbx0 : S.betaP ⟨X, X, f, hf⟩ ∈ S.primitiveIdempotents.ray (k := k) (S.labelP X) (S.labelP X)
          (S.primitiveIdempotents.e (S.labelP X)) :=
        S.primitiveIdempotents.ray_symm (S.betaP_mem_corner ⟨X, X, f, hf⟩) hx
      have hbx : S.betaP ⟨X, X, f, hf⟩ ∈ S.primitiveIdempotents.ray (k := k) (S.pidx X.as.as) (S.pidx X.as.as)
          (𝟙 X.as.as : X.as.as ⟶ X.as.as).1 := by
        rw [S.id_val']
        exact hbx0
      have hu : UnitRayEquivalent (𝟙 X.as.as) (S.repP f) := (S.unitRayEquivalent_iff _ _).2 hbx
      have hf1 : (sh.{0}).symm f = 𝟙 X.as := by
        rw [← S.unitRay_repP, ← (unitRay_eq_iff _ _).2 hu]
        rfl
      change (S.rval L ((sh.{0}).symm f)).1 = _
      rw [hf1, rval_id, S.id_val']
      rfl
  obtain ⟨hli, hspan, -⟩ := S.primitiveIdempotents.rayTransversal_isBasis_fin hb hfinI
  have hcomp : (fun μ : NZ (RaySmall.{0} S.toIdempotents.RayCategory) ↦
      (S.rval L ((sh.{0}).symm μ.2.2.1)).1) = b ∘ φ := by
    funext μ
    simp only [b, Function.comp_apply]
    rw [φ.symm_apply_apply]
  refine ⟨?_, ?_⟩
  · rw [hcomp]
    exact hli.comp φ φ.injective
  · rw [hcomp, Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
    exact hspan

include hzero hscalar in
open Classical in
/-- **The twisted multiplicative basis** (BGRS 2.10): values of chosen paths. -/
def mulBasisOfLift
    (hLI : LinearIndependent k fun μ : NZ (RaySmall.{0} S.toIdempotents.RayCategory) ↦
      (S.rval L ((sh.{0}).symm μ.2.2.1)).1)
    (hspan : Submodule.span k (Set.range fun μ : NZ (RaySmall.{0} S.toIdempotents.RayCategory) ↦
      (S.rval L ((sh.{0}).symm μ.2.2.1)).1) = ⊤) :
    RayQuiver.MulBasis k (RaySmall.{0} S.toIdempotents.RayCategory) B where
  elt f := (S.rval L ((sh.{0}).symm f)).1
  tw f g := if h : (sh.{0}).symm f ≫ (sh.{0}).symm g ≠ 0 then
      ((rval_comp hzero hscalar ((sh.{0}).symm f) ((sh.{0}).symm g)).1 h).choose else 1
  elt_zero := by
    intro x y
    have : (sh.{0}).symm (0 : x ⟶ y) = 0 := by
      rw [Equiv.symm_apply_eq]; rfl
    rw [this, S.rval_zero L]
    rfl
  elt_mul f g := by
    rw [sh_symm_comp]
    have hval : (S.rval L ((sh.{0}).symm g)).1 * (S.rval L ((sh.{0}).symm f)).1 =
        (S.rval L ((sh.{0}).symm f) ≫ S.rval L ((sh.{0}).symm g)).1 :=
      (SplitBasicIdempotents.ProjectiveCategory.comp_val _ _ _).symm
    rw [hval]
    split_ifs with h
    · exact congrArg Subtype.val
        ((rval_comp hzero hscalar ((sh.{0}).symm f) ((sh.{0}).symm g)).1 h).choose_spec
    · push Not at h
      rw [(rval_comp hzero hscalar ((sh.{0}).symm f) ((sh.{0}).symm g)).2 h, h, S.rval_zero L,
        Units.val_one, one_smul]
  elt_mul_ne f g hyy := by
    rename_i x y y' z
    have hne : y'.as.as ≠ y.as.as := by
      intro h
      apply hyy
      rcases y with ⟨⟨y⟩⟩
      rcases y' with ⟨⟨y'⟩⟩
      cases h
      rfl
    rw [← SplitBasicIdempotents.ProjectiveCategory.val_mul_idempotent S.toIdempotents
      (S.rval L ((sh.{0}).symm g)), mul_assoc,
      SplitBasicIdempotents.ProjectiveCategory.idempotent_mul_val_eq_zero_of_ne S.toIdempotents hne,
      mul_zero]
  sum_id := by
    have h1 : ∀ x : RaySmall.{0} S.toIdempotents.RayCategory,
        (S.rval L ((sh.{0}).symm (𝟙 x))).1 = S.primitiveIdempotents.e (S.labelEquiv x) := by
      intro x
      have : (sh.{0}).symm (𝟙 x) = 𝟙 x.as := by rw [Equiv.symm_apply_eq]; rfl
      rw [this, rval_id, S.id_val']
      rfl
    simp only [h1]
    rw [Equiv.sum_comp S.labelEquiv (fun i ↦ S.primitiveIdempotents.e i)]
    exact S.primitiveIdempotents.complete.complete
  tw_id_left f := by
    rename_i x y
    have h1 : (sh.{0}).symm (𝟙 x) = 𝟙 x.as := by rw [Equiv.symm_apply_eq]; rfl
    split_ifs with h
    · have hs := ((rval_comp hzero hscalar ((sh.{0}).symm (𝟙 x)) ((sh.{0}).symm f)).1 h).choose_spec
      set t := ((rval_comp hzero hscalar ((sh.{0}).symm (𝟙 x)) ((sh.{0}).symm f)).1 h).choose
      have hf0 : (sh.{0}).symm f ≠ 0 := by
        intro h0; apply h; rw [h0, comp_zero]
      simp only [h1, Category.id_comp, rval_id] at hs
      exact eq_one_of_smul_self (rval_ne_zero hzero _ hf0) hs
    · rfl
  tw_id_right f := by
    rename_i x y
    have h1 : (sh.{0}).symm (𝟙 y) = 𝟙 y.as := by rw [Equiv.symm_apply_eq]; rfl
    split_ifs with h
    · have hs := ((rval_comp hzero hscalar ((sh.{0}).symm f) ((sh.{0}).symm (𝟙 y))).1 h).choose_spec
      set t := ((rval_comp hzero hscalar ((sh.{0}).symm f) ((sh.{0}).symm (𝟙 y))).1 h).choose
      have hf0 : (sh.{0}).symm f ≠ 0 := by
        intro h0; apply h; rw [h0, zero_comp]
      simp only [h1, Category.comp_id, rval_id] at hs
      exact eq_one_of_smul_self (rval_ne_zero hzero _ hf0) hs
    · rfl
  linearIndependent := hLI
  span := hspan

/-- **BGRS 2.10**: a zero-detecting lift with proportional parallel paths gives a
twisted multiplicative basis, for an algebra with finitely many ideals. -/
def mulBasisOfLift' (hfinI : (Set.univ : Set (TwoSidedIdeal B)).Finite) :
    RayQuiver.MulBasis k (RaySmall.{0} S.toIdempotents.RayCategory) B :=
  mulBasisOfLift hzero hscalar (elt_basis hzero hfinI).1 (elt_basis hzero hfinI).2

end SplitBasicData

end LargeIndecomposable
