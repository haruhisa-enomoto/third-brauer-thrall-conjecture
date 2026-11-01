module

public import LargeIndecomposable.RayCategories.Distributive.SplitBasicRayCategory
public import LargeIndecomposable.RayCategories.Distributive.DistributiveHomFunctor
public import LargeIndecomposable.Modules.Idempotents.IdempotentProjectiveCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Jacobson.Radical

@[expose] public section

/-!
# Split-basic presentations of radical quotients

A two-sided ideal contained in the Jacobson radical does not change the
semisimple quotient.  This file makes that fact concrete for the chosen
primitive idempotents used by SplitBasicIdempotents: their images form the
corresponding chosen split-basic presentation of the quotient algebra.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable

universe u v x

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

/-- Membership in the Jacobson radical of a quotient by a smaller radical
ideal is detected before passing to the quotient. -/
theorem TwoSidedIdeal.quotient_mk_mem_jacobson_iff
    (I : TwoSidedIdeal A) (hI : I.asIdeal ≤ Ring.jacobson A) (a : A) :
    Ideal.Quotient.mk I.asIdeal a ∈ Ring.jacobson (A ⧸ I.asIdeal) ↔
      a ∈ Ring.jacobson A := by
  rw [Ring.jacobson_quotient_of_le hI]
  constructor
  · rintro ⟨b, hbJ, hab⟩
    change Ideal.Quotient.mk I.asIdeal b =
      Ideal.Quotient.mk I.asIdeal a at hab
    have hdiff : a - b ∈ I.asIdeal := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub]
      exact sub_eq_zero.mpr hab.symm
    have hadd := (Ring.jacobson A).add_mem (hI hdiff) hbJ
    simpa only [sub_add_cancel] using hadd
  · intro haJ
    exact ⟨a, haJ, rfl⟩

/-- Quotienting by an ideal contained in the radical square preserves
nonmembership in the first radical layer. -/
theorem TwoSidedIdeal.quotient_mk_not_mem_jacobson_sq
    (I : TwoSidedIdeal A)
    (hI : I.asIdeal ≤ Ring.jacobson A)
    (hI₂ : I.asIdeal ≤ Ring.jacobson A * Ring.jacobson A)
    (a : A) (ha : a ∉ Ring.jacobson A * Ring.jacobson A) :
    Ideal.Quotient.mk I.asIdeal a ∉
      Ring.jacobson (A ⧸ I.asIdeal) *
        Ring.jacobson (A ⧸ I.asIdeal) := by
  let q : A →+* A ⧸ I.asIdeal := Ideal.Quotient.mk I.asIdeal
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hJ : Ring.jacobson (A ⧸ I.asIdeal) =
      Ideal.map q (Ring.jacobson A) := by
    ext z
    obtain ⟨b, rfl⟩ := hq z
    rw [LargeIndecomposable.TwoSidedIdeal.quotient_mk_mem_jacobson_iff I hI]
    constructor
    · intro hb
      exact Ideal.mem_map_of_mem q hb
    · intro hb
      obtain ⟨c, hc, hcb⟩ :=
        (Ideal.mem_map_iff_of_surjective q hq).1 hb
      have hdiff : b - c ∈ I.asIdeal := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [map_sub, hcb, sub_self]
      have hadd := (Ring.jacobson A).add_mem (hI hdiff) hc
      simpa only [sub_add_cancel] using hadd
  intro hbar
  rw [hJ] at hbar
  have hprodLe :
      Ideal.map q (Ring.jacobson A) *
          Ideal.map q (Ring.jacobson A) ≤
        Ideal.map q (Ring.jacobson A * Ring.jacobson A) := by
    apply Ideal.mul_le.2
    intro b hb c hc
    obtain ⟨b₀, hb₀, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective q hq).1 hb
    obtain ⟨c₀, hc₀, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective q hq).1 hc
    rw [← map_mul]
    exact Ideal.mem_map_of_mem q (Ideal.mul_mem_mul hb₀ hc₀)
  have hbar' := hprodLe hbar
  obtain ⟨b, hb, hba⟩ :=
    (Ideal.mem_map_iff_of_surjective q hq).1 hbar'
  apply ha
  have hdiff : a - b ∈ I.asIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, hba.symm, sub_self]
  have hadd := (Ring.jacobson A * Ring.jacobson A).add_mem
    (hI₂ hdiff) hb
  simpa only [sub_add_cancel] using hadd

namespace SplitBasicIdempotents

/-- The images of chosen split-basic primitive idempotents give a chosen
split-basic presentation after quotienting by an ideal contained in the
Jacobson radical. -/
def quotient_of_le_jacobson
    (S : SplitBasicIdempotents (k := k) (A := A) (ι := ι))
    (I : TwoSidedIdeal A) (hI : I.asIdeal ≤ Ring.jacobson A) :
    SplitBasicIdempotents
      (k := k) (A := A ⧸ I.asIdeal) (ι := ι) := by
  let q : (A ⧸ I.asIdeal) →ₐ[k] (ι → k) :=
    S.quotientEquiv.toAlgHom.comp (Ideal.Quotient.factorₐ k hI)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨z, rfl⟩ := S.quotientEquiv.surjective y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk I.asIdeal a, rfl⟩
  have hker : RingHom.ker q =
      Ring.jacobson (A ⧸ I.asIdeal) := by
    ext z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [RingHom.mem_ker,
      LargeIndecomposable.TwoSidedIdeal.quotient_mk_mem_jacobson_iff I hI]
    change S.quotientEquiv
      (Ideal.Quotient.mk (Ring.jacobson A) a) = 0 ↔ _
    rw [map_eq_zero_iff S.quotientEquiv S.quotientEquiv.injective]
    exact Ideal.Quotient.eq_zero_iff_mem
  let eKer :
      ((A ⧸ I.asIdeal) ⧸ RingHom.ker q) ≃ₐ[k] (ι → k) :=
    Ideal.quotientKerAlgEquivOfSurjective hq
  let eJac :
      ((A ⧸ I.asIdeal) ⧸ Ring.jacobson (A ⧸ I.asIdeal)) ≃ₐ[k]
        ((A ⧸ I.asIdeal) ⧸ RingHom.ker q) :=
    Ideal.quotientEquivAlgOfEq k hker.symm
  refine
    { idempotent := (Ideal.Quotient.mk I.asIdeal) ∘ S.idempotent
      complete := S.complete.map (Ideal.Quotient.mk I.asIdeal)
      quotientEquiv := eJac.trans eKer
      quotientEquiv_mk_idempotent := ?_ }
  intro i j
  dsimp [eJac, eKer]
  change S.quotientEquiv
    (Ideal.Quotient.mk (Ring.jacobson A) (S.idempotent i)) j = _
  exact S.quotientEquiv_mk_idempotent i j

/-- The chosen primitive-projective objects before and after a radical
quotient have equivalent label types through their common index `ι`. -/
def projectiveQuotientObjEquiv
    (S : SplitBasicIdempotents (k := k) (A := A) (ι := ι))
    (I : TwoSidedIdeal A) (hI : I.asIdeal ≤ Ring.jacobson A) :
    S.ProjectiveCategory ≃
      (S.quotient_of_le_jacobson I hI).ProjectiveCategory :=
  S.projectiveVertexEquiv.trans
    (S.quotient_of_le_jacobson I hI).projectiveVertexEquiv.symm

@[simp]
theorem projectiveQuotientObjEquiv_projectiveVertex
    (S : SplitBasicIdempotents (k := k) (A := A) (ι := ι))
    (I : TwoSidedIdeal A) (hI : I.asIdeal ≤ Ring.jacobson A)
    (X : S.ProjectiveCategory) :
    (S.quotient_of_le_jacobson I hI).projectiveVertex
      (S.projectiveQuotientObjEquiv I hI X) = S.projectiveVertex X := by
  change (S.quotient_of_le_jacobson I hI).projectiveVertexEquiv
    ((S.projectiveVertexEquiv.trans
      (S.quotient_of_le_jacobson I hI).projectiveVertexEquiv.symm) X) =
        S.projectiveVertex X
  simp

/-- Quotienting corner values gives a functor from the chosen
primitive-projective category of `A` to that of `A/I`. -/
def projectiveQuotientFunctor
    (S : SplitBasicIdempotents (k := k) (A := A) (ι := ι))
    (I : TwoSidedIdeal A) (hI : I.asIdeal ≤ Ring.jacobson A) :
    S.ProjectiveCategory ⥤
      (S.quotient_of_le_jacobson I hI).ProjectiveCategory where
  obj X := S.projectiveQuotientObjEquiv I hI X
  map {X Y} f := by
    let a : A := Classical.choose f.2
    have ha := Classical.choose_spec f.2
    change S.idempotent (S.projectiveVertex Y) * a *
      S.idempotent (S.projectiveVertex X) = f.1 at ha
    refine ⟨Ideal.Quotient.mk I.asIdeal f.1, ?_⟩
    rw [mem_idempotentCorner_iff]
    refine ⟨Ideal.Quotient.mk I.asIdeal a, ?_⟩
    have hX := S.projectiveQuotientObjEquiv_projectiveVertex I hI X
    have hY := S.projectiveQuotientObjEquiv_projectiveVertex I hI Y
    rw [hX, hY]
    change Ideal.Quotient.mk I.asIdeal
      (S.idempotent (S.projectiveVertex Y)) *
        Ideal.Quotient.mk I.asIdeal a *
          Ideal.Quotient.mk I.asIdeal
            (S.idempotent (S.projectiveVertex X)) =
      Ideal.Quotient.mk I.asIdeal f.1
    simpa only [map_mul] using congrArg
      (Ideal.Quotient.mk I.asIdeal) ha
  map_id X := by
    apply Subtype.ext
    dsimp
    have hX := S.projectiveQuotientObjEquiv_projectiveVertex I hI X
    rw [hX]
    rfl
  map_comp f g := by
    apply Subtype.ext
    exact map_mul (Ideal.Quotient.mk I.asIdeal) g.1 f.1

@[simp]
theorem projectiveQuotientFunctor_obj_projectiveVertex
    (S : SplitBasicIdempotents (k := k) (A := A) (ι := ι))
    (I : TwoSidedIdeal A) (hI : I.asIdeal ≤ Ring.jacobson A)
    (X : S.ProjectiveCategory) :
    (S.quotient_of_le_jacobson I hI).projectiveVertex
      ((S.projectiveQuotientFunctor I hI).obj X) =
        S.projectiveVertex X := by
  exact S.projectiveQuotientObjEquiv_projectiveVertex I hI X

@[simp]
theorem projectiveQuotientFunctor_map_val
    (S : SplitBasicIdempotents (k := k) (A := A) (ι := ι))
    (I : TwoSidedIdeal A) (hI : I.asIdeal ≤ Ring.jacobson A)
    {X Y : S.ProjectiveCategory} (f : X ⟶ Y) :
    ((S.projectiveQuotientFunctor I hI).map f).1 =
      Ideal.Quotient.mk I.asIdeal f.1 := by
  simp [projectiveQuotientFunctor]

instance projectiveQuotientFunctor_additive
    (S : SplitBasicIdempotents (k := k) (A := A) (ι := ι))
    (I : TwoSidedIdeal A) (hI : I.asIdeal ≤ Ring.jacobson A) :
    (S.projectiveQuotientFunctor I hI).Additive where
  map_add := by
    intro X Y f g
    apply Subtype.ext
    change Ideal.Quotient.mk I.asIdeal (f.1 + g.1) =
      Ideal.Quotient.mk I.asIdeal f.1 +
        Ideal.Quotient.mk I.asIdeal g.1
    exact map_add (Ideal.Quotient.mk I.asIdeal) f.1 g.1

instance projectiveQuotientFunctor_linear
    (S : SplitBasicIdempotents (k := k) (A := A) (ι := ι))
    (I : TwoSidedIdeal A) (hI : I.asIdeal ≤ Ring.jacobson A) :
    (S.projectiveQuotientFunctor I hI).Linear k where
  map_smul := by
    intro X Y f c
    apply Subtype.ext
    change Ideal.Quotient.mk I.asIdeal (c • f.1) =
      c • Ideal.Quotient.mk I.asIdeal f.1
    exact AlgHom.map_smul_of_tower (Ideal.Quotient.mkₐ k I.asIdeal) c f.1

/-- A primitive-corner morphism vanishes after quotienting exactly when its
ambient value belongs to the quotient ideal. -/
@[simp]
theorem projectiveQuotientFunctor_map_eq_zero_iff
    (S : SplitBasicIdempotents (k := k) (A := A) (ι := ι))
    (I : TwoSidedIdeal A) (hI : I.asIdeal ≤ Ring.jacobson A)
    {X Y : S.ProjectiveCategory} (f : X ⟶ Y) :
    (S.projectiveQuotientFunctor I hI).map f = 0 ↔
      f.1 ∈ I.asIdeal := by
  constructor
  · intro hf
    have hv := congrArg Subtype.val hf
    change Ideal.Quotient.mk I.asIdeal f.1 = 0 at hv
    exact Ideal.Quotient.eq_zero_iff_mem.mp hv
  · intro hf
    apply Subtype.ext
    change Ideal.Quotient.mk I.asIdeal f.1 = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hf

/-- Every morphism between chosen quotient projectives lifts to an ambient
primitive-corner morphism. -/
instance projectiveQuotientFunctor_full
    (S : SplitBasicIdempotents (k := k) (A := A) (ι := ι))
    (I : TwoSidedIdeal A) (hI : I.asIdeal ≤ Ring.jacobson A) :
    (S.projectiveQuotientFunctor I hI).Full where
  map_surjective {X Y} f := by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective f.1
    let g : X ⟶ Y :=
      ⟨S.idempotent (S.projectiveVertex Y) * a *
          S.idempotent (S.projectiveVertex X), ⟨a, rfl⟩⟩
    refine ⟨g, ?_⟩
    apply Subtype.ext
    rw [projectiveQuotientFunctor_map_val]
    change Ideal.Quotient.mk I.asIdeal
      (S.idempotent (S.projectiveVertex Y) * a *
        S.idempotent (S.projectiveVertex X)) = f.1
    rw [map_mul, map_mul, ha]
    have heY : Ideal.Quotient.mk I.asIdeal
        (S.idempotent (S.projectiveVertex Y)) =
        (S.quotient_of_le_jacobson I hI).idempotent
          ((S.quotient_of_le_jacobson I hI).projectiveVertex
            ((S.projectiveQuotientFunctor I hI).obj Y)) := by
      rw [projectiveQuotientFunctor_obj_projectiveVertex]
      rfl
    have heX : Ideal.Quotient.mk I.asIdeal
        (S.idempotent (S.projectiveVertex X)) =
        (S.quotient_of_le_jacobson I hI).idempotent
          ((S.quotient_of_le_jacobson I hI).projectiveVertex
            ((S.projectiveQuotientFunctor I hI).obj X)) := by
      rw [projectiveQuotientFunctor_obj_projectiveVertex]
      rfl
    rw [heY, heX,
      ProjectiveCategory.idempotent_mul_val,
      ProjectiveCategory.val_mul_idempotent]

/-- The quotient functor is essentially surjective; on the chosen labels its
object map is an equivalence. -/
instance projectiveQuotientFunctor_essSurj
    (S : SplitBasicIdempotents (k := k) (A := A) (ι := ι))
    (I : TwoSidedIdeal A) (hI : I.asIdeal ≤ Ring.jacobson A) :
    (S.projectiveQuotientFunctor I hI).EssSurj :=
  (S.projectiveQuotientFunctor I hI).essSurj_of_surj <| by
    simpa only [projectiveQuotientFunctor] using
      (S.projectiveQuotientObjEquiv I hI).surjective

/-- The BGRS distributive Hom structure descends to every quotient by an
ideal contained in the Jacobson radical.  The primitive-projective quotient
functor is full and its object map is an equivalence on the chosen labels. -/
instance quotient_projectiveCategory_hasBGRSDistributiveHomStructure
    (S : SplitBasicIdempotents (k := k) (A := A) (ι := ι))
    (I : TwoSidedIdeal A) (hI : I.asIdeal ≤ Ring.jacobson A)
    [HasBGRSDistributiveHomStructure k S.ProjectiveCategory] :
    HasBGRSDistributiveHomStructure k
      (S.quotient_of_le_jacobson I hI).ProjectiveCategory :=
  HasBGRSDistributiveHomStructure.of_full_surjective
    (S.projectiveQuotientFunctor I hI) <| by
      simpa only [projectiveQuotientFunctor] using
        (S.projectiveQuotientObjEquiv I hI).surjective

/-- The canonical full-functor preimage of a radical endomorphism in a
radical quotient is already radical before quotienting. -/
theorem projectiveQuotientFunctor_preimage_end_mem_jacobson
    (S : SplitBasicIdempotents (k := k) (A := A) (ι := ι))
    (I : TwoSidedIdeal A) (hI : I.asIdeal ≤ Ring.jacobson A)
    [Module.Finite k A] [Module.Finite k (A ⧸ I.asIdeal)]
    {X : S.ProjectiveCategory}
    (a : End ((S.projectiveQuotientFunctor I hI).obj X))
    (ha : a ∈ Ring.jacobson
      (End ((S.projectiveQuotientFunctor I hI).obj X))) :
    End.of ((S.projectiveQuotientFunctor I hI).preimage a.asHom) ∈
      Ring.jacobson (End X) := by
  let F := S.projectiveQuotientFunctor I hI
  let b : End X := End.of (F.preimage a.asHom)
  have haVal : a.1 ∈ Ring.jacobson (A ⧸ I.asIdeal) :=
    ((S.quotient_of_le_jacobson I hI).projectiveEnd_mem_jacobson_iff_val_mem_jacobson
      (F.obj X) a).1 ha
  have hbQuotient : Ideal.Quotient.mk I.asIdeal b.1 ∈
      Ring.jacobson (A ⧸ I.asIdeal) := by
    rw [← S.projectiveQuotientFunctor_map_val]
    change (F.map b.asHom).1 ∈ Ring.jacobson (A ⧸ I.asIdeal)
    rw [show F.map b.asHom = a.asHom by
      simpa only [b] using F.map_preimage a.asHom]
    exact haVal
  apply (S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson X b).2
  exact (LargeIndecomposable.TwoSidedIdeal.quotient_mk_mem_jacobson_iff
    I hI b.1).1 hbQuotient

/-- A projective endomorphism that generates its full Jacobson radical
continues to do so after quotienting by a smaller radical ideal. -/
theorem projectiveQuotientFunctor_end_span_eq_jacobson
    (S : SplitBasicIdempotents (k := k) (A := A) (ι := ι))
    (I : TwoSidedIdeal A) (hI : I.asIdeal ≤ Ring.jacobson A)
    [Module.Finite k A] [Module.Finite k (A ⧸ I.asIdeal)]
    (X : S.ProjectiveCategory) (tau : End X)
    (htauSpan : twoSidedEndomorphismSpan k tau =
      (Ring.jacobson (End X)).restrictScalars k) :
    twoSidedEndomorphismSpan k
        (End.of ((S.projectiveQuotientFunctor I hI).map tau.asHom)) =
      (Ring.jacobson
        (End ((S.projectiveQuotientFunctor I hI).obj X))).restrictScalars k := by
  let F := S.projectiveQuotientFunctor I hI
  let tauBar : End (F.obj X) := End.of (F.map tau.asHom)
  have htauJ : tau ∈ Ring.jacobson (End X) := by
    have hmem := LargeIndecomposable.mem_twoSidedEndomorphismSpan k tau
    rw [htauSpan] at hmem
    exact hmem
  have htauBarJ : tauBar ∈ Ring.jacobson (End (F.obj X)) := by
    apply ((S.quotient_of_le_jacobson I hI).projectiveEnd_mem_jacobson_iff_val_mem_jacobson
        (F.obj X) tauBar).2
    change Ideal.Quotient.mk I.asIdeal tau.1 ∈
      Ring.jacobson (A ⧸ I.asIdeal)
    rw [LargeIndecomposable.TwoSidedIdeal.quotient_mk_mem_jacobson_iff I hI]
    exact (S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson X tau).1 htauJ
  change twoSidedEndomorphismSpan k tauBar = _
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro h ⟨a, b, rfl⟩
    have hring : b * tauBar * a ∈ Ring.jacobson (End (F.obj X)) :=
      (Ring.jacobson (End (F.obj X))).mul_mem_right a
        ((Ring.jacobson (End (F.obj X))).mul_mem_left b htauBarJ)
    change End.of ((a.asHom ≫ tauBar.asHom) ≫ b.asHom) ∈
      Ring.jacobson (End (F.obj X))
    rw [show End.of ((a.asHom ≫ tauBar.asHom) ≫ b.asHom) =
        b * tauBar * a by
      apply End.ext
      simp only [End.mul_def, Category.assoc]]
    exact hring
  · intro a ha
    obtain ⟨b, hb⟩ := F.map_surjective a
    have haVal : a.1 ∈ Ring.jacobson (A ⧸ I.asIdeal) :=
      ((S.quotient_of_le_jacobson I hI).projectiveEnd_mem_jacobson_iff_val_mem_jacobson
          (F.obj X) (End.of a)).1 ha
    have hbQuotient : Ideal.Quotient.mk I.asIdeal b.1 ∈
        Ring.jacobson (A ⧸ I.asIdeal) := by
      rw [← S.projectiveQuotientFunctor_map_val]
      change (F.map b).1 ∈ _
      rw [hb]
      exact haVal
    have hbVal : b.1 ∈ Ring.jacobson A :=
      (LargeIndecomposable.TwoSidedIdeal.quotient_mk_mem_jacobson_iff
        I hI b.1).1 hbQuotient
    have hbJ : End.of b ∈ Ring.jacobson (End X) :=
      (S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson
        X (End.of b)).2 hbVal
    have hbSpan : b ∈ twoSidedEndomorphismSpan k tau.asHom := by
      change End.of b ∈ twoSidedEndomorphismSpan k tau
      rw [htauSpan]
      exact hbJ
    have hmap := LargeIndecomposable.linearFunctor_map_mem_twoSidedEndomorphismSpan
      (k := k) F hbSpan
    change F.map b ∈ twoSidedEndomorphismSpan k tauBar at hmap
    simpa only [hb] using hmap

end SplitBasicIdempotents

/-- A quotient of a split-basic algebra by an ideal contained in the
Jacobson radical is again split basic. -/
theorem IsSplitBasic.quotient_of_le_jacobson
    (hA : IsSplitBasic k A)
    (I : TwoSidedIdeal A) (hI : I.asIdeal ≤ Ring.jacobson A) :
    IsSplitBasic k (A ⧸ I.asIdeal) := by
  obtain ⟨n, ⟨S⟩⟩ := hA
  exact ⟨n, ⟨S.quotient_of_le_jacobson I hI⟩⟩

end LargeIndecomposable
