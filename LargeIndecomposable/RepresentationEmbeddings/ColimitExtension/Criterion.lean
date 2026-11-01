module

public import LargeIndecomposable.RepresentationEmbeddings.ColimitExtension.NoSummand
public import LargeIndecomposable.RepresentationEmbeddings.ColimitExtension.Preserves
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Theorem 2.7: the extension criterion

Let `Φ : D_fin → mod A` be a faithful representation embedding with
retractions on `C_fin` whose kernels satisfy a common nilpotence bound. Then
its colimit extension `F` is a representation embedding on `D`, commutes with
direct sums and filtered colimits, preserves infinite dimension, and has
retractions on `C` with the same bound.

The new point is reflection of isomorphism classes on all of `D`. Write
`T ≅ T₀ ⊕ S₋^(I)` with `T₀ ∈ C` by (2.2). An isomorphism
`F(T) ≅ F(U)` has an invertible block `F(T₀) → F(U₀)` by (2.5), Lemma 2.6 and
the no-summand lemma, and then an invertible Schur complement
`F(S₋^(I)) ≅ F(S₋^(J))`, whence `|I| = |J|`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]

/-! ### The splitting `T ≅ T₀ ⊕ S₋^(I)` inside `D` -/

namespace DSplit

/-- `S₋^(I)` as an object of `D`. -/
def sumD (I : Type u) : D k :=
  ⟨Kron.sumSminus k I, by rw [inD_iff]; intro v _ _; rfl⟩

/-- `T₀ = (V, a(V) + b(V))` as an object of `D`. -/
def T₀D (T : D k) : D k := ⟨Kron.Splitting.T₀ T.obj, (Kron.Splitting.inC_T₀ T.obj T.2).1⟩

lemma inC_T₀D (T : D k) : InC (T₀D T).obj := Kron.Splitting.inC_T₀ T.obj T.2

/-- The binary bicone `T₀ → T ← S₋^(I)` in `D`. -/
def bicone (T : D k) : BinaryBicone (T₀D T) (sumD (Kron.Splitting.I T.obj)) where
  pt := T
  fst := ObjectProperty.homMk (Kron.Splitting.bicone T.obj).fst
  snd := ObjectProperty.homMk (Kron.Splitting.bicone T.obj).snd
  inl := ObjectProperty.homMk (Kron.Splitting.bicone T.obj).inl
  inr := ObjectProperty.homMk (Kron.Splitting.bicone T.obj).inr
  inl_fst := by ext1; exact (Kron.Splitting.bicone T.obj).inl_fst
  inl_snd := by ext1; exact (Kron.Splitting.bicone T.obj).inl_snd
  inr_fst := by ext1; exact (Kron.Splitting.bicone T.obj).inr_fst
  inr_snd := by ext1; exact (Kron.Splitting.bicone T.obj).inr_snd

lemma total (T : D k) :
    (bicone T).fst ≫ (bicone T).inl + (bicone T).snd ≫ (bicone T).inr = 𝟙 T := by
  ext1; exact Kron.Splitting.total T.obj

/-- The cofan exhibiting `S₋^(I)` as a coproduct of copies of `S₋` in `D`. -/
def cofan (I : Type u) : Cofan (fun _ : I ↦ (Extension.Sminus : D k)) :=
  Cofan.mk (sumD I) fun i ↦ ObjectProperty.homMk (Kron.ιSminus I i)

/-- The cofan is a coproduct in `D`. -/
def isColimitCofan (I : Type u) : IsColimit (cofan (k := k) I) :=
  isColimitOfReflects (InD (k := k)).ι
    ((Kron.isColimitSumSminus I).ofIsoColimit (Cocone.ext (Iso.refl _) (by
      rintro ⟨i⟩; simp [cofan]; rfl)))

end DSplit

/-! ### Direct sums of copies of a module -/

/-- The cofan `P → P^(I)`, `P^(I) = I →₀ P`. -/
def finsuppCofan (P : ModuleCat.{u} A) (I : Type u) : Cofan (fun _ : I ↦ P) :=
  Cofan.mk (ModuleCat.of A (I →₀ P)) fun i ↦ ModuleCat.ofHom (Finsupp.lsingle i)

/-- `I →₀ P` is a coproduct of copies of `P`. -/
def isColimitFinsuppCofan (P : ModuleCat.{u} A) (I : Type u) :
    IsColimit (finsuppCofan P I) :=
  Cofan.IsColimit.mk _
    (fun s ↦ ModuleCat.ofHom (Finsupp.lsum ℕ fun i ↦ (s.inj i).hom))
    (fun s i ↦ by ext x; simp [finsuppCofan])
    (fun s m hm ↦ by
      ext1
      refine Finsupp.lhom_ext fun i x ↦ ?_
      have := congrArg (fun φ ↦ φ.hom x) (hm i)
      change m.hom (Finsupp.single i x) = (s.inj i).hom x at this
      change m.hom (Finsupp.single i x) = (Finsupp.lsum ℕ fun i ↦ (s.inj i).hom) (Finsupp.single i x)
      rw [this]; simp)

/-! ### Small lemmas -/

/-- Cancellation of a positive finite factor. -/
lemma Cardinal.eq_of_mul_natCast {a b : Cardinal} {n : ℕ} (hn : n ≠ 0)
    (h : a * n = b * n) : a = b := by
  have hn' : (n : Cardinal) ≠ 0 := by exact_mod_cast hn
  have key : ∀ {a b : Cardinal}, Cardinal.aleph0 ≤ a → a * n = b * n → a = b := by
    intro a b ha h
    have ha' : a * n = a := Cardinal.mul_eq_left ha ((Cardinal.natCast_lt_aleph0).le.trans ha) hn'
    have hb : Cardinal.aleph0 ≤ b := by
      by_contra hb
      rw [not_le] at hb
      have : b * n < Cardinal.aleph0 := Cardinal.mul_lt_aleph0 hb Cardinal.natCast_lt_aleph0
      rw [← h, ha'] at this
      exact absurd ha (not_le.2 this)
    have hb' : b * n = b := Cardinal.mul_eq_left hb ((Cardinal.natCast_lt_aleph0).le.trans hb) hn'
    rw [← ha', h, hb']
  by_cases ha : Cardinal.aleph0 ≤ a
  · exact key ha h
  by_cases hb : Cardinal.aleph0 ≤ b
  · exact (key hb h.symm).symm
  rw [not_le] at ha hb
  obtain ⟨m, rfl⟩ := Cardinal.lt_aleph0.1 ha
  obtain ⟨m', rfl⟩ := Cardinal.lt_aleph0.1 hb
  norm_cast at h ⊢
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hn) h

/-- Nilpotence of an endomorphism of a module, transported to the ring `End M`. -/
lemma isNilpotent_end_of_hom_pow {M : ModuleCat.{u} A} (f : M ⟶ M) {m : ℕ}
    (h : f.hom ^ m = 0) : IsNilpotent (show End M from f) := by
  refine ⟨m, ?_⟩
  have key : ∀ m : ℕ, ((show End M from f) ^ m : End M).hom = f.hom ^ m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ, End.mul_def, ModuleCat.hom_comp, ih, pow_succ]
      rfl
  change ((show End M from f) ^ m : M ⟶ M) = 0
  exact ModuleCat.hom_ext (by rw [key, h]; rfl)

/-- Two bicones with isomorphic summands have isomorphic points. -/
def biconeIso {C : Type*} [Category C] [Preadditive C] {X Y X' Y' : C}
    (b : BinaryBicone X Y) (b' : BinaryBicone X' Y')
    (hb : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt)
    (hb' : b'.fst ≫ b'.inl + b'.snd ≫ b'.inr = 𝟙 b'.pt) (φ : X ≅ X') (ψ : Y ≅ Y') :
    b.pt ≅ b'.pt where
  hom := b.fst ≫ φ.hom ≫ b'.inl + b.snd ≫ ψ.hom ≫ b'.inr
  inv := b'.fst ≫ φ.inv ≫ b.inl + b'.snd ≫ ψ.inv ≫ b.inr
  hom_inv_id := by
    simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      BinaryBicone.inl_fst_assoc, BinaryBicone.inl_snd_assoc, BinaryBicone.inr_fst_assoc,
      BinaryBicone.inr_snd_assoc, Iso.hom_inv_id_assoc, Limits.zero_comp, Limits.comp_zero,
      add_zero, zero_add]
    exact hb
  inv_hom_id := by
    simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      BinaryBicone.inl_fst_assoc, BinaryBicone.inl_snd_assoc, BinaryBicone.inr_fst_assoc,
      BinaryBicone.inr_snd_assoc, Iso.inv_hom_id_assoc, Limits.zero_comp, Limits.comp_zero,
      add_zero, zero_add]
    exact hb'

/-- `S₋^(I) ≅ S₋^(J)` in `D` from a bijection `I ≃ J`. -/
def DSplit.sumDIsoOfEquiv {I J : Type u} (σ : I ≃ J) : DSplit.sumD (k := k) I ≅ DSplit.sumD J where
  hom := ObjectProperty.homMk (Kron.homMk 0
    (ModuleCat.ofHom (Finsupp.domLCongr σ).toLinearMap)
    (by ext x; obtain rfl : x = 0 := rfl; simp) (by ext x; obtain rfl : x = 0 := rfl; simp))
  inv := ObjectProperty.homMk (Kron.homMk 0
    (ModuleCat.ofHom (Finsupp.domLCongr σ.symm).toLinearMap)
    (by ext x; obtain rfl : x = 0 := rfl; simp) (by ext x; obtain rfl : x = 0 := rfl; simp))
  hom_inv_id := by
    ext1; apply Kron.hom_ext
    · ext x; rfl
    · ext x
      exact LinearEquiv.symm_apply_apply (Finsupp.domLCongr (M := k) (R := k) σ) x
  inv_hom_id := by
    ext1; apply Kron.hom_ext
    · ext x; rfl
    · ext x
      exact LinearEquiv.apply_symm_apply (Finsupp.domLCongr (M := k) (R := k) σ) x

/-- An `A`-linear equivalence is `k`-linear on the restricted scalars. -/
def restrictScalarsLinearEquiv {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (e : M ≃ₗ[A] N) : RestrictScalars k A M ≃ₗ[k] RestrictScalars k A N where
  toFun := e
  invFun := e.symm
  map_add' := e.map_add
  map_smul' c x := e.map_smul (algebraMap k A c) x
  left_inv := e.left_inv
  right_inv := e.right_inv

/-- `(I →₀ P)` with restricted scalars is `I →₀ P` over `k`. -/
def restrictScalarsFinsupp (P : Type u) [AddCommGroup P] [Module A P] (I : Type u) :
    RestrictScalars k A (I →₀ P) ≃ₗ[k] (I →₀ RestrictScalars k A P) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

lemma dim_finsupp (P : ModuleCat.{u} A) (I : Type u) :
    Statement.dim k A (ModuleCat.of A (I →₀ P)) = Cardinal.mk I * Statement.dim k A P := by
  have : Module.Free k (RestrictScalars k A P) :=
    @Module.Free.of_divisionRing k (RestrictScalars k A P) _ _ (RestrictScalars.module k A P)
  rw [Statement.dim, (restrictScalarsFinsupp (k := k) P I).rank_eq, rank_finsupp,
    Cardinal.lift_id, Cardinal.lift_id]
  rfl

section

attribute [local instance] ModuleCat.moduleOfAlgebraModule

/-- A nonzero finite-dimensional module has positive dimension (stated through
`RestrictScalars`, avoiding an instance mismatch). -/
lemma finrank_restrictScalars_ne_zero (M : ModuleCat.{u} A)
    (h : Module.Finite k (RestrictScalars k A M)) (hM : Nontrivial M) :
    Module.finrank k (RestrictScalars k A M) ≠ 0 := by
  have : Module.Finite k M := h
  have e : Module.finrank k (RestrictScalars k A M) = Module.finrank k M := rfl
  rw [e]
  exact Module.finrank_pos.ne'

end

/-! ### Reflection of isomorphism classes on `D` -/

namespace Extension

variable (Φ : Dfin k ⥤ ModuleCat.{u} A) (hexact : IsExactOnDfin Φ) [Φ.Additive]

/-- `F(S₋^(I)) ≅ P^(I)` with `P = Φ(S₋)`. -/
def sumIso (I : Type u) :
    (functor Φ).obj (DSplit.sumD I) ≅ ModuleCat.of A (I →₀ Φ.obj SminusFin) :=
  haveI := preservesCoproducts hexact I
  IsColimit.coconePointsIsoOfNatIso (isColimitOfPreserves (functor Φ) (DSplit.isColimitCofan I))
    (isColimitFinsuppCofan _ I)
    (Discrete.natIso fun _ ↦ isoOfFin Φ Sminus Sminus_isFiniteDimensional)

omit [Algebra k A] in
include hexact in
lemma factorsThroughSum_comp {X Y : ModuleCat.{u} A} (I : Type u)
    (g : X ⟶ (functor Φ).obj (DSplit.sumD I)) (h : (functor Φ).obj (DSplit.sumD I) ⟶ Y) :
    FixedSummand.FactorsThroughSum (Φ.obj SminusFin) (g ≫ h) :=
  ⟨I, g ≫ (sumIso Φ hexact I).hom, (sumIso Φ hexact I).inv ≫ h, by simp⟩

/-- The image under `F` of the bicone `T₀ → T ← S₋^(I)`. -/
abbrev fBicone (T : D k) :
    BinaryBicone ((functor Φ).obj (DSplit.T₀D T))
      ((functor Φ).obj (DSplit.sumD (Kron.Splitting.I T.obj))) :=
  (functor Φ).mapBinaryBicone (DSplit.bicone T)

omit [Algebra k A] in
lemma fBicone_total (T : D k) :
    (fBicone Φ T).fst ≫ (fBicone Φ T).inl + (fBicone Φ T).snd ≫ (fBicone Φ T).inr = 𝟙 _ := by
  have := congrArg (functor Φ).map (DSplit.total T)
  rw [Functor.map_add, Functor.map_comp, Functor.map_comp] at this
  exact this.trans ((functor Φ).map_id _)

variable [FiniteDimensional k A]
  (hfin : ∀ X : Dfin k, Module.Finite k (RestrictScalars k A (Φ.obj X)))

include hexact hfin in
/-- Theorem 2.7, reflection of isomorphism classes on `D`. -/
theorem reflects_iso (R : Retractions k (Ψfin Φ)) {n : ℕ} (hn : R.NilpotentBound n)
    (hindS : IsIndecomposable A (Φ.obj SminusFin))
    (hnot : ∀ X : Dfin k, InC X.obj → IsEmpty (Φ.obj SminusFin ≅ Φ.obj X))
    (T U : D k) (e : (functor Φ).obj T ≅ (functor Φ).obj U) : Nonempty (T ≅ U) := by
  have hPfin : Module.Finite k (RestrictScalars k A (Φ.obj SminusFin)) := hfin _
  obtain ⟨ℓ, -, hℓ⟩ := exists_nonunitProductsVanish' (k := k) (Φ.obj SminusFin) hindS
  have hT := fBicone_total Φ T
  have hU := fBicone_total Φ U
  have hnsT := noSummand Φ R hfin hn hnot (DSplit.T₀D T) (DSplit.inC_T₀D T)
  have hnsU := noSummand Φ R hfin hn hnot (DSplit.T₀D U) (DSplit.inC_T₀D U)
  have h₁ : IsNilpotent (show End _ from
      blockγ (fBicone Φ T) (fBicone Φ U) e ≫ blockβ (fBicone Φ U) (fBicone Φ T) e.symm) :=
    isNilpotent_end_of_hom_pow _ (FixedSummand.pow_eq_zero_of_factorsThroughSum hℓ hnsT
      (factorsThroughSum_comp Φ hexact _ _ _))
  have h₂ : IsNilpotent (show End _ from
      blockγ (fBicone Φ U) (fBicone Φ T) e.symm ≫ blockβ (fBicone Φ T) (fBicone Φ U) e) :=
    isNilpotent_end_of_hom_pow _ (FixedSummand.pow_eq_zero_of_factorsThroughSum hℓ hnsU
      (factorsThroughSum_comp Φ hexact _ _ _))
  have := isIso_blockα (fBicone Φ T) (fBicone Φ U) hT hU e h₁ h₂
  -- the summands in `C` are isomorphic
  obtain ⟨φ⟩ : Nonempty (DSplit.T₀D T ≅ DSplit.T₀D U) := by
    obtain ⟨ψ⟩ := Retractions.reflects_iso (retractions Φ R hfin)
      (X := ⟨DSplit.T₀D T, DSplit.inC_T₀D T⟩) (Y := ⟨DSplit.T₀D U, DSplit.inC_T₀D U⟩)
      (asIso (blockα (fBicone Φ T) (fBicone Φ U) e))
    exact ⟨(InCD (k := k)).ι.mapIso ψ⟩
  -- the multiplicities of `S₋` agree
  have := isIso_schur (fBicone Φ T) (fBicone Φ U) hT hU e
  let s := asIso (blockδ (fBicone Φ T) (fBicone Φ U) e -
    blockβ (fBicone Φ T) (fBicone Φ U) e ≫ inv (blockα (fBicone Φ T) (fBicone Φ U) e) ≫
      blockγ (fBicone Φ T) (fBicone Φ U) e)
  let e' := (sumIso Φ hexact _).symm ≪≫ s ≪≫ sumIso Φ hexact _
  have hdim := (restrictScalarsLinearEquiv (k := k) e'.toLinearEquiv).rank_eq
  change Statement.dim k A _ = Statement.dim k A _ at hdim
  rw [dim_finsupp, dim_finsupp, Statement.dim, ← Module.finrank_eq_rank] at hdim
  have hpos : Module.finrank k (RestrictScalars k A (Φ.obj SminusFin)) ≠ 0 :=
    finrank_restrictScalars_ne_zero _ hPfin hindS.1
  obtain ⟨σ⟩ := Cardinal.eq.1 (Cardinal.eq_of_mul_natCast hpos hdim)
  exact ⟨biconeIso (DSplit.bicone T) (DSplit.bicone U) (DSplit.total T) (DSplit.total U) φ
    (DSplit.sumDIsoOfEquiv σ)⟩

end Extension

/-! ### Theorem 2.7 -/

/-- Indecomposability in `D_fin`: nonzero with only trivial idempotents. -/
def IsIndecDfin (X : Dfin k) : Prop := ¬ IsZero X.obj ∧ ∀ e : X ⟶ X, e ≫ e = e → e = 0 ∨ e = 𝟙 X

/-- The hypotheses of Theorem 2.7 on `Φ : D_fin → mod A`, apart from additivity,
`k`-linearity, faithfulness and the retractions: finite-dimensional values,
exactness, and the two facts about `S₋` that the proof uses (implied by
`Φ` being a representation embedding): `Φ(S₋)` is indecomposable, and it is
not isomorphic to `Φ(T)` for `T ∈ C_fin`. -/
structure IsRepEmbeddingFin (Φ : Dfin k ⥤ ModuleCat.{u} A) : Prop where
  fin : ∀ X : Dfin k, Module.Finite k (RestrictScalars k A (Φ.obj X))
  exact : IsExactOnDfin Φ
  indecS : IsIndecomposable A (Φ.obj Extension.SminusFin)
  notIsoS : ∀ X : Dfin k, InC X.obj → IsEmpty (Φ.obj Extension.SminusFin ≅ Φ.obj X)

lemma isIndecDfin_SminusFin : IsIndecDfin (Extension.SminusFin (k := k)) := by
  refine ⟨fun h ↦ Kron.id_Sminus_ne_zero (h.eq_of_src _ _), fun e he ↦ ?_⟩
  let g : k →ₗ[k] k := (e.hom.app one).hom
  have hg : ∀ x : k, g x = x * g 1 := fun x ↦ by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  have h₁ := congrArg (fun φ : Extension.SminusFin ⟶ Extension.SminusFin ↦ (φ.hom.app one).hom) he
  have hc : g (g 1) = g 1 := LinearMap.congr_fun h₁ (1 : k)
  rw [hg (g 1)] at hc
  have h0 : g 1 * (g 1 - 1) = 0 := by rw [mul_sub, hc, mul_one, sub_self]
  rcases mul_eq_zero.mp h0 with h0 | h1
  · left; ext1; apply Kron.hom_ext
    · ext x; rfl
    · apply ModuleCat.hom_ext
      exact LinearMap.ext fun (x : k) ↦ (hg x).trans ((congrArg (fun c ↦ x * c) h0).trans
        (mul_zero x))
  · right; ext1; apply Kron.hom_ext
    · ext x; rfl
    · apply ModuleCat.hom_ext
      exact LinearMap.ext fun (x : k) ↦ (hg x).trans ((congrArg (fun c ↦ x * c)
        (sub_eq_zero.1 h1)).trans (mul_one x))

namespace Extension

variable (Φ : Dfin k ⥤ ModuleCat.{u} A) [FiniteDimensional k A] [Φ.Additive] [Φ.Linear k]
  [Φ.Faithful] (hΦ : IsRepEmbeddingFin Φ) (R : Retractions k (Ψfin Φ)) {n : ℕ}
  (hn : R.NilpotentBound n)

omit [Φ.Faithful] in
include hΦ hn in
/-- Theorem 2.7: the extension `F` is a representation embedding on `D`. -/
theorem isRepresentationEmbedding : IsRepresentationEmbedding (functor Φ) := by
  refine ⟨inferInstance, inferInstance, fun X Y Z f g h ↦ map_shortExact Φ f g hΦ.exact h,
    fun X hX ↦ ?_, fun X Y ⟨e⟩ ↦ reflects_iso Φ hΦ.exact hΦ.fin R hn
      hΦ.indecS hΦ.notIsoS X Y e⟩
  rcases inC_or_iso_Sminus_of_isIndecomposable hX with hC | ⟨⟨e⟩⟩
  · refine Retractions.isIndecomposable (retractions Φ R hΦ.fin) (nilpotentBound Φ R hΦ.fin hn)
      (X := ⟨X, hC⟩) (fun h ↦ hX.1 ?_) (fun e he ↦ ?_)
    · have h' : 𝟙 X.obj = 0 := congrArg (fun φ ↦ InCD.kh φ) h
      exact (IsZero.iff_id_eq_zero _).2 h'
    · rcases hX.2 e.hom (congrArg InducedCategory.Hom.hom he) with h0 | h1
      · left; ext1; exact h0
      · right; ext1; exact h1
  · let e' : X ≅ Sminus := (InD (k := k)).fullyFaithfulι.preimageIso e
    have hS := hΦ.indecS
    exact hS.of_linearEquiv
      (((functor Φ).mapIso e' ≪≫ isoOfFin Φ Sminus Sminus_isFiniteDimensional).symm.toLinearEquiv)

omit [FiniteDimensional k A] [Φ.Additive] [Φ.Linear k] [Φ.Faithful] in
include hΦ in
/-- Theorem 2.7: finite-dimensional modules go to finite-dimensional modules. -/
theorem finite_of_finite (T : D k) (hT : T.obj.IsFiniteDimensional) :
    Module.Finite k (RestrictScalars k A ((functor Φ).obj T)) := by
  have := hΦ.fin (toDfin T hT)
  exact Module.Finite.equiv (restrictScalarsLinearEquiv (isoOfFin Φ T hT).symm.toLinearEquiv)

end Extension

end LargeIndecomposable
