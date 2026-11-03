module

public import LargeIndecomposable.RepresentationEmbeddings.EmbeddingTheorem.Comparison
public import LargeIndecomposable.RepresentationEmbeddings.EmbeddingTheorem.CSub
public import LargeIndecomposable.RepresentationEmbeddings.EmbeddingTheorem.Lift
public import LargeIndecomposable.RepresentationEmbeddings.EmbeddingTheorem.SminusSplitting
public import LargeIndecomposable.Modules.KrullSchmidt.IndecomposableFullyFaithful

/-!
# Theorem 5.2: the embedding theorem

An `EmbeddingData k A` collects what the manuscript establishes for each of the
functors `F_ν : D → Mod A` of (3.5), apart from the reduction of Lemma 3.1:
`F` is `k`-linear, faithful and exact on `D`, has finite-dimensional values on
`D_fin`, satisfies the colimit comparison (3.6), admits retractions on `C` with
a nilpotence bound (Proposition 4.8), and satisfies the two facts about `S₋`
that the proof of Theorem 5.2 takes from the representation-embedding property
on `D_fin`: `F(S₋)` is indecomposable and not isomorphic to `F(T)` for
`T ∈ C_fin`.

Theorem 5.2 (`EmbeddingData.theoremA_conclusion`): such an `F` is a
representation embedding on `D` with the three properties of Theorem A.
The proof follows the manuscript.

* Step 1 (`noSummand`): for `T₀ ∈ C`, `F(T₀)` has no direct summand isomorphic
  to `P = F(S₋)`. A split monomorphism `P → F(T₀)` factors through `F(T₁)` for a
  finite-dimensional `T₁ ⊆ T₀` in `C`, by (3.6). Instead of the Krull–Schmidt
  theorem we use the retractions: the idempotent of `F(T₁)` splitting off `P`
  is conjugate to `F(η)` for the idempotent `η = ρ(ε)` of `T₁`, so `P` is
  isomorphic to `F` of a summand of `T₁` in `C_fin`.
* Step 2 (`reflects_iso`): cancellation of the copies of `P`, by Lemma 5.1 and
  the block computation (5.1).
* Step 3: preservation of indecomposability, by Lemma 2.4 on `C` and the fact
  that `F(S₋)` is indecomposable.

The embedding transports along the functor of Lemma 3.1 (`transport`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair

universe u

variable (k : Type u) [Field k] (A : Type u) [Ring A] [Algebra k A]

/-- The data of Theorem 5.2 for a functor `F : D → Mod A`. -/
structure EmbeddingData where
  /-- The functor. -/
  F : D k ⥤ ModuleCat.{u} A
  [additive : F.Additive]
  [linear : F.Linear k]
  [faithful : F.Faithful]
  exact : IsExactOnD F
  fin : ∀ X : Dfin k, Module.Finite k (RestrictScalars k A ((DfinToD k ⋙ F).obj X))
  comparison : Comparison.IsComparison F
  /-- Retractions on `C`. -/
  R : Retractions k ((InCD (k := k)).ι ⋙ F)
  /-- The nilpotence bound. -/
  n : ℕ
  bound : R.NilpotentBound n
  indecS : IsIndecomposable A (F.obj Extension.Sminus)
  notIsoS : ∀ X : Dfin k, InC X.obj →
    IsEmpty (F.obj Extension.Sminus ≅ F.obj ((DfinToD k).obj X))

attribute [instance] EmbeddingData.additive EmbeddingData.linear EmbeddingData.faithful

variable {k A}

/-- `T` as an object of `C`. -/
abbrev toC (T : D k) (hT : InC T.obj) : (InCD (k := k)).FullSubcategory := ⟨T, hT⟩

/-- A functor of module categories preserving short exact sequences, in the
three-part form of `Statement.IsRepresentationEmbedding`. -/
def PreservesSES {B : Type u} [Ring B] (G : ModuleCat.{u} B ⥤ ModuleCat.{u} A) : Prop :=
  ∀ (L M N : ModuleCat.{u} B) (f : L ⟶ M) (g : M ⟶ N), Function.Injective f.hom →
    Function.Surjective g.hom → LinearMap.range f.hom = LinearMap.ker g.hom →
    Function.Injective (G.map f).hom ∧ Function.Surjective (G.map g).hom ∧
      LinearMap.range (G.map f).hom = LinearMap.ker (G.map g).hom

namespace EmbeddingData

variable (E : EmbeddingData k A)

/-- `F` restricted to `C`. -/
abbrev Ψ : (InCD (k := k)).FullSubcategory ⥤ ModuleCat.{u} A := (InCD (k := k)).ι ⋙ E.F

/-! ### Step 1: no summand `F(S₋)` -/

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable [FiniteDimensional k A]

/-- Step 1 of the proof of Theorem 5.2: for `T₀ ∈ C`, the module `F(T₀)` has no
direct summand isomorphic to `F(S₋)`. -/
theorem noSummand (T₀ : D k) (hT₀ : InC T₀.obj) :
    FixedSummand.NoSummand (E.F.obj Extension.Sminus) (E.F.obj T₀) := by
  intro i p hip
  let Φ := Comparison.fin E.F
  let P := E.F.obj Extension.Sminus
  have : Module.Finite k P := E.fin Extension.SminusFin
  -- factor `i` through `F(T₁)` for a finite-dimensional `T₁ ⊆ T₀` in `C` (3.6)
  let iso := Comparison.isoApp E.comparison T₀
  obtain ⟨U, -, i₀, hi₀⟩ := Extension.exists_lift Φ T₀ (i ≫ iso.hom) ⟨⊥, Kron.Sub.isFin_bot⟩
  obtain ⟨V₀, hV₀⟩ := Kron.FinV.exists_le hT₀ U
  let T₁ : (InCD (k := k)).FullSubcategory :=
    ⟨(DfinToD k).obj ((Extension.finDiagram T₀).obj V₀.toFinSub), Kron.Sub.inC_ofV T₀.2 V₀.1⟩
  let j : (E.Ψ).obj T₁ ⟶ E.F.obj T₀ := E.F.map (Comparison.incl T₀ V₀.toFinSub)
  let i' : P ⟶ (E.Ψ).obj T₁ := i₀ ≫ Extension.trans Φ T₀ hV₀
  have hij : i' ≫ j = i := by
    have h₁ : Extension.trans Φ T₀ hV₀ ≫ j = E.F.map (Comparison.incl T₀ U) :=
      (E.F.map_comp _ _).symm.trans (congrArg E.F.map (Comparison.map_incl T₀ (homOfLE hV₀)))
    have h₂ : E.F.map (Comparison.incl T₀ U) = Extension.ι Φ T₀ U ≫ iso.inv :=
      (Iso.eq_comp_inv iso).2 (Comparison.incl_isoApp E.comparison T₀ U)
    calc i' ≫ j = i₀ ≫ Extension.ι Φ T₀ U ≫ iso.inv := by
          simp only [i', Category.assoc, h₁, h₂]
      _ = (i₀ ≫ Extension.ι Φ T₀ U) ≫ iso.inv := (Category.assoc _ _ _).symm
      _ = i := (Iso.comp_inv_eq iso).2 hi₀
  let p' : (E.Ψ).obj T₁ ⟶ P := j ≫ p
  have hip' : i' ≫ p' = 𝟙 _ := by
    show i' ≫ j ≫ p = 𝟙 _
    rw [← Category.assoc, hij, hip]
  -- the idempotent `ε` and its retraction `η`
  let ε : (E.Ψ).obj T₁ ⟶ (E.Ψ).obj T₁ := p' ≫ i'
  have hε : ε ≫ ε = ε := by
    simp only [ε, Category.assoc]; rw [← Category.assoc i', hip', Category.id_comp]
  let η : T₁ ⟶ T₁ := E.R.ρ T₁ T₁ ε
  have hη : η ≫ η = η := by simp only [η]; rw [← E.R.map_comp, hε]
  let f : (E.Ψ).obj T₁ ⟶ (E.Ψ).obj T₁ := (E.Ψ).map η
  -- the conjugating unit
  let w : (E.Ψ).obj T₁ ⟶ (E.Ψ).obj T₁ := ε ≫ f + (𝟙 _ - ε) ≫ (𝟙 _ - f)
  have hρw : E.R.ρ T₁ T₁ (𝟙 _ - w) = 0 := by
    simp only [w, map_sub, map_add, E.R.map_comp, E.R.ρ_id, f, E.R.ρ_map]
    change 𝟙 T₁ - (η ≫ η + (𝟙 T₁ - η) ≫ (𝟙 T₁ - η)) = 0
    simp [Preadditive.sub_comp, Preadditive.comp_sub, hη]
  have hw : IsIso w := by
    have hnil : IsNilpotent (show End ((E.Ψ).obj T₁) from 𝟙 _ - w) :=
      ⟨E.n, by
        rw [← Extension.Retractions.iter_eq_pow]
        exact E.bound _ (E.R.kerChain_iter _ hρw E.n)⟩
    have := isIso_id_sub_of_isNilpotent _ hnil
    simpa using this
  have hεw : ε ≫ w = w ≫ f := by
    have hff : f ≫ f = f := by simp only [f]; rw [← Functor.map_comp, hη]
    simp only [w, Preadditive.comp_add, Preadditive.add_comp, Preadditive.comp_sub,
      Preadditive.sub_comp, Category.comp_id, Category.id_comp, Category.assoc, hff,
      ← Category.assoc ε ε, hε]
    abel
  -- the summand `T₁' = im η` of `T₁`, finite-dimensional and in `C`
  let ηK : T₁.obj.obj ⟶ T₁.obj.obj := InCD.kh η
  have hηK : ηK ≫ ηK = ηK := by
    change InCD.kh (η ≫ η) = _; rw [hη]
  have hT₁fin : T₁.obj.obj.IsFiniteDimensional := V₀.toFinSub.2
  let T₁' : Dfin k := ⟨(Kron.imSub ηK).toKron, (Kron.imSub ηK).inD T₁.obj.2,
    Kron.isFiniteDimensional_imSub ηK hT₁fin⟩
  let ιT : (DfinToD k).obj T₁' ⟶ T₁.obj := ObjectProperty.homMk (Kron.imSub ηK).ι
  let rT : T₁.obj ⟶ (DfinToD k).obj T₁' := ObjectProperty.homMk (Kron.imRetr ηK)
  have hrι : rT ≫ ιT = η.hom := by ext1; exact Kron.imRetr_ι ηK
  have hιr : ιT ≫ rT = 𝟙 _ := by ext1; exact Kron.ι_imRetr ηK hηK
  -- `F(S₋) ≅ F(T₁')`
  let e : P ≅ E.F.obj ((DfinToD k).obj T₁') :=
    { hom := i' ≫ w ≫ E.F.map rT
      inv := E.F.map ιT ≫ inv w ≫ p'
      hom_inv_id := by
        have h₁ : w ≫ E.F.map rT ≫ E.F.map ιT ≫ inv w = ε := by
          rw [← Category.assoc (E.F.map rT), ← E.F.map_comp, hrι]
          change w ≫ f ≫ inv w = ε
          rw [← Category.assoc, ← hεw, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
        calc i' ≫ (w ≫ E.F.map rT) ≫ E.F.map ιT ≫ inv w ≫ p'
            = i' ≫ (w ≫ E.F.map rT ≫ E.F.map ιT ≫ inv w) ≫ p' := by
              simp only [Category.assoc]
          _ = (i' ≫ p') ≫ (i' ≫ p') := by rw [h₁]; simp only [ε, Category.assoc]
          _ = 𝟙 _ := by rw [hip', Category.id_comp]
      inv_hom_id := by
        have h₁ : inv w ≫ ε ≫ w = f := by rw [hεw, IsIso.inv_hom_id_assoc]
        calc (E.F.map ιT ≫ inv w ≫ p') ≫ i' ≫ w ≫ E.F.map rT
            = E.F.map ιT ≫ (inv w ≫ ε ≫ w) ≫ E.F.map rT := by simp only [ε, Category.assoc]
          _ = E.F.map (ιT ≫ (rT ≫ ιT) ≫ rT) := by
            rw [h₁, hrι]; simp only [E.F.map_comp]; rfl
          _ = 𝟙 _ := by
            rw [show (ιT ≫ (rT ≫ ιT) ≫ rT) = 𝟙 _ by
              rw [← Category.assoc, ← Category.assoc, hιr, Category.id_comp, hιr], E.F.map_id] }
  exact (E.notIsoS T₁' (Kron.inC_imSub ηK T₁.2)).false e

/-! ### Step 2: reflection of isomorphism classes -/

/-- `F(S₋^(I)) ≅ P^(I)` with `P = F(S₋)`. -/
def sumIso (I : Type u) :
    E.F.obj (DSplit.sumD I) ≅ ModuleCat.of A (I →₀ E.F.obj Extension.Sminus) :=
  haveI := Comparison.preservesCoproducts E.comparison E.exact I
  IsColimit.coconePointsIsoOfNatIso (isColimitOfPreserves E.F (DSplit.isColimitCofan I))
    (isColimitFinsuppCofan _ I) (Discrete.natIso fun _ ↦ Iso.refl _)

omit [FiniteDimensional k A] in
lemma factorsThroughSum_comp {X Y : ModuleCat.{u} A} (I : Type u)
    (g : X ⟶ E.F.obj (DSplit.sumD I)) (h : E.F.obj (DSplit.sumD I) ⟶ Y) :
    FixedSummand.FactorsThroughSum (E.F.obj Extension.Sminus) (g ≫ h) :=
  ⟨I, g ≫ (E.sumIso I).hom, (E.sumIso I).inv ≫ h, by simp⟩

/-- The image under `F` of the bicone `T₀ → T ← S₋^(I)`. -/
abbrev fBicone (T : D k) :
    BinaryBicone (E.F.obj (DSplit.T₀D T)) (E.F.obj (DSplit.sumD (Kron.Splitting.I T.obj))) :=
  E.F.mapBinaryBicone (DSplit.bicone T)

omit [FiniteDimensional k A] in
lemma fBicone_total (T : D k) :
    (E.fBicone T).fst ≫ (E.fBicone T).inl + (E.fBicone T).snd ≫ (E.fBicone T).inr = 𝟙 _ := by
  have := congrArg E.F.map (DSplit.total T)
  rw [Functor.map_add, Functor.map_comp, Functor.map_comp] at this
  exact this.trans (E.F.map_id _)

/-- Step 2 of the proof of Theorem 5.2: `F` reflects isomorphism classes on `D`. -/
theorem reflects_iso (T U : D k) (e : E.F.obj T ≅ E.F.obj U) : Nonempty (T ≅ U) := by
  have hPfin : Module.Finite k (RestrictScalars k A (E.F.obj Extension.Sminus)) :=
    E.fin Extension.SminusFin
  obtain ⟨ℓ, -, hℓ⟩ := exists_nonunitProductsVanish' (k := k) (E.F.obj Extension.Sminus) E.indecS
  have hT := E.fBicone_total T
  have hU := E.fBicone_total U
  have hnsT := E.noSummand (DSplit.T₀D T) (DSplit.inC_T₀D T)
  have hnsU := E.noSummand (DSplit.T₀D U) (DSplit.inC_T₀D U)
  have h₁ : IsNilpotent (show End _ from
      blockγ (E.fBicone T) (E.fBicone U) e ≫ blockβ (E.fBicone U) (E.fBicone T) e.symm) :=
    isNilpotent_end_of_hom_pow _ (FixedSummand.pow_eq_zero_of_factorsThroughSum hℓ hnsT
      (E.factorsThroughSum_comp _ _ _))
  have h₂ : IsNilpotent (show End _ from
      blockγ (E.fBicone U) (E.fBicone T) e.symm ≫ blockβ (E.fBicone T) (E.fBicone U) e) :=
    isNilpotent_end_of_hom_pow _ (FixedSummand.pow_eq_zero_of_factorsThroughSum hℓ hnsU
      (E.factorsThroughSum_comp _ _ _))
  have := isIso_blockα (E.fBicone T) (E.fBicone U) hT hU e h₁ h₂
  -- the summands in `C` are isomorphic (Lemma 2.4)
  obtain ⟨φ⟩ : Nonempty (DSplit.T₀D T ≅ DSplit.T₀D U) := by
    obtain ⟨ψ⟩ := Retractions.reflects_iso E.R
      (X := toC (DSplit.T₀D T) (DSplit.inC_T₀D T)) (Y := toC (DSplit.T₀D U) (DSplit.inC_T₀D U))
      (asIso (blockα (E.fBicone T) (E.fBicone U) e))
    exact ⟨(InCD (k := k)).ι.mapIso ψ⟩
  -- the multiplicities of `S₋` agree
  have := isIso_schur (E.fBicone T) (E.fBicone U) hT hU e
  let s := asIso (blockδ (E.fBicone T) (E.fBicone U) e -
    blockβ (E.fBicone T) (E.fBicone U) e ≫ inv (blockα (E.fBicone T) (E.fBicone U) e) ≫
      blockγ (E.fBicone T) (E.fBicone U) e)
  let e' := (E.sumIso _).symm ≪≫ s ≪≫ E.sumIso _
  have hdim := (restrictScalarsLinearEquiv (k := k) e'.toLinearEquiv).rank_eq
  change Statement.dim k A _ = Statement.dim k A _ at hdim
  rw [dim_finsupp, dim_finsupp, Statement.dim, ← Module.finrank_eq_rank] at hdim
  have hpos : Module.finrank k (RestrictScalars k A (E.F.obj Extension.Sminus)) ≠ 0 :=
    finrank_restrictScalars_ne_zero _ hPfin E.indecS.1
  obtain ⟨σ⟩ := Cardinal.eq.1 (Cardinal.eq_of_mul_natCast hpos hdim)
  exact ⟨biconeIso (DSplit.bicone T) (DSplit.bicone U) (DSplit.total T) (DSplit.total U) φ
    (DSplit.sumDIsoOfEquiv σ)⟩

/-! ### Theorem 5.2 -/

/-- Step 3 and the conclusion of Theorem 5.2: `F` is a representation
embedding on `D`. -/
theorem isRepresentationEmbedding : IsRepresentationEmbedding E.F := by
  refine ⟨inferInstance, inferInstance, E.exact, fun X hX ↦ ?_,
    fun X Y ⟨e⟩ ↦ E.reflects_iso X Y e⟩
  rcases inC_or_iso_Sminus_of_isIndecomposable hX with hC | ⟨⟨e⟩⟩
  · refine Retractions.isIndecomposable E.R E.bound (X := toC X hC) (fun h ↦ hX.1 ?_)
      (fun e he ↦ ?_)
    · have h' : 𝟙 X.obj = 0 := congrArg (fun φ ↦ InCD.kh φ) h
      exact (IsZero.iff_id_eq_zero _).2 h'
    · rcases hX.2 e.hom (congrArg InducedCategory.Hom.hom he) with h0 | h1
      · left; ext1; exact h0
      · right; ext1; exact h1
  · let e' : X ≅ Extension.Sminus := (InD (k := k)).fullyFaithfulι.preimageIso e
    exact E.indecS.of_linearEquiv (E.F.mapIso e').symm.toLinearEquiv

include E in
/-- Theorem 5.2: the functor of an `EmbeddingData` satisfies the conclusion of
Theorem A. -/
theorem theoremA_conclusion :
    ∃ F : D k ⥤ ModuleCat.{u} A,
      IsRepresentationEmbedding F ∧
      (∀ T : D k, T.obj.IsFiniteDimensional → Module.Finite k (RestrictScalars k A (F.obj T))) ∧
      (∀ ι : Type u, PreservesColimitsOfShape (Discrete ι) F) ∧
      PreservesFilteredColimitsOfSize.{u, u} F ∧
      (∀ T : D k, Cardinal.aleph0 ≤ T.obj.dim → dim k A (F.obj T) = T.obj.dim) :=
  ⟨E.F, E.isRepresentationEmbedding, fun T hT ↦ E.fin ⟨T.obj, T.2, hT⟩,
    Comparison.preservesCoproducts E.comparison E.exact,
    Comparison.preservesFilteredColimits E.comparison E.exact,
    Comparison.dim_eq E.comparison E.fin⟩

end EmbeddingData

/-! ### Transport along the functor of Lemma 3.1 -/

namespace EmbeddingData

variable {B : Type u} [Ring B] [Algebra k B]

/-- Transport of the data of Theorem 5.2 along a fully faithful exact functor
of module categories that preserves finite dimension and filtered colimits
(the functor `Φ` of Lemma 3.1). -/
def transport (E : EmbeddingData k B) (G : ModuleCat.{u} B ⥤ ModuleCat.{u} A)
    [G.Additive] [G.Linear k] (hG : G.FullyFaithful) (hexact : PreservesSES G)
    (hfin : ∀ M : ModuleCat.{u} B, Module.Finite k (RestrictScalars k B M) →
      Module.Finite k (RestrictScalars k A (G.obj M)))
    [PreservesFilteredColimitsOfSize.{u, u} G] : EmbeddingData k A :=
  haveI := hG.full
  haveI := hG.faithful
  { F := E.F ⋙ G
    exact := fun X Y Z f g h ↦ by
      obtain ⟨h₁, h₂, h₃⟩ := E.exact X Y Z f g h
      exact hexact _ _ _ _ _ h₁ h₂ h₃
    fin := fun X ↦ hfin _ (E.fin X)
    comparison := fun X ↦ ⟨isColimitOfPreserves G (E.comparison X).some⟩
    R := E.R.postcomp hG
    n := E.n
    bound := Retractions.NilpotentBound.postcomp _ hG E.bound
    indecS := (Reduction.isIndecomposable_map_iff G _).2 E.indecS
    notIsoS := fun X hX ↦ ⟨fun e ↦ (E.notIsoS X hX).false (hG.preimageIso e)⟩ }

end EmbeddingData

end LargeIndecomposable
