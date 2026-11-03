module

public import LargeIndecomposable.RepresentationEmbeddings.EmbeddingTheorem.ImageSummand
public import LargeIndecomposable.RepresentationEmbeddings.EmbeddingTheorem.Preserves
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Splitting off the copies of `S₋`

Tools for Step 2 of the proof of Theorem 5.2. Inside `D`, every `T` splits as
`T₀ ⊕ S₋^(I)` with `T₀ ∈ C` (2.2) (`DSplit.bicone`); `S₋^(I)` is a coproduct of
copies of `S₋` in `D`, and `I →₀ P` a coproduct of copies of a module `P`.
Bicones with isomorphic summands have isomorphic points, a positive finite
factor cancels from cardinals, and the dimension of `I →₀ P` is `|I| dim P`.
Also: `S₋` is indecomposable in `D_fin`.
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

/-! ### Indecomposability of `S₋` -/

/-- Indecomposability in `D_fin`: nonzero with only trivial idempotents. -/
def IsIndecDfin (X : Dfin k) : Prop := ¬ IsZero X.obj ∧ ∀ e : X ⟶ X, e ≫ e = e → e = 0 ∨ e = 𝟙 X

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

end LargeIndecomposable
