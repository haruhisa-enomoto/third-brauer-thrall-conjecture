module

public import LargeIndecomposable.RepresentationEmbeddings.EmbeddingTheorem.Elements

/-!
# Finite-dimensional modules are finitely presented with respect to `F`

A homomorphism from a finite-dimensional `A`-module into `F(X)` factors
through some `Φ(U)`, and two such factorizations agree at a later stage. This
is the finite presentation used in the proofs of Proposition 2.5 and
Theorem 2.7. The algebra `A` is finite-dimensional.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A]

namespace Extension

variable (Φ : Dfin k ⥤ ModuleCat.{u} A)


/-- Finitely many finite-dimensional subrepresentations have a common upper
bound above a given one. -/
lemma exists_ge_of_finite {X : Kron k} {ι : Type*} [Finite ι] (U₀ : Kron.FinSub X)
    (U : ι → Kron.FinSub X) : ∃ U' : Kron.FinSub X, U₀ ≤ U' ∧ ∀ i, U i ≤ U' := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨M, hM⟩ := Finset.exists_le (insert U₀ (Finset.univ.image U))
  exact ⟨M, hM _ (Finset.mem_insert_self _ _),
    fun i ↦ hM _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))⟩

/-- Lifting an element of `F(X)` to a stage above a given one. -/
lemma exists_rep_ge' (X : D k) (U₀ : Kron.FinSub X.obj) (x : (functor Φ).obj X) :
    ∃ (U : Kron.FinSub X.obj) (_ : U₀ ≤ U) (y : Φ.obj ((finDiagram X).obj U)),
      (ιF Φ X U).hom y = x :=
  exists_rep_ge Φ X U₀ x

/-- The transition map `Φ(U) → Φ(U')`. -/
abbrev trans (X : D k) {U U' : Kron.FinSub X.obj} (h : U ≤ U') :
    Φ.obj ((finDiagram X).obj U) ⟶ Φ.obj ((finDiagram X).obj U') :=
  Φ.map ((finDiagram X).map (homOfLE h))

lemma trans_ιF (X : D k) {U U' : Kron.FinSub X.obj} (h : U ≤ U') :
    trans Φ X h ≫ ιF Φ X U' = ιF Φ X U :=
  ι_w Φ X h

lemma trans_trans (X : D k) {U U' U'' : Kron.FinSub X.obj} (h : U ≤ U') (h' : U' ≤ U'') :
    trans Φ X h ≫ trans Φ X h' = trans Φ X (h.trans h') := by
  rw [trans, trans, trans, ← Φ.map_comp, ← Functor.map_comp]
  rfl

/-- Finitely many elements of `Φ(U)` that vanish in `F(X)` vanish together at a
later stage. -/
lemma exists_trans_eq_zero (X : D k) (U : Kron.FinSub X.obj) {ι : Type*} [Finite ι]
    (y : ι → Φ.obj ((finDiagram X).obj U)) (hy : ∀ i, (ιF Φ X U).hom (y i) = 0) :
    ∃ (U' : Kron.FinSub X.obj) (h : U ≤ U'), ∀ i, (trans Φ X h).hom (y i) = 0 := by
  choose V hV hV0 using fun i ↦ (ιF_eq_zero_iff Φ X U (y i)).1 (hy i)
  obtain ⟨U', hU', hVU'⟩ := exists_ge_of_finite U V
  refine ⟨U', hU', fun i ↦ ?_⟩
  rw [← trans_trans Φ X (hV i) (hVU' i), ModuleCat.comp_apply, hV0 i, map_zero]

variable [Algebra k A] [FiniteDimensional k A]

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

/-- A homomorphism from a finite-dimensional module into `F(X)` factors
through `Φ(U)` for some `U` above a given `U₀`. -/
lemma exists_lift (X : D k) {M : ModuleCat.{u} A} [Module.Finite k M]
    (g : M ⟶ (functor Φ).obj X) (U₀ : Kron.FinSub X.obj) :
    ∃ (U : Kron.FinSub X.obj) (_ : U₀ ≤ U) (φ : M ⟶ Φ.obj ((finDiagram X).obj U)),
      φ ≫ ιF Φ X U = g := by
  classical
  let bM := Module.finBasis k M
  let bA := Module.finBasis k A
  -- lift the images of a basis of `M`
  choose V hV y hy using fun i ↦ exists_rep_ge Φ X U₀ (g.hom (bM i))
  obtain ⟨U, hU₀, hVU⟩ := exists_ge_of_finite U₀ V
  let y' : Fin _ → Φ.obj ((finDiagram X).obj U) := fun i ↦ (trans Φ X (hVU i)).hom (y i)
  have hy' : ∀ i, (ιF Φ X U).hom (y' i) = g.hom (bM i) := fun i ↦ by
    rw [← hy i, ← trans_ιF Φ X (hVU i)]; rfl
  let φ₀ : M →ₗ[k] Φ.obj ((finDiagram X).obj U) := bM.constr k y'
  have hφ₀ : ∀ m, (ιF Φ X U).hom (φ₀ m) = g.hom m := by
    have : ((ιF Φ X U).hom.restrictScalars k).comp φ₀ = g.hom.restrictScalars k :=
      bM.ext fun i ↦ by simp [φ₀, hy']
    exact fun m ↦ LinearMap.congr_fun this m
  -- the defect of `A`-linearity on the two bases vanishes at a later stage
  let d : Fin (Module.finrank k A) × Fin (Module.finrank k M) → Φ.obj ((finDiagram X).obj U) :=
    fun p ↦ φ₀ (bA p.1 • bM p.2) - bA p.1 • φ₀ (bM p.2)
  obtain ⟨U', hUU', hd⟩ := exists_trans_eq_zero Φ X U d (fun p ↦ by
    simp only [d, map_sub, map_smul, hφ₀, sub_self])
  let t := trans Φ X hUU'
  let φ₁ : M →ₗ[k] Φ.obj ((finDiagram X).obj U') := (t.hom.restrictScalars k).comp φ₀
  have hbasis : ∀ j i, φ₁ (bA j • bM i) = bA j • φ₁ (bM i) := fun j i ↦ by
    have := hd (j, i)
    simp only [d, map_sub, sub_eq_zero] at this
    change (trans Φ X hUU').hom _ = bA j • (trans Φ X hUU').hom _
    rw [this, map_smul]
  have hsmul : ∀ (a : A) (m : M), φ₁ (a • m) = a • φ₁ m := by
    intro a m
    rw [← bA.sum_repr a, ← bM.sum_repr m]
    simp only [Finset.sum_smul, Finset.smul_sum, map_sum, smul_assoc, map_smul,
      smul_comm (_ : A) (_ : k), hbasis]
  let φ : M ⟶ Φ.obj ((finDiagram X).obj U') :=
    ModuleCat.ofHom { toFun := φ₁, map_add' := φ₁.map_add, map_smul' := hsmul }
  refine ⟨U', hU₀.trans hUU', φ, ?_⟩
  ext m
  change (ιF Φ X U').hom (t.hom (φ₀ m)) = g.hom m
  rw [← ModuleCat.comp_apply, trans_ιF, hφ₀]

omit [FiniteDimensional k A] in
/-- Two homomorphisms from a finite-dimensional module into `Φ(U)` that agree
in `F(X)` agree at a later stage. -/
lemma exists_trans_eq (X : D k) {M : ModuleCat.{u} A} [Module.Finite k M]
    (U : Kron.FinSub X.obj) (φ ψ : M ⟶ Φ.obj ((finDiagram X).obj U))
    (h : φ ≫ ιF Φ X U = ψ ≫ ιF Φ X U) :
    ∃ (U' : Kron.FinSub X.obj) (hU : U ≤ U'), φ ≫ trans Φ X hU = ψ ≫ trans Φ X hU := by
  classical
  let bM := Module.finBasis k M
  obtain ⟨U', hU, h0⟩ := exists_trans_eq_zero Φ X U (fun i ↦ φ.hom (bM i) - ψ.hom (bM i))
    (fun i ↦ by
      rw [map_sub, sub_eq_zero, ← ModuleCat.comp_apply, h, ModuleCat.comp_apply])
  refine ⟨U', hU, ?_⟩
  ext m
  have : ((φ ≫ trans Φ X hU).hom.restrictScalars k) = ((ψ ≫ trans Φ X hU).hom.restrictScalars k) :=
    bM.ext fun i ↦ by
      have := h0 i
      rw [map_sub, sub_eq_zero] at this
      simpa using this
  exact LinearMap.congr_fun this m

end Extension

end LargeIndecomposable
