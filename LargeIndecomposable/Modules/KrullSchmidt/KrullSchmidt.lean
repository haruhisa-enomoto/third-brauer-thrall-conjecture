module

public import LargeIndecomposable.Modules.KrullSchmidt.LocalEnd
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Logic.Equiv.Option

/-!
# The Krull–Schmidt theorem for modules of finite length

* Existence: an Artinian module is isomorphic to a finite product
  `Π i, X i` of indecomposable modules (`exists_linearEquiv_pi`).
* Exchange: if an indecomposable module `P` with local endomorphism ring is a
  direct summand of `Π j, X j` with every `X j` indecomposable, then
  `P ≅ X j` for some `j` (`exists_nonempty_linearEquiv_of_comp_eq_id`). This
  is the cancellation form used in the proof of Theorem 5.1.
* Uniqueness: two decompositions of a module of finite length into finitely
  many indecomposables agree up to a bijection of the index sets and
  isomorphisms of the summands (`krullSchmidt`).

Each statement has a `ModuleCat` form with biproducts `⨁ X` and a form with
finite dimension stated through `RestrictScalars k A`, as in `Statement.dim`.
Finite products are used instead of direct sums since the index sets are
finite.

The existence part follows the module specialization in
`Modules/KrullSchmidt/FiniteModuleDecomposition.lean` of
`multiplicative-bases-deformations` at commit
`7b9f39f221d8a420a1531f487a3b93ae6d26ce85`, with induction on submodules
instead of dimension. The uniqueness part is the standard exchange argument.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open Statement CategoryTheory Limits

universe u

variable {A : Type u} [Ring A]

namespace KrullSchmidt

/-! ### Linear-algebra preliminaries -/

/-- `Equiv.piSplitAt` as a linear equivalence. -/
def piSplitAt {ι : Type} [DecidableEq ι] (i : ι) (X : ι → ModuleCat.{u} A) :
    (Π j, X j) ≃ₗ[A] X i × Π j : {j // j ≠ i}, X j where
  __ := Equiv.piSplitAt i (fun j ↦ X j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma piSplitAt_symm_inl {ι : Type} [DecidableEq ι] (i : ι) (X : ι → ModuleCat.{u} A)
    (x : X i) : (piSplitAt i X).symm (x, 0) = Pi.single i x := by
  funext j
  by_cases h : j = i
  · subst h
    simp [piSplitAt]
  · simp [piSplitAt, h]

/-- In a local ring, a finite sum of nonunits is a nonunit. -/
lemma not_isUnit_sum {R ι : Type*} [Ring R] [IsLocalRing R] (s : Finset ι) (f : ι → R)
    (hf : ∀ i ∈ s, ¬ IsUnit (f i)) : ¬ IsUnit (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact IsLocalRing.nonunits_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- A module with local endomorphism ring is nontrivial. -/
lemma nontrivial_of_isLocalRing_end {P : Type u} [AddCommGroup P] [Module A P]
    [IsLocalRing (Module.End A P)] : Nontrivial P := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact one_ne_zero (LinearMap.ext fun x ↦ Subsingleton.elim _ _ : (1 : Module.End A P) = 0)

/-- If `e : X × X' ≅ Y × Y'` has invertible component `X → Y`, then `X' ≅ Y'`:
both `0 × Y'` and `e(0 × X')` are complements of `e(X × 0)`. -/
theorem nonempty_linearEquiv_of_prod {X X' Y Y' : Type u} [AddCommGroup X] [Module A X]
    [AddCommGroup X'] [Module A X'] [AddCommGroup Y] [Module A Y] [AddCommGroup Y']
    [Module A Y'] (e : (X × X') ≃ₗ[A] (Y × Y'))
    (he : Function.Bijective (LinearMap.fst A Y Y' ∘ₗ e.toLinearMap ∘ₗ LinearMap.inl A X X')) :
    Nonempty (X' ≃ₗ[A] Y') := by
  let L : Submodule A (Y × Y') := (LinearMap.range (LinearMap.inl A X X')).map e.toLinearMap
  let C : Submodule A (Y × Y') := LinearMap.range (LinearMap.inr A Y Y')
  let C' : Submodule A (Y × Y') := (LinearMap.range (LinearMap.inr A X X')).map e.toLinearMap
  have h1 : IsCompl L C := by
    constructor
    · rw [Submodule.disjoint_def]
      rintro q ⟨_, ⟨x, rfl⟩, rfl⟩ ⟨y, hy⟩
      have hx : (LinearMap.fst A Y Y' ∘ₗ e.toLinearMap ∘ₗ LinearMap.inl A X X') x = 0 := by
        have := congrArg Prod.fst hy
        simpa using this.symm
      rw [show x = 0 from he.1 (by rw [hx, map_zero])]
      simp
    · rw [codisjoint_iff, eq_top_iff]
      rintro q -
      obtain ⟨x, hx⟩ := he.2 q.1
      have hq : q = e (x, 0) + (0, q.2 - (e (x, 0)).2) := by
        ext
        · simpa using hx.symm
        · simp
      rw [hq]
      exact Submodule.add_mem_sup ⟨_, ⟨x, rfl⟩, rfl⟩ ⟨_, rfl⟩
  have h2 : IsCompl L C' :=
    (Submodule.orderIsoMapComap e).isCompl LinearMap.isCompl_range_inl_inr
  exact ⟨((LinearEquiv.ofInjective _ LinearMap.inr_injective).trans
    (e.submoduleMap _)).trans (((Submodule.quotientEquivOfIsCompl L C' h2).symm.trans
      (Submodule.quotientEquivOfIsCompl L C h1)).trans
        (LinearEquiv.ofInjective _ LinearMap.inr_injective).symm)⟩

/-! ### Exchange -/

/-- If `P` has local endomorphism ring and is a direct summand of `Π j, X j`
(`p ∘ i = id`) with every `X j` indecomposable, then some component
`P → Π j, X j → X j` is bijective. -/
theorem exists_bijective_proj_comp {ι : Type} [Fintype ι] {P : Type u} [AddCommGroup P]
    [Module A P] [IsLocalRing (Module.End A P)] {X : ι → ModuleCat.{u} A}
    (hX : ∀ j, IsIndecomposable A (X j)) (i : P →ₗ[A] Π j, X j) (p : (Π j, X j) →ₗ[A] P)
    (hpi : p ∘ₗ i = LinearMap.id) :
    ∃ j, Function.Bijective (LinearMap.proj (φ := fun j ↦ X j) j ∘ₗ i) := by
  classical
  have := nontrivial_of_isLocalRing_end (A := A) (P := P)
  let u : ι → Module.End A P := fun j ↦
    p ∘ₗ LinearMap.single A (fun j ↦ X j) j ∘ₗ LinearMap.proj j ∘ₗ i
  have hsum : ∑ j, u j = 1 := by
    refine LinearMap.ext fun x ↦ ?_
    rw [LinearMap.sum_apply]
    simp only [u, LinearMap.comp_apply, LinearMap.coe_single, LinearMap.coe_proj,
      Function.eval]
    rw [← map_sum p, Finset.univ_sum_single (i x)]
    exact congrArg (fun φ : P →ₗ[A] P ↦ φ x) hpi
  obtain ⟨j, -, hj⟩ : ∃ j ∈ Finset.univ, IsUnit (u j) := by
    by_contra! h
    exact not_isUnit_sum _ _ h (hsum ▸ isUnit_one)
  refine ⟨j, (hX j).bijective_of_comp_eq_id _
    (↑hj.unit⁻¹ ∘ₗ p ∘ₗ LinearMap.single A (fun j ↦ X j) j) ?_⟩
  have h := hj.val_inv_mul
  rw [Module.End.mul_eq_comp] at h
  simpa [u, LinearMap.comp_assoc, Module.End.one_eq_id] using h

/-- **Exchange.** An indecomposable module of finite length that is a direct
summand of `M ≅ Π j, X j`, with every `X j` indecomposable, is isomorphic to
some `X j`. -/
theorem exists_nonempty_linearEquiv_of_comp_eq_id {ι : Type} [Fintype ι] {P M : Type u}
    [AddCommGroup P] [Module A P] [IsNoetherian A P] [IsArtinian A P] [AddCommGroup M]
    [Module A M] (hP : IsIndecomposable A P) {X : ι → ModuleCat.{u} A}
    (hX : ∀ j, IsIndecomposable A (X j)) (e : M ≃ₗ[A] Π j, X j) (i : P →ₗ[A] M)
    (p : M →ₗ[A] P) (hpi : p ∘ₗ i = LinearMap.id) : ∃ j, Nonempty (P ≃ₗ[A] X j) := by
  have := hP.isLocalRing_end
  obtain ⟨j, hj⟩ := exists_bijective_proj_comp hX (e.toLinearMap ∘ₗ i)
    (p ∘ₗ e.symm.toLinearMap) (by ext x; simpa using congrArg (fun φ ↦ φ x) hpi)
  exact ⟨j, ⟨LinearEquiv.ofBijective _ hj⟩⟩

/-! ### Uniqueness -/

/-- The induction behind `krullSchmidt`. -/
theorem exists_equiv_of_linearEquiv_pi (n : ℕ) :
    ∀ {ι κ : Type} [Fintype ι] [Fintype κ], Fintype.card ι = n →
      ∀ {X : ι → ModuleCat.{u} A} {Y : κ → ModuleCat.{u} A},
        (∀ i, IsIndecomposable A (X i) ∧ IsLocalRing (Module.End A (X i))) →
        (∀ j, IsIndecomposable A (Y j)) → ((Π i, X i) ≃ₗ[A] Π j, Y j) →
        ∃ σ : ι ≃ κ, ∀ i, Nonempty (X i ≃ₗ[A] Y (σ i)) := by
  classical
  induction n with
  | zero =>
    intro ι κ _ _ hn X Y hX hY e
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn
    have : IsEmpty κ := by
      refine ⟨fun j ↦ ?_⟩
      have := (hY j).1
      obtain ⟨y, hy⟩ := exists_ne (0 : Y j)
      have h0 : e.symm (Pi.single j y) = 0 := Subsingleton.elim _ _
      exact hy (by simpa using congrFun (e.symm.injective (h0.trans e.symm.map_zero.symm)) j)
    exact ⟨Equiv.equivOfIsEmpty ι κ, fun i ↦ isEmptyElim i⟩
  | succ n ih =>
    intro ι κ _ _ hn X Y hX hY e
    obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    have := (hX i₀).2
    obtain ⟨j₀, hj₀⟩ := exists_bijective_proj_comp hY
      (e.toLinearMap ∘ₗ LinearMap.single A (fun i ↦ X i) i₀)
      (LinearMap.proj i₀ ∘ₗ e.symm.toLinearMap) (by ext x; simp)
    let e' := ((piSplitAt i₀ X).symm.trans e).trans (piSplitAt j₀ Y)
    have hcomp : ⇑(LinearMap.fst A _ _ ∘ₗ e'.toLinearMap ∘ₗ LinearMap.inl A _ _) =
        ⇑(LinearMap.proj (φ := fun j ↦ Y j) j₀ ∘ₗ
          e.toLinearMap ∘ₗ LinearMap.single A (fun i ↦ X i) i₀) := by
      funext x
      change (piSplitAt j₀ Y (e ((piSplitAt i₀ X).symm (x, 0)))).1 = e (Pi.single i₀ x) j₀
      rw [piSplitAt_symm_inl]
      rfl
    obtain ⟨e''⟩ := nonempty_linearEquiv_of_prod e' (hcomp ▸ hj₀)
    have hcard : Fintype.card {i // i ≠ i₀} = n := by
      simp [Fintype.card_subtype_compl, hn]
    obtain ⟨σ', hσ'⟩ := ih hcard (X := fun i : {i // i ≠ i₀} ↦ X i)
      (Y := fun j : {j // j ≠ j₀} ↦ Y j)
      (fun i ↦ hX i) (fun j ↦ hY j) e''
    let σ : ι ≃ κ := (Equiv.optionSubtypeNe i₀).symm.trans
      ((Equiv.optionCongr σ').trans (Equiv.optionSubtypeNe j₀))
    refine ⟨σ, fun i ↦ ?_⟩
    by_cases h : i = i₀
    · subst h
      have hσ : σ i = j₀ := by simp [σ]
      rw [hσ]
      exact ⟨LinearEquiv.ofBijective _ hj₀⟩
    · have hσ : σ i = σ' ⟨i, h⟩ := by
        simp only [σ, Equiv.trans_apply, Equiv.optionSubtypeNe_symm_of_ne h,
          Equiv.optionCongr_apply, Option.map_some, Equiv.optionSubtypeNe_some]
      rw [hσ]
      exact hσ' ⟨i, h⟩

/-- The summands of a module of finite length are of finite length. -/
lemma isNoetherian_isArtinian_of_linearEquiv_pi {ι : Type} [DecidableEq ι] {M : Type u}
    [AddCommGroup M] [Module A M] [IsNoetherian A M] [IsArtinian A M]
    {X : ι → ModuleCat.{u} A} (e : M ≃ₗ[A] Π i, X i) (i : ι) :
    IsNoetherian A (X i) ∧ IsArtinian A (X i) :=
  ⟨isNoetherian_of_injective (e.symm.toLinearMap ∘ₗ LinearMap.single A (fun i ↦ X i) i)
      (e.symm.injective.comp fun x y h ↦ by simpa using congrFun h i),
    isArtinian_of_injective (e.symm.toLinearMap ∘ₗ LinearMap.single A (fun i ↦ X i) i)
      (e.symm.injective.comp fun x y h ↦ by simpa using congrFun h i)⟩

/-- **Krull–Schmidt uniqueness.** Two decompositions of a module of finite
length into finitely many indecomposable modules agree up to a bijection of
the index sets and isomorphisms of the summands. -/
theorem krullSchmidt {ι κ : Type} [Fintype ι] [Fintype κ] {M : Type u} [AddCommGroup M]
    [Module A M] [IsNoetherian A M] [IsArtinian A M] {X : ι → ModuleCat.{u} A}
    {Y : κ → ModuleCat.{u} A} (hX : ∀ i, IsIndecomposable A (X i))
    (hY : ∀ j, IsIndecomposable A (Y j)) (e : M ≃ₗ[A] Π i, X i) (f : M ≃ₗ[A] Π j, Y j) :
    ∃ σ : ι ≃ κ, ∀ i, Nonempty (X i ≃ₗ[A] Y (σ i)) := by
  classical
  refine exists_equiv_of_linearEquiv_pi _ rfl (fun i ↦ ⟨hX i, ?_⟩) hY (e.symm.trans f)
  obtain ⟨_, _⟩ := isNoetherian_isArtinian_of_linearEquiv_pi e i
  exact (hX i).isLocalRing_end

/-- Krull–Schmidt uniqueness: the numbers of summands agree. -/
theorem krullSchmidt_card {n m : ℕ} {M : Type u} [AddCommGroup M] [Module A M]
    [IsNoetherian A M] [IsArtinian A M] {X : Fin n → ModuleCat.{u} A}
    {Y : Fin m → ModuleCat.{u} A} (hX : ∀ i, IsIndecomposable A (X i))
    (hY : ∀ j, IsIndecomposable A (Y j)) (e : M ≃ₗ[A] Π i, X i) (f : M ≃ₗ[A] Π j, Y j) :
    n = m := by
  obtain ⟨σ, -⟩ := krullSchmidt hX hY e f
  simpa using Fintype.card_congr σ

/-! ### Existence -/

/-- Every submodule of an Artinian module is a finite product of
indecomposable modules. -/
theorem exists_linearEquiv_pi_submodule {M : Type u} [AddCommGroup M] [Module A M]
    [IsArtinian A M] (N : Submodule A M) :
    ∃ (ι : Type) (_ : Fintype ι) (X : ι → ModuleCat.{u} A),
      (∀ i, IsIndecomposable A (X i)) ∧ Nonempty (N ≃ₗ[A] Π i, X i) := by
  induction N using WellFoundedLT.induction with
  | _ N ih =>
  by_cases hsub : Subsingleton N
  · exact ⟨Empty, inferInstance, Empty.elim, fun i ↦ i.elim,
      ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
  by_cases hN : IsIndecomposable A N
  · exact ⟨Unit, inferInstance, fun _ ↦ ModuleCat.of A N, fun _ ↦ hN,
      ⟨(LinearEquiv.piUnique A fun _ : Unit ↦ ModuleCat.of A N).symm⟩⟩
  have hnt : Nontrivial N := not_subsingleton_iff_nontrivial.mp hsub
  obtain ⟨N₁, N₂, hc, h₁, h₂⟩ : ∃ N₁ N₂ : Submodule A N, IsCompl N₁ N₂ ∧ N₁ ≠ ⊥ ∧ N₂ ≠ ⊥ := by
    unfold IsIndecomposable at hN
    push Not at hN
    exact hN hnt
  -- each summand maps to a proper submodule of `N`
  have hlt : ∀ (N' N'' : Submodule A N), IsCompl N' N'' → N'' ≠ ⊥ →
      N'.map N.subtype < N := by
    intro N' N'' hc' h''
    refine lt_of_le_of_ne (Submodule.map_subtype_le N N') fun h ↦ h'' ?_
    have htop : N' = ⊤ := Submodule.map_injective_of_injective N.injective_subtype
      (h.trans (Submodule.map_subtype_top N).symm)
    exact top_disjoint.mp (htop ▸ hc'.disjoint)
  obtain ⟨ι₁, _, X₁, hX₁, ⟨e₁⟩⟩ := ih _ (hlt N₁ N₂ hc h₂)
  obtain ⟨ι₂, _, X₂, hX₂, ⟨e₂⟩⟩ := ih _ (hlt N₂ N₁ hc.symm h₁)
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim X₁ X₂, fun s ↦ ?_, ⟨?_⟩⟩
  · cases s with
    | inl i => exact hX₁ i
    | inr i => exact hX₂ i
  · exact (Submodule.prodEquivOfIsCompl N₁ N₂ hc).symm.trans
      (((Submodule.equivMapOfInjective _ N.injective_subtype N₁).trans e₁).prodCongr
        ((Submodule.equivMapOfInjective _ N.injective_subtype N₂).trans e₂) |>.trans
        (LinearEquiv.sumPiEquivProdPi A ι₁ ι₂
          fun s ↦ ((Sum.elim X₁ X₂ s : ModuleCat.{u} A) : Type u)).symm)

/-- **Krull–Schmidt existence.** An Artinian module (for instance a module of
finite length) is a finite product of indecomposable modules. -/
theorem exists_linearEquiv_pi (M : Type u) [AddCommGroup M] [Module A M] [IsArtinian A M] :
    ∃ (n : ℕ) (X : Fin n → ModuleCat.{u} A),
      (∀ i, IsIndecomposable A (X i)) ∧ Nonempty (M ≃ₗ[A] Π i, X i) := by
  obtain ⟨ι, _, X, hX, ⟨e⟩⟩ := exists_linearEquiv_pi_submodule (⊤ : Submodule A M)
  let σ := (Fintype.equivFin ι).symm
  exact ⟨Fintype.card ι, fun i ↦ X (σ i), fun i ↦ hX (σ i),
    ⟨((LinearEquiv.ofTop ⊤ rfl).symm.trans e).trans (LinearEquiv.piCongrLeft A _ σ).symm⟩⟩

/-! ### Biproducts in `ModuleCat` -/

section ModuleCat

/-- A module isomorphic to the biproduct `⨁ X` is linearly equivalent to `Π i, X i`. -/
def linearEquivPiOfIsoBiproduct {ι : Type} [Fintype ι] {M : ModuleCat.{u} A}
    {X : ι → ModuleCat.{u} A} (e : M ≅ ⨁ X) : M ≃ₗ[A] Π i, X i :=
  (e ≪≫ ModuleCat.biproductIsoPi X).toLinearEquiv

/-- Krull–Schmidt existence in `ModuleCat`, with biproducts. -/
theorem exists_iso_biproduct (M : ModuleCat.{u} A) [IsArtinian A M] :
    ∃ (n : ℕ) (X : Fin n → ModuleCat.{u} A),
      (∀ i, IsIndecomposable A (X i)) ∧ Nonempty (M ≅ ⨁ X) := by
  obtain ⟨n, X, hX, ⟨e⟩⟩ := exists_linearEquiv_pi (A := A) M
  exact ⟨n, X, hX, ⟨e.toModuleIso ≪≫ (ModuleCat.biproductIsoPi X).symm⟩⟩

/-- Exchange in `ModuleCat`: an indecomposable module of finite length that is
a direct summand of `M ≅ ⨁ X`, with every `X j` indecomposable, is isomorphic
to some `X j`. -/
theorem exists_iso_of_comp_eq_id {ι : Type} [Fintype ι] {P M : ModuleCat.{u} A}
    [IsNoetherian A P] [IsArtinian A P] (hP : IsIndecomposable A P)
    {X : ι → ModuleCat.{u} A} (hX : ∀ j, IsIndecomposable A (X j)) (e : M ≅ ⨁ X)
    (i : P ⟶ M) (p : M ⟶ P) (hpi : i ≫ p = 𝟙 P) : ∃ j, Nonempty (P ≅ X j) := by
  obtain ⟨j, ⟨f⟩⟩ := exists_nonempty_linearEquiv_of_comp_eq_id hP hX
    (linearEquivPiOfIsoBiproduct e) i.hom p.hom (congrArg ModuleCat.Hom.hom hpi)
  exact ⟨j, ⟨f.toModuleIso⟩⟩

/-- Krull–Schmidt uniqueness in `ModuleCat`, with biproducts. -/
theorem krullSchmidt_biproduct {ι κ : Type} [Fintype ι] [Fintype κ] {M : ModuleCat.{u} A}
    [IsNoetherian A M] [IsArtinian A M] {X : ι → ModuleCat.{u} A}
    {Y : κ → ModuleCat.{u} A} (hX : ∀ i, IsIndecomposable A (X i))
    (hY : ∀ j, IsIndecomposable A (Y j)) (e : M ≅ ⨁ X) (f : M ≅ ⨁ Y) :
    ∃ σ : ι ≃ κ, ∀ i, Nonempty (X i ≅ Y (σ i)) := by
  obtain ⟨σ, hσ⟩ := krullSchmidt hX hY (linearEquivPiOfIsoBiproduct e)
    (linearEquivPiOfIsoBiproduct f)
  exact ⟨σ, fun i ↦ (hσ i).map LinearEquiv.toModuleIso⟩

end ModuleCat

/-! ### Finite dimension through `RestrictScalars` -/

section RestrictScalars

variable (k : Type u) [Field k] [Algebra k A]

/-- Exchange for a finite-dimensional indecomposable `P`. -/
theorem exists_iso_of_comp_eq_id' {ι : Type} [Fintype ι] {P M : ModuleCat.{u} A}
    [Module.Finite k (RestrictScalars k A P)] (hP : IsIndecomposable A P)
    {X : ι → ModuleCat.{u} A} (hX : ∀ j, IsIndecomposable A (X j)) (e : M ≅ ⨁ X)
    (i : P ⟶ M) (p : M ⟶ P) (hpi : i ≫ p = 𝟙 P) : ∃ j, Nonempty (P ≅ X j) := by
  obtain ⟨_, _⟩ := isNoetherian_isArtinian_of_restrictScalars k (A := A) P
  exact exists_iso_of_comp_eq_id hP hX e i p hpi

/-- Krull–Schmidt existence for a finite-dimensional module. -/
theorem exists_iso_biproduct' (M : ModuleCat.{u} A) [Module.Finite k (RestrictScalars k A M)] :
    ∃ (n : ℕ) (X : Fin n → ModuleCat.{u} A),
      (∀ i, IsIndecomposable A (X i)) ∧ Nonempty (M ≅ ⨁ X) := by
  obtain ⟨_, _⟩ := isNoetherian_isArtinian_of_restrictScalars k (A := A) M
  exact exists_iso_biproduct M

/-- Krull–Schmidt uniqueness for a finite-dimensional module. -/
theorem krullSchmidt_biproduct' {ι κ : Type} [Fintype ι] [Fintype κ] {M : ModuleCat.{u} A}
    [Module.Finite k (RestrictScalars k A M)] {X : ι → ModuleCat.{u} A}
    {Y : κ → ModuleCat.{u} A} (hX : ∀ i, IsIndecomposable A (X i))
    (hY : ∀ j, IsIndecomposable A (Y j)) (e : M ≅ ⨁ X) (f : M ≅ ⨁ Y) :
    ∃ σ : ι ≃ κ, ∀ i, Nonempty (X i ≅ Y (σ i)) := by
  obtain ⟨_, _⟩ := isNoetherian_isArtinian_of_restrictScalars k (A := A) M
  exact krullSchmidt_biproduct hX hY e f

end RestrictScalars

end KrullSchmidt

end LargeIndecomposable
