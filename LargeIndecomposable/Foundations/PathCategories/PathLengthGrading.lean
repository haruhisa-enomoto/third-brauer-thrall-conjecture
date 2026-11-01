module

public import LargeIndecomposable.Foundations.PathCategories.LinearPathCategory
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

@[expose] public section

/-!
# The path-length grading of a free linear category

The Hom space of the free linear category has its path basis.  This file
groups that basis by path length, proves that the resulting submodules form an
internal direct sum, and proves that composition adds degrees.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable

universe u v w z

namespace GradedFinsupp

variable {k : Type u} [Field k]
variable {P : Type z}

/-- The submodule of finitely supported functions supported in one fiber of a
degree function. -/
def degreeComponent (degree : P → ℕ) (n : ℕ) : Submodule k (P →₀ k) :=
  Finsupp.supported k k {p | degree p = n}

theorem degreeComponent_iSupIndep (degree : P → ℕ) :
    iSupIndep (degreeComponent (k := k) degree) := by
  rw [iSupIndep_def]
  intro n
  have hd : Disjoint ({p : P | degree p = n} : Set P)
      {p : P | degree p ≠ n} :=
    Set.disjoint_left.2 fun _ hp hnp ↦ hnp hp
  refine (Finsupp.disjoint_supported_supported (M := k) (R := k) hd).mono
    le_rfl ?_
  refine iSup_le fun m ↦ iSup_le fun hmn ↦ ?_
  exact Finsupp.supported_mono fun p hp hpn ↦ hmn (hp.symm.trans hpn)

theorem iSup_degreeComponent_eq_top (degree : P → ℕ) :
    ⨆ n, degreeComponent (k := k) degree n = ⊤ := by
  change (⨆ n, Finsupp.supported k k {p : P | degree p = n}) = ⊤
  rw [← Finsupp.supported_iUnion]
  have h : (⋃ n, {p : P | degree p = n}) = Set.univ := by
    ext p
    simp
  rw [h, Finsupp.supported_univ]

/-- Finitely supported functions decompose internally according to any
natural-number-valued degree on their basis indices. -/
theorem degreeComponent_isInternal (degree : P → ℕ) :
    DirectSum.IsInternal (degreeComponent (k := k) degree) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (degreeComponent_iSupIndep degree) (iSup_degreeComponent_eq_top degree)

end GradedFinsupp

namespace CategoricalGrading

variable {k : Type u} [Field k]
variable {C : Type z} [Category.{w} C] [Preadditive C] [Linear k C]

/-- Binary degree compatibility implies the corresponding three-factor
compatibility.  This is kept generic so no concrete category implementation
is unfolded while checking the associativity step. -/
theorem comp_comp_mem
    (A : ∀ X Y : C, ℕ → Submodule k (X ⟶ Y))
    (hcomp : ∀ {W X Y : C} {i j : ℕ} {a : W ⟶ X} {b : X ⟶ Y},
      a ∈ A W X i → b ∈ A X Y j → a ≫ b ∈ A W Y (i + j))
    {W X Y Z : C} {i j l : ℕ}
    {a : W ⟶ X} {b : X ⟶ Y} {c : Y ⟶ Z}
    (ha : a ∈ A W X i) (hb : b ∈ A X Y j) (hc : c ∈ A Y Z l) :
    a ≫ b ≫ c ∈ A W Z (i + j + l) := by
  simpa only [Category.assoc] using
    hcomp (W := W) (X := Y) (Y := Z) (i := i + j) (j := l)
      (a := a ≫ b) (b := c)
      (hcomp (W := W) (X := X) (Y := Y) (i := i) (j := j)
        (a := a) (b := b) ha hb) hc

end CategoricalGrading

namespace LinearPathCategory

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]

/-- The degree-`n` submodule of a Hom space in the free linear path category. -/
def lengthComponent (x y : Category k Q) (n : ℕ) : Submodule k (x ⟶ y) :=
  (GradedFinsupp.degreeComponent
    (fun p : Quiver.Path (vertex y) (vertex x) ↦ p.length) n).comap
      (homPathLinearEquiv x y).toLinearMap

@[simp]
theorem mem_lengthComponent_iff (x y : Category k Q) (n : ℕ) (f : x ⟶ y) :
    f ∈ lengthComponent x y n ↔
      ((homPathLinearEquiv x y f).support :
        Set (Quiver.Path (vertex y) (vertex x))) ⊆
          {p : Quiver.Path (vertex y) (vertex x) | p.length = n} :=
  Iff.rfl

@[simp]
theorem pathHom_mem_lengthComponent_iff {x y : Category k Q}
    (p : Quiver.Path (vertex y) (vertex x)) (n : ℕ) :
    pathHom p ∈ lengthComponent x y n ↔ p.length = n := by
  rw [mem_lengthComponent_iff, homPathLinearEquiv_pathHom]
  simp

theorem lengthComponent_eq_map (x y : Category k Q) (n : ℕ) :
    lengthComponent x y n =
      (GradedFinsupp.degreeComponent
        (fun p : Quiver.Path (vertex y) (vertex x) ↦ p.length) n).map
          (homPathLinearEquiv x y).symm.toLinearMap :=
  Submodule.comap_equiv_eq_map_symm (homPathLinearEquiv x y) _

/-- The path-length pieces form an internal direct-sum decomposition of every
Hom space. -/
theorem lengthComponent_isInternal (x y : Category k Q) :
    DirectSum.IsInternal (lengthComponent x y) := by
  let e := homPathLinearEquiv x y
  let A := GradedFinsupp.degreeComponent
    (k := k) (fun p : Quiver.Path (vertex y) (vertex x) ↦ p.length)
  have hA : DirectSum.IsInternal A :=
    GradedFinsupp.degreeComponent_isInternal _
  have hEq : lengthComponent x y =
      fun n ↦ (A n).map e.symm.toLinearMap := by
    funext n
    exact lengthComponent_eq_map x y n
  rw [hEq]
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · exact LinearMap.iSupIndep_map e.symm.toLinearMap e.symm.injective
      hA.submodule_iSupIndep
  · rw [← Submodule.map_iSup, hA.submodule_iSup_eq_top,
      Submodule.map_top]
    exact LinearMap.range_eq_top.2 e.symm.surjective

/-- The path-basis elements of one fixed length. -/
def lengthBasisSet (x y : Category k Q) (n : ℕ) : Set (x ⟶ y) :=
  pathHom '' {p : Quiver.Path (vertex y) (vertex x) | p.length = n}

theorem lengthComponent_eq_span (x y : Category k Q) (n : ℕ) :
    lengthComponent x y n = Submodule.span k (lengthBasisSet x y n) := by
  rw [lengthComponent_eq_map, GradedFinsupp.degreeComponent,
    Finsupp.supported_eq_span_single, Submodule.map_span]
  congr 1
  ext f
  simp only [lengthBasisSet, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨Finsupp.single p 1, ⟨p, hp, rfl⟩, rfl⟩

/-- Composition in the free linear path category adds path length. -/
theorem comp_mem_lengthComponent {x y z : Category k Q} {i j : ℕ}
    {f : x ⟶ y} {g : y ⟶ z}
    (hf : f ∈ lengthComponent x y i)
    (hg : g ∈ lengthComponent y z j) :
    f ≫ g ∈ lengthComponent x z (i + j) := by
  rw [lengthComponent_eq_span] at hf hg ⊢
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨p, hp, rfl⟩
      induction hg using Submodule.span_induction with
      | mem g hg =>
          rcases hg with ⟨q, hq, rfl⟩
          apply Submodule.subset_span
          refine ⟨q.comp p, ?_, (pathHom_comp p q).symm⟩
          change p.length = i at hp
          change q.length = j at hq
          simp [Quiver.Path.length_comp, hp, hq, Nat.add_comm]
      | zero => simp
      | add g h _ _ hg hh => simpa using Submodule.add_mem _ hg hh
      | smul c g _ hg => simpa using Submodule.smul_mem _ c hg
  | zero => simp
  | add f h _ _ hf hh => simpa using Submodule.add_mem _ hf hh
  | smul c f _ hf => simpa using Submodule.smul_mem _ c hf

@[simp]
theorem id_mem_lengthComponent_zero (x : Category k Q) :
    𝟙 x ∈ lengthComponent x x 0 := by
  rw [← pathHom_nil x, pathHom_mem_lengthComponent_iff]
  exact Quiver.Path.length_nil

/-- Between distinct vertices there is no degree-zero morphism. -/
theorem lengthComponent_zero_eq_bot_of_vertex_ne {x y : Category k Q}
    (hxy : vertex y ≠ vertex x) :
    lengthComponent x y 0 = ⊥ := by
  rw [lengthComponent_eq_span, Submodule.span_eq_bot]
  intro f hf
  rcases hf with ⟨p, hp, rfl⟩
  exact False.elim (hxy (Quiver.Path.eq_of_length_zero p hp))

/-- At one vertex the degree-zero endomorphisms are exactly the scalar
multiples of the identity. -/
theorem lengthComponent_zero_self (x : Category k Q) :
    lengthComponent x x 0 = k ∙ (𝟙 x) := by
  rw [lengthComponent_eq_span]
  apply congrArg (Submodule.span k)
  ext f
  simp only [lengthBasisSet, Set.mem_image, Set.mem_setOf_eq,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [Quiver.Path.eq_nil_of_length_zero p hp, pathHom_nil]
  · rintro rfl
    exact ⟨Quiver.Path.nil, Quiver.Path.length_nil, pathHom_nil x⟩

/-- The submodule spanned by nontrivial paths.  Unlike a single homogeneous
length component, this collects all strictly positive path lengths. -/
def positivePathSubmodule (x y : Category k Q) : Submodule k (x ⟶ y) :=
  (Finsupp.supported k k
    {p : Quiver.Path (vertex y) (vertex x) | p.length ≠ 0}).comap
      (homPathLinearEquiv x y).toLinearMap

@[simp]
theorem mem_positivePathSubmodule_iff (x y : Category k Q) (f : x ⟶ y) :
    f ∈ positivePathSubmodule x y ↔
      ((homPathLinearEquiv x y f).support :
        Set (Quiver.Path (vertex y) (vertex x))) ⊆
          {p : Quiver.Path (vertex y) (vertex x) | p.length ≠ 0} :=
  Iff.rfl

/-- The positive-path submodule is the span of its path-basis elements. -/
theorem positivePathSubmodule_eq_span (x y : Category k Q) :
    positivePathSubmodule x y =
      Submodule.span k
        (pathHom ''
          {p : Quiver.Path (vertex y) (vertex x) | p.length ≠ 0}) := by
  rw [positivePathSubmodule, Finsupp.supported_eq_span_single,
    Submodule.comap_equiv_eq_map_symm, Submodule.map_span]
  congr 1
  ext f
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, by simp [pathHom]⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨Finsupp.single p 1, ⟨p, hp, rfl⟩, by simp [pathHom]⟩

/-- Between distinct vertices every free linear morphism is a combination of
positive-length paths. -/
theorem positivePathSubmodule_eq_top_of_vertex_ne {x y : Category k Q}
    (hxy : vertex y ≠ vertex x) :
    positivePathSubmodule x y = ⊤ := by
  rw [eq_top_iff]
  intro f hf
  rw [mem_positivePathSubmodule_iff]
  intro p hp hzero
  exact hxy (Quiver.Path.eq_of_length_zero p hzero)

/-- The coefficient of the trivial path in a free linear endomorphism. -/
def nilPathCoefficient (x : Category k Q) : (x ⟶ x) →ₗ[k] k :=
  (Finsupp.lapply Quiver.Path.nil).comp (homPathLinearEquiv x x).toLinearMap

@[simp]
theorem nilPathCoefficient_id (x : Category k Q) :
    nilPathCoefficient x (𝟙 x) = 1 := by
  simp [nilPathCoefficient]

/-- For endomorphisms, having no trivial-path coefficient is exactly being a
linear combination of positive-length paths. -/
theorem mem_positivePathSubmodule_self_iff (x : Category k Q) (f : x ⟶ x) :
    f ∈ positivePathSubmodule x x ↔ nilPathCoefficient x f = 0 := by
  rw [mem_positivePathSubmodule_iff, nilPathCoefficient,
    LinearMap.comp_apply, Finsupp.lapply_apply]
  constructor
  · intro hf
    rw [← Finsupp.notMem_support_iff]
    exact fun hnil ↦ (hf hnil) Quiver.Path.length_nil
  · intro hnil p hp hpzero
    have hpnil : p = Quiver.Path.nil :=
      Quiver.Path.eq_nil_of_length_zero p hpzero
    subst p
    exact (Finsupp.mem_support_iff.mp hp) hnil

/-- A positive-length homogeneous endomorphism has zero trivial-path
coefficient. -/
theorem nilPathCoefficient_eq_zero_of_mem_lengthComponent
    (x : Category k Q) {n : ℕ} (hn : n ≠ 0) {f : x ⟶ x}
    (hf : f ∈ lengthComponent x x n) :
    nilPathCoefficient x f = 0 := by
  rw [nilPathCoefficient, LinearMap.comp_apply, Finsupp.lapply_apply,
    ← Finsupp.notMem_support_iff]
  intro hnil
  have hlength := (mem_lengthComponent_iff x x n f).mp hf hnil
  exact hn (by simpa using hlength.symm)

end LinearPathCategory

end LargeIndecomposable
