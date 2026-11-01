module

public import LargeIndecomposable.KroneckerModules.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.LinearAlgebra.DFinsupp

/-!
# Colimits in `D`

Lemma 2.2(2): the subcategory `D` of Kronecker modules is closed under
filtered colimits and arbitrary direct sums in the category of all Kronecker
modules. Consequently `D` has these colimits, the inclusion `D ⥤ Kron k`
preserves them, and `Statement.ClosedUnderColimits` holds.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair WalkingParallelPairHom

universe w u

variable {k : Type u} [Field k]

/-! ### Elementwise facts about colimits of vector spaces -/

/-- The leg of a cocone of modules, as a linear map into the cocone point. -/
abbrev legHom {J : Type w} [Category J] {G : J ⥤ ModuleCat.{u} k} (d : Cocone G) (j : J) :
    G.obj j →ₗ[k] d.pt :=
  (d.ι.app j).hom

/-- The images of the legs of a colimit cocone of modules span the cocone
point. -/
lemma iSup_range_ι_eq_top {J : Type w} [Category J] {G : J ⥤ ModuleCat.{u} k}
    {d : Cocone G} (hd : IsColimit d) :
    ⨆ j : J, LinearMap.range (legHom d j) = ⊤ := by
  set N := ⨆ j : J, LinearMap.range (legHom d j)
  have h : ModuleCat.ofHom N.mkQ = 0 := hd.hom_ext fun j ↦ by
    ext x
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      ModuleCat.hom_ofHom, comp_zero, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact le_iSup (fun j ↦ LinearMap.range (legHom d j)) j ⟨x, rfl⟩
  have h' := congrArg (fun f ↦ LinearMap.ker f.hom) h
  simpa using h'

/-- In a filtered category, two conditions on morphisms out of `i` that are
stable under postcomposition and each satisfiable are satisfiable together. -/
lemma IsFiltered.exists_hom_of_stable {J : Type w} [Category J] [IsFiltered J] {i : J}
    (P Q : ∀ {j : J}, (i ⟶ j) → Prop)
    (hP : ∀ {j j' : J} (f : i ⟶ j) (g : j ⟶ j'), P f → P (f ≫ g))
    (hQ : ∀ {j j' : J} (f : i ⟶ j) (g : j ⟶ j'), Q f → Q (f ≫ g))
    (h₁ : ∃ (j : J) (f : i ⟶ j), P f) (h₂ : ∃ (j : J) (f : i ⟶ j), Q f) :
    ∃ (j : J) (f : i ⟶ j), P f ∧ Q f := by
  obtain ⟨j₁, f₁, hf₁⟩ := h₁
  obtain ⟨j₂, f₂, hf₂⟩ := h₂
  let e := IsFiltered.coeqHom (f₁ ≫ IsFiltered.leftToMax j₁ j₂) (f₂ ≫ IsFiltered.rightToMax j₁ j₂)
  refine ⟨_, f₁ ≫ IsFiltered.leftToMax j₁ j₂ ≫ e, hP _ _ hf₁, ?_⟩
  have := IsFiltered.coeq_condition (f₁ ≫ IsFiltered.leftToMax j₁ j₂)
    (f₂ ≫ IsFiltered.rightToMax j₁ j₂)
  simp only [Category.assoc] at this
  rw [this]
  exact hQ _ _ hf₂

/-- An element of a stage of a filtered diagram of modules that vanishes in a
colimit already vanishes at a later stage. -/
lemma exists_map_eq_zero_of_isColimit {R : Type u} [Ring R] {J : Type u} [SmallCategory J]
    [IsFiltered J] {G : J ⥤ ModuleCat.{u} R} {d : Cocone G} (hd : IsColimit d) {j : J}
    (x : G.obj j) (hx : (d.ι.app j).hom x = 0) :
    ∃ (j' : J) (f : j ⟶ j'), (G.map f).hom x = 0 := by
  obtain ⟨j', f, g, e⟩ := (Concrete.isColimit_rep_eq_iff_exists _ hd (i := j) (j := j) x 0).1
    (by simpa using hx)
  exact ⟨j', f, by simpa using e⟩

/-! ### Filtered colimits -/

/-- `D` is closed under filtered colimits (Lemma 2.2(2)). -/
lemma inD_of_isColimit_of_isFiltered {J : Type u} [SmallCategory J] [IsFiltered J]
    {K : J ⥤ Kron k} {c : Cocone K} (hc : IsColimit c) (hK : ∀ j, InD (K.obj j)) :
    InD c.pt := by
  have h0 := isColimitOfPreserves ((evaluation _ _).obj zero) hc
  have h1 := isColimitOfPreserves ((evaluation _ _).obj one) hc
  rw [inD_iff]
  intro v ha hb
  obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep _ h0 v
  have ha' : ((c.ι.app j).app one).hom ((K.obj j).a.hom y) = 0 := by
    rw [Kron.a_apply]; exact ha
  have hb' : ((c.ι.app j).app one).hom ((K.obj j).b.hom y) = 0 := by
    rw [Kron.b_apply]; exact hb
  obtain ⟨m, f, hfa, hfb⟩ := IsFiltered.exists_hom_of_stable
    (fun f ↦ ((K.map f).app one).hom ((K.obj j).a.hom y) = 0)
    (fun f ↦ ((K.map f).app one).hom ((K.obj j).b.hom y) = 0)
    (fun f g h ↦ by simp [h]) (fun f g h ↦ by simp [h])
    (exists_map_eq_zero_of_isColimit h1 _ ha') (exists_map_eq_zero_of_isColimit h1 _ hb')
  have hy : ((K.map f).app zero).hom y = 0 := by
    refine (inD_iff _).1 (hK m) _ ?_ ?_
    · rw [← Kron.a_apply]; exact hfa
    · rw [← Kron.b_apply]; exact hfb
  have := congrArg (fun g ↦ (g.app zero).hom y) (c.w f)
  change _ = ((c.ι.app j).app zero).hom y at this
  change ((c.ι.app j).app zero).hom y = 0
  rw [← this, NatTrans.comp_app, ModuleCat.comp_apply, hy, map_zero]

/-! ### Direct sums -/

section Coproducts

variable {ι : Type w} {K : Discrete ι ⥤ Kron k} {c : Cocone K}

open scoped Classical in
/-- The projection from a direct sum of Kronecker modules onto a summand. -/
def coprodProj (hc : IsColimit c) (i : Discrete ι) : c.pt ⟶ K.obj i :=
  hc.desc ⟨K.obj i, Discrete.natTrans fun j ↦ if h : j = i then eqToHom (by rw [h]; rfl) else 0⟩

lemma ι_coprodProj_self (hc : IsColimit c) (i : Discrete ι) :
    c.ι.app i ≫ coprodProj hc i = 𝟙 _ := by
  classical
  refine (hc.fac _ i).trans ?_
  simp

lemma ι_coprodProj_of_ne (hc : IsColimit c) {i j : Discrete ι} (h : j ≠ i) :
    c.ι.app j ≫ coprodProj hc i = 0 := by
  classical
  refine (hc.fac _ j).trans ?_
  simp [h]

/-- `D` is closed under direct sums (Lemma 2.2(2)). -/
lemma inD_of_isColimit_of_discrete [HasColimitsOfShape (Discrete ι) (ModuleCat.{u} k)]
    (hc : IsColimit c) (hK : ∀ j, InD (K.obj j)) : InD c.pt := by
  classical
  have h0 := isColimitOfPreserves ((evaluation _ _).obj zero) hc
  rw [inD_iff]
  intro x ha hb
  have hP : ∀ i, ((coprodProj hc i).app zero).hom x = 0 := fun i ↦
    (inD_iff _).1 (hK i) _ (by rw [← Kron.a_apply, ha, map_zero])
      (by rw [← Kron.b_apply, hb, map_zero])
  have hP₁ : ∀ i (y : (K.obj i).V),
      ((coprodProj hc i).app zero).hom (((c.ι.app i).app zero).hom y) = y := fun i y ↦ by
    rw [← ModuleCat.comp_apply, ← NatTrans.comp_app, ι_coprodProj_self]; rfl
  have hP₀ : ∀ i j (y : (K.obj j).V), j ≠ i →
      ((coprodProj hc i).app zero).hom (((c.ι.app j).app zero).hom y) = 0 := fun i j y h ↦ by
    rw [← ModuleCat.comp_apply, ← NatTrans.comp_app, ι_coprodProj_of_ne hc h]; rfl
  have hx : x ∈ ⨆ j, LinearMap.range (legHom (((evaluation _ _).obj zero).mapCocone c) j) := by
    rw [iSup_range_ι_eq_top h0]; trivial
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ x).1 hx
  suffices hf0 : f = 0 by simp [hf0]
  ext i
  obtain ⟨y, hy⟩ := hf i
  have := hP i
  rw [Finsupp.sum, map_sum, Finset.sum_eq_single i] at this
  · rw [← hy] at this ⊢
    change ((coprodProj hc i).app zero).hom (((c.ι.app i).app zero).hom y) = 0 at this
    rw [hP₁] at this
    simp [this]
  · intro j _ hj
    obtain ⟨y', hy'⟩ := hf j
    rw [← hy']
    exact hP₀ i j y' hj
  · intro hi
    rw [Finsupp.notMem_support_iff.1 hi, map_zero]

end Coproducts

/-! ### Colimits in `D` -/

instance isClosedUnderColimitsOfShape_inD_of_isFiltered (J : Type u) [SmallCategory J]
    [IsFiltered J] : (InD (k := k)).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := fun _ ⟨h⟩ ↦ inD_of_isColimit_of_isFiltered h.isColimit h.prop_diag_obj

instance isClosedUnderColimitsOfShape_inD_discrete (ι : Type w)
    [HasColimitsOfShape (Discrete ι) (ModuleCat.{u} k)] :
    (InD (k := k)).IsClosedUnderColimitsOfShape (Discrete ι) where
  colimitsOfShape_le := fun _ ⟨h⟩ ↦ inD_of_isColimit_of_discrete h.isColimit h.prop_diag_obj

instance : HasFilteredColimitsOfSize.{u, u} (D k) where
  HasColimitsOfShape _ _ _ := inferInstance

instance (ι : Type u) : HasColimitsOfShape (Discrete ι) (D k) := inferInstance

instance : HasFiniteCoproducts (D k) where
  out _ := inferInstance

/-- The inclusion `D ⥤ Kron k` preserves filtered colimits. -/
instance preservesColimitsOfShape_ι_of_isFiltered (J : Type u) [SmallCategory J]
    [IsFiltered J] : PreservesColimitsOfShape J (InD (k := k)).ι := inferInstance

/-- The inclusion `D ⥤ Kron k` preserves direct sums. -/
instance preservesColimitsOfShape_ι_discrete (ι : Type u) :
    PreservesColimitsOfShape (Discrete ι) (InD (k := k)).ι := inferInstance

/-- `D` has filtered colimits and arbitrary direct sums (Lemma 2.2(2)). -/
theorem closedUnderColimits : Statement.ClosedUnderColimits.{u} :=
  fun _ _ ↦ ⟨inferInstance, fun _ ↦ inferInstance⟩

end LargeIndecomposable
