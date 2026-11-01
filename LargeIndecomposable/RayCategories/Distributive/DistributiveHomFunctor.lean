module

public import LargeIndecomposable.RayCategories.Distributive.DistributiveHomStructure
public import Mathlib.CategoryTheory.Linear.LinearFunctor

@[expose] public section

/-!
# Descent of distributive Hom structure along full quotient functors

A full additive linear functor which is surjective on objects transports the
two local properties packaged by `HasBGRSDistributiveHomStructure`: pull back
Hom subbimodules to compare them, and lift a morphism and its endpoint
endomorphisms to transport transit or cotransit.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.HasBGRSDistributiveHomStructure

universe u v w x y

variable {k : Type u} [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
variable {D : Type x} [Category.{y} D] [Preadditive D] [Linear k D]

/-- Distributive Hom structure descends along a full additive linear functor
whose object map is surjective. -/
theorem of_full_surjective
    (F : C ⥤ D) [F.Full] [F.Additive] [F.Linear k]
    (hobj : Function.Surjective F.obj)
    [HasBGRSDistributiveHomStructure k C] :
    HasBGRSDistributiveHomStructure k D where
  homSubbimodule_comparable := by
    intro X Y S T hS hT
    obtain ⟨X₀, rfl⟩ := hobj X
    obtain ⟨Y₀, rfl⟩ := hobj Y
    let mapHom : (X₀ ⟶ Y₀) →ₗ[k] (F.obj X₀ ⟶ F.obj Y₀) :=
      F.mapLinearMap k
    let S₀ : Submodule k (X₀ ⟶ Y₀) := S.comap mapHom
    let T₀ : Submodule k (X₀ ⟶ Y₀) := T.comap mapHom
    have hS₀ : IsHomSubbimodule S₀ := by
      constructor
      · intro a f hf
        change F.map (a.asHom ≫ f) ∈ S
        rw [F.map_comp]
        exact hS.1 (End.of (F.map a.asHom)) hf
      · intro b f hf
        change F.map (f ≫ b.asHom) ∈ S
        rw [F.map_comp]
        exact hS.2 (End.of (F.map b.asHom)) hf
    have hT₀ : IsHomSubbimodule T₀ := by
      constructor
      · intro a f hf
        change F.map (a.asHom ≫ f) ∈ T
        rw [F.map_comp]
        exact hT.1 (End.of (F.map a.asHom)) hf
      · intro b f hf
        change F.map (f ≫ b.asHom) ∈ T
        rw [F.map_comp]
        exact hT.2 (End.of (F.map b.asHom)) hf
    rcases HasBGRSDistributiveHomStructure.homSubbimodule_comparable
        S₀ T₀ hS₀ hT₀ with hST | hTS
    · left
      intro g hg
      obtain ⟨f, hf⟩ := F.map_surjective g
      have hfS : f ∈ S₀ := by
        change F.map f ∈ S
        simpa only [hf] using hg
      have hfT := hST hfS
      change F.map f ∈ T at hfT
      simpa only [hf] using hfT
    · right
      intro g hg
      obtain ⟨f, hf⟩ := F.map_surjective g
      have hfT : f ∈ T₀ := by
        change F.map f ∈ T
        simpa only [hf] using hg
      have hfS := hTS hfT
      change F.map f ∈ S at hfS
      simpa only [hf] using hfS
  transit_or_cotransit := by
    intro X Y f
    obtain ⟨X₀, rfl⟩ := hobj X
    obtain ⟨Y₀, rfl⟩ := hobj Y
    obtain ⟨f₀, hf₀⟩ := F.map_surjective f
    rcases HasBGRSDistributiveHomStructure.transit_or_cotransit
        (k := k) (C := C) f₀ with
      htransit | hcotransit
    · left
      intro a
      obtain ⟨a₀, ha₀⟩ := F.map_surjective a.asHom
      obtain ⟨b₀, hb₀⟩ := htransit (End.of a₀)
      refine ⟨End.of (F.map b₀.asHom), ?_⟩
      change a.asHom ≫ f = f ≫ F.map b₀.asHom
      rw [← hf₀, ← ha₀, ← F.map_comp, ← F.map_comp, hb₀]
    · right
      intro b
      obtain ⟨b₀, hb₀⟩ := F.map_surjective b.asHom
      obtain ⟨a₀, ha₀⟩ := hcotransit (End.of b₀)
      refine ⟨End.of (F.map a₀.asHom), ?_⟩
      change f ≫ b.asHom = F.map a₀.asHom ≫ f
      rw [← hf₀, ← hb₀, ← F.map_comp, ← F.map_comp, ha₀]

end LargeIndecomposable.HasBGRSDistributiveHomStructure

namespace LargeIndecomposable

universe u v w x y

variable {k : Type u} [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
variable {D : Type x} [Category.{y} D] [Preadditive D] [Linear k D]

/-- A linear functor carries a principal two-sided endomorphism span into the
span of the mapped generator. -/
theorem linearFunctor_map_mem_twoSidedEndomorphismSpan
    (F : C ⥤ D) [F.Additive] [F.Linear k]
    {X Y : C} {a generator : X ⟶ Y}
    (ha : a ∈ twoSidedEndomorphismSpan k generator) :
    F.map a ∈ twoSidedEndomorphismSpan k (F.map generator) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
      rcases ha with ⟨c, d, rfl⟩
      apply Submodule.subset_span
      refine ⟨End.of (F.map c.asHom), End.of (F.map d.asHom), ?_⟩
      simp only [Functor.map_comp]
  | zero => simp
  | add a b _ _ ha hb =>
      rw [F.map_add]
      exact (twoSidedEndomorphismSpan k
        (F.map generator)).add_mem ha hb
  | smul c a _ ha =>
      rw [F.map_smul]
      exact (twoSidedEndomorphismSpan k
        (F.map generator)).smul_mem c ha

/-- Conjugating both endpoints by isomorphisms carries a principal
endomorphism span into the span of the conjugated generator. -/
theorem homCongr_mem_twoSidedEndomorphismSpan
    {X Y X' Y' : C} (eX : X ≅ X') (eY : Y ≅ Y')
    {a generator : X ⟶ Y}
    (ha : a ∈ twoSidedEndomorphismSpan k generator) :
    CategoryTheory.Linear.homCongr k eX eY a ∈
      twoSidedEndomorphismSpan k
        (CategoryTheory.Linear.homCongr k eX eY generator) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
      rcases ha with ⟨c, d, rfl⟩
      apply Submodule.subset_span
      refine ⟨End.of (eX.inv ≫ c.asHom ≫ eX.hom),
        End.of (eY.inv ≫ d.asHom ≫ eY.hom), ?_⟩
      simp only [CategoryTheory.Linear.homCongr_apply]
      simp [Category.assoc]
  | zero => simp
  | add a b _ _ ha hb =>
      rw [map_add]
      exact (twoSidedEndomorphismSpan k
        (CategoryTheory.Linear.homCongr k eX eY generator)).add_mem ha hb
  | smul c a _ ha =>
      rw [map_smul]
      exact (twoSidedEndomorphismSpan k
        (CategoryTheory.Linear.homCongr k eX eY generator)).smul_mem c ha

/-- Generating the complete Hom space is invariant under isomorphisms of the
source and target objects. -/
theorem homCongr_span_eq_top_iff
    {X Y X' Y' : C} (eX : X ≅ X') (eY : Y ≅ Y')
    (f : X ⟶ Y) :
    twoSidedEndomorphismSpan k
        (CategoryTheory.Linear.homCongr k eX eY f) = ⊤ ↔
      twoSidedEndomorphismSpan k f = ⊤ := by
  constructor
  · intro hmap
    apply top_unique
    intro g _
    let g' := CategoryTheory.Linear.homCongr k eX eY g
    have hg' : g' ∈ twoSidedEndomorphismSpan k
        (CategoryTheory.Linear.homCongr k eX eY f) := by
      rw [hmap]
      exact Submodule.mem_top
    have hback := homCongr_mem_twoSidedEndomorphismSpan
      (k := k) eX.symm eY.symm hg'
    simpa [g', CategoryTheory.Linear.homCongr_apply,
      Category.assoc] using hback
  · intro hf
    apply top_unique
    intro g _
    let g' := (CategoryTheory.Linear.homCongr k eX eY).symm g
    have hg' : g' ∈ twoSidedEndomorphismSpan k f := by
      rw [hf]
      exact Submodule.mem_top
    have hmap := homCongr_mem_twoSidedEndomorphismSpan
      (k := k) eX eY hg'
    simpa [g', CategoryTheory.Linear.homCongr_apply,
      CategoryTheory.Linear.homCongr_symm_apply,
      Category.assoc] using hmap

/-- A full linear functor preserves a principal Hom generator. -/
theorem fullLinearFunctor_map_span_eq_top
    (F : C ⥤ D) [F.Full] [F.Additive] [F.Linear k]
    {X Y : C} (f : X ⟶ Y)
    (hf : twoSidedEndomorphismSpan k f = ⊤) :
    twoSidedEndomorphismSpan k (F.map f) = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨g₀, rfl⟩ := F.map_surjective g
  apply linearFunctor_map_mem_twoSidedEndomorphismSpan F
  rw [hf]
  exact Submodule.mem_top

/-- A fully faithful linear functor reflects membership in a principal
two-sided endomorphism span. -/
theorem fullyFaithfulLinearFunctor_mem_span_of_map_mem
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.Additive] [F.Linear k]
    {X Y : C} {f g : X ⟶ Y}
    (hg : F.map g ∈ twoSidedEndomorphismSpan k (F.map f)) :
    g ∈ twoSidedEndomorphismSpan k f := by
  let mapHom : (X ⟶ Y) →ₗ[k] (F.obj X ⟶ F.obj Y) :=
    F.mapLinearMap k
  have hle : twoSidedEndomorphismSpan k (F.map f) ≤
      (twoSidedEndomorphismSpan k f).map mapHom := by
    apply Submodule.span_le.2
    intro h hh
    rcases hh with ⟨a, b, rfl⟩
    obtain ⟨a₀, ha₀⟩ := F.map_surjective a.asHom
    obtain ⟨b₀, hb₀⟩ := F.map_surjective b.asHom
    let h₀ : X ⟶ Y :=
      ((End.of a₀).asHom ≫ f) ≫ (End.of b₀).asHom
    apply Submodule.mem_map.2
    refine ⟨h₀, Submodule.subset_span ⟨End.of a₀, End.of b₀, rfl⟩, ?_⟩
    dsimp only [mapHom, h₀]
    change F.map (((End.of a₀).asHom ≫ f) ≫ (End.of b₀).asHom) =
      (a.asHom ≫ F.map f) ≫ b.asHom
    rw [F.map_comp, F.map_comp, ha₀, hb₀]
  obtain ⟨h, hh, hmap⟩ := Submodule.mem_map.1 (hle hg)
  have heq : h = g := F.map_injective hmap
  simpa only [heq] using hh

/-- A fully faithful linear functor reflects and preserves the statement that
a morphism generates its complete Hom space. -/
theorem fullyFaithfulLinearFunctor_map_span_eq_top_iff
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.Additive] [F.Linear k]
    {X Y : C} (f : X ⟶ Y) :
    twoSidedEndomorphismSpan k (F.map f) = ⊤ ↔
      twoSidedEndomorphismSpan k f = ⊤ := by
  constructor
  · intro hmap
    apply top_unique
    intro g _
    apply fullyFaithfulLinearFunctor_mem_span_of_map_mem F
    rw [hmap]
    exact Submodule.mem_top
  · exact fullLinearFunctor_map_span_eq_top F f

/-- Transit is preserved when both endpoints are replaced by isomorphic
objects. -/
theorem homCongr_allowsTransit
    {X Y X' Y' : C} (eX : X ≅ X') (eY : Y ≅ Y')
    (f : X ⟶ Y) (hf : AllowsTransit f) :
    AllowsTransit (CategoryTheory.Linear.homCongr k eX eY f) := by
  intro a'
  let a : End X := End.of (eX.hom ≫ a'.asHom ≫ eX.inv)
  obtain ⟨b, hb⟩ := hf a
  let b' : End Y' := End.of (eY.inv ≫ b.asHom ≫ eY.hom)
  refine ⟨b', ?_⟩
  calc
    a'.asHom ≫ CategoryTheory.Linear.homCongr k eX eY f =
        eX.inv ≫ (a.asHom ≫ f) ≫ eY.hom := by
      simp [CategoryTheory.Linear.homCongr_apply, a, Category.assoc]
    _ = eX.inv ≫ (f ≫ b.asHom) ≫ eY.hom := by rw [hb]
    _ = CategoryTheory.Linear.homCongr k eX eY f ≫ b'.asHom := by
      simp [CategoryTheory.Linear.homCongr_apply, b', Category.assoc]

/-- Cotransit is preserved when both endpoints are replaced by isomorphic
objects. -/
theorem homCongr_allowsCotransit
    {X Y X' Y' : C} (eX : X ≅ X') (eY : Y ≅ Y')
    (f : X ⟶ Y) (hf : AllowsCotransit f) :
    AllowsCotransit (CategoryTheory.Linear.homCongr k eX eY f) := by
  intro b'
  let b : End Y := End.of (eY.hom ≫ b'.asHom ≫ eY.inv)
  obtain ⟨a, ha⟩ := hf b
  let a' : End X' := End.of (eX.inv ≫ a.asHom ≫ eX.hom)
  refine ⟨a', ?_⟩
  calc
    CategoryTheory.Linear.homCongr k eX eY f ≫ b'.asHom =
        eX.inv ≫ (f ≫ b.asHom) ≫ eY.hom := by
      simp [CategoryTheory.Linear.homCongr_apply, b, Category.assoc]
    _ = eX.inv ≫ (a.asHom ≫ f) ≫ eY.hom := by rw [ha]
    _ = a'.asHom ≫ CategoryTheory.Linear.homCongr k eX eY f := by
      simp [CategoryTheory.Linear.homCongr_apply, a', Category.assoc]

/-- Transit is invariant under simultaneous isomorphism transport of both
endpoints. -/
theorem homCongr_allowsTransit_iff
    {X Y X' Y' : C} (eX : X ≅ X') (eY : Y ≅ Y')
    (f : X ⟶ Y) :
    AllowsTransit (CategoryTheory.Linear.homCongr k eX eY f) ↔
      AllowsTransit f := by
  constructor
  · intro hf
    have hback := homCongr_allowsTransit (k := k)
      eX.symm eY.symm
      (CategoryTheory.Linear.homCongr k eX eY f) hf
    simpa [CategoryTheory.Linear.homCongr_apply,
      Category.assoc] using hback
  · exact homCongr_allowsTransit (k := k) eX eY f

/-- Cotransit is invariant under simultaneous isomorphism transport of both
endpoints. -/
theorem homCongr_allowsCotransit_iff
    {X Y X' Y' : C} (eX : X ≅ X') (eY : Y ≅ Y')
    (f : X ⟶ Y) :
    AllowsCotransit (CategoryTheory.Linear.homCongr k eX eY f) ↔
      AllowsCotransit f := by
  constructor
  · intro hf
    have hback := homCongr_allowsCotransit (k := k)
      eX.symm eY.symm
      (CategoryTheory.Linear.homCongr k eX eY f) hf
    simpa [CategoryTheory.Linear.homCongr_apply,
      Category.assoc] using hback
  · exact homCongr_allowsCotransit (k := k) eX eY f

/-- Transit passes through a full linear functor. -/
theorem fullLinearFunctor_map_allowsTransit
    (F : C ⥤ D) [F.Full] [F.Additive] [F.Linear k]
    {X Y : C} (f : X ⟶ Y) (hf : AllowsTransit f) :
    AllowsTransit (F.map f) := by
  intro a
  obtain ⟨a₀, ha₀⟩ := F.map_surjective a.asHom
  obtain ⟨b₀, hb₀⟩ := hf (End.of a₀)
  refine ⟨End.of (F.map b₀.asHom), ?_⟩
  change a.asHom ≫ F.map f = F.map f ≫ F.map b₀.asHom
  rw [← ha₀, ← F.map_comp, hb₀, F.map_comp]

/-- Cotransit passes through a full linear functor. -/
theorem fullLinearFunctor_map_allowsCotransit
    (F : C ⥤ D) [F.Full] [F.Additive] [F.Linear k]
    {X Y : C} (f : X ⟶ Y) (hf : AllowsCotransit f) :
    AllowsCotransit (F.map f) := by
  intro b
  obtain ⟨b₀, hb₀⟩ := F.map_surjective b.asHom
  obtain ⟨a₀, ha₀⟩ := hf (End.of b₀)
  refine ⟨End.of (F.map a₀.asHom), ?_⟩
  change F.map f ≫ b.asHom = F.map a₀.asHom ≫ F.map f
  rw [← hb₀, ← F.map_comp, ha₀, F.map_comp]

/-- A fully faithful linear functor reflects transit. -/
theorem fullyFaithfulLinearFunctor_reflects_allowsTransit
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.Additive] [F.Linear k]
    {X Y : C} (f : X ⟶ Y) (hf : AllowsTransit (F.map f)) :
    AllowsTransit f := by
  intro a
  obtain ⟨b, hb⟩ := hf (End.of (F.map a.asHom))
  obtain ⟨b₀, hb₀⟩ := F.map_surjective b.asHom
  refine ⟨End.of b₀, F.map_injective ?_⟩
  change F.map (a.asHom ≫ f) = F.map (f ≫ b₀)
  rw [F.map_comp, F.map_comp, hb₀]
  exact hb

/-- A fully faithful linear functor reflects cotransit. -/
theorem fullyFaithfulLinearFunctor_reflects_allowsCotransit
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.Additive] [F.Linear k]
    {X Y : C} (f : X ⟶ Y) (hf : AllowsCotransit (F.map f)) :
    AllowsCotransit f := by
  intro b
  obtain ⟨a, ha⟩ := hf (End.of (F.map b.asHom))
  obtain ⟨a₀, ha₀⟩ := F.map_surjective a.asHom
  refine ⟨End.of a₀, F.map_injective ?_⟩
  change F.map (f ≫ b.asHom) = F.map (a₀ ≫ f)
  rw [F.map_comp, F.map_comp, ha₀]
  exact ha

/-- A fully faithful additive linear functor restricts distributive Hom
structure to its source category. -/
theorem HasBGRSDistributiveHomStructure.of_fullyFaithful
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.Additive] [F.Linear k]
    [HasBGRSDistributiveHomStructure k D] :
    HasBGRSDistributiveHomStructure k C where
  homSubbimodule_comparable := by
    intro X Y S T hS hT
    let mapHom : (X ⟶ Y) →ₗ[k] (F.obj X ⟶ F.obj Y) :=
      F.mapLinearMap k
    let S' : Submodule k (F.obj X ⟶ F.obj Y) := S.map mapHom
    let T' : Submodule k (F.obj X ⟶ F.obj Y) := T.map mapHom
    have hS' : IsHomSubbimodule S' := by
      constructor
      · intro a g hg
        obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hg
        obtain ⟨a₀, ha₀⟩ := F.map_surjective a.asHom
        apply Submodule.mem_map.2
        refine ⟨(End.of a₀).asHom ≫ f, hS.1 (End.of a₀) hf, ?_⟩
        dsimp only [mapHom]
        change F.map ((End.of a₀).asHom ≫ f) =
          a.asHom ≫ F.map f
        rw [F.map_comp, ha₀]
      · intro b g hg
        obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hg
        obtain ⟨b₀, hb₀⟩ := F.map_surjective b.asHom
        apply Submodule.mem_map.2
        refine ⟨f ≫ (End.of b₀).asHom, hS.2 (End.of b₀) hf, ?_⟩
        dsimp only [mapHom]
        change F.map (f ≫ (End.of b₀).asHom) =
          F.map f ≫ b.asHom
        rw [F.map_comp, hb₀]
    have hT' : IsHomSubbimodule T' := by
      constructor
      · intro a g hg
        obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hg
        obtain ⟨a₀, ha₀⟩ := F.map_surjective a.asHom
        apply Submodule.mem_map.2
        refine ⟨(End.of a₀).asHom ≫ f, hT.1 (End.of a₀) hf, ?_⟩
        dsimp only [mapHom]
        change F.map ((End.of a₀).asHom ≫ f) =
          a.asHom ≫ F.map f
        rw [F.map_comp, ha₀]
      · intro b g hg
        obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hg
        obtain ⟨b₀, hb₀⟩ := F.map_surjective b.asHom
        apply Submodule.mem_map.2
        refine ⟨f ≫ (End.of b₀).asHom, hT.2 (End.of b₀) hf, ?_⟩
        dsimp only [mapHom]
        change F.map (f ≫ (End.of b₀).asHom) =
          F.map f ≫ b.asHom
        rw [F.map_comp, hb₀]
    rcases HasBGRSDistributiveHomStructure.homSubbimodule_comparable
        S' T' hS' hT' with hST | hTS
    · left
      intro f hf
      have hfS' : F.map f ∈ S' :=
        Submodule.mem_map.2 ⟨f, hf, rfl⟩
      obtain ⟨g, hg, hgf⟩ := Submodule.mem_map.1 (hST hfS')
      have heq : g = f := F.map_injective hgf
      simpa only [heq] using hg
    · right
      intro f hf
      have hfT' : F.map f ∈ T' :=
        Submodule.mem_map.2 ⟨f, hf, rfl⟩
      obtain ⟨g, hg, hgf⟩ := Submodule.mem_map.1 (hTS hfT')
      have heq : g = f := F.map_injective hgf
      simpa only [heq] using hg
  transit_or_cotransit := by
    intro X Y f
    rcases HasBGRSDistributiveHomStructure.transit_or_cotransit
        (k := k) (C := D) (F.map f) with hT | hC
    · exact Or.inl
        (fullyFaithfulLinearFunctor_reflects_allowsTransit
          (k := k) F f hT)
    · exact Or.inr
        (fullyFaithfulLinearFunctor_reflects_allowsCotransit
          (k := k) F f hC)

end LargeIndecomposable
