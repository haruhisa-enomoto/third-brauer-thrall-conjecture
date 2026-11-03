module

public import LargeIndecomposable.RepresentationEmbeddings.EmbeddingTheorem.Defs
public import LargeIndecomposable.KroneckerModules.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The extension commutes with filtered colimits and direct sums

Proposition 2.3, the part on colimits: if `Φ : D_fin → mod A` is exact, then
its colimit extension `F = Extension.functor Φ : D → Mod A` commutes with
filtered colimits, and, if `Φ` is moreover additive, with arbitrary direct
sums.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A]

/-! ### Subrepresentations: images and spans -/

namespace Kron.Sub

variable {X Y Z : Kron k}

lemma map_map_le (f : X ⟶ Y) (g : Y ⟶ Z) (U : Kron.Sub X) :
    (U.map f).map g ≤ U.map (f ≫ g) :=
  ⟨by rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩; exact ⟨v, hv, rfl⟩,
    by rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩; exact ⟨v, hv, rfl⟩⟩

lemma max_le' {U U' U'' : Kron.Sub X} (h : U ≤ U'') (h' : U' ≤ U'') : max U U' ≤ U'' :=
  ⟨sup_le h.1 h'.1, sup_le h.2 h'.2⟩

lemma map_max_le (f : X ⟶ Y) (U U' : Kron.Sub X) :
    (max U U').map f ≤ max (U.map f) (U'.map f) :=
  ⟨(Submodule.map_sup _ _ _).le, (Submodule.map_sup _ _ _).le⟩

/-- The image of the span of `S, T` is the subrepresentation `U` when `S, T`
map onto spanning sets of `U`. -/
lemma map_span_eq (f : X ⟶ Y) (U : Kron.Sub Y) (S : Set X.V) (T : Set X.W)
    (hS : Submodule.span k ((f.app zero).hom '' S) = U.V)
    (hT : Submodule.span k ((f.app one).hom '' T) = U.W) :
    (span S T).map f = U := by
  have hS' : (f.app zero).hom '' S ⊆ U.V := hS ▸ Submodule.subset_span
  apply le_antisymm
  · refine ⟨?_, ?_⟩
    · change Submodule.map _ (Submodule.span k S) ≤ _
      rw [Submodule.map_span, hS]
    · change Submodule.map _ (Submodule.span k _) ≤ _
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨w, (⟨hw | ⟨v, hv, rfl⟩⟩ | ⟨v, hv, rfl⟩), rfl⟩
      · exact hT ▸ Submodule.subset_span ⟨w, hw, rfl⟩
      · rw [Kron.a_apply]; exact U.map_a _ (hS' ⟨v, hv, rfl⟩)
      · rw [Kron.b_apply]; exact U.map_b _ (hS' ⟨v, hv, rfl⟩)
  · refine ⟨?_, ?_⟩
    · change _ ≤ Submodule.map _ (Submodule.span k S)
      rw [Submodule.map_span, hS]
    · change _ ≤ Submodule.map _ (Submodule.span k _)
      rw [Submodule.map_span, ← hT]
      exact Submodule.span_mono (Set.image_mono fun w hw ↦ Or.inl (Or.inl hw))

/-- The kernel of a morphism of Kronecker modules, as a subrepresentation. -/
def ker (g : X ⟶ Y) : Kron.Sub X where
  V := LinearMap.ker (g.app zero).hom
  W := LinearMap.ker (g.app one).hom
  map_a v hv := by
    simp only [LinearMap.mem_ker] at hv ⊢
    rw [Kron.a_apply, hv, map_zero]
  map_b v hv := by
    simp only [LinearMap.mem_ker] at hv ⊢
    rw [Kron.b_apply, hv, map_zero]

end Kron.Sub

/-! ### Consequences of exactness of `Φ` -/

section Exact

variable (Φ : Dfin k ⥤ ModuleCat.{u} A)

/-- Exactness of `Φ` on short exact sequences in `D_fin`. -/
def IsExactOnDfin : Prop :=
  ∀ (X Y Z : Dfin k) (f : X ⟶ Y) (g : Y ⟶ Z), Kron.IsShortExact f.hom g.hom →
    Function.Injective (Φ.map f).hom ∧ Function.Surjective (Φ.map g).hom ∧
      LinearMap.range (Φ.map f).hom = LinearMap.ker (Φ.map g).hom

variable {Φ}

/-- An exact `Φ` sends vertexwise surjective morphisms to surjections. -/
lemma map_surjective_of_surjective (hexact : IsExactOnDfin Φ) {X Y : Dfin k} (g : X ⟶ Y)
    (h0 : Function.Surjective (g.hom.app zero).hom)
    (h1 : Function.Surjective (g.hom.app one).hom) : Function.Surjective (Φ.map g).hom := by
  let N := Kron.Sub.ker g.hom
  have : FiniteDimensional k X.obj.V := X.2.2.1
  have : FiniteDimensional k X.obj.W := X.2.2.2
  let Z : Dfin k := ⟨N.toKron, N.inD X.2.1,
    ⟨inferInstanceAs (FiniteDimensional k N.V), inferInstanceAs (FiniteDimensional k N.W)⟩⟩
  let f : Z ⟶ X := ObjectProperty.homMk (Kron.Sub.ι N)
  refine (hexact Z X Y f g ?_).2.1
  rintro (_ | _)
  · exact ⟨Subtype.val_injective, h0, Submodule.range_subtype _⟩
  · exact ⟨Subtype.val_injective, h1, Submodule.range_subtype _⟩

/-- `Φ` sends vertexwise bijective morphisms to injections. -/
lemma map_injective_of_bijective {X Y : Dfin k} (g : X ⟶ Y)
    (h0 : Function.Bijective (g.hom.app zero).hom)
    (h1 : Function.Bijective (g.hom.app one).hom) : Function.Injective (Φ.map g).hom := by
  have : ∀ j, IsIso (g.hom.app j) := by
    rintro (_ | _)
    · exact (ConcreteCategory.isIso_iff_bijective _).2 h0
    · exact (ConcreteCategory.isIso_iff_bijective _).2 h1
  have : IsIso ((InDfin (k := k)).ι.map g) := NatIso.isIso_of_isIso_app g.hom
  have : IsIso g := (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map g
  exact ((ConcreteCategory.isIso_iff_bijective (Φ.map g)).1 inferInstance).1

end Exact

/-! ### Elementwise lemmas for the extension -/

namespace Extension

variable (Φ : Dfin k ⥤ ModuleCat.{u} A)

lemma ι_map_apply {X Y : D k} (f : X ⟶ Y) (U : Kron.FinSub X.obj) (U' : Kron.FinSub Y.obj)
    (h : U.1.map f.hom ≤ U'.1) (z : Φ.obj ((finDiagram X).obj U)) :
    (map Φ f).hom ((ι Φ X U).hom z) = (ι Φ Y U').hom ((Φ.map (restrict f U U' h)).hom z) := by
  rw [← ModuleCat.comp_apply, ι_map Φ f U U' h, ModuleCat.comp_apply]

lemma restrict_comp {X Y Z : D k} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Kron.FinSub X.obj)
    (U' : Kron.FinSub Y.obj) (U'' : Kron.FinSub Z.obj) (h : U.1.map f.hom ≤ U'.1)
    (h' : U'.1.map g.hom ≤ U''.1) :
    restrict f U U' h ≫ restrict g U' U'' h' = restrict (f ≫ g) U U''
      ((Kron.Sub.map_comp_le f.hom g.hom U.1).trans ((Kron.Sub.map_mono g.hom h).trans h')) := by
  ext1
  exact (Kron.Sub.restrict_comp f.hom g.hom U.1 U'.1 U''.1 h h'
    ((Kron.Sub.map_comp_le f.hom g.hom U.1).trans ((Kron.Sub.map_mono g.hom h).trans h'))).symm

lemma restrict_congr {X Y : D k} {f f' : X ⟶ Y} (e : f = f') (U : Kron.FinSub X.obj)
    (U' : Kron.FinSub Y.obj) (h : U.1.map f.hom ≤ U'.1) (h' : U.1.map f'.hom ≤ U'.1) :
    restrict f U U' h = restrict f' U U' h' := by
  subst e; rfl

end Extension

/-! ### Linear algebra of restrictions -/

section Restrict

variable {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module k M₁] [Module k M₂] [Module k M₃]

lemma surjective_restrict_of_le (q : M₂ →ₗ[k] M₃) (S : Submodule k M₂) (T : Submodule k M₃)
    (hST : ∀ w ∈ S, q w ∈ T) (hTS : T ≤ S.map q) : Function.Surjective (q.restrict hST) := by
  rintro ⟨w, hw⟩
  obtain ⟨v, hv, rfl⟩ := hTS hw
  exact ⟨⟨v, hv⟩, rfl⟩

lemma injective_restrict_map (p : M₁ →ₗ[k] M₂) (q : M₂ →ₗ[k] M₃) (S : Submodule k M₁)
    (T : Submodule k M₃) (hpq : ∀ v ∈ S, q (p v) = 0 → p v = 0)
    (hST : ∀ w ∈ S.map p, q w ∈ T) : Function.Injective (q.restrict hST) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨_, v, hv, rfl⟩ h
  exact Subtype.ext (hpq v hv (congrArg Subtype.val h))

end Restrict

/-! ### Finite data in filtered colimits of vector spaces -/

section Filtered

variable {J : Type u} [SmallCategory J] [IsFiltered J]

omit [IsFiltered J] in
lemma range_ι_mono {G : J ⥤ ModuleCat.{u} k} (d : Cocone G) {j j' : J} (g : j ⟶ j') :
    Set.range (d.ι.app j).hom ⊆ Set.range (d.ι.app j').hom := by
  rintro _ ⟨y, rfl⟩
  exact ⟨(G.map g).hom y, by rw [← ModuleCat.comp_apply, d.w]⟩

/-- A finite subset of a filtered colimit lies in the image of one stage,
which may be chosen after any given stage. -/
lemma exists_subset_range_ι {G : J ⥤ ModuleCat.{u} k} {d : Cocone G} (hd : IsColimit d)
    (i : J) {s : Set d.pt} (hs : s.Finite) :
    ∃ (j : J) (_ : i ⟶ j), s ⊆ Set.range (d.ι.app j).hom := by
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨i, 𝟙 i, Set.empty_subset _⟩
  | @insert a s _ _ ih =>
    obtain ⟨j, f, hj⟩ := ih
    obtain ⟨j', g, y, hy⟩ := Concrete.exists_hom_ι_eq_of_isColimit G hd a j
    exact ⟨j', f ≫ g, Set.insert_subset ⟨y, hy⟩ (hj.trans (range_ι_mono d g))⟩

/-- Finitely many elements of a stage that vanish in the colimit vanish
together at a later stage. -/
lemma exists_hom_map_eq_zero_of_finite {G : J ⥤ ModuleCat.{u} k} {d : Cocone G}
    (hd : IsColimit d) {l : J} {s : Set (G.obj l)} (hs : s.Finite)
    (h : ∀ v ∈ s, (d.ι.app l).hom v = 0) :
    ∃ (j : J) (γ : l ⟶ j), ∀ v ∈ s, (G.map γ).hom v = 0 := by
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨l, 𝟙 l, by simp⟩
  | @insert a s _ _ ih =>
    obtain ⟨j, γ, h₁, h₂⟩ := IsFiltered.exists_hom_of_stable
      (fun γ ↦ ∀ v ∈ s, (G.map γ).hom v = 0) (fun γ ↦ (G.map γ).hom a = 0)
      (fun f g h v hv ↦ by simp [h v hv]) (fun f g h ↦ by simp [h])
      (ih fun v hv ↦ h v (Set.mem_insert_of_mem _ hv))
      (exists_map_eq_zero_of_isColimit hd a (h a (Set.mem_insert _ _)))
    exact ⟨j, γ, Set.forall_mem_insert.2 ⟨h₂, h₁⟩⟩

/-- A finite-dimensional subspace of a stage that vanishes in the colimit
vanishes at a later stage. -/
lemma exists_hom_map_eq_zero_of_finiteDimensional {G : J ⥤ ModuleCat.{u} k} {d : Cocone G}
    (hd : IsColimit d) {l : J} (N : Submodule k (G.obj l)) (hN : FiniteDimensional k N)
    (h : ∀ v ∈ N, (d.ι.app l).hom v = 0) :
    ∃ (j : J) (γ : l ⟶ j), ∀ v ∈ N, (G.map γ).hom v = 0 := by
  obtain ⟨s, hs, rfl⟩ := Submodule.fg_def.1 ((Submodule.fg_iff_finiteDimensional _).2 hN)
  obtain ⟨j, γ, hγ⟩ := exists_hom_map_eq_zero_of_finite hd hs
    fun v hv ↦ h v (Submodule.subset_span hv)
  exact ⟨j, γ, fun v hv ↦ (Submodule.span_le (p := LinearMap.ker (G.map γ).hom)).2 hγ hv⟩

/-- A finite-dimensional submodule of a filtered colimit in `D` is the image
of a finite-dimensional submodule of a stage after any given stage. -/
lemma exists_lift_finSub {K : J ⥤ D k} {c : Cocone K} (hc : IsColimit c) (i : J)
    (U : Kron.FinSub c.pt.obj) :
    ∃ (j : J) (_ : i ⟶ j) (U' : Kron.FinSub (K.obj j).obj),
      U'.1.map (c.ι.app j).hom = U.1 := by
  have hcK := isColimitOfPreserves (InD (k := k)).ι hc
  have h0 := isColimitOfPreserves ((evaluation _ _).obj zero) hcK
  have h1 := isColimitOfPreserves ((evaluation _ _).obj one) hcK
  have := U.2.1
  have := U.2.2
  obtain ⟨sV, hsV, hspanV⟩ :=
    Submodule.fg_def.1 ((Submodule.fg_iff_finiteDimensional U.1.V).2 ‹_›)
  obtain ⟨sW, hsW, hspanW⟩ :=
    Submodule.fg_def.1 ((Submodule.fg_iff_finiteDimensional U.1.W).2 ‹_›)
  obtain ⟨j₁, f₁, hj₁⟩ := exists_subset_range_ι h0 i hsV
  obtain ⟨j, f₂, hj⟩ := exists_subset_range_ι h1 j₁ hsW
  have hj₁' := hj₁.trans (range_ι_mono _ f₂)
  obtain ⟨tV, -, htV, htV'⟩ := Set.exists_subset_image_finite_and (p := fun t ↦ t = sV) |>.1
    ⟨sV, by rwa [Set.image_univ], hsV, rfl⟩
  obtain ⟨tW, -, htW, htW'⟩ := Set.exists_subset_image_finite_and (p := fun t ↦ t = sW) |>.1
    ⟨sW, by rwa [Set.image_univ], hsW, rfl⟩
  refine ⟨j, f₁ ≫ f₂, ⟨Kron.Sub.span tV tW, Kron.Sub.isFin_span _ _ htV htW⟩,
    Kron.Sub.map_span_eq _ _ _ _ ?_ ?_⟩
  · exact (congrArg (Submodule.span k) htV').trans hspanV
  · exact (congrArg (Submodule.span k) htW').trans hspanW

end Filtered

/-! ### Filtered colimits -/

namespace Extension

variable {Φ : Dfin k ⥤ ModuleCat.{u} A}

/-- Proposition 2.3: the extension `F` commutes with filtered colimits. -/
def isColimit_mapCocone_of_isFiltered (hexact : IsExactOnDfin Φ) {J : Type u}
    [SmallCategory J] [IsFiltered J] {K : J ⥤ D k} {c : Cocone K} (hc : IsColimit c) :
    IsColimit ((functor Φ).mapCocone c) := by
  have hcK := isColimitOfPreserves (InD (k := k)).ι hc
  have h0 := isColimitOfPreserves ((evaluation _ _).obj zero) hcK
  have h1 := isColimitOfPreserves ((evaluation _ _).obj one) hcK
  let φ := colimit.desc (K ⋙ functor Φ) ((functor Φ).mapCocone c)
  have hφ : ∀ j x, φ.hom ((colimit.ι (K ⋙ functor Φ) j).hom x) =
      (map Φ (c.ι.app j)).hom x := fun j x ↦ by
    rw [← ModuleCat.comp_apply, colimit.ι_desc]; rfl
  suffices h : IsIso φ by
    have : IsIso ((colimit.isColimit (K ⋙ functor Φ)).desc ((functor Φ).mapCocone c)) := h
    exact IsColimit.ofPointIso (colimit.isColimit _)
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨?_, ?_⟩
  · -- Injectivity: the paper's choice of `U_j` mapping isomorphically onto `U'`.
    change Function.Injective φ.hom
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨i, xi, rfl⟩ := Concrete.colimit_exists_rep _ x
    obtain ⟨Z, z, hzx⟩ := Concrete.colimit_exists_rep (diag Φ (K.obj i)) xi
    have hx' : (ι Φ c.pt (Kron.FinSub.map (c.ι.app i).hom Z)).hom
        ((Φ.map (restrict (c.ι.app i) Z (Kron.FinSub.map (c.ι.app i).hom Z) le_rfl)).hom z) = 0 := by
      refine (ι_map_apply Φ (c.ι.app i) Z _ le_rfl z).symm.trans ?_
      exact (congrArg (map Φ (c.ι.app i)).hom hzx).trans ((hφ i xi).symm.trans hx)
    obtain ⟨U', e, hU'⟩ := Concrete.colimit_rep_eq_zero A (diag Φ c.pt) _ _ hx'
    have hZU' : Z.1.map (c.ι.app i).hom ≤ U'.1 := leOfHom e
    have hz : (Φ.map (restrict (c.ι.app i) Z U' hZU')).hom z = 0 := by
      have := restrict_comp_map (c.ι.app i) Z (U' := Kron.FinSub.map (c.ι.app i).hom Z)
        le_rfl (leOfHom e)
      rw [← this, Φ.map_comp, ModuleCat.comp_apply]
      exact hU'
    obtain ⟨l, α, A', hA'⟩ := exists_lift_finSub hc i U'
    let Ul : Kron.FinSub (K.obj l).obj :=
      ⟨max A'.1 (Z.1.map (K.map α).hom), A'.2.max (Z.2.map _)⟩
    have eα : (K.map α).hom ≫ (c.ι.app l).hom = (c.ι.app i).hom := by
      rw [← ObjectProperty.FullSubcategory.comp_hom, c.w]
    have hUl : Ul.1.map (c.ι.app l).hom ≤ U'.1 :=
      (Kron.Sub.map_max_le _ _ _).trans (Kron.Sub.max_le' hA'.le
        ((Kron.Sub.map_map_le _ _ _).trans (by rw [eα]; exact hZU')))
    have hUl' : U'.1 ≤ Ul.1.map (c.ι.app l).hom :=
      hA'.ge.trans (Kron.Sub.map_mono _ (Kron.Sub.le_max_left' _ _))
    have := Ul.2.1
    have := Ul.2.2
    have hfinV : FiniteDimensional k
        (Ul.1.V ⊓ LinearMap.ker ((c.ι.app l).hom.app zero).hom : Submodule k _) :=
      Submodule.finiteDimensional_of_le (inf_le_left (b := LinearMap.ker _))
    have hfinW : FiniteDimensional k
        (Ul.1.W ⊓ LinearMap.ker ((c.ι.app l).hom.app one).hom : Submodule k _) :=
      Submodule.finiteDimensional_of_le (inf_le_left (b := LinearMap.ker _))
    obtain ⟨j, γ, hγ0, hγ1⟩ := IsFiltered.exists_hom_of_stable
      (fun γ ↦ ∀ v ∈ Ul.1.V ⊓ LinearMap.ker ((c.ι.app l).hom.app zero).hom,
        ((K.map γ).hom.app zero).hom v = 0)
      (fun γ ↦ ∀ w ∈ Ul.1.W ⊓ LinearMap.ker ((c.ι.app l).hom.app one).hom,
        ((K.map γ).hom.app one).hom w = 0)
      (fun f g h v hv ↦ by simp [h v hv]) (fun f g h v hv ↦ by simp [h v hv])
      (exists_hom_map_eq_zero_of_finiteDimensional h0 _ hfinV fun v hv ↦ hv.2)
      (exists_hom_map_eq_zero_of_finiteDimensional h1 _ hfinW fun v hv ↦ hv.2)
    let Uj : Kron.FinSub (K.obj j).obj := Kron.FinSub.map (K.map γ).hom Ul
    have eγ : (K.map γ).hom ≫ (c.ι.app j).hom = (c.ι.app l).hom := by
      rw [← ObjectProperty.FullSubcategory.comp_hom, c.w]
    have hUj : Uj.1.map (c.ι.app j).hom ≤ U'.1 :=
      (Kron.Sub.map_map_le _ _ _).trans (by rw [eγ]; exact hUl)
    have hUj' : U'.1 ≤ Uj.1.map (c.ι.app j).hom :=
      hUl'.trans (by rw [← eγ]; exact Kron.Sub.map_comp_le _ _ _)
    let g := restrict (c.ι.app j) Uj U' hUj
    have hg : Function.Injective (Φ.map g).hom := by
      refine map_injective_of_bijective g ⟨?_, ?_⟩ ⟨?_, ?_⟩
      · refine injective_restrict_map ((K.map γ).hom.app zero).hom
          ((c.ι.app j).hom.app zero).hom Ul.1.V U'.1.V (fun v hv h ↦ hγ0 v ⟨hv, ?_⟩)
          (fun w hw ↦ hUj.1 ⟨w, hw, rfl⟩)
        show ((c.ι.app l).hom.app zero).hom v = 0
        rw [← eγ]; exact h
      · exact surjective_restrict_of_le _ _ _ (fun w hw ↦ hUj.1 ⟨w, hw, rfl⟩) hUj'.1
      · refine injective_restrict_map ((K.map γ).hom.app one).hom
          ((c.ι.app j).hom.app one).hom Ul.1.W U'.1.W (fun v hv h ↦ hγ1 v ⟨hv, ?_⟩)
          (fun w hw ↦ hUj.2 ⟨w, hw, rfl⟩)
        show ((c.ι.app l).hom.app one).hom v = 0
        rw [← eγ]; exact h
      · exact surjective_restrict_of_le _ _ _ (fun w hw ↦ hUj.2 ⟨w, hw, rfl⟩) hUj'.2
    have hZj : Z.1.map (K.map (α ≫ γ)).hom ≤ Uj.1 := by
      rw [K.map_comp, ObjectProperty.FullSubcategory.comp_hom]
      exact (Kron.Sub.map_comp_le _ _ _).trans
        (Kron.Sub.map_mono _ (Kron.Sub.le_max_right' _ _))
    have hcomp : restrict (K.map (α ≫ γ)) Z Uj hZj ≫ g = restrict (c.ι.app i) Z U' hZU' :=
      (restrict_comp _ _ _ _ _ _ _).trans (restrict_congr (c.w _) _ _ _ _)
    have key : (Φ.map (restrict (K.map (α ≫ γ)) Z Uj hZj)).hom z = 0 := by
      apply hg
      rw [← ModuleCat.comp_apply, ← Φ.map_comp, hcomp, hz, map_zero]
    have hw : (colimit.ι (K ⋙ functor Φ) i).hom xi =
        (colimit.ι (K ⋙ functor Φ) j).hom ((map Φ (K.map (α ≫ γ))).hom xi) :=
      congrArg (fun m ↦ m.hom xi) (colimit.w (K ⋙ functor Φ) (α ≫ γ)).symm
    have hmap : (map Φ (K.map (α ≫ γ))).hom xi = 0 := by
      refine (congrArg (map Φ (K.map (α ≫ γ))).hom hzx.symm).trans ?_
      rw [ι_map_apply Φ _ Z Uj hZj, key, map_zero]
    change (colimit.ι (K ⋙ functor Φ) i).hom xi = 0
    rw [hw, hmap]
    exact map_zero _
  · -- Surjectivity: lift a finite-dimensional submodule to a stage.
    intro y
    obtain ⟨U, u, rfl⟩ := Concrete.colimit_exists_rep (diag Φ c.pt) y
    obtain ⟨j, -, Uj, hUj⟩ := exists_lift_finSub hc (IsFiltered.nonempty.some) U
    let g := restrict (c.ι.app j) Uj U hUj.le
    obtain ⟨u', rfl⟩ := map_surjective_of_surjective hexact g
      (surjective_restrict_of_le _ _ _ (fun w hw ↦ hUj.le.1 ⟨w, hw, rfl⟩) hUj.ge.1)
      (surjective_restrict_of_le _ _ _ (fun w hw ↦ hUj.le.2 ⟨w, hw, rfl⟩) hUj.ge.2) u
    exact ⟨(colimit.ι (K ⋙ functor Φ) j).hom ((ι Φ _ Uj).hom u'),
      (hφ j _).trans (ι_map_apply Φ _ Uj U hUj.le u')⟩

/-- Proposition 2.3: the extension `F` commutes with filtered colimits. -/
theorem preservesFilteredColimits (hexact : IsExactOnDfin Φ) :
    PreservesFilteredColimitsOfSize.{u, u} (functor Φ) where
  preserves_filtered_colimits _ _ _ :=
    ⟨fun {_} ↦ preservesColimit_of_preserves_colimit_cocone (colimit.isColimit _)
      (isColimit_mapCocone_of_isFiltered hexact (colimit.isColimit _))⟩

end Extension

/-! ### Direct sums -/

section Coproducts

open CoproductsFromFiniteFiltered

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {E : Type u₂} [Category.{v₂} E]

lemma ι_liftToFinsetObj_map [HasFiniteCoproducts C] {α : Type w} (F : Discrete α ⥤ C)
    {t t' : Finset (Discrete α)} (h : t ⟶ t') {x : Discrete α} (hx : x ∈ t) :
    Sigma.ι (fun y : t ↦ F.obj y) ⟨x, hx⟩ ≫ (liftToFinsetObj F).map h =
      Sigma.ι (fun y : t' ↦ F.obj y) ⟨x, leOfHom h hx⟩ := by
  simp only [liftToFinsetObj_map]
  exact Sigma.ι_comp_desc _ _

lemma ι_liftToFinsetObj_eq [HasFiniteCoproducts C] {α : Type w} (F : Discrete α ⥤ C)
    [HasColimit (liftToFinsetObj F)] (t : Finset (Discrete α)) {x : Discrete α} (hx : x ∈ t) :
    Sigma.ι (fun y : t ↦ F.obj y) ⟨x, hx⟩ ≫ colimit.ι (liftToFinsetObj F) t =
      Sigma.ι (fun y : ({x} : Finset (Discrete α)) ↦ F.obj y) ⟨x, by simp⟩ ≫
        colimit.ι (liftToFinsetObj F) {x} := by
  have h := homOfLE (Finset.singleton_subset_iff.2 hx)
  exact (congrArg (· ≫ colimit.ι (liftToFinsetObj F) t)
    (ι_liftToFinsetObj_map F h (Finset.mem_singleton_self x)).symm).trans
    ((Category.assoc _ _ _).trans (congrArg _ (colimit.w (liftToFinsetObj F) h)))

/-- A functor preserving finite coproducts and filtered colimits preserves all
coproducts: an arbitrary coproduct is the filtered colimit of its finite
subcoproducts. -/
lemma preservesColimitsOfShape_discrete_of_finite_of_filtered (G : C ⥤ E) (α : Type w)
    [HasFiniteCoproducts C] [HasColimitsOfShape (Finset (Discrete α)) C]
    [PreservesFiniteCoproducts G] [PreservesColimitsOfShape (Finset (Discrete α)) G] :
    PreservesColimitsOfShape (Discrete α) G where
  preservesColimit {F} := by
    let c := liftToFinsetColimitCocone F
    refine preservesColimit_of_preserves_colimit_cocone c.isColimit ?_
    let L := liftToFinsetObj F
    have hL : IsColimit (G.mapCocone (colimit.cocone L)) :=
      isColimitOfPreserves G (colimit.isColimit L)
    have ht : ∀ t : Finset (Discrete α),
        IsColimit (G.mapCocone (colimit.cocone (Discrete.functor fun x : t ↦ F.obj x))) :=
      fun t ↦ isColimitOfPreserves G (colimit.isColimit _)
    let dt (s : Cocone (F ⋙ G)) (t : Finset (Discrete α)) : G.obj (L.obj t) ⟶ s.pt :=
      (ht t).desc ⟨s.pt, Discrete.natTrans fun x ↦ s.ι.app x.as.1⟩
    have hdt : ∀ (s : Cocone (F ⋙ G)) (t : Finset (Discrete α)) (x : Discrete α) (hx : x ∈ t),
        G.map (Sigma.ι (fun y : t ↦ F.obj y) ⟨x, hx⟩) ≫ dt s t = s.ι.app x :=
      fun s t x hx ↦ (ht t).fac _ ⟨⟨x, hx⟩⟩
    let s' (s : Cocone (F ⋙ G)) : Cocone (L ⋙ G) :=
      { pt := s.pt
        ι :=
          { app := dt s
            naturality := fun t t' h ↦ by
              refine (ht t).hom_ext fun ⟨⟨x, hx⟩⟩ ↦ ?_
              have e : Sigma.ι (fun y : t ↦ F.obj y) ⟨x, hx⟩ ≫ L.map h =
                  Sigma.ι (fun y : t' ↦ F.obj y) ⟨x, leOfHom h hx⟩ :=
                ι_liftToFinsetObj_map F h hx
              have h1 := hdt s t x hx
              have h2 := hdt s t' x (leOfHom h hx)
              change G.map (Sigma.ι (fun y : t ↦ F.obj y) ⟨x, hx⟩) ≫ G.map (L.map h) ≫ dt s t' =
                G.map (Sigma.ι (fun y : t ↦ F.obj y) ⟨x, hx⟩) ≫ dt s t ≫ 𝟙 _
              rw [Category.comp_id]
              exact (G.map_comp_assoc _ _ _).symm.trans
                ((congrArg (fun m ↦ G.map m ≫ dt s t') e).trans (h2.trans h1.symm)) } }
    exact
      { desc := fun s ↦ hL.desc (s' s)
        fac := fun s j ↦ by
          have h1 : G.map (colimit.ι L {j}) ≫ hL.desc (s' s) = dt s {j} := hL.fac (s' s) {j}
          have h2 := hdt s {j} j (by simp)
          change G.map (Sigma.ι (fun y : ({j} : Finset (Discrete α)) ↦ F.obj y) ⟨j, by simp⟩ ≫
            colimit.ι L {j}) ≫ hL.desc (s' s) = s.ι.app j
          exact (G.map_comp_assoc _ _ _).trans ((congrArg (fun m ↦ G.map _ ≫ m) h1).trans h2)
        uniq := fun s m hm ↦ by
          refine hL.hom_ext fun t ↦ (ht t).hom_ext fun ⟨⟨x, hx⟩⟩ ↦ ?_
          have h1 : G.map (colimit.ι L t) ≫ hL.desc (s' s) = dt s t := hL.fac (s' s) t
          have h2 := hdt s t x hx
          have h3 : G.map (Sigma.ι (fun y : ({x} : Finset (Discrete α)) ↦ F.obj y) ⟨x, by simp⟩ ≫
              colimit.ι L {x}) ≫ m = s.ι.app x := hm x
          change G.map (Sigma.ι (fun y : t ↦ F.obj y) ⟨x, hx⟩) ≫ G.map (colimit.ι L t) ≫ m =
            G.map (Sigma.ι (fun y : t ↦ F.obj y) ⟨x, hx⟩) ≫ G.map (colimit.ι L t) ≫ hL.desc (s' s)
          refine (G.map_comp_assoc _ _ _).symm.trans ?_
          rw [ι_liftToFinsetObj_eq F t hx, h3]
          exact ((congrArg (fun m' ↦ G.map _ ≫ m') h1).trans h2).symm }

end Coproducts

namespace Extension

variable (Φ : Dfin k ⥤ ModuleCat.{u} A)

instance additive [Φ.Additive] : (functor Φ).Additive where
  map_add {X Y f g} := by
    refine hom_ext' Φ fun U ↦ ?_
    let U' : Kron.FinSub Y.obj :=
      ⟨max (max (U.1.map f.hom) (U.1.map g.hom)) (U.1.map (f + g).hom),
        ((U.2.map _).max (U.2.map _)).max (U.2.map _)⟩
    have h1 : U.1.map f.hom ≤ U'.1 :=
      (Kron.Sub.le_max_left' _ _).trans (Kron.Sub.le_max_left' _ _)
    have h2 : U.1.map g.hom ≤ U'.1 :=
      (Kron.Sub.le_max_right' _ _).trans (Kron.Sub.le_max_left' _ _)
    have h3 : U.1.map (f + g).hom ≤ U'.1 := Kron.Sub.le_max_right' _ _
    have e : restrict (f + g) U U' h3 = restrict f U U' h1 + restrict g U U' h2 := by
      ext1
      apply Kron.hom_ext <;> (ext v; rfl)
    change ι Φ X U ≫ map Φ (f + g) = ι Φ X U ≫ (map Φ f + map Φ g)
    rw [Preadditive.comp_add, ι_map Φ (f + g) U U' h3, ι_map Φ f U U' h1, ι_map Φ g U U' h2,
      ← Preadditive.add_comp, e, Φ.map_add]

variable {Φ} in
/-- Proposition 2.3: the extension `F` of an additive exact `Φ` commutes with
arbitrary direct sums. As in the manuscript, an arbitrary sum is the filtered
colimit of its finite subsums, and `F` preserves finite sums by additivity. -/
theorem preservesCoproducts [Φ.Additive] (hexact : IsExactOnDfin Φ) (ι : Type u) :
    PreservesColimitsOfShape (Discrete ι) (functor Φ) := by
  have := preservesFilteredColimits hexact
  have : HasFiniteBiproducts (D k) := HasFiniteBiproducts.of_hasFiniteCoproducts
  exact preservesColimitsOfShape_discrete_of_finite_of_filtered _ ι

end Extension

end LargeIndecomposable
