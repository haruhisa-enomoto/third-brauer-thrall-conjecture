module

public import LargeIndecomposable.RepresentationEmbeddings.ColimitExtension.Elements
public import LargeIndecomposable.RepresentationEmbeddings.ColimitExtension.Preserves

/-!
# Properties of the colimit extension (Proposition 2.3)

For a functor `Φ : D_fin → Mod A`, the extension `F = Extension.functor Φ`
of (1.1) extends `Φ` (`Extension.isoOfFin`), is `k`-linear when `Φ` is, is
faithful and exact when `Φ` is, and satisfies `dim F(T) = dim T` for
infinite-dimensional `T` (Proposition 2.3). Additivity and colimit
preservation are in `Extension.Preserves`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A]

/-- The whole module as a subrepresentation is isomorphic to the module. -/
def Kron.Sub.topIso (X : Kron k) : (Kron.Sub.top X).toKron ≅ X where
  hom := Kron.Sub.ι _
  inv := Kron.homMk
    (ModuleCat.ofHom (LinearMap.codRestrict (Kron.Sub.top X).V LinearMap.id fun _ ↦ trivial))
    (ModuleCat.ofHom (LinearMap.codRestrict (Kron.Sub.top X).W LinearMap.id fun _ ↦ trivial))
    rfl rfl
  hom_inv_id := by apply Kron.hom_ext <;> rfl
  inv_hom_id := by apply Kron.hom_ext <;> rfl

/-- Restricting a short exact sequence `M → N → P` of vector spaces to
`φ⁻¹(Q) → Q → ψ(Q)` gives a short exact sequence. -/
lemma restrict_comap_map_shortExact {M N P : Type u} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P]
    [Module k M] [Module k N] [Module k P] (φ : M →ₗ[k] N) (ψ : N →ₗ[k] P)
    (hφ : Function.Injective φ) (hrange : LinearMap.range φ = LinearMap.ker ψ)
    (Q : Submodule k N) :
    Function.Injective (φ.restrict (p := Q.comap φ) (q := Q) fun _ hv ↦ hv) ∧
      Function.Surjective (ψ.restrict (p := Q) (q := Q.map ψ) fun y hy ↦ ⟨y, hy, rfl⟩) ∧
      LinearMap.range (φ.restrict (p := Q.comap φ) (q := Q) fun _ hv ↦ hv) =
        LinearMap.ker (ψ.restrict (p := Q) (q := Q.map ψ) fun y hy ↦ ⟨y, hy, rfl⟩) := by
  refine ⟨fun x y h ↦ Subtype.ext (hφ (congrArg Subtype.val h)), ?_, ?_⟩
  · rintro ⟨_, y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  · ext ⟨y, hy⟩
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨⟨x, hx⟩, hxy⟩
      have hxy : φ x = y := congrArg Subtype.val hxy
      apply Subtype.ext
      change ψ y = 0
      rw [← hxy, ← LinearMap.mem_ker, ← hrange]
      exact ⟨x, rfl⟩
    · intro h
      have h : ψ y = 0 := congrArg Subtype.val h
      rw [← LinearMap.mem_ker, ← hrange] at h
      obtain ⟨x, rfl⟩ := h
      exact ⟨⟨x, hy⟩, rfl⟩

namespace Kron.Sub

variable {X Y Z : Kron k}

/-- The preimage of a subrepresentation. -/
def comap (f : X ⟶ Y) (U : Kron.Sub Y) : Kron.Sub X where
  V := U.V.comap (f.app zero).hom
  W := U.W.comap (f.app one).hom
  map_a v hv := by
    change (f.app one).hom (X.a.hom v) ∈ U.W
    rw [Kron.a_apply]; exact U.map_a _ hv
  map_b v hv := by
    change (f.app one).hom (X.b.hom v) ∈ U.W
    rw [Kron.b_apply]; exact U.map_b _ hv

lemma map_comap_le (f : X ⟶ Y) (U : Kron.Sub Y) : (U.comap f).map f ≤ U :=
  ⟨Submodule.map_comap_le _ _, Submodule.map_comap_le _ _⟩

lemma le_comap_of_map_le (f : X ⟶ Y) {U : Kron.Sub X} {U' : Kron.Sub Y} (h : U.map f ≤ U') :
    U ≤ U'.comap f :=
  ⟨fun v hv ↦ h.1 ⟨v, hv, rfl⟩, fun w hw ↦ h.2 ⟨w, hw, rfl⟩⟩

lemma IsFin.comap {U : Kron.Sub Y} (h : U.IsFin) (f : X ⟶ Y)
    (h0 : Function.Injective (f.app zero).hom) (h1 : Function.Injective (f.app one).hom) :
    (U.comap f).IsFin := by
  obtain ⟨_, _⟩ := h
  exact ⟨FiniteDimensional.of_injective ((f.app zero).hom.restrict (q := U.V) fun _ hv ↦ hv)
      fun x y hxy ↦ Subtype.ext (h0 (congrArg Subtype.val hxy)),
    FiniteDimensional.of_injective ((f.app one).hom.restrict (q := U.W) fun _ hv ↦ hv)
      fun x y hxy ↦ Subtype.ext (h1 (congrArg Subtype.val hxy))⟩

/-- Proposition 2.3: a short exact sequence `X → Y → Z` restricts to the short exact
sequence `f⁻¹(U) → U → g(U)` for every subrepresentation `U ⊆ Y`. -/
lemma isShortExact_restrict (f : X ⟶ Y) (g : Y ⟶ Z) (h : Kron.IsShortExact f g)
    (U : Kron.Sub Y) :
    Kron.IsShortExact (restrict f (U.comap f) U (map_comap_le f U))
      (restrict g U (U.map g) le_rfl) := by
  intro j
  cases j
  · exact restrict_comap_map_shortExact _ _ (h zero).1 (h zero).2.2 U.V
  · exact restrict_comap_map_shortExact _ _ (h one).1 (h one).2.2 U.W

end Kron.Sub

namespace Kron.FinSub

variable {Y Z : Kron k}

/-- A finite-dimensional subrepresentation of the target of a surjection is
contained in the image of a finite-dimensional subrepresentation. -/
lemma exists_le_map (g : Y ⟶ Z) (h0 : Function.Surjective (g.app zero).hom)
    (h1 : Function.Surjective (g.app one).hom) (U : Kron.FinSub Z) :
    ∃ U' : Kron.FinSub Y, U ≤ map g U' := by
  classical
  obtain ⟨_, _⟩ := U.2
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional U.1.V).2 inferInstance
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional U.1.W).2 inferInstance
  choose l0 hl0 using h0
  choose l1 hl1 using h1
  obtain ⟨U', hS, hT⟩ := exists_of_finite (l0 '' s) (l1 '' t) (s.finite_toSet.image _)
    (t.finite_toSet.image _)
  refine ⟨U', ?_, ?_⟩
  · change U.1.V ≤ U'.1.V.map (g.app zero).hom
    rw [← hs, Submodule.span_le]
    intro z hz
    exact ⟨l0 z, hS ⟨z, hz, rfl⟩, hl0 z⟩
  · change U.1.W ≤ U'.1.W.map (g.app one).hom
    rw [← ht, Submodule.span_le]
    intro z hz
    exact ⟨l1 z, hT ⟨z, hz, rfl⟩, hl1 z⟩

end Kron.FinSub

namespace Extension

/-- A finite-dimensional object of `D`, as an object of `D_fin`. -/
abbrev toDfin (X : D k) (hX : X.obj.IsFiniteDimensional) : Dfin k := ⟨X.obj, X.2, hX⟩

/-- The largest finite-dimensional subrepresentation of a finite-dimensional
module. -/
def topFin {X : Kron k} (hX : X.IsFiniteDimensional) : Kron.FinSub X :=
  ⟨Kron.Sub.top X, Kron.Sub.isFin_top hX⟩

lemma le_topFin {X : Kron k} (hX : X.IsFiniteDimensional) (U : Kron.FinSub X) :
    U ≤ topFin hX :=
  Kron.Sub.le_top U.1

/-- `topFin` is terminal in the index poset. -/
def isTerminalTopFin {X : Kron k} (hX : X.IsFiniteDimensional) :
    IsTerminal (topFin hX) :=
  IsTerminal.ofUniqueHom (fun U ↦ homOfLE (le_topFin hX U)) fun _ _ ↦ Subsingleton.elim _ _

/-- The top subrepresentation of `X`, in `D_fin`, is isomorphic to `X`. -/
def topIsoDfin (X : D k) (hX : X.obj.IsFiniteDimensional) :
    (finDiagram X).obj (topFin hX) ≅ toDfin X hX :=
  ObjectProperty.isoMk _ (Kron.Sub.topIso X.obj)

variable (Φ : Dfin k ⥤ ModuleCat.{u} A)

instance isIso_ι_topFin (X : D k) (hX : X.obj.IsFiniteDimensional) :
    IsIso (ι Φ X (topFin hX)) :=
  isIso_ι_of_isTerminal (isTerminalTopFin hX) _

/-- Proposition 2.3: on finite-dimensional modules, `F(X) ≅ Φ(X)`. -/
def isoOfFin (X : D k) (hX : X.obj.IsFiniteDimensional) :
    (functor Φ).obj X ≅ Φ.obj (toDfin X hX) :=
  (asIso (ι Φ X (topFin hX))).symm ≪≫ Φ.mapIso (topIsoDfin X hX)

lemma ι_isoOfFin_hom (X : D k) (hX : X.obj.IsFiniteDimensional) :
    ι Φ X (topFin hX) ≫ (isoOfFin Φ X hX).hom = Φ.map (topIsoDfin X hX).hom := by
  change ι Φ X (topFin hX) ≫ inv (ι Φ X (topFin hX)) ≫ Φ.map (topIsoDfin X hX).hom = _
  rw [IsIso.hom_inv_id_assoc]

/-- Proposition 2.3: naturality of `F(X) ≅ Φ(X)` on finite-dimensional
modules. -/
@[reassoc]
lemma isoOfFin_hom_naturality {X Y : D k} (hX : X.obj.IsFiniteDimensional)
    (hY : Y.obj.IsFiniteDimensional) (f : X ⟶ Y) :
    (functor Φ).map f ≫ (isoOfFin Φ Y hY).hom =
      (isoOfFin Φ X hX).hom ≫ Φ.map (ObjectProperty.homMk f.hom : toDfin X hX ⟶ toDfin Y hY) := by
  change map Φ f ≫ inv (ι Φ Y (topFin hY)) ≫ Φ.map (topIsoDfin Y hY).hom =
    inv (ι Φ X (topFin hX)) ≫ Φ.map (topIsoDfin X hX).hom ≫ Φ.map _
  rw [IsIso.eq_inv_comp, ι_map_assoc Φ f (topFin hX) (topFin hY) (Kron.Sub.le_top _),
    IsIso.hom_inv_id_assoc, ← Φ.map_comp, ← Φ.map_comp]
  congr 1
  ext1
  apply Kron.hom_ext <;> rfl

/-! ### Additivity and linearity -/

lemma restrict_add {X Y : D k} (f g : X ⟶ Y) (U : Kron.FinSub X.obj) (U' : Kron.FinSub Y.obj)
    (hf : U.1.map f.hom ≤ U'.1) (hg : U.1.map g.hom ≤ U'.1) (hfg : U.1.map (f + g).hom ≤ U'.1) :
    restrict (f + g) U U' hfg = restrict f U U' hf + restrict g U U' hg := by
  ext1; apply Kron.hom_ext <;> rfl

lemma restrict_smul {X Y : D k} (c : k) (f : X ⟶ Y) (U : Kron.FinSub X.obj)
    (U' : Kron.FinSub Y.obj) (hf : U.1.map f.hom ≤ U'.1) (hcf : U.1.map (c • f).hom ≤ U'.1) :
    restrict (c • f) U U' hcf = c • restrict f U U' hf := by
  ext1; apply Kron.hom_ext <;> rfl

lemma exists_ge₃ {X : Kron k} (U₁ U₂ U₃ : Kron.FinSub X) :
    ∃ U : Kron.FinSub X, U₁ ≤ U ∧ U₂ ≤ U ∧ U₃ ≤ U := by
  obtain ⟨V, h1, h2⟩ := _root_.exists_ge_ge U₁ U₂
  obtain ⟨U, h3, h4⟩ := _root_.exists_ge_ge V U₃
  exact ⟨U, h1.trans h3, h2.trans h3, h4⟩

/-- Proposition 2.3: `F` is `k`-linear. -/
instance linear [Algebra k A] [Φ.Linear k] : (functor Φ).Linear k where
  map_smul {X Y} f c := by
    refine hom_ext' Φ fun U ↦ ?_
    obtain ⟨U', h1, h2⟩ := _root_.exists_ge_ge (Kron.FinSub.map f.hom U)
      (Kron.FinSub.map (c • f).hom U)
    change ι Φ X U ≫ map Φ (c • f) = ι Φ X U ≫ (c • map Φ f)
    rw [ι_map Φ (c • f) U U' h2, Linear.comp_smul, ι_map Φ f U U' h1,
      restrict_smul c f U U' h1 h2, Φ.map_smul, Linear.smul_comp]

/-! ### Faithfulness -/

/-- If `F(f) = 0`, every restriction of `f` to a finite-dimensional
subrepresentation vanishes after enlarging the target. -/
lemma exists_restrict_eq_zero [Algebra k A]
    (hfin : ∀ X : Dfin k, Module.Finite k (RestrictScalars k A (Φ.obj X))) [Φ.Faithful]
    [Φ.Additive] {X Y : D k} (f : X ⟶ Y) (hf : (functor Φ).map f = 0) (U : Kron.FinSub X.obj) :
    ∃ (U' : Kron.FinSub Y.obj) (h : U.1.map f.hom ≤ U'.1), restrict f U U' h = 0 := by
  have h0 : Φ.map (restrict f U (Kron.FinSub.map f.hom U) le_rfl) ≫
      ι Φ Y (Kron.FinSub.map f.hom U) = 0 := by
    refine (ι_map Φ f U _ le_rfl).symm.trans ?_
    have hf' : map Φ f = 0 := hf
    rw [hf', Limits.comp_zero]
  obtain ⟨U', hU', h⟩ := exists_comp_eq_zero Φ Y (hfin _) _ _ h0
  refine ⟨U', hU', Φ.map_injective ?_⟩
  rw [← restrict_comp_map f U le_rfl hU', Φ.map_comp, h, Φ.map_zero]

/-- Proposition 2.3: `F` is faithful. -/
lemma faithful [Algebra k A]
    (hfin : ∀ X : Dfin k, Module.Finite k (RestrictScalars k A (Φ.obj X))) [Φ.Faithful]
    [Φ.Additive] : (functor Φ).Faithful where
  map_injective {X Y f g} h := by
    rw [← sub_eq_zero] at h ⊢
    rw [← Functor.map_sub] at h
    set d := f - g
    have key : ∀ U : Kron.FinSub X.obj, (∀ v ∈ U.1.V, (d.hom.app zero).hom v = 0) ∧
        ∀ w ∈ U.1.W, (d.hom.app one).hom w = 0 := by
      intro U
      obtain ⟨U', hU', h0⟩ := exists_restrict_eq_zero Φ hfin d h U
      constructor
      · intro v hv
        have := congrArg (fun r : _ ⟶ _ ↦ (((r.hom.app zero).hom ⟨v, hv⟩ : U'.1.V) : Y.obj.V)) h0
        exact this
      · intro w hw
        have := congrArg (fun r : _ ⟶ _ ↦ (((r.hom.app one).hom ⟨w, hw⟩ : U'.1.W) : Y.obj.W)) h0
        exact this
    ext1
    apply Kron.hom_ext
    · ext v
      obtain ⟨U, hU, -⟩ := Kron.FinSub.exists_of_finite {v} (∅ : Set X.obj.W)
        (Set.finite_singleton v) Set.finite_empty
      exact (key U).1 v (hU rfl)
    · ext w
      obtain ⟨U, -, hU⟩ := Kron.FinSub.exists_of_finite (∅ : Set X.obj.V) {w}
        Set.finite_empty (Set.finite_singleton w)
      exact (key U).2 w (hU rfl)

/-! ### Exactness -/

section Exact

variable {X Y Z : D k} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The preimage `f⁻¹(U)` of a finite-dimensional subrepresentation under an
injective morphism. -/
def preFin (hf0 : Function.Injective (f.hom.app zero).hom)
    (hf1 : Function.Injective (f.hom.app one).hom) (U : Kron.FinSub Y.obj) :
    Kron.FinSub X.obj :=
  ⟨U.1.comap f.hom, U.2.comap f.hom hf0 hf1⟩

/-- The restriction `f⁻¹(U) → U`. -/
abbrev preι (hf0 : Function.Injective (f.hom.app zero).hom)
    (hf1 : Function.Injective (f.hom.app one).hom) (U : Kron.FinSub Y.obj) :
    (finDiagram X).obj (preFin f hf0 hf1 U) ⟶ (finDiagram Y).obj U :=
  restrict f (preFin f hf0 hf1 U) U (Kron.Sub.map_comap_le f.hom U.1)

lemma restrict_eq_comp {U₁ U₂ : Kron.FinSub X.obj} {U₃ : Kron.FinSub Y.obj} (hU : U₁ ≤ U₂)
    (h : U₁.1.map f.hom ≤ U₃.1) (h' : U₂.1.map f.hom ≤ U₃.1) :
    restrict f U₁ U₃ h = (finDiagram X).map (homOfLE hU) ≫ restrict f U₂ U₃ h' := by
  ext1; apply Kron.hom_ext <;> rfl

omit [Field k] in
lemma map_comp_apply {C : Type*} [Category C] (G : C ⥤ ModuleCat.{u} A) {P Q R : C}
    (a : P ⟶ Q) (b : Q ⟶ R) (y : G.obj P) :
    (G.map (a ≫ b)).hom y = (G.map b).hom ((G.map a).hom y) := by
  rw [G.map_comp, ModuleCat.comp_apply]

variable (hexact : IsExactOnDfin Φ) (h : Kron.IsShortExact f.hom g.hom)

include hexact h

lemma exact_restrict (U : Kron.FinSub Y.obj) :
    Function.Injective (Φ.map (preι f (h zero).1 (h one).1 U)).hom ∧
      Function.Surjective (Φ.map (restrict g U (Kron.FinSub.map g.hom U) le_rfl)).hom ∧
      LinearMap.range (Φ.map (preι f (h zero).1 (h one).1 U)).hom =
        LinearMap.ker (Φ.map (restrict g U (Kron.FinSub.map g.hom U) le_rfl)).hom :=
  hexact _ _ _ _ _ (Kron.Sub.isShortExact_restrict f.hom g.hom h U.1)

lemma injective_map : Function.Injective ((functor Φ).map f).hom := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨U, y, rfl⟩ := exists_rep Φ X x
  rw [map_ιF_apply Φ f U (Kron.FinSub.map f.hom U) le_rfl, ιF_eq_zero_iff] at hx
  obtain ⟨U', hU', hy⟩ := hx
  rw [← map_comp_apply, restrict_comp_map f U le_rfl hU'] at hy
  have hle : U ≤ preFin f (h zero).1 (h one).1 U' :=
    Kron.Sub.le_comap_of_map_le f.hom (le_trans le_rfl hU')
  rw [restrict_eq_comp f hle (le_rfl.trans hU') (Kron.Sub.map_comap_le f.hom U'.1),
    map_comp_apply] at hy
  rw [← ιF_apply_of_le Φ X hle,
    (exact_restrict Φ f g hexact h U').1 (hy.trans (map_zero _).symm), map_zero]

lemma surjective_map : Function.Surjective ((functor Φ).map g).hom := by
  intro z
  obtain ⟨U, z₀, rfl⟩ := exists_rep Φ Z z
  obtain ⟨U', hU'⟩ := Kron.FinSub.exists_le_map g.hom (h zero).2.1 (h one).2.1 U
  obtain ⟨y, hy⟩ := (exact_restrict Φ f g hexact h U').2.1
    ((Φ.map ((finDiagram Z).map (homOfLE hU'))).hom z₀)
  refine ⟨(ιF Φ Y U').hom y, ?_⟩
  rw [map_ιF_apply Φ g U' (Kron.FinSub.map g.hom U') le_rfl, hy, ιF_apply_of_le]

lemma range_map_eq_ker :
    LinearMap.range ((functor Φ).map f).hom = LinearMap.ker ((functor Φ).map g).hom := by
  ext y
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨U, x₀, rfl⟩ := exists_rep Φ X x
    set U' := Kron.FinSub.map f.hom U
    have hle : U ≤ preFin f (h zero).1 (h one).1 U' := Kron.Sub.le_comap_of_map_le f.hom le_rfl
    rw [map_ιF_apply Φ f U U' le_rfl, map_ιF_apply Φ g U' (Kron.FinSub.map g.hom U') le_rfl,
      restrict_eq_comp f hle le_rfl (Kron.Sub.map_comap_le f.hom U'.1), map_comp_apply]
    have hmem : (Φ.map (preι f (h zero).1 (h one).1 U')).hom
        ((Φ.map ((finDiagram X).map (homOfLE hle))).hom x₀) ∈
          LinearMap.ker (Φ.map (restrict g U' (Kron.FinSub.map g.hom U') le_rfl)).hom := by
      rw [← (exact_restrict Φ f g hexact h U').2.2]
      exact ⟨_, rfl⟩
    rw [LinearMap.mem_ker.1 hmem, map_zero]
  · intro hy
    obtain ⟨U, y₀, rfl⟩ := exists_rep Φ Y y
    rw [map_ιF_apply Φ g U (Kron.FinSub.map g.hom U) le_rfl, ιF_eq_zero_iff] at hy
    obtain ⟨U₂, hU₂, hy⟩ := hy
    rw [← map_comp_apply, restrict_comp_map g U le_rfl hU₂] at hy
    obtain ⟨U₃, hU₃⟩ := Kron.FinSub.exists_le_map g.hom (h zero).2.1 (h one).2.1 U₂
    obtain ⟨U', hUU', hU₃U'⟩ := exists_ge_ge U U₃
    have hle : U₂ ≤ Kron.FinSub.map g.hom U' :=
      hU₃.trans (Kron.FinSub.map_mono g.hom hU₃U')
    have hker : (Φ.map ((finDiagram Y).map (homOfLE hUU'))).hom y₀ ∈
        LinearMap.ker (Φ.map (restrict g U' (Kron.FinSub.map g.hom U') le_rfl)).hom := by
      rw [LinearMap.mem_ker, ← map_comp_apply,
        ← restrict_eq_comp g hUU' (Kron.Sub.map_mono g.hom hUU') le_rfl,
        ← restrict_comp_map g U hU₂ hle, map_comp_apply, hy, map_zero]
    rw [← (exact_restrict Φ f g hexact h U').2.2] at hker
    obtain ⟨x, hx⟩ := hker
    refine ⟨(ιF Φ X (preFin f (h zero).1 (h one).1 U')).hom x, ?_⟩
    rw [map_ιF_apply Φ f (preFin f (h zero).1 (h one).1 U') U'
      (Kron.Sub.map_comap_le f.hom U'.1), hx, ιF_apply_of_le Φ Y hUU']

/-- Proposition 2.3: `F` is exact. -/
theorem map_shortExact : Function.Injective ((functor Φ).map f).hom ∧
    Function.Surjective ((functor Φ).map g).hom ∧
      LinearMap.range ((functor Φ).map f).hom = LinearMap.ker ((functor Φ).map g).hom :=
  ⟨injective_map Φ f g hexact h, surjective_map Φ f g hexact h, range_map_eq_ker Φ f g hexact h⟩

end Exact

/-! ### Dimension -/

section Dimension

variable [Algebra k A]

/-- An `A`-linear map as a `k`-linear map between the restrictions of
scalars. -/
def rsMap {M N : ModuleCat.{u} A} (φ : M ⟶ N) :
    RestrictScalars k A M →ₗ[k] RestrictScalars k A N where
  toFun := φ.hom
  map_add' := φ.hom.map_add
  map_smul' c x := φ.hom.map_smul (algebraMap k A c) x

lemma rsMap_apply {M N : ModuleCat.{u} A} (φ : M ⟶ N) (x : M) :
    rsMap (k := k) φ x = φ.hom x := rfl

omit [Algebra k A] in
lemma mk_finset_le (α : Type u) : Cardinal.mk (Finset α) ≤ max Cardinal.aleph0 (Cardinal.mk α) := by
  classical
  exact (Cardinal.mk_le_of_surjective List.toFinset_surjective).trans (Cardinal.mk_list_le_max α)

omit [Algebra k A] in
/-- Every finite-dimensional subrepresentation lies in the span of finitely
many basis vectors. -/
lemma exists_le_span_basis (X : Kron k) {ιV ιW : Type u} (bV : Module.Basis ιV k X.V)
    (bW : Module.Basis ιW k X.W) (U : Kron.FinSub X) :
    ∃ p : Finset ιV × Finset ιW, U.1 ≤ Kron.Sub.span (bV '' p.1) (bW '' p.2) := by
  classical
  obtain ⟨_, _⟩ := U.2
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional U.1.V).2 inferInstance
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional U.1.W).2 inferInstance
  refine ⟨(s.biUnion fun v ↦ (bV.repr v).support, t.biUnion fun w ↦ (bW.repr w).support), ?_, ?_⟩
  · change U.1.V ≤ Submodule.span k _
    rw [← hs, Submodule.span_le]
    intro v hv
    refine Submodule.span_mono ?_ (bV.mem_span_repr_support v)
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨i, Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨v, hv, hi⟩), rfl⟩
  · change U.1.W ≤ Submodule.span k _
    rw [← ht, Submodule.span_le]
    intro w hw
    refine Submodule.span_mono ?_ (bW.mem_span_repr_support w)
    rintro _ ⟨i, hi, rfl⟩
    exact Or.inl (Or.inl ⟨i, Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨w, hw, hi⟩), rfl⟩)

omit [Algebra k A] in
lemma dim_le_of_span_eq_top [Algebra k A] {M : ModuleCat.{u} A} {G : Set (RestrictScalars k A M)}
    (hG : Submodule.span k G = ⊤) : Statement.dim k A M ≤ Cardinal.mk G := by
  have := rank_span_le (R := k) G
  rwa [hG, rank_top] at this

/-- If the `U_i` are cofinal and `g_i` spans `Φ(U_i)`, the images of the `g_i`
span `F(X)` over `k`. -/
lemma span_iUnion_image_ιF (X : D k) {ι : Type u} (fs : ι → Kron.FinSub X.obj)
    (hcof : ∀ U, ∃ i, U ≤ fs i)
    (g : ∀ i, Set (RestrictScalars k A (Φ.obj ((finDiagram X).obj (fs i)))))
    (hg : ∀ i, Submodule.span k (g i) = ⊤) :
    Submodule.span k (⋃ i, rsMap (ιF Φ X (fs i)) '' g i) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨U, y, rfl⟩ := exists_rep Φ X x
  obtain ⟨i, hi⟩ := hcof U
  rw [← ιF_apply_of_le Φ X hi]
  refine Submodule.span_mono (Set.subset_iUnion (fun i ↦ rsMap (ιF Φ X (fs i)) '' g i) i) ?_
  rw [← Submodule.map_span, hg i]
  exact Submodule.mem_map_of_mem trivial

/-- Proposition 2.3, upper bound: `dim F(T) ≤ dim T` for infinite-dimensional
`T`. Different route from the manuscript: `F(T)` is the union of the images of
the `Φ(U)` for `U` spanned by finitely many basis vectors. -/
theorem dim_le (hfin : ∀ X : Dfin k, Module.Finite k (RestrictScalars k A (Φ.obj X)))
    (X : D k) (hX : Cardinal.aleph0 ≤ X.obj.dim) :
    Statement.dim k A ((functor Φ).obj X) ≤ X.obj.dim := by
  classical
  let bV := Module.Free.chooseBasis k X.obj.V
  let bW := Module.Free.chooseBasis k X.obj.W
  let P := Finset (Module.Free.ChooseBasisIndex k X.obj.V) ×
    Finset (Module.Free.ChooseBasisIndex k X.obj.W)
  obtain ⟨fs, hfs⟩ : ∃ fs : P → Kron.FinSub X.obj, ∀ U, ∃ p, U ≤ fs p :=
    ⟨fun p ↦ ⟨Kron.Sub.span (bV '' p.1) (bW '' p.2),
      Kron.Sub.isFin_span _ _ (p.1.finite_toSet.image _) (p.2.finite_toSet.image _)⟩,
      fun U ↦ exists_le_span_basis X.obj bV bW U⟩
  choose g hg using fun p : P ↦ (hfin ((finDiagram X).obj (fs p))).fg_top
  have hG := span_iUnion_image_ιF Φ X fs hfs (fun p ↦ (g p : Set _)) (fun p ↦ by exact hg p)
  have h2 := (dim_le_of_span_eq_top hG).trans (Cardinal.mk_iUnion_le _)
  have hV : Cardinal.mk (Finset (Module.Free.ChooseBasisIndex k X.obj.V)) ≤ X.obj.dim := by
    refine (mk_finset_le _).trans (max_le hX ?_)
    rw [← Module.Free.rank_eq_card_chooseBasisIndex]
    exact self_le_add_right _ _
  have hW : Cardinal.mk (Finset (Module.Free.ChooseBasisIndex k X.obj.W)) ≤ X.obj.dim := by
    refine (mk_finset_le _).trans (max_le hX ?_)
    rw [← Module.Free.rank_eq_card_chooseBasisIndex]
    exact self_le_add_left _ _
  have h3 : Cardinal.mk P * Cardinal.aleph0 ≤ X.obj.dim := by
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    calc _ ≤ X.obj.dim * X.obj.dim * X.obj.dim := by gcongr
      _ = X.obj.dim := by rw [Cardinal.mul_eq_self hX, Cardinal.mul_eq_self hX]
  refine h2.trans ((mul_le_mul_right (ciSup_le' fun p ↦ ?_) _).trans h3)
  exact Cardinal.mk_image_le.trans (Set.Finite.lt_aleph0 (by exact (g p).finite_toSet)).le

omit [Algebra k A] in
lemma cardinal_aux {dV dW dF : Cardinal.{u}} (n : ℕ) (hX : Cardinal.aleph0 ≤ dV + dW)
    (hVW : dV ≤ dW + dW) (hWF : dW ≤ n * dF) : dV + dW ≤ dF := by
  have hW : Cardinal.aleph0 ≤ dW := by
    by_contra hW
    rw [not_le] at hW
    exact (Cardinal.add_lt_aleph0 ((hVW.trans_lt (Cardinal.add_lt_aleph0 hW hW))) hW).not_ge hX
  have hF : Cardinal.aleph0 ≤ dF := by
    by_contra hF
    rw [not_le] at hF
    exact (hWF.trans_lt (Cardinal.mul_lt_aleph0 Cardinal.natCast_lt_aleph0 hF)).not_ge hW
  calc dV + dW ≤ dW + dW + dW := by gcongr
    _ = dW := by rw [Cardinal.add_eq_self hW, Cardinal.add_eq_self hW]
    _ ≤ n * dF := hWF
    _ ≤ max (n : Cardinal) dF := Cardinal.mul_le_max_of_aleph0_le_right hF
    _ = dF := max_eq_right (Cardinal.natCast_lt_aleph0.le.trans hF)

/-- The simple projective Kronecker module `S₋ = (0, k; 0, 0)`, an object of
`D`. -/
def Sminus : D k :=
  ⟨Kron.mk (ModuleCat.of k PUnit) (ModuleCat.of k k) 0 0, by
    rw [inD_iff]; intro v _ _; rfl⟩

omit [Algebra k A] in
lemma Sminus_isFiniteDimensional : (Sminus (k := k)).obj.IsFiniteDimensional :=
  ⟨by change FiniteDimensional k PUnit; infer_instance,
    by change FiniteDimensional k k; infer_instance⟩

/-- The morphism `S₋ → X` sending `1` to `w`. -/
def fromSminus (X : D k) (w : X.obj.W) : Sminus ⟶ X :=
  ObjectProperty.homMk (Kron.homMk (X := Sminus.obj) (Y := X.obj) 0
    (ModuleCat.ofHom (LinearMap.toSpanSingleton k X.obj.W w))
    (by ext v; obtain rfl : v = 0 := rfl; exact (map_zero _).trans (map_zero _).symm)
    (by ext v; obtain rfl : v = 0 := rfl; exact (map_zero _).trans (map_zero _).symm))

omit [Algebra k A] in
lemma fromSminus_app_one (X : D k) (w : X.obj.W) (c : k) :
    (((fromSminus X w).hom.app one).hom c) = c • w := rfl

/-- `W ≅ Hom(S₋, X)`, as an injective linear map. -/
def fromSminusLinear (X : D k) : X.obj.W →ₗ[k] (Sminus ⟶ X) where
  toFun := fromSminus X
  map_add' w w' := by
    ext1; apply Kron.hom_ext
    · ext v
      obtain rfl : v = 0 := rfl
      exact (map_zero _).trans (map_zero _).symm
    · ext
      change (1 : k) • (w + w') = (1 : k) • w + (1 : k) • w'
      rw [smul_add]
  map_smul' c w := by
    ext1; apply Kron.hom_ext
    · ext v
      obtain rfl : v = 0 := rfl
      exact (map_zero _).trans (map_zero _).symm
    · ext
      change (1 : k) • (c • w) = c • ((1 : k) • w)
      rw [one_smul, one_smul]

omit [Algebra k A] in
lemma fromSminusLinear_injective (X : D k) : Function.Injective (fromSminusLinear X) := by
  intro w w' h
  have := congrArg (fun φ : Sminus ⟶ X ↦ (φ.hom.app one).hom (1 : k)) h
  simpa [fromSminusLinear, fromSminus_app_one] using this

/-- Proposition 2.3, lower bound: `dim T ≤ dim F(T)` for infinite-dimensional
`T`, from `W ≅ Hom(S₋, T) ↪ Hom_A(F(S₋), F(T))` and `dim V ≤ 2 dim W`. -/
theorem le_dim (hfin : ∀ X : Dfin k, Module.Finite k (RestrictScalars k A (Φ.obj X)))
    [Φ.Faithful] [Φ.Additive] [Φ.Linear k] (X : D k) (hX : Cardinal.aleph0 ≤ X.obj.dim) :
    X.obj.dim ≤ Statement.dim k A ((functor Φ).obj X) := by
  have hS := Sminus_isFiniteDimensional (k := k)
  have : Module.Finite A ((functor Φ).obj Sminus) := by
    have : Module.Finite A (Φ.obj (toDfin Sminus hS)) := finite_of_restrictScalars (hfin _)
    exact Module.Finite.equiv (isoOfFin Φ Sminus hS).toLinearEquiv.symm
  obtain ⟨n, e, he⟩ := Module.Finite.exists_fin (R := A) (M := (functor Φ).obj Sminus)
  have := faithful Φ hfin
  let ev : ((functor Φ).obj Sminus ⟶ (functor Φ).obj X) →ₗ[k]
      (Fin n → RestrictScalars k A ((functor Φ).obj X)) :=
    { toFun φ i := φ.hom (e i)
      map_add' φ ψ := rfl
      map_smul' c φ := rfl }
  have hev : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ hφ
    ext1
    exact LinearMap.ext_on_range he fun i ↦ congrFun hφ i
  let L := ev ∘ₗ (functor Φ).mapLinearMap k ∘ₗ fromSminusLinear X
  have hL : Function.Injective L :=
    hev.comp ((functor Φ).map_injective.comp (fromSminusLinear_injective X))
  have hWF := L.rank_le_of_injective hL
  have : Module.Free k (RestrictScalars k A ((functor Φ).obj X)) :=
    @Module.Free.of_divisionRing k (RestrictScalars k A ((functor Φ).obj X)) _ _
      (RestrictScalars.module k A ((functor Φ).obj X))
  rw [rank_fun_eq_lift_mul] at hWF
  have hVW : Module.rank k X.obj.V ≤ Module.rank k X.obj.W + Module.rank k X.obj.W := by
    have := (LinearMap.prod X.obj.a.hom X.obj.b.hom).rank_le_of_injective ?_
    · rwa [rank_prod'] at this
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact (inD_iff _).1 X.2 v (congrArg Prod.fst hv) (congrArg Prod.snd hv)
  exact cardinal_aux n hX hVW (by simpa [Statement.dim] using hWF)

/-- Proposition 2.3: `dim F(T) = dim T` for infinite-dimensional `T`. -/
theorem dim_eq (hfin : ∀ X : Dfin k, Module.Finite k (RestrictScalars k A (Φ.obj X)))
    [Φ.Faithful] [Φ.Additive] [Φ.Linear k] (X : D k) (hX : Cardinal.aleph0 ≤ X.obj.dim) :
    Statement.dim k A ((functor Φ).obj X) = X.obj.dim :=
  le_antisymm (dim_le Φ hfin X hX) (le_dim Φ hfin X hX)

end Dimension

end Extension

end LargeIndecomposable
