module

public import LargeIndecomposable.Statement

/-!
# Kronecker modules: basic API

Kronecker modules are functors `WalkingParallelPair ⥤ ModuleCat k`
(`Statement.Kron`). This file provides constructors, componentwise
extensionality, the subcategory `C` (Definition 2.1), Lemma 2.2(1), and
subrepresentations `Kron.Sub`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair WalkingParallelPairHom

universe u

variable {k : Type u} [Field k]

namespace Kron

/-- The Kronecker module `(V, W; a, b)`. -/
abbrev mk (V W : ModuleCat.{u} k) (a b : V ⟶ W) : Kron k := parallelPair a b

/-- A morphism `(g, h)` of Kronecker modules. -/
abbrev homMk {X Y : Kron k} (g : X.V ⟶ Y.V) (h : X.W ⟶ Y.W)
    (ha : X.a ≫ h = g ≫ Y.a) (hb : X.b ≫ h = g ≫ Y.b) : X ⟶ Y :=
  parallelPairHomMk g h ha hb

@[reassoc]
lemma a_comp {X Y : Kron k} (f : X ⟶ Y) : X.a ≫ f.app one = f.app zero ≫ Y.a :=
  f.naturality left

@[reassoc]
lemma b_comp {X Y : Kron k} (f : X ⟶ Y) : X.b ≫ f.app one = f.app zero ≫ Y.b :=
  f.naturality right

lemma a_apply {X Y : Kron k} (f : X ⟶ Y) (v : X.V) :
    (f.app one).hom (X.a.hom v) = Y.a.hom ((f.app zero).hom v) := by
  rw [← ModuleCat.comp_apply, a_comp, ModuleCat.comp_apply]

lemma b_apply {X Y : Kron k} (f : X ⟶ Y) (v : X.V) :
    (f.app one).hom (X.b.hom v) = Y.b.hom ((f.app zero).hom v) := by
  rw [← ModuleCat.comp_apply, b_comp, ModuleCat.comp_apply]

lemma hom_ext {X Y : Kron k} {f f' : X ⟶ Y} (h0 : f.app zero = f'.app zero)
    (h1 : f.app one = f'.app one) : f = f' := by
  ext j : 2
  cases j
  · exact h0
  · exact h1

end Kron

/-! ### The subcategories `D` and `C` -/

lemma inD_iff (X : Kron k) :
    InD X ↔ ∀ v : X.V, X.a.hom v = 0 → X.b.hom v = 0 → v = 0 := by
  unfold InD
  rw [eq_bot_iff]
  constructor
  · intro h v ha hb
    simpa using h ⟨ha, hb⟩
  · rintro h v ⟨ha, hb⟩
    exact (h v ha hb).symm ▸ Submodule.zero_mem _

/-- Definition 2.1: the modules of `D` with `a(V) + b(V) = W`, equivalently
(after (2.3)) the Kronecker modules with neither simple module as a direct
summand. -/
def InC : ObjectProperty (Kron k) :=
  fun X ↦ InD X ∧ LinearMap.range X.a.hom ⊔ LinearMap.range X.b.hom = ⊤

lemma InC.inD {X : Kron k} (h : InC X) : InD X := h.1

/-- Lemma 2.2(1), first half: on `C`, a morphism is determined by its
component at the source vertex. -/
lemma hom_eq_zero_of_app_zero {X Y : Kron k} (hX : InC X) (f : X ⟶ Y)
    (h : f.app zero = 0) : f = 0 := by
  have h1 : f.app one = 0 := by
    ext w
    have hw : w ∈ LinearMap.range X.a.hom ⊔ LinearMap.range X.b.hom := hX.2 ▸ trivial
    obtain ⟨x, ⟨v, rfl⟩, y, ⟨v', rfl⟩, rfl⟩ := Submodule.mem_sup.1 hw
    simp [h]
  exact Kron.hom_ext (by simpa using h) (by simpa using h1)

/-- Lemma 2.2(1), second half: into a module of `D`, a morphism is determined
by its component at the target vertex. -/
lemma hom_eq_zero_of_app_one {X Y : Kron k} (hY : InD Y) (f : X ⟶ Y)
    (h : f.app one = 0) : f = 0 := by
  have h0 : f.app zero = 0 := by
    ext v
    refine (inD_iff Y).1 hY _ ?_ ?_
    · rw [← Kron.a_apply, h]; simp
    · rw [← Kron.b_apply, h]; simp
  exact Kron.hom_ext (by simpa using h0) (by simpa using h)

/-! ### Subrepresentations -/

/-- A subrepresentation of a Kronecker module: subspaces `V₀ ⊆ V`, `W₀ ⊆ W`
with `a(V₀) + b(V₀) ⊆ W₀`. -/
@[ext]
structure Kron.Sub (X : Kron k) where
  /-- The subspace at the source vertex. -/
  V : Submodule k X.V
  /-- The subspace at the target vertex. -/
  W : Submodule k X.W
  map_a : ∀ v ∈ V, X.a.hom v ∈ W
  map_b : ∀ v ∈ V, X.b.hom v ∈ W

namespace Kron.Sub

variable {X : Kron k}

instance : PartialOrder (Kron.Sub X) where
  le U U' := U.V ≤ U'.V ∧ U.W ≤ U'.W
  le_refl U := ⟨le_rfl, le_rfl⟩
  le_trans U U' U'' h h' := ⟨h.1.trans h'.1, h.2.trans h'.2⟩
  le_antisymm U U' h h' := Kron.Sub.ext (le_antisymm h.1 h'.1) (le_antisymm h.2 h'.2)

instance : Max (Kron.Sub X) where
  max U U' := ⟨U.V ⊔ U'.V, U.W ⊔ U'.W,
    fun v hv ↦ by
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
      rw [map_add]
      exact Submodule.add_mem_sup (U.map_a x hx) (U'.map_a y hy),
    fun v hv ↦ by
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
      rw [map_add]
      exact Submodule.add_mem_sup (U.map_b x hx) (U'.map_b y hy)⟩

instance : Bot (Kron.Sub X) where
  bot := ⟨⊥, ⊥, fun v hv ↦ by simp_all, fun v hv ↦ by simp_all⟩

lemma le_max_left' (U U' : Kron.Sub X) : U ≤ max U U' := ⟨le_sup_left, le_sup_left⟩

lemma le_max_right' (U U' : Kron.Sub X) : U' ≤ max U U' := ⟨le_sup_right, le_sup_right⟩

/-- The Kronecker module of a subrepresentation. -/
abbrev toKron (U : Kron.Sub X) : Kron k :=
  Kron.mk (ModuleCat.of k U.V) (ModuleCat.of k U.W)
    (ModuleCat.ofHom (X.a.hom.restrict U.map_a)) (ModuleCat.ofHom (X.b.hom.restrict U.map_b))

/-- The inclusion of a subrepresentation. -/
def ι (U : Kron.Sub X) : U.toKron ⟶ X :=
  Kron.homMk (ModuleCat.ofHom U.V.subtype) (ModuleCat.ofHom U.W.subtype) rfl rfl

@[simp]
lemma ι_app_zero_apply (U : Kron.Sub X) (v : U.V) : ((ι U).app zero).hom v = v := rfl

@[simp]
lemma ι_app_one_apply (U : Kron.Sub X) (w : U.W) : ((ι U).app one).hom w = w := rfl

/-- The inclusion between nested subrepresentations. -/
def homOfLE {U U' : Kron.Sub X} (h : U ≤ U') : U.toKron ⟶ U'.toKron :=
  Kron.homMk (ModuleCat.ofHom (Submodule.inclusion h.1))
    (ModuleCat.ofHom (Submodule.inclusion h.2)) rfl rfl

@[reassoc (attr := simp)]
lemma homOfLE_ι {U U' : Kron.Sub X} (h : U ≤ U') : homOfLE h ≫ ι U' = ι U := by
  apply Kron.hom_ext <;> rfl

@[simp]
lemma homOfLE_refl (U : Kron.Sub X) : homOfLE (le_refl U) = 𝟙 _ := by
  apply Kron.hom_ext <;> rfl

@[reassoc (attr := simp)]
lemma homOfLE_comp {U U' U'' : Kron.Sub X} (h : U ≤ U') (h' : U' ≤ U'') :
    homOfLE h ≫ homOfLE h' = homOfLE (h.trans h') := by
  apply Kron.hom_ext <;> rfl

/-- A subrepresentation is finite-dimensional if both of its subspaces are. -/
def IsFin (U : Kron.Sub X) : Prop := FiniteDimensional k U.V ∧ FiniteDimensional k U.W

lemma isFin_bot : IsFin (⊥ : Kron.Sub X) :=
  ⟨by change FiniteDimensional k (⊥ : Submodule k X.V); infer_instance,
   by change FiniteDimensional k (⊥ : Submodule k X.W); infer_instance⟩

lemma IsFin.max {U U' : Kron.Sub X} (h : U.IsFin) (h' : U'.IsFin) : (max U U').IsFin := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  exact ⟨Submodule.finiteDimensional_sup _ _, Submodule.finiteDimensional_sup _ _⟩

lemma isFin_iff (U : Kron.Sub X) : U.IsFin ↔ U.toKron.IsFiniteDimensional := Iff.rfl

end Kron.Sub

end LargeIndecomposable

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair WalkingParallelPairHom

universe u

variable {k : Type u} [Field k]

namespace Kron.Sub

variable {X Y Z : Kron k}

/-- The image of a subrepresentation under a morphism. -/
def map (f : X ⟶ Y) (U : Kron.Sub X) : Kron.Sub Y where
  V := U.V.map (f.app zero).hom
  W := U.W.map (f.app one).hom
  map_a := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨_, U.map_a v hv, Kron.a_apply f v⟩
  map_b := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨_, U.map_b v hv, Kron.b_apply f v⟩

lemma IsFin.map {U : Kron.Sub X} (h : U.IsFin) (f : X ⟶ Y) : (U.map f).IsFin := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨Module.Finite.map U.V (f.app zero).hom, Module.Finite.map U.W (f.app one).hom⟩

lemma map_mono (f : X ⟶ Y) {U U' : Kron.Sub X} (h : U ≤ U') : U.map f ≤ U'.map f :=
  ⟨Submodule.map_mono h.1, Submodule.map_mono h.2⟩

/-- The restriction of `f : X ⟶ Y` to subrepresentations `U` and `U'` with
`f(U) ⊆ U'`. -/
def restrict (f : X ⟶ Y) (U : Kron.Sub X) (U' : Kron.Sub Y) (h : U.map f ≤ U') :
    U.toKron ⟶ U'.toKron :=
  Kron.homMk
    (ModuleCat.ofHom ((f.app zero).hom.restrict fun v hv ↦ h.1 ⟨v, hv, rfl⟩))
    (ModuleCat.ofHom ((f.app one).hom.restrict fun w hw ↦ h.2 ⟨w, hw, rfl⟩))
    (by ext v; exact Subtype.ext (Kron.a_apply f v.1))
    (by ext v; exact Subtype.ext (Kron.b_apply f v.1))

@[simp]
lemma restrict_app_zero_apply (f : X ⟶ Y) (U : Kron.Sub X) (U' : Kron.Sub Y)
    (h : U.map f ≤ U') (v : U.V) :
    (Subtype.val (p := (· ∈ U'.V)) (((restrict f U U' h).app zero).hom v)) = (f.app zero).hom v := rfl

@[simp]
lemma restrict_app_one_apply (f : X ⟶ Y) (U : Kron.Sub X) (U' : Kron.Sub Y)
    (h : U.map f ≤ U') (w : U.W) :
    (Subtype.val (p := (· ∈ U'.W)) (((restrict f U U' h).app one).hom w)) = (f.app one).hom w := rfl

@[reassoc (attr := simp)]
lemma restrict_ι (f : X ⟶ Y) (U : Kron.Sub X) (U' : Kron.Sub Y) (h : U.map f ≤ U') :
    restrict f U U' h ≫ ι U' = ι U ≫ f := by
  apply Kron.hom_ext <;> rfl

lemma restrict_id (U U' : Kron.Sub X) (h : U.map (𝟙 X) ≤ U') :
    restrict (𝟙 X) U U' h = homOfLE (le_trans (by
      refine ⟨fun v hv ↦ ⟨v, hv, rfl⟩, fun w hw ↦ ⟨w, hw, rfl⟩⟩) h) := by
  apply Kron.hom_ext <;> rfl

@[reassoc]
lemma restrict_comp (f : X ⟶ Y) (g : Y ⟶ Z) (U : Kron.Sub X) (U' : Kron.Sub Y)
    (U'' : Kron.Sub Z) (h : U.map f ≤ U') (h' : U'.map g ≤ U'') (h'' : U.map (f ≫ g) ≤ U'') :
    restrict (f ≫ g) U U'' h'' = restrict f U U' h ≫ restrict g U' U'' h' := by
  apply Kron.hom_ext <;> rfl

@[reassoc]
lemma homOfLE_restrict (f : X ⟶ Y) {U₁ U₂ : Kron.Sub X} (hU : U₁ ≤ U₂) (U' : Kron.Sub Y)
    (h : U₂.map f ≤ U') :
    homOfLE hU ≫ restrict f U₂ U' h = restrict f U₁ U' ((map_mono f hU).trans h) := by
  apply Kron.hom_ext <;> rfl

@[reassoc]
lemma restrict_homOfLE (f : X ⟶ Y) (U : Kron.Sub X) {U' U'' : Kron.Sub Y} (h : U.map f ≤ U')
    (hU : U' ≤ U'') :
    restrict f U U' h ≫ homOfLE hU = restrict f U U'' (h.trans hU) := by
  apply Kron.hom_ext <;> rfl

lemma map_id_le (U : Kron.Sub X) : U.map (𝟙 X) ≤ U :=
  ⟨by rintro _ ⟨v, hv, rfl⟩; exact hv, by rintro _ ⟨v, hv, rfl⟩; exact hv⟩

lemma map_comp_le (f : X ⟶ Y) (g : Y ⟶ Z) (U : Kron.Sub X) :
    U.map (f ≫ g) ≤ (U.map f).map g :=
  ⟨by rintro _ ⟨v, hv, rfl⟩; exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩,
    by rintro _ ⟨v, hv, rfl⟩; exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩⟩

/-- The whole module as a subrepresentation. -/
def top (X : Kron k) : Kron.Sub X := ⟨⊤, ⊤, fun _ _ ↦ trivial, fun _ _ ↦ trivial⟩

lemma le_top (U : Kron.Sub X) : U ≤ top X := ⟨_root_.le_top, _root_.le_top⟩

lemma isFin_top (h : X.IsFiniteDimensional) : (top X).IsFin := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨inferInstanceAs (FiniteDimensional k (⊤ : Submodule k X.V)),
    inferInstanceAs (FiniteDimensional k (⊤ : Submodule k X.W))⟩

/-- The subrepresentation generated by finite sets of vectors. -/
def span (S : Set X.V) (T : Set X.W) : Kron.Sub X where
  V := Submodule.span k S
  W := Submodule.span k (T ∪ X.a.hom '' S ∪ X.b.hom '' S)
  map_a := by
    intro v hv
    have : Submodule.map X.a.hom (Submodule.span k S) ≤
        Submodule.span k (T ∪ X.a.hom '' S ∪ X.b.hom '' S) := by
      rw [Submodule.map_span]
      exact Submodule.span_mono (by intro x hx; left; right; exact hx)
    exact this ⟨v, hv, rfl⟩
  map_b := by
    intro v hv
    have : Submodule.map X.b.hom (Submodule.span k S) ≤
        Submodule.span k (T ∪ X.a.hom '' S ∪ X.b.hom '' S) := by
      rw [Submodule.map_span]
      exact Submodule.span_mono (by intro x hx; right; exact hx)
    exact this ⟨v, hv, rfl⟩

lemma isFin_span (S : Set X.V) (T : Set X.W) (hS : S.Finite) (hT : T.Finite) :
    (span S T).IsFin :=
  ⟨FiniteDimensional.span_of_finite k hS,
    FiniteDimensional.span_of_finite k ((hT.union (hS.image _)).union (hS.image _))⟩

lemma subset_span_V (S : Set X.V) (T : Set X.W) : S ⊆ (span S T).V := Submodule.subset_span

lemma subset_span_W (S : Set X.V) (T : Set X.W) : T ⊆ (span S T).W :=
  fun _ h ↦ Submodule.subset_span (Or.inl (Or.inl h))

end Kron.Sub

/-! ### Finite-dimensional subrepresentations -/

/-- The directed poset of finite-dimensional subrepresentations. -/
abbrev Kron.FinSub (X : Kron k) : Type u := {U : Kron.Sub X // U.IsFin}

namespace Kron.FinSub

variable {X Y : Kron k}

instance : PartialOrder (Kron.FinSub X) := Subtype.partialOrder _

instance : IsDirectedOrder (Kron.FinSub X) where
  directed U U' := ⟨⟨max U.1 U'.1, U.2.max U'.2⟩, Sub.le_max_left' _ _, Sub.le_max_right' _ _⟩

instance : Nonempty (Kron.FinSub X) := ⟨⟨⊥, Sub.isFin_bot⟩⟩

/-- The image of a finite-dimensional subrepresentation. -/
def map (f : X ⟶ Y) (U : Kron.FinSub X) : Kron.FinSub Y := ⟨U.1.map f, U.2.map f⟩

lemma map_mono (f : X ⟶ Y) {U U' : Kron.FinSub X} (h : U ≤ U') : map f U ≤ map f U' :=
  Sub.map_mono f h

/-- Every finite set of vectors lies in a finite-dimensional
subrepresentation (Lemma 2.2(3)). -/
lemma exists_of_finite (S : Set X.V) (T : Set X.W) (hS : S.Finite) (hT : T.Finite) :
    ∃ U : Kron.FinSub X, S ⊆ U.1.V ∧ T ⊆ U.1.W :=
  ⟨⟨Sub.span S T, Sub.isFin_span S T hS hT⟩, Sub.subset_span_V S T, Sub.subset_span_W S T⟩

end Kron.FinSub

/-! ### The category `D_fin` -/

/-- Finite-dimensional modules of `D`. -/
def InDfin : ObjectProperty (Kron k) := fun X ↦ InD X ∧ X.IsFiniteDimensional

variable (k) in
/-- The category `D_fin`. -/
abbrev Dfin : Type (u + 1) := (InDfin (k := k)).FullSubcategory

lemma inD_of_mono {X Y : Kron k} (hY : InD Y) (f : X ⟶ Y)
    (hf : Function.Injective (f.app zero).hom) : InD X := by
  rw [inD_iff] at hY ⊢
  intro v ha hb
  apply hf
  rw [map_zero]
  apply hY
  · rw [← Kron.a_apply, ha, map_zero]
  · rw [← Kron.b_apply, hb, map_zero]

lemma Kron.Sub.inD {X : Kron k} (hX : InD X) (U : Kron.Sub X) : InD U.toKron :=
  inD_of_mono hX (Kron.Sub.ι U) Subtype.val_injective

end LargeIndecomposable
