module

public import LargeIndecomposable.KroneckerModules.Subcategories

/-!
# Gluing morphisms along the subrepresentations `T_{V₀}`

For `X ∈ C`, the subrepresentations `T_{V₀} = (V₀, a(V₀) + b(V₀))` with
`V₀ ⊆ V` finite-dimensional are cofinal among the finite-dimensional
subrepresentations (Lemma 2.2(3)). A compatible family of morphisms
`T_{V₀} → Z` glues to a unique morphism `X → Z`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair WalkingParallelPairHom

universe u

variable {k : Type u} [Field k]

/-- Finite-dimensional subspaces of the source space of a Kronecker module. -/
abbrev Kron.FinV (X : Kron k) : Type u := {V₀ : Submodule k X.V // FiniteDimensional k V₀}

namespace Kron.FinV

variable {X : Kron k}

instance : PartialOrder (Kron.FinV X) := Subtype.partialOrder _

instance (V₀ : Kron.FinV X) : FiniteDimensional k V₀.1 := V₀.2

/-- The supremum of two finite-dimensional subspaces. -/
def sup (V₀ V₁ : Kron.FinV X) : Kron.FinV X :=
  ⟨V₀.1 ⊔ V₁.1, Submodule.finiteDimensional_sup _ _⟩

lemma le_sup_left (V₀ V₁ : Kron.FinV X) : V₀ ≤ sup V₀ V₁ := _root_.le_sup_left (a := V₀.1)

lemma le_sup_right (V₀ V₁ : Kron.FinV X) : V₁ ≤ sup V₀ V₁ := _root_.le_sup_right (a := V₀.1)

/-- The line spanned by a vector. -/
def span (v : X.V) : Kron.FinV X := ⟨Submodule.span k {v}, inferInstance⟩

lemma mem_span (v : X.V) : v ∈ (span v).1 := Submodule.mem_span_singleton_self v

/-- The subrepresentation `T_{V₀}`. -/
abbrev sub (V₀ : Kron.FinV X) : Kron.Sub X := Kron.Sub.ofV V₀.1

/-- `T_{V₀}` as a finite-dimensional subrepresentation. -/
def toFinSub (V₀ : Kron.FinV X) : Kron.FinSub X := ⟨sub V₀, Kron.Sub.isFin_ofV V₀.1⟩

lemma sub_mono {V₀ V₁ : Kron.FinV X} (h : V₀ ≤ V₁) : sub V₀ ≤ sub V₁ := Kron.Sub.ofV_mono h

lemma toFinSub_mono {V₀ V₁ : Kron.FinV X} (h : V₀ ≤ V₁) : toFinSub V₀ ≤ toFinSub V₁ :=
  Kron.Sub.ofV_mono h

lemma le_sub_of_mem {V₀ : Kron.FinV X} {v : X.V} (hv : v ∈ V₀.1) : span v ≤ V₀ :=
  (Submodule.span_singleton_le_iff_mem v V₀.1).2 hv

/-- Every vector of `W` lies in some `T_{V₀}` when `X ∈ C`. -/
lemma exists_mem_W (hX : InC X) (w : X.W) : ∃ V₀ : Kron.FinV X, w ∈ (sub V₀).W := by
  have hw : w ∈ LinearMap.range X.a.hom ⊔ LinearMap.range X.b.hom := hX.2 ▸ trivial
  obtain ⟨_, ⟨v, rfl⟩, _, ⟨v', rfl⟩, rfl⟩ := Submodule.mem_sup.1 hw
  let V₀ : Kron.FinV X := sup (span v) (span v')
  refine ⟨V₀, Submodule.add_mem_sup ⟨v, ?_, rfl⟩ ⟨v', ?_, rfl⟩⟩
  · exact le_sup_left (span v) (span v') (mem_span v)
  · exact le_sup_right (span v) (span v') (mem_span v')

/-- Every finite-dimensional subrepresentation of `X ∈ C` lies in some
`T_{V₀}` (Lemma 2.2(3)). -/
lemma exists_le (hX : InC X) (U : Kron.FinSub X) : ∃ V₀ : Kron.FinV X, U ≤ toFinSub V₀ := by
  obtain ⟨V₀, h, hle⟩ := Kron.FinSub.exists_le_ofV hX U
  exact ⟨⟨V₀, h⟩, hle⟩

end Kron.FinV

namespace Kron

variable {X Z : Kron k}

/-- A family of morphisms out of the subrepresentations `T_{V₀}`, compatible
with the inclusions. -/
structure CompatFamily (X Z : Kron k) where
  /-- The morphism on `T_{V₀}`. -/
  s : ∀ V₀ : Kron.FinV X, (Kron.FinV.sub V₀).toKron ⟶ Z
  compat : ∀ {V₀ V₁ : Kron.FinV X} (h : V₀ ≤ V₁),
    Kron.Sub.homOfLE (Kron.FinV.sub_mono h) ≫ s V₁ = s V₀

namespace CompatFamily

variable (σ : CompatFamily X Z)

lemma app_zero_eq {V₀ V₁ : Kron.FinV X} (h : V₀ ≤ V₁) (v : X.V) (h₀ : v ∈ V₀.1) :
    ((σ.s V₀).app zero).hom ⟨v, h₀⟩ = ((σ.s V₁).app zero).hom ⟨v, h h₀⟩ := by
  rw [← σ.compat h]; rfl

lemma app_one_eq {V₀ V₁ : Kron.FinV X} (h : V₀ ≤ V₁) (w : X.W) (h₀ : w ∈ (Kron.FinV.sub V₀).W) :
    ((σ.s V₀).app one).hom ⟨w, h₀⟩ =
      ((σ.s V₁).app one).hom ⟨w, (Kron.FinV.sub_mono h).2 h₀⟩ := by
  rw [← σ.compat h]; rfl

/-- Values at the source vertex do not depend on the chosen `V₀`. -/
lemma app_zero_eq' (V₀ V₁ : Kron.FinV X) (v : X.V) (h₀ : v ∈ V₀.1) (h₁ : v ∈ V₁.1) :
    ((σ.s V₀).app zero).hom ⟨v, h₀⟩ = ((σ.s V₁).app zero).hom ⟨v, h₁⟩ := by
  rw [σ.app_zero_eq (Kron.FinV.le_sup_left V₀ V₁), σ.app_zero_eq (Kron.FinV.le_sup_right V₀ V₁)]

/-- Values at the target vertex do not depend on the chosen `V₀`. -/
lemma app_one_eq' (V₀ V₁ : Kron.FinV X) (w : X.W) (h₀ : w ∈ (Kron.FinV.sub V₀).W)
    (h₁ : w ∈ (Kron.FinV.sub V₁).W) :
    ((σ.s V₀).app one).hom ⟨w, h₀⟩ = ((σ.s V₁).app one).hom ⟨w, h₁⟩ := by
  rw [σ.app_one_eq (Kron.FinV.le_sup_left V₀ V₁), σ.app_one_eq (Kron.FinV.le_sup_right V₀ V₁)]

variable (hX : InC X)

/-- The glued map at the source vertex. -/
def glue0 : X.V →ₗ[k] Z.V where
  toFun v := ((σ.s (Kron.FinV.span v)).app zero).hom ⟨v, Kron.FinV.mem_span v⟩
  map_add' v v' := by
    let V₀ := Kron.FinV.sup (Kron.FinV.span v) (Kron.FinV.span v')
    have hv := Kron.FinV.le_sup_left (Kron.FinV.span v) (Kron.FinV.span v') (Kron.FinV.mem_span v)
    have hv' := Kron.FinV.le_sup_right (Kron.FinV.span v) (Kron.FinV.span v')
      (Kron.FinV.mem_span v')
    rw [σ.app_zero_eq' _ V₀ v _ hv, σ.app_zero_eq' _ V₀ v' _ hv',
      σ.app_zero_eq' _ V₀ (v + v') _ (V₀.1.add_mem hv hv'), ← map_add]
    rfl
  map_smul' c v := by
    rw [σ.app_zero_eq' _ (Kron.FinV.span v) (c • v) _
      ((Kron.FinV.span v).1.smul_mem c (Kron.FinV.mem_span v)), RingHom.id_apply, ← map_smul]
    rfl

lemma glue0_apply (V₀ : Kron.FinV X) (v : X.V) (h : v ∈ V₀.1) :
    σ.glue0 v = ((σ.s V₀).app zero).hom ⟨v, h⟩ :=
  σ.app_zero_eq' _ _ v _ h

include hX in
/-- The glued map at the target vertex. -/
def glue1 : X.W →ₗ[k] Z.W where
  toFun w := ((σ.s (Kron.FinV.exists_mem_W hX w).choose).app one).hom
    ⟨w, (Kron.FinV.exists_mem_W hX w).choose_spec⟩
  map_add' w w' := by
    set V₁ := (Kron.FinV.exists_mem_W hX w).choose
    set V₂ := (Kron.FinV.exists_mem_W hX w').choose
    let V₀ := Kron.FinV.sup V₁ V₂
    have hw : w ∈ (Kron.FinV.sub V₀).W := (Kron.FinV.sub_mono (Kron.FinV.le_sup_left V₁ V₂)).2
      (Kron.FinV.exists_mem_W hX w).choose_spec
    have hw' : w' ∈ (Kron.FinV.sub V₀).W := (Kron.FinV.sub_mono (Kron.FinV.le_sup_right V₁ V₂)).2
      (Kron.FinV.exists_mem_W hX w').choose_spec
    rw [σ.app_one_eq' _ V₀ w _ hw, σ.app_one_eq' _ V₀ w' _ hw',
      σ.app_one_eq' _ V₀ (w + w') _ ((Kron.FinV.sub V₀).W.add_mem hw hw'), ← map_add]
    rfl
  map_smul' c w := by
    have h := (Kron.FinV.exists_mem_W hX w).choose_spec
    rw [σ.app_one_eq' _ (Kron.FinV.exists_mem_W hX w).choose (c • w) _
      ((Kron.FinV.sub _).W.smul_mem c h), RingHom.id_apply, ← map_smul]
    rfl

lemma glue1_apply (V₀ : Kron.FinV X) (w : X.W) (h : w ∈ (Kron.FinV.sub V₀).W) :
    σ.glue1 hX w = ((σ.s V₀).app one).hom ⟨w, h⟩ :=
  σ.app_one_eq' _ _ w _ h

/-- The glued morphism `X → Z`. -/
def glue : X ⟶ Z :=
  Kron.homMk (ModuleCat.ofHom σ.glue0) (ModuleCat.ofHom (σ.glue1 hX))
    (by
      ext v
      have h : X.a.hom v ∈ (Kron.FinV.sub (Kron.FinV.span v)).W :=
        (Kron.FinV.sub (Kron.FinV.span v)).map_a v (Kron.FinV.mem_span v)
      change σ.glue1 hX (X.a.hom v) = Z.a.hom (σ.glue0 v)
      rw [σ.glue1_apply hX _ _ h, σ.glue0_apply _ v (Kron.FinV.mem_span v), ← Kron.a_apply]
      rfl)
    (by
      ext v
      have h : X.b.hom v ∈ (Kron.FinV.sub (Kron.FinV.span v)).W :=
        (Kron.FinV.sub (Kron.FinV.span v)).map_b v (Kron.FinV.mem_span v)
      change σ.glue1 hX (X.b.hom v) = Z.b.hom (σ.glue0 v)
      rw [σ.glue1_apply hX _ _ h, σ.glue0_apply _ v (Kron.FinV.mem_span v), ← Kron.b_apply]
      rfl)

@[simp]
lemma ι_glue (V₀ : Kron.FinV X) : (Kron.FinV.sub V₀).ι ≫ σ.glue hX = σ.s V₀ := by
  apply Kron.hom_ext
  · ext ⟨v, hv⟩
    exact (σ.glue0_apply V₀ v hv)
  · ext ⟨w, hw⟩
    exact (σ.glue1_apply hX V₀ w hw)

end CompatFamily

/-- Morphisms out of `X ∈ C` are determined on the subrepresentations
`T_{V₀}`. -/
lemma hom_ext_finV {g g' : X ⟶ Z} (hX : InC X)
    (h : ∀ V₀ : Kron.FinV X, (Kron.FinV.sub V₀).ι ≫ g = (Kron.FinV.sub V₀).ι ≫ g') : g = g' := by
  apply Kron.hom_ext
  · ext v
    exact congrArg (fun φ : (Kron.FinV.sub (Kron.FinV.span v)).toKron ⟶ Z ↦
      ((φ.app zero).hom ⟨v, Kron.FinV.mem_span v⟩)) (h (Kron.FinV.span v))
  · ext w
    obtain ⟨V₀, hw⟩ := Kron.FinV.exists_mem_W hX w
    exact congrArg (fun φ : (Kron.FinV.sub V₀).toKron ⟶ Z ↦ ((φ.app one).hom ⟨w, hw⟩)) (h V₀)

end Kron

end LargeIndecomposable
