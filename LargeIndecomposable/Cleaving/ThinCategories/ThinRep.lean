module

public import LargeIndecomposable.Cleaving.ThinCategories.Thin
public import LargeIndecomposable.Cleaving.Functors.Cleaving

/-!
# Representations of thin ray categories

A representation of a thin ray category `ThinCat T` is a family of vector
spaces `sp x` with maps `map x y : sp x → sp y` for `le x y`, compatible with
composition (`map y z ∘ map x y = map x z` if the composite is nonzero, `0`
otherwise). Its total space is a module over the linearization
(`RayCat.ThinRep.Tot`). A module map between total spaces is given by its
vertex components, which commute with the maps (`RayCat.ThinRep.comp_map`);
this reduces brick and isomorphism questions to linear algebra.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayQuiver

universe u

namespace RayCat

variable {V : Type} [Fintype V] [DecidableEq V] {T : ThinData V} (k : Type u) [Field k]

open Classical in
variable (T) in
/-- A representation of `ThinCat T`. -/
structure ThinRep where
  sp : V → ModuleCat.{u} k
  map : ∀ x y, T.le x y → (sp x →ₗ[k] sp y)
  map_id : ∀ x, map x x (T.refl x) = LinearMap.id
  map_comp : ∀ x y z (h : T.le x y) (h' : T.le y z),
    map y z h' ∘ₗ map x y h = if hn : T.nz x y z then map x z (T.nz_le x y z h h' hn) else 0

namespace ThinRep

variable {k} (R : ThinRep T k)

/-- The total space. -/
@[ext]
structure Tot where
  /-- The components. -/
  val : ∀ x : V, R.sp x

namespace Tot

variable {R}

instance : Zero R.Tot := ⟨⟨fun _ ↦ 0⟩⟩
instance : Add R.Tot := ⟨fun φ ψ ↦ ⟨fun v ↦ φ.val v + ψ.val v⟩⟩
instance : Neg R.Tot := ⟨fun φ ↦ ⟨fun v ↦ -φ.val v⟩⟩
instance : Sub R.Tot := ⟨fun φ ψ ↦ ⟨fun v ↦ φ.val v - ψ.val v⟩⟩
instance : SMul ℕ R.Tot := ⟨fun n φ ↦ ⟨fun v ↦ n • φ.val v⟩⟩
instance : SMul ℤ R.Tot := ⟨fun n φ ↦ ⟨fun v ↦ n • φ.val v⟩⟩
instance : SMul k R.Tot := ⟨fun a φ ↦ ⟨fun v ↦ a • φ.val v⟩⟩

@[simp] lemma zero_val (v : V) : (0 : R.Tot).val v = 0 := rfl
@[simp] lemma add_val (φ ψ : R.Tot) (v : V) : (φ + ψ).val v = φ.val v + ψ.val v := rfl
@[simp] lemma smul_val (a : k) (φ : R.Tot) (v : V) : (a • φ).val v = a • φ.val v := rfl

lemma val_injective : Function.Injective (Tot.val : R.Tot → _) := fun _ _ h ↦ Tot.ext h

instance : AddCommGroup R.Tot :=
  val_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance : Module k R.Tot :=
  val_injective.module k (⟨⟨Tot.val, rfl⟩, fun _ _ ↦ rfl⟩ : R.Tot →+ _) fun _ _ ↦ rfl

end Tot

/-- The component map of a morphism of `ThinCat T`. -/
def homMap {X Y : ThinCat T} : (X ⟶ Y) → (R.sp X.as →ₗ[k] R.sp Y.as)
  | none => 0
  | some ⟨_, h⟩ => R.map X.as Y.as h

/-- The action of a morphism on the total space. -/
def act {X Y : ThinCat T} (f : X ⟶ Y) : Module.End k R.Tot where
  toFun φ := ⟨Pi.single Y.as (R.homMap f (φ.val X.as))⟩
  map_add' φ ψ := by
    ext v
    simp only [Tot.add_val, map_add, Pi.single_add, Pi.add_apply]
  map_smul' a φ := by
    ext v
    simp only [Tot.smul_val, map_smul, Pi.single_smul, Pi.smul_apply, RingHom.id_apply]

lemma act_val {X Y : ThinCat T} (f : X ⟶ Y) (φ : R.Tot) (v : V) :
    (R.act f φ).val v = Pi.single (M := fun v ↦ R.sp v) Y.as (R.homMap f (φ.val X.as)) v := rfl

lemma homMap_comp {X Y Z : ThinCat T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    R.homMap (f ≫ g) = R.homMap g ∘ₗ R.homMap f := by
  rw [ThinCat.comp_def]
  rcases f with _ | ⟨⟨⟩, hf⟩
  · simp [ThinHom.comp_none_left, homMap]
  rcases g with _ | ⟨⟨⟩, hg⟩
  · rw [ThinHom.comp_none_right]; simp [homMap]
  rw [ThinHom.comp_some, homMap, homMap, R.map_comp]
  split_ifs <;> rfl

lemma homMap_id (X : ThinCat T) : R.homMap (𝟙 X) = LinearMap.id := R.map_id X.as

lemma act_zero {X Y : ThinCat T} : R.act (0 : X ⟶ Y) = 0 := by
  refine LinearMap.ext fun φ ↦ Tot.ext (funext fun v ↦ ?_)
  rw [act_val]
  simp [homMap, show (0 : X ⟶ Y) = (none : ThinHom T _ _) from rfl]

/-- The representation of the linearization on the total space. -/
def rep : Linearization (ThinCat T) k →ₐ[k] Module.End k R.Tot :=
  linLift k (fun f ↦ R.act f) R.act_zero
    (by
      intro X Y Z f g
      refine LinearMap.ext fun φ ↦ Tot.ext (funext fun v ↦ ?_)
      simp only [Module.End.mul_apply, act_val, homMap_comp, LinearMap.comp_apply,
        Pi.single_eq_same])
    (by
      intro X Y Y' Z f g hY
      refine LinearMap.ext fun φ ↦ Tot.ext (funext fun v ↦ ?_)
      have : Y'.as ≠ Y.as := fun h ↦ hY (ThinCat.ext_as h.symm)
      simp only [Module.End.mul_apply, act_val, Pi.single_eq_of_ne this, map_zero,
        Pi.single_zero, LinearMap.zero_apply, Tot.zero_val]
      rfl)
    (by
      refine LinearMap.ext fun φ ↦ Tot.ext (funext fun v ↦ ?_)
      rw [LinearMap.sum_apply]
      rw [show (∑ X : ThinCat T, R.act (𝟙 X) φ).val v = ∑ X : ThinCat T, (R.act (𝟙 X) φ).val v
        from map_sum (⟨⟨fun ψ : R.Tot ↦ ψ.val v, rfl⟩, fun _ _ ↦ rfl⟩ : R.Tot →+ R.sp v) _ _]
      simp only [act_val, Module.End.one_apply]
      rw [Finset.sum_eq_single (⟨v⟩ : ThinCat T) (fun X _ hX ↦ by
        rw [Pi.single_eq_of_ne]
        exact fun h ↦ hX (ThinCat.ext_as h.symm)) (by simp), Pi.single_eq_same, homMap_id]
      rfl)

instance : Module (Linearization (ThinCat T) k) R.Tot := Module.compHom _ R.rep.toRingHom

instance : IsScalarTower k (Linearization (ThinCat T) k) R.Tot where
  smul_assoc a b φ := by
    change R.rep (a • b) φ = a • R.rep b φ
    rw [map_smul]
    rfl

lemma morElt_smul_val {X Y : ThinCat T} (f : X ⟶ Y) (φ : R.Tot) (v : V) :
    (morElt k f • φ).val v = Pi.single (M := fun v ↦ R.sp v) Y.as (R.homMap f (φ.val X.as)) v := by
  change (R.rep (morElt k f) φ).val v = _
  rw [show R.rep (morElt k f) = R.act f from linLiftₗ_morElt k _ R.act_zero f]
  rfl

/-- The element supported at one vertex. -/
def single (v : V) (m : R.sp v) : R.Tot := ⟨Pi.single v m⟩

lemma id_smul_eq_single (v : V) (φ : R.Tot) :
    morElt k (𝟙 (⟨v⟩ : ThinCat T)) • φ = R.single v (φ.val v) := by
  ext w
  rw [morElt_smul_val, homMap_id]
  rfl

lemma mor_smul_single {x y : V} (h : T.le x y) (m : R.sp x) :
    morElt k (ThinCat.mor (X := ⟨x⟩) (Y := ⟨y⟩) h) • R.single x m = R.single y (R.map x y h m) := by
  ext w
  rw [morElt_smul_val]
  simp only [single, ThinCat.mor, homMap, Pi.single_eq_same]

variable {R} {R' : ThinRep T k}

/-- The vertex component of a module map. -/
def comp (g : R.Tot →ₗ[Linearization (ThinCat T) k] R'.Tot) (v : V) : R.sp v →ₗ[k] R'.sp v where
  toFun m := (g (R.single v m)).val v
  map_add' m m' := by
    rw [show R.single v (m + m') = R.single v m + R.single v m' by
      ext w; simp [single, Pi.single_add], map_add]; rfl
  map_smul' a m := by
    rw [show R.single v (a • m) = a • R.single v m by ext w; simp [single, Pi.single_smul],
      LinearMap.map_smul_of_tower]; rfl

/-- **Module maps are given by their vertex components.** -/
lemma apply_val (g : R.Tot →ₗ[Linearization (ThinCat T) k] R'.Tot) (φ : R.Tot) (v : V) :
    (g φ).val v = comp g v (φ.val v) := by
  change _ = (g (R.single v (φ.val v))).val v
  rw [← id_smul_eq_single R v φ, map_smul, id_smul_eq_single]
  simp [single]

/-- **The vertex components commute with the maps.** -/
lemma comp_map (g : R.Tot →ₗ[Linearization (ThinCat T) k] R'.Tot) {x y : V} (h : T.le x y)
    (m : R.sp x) : comp g y (R.map x y h m) = R'.map x y h (comp g x m) := by
  change (g (R.single y (R.map x y h m))).val y = _
  rw [← mor_smul_single R h m, map_smul, morElt_smul_val]
  simp [ThinCat.mor, homMap]
  rfl

/-! ### Bricks and a representation-infiniteness criterion -/

variable {R R' : ThinRep T k}

/-- A natural family of linear maps between representations. -/
def IsNatural (f : ∀ x, R.sp x →ₗ[k] R'.sp x) : Prop :=
  ∀ x y (h : T.le x y) (m : R.sp x), f y (R.map x y h m) = R'.map x y h (f x m)

lemma isNatural_comp (g : R.Tot →ₗ[Linearization (ThinCat T) k] R'.Tot) : IsNatural (comp g) :=
  fun _ _ h m ↦ comp_map g h m

lemma comp_symm_comp (e : R.Tot ≃ₗ[Linearization (ThinCat T) k] R'.Tot) (x : V) (m : R.sp x) :
    comp e.symm.toLinearMap x (comp e.toLinearMap x m) = m := by
  have h1 := apply_val e.toLinearMap (R.single x m) x
  have h2 := apply_val e.symm.toLinearMap (e (R.single x m)) x
  simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h1 h2
  rw [show (R.single x m).val x = m by simp [single]] at h1 h2
  rw [← h1, ← h2]

instance [∀ x, FiniteDimensional k (R.sp x)] : Module.Finite k R.Tot :=
  Module.Finite.of_injective
    (⟨⟨Tot.val, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩ : R.Tot →ₗ[k] ∀ x : V, R.sp x)
    Tot.val_injective

/-- **A thin representation whose natural endomorphisms are scalars is
indecomposable.** -/
lemma isIndecomposable (hnt : ∃ x, Nontrivial (R.sp x))
    (hend : ∀ f : ∀ x, R.sp x →ₗ[k] R.sp x, IsNatural f → ∃ c : k, ∀ x, f x = c • LinearMap.id) :
    Statement.IsIndecomposable (Linearization (ThinCat T) k) R.Tot := by
  obtain ⟨x₀, hx₀⟩ := hnt
  obtain ⟨m₀, m₁, hm⟩ := hx₀
  refine ⟨⟨R.single x₀ m₀, R.single x₀ m₁, fun h ↦ hm ?_⟩, fun N N' hN ↦ ?_⟩
  · simpa [single] using congrArg (fun φ : R.Tot ↦ φ.val x₀) h
  let π : R.Tot →ₗ[Linearization (ThinCat T) k] R.Tot :=
    N.subtype ∘ₗ Submodule.projectionOnto (R := Linearization (ThinCat T) k) N N' hN
  obtain ⟨c, hc⟩ := hend (comp π) (isNatural_comp π)
  have hπ : ∀ φ, π φ = c • φ := fun φ ↦ Tot.ext (funext fun x ↦ by
    rw [apply_val, hc]; rfl)
  have hidem : c * c = c := by
    have h2 : π (π (R.single x₀ (m₀ - m₁))) = π (R.single x₀ (m₀ - m₁)) := by
      simp only [π, LinearMap.comp_apply, Submodule.coe_subtype]
      rw [Submodule.projectionOnto_apply_left (R := Linearization (ThinCat T) k) (p := N) (q := N') hN]
    rw [hπ, hπ, smul_smul] at h2
    have h3 := congrArg (fun φ : R.Tot ↦ φ.val x₀) h2
    simp only [Tot.smul_val, single, Pi.single_eq_same] at h3
    exact smul_left_injective k (sub_ne_zero.2 hm) h3
  have hd01 : c * (c - 1) = 0 := by rw [mul_sub, mul_one, hidem, sub_self]
  rcases mul_eq_zero.1 hd01 with h0 | h1
  · left
    refine eq_bot_iff.2 fun x hx ↦ ?_
    have : π x = x := by
      simp [π, Submodule.projectionOnto_apply_left (R := Linearization (ThinCat T) k) (p := N)
        (q := N') hN ⟨x, hx⟩]
    rw [hπ, h0, zero_smul] at this
    exact (Submodule.mem_bot _).2 this.symm
  · right
    have h1 : c = 1 := sub_eq_zero.1 h1
    refine eq_bot_iff.2 fun x hx ↦ ?_
    have : π x = 0 := by
      simp [π, Submodule.projectionOnto_apply_right (R := Linearization (ThinCat T) k) (p := N)
        (q := N') hN ⟨x, hx⟩]
    rw [hπ, h1, one_smul] at this
    exact (Submodule.mem_bot _).2 this

/-- **Representation-infiniteness from a family of thin bricks.** If an
infinite family of finite-dimensional representations has scalar natural
endomorphisms and members related by a natural family of bijections are
equal, the linearization is representation-infinite. -/
theorem not_isRepresentationFinite {α : Type*} [Infinite α] (R : α → ThinRep T k)
    (hfin : ∀ t x, FiniteDimensional k ((R t).sp x)) (hnt : ∀ t, ∃ x, Nontrivial ((R t).sp x))
    (hend : ∀ t (f : ∀ x, (R t).sp x →ₗ[k] (R t).sp x), IsNatural f →
      ∃ c : k, ∀ x, f x = c • LinearMap.id)
    (hiso : ∀ t t' (f : ∀ x, (R t).sp x →ₗ[k] (R t').sp x), IsNatural f →
      (∀ x, Function.Bijective (f x)) → t = t') :
    ¬Statement.IsRepresentationFinite (Linearization (ThinCat T) k) := by
  rintro ⟨n, Bs, hB⟩
  have hfin' : ∀ t, Module.Finite (Linearization (ThinCat T) k) (R t).Tot := fun t ↦ by
    have := hfin t
    exact Module.Finite.of_restrictScalars_finite k _ _
  choose i hi using fun t : α ↦
    @hB (R t).Tot _ _ (hfin' t) (isIndecomposable (hnt t) (hend t))
  obtain ⟨t, t', hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite i
  obtain ⟨e⟩ := hi t
  obtain ⟨e'⟩ := hi t'
  rw [heq] at e
  let g := e.trans e'.symm
  refine hne (hiso t t' (comp g.toLinearMap) (isNatural_comp _) fun x ↦ ?_)
  refine ⟨fun m m' h ↦ ?_, fun m ↦ ⟨comp g.symm.toLinearMap x m, ?_⟩⟩
  · rw [← comp_symm_comp g x m, ← comp_symm_comp g x m', h]
  · have := comp_symm_comp g.symm x m
    simpa using this

end ThinRep

end RayCat

end LargeIndecomposable
