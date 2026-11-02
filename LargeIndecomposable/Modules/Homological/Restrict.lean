module

public import LargeIndecomposable.DirectedAlgebras.Directing.PredDirecting

/-!
# Restriction along a surjective algebra map

For a surjective `φ : A →ₐ[k] A'`, every `A'`-module is an `A`-module (`resFD φ X`). Restriction is
fully faithful (`resHomEquiv`), and it preserves and reflects indecomposability
(`isIndecMod_res_iff`). This identifies modules over a quotient algebra, for instance over a convex
subpiece, with the `A`-modules they give.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A A' : Type u} [Field k] [Ring A] [Algebra k A] [Ring A'] [Algebra k A']

/-- Restriction of an `A'`-module along `φ`. -/
def resFD (φ : A →ₐ[k] A') (X : FDMod k A') : FDMod k A :=
  letI : Module A X := Module.compHom X φ.toRingHom
  { carrier := X
    isScalarTower := ⟨fun c a x ↦ show φ (c • a) • x = c • (φ a • x) by
      rw [map_smul, smul_assoc]⟩ }

variable {φ : A →ₐ[k] A'}

/-- Elements of the restriction as elements of `X`. -/
def toX {X : FDMod k A'} (x : resFD φ X) : X := x

/-- Elements of `X` as elements of the restriction. -/
def ofX {X : FDMod k A'} (x : X) : resFD φ X := x

@[simp] lemma toX_ofX {X : FDMod k A'} (x : X) : toX (ofX (φ := φ) x) = x := rfl
@[simp] lemma ofX_toX {X : FDMod k A'} (x : resFD φ X) : ofX (toX x) = x := rfl

lemma toX_smul {X : FDMod k A'} (a : A) (x : resFD φ X) : toX (a • x) = φ a • toX x := rfl
lemma toX_add {X : FDMod k A'} (x y : resFD φ X) : toX (x + y) = toX x + toX y := rfl
lemma toX_zero {X : FDMod k A'} : toX (0 : resFD φ X) = 0 := rfl
lemma toX_injective {X : FDMod k A'} : Function.Injective (toX (φ := φ) (X := X)) :=
  fun _ _ h ↦ h

/-- An `A'`-linear map as an `A`-linear map. -/
def resHom (φ : A →ₐ[k] A') {X Y : FDMod k A'} (f : X ⟶ Y) : resFD φ X ⟶ resFD φ Y :=
  FDMod.ofLin
  { toFun x := ofX (FDMod.lin f (toX x))
    map_add' x y := map_add (FDMod.lin f) (toX x) (toX y)
    map_smul' a x := map_smul (FDMod.lin f) (φ a) (toX x) }

/-- An `A`-linear map between restrictions is `A'`-linear. -/
def unresHom (hφ : Function.Surjective φ) {X Y : FDMod k A'} (f : resFD φ X ⟶ resFD φ Y) :
    X ⟶ Y :=
  FDMod.ofLin
  { toFun x := toX (FDMod.lin f (ofX x))
    map_add' x y := map_add (FDMod.lin f) (ofX x) (ofX y)
    map_smul' a' x := by
      obtain ⟨a, rfl⟩ := hφ a'
      exact map_smul (FDMod.lin f) a (ofX x) }

/-- **Restriction is fully faithful.** -/
def resHomEquiv (hφ : Function.Surjective φ) {X Y : FDMod k A'} :
    (X ⟶ Y) ≃ (resFD φ X ⟶ resFD φ Y) where
  toFun := resHom φ
  invFun := unresHom hφ
  left_inv _ := rfl
  right_inv _ := rfl

lemma lin_resHom {X Y : FDMod k A'} (f : X ⟶ Y) (x : resFD φ X) :
    toX (FDMod.lin (resHom φ f) x) = FDMod.lin f (toX x) := rfl

lemma lin_unresHom (hφ : Function.Surjective φ) {X Y : FDMod k A'} (f : resFD φ X ⟶ resFD φ Y)
    (x : X) : FDMod.lin (unresHom hφ f) x = toX (FDMod.lin f (ofX x)) := rfl

/-- `A`-submodules of a restriction are `A'`-submodules. -/
def subOfRes (hφ : Function.Surjective φ) {X : FDMod k A'} (U : Submodule A (resFD φ X)) :
    Submodule A' X where
  carrier := {x | ofX x ∈ U}
  add_mem' hx hy := U.add_mem hx hy
  zero_mem' := U.zero_mem
  smul_mem' a' x hx := by
    obtain ⟨a, rfl⟩ := hφ a'
    exact U.smul_mem a hx

/-- `A'`-submodules as `A`-submodules of the restriction. -/
def subToRes {X : FDMod k A'} (U : Submodule A' X) : Submodule A (resFD φ X) where
  carrier := {x | toX x ∈ U}
  add_mem' hx hy := U.add_mem hx hy
  zero_mem' := U.zero_mem
  smul_mem' a x hx := U.smul_mem (φ a) hx

lemma mem_subToRes {X : FDMod k A'} (U : Submodule A' X) (x : resFD φ X) :
    x ∈ subToRes (φ := φ) U ↔ toX x ∈ U := Iff.rfl

lemma mem_subOfRes (hφ : Function.Surjective φ) {X : FDMod k A'} (U : Submodule A (resFD φ X))
    (x : X) : x ∈ subOfRes hφ U ↔ ofX x ∈ U := Iff.rfl

/-- **Restriction preserves and reflects indecomposability.** -/
theorem isIndecMod_res_iff (hφ : Function.Surjective φ) (X : FDMod k A') :
    IsIndecMod A (resFD φ X) ↔ IsIndecMod A' X := by
  constructor
  · intro h U V hUV
    have hc : IsCompl (subToRes (φ := φ) U) (subToRes V) := by
      constructor
      · rw [Submodule.disjoint_def]
        intro x hx hx'
        exact toX_injective (Submodule.disjoint_def.1 hUV.disjoint _ hx hx')
      · rw [codisjoint_iff, eq_top_iff]
        intro x _
        have hx : toX x ∈ U ⊔ V := hUV.codisjoint.eq_top ▸ Submodule.mem_top
        obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hx
        have : x = ofX u + ofX v := toX_injective (by rw [toX_add]; exact huv.symm)
        rw [this]
        exact Submodule.add_mem_sup (show toX (ofX (φ := φ) u) ∈ U from hu)
          (show toX (ofX (φ := φ) v) ∈ V from hv)
    rcases h _ _ hc with h1 | h1
    · left; rw [eq_bot_iff]; intro x hx
      have : ofX (φ := φ) x ∈ subToRes (φ := φ) U := hx
      rw [h1] at this; exact this
    · right; rw [eq_bot_iff]; intro x hx
      have : ofX (φ := φ) x ∈ subToRes (φ := φ) V := hx
      rw [h1] at this; exact this
  · intro h U V hUV
    have hc : IsCompl (subOfRes hφ U) (subOfRes hφ V) := by
      constructor
      · rw [Submodule.disjoint_def]
        intro x hx hx'
        exact Submodule.disjoint_def.1 hUV.disjoint _ hx hx'
      · rw [codisjoint_iff, eq_top_iff]
        intro x _
        have hx : ofX (φ := φ) x ∈ U ⊔ V := hUV.codisjoint.eq_top ▸ Submodule.mem_top
        obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hx
        have : x = toX u + toX v := by rw [← toX_add, huv]; rfl
        rw [this]
        exact Submodule.add_mem_sup (show ofX (toX u) ∈ U from hu) (show ofX (toX v) ∈ V from hv)
    rcases h _ _ hc with h1 | h1
    · left; rw [eq_bot_iff]; intro x hx
      have : toX x ∈ subOfRes hφ U := hx
      rw [h1] at this; exact this
    · right; rw [eq_bot_iff]; intro x hx
      have : toX x ∈ subOfRes hφ V := hx
      rw [h1] at this; exact this

lemma nontrivial_res_iff (X : FDMod k A') : Nontrivial (resFD φ X) ↔ Nontrivial X := Iff.rfl

lemma indNT_res_iff (hφ : Function.Surjective φ) (X : FDMod k A') :
    IndNT (resFD φ X) ↔ IndNT X := by
  unfold IndNT
  rw [isIndecMod_res_iff hφ]
  rfl

section Descend

variable (hφ : Function.Surjective φ) (M : FDMod k A)
  (hM : ∀ a : A, φ a = 0 → ∀ m : M, a • m = 0)

include hM in
lemma smul_eq_of_eq {a b : A} (h : φ a = φ b) (m : M) : a • m = b • m := by
  have := hM (a - b) (by rw [map_sub, h, sub_self]) m
  rwa [sub_smul, sub_eq_zero] at this

/-- The `A'`-action on a module killed by `ker φ`. -/
def descSMul (a' : A') (m : M) : M := Function.surjInv hφ a' • m

include hM in
lemma descSMul_eq (a : A) (m : M) : descSMul hφ M (φ a) m = a • m :=
  smul_eq_of_eq M hM (Function.surjInv_eq hφ (φ a)) m

/-- **A module killed by `ker φ` descends to `A'`.** -/
def descend : FDMod k A' :=
  letI : SMul A' M := ⟨descSMul hφ M⟩
  letI : Module A' M :=
    { one_smul m := by
        change descSMul hφ M 1 m = m
        rw [← map_one φ, descSMul_eq hφ M hM, one_smul]
      mul_smul a' b' m := by
        obtain ⟨a, rfl⟩ := hφ a'; obtain ⟨b, rfl⟩ := hφ b'
        change descSMul hφ M (φ a * φ b) m = descSMul hφ M (φ a) (descSMul hφ M (φ b) m)
        rw [← map_mul, descSMul_eq hφ M hM, descSMul_eq hφ M hM, descSMul_eq hφ M hM, mul_smul]
      smul_zero a' := smul_zero _
      smul_add a' m n := smul_add _ m n
      add_smul a' b' m := by
        obtain ⟨a, rfl⟩ := hφ a'; obtain ⟨b, rfl⟩ := hφ b'
        change descSMul hφ M (φ a + φ b) m = descSMul hφ M (φ a) m + descSMul hφ M (φ b) m
        rw [← map_add, descSMul_eq hφ M hM, descSMul_eq hφ M hM, descSMul_eq hφ M hM, add_smul]
      zero_smul m := by
        change descSMul hφ M 0 m = 0
        rw [← map_zero φ, descSMul_eq hφ M hM, zero_smul] }
  { carrier := M
    isScalarTower := ⟨fun c a' m ↦ by
      obtain ⟨a, rfl⟩ := hφ a'
      change descSMul hφ M (c • φ a) m = c • descSMul hφ M (φ a) m
      rw [← map_smul, descSMul_eq hφ M hM, descSMul_eq hφ M hM, smul_assoc]⟩ }

/-- The identity from the restriction of the descent back to `M`. -/
def descIso : resFD φ (descend hφ M hM) ⟶ M :=
  FDMod.ofLin
  { toFun x := (show M from x)
    map_add' _ _ := rfl
    map_smul' a x := descSMul_eq hφ M hM a x }

/-- The identity from `M` to the restriction of its descent. -/
def descIsoInv : M ⟶ resFD φ (descend hφ M hM) :=
  FDMod.ofLin
  { toFun x := (show resFD φ (descend hφ M hM) from x)
    map_add' _ _ := rfl
    map_smul' a x := (descSMul_eq hφ M hM a x).symm }

lemma descIso_bijective : Function.Bijective (FDMod.lin (descIso hφ M hM)) :=
  Function.bijective_id

end Descend

section RAS

variable (hφ : Function.Surjective φ)

include hφ in
lemma splitEpi_res_iff {W Z : FDMod k A'} (v : W ⟶ Z) :
    (∃ s : resFD φ Z ⟶ resFD φ W, FDMod.lin (resHom φ v) ∘ₗ FDMod.lin s = LinearMap.id) ↔
      ∃ s : Z ⟶ W, FDMod.lin v ∘ₗ FDMod.lin s = LinearMap.id := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨unresHom hφ s, LinearMap.ext fun z ↦ LinearMap.congr_fun hs (ofX z)⟩
  · rintro ⟨s, hs⟩
    exact ⟨resHom φ s, LinearMap.ext fun z ↦ LinearMap.congr_fun hs (toX z)⟩

include hφ in
/-- **A right almost split map of `A`-modules between restrictions is right almost split over
`A'`.** -/
theorem isRightAS_unres {E Z : FDMod k A'} {g : E ⟶ Z} (hg : IsRightAS (resHom φ g)) :
    IsRightAS g := by
  refine ⟨fun hs ↦ hg.1 ((FDMod.exists_comp_eq_id_iff _).2 (((splitEpi_res_iff hφ g).2 ((FDMod.exists_comp_eq_id_iff _).1 hs)))), fun W v hv ↦ ?_⟩
  obtain ⟨t, ht⟩ := hg.2 (resFD φ W) (resHom φ v) fun hs ↦ hv ((FDMod.exists_comp_eq_id_iff _).2 (((splitEpi_res_iff hφ v).1 ((FDMod.exists_comp_eq_id_iff _).1 hs))))
  exact ⟨unresHom hφ t, (FDMod.hom_ext (LinearMap.ext fun w ↦ LinearMap.congr_fun (congrArg FDMod.lin ht) (ofX w)))⟩

include hφ in
/-- **A right almost split map over `A'` is right almost split among the `A`-modules killed by
`ker φ`.** -/
theorem rightAS_res_factor {E Z : FDMod k A'} {g : E ⟶ Z} (hg : IsRightAS g) (W : FDMod k A)
    (hW : ∀ a : A, φ a = 0 → ∀ m : W, a • m = 0) (v : W ⟶ resFD φ Z)
    (hv : ¬∃ s : resFD φ Z ⟶ W, FDMod.lin v ∘ₗ FDMod.lin s = LinearMap.id) :
    ∃ t : W ⟶ resFD φ E, t ≫ resHom φ g = v := by
  let d := descIso hφ W hW
  let d' := descIsoInv hφ W hW
  let v' : descend hφ W hW ⟶ Z := unresHom hφ (d ≫ v)
  have hv' : ¬∃ s : Z ⟶ descend hφ W hW, FDMod.lin v' ∘ₗ FDMod.lin s = LinearMap.id := by
    rintro ⟨s, hs⟩
    exact hv ⟨resHom φ s ≫ d, LinearMap.ext fun z ↦ LinearMap.congr_fun hs (toX z)⟩
  obtain ⟨t', ht'⟩ := hg.2 _ v' (mt (FDMod.exists_comp_eq_id_iff _).1 hv')
  refine ⟨d' ≫ resHom φ t', (FDMod.hom_ext (LinearMap.ext fun w ↦ ?_))⟩
  have := LinearMap.congr_fun (congrArg FDMod.lin ht') (show descend hφ W hW from w)
  exact this

end RAS

end LargeIndecomposable.AR
