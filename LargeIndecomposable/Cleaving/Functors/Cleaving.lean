module

public import LargeIndecomposable.MultiplicativeBases.Twisted.MulBasis
public import LargeIndecomposable.RepresentationType.Basic.Retract

/-!
# Cleaving functors (Gabriel–Roiter 13.8)

Let `A` be a `k`-algebra with a twisted multiplicative basis `B` over a finite
ray category `P` (for instance `k(P)`, or a twisted linearization), and let
`F : D ⥤ P` be a functor from a finite ray category along which the twist is
trivial (`MulBasis.Untwisted`). An `A`-module `M` gives the `k(D)`-module
`F^* M = {v : D → M | e_{F x} v x = v x}` on which a morphism `f : x ⟶ y` of
`D` acts by `F f` (`RayQuiver.Res`).

`F` is cleaving (in the form used here) when it reflects zero, is injective on
morphisms, and a morphism `ρ : F x ⟶ F y` lies in the image of `F` as soon as
some composite `F μ ≫ ρ ≫ F ν` is the image of a nonzero morphism. These are
the conditions making the retraction `e_{F y} A e_{F x} → k(D)(x, y)` (a basis
morphism `F λ` goes to `λ`, the others to `0`) functorial, which is how
Gabriel–Roiter use conditions a), b) of 13.8. Then every finite-dimensional
`k(D)`-module is a retract of `F^* L` for a finite-dimensional `A`-module `L`
(the coinduced module), and `k(D)` is representation-finite when `A` is
(`RayQuiver.isRepresentationFinite_of_cleaving`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits FinQuiver

universe u

namespace RayQuiver

section Finite

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] (k : Type u) [Field k]

instance : Finite (NZ P) := by
  have := fun x y : P ↦ IsRayCategory.finite_hom x y
  infer_instance

instance : FiniteDimensional k (Linearization P k) := Module.Finite.of_basis (linBasis k)

/-- A `k`-linear map between `k(P)`-modules commuting with the elements of
morphisms is `k(P)`-linear. -/
lemma map_smul_of_morElt {V W : Type*} [AddCommGroup V] [Module k V] [Module (Linearization P k) V]
    [IsScalarTower k (Linearization P k) V] [AddCommGroup W] [Module k W]
    [Module (Linearization P k) W] [IsScalarTower k (Linearization P k) W] (φ : V →ₗ[k] W)
    (h : ∀ {x y : P} (f : x ⟶ y) (v : V), φ (morElt k f • v) = morElt k f • φ v)
    (a : Linearization P k) (v : V) : φ (a • v) = a • φ v := by
  have := Fintype.ofFinite (NZ P)
  rw [← (linBasis k).sum_repr a]
  simp only [Finset.sum_smul, map_sum, smul_assoc, map_smul, linBasis_apply, rayElt_eq_morElt, h]

/-- The `k(P)`-linear map of a `k`-linear map commuting with morphisms. -/
def linOfMorElt {V W : Type*} [AddCommGroup V] [Module k V] [Module (Linearization P k) V]
    [IsScalarTower k (Linearization P k) V] [AddCommGroup W] [Module k W]
    [Module (Linearization P k) W] [IsScalarTower k (Linearization P k) W] (φ : V →ₗ[k] W)
    (h : ∀ {x y : P} (f : x ⟶ y) (v : V), φ (morElt k f • v) = morElt k f • φ v) :
    V →ₗ[Linearization P k] W where
  toFun := φ
  map_add' := φ.map_add
  map_smul' a v := map_smul_of_morElt k φ h a v

end Finite

variable {D P : Type} [Category.{0} D] [HasZeroMorphisms D] [IsRayCategory D] [Fintype D]
  [DecidableEq D] [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]
  (B : MulBasis k P A) (F : D ⥤ P) [F.PreservesZeroMorphisms]

/-- The twist of `B` is trivial along `F`. -/
def MulBasis.Untwisted : Prop :=
  ∀ {x y z : D} (f : x ⟶ y) (g : y ⟶ z), F.map (f ≫ g) ≠ 0 → B.tw (F.map f) (F.map g) = 1

/-- A gauge making the twist of `B` trivial along `F`: scalars `c` on the
morphisms of `D` with `c f * c g * tw (F f) (F g) = c (f ≫ g)`. -/
class MulBasis.Gauge where
  c : ∀ {x y : D}, (x ⟶ y) → kˣ
  c_id : ∀ x : D, c (𝟙 x) = 1
  c_mul : ∀ {x y z : D} (f : x ⟶ y) (g : y ⟶ z), F.map (f ≫ g) ≠ 0 →
    c f * c g * B.tw (F.map f) (F.map g) = c (f ≫ g)

variable {B F} in
/-- The trivial gauge of an untwisted basis. -/
def MulBasis.Untwisted.gauge (hU : B.Untwisted F) : B.Gauge F where
  c _ := 1
  c_id _ := rfl
  c_mul f g h := by rw [hU f g h]; simp

section Gauge

variable [G : B.Gauge F]

variable {B F} in
/-- The gauged basis element of a morphism of `D`. -/
def gelt {x y : D} (f : x ⟶ y) : A := (G.c f : k) • B.elt (F.map f)

lemma gelt_mul {x y z : D} (f : x ⟶ y) (g : y ⟶ z) :
    gelt (B := B) (F := F) g * gelt (B := B) (F := F) f = gelt (B := B) (F := F) (f ≫ g) := by
  unfold gelt
  rw [smul_mul_smul_comm, B.elt_mul, smul_smul, ← F.map_comp]
  by_cases h : F.map (f ≫ g) = 0
  · rw [h, B.elt_zero, smul_zero, smul_zero]
  · rw [← G.c_mul f g h, F.map_comp]
    congr 1
    simp only [Units.val_mul]
    ring

lemma gelt_id (x : D) : gelt (B := B) (F := F) (𝟙 x) = B.elt (𝟙 (F.obj x)) := by
  simp [gelt, G.c_id, F.map_id]

lemma gelt_zero {x y : D} : gelt (B := B) (F := F) (0 : x ⟶ y) = 0 := by
  simp [gelt, B.elt_zero]

lemma elt_map_eq {x y : D} (f : x ⟶ y) :
    B.elt (F.map f) = (((G.c f)⁻¹ : kˣ) : k) • gelt (B := B) (F := F) f := by
  rw [gelt, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

lemma id_mul_gelt {x y : D} (f : x ⟶ y) :
    B.elt (𝟙 (F.obj y)) * gelt (B := B) (F := F) f = gelt (B := B) (F := F) f := by
  rw [gelt, mul_smul_comm, B.id_mul]

lemma gelt_mul_id {x y : D} (f : x ⟶ y) :
    gelt (B := B) (F := F) f * B.elt (𝟙 (F.obj x)) = gelt (B := B) (F := F) f := by
  rw [gelt, smul_mul_assoc, B.mul_id]

end Gauge

include B in
lemma MulBasis.finiteDimensional : FiniteDimensional k A := Module.Finite.of_basis B.basis

/-! ### Restriction along `F` -/

section Restrict

variable (M : Type u) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

/-- The underlying subspace of `F^* M`. -/
def resSub : Submodule k (D → M) where
  carrier := {v | ∀ x, B.elt (𝟙 (F.obj x)) • v x = v x}
  add_mem' {v w} hv hw x := by simp [smul_add, hv x, hw x]
  zero_mem' x := by simp
  smul_mem' c v hv x := by simp [smul_comm _ c, hv x]

/-- The restriction `F^* M`. -/
def Res : Type u := resSub B F M

instance : AddCommGroup (Res B F M) := inferInstanceAs (AddCommGroup (resSub B F M))
instance : Module k (Res B F M) := inferInstanceAs (Module k (resSub B F M))

variable {B F M} in
/-- The components of an element of `F^* M`. -/
def Res.val (v : Res B F M) : D → M := Subtype.val (p := (· ∈ resSub B F M)) v

variable {B F M} in
lemma Res.prop (v : Res B F M) (x : D) : B.elt (𝟙 (F.obj x)) • v.val x = v.val x :=
  Subtype.prop (p := (· ∈ resSub B F M)) v x

variable {B F M} in
@[ext]
lemma Res.ext {v w : Res B F M} (h : ∀ x, v.val x = w.val x) : v = w :=
  Subtype.ext (funext h)

variable {B F M} in
@[simp] lemma Res.add_val (v w : Res B F M) (x : D) : (v + w).val x = v.val x + w.val x := rfl
variable {B F M} in
@[simp] lemma Res.zero_val (x : D) : (0 : Res B F M).val x = 0 := rfl
variable {B F M} in
@[simp] lemma Res.smul_val (c : k) (v : Res B F M) (x : D) : (c • v).val x = c • v.val x := rfl

variable {B F M} in
/-- An element of `F^* M` from components. -/
def Res.mk (v : D → M) (hv : ∀ x, B.elt (𝟙 (F.obj x)) • v x = v x) : Res B F M := ⟨v, hv⟩

variable {B F M} in
@[simp] lemma Res.mk_val (v : D → M) (hv) (x : D) : (Res.mk (B := B) (F := F) v hv).val x = v x :=
  rfl

variable [G : B.Gauge F]

/-- The action of a morphism of `D` on `F^* M`. -/
def resAct {x y : D} (f : x ⟶ y) : Module.End k (Res B F M) where
  toFun v := Res.mk (fun z ↦ if h : y = z then gelt (B := B) (F := F) (f ≫ eqToHom h) • v.val x else 0)
    fun z ↦ by
      split_ifs with h
      · rw [← mul_smul, id_mul_gelt]
      · rw [smul_zero]
  map_add' v w := by
    ext z
    simp only [Res.mk_val, Res.add_val]
    split_ifs <;> simp [smul_add]
  map_smul' c v := by
    ext z
    simp only [Res.mk_val, Res.smul_val, RingHom.id_apply]
    split_ifs <;> simp [smul_comm _ c]

variable {B F M} in
lemma resAct_val {x y : D} (f : x ⟶ y) (v : Res B F M) (z : D) :
    (resAct B F M f v).val z =
      if h : y = z then gelt (B := B) (F := F) (f ≫ eqToHom h) • v.val x else 0 := rfl

/-- The representation of `k(D)` on `F^* M`. -/
def resRep : Linearization D k →ₐ[k] Module.End k (Res B F M) :=
  linLift k (fun f ↦ resAct B F M f)
    (by
      intro x y
      ext v z
      simp [resAct_val, gelt_zero])
    (by
      intro x y z f g
      ext v w
      simp only [Module.End.mul_apply, resAct_val]
      by_cases h : z = w
      · subst h
        simp only [eqToHom_refl, Category.comp_id, dite_true, ← mul_smul, gelt_mul]
      · simp [h])
    (by
      intro x y y' z f g hy
      ext v w
      simp only [Module.End.mul_apply, resAct_val, dif_neg hy, smul_zero, dite_eq_ite, ite_self,
        LinearMap.zero_apply, Res.zero_val])
    (by
      ext v z
      rw [Module.End.one_apply, LinearMap.sum_apply]
      rw [show (∑ c : D, resAct B F M (𝟙 c) v).val z = ∑ c : D, (resAct B F M (𝟙 c) v).val z from
        map_sum (⟨⟨fun w : Res B F M ↦ w.val z, rfl⟩, fun _ _ ↦ rfl⟩ : Res B F M →+ M) _ _]
      simp only [resAct_val]
      rw [Finset.sum_eq_single z (fun c _ hc ↦ dif_neg hc) (by simp), dif_pos rfl]
      simpa [gelt_id] using v.prop z)

instance : Module (Linearization D k) (Res B F M) := Module.compHom _ (resRep B F M).toRingHom

instance : IsScalarTower k (Linearization D k) (Res B F M) where
  smul_assoc c a v := by
    change resRep B F M (c • a) v = c • resRep B F M a v
    rw [map_smul]
    rfl

variable {B F M} in
lemma resRep_morElt {x y : D} (f : x ⟶ y) : resRep B F M (morElt k f) = resAct B F M f := by
  change linLiftₗ k (fun f ↦ resAct B F M f) (morElt k f) = _
  refine linLiftₗ_morElt k _ ?_ f
  intro x y
  ext v z
  simp [resAct_val, gelt_zero]

variable {B F M} in
lemma morElt_smul_res_val {x y : D} (f : x ⟶ y) (v : Res B F M) (z : D) :
    (morElt k f • v).val z =
      if h : y = z then gelt (B := B) (F := F) (f ≫ eqToHom h) • v.val x else 0 := by
  change (resRep B F M (morElt k f) v).val z = _
  rw [resRep_morElt]
  rfl

end Restrict

/-! ### The retraction of a cleaving functor -/

/-- A functor of ray categories is cleaving (in the form used here). -/
structure IsCleaving : Prop where
  map_eq_zero_iff : ∀ {x y : D} (f : x ⟶ y), F.map f = 0 ↔ f = 0
  map_injective : ∀ {x y : D} {f g : x ⟶ y}, F.map f = F.map g → f = g
  image_closed : ∀ {x x' y y' : D} (μ : x' ⟶ x) (ρ : F.obj x ⟶ F.obj y) (ν : y ⟶ y')
    (κ : x' ⟶ y'), F.map μ ≫ ρ ≫ F.map ν = F.map κ → κ ≠ 0 → ∃ l : x ⟶ y, ρ = F.map l

section Retraction

variable {B F} (hF : IsCleaving F) [G : B.Gauge F]

variable (B) in
open Classical in
/-- The retraction on basis morphisms. -/
def retrBasis (x z : D) (μ : NZ P) : Linearization D k :=
  if h : μ.1 = F.obj x ∧ μ.2.1 = F.obj z then
    if h' : ∃ l : x ⟶ z, F.map l = eqToHom h.1.symm ≫ μ.2.2.1 ≫ eqToHom h.2 then
      (((G.c h'.choose)⁻¹ : kˣ) : k) • morElt k h'.choose
    else 0
  else 0

variable (B F) in
/-- The retraction `A → k(D)` at `(x, z)`: `F l ↦ l` on basis morphisms
`F x ⟶ F z`, all other basis morphisms to `0`. -/
def retr (x z : D) : A →ₗ[k] Linearization D k :=
  B.basis.constr k (retrBasis B (k := k) (F := F) x z)

include hF in
lemma IsCleaving.map_ne_zero {x y : D} {f : x ⟶ y} (hf : f ≠ 0) : F.map f ≠ 0 :=
  fun h ↦ hf ((hF.map_eq_zero_iff f).1 h)

lemma retr_elt_basis {s t : P} (ρ : s ⟶ t) (hρ : ρ ≠ 0) (x z : D) :
    retr B F x z (B.elt ρ) = retrBasis B (k := k) (F := F) x z ⟨s, t, ρ, hρ⟩ := by
  rw [show B.elt ρ = B.basis ⟨s, t, ρ, hρ⟩ by rw [B.basis_apply], retr,
    Module.Basis.constr_basis]

/-- Basis morphisms outside `F x ⟶ F z` go to zero. -/
lemma retr_elt_of_not {s t : P} (ρ : s ⟶ t) (x z : D) (h : ¬(s = F.obj x ∧ t = F.obj z)) :
    retr B F x z (B.elt ρ) = 0 := by
  by_cases hρ : ρ = 0
  · subst hρ
    rw [B.elt_zero, map_zero]
  · rw [retr_elt_basis ρ hρ, retrBasis, dif_neg h]

include hF in
/-- Images of morphisms go back. -/
lemma retr_elt_map {x z : D} (l : x ⟶ z) :
    retr B F x z (B.elt (F.map l)) = (((G.c l)⁻¹ : kˣ) : k) • morElt k l := by
  by_cases hl : l = 0
  · subst hl
    rw [F.map_zero, B.elt_zero, morElt_zero, map_zero, smul_zero]
  · have h0 := hF.map_ne_zero hl
    have hex : ∃ l' : x ⟶ z, F.map l' = eqToHom (rfl : F.obj x = F.obj x).symm ≫ F.map l ≫
        eqToHom (rfl : F.obj z = F.obj z) := ⟨l, by simp⟩
    rw [retr_elt_basis _ h0, retrBasis, dif_pos ⟨rfl, rfl⟩, dif_pos hex]
    have : hex.choose = l := hF.map_injective (hex.choose_spec.trans (by simp))
    rw [this]

include hF in
lemma retr_gelt {x z : D} (l : x ⟶ z) : retr B F x z (gelt (B := B) (F := F) l) = morElt k l := by
  rw [gelt, map_smul, retr_elt_map hF, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    one_smul]

/-- Morphisms `F x ⟶ F z` outside the image go to zero. -/
lemma retr_elt_of_not_mem {x z : D} (ρ : F.obj x ⟶ F.obj z) (h : ¬∃ l : x ⟶ z, ρ = F.map l) :
    retr B F x z (B.elt ρ) = 0 := by
  by_cases hρ : ρ = 0
  · subst hρ
    rw [B.elt_zero, map_zero]
  · rw [retr_elt_basis ρ hρ, retrBasis, dif_pos ⟨rfl, rfl⟩, dif_neg]
    rintro ⟨l, hl⟩
    exact h ⟨l, by simpa using hl.symm⟩

include hF in
/-- The retraction is natural on the left. -/
lemma retr_mul_left {x y y' : D} (μ : y ⟶ y') (a : A) :
    retr B F x y' (gelt (B := B) (F := F) μ * a) = morElt k μ * retr B F x y a := by
  suffices H : (retr B F x y' ∘ₗ LinearMap.mulLeft k (gelt (B := B) (F := F) μ) :
      A →ₗ[k] Linearization D k) =
      LinearMap.mulLeft k (morElt k μ) ∘ₗ retr B F x y by
    simpa using LinearMap.congr_fun H a
  apply B.linMap_ext
  intro s t ρ
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
  by_cases ht : t = F.obj y
  · subst ht
    by_cases hs : s = F.obj x
    · subst hs
      by_cases him : ∃ l, ρ = F.map l
      · obtain ⟨l, rfl⟩ := him
        rw [elt_map_eq B F l, mul_smul_comm, gelt_mul, map_smul, retr_gelt hF, map_smul,
          retr_gelt hF, mul_smul_comm, morElt_mul]
      · rw [gelt, smul_mul_assoc, B.elt_mul, map_smul, map_smul, retr_elt_of_not_mem _ him,
          mul_zero]
        by_cases him2 : ∃ κ, ρ ≫ F.map μ = F.map κ
        · obtain ⟨κ, hκ⟩ := him2
          by_cases hκ0 : κ = 0
          · subst hκ0
            rw [hκ, F.map_zero, B.elt_zero, map_zero, smul_zero, smul_zero]
          · exact absurd (hF.image_closed (𝟙 x) ρ μ κ (by simpa using hκ) hκ0) him
        · rw [retr_elt_of_not_mem _ fun ⟨l, hl⟩ ↦ him2 ⟨l, hl⟩, smul_zero, smul_zero]
    · rw [gelt, smul_mul_assoc, B.elt_mul, map_smul, map_smul, retr_elt_of_not _ _ _ fun h ↦ hs h.1,
        retr_elt_of_not _ _ _ fun h ↦ hs h.1, smul_zero, smul_zero, mul_zero]
  · rw [gelt, smul_mul_assoc, B.elt_mul_ne ρ (F.map μ) ht, smul_zero, map_zero,
      retr_elt_of_not _ _ _ fun h ↦ ht h.2, mul_zero]

include hF in
/-- The retraction is natural on the right. -/
lemma retr_mul_right {x x' z : D} (μ : x ⟶ x') (a : A) :
    retr B F x z (a * gelt (B := B) (F := F) μ) = retr B F x' z a * morElt k μ := by
  suffices H : (retr B F x z ∘ₗ LinearMap.mulRight k (gelt (B := B) (F := F) μ) :
      A →ₗ[k] Linearization D k) =
      LinearMap.mulRight k (morElt k μ) ∘ₗ retr B F x' z by
    simpa using LinearMap.congr_fun H a
  apply B.linMap_ext
  intro s t ρ
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply]
  by_cases hs : s = F.obj x'
  · subst hs
    by_cases ht : t = F.obj z
    · subst ht
      by_cases him : ∃ l, ρ = F.map l
      · obtain ⟨l, rfl⟩ := him
        rw [elt_map_eq B F l, smul_mul_assoc, gelt_mul, map_smul, retr_gelt hF, map_smul,
          retr_gelt hF, smul_mul_assoc, morElt_mul]
      · rw [gelt, mul_smul_comm, B.elt_mul, map_smul, map_smul, retr_elt_of_not_mem _ him,
          zero_mul]
        by_cases him2 : ∃ κ, F.map μ ≫ ρ = F.map κ
        · obtain ⟨κ, hκ⟩ := him2
          by_cases hκ0 : κ = 0
          · subst hκ0
            rw [hκ, F.map_zero, B.elt_zero, map_zero, smul_zero, smul_zero]
          · exact absurd (hF.image_closed μ ρ (𝟙 z) κ (by simpa using hκ) hκ0) him
        · rw [retr_elt_of_not_mem _ fun ⟨l, hl⟩ ↦ him2 ⟨l, hl⟩, smul_zero, smul_zero]
    · rw [gelt, mul_smul_comm, B.elt_mul, map_smul, map_smul,
        retr_elt_of_not _ _ _ fun h ↦ ht h.2, retr_elt_of_not _ _ _ fun h ↦ ht h.2, smul_zero,
        smul_zero, zero_mul]
  · rw [gelt, mul_smul_comm, B.elt_mul_ne (F.map μ) ρ (Ne.symm hs), smul_zero, map_zero,
      retr_elt_of_not _ _ _ fun h ↦ hs h.1, zero_mul]

lemma retr_idem_left {x z : D} (a : A) :
    retr B F x z (B.elt (𝟙 (F.obj z)) * a) = retr B F x z a := by
  suffices H : (retr B F x z ∘ₗ LinearMap.mulLeft k (B.elt (𝟙 (F.obj z))) :
      A →ₗ[k] Linearization D k) = retr B F x z by
    simpa using LinearMap.congr_fun H a
  apply B.linMap_ext
  intro s t ρ
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
  by_cases ht : t = F.obj z
  · subst ht
    rw [B.id_mul]
  · rw [B.elt_mul_ne ρ _ ht, map_zero, retr_elt_of_not _ _ _ fun h ↦ ht h.2]

lemma retr_idem_right {x z : D} (a : A) :
    retr B F x z (a * B.elt (𝟙 (F.obj x))) = retr B F x z a := by
  suffices H : (retr B F x z ∘ₗ LinearMap.mulRight k (B.elt (𝟙 (F.obj x))) :
      A →ₗ[k] Linearization D k) = retr B F x z by
    simpa using LinearMap.congr_fun H a
  apply B.linMap_ext
  intro s t ρ
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply]
  by_cases hs : s = F.obj x
  · subst hs
    rw [B.mul_id]
  · rw [B.elt_mul_ne _ ρ (Ne.symm hs), map_zero, retr_elt_of_not _ _ _ fun h ↦ hs h.1]

include hF in
lemma id_mul_retr {x z : D} (a : A) :
    morElt k (𝟙 z) * retr B F x z a = retr B F x z a := by
  rw [← retr_mul_left hF, gelt_id, retr_idem_left]

include hF in
lemma retr_mul_id {x z : D} (a : A) :
    retr B F x z a * morElt k (𝟙 x) = retr B F x z a := by
  rw [← retr_mul_right hF, gelt_id, retr_idem_right]

include hF in
lemma mul_retr_eq_zero {x z w w' : D} (ν : w ⟶ w') (h : z ≠ w) (a : A) :
    morElt k ν * retr B F x z a = 0 := by
  rw [← id_mul_retr hF, ← mul_assoc, morElt_mul_ne k _ ν h, zero_mul]

include hF in
lemma retr_mul_eq_zero {x z w w' : D} (ν : w ⟶ w') (h : w' ≠ x) (a : A) :
    retr B F x z a * morElt k ν = 0 := by
  rw [← retr_mul_id hF, mul_assoc, morElt_mul_ne k ν _ h, mul_zero]

end Retraction

/-! ### Coinduction -/

section Coind

variable {B F} [G : B.Gauge F]

/-- Right multiplication on `F^* A`, as a `k`-linear map. -/
def rmulResₗ (a : A) : Res B F A →ₗ[k] Res B F A where
  toFun v := Res.mk (fun x ↦ v.val x * a) fun x ↦ by
    rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul (B.elt _) (v.val x), v.prop]
  map_add' v w := by ext x; simp [add_mul]
  map_smul' c v := by ext x; simp

/-- Right multiplication on `F^* A`. -/
def rmulRes (a : A) : Res B F A →ₗ[Linearization D k] Res B F A :=
  linOfMorElt k (rmulResₗ a) fun {x y} f v ↦ by
    ext z
    simp only [rmulResₗ, LinearMap.coe_mk, AddHom.coe_mk, Res.mk_val, morElt_smul_res_val]
    split_ifs <;> simp [mul_assoc]

@[simp] lemma rmulRes_val (a : A) (v : Res B F A) (x : D) :
    (rmulRes a v).val x = v.val x * a := rfl

lemma rmulRes_mul (a b : A) : rmulRes (B := B) (F := F) (a * b) = rmulRes b ∘ₗ rmulRes a := by
  ext v x
  simp [mul_assoc]

lemma rmulRes_one : rmulRes (B := B) (F := F) (1 : A) = LinearMap.id := by
  ext v x
  simp

lemma rmulRes_add (a b : A) : rmulRes (B := B) (F := F) (a + b) = rmulRes a + rmulRes b := by
  ext v x
  simp [mul_add]

lemma rmulRes_zero : rmulRes (B := B) (F := F) (0 : A) = 0 := by
  ext v x
  simp

lemma rmulRes_algebraMap (c : k) (v : Res B F A) : rmulRes (algebraMap k A c) v = c • v := by
  ext x
  simp [Algebra.smul_def, Algebra.commutes]

variable (B F) in
/-- The coinduced module `Hom_{k(D)}(F^* A, N)`. -/
def Coind (N : Type u) [AddCommGroup N] [Module (Linearization D k) N] : Type u :=
  Res B F A →ₗ[Linearization D k] N

variable (N : Type u) [AddCommGroup N] [Module (Linearization D k) N]

instance : AddCommGroup (Coind B F N) :=
  inferInstanceAs (AddCommGroup (Res B F A →ₗ[Linearization D k] N))

variable {N} in
/-- The underlying linear map. -/
def Coind.toLin (φ : Coind B F N) : Res B F A →ₗ[Linearization D k] N := φ

variable {N} in
/-- An element from a linear map. -/
def Coind.ofLin (φ : Res B F A →ₗ[Linearization D k] N) : Coind B F N := φ

variable {N} in
@[ext] lemma Coind.ext {φ ψ : Coind B F N} (h : ∀ v, φ.toLin v = ψ.toLin v) : φ = ψ :=
  LinearMap.ext h

variable {N} in
@[simp] lemma Coind.add_toLin (φ ψ : Coind B F N) (v) : (φ + ψ).toLin v = φ.toLin v + ψ.toLin v :=
  rfl
variable {N} in
@[simp] lemma Coind.zero_toLin (v) : (0 : Coind B F N).toLin v = 0 := rfl
variable {N} in
@[simp] lemma Coind.ofLin_toLin (φ : Res B F A →ₗ[Linearization D k] N) (v) :
    (Coind.ofLin (B := B) (F := F) φ).toLin v = φ v := rfl

instance : SMul A (Coind B F N) where
  smul a φ := Coind.ofLin (φ.toLin ∘ₗ rmulRes a)

variable {N} in
@[simp] lemma Coind.smul_toLin (a : A) (φ : Coind B F N) (v) :
    (a • φ).toLin v = φ.toLin (rmulRes a v) := rfl

instance : Module A (Coind B F N) where
  one_smul φ := by ext v; simp [rmulRes_one]
  mul_smul a b φ := by ext v; simp [rmulRes_mul]
  smul_zero a := by ext v; simp
  smul_add a φ ψ := by ext v; simp
  add_smul a b φ := by ext v; simp [rmulRes_add]
  zero_smul φ := by ext v; simp [rmulRes_zero]

instance : Module k (Coind B F N) := Module.compHom _ (algebraMap k A)

instance : IsScalarTower k A (Coind B F N) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

variable [Module k N] [IsScalarTower k (Linearization D k) N]

variable {N} in
@[simp] lemma Coind.k_smul_toLin (c : k) (φ : Coind B F N) (v) :
    (c • φ).toLin v = c • φ.toLin v := by
  change φ.toLin (rmulRes (algebraMap k A c) v) = _
  rw [rmulRes_algebraMap, LinearMap.map_smul_of_tower]

end Coind

/-! ### The coinduced module retracts onto `N` -/

section Section

variable {B F} [G : B.Gauge F] (hF : IsCleaving F) {N : Type u} [AddCommGroup N]
  [Module (Linearization D k) N] [Module k N] [IsScalarTower k (Linearization D k) N]

/-- `v ↦ ∑_z r_{x,z}(v_z) n`, as a `k`-linear map. -/
def coindEltₗ (x : D) (n : N) : Res B F A →ₗ[k] N where
  toFun v := ∑ z : D, retr B F x z (v.val z) • n
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum, smul_assoc]

include hF in
lemma coindEltₗ_morElt (x : D) (n : N) {y y' : D} (μ : y ⟶ y') (v : Res B F A) :
    coindEltₗ x n (morElt k μ • v) = morElt k μ • coindEltₗ x n v := by
  simp only [coindEltₗ, LinearMap.coe_mk, AddHom.coe_mk, morElt_smul_res_val, Finset.smul_sum,
    ← mul_smul]
  rw [Finset.sum_eq_single y' (fun z _ hz ↦ by rw [dif_neg (Ne.symm hz), map_zero, zero_smul])
    (by simp), dif_pos rfl, Finset.sum_eq_single y (fun z _ hz ↦ by
      rw [mul_retr_eq_zero hF μ hz, zero_smul]) (by simp)]
  simp only [eqToHom_refl, Category.comp_id]
  rw [smul_eq_mul, retr_mul_left hF]

/-- The element `v ↦ ∑_z r_{x,z}(v_z) n` of the coinduced module. -/
def coindElt (x : D) (n : N) : Coind B F N :=
  Coind.ofLin (linOfMorElt k (coindEltₗ x n) fun μ v ↦ coindEltₗ_morElt hF x n μ v)

lemma coindElt_toLin (x : D) (n : N) (v : Res B F A) :
    (coindElt (B := B) hF x n).toLin v = ∑ z : D, retr B F x z (v.val z) • n := rfl

lemma coindElt_prop (x : D) (n : N) :
    B.elt (𝟙 (F.obj x)) • coindElt (B := B) hF x n = coindElt hF x n := by
  ext v
  simp only [Coind.smul_toLin, coindElt_toLin, rmulRes_val, retr_idem_right]

/-- The section `N → F^* (coinduced module)`, as a `k`-linear map. -/
def coindSecₗ : N →ₗ[k] Res B F (Coind B F N) where
  toFun n := Res.mk (fun x ↦ coindElt hF x n) fun x ↦ coindElt_prop hF x n
  map_add' n m := by
    ext x v
    simp [coindElt_toLin, smul_add, Finset.sum_add_distrib]
  map_smul' c n := by
    ext x v
    simp only [Res.mk_val, Res.smul_val, Coind.k_smul_toLin, coindElt_toLin, RingHom.id_apply,
      Finset.smul_sum]
    exact Finset.sum_congr rfl fun z _ ↦ smul_comm _ _ _

lemma coindSec_morElt {y y' : D} (μ : y ⟶ y') (n : N) :
    coindSecₗ (B := B) hF (morElt k μ • n) = morElt k μ • coindSecₗ hF n := by
  ext x v
  simp only [coindSecₗ, LinearMap.coe_mk, AddHom.coe_mk, Res.mk_val, morElt_smul_res_val]
  by_cases h : y' = x
  · subst h
    simp only [dif_pos, eqToHom_refl, Category.comp_id, Coind.smul_toLin, coindElt_toLin,
      rmulRes_val, ← mul_smul]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [retr_mul_right hF]
  · rw [dif_neg h]
    simp only [coindElt_toLin, Coind.zero_toLin, ← mul_smul]
    exact Finset.sum_eq_zero fun z _ ↦ by rw [retr_mul_eq_zero hF μ h, zero_smul]

/-- The section `N → F^* (coinduced module)`. -/
def coindSec : N →ₗ[Linearization D k] Res B F (Coind B F N) :=
  linOfMorElt k (coindSecₗ hF) fun μ n ↦ coindSec_morElt hF μ n

omit G in
/-- The element `e_{F z}` at each `z`. -/
def unitRes : Res B F A :=
  Res.mk (fun z ↦ B.elt (𝟙 (F.obj z))) fun z ↦ by rw [smul_eq_mul, B.id_mul]

/-- The idempotent `e_{F x}` placed at `x`. -/
def iota (x : D) : Res B F A := morElt k (𝟙 x) • unitRes (B := B) (F := F)

lemma iota_val (x z : D) : (iota (B := B) (F := F) x).val z =
    if h : x = z then gelt (B := B) (F := F) (eqToHom h) else 0 := by
  rw [iota, morElt_smul_res_val]
  by_cases h : x = z
  · subst h
    simp [unitRes, gelt_id, B.id_mul]
  · simp [h]

lemma iota_val_self (x : D) : (iota (B := B) (F := F) x).val x = B.elt (𝟙 (F.obj x)) := by
  simp [iota_val, gelt_id]

lemma rmulRes_iota {y y' : D} (μ : y ⟶ y') :
    rmulRes (gelt (B := B) (F := F) μ) (iota (B := B) (F := F) y') = morElt k μ • iota y := by
  ext w
  rw [rmulRes_val, iota_val, morElt_smul_res_val, iota_val_self]
  by_cases h : y' = w
  · subst h
    simp [gelt_id, id_mul_gelt, gelt_mul_id]
  · simp [h]

lemma id_smul_iota (x : D) : morElt k (𝟙 x) • iota (B := B) (F := F) x = iota x := by
  rw [iota, ← mul_smul, morElt_mul, Category.comp_id]

/-- The retraction `F^* (coinduced module) → N`, as a `k`-linear map. -/
def coindRetₗ : Res B F (Coind B F N) →ₗ[k] N where
  toFun φ := ∑ x : D, (φ.val x).toLin (iota x)
  map_add' φ ψ := by simp [Finset.sum_add_distrib]
  map_smul' c φ := by simp [Finset.smul_sum]

lemma coindRet_morElt {y y' : D} (μ : y ⟶ y') (φ : Res B F (Coind B F N)) :
    coindRetₗ (morElt k μ • φ) = morElt k μ • coindRetₗ φ := by
  simp only [coindRetₗ, LinearMap.coe_mk, AddHom.coe_mk, morElt_smul_res_val, Finset.smul_sum]
  rw [Finset.sum_eq_single y' (fun z _ hz ↦ by rw [dif_neg (Ne.symm hz)]; rfl) (by simp),
    dif_pos rfl, Finset.sum_eq_single y (fun z _ hz ↦ ?_) (by simp)]
  · simp only [eqToHom_refl, Category.comp_id, Coind.smul_toLin, rmulRes_iota, map_smul]
  · rw [← id_smul_iota z, map_smul, ← mul_smul, morElt_mul_ne k _ μ hz, zero_smul]

/-- The retraction `F^* (coinduced module) → N`. -/
def coindRet : Res B F (Coind B F N) →ₗ[Linearization D k] N :=
  linOfMorElt k coindRetₗ fun μ φ ↦ coindRet_morElt μ φ

include hF in
lemma coindRet_coindSec (n : N) : coindRet (coindSec (B := B) hF n) = n := by
  change ∑ x : D, (coindElt hF x n).toLin (iota x) = n
  simp only [coindElt_toLin, iota_val]
  have : ∀ x : D, ∑ z : D,
      retr B F x z (if h : x = z then gelt (B := B) (F := F) (eqToHom h) else 0) • n =
      morElt k (𝟙 x) • n := fun x ↦ by
    rw [Finset.sum_eq_single x (fun z _ hz ↦ by rw [dif_neg (Ne.symm hz), map_zero, zero_smul])
      (by simp), dif_pos rfl, eqToHom_refl, retr_gelt hF]
  simp only [this, ← Finset.sum_smul, sum_morElt_id, one_smul]

end Section

/-! ### Restriction of module categories and the cleaving lemma -/

section Main

variable {B F} [G : B.Gauge F]

/-- `F^*` on linear maps. -/
def Res.map {M M' : Type u} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [AddCommGroup M'] [Module k M'] [Module A M'] [IsScalarTower k A M']
    (g : M →ₗ[A] M') : Res B F M →ₗ[Linearization D k] Res B F M' :=
  linOfMorElt k
    { toFun v := Res.mk (fun x ↦ g (v.val x)) fun x ↦ by rw [← map_smul, v.prop]
      map_add' v w := by ext x; simp
      map_smul' c v := by ext x; simp [LinearMap.map_smul_of_tower] }
    fun {x y} f v ↦ by
      ext z
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Res.mk_val, morElt_smul_res_val]
      split_ifs <;> simp

/-- The `k`-structure of an `A`-module. -/
abbrev kMod (M : ModuleCat.{u} A) : Module k M := Module.compHom M (algebraMap k A)

lemma kTower (M : ModuleCat.{u} A) :
    letI := kMod (k := k) M
    IsScalarTower k A M :=
  letI := kMod (k := k) M
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

variable (B F) in
/-- The restriction functor `F^* : Mod A ⥤ Mod k(D)`. -/
def resFunctor : ModuleCat.{u} A ⥤ ModuleCat.{u} (Linearization D k) where
  obj M :=
    letI := kMod (k := k) M
    haveI := kTower (k := k) M
    ModuleCat.of _ (Res B F M)
  map {M M'} g :=
    letI := kMod (k := k) M
    haveI := kTower (k := k) M
    letI := kMod (k := k) M'
    haveI := kTower (k := k) M'
    ModuleCat.ofHom (Res.map g.hom)
  map_id M := by
    letI := kMod (k := k) M
    haveI := kTower (k := k) M
    ext v x
    rfl
  map_comp {M M' M''} f g := by
    letI := kMod (k := k) M
    haveI := kTower (k := k) M
    letI := kMod (k := k) M'
    haveI := kTower (k := k) M'
    letI := kMod (k := k) M''
    haveI := kTower (k := k) M''
    ext v x
    rfl

instance : (resFunctor B F).Additive where
  map_add {M M'} f g := by
    letI := kMod (k := k) M
    haveI := kTower (k := k) M
    letI := kMod (k := k) M'
    haveI := kTower (k := k) M'
    ext v x
    rfl

omit G in
lemma finite_res (M : Type u) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [Module.Finite k M] : Module.Finite k (Res B F M) :=
  inferInstanceAs (Module.Finite k (resSub B F M))

lemma finite_coind (N : Type u) [AddCommGroup N] [Module (Linearization D k) N] [Module k N]
    [IsScalarTower k (Linearization D k) N] [Module.Finite k N] :
    Module.Finite k (Coind B F N) := by
  have := B.finiteDimensional
  have := finite_res (B := B) (F := F) A
  let ι : Coind B F N →ₗ[k] (Res B F A →ₗ[k] N) :=
    { toFun φ := φ.toLin.restrictScalars k
      map_add' φ ψ := by ext v; simp
      map_smul' c φ := by ext v; simp }
  refine Module.Finite.of_injective ι fun φ ψ h ↦ Coind.ext fun v ↦ ?_
  exact LinearMap.congr_fun h v

omit G in
/-- **The cleaving lemma** (Gabriel–Roiter 13.8): if `F : D ⥤ P` is cleaving,
the twist of `B` is a coboundary along `F`, and `A` is representation-finite,
so is `k(D)`. -/
theorem isRepresentationFinite_of_cleaving_gauge (hF : IsCleaving F) (G : B.Gauge F)
    (h : Statement.IsRepresentationFinite A) :
    Statement.IsRepresentationFinite (Linearization D k) := by
  have := B.finiteDimensional
  refine Reduction.isRepresentationFinite_of_retract k (resFunctor B F) (fun L hL ↦ ?_)
    (fun N hN _ ↦ ?_) h
  · let := kMod (k := k) L
    have := kTower (k := k) L
    have : Module.Finite k L := Module.Finite.trans A L
    have := finite_res (B := B) (F := F) L
    change Module.Finite (Linearization D k) (Res B F L)
    exact Module.Finite.of_restrictScalars_finite k _ _
  · letI : Module k N := Module.compHom N (algebraMap k (Linearization D k))
    haveI : IsScalarTower k (Linearization D k) N :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    have : Module.Finite k N := Module.Finite.trans (Linearization D k) N
    have := finite_coind (B := B) (F := F) N
    have hL : Module.Finite A (Coind B F N) := Module.Finite.of_restrictScalars_finite k _ _
    refine ⟨ModuleCat.of _ (Coind B F N), hL, ModuleCat.ofHom (coindSec hF),
      ModuleCat.ofHom coindRet, ?_⟩
    ext n
    exact coindRet_coindSec hF n

omit G in
/-- **The cleaving lemma**, untwisted form. -/
theorem isRepresentationFinite_of_cleaving (hF : IsCleaving F) (hU : B.Untwisted F)
    (h : Statement.IsRepresentationFinite A) :
    Statement.IsRepresentationFinite (Linearization D k) :=
  isRepresentationFinite_of_cleaving_gauge hF hU.gauge h

end Main

end RayQuiver

end LargeIndecomposable
