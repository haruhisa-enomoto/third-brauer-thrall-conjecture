module

public import LargeIndecomposable.Modules.Corners.Corner
public import LargeIndecomposable.Modules.KrullSchmidt.IndecomposableFullyFaithful
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Tactic.NoncommRing

/-!
# The Morita equivalence of a full corner

For an idempotent `e` of a ring `A`, write `C = eAe` for the corner ring and
`eA` for the right ideal, a left `C`-module. The functor

`Morita.functor e : Mod C ⥤ Mod A`, `M ↦ Hom_C(eA, M)`, `(a φ)(x) = φ(x a)`

is fully faithful for every idempotent (`full`, `faithful`); when `e` is full,
that is `∑ᵢ aᵢ e bᵢ = 1` for some `aᵢ, bᵢ`, it is essentially surjective
(`X ≅ Hom_C(eA, eX)`) and hence an equivalence of categories (`isEquivalence`).
This is the Morita equivalence used in the proof of Lemma 3.1.

For a `k`-algebra `A` it is `k`-linear, preserves short exact sequences
(`preservesShortExact`), and multiplies `k`-dimensions by at most the number
of terms in `∑ aᵢ e bᵢ = 1` (`rank_le`, `le_rank`), so it preserves
finite-dimensionality and the dimension of infinite-dimensional modules.

The construction follows the right-module coinduction of
`LargeIndecomposable/Foundations/CornerRepFinite.lean` and
`FullIdempotent.lean` (`multiplicative-bases-deformations`, commit
7b9f39f221d8a420a1531f487a3b93ae6d26ce85), transposed to left modules.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement

universe u

namespace Morita

variable {A : Type u} [Ring A] {e : A}

/-- The right ideal `eA`. -/
def rightIdeal (e : A) : AddSubgroup A where
  carrier := {x | e * x = x}
  add_mem' {x y} hx hy := by simp only [Set.mem_ofPred_eq] at *; rw [mul_add, hx, hy]
  zero_mem' := by simp
  neg_mem' {x} hx := by simp only [Set.mem_ofPred_eq] at *; rw [mul_neg, hx]

theorem mem_rightIdeal {x : A} : x ∈ rightIdeal e ↔ e * x = x := Iff.rfl

variable (he : IsIdempotentElem e)

instance : SMul he.Corner (rightIdeal e) where
  smul c x := ⟨Corner.val he c * x, by
    rw [mem_rightIdeal, ← mul_assoc, Corner.mul_val]⟩

theorem smul_val (c : he.Corner) (x : rightIdeal e) :
    ((c • x : rightIdeal e) : A) = Corner.val he c * x := rfl

instance : Module he.Corner (rightIdeal e) where
  one_smul x := Subtype.ext (by rw [smul_val, Corner.val_one]; exact x.2)
  mul_smul c d x := Subtype.ext (by simp only [smul_val, Corner.val_mul, mul_assoc])
  smul_zero c := Subtype.ext (by simp [smul_val])
  smul_add c x y := Subtype.ext (by simp [smul_val, mul_add])
  add_smul c d x := Subtype.ext (by simp [smul_val, add_mul])
  zero_smul x := Subtype.ext (by simp [smul_val])

/-- Right multiplication by `a` on `eA`. -/
def rmul (a : A) : rightIdeal e →ₗ[he.Corner] rightIdeal e where
  toFun x := ⟨x * a, by rw [mem_rightIdeal, ← mul_assoc, x.2]⟩
  map_add' x y := Subtype.ext (add_mul _ _ _)
  map_smul' c x := Subtype.ext (by simp [smul_val, mul_assoc])

@[simp]
theorem rmul_val (a : A) (x : rightIdeal e) : ((rmul he a x : rightIdeal e) : A) = x * a := rfl

/-- `Hom_C(eA, M)`. -/
def Obj (M : ModuleCat.{u} he.Corner) : Type u := rightIdeal e →ₗ[he.Corner] M

instance (M : ModuleCat.{u} he.Corner) : AddCommGroup (Obj he M) :=
  inferInstanceAs (AddCommGroup (rightIdeal e →ₗ[he.Corner] M))

instance (M : ModuleCat.{u} he.Corner) : FunLike (Obj he M) (rightIdeal e) M :=
  inferInstanceAs (FunLike (rightIdeal e →ₗ[he.Corner] M) (rightIdeal e) M)

instance (M : ModuleCat.{u} he.Corner) :
    LinearMapClass (Obj he M) he.Corner (rightIdeal e) M :=
  inferInstanceAs (LinearMapClass (rightIdeal e →ₗ[he.Corner] M) he.Corner (rightIdeal e) M)

/-- An element of `Hom_C(eA, M)` as a linear map. -/
def Obj.toLin {M : ModuleCat.{u} he.Corner} (φ : Obj he M) : rightIdeal e →ₗ[he.Corner] M := φ

@[simp]
theorem Obj.toLin_apply {M : ModuleCat.{u} he.Corner} (φ : Obj he M) (x : rightIdeal e) :
    Obj.toLin he φ x = φ x := rfl

/-- A linear map as an element of `Hom_C(eA, M)`. -/
def Obj.ofLin {M : ModuleCat.{u} he.Corner} (φ : rightIdeal e →ₗ[he.Corner] M) : Obj he M := φ

@[simp]
theorem Obj.ofLin_apply {M : ModuleCat.{u} he.Corner} (φ : rightIdeal e →ₗ[he.Corner] M)
    (x : rightIdeal e) : Obj.ofLin he φ x = φ x := rfl

@[ext]
theorem Obj.ext {M : ModuleCat.{u} he.Corner} {φ ψ : Obj he M} (h : ∀ x, φ x = ψ x) : φ = ψ :=
  show (φ : rightIdeal e →ₗ[he.Corner] M) = ψ from LinearMap.ext h

@[simp]
theorem Obj.add_apply {M : ModuleCat.{u} he.Corner} (φ ψ : Obj he M) (x : rightIdeal e) :
    (φ + ψ) x = φ x + ψ x := rfl

@[simp]
theorem Obj.zero_apply {M : ModuleCat.{u} he.Corner} (x : rightIdeal e) :
    (0 : Obj he M) x = 0 := rfl

instance (M : ModuleCat.{u} he.Corner) : SMul A (Obj he M) where
  smul a φ := Obj.ofLin he ((Obj.toLin he φ).comp (rmul he a))

@[simp]
theorem Obj.smul_apply {M : ModuleCat.{u} he.Corner} (a : A) (φ : Obj he M) (x : rightIdeal e) :
    (a • φ) x = φ (rmul he a x) := rfl

instance (M : ModuleCat.{u} he.Corner) : Module A (Obj he M) where
  one_smul φ := Obj.ext he fun x ↦ by
    rw [Obj.smul_apply]; congr 1; exact Subtype.ext (mul_one _)
  mul_smul a b φ := Obj.ext he fun x ↦ by
    simp only [Obj.smul_apply]; congr 1; exact Subtype.ext (mul_assoc _ _ _).symm
  smul_zero a := Obj.ext he fun x ↦ rfl
  smul_add a φ ψ := Obj.ext he fun x ↦ rfl
  add_smul a b φ := Obj.ext he fun x ↦ by
    simp only [Obj.smul_apply, Obj.add_apply, ← map_add]
    congr 1; exact Subtype.ext (mul_add _ _ _)
  zero_smul φ := Obj.ext he fun x ↦ by
    simp only [Obj.smul_apply, Obj.zero_apply]
    rw [show rmul he 0 x = 0 from Subtype.ext (mul_zero _), map_zero]

/-- The functor on objects. -/
abbrev coind (M : ModuleCat.{u} he.Corner) : ModuleCat.{u} A := ModuleCat.of A (Obj he M)

/-- Postcomposition. -/
def mapLin {M N : ModuleCat.{u} he.Corner} (f : M ⟶ N) : Obj he M →ₗ[A] Obj he N where
  toFun φ := Obj.ofLin he (f.hom.comp (Obj.toLin he φ))
  map_add' φ ψ := Obj.ext he fun x ↦ map_add f.hom (φ x) (ψ x)
  map_smul' a φ := Obj.ext he fun x ↦ rfl

@[simp]
theorem mapLin_apply {M N : ModuleCat.{u} he.Corner} (f : M ⟶ N) (φ : Obj he M)
    (x : rightIdeal e) : mapLin he f φ x = f.hom (φ x) := rfl

/-- The coinduction functor `M ↦ Hom_C(eA, M)`. -/
abbrev functor : ModuleCat.{u} he.Corner ⥤ ModuleCat.{u} A where
  obj M := coind he M
  map f := ModuleCat.ofHom (mapLin he f)
  map_id M := by ext φ; rfl
  map_comp f g := by ext φ; rfl

@[simp]
theorem functor_map_hom {M N : ModuleCat.{u} he.Corner} (f : M ⟶ N) (φ : Obj he M) :
    ((functor he).map f).hom φ = mapLin he f φ := rfl

instance : (functor he).Additive where
  map_add {M N f g} := by ext φ; rfl

/-! ### Full faithfulness -/

/-- The generator `e ∈ eA`. -/
def eP : rightIdeal e := ⟨e, he.eq⟩

include he in
theorem cornerOf_mem (x : rightIdeal e) : (x : A) * e ∈ Subsemigroup.corner e := by
  rw [Corner.mem_iff he, ← mul_assoc, x.2, mul_assoc, he.eq]
  exact ⟨rfl, rfl⟩

/-- `x ↦ xe`, from `eA` to `eAe`. -/
def cornerOf (x : rightIdeal e) : he.Corner := Corner.mk he ((x : A) * e) (cornerOf_mem he x)

theorem cornerOf_add (x y : rightIdeal e) : cornerOf he (x + y) = cornerOf he x + cornerOf he y :=
  Corner.ext he (add_mul _ _ _)

theorem cornerOf_smul (c : he.Corner) (x : rightIdeal e) :
    cornerOf he (c • x) = c * cornerOf he x :=
  Corner.ext he (by simp [cornerOf, smul_val, mul_assoc])

theorem cornerOf_eP : cornerOf he (eP he) = 1 := Corner.ext he (by simp [cornerOf, eP, he.eq])

variable {he} in
/-- `m ↦ (x ↦ (xe) m)`, from `M` to `Hom_C(eA, M)`. -/
def psi {M : ModuleCat.{u} he.Corner} (m : M) : Obj he M :=
  Obj.ofLin he
    { toFun x := cornerOf he x • m
      map_add' x y := by rw [cornerOf_add, add_smul]
      map_smul' c x := by rw [cornerOf_smul, mul_smul]; rfl }

@[simp]
theorem psi_apply {M : ModuleCat.{u} he.Corner} (m : M) (x : rightIdeal e) :
    psi m x = cornerOf he x • m := rfl

theorem psi_eP {M : ModuleCat.{u} he.Corner} (m : M) : psi m (eP he) = m := by
  rw [psi_apply, cornerOf_eP, one_smul]

theorem psi_add {M : ModuleCat.{u} he.Corner} (m n : M) : psi (m + n) = psi m + psi n :=
  Obj.ext he fun x ↦ by simp [smul_add]

theorem psi_smul {M : ModuleCat.{u} he.Corner} (c : he.Corner) (m : M) :
    psi (c • m) = Corner.val he c • psi m :=
  Obj.ext he fun x ↦ by
    rw [psi_apply, Obj.smul_apply, psi_apply, ← mul_smul]
    congr 1
    apply Corner.ext he
    simp [cornerOf, mul_assoc, Corner.val_mul_e, Corner.mul_val]

theorem psi_apply_self {M : ModuleCat.{u} he.Corner} (φ : Obj he M) (x : rightIdeal e) :
    psi (φ x) = (x : A) • φ :=
  Obj.ext he fun y ↦ by
    rw [psi_apply, Obj.smul_apply, ← map_smul]
    congr 1
    apply Subtype.ext
    simp [cornerOf, smul_val, mul_assoc, show e * (x : A) = x from x.2]

instance faithful : (functor he).Faithful where
  map_injective {M N f g} h := by
    ext m
    have := congrArg (fun F ↦ Obj.toLin he (F.hom (psi m)) (eP he)) h
    simpa [functor_map_hom, psi_eP, cornerOf_eP] using this

/-- The preimage of a morphism. -/
def preimageLin {M N : ModuleCat.{u} he.Corner} (g : coind he M ⟶ coind he N) : M →ₗ[he.Corner] N where
  toFun m := Obj.toLin he (g.hom (psi m)) (eP he)
  map_add' m n := by rw [psi_add, map_add]; rfl
  map_smul' c m := by
    rw [psi_smul, map_smul, RingHom.id_apply]
    change Obj.toLin he (g.hom (psi m)) (rmul he (Corner.val he c) (eP he)) =
      c • Obj.toLin he (g.hom (psi m)) (eP he)
    rw [← map_smul]
    congr 1
    apply Subtype.ext
    simp [eP, smul_val, Corner.mul_val, Corner.val_mul_e]

instance full : (functor he).Full where
  map_surjective {M N} g := ⟨ModuleCat.ofHom (preimageLin he g), by
    refine ModuleCat.hom_ext (LinearMap.ext fun (φ : Obj he M) ↦ Obj.ext he fun x ↦ ?_)
    change Obj.toLin he (g.hom (psi (φ x))) (eP he) = _
    rw [psi_apply_self, map_smul]
    change Obj.toLin he (g.hom φ) (rmul he x (eP he)) = _
    congr 1
    exact Subtype.ext (by simp [eP, show e * (x : A) = x from x.2])⟩

/-! ### Essential surjectivity for a full idempotent -/

/-- `eX` as an additive subgroup of an `A`-module `X`. -/
def cornerSub (X : ModuleCat.{u} A) : AddSubgroup X where
  carrier := {x | e • x = x}
  add_mem' {x y} hx hy := by simp only [Set.mem_ofPred_eq] at *; rw [smul_add, hx, hy]
  zero_mem' := by simp
  neg_mem' {x} hx := by simp only [Set.mem_ofPred_eq] at *; rw [smul_neg, hx]

instance (X : ModuleCat.{u} A) : SMul he.Corner (cornerSub (e := e) X) where
  smul c x := ⟨Corner.val he c • (x : X), by
    change e • _ = _
    rw [smul_smul, Corner.mul_val]⟩

theorem cornerSub_smul_val (X : ModuleCat.{u} A) (c : he.Corner) (x : cornerSub (e := e) X) :
    ((c • x : cornerSub (e := e) X) : X) = Corner.val he c • (x : X) := rfl

instance (X : ModuleCat.{u} A) : Module he.Corner (cornerSub (e := e) X) where
  one_smul x := Subtype.ext (by rw [cornerSub_smul_val, Corner.val_one]; exact x.2)
  mul_smul c d x := Subtype.ext (by simp only [cornerSub_smul_val, Corner.val_mul, mul_smul])
  smul_zero c := Subtype.ext (by simp [cornerSub_smul_val])
  smul_add c x y := Subtype.ext (by simp [cornerSub_smul_val, smul_add])
  add_smul c d x := Subtype.ext (by simp [cornerSub_smul_val, add_smul])
  zero_smul x := Subtype.ext (by simp [cornerSub_smul_val])

/-- `eX` as a `C`-module. -/
abbrev res (X : ModuleCat.{u} A) : ModuleCat.{u} he.Corner := ModuleCat.of he.Corner (cornerSub (e := e) X)

/-- `X → Hom_C(eA, eX)`, `x ↦ (p ↦ p x)`. -/
def theta (X : ModuleCat.{u} A) : X →ₗ[A] Obj he (res he X) where
  toFun x := Obj.ofLin he
    { toFun p := ⟨(p : A) • x, by change e • _ = _; rw [smul_smul, p.2]⟩
      map_add' p q := Subtype.ext (add_smul _ _ _)
      map_smul' c p := Subtype.ext (by
        change ((c • p : rightIdeal e) : A) • x = Corner.val he c • ((p : A) • x)
        rw [smul_val, mul_smul]) }
  map_add' x y := Obj.ext he fun p ↦ Subtype.ext (smul_add _ _ _)
  map_smul' a x := Obj.ext he fun p ↦ Subtype.ext (by
    change (p : A) • a • x = ((p : A) * a) • x
    rw [mul_smul])

theorem theta_apply_val (X : ModuleCat.{u} A) (x : X) (p : rightIdeal e) :
    ((theta he X x p : cornerSub (e := e) X) : X) = (p : A) • x := rfl

/-- `e` is full: `∑ᵢ aᵢ e bᵢ = 1`. -/
def IsFull (e : A) : Prop := ∃ (n : ℕ) (a b : Fin n → A), ∑ i, a i * e * b i = 1

variable {he}

variable (he) in
/-- The element `e bᵢ ∈ eA`. -/
def eb (b : A) : rightIdeal e := ⟨e * b, by rw [mem_rightIdeal, ← mul_assoc, he.eq]⟩

variable (he) in
include he in
theorem coeff_mem (a : A) (p : rightIdeal e) : (p : A) * a * e ∈ Subsemigroup.corner e := by
  rw [Corner.mem_iff he]
  constructor
  · rw [← mul_assoc, ← mul_assoc, show e * (p : A) = p from p.2]
  · rw [mul_assoc _ e e, he.eq]

variable (he) in
/-- The coefficient `p a e ∈ eAe` of `p ∈ eA`. -/
def coeff (a : A) : rightIdeal e →ₗ[he.Corner] he.Corner where
  toFun p := Corner.mk he ((p : A) * a * e) (coeff_mem he a p)
  map_add' p q := Corner.ext he (by simp [add_mul])
  map_smul' c p := Corner.ext he (by simp [smul_val, mul_assoc])

/-- `p = ∑ᵢ (p aᵢ e) (e bᵢ)`. -/
theorem decomp {n : ℕ} {a b : Fin n → A} (h : ∑ i, a i * e * b i = 1) (p : rightIdeal e) :
    p = ∑ i, coeff he (a i) p • eb he (b i) := by
  apply Subtype.ext
  rw [AddSubgroup.val_finsetSum]
  simp only [smul_val, coeff, eb, LinearMap.coe_mk, AddHom.coe_mk, Corner.val_mk]
  conv_lhs => rw [← mul_one (p : A), ← h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show (p : A) * a i * e * (e * b i) = (p : A) * a i * (e * e) * b i by noncomm_ring, he.eq]
  noncomm_ring

theorem apply_eq_sum {M : ModuleCat.{u} he.Corner} {n : ℕ} {a b : Fin n → A}
    (h : ∑ i, a i * e * b i = 1) (φ : Obj he M) (p : rightIdeal e) :
    φ p = ∑ i, coeff he (a i) p • φ (eb he (b i)) := by
  conv_lhs => rw [decomp (he := he) h p]
  rw [map_sum]
  simp only [map_smul]

theorem theta_bijective (hfull : IsFull e) (X : ModuleCat.{u} A) :
    Function.Bijective (theta he X) := by
  obtain ⟨n, a, b, h⟩ := hfull
  refine ⟨fun x y hxy ↦ ?_, fun φ ↦ ?_⟩
  · have key : ∀ x : X, x = ∑ i, a i • ((theta he X x (eb he (b i)) : cornerSub (e := e) X) : X) := by
      intro x
      simp only [theta_apply_val, eb, smul_smul]
      conv_lhs => rw [← one_smul A x, ← h, Finset.sum_smul]
      simp only [mul_assoc]
    rw [key x, key y, hxy]
  · refine ⟨∑ i, a i • ((φ (eb he (b i)) : cornerSub (e := e) X) : X), Obj.ext he fun p ↦ ?_⟩
    apply Subtype.ext
    rw [theta_apply_val, apply_eq_sum h φ p, AddSubgroup.val_finsetSum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [cornerSub_smul_val, smul_smul]
    have hφ : e • ((φ (eb he (b i)) : cornerSub (e := e) X) : X) = φ (eb he (b i)) := (φ (eb he (b i))).2
    conv_lhs => rw [← hφ, smul_smul]
    simp [coeff, mul_assoc]

/-- `X ≅ Hom_C(eA, eX)` for a full idempotent. -/
def unitIso (hfull : IsFull e) (X : ModuleCat.{u} A) : X ≅ (functor he).obj (res he X) :=
  (LinearEquiv.ofBijective (theta he X) (theta_bijective hfull X)).toModuleIso

theorem essSurj (hfull : IsFull e) : (functor he).EssSurj :=
  ⟨fun X ↦ ⟨res he X, ⟨(unitIso hfull X).symm⟩⟩⟩

/-- For a full idempotent, coinduction is an equivalence of categories. -/
theorem isEquivalence (hfull : IsFull e) : (functor he).IsEquivalence where
  essSurj := essSurj hfull

/-! ### Exactness -/

/-- Exactness in the three-part form of `Statement.IsRepresentationEmbedding`. -/
theorem preservesShortExact (hfull : IsFull e) {L M N : ModuleCat.{u} he.Corner}
    (f : L ⟶ M) (g : M ⟶ N) (hf : Function.Injective f.hom) (hg : Function.Surjective g.hom)
    (hfg : LinearMap.range f.hom = LinearMap.ker g.hom) :
    Function.Injective ((functor he).map f).hom ∧ Function.Surjective ((functor he).map g).hom ∧
      LinearMap.range ((functor he).map f).hom = LinearMap.ker ((functor he).map g).hom := by
  obtain ⟨n, a, b, h⟩ := hfull
  refine ⟨fun (φ ψ : Obj he L) hφψ ↦ Obj.ext he fun x ↦ hf ?_, fun (φ : Obj he N) ↦ ?_, ?_⟩
  · simpa [functor_map_hom] using congrArg (fun χ : Obj he M ↦ χ x) hφψ
  · choose m hm using fun i ↦ hg (φ (eb he (b i)))
    let ψ : Obj he M := Obj.ofLin he
      { toFun p := ∑ i, coeff he (a i) p • m i
        map_add' p q := by simp [add_smul, Finset.sum_add_distrib]
        map_smul' c p := by simp [mul_smul, Finset.smul_sum] }
    refine ⟨ψ, Obj.ext he fun p ↦ ?_⟩
    rw [functor_map_hom, mapLin_apply, apply_eq_sum h φ p]
    simp [ψ, hm]
  · refine Submodule.ext fun (φ : Obj he M) ↦ ?_
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨χ, rfl⟩
      refine Obj.ext he fun x ↦ ?_
      simp only [Obj.zero_apply]
      have : f.hom (χ x) ∈ LinearMap.ker g.hom := hfg ▸ LinearMap.mem_range_self _ _
      exact this
    · intro hφ
      have hmem : ∀ x, φ x ∈ LinearMap.range f.hom := fun x ↦ by
        rw [hfg, LinearMap.mem_ker]
        simpa [functor_map_hom] using congrArg (fun χ : Obj he N ↦ χ x) hφ
      let ψ : Obj he L := Obj.ofLin he
        ((LinearEquiv.ofInjective f.hom hf).symm.toLinearMap.comp
          ((Obj.toLin he φ).codRestrict (LinearMap.range f.hom) hmem))
      refine ⟨ψ, Obj.ext he fun x ↦ ?_⟩
      rw [functor_map_hom, mapLin_apply]
      exact LinearEquiv.ofInjective_symm_apply (f := f.hom) (h := hf) (⟨φ x, hmem x⟩ : LinearMap.range f.hom)

end Morita

end LargeIndecomposable
