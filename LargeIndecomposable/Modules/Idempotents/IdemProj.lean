module

public import LargeIndecomposable.Modules.Homological.Restrict

/-!
# Projectives of idempotents

For an idempotent `e`, the left ideal `Ae = {a | a e = a}` is a projective module with
`Hom_A(Ae, M) ≅ eM = {m | e m = m}` (`homProjEquiv`), via `f ↦ f e`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- The regular module. -/
abbrev FDMod.self : FDMod k A where
  carrier := A

/-- The left ideal `Ae`. -/
def leftIdeal {e : A} (he : IsIdempotentElem e) : Submodule A A where
  carrier := {a | a * e = a}
  add_mem' {a b} ha hb := by
    change (a + b) * e = a + b
    rw [add_mul, show a * e = a from ha, show b * e = b from hb]
  zero_mem' := zero_mul e
  smul_mem' c a ha := by
    change c * a * e = c * a
    rw [mul_assoc, show a * e = a from ha]

/-- **The projective `P(e) = Ae`.** -/
abbrev projE {e : A} (he : IsIdempotentElem e) : FDMod k A :=
  FDMod.ofSub (P := (FDMod.self : FDMod k A)) (leftIdeal he)

lemma e_mem {e : A} (he : IsIdempotentElem e) : e ∈ leftIdeal he := he.eq

/-- The subspace `eM = {m | e m = m}`. -/
def eSub (M : FDMod k A) (e : A) : Submodule k M where
  carrier := {m | e • m = m}
  add_mem' {m n} hm hn := by
    change e • (m + n) = m + n
    rw [smul_add, show e • m = m from hm, show e • n = n from hn]
  zero_mem' := smul_zero e
  smul_mem' c m hm := by
    change e • (c • m) = c • m
    rw [smul_comm, show e • m = m from hm]

/-- **`Hom(Ae, M) ≅ eM`.** -/
def homProjEquiv {e : A} (he : IsIdempotentElem e) (M : FDMod k A) :
    (leftIdeal he →ₗ[A] M) ≃ₗ[k] eSub M e where
  toFun f := ⟨f ⟨e, e_mem he⟩, by
    change e • f ⟨e, e_mem he⟩ = f ⟨e, e_mem he⟩
    rw [← map_smul]
    congr 1
    exact Subtype.ext he.eq⟩
  map_add' f g := rfl
  map_smul' c f := rfl
  invFun m :=
    { toFun a := (a : A) • (m : M)
      map_add' a b := add_smul _ _ _
      map_smul' c a := by
        change (c * (a : A)) • (m : M) = c • ((a : A) • (m : M))
        rw [mul_smul] }
  left_inv f := by
    apply LinearMap.ext
    rintro ⟨a, ha⟩
    change a • f ⟨e, e_mem he⟩ = f ⟨a, ha⟩
    rw [← map_smul]
    congr 1
    exact Subtype.ext ha
  right_inv m := Subtype.ext m.2

lemma homProjEquiv_symm_apply {e : A} (he : IsIdempotentElem e) (M : FDMod k A)
    (m : eSub M e) (a : leftIdeal he) :
    (homProjEquiv (k := k) he M).symm m a = (a : A) • (m : M) := rfl

/-- **`Ae` is projective.** -/
theorem projE_lift {e : A} (he : IsIdempotentElem e) {X Y : FDMod k A} (p : X ⟶ Y)
    (hp : Function.Surjective (FDMod.lin p)) (f : projE (k := k) he ⟶ Y) :
    ∃ g : projE (k := k) he ⟶ X, g ≫ p = f := by
  obtain ⟨x, hx⟩ := hp (FDMod.lin f ⟨e, e_mem he⟩)
  have hex : e • x ∈ eSub X e := by
    change e • (e • x) = e • x
    rw [← mul_smul, he.eq]
  refine ⟨(FDMod.ofLin ((homProjEquiv (k := k) he X).symm ⟨e • x, hex⟩)), ?_⟩
  apply FDMod.hom_ext; apply (homProjEquiv (k := k) he Y).injective
  apply Subtype.ext
  change FDMod.lin p ((e : A) • (e • x)) = FDMod.lin f ⟨e, e_mem he⟩
  rw [← mul_smul, he.eq, map_smul, hx, ← map_smul]
  congr 1
  exact Subtype.ext he.eq

/-- **If `eAe = k e` and `e ≠ 0`, then `Ae` is a brick.** -/
theorem projE_brick {e : A} (he : IsIdempotentElem e) (h1 : ∀ a : A, ∃ c : k, e * a * e = c • e)
    (φ : projE (k := k) he ⟶ projE he) : ∃ c : k, FDMod.lin φ = c • LinearMap.id := by
  let y : A := (FDMod.lin φ ⟨e, e_mem he⟩ : A)
  have hy : y * e = y := (FDMod.lin φ ⟨e, e_mem he⟩).2
  have hey : e * y = y := by
    have := congrArg Subtype.val (map_smul (FDMod.lin φ) e (⟨e, e_mem he⟩ : leftIdeal he))
    have h2 : (e • (⟨e, e_mem he⟩ : leftIdeal he)) = ⟨e, e_mem he⟩ := Subtype.ext he.eq
    rw [h2] at this
    exact this.symm
  obtain ⟨c, hc⟩ := h1 y
  have hyc : y = c • e := by rw [← hc, mul_assoc, hy, hey]
  refine ⟨c, LinearMap.ext fun ⟨a, ha⟩ ↦ Subtype.ext ?_⟩
  have h3 := congrArg Subtype.val (map_smul (FDMod.lin φ) a (⟨e, e_mem he⟩ : leftIdeal he))
  have h4 : (a • (⟨e, e_mem he⟩ : leftIdeal he)) = ⟨a, ha⟩ := Subtype.ext ha
  rw [h4] at h3
  change (FDMod.lin φ ⟨a, ha⟩ : A) = c • a
  rw [h3]
  change a * y = c • a
  rw [hyc, mul_smul_comm, ha]

end LargeIndecomposable.AR
