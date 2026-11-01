module

public import LargeIndecomposable.AuslanderReiten.Irreducible.IrrSummand

/-!
# Modules living on a set of points

An `A`-module lives on `T'` if the idempotents outside `T'` kill it (`LivesOn`), i.e. its support
lies in `T'` (`livesOn_iff_supp`). Such a module is the restriction of a module over the quotient
algebra `A / ⟨e_v : v ∉ T'⟩` (`descendQ`, `descIsoQ`), built through the universal property of the
quotient, and restrictions live on `T'` (`livesOn_res`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

namespace DirData

variable {D : DirData k A}

/-- `M` lives on `T'`. -/
def LivesOn (T' : Set D.ι) (M : FDMod k A) : Prop := ∀ v, v ∉ T' → ∀ m : M, D.e v • m = 0

lemma livesOn_iff_supp (T' : Set D.ι) (M : FDMod k A) : LivesOn T' M ↔ D.Supp M ⊆ T' := by
  constructor
  · rintro h y ⟨m, hm⟩
    by_contra hy
    exact hm (h y hy m)
  · intro h v hv m
    by_contra h0
    exact hv (h ⟨m, h0⟩)

variable {T' : Set D.ι}

lemma livesOn_res (X : FDMod k (D.QAlg T')) : LivesOn T' (resFD (D.qmap T') X) := by
  intro v hv m
  change D.qmap T' (D.e v) • (show X from m) = 0
  rw [D.qmap_e_out T' hv, zero_smul]

/-- The action of `A` on a module living on `T'`, through the quotient. -/
def actQ (M : FDMod k A) (hM : LivesOn T' M) : D.QAlg T' →ₐ[k] Module.End k M :=
  RingQuot.liftAlgHom k ⟨Algebra.lsmul k k M, by
    rintro _ _ ⟨⟨v, hv, rfl⟩, rfl⟩
    rw [map_zero]
    exact LinearMap.ext fun m ↦ hM v hv m⟩

lemma actQ_qmap (M : FDMod k A) (hM : LivesOn T' M) (a : A) (m : M) :
    actQ M hM (D.qmap T' a) m = a • m := by
  simp [actQ]

/-- **A module living on `T'` as a module over the quotient algebra.** -/
def descendQ (M : FDMod k A) (hM : LivesOn T' M) : FDMod k (D.QAlg T') :=
  letI : Module (D.QAlg T') M := Module.compHom M (actQ M hM).toRingHom
  { carrier := M
    isScalarTower := ⟨fun c a m ↦ by
      change actQ M hM (c • a) m = c • actQ M hM a m
      rw [map_smul]
      rfl⟩ }

/-- The identity from the restriction of the descent to `M`. -/
def descIsoQ (M : FDMod k A) (hM : LivesOn T' M) : resFD (D.qmap T') (descendQ M hM) ⟶ M :=
  show resFD (D.qmap T') (descendQ M hM) →ₗ[A] M from
  { toFun x := (show M from x)
    map_add' _ _ := rfl
    map_smul' a x := actQ_qmap M hM a x }

/-- The identity from `M` to the restriction of its descent. -/
def descIsoQInv (M : FDMod k A) (hM : LivesOn T' M) : M ⟶ resFD (D.qmap T') (descendQ M hM) :=
  show M →ₗ[A] resFD (D.qmap T') (descendQ M hM) from
  { toFun x := (show resFD (D.qmap T') (descendQ M hM) from x)
    map_add' _ _ := rfl
    map_smul' a x := (actQ_qmap M hM a x).symm }

lemma isoM_descend (M : FDMod k A) (hM : LivesOn T' M) :
    IsoM (resFD (D.qmap T') (descendQ M hM)) M :=
  ⟨descIsoQ M hM, Function.bijective_id⟩

lemma isoM_descend' (M : FDMod k A) (hM : LivesOn T' M) :
    IsoM M (resFD (D.qmap T') (descendQ M hM)) :=
  ⟨descIsoQInv M hM, Function.bijective_id⟩

lemma livesOn_of_inj {M N : FDMod k A} (g : M ⟶ N) (hg : Function.Injective (FDMod.lin g))
    (hN : LivesOn T' N) : LivesOn T' M := by
  rw [livesOn_iff_supp] at hN ⊢
  exact (supp_of_inj g hg).trans hN

lemma livesOn_of_surj {M N : FDMod k A} (g : M ⟶ N) (hg : Function.Surjective (FDMod.lin g))
    (hM : LivesOn T' M) : LivesOn T' N := by
  rw [livesOn_iff_supp] at hM ⊢
  exact (supp_of_surj g hg).trans hM

lemma livesOn_iso {M N : FDMod k A} (h : IsoM M N) (hM : LivesOn T' M) : LivesOn T' N :=
  livesOn_of_surj h.choose h.choose_spec.2 hM

end DirData

end LargeIndecomposable.AR
