module

public import LargeIndecomposable.Quivers.PushDown.PushDownModule

/-!
# Full subquivers and restriction of push-downs

For a finite quiver `D` and a finite set `T` of vertices, `fullSub D T` is the full subquiver on
`T`. A morphism `p : D → Q` restricts to `fullSubHom p T`. A representation `X` of `D` restricts
to `X.res T`; if `X` vanishes outside `T`, the push-down action of `kQ` on `X.res T` is the
conjugate of that on `X` by extension by zero (`pdAct_res`), so relations killing the push-down of
`X` kill that of `X.res T` (`pdAct_res_eq_zero`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory

universe u

namespace FinQuiver

variable (D : FinQuiver) (T : Finset D.V)

/-- The full subquiver on a set of vertices. -/
def fullSub : FinQuiver where
  V := {i // i ∈ T}
  A := {α : D.A // D.src α ∈ T ∧ D.tgt α ∈ T}
  src α := ⟨D.src α.1, α.2.1⟩
  tgt α := ⟨D.tgt α.1, α.2.2⟩

variable {D} {Q : FinQuiver}

/-- The restriction of a morphism of quivers to a full subquiver. -/
def fullSubHom (p : Hom D Q) : Hom (fullSub D T) Q where
  vert i := p.vert i.1
  arr α := p.arr α.1
  map_src α := p.map_src α.1
  map_tgt α := p.map_tgt α.1

lemma fullSubHom_locallyInjective {p : Hom D Q} (hp : p.LocallyInjective) :
    (fullSubHom T p).LocallyInjective :=
  ⟨fun e e' hs ha ↦ Subtype.ext (hp.1 e.1 e'.1 (congrArg Subtype.val hs) ha),
    fun e e' ht ha ↦ Subtype.ext (hp.2 e.1 e'.1 (congrArg Subtype.val ht) ha)⟩

end FinQuiver

namespace Rep

open FinQuiver

variable {k : Type u} [Field k] {D Q : FinQuiver} (T : Finset D.V)

/-- The restriction of a representation to a full subquiver. -/
def res (X : Rep k D) : Rep k (fullSub D T) where
  obj i := X.obj i.1
  map α := X.map α.1

variable (X : Rep k D) (hX : ∀ i, i ∉ T → Subsingleton (X.obj i))

/-- Extension by zero is an isomorphism of total spaces. -/
def resEquiv : X.Tot ≃ₗ[k] (X.res T).Tot where
  toFun x i := x i.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y i := if h : i ∈ T then y ⟨i, h⟩ else 0
  left_inv x := by
    funext i
    by_cases h : i ∈ T
    · simp [h]
    · simp only [h, dite_false]
      have := hX i h
      exact Subsingleton.elim _ _
  right_inv y := by
    funext i
    simp [i.2]
    rfl

lemma resEquiv_apply (x : X.Tot) (i : (fullSub D T).V) : resEquiv T X hX x i = x i.1 := rfl

lemma resEquiv_symm_apply (y : (X.res T).Tot) (i : D.V) :
    (resEquiv T X hX).symm y i = if h : i ∈ T then y ⟨i, h⟩ else 0 := rfl

/-- **The push-down of a restriction is conjugate to the push-down.** -/
theorem pdAct_res (p : FinQuiver.Hom D Q) :
    (X.res T).pdAct (fullSubHom T p) =
      ((resEquiv T X hX).conjAlgEquiv k).toAlgHom.comp (X.pdAct p) := by
  apply algHom_ext
  · intro q
    rw [pdAct_vertex, AlgHom.comp_apply, pdAct_vertex]
    refine LinearMap.ext fun y ↦ funext fun i ↦ ?_
    change (X.res T).pdVert (fullSubHom T p) q y i =
      resEquiv T X hX (X.pdVert p q ((resEquiv T X hX).symm y)) i
    rw [resEquiv_apply, pdVert_apply, pdVert_apply, resEquiv_symm_apply]
    simp [fullSubHom, i.2]
    rfl
  · intro c
    rw [pdAct_arrow, AlgHom.comp_apply, pdAct_arrow]
    refine LinearMap.ext fun y ↦ funext fun j ↦ ?_
    change (X.res T).pdArr (fullSubHom T p) c y j =
      resEquiv T X hX (X.pdArr p c ((resEquiv T X hX).symm y)) j
    rw [resEquiv_apply, pdArr_apply, pdArr_apply]
    classical
    -- arrows leaving `T` contribute nothing
    have hzero : ∀ e ∈ Finset.univ.filter (p.arr · = c), ¬(D.src e ∈ T ∧ D.tgt e ∈ T) →
        (Pi.single (D.tgt e) ((X.map e).hom ((resEquiv T X hX).symm y (D.src e))) : X.Tot) j.1
          = 0 := by
      intro e _ he
      by_cases hs : D.src e ∈ T
      · have ht : D.tgt e ∉ T := fun ht ↦ he ⟨hs, ht⟩
        have hne : j.1 ≠ D.tgt e := fun h ↦ ht (h ▸ j.2)
        exact Pi.single_eq_of_ne hne _
      · rw [resEquiv_symm_apply]
        simp [hs]
    rw [← Finset.sum_filter_of_ne (p := fun e ↦ D.src e ∈ T ∧ D.tgt e ∈ T)
      (fun e he h0 ↦ by_contra fun hn ↦ h0 (hzero e he hn))]
    rw [Finset.filter_filter]
    refine Finset.sum_bij (fun e _ ↦ e.1) ?_ ?_ ?_ ?_
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      exact ⟨he, e.2.1, e.2.2⟩
    · intro e _ e' _ h
      exact Subtype.ext h
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      refine ⟨⟨e, he.2⟩, ?_, rfl⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, he.1⟩
    · intro e _
      by_cases hj : j = (fullSub D T).tgt e
      · subst hj
        rw [Pi.single_eq_same]
        change _ = (Pi.single (D.tgt e.1) _ : X.Tot) (D.tgt e.1)
        rw [Pi.single_eq_same, resEquiv_symm_apply]
        simp [e.2.1]
        rfl
      · rw [Pi.single_eq_of_ne hj]
        have hj' : j.1 ≠ D.tgt e.1 := fun h ↦ hj (Subtype.ext h)
        rw [Pi.single_eq_of_ne hj']
        rfl

include hX in
/-- **Relations killing a push-down kill the push-down of the restriction.** -/
theorem pdAct_res_eq_zero (p : FinQuiver.Hom D Q) (z : Q.PathAlgebra k) (hz : X.pdAct p z = 0) :
    (X.res T).pdAct (fullSubHom T p) z = 0 := by
  rw [pdAct_res T X hX, AlgHom.comp_apply, hz, map_zero]

end Rep

end LargeIndecomposable
