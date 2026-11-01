module

public import LargeIndecomposable.RepresentationEmbeddings.CoveringConstruction.KroneckerPair
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# The free covering of a quiver

For a finite quiver `Q` let `G = FreeGroup Q₁`. The quiver `Q̃` has vertices
`(h, v)` with `h ∈ G`, `v ∈ Q₀`, and an arrow `(h, a) : (h, s(a)) → (h·a, t(a))`
for each arrow `a` of `Q`. The group `G` acts freely by left multiplication on
the first coordinate, its orbits are the fibres of `(h, v) ↦ v`, and equally
labelled arrows are translates. A finite set `S` of vertices of `Q̃` spans a
finite full subquiver `D_S` with a locally injective map `p_S : D_S → Q`, and
the action gives covering data (`FreeCover.coverData`). `G` is torsion-free.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory FinQuiver

universe u

namespace FreeCover

variable (Q : FinQuiver)

/-- The free group on the arrows. -/
abbrev G : Type := FreeGroup Q.A

/-- The vertices of the free covering. -/
abbrev Vert : Type := G Q × Q.V

instance : MulAction (G Q) (Vert Q) where
  smul g x := (g * x.1, x.2)
  one_smul x := by simp [HSMul.hSMul]
  mul_smul g h x := by simp [HSMul.hSMul, mul_assoc]

lemma smul_def (g : G Q) (x : Vert Q) : g • x = (g * x.1, x.2) := rfl

variable {Q} (S : Finset (Vert Q))

/-- The arrows of the full subquiver on `S`: an arrow `a` of `Q` at a vertex
`(h, s(a))` of `S` whose target `(h·a, t(a))` lies in `S`. -/
def Arr : Type := {x : S × Q.A // Q.src x.2 = x.1.1.2 ∧ (x.1.1.1 * FreeGroup.of x.2, Q.tgt x.2) ∈ S}

instance : Fintype (Arr S) := by unfold Arr; infer_instance

instance : DecidableEq (Arr S) := by unfold Arr; infer_instance

/-- The full subquiver of the free covering on `S`. -/
def quiver : FinQuiver where
  V := S
  A := Arr S
  src x := x.1.1
  tgt x := ⟨(x.1.1.1.1 * FreeGroup.of x.1.2, Q.tgt x.1.2), x.2.2⟩

/-- The covering map restricted to `S`. -/
def proj : FinQuiver.Hom (quiver S) Q where
  vert x := x.1.2
  arr x := x.1.2
  map_src x := x.2.1
  map_tgt _ := rfl

lemma proj_locInj : (proj S).LocallyInjective := by
  constructor
  · intro e e' hs hl
    refine Subtype.ext (Prod.ext hs hl)
  · intro e e' ht hl
    have h1 := congrArg (fun x : S ↦ x.1.1) ht
    simp only [quiver] at h1
    change e.1.2 = e'.1.2 at hl
    rw [hl, mul_left_inj] at h1
    refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext h1 ?_)) hl)
    rw [← e.2.1, ← e'.2.1, hl]

/-- The covering data of the full subquiver on `S`. -/
def coverData : Covering.CoverData (proj S) where
  G := G Q
  torsionFree g hg n hn := by
    intro h
    exact hg ((pow_left_injective (Nat.pos_iff_ne_zero.1 hn)) (h.trans (one_pow n).symm))
  R₀ := Vert Q
  free g x h := by
    have := congrArg Prod.fst h
    rw [smul_def] at this
    exact mul_eq_right.1 this
  ι := Subtype.val
  ι_inj := Subtype.val_injective
  fibre x y h := ⟨y.1.1 * x.1.1⁻¹, by
    rw [smul_def]
    refine Prod.ext (by simp) ?_
    exact h.symm⟩
  arrows α β h := by
    refine ⟨β.1.1.1.1 * α.1.1.1.1⁻¹, ?_, ?_⟩
    · rw [smul_def]
      refine Prod.ext (by simp [quiver]) ?_
      change β.1.1.1.2 = α.1.1.1.2
      rw [← β.2.1, ← α.2.1]
      exact congrArg Q.src h.symm
    · rw [smul_def]
      refine Prod.ext ?_ ?_
      · change β.1.1.1.1 * FreeGroup.of β.1.2 =
          β.1.1.1.1 * α.1.1.1.1⁻¹ * (α.1.1.1.1 * FreeGroup.of α.1.2)
        change α.1.2 = β.1.2 at h
        rw [h]; group
      · change Q.tgt β.1.2 = Q.tgt α.1.2
        exact congrArg Q.tgt h.symm

end FreeCover

namespace Covering

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]

variable (k A) in
/-- The covering alternative over the free covering of the quiver of a
presentation: a presentation `π : kQ → A`, a finite set `S` of vertices of the
free covering, a Kronecker pair on the full subquiver on `S` whose supports
cover `S`, such that the kernel of `π` acts by zero on the push-downs. -/
structure FreeCoverPair where
  /-- The quiver of the presentation. -/
  Q : FinQuiver
  /-- The presentation. -/
  π : Q.PathAlgebra k →ₐ[k] A
  surj : Function.Surjective π
  /-- The finite piece of the free covering. -/
  S : Finset (FreeCover.Vert Q)
  /-- The Kronecker pair. -/
  K : KroneckerPair k (FreeCover.quiver S)
  supp : ∀ i, Nontrivial (K.P.obj i) ∨ Nontrivial (K.Q₀.obj i)
  kills : ∀ (T : Dfin k) (z : Q.PathAlgebra k), π z = 0 →
    (K.functor.obj ((DfinToKfin k).obj T)).pdAct (FreeCover.proj S) z = 0

/-- Free-covering data are covering data with a Kronecker pair. -/
def FreeCoverPair.toPairCoveringData (W : FreeCoverPair k A) : PairCoveringData k A where
  D := FreeCover.quiver W.S
  Q := W.Q
  p := FreeCover.proj W.S
  locInj := FreeCover.proj_locInj W.S
  C := FreeCover.coverData W.S
  K := W.K
  supp := W.supp
  π := W.π
  surj := W.surj
  kills := W.kills

end Covering

end LargeIndecomposable
