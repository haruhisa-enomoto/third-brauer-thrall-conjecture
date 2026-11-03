module

public import LargeIndecomposable.RepresentationEmbeddings.CoveringConstruction.KroneckerPair

/-!
# Push-downs of `L(T)` are modules if two of them are

For a Kronecker pair and a quiver morphism `p : D → Q`, an element `z` of the
path algebra `kQ` that acts by zero on the push-downs of `L(S₋) = Q₀` and of
`L(P₁)`, where `P₁ = (k, k²)` is the projective Kronecker module (`L(P₁)` is
the universal extension of `P` by `Q₀²` given by `z₁, z₂`), acts by zero on the
push-down of every `L(T)` (`kills_of_generators`). Every vector of `L(T)` is a
sum of images of `L(f)` for morphisms `f : S₋ → T` and `f : P₁ → T`, and the
action of `kQ` on push-downs is natural.

So the `kills` condition of covering data with a Kronecker pair reduces to the
finite statement that `Q₀` and the universal extension are `A`-modules
(`PairCoveringData.mk'`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair TensorProduct Rep

universe u

namespace Covering

variable {k : Type u} [Field k]

variable (k) in
/-- The projective Kronecker module `P₁ = (k, k²; inl, inr)`. -/
def P1K : Kron k :=
  Kron.mk (ModuleCat.of k k) (ModuleCat.of k (k × k)) (ModuleCat.ofHom (LinearMap.inl k k k))
    (ModuleCat.ofHom (LinearMap.inr k k k))

/-- The morphism `P₁ → T` sending the generator to `v`. -/
def fromP1 (T : Kron k) (v : T.V) : P1K k ⟶ T :=
  (Kron.homMk (ModuleCat.ofHom (LinearMap.toSpanSingleton k _ v))
    (ModuleCat.ofHom (LinearMap.coprod (LinearMap.toSpanSingleton k _ (T.a.hom v))
      (LinearMap.toSpanSingleton k _ (T.b.hom v))))
    (ModuleCat.hom_ext (LinearMap.ext fun (t : k) ↦ by
      change LinearMap.coprod _ _ (t, 0) = T.a.hom (t • v)
      simp))
    (ModuleCat.hom_ext (LinearMap.ext fun (t : k) ↦ by
      change LinearMap.coprod _ _ (0, t) = T.b.hom (t • v)
      simp)))

/-- The morphism `S₋ → T` sending the generator to `w`. -/
def fromSminus (T : Kron k) (w : T.W) : Kron.Sminus k ⟶ T :=
  Kron.homMk 0 (ModuleCat.ofHom (LinearMap.toSpanSingleton k _ w))
    (hom_ext_punit' _ _) (hom_ext_punit' _ _)

namespace KroneckerPair

variable {D Q : FinQuiver} (K : KroneckerPair k D) (p : FinQuiver.Hom D Q)

lemma tot_single_inl (T : Kron k) (i : D.V) (q : K.Q₀.obj i) (w : T.W) :
    (Pi.single (M := K.space T) i (q ⊗ₜ[k] w, 0) : (K.functor.obj T).Tot) =
      (K.functor.map (fromSminus T w)).tot
        (Pi.single (M := K.space (Kron.Sminus k)) i (q ⊗ₜ[k] (show (Kron.Sminus k).W from (1 : k)), 0)) := by
  funext j
  by_cases hj : j = i
  · subst hj
    change Pi.single (M := K.space T) j _ j =
      K.vmap (fromSminus T w) j (Pi.single (M := K.space (Kron.Sminus k)) j _ j)
    rw [Pi.single_eq_same, Pi.single_eq_same]
    simp [vmap, fromSminus]
  · change Pi.single (M := K.space T) i _ j =
      K.vmap (fromSminus T w) j (Pi.single (M := K.space (Kron.Sminus k)) i _ j)
    rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, map_zero]

lemma tot_single_inr (T : Kron k) (i : D.V) (x : K.P.obj i) (v : T.V) :
    (Pi.single (M := K.space T) i (0, x ⊗ₜ[k] v) : (K.functor.obj T).Tot) =
      (K.functor.map (fromP1 T v)).tot
        (Pi.single (M := K.space (P1K k)) i (0, x ⊗ₜ[k] (show (P1K k).V from (1 : k)))) := by
  funext j
  by_cases hj : j = i
  · subst hj
    change Pi.single (M := K.space T) j _ j =
      K.vmap (fromP1 T v) j (Pi.single (M := K.space (P1K k)) j _ j)
    rw [Pi.single_eq_same, Pi.single_eq_same]
    simp [vmap, fromP1]
    erw [TensorProduct.map_tmul]
    change x ⊗ₜ[k] v = x ⊗ₜ[k] ((1 : k) • v)
    rw [one_smul]
  · change Pi.single (M := K.space T) i _ j =
      K.vmap (fromP1 T v) j (Pi.single (M := K.space (P1K k)) i _ j)
    rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, map_zero]

/-- The push-down of every `L(T)` is killed by the elements of `kQ` that kill the
push-downs of `L(S₋)` and `L(P₁)`. -/
theorem kills_of_generators (z : Q.PathAlgebra k)
    (h₁ : (K.functor.obj (Kron.Sminus k)).pdAct p z = 0) (h₂ : (K.functor.obj (P1K k)).pdAct p z = 0)
    (T : Kron k) : (K.functor.obj T).pdAct p z = 0 := by
  have hnat : ∀ {U : Kron k} (f : U ⟶ T) (y : (K.functor.obj U).Tot),
      (K.functor.obj T).pdAct p z ((K.functor.map f).tot y) =
        (K.functor.map f).tot ((K.functor.obj U).pdAct p z y) := by
    intro U f y
    have hf := Hom.isPdHom_tot p (K.functor.map f)
    exact (LinearMap.congr_fun (commute_pdAct p _ _ hf.1 hf.2 z) y).symm
  have hA : ∀ i (a : K.Q₀.obj i ⊗[k] T.W),
      (K.functor.obj T).pdAct p z (Pi.single (M := K.space T) i (a, 0)) = 0 := by
    intro i a
    induction a using TensorProduct.inductionOn with
    | tmul q w =>
      rw [tot_single_inl]
      exact (hnat _ _).trans (by rw [h₁]; exact map_zero _)
    | add a a' ha ha' =>
      have e : (Pi.single (M := K.space T) i (a + a', 0) : (K.functor.obj T).Tot) =
          Pi.single (M := K.space T) i (a, 0) + Pi.single (M := K.space T) i (a', 0) := by
        rw [← Pi.single_add]; simp
      rw [e]
      exact (map_add ((K.functor.obj T).pdAct p z) _ _).trans (by rw [ha, ha', add_zero])
  have hB : ∀ i (b : K.P.obj i ⊗[k] T.V),
      (K.functor.obj T).pdAct p z (Pi.single (M := K.space T) i (0, b)) = 0 := by
    intro i b
    induction b using TensorProduct.inductionOn with
    | tmul x v =>
      rw [tot_single_inr]
      exact (hnat _ _).trans (by rw [h₂]; exact map_zero _)
    | add b b' hb hb' =>
      have e : (Pi.single (M := K.space T) i (0, b + b') : (K.functor.obj T).Tot) =
          Pi.single (M := K.space T) i (0, b) + Pi.single (M := K.space T) i (0, b') := by
        rw [← Pi.single_add]; simp
      rw [e]
      exact (map_add ((K.functor.obj T).pdAct p z) _ _).trans (by rw [hb, hb', add_zero])
  refine LinearMap.ext fun x ↦ ?_
  have hx : x = ∑ i, ((Pi.single (M := K.space T) i ((x i).1, 0) : (K.functor.obj T).Tot) +
      Pi.single (M := K.space T) i (0, (x i).2)) := by
    conv_lhs => rw [← Finset.univ_sum_single (M := K.space T) x]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Pi.single_add, Prod.mk_add_mk, add_zero, zero_add]
    rfl
  rw [LinearMap.zero_apply, hx]
  refine (map_sum ((K.functor.obj T).pdAct p z) _ _).trans (Finset.sum_eq_zero fun i _ ↦ ?_)
  exact (map_add ((K.functor.obj T).pdAct p z) _ _).trans (by rw [hA, hB, add_zero])

end KroneckerPair

variable {A : Type u} [Ring A] [Algebra k A]

/-- Covering data with a Kronecker pair, checking `kills` only on `L(S₋)` and
`L(P₁)`. -/
def PairCoveringData.mk' (D Q : FinQuiver) (p : FinQuiver.Hom D Q) (locInj : p.LocallyInjective)
    (C : CoverData p) (K : KroneckerPair k D)
    (supp : ∀ i, Nontrivial (K.P.obj i) ∨ Nontrivial (K.Q₀.obj i))
    (π : Q.PathAlgebra k →ₐ[k] A) (surj : Function.Surjective π)
    (kills₁ : ∀ z, π z = 0 → (K.functor.obj (Kron.Sminus k)).pdAct p z = 0)
    (kills₂ : ∀ z, π z = 0 → (K.functor.obj (P1K k)).pdAct p z = 0) :
    PairCoveringData k A where
  D := D
  Q := Q
  p := p
  locInj := locInj
  C := C
  K := K
  supp := supp
  π := π
  surj := surj
  kills T z hz := K.kills_of_generators p z (kills₁ z hz) (kills₂ z hz) _

end Covering

end LargeIndecomposable
