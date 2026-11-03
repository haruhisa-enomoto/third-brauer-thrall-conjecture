module

public import LargeIndecomposable.Quivers.PushDown.PushDownModule
public import LargeIndecomposable.KroneckerModules.Basic

/-!
# The cycle of a closed walk with a sink and the functor `L`

Setting 3.11 and Construction 3.12, in the dual form with a sink. A primitive
cyclically reduced closed walk `w` of length `r = n + 2` whose cycle `D_w` is
not oriented has a sink `u`. The cycle is recorded with `u` as `none` and the
other `n + 1` vertices `some 0, …, some n` in cyclic order; the two arrows into
`u` come from `some 0` (`first`) and `some n` (`second`), and the `n` middle
arrows join `some j` and `some (j + 1)` with an orientation `ε j` (`true`:
towards `some (j + 1)`).

For a Kronecker module `T = (V, W; a, b)`, `L(T)` has `W` at `u`, `V` at the
other vertices, `a` and `b` on the first and second arrows into `u`, and
identities on the middle arrows. This is the construction of the paper applied
to the opposite walk followed by the duality; with a sink, `L(S₋)` is the simple
representation at `u`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair

universe u

/-- Arrows of the cycle: the two arrows out of `u` and the middle arrows. -/
inductive CycArr (n : ℕ) where
  | first : CycArr n
  | second : CycArr n
  | mid : Fin n → CycArr n
  deriving DecidableEq

/-- `CycArr n ≃ Bool ⊕ Fin n`, for the finiteness instance. -/
def CycArr.equiv (n : ℕ) : CycArr n ≃ Bool ⊕ Fin n where
  toFun
    | .first => .inl true
    | .second => .inl false
    | .mid j => .inr j
  invFun
    | .inl true => .first
    | .inl false => .second
    | .inr j => .mid j
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with (_ | _) | j <;> rfl

instance (n : ℕ) : Fintype (CycArr n) := Fintype.ofEquiv _ (CycArr.equiv n).symm

/-- The cycle quiver `D_w` with sink `u`, for `n + 2` vertices and middle
orientations `ε`. -/
abbrev cycleQuiver (n : ℕ) (ε : Fin n → Bool) : FinQuiver where
  V := Option (Fin (n + 1))
  A := CycArr n
  src
    | .first => some 0
    | .second => some (Fin.last n)
    | .mid j => some (if ε j then j.castSucc else j.succ)
  tgt
    | .first => none
    | .second => none
    | .mid j => some (if ε j then j.succ else j.castSucc)

variable {k : Type u} [Field k] {n : ℕ} {ε : Fin n → Bool}

/-- Construction 3.12: the representation `L(T)` of the cycle. -/
def cycleRep (T : Kron k) : Rep k (cycleQuiver n ε) where
  obj x := x.elim T.W fun _ ↦ T.V
  map
    | .first => T.a
    | .second => T.b
    | .mid _ => 𝟙 T.V

/-- `L` on morphisms. -/
def cycleRepMap {T U : Kron k} (f : T ⟶ U) : cycleRep (ε := ε) T ⟶ cycleRep U where
  app
    | none => f.app one
    | some _ => f.app zero
  comm
    | .first => Kron.a_comp f
    | .second => Kron.b_comp f
    | .mid _ => by simp [cycleRep, cycleQuiver]

/-- The functor `L` of Construction 3.12. -/
def cycleFunctor (n : ℕ) (ε : Fin n → Bool) : Kron k ⥤ Rep k (cycleQuiver n ε) where
  obj := cycleRep
  map := cycleRepMap
  map_id T := by ext x; rcases x with _ | _ <;> rfl
  map_comp f g := by ext x; rcases x with _ | _ <;> rfl

lemma cycleFunctor_map_app_none {T U : Kron k} (f : T ⟶ U) :
    ((cycleFunctor n ε).map f).app none = f.app one := rfl

lemma cycleFunctor_map_app_some {T U : Kron k} (f : T ⟶ U) (j : Fin (n + 1)) :
    ((cycleFunctor n ε).map f).app (some j) = f.app zero := rfl

/-- `L` is full: the identity arrows force one common map on the
vertices other than the sink. -/
lemma cycleFunctor_full_aux {T U : Kron k} (φ : cycleRep (ε := ε) T ⟶ cycleRep U) :
    ∀ j : Fin (n + 1), φ.app (some j) = φ.app (some 0) := by
  intro j
  induction j using Fin.induction with
  | zero => rfl
  | succ j ih =>
    have h := Rep.Hom.comm φ (CycArr.mid j)
    dsimp only [cycleQuiver, cycleRep] at h
    have ih' : (φ.app (some j.castSucc) : T.V ⟶ U.V) = φ.app (some 0) := ih
    cases hj : ε j
    · rw [hj] at h
      change 𝟙 T.V ≫ (φ.app (some j.castSucc) : T.V ⟶ U.V) =
        (φ.app (some j.succ) : T.V ⟶ U.V) ≫ 𝟙 U.V at h
      erw [Category.id_comp, Category.comp_id] at h
      exact h.symm.trans ih'
    · rw [hj] at h
      change 𝟙 T.V ≫ (φ.app (some j.succ) : T.V ⟶ U.V) =
        (φ.app (some j.castSucc) : T.V ⟶ U.V) ≫ 𝟙 U.V at h
      erw [Category.id_comp, Category.comp_id] at h
      exact h.trans ih'

/-- The preimage under `L` of a morphism of cycle representations. -/
def cyclePreimage {T U : Kron k} (φ : cycleRep (ε := ε) T ⟶ cycleRep U) : T ⟶ U :=
  Kron.homMk (φ.app (some 0)) (φ.app none) (Rep.Hom.comm φ CycArr.first) (by
    have h := Rep.Hom.comm φ CycArr.second
    rw [cycleFunctor_full_aux φ (Fin.last n)] at h
    exact h)

lemma cycleFunctor_map_preimage {T U : Kron k} (φ : cycleRep (ε := ε) T ⟶ cycleRep U) :
    (cycleFunctor n ε).map (cyclePreimage φ) = φ := by
  refine Rep.hom_ext fun x ↦ ?_
  rcases x with _ | j
  · rfl
  · exact (cycleFunctor_full_aux φ j).symm

/-- `L` is fully faithful (Construction 3.12). -/
def cycleFunctorFullyFaithful : (cycleFunctor (k := k) n ε).FullyFaithful where
  preimage := cyclePreimage
  map_preimage := cycleFunctor_map_preimage
  preimage_map _ := Kron.hom_ext rfl rfl

end LargeIndecomposable
