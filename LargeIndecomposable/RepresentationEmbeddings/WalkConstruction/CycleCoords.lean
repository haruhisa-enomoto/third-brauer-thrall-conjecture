module

public import LargeIndecomposable.RepresentationEmbeddings.WalkConstruction.Cycle
public import LargeIndecomposable.RepresentationEmbeddings.WalkConstruction.Matching

/-!
# Cycle coordinates on the cycle quiver

The cycle quiver `cycleQuiver n ε` with `r = n + 2` vertices gets the cycle
coordinates of `FinQuiver.CycleCoords`: the sink `u` is at position `0`,
the vertex `some j` at position `j + 1`; the first arrow into `u` is at
position `0`, the middle arrow `j` at position `j + 1`, and the second arrow into
`u` at position `n + 1`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open FinQuiver

instance (n : ℕ) : Fact (1 < n + 2) := ⟨by omega⟩

namespace CycArr

/-- The position of an arrow of the cycle. -/
def posFun (n : ℕ) : CycArr n → ZMod (n + 2)
  | .first => 0
  | .mid j => ((j : ℕ) + 1 : ℕ)
  | .second => ((n + 1 : ℕ) : ZMod (n + 2))

lemma card (n : ℕ) : Fintype.card (CycArr n) = n + 2 := by
  rw [Fintype.card_congr (CycArr.equiv n)]; simp; omega

/-- The position of an arrow as a natural number. -/
def posNat (n : ℕ) : CycArr n → ℕ
  | .first => 0
  | .mid j => (j : ℕ) + 1
  | .second => n + 1

lemma posNat_lt (n : ℕ) (x : CycArr n) : posNat n x < n + 2 := by
  cases x <;> simp only [posNat] <;> omega

lemma posFun_eq (n : ℕ) (x : CycArr n) : posFun n x = (posNat n x : ZMod (n + 2)) := by
  cases x <;> simp [posFun, posNat]

lemma posNat_injective (n : ℕ) : Function.Injective (posNat n) := by
  intro x y h
  cases x <;> cases y <;> simp only [posNat] at h <;> first | rfl | omega |
    exact congrArg _ (Fin.ext (by omega))

lemma posFun_injective (n : ℕ) : Function.Injective (posFun n) := by
  intro x y h
  rw [posFun_eq, posFun_eq] at h
  have := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt (posNat_lt n x), ZMod.val_natCast_of_lt (posNat_lt n y)] at this
  exact posNat_injective n this

end CycArr

/-- The position of a vertex of the cycle. -/
def cyclePosFun (n : ℕ) : Option (Fin (n + 1)) → ZMod (n + 2)
  | none => 0
  | some j => ((j : ℕ) + 1 : ℕ)

lemma cyclePosFun_injective (n : ℕ) : Function.Injective (cyclePosFun n) := by
  have hv : ∀ m : ℕ, m < n + 2 → (((m : ℕ) : ZMod (n + 2))).val = m :=
    fun m hm ↦ ZMod.val_natCast_of_lt hm
  intro x y h
  have h' := congrArg ZMod.val h
  cases x <;> cases y <;> simp only [cyclePosFun, ZMod.val_zero] at h' ⊢
  · rename_i j; rw [hv _ (by omega)] at h'; omega
  · rename_i j; rw [hv _ (by omega)] at h'; omega
  · rename_i j j'
    rw [hv _ (by omega), hv _ (by omega)] at h'
    exact congrArg _ (Fin.ext (by omega))

/-- The cycle coordinates of `cycleQuiver n ε`. -/
def cycleCoords (n : ℕ) (ε : Fin n → Bool) : CycleCoords (cycleQuiver n ε) (n + 2) where
  pos := Equiv.ofBijective (cyclePosFun n) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨cyclePosFun_injective n, by simp⟩)
  eix := Equiv.ofBijective (CycArr.posFun n) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨CycArr.posFun_injective n, by rw [CycArr.card]; simp⟩)
  fwd
    | .first => false
    | .second => true
    | .mid j => ε j
  pos_src e := by
    cases e with
    | first =>
      show cyclePosFun n (some 0) = 0 + 1
      simp [cyclePosFun]
    | second =>
      show cyclePosFun n (some (Fin.last n)) = ((n + 1 : ℕ) : ZMod (n + 2))
      simp [cyclePosFun]
    | mid j =>
      show cyclePosFun n (some (if ε j then j.castSucc else j.succ)) =
        if ε j then CycArr.posFun n (.mid j) else CycArr.posFun n (.mid j) + 1
      cases ε j <;> simp [cyclePosFun, CycArr.posFun]
  pos_tgt e := by
    cases e with
    | first => rfl
    | second =>
      show (0 : ZMod (n + 2)) = ((n + 1 : ℕ) : ZMod (n + 2)) + 1
      rw [show ((n + 1 : ℕ) : ZMod (n + 2)) + 1 = ((n + 2 : ℕ) : ZMod (n + 2)) by push_cast; ring,
        ZMod.natCast_self]
    | mid j =>
      show cyclePosFun n (some (if ε j then j.succ else j.castSucc)) =
        if ε j then CycArr.posFun n (.mid j) + 1 else CycArr.posFun n (.mid j)
      cases ε j <;> simp [cyclePosFun, CycArr.posFun]

end LargeIndecomposable
