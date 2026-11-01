module

public import LargeIndecomposable.RayCategories.RoiterVanishing.RayTackleReplacement
public import Mathlib.Data.Fintype.Pigeonhole

@[expose] public section

/-!
# From crowns to closed ray chains

Package the cancellation law of BGRS 1.13(d).  Factorization witnesses around
a crown in `x/P` then form a closed alternating chain.  In particular, absence
of infinite chains implies the four- and six-crown consequences used in 8.5.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The two-sided nonzero cancellation law for a ray category, BGRS 1.13(d). -/
class HasRayCancellation (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] : Prop where
  cancel_right : ∀ {X Y Z : C} (f g : X ⟶ Y) (h : Y ⟶ Z),
    f ≫ h = g ≫ h → f ≫ h ≠ 0 → f = g
  cancel_left : ∀ {X Y Z : C} (h : X ⟶ Y) (f g : Y ⟶ Z),
    h ≫ f = h ≫ g → h ≫ f ≠ 0 → f = g

/-- In a finite endomorphism monoid with nonzero cancellation and no
nontrivial automorphisms, every nonidentity endomorphism is nilpotent. -/
theorem endomorphism_nilpotent_of_finite_of_rayCancellation
    [HasRayCancellation C] {X : C} [Finite (End X)]
    (hid : (𝟙 X : End X) ≠ 0)
    (hauto : ∀ (a : End X), [IsIso a] → a = 𝟙 X)
    (f : End X) (hf : f ≠ 𝟙 X) :
    ∃ n : ℕ, 0 < n ∧ f ^ n = (0 : End X) := by
  obtain ⟨i, j, hij, hpows⟩ :=
    Finite.exists_ne_map_eq_of_infinite (α := ℕ) (f ^ ·)
  wlog hlt : i < j generalizing i j
  · have hji : j < i := by omega
    exact this j i hij.symm hpows.symm hji
  by_cases hzero : f ^ i = 0
  · refine ⟨i, ?_, hzero⟩
    exact Nat.pos_of_ne_zero fun hi ↦ by
      subst i
      simp only [pow_zero] at hzero
      exact hid hzero
  · exfalso
    let d := j - i
    have hd : 0 < d := by
      dsimp [d]
      omega
    have hcomp :
        (f ^ i : End X) ≫ (f ^ d : End X) =
          (f ^ i : End X) ≫ (𝟙 X : End X) := by
      change f ^ d * f ^ i = 1 * f ^ i
      rw [← pow_add]
      have hdadd : d + i = j := by
        dsimp [d]
        omega
      rw [hdadd, ← hpows]
      simp
    have hcomp_ne :
        (f ^ i : End X) ≫ (f ^ d : End X) ≠ 0 := by
      rw [hcomp, Category.comp_id]
      exact hzero
    have hdone : f ^ d = (𝟙 X : End X) :=
      HasRayCancellation.cancel_left (f ^ i) (f ^ d) (𝟙 X)
        hcomp hcomp_ne
    have hunitpow : IsUnit (f ^ d) := by
      rw [hdone]
      exact isUnit_one
    have hunit : IsUnit f :=
      (isUnit_pow_iff (Nat.ne_of_gt hd)).1 hunitpow
    letI : IsIso f := (isUnit_iff_isIso f).1 hunit
    exact hf (hauto f)

/-- Ray cancellation implies the source-stabilizer law used in
`IsFiniteRayCategory`. -/
theorem source_stabilizer_trivial_of_rayCancellation
    [HasRayCancellation C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (a : End X)
    (hfg : f ≫ g ≠ 0) (heq : (a ≫ f) ≫ g = f ≫ g) :
    a = 𝟙 X := by
  have haf : a ≫ f = f :=
    HasRayCancellation.cancel_right (a ≫ f) f g heq
      (heq.trans_ne hfg)
  apply HasRayCancellation.cancel_right a (𝟙 X) f
  · simpa using haf
  · intro hzero
    apply hfg
    rw [← haf, hzero, zero_comp]

namespace NonzeroMorphismFrom

/-- Choose the nonzero postfactor witnessing one inequality in `x/P`. -/
def chosenPostfactor {x : C} {f g : NonzeroMorphismFrom x}
    (hfg : f ≤ g) : NonzeroHom f.target g.target :=
  ⟨Classical.choose hfg, by
    intro hzero
    apply g.ne_zero
    rw [← Classical.choose_spec hfg, hzero, comp_zero]⟩

@[simp]
theorem comp_chosenPostfactor {x : C}
    {f g : NonzeroMorphismFrom x} (hfg : f ≤ g) :
    f.hom ≫ (chosenPostfactor hfg).1 = g.hom :=
  Classical.choose_spec hfg

/-- Factors from two incomparable lower rays to one common upper ray are
incomparable at their common target. -/
theorem chosenPostfactor_targetIncomparable
    [HasRayCancellation C]
    {x : C} {a b u : NonzeroMorphismFrom x}
    (hab : OrderIncomparable a b) (hau : a ≤ u) (hbu : b ≤ u) :
    RayTargetIncomparable (chosenPostfactor hau) (chosenPostfactor hbu) := by
  constructor
  · rintro ⟨h, hh⟩
    apply hab.1
    refine ⟨h, ?_⟩
    apply HasRayCancellation.cancel_right
      (a.hom ≫ h) b.hom (chosenPostfactor hbu).1
    · rw [Category.assoc, hh, comp_chosenPostfactor,
        comp_chosenPostfactor]
    · intro hzero
      apply u.ne_zero
      rw [← comp_chosenPostfactor hau, ← hh, ← Category.assoc]
      exact hzero
  · rintro ⟨h, hh⟩
    apply hab.2
    refine ⟨h, ?_⟩
    apply HasRayCancellation.cancel_right
      (b.hom ≫ h) a.hom (chosenPostfactor hau).1
    · rw [Category.assoc, hh, comp_chosenPostfactor,
        comp_chosenPostfactor]
    · intro hzero
      apply u.ne_zero
      rw [← comp_chosenPostfactor hbu, ← hh, ← Category.assoc]
      exact hzero

/-- Factors from one lower ray to two incomparable upper rays are
incomparable at their common source. -/
theorem chosenPostfactor_sourceIncomparable
    {x : C} {a u v : NonzeroMorphismFrom x}
    (huv : OrderIncomparable u v) (hau : a ≤ u) (hav : a ≤ v) :
    RaySourceIncomparable (chosenPostfactor hau) (chosenPostfactor hav) := by
  constructor
  · rintro ⟨h, hh⟩
    apply huv.1
    refine ⟨h, ?_⟩
    rw [← comp_chosenPostfactor hau, Category.assoc, hh,
      comp_chosenPostfactor hav]
  · rintro ⟨h, hh⟩
    apply huv.2
    refine ⟨h, ?_⟩
    rw [← comp_chosenPostfactor hav, Category.assoc, hh,
      comp_chosenPostfactor hau]

end NonzeroMorphismFrom

namespace NonzeroMorphismTo

/-- Choose the nonzero prefactor witnessing one inequality in the
fixed-target order. -/
def chosenPrefactor {y : C} {f g : NonzeroMorphismTo y}
    (hfg : f ≤ g) : NonzeroHom f.source g.source :=
  ⟨Classical.choose hfg, by
    intro hzero
    apply f.ne_zero
    rw [← Classical.choose_spec hfg, hzero, zero_comp]⟩

@[simp]
theorem chosenPrefactor_comp {y : C}
    {f g : NonzeroMorphismTo y} (hfg : f ≤ g) :
    (chosenPrefactor hfg).1 ≫ g.hom = f.hom :=
  Classical.choose_spec hfg

/-- Prefactors from two incomparable lower rays to one common upper ray are
incomparable at their common target. -/
theorem chosenPrefactor_targetIncomparable
    {y : C} {a b u : NonzeroMorphismTo y}
    (hab : OrderIncomparable a b) (hau : a ≤ u) (hbu : b ≤ u) :
    RayTargetIncomparable (chosenPrefactor hau) (chosenPrefactor hbu) := by
  constructor
  · rintro ⟨h, hh⟩
    apply hab.1
    refine ⟨h, ?_⟩
    rw [← chosenPrefactor_comp hbu, ← chosenPrefactor_comp hau,
      ← Category.assoc, hh]
  · rintro ⟨h, hh⟩
    apply hab.2
    refine ⟨h, ?_⟩
    rw [← chosenPrefactor_comp hau, ← chosenPrefactor_comp hbu,
      ← Category.assoc, hh]

/-- Prefactors from one lower ray to two incomparable upper rays are
incomparable at their common source. -/
theorem chosenPrefactor_sourceIncomparable
    [HasRayCancellation C]
    {y : C} {a u v : NonzeroMorphismTo y}
    (huv : OrderIncomparable u v) (hau : a ≤ u) (hav : a ≤ v) :
    RaySourceIncomparable (chosenPrefactor hau) (chosenPrefactor hav) := by
  constructor
  · rintro ⟨h, hh⟩
    apply huv.1
    refine ⟨h, ?_⟩
    have heq : (chosenPrefactor hau).1 ≫ (h ≫ v.hom) = a.hom := by
      rw [← Category.assoc, hh, chosenPrefactor_comp hav]
    apply HasRayCancellation.cancel_left
      (chosenPrefactor hau).1 (h ≫ v.hom) u.hom
    · rw [heq, chosenPrefactor_comp hau]
    · exact fun hzero ↦ a.ne_zero (heq.symm.trans hzero)
  · rintro ⟨h, hh⟩
    apply huv.2
    refine ⟨h, ?_⟩
    have heq : (chosenPrefactor hav).1 ≫ (h ≫ u.hom) = a.hom := by
      rw [← Category.assoc, hh, chosenPrefactor_comp hau]
    apply HasRayCancellation.cancel_left
      (chosenPrefactor hav).1 (h ≫ u.hom) v.hom
    · rw [heq, chosenPrefactor_comp hav]
    · exact fun hzero ↦ a.ne_zero (heq.symm.trans hzero)

end NonzeroMorphismTo

/-- The next vertex in a nonempty finite cyclic index type. -/
def finCycleNext {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨(i.1 + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩

/-- A crown of length `n+3` in the fixed-source factorization order.  Only
adjacent lower and upper incomparabilities and the two incident order edges
are retained, exactly the data needed to form an alternating chain. -/
structure RayOrderCrown (x : C) (n : ℕ) where
  lower : Fin (n + 3) → NonzeroMorphismFrom x
  upper : Fin (n + 3) → NonzeroMorphismFrom x
  lower_next_incomparable : ∀ i,
    OrderIncomparable (lower i) (lower (finCycleNext i))
  upper_next_incomparable : ∀ i,
    OrderIncomparable (upper i) (upper (finCycleNext i))
  lower_le_upper : ∀ i, lower i ≤ upper i
  next_lower_le_upper : ∀ i, lower (finCycleNext i) ≤ upper i

namespace RayOrderCrown

variable {x : C} {n : ℕ}

/-- The selected factor from the current lower ray to the current upper ray. -/
def currentFactor (c : RayOrderCrown (C := C) x n) (i : Fin (n + 3)) :=
  NonzeroMorphismFrom.chosenPostfactor (c.lower_le_upper i)

/-- The selected factor from the next lower ray to the current upper ray. -/
def nextFactor (c : RayOrderCrown (C := C) x n) (i : Fin (n + 3)) :=
  NonzeroMorphismFrom.chosenPostfactor (c.next_lower_le_upper i)

/-- Package a current crown factor as a varying-endpoint nonzero morphism. -/
def factorState (c : RayOrderCrown (C := C) x n) (i : Fin (n + 3)) :
    NonzeroCategoryMorphism C :=
  ⟨(c.lower i).target, (c.upper i).target,
    (c.currentFactor i).1, (c.currentFactor i).2⟩

/-- Every edge around a crown is one alternating ray-chain step. -/
theorem factorState_step [HasRayCancellation C]
    (c : RayOrderCrown (C := C) x n) (i : Fin (n + 3)) :
    RayChainStep (c.factorState i) (c.factorState (finCycleNext i)) := by
  refine ⟨c.nextFactor i, ?_, ?_⟩
  · exact NonzeroMorphismFrom.chosenPostfactor_targetIncomparable
      (c.lower_next_incomparable i)
      (c.lower_le_upper i) (c.next_lower_le_upper i)
  · exact NonzeroMorphismFrom.chosenPostfactor_sourceIncomparable
      (c.upper_next_incomparable i)
      (c.next_lower_le_upper i)
      (c.lower_le_upper (finCycleNext i))

/-- Periodic indexing of a crown by the natural numbers. -/
def cycleIndex (r : ℕ) : Fin (n + 3) :=
  ⟨r % (n + 3), Nat.mod_lt _ (by omega)⟩

theorem cycleIndex_succ (r : ℕ) :
    cycleIndex (n := n) (r + 1) =
      finCycleNext (cycleIndex (n := n) r) := by
  apply Fin.ext
  simp [cycleIndex, finCycleNext, Nat.add_mod]

/-- Repeating the factorization witnesses around a crown gives an infinite
alternating BGRS chain. -/
def toInfinite [HasRayCancellation C]
    (c : RayOrderCrown (C := C) x n) : RayInfiniteChain (C := C) where
  state r := c.factorState (cycleIndex r)
  step r := by
    rw [cycleIndex_succ]
    exact c.factorState_step (cycleIndex r)

/-- Reverse an incomparability. -/
theorem _root_.LargeIndecomposable.OrderIncomparable.symm
    {P : Type*} [LE P] {a b : P} (h : OrderIncomparable a b) :
    OrderIncomparable b a :=
  ⟨h.2, h.1⟩

/-- A full four-element crown gives a cyclic crown of length four by going
around it twice. -/
def ofFour {a b u v : NonzeroMorphismFrom x}
    (h : IsFourCrown a b u v) : RayOrderCrown (C := C) x 1 := by
  rcases h with ⟨hab, huv, hau, hbu, hav, hbv⟩
  let hba := hab.symm
  let hvu := huv.symm
  refine
    { lower := ![a, b, a, b]
      upper := ![u, v, u, v]
      lower_next_incomparable := ?_
      upper_next_incomparable := ?_
      lower_le_upper := ?_
      next_lower_le_upper := ?_ }
  · intro i
    fin_cases i <;> simp [finCycleNext] <;> assumption
  · intro i
    fin_cases i <;> simp [finCycleNext] <;> assumption
  · intro i
    fin_cases i <;> simp <;> assumption
  · intro i
    fin_cases i <;> simp [finCycleNext] <;> assumption

/-- A full six-element crown gives its cyclic crown of length three. -/
def ofSix {a b c ab bc ac : NonzeroMorphismFrom x}
    (h : IsSixCrown a b c ab bc ac) : RayOrderCrown (C := C) x 0 := by
  rcases h with ⟨hab, hac, hbc, habbc, habac, hbcac,
    haab, hbab, hbbc, hcbc, haac, hcac, -, -, -⟩
  let hca := hac.symm
  let hacab := habac.symm
  refine
    { lower := ![a, b, c]
      upper := ![ab, bc, ac]
      lower_next_incomparable := ?_
      upper_next_incomparable := ?_
      lower_le_upper := ?_
      next_lower_le_upper := ?_ }
  · intro i
    fin_cases i <;> simp [finCycleNext] <;> assumption
  · intro i
    fin_cases i <;> simp [finCycleNext] <;> assumption
  · intro i
    fin_cases i <;> simp <;> assumption
  · intro i
    fin_cases i <;> simp [finCycleNext] <;> assumption

end RayOrderCrown

/-- A crown in the fixed-target factorization order.  Its chosen prefactors
form the orientation-dual alternating chain. -/
structure RayCoOrderCrown (y : C) (n : ℕ) where
  lower : Fin (n + 3) → NonzeroMorphismTo y
  upper : Fin (n + 3) → NonzeroMorphismTo y
  lower_next_incomparable : ∀ i,
    OrderIncomparable (lower i) (lower (finCycleNext i))
  upper_next_incomparable : ∀ i,
    OrderIncomparable (upper i) (upper (finCycleNext i))
  lower_le_upper : ∀ i, lower i ≤ upper i
  next_lower_le_upper : ∀ i, lower (finCycleNext i) ≤ upper i

namespace RayCoOrderCrown

variable {y : C} {n : ℕ}

/-- The selected prefactor from the current lower ray to the current upper
ray. -/
def currentFactor (c : RayCoOrderCrown (C := C) y n)
    (i : Fin (n + 3)) :=
  NonzeroMorphismTo.chosenPrefactor (c.lower_le_upper i)

/-- The selected prefactor from the next lower ray to the current upper
ray. -/
def nextFactor (c : RayCoOrderCrown (C := C) y n)
    (i : Fin (n + 3)) :=
  NonzeroMorphismTo.chosenPrefactor (c.next_lower_le_upper i)

/-- Package a current cocrown prefactor as a varying-endpoint nonzero
morphism. -/
def factorState (c : RayCoOrderCrown (C := C) y n)
    (i : Fin (n + 3)) : NonzeroCategoryMorphism C :=
  ⟨(c.lower i).source, (c.upper i).source,
    (c.currentFactor i).1, (c.currentFactor i).2⟩

/-- Every edge around a fixed-target crown is one alternating ray-chain
step. -/
theorem factorState_step [HasRayCancellation C]
    (c : RayCoOrderCrown (C := C) y n) (i : Fin (n + 3)) :
    RayChainStep (c.factorState i) (c.factorState (finCycleNext i)) := by
  refine ⟨c.nextFactor i, ?_, ?_⟩
  · exact NonzeroMorphismTo.chosenPrefactor_targetIncomparable
      (c.lower_next_incomparable i)
      (c.lower_le_upper i) (c.next_lower_le_upper i)
  · exact NonzeroMorphismTo.chosenPrefactor_sourceIncomparable
      (c.upper_next_incomparable i)
      (c.next_lower_le_upper i)
      (c.lower_le_upper (finCycleNext i))

/-- Periodic indexing of a fixed-target crown by the natural numbers. -/
def cycleIndex (r : ℕ) : Fin (n + 3) :=
  ⟨r % (n + 3), Nat.mod_lt _ (by omega)⟩

theorem cycleIndex_succ (r : ℕ) :
    cycleIndex (n := n) (r + 1) =
      finCycleNext (cycleIndex (n := n) r) := by
  apply Fin.ext
  simp [cycleIndex, finCycleNext, Nat.add_mod]

/-- Repeating the chosen prefactors around a fixed-target crown gives an
infinite alternating BGRS chain. -/
def toInfinite [HasRayCancellation C]
    (c : RayCoOrderCrown (C := C) y n) : RayInfiniteChain (C := C) where
  state r := c.factorState (cycleIndex r)
  step r := by
    rw [cycleIndex_succ]
    exact c.factorState_step (cycleIndex r)

/-- A full fixed-target four-element crown gives a cyclic crown of length
four. -/
def ofFour {a b u v : NonzeroMorphismTo y}
    (h : IsFourCrown a b u v) : RayCoOrderCrown (C := C) y 1 := by
  rcases h with ⟨hab, huv, hau, hbu, hav, hbv⟩
  let hba := hab.symm
  let hvu := huv.symm
  refine
    { lower := ![a, b, a, b]
      upper := ![u, v, u, v]
      lower_next_incomparable := ?_
      upper_next_incomparable := ?_
      lower_le_upper := ?_
      next_lower_le_upper := ?_ }
  · intro i
    fin_cases i <;> simp [finCycleNext] <;> assumption
  · intro i
    fin_cases i <;> simp [finCycleNext] <;> assumption
  · intro i
    fin_cases i <;> simp <;> assumption
  · intro i
    fin_cases i <;> simp [finCycleNext] <;> assumption

/-- A full fixed-target six-element crown gives its cyclic crown of length
three. -/
def ofSix {a b c ab bc ac : NonzeroMorphismTo y}
    (h : IsSixCrown a b c ab bc ac) : RayCoOrderCrown (C := C) y 0 := by
  rcases h with ⟨hab, hac, hbc, habbc, habac, hbcac,
    haab, hbab, hbbc, hcbc, haac, hcac, -, -, -⟩
  let hca := hac.symm
  let hacab := habac.symm
  refine
    { lower := ![a, b, c]
      upper := ![ab, bc, ac]
      lower_next_incomparable := ?_
      upper_next_incomparable := ?_
      lower_le_upper := ?_
      next_lower_le_upper := ?_ }
  · intro i
    fin_cases i <;> simp [finCycleNext] <;> assumption
  · intro i
    fin_cases i <;> simp [finCycleNext] <;> assumption
  · intro i
    fin_cases i <;> simp <;> assumption
  · intro i
    fin_cases i <;> simp [finCycleNext] <;> assumption

end RayCoOrderCrown

/-- The no-infinite-chain hypothesis and ray cancellation exclude the four-
and six-crowns needed in BGRS 8.5. -/
theorem isRayCrownFree_of_noInfinite
    [HasRayCancellation C] [HasNoInfiniteRayChain C] :
    IsRayCrownFree C where
  no_four := by
    intro x a b u v h
    exact (HasNoInfiniteRayChain.isEmpty (C := C)).false
      (RayOrderCrown.ofFour h).toInfinite
  no_six := by
    intro x a b c ab bc ac h
    exact (HasNoInfiniteRayChain.isEmpty (C := C)).false
      (RayOrderCrown.ofSix h).toInfinite

/-- Make the no-infinite-chain consequence available automatically wherever
the BGRS ray cancellation law is present. -/
instance noInfiniteRayChain_isRayCrownFree
    [HasRayCancellation C] [HasNoInfiniteRayChain C] :
    IsRayCrownFree C :=
  isRayCrownFree_of_noInfinite

/-- The same cancellation and chainlessness hypotheses exclude four- and
six-crowns in every fixed-target factorization order. -/
theorem isRayCocrownFree_of_noInfinite
    [HasRayCancellation C] [HasNoInfiniteRayChain C] :
    IsRayCocrownFree C where
  no_four := by
    intro y a b u v h
    exact (HasNoInfiniteRayChain.isEmpty (C := C)).false
      (RayCoOrderCrown.ofFour h).toInfinite
  no_six := by
    intro y a b c ab bc ac h
    exact (HasNoInfiniteRayChain.isEmpty (C := C)).false
      (RayCoOrderCrown.ofSix h).toInfinite

/-- Make fixed-target cocrown-freeness automatic under the source
cancellation and no-infinite-chain hypotheses. -/
instance noInfiniteRayChain_isRayCocrownFree
    [HasRayCancellation C] [HasNoInfiniteRayChain C] :
    IsRayCocrownFree C :=
  isRayCocrownFree_of_noInfinite

/-- The BGRS cancellation law descends to every zero-Hom-ideal quotient. -/
theorem ZeroHomIdeal.quotientHasRayCancellation
    (I : ZeroHomIdeal C) [HasRayCancellation C] :
    HasRayCancellation (CategoryTheory.Quotient I.rel) where
  cancel_right := by
    intro X Y Z f g h heq hne
    induction f using Quot.inductionOn with
    | _ f =>
        induction g using Quot.inductionOn with
        | _ g =>
            induction h using Quot.inductionOn with
            | _ h =>
                have hcompNe : f ≫ h ≠ 0 := by
                  intro hzero
                  apply hne
                  change Quot.mk _ (f ≫ h) = Quot.mk _ 0
                  rw [hzero]
                have hnotMem : ¬I.mem (f ≫ h) := by
                  intro hmem
                  apply hne
                  change (CategoryTheory.Quotient.functor I.rel).map
                    (f ≫ h) = 0
                  exact (I.functor_map_eq_zero_iff (f ≫ h)).2 hmem
                have hrel : I.rel (f ≫ h) (g ≫ h) := by
                  apply (CategoryTheory.Quotient.functor_map_eq_iff
                    I.rel (f ≫ h) (g ≫ h)).1
                  exact heq
                have heq' : f ≫ h = g ≫ h := by
                  rcases hrel with hrel | hrel
                  · exact hrel
                  · exact False.elim (hnotMem hrel.1)
                have hfg := HasRayCancellation.cancel_right f g h heq' hcompNe
                subst g
                rfl
  cancel_left := by
    intro X Y Z h f g heq hne
    induction h using Quot.inductionOn with
    | _ h =>
        induction f using Quot.inductionOn with
        | _ f =>
            induction g using Quot.inductionOn with
            | _ g =>
                have hcompNe : h ≫ f ≠ 0 := by
                  intro hzero
                  apply hne
                  change Quot.mk _ (h ≫ f) = Quot.mk _ 0
                  rw [hzero]
                have hnotMem : ¬I.mem (h ≫ f) := by
                  intro hmem
                  apply hne
                  change (CategoryTheory.Quotient.functor I.rel).map
                    (h ≫ f) = 0
                  exact (I.functor_map_eq_zero_iff (h ≫ f)).2 hmem
                have hrel : I.rel (h ≫ f) (h ≫ g) := by
                  apply (CategoryTheory.Quotient.functor_map_eq_iff
                    I.rel (h ≫ f) (h ≫ g)).1
                  exact heq
                have heq' : h ≫ f = h ≫ g := by
                  rcases hrel with hrel | hrel
                  · exact hrel
                  · exact False.elim (hnotMem hrel.1)
                have hfg := HasRayCancellation.cancel_left h f g heq' hcompNe
                subst g
                rfl

/-- Every zero-ideal quotient is crown-free once the original ray category has
the cancellation and no-infinite-chain properties. -/
theorem ZeroHomIdeal.quotientIsRayCrownFree
    (I : ZeroHomIdeal C) [HasRayCancellation C]
    [HasNoInfiniteRayChain C] :
    IsRayCrownFree (CategoryTheory.Quotient I.rel) := by
  letI : HasRayCancellation (CategoryTheory.Quotient I.rel) :=
    I.quotientHasRayCancellation
  letI : HasNoInfiniteRayChain (CategoryTheory.Quotient I.rel) :=
    I.quotientHasNoInfiniteRayChain
  exact isRayCrownFree_of_noInfinite

/-- Every zero-ideal quotient is fixed-target cocrown-free under the same
source hypotheses. -/
theorem ZeroHomIdeal.quotientIsRayCocrownFree
    (I : ZeroHomIdeal C) [HasRayCancellation C]
    [HasNoInfiniteRayChain C] :
    IsRayCocrownFree (CategoryTheory.Quotient I.rel) := by
  letI : HasRayCancellation (CategoryTheory.Quotient I.rel) :=
    I.quotientHasRayCancellation
  letI : HasNoInfiniteRayChain (CategoryTheory.Quotient I.rel) :=
    I.quotientHasNoInfiniteRayChain
  exact isRayCocrownFree_of_noInfinite

/-- A principal residue which supports a tackle supports an efficient one,
with all finite-ray, cancellation, chain-bound, and crown-free structure
installed from the original ray category. -/
theorem rayResidueCategory_exists_isEfficientAt
    [Finite C] [IsFiniteRayCategory C] [HasRayCancellation C]
    [HasNoInfiniteRayChain C]
    {A B : C} (mu : A ⟶ B) (hmuIso : ¬IsIso mu)
    (y : RayResidueCategory mu)
    (hy : ∃ t : RayTackle (RayResidueCategory mu), t.start = y) :
    letI : IsFiniteRayCategory (RayResidueCategory mu) :=
      rayResidueCategory_isFiniteRayCategory mu hmuIso
    ∃ t : RayTackle (RayResidueCategory mu), t.IsEfficientAt y := by
  let I := principalZeroHomIdeal mu
  letI : IsFiniteRayCategory (RayResidueCategory mu) :=
    rayResidueCategory_isFiniteRayCategory mu hmuIso
  letI : HasRayCancellation (RayResidueCategory mu) :=
    I.quotientHasRayCancellation
  letI : HasNoInfiniteRayChain (RayResidueCategory mu) :=
    I.quotientHasNoInfiniteRayChain
  exact RayTackle.exists_isEfficientAt_of_bounded y hy

end LargeIndecomposable
