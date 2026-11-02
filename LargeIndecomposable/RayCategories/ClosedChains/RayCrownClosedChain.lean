module

public import LargeIndecomposable.RayCategories.RoiterVanishing.RayResidueCategory
public import LargeIndecomposable.RayCategories.RoiterVanishing.RayTackle
public import Mathlib.Data.Fintype.Card
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

end NonzeroMorphismTo

/-- The next vertex in a nonempty finite cyclic index type. -/
def finCycleNext {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨(i.1 + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩

namespace RayOrderCrown

variable {x : C} {n : ℕ}

/-- Periodic indexing of a crown by the natural numbers. -/
def cycleIndex (r : ℕ) : Fin (n + 3) :=
  ⟨r % (n + 3), Nat.mod_lt _ (by omega)⟩

theorem cycleIndex_succ (r : ℕ) :
    cycleIndex (n := n) (r + 1) =
      finCycleNext (cycleIndex (n := n) r) := by
  apply Fin.ext
  simp [cycleIndex, finCycleNext, Nat.add_mod]

end RayOrderCrown

namespace RayCoOrderCrown

variable {y : C} {n : ℕ}

/-- Periodic indexing of a fixed-target crown by the natural numbers. -/
def cycleIndex (r : ℕ) : Fin (n + 3) :=
  ⟨r % (n + 3), Nat.mod_lt _ (by omega)⟩

theorem cycleIndex_succ (r : ℕ) :
    cycleIndex (n := n) (r + 1) =
      finCycleNext (cycleIndex (n := n) r) := by
  apply Fin.ext
  simp [cycleIndex, finCycleNext, Nat.add_mod]

end RayCoOrderCrown

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

end LargeIndecomposable
