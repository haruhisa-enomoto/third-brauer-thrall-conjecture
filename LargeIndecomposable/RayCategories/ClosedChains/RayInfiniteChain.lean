module

public import LargeIndecomposable.RayCategories.RoiterVanishing.RayResidueMeasure
public import LargeIndecomposable.RayCategories.RoiterVanishing.RayTackleFiniteness

@[expose] public section

/-!
# Infinite ray chains and the finite-state bound

Encode the alternating chains of BGRS 1.9 as walks on the finite type of
nonzero category morphisms.  A repeated state pumps to an infinite periodic
chain.  Consequently, absence of infinite chains supplies the common finite
bound used by efficient-tackle selection.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace NonzeroCategoryMorphism

/-- Regard a nonzero morphism with varying endpoints as a `NonzeroHom`. -/
def toNonzeroHom (f : NonzeroCategoryMorphism C) :
    NonzeroHom f.source f.target :=
  ⟨f.hom, f.ne_zero⟩

@[simp]
theorem coe_toNonzeroHom (f : NonzeroCategoryMorphism C) :
    f.toNonzeroHom.1 = f.hom :=
  rfl

/-- Taking a chosen quotient representative commutes with forgetting to a
`NonzeroHom`. -/
theorem quotOut_toNonzeroHom (I : ZeroHomIdeal C)
    (f : NonzeroCategoryMorphism (CategoryTheory.Quotient I.rel)) :
    (f.quotOut I).toNonzeroHom = I.quotOutNonzeroHom f.toNonzeroHom := by
  rcases f with ⟨X, Y, f, hf⟩
  rfl

end NonzeroCategoryMorphism

/-- One alternating step `rho_i, sigma_i, rho_(i+1)` in a BGRS chain. -/
def RayChainStep (f g : NonzeroCategoryMorphism C) : Prop :=
  ∃ sigma : NonzeroHom g.source f.target,
    RayTargetIncomparable f.toNonzeroHom sigma ∧
      RaySourceIncomparable sigma g.toNonzeroHom

/-- Lift one alternating quotient step to chosen original representatives. -/
theorem RayChainStep.quotOut (I : ZeroHomIdeal C)
    {f g : NonzeroCategoryMorphism (CategoryTheory.Quotient I.rel)}
    (h : RayChainStep f g) :
    RayChainStep (f.quotOut I) (g.quotOut I) := by
  obtain ⟨sigma, hpeak, hvalley⟩ := h
  refine ⟨I.quotOutNonzeroHom sigma, ?_, ?_⟩
  · rw [NonzeroCategoryMorphism.quotOut_toNonzeroHom]
    exact I.rayTargetIncomparable_quotOut f.toNonzeroHom sigma hpeak
  · rw [NonzeroCategoryMorphism.quotOut_toNonzeroHom]
    exact I.raySourceIncomparable_quotOut sigma g.toNonzeroHom hvalley

/-- A finite walk of `m` alternating steps. -/
structure RayFiniteChain (m : ℕ) where
  state : Fin (m + 1) → NonzeroCategoryMorphism C
  step : ∀ i : Fin m, RayChainStep (state i.castSucc) (state i.succ)

/-- Forget a hook chain to its finite-state walk. -/
def RayHookChain.toRayFiniteChain {m : ℕ}
    (t : RayHookChain (C := C) m) : RayFiniteChain (C := C) m where
  state i := ⟨t.x i, t.z i, (t.rho i).1, (t.rho i).2⟩
  step i := ⟨t.sigma i, t.peak_incomparable i, t.valley_incomparable i⟩

/-- Forget the final `sigma` of a cohook chain and retain its finite-state
walk through the `rho` morphisms. -/
def RayCohookChain.toRayFiniteChain {m : ℕ}
    (t : RayCohookChain (C := C) m) : RayFiniteChain (C := C) m where
  state i :=
    ⟨t.x i.castSucc, t.z i, (t.rho i).1, (t.rho i).2⟩
  step i := by
    refine ⟨t.sigma i.castSucc, t.peak_incomparable i.castSucc, ?_⟩
    change RaySourceIncomparable (t.sigma i.castSucc) (t.rho i.succ)
    exact t.valley_incomparable i

/-- An infinite alternating BGRS chain, encoded by its successive `rho`
states and the intervening `sigma` steps. -/
structure RayInfiniteChain where
  state : ℕ → NonzeroCategoryMorphism C
  step : ∀ n : ℕ, RayChainStep (state n) (state (n + 1))

/-- The source hypothesis that there is no infinite alternating chain. -/
class HasNoInfiniteRayChain (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] : Prop where
  isEmpty : IsEmpty (RayInfiniteChain (C := C))

/-- Truncate an infinite alternating chain to its first `m` hook steps. -/
def RayInfiniteChain.toRayHookChain
    (t : RayInfiniteChain (C := C)) (m : ℕ) :
    RayHookChain (C := C) m where
  x i := (t.state i).source
  z i := (t.state i).target
  rho i := (t.state i).toNonzeroHom
  sigma i := Classical.choose (t.step i)
  peak_incomparable i := (Classical.choose_spec (t.step i)).1
  valley_incomparable i := (Classical.choose_spec (t.step i)).2

/-- A uniform finite bound on hook chains excludes an infinite chain. -/
theorem hasNoInfiniteRayChainOfBounded
    [HasBoundedRayChains C] : HasNoInfiniteRayChain C where
  isEmpty := ⟨fun t ↦ by
    let m := HasBoundedRayChains.bound (C := C)
    have hlt : m < m :=
      HasBoundedRayChains.hook_lt ⟨t.toRayHookChain m⟩
    exact (Nat.lt_irrefl m) hlt⟩

/-- Lift an infinite chain in a zero-ideal quotient to chosen original
representatives. -/
def RayInfiniteChain.quotOut (I : ZeroHomIdeal C)
    (t : RayInfiniteChain
      (C := CategoryTheory.Quotient I.rel)) :
    RayInfiniteChain (C := C) where
  state n := (t.state n).quotOut I
  step n := (t.step n).quotOut I

/-- Absence of infinite chains descends to every zero-ideal quotient. -/
theorem ZeroHomIdeal.quotientHasNoInfiniteRayChain
    (I : ZeroHomIdeal C) [HasNoInfiniteRayChain C] :
    HasNoInfiniteRayChain (CategoryTheory.Quotient I.rel) where
  isEmpty :=
    ⟨fun t ↦ (HasNoInfiniteRayChain.isEmpty (C := C)).false (t.quotOut I)⟩

/-- A repeated state in a finite chain pumps to an infinite periodic chain. -/
def RayFiniteChain.toInfiniteOfEq {m : ℕ}
    (t : RayFiniteChain (C := C) m) (i j : Fin (m + 1))
    (hij : i.1 < j.1) (hstate : t.state i = t.state j) :
    RayInfiniteChain (C := C) := by
  let period := j.1 - i.1
  have hperiod : 0 < period := by
    dsimp [period]
    omega
  let index (n : ℕ) : Fin (m + 1) :=
    ⟨i.1 + n % period, by
      have hmod := Nat.mod_lt n hperiod
      dsimp [period] at hmod ⊢
      omega⟩
  refine
    { state := fun n ↦ t.state (index n)
      step := ?_ }
  intro n
  let r := n % period
  have hr : r < period := Nat.mod_lt n hperiod
  by_cases hlast : r + 1 = period
  · have hindex : index n = ⟨j.1 - 1, by omega⟩ := by
      apply Fin.ext
      dsimp [index, r]
      omega
    have hnext : index (n + 1) = i := by
      apply Fin.ext
      dsimp [index, r]
      have hnmod : n % period = period - 1 := by omega
      have hpred : period - 1 + 1 = period := by omega
      by_cases hpone : period = 1
      · rw [hpone]
        omega
      · have hone : 1 < period := by omega
        rw [Nat.add_mod, Nat.mod_eq_of_lt hone, hnmod, hpred,
          Nat.mod_self]
        simp
    have hjpred : j.1 - 1 < m := by omega
    let q : Fin m := ⟨j.1 - 1, hjpred⟩
    have hqcast : q.castSucc = index n := by
      apply Fin.ext
      simp [q, hindex]
    have hqsucc : q.succ = j := by
      apply Fin.ext
      simp [q]
      omega
    rw [hnext, hstate]
    simpa [← hqcast, ← hqsucc] using t.step q
  · have hnextval : (n + 1) % period = r + 1 := by
      rw [Nat.add_mod]
      have hrle : r + 1 < period := by omega
      simp [r, Nat.mod_eq_of_lt hrle]
    have hcur_lt_m : i.1 + r < m := by
      dsimp [period] at hr
      omega
    let q : Fin m := ⟨i.1 + r, hcur_lt_m⟩
    have hqcast : q.castSucc = index n := by
      apply Fin.ext
      rfl
    have hqsucc : q.succ = index (n + 1) := by
      apply Fin.ext
      dsimp [q, index]
      rw [hnextval]
      omega
    simpa [← hqcast, ← hqsucc] using t.step q

/-- Four nonzero morphisms alternating around two objects cannot form a
period-two crown in a category with no infinite ray chains.  This is the
literal `A~(rho₀, sigma₀, rho₁, sigma₁)` obstruction used in Bongartz's
dumb-bell argument; unlike `RayClosedChain`, it intentionally allows period
two. -/
theorem not_rayPeriodTwoCrown [HasNoInfiniteRayChain C]
    {X Y : C}
    (rho₀ : NonzeroHom X X) (sigma₀ : NonzeroHom Y X)
    (rho₁ : NonzeroHom Y Y) (sigma₁ : NonzeroHom X Y)
    (hpeak₀ : RayTargetIncomparable rho₀ sigma₀)
    (hvalley₀ : RaySourceIncomparable sigma₀ rho₁)
    (hpeak₁ : RayTargetIncomparable rho₁ sigma₁)
    (hvalley₁ : RaySourceIncomparable sigma₁ rho₀) : False := by
  let t : RayFiniteChain (C := C) 2 :=
    { state := ![
        (⟨X, X, rho₀.1, rho₀.2⟩ : NonzeroCategoryMorphism C),
        (⟨Y, Y, rho₁.1, rho₁.2⟩ : NonzeroCategoryMorphism C),
        (⟨X, X, rho₀.1, rho₀.2⟩ : NonzeroCategoryMorphism C)]
      step := by
        intro i
        fin_cases i
        · exact ⟨sigma₀, hpeak₀, hvalley₀⟩
        · exact ⟨sigma₁, hpeak₁, hvalley₁⟩ }
  exact (HasNoInfiniteRayChain.isEmpty (C := C)).false
    (t.toInfiniteOfEq (0 : Fin 3) (2 : Fin 3) (by decide) rfl)

/-- If the finite-state walk is at least as long as the number of possible
nonzero-morphism states, then it pumps to an infinite chain. -/
theorem RayFiniteChain.exists_infinite_of_card_le_length
    [Finite C] [IsFiniteRayCategory C]
    {m : ℕ} (t : RayFiniteChain (C := C) m)
    (hcard : Nat.card (NonzeroCategoryMorphism C) ≤ m) :
    Nonempty (RayInfiniteChain (C := C)) := by
  classical
  letI : Fintype (NonzeroCategoryMorphism C) := Fintype.ofFinite _
  have hlt : Fintype.card (NonzeroCategoryMorphism C) <
      Fintype.card (Fin (m + 1)) := by
    simpa [Nat.card_eq_fintype_card] using hcard
  obtain ⟨i, j, hij, hstate⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt t.state hlt
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · exact ⟨t.toInfiniteOfEq i j hij' hstate⟩
  · exact ⟨t.toInfiniteOfEq j i hji' hstate.symm⟩

/-- In a finite ray category, absence of infinite alternating chains gives one
common strict bound for both finite chain shapes. -/
@[reducible]
def hasBoundedRayChainsOfNoInfinite
    [Finite C] [IsFiniteRayCategory C] [HasNoInfiniteRayChain C] :
    HasBoundedRayChains C where
  bound := Nat.card (NonzeroCategoryMorphism C)
  hook_lt := by
    intro m ht
    by_contra hlt
    exact ht.elim fun t ↦
      (t.toRayFiniteChain.exists_infinite_of_card_le_length
        (Nat.le_of_not_gt hlt)).elim fun infinite ↦
          (HasNoInfiniteRayChain.isEmpty (C := C)).false infinite
  cohook_lt := by
    intro m ht
    by_contra hlt
    exact ht.elim fun t ↦
      (t.toRayFiniteChain.exists_infinite_of_card_le_length
      (Nat.le_of_not_gt hlt)).elim fun infinite ↦
          (HasNoInfiniteRayChain.isEmpty (C := C)).false infinite

/-- The exact finite first-shape closed chain of BGRS 1.9: its first and last
`rho` states agree and its length is at least three. -/
structure RayClosedChain where
  length : ℕ
  chain : RayHookChain (C := C) length
  length_ge_three : 3 ≤ length
  first_eq_last :
    chain.toRayFiniteChain.state 0 =
      chain.toRayFiniteChain.state (Fin.last length)

/-- Repeating a closed chain produces an infinite chain. -/
def RayClosedChain.toInfinite (t : RayClosedChain (C := C)) :
    RayInfiniteChain (C := C) :=
  t.chain.toRayFiniteChain.toInfiniteOfEq 0 (Fin.last t.length)
    (by
      change 0 < t.length
      exact lt_of_lt_of_le (by decide : 0 < 3) t.length_ge_three)
    t.first_eq_last

/-- Truncate an infinite chain starting at an arbitrary state. -/
def RayInfiniteChain.toRayHookChainFrom
    (t : RayInfiniteChain (C := C)) (start length : ℕ) :
    RayHookChain (C := C) length where
  x i := (t.state (start + i.1)).source
  z i := (t.state (start + i.1)).target
  rho i := (t.state (start + i.1)).toNonzeroHom
  sigma i := Classical.choose (t.step (start + i.1))
  peak_incomparable i :=
    (Classical.choose_spec (t.step (start + i.1))).1
  valley_incomparable i :=
    (Classical.choose_spec (t.step (start + i.1))).2

/-- Equal states at distance at least three form an exact BGRS closed chain. -/
def RayInfiniteChain.toRayClosedChainOfEq
    (t : RayInfiniteChain (C := C)) (i j : ℕ)
    (hij : i < j) (hgap : 3 ≤ j - i)
    (hstate : t.state i = t.state j) :
    RayClosedChain (C := C) where
  length := j - i
  chain := t.toRayHookChainFrom i (j - i)
  length_ge_three := hgap
  first_eq_last := by
    change t.state (i + (0 : ℕ)) = t.state (i + (j - i))
    simpa [Nat.add_sub_of_le (Nat.le_of_lt hij)] using hstate

/-- On finite ray state, excluding BGRS closed chains excludes infinite
alternating chains. -/
theorem hasNoInfiniteRayChainOfNoClosed
    [Finite C] [IsFiniteRayCategory C]
    (hclosed : IsEmpty (RayClosedChain (C := C))) :
    HasNoInfiniteRayChain C where
  isEmpty := ⟨fun t ↦ by
    obtain ⟨i, j, hij, hstate⟩ :=
      Finite.exists_ne_map_eq_of_infinite
        (fun n : ℕ ↦ t.state (3 * n))
    rcases lt_or_gt_of_ne hij with hij' | hji'
    · exact hclosed.false <|
        t.toRayClosedChainOfEq (3 * i) (3 * j)
          (by omega) (by omega) hstate
    · exact hclosed.false <|
        t.toRayClosedChainOfEq (3 * j) (3 * i)
          (by omega) (by omega) hstate.symm⟩

/-- A category without infinite chains has no closed BGRS chain. -/
theorem HasNoInfiniteRayChain.isEmpty_rayClosedChain
    [HasNoInfiniteRayChain C] : IsEmpty (RayClosedChain (C := C)) :=
  ⟨fun t ↦ (HasNoInfiniteRayChain.isEmpty (C := C)).false t.toInfinite⟩

/-- Make the finite-state consequence available to tackle selection through
typeclass inference. -/
instance noInfiniteRayChain_hasBoundedRayChains
    [Finite C] [IsFiniteRayCategory C] [HasNoInfiniteRayChain C] :
    HasBoundedRayChains C :=
  hasBoundedRayChainsOfNoInfinite

end LargeIndecomposable
