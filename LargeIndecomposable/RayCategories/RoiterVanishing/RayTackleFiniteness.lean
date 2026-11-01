module

public import LargeIndecomposable.RayCategories.RoiterVanishing.RayResidueTackle

@[expose] public section

/-!
# Finiteness of bounded ray tackles

Package the bounded-chain consequence of the BGRS no-infinite-chain
hypothesis and derive finiteness of the full dependent tackle type.  The bound
is also transported through zero-ideal quotients.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Data fields of a fixed-length hook chain, with the incomparability proofs
erased. -/
abbrev RayHookChainCode (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] (m : ℕ) :=
  Σ x : Fin (m + 1) → C, Σ z : Fin (m + 1) → C,
    (∀ i : Fin (m + 1), NonzeroHom (x i) (z i)) ×
      (∀ i : Fin m, NonzeroHom (x i.succ) (z i.castSucc))

/-- Forget the proposition-valued fields of a hook chain. -/
def RayHookChain.code {m : ℕ} (t : RayHookChain (C := C) m) :
    RayHookChainCode C m :=
  ⟨t.x, t.z, t.rho, t.sigma⟩

theorem RayHookChain.code_injective {m : ℕ} :
    Function.Injective (RayHookChain.code (C := C) (m := m)) := by
  intro t s h
  rcases t with ⟨x, z, rho, sigma, hp, hv⟩
  rcases s with ⟨x', z', rho', sigma', hp', hv'⟩
  dsimp [RayHookChain.code] at h
  cases h
  rfl

/-- Data fields of a fixed-length cohook chain, with proposition-valued
fields erased. -/
abbrev RayCohookChainCode (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] (m : ℕ) :=
  Σ x : Fin (m + 2) → C, Σ z : Fin (m + 1) → C,
    (∀ i : Fin (m + 1), NonzeroHom (x i.castSucc) (z i)) ×
      (∀ i : Fin (m + 1), NonzeroHom (x i.succ) (z i))

/-- Forget the proposition-valued fields of a cohook chain. -/
def RayCohookChain.code {m : ℕ} (t : RayCohookChain (C := C) m) :
    RayCohookChainCode C m :=
  ⟨t.x, t.z, t.rho, t.sigma⟩

theorem RayCohookChain.code_injective {m : ℕ} :
    Function.Injective (RayCohookChain.code (C := C) (m := m)) := by
  intro t s h
  rcases t with ⟨x, z, rho, sigma, hp, hv⟩
  rcases s with ⟨x', z', rho', sigma', hp', hv'⟩
  dsimp [RayCohookChain.code] at h
  cases h
  rfl

/-- Fixed-length hook chains form a finite type. -/
instance [Finite C] [IsFiniteRayCategory C] (m : ℕ) :
    Finite (RayHookChain (C := C) m) := by
  classical
  letI (X Y : C) : Finite (X ⟶ Y) :=
    IsFiniteRayCategory.hom_finite X Y
  letI : Fintype C := Fintype.ofFinite C
  letI (X Y : C) : Fintype (X ⟶ Y) := Fintype.ofFinite (X ⟶ Y)
  letI : Fintype (RayHookChainCode C m) := inferInstance
  apply Finite.of_injective (RayHookChain.code (C := C) (m := m))
  exact RayHookChain.code_injective

/-- Fixed-length cohook chains form a finite type. -/
instance [Finite C] [IsFiniteRayCategory C] (m : ℕ) :
    Finite (RayCohookChain (C := C) m) := by
  classical
  letI (X Y : C) : Finite (X ⟶ Y) :=
    IsFiniteRayCategory.hom_finite X Y
  letI : Fintype C := Fintype.ofFinite C
  letI (X Y : C) : Fintype (X ⟶ Y) := Fintype.ofFinite (X ⟶ Y)
  letI : Fintype (RayCohookChainCode C m) := inferInstance
  apply Finite.of_injective (RayCohookChain.code (C := C) (m := m))
  exact RayCohookChain.code_injective

/-- Fixed-length hook tackles form a finite type. -/
instance [Finite C] [IsFiniteRayCategory C] (m : ℕ) :
    Finite (RayHookTackle (C := C) m) := by
  apply Finite.of_injective RayHookTackle.toRayHookChain
  intro t s h
  rcases t with ⟨t, ht⟩
  rcases s with ⟨s, hs⟩
  dsimp at h
  cases h
  rfl

/-- Fixed-length cohook tackles form a finite type. -/
instance [Finite C] [IsFiniteRayCategory C] (m : ℕ) :
    Finite (RayCohookTackle (C := C) m) := by
  apply Finite.of_injective RayCohookTackle.toRayCohookChain
  intro t s h
  rcases t with ⟨t, ht⟩
  rcases s with ⟨s, hs⟩
  dsimp at h
  cases h
  rfl

/-- Finite bounded form of the no-infinite-chain consequence used in BGRS:
the lengths of both alternating chain shapes admit one common bound. -/
class HasBoundedRayChains (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] : Type where
  bound : ℕ
  hook_lt : ∀ {m : ℕ}, Nonempty (RayHookChain (C := C) m) → m < bound
  cohook_lt : ∀ {m : ℕ}, Nonempty (RayCohookChain (C := C) m) → m < bound

/-- Finite code containing all tackles of length below `bound`. -/
abbrev BoundedRayTackleCode (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] (bound : ℕ) :=
  (Σ i : Fin bound, RayHookTackle (C := C) i.1) ⊕
    (Σ i : Fin bound, RayCohookTackle (C := C) i.1)

/-- Bounded alternating chains imply that the complete tackle type is finite. -/
instance [Finite C] [IsFiniteRayCategory C] [HasBoundedRayChains C] :
    Finite (RayTackle C) := by
  classical
  let bound := HasBoundedRayChains.bound (C := C)
  letI (i : Fin bound) : Fintype (RayHookTackle (C := C) i.1) :=
    Fintype.ofFinite _
  letI (i : Fin bound) : Fintype (RayCohookTackle (C := C) i.1) :=
    Fintype.ofFinite _
  letI : Fintype (BoundedRayTackleCode C bound) := inferInstance
  let decode : BoundedRayTackleCode C bound → RayTackle C
    | .inl ⟨i, t⟩ => .hook i.1 t
    | .inr ⟨i, t⟩ => .cohook i.1 t
  apply Finite.of_surjective decode
  intro t
  cases t with
  | hook m t =>
      let i : Fin bound :=
        ⟨m, HasBoundedRayChains.hook_lt ⟨t.toRayHookChain⟩⟩
      exact ⟨.inl ⟨i, t⟩, rfl⟩
  | cohook m t =>
      let i : Fin bound :=
        ⟨m, HasBoundedRayChains.cohook_lt ⟨t.toRayCohookChain⟩⟩
      exact ⟨.inr ⟨i, t⟩, rfl⟩

/-- Under the bounded-chain consequence, every object which supports a tackle
supports an efficient tackle. -/
theorem RayTackle.exists_isEfficientAt_of_bounded
    [Finite C] [IsFiniteRayCategory C] [HasBoundedRayChains C]
    (y : C) (hy : ∃ t : RayTackle C, t.start = y) :
    ∃ t : RayTackle C, t.IsEfficientAt y :=
  RayTackle.exists_isEfficientAt_of_exists_start y hy

/-- A zero-ideal quotient inherits the same common chain-length
bound. -/
@[reducible]
def ZeroHomIdeal.quotientHasBoundedRayChains
    (I : ZeroHomIdeal C) [HasBoundedRayChains C] :
    HasBoundedRayChains (CategoryTheory.Quotient I.rel) where
  bound := HasBoundedRayChains.bound (C := C)
  hook_lt := by
    intro m ht
    obtain ⟨t⟩ := ht
    exact HasBoundedRayChains.hook_lt ⟨t.quotOut⟩
  cohook_lt := by
    intro m ht
    obtain ⟨t⟩ := ht
    exact HasBoundedRayChains.cohook_lt ⟨t.quotOut⟩

end LargeIndecomposable
