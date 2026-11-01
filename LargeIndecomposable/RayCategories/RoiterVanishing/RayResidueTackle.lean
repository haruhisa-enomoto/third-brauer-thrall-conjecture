module

public import LargeIndecomposable.RayCategories.RoiterVanishing.RayResidueCategory
public import LargeIndecomposable.RayCategories.RoiterVanishing.RayTackle

@[expose] public section

/-!
# Tackle data in ray residue categories

Transport the nonzero morphisms and alternating nonfactorization conditions
of BGRS tackles through a proper zero-ideal quotient.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace ZeroHomIdeal

variable (I : ZeroHomIdeal C)

/-- Map a morphism known to survive the zero-ideal quotient. -/
def mapNonzeroHom {X Y : C} (f : NonzeroHom X Y)
    (hf : ¬I.mem f.1) :
    NonzeroHom
      ((CategoryTheory.Quotient.functor I.rel).obj X)
      ((CategoryTheory.Quotient.functor I.rel).obj Y) :=
  ⟨(CategoryTheory.Quotient.functor I.rel).map f.1,
    (I.functor_map_ne_zero_iff f.1).2 hf⟩

@[simp]
theorem coe_mapNonzeroHom {X Y : C} (f : NonzeroHom X Y)
    (hf : ¬I.mem f.1) :
    (I.mapNonzeroHom f hf).1 =
      (CategoryTheory.Quotient.functor I.rel).map f.1 :=
  rfl

/-- Fixed-source incomparability is preserved and reflected for two
surviving morphisms. -/
theorem raySourceIncomparable_mapNonzeroHom_iff
    {X Y Z : C} (f : NonzeroHom X Y) (g : NonzeroHom X Z)
    (hf : ¬I.mem f.1) (hg : ¬I.mem g.1) :
    RaySourceIncomparable (I.mapNonzeroHom f hf)
        (I.mapNonzeroHom g hg) ↔
      RaySourceIncomparable f g := by
  change
    ((¬∃ h, (CategoryTheory.Quotient.functor I.rel).map f.1 ≫ h =
        (CategoryTheory.Quotient.functor I.rel).map g.1) ∧
      (¬∃ h, (CategoryTheory.Quotient.functor I.rel).map g.1 ≫ h =
        (CategoryTheory.Quotient.functor I.rel).map f.1)) ↔
      ((¬∃ h, f.1 ≫ h = g.1) ∧ (¬∃ h, g.1 ≫ h = f.1))
  rw [I.exists_postfactor_map_iff f.1 g.1 hg,
    I.exists_postfactor_map_iff g.1 f.1 hf]

/-- Fixed-target incomparability is preserved and reflected for two
surviving morphisms. -/
theorem rayTargetIncomparable_mapNonzeroHom_iff
    {X Y Z : C} (f : NonzeroHom X Z) (g : NonzeroHom Y Z)
    (hf : ¬I.mem f.1) (hg : ¬I.mem g.1) :
    RayTargetIncomparable (I.mapNonzeroHom f hf)
        (I.mapNonzeroHom g hg) ↔
      RayTargetIncomparable f g := by
  change
    ((¬∃ h, h ≫ (CategoryTheory.Quotient.functor I.rel).map g.1 =
        (CategoryTheory.Quotient.functor I.rel).map f.1) ∧
      (¬∃ h, h ≫ (CategoryTheory.Quotient.functor I.rel).map f.1 =
        (CategoryTheory.Quotient.functor I.rel).map g.1)) ↔
      ((¬∃ h, h ≫ g.1 = f.1) ∧ (¬∃ h, h ≫ f.1 = g.1))
  rw [I.exists_prefactor_map_iff f.1 g.1 hf,
    I.exists_prefactor_map_iff g.1 f.1 hg]

/-- Choose an original representative of a nonzero quotient morphism. -/
def quotOutNonzeroHom
    {X Y : CategoryTheory.Quotient I.rel} (f : NonzeroHom X Y) :
    NonzeroHom X.as Y.as :=
  ⟨Quot.out f.1, by
    intro hzero
    apply f.2
    have hout : Quot.mk _ (Quot.out f.1) = f.1 := by simp
    rw [← hout, hzero]
    rfl⟩

/-- The chosen representative of a nonzero quotient morphism is not in the
collapsed ideal. -/
theorem quotOutNonzeroHom_not_mem
    {X Y : CategoryTheory.Quotient I.rel} (f : NonzeroHom X Y) :
    ¬I.mem (I.quotOutNonzeroHom f).1 := by
  intro hmem
  apply f.2
  have hout : Quot.mk _ (Quot.out f.1) = f.1 := by simp
  rw [← hout]
  exact CategoryTheory.Quotient.sound I.rel
    (Or.inr ⟨hmem, I.zero_mem X.as Y.as⟩)

/-- Irreducibility of a quotient morphism lifts to its chosen original
representative. -/
theorem quotOut_isIrreducible (hI : I.IsProper)
    {X Y : CategoryTheory.Quotient I.rel} (f : X ⟶ Y)
    (hf : IsIrreducibleRayMorphism f) :
    IsIrreducibleRayMorphism (Quot.out f) := by
  rcases X with ⟨X⟩
  rcases Y with ⟨Y⟩
  have hmap : IsIrreducibleRayMorphism
      ((CategoryTheory.Quotient.functor I.rel).map (Quot.out f)) := by
    simpa [CategoryTheory.Quotient.functor] using hf
  exact ((I.functor_map_isIrreducible_iff hI (Quot.out f)).1 hmap).1

/-- Fixed-source incomparability lifts from quotient morphisms to their
chosen original representatives. -/
theorem raySourceIncomparable_quotOut
    {X Y Z : CategoryTheory.Quotient I.rel}
    (f : NonzeroHom X Y) (g : NonzeroHom X Z)
    (hfg : RaySourceIncomparable f g) :
    RaySourceIncomparable (I.quotOutNonzeroHom f)
      (I.quotOutNonzeroHom g) := by
  rcases X with ⟨X⟩
  rcases Y with ⟨Y⟩
  rcases Z with ⟨Z⟩
  let f' := I.quotOutNonzeroHom f
  let g' := I.quotOutNonzeroHom g
  have hf' : ¬I.mem f'.1 := I.quotOutNonzeroHom_not_mem f
  have hg' : ¬I.mem g'.1 := I.quotOutNonzeroHom_not_mem g
  apply (I.raySourceIncomparable_mapNonzeroHom_iff
    f' g' hf' hg').1
  simpa [mapNonzeroHom, f', g', quotOutNonzeroHom,
    CategoryTheory.Quotient.functor] using hfg

/-- Fixed-target incomparability lifts from quotient morphisms to their
chosen original representatives. -/
theorem rayTargetIncomparable_quotOut
    {X Y Z : CategoryTheory.Quotient I.rel}
    (f : NonzeroHom X Z) (g : NonzeroHom Y Z)
    (hfg : RayTargetIncomparable f g) :
    RayTargetIncomparable (I.quotOutNonzeroHom f)
      (I.quotOutNonzeroHom g) := by
  rcases X with ⟨X⟩
  rcases Y with ⟨Y⟩
  rcases Z with ⟨Z⟩
  let f' := I.quotOutNonzeroHom f
  let g' := I.quotOutNonzeroHom g
  have hf' : ¬I.mem f'.1 := I.quotOutNonzeroHom_not_mem f
  have hg' : ¬I.mem g'.1 := I.quotOutNonzeroHom_not_mem g
  apply (I.rayTargetIncomparable_mapNonzeroHom_iff
    f' g' hf' hg').1
  simpa [mapNonzeroHom, f', g', quotOutNonzeroHom,
    CategoryTheory.Quotient.functor] using hfg

end ZeroHomIdeal

namespace RayHookChain

/-- Map a hook chain whose every component survives the zero-ideal
quotient. -/
def mapQuotient {m : ℕ} (t : RayHookChain (C := C) m)
    (I : ZeroHomIdeal C)
    (hrho : ∀ i, ¬I.mem (t.rho i).1)
    (hsigma : ∀ i, ¬I.mem (t.sigma i).1) :
    RayHookChain (C := CategoryTheory.Quotient I.rel) m where
  x i := (CategoryTheory.Quotient.functor I.rel).obj (t.x i)
  z i := (CategoryTheory.Quotient.functor I.rel).obj (t.z i)
  rho i := I.mapNonzeroHom (t.rho i) (hrho i)
  sigma i := I.mapNonzeroHom (t.sigma i) (hsigma i)
  peak_incomparable i :=
    (I.rayTargetIncomparable_mapNonzeroHom_iff
      (t.rho i.castSucc) (t.sigma i)
      (hrho i.castSucc) (hsigma i)).2 (t.peak_incomparable i)
  valley_incomparable i :=
    (I.raySourceIncomparable_mapNonzeroHom_iff
      (t.sigma i) (t.rho i.succ)
      (hsigma i) (hrho i.succ)).2 (t.valley_incomparable i)

end RayHookChain

namespace RayCohookChain

/-- Map a cohook chain whose every component survives the zero-ideal
quotient. -/
def mapQuotient {m : ℕ} (t : RayCohookChain (C := C) m)
    (I : ZeroHomIdeal C)
    (hrho : ∀ i, ¬I.mem (t.rho i).1)
    (hsigma : ∀ i, ¬I.mem (t.sigma i).1) :
    RayCohookChain (C := CategoryTheory.Quotient I.rel) m where
  x i := (CategoryTheory.Quotient.functor I.rel).obj (t.x i)
  z i := (CategoryTheory.Quotient.functor I.rel).obj (t.z i)
  rho i := I.mapNonzeroHom (t.rho i) (hrho i)
  sigma i := I.mapNonzeroHom (t.sigma i) (hsigma i)
  peak_incomparable i :=
    (I.rayTargetIncomparable_mapNonzeroHom_iff
      (t.rho i) (t.sigma i) (hrho i) (hsigma i)).2
      (t.peak_incomparable i)
  valley_incomparable i :=
    (I.raySourceIncomparable_mapNonzeroHom_iff
      (t.sigma i.castSucc) (t.rho i.succ)
      (hsigma i.castSucc) (hrho i.succ)).2 (t.valley_incomparable i)

end RayCohookChain

namespace RayHookChain

/-- Lift a hook chain in the quotient to chosen original representatives. -/
def quotOut {m : ℕ} {I : ZeroHomIdeal C}
    (t : RayHookChain (C := CategoryTheory.Quotient I.rel) m) :
    RayHookChain (C := C) m where
  x i := (t.x i).as
  z i := (t.z i).as
  rho i := I.quotOutNonzeroHom (t.rho i)
  sigma i := I.quotOutNonzeroHom (t.sigma i)
  peak_incomparable i :=
    I.rayTargetIncomparable_quotOut
      (t.rho i.castSucc) (t.sigma i) (t.peak_incomparable i)
  valley_incomparable i :=
    I.raySourceIncomparable_quotOut
      (t.sigma i) (t.rho i.succ) (t.valley_incomparable i)

end RayHookChain

namespace RayCohookChain

/-- Lift a cohook chain in the quotient to chosen original representatives. -/
def quotOut {m : ℕ} {I : ZeroHomIdeal C}
    (t : RayCohookChain (C := CategoryTheory.Quotient I.rel) m) :
    RayCohookChain (C := C) m where
  x i := (t.x i).as
  z i := (t.z i).as
  rho i := I.quotOutNonzeroHom (t.rho i)
  sigma i := I.quotOutNonzeroHom (t.sigma i)
  peak_incomparable i :=
    I.rayTargetIncomparable_quotOut
      (t.rho i) (t.sigma i) (t.peak_incomparable i)
  valley_incomparable i :=
    I.raySourceIncomparable_quotOut
      (t.sigma i.castSucc) (t.rho i.succ) (t.valley_incomparable i)

end RayCohookChain

namespace RayHookTackle

/-- Map a hook tackle whose every component survives a proper zero-ideal
quotient. -/
def mapQuotient {m : ℕ} (t : RayHookTackle (C := C) m)
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    (hrho : ∀ i, ¬I.mem (t.rho i).1)
    (hsigma : ∀ i, ¬I.mem (t.sigma i).1) :
    RayHookTackle (C := CategoryTheory.Quotient I.rel) m where
  toRayHookChain := t.toRayHookChain.mapQuotient I hrho hsigma
  last_irreducible :=
    (I.functor_map_isIrreducible_iff hI (t.rho (Fin.last m)).1).2
      ⟨t.last_irreducible, hrho (Fin.last m)⟩

end RayHookTackle

namespace RayCohookTackle

/-- Map a cohook tackle whose every component survives a proper zero-ideal
quotient. -/
def mapQuotient {m : ℕ} (t : RayCohookTackle (C := C) m)
    (I : ZeroHomIdeal C) (hI : I.IsProper)
    (hrho : ∀ i, ¬I.mem (t.rho i).1)
    (hsigma : ∀ i, ¬I.mem (t.sigma i).1) :
    RayCohookTackle (C := CategoryTheory.Quotient I.rel) m where
  toRayCohookChain := t.toRayCohookChain.mapQuotient I hrho hsigma
  last_irreducible :=
    (I.functor_map_isIrreducible_iff hI (t.sigma (Fin.last m)).1).2
      ⟨t.last_irreducible, hsigma (Fin.last m)⟩

end RayCohookTackle

namespace RayHookTackle

/-- Lift a quotient hook tackle to chosen original representatives. -/
def quotOut {m : ℕ} {I : ZeroHomIdeal C} (hI : I.IsProper)
    (t : RayHookTackle (C := CategoryTheory.Quotient I.rel) m) :
    RayHookTackle (C := C) m where
  toRayHookChain := t.toRayHookChain.quotOut
  last_irreducible :=
    I.quotOut_isIrreducible hI (t.rho (Fin.last m)).1
      t.last_irreducible

end RayHookTackle

namespace RayCohookTackle

/-- Lift a quotient cohook tackle to chosen original representatives. -/
def quotOut {m : ℕ} {I : ZeroHomIdeal C} (hI : I.IsProper)
    (t : RayCohookTackle (C := CategoryTheory.Quotient I.rel) m) :
    RayCohookTackle (C := C) m where
  toRayCohookChain := t.toRayCohookChain.quotOut
  last_irreducible :=
    I.quotOut_isIrreducible hI (t.sigma (Fin.last m)).1
      t.last_irreducible

end RayCohookTackle

namespace RayTackle

/-- Every nonzero component of a tackle lies outside the zero Hom ideal. -/
def ComponentsSurvive (I : ZeroHomIdeal C) : RayTackle C → Prop
  | .hook _ t =>
      (∀ i, ¬I.mem (t.rho i).1) ∧ (∀ i, ¬I.mem (t.sigma i).1)
  | .cohook _ t =>
      (∀ i, ¬I.mem (t.rho i).1) ∧ (∀ i, ¬I.mem (t.sigma i).1)

/-- Map a tackle all of whose components survive a proper zero-ideal
quotient. -/
def mapQuotient (I : ZeroHomIdeal C) (hI : I.IsProper)
    (t : RayTackle C) (ht : t.ComponentsSurvive I) :
    RayTackle (CategoryTheory.Quotient I.rel) :=
  match t with
  | .hook m s => .hook m (s.mapQuotient I hI ht.1 ht.2)
  | .cohook m s => .cohook m (s.mapQuotient I hI ht.1 ht.2)

/-- Lift a quotient tackle to chosen original representatives. -/
def quotOut {I : ZeroHomIdeal C} (hI : I.IsProper) :
    RayTackle (CategoryTheory.Quotient I.rel) → RayTackle C
  | .hook m t => .hook m (t.quotOut hI)
  | .cohook m t => .cohook m (t.quotOut hI)

/-- Every component of a lifted quotient tackle survives the original
zero-ideal quotient. -/
theorem componentsSurvive_quotOut {I : ZeroHomIdeal C} (hI : I.IsProper)
    (t : RayTackle (CategoryTheory.Quotient I.rel)) :
    (t.quotOut hI).ComponentsSurvive I := by
  cases t with
  | hook m t =>
      constructor
      · intro i
        exact I.quotOutNonzeroHom_not_mem (t.rho i)
      · intro i
        exact I.quotOutNonzeroHom_not_mem (t.sigma i)
  | cohook m t =>
      constructor
      · intro i
        exact I.quotOutNonzeroHom_not_mem (t.rho i)
      · intro i
        exact I.quotOutNonzeroHom_not_mem (t.sigma i)

end RayTackle

end LargeIndecomposable
