module

public import LargeIndecomposable.RayCategories.ClosedChains.RayCrownFree

@[expose] public section

/-!
# Replacing the last arrow of an efficient tackle

Construct the dependent hook-tackle obtained by replacing its last `rho`
with a compatible irreducible morphism.  Since both old and new last hooks
have depth one, the efficiency word is unchanged.  This turns the order
conclusion for Figures 57--60 into the exact BGRS 8.5 efficient-hook lemma.
The orientation-dual cohook replacement is packaged in the same way.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace NonzeroHom

/-- Transport both endpoints of a nonzero morphism. -/
def cast {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    (f : NonzeroHom X Y) : NonzeroHom X' Y' := by
  subst X'
  subst Y'
  exact f

@[simp]
theorem cast_rfl {X Y : C} (f : NonzeroHom X Y) :
    f.cast rfl rfl = f :=
  rfl

/-- Endpoint transport preserves ray-morphism depth. -/
@[simp]
theorem depth_cast [HasFiniteRayPathDepth C]
    {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    (f : NonzeroHom X Y) :
    (f.cast hx hy).depth = f.depth := by
  subst X'
  subst Y'
  rfl

end NonzeroHom

/-- Endpoint transport preserves irreducibility. -/
theorem isIrreducibleMorphism_cast
    {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    (f : NonzeroHom X Y) (hf : IsIrreducibleRayMorphism f.1) :
    IsIrreducibleRayMorphism (f.cast hx hy).1 := by
  subst X'
  subst Y'
  exact hf

/-- Endpoint transport preserves fixed-target incomparability. -/
theorem RayTargetIncomparable.cast
    {X Y Z X' Y' Z' : C}
    {f : NonzeroHom X Z} {g : NonzeroHom Y Z}
    (h : RayTargetIncomparable f g)
    (hx : X = X') (hy : Y = Y') (hz : Z = Z') :
    RayTargetIncomparable (f.cast hx hz) (g.cast hy hz) := by
  subst X'
  subst Y'
  subst Z'
  exact h

/-- Endpoint transport preserves fixed-source incomparability. -/
theorem RaySourceIncomparable.cast
    {X Y Z X' Y' Z' : C}
    {f : NonzeroHom X Y} {g : NonzeroHom X Z}
    (h : RaySourceIncomparable f g)
    (hx : X = X') (hy : Y = Y') (hz : Z = Z') :
    RaySourceIncomparable (f.cast hx hy) (g.cast hx hz) := by
  subst X'
  subst Y'
  subst Z'
  exact h

namespace RayHookTackle

/-- Replace the last hook by a compatible irreducible morphism, retaining the
entire preceding alternating chain. -/
def replaceLast {m : ℕ} (t : RayHookTackle (C := C) m)
    {Z : C} (f : NonzeroHom (t.x (Fin.last m)) Z)
    (hf : IsIrreducibleRayMorphism f.1)
    (hcompatible : t.LastReplacementCompatible f) :
    RayHookTackle (C := C) m := by
  cases m with
  | zero =>
      refine
        { x := t.x
          z := fun _ ↦ Z
          rho := fun i ↦ by
            have hi : i = Fin.last 0 := by
              apply Fin.ext
              omega
            subst i
            exact f
          sigma := fun i ↦ Fin.elim0 i
          peak_incomparable := fun i ↦ Fin.elim0 i
          valley_incomparable := fun i ↦ Fin.elim0 i
          last_irreducible := hf }
  | succ n =>
      let z' : Fin (n + 2) → C := fun i ↦
        if i = Fin.last (n + 1) then Z else t.z i
      let rho' : ∀ i : Fin (n + 2), NonzeroHom (t.x i) (z' i) :=
        fun i ↦ if hi : i = Fin.last (n + 1) then
          f.cast (congrArg t.x hi.symm) (by subst i; simp [z'])
        else
          (t.rho i).cast rfl (by simp [z', hi])
      let sigma' : ∀ i : Fin (n + 1),
          NonzeroHom (t.x i.succ) (z' i.castSucc) := fun i ↦
        (t.sigma i).cast rfl (by simp [z'])
      refine
        { x := t.x
          z := z'
          rho := rho'
          sigma := sigma'
          peak_incomparable := fun i ↦ by
            have hi : i.castSucc ≠ Fin.last (n + 1) := by
              intro h
              have hval := congrArg Fin.val h
              simp at hval
              exact (Nat.ne_of_lt i.isLt) hval
            have hz : t.z i.castSucc = z' i.castSucc := by
              simp [z', hi]
            simpa [rho', sigma', hi] using
              (t.peak_incomparable i).cast rfl rfl hz
          valley_incomparable := fun i ↦ by
            by_cases hi : i.succ = Fin.last (n + 1)
            · have hilast : i = Fin.last n := by
                apply Fin.ext
                have := congrArg Fin.val hi
                simp at this ⊢
                omega
              subst i
              have hzSigma : t.z (Fin.last n).castSucc =
                  z' (Fin.last n).castSucc := by
                simp [z']
              have hzRho : Z = z' (Fin.last n).succ := by
                simp [z']
              simpa [rho', sigma', LastReplacementCompatible] using
                hcompatible.cast rfl hzSigma hzRho
            · have hzSigma : t.z i.castSucc = z' i.castSucc := by
                simp [z']
              have hzRho : t.z i.succ = z' i.succ := by
                simp [z', hi]
              simpa [rho', sigma', hi] using
                (t.valley_incomparable i).cast rfl hzSigma hzRho
          last_irreducible := by
            have hz : Z = z' (Fin.last (n + 1)) := by simp [z']
            simpa [rho'] using
              isIrreducibleMorphism_cast rfl hz f hf }

@[simp]
theorem replaceLast_x {m : ℕ} (t : RayHookTackle (C := C) m)
    {Z : C} (f : NonzeroHom (t.x (Fin.last m)) Z)
    (hf : IsIrreducibleRayMorphism f.1)
    (hcompatible : t.LastReplacementCompatible f)
    (i : Fin (m + 1)) :
    (t.replaceLast f hf hcompatible).x i = t.x i := by
  cases m <;> simp [replaceLast]

@[simp]
theorem replaceLast_rho_castSucc_depth
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    {m : ℕ}
    (t : RayHookTackle (C := C) m)
    {Z : C} (f : NonzeroHom (t.x (Fin.last m)) Z)
    (hf : IsIrreducibleRayMorphism f.1)
    (hcompatible : t.LastReplacementCompatible f)
    (i : Fin m) :
    ((t.replaceLast f hf hcompatible).rho i.castSucc).depth =
      (t.rho i.castSucc).depth := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ n => simp [replaceLast]

@[simp]
theorem replaceLast_sigma_depth
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    {m : ℕ}
    (t : RayHookTackle (C := C) m)
    {Z : C} (f : NonzeroHom (t.x (Fin.last m)) Z)
    (hf : IsIrreducibleRayMorphism f.1)
    (hcompatible : t.LastReplacementCompatible f)
    (i : Fin m) :
    ((t.replaceLast f hf hcompatible).sigma i).depth =
      (t.sigma i).depth := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ n => simp [replaceLast]

/-- Replacing an irreducible last hook preserves the complete efficiency
word. -/
theorem efficiency_replaceLast
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    {m : ℕ} (t : RayHookTackle (C := C) m)
    {Z : C} (f : NonzeroHom (t.x (Fin.last m)) Z)
    (hf : IsIrreducibleRayMorphism f.1)
    (hcompatible : t.LastReplacementCompatible f) :
    (t.replaceLast f hf hcompatible).efficiency = t.efficiency := by
  apply congrArg₂ alternateLists
  · apply congrArg List.ofFn
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [(t.replaceLast f hf hcompatible).last_depth_eq_one,
        t.last_depth_eq_one]
    · simp
  · apply congrArg List.ofFn
    funext i
    simp

/-- Replacing the last hook of an efficient tackle by a compatible
irreducible hook gives another efficient tackle at the same start. -/
theorem isEfficientAt_replaceLast
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    {m : ℕ} (t : RayHookTackle (C := C) m) {y : C}
    (ht : (RayTackle.hook m t).IsEfficientAt y)
    {Z : C} (f : NonzeroHom (t.x (Fin.last m)) Z)
    (hf : IsIrreducibleRayMorphism f.1)
    (hcompatible : t.LastReplacementCompatible f) :
    (RayTackle.hook m (t.replaceLast f hf hcompatible)).IsEfficientAt y := by
  refine ⟨?_, ?_⟩
  · simpa [RayTackle.start] using ht.1
  · intro s hs hlex
    apply ht.2 s hs
    simpa [RayTackle.efficiency, efficiency_replaceLast] using hlex

end RayHookTackle

namespace RayCohookTackle

/-- Replace the last cohook by a compatible irreducible morphism, retaining
the entire preceding alternating chain. -/
def replaceLast {m : ℕ} (t : RayCohookTackle (C := C) m)
    {X : C} (f : NonzeroHom X (t.z (Fin.last m)))
    (hf : IsIrreducibleRayMorphism f.1)
    (hcompatible : t.LastReplacementCompatible f) :
    RayCohookTackle (C := C) m := by
  let x' : Fin (m + 2) → C :=
    Fin.lastCases X (fun i : Fin (m + 1) ↦ t.x i.castSucc)
  have hxCast (i : Fin (m + 1)) :
      x' i.castSucc = t.x i.castSucc := by
    simp [x']
  have hxPrevious (i : Fin m) :
      x' i.castSucc.succ = t.x i.castSucc.succ := by
    rw [Fin.succ_castSucc]
    simpa [Fin.castSucc_succ] using hxCast i.succ
  have hxLast : x' (Fin.last (m + 1)) = X := by
    simp [x']
  let rho' : ∀ i : Fin (m + 1),
      NonzeroHom (x' i.castSucc) (t.z i) := fun i ↦
    (t.rho i).cast (hxCast i).symm rfl
  let sigma' : ∀ i : Fin (m + 1),
      NonzeroHom (x' i.succ) (t.z i) :=
    Fin.lastCases
      (f.cast hxLast.symm rfl)
      (fun i : Fin m ↦
        (t.sigma i.castSucc).cast (hxPrevious i).symm rfl)
  exact
    { x := x'
      z := t.z
      rho := rho'
      sigma := sigma'
      peak_incomparable := Fin.lastCases
        (by
          simp only [rho', sigma', Fin.lastCases_last]
          exact hcompatible.cast
            (hxCast (Fin.last m)).symm hxLast.symm rfl)
        (fun i : Fin m ↦ by
          simp only [rho', sigma', Fin.lastCases_castSucc]
          exact (t.peak_incomparable i.castSucc).cast
            (hxCast i.castSucc).symm (hxPrevious i).symm rfl)
      valley_incomparable := fun i ↦ by
        simp only [rho', sigma', Fin.lastCases_castSucc]
        have hi : i.castSucc.succ = i.succ.castSucc := by
          exact Fin.ext (by rfl)
        cases hi
        exact (t.valley_incomparable i).cast
          (hxPrevious i).symm rfl rfl
      last_irreducible := by
        simp only [sigma', Fin.lastCases_last]
        exact isIrreducibleMorphism_cast hxLast.symm rfl f hf }

@[simp]
theorem replaceLast_x_zero {m : ℕ}
    (t : RayCohookTackle (C := C) m)
    {X : C} (f : NonzeroHom X (t.z (Fin.last m)))
    (hf : IsIrreducibleRayMorphism f.1)
    (hcompatible : t.LastReplacementCompatible f) :
    (t.replaceLast f hf hcompatible).x 0 = t.x 0 := by
  change Fin.lastCases X (fun i : Fin (m + 1) ↦ t.x i.castSucc)
      ((0 : Fin (m + 1)).castSucc) = t.x 0
  simpa using (Fin.lastCases_castSucc
    (motive := fun _ : Fin (m + 2) ↦ C)
    (last := X) (cast := fun i : Fin (m + 1) ↦ t.x i.castSucc)
    (0 : Fin (m + 1)))

@[simp]
theorem replaceLast_rho_depth
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    {m : ℕ} (t : RayCohookTackle (C := C) m)
    {X : C} (f : NonzeroHom X (t.z (Fin.last m)))
    (hf : IsIrreducibleRayMorphism f.1)
    (hcompatible : t.LastReplacementCompatible f)
    (i : Fin (m + 1)) :
    ((t.replaceLast f hf hcompatible).rho i).depth =
      (t.rho i).depth := by
  simp [replaceLast]

@[simp]
theorem replaceLast_sigma_castSucc_depth
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    {m : ℕ} (t : RayCohookTackle (C := C) m)
    {X : C} (f : NonzeroHom X (t.z (Fin.last m)))
    (hf : IsIrreducibleRayMorphism f.1)
    (hcompatible : t.LastReplacementCompatible f)
    (i : Fin m) :
    ((t.replaceLast f hf hcompatible).sigma i.castSucc).depth =
      (t.sigma i.castSucc).depth := by
  simp [replaceLast]

/-- Replacing an irreducible last cohook preserves the complete efficiency
word. -/
theorem efficiency_replaceLast
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    {m : ℕ} (t : RayCohookTackle (C := C) m)
    {X : C} (f : NonzeroHom X (t.z (Fin.last m)))
    (hf : IsIrreducibleRayMorphism f.1)
    (hcompatible : t.LastReplacementCompatible f) :
    (t.replaceLast f hf hcompatible).efficiency = t.efficiency := by
  apply congrArg₂ alternateLists
  · apply congrArg List.ofFn
    funext i
    simp
  · apply congrArg List.ofFn
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [(t.replaceLast f hf hcompatible).last_depth_eq_one,
        t.last_depth_eq_one]
    · simp

/-- Replacing the last cohook of an efficient tackle by a compatible
irreducible cohook gives another efficient tackle at the same start. -/
theorem isEfficientAt_replaceLast
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    {m : ℕ} (t : RayCohookTackle (C := C) m) {y : C}
    (ht : (RayTackle.cohook m t).IsEfficientAt y)
    {X : C} (f : NonzeroHom X (t.z (Fin.last m)))
    (hf : IsIrreducibleRayMorphism f.1)
    (hcompatible : t.LastReplacementCompatible f) :
    (RayTackle.cohook m (t.replaceLast f hf hcompatible)).IsEfficientAt y := by
  refine ⟨?_, ?_⟩
  · simpa [RayTackle.start] using ht.1
  · intro s hs hlex
    apply ht.2 s hs
    simpa [RayTackle.efficiency, efficiency_replaceLast] using hlex

end RayCohookTackle

/-- BGRS Lemma 8.5: if `gamma` is the hook of an efficient tackle and the
three irreducible arrows form one of Figures 57--60, then `beta` or `delta`
is the hook of an efficient tackle with the same prefix. -/
theorem RayHookTackle.exists_efficient_replacement_of_figure
    [Finite C] [IsFiniteRayCategory C] [IsRayCrownFree C]
    {m : ℕ} (t : RayHookTackle (C := C) m) {y : C}
    (ht : (RayTackle.hook m t).IsEfficientAt y)
    {B D : C}
    (beta : NonzeroHom (t.x (Fin.last m)) B)
    (delta : NonzeroHom (t.x (Fin.last m)) D)
    (hbeta : IsIrreducibleRayMorphism beta.1)
    (hdelta : IsIrreducibleRayMorphism delta.1)
    (hfigure : IsRayThreeArrowFigure beta.toMorphismFrom
      (t.rho (Fin.last m)).toMorphismFrom delta.toMorphismFrom) :
    (∃ h : t.LastReplacementCompatible beta,
      (RayTackle.hook m (t.replaceLast beta hbeta h)).IsEfficientAt y) ∨
    (∃ h : t.LastReplacementCompatible delta,
      (RayTackle.hook m (t.replaceLast delta hdelta h)).IsEfficientAt y) := by
  rcases t.lastReplacementCompatible_or_of_figure
      beta delta hbeta hdelta hfigure with hbetaCompatible | hdeltaCompatible
  · exact Or.inl ⟨hbetaCompatible,
      t.isEfficientAt_replaceLast ht beta hbeta hbetaCompatible⟩
  · exact Or.inr ⟨hdeltaCompatible,
      t.isEfficientAt_replaceLast ht delta hdelta hdeltaCompatible⟩

/-- The cohook-dual BGRS 8.5 replacement, isolated at its exact
fixed-target order-theoretic hypothesis.  Once the three-arrow figure supplies
the dual middle condition, one of the two outer irreducible arrows replaces
the last cohook without changing efficiency. -/
theorem RayCohookTackle.exists_efficient_replacement_of_middleCondition
    [Finite C] [IsFiniteRayCategory C]
    {m : ℕ} (t : RayCohookTackle (C := C) m) {y : C}
    (ht : (RayTackle.cohook m t).IsEfficientAt y)
    {B D : C}
    (beta : NonzeroHom B (t.z (Fin.last m)))
    (delta : NonzeroHom D (t.z (Fin.last m)))
    (hbeta : IsIrreducibleRayMorphism beta.1)
    (hdelta : IsIrreducibleRayMorphism delta.1)
    (hforced : RayCoThreeArrowMiddleCondition beta
      (t.sigma (Fin.last m)) delta) :
    (∃ h : t.LastReplacementCompatible beta,
      (RayTackle.cohook m (t.replaceLast beta hbeta h)).IsEfficientAt y) ∨
    (∃ h : t.LastReplacementCompatible delta,
      (RayTackle.cohook m (t.replaceLast delta hdelta h)).IsEfficientAt y) := by
  rcases t.lastReplacementCompatible_or beta delta hbeta hdelta hforced with
    hbetaCompatible | hdeltaCompatible
  · exact Or.inl ⟨hbetaCompatible,
      t.isEfficientAt_replaceLast ht beta hbeta hbetaCompatible⟩
  · exact Or.inr ⟨hdeltaCompatible,
      t.isEfficientAt_replaceLast ht delta hdelta hdeltaCompatible⟩

/-- The cohook-dual BGRS Lemma 8.5: if the last cohook and two alternative
irreducible arrows form one of the fixed-target Figures 57--60, one outer
arrow is the last cohook of an efficient replacement tackle with the same
prefix. -/
theorem RayCohookTackle.exists_efficient_replacement_of_figure
    [Finite C] [IsFiniteRayCategory C] [IsRayCocrownFree C]
    {m : ℕ} (t : RayCohookTackle (C := C) m) {y : C}
    (ht : (RayTackle.cohook m t).IsEfficientAt y)
    {B D : C}
    (beta : NonzeroHom B (t.z (Fin.last m)))
    (delta : NonzeroHom D (t.z (Fin.last m)))
    (hbeta : IsIrreducibleRayMorphism beta.1)
    (hdelta : IsIrreducibleRayMorphism delta.1)
    (hfigure : IsRayCoThreeArrowFigure beta.toMorphismTo
      (t.sigma (Fin.last m)).toMorphismTo delta.toMorphismTo) :
    (∃ h : t.LastReplacementCompatible beta,
      (RayTackle.cohook m (t.replaceLast beta hbeta h)).IsEfficientAt y) ∨
    (∃ h : t.LastReplacementCompatible delta,
      (RayTackle.cohook m (t.replaceLast delta hdelta h)).IsEfficientAt y) := by
  rcases t.lastReplacementCompatible_or_of_figure
      beta delta hbeta hdelta hfigure with hbetaCompatible | hdeltaCompatible
  · exact Or.inl ⟨hbetaCompatible,
      t.isEfficientAt_replaceLast ht beta hbeta hbetaCompatible⟩
  · exact Or.inr ⟨hdeltaCompatible,
      t.isEfficientAt_replaceLast ht delta hdelta hdeltaCompatible⟩

end LargeIndecomposable
