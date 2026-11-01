module

public import LargeIndecomposable.RayCategories.RoiterVanishing.RayTackleReplacement

@[expose] public section

/-!
# Extending a hook tackle to a cohook tackle

Package the dependent-index construction used in BGRS Lemma 8.4.  A
compatible replacement for the final hook, together with an incomparable
irreducible morphism into the same new peak, extends the old hook tackle by
one final cohook.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Precomposition by an isomorphism preserves irreducibility. -/
theorem IsIrreducibleRayMorphism.isIso_comp
    {W X Y : C} (e : W ⟶ X) [IsIso e] {f : X ⟶ Y}
    (hf : IsIrreducibleRayMorphism f) :
    IsIrreducibleRayMorphism (e ≫ f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    apply hf.1
    have hcomp := congrArg (fun q ↦ inv e ≫ q) hzero
    simpa [Category.assoc] using hcomp
  · intro hcomp
    letI : IsIso (e ≫ f) := hcomp
    exact hf.2.1 (IsIso.of_isIso_comp_left e f)
  · intro Z g h hgh
    have hfactor : (inv e ≫ g) ≫ h = f := by
      have hcomp := congrArg (fun q ↦ inv e ≫ q) hgh
      simpa [Category.assoc] using hcomp
    rcases hf.2.2 Z (inv e ≫ g) h hfactor with hig | hih
    · left
      letI : IsIso (inv e ≫ g) := hig
      exact IsIso.of_isIso_comp_left (inv e) g
    · exact Or.inr hih

/-- An invertible nonzero ray morphism has depth zero. -/
theorem NonzeroHom.depth_eq_zero_of_isIso
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    {X Y : C} (f : NonzeroHom X Y) [IsIso f.1] :
    f.depth = 0 := by
  obtain ⟨p, hp⟩ :=
    exists_rayPathPresentation_length_eq_depth f.toMorphismFrom
  haveI : IsIso (rayPathMap p.path) := by
    rw [p.map_eq]
    infer_instance
  have hlength : p.path.length = 0 := by
    by_contra hne
    exact rayPathMap_not_isIso_of_length_ne_zero p.path hne inferInstance
  exact hp.symm.trans hlength

/-- A morphism of depth greater than one cannot be a right factor of an
irreducible morphism. -/
theorem not_exists_comp_eq_irreducible_of_one_lt_depth
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    {X Y Z : C} (f : NonzeroHom X Z) (g : NonzeroHom Y Z)
    (hfdepth : 1 < f.depth) (hg : IsIrreducibleRayMorphism g.1) :
    ¬∃ h : Y ⟶ X, h ≫ f.1 = g.1 := by
  rintro ⟨h, hh⟩
  rcases hg.2.2 X h f.1 hh with hIso | fIso
  · letI : IsIso h := hIso
    have hfh : inv h ≫ g.1 = f.1 := by
      have hcomp := congrArg (fun q ↦ inv h ≫ q) hh
      simpa [Category.assoc] using hcomp.symm
    have hfIrreducible : IsIrreducibleRayMorphism f.1 := by
      rw [← hfh]
      exact hg.isIso_comp (inv h)
    have hfdepthOne := rayMorphismDepth_eq_one_of_irreducible f hfIrreducible
    omega
  · letI : IsIso f.1 := fIso
    have hfdepthZero := f.depth_eq_zero_of_isIso
    omega

/-- For a depth-greater-than-one left ray and an irreducible right ray with
the same target, only the factorization of the left ray through the right one
must be excluded to obtain target incomparability. -/
theorem rayTargetIncomparable_of_not_exists_factor_of_one_lt_depth
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    {X Y Z : C} (f : NonzeroHom X Z) (g : NonzeroHom Y Z)
    (hfdepth : 1 < f.depth) (hg : IsIrreducibleRayMorphism g.1)
    (hfactor : ¬∃ h : X ⟶ Y, h ≫ g.1 = f.1) :
    RayTargetIncomparable f g :=
  ⟨hfactor,
    not_exists_comp_eq_irreducible_of_one_lt_depth f g hfdepth hg⟩

/-- A morphism of depth greater than one cannot be a left factor of an
irreducible morphism. -/
theorem not_exists_postcomp_eq_irreducible_of_one_lt_depth
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    {X Y Z : C} (f : NonzeroHom X Y) (g : NonzeroHom X Z)
    (hfdepth : 1 < f.depth) (hg : IsIrreducibleRayMorphism g.1) :
    ¬∃ h : Y ⟶ Z, f.1 ≫ h = g.1 := by
  rintro ⟨h, hh⟩
  rcases hg.2.2 Y f.1 h hh with fIso | hIso
  · letI : IsIso f.1 := fIso
    have hfdepthZero := f.depth_eq_zero_of_isIso
    omega
  · letI : IsIso h := hIso
    have hfh : g.1 ≫ inv h = f.1 := by
      have hcomp := congrArg (fun q ↦ q ≫ inv h) hh
      simpa [Category.assoc] using hcomp.symm
    have hfIrreducible : IsIrreducibleRayMorphism f.1 := by
      rw [← hfh]
      exact hg.comp_isIso (inv h)
    have hfdepthOne := rayMorphismDepth_eq_one_of_irreducible f hfIrreducible
    omega

/-- Dually, for a depth-greater-than-one left ray and an irreducible right
ray with the same source, only factorization of the left ray through the
right one must be excluded to obtain source incomparability. -/
theorem raySourceIncomparable_of_not_exists_factor_of_one_lt_depth
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C]
    {X Y Z : C} (f : NonzeroHom X Y) (g : NonzeroHom X Z)
    (hfdepth : 1 < f.depth) (hg : IsIrreducibleRayMorphism g.1)
    (hfactor : ¬∃ h : Z ⟶ Y, g.1 ≫ h = f.1) :
    RaySourceIncomparable f g :=
  ⟨not_exists_postcomp_eq_irreducible_of_one_lt_depth f g hfdepth hg,
    hfactor⟩

/-- Alternating two equally long lists after appending one final entry to the
left list appends that entry to the alternating word. -/
theorem alternateLists_concat_left_of_length_eq {α : Type*}
    (xs ys : List α) (x : α) (h : xs.length = ys.length) :
    alternateLists (xs.concat x) ys = (alternateLists xs ys).concat x := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => simp [alternateLists]
      | cons b ys => simp at h
  | cons a xs ih =>
      cases ys with
      | nil => simp at h
      | cons b ys =>
          simp only [List.length_cons, Nat.succ.injEq] at h
          simpa [List.concat_eq_append, alternateLists] using
            congrArg (fun zs ↦ a :: b :: zs) (ih ys h)

/-- Alternating two equally long lists after appending one entry to each
appends those two entries, in left-right order, to the alternating word. -/
theorem alternateLists_concat_both_of_length_eq {α : Type*}
    (xs ys : List α) (x y : α) (h : xs.length = ys.length) :
    alternateLists (xs.concat x) (ys.concat y) =
      alternateLists xs ys ++ [x, y] := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => simp [alternateLists]
      | cons b ys => simp at h
  | cons a xs ih =>
      cases ys with
      | nil => simp at h
      | cons b ys =>
          simp only [List.length_cons, Nat.succ.injEq] at h
          simpa [List.concat_eq_append, alternateLists] using
            congrArg (fun zs ↦ a :: b :: zs) (ih ys h)

/-- If the left list has one extra entry, appending to the right list appends
that entry after the existing alternating word. -/
theorem alternateLists_concat_right_of_length_eq_succ {α : Type*}
    (xs ys : List α) (y : α) (h : xs.length = ys.length + 1) :
    alternateLists xs (ys.concat y) = alternateLists xs ys ++ [y] := by
  induction xs generalizing ys with
  | nil => simp at h
  | cons a xs ih =>
      cases ys with
      | nil =>
          cases xs with
          | nil => simp [alternateLists]
          | cons b xs => simp at h
      | cons b ys =>
          simp only [List.length_cons, Nat.succ.injEq] at h
          simpa [List.concat_eq_append, alternateLists] using
            congrArg (fun zs ↦ a :: b :: zs) (ih ys h)

/-- If the left list has one extra entry, appending to both lists adds the
new right entry and then the new left entry to the alternating word. -/
theorem alternateLists_concat_both_of_length_eq_succ {α : Type*}
    (xs ys : List α) (x y : α) (h : xs.length = ys.length + 1) :
    alternateLists (xs.concat x) (ys.concat y) =
      alternateLists xs ys ++ [y, x] := by
  induction xs generalizing ys with
  | nil => simp at h
  | cons a xs ih =>
      cases ys with
      | nil =>
          cases xs with
          | nil => simp [alternateLists]
          | cons b xs => simp at h
      | cons b ys =>
          simp only [List.length_cons, Nat.succ.injEq] at h
          simpa [List.concat_eq_append, alternateLists] using
            congrArg (fun zs ↦ a :: b :: zs) (ih ys h)

namespace RayHookTackle

/-- The alternating depth word before the final hook. -/
def efficiencyPrefix [HasFiniteRayPathDepth C] {m : ℕ}
    (t : RayHookTackle (C := C) m) : List ℕ :=
  alternateLists
    (List.ofFn fun i : Fin m ↦ (t.rho i.castSucc).depth)
    (List.ofFn fun i : Fin m ↦ (t.sigma i).depth)

/-- A hook-tackle efficiency word is its alternating proper prefix followed
by the depth of the last hook. -/
theorem efficiency_eq_efficiencyPrefix_concat_last
    [HasFiniteRayPathDepth C] {m : ℕ}
    (t : RayHookTackle (C := C) m) :
    t.efficiency =
      t.efficiencyPrefix.concat (t.rho (Fin.last m)).depth := by
  unfold RayHookTackle.efficiency efficiencyPrefix
  rw [List.ofFn_succ']
  exact alternateLists_concat_left_of_length_eq _ _ _ (by simp)

/-- The first propagation step in BGRS Figure 55.  If an extension of the
last hook is not compatible with the preceding `sigma`, then it factors
through that `sigma`.  The opposite factorization direction would force the
old last hook to factor through `sigma`, contradicting the old tackle
valley. -/
theorem exists_precedingSigma_factor_of_not_lastReplacementCompatible
    {n : ℕ} (t : RayHookTackle (C := C) (n + 1))
    {Z : C} (f : NonzeroHom (t.x (Fin.last (n + 1))) Z)
    (b : t.z (Fin.last (n + 1)) ⟶ Z)
    (hfactor : (t.rho (Fin.last (n + 1))).1 ≫ b = f.1)
    (hnot : ¬t.LastReplacementCompatible f) :
    ∃ h : t.z (Fin.last n).castSucc ⟶ Z,
      h ≠ 0 ∧ (t.sigma (Fin.last n)).1 ≫ h = f.1 := by
  change ¬RaySourceIncomparable (t.sigma (Fin.last n)) f at hnot
  by_cases hsf : ∃ h, (t.sigma (Fin.last n)).1 ≫ h = f.1
  · obtain ⟨h, hh⟩ := hsf
    refine ⟨h, ?_, hh⟩
    rintro rfl
    apply f.2
    simpa using hh.symm
  · have hfs : ∃ h, f.1 ≫ h = (t.sigma (Fin.last n)).1 := by
      by_contra hfs
      exact hnot ⟨hsf, hfs⟩
    obtain ⟨h, hh⟩ := hfs
    exfalso
    apply (t.valley_incomparable (Fin.last n)).2
    refine ⟨b ≫ h, ?_⟩
    have hfactor' : (t.rho (Fin.last n).succ).1 ≫ b = f.1 := by
      simpa using hfactor
    rw [← Category.assoc, hfactor']
    simpa using hh

/-- Replace the last hook by `f` and append the irreducible cohook `g`, while
retaining the complete preceding alternating chain. -/
def extendLastToCohook {m : ℕ} (t : RayHookTackle (C := C) m)
    {Z X : C} (f : NonzeroHom (t.x (Fin.last m)) Z)
    (g : NonzeroHom X Z)
    (hcompatible : t.LastReplacementCompatible f)
    (hfg : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    RayCohookTackle (C := C) m := by
  let x' : Fin (m + 2) → C := Fin.lastCases X t.x
  let z' : Fin (m + 1) → C :=
    Fin.lastCases Z (fun i : Fin m ↦ t.z i.castSucc)
  have hxCastSucc (i : Fin (m + 1)) : x' i.castSucc = t.x i := by
    simp [x']
  have hxValley (i : Fin m) : x' i.castSucc.succ = t.x i.succ := by
    rw [Fin.succ_castSucc]
    exact hxCastSucc i.succ
  have hxNewLast : x' (Fin.last m).succ = X := by
    simp [x']
  have hzCastSucc (i : Fin m) : z' i.castSucc = t.z i.castSucc := by
    simp [z']
  have hzLast : z' (Fin.last m) = Z := by
    simp [z']
  let rho' : ∀ i : Fin (m + 1),
      NonzeroHom (x' i.castSucc) (z' i) :=
    Fin.lastCases
      (f.cast (hxCastSucc (Fin.last m)).symm hzLast.symm)
      (fun i : Fin m ↦
        (t.rho i.castSucc).cast
          (hxCastSucc i.castSucc).symm (hzCastSucc i).symm)
  let sigma' : ∀ i : Fin (m + 1),
      NonzeroHom (x' i.succ) (z' i) :=
    Fin.lastCases
      (g.cast hxNewLast.symm hzLast.symm)
      (fun i : Fin m ↦
        (t.sigma i).cast (hxValley i).symm (hzCastSucc i).symm)
  exact
    { x := x'
      z := z'
      rho := rho'
      sigma := sigma'
      peak_incomparable := Fin.lastCases
        (by
          simp only [rho', sigma', Fin.lastCases_last]
          exact hfg.cast (hxCastSucc (Fin.last m)).symm
            hxNewLast.symm hzLast.symm)
        (fun i : Fin m ↦ by
          simp only [rho', sigma', Fin.lastCases_castSucc]
          exact (t.peak_incomparable i).cast
            (hxCastSucc i.castSucc).symm (hxValley i).symm
            (hzCastSucc i).symm)
      valley_incomparable := fun i ↦ by
        cases m with
        | zero => exact Fin.elim0 i
        | succ n =>
            refine Fin.lastCases
              (by
                have hsource : t.x (Fin.last (n + 1)) =
                    x' (Fin.last n).castSucc.succ := by
                  simpa using (hxValley (Fin.last n)).symm
                simp only [rho', sigma', Fin.lastCases_castSucc,
                  Fin.succ_last, Fin.lastCases_last]
                exact hcompatible.cast hsource
                  (hzCastSucc (Fin.last n)).symm hzLast.symm)
              (fun j : Fin n ↦ by
                have hzNext : t.z j.castSucc.succ =
                    z' j.castSucc.succ := by
                  simpa [Fin.castSucc_succ] using
                    (hzCastSucc j.succ).symm
                have hsource : t.x j.castSucc.succ =
                    x' j.castSucc.castSucc.succ := by
                  exact (hxValley j.castSucc).symm
                simp only [rho', sigma', Fin.lastCases_castSucc,
                  Fin.succ_castSucc]
                exact (t.valley_incomparable j.castSucc).cast
                  hsource (hzCastSucc j.castSucc).symm hzNext)
              i
      last_irreducible := by
        simp only [sigma', Fin.lastCases_last]
        exact isIrreducibleMorphism_cast hxNewLast.symm hzLast.symm g hg }

@[simp]
theorem extendLastToCohook_x_zero {m : ℕ}
    (t : RayHookTackle (C := C) m)
    {Z X : C} (f : NonzeroHom (t.x (Fin.last m)) Z)
    (g : NonzeroHom X Z)
    (hcompatible : t.LastReplacementCompatible f)
    (hfg : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    (t.extendLastToCohook f g hcompatible hfg hg).x 0 = t.x 0 := by
  change Fin.lastCases X t.x ((0 : Fin (m + 1)).castSucc) = t.x 0
  exact Fin.lastCases_castSucc 0

@[simp]
theorem extendLastToCohook_rho_castSucc_depth
    [HasFiniteRayPathDepth C] {m : ℕ}
    (t : RayHookTackle (C := C) m)
    {Z X : C} (f : NonzeroHom (t.x (Fin.last m)) Z)
    (g : NonzeroHom X Z)
    (hcompatible : t.LastReplacementCompatible f)
    (hfg : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) (i : Fin m) :
    ((t.extendLastToCohook f g hcompatible hfg hg).rho i.castSucc).depth =
      (t.rho i.castSucc).depth := by
  simp [extendLastToCohook]

@[simp]
theorem extendLastToCohook_rho_last_depth
    [HasFiniteRayPathDepth C] {m : ℕ}
    (t : RayHookTackle (C := C) m)
    {Z X : C} (f : NonzeroHom (t.x (Fin.last m)) Z)
    (g : NonzeroHom X Z)
    (hcompatible : t.LastReplacementCompatible f)
    (hfg : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    ((t.extendLastToCohook f g hcompatible hfg hg).rho (Fin.last m)).depth =
      f.depth := by
  simp [extendLastToCohook]

@[simp]
theorem extendLastToCohook_sigma_castSucc_depth
    [HasFiniteRayPathDepth C] {m : ℕ}
    (t : RayHookTackle (C := C) m)
    {Z X : C} (f : NonzeroHom (t.x (Fin.last m)) Z)
    (g : NonzeroHom X Z)
    (hcompatible : t.LastReplacementCompatible f)
    (hfg : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) (i : Fin m) :
    ((t.extendLastToCohook f g hcompatible hfg hg).sigma i.castSucc).depth =
      (t.sigma i).depth := by
  simp [extendLastToCohook]

@[simp]
theorem extendLastToCohook_sigma_last_depth
    [HasFiniteRayPathDepth C] {m : ℕ}
    (t : RayHookTackle (C := C) m)
    {Z X : C} (f : NonzeroHom (t.x (Fin.last m)) Z)
    (g : NonzeroHom X Z)
    (hcompatible : t.LastReplacementCompatible f)
    (hfg : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    ((t.extendLastToCohook f g hcompatible hfg hg).sigma (Fin.last m)).depth =
      g.depth := by
  simp [extendLastToCohook]

/-- The extended cohook tackle has the old efficiency prefix, followed by the
replacement depth and then the new irreducible cohook depth. -/
theorem efficiency_extendLastToCohook
    [HasFiniteRayPathDepth C] {m : ℕ}
    (t : RayHookTackle (C := C) m)
    {Z X : C} (f : NonzeroHom (t.x (Fin.last m)) Z)
    (g : NonzeroHom X Z)
    (hcompatible : t.LastReplacementCompatible f)
    (hfg : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    (t.extendLastToCohook f g hcompatible hfg hg).efficiency =
      t.efficiencyPrefix ++ [f.depth, g.depth] := by
  unfold RayCohookTackle.efficiency efficiencyPrefix
  rw [List.ofFn_succ', List.ofFn_succ']
  rw [alternateLists_concat_both_of_length_eq _ _ _ _ (by simp)]
  congr 1 <;> simp

/-- If the replacement final hook has depth greater than one, appending the
new irreducible cohook produces a strictly larger tackle-efficiency word. -/
theorem efficiency_lex_extendLastToCohook
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C] {m : ℕ}
    (t : RayHookTackle (C := C) m)
    {Z X : C} (f : NonzeroHom (t.x (Fin.last m)) Z)
    (g : NonzeroHom X Z)
    (hcompatible : t.LastReplacementCompatible f)
    (hfg : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : 1 < f.depth) :
    List.Lex (fun a b : ℕ ↦ a < b)
      (RayTackle.hook m t).efficiency
      (RayTackle.cohook m
        (t.extendLastToCohook f g hcompatible hfg hg)).efficiency := by
  simp only [RayTackle.efficiency]
  rw [t.efficiency_eq_efficiencyPrefix_concat_last,
    t.efficiency_extendLastToCohook f g hcompatible hfg hg,
    t.last_depth_eq_one]
  have htail : List.Lex (fun a b : ℕ ↦ a < b)
      [1] [f.depth, g.depth] :=
    List.Lex.rel hfdepth
  simpa [List.concat_eq_append] using
    List.Lex.append_left (fun a b : ℕ ↦ a < b)
      htail t.efficiencyPrefix

/-- If the replacement is still the old depth-one hook, appending a cohook
strictly increases efficiency because the old word is a proper prefix of the
new word. -/
theorem efficiency_lex_extendLastToCohook_of_depth_eq_one
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C] {m : ℕ}
    (t : RayHookTackle (C := C) m)
    {Z X : C} (f : NonzeroHom (t.x (Fin.last m)) Z)
    (g : NonzeroHom X Z)
    (hcompatible : t.LastReplacementCompatible f)
    (hfg : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : f.depth = 1) :
    List.Lex (fun a b : ℕ ↦ a < b)
      (RayTackle.hook m t).efficiency
      (RayTackle.cohook m
        (t.extendLastToCohook f g hcompatible hfg hg)).efficiency := by
  simp only [RayTackle.efficiency]
  rw [t.efficiency_eq_efficiencyPrefix_concat_last,
    t.efficiency_extendLastToCohook f g hcompatible hfg hg,
    t.last_depth_eq_one, hfdepth]
  have htail : List.Lex (fun a b : ℕ ↦ a < b)
      [1] [1, g.depth] :=
    List.Lex.cons List.Lex.nil
  simpa [List.concat_eq_append] using
    List.Lex.append_left (fun a b : ℕ ↦ a < b)
      htail t.efficiencyPrefix

end RayHookTackle

namespace RayCohookTackle

/-- The dual first propagation step in Figure 55.  If a left extension of the
last cohook is not compatible with the old last `rho`, then it factors through
that `rho`; the opposite direction contradicts the old final peak. -/
theorem exists_factorThroughLastRho_of_not_lastReplacementCompatible
    {m : ℕ} (t : RayCohookTackle (C := C) m)
    {X : C} (f : NonzeroHom X (t.z (Fin.last m)))
    (b : X ⟶ t.x (Fin.last m).succ)
    (hfactor : b ≫ (t.sigma (Fin.last m)).1 = f.1)
    (hnot : ¬t.LastReplacementCompatible f) :
    ∃ h : X ⟶ t.x (Fin.last m).castSucc,
      h ≠ 0 ∧ h ≫ (t.rho (Fin.last m)).1 = f.1 := by
  by_cases hfr : ∃ h, h ≫ (t.rho (Fin.last m)).1 = f.1
  · obtain ⟨h, hh⟩ := hfr
    refine ⟨h, ?_, hh⟩
    rintro rfl
    apply f.2
    simpa using hh.symm
  · have hrf : ∃ h, h ≫ f.1 = (t.rho (Fin.last m)).1 := by
      by_contra hrf
      exact hnot ⟨hrf, hfr⟩
    obtain ⟨h, hh⟩ := hrf
    exfalso
    apply (t.peak_incomparable (Fin.last m)).1
    refine ⟨h ≫ b, ?_⟩
    rw [Category.assoc, hfactor, hh]

/-- The alternating depth word before the final cohook. -/
def efficiencyPrefix [HasFiniteRayPathDepth C] {m : ℕ}
    (t : RayCohookTackle (C := C) m) : List ℕ :=
  alternateLists
    (List.ofFn fun i : Fin (m + 1) ↦ (t.rho i).depth)
    (List.ofFn fun i : Fin m ↦ (t.sigma i.castSucc).depth)

/-- A cohook-tackle efficiency word is its alternating proper prefix followed
by the depth of the last cohook. -/
theorem efficiency_eq_efficiencyPrefix_concat_last
    [HasFiniteRayPathDepth C] {m : ℕ}
    (t : RayCohookTackle (C := C) m) :
    t.efficiency =
      t.efficiencyPrefix.concat (t.sigma (Fin.last m)).depth := by
  unfold RayCohookTackle.efficiency efficiencyPrefix
  rw [List.ofFn_succ'
    (fun i : Fin (m + 1) ↦ (t.sigma i).depth)]
  simpa [List.concat_eq_append] using
    alternateLists_concat_right_of_length_eq_succ
      (List.ofFn fun i : Fin (m + 1) ↦ (t.rho i).depth)
      (List.ofFn fun i : Fin m ↦ (t.sigma i.castSucc).depth)
      (t.sigma (Fin.last m)).depth (by simp)

/-- Replace the last cohook by `f` and append the irreducible hook `g`, while
retaining the complete preceding alternating chain. -/
def extendLastToHook {m : ℕ} (t : RayCohookTackle (C := C) m)
    {X Z : C} (f : NonzeroHom X (t.z (Fin.last m)))
    (g : NonzeroHom X Z)
    (hcompatible : t.LastReplacementCompatible f)
    (hfg : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    RayHookTackle (C := C) (m + 1) := by
  let x' : Fin (m + 2) → C :=
    Fin.lastCases X (fun i : Fin (m + 1) ↦ t.x i.castSucc)
  let z' : Fin (m + 2) → C := Fin.lastCases Z t.z
  have hxCastSucc (i : Fin (m + 1)) :
      x' i.castSucc = t.x i.castSucc := by
    simp [x']
  have hxPrevious (i : Fin m) :
      x' i.castSucc.succ = t.x i.castSucc.succ := by
    rw [Fin.succ_castSucc]
    simpa [Fin.castSucc_succ] using hxCastSucc i.succ
  have hxLast : x' (Fin.last (m + 1)) = X := by
    simp [x']
  have hzCastSucc (i : Fin (m + 1)) : z' i.castSucc = t.z i := by
    simp [z']
  have hzLast : z' (Fin.last (m + 1)) = Z := by
    simp [z']
  let rho' : ∀ i : Fin (m + 2), NonzeroHom (x' i) (z' i) :=
    Fin.lastCases
      (g.cast hxLast.symm hzLast.symm)
      (fun i : Fin (m + 1) ↦
        (t.rho i).cast (hxCastSucc i).symm (hzCastSucc i).symm)
  let sigma' : ∀ i : Fin (m + 1),
      NonzeroHom (x' i.succ) (z' i.castSucc) :=
    Fin.lastCases
      (f.cast hxLast.symm (hzCastSucc (Fin.last m)).symm)
      (fun i : Fin m ↦
        (t.sigma i.castSucc).cast (hxPrevious i).symm
          (hzCastSucc i.castSucc).symm)
  exact
    { x := x'
      z := z'
      rho := rho'
      sigma := sigma'
      peak_incomparable := Fin.lastCases
        (by
          simp only [rho', sigma', Fin.lastCases_castSucc,
            Fin.lastCases_last]
          exact hcompatible.cast (hxCastSucc (Fin.last m)).symm
            hxLast.symm
            (hzCastSucc (Fin.last m)).symm)
        (fun i : Fin m ↦ by
          simp only [rho', sigma', Fin.lastCases_castSucc]
          exact (t.peak_incomparable i.castSucc).cast
            (hxCastSucc i.castSucc).symm (hxPrevious i).symm
            (hzCastSucc i.castSucc).symm)
      valley_incomparable := Fin.lastCases
        (by
          simp only [rho', sigma', Fin.lastCases_last, Fin.succ_last]
          exact hfg.cast hxLast.symm
            (hzCastSucc (Fin.last m)).symm hzLast.symm)
        (fun i : Fin m ↦ by
          have hzNext : t.z i.succ = z' i.castSucc.succ := by
            simpa [Fin.castSucc_succ] using (hzCastSucc i.succ).symm
          simp only [rho', sigma', Fin.lastCases_castSucc,
            Fin.succ_castSucc]
          exact (t.valley_incomparable i).cast (hxPrevious i).symm
            (hzCastSucc i.castSucc).symm hzNext)
      last_irreducible := by
        simp only [rho', Fin.lastCases_last]
        exact isIrreducibleMorphism_cast hxLast.symm hzLast.symm g hg }

@[simp]
theorem extendLastToHook_x_zero {m : ℕ}
    (t : RayCohookTackle (C := C) m) {X Z : C}
    (f : NonzeroHom X (t.z (Fin.last m)))
    (g : NonzeroHom X Z)
    (hcompatible : t.LastReplacementCompatible f)
    (hfg : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    (t.extendLastToHook f g hcompatible hfg hg).x 0 = t.x 0 := by
  change Fin.lastCases X (fun i : Fin (m + 1) ↦ t.x i.castSucc)
      ((0 : Fin (m + 1)).castSucc) = t.x 0
  simpa using (Fin.lastCases_castSucc
    (motive := fun _ : Fin (m + 2) ↦ C)
    (last := X) (cast := fun i : Fin (m + 1) ↦ t.x i.castSucc) 0)

@[simp]
theorem extendLastToHook_rho_castSucc_depth
    [HasFiniteRayPathDepth C] {m : ℕ}
    (t : RayCohookTackle (C := C) m) {X Z : C}
    (f : NonzeroHom X (t.z (Fin.last m)))
    (g : NonzeroHom X Z)
    (hcompatible : t.LastReplacementCompatible f)
    (hfg : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) (i : Fin (m + 1)) :
    ((t.extendLastToHook f g hcompatible hfg hg).rho i.castSucc).depth =
      (t.rho i).depth := by
  simp [extendLastToHook]

@[simp]
theorem extendLastToHook_rho_last_depth
    [HasFiniteRayPathDepth C] {m : ℕ}
    (t : RayCohookTackle (C := C) m) {X Z : C}
    (f : NonzeroHom X (t.z (Fin.last m)))
    (g : NonzeroHom X Z)
    (hcompatible : t.LastReplacementCompatible f)
    (hfg : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    ((t.extendLastToHook f g hcompatible hfg hg).rho
      (Fin.last (m + 1))).depth = g.depth := by
  simp [extendLastToHook]

@[simp]
theorem extendLastToHook_sigma_castSucc_depth
    [HasFiniteRayPathDepth C] {m : ℕ}
    (t : RayCohookTackle (C := C) m) {X Z : C}
    (f : NonzeroHom X (t.z (Fin.last m)))
    (g : NonzeroHom X Z)
    (hcompatible : t.LastReplacementCompatible f)
    (hfg : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) (i : Fin m) :
    ((t.extendLastToHook f g hcompatible hfg hg).sigma i.castSucc).depth =
      (t.sigma i.castSucc).depth := by
  simp [extendLastToHook]

@[simp]
theorem extendLastToHook_sigma_last_depth
    [HasFiniteRayPathDepth C] {m : ℕ}
    (t : RayCohookTackle (C := C) m) {X Z : C}
    (f : NonzeroHom X (t.z (Fin.last m)))
    (g : NonzeroHom X Z)
    (hcompatible : t.LastReplacementCompatible f)
    (hfg : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    ((t.extendLastToHook f g hcompatible hfg hg).sigma
      (Fin.last m)).depth = f.depth := by
  simp [extendLastToHook]

/-- The extended hook tackle has the old cohook-efficiency prefix, followed
by the replacement depth and then the new irreducible hook depth. -/
theorem efficiency_extendLastToHook
    [HasFiniteRayPathDepth C] {m : ℕ}
    (t : RayCohookTackle (C := C) m) {X Z : C}
    (f : NonzeroHom X (t.z (Fin.last m)))
    (g : NonzeroHom X Z)
    (hcompatible : t.LastReplacementCompatible f)
    (hfg : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    (t.extendLastToHook f g hcompatible hfg hg).efficiency =
      t.efficiencyPrefix ++ [f.depth, g.depth] := by
  unfold RayHookTackle.efficiency efficiencyPrefix
  rw [List.ofFn_succ'
    (fun i : Fin (m + 2) ↦
      ((t.extendLastToHook f g hcompatible hfg hg).rho i).depth)]
  rw [List.ofFn_succ'
    (fun i : Fin (m + 1) ↦
      ((t.extendLastToHook f g hcompatible hfg hg).sigma i).depth)]
  rw [alternateLists_concat_both_of_length_eq_succ _ _ _ _ (by simp)]
  congr 1 <;> simp

/-- If the replacement final cohook has depth greater than one, appending the
new irreducible hook produces a strictly larger tackle-efficiency word. -/
theorem efficiency_lex_extendLastToHook
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C] {m : ℕ}
    (t : RayCohookTackle (C := C) m) {X Z : C}
    (f : NonzeroHom X (t.z (Fin.last m)))
    (g : NonzeroHom X Z)
    (hcompatible : t.LastReplacementCompatible f)
    (hfg : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : 1 < f.depth) :
    List.Lex (fun a b : ℕ ↦ a < b)
      (RayTackle.cohook m t).efficiency
      (RayTackle.hook (m + 1)
        (t.extendLastToHook f g hcompatible hfg hg)).efficiency := by
  simp only [RayTackle.efficiency]
  rw [t.efficiency_eq_efficiencyPrefix_concat_last,
    t.efficiency_extendLastToHook f g hcompatible hfg hg,
    t.last_depth_eq_one]
  have htail : List.Lex (fun a b : ℕ ↦ a < b)
      [1] [f.depth, g.depth] :=
    List.Lex.rel hfdepth
  simpa [List.concat_eq_append] using
    List.Lex.append_left (fun a b : ℕ ↦ a < b)
      htail t.efficiencyPrefix

/-- If the replacement is still the old depth-one cohook, appending a hook
strictly increases efficiency because the old word is a proper prefix of the
new word. -/
theorem efficiency_lex_extendLastToHook_of_depth_eq_one
    [IsFiniteRayCategory C] [HasFiniteRayPathDepth C] {m : ℕ}
    (t : RayCohookTackle (C := C) m) {X Z : C}
    (f : NonzeroHom X (t.z (Fin.last m)))
    (g : NonzeroHom X Z)
    (hcompatible : t.LastReplacementCompatible f)
    (hfg : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : f.depth = 1) :
    List.Lex (fun a b : ℕ ↦ a < b)
      (RayTackle.cohook m t).efficiency
      (RayTackle.hook (m + 1)
        (t.extendLastToHook f g hcompatible hfg hg)).efficiency := by
  simp only [RayTackle.efficiency]
  rw [t.efficiency_eq_efficiencyPrefix_concat_last,
    t.efficiency_extendLastToHook f g hcompatible hfg hg,
    t.last_depth_eq_one, hfdepth]
  have htail : List.Lex (fun a b : ℕ ↦ a < b)
      [1] [1, g.depth] :=
    List.Lex.cons List.Lex.nil
  simpa [List.concat_eq_append] using
    List.Lex.append_left (fun a b : ℕ ↦ a < b)
      htail t.efficiencyPrefix

end RayCohookTackle

end LargeIndecomposable
