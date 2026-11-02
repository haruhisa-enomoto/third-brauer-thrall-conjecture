module

public import LargeIndecomposable.MildContours.Setup.RayPathBridge
public import LargeIndecomposable.MildContours.Contours.ExcContour
public import LargeIndecomposable.MultiplicativeBases.Twisted.LoopEndomorphismKill

/-!
# From the ray-level exceptional data to twist hypotheses

Arrows and paths of `RaySmall C` versus reversed ray paths (`fromArr`, `fromP`): the kill
conditions, loop generation and "another arrow" statements transfer.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable

universe v

namespace RayCat

lemma rpow_eq_pow {D : Type*} [Category D] {X : D} (f : X ⟶ X) :
    ∀ n, (End.of f ^ n).asHom = rpow f n
  | 0 => rfl
  | n + 1 => by
    rw [pow_succ, End.mul_def]
    change f ≫ (End.of f ^ n).asHom = _
    rw [rpow_eq_pow f n, ← rpow_succ', rpow_succ]

variable {C : Type} [Category.{v} C] [HasZeroMorphisms C] [LocallySmall.{0} C]

lemma sh_rpow {X : RaySmall.{0} C} (f : X.as ⟶ X.as) :
    ∀ n, RaySmall.sh (rpow f n) = rpow (RaySmall.sh f) n
  | 0 => rfl
  | n + 1 => by rw [rpow_succ, RaySmall.sh_comp, sh_rpow f n, rpow_succ]

lemma rayPathMap_loopPath {i : RayVertex C} (ℓ : i ⟶ i) (n : ℕ) :
    rayPathMap (RadicalLoopKill.loopPath ℓ n) = rpow ℓ.1 n := by
  rw [← rpow_eq_pow]
  exact RadicalLoopKill.pathMap_loopPath RayVertex.obj rayArrowMorphism ℓ n

lemma reversedArr_fromArr {X Y : RayVert (RaySmall.{0} C)} (e : X ⟶ Y) : reversedArr (fromArr e) = e :=
  Subtype.ext (Equiv.apply_symm_apply _ _)

lemma fromArr_reversedArr {i j : RayVertex C} (a : i ⟶ j) : fromArr (reversedArr a) = a :=
  Subtype.ext (Equiv.symm_apply_apply _ _)

/-- "Another arrow" transfers from the reversed ray quiver to `RaySmall C` (arrows out of a point). -/
lemma not_heq_reversedArr_out {m X : RayVertex C} (e : X ⟶ m) (ℓ : X ⟶ X)
    (he : ¬∃ _ : m = X, HEq e ℓ) :
    ¬∃ _ : (RayVert.mk (⟨m.obj⟩ : RaySmall.{0} C) : RayVert (RaySmall.{0} C)) = RayVert.mk ⟨X.obj⟩,
      HEq (reversedArr e) (reversedArr ℓ) := by
  rintro ⟨hm, hh⟩
  apply he
  have hmX : m = X := by
    have := congrArg (fun z : RaySmall.{0} C ↦ (⟨z.as⟩ : RayVertex C)) hm
    exact this
  subst hmX
  refine ⟨rfl, heq_of_eq ?_⟩
  have := congrArg fromArr (eq_of_heq hh)
  rwa [fromArr_reversedArr, fromArr_reversedArr] at this

/-- "Another arrow" transfers from the reversed ray quiver to `RaySmall C` (arrows into a point). -/
lemma not_heq_reversedArr_in {m X : RayVertex C} (e : m ⟶ X) (ℓ : X ⟶ X)
    (he : ¬∃ _ : m = X, HEq e ℓ) :
    ¬∃ _ : (RayVert.mk (⟨m.obj⟩ : RaySmall.{0} C) : RayVert (RaySmall.{0} C)) = RayVert.mk ⟨X.obj⟩,
      HEq (reversedArr e) (reversedArr ℓ) := by
  rintro ⟨hm, hh⟩
  apply he
  have hmX : m = X := by
    have := congrArg (fun z : RaySmall.{0} C ↦ (⟨z.as⟩ : RayVertex C)) hm
    exact this
  subst hmX
  refine ⟨rfl, heq_of_eq ?_⟩
  have := congrArg fromArr (eq_of_heq hh)
  rwa [fromArr_reversedArr, fromArr_reversedArr] at this

/-- **Kill on the target side**, from `RaySmall C` to the reversed ray quiver. -/
lemma kill_tgt_transfer {i₀ X : RayVertex C} (ac : i₀ ⟶ X) (ℓc : X ⟶ X)
    (hP : ∀ {m' : RayVert (RaySmall.{0} C)} (e' : m' ⟶ RayVert.mk ⟨X.obj⟩),
      ¬(∃ _ : m' = RayVert.mk ⟨X.obj⟩, HEq e' (reversedArr ℓc)) →
        ∀ n, e'.1 ≫ rpow (reversedArr ℓc).1 n ≫ (reversedArr ac).1 = 0)
    {m : RayVertex C} (e : X ⟶ m) (he : ¬∃ _ : m = X, HEq e ℓc) (n : ℕ) :
    rayPathMap (((Quiver.Path.nil.cons ac).comp (RadicalLoopKill.loopPath ℓc n)).cons e) = 0 := by
  have h := hP (reversedArr e) (not_heq_reversedArr_out e ℓc he) n
  rw [rayPathMap_cons', rayPathMap_comp', rayPathMap_loopPath, rayPathMap_cons', rayPathMap_nil',
    Category.comp_id]
  apply (RaySmall.sh_eq_zero_iff (X := (⟨m.obj⟩ : RaySmall.{0} C)) (Y := ⟨i₀.obj⟩) _).1
  rw [RaySmall.sh_comp (Y := (⟨X.obj⟩ : RaySmall.{0} C)), RaySmall.sh_comp (Y := (⟨X.obj⟩ : RaySmall.{0} C)),
    sh_rpow]
  exact h

/-- **Kill on the source side**, from `RaySmall C` to the reversed ray quiver. -/
lemma kill_src_transfer {X j₀ : RayVertex C} (ac : X ⟶ j₀) (ℓc : X ⟶ X)
    (hP : ∀ {m' : RayVert (RaySmall.{0} C)} (e' : RayVert.mk ⟨X.obj⟩ ⟶ m'),
      ¬(∃ _ : m' = RayVert.mk ⟨X.obj⟩, HEq e' (reversedArr ℓc)) →
        ∀ n, (reversedArr ac).1 ≫ rpow (reversedArr ℓc).1 n ≫ e'.1 = 0)
    {m : RayVertex C} (e : m ⟶ X) (he : ¬∃ _ : m = X, HEq e ℓc) (n : ℕ) :
    rayPathMap (((Quiver.Path.nil.cons e).comp (RadicalLoopKill.loopPath ℓc n)).cons ac) = 0 := by
  have h := hP (reversedArr e) (not_heq_reversedArr_in e ℓc he) n
  rw [rayPathMap_cons', rayPathMap_comp', rayPathMap_loopPath, rayPathMap_cons', rayPathMap_nil',
    Category.comp_id]
  apply (RaySmall.sh_eq_zero_iff (X := (⟨j₀.obj⟩ : RaySmall.{0} C)) (Y := ⟨m.obj⟩) _).1
  rw [RaySmall.sh_comp (Y := (⟨X.obj⟩ : RaySmall.{0} C)), RaySmall.sh_comp (Y := (⟨X.obj⟩ : RaySmall.{0} C)),
    sh_rpow]
  exact h

/-- **Loop generation** transfers from `RaySmall C` to the reversed ray quiver. -/
lemma loopGen_transfer {X : RayVertex C} (ℓc : X ⟶ X) (h : LoopGen' (reversedArr ℓc)) :
    ∀ f : X.obj ⟶ X.obj, ¬IsIso f → ∃ n, 0 < n ∧ f = (End.of ℓc.1 ^ n).asHom := by
  intro f hf
  obtain ⟨n, hn, hfn⟩ := h (RaySmall.sh (X := (⟨X.obj⟩ : RaySmall.{0} C)) (Y := ⟨X.obj⟩) f)
    (fun h' ↦ hf ((RaySmall.isIso_sh_iff (X := (⟨X.obj⟩ : RaySmall.{0} C)) (Y := ⟨X.obj⟩) f).1 h'))
  refine ⟨n, hn, ?_⟩
  rw [rpow_eq_pow]
  apply (RaySmall.sh (X := (⟨X.obj⟩ : RaySmall.{0} C)) (Y := ⟨X.obj⟩)).injective
  rw [sh_rpow]
  exact hfn

end RayCat

end LargeIndecomposable
