module

public import LargeIndecomposable.RayCategories.Basic.QuotRay
public import LargeIndecomposable.FundamentalGroups.Fischbacher.CycleStep
public import LargeIndecomposable.FundamentalGroups.Basic.CocycleExtend
public import LargeIndecomposable.FundamentalGroups.Fischbacher.Lemma42

/-!
# Nested quotients

Let `I ≤ J` be proper zero ideals of a ray category `C`, `A = C/I` and `B = C/J`. An arrow of `A`
is *new* when its lift lies in `J`. Old paths of `A` are paths of `B` (`toB`), and conversely
(`toA`). Hence cycle-freeness and interval-finiteness of `B` give the old-path hypotheses of
`cycleFree_of_step` and `intervalFinite_of_step` for `A` (`oldCycle_trivial`,
`oldInterval_finite`), and if `B` is simply connected and every new arrow `e` satisfies a nonzero
relation `e uₑ = u` with old paths `uₑ, u`, then `A` is simply connected (`isCoboundary_of_nested`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits LargeIndecomposable

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [IsRayCategory C]
  {I J : ZeroHomIdeal C} (hI : I.IsProper) (hJ : J.IsProper)

lemma liftArrQ_qArrI' {x y : RayVert C} (e : x ⟶ y) (he : ¬I.mem e.1) :
    (liftArrQ hI (qArrI hI e he)).1 = e.1 := by
  have h : (qF (I := I)).map (liftArrQ hI (qArrI hI e he)).1 = (qF (I := I)).map e.1 :=
    Quot.out_eq _
  rcases (CategoryTheory.Quotient.functor_map_eq_iff _ _ _).1 h with h | h
  · exact h
  · exact absurd h.2 he

omit [IsRayCategory C] in
lemma length_toQI {x : RayVert C} : ∀ {y : RayVert C} (p : Quiver.Path x y) (h : AvoidsI I p),
    (toQI hI p h).length = p.length
  | _, .nil, _ => rfl
  | _, .cons p _, h => by
    change (toQI hI p h.1).length + 1 = p.length + 1
    rw [length_toQI p h.1]

omit [IsRayCategory C] in
lemma length_inclQ {x : RayVert (CategoryTheory.Quotient I.rel)} :
    ∀ {y : RayVert (CategoryTheory.Quotient I.rel)} (r : Quiver.Path x y),
      ((inclQ hI).mapPath r).length = r.length
  | _, .nil => rfl
  | _, .cons r _ => by
    change ((inclQ hI).mapPath r).length + 1 = r.length + 1
    rw [length_inclQ r]

/-- New arrows of `C/I`: their lifts lie in `J`. -/
def IsNewA {x y : RayVert (CategoryTheory.Quotient I.rel)} (e : x ⟶ y) : Prop :=
  J.mem (liftArrQ hI e).1

lemma avoidsJ_of_old {x : RayVert (CategoryTheory.Quotient I.rel)} :
    ∀ {y : RayVert (CategoryTheory.Quotient I.rel)} (r : Quiver.Path x y),
      OldPath (IsNewA (J := J) hI) r → AvoidsI J ((inclQ hI).mapPath r)
  | _, .nil, _ => trivial
  | _, .cons r _, h => ⟨avoidsJ_of_old r h.1, h.2⟩

/-- An old path of `C/I` as a path of `C/J`. -/
def toB {x y : RayVert (CategoryTheory.Quotient I.rel)} (r : Quiver.Path x y)
    (h : OldPath (IsNewA (J := J) hI) r) :
    Quiver.Path (qVt (I := J) ((inclQ hI).obj x)) (qVt (I := J) ((inclQ hI).obj y)) :=
  toQI hJ ((inclQ hI).mapPath r) (avoidsJ_of_old hI r h)

lemma length_toB {x y : RayVert (CategoryTheory.Quotient I.rel)} (r : Quiver.Path x y)
    (h : OldPath (IsNewA (J := J) hI) r) : (toB hI hJ r h).length = r.length := by
  rw [toB, length_toQI, length_inclQ]

variable [IsRayCategory (CategoryTheory.Quotient I.rel)] [IsRayCategory (CategoryTheory.Quotient J.rel)]

include hJ in
/-- **Old cycles are trivial** when `C/J` has no oriented cycles. -/
theorem oldCycle_trivial
    (hcf : ∀ (x : RayVert (CategoryTheory.Quotient J.rel)) (p : Quiver.Path x x), p.length = 0) :
    ∀ (x : RayVert (CategoryTheory.Quotient I.rel)) (p : Quiver.Path x x),
      OldPath (IsNewA (J := J) hI) p → p.length = 0 := fun x p h ↦ by
  rw [← length_toB hI hJ p h]
  exact hcf _ _

include hJ in
/-- **Old intervals are finite** when `C/J` is interval-finite. -/
theorem oldInterval_finite (hint : ∀ a b : CategoryTheory.Quotient J.rel, (interval a b).Finite)
    (a b : CategoryTheory.Quotient I.rel) :
    {z : CategoryTheory.Quotient I.rel | (∃ p : Quiver.Path (RayVert.mk a) (RayVert.mk z),
      OldPath (IsNewA (J := J) hI) p) ∧ ∃ q : Quiver.Path (RayVert.mk z) (RayVert.mk b),
        OldPath (IsNewA (J := J) hI) q}.Finite := by
  have hinj : Function.Injective (fun z : CategoryTheory.Quotient I.rel ↦
      (⟨z.as⟩ : CategoryTheory.Quotient J.rel)) := fun z z' h ↦ by
    cases z; cases z'; cases h; rfl
  refine (((hint ⟨a.as⟩ ⟨b.as⟩).preimage hinj.injOn).subset ?_)
  rintro z ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
  exact ⟨⟨toB hI hJ p hp⟩, ⟨toB hI hJ q hq⟩⟩

variable (hIJ : ∀ {X Y : C} (f : X ⟶ Y), I.mem f → J.mem f)

include hIJ in
omit [IsRayCategory (CategoryTheory.Quotient I.rel)]
  [IsRayCategory (CategoryTheory.Quotient J.rel)] in
lemma avoidsI_of_avoidsJ {x : RayVert C} : ∀ {y : RayVert C} (p : Quiver.Path x y),
    AvoidsI J p → AvoidsI I p
  | _, .nil, _ => trivial
  | _, .cons p _, h => ⟨avoidsI_of_avoidsJ p h.1, fun hm ↦ h.2 (hIJ _ hm)⟩

/-- A path of `C/J` as a path of `C/I`. -/
def toA {x y : RayVert (CategoryTheory.Quotient J.rel)} (r : Quiver.Path x y) :
    Quiver.Path (qVt (I := I) ((inclQ hJ).obj x)) (qVt (I := I) ((inclQ hJ).obj y)) :=
  toQI hI ((inclQ hJ).mapPath r) (avoidsI_of_avoidsJ hIJ _ (avoidsI_inclQ hJ r))

/-- The restriction of a weight of `C/I` to `C/J`. -/
def resB (c : ArrowWeight (CategoryTheory.Quotient I.rel)) :
    ArrowWeight (CategoryTheory.Quotient J.rel) := fun {_ _} e ↦
  c (qArrI hI (liftArrQ hJ e) (fun h ↦ liftArrQ_not_mem hJ e (hIJ _ h)))

lemma pathWeight_toA (c : ArrowWeight (CategoryTheory.Quotient I.rel))
    {x : RayVert (CategoryTheory.Quotient J.rel)} :
    ∀ {y : RayVert (CategoryTheory.Quotient J.rel)} (r : Quiver.Path x y),
      pathWeight (resB hI hJ hIJ c) r = pathWeight c (toA hI hJ hIJ r)
  | _, .nil => rfl
  | _, .cons r e => by
    change pathWeight (resB hI hJ hIJ c) r + resB hI hJ hIJ c e =
      pathWeight c (toA hI hJ hIJ r) + c _
    rw [pathWeight_toA c r]
    rfl

lemma isCocycle_resB {c : ArrowWeight (CategoryTheory.Quotient I.rel)} (hc : IsCocycle c) :
    IsCocycle (resB hI hJ hIJ c) := by
  intro x y p q hpq h0
  rw [pathWeight_toA, pathWeight_toA]
  have hp := pathVal_inclQ hJ p
  have hq := pathVal_inclQ hJ q
  have hm : ¬J.mem (pathVal ((inclQ hJ).mapPath p)) :=
    (J.functor_map_ne_zero_iff _).1 (hp ▸ h0)
  have heq : pathVal ((inclQ hJ).mapPath p) = pathVal ((inclQ hJ).mapPath q) := by
    have h1 : (qF (I := J)).map (pathVal ((inclQ hJ).mapPath p)) =
        (qF (I := J)).map (pathVal ((inclQ hJ).mapPath q)) := by rw [hp, hq, hpq]
    rcases (CategoryTheory.Quotient.functor_map_eq_iff _ _ _).1 h1 with h | h
    · exact h
    · exact absurd h.1 hm
  refine hc _ _ ?_ ?_
  · rw [toA, toA, pathVal_toQI, pathVal_toQI, heq]
  · rw [toA, pathVal_toQI]
    exact (I.functor_map_ne_zero_iff _).2 fun h ↦ hm (hIJ _ h)

include hIJ in
omit [IsRayCategory (CategoryTheory.Quotient I.rel)]
  [IsRayCategory (CategoryTheory.Quotient J.rel)] in
/-- A path of `C` avoiding `J` is an old path of `C/I`. -/
lemma oldPath_toQI {x : RayVert C} : ∀ {y : RayVert C} (p : Quiver.Path x y) (h : AvoidsI J p),
    OldPath (IsNewA (J := J) hI) (toQI hI p (avoidsI_of_avoidsJ hIJ p h))
  | _, .nil, _ => trivial
  | _, .cons p e, h => ⟨oldPath_toQI p h.1, fun hn ↦ h.2 (by
      have := liftArrQ_qArrI' hI e (fun hm ↦ h.2 (hIJ _ hm))
      exact (congrArg (fun t ↦ J.mem t) this).mp hn)⟩

include hJ hIJ in
/-- **Nested quotients and simple connectivity**: if `C/J` is simply connected and every new
arrow of `C/I` satisfies a nonzero relation through old paths, `C/I` is simply connected. -/
theorem isCoboundary_of_nested
    (hold : ∀ c' : ArrowWeight (CategoryTheory.Quotient J.rel), IsCocycle c' → IsCoboundary c')
    (hrel : ∀ {x y : RayVert (CategoryTheory.Quotient I.rel)} (e : x ⟶ y), IsNewA (J := J) hI e →
      ∃ (z : RayVert (CategoryTheory.Quotient I.rel)) (ue : Quiver.Path y z) (u : Quiver.Path x z),
        OldPath (IsNewA (J := J) hI) ue ∧ OldPath (IsNewA (J := J) hI) u ∧
          e.1 ≫ pathVal ue = pathVal u ∧ pathVal u ≠ 0)
    (c : ArrowWeight (CategoryTheory.Quotient I.rel)) (hc : IsCocycle c) : IsCoboundary c := by
  obtain ⟨φ', hφ'⟩ := hold _ (isCocycle_resB hI hJ hIJ hc)
  let φ : RayVert (CategoryTheory.Quotient I.rel) → ℤ :=
    fun x ↦ φ' (qVt (I := J) ((inclQ hI).obj x))
  have hold_arr : ∀ {x y : RayVert (CategoryTheory.Quotient I.rel)} (e : x ⟶ y),
      ¬IsNewA (J := J) hI e → c e = φ y - φ x := by
    intro x y e he
    have h3 : (qArrI hI (liftArrQ hJ (qArrI hJ (liftArrQ hI e) he))
        (fun h ↦ liftArrQ_not_mem hJ _ (hIJ _ h)) : x ⟶ y) = e := by
      apply Subtype.ext
      change (qF (I := I)).map (liftArrQ hJ (qArrI hJ (liftArrQ hI e) he)).1 = e.1
      exact (congrArg (qF (I := I)).map (liftArrQ_qArrI' hJ (liftArrQ hI e) he)).trans
        (Quot.out_eq e.1)
    have h2 : resB hI hJ hIJ c (qArrI hJ (liftArrQ hI e) he) = c e :=
      congrArg (fun t : x ⟶ y ↦ c t) h3
    exact h2.symm.trans (hφ' _)
  have hpath : ∀ {x : RayVert (CategoryTheory.Quotient I.rel)}
      {y : RayVert (CategoryTheory.Quotient I.rel)} (r : Quiver.Path x y),
      OldPath (IsNewA (J := J) hI) r → pathWeight c r = φ y - φ x := by
    intro x y r
    induction r with
    | nil => intro; simp [pathWeight]
    | cons r e ih =>
      intro h
      change pathWeight c r + c e = _
      rw [ih h.1, hold_arr e h.2]
      ring
  refine ⟨φ, fun {x y} e ↦ ?_⟩
  by_cases he : IsNewA (J := J) hI e
  · obtain ⟨z, ue, u, hue, hu, hv, h0⟩ := hrel e he
    have h := hc (e.toPath.comp ue) u (by rw [pathVal_comp, pathVal_toPath]; exact hv)
      (by rw [pathVal_comp, pathVal_toPath, hv]; exact h0)
    rw [pathWeight_comp, hpath ue hue, hpath u hu] at h
    have h4 : pathWeight c e.toPath = c e := by
      change 0 + c e = c e
      rw [zero_add]
    rw [h4] at h
    linarith
  · exact hold_arr e he

end LargeIndecomposable.RayCat
