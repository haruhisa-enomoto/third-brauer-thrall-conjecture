module

public import LargeIndecomposable.FundamentalGroups.SimplyConnectedStages.Stage

/-!
# The stages are simply connected (Fischbacher, Lemmas 2.2 and 2.4, cocycle form)

For a cocycle `c` on a stage `Y_K`, walks of `P' = P/⟨αᵢ⟩` act on pairs (point of the cover over
their start, integer) by lifting arrows and adding the `c`-weights of the lifted arrows
(`liftAct`); homotopies of `P'` lift, so this is an action of the fundamental groupoid of `P'`
(`liftAct_sound`). It transports the equalities of classes in Lemma 2.1's data to equalities of
weights in `Y_K`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [LargeIndecomposable.IsFiniteRayCategory0 P]
  [Finite P] {x₀ : P} {ι : Type} {b : P} {d : ι → P} {α : ∀ i, b ⟶ d i}
  (hα : ∀ i, ¬IsIso (α i))

attribute [local instance] isRayCategory_of_finiteRayCategory

namespace Stage

variable (K : Set (vtx x₀ ⟶ vtx b)) (c : ArrowWeight (Y (x₀ := x₀) (α := α) K))

/-- The lift of an arrow of `P'` to `P`. -/
abbrev inclA {x y : RayVert (ArrowQuot α)} (e : x ⟶ y) :
    RayVert.mk x.out.as ⟶ RayVert.mk y.out.as :=
  (inclQuiver α hα).map e

include hα in
lemma not_mem_lift {x y : RayVert (ArrowQuot α)} (e : x ⟶ y) (u : vtx x₀ ⟶ vtx x.out.as) :
    ¬(arrSetIdeal (killed (x₀ := x₀) (α := α) K)).mem
      (liftArr (⟨x.out.as, u⟩ : Cover x₀) (inclA hα e)).1 :=
  not_mem_of_proj K _ (liftQ_not_mem α hα e.2)

/-- The weight of the lift of an arrow of `P'` at `⟨x, u⟩`. -/
def liftWtQ {x y : RayVert (ArrowQuot α)} (e : x ⟶ y) (u : vtx x₀ ⟶ vtx x.out.as) : ℤ :=
  c (qArrI (isProper K) (liftArr (⟨x.out.as, u⟩ : Cover x₀) (inclA hα e)) (not_mem_lift hα K e u))

/-- The action of an arrow of `P'`. -/
def arrActQ {x y : RayVert (ArrowQuot α)} (e : x ⟶ y) :
    ((vtx x₀ ⟶ vtx x.out.as) × ℤ) ≃ ((vtx x₀ ⟶ vtx y.out.as) × ℤ) where
  toFun p := (p.1 ≫ cls (inclA hα e).1 (inclA hα e).2.1, p.2 + liftWtQ hα K c e p.1)
  invFun q := (q.1 ≫ inv (cls (inclA hα e).1 (inclA hα e).2.1),
    q.2 - liftWtQ hα K c e (q.1 ≫ inv (cls (inclA hα e).1 (inclA hα e).2.1)))
  left_inv p := by
    obtain ⟨u, n⟩ := p
    have h : (u ≫ cls (inclA hα e).1 (inclA hα e).2.1) ≫
        inv (cls (inclA hα e).1 (inclA hα e).2.1) = u := by simp
    simp only [h, add_sub_cancel_right]
  right_inv q := by
    obtain ⟨v, m⟩ := q
    simp

/-- The action of arrows of `P'` as a prefunctor. -/
def liftPreQ : RayVert (ArrowQuot α) ⥤q EqvGrpd where
  obj x := ⟨(vtx x₀ ⟶ vtx x.out.as) × ℤ⟩
  map e := arrActQ hα K c e

/-- The action of walks of `P'`. -/
def liftAct : Quiver.FreeGroupoid (RayVert (ArrowQuot α)) ⥤ EqvGrpd :=
  Quiver.FreeGroupoid.lift (liftPreQ hα K c)

/-- A cover morphism whose projection lies outside the ideal of `P` lies outside the stage
ideal. -/
lemma not_mem_K_of_val {a a' : Cover x₀} (f : a ⟶ a') (h : ¬(arrowIdeal α).mem (Cover.val f)) :
    ¬(arrSetIdeal (killed (x₀ := x₀) (α := α) K)).mem f := by
  rintro (h0 | ⟨x, y, e, ⟨w, -, rfl, hm⟩, g, k, rfl⟩)
  · exact h (by rw [h0]; exact Or.inl rfl)
  · apply h
    rw [Cover.val_comp, Cover.val_comp]
    exact (arrowIdeal α).precomp _ ((arrowIdeal α).postcomp _ hm)

lemma ev_liftAct_comp {X Y Z : Quiver.FreeGroupoid (RayVert (ArrowQuot α))} (f : X ⟶ Y)
    (g : Y ⟶ Z) (p : ((liftAct hα K c).obj X).carrier) :
    ev ((liftAct hα K c).map (f ≫ g)) p = ev ((liftAct hα K c).map g) (ev ((liftAct hα K c).map f) p) := by
  rw [Functor.map_comp]
  rfl

/-- **Lifting a path of `P'`.** -/
lemma liftAct_path {x : RayVert (ArrowQuot α)} : ∀ {y : RayVert (ArrowQuot α)}
    (p : Quiver.Path x y) (u : vtx x₀ ⟶ vtx x.out.as) (n : ℤ),
    ∃ (v : vtx x₀ ⟶ vtx y.out.as) (pt : Quiver.Path (RayVert.mk (⟨x.out.as, u⟩ : Cover x₀))
        (RayVert.mk (⟨y.out.as, v⟩ : Cover x₀)))
      (h : AvoidsI (arrSetIdeal (killed (x₀ := x₀) (α := α) K)) pt),
      v = u ≫ Cover.pcls ((inclQuiver α hα).mapPath p) ∧
      ev ((liftAct hα K c).map (pathFG p)) ((u, n) : (vtx x₀ ⟶ vtx x.out.as) × ℤ) =
          (v, n + pathWeight c (toQI (isProper K) pt h)) ∧
        Cover.val (pathVal pt) = pathVal ((inclQuiver α hα).mapPath p)
  | _, .nil, u, n => by
    refine ⟨u, Quiver.Path.nil, show AvoidsI _ Quiver.Path.nil from trivial, ?_, ?_, rfl⟩
    · change u = u ≫ (CategoryTheory.Quotient.functor homotopy).map (𝟙 _)
      rw [CategoryTheory.Functor.map_id]
      exact (Category.comp_id (obj := FundGroupoid P) u).symm
    · simp only [pathFG, CategoryTheory.Functor.map_id]
      exact Prod.ext rfl (by change n = n + 0; rw [add_zero])
  | _, .cons p e, u, n => by
    obtain ⟨v, pt, hpt, hv, h1, h2⟩ := liftAct_path p u n
    refine ⟨v ≫ cls (inclA hα e).1 (inclA hα e).2.1,
      pt.cons (liftArr (⟨_, v⟩ : Cover x₀) (inclA hα e)), ⟨hpt, not_mem_lift hα K e _⟩, ?_, ?_, ?_⟩
    · rw [hv, Prefunctor.mapPath_cons]
      exact ((congrArg (u ≫ ·) (Cover.pcls_cons _ _)).trans (Category.assoc _ _ _).symm).symm
    · change ev ((liftAct hα K c).map (pathFG p ≫ (Quiver.FreeGroupoid.of _).map e))
        ((u, n) : (vtx x₀ ⟶ vtx x.out.as) × ℤ) = _
      erw [ev_liftAct_comp, h1]
      exact Prod.ext rfl (add_assoc _ _ _)
    · change Cover.val (pathVal pt ≫ (liftArr _ (inclA hα e)).1) =
        pathVal ((inclQuiver α hα).mapPath p) ≫ (inclA hα e).1
      rw [Cover.val_comp, h2]
      rfl

/-- **Homotopies of `P'` lift.** -/
lemma liftAct_sound (hc : IsCocycle c) {X Y : Quiver.FreeGroupoid (RayVert (ArrowQuot α))}
    (f g : X ⟶ Y) (h : homotopy f g) : (liftAct hα K c).map f = (liftAct hα K c).map g := by
  cases h with
  | path p q hpq h0 =>
    refine Equiv.ext fun (un : (vtx x₀ ⟶ vtx _) × ℤ) ↦ ?_
    obtain ⟨u, n⟩ := un
    obtain ⟨v, pt, hpt, hv, h1, h2⟩ := liftAct_path hα K c p u n
    obtain ⟨v', qt, hqt, hv', h1', h2'⟩ := liftAct_path hα K c q u n
    have hm : ¬(arrowIdeal α).mem (pathVal ((inclQuiver α hα).mapPath p)) := by
      rw [← (arrowIdeal α).functor_map_ne_zero_iff, pathVal_inclQuiver]; exact h0
    have hpq' : pathVal ((inclQuiver α hα).mapPath p) = pathVal ((inclQuiver α hα).mapPath q) :=
      quotF_map_injective α hm (by rw [pathVal_inclQuiver, pathVal_inclQuiver, hpq])
    have hvv : v = v' := by
      rw [hv, hv']
      congr 1
      exact homotopic_of_pathVal_eq _ _ hpq' (fun h ↦ hm (h ▸ (arrowIdeal α).zero_mem _ _))
    subst hvv
    have hval : pathVal pt = pathVal qt := Cover.val_injective (h2.trans (hpq'.trans h2'.symm))
    have hne : pathVal (toQI (isProper K) pt hpt) ≠ 0 := by
      rw [pathVal_toQI]
      exact (LargeIndecomposable.ZeroHomIdeal.functor_map_ne_zero_iff _ _).2
        (not_mem_K_of_val K _ (by rw [h2]; exact hm))
    change ev ((liftAct hα K c).map (pathFG p)) ((u, n) : (vtx x₀ ⟶ vtx _) × ℤ) =
      ev ((liftAct hα K c).map (pathFG q)) ((u, n) : (vtx x₀ ⟶ vtx _) × ℤ)
    erw [h1, h1']
    have hw := hc (toQI (isProper K) pt hpt) (toQI (isProper K) qt hqt)
      (by simp only [pathVal_toQI, hval]) hne
    exact Prod.ext rfl (congrArg (n + ·) hw)

/-- **The action of the fundamental groupoid of `P'`.** -/
def liftActQ (hc : IsCocycle c) : FundGroupoid (ArrowQuot α) ⥤ EqvGrpd :=
  CategoryTheory.Quotient.lift homotopy (liftAct hα K c) fun _ _ f g h ↦ liftAct_sound hα K c hc f g h

variable (D : RedData α)

lemma avoids_uT (w : vtx x₀ ⟶ vtx b) :
    AvoidsI (arrSetIdeal (killed (x₀ := x₀) (α := α) K)) (uT D w) :=
  avoidsI_of_proj K _ (by rw [projPath_uT]; exact D.hu)

lemma avoids_usT (w : vtx x₀ ⟶ vtx b) (i : ι) :
    AvoidsI (arrSetIdeal (killed (x₀ := x₀) (α := α) K)) (usT D w i) :=
  avoidsI_of_proj K _ (by rw [eq_of_heq (projPath_usT D w i)]; exact D.avoids_us i)

/-- The weight of a killed lift of `aᵢ` at `⟨b, w⟩`: `c(ũ) − c(ũᵢ)`. -/
def killedWt (w : vtx x₀ ⟶ vtx b) (i : ι) : ℤ :=
  pathWeight c (toQI (isProper K) (uT D w) (avoids_uT K D w)) -
    pathWeight c (toQI (isProper K) (usT D w i) (avoids_usT K D w i))

open Classical in
/-- **The extension of a stage weight to the cover.** -/
def cT : ArrowWeight (Cover x₀) := fun {x y} e ↦
  if h : killed (α := α) K e then
    killedWt K c D (eq_aT_of_killed (hα := hα) D K e h).choose
      (eq_aT_of_killed (hα := hα) D K e h).choose_spec.2.choose
  else c (qArrI (isProper K) e fun hm ↦ h (mem_of_irreducible _ e hm))

lemma cT_of_not_killed {x y : RayVert (Cover x₀)} (e : x ⟶ y) (h : ¬killed (α := α) K e) :
    cT hα K c D e = c (qArrI (isProper K) e fun hm ↦ h (mem_of_irreducible _ e hm)) :=
  dif_neg h

lemma cT_of_not_mem {x y : RayVert (Cover x₀)} (e : x ⟶ y)
    (h : ¬(arrSetIdeal (killed (x₀ := x₀) (α := α) K)).mem e.1) :
    cT hα K c D e = c (qArrI (isProper K) e h) :=
  cT_of_not_killed hα K c D e fun hk ↦ h (Or.inr ⟨_, _, e, hk, 𝟙 _, 𝟙 _, by simp⟩)

/-- The weight of a path avoiding the stage ideal is its stage weight. -/
lemma pathWeight_cT {x : RayVert (Cover x₀)} : ∀ {y : RayVert (Cover x₀)} (p : Quiver.Path x y)
    (h : AvoidsI (arrSetIdeal (killed (x₀ := x₀) (α := α) K)) p),
    pathWeight (cT hα K c D) p = pathWeight c (toQI (isProper K) p h)
  | _, .nil, _ => rfl
  | _, .cons p e, h => by
    change pathWeight (cT hα K c D) p + cT hα K c D e =
      pathWeight c (toQI (isProper K) p h.1) + c (qArrI (isProper K) e h.2)
    rw [pathWeight_cT p h.1, cT_of_not_mem hα K c D e h.2]

lemma aT_killed_iff (w : vtx x₀ ⟶ vtx b) (i : ι) :
    killed (α := α) K (aT D w i) ↔ w ∈ K := by
  constructor
  · rintro ⟨w', hw', hx, -⟩
    have : w = w' := (Cover.mk.inj hx).2 |> eq_of_heq
    exact this ▸ hw'
  · intro hw
    refine ⟨w, hw, rfl, Or.inr ⟨i, 𝟙 _, 𝟙 _, ?_⟩⟩
    change (D.a i).1 = _
    rw [Category.id_comp, Category.comp_id]; exact D.a_val i

lemma val_heq {a : Cover x₀} {T T' : Cover x₀} (hT : T = T')
    (e : RayVert.mk a ⟶ RayVert.mk T) (e' : RayVert.mk a ⟶ RayVert.mk T') (h : HEq e e') :
    Cover.val e.1 ≫ eqToHom (congrArg Cover.y hT) = Cover.val e'.1 := by
  subst hT
  rw [eq_of_heq h]
  simp

lemma killedWt_unique (w : vtx x₀ ⟶ vtx b) (i : ι) (w' : vtx x₀ ⟶ vtx b) (i' : ι)
    (hx : (RayVert.mk (pt w) : RayVert (Cover x₀)) = RayVert.mk (pt w'))
    (hy : (RayVert.mk (⟨d i, w ≫ cls (D.a i).1 (D.a i).2.1⟩ : Cover x₀) : RayVert (Cover x₀)) =
      RayVert.mk (⟨d i', w' ≫ cls (D.a i').1 (D.a i').2.1⟩ : Cover x₀))
    (he : HEq (aT D w i) (aT D w' i')) : killedWt K c D w' i' = killedWt K c D w i := by
  have hww : w = w' := (Cover.mk.inj hx).2 |> eq_of_heq
  subst hww
  have hval := val_heq hy _ _ he
  have hii : i = i' := by
    refine D.a_inj _ _ (Cover.mk.inj hy).1 ?_
    have h1 : Cover.val (aT D w i).1 = α i := D.a_val i
    have h2 : Cover.val (aT D w i').1 = α i' := D.a_val i'
    rw [h1, h2] at hval
    exact hval
  rw [hii]

/-- **The weight of a killed lift of `aᵢ`.** -/
lemma cT_aT {w : vtx x₀ ⟶ vtx b} (hw : w ∈ K) (i : ι) :
    cT hα K c D (aT D w i) = killedWt K c D w i := by
  have hk : killed (α := α) K (aT D w i) := (aT_killed_iff K D w i).2 hw
  unfold cT
  rw [dif_pos hk]
  obtain ⟨hx, hy, he⟩ := (eq_aT_of_killed (hα := hα) D K (aT D w i) hk).choose_spec.2.choose_spec
  exact killedWt_unique K c D w i _ _ hx hy he

/-- The weight of a surviving lift of `aᵢ`. -/
lemma cT_aT_of_not_mem {w : vtx x₀ ⟶ vtx b} (hw : w ∉ K) (i : ι) :
    cT hα K c D (aT D w i) =
      c (qArrI (isProper K) (aT D w i) fun hm ↦ hw ((aT_killed_iff K D w i).1
        (mem_of_irreducible _ _ hm))) :=
  cT_of_not_killed hα K c D _ fun hk ↦ hw ((aT_killed_iff K D w i).1 hk)

end Stage

end LargeIndecomposable.RayCat
