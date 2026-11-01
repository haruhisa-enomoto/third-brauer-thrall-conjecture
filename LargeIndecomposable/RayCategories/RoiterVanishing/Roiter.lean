module

public import LargeIndecomposable.FundamentalGroups.Basic.FreePi

/-!
# Roiter's vanishing theorem

A contour function with values in an abelian group `Z` assigns `c p q ∈ Z` to
paths `p, q` with the same nonzero value, additively in the contour and
invariantly under common whiskers; it is exact if `c p q = a(p) − a(q)` for a
function `a` on the arrows. Roiter's theorem (Fischbacher, §3.2): on a finite
chain-bounded ray category with cancellation every contour function is exact
(`RayCat.ContourFn.exact`). The proof follows the reduction of Lemma 2.1/2.2.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Opposite

universe v u

namespace RayCat

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P] {Z : Type*} [AddCommGroup Z]

/-- The sum of an arrow function along a path. -/
def pathSum (a : ∀ {x y : RayVert P}, (x ⟶ y) → Z) {x : RayVert P} :
    ∀ {y : RayVert P}, Quiver.Path x y → Z
  | _, .nil => 0
  | _, .cons p e => pathSum a p + a e

lemma pathSum_comp (a : ∀ {x y : RayVert P}, (x ⟶ y) → Z) {x y : RayVert P}
    (p : Quiver.Path x y) : ∀ {z : RayVert P} (q : Quiver.Path y z),
    pathSum a (p.comp q) = pathSum a p + pathSum a q
  | _, .nil => (add_zero _).symm
  | _, .cons q e => by
    change pathSum a (p.comp q) + a e = pathSum a p + (pathSum a q + a e)
    rw [pathSum_comp a p q, add_assoc]

/-- A contour function with values in `Z`. -/
structure ContourFn (P : Type u) [Category.{v} P] [HasZeroMorphisms P] (Z : Type*)
    [AddCommGroup Z] where
  /-- The value on a pair of parallel paths. -/
  c : ∀ {x y : RayVert P}, Quiver.Path x y → Quiver.Path x y → Z
  trans : ∀ {x y : RayVert P} (p q r : Quiver.Path x y), pathVal p = pathVal q →
    pathVal q = pathVal r → pathVal p ≠ 0 → c p q + c q r = c p r
  left : ∀ {w x y : RayVert P} (s : Quiver.Path w x) (p q : Quiver.Path x y),
    pathVal p = pathVal q → pathVal (s.comp p) ≠ 0 → c (s.comp p) (s.comp q) = c p q
  right : ∀ {x y z : RayVert P} (p q : Quiver.Path x y) (t : Quiver.Path y z),
    pathVal p = pathVal q → pathVal (p.comp t) ≠ 0 → c (p.comp t) (q.comp t) = c p q

namespace ContourFn

variable (C : ContourFn P Z)

/-- `c = δa` on all contours. -/
def IsCoboundary (a : ∀ {x y : RayVert P}, (x ⟶ y) → Z) : Prop :=
  ∀ {x y : RayVert P} (p q : Quiver.Path x y), pathVal p = pathVal q → pathVal p ≠ 0 →
    C.c p q = pathSum a p - pathSum a q

/-- Exactness: `c` is a coboundary. -/
def Exact : Prop := ∃ a : ∀ {x y : RayVert P}, (x ⟶ y) → Z, C.IsCoboundary a

lemma c_self {x y : RayVert P} (p : Quiver.Path x y) (h0 : pathVal p ≠ 0) : C.c p p = 0 := by
  have := C.trans p p p rfl rfl h0
  exact left_eq_add.1 this.symm |>.symm ▸ (by
    have h := C.trans p p p rfl rfl h0
    rwa [add_eq_left] at h)

lemma c_symm {x y : RayVert P} (p q : Quiver.Path x y) (h : pathVal p = pathVal q)
    (h0 : pathVal p ≠ 0) : C.c q p = -C.c p q := by
  have := C.trans p q p h h.symm h0
  rw [C.c_self p h0] at this
  exact eq_neg_of_add_eq_zero_right this

section Finite

variable [LargeIndecomposable.IsFiniteRayCategory P] [Finite P]

attribute [local instance] isRayCategory_of_finiteRayCategory

/-- The measure of a contour: nonzero morphisms below its value. -/
abbrev meas {x y : RayVert P} (p : Quiver.Path x y) : ℕ :=
  (IsRayCategory.below (⟨x.out, y.out, pathVal p⟩ : RayMor P)).ncard

lemma pathSum_comp3 (a : ∀ {x y : RayVert P}, (x ⟶ y) → Z) {x b c y : RayVert P}
    (p : Quiver.Path x b) (v : Quiver.Path b c) (q : Quiver.Path c y) :
    pathSum a ((p.comp v).comp q) = pathSum a p + pathSum a v + pathSum a q := by
  rw [pathSum_comp, pathSum_comp]

/-- Interlaced pairs reduce to contours of smaller measure. -/
lemma interlaced_case (a : ∀ {x y : RayVert P}, (x ⟶ y) → Z) (n : ℕ)
    (ih : ∀ {x y : RayVert P} (p q : Quiver.Path x y), pathVal p = pathVal q → pathVal p ≠ 0 →
      meas p ≤ n → C.c p q = pathSum a p - pathSum a q)
    {x y : RayVert P} (s t : Quiver.Path x y) (h : Interlaced s t) (h0 : pathVal s ≠ 0)
    (hle : meas s ≤ n + 1) : C.c s t = pathSum a s - pathSum a t := by
  have key : ∀ (s' t' : Quiver.Path x y), Interlaced s' t' → pathVal s' = pathVal s →
      C.c s' t' = pathSum a s' - pathSum a t' := by
    intro s' t' h
    induction h with
    | rel s' t' hstep =>
      intro hv
      obtain ⟨b, c, p, v', w', q, rfl, rfl, hvw, hv0, hlen⟩ := hstep
      have hne : pathVal ((p.comp v').comp q) ≠ 0 := hv ▸ h0
      have hne' : pathVal (p.comp v') ≠ 0 := fun h' ↦ hne (by rw [pathVal_comp, h', zero_comp])
      rw [C.right _ _ q (by rw [pathVal_comp, pathVal_comp, hvw]) hne,
        C.left p v' w' hvw hne', pathSum_comp3, pathSum_comp3]
      rw [ih v' w' hvw hv0 (Nat.lt_succ_iff.1 (lt_of_lt_of_le ?_ hle))]
      · abel
      · have := below_lt_of_step p v' q (hv ▸ h0) hlen
        rwa [hv] at this
    | refl s' =>
      intro hv
      rw [C.c_self s' (hv ▸ h0), sub_self]
    | symm s' t' h ih' =>
      intro hv
      have hv' : pathVal s' = pathVal s := (interlaced_val h).trans hv
      rw [C.c_symm s' t' (interlaced_val h) (hv' ▸ h0), ih' hv']
      abel
    | trans s' u' t' h h' ih' ih'' =>
      intro hv
      have hu : pathVal u' = pathVal s := (interlaced_val h).symm.trans hv
      rw [← C.trans s' u' t' (interlaced_val h) (interlaced_val h') (hv ▸ h0), ih' hv, ih'' hu]
      abel
  exact key s t h rfl

/-- **Base case**: without essential contours every contour function vanishes. -/
theorem isCoboundary_zero_of_noEss (hP : NoEssContour (P := P)) :
    C.IsCoboundary (fun _ ↦ 0) := by
  have : ∀ n {x y : RayVert P} (p q : Quiver.Path x y), pathVal p = pathVal q →
      pathVal p ≠ 0 → meas p ≤ n → C.c p q = pathSum (fun _ ↦ (0 : Z)) p - pathSum (fun _ ↦ 0) q := by
    intro n
    induction n with
    | zero =>
      intro x y p q _ h0 hle
      unfold meas at hle
      exfalso
      have := (Set.ncard_pos (IsRayCategory.below_finite (⟨x.out, y.out, pathVal p⟩ : RayMor P)
        h0)).2 ⟨(⟨x.out, y.out, pathVal p⟩ : RayMor P), h0, IsRayCategory.le_refl _⟩
      omega
    | succ n ih =>
      intro x y p q hpq h0 hle
      exact interlaced_case C _ n ih p q (hP p q hpq h0) h0 hle
  intro x y p q hpq h0
  exact this _ p q hpq h0 le_rfl

section Red

variable {ι : Type*} {b : P} {d : ι → P} (α : ∀ i, b ⟶ d i) (hα : ∀ i, ¬IsIso (α i))

/-- Values of included paths. -/
lemma incl_val_eq {x y : RayVert (ArrowQuot α)} (p q : Quiver.Path x y)
    (hpq : pathVal p = pathVal q) (h0 : pathVal p ≠ 0) :
    pathVal ((inclQuiver α hα).mapPath p) = pathVal ((inclQuiver α hα).mapPath q) ∧
      pathVal ((inclQuiver α hα).mapPath p) ≠ 0 := by
  have hp := pathVal_inclQuiver α hα p
  have hq := pathVal_inclQuiver α hα q
  have hm : ¬(arrowIdeal α).mem (pathVal ((inclQuiver α hα).mapPath p)) := by
    rw [← (arrowIdeal α).functor_map_ne_zero_iff, hp]
    exact h0
  exact ⟨quotF_map_injective α hm (hp.trans (hpq.trans hq.symm)), fun h ↦ hm (Or.inl h)⟩

lemma incl_val_ne_zero {x y : RayVert (ArrowQuot α)} (p : Quiver.Path x y) (h0 : pathVal p ≠ 0) :
    pathVal ((inclQuiver α hα).mapPath p) ≠ 0 :=
  (incl_val_eq α hα p p rfl h0).2

/-- The restriction of a contour function to `P/⟨αᵢ⟩`. -/
def restrict : ContourFn (ArrowQuot α) Z where
  c p q := C.c ((inclQuiver α hα).mapPath p) ((inclQuiver α hα).mapPath q)
  trans p q r hpq hqr h0 := by
    obtain ⟨h1, h0'⟩ := incl_val_eq α hα p q hpq h0
    obtain ⟨h2, -⟩ := incl_val_eq α hα q r hqr (hpq ▸ h0)
    exact C.trans _ _ _ h1 h2 h0'
  left s p q hpq h0 := by
    have hp0 : pathVal p ≠ 0 := fun h ↦ h0 (by rw [pathVal_comp, h, comp_zero])
    rw [Prefunctor.mapPath_comp, Prefunctor.mapPath_comp]
    refine C.left _ _ _ (incl_val_eq α hα p q hpq hp0).1 ?_
    rw [← Prefunctor.mapPath_comp]
    exact incl_val_ne_zero α hα _ h0
  right p q t hpq h0 := by
    have hp0 : pathVal p ≠ 0 := fun h ↦ h0 (by rw [pathVal_comp, h, zero_comp])
    rw [Prefunctor.mapPath_comp, Prefunctor.mapPath_comp]
    refine C.right _ _ _ (incl_val_eq α hα p q hpq hp0).1 ?_
    rw [← Prefunctor.mapPath_comp]
    exact incl_val_ne_zero α hα _ h0

variable {α hα}

/-- The value assigned to `αᵢ`: `c(αᵢuᵢ, u) − a'(uᵢ) + a'(u)`. -/
def aAlpha (D : RedData α) (a' : ∀ {x y : RayVert (ArrowQuot α)}, (x ⟶ y) → Z) (i : ι) : Z :=
  C.c ((Quiver.Path.nil.cons (D.a i)).comp (D.us i)) D.u -
    pathSum a' (toQ α hα (D.us i) (D.avoids_us i)) + pathSum a' (toQ α hα D.u D.hu)

open Classical in
/-- The arrow function on `P` extending `a'`. -/
def extA (D : RedData α) (a' : ∀ {x y : RayVert (ArrowQuot α)}, (x ⟶ y) → Z) {x y : RayVert P}
    (e : x ⟶ y) : Z :=
  if h : (arrowIdeal α).mem e.1 then C.aAlpha (hα := hα) D a' (eq_alpha_of_mem α hα e.2 h).choose
  else a' (qArr α hα e h)

lemma extA_of_not_mem (D : RedData α) (a' : ∀ {x y : RayVert (ArrowQuot α)}, (x ⟶ y) → Z)
    {x y : RayVert P} (e : x ⟶ y) (h : ¬(arrowIdeal α).mem e.1) :
    C.extA (hα := hα) D a' e = a' (qArr α hα e h) := dif_neg h

lemma extA_a (D : RedData α) (a' : ∀ {x y : RayVert (ArrowQuot α)}, (x ⟶ y) → Z) (i : ι) :
    C.extA (hα := hα) D a' (D.a i) = C.aAlpha (hα := hα) D a' i := by
  have hm : (arrowIdeal α).mem (D.a i).1 := Or.inr ⟨i, 𝟙 b, 𝟙 (d i), by rw [D.a_val]; simp⟩
  rw [extA, dif_pos hm]
  congr 1
  obtain ⟨hx, hy, he⟩ := (eq_alpha_of_mem α hα (D.a i).2 hm).choose_spec
  have h2 := (D.a_val i).symm.trans he
  refine D.a_inj _ _ hy.symm ?_
  rw [h2]
  simp

lemma pathSum_extA (D : RedData α) (a' : ∀ {x y : RayVert (ArrowQuot α)}, (x ⟶ y) → Z)
    {x : RayVert P} : ∀ {y : RayVert P} (p : Quiver.Path x y) (h : Avoids α p),
    pathSum (C.extA (hα := hα) D a') p = pathSum a' (toQ α hα p h)
  | _, .nil, _ => rfl
  | _, .cons p e, h => by
    have := pathSum_extA D a' p h.1
    change pathSum _ p + C.extA (hα := hα) D a' e =
      pathSum a' (toQ α hα p h.1) + a' (qArr α hα e h.2)
    rw [this, extA_of_not_mem]

/-- Contours whose value is not killed. -/
lemma coboundary_not_mem (D : RedData α) (a' : ∀ {x y : RayVert (ArrowQuot α)}, (x ⟶ y) → Z)
    (ha' : (C.restrict α hα).IsCoboundary a') {x y : RayVert P} (s t : Quiver.Path x y)
    (hst : pathVal s = pathVal t) (hm : ¬(arrowIdeal α).mem (pathVal s)) :
    C.c s t = pathSum (C.extA (hα := hα) D a') s - pathSum (C.extA (hα := hα) D a') t := by
  have hs := avoids_of_not_mem α s hm
  have ht := avoids_of_not_mem α t (hst ▸ hm)
  have h1 : C.c s t = (C.restrict α hα).c (toQ α hα s hs) (toQ α hα t ht) := by
    change _ = C.c ((inclQuiver α hα).mapPath _) ((inclQuiver α hα).mapPath _)
    rw [incl_toQ, incl_toQ]
    rfl
  rw [h1, ha' _ _ (by rw [pathVal_toQ, pathVal_toQ, hst]) (by
      rw [pathVal_toQ]; exact ((arrowIdeal α).functor_map_ne_zero_iff _).2 hm),
    C.pathSum_extA D a' s hs, C.pathSum_extA D a' t ht]

/-- **The reduction step of Roiter's theorem.** -/
theorem isCoboundary_of_red (D : RedData α) (hE : D.EssHypVal)
    (a' : ∀ {x y : RayVert (ArrowQuot α)}, (x ⟶ y) → Z) (ha' : (C.restrict α hα).IsCoboundary a') :
    C.IsCoboundary (C.extA (hα := hα) D a') := by
  have main : ∀ n {x y : RayVert P} (s t : Quiver.Path x y), pathVal s = pathVal t →
      pathVal s ≠ 0 → meas s ≤ n →
        C.c s t = pathSum (C.extA (hα := hα) D a') s - pathSum (C.extA (hα := hα) D a') t := by
    intro n
    induction n with
    | zero =>
      intro x y s t _ h0 hle
      unfold meas at hle
      exfalso
      have := (Set.ncard_pos (IsRayCategory.below_finite (⟨x.out, y.out, pathVal s⟩ : RayMor P)
        h0)).2 ⟨(⟨x.out, y.out, pathVal s⟩ : RayMor P), h0, IsRayCategory.le_refl _⟩
      omega
    | succ n ih =>
      intro x y s t hst h0 hle
      by_cases hm : (arrowIdeal α).mem (pathVal s)
      · by_cases hi : Interlaced s t
        · exact interlaced_case C _ n ih s t hi h0 hle
        · have hx := hE.1 s t hst h0 hm hi
          subst hx
          obtain ⟨s₁, gs, gt⟩ := hE.2 s t hst h0 hm hi
          -- the value of `r s₁` is `ū`
          have hgood : ∀ r : Quiver.Path x y, pathVal r = pathVal s → D.GoodVal r s₁ →
              pathVal (r.comp s₁) = pathVal D.u ∧
                C.c (r.comp s₁) D.u = pathSum (C.extA (hα := hα) D a') (r.comp s₁) -
                  pathSum (C.extA (hα := hα) D a') D.u := by
            intro r hr g
            rcases g with ⟨i, r₀, rfl, hv⟩ | ⟨hl, hint⟩
            · have hval : pathVal (((Quiver.Path.nil.cons (D.a i)).comp r₀).comp s₁) =
                  pathVal D.u := by
                rw [Quiver.Path.comp_assoc, pathVal_comp, hv]
                change (𝟙 _ ≫ (D.a i).1) ≫ _ = _
                rw [Category.id_comp, D.a_val, D.hcomp]
              refine ⟨hval, ?_⟩
              have hu0 := D.hu0
              have hmid : pathVal ((Quiver.Path.nil.cons (D.a i)).comp (D.us i)) = pathVal D.u := by
                rw [pathVal_comp]
                change (𝟙 _ ≫ (D.a i).1) ≫ _ = _
                rw [Category.id_comp, D.a_val, D.hcomp]
              rw [← C.trans _ ((Quiver.Path.nil.cons (D.a i)).comp (D.us i)) D.u
                  (hval.trans hmid.symm) hmid (hval ▸ hu0), Quiver.Path.comp_assoc,
                C.left _ _ _ hv (by rw [← Quiver.Path.comp_assoc, hval]; exact hu0)]
              have hus := D.hus i
              rw [C.coboundary_not_mem D a' ha' _ _ hv (hv ▸ hus)]
              rw [pathSum_comp, pathSum_comp, C.pathSum_extA D a' (D.us i) (D.avoids_us i),
                C.pathSum_extA D a' D.u D.hu]
              have hfst : pathSum (C.extA (hα := hα) D a') (Quiver.Path.nil.cons (D.a i)) =
                  C.c ((Quiver.Path.nil.cons (D.a i)).comp (D.us i)) D.u -
                    pathSum a' (toQ α hα (D.us i) (D.avoids_us i)) +
                      pathSum a' (toQ α hα D.u D.hu) := by
                change 0 + C.extA (hα := hα) D a' (D.a i) = _
                rw [zero_add]
                exact C.extA_a D a' i
              rw [hfst]
              try rw [pathSum_comp]
              abel
            · have hy := Quiver.Path.eq_of_length_zero s₁ hl
              subst hy
              have hn := Quiver.Path.eq_nil_of_length_zero s₁ hl
              subst hn
              simp only [Quiver.Path.comp_nil] at hint ⊢
              refine ⟨interlaced_val hint, ?_⟩
              exact interlaced_case C _ n ih r D.u hint (hr ▸ h0) (by
                unfold meas at hle ⊢; rw [hr]; exact hle)
          obtain ⟨hvs, hcs⟩ := hgood s rfl gs
          obtain ⟨hvt, hct⟩ := hgood t hst.symm gt
          have hne : pathVal (s.comp s₁) ≠ 0 := hvs ▸ D.hu0
          rw [← C.right s t s₁ hst hne, ← C.trans _ D.u _ hvs hvt.symm hne,
            C.c_symm _ _ hvt (hvt ▸ D.hu0), hcs, hct, pathSum_comp, pathSum_comp]
          abel
      · exact C.coboundary_not_mem D a' ha' s t hst hm
  intro x y s t hst h0
  exact main _ s t hst h0 le_rfl

end Red

end Finite

/-! ### The opposite category -/

/-- A contour function, transported to `Pᵒᵖ`. -/
def op : ContourFn Pᵒᵖ Z where
  c p q := C.c (unrevPath p) (unrevPath q)
  trans p q r hpq hqr h0 := C.trans _ _ _ (by rw [pathVal_unrevPath, pathVal_unrevPath, hpq])
    (by rw [pathVal_unrevPath, pathVal_unrevPath, hqr])
    (by rw [pathVal_unrevPath]; exact fun h ↦ h0 (Quiver.Hom.unop_inj (by rw [h, unop_zero])))
  left s p q hpq h0 := by
    rw [unrevPath_comp, unrevPath_comp]
    refine C.right _ _ _ (by rw [pathVal_unrevPath, pathVal_unrevPath, hpq]) ?_
    rw [← unrevPath_comp, pathVal_unrevPath]
    exact fun h ↦ h0 (Quiver.Hom.unop_inj (by rw [h, unop_zero]))
  right p q t hpq h0 := by
    rw [unrevPath_comp, unrevPath_comp]
    refine C.left _ _ _ (by rw [pathVal_unrevPath, pathVal_unrevPath, hpq]) ?_
    rw [← unrevPath_comp, pathVal_unrevPath]
    exact fun h ↦ h0 (Quiver.Hom.unop_inj (by rw [h, unop_zero]))

lemma pathSum_revPath (a : ∀ {x y : RayVert Pᵒᵖ}, (x ⟶ y) → Z) {x : RayVert P} :
    ∀ {y : RayVert P} (p : Quiver.Path x y),
    pathSum a (revPath p) = pathSum (fun e ↦ a (revArr e)) p
  | _, .nil => rfl
  | _, .cons p e => by
    change pathSum a ((revArr e).toPath.comp (revPath p)) = pathSum _ p + a (revArr e)
    rw [pathSum_comp, pathSum_revPath a p]
    change (0 + a (revArr e)) + _ = _
    abel

/-- Exactness on `Pᵒᵖ` gives exactness on `P`. -/
lemma exact_of_op (h : C.op.Exact) : C.Exact := by
  obtain ⟨a, ha⟩ := h
  refine ⟨fun e ↦ a (revArr e), fun {x y} p q hpq h0 ↦ ?_⟩
  have := ha (revPath p) (revPath q) (by rw [pathVal_revPath, pathVal_revPath, hpq]) (by
    rw [pathVal_revPath]; exact fun h ↦ h0 (Quiver.Hom.op_inj (by rw [h, op_zero])))
  change C.c (unrevPath (revPath p)) (unrevPath (revPath q)) = _ at this
  rw [unrevPath_revPath, unrevPath_revPath, pathSum_revPath, pathSum_revPath] at this
  exact this

end ContourFn

/-! ### The iteration -/

attribute [local instance] isRayCategory_of_finiteRayCategory in
/-- **Roiter's vanishing theorem** for finite chain-bounded ray categories with
cancellation: every contour function is exact. -/
theorem ContourFn.exact_of_chainBounded (Z : Type*) [AddCommGroup Z] :
    ∀ (n : ℕ) (Q : Type u) [Category.{v} Q] [HasZeroMorphisms Q]
      [LargeIndecomposable.IsFiniteRayCategory Q] [Finite Q], LeftCancel Q → RightCancel Q →
      ChainBounded Q → arrowCount Q ≤ n → ∀ C : ContourFn Q Z, C.Exact := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q _ _ _ _ hL hR hCB hn C
  by_cases hess : NoEssContour (P := Q)
  · exact ⟨fun _ ↦ 0, C.isCoboundary_zero_of_noEss hess⟩
  · simp only [NoEssContour, not_forall] at hess
    obtain ⟨x, y, s, t, hst, h0, hi⟩ := hess
    rcases hasRedData_or_op hL hR hCB s t hst h0 hi with
      ⟨b, ι, d, α, hα, D, -, hV, hι⟩ | ⟨b, ι, d, α, hα, D, -, hV, hι⟩
    · have := (arrowIdeal α).quotientIsFiniteRayCategory (arrowIdeal_isProper α hα)
      have hlt := arrowCount_quot_lt α hα D hι
      obtain ⟨a', ha'⟩ := ih (arrowCount (ArrowQuot α)) (by omega) (ArrowQuot α)
        (leftCancel_quot α hL) (rightCancel_quot α hR) (chainBounded_quot α hCB) le_rfl
        (C.restrict α hα)
      exact ⟨_, C.isCoboundary_of_red D hV a' ha'⟩
    · have := (arrowIdeal α).quotientIsFiniteRayCategory (arrowIdeal_isProper α hα)
      have hlt := arrowCount_quot_lt α hα D hι
      rw [arrowCount_op] at hlt
      obtain ⟨a', ha'⟩ := ih (arrowCount (ArrowQuot α)) (by omega) (ArrowQuot α)
        (leftCancel_quot α (leftCancel_op hR)) (rightCancel_quot α (rightCancel_op hL))
        (chainBounded_quot α (chainBounded_op hCB)) le_rfl (C.op.restrict α hα)
      exact C.exact_of_op ⟨_, C.op.isCoboundary_of_red D hV a' ha'⟩

end RayCat

end LargeIndecomposable
