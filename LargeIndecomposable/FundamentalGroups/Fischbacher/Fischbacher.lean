module

public import LargeIndecomposable.FundamentalGroups.Fischbacher.Selection
public import LargeIndecomposable.FundamentalGroups.Fischbacher.KillingArrows

/-!
# Fischbacher's reduction lemma (Lemma 2.1)

From the selection (`RayCat.exists_selection`) and the key lemma in the form
(K') — an arrow `γ ≰ τ` from `b` occurs in essential contours only as the first
arrow — we build the data `RedData` and the hypothesis `EssHyp` of Lemma 2.2
(`RayCat.exists_redData`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe v u

namespace RayCat

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P]
  [LargeIndecomposable.IsFiniteRayCategory0 P] [Finite P]

attribute [local instance] isRayCategory_of_finiteRayCategory

section QLemmas

variable {ι : Type*} {b : P} {d : ι → P} (α : ∀ i, b ⟶ d i) (hα : ∀ i, ¬IsIso (α i))

omit [Finite P] in
lemma toQ_comp {x y : RayVert P} (p : Quiver.Path x y) : ∀ {z : RayVert P}
    (q : Quiver.Path y z) (h : Avoids α (p.comp q)) (hp : Avoids α p) (hq : Avoids α q),
    toQ α hα (p.comp q) h = (toQ α hα p hp).comp (toQ α hα q hq)
  | _, .nil, _, _, _ => rfl
  | _, .cons q e, h, hp, hq => by
    change Quiver.Path.cons (toQ α hα (p.comp q) h.1) (qArr α hα e h.2) = _
    rw [toQ_comp p q h.1 hp hq.1]
    rfl

omit [Finite P] in
lemma clsQ_comp {x y z : RayVert P} (p : Quiver.Path x y) (q : Quiver.Path y z)
    (h : Avoids α (p.comp q)) (hp : Avoids α p) (hq : Avoids α q) :
    clsQ α hα (p.comp q) h = clsQ α hα p hp ≫ clsQ α hα q hq := by
  change (CategoryTheory.Quotient.functor homotopy).map (pathFG (toQ α hα (p.comp q) h)) = _
  rw [toQ_comp α hα p q h hp hq, pathFG_comp, Functor.map_comp]

omit [Finite P] in
lemma clsQ_nil {x : RayVert P} (h : Avoids α (Quiver.Path.nil : Quiver.Path x x)) :
    clsQ α hα Quiver.Path.nil h = 𝟙 _ :=
  (CategoryTheory.Quotient.functor _).map_id _

omit [Finite P] in
/-- Avoiding paths with the same value outside the ideal have the same class. -/
lemma clsQ_eq_of_val {x y : RayVert P} (p q : Quiver.Path x y) (hp : Avoids α p)
    (hq : Avoids α q) (hv : pathVal p = pathVal q) (hn : ¬(arrowIdeal α).mem (pathVal p)) :
    clsQ α hα p hp = clsQ α hα q hq := by
  refine CategoryTheory.Quotient.sound _ (homotopy.path _ _ ?_ ?_)
  · rw [pathVal_toQ, pathVal_toQ, hv]
  · rw [pathVal_toQ]
    exact ((arrowIdeal α).functor_map_ne_zero_iff _).2 hn

omit [LargeIndecomposable.IsFiniteRayCategory0 P] [Finite P] in
/-- A path avoids the ideal if none of its arrows lies in it. -/
lemma avoids_of_forall {x : RayVert P} : ∀ {y : RayVert P} (v : Quiver.Path x y),
    (∀ {a c : RayVert P} (p : Quiver.Path x a) (e : a ⟶ c) (q : Quiver.Path c y),
      v = (p.cons e).comp q → ¬(arrowIdeal α).mem e.1) → Avoids α v
  | _, .nil, _ => trivial
  | _, .cons v e, h => ⟨avoids_of_forall v fun p e' q hv ↦ h p e' (q.cons e) (by rw [hv]; rfl),
      h v e .nil rfl⟩

omit [LargeIndecomposable.IsFiniteRayCategory0 P] [Finite P] in
lemma avoids_of_length_zero {x y : RayVert P} (p : Quiver.Path x y) (h : p.length = 0) :
    Avoids α p := by
  cases p with
  | nil => trivial
  | cons p e => simp at h

end QLemmas

namespace RedData

variable {ι : Type*} {b : P} {d : ι → P} {α : ∀ i, b ⟶ d i} (hα : ∀ i, ¬IsIso (α i))
  (D : RedData α)

/-- The value-level form of `Good'`: `s = aᵢ s₀` with `s̄₀ s̄₁ = ūᵢ`, or `s s₁`
interlaced with `u` and `s₁` trivial. -/
def GoodVal {y : RayVert P} (s : Quiver.Path (RayVert.mk b) y)
    (s₁ : Quiver.Path y (RayVert.mk D.c)) : Prop :=
  (∃ (i : ι) (s₀ : Quiver.Path (RayVert.mk (d i)) y),
      s = (Quiver.Path.nil.cons (D.a i)).comp s₀ ∧ pathVal (s₀.comp s₁) = pathVal (D.us i)) ∨
    (s₁.length = 0 ∧ Interlaced (s.comp s₁) D.u)

/-- The value-level form of `EssHyp`. -/
def EssHypVal : Prop :=
  (∀ {x y : RayVert P} (s t : Quiver.Path x y), pathVal s = pathVal t → pathVal s ≠ 0 →
      (arrowIdeal α).mem (pathVal s) → ¬Interlaced s t → x = RayVert.mk b) ∧
    ∀ {y : RayVert P} (s t : Quiver.Path (RayVert.mk b) y), pathVal s = pathVal t →
      pathVal s ≠ 0 → (arrowIdeal α).mem (pathVal s) → ¬Interlaced s t →
        ∃ s₁ : Quiver.Path y (RayVert.mk D.c), D.GoodVal s s₁ ∧ D.GoodVal t s₁

include hα in
lemma essHyp_of_essHypVal (h : D.EssHypVal) : D.EssHyp (hα := hα) := by
  refine ⟨h.1, fun {y} s t hst h0 hm hi ↦ ?_⟩
  obtain ⟨s₁, gs, gt⟩ := h.2 s t hst h0 hm hi
  have h₁ : Avoids α s₁ := by
    by_cases hl1 : s₁.length = 0
    · exact avoids_of_length_zero α s₁ hl1
    · rcases gs with ⟨j, r₀, -, hv⟩ | ⟨hl, -⟩
      · exact ((avoids_comp α r₀ s₁).1 (avoids_of_not_mem α _ (hv ▸ D.hus j))).2
      · exact absurd hl hl1
  have hgood : ∀ r : Quiver.Path (RayVert.mk b) y, D.GoodVal r s₁ → D.Good' (hα := hα) r s₁ h₁ := by
    intro r hr
    rcases hr with ⟨j, r₀, hr0, hv⟩ | ⟨hl1, hint⟩
    · left
      left
      have hav := avoids_of_not_mem α _ (hv ▸ D.hus j)
      have hav0 := ((avoids_comp α r₀ s₁).1 hav).1
      refine ⟨j, r₀, hav0, hr0, ?_⟩
      rw [← clsQ_comp α hα r₀ s₁ hav hav0 h₁]
      exact clsQ_eq_of_val α hα _ _ hav (D.avoids_us j) hv (hv ▸ D.hus j)
    · right
      exact ⟨hl1, hint⟩
  exact ⟨s₁, h₁, hgood s gs, hgood t gt⟩

end RedData

/-- (K'): the arrows `γ ≰ τ` from `b` occur in essential contours only first. -/
def KeyProp (b : P) (τ : BMor b) : Prop :=
  ∀ γ : BMor b, IsArr γ → ¬BLe γ τ → ∀ {x y : RayVert P} (v w : Quiver.Path x y),
    pathVal v = pathVal w → pathVal v ≠ 0 → ¬Interlaced v w →
    ∀ (p : Quiver.Path x (RayVert.mk b)) (e : RayVert.mk b ⟶ RayVert.mk γ.1)
      (q : Quiver.Path (RayVert.mk γ.1) y), e.1 = γ.2 → v = (p.cons e).comp q → p.length = 0

/-- **Fischbacher's Lemma 2.1** (start version): from the selection and (K'),
the data and hypotheses of Lemma 2.2. -/
theorem exists_redData (hL : LeftCancel P) (hR : RightCancel P) (hCB : ChainBounded P)
    {b : P} {τ β ν : BMor b} (hτ0 : τ.2 ≠ 0) (hβ : IsArr β) (hβτ : ¬BLe β τ) (hν : IsEssVal ν)
    (hβν : BLe β ν) (hK : KeyProp b τ) :
    ∃ (ι : Type (max u v)) (d : ι → P) (α : ∀ i, b ⟶ d i) (hα : ∀ i, ¬IsIso (α i))
      (D : RedData α), D.EssHyp (hα := hα) ∧ D.EssHypVal ∧ Nonempty ι := by
  classical
  obtain ⟨μ, u, A, hμ0, hu, hA, hA4, hS5, α₀, hα₀⟩ :=
    exists_selection hL hR hCB hτ0 hβ hβτ hν hβν
  let ι := {γ : BMor b // A γ}
  let d : ι → P := fun i ↦ i.1.1
  let α : ∀ i, b ⟶ d i := fun i ↦ i.1.2
  have hαirr : ∀ i, IsIrreducible (α i) := fun i ↦ (hA _ i.2).1
  have hα : ∀ i, ¬IsIso (α i) := fun i ↦ (hαirr i).2.1
  let e : ∀ i, RayVert.mk b ⟶ RayVert.mk (d i) := fun i ↦ ⟨α i, hαirr i⟩
  have hK' : ∀ i {x y : RayVert P} (v w : Quiver.Path x y), pathVal v = pathVal w →
      pathVal v ≠ 0 → ¬Interlaced v w → ∀ (p : Quiver.Path x (RayVert.mk b))
      (q : Quiver.Path (RayVert.mk (d i)) y), v = (p.cons (e i)).comp q → p.length = 0 :=
    fun i _ _ v w hvw h0 hi p q hv ↦
      hK i.1 (hA _ i.2).1 (hA _ i.2).2.1 v w hvw h0 hi p (e i) q rfl hv
  -- the first arrow of `e i · r` is `i`
  have hfirst : ∀ i {z : RayVert P} (r : Quiver.Path (RayVert.mk (d i)) z),
      IsFirst ((e i).toPath.comp r) i.1 := fun i _ r ↦ ⟨e i, r, rfl, rfl⟩
  -- an essential contour whose value lies in the ideal passes through some `αᵢ` at `b`
  have hthrough : ∀ {x y : RayVert P} (s t : Quiver.Path x y), pathVal s = pathVal t →
      pathVal s ≠ 0 → ¬Interlaced s t → (arrowIdeal α).mem (pathVal s) →
      ∃ (i : ι) (a : x.out ⟶ b) (c : d i ⟶ y.out) (p : Quiver.Path x (RayVert.mk b)),
        pathVal p = a ∧ p.length = 0 ∧ pathVal s = a ≫ α i ≫ c := by
    intro x y s t hst h0 hi hm
    rcases hm with hm | ⟨i, a, c, hs⟩
    · exact absurd hm h0
    have ha : a ≠ 0 := fun h ↦ h0 (by rw [hs, h, zero_comp])
    have hc : c ≠ 0 := fun h ↦ h0 (by rw [hs, h, comp_zero, comp_zero])
    let pa := pathOf (x := x.out) (y := b) a ha
    let pc := pathOf (x := d i) (y := y.out) c hc
    let r := (pa.cons (e i)).comp pc
    have hr : pathVal r = pathVal s := by
      change pathVal ((pa.cons (e i)).comp pc) = _
      rw [pathVal_comp, hs, pathVal_pathOf]
      change (pathVal pa ≫ α i) ≫ c = _
      rw [pathVal_pathOf, Category.assoc]
    refine ⟨i, a, c, pa, pathVal_pathOf _ ha, ?_, hs⟩
    by_cases hrs : Interlaced r s
    · exact hK' i r t (hr.trans hst) (hr ▸ h0)
        (fun h ↦ hi ((Relation.EqvGen.symm _ _ hrs).trans _ _ _ h)) _ _ rfl
    · exact hK' i r s hr (hr ▸ h0) hrs _ _ rfl
  -- the paths `uᵢ`
  have hle : ∀ i : ι, ∃ ρ : d i ⟶ μ.1, α i ≫ ρ = μ.2 := fun i ↦ (hA _ i.2).2.2
  choose ρ hρ using hle
  have hρ0 : ∀ i, ρ i ≠ 0 := fun i h ↦ hμ0 (by rw [← hρ i, h, comp_zero])
  let us : ∀ i, Quiver.Path (RayVert.mk (d i)) (RayVert.mk μ.1) := fun i ↦
    pathOf (x := d i) (y := μ.1) (ρ i) (hρ0 i)
  have hus_val : ∀ i, pathVal (us i) = ρ i := fun i ↦ pathVal_pathOf _ (hρ0 i)
  -- an essential contour through `u`
  obtain ⟨w₀, hw₀, hw₀'⟩ := exists_path_first (hA α₀ hα₀).1 (hA α₀ hα₀).2.2 hμ0
  have hw₀u : ¬Interlaced w₀ u := (hS5 w₀ hw₀ α₀ hw₀').1 hα₀
  -- `u` avoids the ideal
  have hu_av : Avoids α u := by
    refine avoids_of_forall α u fun {a c} p e' q hv hm ↦ ?_
    obtain ⟨j, hx, hy, he'⟩ := eq_alpha_of_mem α hα e'.2 hm
    have hx' : a = RayVert.mk b := hx
    have hy' : c = RayVert.mk (d j) := hy
    subst hx' hy'
    have hej : e' = e j := Subtype.ext (by rw [he']; simp only [eqToHom_refl, Category.id_comp]; exact Category.comp_id _)
    subst hej
    have hp := hK' j u w₀ (hu.trans hw₀.symm) (hu ▸ hμ0) (fun h ↦ hw₀u
      (Relation.EqvGen.symm _ _ h)) p q hv
    have hpn := Quiver.Path.eq_nil_of_length_zero p hp
    subst hpn
    have hf : IsFirst u j.1 := ⟨e j, q, rfl, by rw [hv]; rfl⟩
    exact (hS5 u hu j.1 hf).1 j.2 (.refl _)
  -- `ūᵢ` is not killed
  have hus : ∀ i, ¬(arrowIdeal α).mem (pathVal (us i)) := by
    intro i hm
    rw [hus_val] at hm
    rcases hm with hm | ⟨j, a', c', hm⟩
    · exact hρ0 i hm
    have ha' : a' ≠ 0 := fun h ↦ hρ0 i (by rw [hm, h, zero_comp])
    have hc' : c' ≠ 0 := fun h ↦ hρ0 i (by rw [hm, h, comp_zero, comp_zero])
    let pa := pathOf (x := d i) (y := b) a' ha'
    let pc := pathOf (x := d j) (y := μ.1) c' hc'
    let R := (((e i).toPath.comp pa).cons (e j)).comp pc
    have hR : pathVal R = μ.2 := by
      change pathVal ((((e i).toPath.comp pa).cons (e j)).comp pc) = _
      rw [pathVal_comp, pathVal_pathOf]
      change (pathVal ((e i).toPath.comp pa) ≫ α j) ≫ c' = _
      rw [pathVal_comp, pathVal_toPath, pathVal_pathOf]
      change ((α i ≫ a') ≫ α j) ≫ c' = _
      rw [← hρ i, hm]
      simp only [Category.assoc]
    have hRf : IsFirst R i.1 := by
      have := IsFirst.comp (IsFirst.comp (hfirst i pa) (e j).toPath) pc
      exact this
    have hRu : ¬Interlaced R u := (hS5 R hR i.1 hRf).1 i.2
    have := hK' j R u (hR.trans hu.symm) (hR ▸ hμ0) hRu _ pc rfl
    simp at this
  let D : RedData α :=
    { a := e
      a_val := fun _ ↦ rfl
      a_inj := fun i i' h heq ↦ Subtype.ext (eq_of_comp_isIso (eqToHom h) heq)
      c := μ.1
      u := u
      us := us
      hu := hu_av
      hus := hus
      hcomp := fun i ↦ by rw [hus_val, hρ, hu]
      hu0 := hu ▸ hμ0 }
  suffices hval : D.EssHypVal from ⟨ι, d, α, hα, D, D.essHyp_of_essHypVal hα hval, hval, ⟨⟨α₀, hα₀⟩⟩⟩
  refine ⟨fun s t hst h0 hm hi ↦ ?_, fun {y} s t hst h0 hm hi ↦ ?_⟩
  · obtain ⟨i, a, c, p, -, hl, -⟩ := hthrough s t hst h0 hi hm
    exact Quiver.Path.eq_of_length_zero p hl
  · obtain ⟨i, a, c, p, hpa, hl, hs⟩ := hthrough s t hst h0 hi hm
    have hpn := Quiver.Path.eq_nil_of_length_zero p hl
    subst hpn
    have ha : a = 𝟙 b := hpa.symm
    subst ha
    have hs' : pathVal s = α i ≫ c := by rw [hs, Category.id_comp]
    have hess : IsEssVal (⟨y.out, pathVal s⟩ : BMor b) := ⟨s, t, rfl, hst.symm, h0, hi⟩
    obtain ⟨σ, hσ⟩ := hA4 i.1 i.2 _ hess ⟨c, hs'.symm⟩
    have hσ0 : σ ≠ 0 := fun h ↦ hμ0 (by rw [← hσ, h, comp_zero])
    let s₁ : Quiver.Path y (RayVert.mk μ.1) := pathOf (x := y.out) (y := μ.1) σ hσ0
    have hs₁ : pathVal s₁ = σ := pathVal_pathOf _ hσ0
    have hc0 : c ≠ 0 := fun h ↦ h0 (by rw [hs', h, comp_zero])
    -- the two kinds of paths of the contour
    have hcl : ∀ r : Quiver.Path (RayVert.mk b) y, pathVal r = pathVal s →
        (∃ (j : ι) (r₀ : Quiver.Path (RayVert.mk (d j)) y),
          r = (Quiver.Path.nil.cons (e j)).comp r₀ ∧ pathVal (r₀.comp s₁) = pathVal (us j)) ∨
        (s₁.length = 0 ∧ Interlaced (r.comp s₁) u) := by
      intro r hr
      have hrs : pathVal (r.comp s₁) = μ.2 := by
        change pathVal (r.comp s₁) = _
        rw [pathVal_comp, hr, hs₁, hσ]
      have hrl : 0 < r.length := by
        by_contra hl0
        have h1 : IsIso (α i ≫ c) := by
          rw [← hs', ← hr]
          exact isIso_pathVal_of_length_zero r (by omega)
        exact hα i (isIso_of_isIso_comp _ _ (hαirr i).1 h1)
      obtain ⟨γ, hγ⟩ := exists_isFirst r hrl
      have hγ' := IsFirst.comp hγ s₁
      by_cases hAγ : A γ
      · left
        obtain ⟨e', r₀, he', hr0⟩ := hγ
        have hee : e' = e ⟨γ, hAγ⟩ := Subtype.ext he'
        subst hee
        refine ⟨⟨γ, hAγ⟩, r₀, hr0, ?_⟩
        rw [hus_val]
        have hv' : pathVal (r.comp s₁) = γ.2 ≫ pathVal (r₀.comp s₁) := by
          rw [hr0, Quiver.Path.comp_assoc, pathVal_comp, pathVal_toPath]
        refine hL γ.2 _ _ ?_ ?_
        · rw [← hv', hrs, ← hρ ⟨γ, hAγ⟩]
        · rw [← hv', hrs]
          exact hμ0
      · right
        have hint : Interlaced (r.comp s₁) u := by
          by_contra h
          exact hAγ ((hS5 _ hrs γ hγ').2 h)
        refine ⟨?_, hint⟩
        by_contra hl1
        let r' := (e i).toPath.comp (pathOf (x := d i) (y := y.out) c hc0)
        have hr' : pathVal r' = pathVal r := by
          change pathVal ((e i).toPath.comp _) = _
          rw [pathVal_comp, pathVal_toPath, pathVal_pathOf, hr, hs']
        have h1 : Interlaced (r'.comp s₁) (r.comp s₁) :=
          Relation.EqvGen.rel _ _ (interStep_suffix r' r s₁ (by omega) hr'
            (by rw [hr', hr]; exact h0))
        have hf : IsFirst (r'.comp s₁) i.1 := IsFirst.comp (hfirst i _) s₁
        have hval : pathVal (r'.comp s₁) = μ.2 := by rw [pathVal_comp, hr', ← pathVal_comp, hrs]
        exact (hS5 _ hval i.1 hf).1 i.2 (h1.trans _ _ _ hint)
    exact ⟨s₁, hcl s rfl, hcl t hst.symm⟩

end RayCat

end LargeIndecomposable
