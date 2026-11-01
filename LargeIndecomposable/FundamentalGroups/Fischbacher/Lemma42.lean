module

public import LargeIndecomposable.RayCategories.Basic.Exhaust
public import LargeIndecomposable.RayCategories.RoiterVanishing.KeyLemma

/-!
# Fischbacher's Lemma 4.2: parallel paths have the same value

In an interval-finite ray category without oriented cycles in which every cocycle on a finite
convex set is a coboundary there, two paths with the same endpoints have the same value
(`pathVal_eq_of_parallel`; Fischbacher, *Zur Kombinatorik der Algebren mit endlich vielen
Idealen*, Lemma 4.2, "insbesondere"). Induction on the interval `[a, b]`: the last arrows of
the two paths lie in one component of the morphisms into `b` (`sepComp_of_coboundary`), and
along such a component the value of "a path from `a`, then the morphism" is constant by
induction.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

universe v u

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [IsRayCategory A]

/-- The interval `[a, b]`. -/
def interval (a b : A) : Set A := {z | Reaches a z ∧ Reaches z b}

lemma convexR_interval (a b : A) : ConvexR (interval a b) :=
  fun _ hx _ hy _ hxz hzy ↦ ⟨hx.1.trans hxz, hzy.trans hy.2⟩

/-- A walk inside `D \ {b}` from a path inside it. -/
lemma eqvGen_adjOff_of_path {D : Set A} {b : A} {x : RayVert A} :
    ∀ {y : RayVert A} (p : Quiver.Path x y), PathIn (D \ {b}) p →
      Relation.EqvGen (AdjOff D b) x.out y.out
  | _, .nil, _ => Relation.EqvGen.refl _
  | _, .cons (b := y') p e, h => by
    refine (eqvGen_adjOff_of_path p h.1).trans _ _ _ (Relation.EqvGen.rel _ _ ?_)
    have h1 := PathIn.target h.1
    exact ⟨h1.1, h.2.1, h1.2, h.2.2, Or.inl ⟨e⟩⟩

variable (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)), p.length = 0)
include hcf

lemma eq_of_reaches_both {x y : A} (h₁ : Reaches x y) (h₂ : Reaches y x) : x = y := by
  have := eq_of_reaches_cycle (H := Set.univ) (fun z _ ↦ hcf z) (Set.mem_univ x) h₁ h₂
  exact this.symm

/-- **Fischbacher's Lemma 4.2** (values): parallel paths have the same value. -/
theorem pathVal_eq_of_parallel (hint : ∀ a b : A, (interval a b).Finite)
    (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
      IsCoboundaryOn D c) :
    ∀ n : ℕ, ∀ a b : A, (interval a b).ncard = n →
      ∀ v w : Quiver.Path (RayVert.mk a) (RayVert.mk b), pathVal v = pathVal w := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn v w
  by_cases hab : a = b
  · subst hab
    rw [Quiver.Path.eq_nil_of_length_zero v (hcf a v),
      Quiver.Path.eq_nil_of_length_zero w (hcf a w)]
  -- the interval and its properties
  set D := interval a b with hDdef
  have hDfin := hint a b
  have hDconv := convexR_interval a b
  have hbD : b ∈ D := ⟨⟨v⟩, Reaches.refl b⟩
  have hmax : ∀ {y : RayVert A} (_ : RayVert.mk b ⟶ y), y.out ∉ D := by
    intro y e hy
    obtain ⟨q⟩ := hy.2
    have := hcf b (e.toPath.comp q)
    rw [Quiver.Path.length_comp] at this
    simp at this
  have hDb : ConvexR (D \ {b}) := by
    rintro x ⟨hx, -⟩ y ⟨hy, hyb⟩ z hxz hzy
    refine ⟨hDconv _ hx _ hy _ hxz hzy, fun hz ↦ hyb ?_⟩
    rw [Set.mem_singleton_iff] at hz
    rw [hz] at hzy
    exact eq_of_reaches_both hcf hy.2 hzy
  -- smaller intervals
  let good : (Σ x : A, x ⟶ b) → Prop := fun g ↦ g.2 ≠ 0 ∧ g.1 ∈ D ∧ g.1 ≠ b
  have hsmall : ∀ g, good g → ∀ p q : Quiver.Path (RayVert.mk a) (RayVert.mk g.1),
      pathVal p = pathVal q := by
    intro g hg p q
    have hsub : interval a g.1 ⊂ D := by
      refine ⟨fun z hz ↦ ⟨hz.1, hz.2.trans hg.2.1.2⟩, fun h ↦ hg.2.2 ?_⟩
      have := h hbD
      exact eq_of_reaches_both hcf hg.2.1.2 this.2
    exact ih _ (hn ▸ Set.ncard_lt_ncard hsub hDfin) a g.1 rfl p q
  -- the last arrows
  rcases v with _ | ⟨v', ev⟩
  · exact absurd rfl hab
  rcases w with _ | ⟨w', ew⟩
  · exact absurd rfl hab
  rename_i cv cw
  have hne : ∀ {c : RayVert A} (e : c ⟶ RayVert.mk b), c.out ≠ b := by
    intro c e h
    obtain rfl : RayVert.mk b = c := h.symm
    have := hcf b e.toPath
    simp at this
  have haD : a ∈ D \ {b} := ⟨⟨Reaches.refl a, ⟨v'.cons ev⟩⟩, hab⟩
  have hcvD : cv.out ∈ D := ⟨⟨v'⟩, ⟨ev.toPath⟩⟩
  have hcwD : cw.out ∈ D := ⟨⟨w'⟩, ⟨ew.toPath⟩⟩
  have hv'in : PathIn (D \ {b}) v' := pathConvex_of_convexR hDb v' haD ⟨hcvD, hne ev⟩
  have hw'in : PathIn (D \ {b}) w' := pathConvex_of_convexR hDb w' haD ⟨hcwD, hne ew⟩
  have hconn : Relation.EqvGen (AdjOff D b) cv.out cw.out :=
    (eqvGen_adjOff_of_path v' hv'in).symm.trans _ _ _ (eqvGen_adjOff_of_path w' hw'in)
  have hsep := sepComp_of_coboundary hbD hmax (hsc D hDfin hDconv) ev ew hcvD hcwD
    (hne ev) (hne ew) hconn
  unfold SepComp at hsep
  rw [← Relation.EqvGen.reflTransGen_symmGen] at hsep
  let f₀ : Σ x : A, x ⟶ b := ⟨cv.out, ev.1⟩
  have key : ∀ g, Relation.ReflTransGen (Relation.SymmGen (SepLe D b)) f₀ g → good g ∧
      ∀ (p : Quiver.Path (RayVert.mk a) (RayVert.mk f₀.1))
        (q : Quiver.Path (RayVert.mk a) (RayVert.mk g.1)), pathVal p ≫ f₀.2 = pathVal q ≫ g.2 := by
    intro g hg
    induction hg with
    | refl =>
      have hgood : good f₀ := ⟨ev.2.1, hcvD, hne ev⟩
      exact ⟨hgood, fun p q ↦ by rw [hsmall f₀ hgood p q]⟩
    | @tail g h _ hgh ih =>
      obtain ⟨hgood, hval⟩ := ih
      rcases hgh with ⟨-, hh0, -, hhD, -, hhb, k, hk⟩ | ⟨hh0, -, hhD, -, hhb, -, k, hk⟩
      · refine ⟨⟨hh0, hhD, hhb⟩, fun p q' ↦ ?_⟩
        obtain ⟨q⟩ := hgood.2.1.1
        have hk0 : k ≠ 0 := fun h0 ↦ hh0 (by rw [hk, h0, zero_comp])
        have e1 := hsmall g hgood (q'.comp (pathOf (P := A) k hk0)) q
        have hpo : pathVal (pathOf (P := A) k hk0) = k := pathVal_pathOf (P := A) k hk0
        rw [pathVal_comp, hpo] at e1
        rw [hval p q, ← e1, Category.assoc, ← hk]
      · refine ⟨⟨hh0, hhD, hhb⟩, fun p q' ↦ ?_⟩
        obtain ⟨q⟩ := hgood.2.1.1
        have hk0 : k ≠ 0 := fun h0 ↦ hgood.1 (by rw [hk, h0, zero_comp])
        have e1 := hsmall h ⟨hh0, hhD, hhb⟩ (q.comp (pathOf (P := A) k hk0)) q'
        have hpo : pathVal (pathOf (P := A) k hk0) = k := pathVal_pathOf (P := A) k hk0
        rw [pathVal_comp, hpo] at e1
        rw [hval p q, hk, ← e1, Category.assoc]
  exact (key _ hsep).2 v' w'

end LargeIndecomposable.RayCat
