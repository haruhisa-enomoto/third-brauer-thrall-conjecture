module

public import LargeIndecomposable.RayCategories.Linearization.Twisted
public import LargeIndecomposable.RayCategories.RoiterVanishing.Roiter

/-!
# Twists from contour functions

Words of `Q_P` (lists of arrows) give paths of the quiver of `P`
(`RayQuiver.toQPath`). A contour function with values in `Additive kˣ` gives a
twist of the linearization (`RayQuiver.twistOf`), and exact contour functions
give exact twists. With Roiter's theorem, a twisted linearization of a
chain-bounded ray category with cancellation is the linearization
(`RayQuiver.twistedLinEquiv_of_chainBounded`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits FinQuiver RayCat

namespace RayQuiver

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P]

/-- The arrow of the quiver of `P` given by an arrow of `Q_P`. -/
def qArrOf (e : (quiver P).A) : RayVert.mk e.1 ⟶ RayVert.mk e.2.1 := ⟨e.2.2.1, e.2.2.2⟩

/-- The path of the quiver of `P` given by a word of `Q_P`. -/
def toQPath : ∀ (l : List (quiver P).A) (x y : P), PathFrom (D := quiver P) x l y →
    Quiver.Path (RayVert.mk x) (RayVert.mk y)
  | [], x, _, h => Quiver.Path.cast rfl (congrArg RayVert.mk (h : x = _)) Quiver.Path.nil
  | e :: l, _, y, h => Quiver.Path.cast (congrArg RayVert.mk h.1) rfl
      ((qArrOf e).toPath.comp (toQPath l e.2.1 y h.2))

lemma pathVal_toQPath : ∀ (l : List (quiver P).A) (x y : P) (h : PathFrom (D := quiver P) x l y),
    pathVal (toQPath l x y h) = pathMor l x y h
  | [], x, y, h => by
    change x = y at h
    subst h
    rfl
  | e :: l, x, y, h => by
    obtain ⟨h1, h2⟩ := h
    change e.1 = x at h1
    subst h1
    change pathVal ((qArrOf e).toPath.comp (toQPath l e.2.1 y h2)) = eqToHom rfl ≫ e.2.2.1 ≫ _
    rw [pathVal_comp, pathVal_toPath, pathVal_toQPath l, eqToHom_refl, Category.id_comp]
    rfl

variable {Z : Type*} [AddCommGroup Z]

lemma pathSum_toQPath (a : ∀ {x y : RayVert P}, (x ⟶ y) → Z) :
    ∀ (l : List (quiver P).A) (x y : P) (h : PathFrom (D := quiver P) x l y),
      pathSum a (toQPath l x y h) = (l.map fun e ↦ a (qArrOf e)).sum
  | [], x, y, h => by
    change x = y at h
    subst h
    rfl
  | e :: l, x, y, h => by
    obtain ⟨h1, h2⟩ := h
    change e.1 = x at h1
    subst h1
    change pathSum a ((qArrOf e).toPath.comp (toQPath l e.2.1 y h2)) = _
    rw [pathSum_comp, pathSum_toQPath a l, List.map_cons, List.sum_cons]
    change 0 + a (qArrOf e) + _ = _
    rw [zero_add]

variable (k : Type*) [Field k]

/-- The twist given by a contour function with values in `Additive kˣ`. -/
def twistOf (C : ContourFn P (Additive kˣ)) : TwistFn P k :=
  fun l l' x y h h' ↦ Additive.toMul (C.c (toQPath l x y h) (toQPath l' x y h'))

/-- Exact contour functions give exact twists. -/
lemma isExactTwist_of_isCoboundary (C : ContourFn P (Additive kˣ))
    (a : ∀ {x y : RayVert P}, (x ⟶ y) → Additive kˣ) (ha : C.IsCoboundary a) :
    IsExactTwist (twistOf k C) (fun e ↦ Additive.toMul (a (qArrOf e))) := by
  intro l l' x y h h' he hne
  have := ha (toQPath l x y h) (toQPath l' x y h')
    (by rw [pathVal_toQPath, pathVal_toQPath, he]) (by rw [pathVal_toQPath]; exact hne)
  rw [twistOf, this, pathSum_toQPath, pathSum_toQPath, toMul_sub, wordProd, wordProd]
  congr 1 <;> · rw [toMul_list_sum, List.map_map]; rfl

/-- **Standardness from a twist** (chain-bounded case): a twisted linearization
of a finite chain-bounded ray category with cancellation is the
linearization (Roiter's theorem and rescaling of the arrows). -/
theorem twistedLinEquiv_of_chainBounded [LargeIndecomposable.IsFiniteRayCategory P]
    (hL : LeftCancel P) (hR : RightCancel P) (hCB : ChainBounded P)
    (C : ContourFn P (Additive kˣ)) :
    Nonempty (TwistedLin P k (twistOf k C) ≃ₐ[k] Linearization P k) := by
  obtain ⟨a, ha⟩ := ContourFn.exact_of_chainBounded (Additive kˣ) _ P hL hR hCB le_rfl C
  exact ⟨twistedLinEquiv (isExactTwist_of_isCoboundary k C a ha)⟩

/-- The same with exactness given directly. -/
theorem twistedLinEquiv_of_exact (C : ContourFn P (Additive kˣ)) (hC : C.Exact) :
    Nonempty (TwistedLin P k (twistOf k C) ≃ₐ[k] Linearization P k) := by
  obtain ⟨a, ha⟩ := hC
  exact ⟨twistedLinEquiv (isExactTwist_of_isCoboundary k C a ha)⟩

end RayQuiver

end LargeIndecomposable
