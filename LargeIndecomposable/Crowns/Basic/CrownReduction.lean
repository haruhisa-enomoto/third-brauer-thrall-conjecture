module

public import LargeIndecomposable.RayCategories.RoiterVanishing.Roiter
public import LargeIndecomposable.RayCategories.Basic.ResidueQuiver

/-!
# The crown case: reduction to `P/μ`

Let `μ` be a long morphism (maximal and not irreducible) of a finite ray
category `P` with cancellation which occurs in no contour. If `P/μ` is
chain-bounded, the fundamental group of `P` is free and every contour function
on `P` is exact (BO13a, proof of Theorem 2, with the lemma of §3.1:
`RayCategories/Basic/ResidueQuiver.lean`, Fischbacher for `Π` and Roiter for `H²`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe v u

namespace RayCat

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P]

/-! ### Quotients by ideals -/

lemma leftCancel_quotient (I : LargeIndecomposable.ZeroHomIdeal P) (hL : LeftCancel P) :
    LeftCancel (CategoryTheory.Quotient I.rel) := by
  intro x y z f g h hfg h0
  obtain ⟨f₀, rfl⟩ := (CategoryTheory.Quotient.functor I.rel).map_surjective f
  obtain ⟨g₀, rfl⟩ := (CategoryTheory.Quotient.functor I.rel).map_surjective g
  obtain ⟨h₀, rfl⟩ := (CategoryTheory.Quotient.functor I.rel).map_surjective h
  simp only [← Functor.map_comp] at hfg h0
  have hm : ¬I.mem (f₀ ≫ g₀) := (I.functor_map_ne_zero_iff _).1 h0
  rcases (CategoryTheory.Quotient.functor_map_eq_iff _ _ _).1 hfg with h1 | h1
  · exact congrArg _ (hL _ _ _ h1 fun h' ↦ hm (by rw [h']; exact I.zero_mem _ _))
  · exact absurd h1.1 hm

lemma rightCancel_quotient (I : LargeIndecomposable.ZeroHomIdeal P) (hR : RightCancel P) :
    RightCancel (CategoryTheory.Quotient I.rel) := by
  intro x y z f g h hfg h0
  obtain ⟨f₀, rfl⟩ := (CategoryTheory.Quotient.functor I.rel).map_surjective f
  obtain ⟨g₀, rfl⟩ := (CategoryTheory.Quotient.functor I.rel).map_surjective g
  obtain ⟨h₀, rfl⟩ := (CategoryTheory.Quotient.functor I.rel).map_surjective h
  simp only [← Functor.map_comp] at hfg h0
  have hm : ¬I.mem (f₀ ≫ h₀) := (I.functor_map_ne_zero_iff _).1 h0
  rcases (CategoryTheory.Quotient.functor_map_eq_iff _ _ _).1 hfg with h1 | h1
  · exact congrArg _ (hR _ _ _ h1 fun h' ↦ hm (by rw [h']; exact I.zero_mem _ _))
  · exact absurd h1.1 hm

/-- A quotient of a connected category is connected. -/
lemma isConnected_quotient {C : Type*} [Category C] (r : HomRel C) [IsConnected C] :
    IsConnected (CategoryTheory.Quotient r) := by
  obtain ⟨X₀⟩ := (inferInstance : Nonempty C)
  have : Nonempty (CategoryTheory.Quotient r) := ⟨⟨X₀⟩⟩
  refine zigzag_isConnected fun X Y ↦ ?_
  exact zigzag_obj_of_zigzag (CategoryTheory.Quotient.functor r)
    (isPreconnected_zigzag X.as Y.as)

/-! ### The fundamental group -/

section Residue

variable [LargeIndecomposable.IsFiniteRayCategory P] [Finite P] {a b : P} (μ : a ⟶ b)
  (hμ : ¬IsIso μ) (hμr : ¬IsIrreducible μ) (hμ0 : μ ≠ 0)

attribute [local instance] isRayCategory_of_finiteRayCategory

/-- The free groupoids of `P` and `P/μ` are equivalent. -/
def resFGEquiv : Quiver.FreeGroupoid (RayVert P) ≌ Quiver.FreeGroupoid (RayVert (Res μ)) :=
  CategoryTheory.Equivalence.mk (resFG μ hμ hμr hμ0) (resFGInv μ hμ hμr hμ0)
    (eqToIso (resFG_comp_inv μ hμ hμr hμ0).symm) (eqToIso (resFG_inv_comp μ hμ hμr hμ0))

include hμ hμr hμ0 in
/-- **The crown case for `Π`**: if the long morphism `μ` occurs in no contour
and `P/μ` is chain-bounded, the fundamental group of `P` is free. -/
theorem isFreeGroup_end_of_residue (hlong : IsLongAt μ) (hcont : NotInContour μ)
    (hL : LeftCancel P) (hR : RightCancel P) (hCB : ChainBounded (Res μ))
    (hcon : IsConnected (FundGroupoid P)) (X : FundGroupoid P) : IsFreeGroup (End X) := by
  have := LargeIndecomposable.rayResidueCategory_isFiniteRayCategory μ hμ
  have : IsConnected (Quiver.FreeGroupoid (RayVert P)) := isConnected_of_quotient homotopy
  have : IsConnected (Quiver.FreeGroupoid (RayVert (Res μ))) :=
    isConnected_of_equivalent (resFGEquiv μ hμ hμr hμ0)
  have hcon' : IsConnected (FundGroupoid (Res μ)) := isConnected_quotient homotopy
  have hfree := isFreeGroup_end_fund _ (Res μ)
    (leftCancel_quotient (LargeIndecomposable.principalZeroHomIdeal μ) hL)
    (rightCancel_quotient (LargeIndecomposable.principalZeroHomIdeal μ) hR) hCB hcon' le_rfl
    ((CategoryTheory.Quotient.functor homotopy).obj ((resFG μ hμ hμr hμ0).obj X.as))
  exact IsFreeGroup.ofMulEquiv (G := End ((CategoryTheory.Quotient.functor homotopy).obj
    ((resFG μ hμ hμr hμ0).obj X.as))) (pi1Equiv μ hμ hμr hμ0 hlong hcont X.as).symm

/-! ### Contour functions -/

variable {Z : Type*} [AddCommGroup Z]

lemma inv_mapPath_mapPath {x : RayVert P} : ∀ {y : RayVert P} (s : Quiver.Path x y),
    (residueQuiverInv μ hμ hμr hμ0).mapPath ((residueQuiverMap μ hμ hμr hμ0).mapPath s) = s
  | _, .nil => rfl
  | _, .cons s e => by
    rw [Prefunctor.mapPath_cons, Prefunctor.mapPath_cons, inv_mapPath_mapPath s]
    congr 1
    exact Subtype.ext (resF_map_injective μ
      (not_factors_of_irreducible μ hμ hμr hμ0 (lift_irreducible μ hμ hμr hμ0
        (resF_irreducible μ hμ hμr hμ0 e.2))) (resF_lift μ _))

/-- Values of included paths of `P/μ`. -/
lemma inv_val_eq {x y : RayVert (Res μ)} (p q : Quiver.Path x y)
    (hpq : pathVal p = pathVal q) (h0 : pathVal p ≠ 0) :
    pathVal ((residueQuiverInv μ hμ hμr hμ0).mapPath p) =
        pathVal ((residueQuiverInv μ hμ hμr hμ0).mapPath q) ∧
      pathVal ((residueQuiverInv μ hμ hμr hμ0).mapPath p) ≠ 0 := by
  have hp := pathVal_inv_mapPath μ hμ hμr hμ0 p
  have hq := pathVal_inv_mapPath μ hμ hμr hμ0 q
  have hm : ¬LargeIndecomposable.FactorsThroughMorphism μ
      (pathVal ((residueQuiverInv μ hμ hμr hμ0).mapPath p)) := by
    rw [← LargeIndecomposable.rayResidueFunctor_map_eq_zero_iff]
    change ¬(resF μ).map _ = 0
    rw [hp]
    exact h0
  refine ⟨resF_map_injective μ hm (hp.trans (hpq.trans hq.symm)), fun h ↦ hm ?_⟩
  rw [h]
  exact ⟨0, 0, by simp⟩

/-- The restriction of a contour function to `P/μ`. -/
def restrictRes (C : ContourFn P Z) : ContourFn (Res μ) Z where
  c p q := C.c ((residueQuiverInv μ hμ hμr hμ0).mapPath p)
    ((residueQuiverInv μ hμ hμr hμ0).mapPath q)
  trans p q r hpq hqr h0 := by
    obtain ⟨h1, h0'⟩ := inv_val_eq μ hμ hμr hμ0 p q hpq h0
    obtain ⟨h2, -⟩ := inv_val_eq μ hμ hμr hμ0 q r hqr (hpq ▸ h0)
    exact C.trans _ _ _ h1 h2 h0'
  left s p q hpq h0 := by
    have hp0 : pathVal p ≠ 0 := fun h ↦ h0 (by rw [pathVal_comp, h, comp_zero])
    rw [Prefunctor.mapPath_comp, Prefunctor.mapPath_comp]
    refine C.left _ _ _ (inv_val_eq μ hμ hμr hμ0 p q hpq hp0).1 ?_
    rw [← Prefunctor.mapPath_comp]
    exact (inv_val_eq μ hμ hμr hμ0 _ _ rfl h0).2
  right p q t hpq h0 := by
    have hp0 : pathVal p ≠ 0 := fun h ↦ h0 (by rw [pathVal_comp, h, zero_comp])
    rw [Prefunctor.mapPath_comp, Prefunctor.mapPath_comp]
    refine C.right _ _ _ (inv_val_eq μ hμ hμr hμ0 p q hpq hp0).1 ?_
    rw [← Prefunctor.mapPath_comp]
    exact (inv_val_eq μ hμ hμr hμ0 _ _ rfl h0).2

lemma pathSum_mapPath (a' : ∀ {x y : RayVert (Res μ)}, (x ⟶ y) → Z) {x : RayVert P} :
    ∀ {y : RayVert P} (s : Quiver.Path x y),
    pathSum a' ((residueQuiverMap μ hμ hμr hμ0).mapPath s) =
      pathSum (fun e ↦ a' ((residueQuiverMap μ hμ hμr hμ0).map e)) s
  | _, .nil => rfl
  | _, .cons s e => by
    rw [Prefunctor.mapPath_cons]
    change pathSum a' _ + _ = pathSum _ s + _
    rw [pathSum_mapPath a' s]

include hμ hμr hμ0 in
/-- **The crown case for contour functions**: if the long morphism `μ` occurs
in no contour and `P/μ` is chain-bounded, every contour function on `P` is
exact. -/
theorem exact_of_residue (hlong : IsLongAt μ) (hcont : NotInContour μ)
    (hL : LeftCancel P) (hR : RightCancel P) (hCB : ChainBounded (Res μ))
    (C : ContourFn P Z) : C.Exact := by
  have := LargeIndecomposable.rayResidueCategory_isFiniteRayCategory μ hμ
  obtain ⟨a', ha'⟩ := ContourFn.exact_of_chainBounded Z _ (Res μ)
    (leftCancel_quotient (LargeIndecomposable.principalZeroHomIdeal μ) hL)
    (rightCancel_quotient (LargeIndecomposable.principalZeroHomIdeal μ) hR) hCB le_rfl
    (restrictRes μ hμ hμr hμ0 C)
  let aP : ∀ {x y : RayVert P}, (x ⟶ y) → Z := fun e ↦ a' ((residueQuiverMap μ hμ hμr hμ0).map e)
  refine ⟨aP, ?_⟩
  have main : ∀ n {x y : RayVert P} (s t : Quiver.Path x y), pathVal s = pathVal t →
      pathVal s ≠ 0 → ContourFn.meas s ≤ n → C.c s t = pathSum aP s - pathSum aP t := by
    intro n
    induction n with
    | zero =>
      intro x y s t _ h0 hle
      unfold ContourFn.meas at hle
      exfalso
      have := (Set.ncard_pos (IsRayCategory.below_finite (⟨x.out, y.out, pathVal s⟩ : RayMor P)
        h0)).2 ⟨(⟨x.out, y.out, pathVal s⟩ : RayMor P), h0, IsRayCategory.le_refl _⟩
      omega
    | succ n ih =>
      intro x y s t hst h0 hle
      by_cases hm : LargeIndecomposable.FactorsThroughMorphism μ (pathVal s)
      · obtain ⟨hx, hy, hs⟩ := hlong _ h0 hm
        have hx' : x = RayVert.mk a := hx
        have hy' : y = RayVert.mk b := hy
        subst hx' hy'
        have hs' : pathVal s = μ := by
          rw [hs]
          erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
        have hi := hcont s t hs' (hst ▸ hs')
        exact C.interlaced_case _ n ih s t hi h0 hle
      · have hne : ∀ r : Quiver.Path x y, pathVal r = pathVal s →
            pathVal ((residueQuiverMap μ hμ hμr hμ0).mapPath r) ≠ 0 := by
          intro r hr h
          rw [pathVal_mapPath, hr] at h
          exact hm ((LargeIndecomposable.rayResidueFunctor_map_eq_zero_iff μ _).1 h)
        have h1 := ha' ((residueQuiverMap μ hμ hμr hμ0).mapPath s)
          ((residueQuiverMap μ hμ hμr hμ0).mapPath t)
          (by rw [pathVal_mapPath, pathVal_mapPath, hst]) (hne s rfl)
        change C.c ((residueQuiverInv μ hμ hμr hμ0).mapPath _)
          ((residueQuiverInv μ hμ hμr hμ0).mapPath _) = _ at h1
        rw [inv_mapPath_mapPath, inv_mapPath_mapPath, pathSum_mapPath, pathSum_mapPath] at h1
        exact h1
  intro x y s t hst h0
  exact main _ s t hst h0 le_rfl

end Residue

end RayCat

end LargeIndecomposable
