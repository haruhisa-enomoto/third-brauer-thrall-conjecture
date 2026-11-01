module

public import LargeIndecomposable.FundamentalGroups.Basic.OpFund
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# Free fundamental groups of chain-bounded ray categories

Fischbacher's iteration (Satz 1.6 b) for finite `P`): a finite connected
chain-bounded ray category with cancellation has a free fundamental group
(`RayCat.isFreeGroup_end_fund`). Each step removes the arrows `αᵢ` of
Lemma 2.1 from `P` or from `Pᵒᵖ`; the fundamental group does not change
(Lemma 2.2, `RayCat.endEquivOp`) and the number of arrows drops. Without
essential contours the fundamental groupoid is free.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Opposite

universe v u

namespace RayCat

/-! ### Connectivity -/

lemma zigzag_of_quotient {C : Type*} [Category C] (r : HomRel C) {X : C} :
    ∀ {Z : CategoryTheory.Quotient r}, Zigzag ((CategoryTheory.Quotient.functor r).obj X) Z →
      Zigzag X Z.as := by
  intro Z h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hzag ih =>
    refine ih.tail ?_
    rcases hzag with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
    · exact Or.inl ⟨Quot.out f⟩
    · exact Or.inr ⟨Quot.out f⟩

/-- A connected quotient of a category is the quotient of a connected category. -/
lemma isConnected_of_quotient {C : Type*} [Category C] (r : HomRel C)
    [IsConnected (CategoryTheory.Quotient r)] : IsConnected C := by
  obtain ⟨X₀⟩ := (inferInstance : Nonempty (CategoryTheory.Quotient r))
  have : Nonempty C := ⟨X₀.as⟩
  refine zigzag_isConnected fun X Y ↦ ?_
  exact zigzag_of_quotient r (isPreconnected_zigzag _ (⟨Y⟩ : CategoryTheory.Quotient r))

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P]

/-! ### Counting arrows -/

/-- The arrows of the quiver of `P`. -/
abbrev Arrows (P : Type u) [Category.{v} P] [HasZeroMorphisms P] : Type (max u v) :=
  Σ (x y : RayVert P), x ⟶ y

/-- The number of arrows of `P`. -/
noncomputable def arrowCount (P : Type u) [Category.{v} P] [HasZeroMorphisms P] : ℕ :=
  Nat.card (Arrows P)

/-- Arrows of `P` and of `Pᵒᵖ` correspond. -/
def arrowsOpEquiv : Arrows P ≃ Arrows Pᵒᵖ where
  toFun a := ⟨RayVert.mk (op a.2.1.out), RayVert.mk (op a.1.out), revArr a.2.2⟩
  invFun A := ⟨RayVert.mk A.2.1.out.unop, RayVert.mk A.1.out.unop, unrevArr A.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma arrowCount_op : arrowCount Pᵒᵖ = arrowCount P :=
  (Nat.card_congr arrowsOpEquiv).symm

/-! ### The equivalence of Lemma 2.2 -/

section Red

variable [LargeIndecomposable.IsFiniteRayCategory0 P] [Finite P] {ι : Type*} {b : P}
  {d : ι → P} {α : ∀ i, b ⟶ d i} {hα : ∀ i, ¬IsIso (α i)}

/-- Lemma 2.2 as an equivalence of fundamental groupoids. -/
def RedData.fundEquiv (D : RedData α) (hE : D.EssHyp (hα := hα)) :
    FundGroupoid P ≌ FundGroupoid (ArrowQuot α) :=
  CategoryTheory.Equivalence.mk (D.psiBar hE) (phiBar α hα)
    (eqToIso (D.psiBar_phiBar hE).symm) (eqToIso (D.phiBar_psiBar hE))

variable (α hα)

/-- `P/⟨αᵢ⟩` has left cancellation if `P` has. -/
lemma leftCancel_quot (hL : LeftCancel P) : LeftCancel (ArrowQuot α) := by
  intro x y z f g h hfg h0
  rw [← quotF_liftQ α f, ← quotF_liftQ α g, ← quotF_liftQ α h, ← Functor.map_comp,
    ← Functor.map_comp] at hfg
  have hm : ¬(arrowIdeal α).mem (liftQ α f ≫ liftQ α g) := by
    rw [← (arrowIdeal α).functor_map_ne_zero_iff, Functor.map_comp, quotF_liftQ, quotF_liftQ]
    exact h0
  have h1 := quotF_map_injective α hm hfg
  rw [← quotF_liftQ α g, ← quotF_liftQ α h]
  congr 1
  exact hL _ _ _ h1 (fun h' ↦ hm (Or.inl h'))

/-- `P/⟨αᵢ⟩` has right cancellation if `P` has. -/
lemma rightCancel_quot (hR : RightCancel P) : RightCancel (ArrowQuot α) := by
  intro x y z f g h hfg h0
  rw [← quotF_liftQ α f, ← quotF_liftQ α g, ← quotF_liftQ α h, ← Functor.map_comp,
    ← Functor.map_comp] at hfg
  have hm : ¬(arrowIdeal α).mem (liftQ α f ≫ liftQ α h) := by
    rw [← (arrowIdeal α).functor_map_ne_zero_iff, Functor.map_comp, quotF_liftQ, quotF_liftQ]
    exact h0
  have h1 := quotF_map_injective α hm hfg
  rw [← quotF_liftQ α f, ← quotF_liftQ α g]
  congr 1
  exact hR _ _ _ h1 (fun h' ↦ hm (Or.inl h'))

/-- A morphism of `P/⟨αᵢ⟩`, lifted to `P`. -/
def liftRM (F : RayMor (ArrowQuot α)) : RayMor P := ⟨F.1.as, F.2.1.as, liftQ α F.2.2⟩

lemma peak_liftRM {F G : RayMor (ArrowQuot α)} (h : Peak F G) :
    Peak (liftRM α F) (liftRM α G) := by
  obtain ⟨X, Y, φ⟩ := F
  obtain ⟨X', Y', ψ⟩ := G
  obtain ⟨hY, -⟩ := id h
  change Y = Y' at hY
  subst hY
  rw [peak_mk_iff] at h
  change Peak ⟨X.as, Y.as, liftQ α φ⟩ ⟨X'.as, Y.as, liftQ α ψ⟩
  rw [peak_mk_iff]
  refine ⟨fun ⟨k, hk⟩ ↦ h.1 ⟨(arrowQuotF α).map k, ?_⟩, fun ⟨k, hk⟩ ↦ h.2 ⟨(arrowQuotF α).map k, ?_⟩⟩
  · rw [← quotF_liftQ α ψ, ← Functor.map_comp, hk, quotF_liftQ]
  · rw [← quotF_liftQ α φ, ← Functor.map_comp, hk, quotF_liftQ]

lemma valley_liftRM {F G : RayMor (ArrowQuot α)} (h : Valley F G) :
    Valley (liftRM α F) (liftRM α G) := by
  obtain ⟨X, Y, φ⟩ := F
  obtain ⟨X', Y', ψ⟩ := G
  obtain ⟨hX, -⟩ := id h
  change X = X' at hX
  subst hX
  rw [valley_mk_iff] at h
  change Valley ⟨X.as, Y.as, liftQ α φ⟩ ⟨X.as, Y'.as, liftQ α ψ⟩
  rw [valley_mk_iff]
  refine ⟨fun ⟨k, hk⟩ ↦ h.1 ⟨(arrowQuotF α).map k, ?_⟩, fun ⟨k, hk⟩ ↦ h.2 ⟨(arrowQuotF α).map k, ?_⟩⟩
  · rw [← quotF_liftQ α φ, ← Functor.map_comp, hk, quotF_liftQ]
  · rw [← quotF_liftQ α ψ, ← Functor.map_comp, hk, quotF_liftQ]

/-- `P/⟨αᵢ⟩` is chain-bounded if `P` is. -/
lemma chainBounded_quot (hCB : ChainBounded P) : ChainBounded (ArrowQuot α) := by
  obtain ⟨N, hN⟩ := hCB
  refine ⟨N, fun L hL ↦ ?_⟩
  have : IsChain 0 (L.map (liftRM α)) := by
    refine ⟨fun f hf ↦ ?_, fun j hj ↦ ?_⟩
    · obtain ⟨F, hF, rfl⟩ := List.mem_map.1 hf
      intro h0
      have h0' : liftQ α F.2.2 = 0 := h0
      apply hL.1 F hF
      rw [← quotF_liftQ α F.2.2, h0', Functor.map_zero]
    · have := hL.2 j (by simpa using hj)
      simp only [List.getElem_map]
      unfold Link at this ⊢
      split_ifs at this ⊢
      · exact peak_liftRM α this
      · exact valley_liftRM α this
  simpa using hN _ this

lemma arrows_finite : Finite (Arrows P) := by
  have : ∀ x y : P, Finite (x ⟶ y) := LargeIndecomposable.IsFiniteRayCategory0.hom_finite
  have : Finite (RayVert P) := inferInstanceAs (Finite P)
  have : ∀ x y : RayVert P, Finite (x ⟶ y) := fun x y ↦ Subtype.finite
  infer_instance

include hα in
/-- Removing the arrows `αᵢ` lowers the number of arrows. -/
lemma arrowCount_quot_lt (D : RedData α) (hι : Nonempty ι) :
    arrowCount (ArrowQuot α) < arrowCount P := by
  classical
  have := (arrowIdeal α).quotientIsFiniteRayCategory0 (arrowIdeal_isProper α hα)
  have := arrows_finite (P := P)
  have := arrows_finite (P := ArrowQuot α)
  haveI := Fintype.ofFinite (Arrows P)
  haveI := Fintype.ofFinite (Arrows (ArrowQuot α))
  let F := inclQuiver α hα
  let f : Arrows (ArrowQuot α) → Arrows P := fun a ↦ ⟨F.obj a.1, F.obj a.2.1, F.map a.2.2⟩
  have hobj : Function.Injective F.obj := fun x y h ↦ CategoryTheory.Quotient.ext h
  have hmap : ∀ {x y : RayVert (ArrowQuot α)} (e e' : x ⟶ y), F.map e = F.map e' → e = e' := by
    intro x y e e' h
    apply Subtype.ext
    rw [← quotF_liftQ α e.1, ← quotF_liftQ α e'.1]
    exact congrArg (fun g ↦ (arrowQuotF α).map g.1) h
  have hf : Function.Injective f := by
    rintro ⟨x, y, e⟩ ⟨x', y', e'⟩ h
    obtain ⟨h1, h2⟩ := Sigma.mk.inj h
    obtain rfl := hobj h1
    obtain ⟨h3, h4⟩ := Sigma.mk.inj (eq_of_heq h2)
    obtain rfl := hobj h3
    rw [hmap e e' (eq_of_heq h4)]
  obtain ⟨i⟩ := hι
  have hnot : (⟨RayVert.mk b, RayVert.mk (d i), D.a i⟩ : Arrows P) ∉ Set.range f := by
    rintro ⟨a, ha⟩
    have h1 : ¬(arrowIdeal α).mem (f a).2.2.1 := liftQ_not_mem α hα a.2.2.2
    rw [ha] at h1
    apply h1
    refine Or.inr ⟨i, 𝟙 b, 𝟙 (d i), ?_⟩
    rw [D.a_val]
    simp
  rw [arrowCount, arrowCount, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_of_notMem f hf hnot

end Red

/-! ### The iteration -/

attribute [local instance] isRayCategory_of_finiteRayCategory

/-- **Fischbacher's Satz 1.6 b)** for finite ray categories: a finite connected
chain-bounded ray category with cancellation has a free fundamental group. -/
theorem isFreeGroup_end_fund : ∀ (n : ℕ) (Q : Type u) [Category.{v} Q] [HasZeroMorphisms Q]
    [LargeIndecomposable.IsFiniteRayCategory0 Q] [Finite Q], LeftCancel Q → RightCancel Q →
    ChainBounded Q → IsConnected (FundGroupoid Q) → arrowCount Q ≤ n →
    ∀ X : FundGroupoid Q, IsFreeGroup (End X) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q _ _ _ _ hL hR hCB hcon hn X
  by_cases hess : NoEssContour (P := Q)
  · have : IsConnected (Quiver.FreeGroupoid (RayVert Q)) := isConnected_of_quotient homotopy
    exact isFreeGroup_end_of_noEss hess X.as
  · simp only [NoEssContour, not_forall] at hess
    obtain ⟨x, y, s, t, hst, h0, hi⟩ := hess
    rcases hasRedData_or_op hL hR hCB s t hst h0 hi with
      ⟨b, ι, d, α, hα, D, hE, -, hι⟩ | ⟨b, ι, d, α, hα, D, hE, -, hι⟩
    · have := (arrowIdeal α).quotientIsFiniteRayCategory0 (arrowIdeal_isProper α hα)
      have hlt := arrowCount_quot_lt α hα D hι
      have hcon' : IsConnected (FundGroupoid (ArrowQuot α)) :=
        isConnected_of_equivalent (D.fundEquiv hE)
      have := ih (arrowCount (ArrowQuot α)) (by omega) (ArrowQuot α) (leftCancel_quot α hL)
        (rightCancel_quot α hR) (chainBounded_quot α hCB) hcon' le_rfl ((D.psiBar hE).obj X)
      exact IsFreeGroup.ofMulEquiv (G := End ((D.psiBar hE).obj X)) (D.pi1Equiv hE X).symm
    · have := (arrowIdeal α).quotientIsFiniteRayCategory0 (arrowIdeal_isProper α hα)
      have hlt := arrowCount_quot_lt α hα D hι
      rw [arrowCount_op] at hlt
      have hcon₁ : IsConnected (FundGroupoid Qᵒᵖ) := isConnected_of_equivalent opEquivFund
      have hcon' : IsConnected (FundGroupoid (ArrowQuot α)) :=
        isConnected_of_equivalent (D.fundEquiv hE)
      have := ih (arrowCount (ArrowQuot α)) (by omega) (ArrowQuot α)
        (leftCancel_quot α (leftCancel_op hR)) (rightCancel_quot α (rightCancel_op hL))
        (chainBounded_quot α (chainBounded_op hCB)) hcon' le_rfl
        ((D.psiBar hE).obj (opBar.obj X))
      have h1 : IsFreeGroup (End (opBar.obj X)) :=
        IsFreeGroup.ofMulEquiv (G := End ((D.psiBar hE).obj (opBar.obj X)))
          (D.pi1Equiv hE (opBar.obj X)).symm
      exact IsFreeGroup.ofMulEquiv (G := End (opBar.obj X)) (endEquivOp X).symm

/-- Free groups are torsion-free. -/
lemma pow_ne_one_of_isFreeGroup {G : Type*} [Group G] [IsFreeGroup G] (g : G) (hg : g ≠ 1)
    (n : ℕ) (hn : 0 < n) : g ^ n ≠ 1 := by
  intro h
  let e := IsFreeGroup.toFreeGroup G
  have h1 : (e g) ^ n = (e 1) ^ n := by rw [← map_pow, h, map_one, one_pow]
  exact hg (e.injective (IsMulTorsionFree.pow_left_injective hn.ne' h1))

/-- Automorphism groups in a groupoid with free vertex groups are torsion-free. -/
lemma aut_pow_ne_one_of_isFreeGroup_end {G : Type*} [Groupoid G] (X : G)
    (hfree : IsFreeGroup (End X)) (g : Aut X) (hg : g ≠ 1) (n : ℕ) (hn : 0 < n) : g ^ n ≠ 1 := by
  let e : Aut X ≃* End X := (Aut.unitsEndEquivAut X).symm.trans (toUnits (G := End X)).symm
  intro h
  refine pow_ne_one_of_isFreeGroup (e g) (fun h' ↦ hg (e.injective (h'.trans e.map_one.symm))) n hn
    ?_
  rw [← map_pow, h, map_one]

/-- The fundamental group of a finite connected chain-bounded ray category with
cancellation is torsion-free (in the form used by the covering data). -/
theorem pi1_torsionFree {Q : Type u} [Category.{v} Q] [HasZeroMorphisms Q]
    [LargeIndecomposable.IsFiniteRayCategory0 Q] [Finite Q] (hL : LeftCancel Q) (hR : RightCancel Q)
    (hCB : ChainBounded Q) (hcon : IsConnected (FundGroupoid Q)) (X : FundGroupoid Q)
    (g : Aut X) (hg : g ≠ 1) (n : ℕ) (hn : 0 < n) : g ^ n ≠ 1 := by
  have hfree := isFreeGroup_end_fund _ Q hL hR hCB hcon le_rfl X
  let e : Aut X ≃* End X := (Aut.unitsEndEquivAut X).symm.trans (toUnits (G := End X)).symm
  intro h
  refine pow_ne_one_of_isFreeGroup (e g) (fun h' ↦ hg (e.injective (h'.trans e.map_one.symm))) n hn
    ?_
  rw [← map_pow, h, map_one]

end RayCat

end LargeIndecomposable
