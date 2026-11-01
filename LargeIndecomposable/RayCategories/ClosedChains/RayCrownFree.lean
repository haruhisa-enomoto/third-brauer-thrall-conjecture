module

public import LargeIndecomposable.RayCategories.ClosedChains.RayInfiniteChain

@[expose] public section

/-!
# Crown-free factorization orders

Formalize the finite-poset content of BGRS 8.5.  Excluding the four-element
crown makes every bounded pair admit a supremum.  Excluding the six-element
crown forces the three pairwise suprema of three incomparable elements into
one of the three configurations obtained from Figures 57--59 by permutation.
Figure 60 is recorded separately as the case in which only the two adjacent
suprema exist.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v w

/-- Two elements of a preorder are incomparable. -/
def OrderIncomparable {P : Type w} [LE P] (a b : P) : Prop :=
  ¬a ≤ b ∧ ¬b ≤ a

/-- Four elements form the full four-element crown: the two lower elements
are incomparable, the two upper elements are incomparable, and every lower
element lies below every upper element. -/
def IsFourCrown {P : Type w} [LE P] (a b u v : P) : Prop :=
  OrderIncomparable a b ∧ OrderIncomparable u v ∧
    a ≤ u ∧ b ≤ u ∧ a ≤ v ∧ b ≤ v

/-- The four-element crown does not occur in `P`. -/
def HasNoFourCrown (P : Type w) [LE P] : Prop :=
  ∀ a b u v : P, ¬IsFourCrown a b u v

/-- Six elements form the full six-element crown, with lower vertices
`a,b,c` and upper vertices `ab,bc,ac`. -/
def IsSixCrown {P : Type w} [LE P]
    (a b c ab bc ac : P) : Prop :=
  OrderIncomparable a b ∧ OrderIncomparable a c ∧
    OrderIncomparable b c ∧
  OrderIncomparable ab bc ∧ OrderIncomparable ab ac ∧
    OrderIncomparable bc ac ∧
  a ≤ ab ∧ b ≤ ab ∧ b ≤ bc ∧ c ≤ bc ∧ a ≤ ac ∧ c ≤ ac ∧
  ¬a ≤ bc ∧ ¬b ≤ ac ∧ ¬c ≤ ab

/-- The six-element crown does not occur in `P`. -/
def HasNoSixCrown (P : Type w) [LE P] : Prop :=
  ∀ a b c ab bc ac : P, ¬IsSixCrown a b c ab bc ac

/-- Four-crown exclusion is invariant under reversing the order. -/
theorem hasNoFourCrown_orderDual {P : Type w} [LE P]
    (hfree : HasNoFourCrown P) : HasNoFourCrown (OrderDual P) := by
  intro a b u v h
  rcases h with ⟨hab, huv, hau, hbu, hav, hbv⟩
  exact hfree u v a b
    ⟨⟨huv.2, huv.1⟩, ⟨hab.2, hab.1⟩, hau, hav, hbu, hbv⟩

/-- Six-crown exclusion is invariant under reversing the order. -/
theorem hasNoSixCrown_orderDual {P : Type w} [LE P]
    (hfree : HasNoSixCrown P) : HasNoSixCrown (OrderDual P) := by
  intro a b c ab bc ac h
  rcases h with ⟨hab, hac, hbc, habbc, habac, hbcac,
    haab, hbab, hbbc, hcbc, haac, hcac, hnabc, hnbac, hncab⟩
  exact hfree ab bc ac b c a
    ⟨⟨habbc.2, habbc.1⟩, ⟨habac.2, habac.1⟩,
      ⟨hbcac.2, hbcac.1⟩, ⟨hbc.2, hbc.1⟩,
      ⟨hab.1, hab.2⟩, ⟨hac.1, hac.2⟩,
      hbab, hbbc, hcbc, hcac, haab, haac,
      hncab, hnabc, hnbac⟩

/-- In a four-crown-free order, two common upper bounds of an incomparable
pair must be comparable. -/
theorem comparable_commonUpperBounds_of_noFourCrown
    {P : Type w} [LE P] (hfree : HasNoFourCrown P)
    {a b u v : P} (hab : OrderIncomparable a b)
    (hau : a ≤ u) (hbu : b ≤ u) (hav : a ≤ v) (hbv : b ≤ v) :
    u ≤ v ∨ v ≤ u := by
  by_contra huv
  push Not at huv
  exact hfree a b u v
    ⟨hab, ⟨huv.1, huv.2⟩, hau, hbu, hav, hbv⟩

/-- The order-dual form: two common lower bounds of an incomparable pair
must be comparable in a four-crown-free order. -/
theorem comparable_commonLowerBounds_of_noFourCrown
    {P : Type w} [LE P] (hfree : HasNoFourCrown P)
    {a b u v : P} (hab : OrderIncomparable a b)
    (hua : u ≤ a) (hub : u ≤ b) (hva : v ≤ a) (hvb : v ≤ b) :
    u ≤ v ∨ v ≤ u := by
  by_contra huv
  push Not at huv
  exact hfree u v a b
    ⟨⟨huv.1, huv.2⟩, hab, hua, hva, hub, hvb⟩

/-- An element is the supremum of a specified pair. -/
def IsPairSupremum {P : Type w} [LE P] (a b s : P) : Prop :=
  a ≤ s ∧ b ≤ s ∧ ∀ u : P, a ≤ u → b ≤ u → s ≤ u

/-- An element is the infimum of a specified pair. -/
def IsPairInfimum {P : Type w} [LE P] (a b s : P) : Prop :=
  s ≤ a ∧ s ≤ b ∧ ∀ u : P, u ≤ a → u ≤ b → u ≤ s

/-- A pair supremum in the reversed order is exactly a pair infimum. -/
theorem isPairSupremum_orderDual_iff_isPairInfimum
    {P : Type w} [LE P] (a b s : P) :
    @IsPairSupremum (OrderDual P) (OrderDual.instLE P) a b s ↔
      IsPairInfimum a b s :=
  Iff.rfl

/-- In a finite partial order without a four-element crown, every pair with a
common upper bound has a supremum. -/
theorem exists_isPairSupremum_of_noFourCrown
    {P : Type w} [PartialOrder P] [Finite P]
    (hfree : HasNoFourCrown P) (a b u : P)
    (hau : a ≤ u) (hbu : b ≤ u) :
    ∃ s : P, IsPairSupremum a b s := by
  classical
  by_cases hab : a ≤ b
  · exact ⟨b, hab, le_rfl, fun _ _ hbv ↦ hbv⟩
  by_cases hba : b ≤ a
  · exact ⟨a, le_rfl, hba, fun _ hav _ ↦ hav⟩
  let upper : Set P := {s | a ≤ s ∧ b ≤ s}
  have hupperFinite : upper.Finite := Set.toFinite upper
  have hupperNonempty : upper.Nonempty := ⟨u, hau, hbu⟩
  obtain ⟨s, hs⟩ := hupperFinite.exists_minimal hupperNonempty
  refine ⟨s, hs.prop.1, hs.prop.2, ?_⟩
  intro t hat hbt
  by_contra hst
  let below : Set P := {r | r ∈ upper ∧ r ≤ t}
  have hbelowFinite : below.Finite := Set.toFinite below
  have hbelowNonempty : below.Nonempty := ⟨t, ⟨hat, hbt⟩, le_rfl⟩
  obtain ⟨r, hr⟩ := hbelowFinite.exists_minimal hbelowNonempty
  have hrUpper : r ∈ upper := hr.prop.1
  have hrMinimal : Minimal (· ∈ upper) r := by
    refine ⟨hrUpper, ?_⟩
    intro q hqUpper hqr
    apply hr.le_of_le
    · exact ⟨hqUpper, hqr.trans hr.prop.2⟩
    · exact hqr
  have hsr : ¬s ≤ r := fun hsr ↦ hst (hsr.trans hr.prop.2)
  have hrs : ¬r ≤ s := by
    intro hrs
    have hsr' := hs.le_of_le hrUpper hrs
    exact hst (hsr'.trans hr.prop.2)
  exact hfree a b s r
    ⟨⟨hab, hba⟩, ⟨hsr, hrs⟩,
      hs.prop.1, hs.prop.2, hrUpper.1, hrUpper.2⟩

/-- In a finite partial order without a four-element crown, every pair with a
common lower bound has an infimum. -/
theorem exists_isPairInfimum_of_noFourCrown
    {P : Type w} [PartialOrder P] [Finite P]
    (hfree : HasNoFourCrown P) (a b u : P)
    (hua : u ≤ a) (hub : u ≤ b) :
    ∃ s : P, IsPairInfimum a b s := by
  obtain ⟨s, hs⟩ := exists_isPairSupremum_of_noFourCrown
    (P := OrderDual P) (hasNoFourCrown_orderDual hfree)
      a b u hua hub
  exact ⟨s, (isPairSupremum_orderDual_iff_isPairInfimum a b s).1 hs⟩

/-- Pairwise incomparable pair suprema of three incomparable elements form a
full six-element crown. -/
theorem isSixCrown_of_pairSuprema_incomparable
    {P : Type w} [PartialOrder P]
    {a b c ab bc ac : P}
    (hab : OrderIncomparable a b) (hac : OrderIncomparable a c)
    (hbc : OrderIncomparable b c)
    (hsab : IsPairSupremum a b ab)
    (hsbc : IsPairSupremum b c bc)
    (hsac : IsPairSupremum a c ac)
    (habbc : OrderIncomparable ab bc)
    (habac : OrderIncomparable ab ac)
    (hbcac : OrderIncomparable bc ac) :
    IsSixCrown a b c ab bc ac := by
  refine ⟨hab, hac, hbc, habbc, habac, hbcac,
    hsab.1, hsab.2.1, hsbc.1, hsbc.2.1, hsac.1, hsac.2.1,
    ?_, ?_, ?_⟩
  · intro habc
    exact habbc.1 (hsab.2.2 bc habc hsbc.1)
  · intro hbac
    exact habac.1 (hsab.2.2 ac hsac.1 hbac)
  · intro hcab
    exact habbc.2 (hsbc.2.2 ab hsab.2.1 hcab)

/-- If the six-element crown is forbidden, one of the three pair suprema lies
above the other two.  These are Figures 57--59 up to permutation. -/
theorem pairSuprema_dominating_of_noSixCrown
    {P : Type w} [PartialOrder P]
    (hfree : HasNoSixCrown P)
    {a b c ab bc ac : P}
    (hab : OrderIncomparable a b) (hac : OrderIncomparable a c)
    (hbc : OrderIncomparable b c)
    (hsab : IsPairSupremum a b ab)
    (hsbc : IsPairSupremum b c bc)
    (hsac : IsPairSupremum a c ac) :
    (ab ≤ ac ∧ bc ≤ ac) ∨
      (ab ≤ bc ∧ ac ≤ bc) ∨
      (bc ≤ ab ∧ ac ≤ ab) := by
  classical
  by_cases habbc : ab ≤ bc
  · exact Or.inr <| Or.inl ⟨habbc,
      hsac.2.2 bc (hsab.1.trans habbc) hsbc.2.1⟩
  by_cases hbcab : bc ≤ ab
  · exact Or.inr <| Or.inr ⟨hbcab,
      hsac.2.2 ab hsab.1 (hsbc.2.1.trans hbcab)⟩
  by_cases habac : ab ≤ ac
  · exact Or.inl ⟨habac,
      hsbc.2.2 ac (hsab.2.1.trans habac) hsac.2.1⟩
  by_cases hacab : ac ≤ ab
  · exact Or.inr <| Or.inr ⟨
      hsbc.2.2 ab hsab.2.1 (hsac.2.1.trans hacab), hacab⟩
  by_cases hbcac : bc ≤ ac
  · exact Or.inl ⟨
      hsab.2.2 ac hsac.1 (hsbc.1.trans hbcac), hbcac⟩
  by_cases hacbc : ac ≤ bc
  · exact Or.inr <| Or.inl ⟨
      hsab.2.2 bc (hsac.1.trans hacbc) hsbc.1, hacbc⟩
  exact ((hfree a b c ab bc ac) <|
    isSixCrown_of_pairSuprema_incomparable hab hac hbc hsab hsbc hsac
      ⟨habbc, hbcab⟩ ⟨habac, hacab⟩ ⟨hbcac, hacbc⟩).elim

/-- If the six-element crown is forbidden, one of the three pair infima lies
below the other two.  This is the order dual of the preceding theorem. -/
theorem pairInfima_subordinate_of_noSixCrown
    {P : Type w} [PartialOrder P]
    (hfree : HasNoSixCrown P)
    {a b c ab bc ac : P}
    (hab : OrderIncomparable a b) (hac : OrderIncomparable a c)
    (hbc : OrderIncomparable b c)
    (hiab : IsPairInfimum a b ab)
    (hibc : IsPairInfimum b c bc)
    (hiac : IsPairInfimum a c ac) :
    (ac ≤ ab ∧ ac ≤ bc) ∨
      (bc ≤ ab ∧ bc ≤ ac) ∨
      (ab ≤ bc ∧ ab ≤ ac) := by
  exact pairSuprema_dominating_of_noSixCrown
    (P := OrderDual P) (hasNoSixCrown_orderDual hfree)
    ⟨hab.2, hab.1⟩ ⟨hac.2, hac.1⟩ ⟨hbc.2, hbc.1⟩
    ((isPairSupremum_orderDual_iff_isPairInfimum a b ab).2 hiab)
    ((isPairSupremum_orderDual_iff_isPairInfimum b c bc).2 hibc)
    ((isPairSupremum_orderDual_iff_isPairInfimum a c ac).2 hiac)

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The four- and six-crown consequences of chainlessness in the fixed-source
factorization order `x/P`. -/
class IsRayCrownFree (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] : Prop where
  no_four : ∀ x : C, HasNoFourCrown (NonzeroMorphismFrom x)
  no_six : ∀ x : C, HasNoSixCrown (NonzeroMorphismFrom x)

/-- The orientation-dual crown consequences in the fixed-target
factorization order. -/
class IsRayCocrownFree (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] : Prop where
  no_four : ∀ x : C, HasNoFourCrown (NonzeroMorphismTo x)
  no_six : ∀ x : C, HasNoSixCrown (NonzeroMorphismTo x)

/-- Crown-freeness gives the pair-supremum property used throughout BGRS 8.5. -/
theorem exists_isRayPairSupremum_of_common_upper
    [Finite C] [IsFiniteRayCategory C] [IsRayCrownFree C]
    {x : C} (f g u : NonzeroMorphismFrom x)
    (hfu : f ≤ u) (hgu : g ≤ u) :
    ∃ s : NonzeroMorphismFrom x, IsRayPairSupremum f g s := by
  obtain ⟨s, hs⟩ := exists_isPairSupremum_of_noFourCrown
    (IsRayCrownFree.no_four x) f g u hfu hgu
  exact ⟨s, hs⟩

/-- Fixed-target cocrown-freeness gives the pair-infimum property used in the
cohook dual of BGRS 8.5. -/
theorem exists_isRayPairInfimum_of_common_lower
    [Finite C] [IsFiniteRayCategory C] [IsRayCocrownFree C]
    {x : C} (f g u : NonzeroMorphismTo x)
    (huf : u ≤ f) (hug : u ≤ g) :
    ∃ s : NonzeroMorphismTo x, IsRayPairInfimum f g s := by
  obtain ⟨s, hs⟩ := exists_isPairInfimum_of_noFourCrown
    (IsRayCocrownFree.no_four x) f g u huf hug
  exact ⟨s, hs⟩

/-- The order content of Figures 57--59: for three incomparable rays whose
three pair suprema exist, one of the three choices of middle ray lies below
the supremum of the two outer rays. -/
theorem rayPairSuprema_dominating_of_crownFree
    [IsFiniteRayCategory C] [IsRayCrownFree C]
    {x : C} {a b c ab bc ac : NonzeroMorphismFrom x}
    (hab : OrderIncomparable a b) (hac : OrderIncomparable a c)
    (hbc : OrderIncomparable b c)
    (hsab : IsRayPairSupremum a b ab)
    (hsbc : IsRayPairSupremum b c bc)
    (hsac : IsRayPairSupremum a c ac) :
    (ab ≤ ac ∧ bc ≤ ac) ∨
      (ab ≤ bc ∧ ac ≤ bc) ∨
      (bc ≤ ab ∧ ac ≤ ab) :=
  pairSuprema_dominating_of_noSixCrown
    (IsRayCrownFree.no_six x) hab hac hbc hsab hsbc hsac

/-- The fixed-target dual of the preceding three-suprema conclusion: one of
the three pair infima lies below the other two. -/
theorem rayPairInfima_subordinate_of_cocrownFree
    [IsFiniteRayCategory C] [IsRayCocrownFree C]
    {x : C} {a b c ab bc ac : NonzeroMorphismTo x}
    (hab : OrderIncomparable a b) (hac : OrderIncomparable a c)
    (hbc : OrderIncomparable b c)
    (hiab : IsRayPairInfimum a b ab)
    (hibc : IsRayPairInfimum b c bc)
    (hiac : IsRayPairInfimum a c ac) :
    (ac ≤ ab ∧ ac ≤ bc) ∨
      (bc ≤ ab ∧ bc ≤ ac) ∨
      (ab ≤ bc ∧ ab ≤ ac) :=
  pairInfima_subordinate_of_noSixCrown
    (IsRayCocrownFree.no_six x) hab hac hbc hiab hibc hiac

/-- Figures 57--60 with `gamma` distinguished as the middle arrow.  In the
first alternative the outer supremum exists above `gamma`; in Figure 60 only
the two adjacent suprema exist. -/
def IsRayThreeArrowFigure {x : C}
    (beta gamma delta : NonzeroMorphismFrom x) : Prop :=
  (∃ s, IsRayPairSupremum beta delta s ∧ gamma ≤ s) ∨
    ((∃ s, IsRayPairSupremum beta gamma s) ∧
      (∃ s, IsRayPairSupremum gamma delta s) ∧
      ¬∃ s, IsRayPairSupremum beta delta s)

/-- Figures 57--59 can be labeled so that one arrow is the middle arrow below
the supremum of the other two. -/
theorem exists_permutation_isRayThreeArrowFigure_of_pairSuprema
    [IsFiniteRayCategory C] [IsRayCrownFree C]
    {x : C} {a b c ab bc ac : NonzeroMorphismFrom x}
    (hab : OrderIncomparable a b) (hac : OrderIncomparable a c)
    (hbc : OrderIncomparable b c)
    (hsab : IsRayPairSupremum a b ab)
    (hsbc : IsRayPairSupremum b c bc)
    (hsac : IsRayPairSupremum a c ac) :
    IsRayThreeArrowFigure a b c ∨
      IsRayThreeArrowFigure a c b ∨
      IsRayThreeArrowFigure b a c := by
  rcases rayPairSuprema_dominating_of_crownFree
      hab hac hbc hsab hsbc hsac with hacTop | hbcTop | habTop
  · exact Or.inl <| Or.inl ⟨ac, hsac,
      hsab.2.1.trans hacTop.1⟩
  · exact Or.inr <| Or.inr <| Or.inl ⟨bc, hsbc,
      hsab.1.trans hbcTop.1⟩
  · exact Or.inr <| Or.inl <| Or.inl ⟨ab, hsab,
      hsbc.2.1.trans habTop.1⟩

/-- The fixed-target duals of Figures 57--60, with `gamma` distinguished as
the middle arrow.  In the first alternative the outer infimum lies below
`gamma`; in Figure 60 only the two adjacent infima exist. -/
def IsRayCoThreeArrowFigure {x : C}
    (beta gamma delta : NonzeroMorphismTo x) : Prop :=
  (∃ s, IsRayPairInfimum beta delta s ∧ s ≤ gamma) ∨
    ((∃ s, IsRayPairInfimum beta gamma s) ∧
      (∃ s, IsRayPairInfimum gamma delta s) ∧
      ¬∃ s, IsRayPairInfimum beta delta s)

/-- The fixed-target duals of Figures 57--59 can be labeled so that one arrow
is the middle arrow above the infimum of the two outer rays. -/
theorem exists_permutation_isRayCoThreeArrowFigure_of_pairInfima
    [IsFiniteRayCategory C] [IsRayCocrownFree C]
    {x : C} {a b c ab bc ac : NonzeroMorphismTo x}
    (hab : OrderIncomparable a b) (hac : OrderIncomparable a c)
    (hbc : OrderIncomparable b c)
    (hiab : IsRayPairInfimum a b ab)
    (hibc : IsRayPairInfimum b c bc)
    (hiac : IsRayPairInfimum a c ac) :
    IsRayCoThreeArrowFigure a b c ∨
      IsRayCoThreeArrowFigure a c b ∨
      IsRayCoThreeArrowFigure b a c := by
  rcases rayPairInfima_subordinate_of_cocrownFree
      hab hac hbc hiab hibc hiac with hacBottom | hbcBottom | habBottom
  · exact Or.inl <| Or.inl ⟨ac, hiac,
      hacBottom.1.trans hiab.2.1⟩
  · exact Or.inr <| Or.inr <| Or.inl ⟨bc, hibc,
      hbcBottom.1.trans hiab.1⟩
  · exact Or.inr <| Or.inl <| Or.inl ⟨ab, hiab,
      habBottom.1.trans hibc.2.1⟩

/-- In Figure 60, failure of both possible hook replacements would create the
missing outer supremum. -/
theorem RayHookTackle.lastReplacementCompatible_or_of_no_outer_supremum
    [Finite C] [IsFiniteRayCategory C] [IsRayCrownFree C]
    {m : ℕ} (t : RayHookTackle (C := C) m)
    {B D : C}
    (beta : NonzeroHom (t.x (Fin.last m)) B)
    (delta : NonzeroHom (t.x (Fin.last m)) D)
    (hbeta : IsIrreducibleRayMorphism beta.1)
    (hdelta : IsIrreducibleRayMorphism delta.1)
    (hno : ¬∃ s, IsRayPairSupremum beta.toMorphismFrom
      delta.toMorphismFrom s) :
    t.LastReplacementCompatible beta ∨
      t.LastReplacementCompatible delta := by
  cases m with
  | zero => simp [RayHookTackle.LastReplacementCompatible]
  | succ n =>
      let sigma := t.sigma (Fin.last n)
      let gamma := t.rho (Fin.last (n + 1))
      have hvalley : RaySourceIncomparable sigma gamma := by
        simpa [sigma, gamma] using t.valley_incomparable (Fin.last n)
      have hsigmaIso : ¬IsIso sigma.1 := by
        intro hsigma
        apply hvalley.1
        letI : IsIso sigma.1 := hsigma
        refine ⟨inv sigma.1 ≫ gamma.1, ?_⟩
        rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
      by_contra hcompat
      push Not at hcompat
      have hbetaSigma : beta.toMorphismFrom ≤ sigma.toMorphismFrom :=
        le_of_not_raySourceIncomparable_of_right_irreducible
          sigma beta hbeta hsigmaIso (by
            simpa [RayHookTackle.LastReplacementCompatible, sigma] using
              hcompat.1)
      have hdeltaSigma : delta.toMorphismFrom ≤ sigma.toMorphismFrom :=
        le_of_not_raySourceIncomparable_of_right_irreducible
          sigma delta hdelta hsigmaIso (by
            simpa [RayHookTackle.LastReplacementCompatible, sigma] using
              hcompat.2)
      exact hno <| exists_isRayPairSupremum_of_common_upper
        beta.toMorphismFrom delta.toMorphismFrom sigma.toMorphismFrom
          hbetaSigma hdeltaSigma

/-- The BGRS 8.5 hook-replacement conclusion for all four figures. -/
theorem RayHookTackle.lastReplacementCompatible_or_of_figure
    [Finite C] [IsFiniteRayCategory C] [IsRayCrownFree C]
    {m : ℕ} (t : RayHookTackle (C := C) m)
    {B D : C}
    (beta : NonzeroHom (t.x (Fin.last m)) B)
    (delta : NonzeroHom (t.x (Fin.last m)) D)
    (hbeta : IsIrreducibleRayMorphism beta.1)
    (hdelta : IsIrreducibleRayMorphism delta.1)
    (hfigure : IsRayThreeArrowFigure beta.toMorphismFrom
      (t.rho (Fin.last m)).toMorphismFrom delta.toMorphismFrom) :
    t.LastReplacementCompatible beta ∨
      t.LastReplacementCompatible delta := by
  rcases hfigure with htop | hsixty
  · obtain ⟨s, hs, hgamma⟩ := htop
    exact t.lastReplacementCompatible_or beta delta hbeta hdelta
      (rayThreeArrowMiddleCondition_of_le_supremum beta
        (t.rho (Fin.last m)) delta s hs hgamma)
  · exact t.lastReplacementCompatible_or_of_no_outer_supremum
      beta delta hbeta hdelta hsixty.2.2

/-- In the fixed-target Figure 60, any common lower bound of the two outer
arrows would create the missing outer infimum.  The dual middle condition is
therefore vacuous, and one cohook replacement is compatible. -/
theorem RayCohookTackle.lastReplacementCompatible_or_of_no_outer_infimum
    [Finite C] [IsFiniteRayCategory C] [IsRayCocrownFree C]
    {m : ℕ} (t : RayCohookTackle (C := C) m)
    {B D : C}
    (beta : NonzeroHom B (t.z (Fin.last m)))
    (delta : NonzeroHom D (t.z (Fin.last m)))
    (hbeta : IsIrreducibleRayMorphism beta.1)
    (hdelta : IsIrreducibleRayMorphism delta.1)
    (hno : ¬∃ s, IsRayPairInfimum beta.toMorphismTo
      delta.toMorphismTo s) :
    t.LastReplacementCompatible beta ∨
      t.LastReplacementCompatible delta := by
  apply t.lastReplacementCompatible_or beta delta hbeta hdelta
  intro u hbetaLower hdeltaLower
  exact (hno <| exists_isRayPairInfimum_of_common_lower
    beta.toMorphismTo delta.toMorphismTo u
      hbetaLower hdeltaLower).elim

/-- The cohook-dual BGRS 8.5 compatibility conclusion for all four
fixed-target figures. -/
theorem RayCohookTackle.lastReplacementCompatible_or_of_figure
    [Finite C] [IsFiniteRayCategory C] [IsRayCocrownFree C]
    {m : ℕ} (t : RayCohookTackle (C := C) m)
    {B D : C}
    (beta : NonzeroHom B (t.z (Fin.last m)))
    (delta : NonzeroHom D (t.z (Fin.last m)))
    (hbeta : IsIrreducibleRayMorphism beta.1)
    (hdelta : IsIrreducibleRayMorphism delta.1)
    (hfigure : IsRayCoThreeArrowFigure beta.toMorphismTo
      (t.sigma (Fin.last m)).toMorphismTo delta.toMorphismTo) :
    t.LastReplacementCompatible beta ∨
      t.LastReplacementCompatible delta := by
  rcases hfigure with hbottom | hsixty
  · obtain ⟨s, hs, hgamma⟩ := hbottom
    exact t.lastReplacementCompatible_or beta delta hbeta hdelta
      (rayCoThreeArrowMiddleCondition_of_infimum_le beta
        (t.sigma (Fin.last m)) delta s hs hgamma)
  · exact t.lastReplacementCompatible_or_of_no_outer_infimum
      beta delta hbeta hdelta hsixty.2.2

end LargeIndecomposable
