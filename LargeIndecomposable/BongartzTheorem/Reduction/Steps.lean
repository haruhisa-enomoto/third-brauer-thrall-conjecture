module

public import LargeIndecomposable.BongartzTheorem.Reduction.DataForm
public import LargeIndecomposable.Coverings.UniversalCover.PairData
public import LargeIndecomposable.FundamentalGroups.Basic.SmallFree
public import LargeIndecomposable.MultiplicativeBases.Twisted.TwistBridge
public import LargeIndecomposable.Crowns.Basic.CrownReduction
public import LargeIndecomposable.MultiplicativeBases.Twisted.MulBasisQuot
public import LargeIndecomposable.MultiplicativeBases.Twisted.MulBasisStd

/-!
# Bongartz's Theorem 6 from its remaining nodes

`BongartzDistributive` follows from three statements about the small model
`P` of the ray category of a distributive minimal representation-infinite
algebra `B` (`bongartzDistributive_of_nodes`):

* `StandardnessNode`: `B ≅ k(P)`;
* `CrownNode`: if `P` is not chain-bounded, its fundamental group is
  free (the chain-bounded case is Fischbacher's theorem, proved in
  `FundamentalGroups/Basic/FreePi.lean`);
* `DichotomyNode`: given `B ≅ k(P)` and a torsion-free fundamental
  group, a finite convex piece of the universal cover carries a Kronecker pair
  respecting the relations of the cover, or `B` has a monomial band.

The covering data are then built by `RayCat.pairCoveringData`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Statement RayCat RayCat.Cover RayQuiver Covering

universe u

/-- The algebra is the linearization of (the small model of) its ray
category. -/
def StandardnessNode : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B] [Algebra k B]
    [FiniteDimensional k B] (ι : Type) [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι),
    IsMinimalRepInfinite B → ∀ hd : IsDistribIdeals B,
      letI := S.distribHomStructure hd
      letI := S.locallySmall hd
      letI := S.isRayCategory hd
      letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
      letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
      Nonempty (Linearization (RaySmall.{0} S.toIdempotents.RayCategory) k ≃ₐ[k] B)

/-- The crown case of BO13a Theorem 2 b). -/
def CrownNode : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B] [Algebra k B]
    [FiniteDimensional k B] (ι : Type) [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι),
    IsMinimalRepInfinite B → ∀ hd : IsDistribIdeals B,
      letI := S.distribHomStructure hd
      letI := S.locallySmall hd
      ¬ChainBounded S.toIdempotents.RayCategory →
        ∀ X : FundGroupoid (RaySmall.{0} S.toIdempotents.RayCategory), IsFreeGroup (End X)

/-- The dichotomy on the universal cover. -/
def DichotomyNode : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B] [Algebra k B]
    [FiniteDimensional k B] (ι : Type) [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι),
    IsMinimalRepInfinite B → ∀ hd : IsDistribIdeals B,
      letI := S.distribHomStructure hd
      letI := S.locallySmall hd
      letI := S.isRayCategory hd
      letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
      letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
      ∀ (_ : Linearization (RaySmall.{0} S.toIdempotents.RayCategory) k ≃ₐ[k] B)
        (x₀ : RaySmall.{0} S.toIdempotents.RayCategory),
        (∀ g : Pi1 x₀, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1) →
          (∃ (Sp : Finset (Cover x₀)) (_ : Convex (Sp : Set (Cover x₀)))
            (K : KroneckerPair k (pieceQuiver Sp)),
            (∀ i, Nontrivial (K.P.obj i) ∨ Nontrivial (K.Q₀.obj i)) ∧
              RespectsCover (K.functor.obj (SminusK k)) ∧ RespectsCover (K.functor.obj (P1K k))) ∨
          Nonempty (Walk.MonomialBand k B)

/-- A minimal representation-infinite split basic algebra has at least one
primitive idempotent. -/
lemma SplitBasicData.nonempty_of_minimal {k : Type u} [Field k] {B : Type u} [Ring B]
    [Algebra k B] {ι : Type} [Fintype ι] (S : SplitBasicData k B ι) (hB : IsMinimalRepInfinite B) :
    Nonempty ι := by
  by_contra h
  rw [not_nonempty_iff] at h
  have h1 : (1 : B) = 0 := by
    rw [← S.complete.complete]
    exact Finset.sum_of_isEmpty _
  have : Subsingleton B := subsingleton_of_zero_eq_one h1.symm
  refine hB.1 ⟨0, Fin.elim0, fun M _ _ _ hM ↦ absurd hM.1 ?_⟩
  intro hnt
  obtain ⟨x, y, hxy⟩ := hnt
  apply hxy
  rw [← one_smul B x, ← one_smul B y, h1, zero_smul, zero_smul]

/-- **Bongartz's Theorem 6 (data form) from its remaining nodes.** -/
theorem bongartzDistributive_of_nodes (hStd : StandardnessNode.{u}) (hCrown : CrownNode.{u})
    (hDich : DichotomyNode.{u}) : BongartzDistributive.{u} := by
  intro k _ _ B _ _ _ ι _ S hB hd
  classical
  have hι := S.nonempty_of_minimal hB
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isRayCategory hd
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  obtain ⟨e⟩ := hStd k B ι S hB hd
  let x₀ : RaySmall.{0} S.toIdempotents.RayCategory :=
    ⟨⟨S.toIdempotents.projectiveVertexEquiv.symm (Classical.arbitrary ι)⟩⟩
  have hfree : ∀ X : FundGroupoid (RaySmall.{0} S.toIdempotents.RayCategory), IsFreeGroup (End X) := by
    by_cases hCB : ChainBounded S.toIdempotents.RayCategory
    · exact S.small_isFreeGroup_end hd hB hCB
    · exact hCrown k B ι S hB hd hCB
  have htf : ∀ g : Pi1 x₀, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1 := fun g hg n hn ↦
    aut_pow_ne_one_of_isFreeGroup_end _ (hfree _) g hg n hn
  rcases hDich k B ι S hB hd e x₀ htf with ⟨Sp, hS, K, hsupp, h₁, h₂⟩ | hband
  · exact Or.inl ⟨pairCoveringData e htf Sp hS K hsupp h₁ h₂⟩
  · exact Or.inr hband

/-- The algebra is a twisted linearization of (the small model of) its
ray category, the twist coming from a contour function (BGRS multiplicative
bases; Gabriel–Roiter 13.17 a)). -/
def TwistNode : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B] [Algebra k B]
    [FiniteDimensional k B] (ι : Type) [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι),
    IsMinimalRepInfinite B → ∀ hd : IsDistribIdeals B,
      letI := S.distribHomStructure hd
      letI := S.locallySmall hd
      letI := S.isRayCategory hd
      letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
      letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
      ∃ C : ContourFn (RaySmall.{0} S.toIdempotents.RayCategory) (Additive kˣ),
        Nonempty (TwistedLin (RaySmall.{0} S.toIdempotents.RayCategory) k (twistOf k C) ≃ₐ[k] B)

/-- Crown case: contour functions are exact (BO13a, proof of
Theorem 2, via Proposition 2 and the §3.1 lemma). -/
def CrownH2Node : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B] [Algebra k B]
    [FiniteDimensional k B] (ι : Type) [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι),
    IsMinimalRepInfinite B → ∀ hd : IsDistribIdeals B,
      letI := S.distribHomStructure hd
      letI := S.locallySmall hd
      letI := S.isRayCategory hd
      ¬ChainBounded S.toIdempotents.RayCategory →
        ∀ C : ContourFn (RaySmall.{0} S.toIdempotents.RayCategory) (Additive kˣ), C.Exact

/-- Standardness from the twist node: in the chain-bounded case by Roiter's
theorem, in the crown case by `CrownH2Node`. -/
theorem standardnessNode_of (hT : TwistNode.{u}) (hC : CrownH2Node.{u}) :
    StandardnessNode.{u} := by
  intro k _ _ B _ _ _ ι _ _ S hB hd
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isRayCategory hd
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  have := S.isFiniteRayCategory hd
  obtain ⟨C, ⟨e⟩⟩ := hT k B ι S hB hd
  by_cases hCB : ChainBounded S.toIdempotents.RayCategory
  · obtain ⟨e'⟩ := twistedLinEquiv_of_chainBounded k (RaySmall.leftCancel (S.leftCancel hd))
      (RaySmall.rightCancel (S.rightCancel hd)) (RaySmall.chainBounded hCB) C
    exact ⟨e'.symm.trans e⟩
  · obtain ⟨e'⟩ := twistedLinEquiv_of_exact k C (hC k B ι S hB hd hCB C)
    exact ⟨e'.symm.trans e⟩

/-- **Bongartz's Theorem 6 (data form)** from the remaining nodes: the BGRS
twist, the crown case (contour functions and fundamental group), and the
dichotomy on the universal cover. -/
theorem bongartzDistributive_of_nodes' (hT : TwistNode.{u}) (hH : CrownH2Node.{u})
    (hCrown : CrownNode.{u}) (hDich : DichotomyNode.{u}) : BongartzDistributive.{u} :=
  bongartzDistributive_of_nodes (standardnessNode_of hT hH) hCrown hDich

/-- Crown case with a long morphism: the fundamental group is free. -/
def CrownLongNode : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B] [Algebra k B]
    [FiniteDimensional k B] (ι : Type) [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι),
    IsMinimalRepInfinite B → ∀ hd : IsDistribIdeals B,
      letI := S.distribHomStructure hd
      letI := S.locallySmall hd
      ¬ChainBounded S.toIdempotents.RayCategory → HasLong (RaySmall.{0} S.toIdempotents.RayCategory) →
        ∀ X : FundGroupoid (RaySmall.{0} S.toIdempotents.RayCategory), IsFreeGroup (End X)

/-- Crown case with a long morphism: contour functions are exact. -/
def CrownLongH2Node : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B] [Algebra k B]
    [FiniteDimensional k B] (ι : Type) [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι),
    IsMinimalRepInfinite B → ∀ hd : IsDistribIdeals B,
      letI := S.distribHomStructure hd
      letI := S.locallySmall hd
      letI := S.isRayCategory hd
      ¬ChainBounded S.toIdempotents.RayCategory → HasLong (RaySmall.{0} S.toIdempotents.RayCategory) →
        ∀ C : ContourFn (RaySmall.{0} S.toIdempotents.RayCategory) (Additive kˣ), C.Exact

attribute [local instance] isRayCategory_of_finiteRayCategory in
/-- Without long morphisms the crown case is the base case. -/
theorem crownNode_of (h : CrownLongNode.{u}) : CrownNode.{u} := by
  intro k _ _ B _ _ _ ι _ _ S hB hd
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  have := S.isFiniteRayCategory hd
  intro hCB X
  by_cases hL : HasLong (RaySmall.{0} S.toIdempotents.RayCategory)
  · exact h k B ι S hB hd hCB hL X
  · have hι := S.nonempty_of_minimal hB
    have : Nonempty (RaySmall.{0} S.toIdempotents.RayCategory) :=
      ⟨⟨⟨S.toIdempotents.projectiveVertexEquiv.symm (Classical.arbitrary ι)⟩⟩⟩
    have hcon : IsConnected (FundGroupoid (RaySmall.{0} S.toIdempotents.RayCategory)) :=
      isConnected_fund_of_nzConnected fun x y ↦ RaySmall.nzConnected
        (S.nzConnected hd (fun e he hc ↦ hB.central_idempotent e he hc) x.as y.as)
    have : IsConnected (Quiver.FreeGroupoid (RayVert (RaySmall.{0} S.toIdempotents.RayCategory))) :=
      isConnected_of_quotient homotopy
    exact isFreeGroup_end_of_noEss (noEssContour_of_not_hasLong hL) X.as

attribute [local instance] isRayCategory_of_finiteRayCategory in
/-- Without long morphisms contour functions vanish. -/
theorem crownH2Node_of (h : CrownLongH2Node.{u}) : CrownH2Node.{u} := by
  intro k _ _ B _ _ _ ι _ _ S hB hd
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isRayCategory hd
  have := S.isFiniteRayCategory hd
  intro hCB C
  by_cases hL : HasLong (RaySmall.{0} S.toIdempotents.RayCategory)
  · exact h k B ι S hB hd hCB hL C
  · exact ⟨fun _ ↦ 0, C.isCoboundary_zero_of_noEss (noEssContour_of_not_hasLong hL)⟩

/-- **Bongartz's Theorem 6 (data form)** from the BGRS twist node, the crown
case with a long morphism (fundamental group and contour functions), and the
dichotomy on the universal cover. -/
theorem bongartzDistributive_of_nodes'' (hT : TwistNode.{u}) (hH : CrownLongH2Node.{u})
    (hCrown : CrownLongNode.{u}) (hDich : DichotomyNode.{u}) : BongartzDistributive.{u} :=
  bongartzDistributive_of_nodes' hT (crownH2Node_of hH) (crownNode_of hCrown) hDich

/-- BO13a Proposition 2 (with the crown-freeness of `P/μ` used in the proof of
its Theorem 2): a crown and a long morphism give a long morphism `μ` that
occurs in no contour, with `P/μ` chain-bounded. -/
def Prop2Node : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B] [Algebra k B]
    [FiniteDimensional k B] (ι : Type) [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι),
    IsMinimalRepInfinite B → ∀ hd : IsDistribIdeals B,
      letI := S.distribHomStructure hd
      letI := S.locallySmall hd
      letI := S.isFiniteRayCategory hd
      letI := isRayCategory_of_finiteRayCategory (C := RaySmall.{0} S.toIdempotents.RayCategory)
      ¬ChainBounded S.toIdempotents.RayCategory → HasLong (RaySmall.{0} S.toIdempotents.RayCategory) →
        ∃ (a b : RaySmall.{0} S.toIdempotents.RayCategory) (μ : a ⟶ b) (_ : ¬IsIso μ)
          (_ : ¬IsIrreducible μ) (_ : μ ≠ 0), IsLongAt μ ∧ NotInContour μ ∧ ChainBounded (Res μ)

attribute [local instance] isRayCategory_of_finiteRayCategory in
theorem crownLongNode_of (h : Prop2Node.{u}) : CrownLongNode.{u} := by
  intro k _ _ B _ _ _ ι _ _ S hB hd
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isFiniteRayCategory hd
  intro hCB hL X
  obtain ⟨a, b, μ, hμ, hμr, hμ0, hlong, hcont, hCB'⟩ := h k B ι S hB hd hCB hL
  have hι := S.nonempty_of_minimal hB
  have : Nonempty (RaySmall.{0} S.toIdempotents.RayCategory) :=
    ⟨⟨⟨S.toIdempotents.projectiveVertexEquiv.symm (Classical.arbitrary ι)⟩⟩⟩
  have hcon : IsConnected (FundGroupoid (RaySmall.{0} S.toIdempotents.RayCategory)) :=
    isConnected_fund_of_nzConnected fun x y ↦ RaySmall.nzConnected
      (S.nzConnected hd (fun e he hc ↦ hB.central_idempotent e he hc) x.as y.as)
  exact isFreeGroup_end_of_residue μ hμ hμr hμ0 hlong hcont
    (RaySmall.leftCancel (S.leftCancel hd)) (RaySmall.rightCancel (S.rightCancel hd)) hCB' hcon X

attribute [local instance] isRayCategory_of_finiteRayCategory in
theorem crownLongH2Node_of (h : Prop2Node.{u}) : CrownLongH2Node.{u} := by
  intro k _ _ B _ _ _ ι _ _ S hB hd
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isRayCategory hd
  letI := S.isFiniteRayCategory hd
  intro hCB hL C
  obtain ⟨a, b, μ, hμ, hμr, hμ0, hlong, hcont, hCB'⟩ := h k B ι S hB hd hCB hL
  exact exact_of_residue μ hμ hμr hμ0 hlong hcont
    (RaySmall.leftCancel (S.leftCancel hd)) (RaySmall.rightCancel (S.rightCancel hd)) hCB' C

/-- **Bongartz's Theorem 6 (data form)** from the BGRS twist node, BO13a
Proposition 2, and the dichotomy on the universal cover. -/
theorem bongartzDistributive_of_prop2 (hT : TwistNode.{u}) (hP2 : Prop2Node.{u})
    (hDich : DichotomyNode.{u}) : BongartzDistributive.{u} :=
  bongartzDistributive_of_nodes'' hT (crownLongH2Node_of hP2) (crownLongNode_of hP2) hDich

/-! ### Nodes in multiplicative-basis form -/

/-- BGRS (Gabriel–Roiter 13.10–13.17): a minimal representation-infinite
distributive algebra has a twisted multiplicative basis over its ray
category. -/
def MulBasisNode : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B] [Algebra k B]
    [FiniteDimensional k B] (ι : Type) [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι),
    IsMinimalRepInfinite B → ∀ hd : IsDistribIdeals B,
      letI := S.distribHomStructure hd
      letI := S.locallySmall hd
      letI := S.isRayCategory hd
      letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
      letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
      Nonempty (RayQuiver.MulBasis k (RaySmall.{0} S.toIdempotents.RayCategory) B)

/-- BO13a Proposition 2: a crown and a long morphism give a long morphism that
occurs in no contour. -/
def LongNotInContourNode : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B] [Algebra k B]
    [FiniteDimensional k B] (ι : Type) [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι),
    IsMinimalRepInfinite B → ∀ hd : IsDistribIdeals B,
      letI := S.distribHomStructure hd
      letI := S.locallySmall hd
      letI := S.isFiniteRayCategory hd
      letI := isRayCategory_of_finiteRayCategory (C := RaySmall.{0} S.toIdempotents.RayCategory)
      ¬ChainBounded S.toIdempotents.RayCategory → HasLong (RaySmall.{0} S.toIdempotents.RayCategory) →
        ∃ (a b : RaySmall.{0} S.toIdempotents.RayCategory) (μ : a ⟶ b) (_ : ¬IsIso μ)
          (_ : ¬IsIrreducible μ) (_ : μ ≠ 0), IsLongAt μ ∧ NotInContour μ

/-- `P/μ` has bounded chains: `B/⟨μ⟩` is representation-finite by minimality
and has a twisted multiplicative basis over `P/μ`. -/
theorem prop2Node_of (hM : MulBasisNode.{u}) (hL : LongNotInContourNode.{u}) : Prop2Node.{u} := by
  intro k _ _ B _ _ _ ι _ _ S hB hd
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isFiniteRayCategory hd
  letI := isRayCategory_of_finiteRayCategory (C := RaySmall.{0} S.toIdempotents.RayCategory)
  intro hCB hL'
  obtain ⟨a, b, μ, hμ, hμr, hμ0, hlong, hcont⟩ := hL k B ι S hB hd hCB hL'
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  obtain ⟨Bm⟩ := hM k B ι S hB hd
  exact ⟨a, b, μ, hμ, hμr, hμ0, hlong, hcont,
    Bm.chainBounded_res hμ (hB.2 _ (RayQuiver.MulBasis.ideal_ne_bot hμ0))⟩

/-- Standardness from a twisted multiplicative basis: its contour function is
exact by Roiter's theorem (no crown) or by `CrownH2Node`. -/
theorem standardnessNode_of_mulBasis (hM : MulBasisNode.{u}) (hC : CrownH2Node.{u}) :
    StandardnessNode.{u} := by
  intro k _ _ B _ _ _ ι _ _ S hB hd
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isRayCategory hd
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  have := S.isFiniteRayCategory hd
  obtain ⟨Bm⟩ := hM k B ι S hB hd
  have hex : Bm.contourFn.Exact := by
    by_cases hCB : ChainBounded S.toIdempotents.RayCategory
    · exact ContourFn.exact_of_chainBounded (Additive kˣ) _ _
        (RaySmall.leftCancel (S.leftCancel hd)) (RaySmall.rightCancel (S.rightCancel hd))
        (RaySmall.chainBounded hCB) le_rfl Bm.contourFn
    · exact hC k B ι S hB hd hCB Bm.contourFn
  obtain ⟨a, ha⟩ := hex
  exact Bm.nonempty_algEquiv ha

/-- **Bongartz's Theorem 6 (data form)** from three nodes: BGRS multiplicative
bases, BO13a Proposition 2, and the dichotomy on the universal cover. -/
theorem bongartzDistributive_of_mulBasis (hM : MulBasisNode.{u}) (hL : LongNotInContourNode.{u})
    (hDich : DichotomyNode.{u}) : BongartzDistributive.{u} :=
  bongartzDistributive_of_nodes
    (standardnessNode_of_mulBasis hM (crownH2Node_of (crownLongH2Node_of (prop2Node_of hM hL))))
    (crownNode_of (crownLongNode_of (prop2Node_of hM hL))) hDich

end LargeIndecomposable
