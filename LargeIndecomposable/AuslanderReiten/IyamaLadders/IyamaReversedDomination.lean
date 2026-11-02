module

public import LargeIndecomposable.AuslanderReiten.IyamaLadders.IyamaLeftLadderPropagation
public import LargeIndecomposable.AuslanderReiten.IyamaLadders.IyamaLeftLadderIteration
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import LargeIndecomposable.AuslanderReiten.TauCategories.FiniteTauCategory
public import LargeIndecomposable.AuslanderReiten.IyamaLadders.IyamaLadderRadical
public import LargeIndecomposable.Foundations.CategoryTheory.SplitMorphismComplement
public import LargeIndecomposable.AuslanderReiten.IyamaLadders.IyamaRightLadderIteration
public import LargeIndecomposable.AuslanderReiten.IyamaLadders.IyamaRightLadderPropagation

set_option backward.isDefEq.respectTransparency.types false

/-!
# Reversed domination and finite comparison propagation

This is the explicit triangular-matrix step used when a finite left ladder is
read backwards against a right ladder.  It is entirely categorical: no
concrete algebra or module classification is involved.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace LargeIndecomposable.Iyama.TauSequenceComparison

open CategoricalRadical

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

omit [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- The composite of two explicitly split-monic morphisms is split monic. -/
theorem isSplitMono_comp_of_isSplitMono
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsSplitMono f) (hg : IsSplitMono g) :
    IsSplitMono (f ≫ g) := by
  letI : IsSplitMono f := hf
  letI : IsSplitMono g := hg
  apply IsSplitMono.mk'
  exact
    (Classical.choice (IsSplitMono.exists_splitMono (f := f))).comp
      (Classical.choice (IsSplitMono.exists_splitMono (f := g)))

/-! ## Global reversed propagation -/

/-- A right-ladder prefix whose indexing has already been reversed, so its
rung `i` runs from the arrow at `i.castSucc` to the arrow at `i.succ`.
This removes all subtraction arithmetic from the propagation theorem. -/
structure ReversedRightPrefix
    (T : FiniteTauCategoryData C Ind) (n : ℕ) where
  Z : Fin (n + 1) → C
  Y : Fin (n + 1) → C
  U : Fin (n + 1) → C
  b : ∀ i, Z i ⟶ Y i
  f : ∀ i : Fin n, Y i.castSucc ⟶ Y i.succ
  g : ∀ i : Fin n, Z i.castSucc ⟶ Z i.succ
  h : ∀ i : Fin n, U i.castSucc ⟶ Z i.succ
  comm : ∀ i : Fin n, b i.castSucc ≫ f i = g i ≫ b i.succ
  hzero : ∀ i : Fin n, h i ≫ b i.succ = 0
  meshIso : ∀ i : Fin n, Nonempty
    (T.rightMesh (Y i.succ) ≅
      RightLadder.stepComplex (b i.succ) (b i.castSucc)
        (f i) (g i) (h i) (comm i) (hzero i))

def ReversedRightPrefix.paddedArrow
    {T : FiniteTauCategoryData C Ind} {n : ℕ}
    (R : ReversedRightPrefix T n) (i : Fin (n + 1)) :
    R.Z i ⊞ R.U i ⟶ R.Y i :=
  biprod.desc (R.b i) 0

/-- A chosen split-monic piece of the complementary object at the reversed
boundary.  Taking a chosen indecomposable summand here is sufficient for the
comparison and avoids any indecomposability hypothesis on the whole
complement. -/
structure BoundaryEmbedding
    {T : FiniteTauCategoryData C Ind} {n : ℕ}
    (R : ReversedRightPrefix T n) (U₀ : C) where
  hom : U₀ ⟶ R.U 0
  isSplitMono : IsSplitMono hom

/-- The original whole-boundary comparison is the identity special case. -/
def BoundaryEmbedding.identity
    {T : FiniteTauCategoryData C Ind} {n : ℕ}
    (R : ReversedRightPrefix T n) : BoundaryEmbedding R (R.U 0) where
  hom := 𝟙 _
  isSplitMono := inferInstance

/-- The split-monic comparison state along an aligned reversed prefix. -/
def DiagonalComparisonAt
    {T : FiniteTauCategoryData C Ind} {U₀ : C} {n : ℕ}
    (R : ReversedRightPrefix T n)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T U₀ n)
    (i : Fin (n + 1)) : Prop :=
  ∃ q : Arrow.mk (L.b i) ⟶ Arrow.mk (R.paddedArrow i),
    IsSplitMono q.left ∧ IsSplitMono q.right

/-- A split-monic boundary piece gives the first diagonal comparison
square. -/
theorem diagonalComparisonAt_zero_of_boundaryEmbedding
    {T : FiniteTauCategoryData C Ind} {U₀ : C} {n : ℕ}
    (R : ReversedRightPrefix T n)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T U₀ n)
    (E : BoundaryEmbedding R U₀) :
    DiagonalComparisonAt R L 0 := by
  let source : L.Y 0 ⟶ R.Z 0 ⊞ R.U 0 :=
    L.initialSourceIso.inv ≫ E.hom ≫ biprod.inr
  let target : L.Z 0 ⟶ R.Y 0 := 0
  have hcomm : source ≫ R.paddedArrow 0 = L.b 0 ≫ target := by
    simp [source, target, ReversedRightPrefix.paddedArrow, Category.assoc]
  let q : Arrow.mk (L.b 0) ⟶ Arrow.mk (R.paddedArrow 0) :=
    { left := source
      right := target
      w := hcomm }
  have hsource : IsSplitMono source := by
    dsimp only [source]
    have hfirst : IsSplitMono (L.initialSourceIso.inv ≫ E.hom) :=
      isSplitMono_comp_of_isSplitMono L.initialSourceIso.inv E.hom
        (by infer_instance) E.isSplitMono
    simpa only [Category.assoc] using
      (isSplitMono_comp_of_isSplitMono
        (L.initialSourceIso.inv ≫ E.hom)
        (biprod.inr : R.U 0 ⟶ R.Z 0 ⊞ R.U 0)
        hfirst (by infer_instance))
  have htarget : IsSplitMono target := by
    apply IsSplitMono.mk'
    exact
      { retraction := 0
        id := L.initialTargetZero.eq_of_src _ _ }
  exact ⟨q, hsource, htarget⟩

/-- The zero boundary gives the first diagonal comparison square when the
whole complementary object is used. -/
theorem diagonalComparisonAt_zero
    {T : FiniteTauCategoryData C Ind} {n : ℕ}
    (R : ReversedRightPrefix T n)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T (R.U 0) n) :
    DiagonalComparisonAt R L 0 :=
  diagonalComparisonAt_zero_of_boundaryEmbedding R L
    (BoundaryEmbedding.identity R)

/-! ## The terminal four-cycle -/

/-- The literal inclusion of a right-ladder essential arrow into its
zero-padded arrow. -/
def ReversedRightPrefix.essentialToPaddedSquare
    {T : FiniteTauCategoryData C Ind} {n : ℕ}
    (R : ReversedRightPrefix T n) (i : Fin (n + 1)) :
    Arrow.mk (R.b i) ⟶ Arrow.mk (R.paddedArrow i) :=
  { left := biprod.inl
    right := 𝟙 _
    w := by
      change biprod.inl ≫ biprod.desc (R.b i) 0 = R.b i ≫ 𝟙 _
      rw [biprod.inl_desc, Category.comp_id] }

/-- Both components of the right zero-padding square are split monic. -/
theorem ReversedRightPrefix.essentialToPaddedSquare_components
    {T : FiniteTauCategoryData C Ind} {n : ℕ}
    (R : ReversedRightPrefix T n) (i : Fin (n + 1)) :
    IsSplitMono (R.essentialToPaddedSquare i).left ∧
      IsSplitMono (R.essentialToPaddedSquare i).right := by
  constructor
  · change IsSplitMono
      (biprod.inl : R.Z i ⟶ R.Z i ⊞ R.U i)
    infer_instance
  · change IsSplitMono (𝟙 (R.Y i))
    infer_instance

/-- The literal inclusion of a left-ladder essential arrow into its
zero-padded arrow. -/
def leftEssentialToPaddedSquare
    {T : FiniteTauCategoryData C Ind} {U₀ : C} {n : ℕ}
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T U₀ n)
    (i : Fin (n + 1)) :
    Arrow.mk (L.b i) ⟶ Arrow.mk (L.paddedArrow i) :=
  { left := 𝟙 _
    right := biprod.inl
    w := by
      change 𝟙 _ ≫ biprod.lift (L.b i) 0 = L.b i ≫ biprod.inl
      rw [Category.id_comp]
      apply biprod.hom_ext <;> simp }

/-- Both components of the left zero-padding square are split monic. -/
theorem leftEssentialToPaddedSquare_components
    {T : FiniteTauCategoryData C Ind} {U₀ : C} {n : ℕ}
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T U₀ n)
    (i : Fin (n + 1)) :
    IsSplitMono (leftEssentialToPaddedSquare L i).left ∧
      IsSplitMono (leftEssentialToPaddedSquare L i).right := by
  constructor
  · change IsSplitMono (𝟙 (L.Y i))
    infer_instance
  · change IsSplitMono
      (biprod.inl : L.Z i ⟶ L.Z i ⊞ L.U i)
    infer_instance

/-- The middle edge of the domination chain produced by one reversed rung:
the previous essential right arrow contains the next padded left arrow. -/
def CrossComparisonAt
    {T : FiniteTauCategoryData C Ind} {n : ℕ}
    (R : ReversedRightPrefix T n)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T (R.U 0) n)
    (i : Fin n) : Prop :=
  ∃ q : Arrow.mk (L.paddedArrow i.succ) ⟶ Arrow.mk (R.b i.succ),
    IsSplitMono q.left ∧ IsSplitMono q.right

omit [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- Two split-monic arrow squares in opposite directions are inverse up to
arrow isomorphism when endomorphisms of the receiving endpoints are directly
finite. -/
theorem nonempty_arrow_iso_of_mutual_splitMono_squares
    (hfinite : ∀ (X : C) (e : X ⟶ X), IsSplitMono e → IsIso e)
    {Xa Ya Xb Yb : C} {a : Xa ⟶ Ya} {b : Xb ⟶ Yb}
    (d : Arrow.mk b ⟶ Arrow.mk a)
    (hdleft : IsSplitMono d.left) (hdright : IsSplitMono d.right)
    (e : Arrow.mk a ⟶ Arrow.mk b)
    (heleft : IsSplitMono e.left) (heright : IsSplitMono e.right) :
    Nonempty (Arrow.mk a ≅ Arrow.mk b) := by
  letI : IsSplitMono d.left := hdleft
  letI : IsSplitMono d.right := hdright
  letI : IsSplitMono e.left := heleft
  letI : IsSplitMono e.right := heright
  have hleftCompSplit : IsSplitMono (e.left ≫ d.left) := inferInstance
  have hrightCompSplit : IsSplitMono (e.right ≫ d.right) := inferInstance
  haveI hleftCompIso : IsIso (e.left ≫ d.left) :=
    hfinite Xa _ hleftCompSplit
  haveI hrightCompIso : IsIso (e.right ≫ d.right) :=
    hfinite Ya _ hrightCompSplit
  have hdleftEpi : IsSplitEpi d.left := by
    apply IsSplitEpi.mk'
    exact
      { section_ := inv (e.left ≫ d.left) ≫ e.left
        id := by rw [Category.assoc, IsIso.inv_hom_id] }
  have hdrightEpi : IsSplitEpi d.right := by
    apply IsSplitEpi.mk'
    exact
      { section_ := inv (e.right ≫ d.right) ≫ e.right
        id := by rw [Category.assoc, IsIso.inv_hom_id] }
  letI : IsSplitEpi d.left := hdleftEpi
  letI : IsSplitEpi d.right := hdrightEpi
  have hdleftIso : IsIso d.left :=
    isIso_of_mono_of_isSplitEpi d.left
  have hdrightIso : IsIso d.right :=
    isIso_of_mono_of_isSplitEpi d.right
  letI : IsIso d.left := hdleftIso
  letI : IsIso d.right := hdrightIso
  have hdIso : IsIso d :=
    Arrow.isIso_of_isIso_left_of_isIso_right d
  letI : IsIso d := hdIso
  exact ⟨(asIso d).symm⟩

omit [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- The forward square itself is componentwise invertible under the same
mutual-domination and direct-finiteness hypotheses. -/
theorem isIso_components_of_mutual_splitMono_squares
    (hfinite : ∀ (X : C) (f : X ⟶ X), IsSplitMono f → IsIso f)
    {Xa Ya Xb Yb : C} {a : Xa ⟶ Ya} {b : Xb ⟶ Yb}
    (d : Arrow.mk b ⟶ Arrow.mk a)
    (hdleft : IsSplitMono d.left) (hdright : IsSplitMono d.right)
    (e : Arrow.mk a ⟶ Arrow.mk b)
    (heleft : IsSplitMono e.left) (heright : IsSplitMono e.right) :
    IsIso d.left ∧ IsIso d.right := by
  letI : IsSplitMono d.left := hdleft
  letI : IsSplitMono d.right := hdright
  letI : IsSplitMono e.left := heleft
  letI : IsSplitMono e.right := heright
  have hleftCompSplit : IsSplitMono (e.left ≫ d.left) := inferInstance
  have hrightCompSplit : IsSplitMono (e.right ≫ d.right) := inferInstance
  haveI hleftCompIso : IsIso (e.left ≫ d.left) :=
    hfinite Xa _ hleftCompSplit
  haveI hrightCompIso : IsIso (e.right ≫ d.right) :=
    hfinite Ya _ hrightCompSplit
  have hdleftEpi : IsSplitEpi d.left := by
    apply IsSplitEpi.mk'
    exact
      { section_ := inv (e.left ≫ d.left) ≫ e.left
        id := by rw [Category.assoc, IsIso.inv_hom_id] }
  have hdrightEpi : IsSplitEpi d.right := by
    apply IsSplitEpi.mk'
    exact
      { section_ := inv (e.right ≫ d.right) ≫ e.right
        id := by rw [Category.assoc, IsIso.inv_hom_id] }
  letI : IsSplitEpi d.left := hdleftEpi
  letI : IsSplitEpi d.right := hdrightEpi
  exact ⟨isIso_of_mono_of_isSplitEpi d.left,
    isIso_of_mono_of_isSplitEpi d.right⟩

omit [HasFiniteBiproducts C] [IsIdempotentComplete C] in
/-- In an invertible biproduct matrix with zero upper-left block, the
upper-right block is split epic.  Its section is the lower-left block of the
inverse matrix. -/
theorem isSplitEpi_biprod_inr_comp_fst_of_isIso
    {A B D E : C} (m : A ⊞ B ⟶ D ⊞ E) (hm : IsIso m)
    (hzero :
      (biprod.inl : A ⟶ A ⊞ B) ≫ m ≫
        (biprod.fst : D ⊞ E ⟶ D) = 0) :
    IsSplitEpi
      ((biprod.inr : B ⟶ A ⊞ B) ≫ m ≫
        (biprod.fst : D ⊞ E ⟶ D)) := by
  letI : IsIso m := hm
  apply IsSplitEpi.mk'
  let s : D ⟶ B :=
    (biprod.inl : D ⟶ D ⊞ E) ≫ inv m ≫ biprod.snd
  refine { section_ := s, id := ?_ }
  have hfirst :
      (biprod.inl : D ⟶ D ⊞ E) ≫ inv m ≫
          (biprod.fst : A ⊞ B ⟶ A) ≫ biprod.inl ≫ m ≫
            (biprod.fst : D ⊞ E ⟶ D) = 0 := by
    rw [hzero, comp_zero, comp_zero, comp_zero]
  calc
    s ≫ biprod.inr ≫ m ≫ biprod.fst =
        0 + s ≫ biprod.inr ≫ m ≫ biprod.fst := by simp
    _ =
        (biprod.inl : D ⟶ D ⊞ E) ≫ inv m ≫
            (biprod.fst : A ⊞ B ⟶ A) ≫ biprod.inl ≫ m ≫
              (biprod.fst : D ⊞ E ⟶ D) +
          s ≫ biprod.inr ≫ m ≫ biprod.fst := by rw [hfirst]
    _ =
        (biprod.inl : D ⟶ D ⊞ E) ≫ inv m ≫
          ((biprod.fst : A ⊞ B ⟶ A) ≫ biprod.inl +
            (biprod.snd : A ⊞ B ⟶ B) ≫ biprod.inr) ≫
              m ≫ (biprod.fst : D ⊞ E ⟶ D) := by
        simp only [s, Preadditive.comp_add, Preadditive.add_comp,
          Category.assoc]
    _ =
        (biprod.inl : D ⟶ D ⊞ E) ≫ inv m ≫
          𝟙 (A ⊞ B) ≫ m ≫
            (biprod.fst : D ⊞ E ⟶ D) := by rw [biprod.total]
    _ = 𝟙 D := by simp

omit [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- Four split-monic arrow squares which close to a cycle make every edge an
arrow isomorphism under direct finiteness. -/
theorem nonempty_adjacent_arrow_isos_of_splitMono_four_cycle
    (hfinite : ∀ (X : C) (e : X ⟶ X), IsSplitMono e → IsIso e)
    {X₀ Y₀ X₁ Y₁ X₂ Y₂ X₃ Y₃ : C}
    {a₀ : X₀ ⟶ Y₀} {a₁ : X₁ ⟶ Y₁}
    {a₂ : X₂ ⟶ Y₂} {a₃ : X₃ ⟶ Y₃}
    (q₀₁ : Arrow.mk a₁ ⟶ Arrow.mk a₀)
    (h₀₁l : IsSplitMono q₀₁.left)
    (h₀₁r : IsSplitMono q₀₁.right)
    (q₁₂ : Arrow.mk a₂ ⟶ Arrow.mk a₁)
    (h₁₂l : IsSplitMono q₁₂.left)
    (h₁₂r : IsSplitMono q₁₂.right)
    (q₂₃ : Arrow.mk a₃ ⟶ Arrow.mk a₂)
    (h₂₃l : IsSplitMono q₂₃.left)
    (h₂₃r : IsSplitMono q₂₃.right)
    (q₃₀ : Arrow.mk a₀ ⟶ Arrow.mk a₃)
    (h₃₀l : IsSplitMono q₃₀.left)
    (h₃₀r : IsSplitMono q₃₀.right) :
    Nonempty (Arrow.mk a₀ ≅ Arrow.mk a₁) ∧
      Nonempty (Arrow.mk a₁ ≅ Arrow.mk a₂) ∧
      Nonempty (Arrow.mk a₂ ≅ Arrow.mk a₃) ∧
      Nonempty (Arrow.mk a₃ ≅ Arrow.mk a₀) := by
  have hcomp₁₀l : IsSplitMono
      (q₃₀.left ≫ q₂₃.left ≫ q₁₂.left) := by
    exact isSplitMono_comp_of_isSplitMono _ _
      h₃₀l (isSplitMono_comp_of_isSplitMono _ _ h₂₃l h₁₂l)
  have hcomp₁₀r : IsSplitMono
      (q₃₀.right ≫ q₂₃.right ≫ q₁₂.right) := by
    exact isSplitMono_comp_of_isSplitMono _ _
      h₃₀r (isSplitMono_comp_of_isSplitMono _ _ h₂₃r h₁₂r)
  have hcomp₂₁l : IsSplitMono
      (q₀₁.left ≫ q₃₀.left ≫ q₂₃.left) := by
    exact isSplitMono_comp_of_isSplitMono _ _
      h₀₁l (isSplitMono_comp_of_isSplitMono _ _ h₃₀l h₂₃l)
  have hcomp₂₁r : IsSplitMono
      (q₀₁.right ≫ q₃₀.right ≫ q₂₃.right) := by
    exact isSplitMono_comp_of_isSplitMono _ _
      h₀₁r (isSplitMono_comp_of_isSplitMono _ _ h₃₀r h₂₃r)
  have hcomp₃₂l : IsSplitMono
      (q₁₂.left ≫ q₀₁.left ≫ q₃₀.left) := by
    exact isSplitMono_comp_of_isSplitMono _ _
      h₁₂l (isSplitMono_comp_of_isSplitMono _ _ h₀₁l h₃₀l)
  have hcomp₃₂r : IsSplitMono
      (q₁₂.right ≫ q₀₁.right ≫ q₃₀.right) := by
    exact isSplitMono_comp_of_isSplitMono _ _
      h₁₂r (isSplitMono_comp_of_isSplitMono _ _ h₀₁r h₃₀r)
  have hcomp₀₃l : IsSplitMono
      (q₂₃.left ≫ q₁₂.left ≫ q₀₁.left) := by
    exact isSplitMono_comp_of_isSplitMono _ _
      h₂₃l (isSplitMono_comp_of_isSplitMono _ _ h₁₂l h₀₁l)
  have hcomp₀₃r : IsSplitMono
      (q₂₃.right ≫ q₁₂.right ≫ q₀₁.right) := by
    exact isSplitMono_comp_of_isSplitMono _ _
      h₂₃r (isSplitMono_comp_of_isSplitMono _ _ h₁₂r h₀₁r)
  let q₁₀ : Arrow.mk a₀ ⟶ Arrow.mk a₁ :=
    q₃₀ ≫ q₂₃ ≫ q₁₂
  let q₂₁ : Arrow.mk a₁ ⟶ Arrow.mk a₂ :=
    q₀₁ ≫ q₃₀ ≫ q₂₃
  let q₃₂ : Arrow.mk a₂ ⟶ Arrow.mk a₃ :=
    q₁₂ ≫ q₀₁ ≫ q₃₀
  let q₀₃ : Arrow.mk a₃ ⟶ Arrow.mk a₀ :=
    q₂₃ ≫ q₁₂ ≫ q₀₁
  refine ⟨
    nonempty_arrow_iso_of_mutual_splitMono_squares hfinite
      q₀₁ h₀₁l h₀₁r q₁₀ hcomp₁₀l hcomp₁₀r,
    nonempty_arrow_iso_of_mutual_splitMono_squares hfinite
      q₁₂ h₁₂l h₁₂r q₂₁ hcomp₂₁l hcomp₂₁r,
    nonempty_arrow_iso_of_mutual_splitMono_squares hfinite
      q₂₃ h₂₃l h₂₃r q₃₂ hcomp₃₂l hcomp₃₂r,
    nonempty_arrow_iso_of_mutual_splitMono_squares hfinite
      q₃₀ h₃₀l h₃₀r q₀₃ hcomp₀₃l hcomp₀₃r⟩

end LargeIndecomposable.Iyama.TauSequenceComparison
