module

public import LargeIndecomposable.Cleaving.ClosedChains.ClosedZigzag
public import LargeIndecomposable.RayCategories.Distributive.BGRSRayPathLift
public import LargeIndecomposable.RayCategories.Basic.RayMorphismDepth

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasWellDefinedBGRSRayProduct C]
variable [HasFiniteRayPathDepth (BGRSRayCategory C)]

/-- A chosen irreducible-path presentation of a nonzero BGRS ray. -/
def chosenBGRSRayPathPresentation
    {X Y : BGRSRayCategory C} (f : NonzeroHom X Y) :
    RayPathPresentation f.toMorphismFrom :=
  Classical.choice
    (HasFiniteRayPathDepth.presentation_nonempty f.toMorphismFrom)

/-- The ordinary composite attached to a chosen stable irreducible path
presenting `f`.  Its individual irreducible arrows are lifted by the quotient
representatives; the whole composite, rather than `f.1.out`, is the BGRS 3.7
generator. -/
def stableBGRSRayRepresentative
    {X Y : BGRSRayCategory C} (f : NonzeroHom X Y) :
    X.as ⟶ Y.as :=
  BGRSRayArrowLift.quotientOut.pathMap
    (chosenBGRSRayPathPresentation f).path

/-- The selected path really presents the requested ray. -/
theorem rayPathMap_chosenBGRSRayPathPresentation
    {X Y : BGRSRayCategory C} (f : NonzeroHom X Y) :
    rayPathMap (chosenBGRSRayPathPresentation f).path = f.1 :=
  (chosenBGRSRayPathPresentation f).map_eq

/-- BGRS stability in its representative-independent operational form: every
choice of source-category representatives for the irreducible arrows has
nonzero composite along the selected path. -/
theorem chosenBGRSRayPathPresentation_stable
    {X Y : BGRSRayCategory C} (f : NonzeroHom X Y)
    (L : BGRSRayArrowLift (C := C)) :
    L.pathMap (chosenBGRSRayPathPresentation f).path ≠ 0 := by
  apply L.pathMap_ne_zero_of_rayPathMap_ne_zero
  rw [rayPathMap_chosenBGRSRayPathPresentation]
  exact f.2

/-- The ordinary stable-path composite lies in exactly the requested unit
ray. -/
theorem unitRay_stableBGRSRayRepresentative
    {X Y : BGRSRayCategory C} (f : NonzeroHom X Y) :
    unitRay (stableBGRSRayRepresentative f) = f.1 := by
  have hp : rayPathMap (chosenBGRSRayPathPresentation f).path ≠ 0 := by
    rw [rayPathMap_chosenBGRSRayPathPresentation]
    exact f.2
  exact
    (BGRSRayArrowLift.unitRay_pathMap_eq_rayPathMap_of_ne_zero
      (L := BGRSRayArrowLift.quotientOut)
      (chosenBGRSRayPathPresentation f).path hp).trans
        (rayPathMap_chosenBGRSRayPathPresentation f)

/-- In particular, the selected stable-path composite is nonzero. -/
theorem stableBGRSRayRepresentative_ne_zero
    {X Y : BGRSRayCategory C} (f : NonzeroHom X Y) :
    stableBGRSRayRepresentative f ≠ 0 :=
  chosenBGRSRayPathPresentation_stable f
    BGRSRayArrowLift.quotientOut

namespace ClosedZigzag

/-- Stable-path representative of a `rho` ray in a closed chain. -/
def stableChainRhoRepresentative
    (t : RayClosedChain (C := BGRSRayCategory C))
    (i : Fin ((t.length - 1) + 1)) :
    chainVertexObj t (.source i) ⟶ chainVertexObj t (.sink i) :=
  stableBGRSRayRepresentative
    (t.chain.rho (chainIndex t i).castSucc)

/-- Stable-path representative of a non-closing `sigma` ray. -/
def stableChainSigmaRepresentative
    (t : RayClosedChain (C := BGRSRayCategory C))
    (i : Fin (t.length - 1)) :
    chainVertexObj t (.source i.succ) ⟶
      chainVertexObj t (.sink i.castSucc) := by
  let j : Fin t.length := chainSigmaIndex t i
  exact Quiver.homOfEq
    (stableBGRSRayRepresentative (t.chain.sigma j))
    (congrArg (fun q ↦ (t.chain.x q).as) (by
      apply Fin.ext
      rfl))
    (congrArg (fun q ↦ (t.chain.z q).as) (by
      apply Fin.ext
      rfl))

/-- Stable-path representative of the final `sigma`, transported around the
closed-chain identification. -/
def stableChainCloseRepresentative
    (t : RayClosedChain (C := BGRSRayCategory C)) :
    chainVertexObj t (.source 0) ⟶
      chainVertexObj t (.sink (Fin.last (t.length - 1))) := by
  let j : Fin t.length := chainIndex t (Fin.last (t.length - 1))
  exact Quiver.homOfEq
    (stableBGRSRayRepresentative (t.chain.sigma j))
    (calc
      (t.chain.x j.succ).as =
          (t.chain.x (Fin.last t.length)).as := by
        apply congrArg (fun q ↦ (t.chain.x q).as)
        apply Fin.ext
        dsimp [j, chainIndex]
        have := t.length_ge_three
        omega
      _ = (t.chain.x 0).as :=
        (chain_first_source_eq_last_source t).symm
      _ = (t.chain.x (chainIndex t 0).castSucc).as := by
        apply congrArg (fun q ↦ (t.chain.x q).as)
        apply Fin.ext
        rfl)
    (by rfl)

/-- BGRS 3.7's actual generator prefunctor: each generator is the composite
of a stable irreducible path representing the corresponding ray. -/
def stableChainRepresentativePrefunctor
    (t : RayClosedChain (C := BGRSRayCategory C)) :
    Vertex (t.length - 1) ⥤q C where
  obj := chainVertexObj t
  map
    | .rho i => stableChainRhoRepresentative t i
    | .sigma i => stableChainSigmaRepresentative t i
    | .close => stableChainCloseRepresentative t

omit [HasWellDefinedBGRSRayProduct C]
    [HasFiniteRayPathDepth (BGRSRayCategory C)] in
private theorem homOfEq_ne_zero_stable
    {X Y X' Y' : C} (f : X ⟶ Y) (hf : f ≠ 0)
    (hX : X = X') (hY : Y = Y') :
    Quiver.homOfEq f hX hY ≠ 0 := by
  subst hX
  subst hY
  exact hf

/-- Every stable-path chain generator is nonzero, including after endpoint
transport. -/
theorem stableChainRepresentativePrefunctor_map_ne_zero
    (t : RayClosedChain (C := BGRSRayCategory C))
    {a b : Vertex (t.length - 1)} (e : a ⟶ b) :
    (stableChainRepresentativePrefunctor t).map e ≠ 0 := by
  cases e with
  | rho i =>
      exact stableBGRSRayRepresentative_ne_zero
        (t.chain.rho (chainIndex t i).castSucc)
  | sigma i =>
      change stableChainSigmaRepresentative t i ≠ 0
      unfold stableChainSigmaRepresentative
      apply homOfEq_ne_zero_stable
      exact stableBGRSRayRepresentative_ne_zero
        (t.chain.sigma (chainSigmaIndex t i))
  | close =>
      change stableChainCloseRepresentative t ≠ 0
      unfold stableChainCloseRepresentative
      apply homOfEq_ne_zero_stable
      exact stableBGRSRayRepresentative_ne_zero
        (t.chain.sigma
          (chainIndex t (Fin.last (t.length - 1))))

/-- The stable-path replacement has the same objectwise nonzero identities. -/
theorem stableChainVertexObj_id_ne_zero
    (t : RayClosedChain (C := BGRSRayCategory C))
    (a : Vertex (t.length - 1)) :
    𝟙 (chainVertexObj t a) ≠ 0 := by
  cases a with
  | source i =>
      intro hid
      change 𝟙 ((stableChainRepresentativePrefunctor t).obj (.source i)) = 0 at hid
      have hf := stableChainRepresentativePrefunctor_map_ne_zero
        t (.rho i)
      apply hf
      calc
        (stableChainRepresentativePrefunctor t).map (.rho i) =
            𝟙 ((stableChainRepresentativePrefunctor t).obj (.source i)) ≫
              (stableChainRepresentativePrefunctor t).map (.rho i) := by simp
        _ = 0 := by rw [hid]; simp
  | sink i =>
      intro hid
      change 𝟙 ((stableChainRepresentativePrefunctor t).obj (.sink i)) = 0 at hid
      have hf := stableChainRepresentativePrefunctor_map_ne_zero
        t (.rho i)
      apply hf
      calc
        (stableChainRepresentativePrefunctor t).map (.rho i) =
            (stableChainRepresentativePrefunctor t).map (.rho i) ≫
              𝟙 ((stableChainRepresentativePrefunctor t).obj (.sink i)) := by simp
        _ = 0 := by rw [hid]; simp

section Linear

variable {k : Type w} [Field k] [Linear k C]

/-- Linearization of the stable-path closed-chain prefunctor. -/
def stableChainRepresentativeLinearFunctor
    (t : RayClosedChain (C := BGRSRayCategory C)) :
    LinearPathCategory.Category k (Vertex (t.length - 1))ᵒᵖ ⥤ C :=
  LinearPathCategory.lift
    (fun a ↦ chainVertexObj t a.unop)
    (fun {_ _} e ↦ (stableChainRepresentativePrefunctor t).map e.unop)

instance stableChainRepresentativeLinearFunctor_additive
    (t : RayClosedChain (C := BGRSRayCategory C)) :
    (stableChainRepresentativeLinearFunctor (k := k) t).Additive := by
  unfold stableChainRepresentativeLinearFunctor
  infer_instance

instance stableChainRepresentativeLinearFunctor_linear
    (t : RayClosedChain (C := BGRSRayCategory C)) :
    (stableChainRepresentativeLinearFunctor (k := k) t).Linear k := by
  unfold stableChainRepresentativeLinearFunctor
  infer_instance

/-- Every path-basis vector has nonzero image under the stable-path functor. -/
theorem stableChainRepresentativeLinearFunctor_map_pathHom_ne_zero
    (t : RayClosedChain (C := BGRSRayCategory C))
    {x y : LinearPathCategory.Category k
      (Vertex (t.length - 1))ᵒᵖ}
    (p : Quiver.Path (LinearPathCategory.vertex y)
      (LinearPathCategory.vertex x)) :
    (stableChainRepresentativeLinearFunctor (k := k) t).map
        (LinearPathCategory.pathHom p) ≠ 0 := by
  unfold stableChainRepresentativeLinearFunctor
  rw [LinearPathCategory.lift_map_pathHom]
  cases p with
  | nil =>
      simp only [LinearPathCategory.pathMap_nil]
      exact stableChainVertexObj_id_ne_zero t
        (LinearPathCategory.vertex x).unop
  | cons p e =>
      have hp0 := opposite_path_length_zero_before_arrow
        (t.length - 1) p e
      have hstart := p.eq_of_length_zero hp0
      subst_vars
      rw [Quiver.Path.eq_nil_of_length_zero p hp0]
      simp only [LinearPathCategory.pathMap_cons,
        LinearPathCategory.pathMap_nil, Category.comp_id]
      exact stableChainRepresentativePrefunctor_map_ne_zero t e.unop

/-- BGRS 3.4(a) injectivity for the source-faithful stable-path realization. -/
theorem stableChainRepresentativeLinearFunctor_map_injective
    (t : RayClosedChain (C := BGRSRayCategory C))
    (x y : LinearPathCategory.Category k
      (Vertex (t.length - 1))ᵒᵖ) :
    Function.Injective
      ((stableChainRepresentativeLinearFunctor (k := k) t).mapLinearMap k
        (X := x) (Y := y)) := by
  have hn : 2 ≤ t.length - 1 := by
    have := t.length_ge_three
    omega
  letI : Subsingleton
      (Quiver.Path (LinearPathCategory.vertex y)
        (LinearPathCategory.vertex x)) :=
    opposite_path_subsingleton (t.length - 1) hn _ _
  apply LinearMap.injective_of_linearIndependent
    (LinearPathCategory.homPathBasis x y).span_eq
  rw [linearIndependent_subsingleton_index_iff]
  intro p
  change (stableChainRepresentativeLinearFunctor (k := k) t).map
      (LinearPathCategory.homPathBasis x y p) ≠ 0
  rw [LinearPathCategory.homPathBasis_apply]
  exact stableChainRepresentativeLinearFunctor_map_pathHom_ne_zero t p

/-- Faithfulness of the stable-path realization. -/
theorem stableChainRepresentativeLinearFunctorFaithful
    (t : RayClosedChain (C := BGRSRayCategory C)) :
    (stableChainRepresentativeLinearFunctor (k := k) t).Faithful where
  map_injective := by
    intro X Y
    change Function.Injective
      ((stableChainRepresentativeLinearFunctor (k := k) t).mapLinearMap k
        (X := X) (Y := Y))
    exact stableChainRepresentativeLinearFunctor_map_injective t X Y

end Linear

end ClosedZigzag
end LargeIndecomposable
