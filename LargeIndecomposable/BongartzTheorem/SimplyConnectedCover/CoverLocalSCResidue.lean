module

public import LargeIndecomposable.BongartzTheorem.SimplyConnectedCover.CoverLocalSCNoLong

/-!
# Local simple connectivity passes from `P/μ` to `P`

Arrows of the cover of `P/μ` out of the image of an object lift to arrows of the cover of `P`
(`arrow_lift`). An injective quiver map with arrow lifting and reflection of path values pulls
local simple connectivity back (`isCoboundaryOn_of_transfer`); applied to the residue map this
gives `coverLocalSC_of_residue`, and with the chain-bounded and no-long cases,
`coverLocallySimplyConnected`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover

section General

variable {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] [IsRayCategory Q] {q₀ : Q}

/-- **A cover morphism with irreducible value is irreducible.** -/
lemma isIrreducible_of_val {a b : Cover q₀} {f : a ⟶ b} (hf : IsIrreducible (val f)) :
    IsIrreducible f := by
  refine ⟨fun h ↦ hf.1 (by rw [h]; rfl), fun hiso ↦ hf.2.1 (isIso_val f), fun z g h hgh ↦ ?_⟩
  have hv : val f = val g ≫ val h := by rw [hgh, val_comp]
  rcases hf.2.2 _ (val g) (val h) hv with h1 | h1
  · exact Or.inl (isIso_of_isIso_val g h1)
  · exact Or.inr (isIso_of_isIso_val h h1)

section Transfer

variable {A B : Type} [Category.{0} A] [HasZeroMorphisms A] [Category.{0} B] [HasZeroMorphisms B]
  (F : RayVert A ⥤q RayVert B) (hinj : Function.Injective F.obj)
  (hlift : ∀ {X : RayVert A} {Y' : RayVert B} (e' : F.obj X ⟶ Y'),
    ∃ (Y : RayVert A) (e : X ⟶ Y), F.obj Y = Y' ∧ HEq (F.map e) e')
  (hval : ∀ {X Y : RayVert A} (p q : Quiver.Path X Y), pathVal (F.mapPath p) ≠ 0 →
    pathVal (F.mapPath p) = pathVal (F.mapPath q) → pathVal p = pathVal q ∧ pathVal p ≠ 0)

include hlift in
lemma path_lift_of {X : RayVert A} : ∀ {Y' : RayVert B} (p' : Quiver.Path (F.obj X) Y'),
    ∃ (Y : RayVert A) (p : Quiver.Path X Y), F.obj Y = Y' ∧ HEq (F.mapPath p) p'
  | _, .nil => ⟨X, .nil, rfl, HEq.rfl⟩
  | _, .cons p' e' => by
    obtain ⟨Y, p, hY, hp⟩ := path_lift_of p'
    subst hY
    obtain rfl := eq_of_heq hp
    obtain ⟨Z, e, hZ, he⟩ := hlift e'
    subst hZ
    obtain rfl := eq_of_heq he
    exact ⟨Z, p.cons e, rfl, HEq.rfl⟩

include hval in
lemma map_injective_of {X Y : RayVert A} {e₁ e₂ : X ⟶ Y} (h : F.map e₁ = F.map e₂) : e₁ = e₂ := by
  have h0 : pathVal (F.mapPath (Quiver.Path.nil.cons e₁)) ≠ 0 := by
    change 𝟙 _ ≫ (F.map e₁).1 ≠ 0
    rw [Category.id_comp]
    exact (F.map e₁).2.1
  have := (hval _ (Quiver.Path.nil.cons e₂) h0 (by
    change 𝟙 _ ≫ (F.map e₁).1 = 𝟙 _ ≫ (F.map e₂).1
    rw [h])).1
  change 𝟙 _ ≫ e₁.1 = 𝟙 _ ≫ e₂.1 at this
  rw [Category.id_comp, Category.id_comp] at this
  exact Subtype.ext this

/-- The chosen lift of an arrow. -/
def trArr {X : RayVert A} {Y' : RayVert B} (e' : F.obj X ⟶ Y') : Σ Y : RayVert A, X ⟶ Y :=
  ⟨(hlift e').choose, (hlift e').choose_spec.choose⟩

/-- Transport of the source of an arrow along an equality. -/
def castSrc {Q : Type} [Quiver Q] {X₁ X₂ Y : Q} : X₁ = X₂ → (X₂ ⟶ Y) → (X₁ ⟶ Y)
  | rfl, e => e

open Classical in
/-- The weight on `B` transported from a weight on `A`. -/
def trWeight (c : ArrowWeight A) : ArrowWeight B := fun {X' Y'} e' ↦
  if h : ∃ X, F.obj X = X' then
    c (trArr F hlift (castSrc h.choose_spec e')).2
  else 0

include hinj hval in
lemma trWeight_map (c : ArrowWeight A) {X Y : RayVert A} (e : X ⟶ Y) :
    trWeight F hlift c (F.map e) = c e := by
  classical
  have h : ∃ X₀, F.obj X₀ = F.obj X := ⟨X, rfl⟩
  have hs := (hlift (F.map e)).choose_spec.choose_spec
  have gen : ∀ s : Σ Y₁ : RayVert A, X ⟶ Y₁, F.obj s.1 = F.obj Y → HEq (F.map s.2) (F.map e) →
      c s.2 = c e := by
    rintro ⟨Y₁, e₁⟩ h1 h2
    obtain rfl := hinj h1
    rw [map_injective_of F hval (eq_of_heq h2)]
  have key : ∀ (X₀ : RayVert A) (hX₀ : F.obj X₀ = F.obj X),
      c (trArr F hlift (castSrc hX₀ (F.map e))).2 = c e := by
    intro X₀ hX₀
    have hX := hinj hX₀
    subst hX
    exact gen (trArr F hlift (F.map e)) hs.1 hs.2
  unfold trWeight
  rw [dite_cond_eq_true (eq_true h)]
  exact key _ h.choose_spec

include hinj hval in
lemma pathWeight_trWeight (c : ArrowWeight A) {X : RayVert A} :
    ∀ {Y : RayVert A} (p : Quiver.Path X Y),
      pathWeight (trWeight F hlift c) (F.mapPath p) = pathWeight c p
  | _, .nil => rfl
  | _, .cons p e => by
    change pathWeight (trWeight F hlift c) (F.mapPath p) + trWeight F hlift c (F.map e) =
      pathWeight c p + c e
    rw [pathWeight_trWeight c p, trWeight_map F hinj hlift hval c e]

include hinj hlift hval in
/-- **Local simple connectivity pulls back along an injective quiver map with lifting.** -/
theorem isCoboundaryOn_of_transfer
    (hB : ∀ D' : Set B, D'.Finite → ConvexR D' → ∀ c' : ArrowWeight B,
      IsCocycleOn D' c' → IsCoboundaryOn D' c')
    {D : Set A} (hD : D.Finite) (hDc : ConvexR D) (c : ArrowWeight A) (hc : IsCocycleOn D c) :
    IsCoboundaryOn D c := by
  let fo : A → B := fun a ↦ (F.obj (RayVert.mk a)).out
  have hfo : Function.Injective fo := fun a b h ↦ hinj h
  let D' : Set B := fo '' D
  have hmem : ∀ a, fo a ∈ D' → a ∈ D := fun a ⟨a', ha', h⟩ ↦ (hfo h) ▸ ha'
  have hpin : ∀ {X Y : RayVert A} (p : Quiver.Path X Y), PathIn D' (F.mapPath p) → PathIn D p := by
    intro X Y p
    induction p with
    | nil => exact hmem _
    | cons p e ih => exact fun h ↦ ⟨ih h.1, hmem _ h.2⟩
  have hconv : ConvexR D' := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ z ⟨p'⟩ ⟨q'⟩
    obtain ⟨Z, p, hZ, -⟩ := path_lift_of F hlift (X := RayVert.mk x) p'
    rw [← hZ] at q'
    obtain ⟨W, q, hW, -⟩ := path_lift_of F hlift q'
    have hWy : W = RayVert.mk y := hinj hW
    have hq : Reaches Z.out y := ⟨hWy ▸ q⟩
    exact ⟨Z.out, hDc x hx y hy Z.out ⟨p⟩ hq, congrArg RayVert.out hZ⟩
  have hc' : IsCocycleOn D' (trWeight F hlift c) := by
    intro X' Y' p' q' hp' hq' hv hv0
    obtain ⟨x, -, hxX⟩ := PathIn.start hp'
    change F.obj (RayVert.mk x) = X' at hxX
    subst hxX
    obtain ⟨Y₁, p, h1, hp⟩ := path_lift_of F hlift p'
    obtain ⟨Y₂, q, h2, hq⟩ := path_lift_of F hlift q'
    obtain rfl := hinj (h1.trans h2.symm)
    subst h1
    obtain rfl := eq_of_heq hp
    obtain rfl := eq_of_heq hq
    obtain ⟨hvq, hv0'⟩ := hval p q hv0 hv
    rw [pathWeight_trWeight F hinj hlift hval c p, pathWeight_trWeight F hinj hlift hval c q]
    exact hc p q (hpin p hp') (hpin q hq') hvq hv0'
  obtain ⟨φ', hφ'⟩ := hB D' (hD.image fo) hconv _ hc'
  refine ⟨fun a ↦ φ' (fo a), fun {X Y} e hX hY ↦ ?_⟩
  have := hφ' (F.map e) ⟨X.out, hX, rfl⟩ ⟨Y.out, hY, rfl⟩
  exact (trWeight_map F hinj hlift hval c e).symm.trans this

end Transfer

end General

section Residue

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [Fintype P] [DecidableEq P]
  [LargeIndecomposable.IsFiniteRayCategory P] {a b : P} (μ : a ⟶ b) (hμ : ¬IsIso μ)
  (hμr : ¬IsIrreducible μ) (hμ0 : μ ≠ 0) (hlong : IsLongAt μ) (hcont : NotInContour μ)
  {x₀ : P} [IsRayCategory (Res μ)]

attribute [local instance] isRayCategory_of_finiteRayCategory

omit [Fintype P] [DecidableEq P] [LargeIndecomposable.IsFiniteRayCategory P] in
lemma cls_irr {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] [IsRayCategory Q] {y z : Q}
    {f : y ⟶ z} (hf : IsIrreducible f) :
    cls f hf.1 = arrCls (⟨f, hf⟩ : RayVert.mk y ⟶ RayVert.mk z) := by
  rw [cls_eq f hf.1 (Quiver.Path.nil.cons ⟨f, hf⟩) (Category.id_comp _)]
  simp [pathFG]

include hμ hμr hμ0 hlong hcont in
/-- **Arrows of the residue cover lift.** -/
lemma arrow_lift (c : Cover x₀) (dy : P) (du : vtx ((resF μ).obj x₀) ⟶ vtx ((resF μ).obj dy))
    (e' : resCoverMap μ hμ hμr hμ0 hlong hcont c ⟶ (⟨(resF μ).obj dy, du⟩ : Cover _))
    (he' : IsIrreducible e') :
    ∃ (u : vtx x₀ ⟶ vtx dy) (e : c ⟶ (⟨dy, u⟩ : Cover x₀)), IsIrreducible e ∧
      resCoverMap μ hμ hμr hμ0 hlong hcont ⟨dy, u⟩ = ⟨(resF μ).obj dy, du⟩ ∧
      (resF μ).map (val e) = val e' := by
  have hg := isIrreducible_val he'
  let g : (resF μ).obj c.y ⟶ (resF μ).obj dy := val e'
  have hf := lift_irreducible μ hμ hμr hμ0 (g := g) hg
  refine ⟨c.u ≫ cls (lift μ g) hf.1, liftAt c _ hf.1, isIrreducible_liftAt c hf, ?_,
    resF_lift μ g⟩
  have hu : du = _ := u_eq e' he'.1
  change (⟨(resF μ).obj dy, (resPhi μ hμ hμr hμ0 hlong hcont).map (c.u ≫ cls (lift μ g) hf.1)⟩ :
    Cover ((resF μ).obj x₀)) = ⟨(resF μ).obj dy, du⟩
  congr 1
  rw [hu, Functor.map_comp, cls_irr hf, resPhi_arrCls]
  rw [cls_irr hg]
  congr 2
  exact Subtype.ext (resF_lift μ g)

include hμ hμr hμ0 hlong hcont in
lemma resCover_u {c d : Cover x₀} (e : RayVert.mk c ⟶ RayVert.mk d) :
    (resCoverMap μ hμ hμr hμ0 hlong hcont d).u = (resCoverMap μ hμ hμr hμ0 hlong hcont c).u ≫
      cls ((resF μ).map (val e.1)) (resF_irreducible μ hμ hμr hμ0 (isIrreducible_val e.2)).1 := by
  have hv := isIrreducible_val e.2
  change (resPhi μ hμ hμr hμ0 hlong hcont).map d.u = (resPhi μ hμ hμr hμ0 hlong hcont).map c.u ≫ _
  rw [u_eq e.1 e.2.1, Functor.map_comp, cls_irr hv, resPhi_arrCls]
  erw [cls_irr (resF_irreducible μ hμ hμr hμ0 hv)]
  rfl

/-- The quiver map of universal covers. -/
def resCoverQ : RayVert (Cover x₀) ⥤q RayVert (Cover ((resF μ).obj x₀)) where
  obj X := RayVert.mk (resCoverMap μ hμ hμr hμ0 hlong hcont X.out)
  map {X Y} e := ⟨some ⟨(resF μ).map (val e.1),
      (resF_irreducible μ hμ hμr hμ0 (isIrreducible_val e.2)).1,
      resCover_u μ hμ hμr hμ0 hlong hcont e⟩,
    isIrreducible_of_val (resF_irreducible μ hμ hμr hμ0 (isIrreducible_val e.2))⟩

lemma val_pathVal_resCoverQ {X : RayVert (Cover x₀)} : ∀ {Y : RayVert (Cover x₀)}
    (p : Quiver.Path X Y),
    val (pathVal ((resCoverQ μ hμ hμr hμ0 hlong hcont).mapPath p)) = (resF μ).map (val (pathVal p))
  | _, .nil => ((resF μ).map_id _).symm
  | _, .cons p e => by
    rw [Prefunctor.mapPath_cons, pathVal, pathVal, val_comp, val_comp, Functor.map_comp,
      val_pathVal_resCoverQ p]
    rfl

include hμ hμr hμ0 hlong hcont in
lemma resCoverQ_lift {X : RayVert (Cover x₀)} {Y' : RayVert (Cover ((resF μ).obj x₀))}
    (e' : (resCoverQ μ hμ hμr hμ0 hlong hcont).obj X ⟶ Y') :
    ∃ (Y : RayVert (Cover x₀)) (e : X ⟶ Y), (resCoverQ μ hμ hμr hμ0 hlong hcont).obj Y = Y' ∧
      HEq ((resCoverQ μ hμ hμr hμ0 hlong hcont).map e) e' := by
  obtain ⟨⟨dy⟩, du⟩ := Y'
  obtain ⟨g, hg⟩ := e'
  obtain ⟨u, e, he, hobj, hv⟩ := arrow_lift μ hμ hμr hμ0 hlong hcont X.out dy du g hg
  have hdu : (resPhi μ hμ hμr hμ0 hlong hcont).map u = du := by
    change Cover.mk _ _ = Cover.mk _ _ at hobj
    exact eq_of_heq (Cover.mk.inj hobj).2
  subst hdu
  refine ⟨RayVert.mk ⟨dy, u⟩, ⟨e, he⟩, rfl, heq_of_eq (Subtype.ext (val_injective ?_))⟩
  exact hv

include hμ hμr hμ0 hlong hcont in
lemma resCoverQ_val {X Y : RayVert (Cover x₀)} (p q : Quiver.Path X Y)
    (h0 : pathVal ((resCoverQ μ hμ hμr hμ0 hlong hcont).mapPath p) ≠ 0)
    (h : pathVal ((resCoverQ μ hμ hμr hμ0 hlong hcont).mapPath p) =
      pathVal ((resCoverQ μ hμ hμr hμ0 hlong hcont).mapPath q)) :
    pathVal p = pathVal q ∧ pathVal p ≠ 0 := by
  have hp := val_pathVal_resCoverQ μ hμ hμr hμ0 hlong hcont p
  have hq := val_pathVal_resCoverQ μ hμ hμr hμ0 hlong hcont q
  have hne : (resF μ).map (val (pathVal p)) ≠ 0 := by
    rw [← hp]
    intro h'
    exact h0 (val_injective (by rw [h']; rfl))
  have hnf : ¬LargeIndecomposable.FactorsThroughMorphism μ (val (pathVal p)) := fun hf ↦
    hne ((LargeIndecomposable.rayResidueFunctor_map_eq_zero_iff μ _).2 hf)
  refine ⟨val_injective (resF_map_injective μ hnf (by rw [← hp, ← hq, h])), fun h' ↦ hne ?_⟩
  rw [h', val_zero]
  exact Functor.map_zero _ _ _

include hμ hμr hμ0 hlong hcont in
/-- **Local simple connectivity passes from `P/μ` to `P`.** -/
theorem coverLocalSC_of_residue (h : CoverLocalSC ((resF μ).obj x₀)) : CoverLocalSC x₀ :=
  fun _ hD hDc c hc ↦ isCoboundaryOn_of_transfer (resCoverQ μ hμ hμr hμ0 hlong hcont)
    (fun _ _ h ↦ resCoverMap_injective μ hμ hμr hμ0 hlong hcont h)
    (resCoverQ_lift μ hμ hμr hμ0 hlong hcont) (resCoverQ_val μ hμ hμr hμ0 hlong hcont) h hD hDc c hc

end Residue

universe u

open Statement in
/-- **The universal cover of a minimal representation-infinite distributive algebra is locally
simply connected.** -/
theorem coverLocallySimplyConnected (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [Ring B]
    [Algebra k B] [FiniteDimensional k B] (ι : Type) [Fintype ι] [DecidableEq ι]
    (S : SplitBasicData k B ι) (hB : IsMinimalRepInfinite B) (hd : IsDistribIdeals B) :
    letI := S.distribHomStructure hd
    letI := S.locallySmall hd
    letI := S.isRayCategory hd
    letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
    letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
    ∀ (x₀ : RaySmall.{0} S.toIdempotents.RayCategory), CoverLocalSC x₀ := by
  letI := S.distribHomStructure hd
  letI := S.locallySmall hd
  letI := S.isRayCategory hd
  letI : Fintype (RaySmall.{0} S.toIdempotents.RayCategory) := Fintype.ofFinite _
  letI : DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory) := Classical.decEq _
  intro x₀
  have hι := S.nonempty_of_minimal hB
  have : Nonempty (RaySmall.{0} S.toIdempotents.RayCategory) :=
    ⟨⟨⟨S.toIdempotents.projectiveVertexEquiv.symm (Classical.arbitrary ι)⟩⟩⟩
  have hcon : IsConnected (FundGroupoid (RaySmall.{0} S.toIdempotents.RayCategory)) :=
    isConnected_fund_of_nzConnected fun x y ↦ RaySmall.nzConnected
      (S.nzConnected hd (fun e he hc ↦ hB.central_idempotent e he hc) x.as y.as)
  by_cases hCB : ChainBounded S.toIdempotents.RayCategory
  · exact coverLocalSC_of_chainBounded simplyConnectedStageStep _ (RaySmall.leftCancel (S.leftCancel hd))
      (RaySmall.rightCancel (S.rightCancel hd)) (RaySmall.chainBounded hCB) hcon x₀
  by_cases hL : HasLong (RaySmall.{0} S.toIdempotents.RayCategory)
  swap
  · exact coverLocalSC_of_not_hasLong hL
  letI := S.isFiniteRayCategory hd
  obtain ⟨a, b, μ, hμ, hμr, hμ0, hlong, hcont, hCB'⟩ :=
    bongartzProposition2_of twistedMulBasisExists (longMorphismNotInContour_of_mulBasis twistedMulBasisExists) k B ι S hB hd hCB hL
  haveI := LargeIndecomposable.rayResidueCategory_isFiniteRayCategory μ hμ
  haveI : Finite (Res μ) :=
    Finite.of_surjective (fun x ↦ (⟨x⟩ : Res μ)) fun ⟨x⟩ ↦ ⟨x, rfl⟩
  haveI : IsRayCategory (Res μ) := isRayCategory_of_finiteRayCategory
  letI : Fintype (Res μ) := Fintype.ofFinite _
  letI : DecidableEq (Res μ) := Classical.decEq _
  have : IsConnected (Quiver.FreeGroupoid (RayVert (RaySmall.{0} S.toIdempotents.RayCategory))) :=
    isConnected_of_quotient homotopy
  have : IsConnected (Quiver.FreeGroupoid (RayVert (Res μ))) :=
    isConnected_of_equivalent (resFGEquiv μ hμ hμr hμ0)
  have hcon' : IsConnected (FundGroupoid (Res μ)) := isConnected_quotient homotopy
  exact coverLocalSC_of_residue μ hμ hμr hμ0 hlong hcont
    (coverLocalSC_of_chainBounded simplyConnectedStageStep _
      (leftCancel_quotient _ (RaySmall.leftCancel (S.leftCancel hd)))
      (rightCancel_quotient _ (RaySmall.rightCancel (S.rightCancel hd))) hCB' hcon' _)

end LargeIndecomposable.RayCat
