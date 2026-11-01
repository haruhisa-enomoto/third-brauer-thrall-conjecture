module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.SinkCount
public import LargeIndecomposable.DirectedAlgebras.Directing.RigidMin

/-!
# Rigid modules over a piece have no cocycles beyond coboundaries

For representations `X`, `Y` of a piece respecting the cover and a family `F` of relations
generating those of the cover, a cocycle `z` of `F` gives an extension `E(z)` respecting the cover
(`respectsCover_extR`). If every extension of the module of `X` by that of `Y` splits, a section
is a morphism of representations, so `z` is a coboundary (`cocycles_le_range_cob`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver

universe u

lemma _root_.LargeIndecomposable.FinQuiver.Hom.id_locallyInjective (Q : FinQuiver) :
    (FinQuiver.Hom.id Q).LocallyInjective :=
  ⟨fun _ _ _ h ↦ h, fun _ _ _ h ↦ h⟩

section ExtR

variable {k : Type u} [Field k] {D : FinQuiver} {X Y : Rep k D} (z : Ext.Data X Y)

lemma extR_eq_zero (w : (Ext.extR z).Tot) (h1 : Ext.πX z w = 0) (h2 : Ext.πY z w = 0) :
    w = 0 := by
  funext l
  exact Prod.ext (congrFun h2 l) (congrFun h1 l)

lemma act_extR_eq_zero (a : D.PathAlgebra k) (hX : Ext.act X a = 0) (hY : Ext.act Y a = 0)
    (hz : Ext.crossA z a = 0) : Ext.act (Ext.extR z) a = 0 := by
  refine LinearMap.ext fun w ↦ extR_eq_zero z _ ?_ ?_
  · have := LinearMap.congr_fun (Ext.πX_act z a) w
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hX, LinearMap.zero_apply] at this
    exact this
  · have := LinearMap.congr_fun (Ext.πY_act z a) w
    rw [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      hY, hz, LinearMap.zero_apply, LinearMap.zero_apply, add_zero] at this
    exact this

/-- The inclusion of `Y` into `E(z)`. -/
def inY : Y ⟶ Ext.extR z where
  app i := ModuleCat.ofHom (LinearMap.inl k _ _)
  comm α := by
    ext y
    change ((Y.map α).hom y, (0 : X.obj (D.tgt α))) =
      ((Y.map α).hom y + z α 0, (X.map α).hom 0)
    simp

/-- The projection of `E(z)` onto `X`. -/
def prX : Ext.extR z ⟶ X where
  app i := ModuleCat.ofHom (LinearMap.snd k _ _)
  comm α := by
    ext w
    rfl

end ExtR

variable {k : Type u} [Field k]
  {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)}

lemma pieceAct_comm {X Y : Rep k (pieceQuiver S)} {hX : RespectsCover X} {hY : RespectsCover Y}
    (s : PieceMod X hX →ₗ[PieceAlg k S] PieceMod Y hY) (a : PieceAlg k S) (x : X.Tot) :
    s (pieceAct X hX a x) = pieceAct Y hY a (s x) :=
  s.map_smul a x

/-- **A module map between representations respecting the cover is a morphism.** -/
def homOfLin {X Y : Rep k (pieceQuiver S)} {hX : RespectsCover X} {hY : RespectsCover Y}
    (s : PieceMod X hX →ₗ[PieceAlg k S] PieceMod Y hY) : X ⟶ Y :=
  Rep.diagHom (FinQuiver.Hom.id_locallyInjective _)
    (show X.Tot →ₗ[k] Y.Tot from s.restrictScalars k) <| by
    refine (Rep.isPdHom_iff _ _).1 ⟨fun q ↦ LinearMap.ext fun x ↦ ?_, fun c ↦
      LinearMap.ext fun x ↦ ?_⟩
    · have h := pieceAct_comm s (RingQuot.mkAlgHom k _ (FinQuiver.vertex k _ q)) x
      rw [pieceAct_mk, pieceAct_mk, Rep.pdAct_vertex, Rep.pdAct_vertex] at h
      exact h
    · have h := pieceAct_comm s (RingQuot.mkAlgHom k _ (FinQuiver.arrow k _ c)) x
      rw [pieceAct_mk, pieceAct_mk, Rep.pdAct_arrow, Rep.pdAct_arrow] at h
      exact h

lemma homOfLin_app {X Y : Rep k (pieceQuiver S)} {hX : RespectsCover X} {hY : RespectsCover Y}
    (s : PieceMod X hX →ₗ[PieceAlg k S] PieceMod Y hY) (i : (pieceQuiver S).V) (x : X.obj i) :
    ((homOfLin s).app i).hom x = (show Y.Tot from s (show X.Tot from Pi.single i x)) i := rfl

/-- **Cocycles of a generating family give extensions respecting the cover.** -/
theorem respectsCover_extR (F : Ext.RelFam (pieceQuiver S) k)
    (hF : ∀ r, F.ρ r ∈ TwoSidedIdeal.span (relGens k S))
    (hgen : relGens k S ⊆ TwoSidedIdeal.span (Set.range F.ρ))
    {X Y : Rep k (pieceQuiver S)} (hX : RespectsCover X) (hY : RespectsCover Y)
    (z : Ext.Data X Y) (hz : z ∈ Ext.cocycles F (X := X) (Y := Y)) :
    RespectsCover (Ext.extR z) := by
  have hle : TwoSidedIdeal.span (Set.range F.ρ) ≤ TwoSidedIdeal.span (relGens k S) := by
    rw [TwoSidedIdeal.span_le]
    rintro _ ⟨r, rfl⟩
    exact hF r
  have hall : ∀ ρ ∈ TwoSidedIdeal.span (Set.range F.ρ), Ext.crossA z ρ = 0 :=
    Ext.crossA_eq_zero_of_span z _ (fun ρ hρ ↦ act_eq_zero_of_mem_span hX ρ (hle hρ))
      (fun ρ hρ ↦ act_eq_zero_of_mem_span hY ρ (hle hρ))
      (by rintro _ ⟨r, rfl⟩; exact (Ext.mem_cocycles F z).1 hz r)
  rw [respectsCover_iff]
  intro r hr
  exact act_extR_eq_zero z r (act_eq_zero_of_mem_span hX r (TwoSidedIdeal.subset_span hr))
    (act_eq_zero_of_mem_span hY r (TwoSidedIdeal.subset_span hr)) (hall r (hgen hr))

/-- **If extensions of modules split, cocycles are coboundaries.** -/
theorem cocycles_le_range_cob (F : Ext.RelFam (pieceQuiver S) k)
    (hF : ∀ r, F.ρ r ∈ TwoSidedIdeal.span (relGens k S))
    (hgen : relGens k S ⊆ TwoSidedIdeal.span (Set.range F.ρ))
    {X Y : Rep k (pieceQuiver S)} (hX : RespectsCover X) (hY : RespectsCover Y)
    [∀ i, FiniteDimensional k (X.obj i)] [∀ i, FiniteDimensional k (Y.obj i)]
    (hv : AR.ExtVanish (toFDMod X hX) (toFDMod Y hY)) :
    Ext.cocycles F (X := X) (Y := Y) ≤ LinearMap.range (Ext.cobL (X := X) (Y := Y)) := by
  intro z hz
  have hE := respectsCover_extR F hF hgen hX hY z hz
  haveI : ∀ i, FiniteDimensional k ((Ext.extR z).obj i) := fun i ↦
    inferInstanceAs (FiniteDimensional k (Y.obj i × X.obj i))
  let i : PieceMod Y hY →ₗ[PieceAlg k S] PieceMod (Ext.extR z) hE := toFDModHom hY hE (inY z)
  let p : PieceMod (Ext.extR z) hE →ₗ[PieceAlg k S] PieceMod X hX := toFDModHom hE hX (prX z)
  have hi : Function.Injective i := fun a b h ↦ by
    funext l
    exact congrArg Prod.fst (congrFun (show (inY z).tot a = (inY z).tot b from h) l)
  have hp : Function.Surjective p := fun x ↦
    ⟨show (Ext.extR z).Tot from fun l ↦ ((0 : Y.obj l), x l), rfl⟩
  have hex : LinearMap.range i = LinearMap.ker p := by
    ext w
    constructor
    · rintro ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      rfl
    · intro h
      rw [LinearMap.mem_ker] at h
      refine ⟨show Y.Tot from fun l ↦ ((show (Ext.extR z).Tot from w) l).1, ?_⟩
      funext l
      refine Prod.ext rfl ?_
      have := congrFun (show (prX z).tot w = 0 from h) l
      exact this.symm
  obtain ⟨s, hs⟩ := hv (toFDMod (Ext.extR z) hE) i p hi hp hex
  have hσ : ∀ l (x : X.obj l), (((homOfLin s).app l).hom x).2 = x := by
    intro l x
    change ((show (Ext.extR z).Tot from s (show X.Tot from Pi.single l x)) l).2 = x
    have := congrFun (show (prX z).tot (s (show X.Tot from Pi.single l x)) =
      (show X.Tot from Pi.single l x) from LinearMap.congr_fun hs _) l
    rw [Pi.single_eq_same] at this
    exact this
  exact ⟨fun l ↦ LinearMap.fst k _ _ ∘ₗ ((homOfLin s).app l).hom,
    (Ext.eq_cob_of_section z (homOfLin s) hσ).symm⟩

end LargeIndecomposable.RayCat
