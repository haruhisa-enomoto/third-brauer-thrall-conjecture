module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.PieceTits
public import LargeIndecomposable.RepresentationType.MinimalInfinite.BoundedFinite

/-!
# Pieces of bounded representation length are representation-finite

A module map between representations respecting the cover is a morphism whose total map is the
module map (`homOfLin_tot`). So indecomposable representations give indecomposable modules
(`indNT_toFDMod`), and isomorphic modules give isomorphic representations (`iso_of_isoM`). With
`finite_of_bounded` this shows that a connected convex piece whose indecomposable modules have
bounded dimension is representation-finite (`pieceRepFin_of_bounded`); hence a
representation-infinite one has indecomposables of every size (`unbounded_of_not_pieceRepFin`),
and so has its preprojective component.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver Module

universe u

variable {k : Type u} [Field k]
  {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)}

/-- **The total map of `homOfLin s` is `s`.** -/
lemma homOfLin_tot {X Y : Rep k (pieceQuiver S)} {hX : RespectsCover X} {hY : RespectsCover Y}
    (s : PieceMod X hX →ₗ[PieceAlg k S] PieceMod Y hY) (x : X.Tot) :
    (homOfLin s).tot x = s x := by
  funext i
  rw [Rep.Hom.tot_apply, homOfLin_app]
  have h1 := pieceAct_comm s (pev i) x
  rw [pieceAct_pev, pieceAct_pev] at h1
  have h2 := congrFun h1 i
  change (show Y.Tot from s (show X.Tot from Pi.single i (x i))) i =
    (Pi.single i ((show Y.Tot from s x) i) : Y.Tot) i at h2
  rw [Pi.single_eq_same] at h2
  exact h2

/-- Morphisms with the same total map are equal. -/
lemma hom_eq_of_tot {D : FinQuiver} {X Y : Rep k D} {f g : X ⟶ Y} (h : f.tot = g.tot) : f = g := by
  refine Rep.hom_ext fun j ↦ ?_
  ext v
  have := congrFun (LinearMap.congr_fun h (Pi.single j v)) j
  simpa [Rep.Hom.tot_apply] using this

lemma homOfLin_comp {X Y Z : Rep k (pieceQuiver S)} {hX : RespectsCover X} {hY : RespectsCover Y}
    {hZ : RespectsCover Z} (s : PieceMod X hX →ₗ[PieceAlg k S] PieceMod Y hY)
    (t : PieceMod Y hY →ₗ[PieceAlg k S] PieceMod Z hZ) :
    homOfLin s ≫ homOfLin t = homOfLin (t ∘ₗ s) := by
  refine hom_eq_of_tot (LinearMap.ext fun x ↦ ?_)
  rw [Rep.Hom.tot_comp, LinearMap.comp_apply, homOfLin_tot, homOfLin_tot, homOfLin_tot]
  rfl

/-- **Indecomposable representations give indecomposable modules.** -/
theorem indNT_toFDMod {X : Rep k (pieceQuiver S)} (hX : RespectsCover X)
    [∀ i, FiniteDimensional k (X.obj i)] (hind : X.IsIndec) : AR.IndNT (toFDMod X hX) := by
  obtain ⟨⟨i, hi⟩, hidem⟩ := hind
  refine ⟨fun U V hUV ↦ ?_, ?_⟩
  · let e : PieceMod X hX →ₗ[PieceAlg k S] PieceMod X hX :=
      U.subtype ∘ₗ Submodule.linearProjOfIsCompl U V hUV
    have heU : ∀ u ∈ U, e u = u := fun u hu ↦
      congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hUV ⟨u, hu⟩)
    have heV : ∀ v ∈ V, e v = 0 := fun v hv ↦ by
      have := congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hUV ⟨v, hv⟩)
      exact this
    have hh : homOfLin e ≫ homOfLin e = homOfLin e := by
      rw [homOfLin_comp]
      congr 1
      refine LinearMap.ext fun x ↦ ?_
      exact heU _ (Submodule.coe_mem _)
    have key : ∀ x : X.Tot, (homOfLin e).tot x = e x := homOfLin_tot e
    rcases hidem _ hh with h0 | h1
    · left
      rw [eq_bot_iff]
      intro u hu
      rw [Submodule.mem_bot]
      refine (heU u hu).symm.trans ((key u).symm.trans ?_)
      funext j
      change ((homOfLin e).app j).hom (u j) = 0
      rw [h0 j]
      rfl
    · right
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_bot]
      refine Eq.trans ?_ ((key v).trans (heV v hv))
      rw [h1, Rep.Hom.tot_id]
      rfl
  · exact ⟨⟨show X.Tot from Pi.single i (Classical.choose (exists_ne (0 : X.obj i))), 0, by
      intro h
      have := congrFun h i
      rw [Pi.single_eq_same] at this
      exact Classical.choose_spec (exists_ne (0 : X.obj i)) this⟩⟩

lemma homOfLin_id {X : Rep k (pieceQuiver S)} {hX : RespectsCover X} :
    homOfLin (LinearMap.id : PieceMod X hX →ₗ[PieceAlg k S] PieceMod X hX) = 𝟙 X :=
  hom_eq_of_tot (LinearMap.ext fun x ↦ by rw [homOfLin_tot, Rep.Hom.tot_id]; rfl)

/-- **Isomorphic modules give isomorphic representations.** -/
theorem iso_of_isoM {X : Rep k (pieceQuiver S)} (hX : RespectsCover X)
    [∀ i, FiniteDimensional k (X.obj i)] {Z : AR.FDMod k (PieceAlg k S)}
    (h : AR.IsoM (toFDMod X hX) Z) : Nonempty (X ≅ repOf Z) := by
  obtain ⟨g, hg⟩ := h
  let e₁ : PieceMod X hX ≃ₗ[PieceAlg k S] Z := LinearEquiv.ofBijective (AR.FDMod.lin g) hg
  let s : PieceMod X hX →ₗ[PieceAlg k S] PieceMod (repOf Z) (respectsCover_repOf Z) :=
    (repOfEquivA Z).symm.toLinearMap ∘ₗ e₁.toLinearMap
  let t : PieceMod (repOf Z) (respectsCover_repOf Z) →ₗ[PieceAlg k S] PieceMod X hX :=
    e₁.symm.toLinearMap ∘ₗ (repOfEquivA Z).toLinearMap
  refine ⟨⟨homOfLin s, homOfLin t, ?_, ?_⟩⟩
  · rw [homOfLin_comp, ← homOfLin_id (hX := hX)]
    congr 1
    refine LinearMap.ext fun x ↦ ?_
    simp [s, t]
  · rw [homOfLin_comp, ← homOfLin_id (hX := respectsCover_repOf Z)]
    congr 1
    refine LinearMap.ext fun x ↦ ?_
    simp [s, t]

section Bounded

variable (hS : Convex (S : Set (Cover x₀))) (hne : S.Nonempty)
    (hacycCov : CoverAcyclic x₀) (hint : ∀ a b : Cover x₀, (interval a b).Finite)
    (hlsc : CoverLocalSC x₀)
    (hconnS : ∀ T : Set (pieceQuiver S).V, T.Nonempty →
      (∀ α : (pieceQuiver S).A, (pieceQuiver S).src α ∈ T ↔ (pieceQuiver S).tgt α ∈ T) →
        T = Set.univ)
include hS hne hacycCov hint hlsc hconnS

/-- **A connected convex piece of bounded length is representation-finite.** -/
theorem pieceRepFin_of_bounded
    (hb : ∃ b, ∀ N : AR.FDMod k (PieceAlg k S), AR.IndNT N → finrank k N ≤ b) :
    PieceRepFin k S := by
  classical
  obtain ⟨𝒞, h𝒞⟩ := piece_preprojComp (k := k) hS hne hacycCov hint hlsc
  have hpar : ParEq S := parEq_of_cover hacycCov hint hlsc
  have hacyc := piece_acyclic (S := S) hacycCov
  let D := pieceDirData (k := k) hacyc
  obtain ⟨L, hL⟩ := AR.finite_of_bounded D.e D.idem D.sum (fun x ↦ D.projIndNT x (Set.mem_univ x))
    (fun T hT hcl ↦ hconnS T hT fun α ↦ ⟨fun h ↦ hcl _ _ h (Or.inr (D.arrNe _ _ (parr_arrow hpar α))),
      fun h ↦ hcl _ _ h (Or.inl (D.arrNe _ _ (parr_arrow hpar α)))⟩) h𝒞 hb
  refine ⟨L.length, fun j ↦ repOf (L.get j), fun X hfin hX hind ↦ ?_⟩
  obtain ⟨Z, hZ, hiso⟩ := hL _ (indNT_toFDMod hX hind)
  obtain ⟨j, rfl⟩ := List.get_of_mem hZ
  exact ⟨j, iso_of_isoM hX hiso⟩

/-- **A representation-infinite connected convex piece has indecomposables of every size.** -/
theorem unbounded_of_not_pieceRepFin (hrep : ¬PieceRepFin k S) (b : ℕ) :
    ∃ N : AR.FDMod k (PieceAlg k S), AR.IndNT N ∧ b < finrank k N := by
  by_contra h
  push Not at h
  exact hrep (pieceRepFin_of_bounded hS hne hacycCov hint hlsc hconnS ⟨b, h⟩)

end Bounded

end LargeIndecomposable.RayCat
