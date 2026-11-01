module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.PieceCritical
public import LargeIndecomposable.DirectedAlgebras.Sincere.PolyBuild
public import LargeIndecomposable.Coverings.GradedModules.PdGraded

/-!
# Representation-finite pieces

All indecomposable modules over a connected representation-finite convex piece of the cover are
directing, and the same holds for its quotients by idempotents.
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

/-- Dimensions of indecomposables over a representation-finite piece are bounded. -/
theorem bounded_of_pieceRepFin (hacycCov : CoverAcyclic x₀) (hrep : PieceRepFin k S) :
    ∃ b, ∀ N : AR.FDMod k (PieceAlg k S), AR.IndNT N → finrank k N ≤ b := by
  classical
  obtain ⟨n, Y, hY⟩ := hrep
  refine ⟨Finset.univ.sup fun j ↦ finrank k (Y j).Tot, fun N hN ↦ ?_⟩
  obtain ⟨j, ⟨φ⟩⟩ := hY (repOf N) (fun i ↦ inferInstance) (respectsCover_repOf N)
    (isIndec_repOf N hN)
  have h1 : finrank k N = finrank k (Y j).Tot := by
    rw [← (totEquiv N).finrank_eq, (totEquivOfIso φ).finrank_eq]
  rw [h1]
  exact Finset.le_sup (f := fun j ↦ finrank k (Y j).Tot) (Finset.mem_univ j)

section Conn

variable [IsAlgClosed k] (hS : Convex (S : Set (Cover x₀))) (hne : S.Nonempty)
  (hacycCov : CoverAcyclic x₀) (hint : ∀ a b : Cover x₀, (interval a b).Finite)
  (hlsc : CoverLocalSC x₀)
  (hconnS : ∀ T : Set (pieceQuiver S).V, T.Nonempty →
    (∀ α : (pieceQuiver S).A, (pieceQuiver S).src α ∈ T ↔ (pieceQuiver S).tgt α ∈ T) →
      T = Set.univ)
  (hrep : PieceRepFin k S)
include hS hne hacycCov hint hlsc hconnS hrep

/-- **All indecomposables of a connected representation-finite piece lie in the preprojective
component.** -/
theorem exists_all_preproj :
    ∃ 𝒞 : AR.FDMod k (PieceAlg k S) → Prop, AR.PreprojComp 𝒞 ∧
      ∀ N : AR.FDMod k (PieceAlg k S), AR.IndNT N → 𝒞 N := by
  classical
  obtain ⟨𝒞, h𝒞⟩ := piece_preprojComp (k := k) hS hne hacycCov hint hlsc
  have hpar : ParEq S := parEq_of_cover hacycCov hint hlsc
  have hacyc := piece_acyclic (S := S) hacycCov
  let D := pieceDirData (k := k) hacyc
  have hb := bounded_of_pieceRepFin hacycCov hrep
  have hcl := h𝒞.closedClass hb
  obtain ⟨M, hM⟩ := h𝒞.nonempty
  exact ⟨𝒞, h𝒞, fun N hN ↦ AR.all_of_closed D.e D.idem D.sum (fun x ↦ D.projIndNT x (Set.mem_univ x))
    (fun T hT hcl ↦ hconnS T hT fun α ↦ ⟨fun h ↦ hcl _ _ h (Or.inr (D.arrNe _ _ (parr_arrow hpar α))),
      fun h ↦ hcl _ _ h (Or.inl (D.arrNe _ _ (parr_arrow hpar α)))⟩) hcl hM N hN⟩

/-- Projectives of a connected representation-finite piece are good. -/
theorem goodProj_of_repFin (x : (pieceQuiver S).V) :
    AR.Good (AR.projE (k := k) ((pieceDirData (k := k) (piece_acyclic (S := S) hacycCov)).idem x)) := by
  obtain ⟨𝒞, h𝒞, hall⟩ := exists_all_preproj hS hne hacycCov hint hlsc hconnS hrep
  exact h𝒞.good (hall _ ((pieceDirData (k := k) (piece_acyclic (S := S) hacycCov)).projIndNT x
    (Set.mem_univ x)))

/-- **Directing on quotients.** -/
theorem directing_quot (T' : Set (pieceQuiver S).V) (N : AR.FDMod k
    ((pieceDirData (k := k) (piece_acyclic (S := S) hacycCov)).QAlg T')) (hN : AR.IndNT N) :
    AR.Directing N := by
  have hacyc := piece_acyclic (S := S) hacycCov
  obtain ⟨b, hb⟩ := bounded_of_pieceRepFin (k := k) hacycCov hrep
  exact AR.DirData.directing_quotAny (A := PieceAlg k S) (pieceDirData (k := k) hacyc) T'
    (fun _ _ ↦ Set.mem_univ _)
    (fun x ↦ goodProj_of_repFin hS hne hacycCov hint hlsc hconnS hrep x) (fun _ ↦ Set.mem_univ _)
    b hb N hN

end Conn

end LargeIndecomposable.RayCat
