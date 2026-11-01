module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.BoundedLength

/-!
# Subpieces

For finite sets `T ⊆ S` of points of the cover, the quiver of `T` embeds into that of `S`
(`incH`), compatibly with composites in the cover (`compD_map`). A representation of the piece of
`S` restricts to one of `T` (`resP`); its path maps are those of `S` read on `T`
(`pathTot_resP`), so restriction preserves respecting the cover (`respectsCover_resP`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver Module

universe u

variable {k : Type u} [Field k]
  {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S T : Finset (Cover x₀)} (hTS : T ⊆ S)

/-- The inclusion of a subpiece. -/
def incH : FinQuiver.Hom (pieceQuiver T) (pieceQuiver S) where
  vert a := ⟨(show T from a).1, hTS (show T from a).2⟩
  arr α := ⟨⟨α.1.1, hTS α.1.2⟩, ⟨α.2.1.1, hTS α.2.1.2⟩, α.2.2⟩
  map_src _ := rfl
  map_tgt _ := rfl

lemma compD_map : ∀ (le : List (pieceQuiver T).A) (i j : (pieceQuiver T).V)
    (h : PathFrom i le j),
    (show pt T i ⟶ pt T j from compD S (le.map (incH hTS).arr) ((incH hTS).vert i)
      ((incH hTS).vert j) (pathFrom_map (incH hTS) le i j h)) = compD T le i j h
  | [], _, _, h => rfl
  | e :: le, i, j, h => by
    obtain ⟨h1, h2⟩ := h
    change e.1 = i at h1
    subst h1
    have ih := compD_map le _ j h2
    simp only [List.map_cons, compD]
    congr 1
    exact congrArg (e.2.2.1 ≫ ·) ih

/-- The restriction of a representation to a subpiece. -/
def resP (X : Rep k (pieceQuiver S)) : Rep k (pieceQuiver T) where
  obj a := X.obj ((incH hTS).vert a)
  map α := X.map ((incH hTS).arr α)

instance (X : Rep k (pieceQuiver S)) [∀ i, FiniteDimensional k (X.obj i)]
    (a : (pieceQuiver T).V) : FiniteDimensional k ((resP hTS X).obj a) :=
  inferInstanceAs (FiniteDimensional k (X.obj _))

variable (X : Rep k (pieceQuiver S))

/-- Restriction of total spaces. -/
def rTot : X.Tot →ₗ[k] (resP hTS X).Tot where
  toFun x a := x ((incH hTS).vert a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open Classical in
/-- Extension by zero of total spaces. -/
def eTot : (resP hTS X).Tot →ₗ[k] X.Tot where
  toFun y s := if h : (show S from s).1 ∈ T then y ⟨(show S from s).1, h⟩ else 0
  map_add' y y' := by
    funext s
    by_cases h : (show S from s).1 ∈ T <;> simp [h] <;> rfl
  map_smul' c y := by
    funext s
    by_cases h : (show S from s).1 ∈ T <;> simp [h] <;> rfl

lemma incV_injective : Function.Injective (incH (x₀ := x₀) hTS).vert := fun a b h ↦
  Subtype.ext (congrArg (fun s : (pieceQuiver S).V ↦ (show S from s).1) h)

lemma eTot_inc (y : (resP hTS X).Tot) (a : (pieceQuiver T).V) :
    eTot hTS X y ((incH hTS).vert a) = y a := by
  classical
  exact dif_pos (show T from a).2

lemma eTot_out (y : (resP hTS X).Tot) (s : (pieceQuiver S).V)
    (hs : ∀ a, (incH hTS).vert a ≠ s) : eTot hTS X y s = 0 := by
  classical
  refine dif_neg fun h ↦ hs ⟨(show S from s).1, h⟩ rfl

lemma rTot_eTot (y : (resP hTS X).Tot) : rTot hTS X (eTot hTS X y) = y := by
  funext a
  exact eTot_inc hTS X y a

lemma eTot_rTot_arrOp (α : (pieceQuiver T).A) (y : (resP hTS X).Tot) :
    eTot hTS X (rTot hTS X (X.arrOp ((incH hTS).arr α) (eTot hTS X y))) =
      X.arrOp ((incH hTS).arr α) (eTot hTS X y) := by
  funext s
  by_cases hs : ∃ a, (incH hTS).vert a = s
  · obtain ⟨a, rfl⟩ := hs
    rw [eTot_inc]
    rfl
  · push Not at hs
    rw [eTot_out hTS X _ s hs, Rep.arrOp_apply, Pi.single_eq_of_ne]
    intro h
    exact hs _ h.symm

lemma resP_arrOp (α : (pieceQuiver T).A) :
    (resP hTS X).arrOp α = rTot hTS X ∘ₗ X.arrOp ((incH hTS).arr α) ∘ₗ eTot hTS X := by
  refine LinearMap.ext fun y ↦ funext fun a ↦ ?_
  simp only [LinearMap.comp_apply, Rep.arrOp_apply]
  change _ = (Pi.single ((pieceQuiver S).tgt ((incH hTS).arr α))
      ((X.map ((incH hTS).arr α)).hom (eTot hTS X y ((incH hTS).vert ((pieceQuiver T).src α)))) :
      X.Tot) ((incH hTS).vert a)
  rw [eTot_inc]
  change _ = (Pi.single ((incH hTS).vert ((pieceQuiver T).tgt α))
      ((X.map ((incH hTS).arr α)).hom (y ((pieceQuiver T).src α))) : X.Tot) ((incH hTS).vert a)
  by_cases ha : a = (pieceQuiver T).tgt α
  · subst ha
    rw [Pi.single_eq_same]
    exact (Pi.single_eq_same (M := fun s ↦ X.obj s) _ _).symm
  · rw [Pi.single_eq_of_ne ha]
    exact (Pi.single_eq_of_ne (M := fun s ↦ X.obj s)
      (fun h ↦ ha (incV_injective hTS h)) _).symm

/-- **Path maps of the restriction.** -/
lemma pathTot_resP : ∀ le : List (pieceQuiver T).A,
    (resP hTS X).pathTot le = rTot hTS X ∘ₗ X.pathTot (le.map (incH hTS).arr) ∘ₗ eTot hTS X
  | [] => by
    refine LinearMap.ext fun y ↦ ?_
    change y = rTot hTS X (eTot hTS X y)
    rw [rTot_eTot]
  | α :: le => by
    change (resP hTS X).pathTot le ∘ₗ (resP hTS X).arrOp α =
      rTot hTS X ∘ₗ (X.pathTot (le.map (incH hTS).arr) ∘ₗ X.arrOp ((incH hTS).arr α)) ∘ₗ
        eTot hTS X
    rw [pathTot_resP le, resP_arrOp]
    refine LinearMap.ext fun y ↦ ?_
    simp only [LinearMap.comp_apply]
    rw [eTot_rTot_arrOp]

/-- **Restriction preserves respecting the cover.** -/
theorem respectsCover_resP (hX : RespectsCover X) : RespectsCover (resP hTS X) := by
  refine ⟨fun le i j h h0 ↦ ?_, fun le le' i j h h' he ↦ ?_⟩
  · rw [pathTot_resP, hX.1 _ _ _ (pathFrom_map (incH hTS) le i j h)
      ((compD_map hTS le i j h).trans h0)]
    simp
  · rw [pathTot_resP, pathTot_resP, hX.2 _ _ _ _ (pathFrom_map (incH hTS) le i j h)
      (pathFrom_map (incH hTS) le' i j h')
      ((compD_map hTS le i j h).trans (he.trans (compD_map hTS le' i j h').symm))]

end LargeIndecomposable.RayCat
