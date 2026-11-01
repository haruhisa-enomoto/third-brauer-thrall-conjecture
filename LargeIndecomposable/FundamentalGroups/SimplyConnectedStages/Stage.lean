module

public import LargeIndecomposable.Coverings.UniversalCover.CoverPath
public import LargeIndecomposable.RayCategories.Basic.ArrSetIdeal
public import LargeIndecomposable.FundamentalGroups.Fischbacher.KillingArrows

/-!
# The stages of Fischbacher's Satz 5.1

Let `P` be a finite ray category with reduction data `D` (Lemma 2.1): arrows `aᵢ : b → dᵢ` with
values `αᵢ`, and paths `u : b ⇝ c`, `uᵢ : dᵢ ⇝ c` avoiding the `αᵢ` with `αᵢ uᵢ = u ≠ 0`. In the
universal cover `X` of `P`, for a set `K` of lifts `⟨b, w⟩` of `b`, the stage `Y_K` kills the lifts
of the `αᵢ` starting at the points of `K` (`killed`, `Stage`). The lifts of `u` and `uᵢ`
(`uT`, `usT`) avoid all killed arrows.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [LargeIndecomposable.IsFiniteRayCategory0 P]
  [Finite P] {x₀ : P} {ι : Type} {b : P} {d : ι → P} {α : ∀ i, b ⟶ d i}
  {hα : ∀ i, ¬IsIso (α i)}

attribute [local instance] isRayCategory_of_finiteRayCategory

namespace Stage

variable (D : RedData α) (K : Set (vtx x₀ ⟶ vtx b))

/-- The killed arrows: lifts of the `αᵢ` at points of `K`. -/
def killed {x y : RayVert (Cover x₀)} (e : x ⟶ y) : Prop :=
  ∃ w ∈ K, x = (⟨b, w⟩ : Cover x₀) ∧ (arrowIdeal α).mem (Cover.projArr e).1

/-- The stage: the cover with the killed arrows annihilated. -/
abbrev Y := CategoryTheory.Quotient (arrSetIdeal (killed (x₀ := x₀) (α := α) K)).rel

lemma isProper : (arrSetIdeal (killed (x₀ := x₀) (α := α) K)).IsProper :=
  arrSetIdeal_isProper _

instance : IsRayCategory (Y (x₀ := x₀) (α := α) K) :=
  isRayCategory_quotient _ (isProper K)

/-- An arrow whose projection avoids the `αᵢ` is not killed. -/
lemma not_killed {x y : RayVert (Cover x₀)} (e : x ⟶ y) (h : ¬(arrowIdeal α).mem (Cover.projArr e).1) :
    ¬killed (α := α) K e := fun ⟨_, _, _, hm⟩ ↦ h hm

/-- The ideal of the stage contains no arrow with projection outside the ideal of `P`. -/
lemma not_mem_of_proj {x y : RayVert (Cover x₀)} (e : x ⟶ y)
    (h : ¬(arrowIdeal α).mem (Cover.projArr e).1) :
    ¬(arrSetIdeal (killed (x₀ := x₀) (α := α) K)).mem e.1 :=
  fun hm ↦ not_killed K e h (mem_of_irreducible _ e hm)

/-- A path of the cover whose projection avoids the `αᵢ` avoids the stage ideal. -/
lemma avoidsI_of_proj {x : RayVert (Cover x₀)} : ∀ {y : RayVert (Cover x₀)}
    (p : Quiver.Path x y), Avoids α (Cover.projPath p) →
    AvoidsI (arrSetIdeal (killed (x₀ := x₀) (α := α) K)) p
  | _, .nil, _ => trivial
  | _, .cons p e, h => ⟨avoidsI_of_proj p h.1, not_mem_of_proj K e h.2⟩

/-- A lift of `b`. -/
abbrev pt (w : vtx x₀ ⟶ vtx b) : Cover x₀ := ⟨b, w⟩

/-- The lift of `aᵢ` at `⟨b, w⟩`. -/
abbrev aT (w : vtx x₀ ⟶ vtx b) (i : ι) :
    RayVert.mk (pt w) ⟶ RayVert.mk (⟨d i, w ≫ cls (D.a i).1 (D.a i).2.1⟩ : Cover x₀) :=
  liftArr (pt w) (D.a i)

/-- The end of the lifts of `u` and `uᵢ`. -/
abbrev uEnd (w : vtx x₀ ⟶ vtx b) : Cover x₀ := ⟨D.c, w ≫ Cover.pcls D.u⟩

lemma exists_liftPath' (a : Cover x₀) {y : RayVert P} (p : Quiver.Path (RayVert.mk a.y) y)
    (E : Cover x₀) (hE : E = ⟨y.out, a.u ≫ Cover.pcls p⟩) :
    ∃ q : Quiver.Path (RayVert.mk a) (RayVert.mk E), HEq (Cover.projPath q) p := by
  obtain ⟨b', q, rfl, hq⟩ := Cover.exists_liftPath a p
  subst hE
  exact ⟨q, hq⟩

/-- The lift of `u` at `⟨b, w⟩`. -/
def uT (w : vtx x₀ ⟶ vtx b) : Quiver.Path (RayVert.mk (pt w)) (RayVert.mk (uEnd D w)) :=
  (exists_liftPath' (pt w) D.u _ rfl).choose

lemma projPath_uT (w : vtx x₀ ⟶ vtx b) : Cover.projPath (uT D w) = D.u :=
  eq_of_heq (exists_liftPath' (pt w) D.u _ rfl).choose_spec

/-- `[aᵢ][uᵢ] = [u]` in the fundamental groupoid of `P`. -/
lemma cls_a_us (i : ι) : cls (D.a i).1 (D.a i).2.1 ≫ Cover.pcls (D.us i) = Cover.pcls D.u := by
  have h1 : cls (D.a i).1 (D.a i).2.1 = Cover.pcls (D.a i).toPath := by
    rw [cls_eq_arr]; rfl
  rw [h1, ← Cover.pcls_comp]
  refine homotopic_of_pathVal_eq _ _ ?_ ?_
  · rw [pathVal_comp, pathVal_toPath, D.a_val, D.hcomp]
  · rw [pathVal_comp, pathVal_toPath, D.a_val, D.hcomp]; exact D.hu0

lemma uEnd_eq (w : vtx x₀ ⟶ vtx b) (i : ι) :
    (⟨D.c, (w ≫ cls (D.a i).1 (D.a i).2.1) ≫ Cover.pcls (D.us i)⟩ : Cover x₀) = uEnd D w := by
  rw [Category.assoc, cls_a_us]

/-- The lift of `uᵢ` at the end of the lift of `aᵢ`. -/
def usT (w : vtx x₀ ⟶ vtx b) (i : ι) :
    Quiver.Path (RayVert.mk (⟨d i, w ≫ cls (D.a i).1 (D.a i).2.1⟩ : Cover x₀))
      (RayVert.mk (uEnd D w)) :=
  (exists_liftPath' (⟨d i, w ≫ cls (D.a i).1 (D.a i).2.1⟩ : Cover x₀) (D.us i) _
    (uEnd_eq D w i).symm).choose

lemma projPath_usT (w : vtx x₀ ⟶ vtx b) (i : ι) : HEq (Cover.projPath (usT D w i)) (D.us i) :=
  (exists_liftPath' (⟨d i, w ≫ cls (D.a i).1 (D.a i).2.1⟩ : Cover x₀) (D.us i) _
    (uEnd_eq D w i).symm).choose_spec

include hα in
/-- **A killed arrow is the lift of some `aᵢ` at a point of `K`.** -/
lemma eq_aT_of_killed {x y : RayVert (Cover x₀)} (e : x ⟶ y) (h : killed (α := α) K e) :
    ∃ w ∈ K, ∃ i : ι, x = RayVert.mk (pt w) ∧
      y = RayVert.mk (⟨d i, w ≫ cls (D.a i).1 (D.a i).2.1⟩ : Cover x₀) ∧ HEq e (aT D w i) := by
  obtain ⟨w, hw, rfl, hm⟩ := h
  obtain ⟨i, hx, hy, he⟩ := eq_alpha_of_mem α hα (Cover.projArr e).2 hm
  refine ⟨w, hw, i, rfl, ?_⟩
  have hyy : y.out.y = d i := hy
  obtain ⟨hyeq, hee⟩ := Cover.arr_ext e (aT D w i) hyy (by
    have hval : (Cover.projArr e).1 = (Cover.projArr (aT D w i)).1 ≫ eqToHom hyy.symm := by
      rw [he]
      change eqToHom hx ≫ α i ≫ eqToHom hy.symm = (D.a i).1 ≫ eqToHom hyy.symm
      rw [D.a_val]
      simp
    have key : ∀ {z : P} (hz : z = d i) (f : RayVert.mk (pt w).y ⟶ RayVert.mk z)
        (g : RayVert.mk (pt w).y ⟶ RayVert.mk (d i)), f.1 = g.1 ≫ eqToHom hz.symm → HEq f g := by
      intro z hz f g hfg
      subst hz
      simp only [eqToHom_refl, Category.comp_id] at hfg
      exact heq_of_eq (Subtype.ext hfg)
    exact key hyy _ _ hval)
  exact ⟨hyeq, hee⟩

end Stage

end LargeIndecomposable.RayCat
