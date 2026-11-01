module

public import LargeIndecomposable.Coverings.GradedModules.RayRadical
public import LargeIndecomposable.Coverings.Pieces.PdModule

/-!
# Graded `k(P)`-modules as representations of pieces of the cover

For a graded `k(P)`-module `M` (grading `rayGrAlg ℓ k`), the cover object `a = (y, u)`
corresponds to the degree `g(a) = u ≫ (ℓ y)⁻¹` (`gOf`), and `W a = e_y M_{g(a)}` is the
space of `M` "at `a`". A ray `f : y ⟶ z` lifted at `a` maps `W a` into `W b` for the
target `b` of the lift (`gOf_target`). This gives a representation `grRep S` of the
piece `D_S` for every finite set `S` of cover objects.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits LargeIndecomposable.Graded RayQuiver Cover AR Classical FinQuiver

universe u

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} (ℓ : ∀ y : P, vtx x₀ ⟶ vtx y)

/-- The degree of a cover object. -/
def gOf (a : Cover x₀) : Pi1 x₀ := asIso (a.u ≫ inv (ℓ a.y))

/-- Degrees move along nonzero morphisms of the cover by the degree of the value. -/
lemma gOf_target {a b : Cover x₀} (f : a ⟶ b) (hf : f ≠ 0) (hv : val f ≠ 0) :
    gOf ℓ b = rayDeg ℓ ⟨a.y, b.y, val f, hv⟩ * gOf ℓ a := by
  apply Iso.ext
  change b.u ≫ inv (ℓ b.y) = (a.u ≫ inv (ℓ a.y)) ≫ (ℓ a.y ≫ cls (val f) hv ≫ inv (ℓ b.y))
  rw [u_eq_of_ne_zero f hf hv]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]

variable (k : Type u) [Field k]
variable {M : Type u} [AddCommGroup M] [Module (Linearization P k) M] [Module k M]
  [IsScalarTower k (Linearization P k) M] (μ : GrMod (rayGrAlg ℓ k) M)

/-- The space of `M` at a cover object. -/
def W (a : Cover x₀) : Submodule k M where
  carrier := {m | morElt k (𝟙 a.y) • m = m ∧ μ.Mem (gOf ℓ a) m}
  add_mem' := fun {m n} hm hn ↦ ⟨by rw [smul_add, hm.1, hn.1], μ.mem_add hm.2 hn.2⟩
  zero_mem' := ⟨smul_zero _, μ.mem_zero _⟩
  smul_mem' := fun c {m} hm ↦ ⟨by rw [smul_comm, hm.1], μ.mem_smul c hm.2⟩

lemma morElt_mem_rayGrAlg {y z : P} (f : y ⟶ z) (hf : f ≠ 0) :
    (rayGrAlg ℓ k).Mem (rayDeg ℓ ⟨y, z, f, hf⟩) (morElt k f) := by
  have := rayGrading_mem_basis ℓ k ⟨y, z, f, hf⟩
  rwa [linBasisR_apply] at this

/-- A lifted ray maps `W a` into `W b`. -/
lemma smul_mem_W {a b : Cover x₀} (f : a ⟶ b) (hf : f ≠ 0) (hv : val f ≠ 0) {m : M}
    (hm : m ∈ W ℓ k μ a) : morElt k (val f) • m ∈ W ℓ k μ b := by
  refine ⟨?_, ?_⟩
  · rw [← mul_smul, morElt_mul, Category.comp_id]
  · rw [gOf_target ℓ f hf hv]
    exact μ.smul_mem _ _ _ _ (morElt_mem_rayGrAlg ℓ k _ hv) hm.2

variable (S : Finset (Cover x₀))

/-- **The representation of the piece `D_S` given by a graded module.** -/
def grRep : Rep k (pieceQuiver S) where
  obj a := ModuleCat.of k (W ℓ k μ (show S from a).1)
  map α := ModuleCat.ofHom
    { toFun w := ⟨morElt k (val α.2.2.1) • (w : M), smul_mem_W ℓ k μ α.2.2.1
        α.2.2.2.1 (isIrreducible_val α.2.2.2).1 w.2⟩
      map_add' w w' := Subtype.ext (smul_add _ _ _)
      map_smul' c w := Subtype.ext (smul_comm _ c _) }

variable {ℓ k μ S}

/-- The vector of `M` underlying an element of `grRep` at a vertex. -/
def toM {a : (pieceQuiver S).V} (w : (grRep ℓ k μ S).obj a) : M :=
  ((show W ℓ k μ (pt S a) from w) : M)

lemma toM_injective {a : (pieceQuiver S).V} :
    Function.Injective (toM (ℓ := ℓ) (k := k) (μ := μ) (S := S) (a := a)) :=
  fun _ _ h ↦ Subtype.ext h

@[simp] lemma toM_zero {a : (pieceQuiver S).V} :
    toM (ℓ := ℓ) (k := k) (μ := μ) (S := S) (0 : (grRep ℓ k μ S).obj a) = 0 := rfl

lemma grRep_map_apply (α : (pieceQuiver S).A) (w : (grRep ℓ k μ S).obj ((pieceQuiver S).src α)) :
    toM (((grRep ℓ k μ S).map α).hom w) = morElt k (val α.2.2.1) • toM w := rfl

/-- **Path operators of `grRep`**: a path acts through the composite of its labels. -/
lemma pathTot_grRep_single : ∀ (le : List (pieceQuiver S).A) (i j : (pieceQuiver S).V)
    (h : PathFrom i le j) (w : (grRep ℓ k μ S).obj i) (l : (pieceQuiver S).V),
    toM (((grRep ℓ k μ S).pathTot le (Pi.single i w)) l) =
      if l = j then morElt k (val (compD S le i j h)) • toM w else 0
  | [], i, j, h, w, l => by
    change i = j at h
    subst h
    simp only [Rep.pathTot, LinearMap.id_apply]
    by_cases hl : l = i
    · subst hl
      simp only [Pi.single_eq_same, if_true]
      simp only [compD, eqToHom_refl, val_id]
      exact (show W ℓ k μ _ from w).2.1.symm
    · rw [Pi.single_eq_of_ne hl, if_neg hl]; rfl
  | e :: le, i, j, h, w, l => by
    obtain ⟨h1, h2⟩ := h
    change e.1 = i at h1
    subst h1
    simp only [Rep.pathTot, LinearMap.comp_apply]
    rw [Rep.arrOp_apply]
    have hs : (Pi.single e.1 w : (grRep ℓ k μ S).Tot) ((pieceQuiver S).src e) = w := by
      exact Pi.single_eq_same (M := fun a ↦ (grRep ℓ k μ S).obj a) e.1 w
    rw [hs, pathTot_grRep_single le _ j h2 _ l]
    split_ifs with hl
    · rw [show toM (((grRep ℓ k μ S).map e).hom w) = morElt k (val e.2.2.1) • toM w from rfl,
        ← mul_smul]
      erw [morElt_mul]
      congr 2
      change _ = val (eqToHom rfl ≫ e.2.2.1 ≫ compD S le _ j h2)
      rw [eqToHom_refl, Category.id_comp, val_comp]
      rfl
    · rfl

/-- A nonempty path acts only on its starting component. -/
lemma pathTot_cons_eq (e : (pieceQuiver S).A) (le : List (pieceQuiver S).A)
    (x : (grRep ℓ k μ S).Tot) :
    (grRep ℓ k μ S).pathTot (e :: le) x =
      (grRep ℓ k μ S).pathTot (e :: le) (Pi.single ((pieceQuiver S).src e)
        (x ((pieceQuiver S).src e))) := by
  simp only [Rep.pathTot, LinearMap.comp_apply, Rep.arrOp_apply, Pi.single_eq_same]

/-- **Graded modules give representations respecting the cover.** -/
theorem respectsCover_grRep : RespectsCover (grRep ℓ k μ S) := by
  classical
  have key : ∀ (le : List (pieceQuiver S).A) (i j : (pieceQuiver S).V) (h : PathFrom i le j),
      le ≠ [] → ∀ x l, toM (((grRep ℓ k μ S).pathTot le x) l) =
        if l = j then morElt k (val (compD S le i j h)) • toM (x i)
        else 0 := by
    intro le i j h hne x l
    obtain ⟨e, le', rfl⟩ := List.exists_cons_of_ne_nil hne
    have hi : (pieceQuiver S).src e = i := h.1
    rw [pathTot_cons_eq, ← pathTot_grRep_single (e :: le') _ j (hi ▸ h)]
    subst hi
    rfl
  refine ⟨fun le i j h h0 ↦ ?_, fun le le' i j h h' heq ↦ ?_⟩
  · rcases le with _ | ⟨e, le'⟩
    · exfalso
      change i = j at h
      subst h
      exact IsRayCategory.id_ne_zero (pt S i) (by simpa [compD] using h0)
    · refine LinearMap.ext fun x ↦ funext fun l ↦ toM_injective ?_
      rw [key _ i j h (List.cons_ne_nil _ _), h0, val_zero, morElt_zero, zero_smul]
      simp
  · -- both empty, or both nonempty
    have hnil : ∀ (l₁ l₂ : List (pieceQuiver S).A) (h₁ : PathFrom i l₁ j) (h₂ : PathFrom i l₂ j),
        compD S l₁ i j h₁ = compD S l₂ i j h₂ → l₁ = [] → l₂ = [] := by
      intro l₁ l₂ h₁ h₂ he hl₁ 
      subst hl₁
      by_contra hl₂
      obtain ⟨e, l₃, rfl⟩ := List.exists_cons_of_ne_nil hl₂
      change i = j at h₁
      subst h₁
      have hv := val_compD S (e :: l₃) i i h₂
      rw [← he] at hv
      simp only [compD, eqToHom_refl, val_id] at hv
      exact pathMor_ne_id ((pieceProj S).arr e) (l₃.map (pieceProj S).arr) (pt S i).y
        (pathFrom_map (pieceProj S) (e :: l₃) i i h₂) hv.symm
    by_cases hle : le = []
    · have hle' := hnil le le' h h' heq hle
      subst hle hle'
      rfl
    · have hle' : le' ≠ [] := fun h0 ↦ hle (hnil le' le h' h heq.symm h0)
      refine LinearMap.ext fun x ↦ funext fun l ↦ toM_injective ?_
      rw [key le i j h hle, key le' i j h' hle', heq]

end LargeIndecomposable.RayCat
