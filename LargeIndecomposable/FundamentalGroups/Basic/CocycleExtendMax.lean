module

public import LargeIndecomposable.FundamentalGroups.Basic.CocycleExtend
public import LargeIndecomposable.RayCategories.Basic.Op

/-!
# Extending a cocycle across a maximal point

The dual of `exists_extend_min`, by passing to the opposite ray category
(`isRayCategory_op`): paths reverse (`revPath`), cocycles and path-convex sets transfer, and
a maximal point of `S` is minimal in `Sᵒᵖ` (`exists_extend_max`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Opposite

universe v u

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

lemma rpow_comm_self {x : A} (e : x ⟶ x) : ∀ n, rpow e n ≫ e = e ≫ rpow e n
  | 0 => by simp
  | n + 1 => by rw [rpow_succ, ← Category.assoc e, ← rpow_comm_self e n]

lemma unop_rpow_op {X : Aᵒᵖ} (e : X ⟶ X) : ∀ n, (rpow e n).unop = rpow e.unop n
  | 0 => rfl
  | n + 1 => by
    rw [rpow_succ, unop_comp, unop_rpow_op e n, rpow_succ, rpow_comm_self]

/-- The opposite of a ray category. -/
instance isRayCategory_op [IsRayCategory A] : IsRayCategory Aᵒᵖ where
  skeletal X Y h := by
    obtain ⟨e⟩ := h
    exact unop_injective (IsRayCategory.skeletal ⟨e.unop.symm⟩)
  finite_out X := by
    refine ((IsRayCategory.finite_in X.unop).image op).subset ?_
    rintro Y ⟨f, hf⟩
    exact ⟨Y.unop, ⟨f.unop, fun h ↦ hf (Quiver.Hom.unop_inj h)⟩, rfl⟩
  finite_in X := by
    refine ((IsRayCategory.finite_out X.unop).image op).subset ?_
    rintro Y ⟨f, hf⟩
    exact ⟨Y.unop, ⟨f.unop, fun h ↦ hf (Quiver.Hom.unop_inj h)⟩, rfl⟩
  finite_hom X Y := by
    have := IsRayCategory.finite_hom Y.unop X.unop
    exact Finite.of_equiv _ (opEquiv X Y).symm
  id_ne_zero X h := IsRayCategory.id_ne_zero X.unop (by simpa using congrArg Quiver.Hom.unop h)
  nil X e he := by
    have he' : e.unop ≠ 𝟙 X.unop := fun h ↦ he (Quiver.Hom.unop_inj h)
    obtain ⟨n, hn⟩ := IsRayCategory.nil X.unop e.unop he'
    exact ⟨n, Quiver.Hom.unop_inj (by rw [unop_rpow_op, hn]; rfl)⟩

lemma pathIn_comp_iff {S : Set A} {x y : RayVert A} (a : Quiver.Path x y) :
    ∀ {z : RayVert A} (b : Quiver.Path y z), PathIn S (a.comp b) ↔ PathIn S a ∧ PathIn S b
  | _, .nil => ⟨fun h ↦ ⟨h, PathIn.target h⟩, fun h ↦ h.1⟩
  | _, .cons b _ => by
    change PathIn S (a.comp b) ∧ _ ↔ PathIn S a ∧ (PathIn S b ∧ _)
    rw [pathIn_comp_iff a b, and_assoc]

/-- The image of a set of objects in the opposite category. -/
def opSet (S : Set A) : Set Aᵒᵖ := {X | X.unop ∈ S}

lemma pathIn_revPath {S : Set A} {x : RayVert A} : ∀ {y : RayVert A} (p : Quiver.Path x y),
    PathIn (opSet S) (revPath p) ↔ PathIn S p
  | _, .nil => Iff.rfl
  | _, .cons p e => by
    change PathIn (opSet S) ((revArr e).toPath.comp (revPath p)) ↔ PathIn S p ∧ _
    rw [pathIn_comp_iff, pathIn_revPath p]
    constructor
    · intro h; exact ⟨h.2, h.1.1⟩
    · intro h; exact ⟨⟨h.2, PathIn.target (D := S) h.1⟩, h.1⟩

lemma pathWeight_revPath (c : ArrowWeight Aᵒᵖ) {x : RayVert A} :
    ∀ {y : RayVert A} (p : Quiver.Path x y),
      pathWeight c (revPath p) = pathWeight (fun e ↦ c (revArr e)) p
  | _, .nil => rfl
  | _, .cons p e => by
    change pathWeight c ((revArr e).toPath.comp (revPath p)) = _
    rw [pathWeight_comp, pathWeight_revPath c p]
    change 0 + c (revArr e) + _ = _ + c (revArr e)
    ring

lemma pathWeight_unrevPath (c : ArrowWeight A) {X : RayVert Aᵒᵖ} :
    ∀ {Y : RayVert Aᵒᵖ} (p : Quiver.Path X Y),
      pathWeight c (unrevPath p) = pathWeight (fun e ↦ c (unrevArr e)) p
  | _, .nil => rfl
  | _, .cons p e => by
    change pathWeight c ((unrevArr e).toPath.comp (unrevPath p)) = _
    rw [pathWeight_comp, pathWeight_unrevPath c p]
    change 0 + c (unrevArr e) + _ = _ + c (unrevArr e)
    ring

lemma pathIn_unrevPath {S : Set A} {X : RayVert Aᵒᵖ} {Y : RayVert Aᵒᵖ} (p : Quiver.Path X Y) :
    PathIn S (unrevPath p) ↔ PathIn (opSet S) p := by
  rw [← pathIn_revPath, revPath_unrevPath]
  exact Iff.rfl

variable [IsRayCategory A]

/-- **Extending a cocycle across a maximal point.** -/
theorem exists_extend_max (hL : LeftCancel A) (hR : RightCancel A) (hCB : ChainBounded A)
    {S : Set A} {s : A} (hconv : PathConvex S)
    (hmax : ∀ {y : RayVert A} (_ : RayVert.mk s ⟶ y), y.out ∉ S)
    (c : ArrowWeight A) (hc : IsCocycleOn (S \ {s}) c) :
    ∃ c' : ArrowWeight A, IsCocycleOn S c' ∧
      ∀ {x y : RayVert A} (e : x ⟶ y), y.out ≠ s → c' e = c e := by
  let cop : ArrowWeight Aᵒᵖ := fun e ↦ c (unrevArr e)
  have hconv' : PathConvex (opSet S) := by
    intro X Y p hX hY
    rw [← pathIn_unrevPath]
    exact hconv _ hY hX
  have hmin' : ∀ {X : RayVert Aᵒᵖ} (_ : X ⟶ RayVert.mk (op s)), X.out ∉ opSet S :=
    fun e ↦ hmax (unrevArr e)
  have hdiff : opSet (S \ {s}) = opSet S \ {op s} := by
    ext X
    simp only [opSet, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    exact and_congr_right fun _ ↦ ⟨fun h h' ↦ h (by rw [h']),
      fun h h' ↦ h (by rw [← h'])⟩
  have hc' : IsCocycleOn (opSet S \ {op s}) cop := by
    intro X Y p q hp hq hpq h0
    rw [← hdiff, ← pathIn_unrevPath] at hp hq
    have h := hc (unrevPath p) (unrevPath q) hp hq
      (by rw [pathVal_unrevPath, pathVal_unrevPath, hpq])
      (by rw [pathVal_unrevPath]; exact fun h ↦ h0 (Quiver.Hom.unop_inj h))
    rwa [pathWeight_unrevPath, pathWeight_unrevPath] at h
  obtain ⟨c'', hc'', hoff⟩ := exists_extend_min (leftCancel_op hR) (rightCancel_op hL)
    (chainBounded_op hCB) hconv' hmin' cop hc'
  refine ⟨fun e ↦ c'' (revArr e), ?_, fun e hy ↦ ?_⟩
  · intro x y p q hp hq hpq h0
    rw [← pathIn_revPath] at hp hq
    have h := hc'' (revPath p) (revPath q) hp hq
      (by rw [pathVal_revPath, pathVal_revPath, hpq])
      (by rw [pathVal_revPath]; exact fun h ↦ h0 (Quiver.Hom.op_inj h))
    rwa [pathWeight_revPath, pathWeight_revPath] at h
  · exact hoff (revArr e) (fun h ↦ hy (congrArg unop h))

end LargeIndecomposable.RayCat
