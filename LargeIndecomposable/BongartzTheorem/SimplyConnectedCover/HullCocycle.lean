module

public import LargeIndecomposable.BongartzTheorem.SimplyConnectedCover.HullAcyclic
public import LargeIndecomposable.FundamentalGroups.Basic.Cocycle
public import LargeIndecomposable.RayCategories.RoiterVanishing.Efficient

/-!
# Interval-finiteness of the cover from a positive cocycle

A cocycle `c` with `c e ≥ 1` on every arrow gives a height on the universal cover: the
weight of the walk class of an object. It increases strictly along arrows of the cover, so
intervals of the cover are finite and every finite set lies in a finite convex piece
(`hullFinite_of_posCocycle`). Without long morphisms the constant weight `1` is a cocycle
(`hullFinite_of_not_hasLong`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P}

/-- An irreducible morphism of the cover lies over an arrow of the quiver of `P`. -/
lemma exists_arrow_of_irreducible {a b : Cover x₀} {f : a ⟶ b} (hf : IsIrreducible f) :
    ∃ e : RayVert.mk a.y ⟶ RayVert.mk b.y, b.u = a.u ≫ arrCls e := by
  have hv := isIrreducible_val hf
  rcases f with _ | f
  · exact absurd rfl hf.1
  obtain ⟨hf0, hfu⟩ := f.2
  refine ⟨⟨f.1, hv⟩, hfu.trans ?_⟩
  rw [cls_eq f.1 hf0 (Quiver.Path.nil.cons ⟨f.1, hv⟩) (Category.id_comp _)]
  simp [pathFG]

lemma cocycleFunctor_arrCls (c : ArrowWeight P) (hc : IsCocycle c) {x y : RayVert P}
    (e : x ⟶ y) : (cocycleFunctor c hc).map (arrCls e) = Multiplicative.ofAdd (c e) := by
  change (cocycleFunctor c hc).map ((CategoryTheory.Quotient.functor homotopy).map
    ((Quiver.FreeGroupoid.of (RayVert P)).map e)) = _
  rw [cocycleFunctor_map]
  have h := Quiver.FreeGroupoid.lift_spec (weightPrefunctor c)
  exact congrArg (fun (G : RayVert P ⥤q SingleObj (Multiplicative ℤ)) ↦
    (G.map e : Multiplicative ℤ)) h

variable (c : ArrowWeight P) (hc : IsCocycle c)

/-- The height of an object of the cover: the weight of its walk class. -/
def coverHt (a : Cover x₀) : ℤ := Multiplicative.toAdd ((cocycleFunctor c hc).map a.u)

variable (hpos : ∀ {x y : RayVert P} (e : x ⟶ y), 1 ≤ c e)
include c hc hpos

lemma coverHt_lt {a b : Cover x₀} {f : a ⟶ b} (hf : IsIrreducible f) :
    coverHt c hc a < coverHt c hc b := by
  obtain ⟨e, he⟩ := exists_arrow_of_irreducible hf
  unfold coverHt
  rw [he, CategoryTheory.Functor.map_comp, SingleObj.comp_as_mul, toAdd_mul,
    cocycleFunctor_arrCls, toAdd_ofAdd]
  have := hpos e
  omega

lemma coverHt_le {a b : Cover x₀} (h : Reach a b) : coverHt c hc a ≤ coverHt c hc b := by
  induction h with
  | refl => exact le_rfl
  | step f hf _ ih => exact (coverHt_lt c hc hpos hf).le.trans ih

lemma finite_interval_of_posCocycle (b : Cover x₀) :
    ∀ n : ℕ, ∀ a : Cover x₀, coverHt c hc b - coverHt c hc a < n →
      {d | Reach a d ∧ Reach d b}.Finite := by
  intro n
  induction n with
  | zero =>
    intro a ha
    refine Set.Finite.subset Set.finite_empty fun d ⟨had, hdb⟩ ↦ ?_
    have := (coverHt_le c hc hpos had).trans (coverHt_le c hc hpos hdb)
    push_cast at ha
    omega
  | succ n ih =>
    intro a ha
    have hsucc : {a' : Cover x₀ | ∃ f : a ⟶ a', IsIrreducible f}.Finite :=
      (IsRayCategory.finite_out a).subset fun _ ⟨f, hf⟩ ↦ ⟨f, hf.1⟩
    have hsub : {d | Reach a d ∧ Reach d b} ⊆
        {a} ∪ ⋃ a' ∈ {a' : Cover x₀ | ∃ f : a ⟶ a', IsIrreducible f},
          {d | Reach a' d ∧ Reach d b} := by
      rintro d ⟨had, hdb⟩
      cases had with
      | refl => exact Or.inl rfl
      | step f hf ha'd => exact Or.inr (Set.mem_biUnion ⟨f, hf⟩ ⟨ha'd, hdb⟩)
    refine ((Set.finite_singleton a).union (hsucc.biUnion fun a' ⟨f, hf⟩ ↦ ?_)).subset hsub
    have := coverHt_lt c hc hpos hf
    exact ih a' (by push_cast at ha ⊢; omega)

/-- **A positive cocycle makes the universal cover interval-finite.** -/
theorem hullFinite_of_posCocycle : HullFinite x₀ := by
  intro T
  let H : Set (Cover x₀) := {b | ∃ a ∈ T, ∃ d ∈ T, Reach a b ∧ Reach b d}
  have hH : H.Finite := by
    refine (T.finite_toSet.biUnion fun a _ ↦ T.finite_toSet.biUnion fun d _ ↦
      finite_interval_of_posCocycle c hc hpos d ((coverHt c hc d - coverHt c hc a).toNat + 1)
        a (by push_cast; omega)).subset fun b ⟨a, ha, d, hd, hab, hbd⟩ ↦ ?_
    exact Set.mem_biUnion ha (Set.mem_biUnion hd ⟨hab, hbd⟩)
  refine ⟨hH.toFinset, fun t ht ↦ ?_, fun a b d ha hd hab hbd ↦ ?_⟩
  · exact hH.mem_toFinset.2 ⟨t, ht, t, ht, Reach.refl t, Reach.refl t⟩
  · obtain ⟨a', ha', -, -, ha'a, -⟩ := hH.mem_toFinset.1 ha
    obtain ⟨-, -, d', hd', -, hdd'⟩ := hH.mem_toFinset.1 hd
    exact hH.mem_toFinset.2 ⟨a', ha', d', hd', ha'a.trans hab, hbd.trans hdd'⟩

omit c hc hpos

/-- The constant weight `1`. -/
def oneWeight : ArrowWeight P := fun _ ↦ 1

lemma pathWeight_one {x : RayVert P} : ∀ {y : RayVert P} (p : Quiver.Path x y),
    pathWeight oneWeight p = p.length
  | _, .nil => rfl
  | _, .cons p _ => by rw [pathWeight, pathWeight_one p, Quiver.Path.length_cons]; push_cast; rfl

/-- **Without long morphisms the universal cover is interval-finite.** -/
theorem hullFinite_of_not_hasLong (h : ¬HasLong P) : HullFinite x₀ := by
  have hc : IsCocycle (oneWeight (P := P)) := by
    intro x y s t hst h0
    rw [pathWeight_one, pathWeight_one]
    by_cases hiso : IsIso (pathVal s)
    · have hs : s.length = 0 := by
        by_contra hl
        exact not_isIso_pathVal s (by omega) hiso
      have ht : t.length = 0 := by
        by_contra hl
        exact not_isIso_pathVal t (by omega) (hst ▸ hiso)
      rw [hs, ht]
    · have hirr : IsIrreducible (pathVal s) := by
        by_contra hni
        exact h ⟨_, _, _, h0, hiso, hni⟩
      obtain ⟨e, rfl⟩ := eq_toPath_of_isIrreducible s hirr
      obtain ⟨e', rfl⟩ := eq_toPath_of_isIrreducible t (hst ▸ hirr)
      rfl
  exact hullFinite_of_posCocycle oneWeight hc fun _ ↦ le_rfl

end LargeIndecomposable.RayCat
