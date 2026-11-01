module

public import LargeIndecomposable.FundamentalGroups.Fischbacher.SeparationCocycle
public import LargeIndecomposable.FundamentalGroups.Basic.HyperForest
public import LargeIndecomposable.FundamentalGroups.Fischbacher.Selection

/-!
# Extending a cocycle across a minimal point

Let `S` be a path-convex set of objects of a chain-bounded ray category with cancellation and
`s ∈ S` a point with no arrow into it from `S`. A cocycle on `S \ {s}` extends to a cocycle on
`S` (`exists_extend_min`). The weights of the arrows out of `s` are a potential on the
hyperforest whose hyperedges are the maximal nonzero morphisms out of `s` (with target in
`S`), each containing the arrows below it; it is a hyperforest by chain-boundedness
(`eq_of_walkConn`). This is the cocycle form of the injectivity `H₁ A' → H₁ A` in the proof of
Bretscher–Gabriel 2.6 and Bongartz, *A criterion for finite representation type*, 2.2–2.3.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

universe v u

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

lemma pathWeight_comp (c : ArrowWeight A) {x y : RayVert A} (p : Quiver.Path x y) :
    ∀ {z : RayVert A} (q : Quiver.Path y z),
      pathWeight c (p.comp q) = pathWeight c p + pathWeight c q
  | _, .nil => by simp [pathWeight]
  | _, .cons q e => by
    rw [Quiver.Path.comp_cons, pathWeight, pathWeight, pathWeight_comp c p q, add_assoc]

/-- Paths between points of `S` stay in `S`. -/
def PathConvex (S : Set A) : Prop :=
  ∀ {x y : RayVert A} (p : Quiver.Path x y), x.out ∈ S → y.out ∈ S → PathIn S p

section Avoid

variable {S : Set A} {s : A} (hmin : ∀ {x : RayVert A} (_ : x ⟶ RayVert.mk s), x.out ∉ S)
include hmin

/-- A path in `S` not starting at `s` avoids `s`. -/
lemma pathIn_diff {x : RayVert A} (hx : x.out ≠ s) :
    ∀ {y : RayVert A} (p : Quiver.Path x y), PathIn S p → PathIn (S \ {s}) p
  | _, .nil, h => ⟨h, hx⟩
  | _, .cons (b := y') p e, h => by
    refine ⟨pathIn_diff hx p h.1, h.2, fun hy ↦ ?_⟩
    obtain rfl : RayVert.mk s = _ := (Set.mem_singleton_iff.1 hy).symm
    exact hmin e (PathIn.target h.1)

end Avoid

lemma PathIn.of_comp_right {S : Set A} {x y : RayVert A} (a : Quiver.Path x y) :
    ∀ {z : RayVert A} (b : Quiver.Path y z), PathIn S (a.comp b) → PathIn S b
  | _, .nil, h => PathIn.target h
  | _, .cons b _, h => ⟨PathIn.of_comp_right a b h.1, h.2⟩

/-- On a path avoiding `s`, two weights agreeing off `s` have the same total. -/
lemma pathWeight_congr_off {s : A} (c c' : ArrowWeight A)
    (hcc : ∀ {x y : RayVert A} (e : x ⟶ y), x.out ≠ s → c' e = c e) {H : Set A}
    (hH : ∀ a ∈ H, a ≠ s) {x : RayVert A} :
    ∀ {y : RayVert A} (p : Quiver.Path x y), PathIn H p → pathWeight c' p = pathWeight c p
  | _, .nil, _ => rfl
  | _, .cons p e, h => by
    rw [pathWeight, pathWeight, pathWeight_congr_off c c' hcc hH p h.1,
      hcc e (hH _ (PathIn.target h.1))]

section Extend

variable [IsRayCategory A]

/-- Arrows connected through common upper bounds in `X` are joined by a walk through `X`. -/
lemma walkConn_of_eqvGen {b : A} {X : Set (BMor b)} {E : BMor b → Set (BMor b)}
    (hE : ∀ M e, e ∈ E M → IsArr e ∧ BLe e M) {e e' : BMor b} (he : IsArr e)
    (h : Relation.EqvGen (HAdj E X) e e') : WalkConn (· ∈ X) e e' := by
  rw [← Relation.EqvGen.reflTransGen_symmGen] at h
  induction h with
  | refl => exact walkConn_refl he
  | @tail a a' _ hab ih =>
    have hab' : HAdj E X a a' := by
      rcases hab with hab | hab
      · exact hab
      · obtain ⟨M, hM, h1, h2⟩ := hab
        exact ⟨M, hM, h2, h1⟩
    obtain ⟨M, hM, h1, h2⟩ := hab'
    exact ih.snoc hM (hE M _ h1).2 (hE M _ h2).1 (hE M _ h2).2

/-- **Extending a cocycle across a minimal point.** -/
theorem exists_extend_min (hL : LeftCancel A) (hR : RightCancel A) (hCB : ChainBounded A)
    {S : Set A} {s : A} (hconv : PathConvex S)
    (hmin : ∀ {x : RayVert A} (_ : x ⟶ RayVert.mk s), x.out ∉ S)
    (c : ArrowWeight A) (hc : IsCocycleOn (S \ {s}) c) :
    ∃ c' : ArrowWeight A, IsCocycleOn S c' ∧
      ∀ {x y : RayVert A} (e : x ⟶ y), x.out ≠ s → c' e = c e := by
  classical
  set H := S \ {s} with hHdef
  -- the weight of a nonzero morphism between points of `H`
  let C : ∀ {y z : A}, (y ⟶ z) → ℤ := fun {y z} ρ ↦
    if h : ρ ≠ 0 then pathWeight c (pathOf ρ h) else 0
  have hC : ∀ {y z : RayVert A} (p : Quiver.Path y z), PathIn H p → pathVal p ≠ 0 →
      pathWeight c p = C (pathVal p) := by
    intro y z p hp h0
    simp only [C, dif_pos h0]
    have hy := PathIn.start hp
    have hz := PathIn.target hp
    refine hc p (pathOf (P := A) (pathVal p) h0) hp
      (pathIn_diff hmin hy.2 _ (hconv (pathOf (P := A) (pathVal p) h0) hy.1 hz.1)) ?_ h0
    exact (pathVal_pathOf _ h0).symm
  -- nonzero morphisms out of `s` into `H`, and the maximal ones
  let F : Set (BMor s) := {m | m.2 ≠ 0 ∧ m.1 ∈ H}
  have hFfin : F.Finite := by
    refine ((IsRayCategory.finite_out s).biUnion fun y _ ↦
      (haveI := IsRayCategory.finite_hom s y; Set.finite_range (Sigma.mk y : (s ⟶ y) → BMor s))
      ).subset ?_
    rintro ⟨y, f⟩ ⟨hf, -⟩
    exact Set.mem_biUnion ⟨f, hf⟩ ⟨f, rfl⟩
  let T : Set (BMor s) := {M | M ∈ F ∧ ∀ m ∈ F, BLe M m → m = M}
  have hTfin : T.Finite := hFfin.subset fun M h ↦ h.1
  have habove : ∀ m ∈ F, ∃ M ∈ T, BLe m M := by
    intro m hm
    obtain ⟨μ, ⟨hμ, hmμ⟩, hmax⟩ := Set.exists_max_image {y : BMor s | y ∈ F ∧ BLe m y}
      (fun y ↦ depth y.2) (hFfin.subset fun y h ↦ h.1) ⟨m, hm, BLe.refl _⟩
    refine ⟨μ, ⟨hμ, fun ν hν hle ↦ ?_⟩, hmμ⟩
    obtain ⟨ρ, hρ⟩ := hle
    by_cases hi : IsIso ρ
    · haveI := hi
      exact (eq_of_comp_isIso ρ hρ).symm
    · have h1 := depth_lt_comp_right μ.2 ρ (by rw [hρ]; exact hν.1) hi
      have h2 := hmax ν ⟨hν, hmμ.trans ⟨ρ, hρ⟩⟩
      rw [hρ] at h1
      omega
  -- the hyperforest
  let E : BMor s → Set (BMor s) := fun M ↦ {e | IsArr e ∧ e.1 ∈ H ∧ BLe e M}
  let r : BMor s → BMor s → ℤ := fun M e ↦ if h : BLe e M then C h.choose else 0
  have hacyc : HAcyclic E (hTfin.toFinset : Set (BMor s)) := by
    rw [Set.Finite.coe_toFinset]
    intro M hM e he e' he' hconn
    have hw := walkConn_of_eqvGen (E := E) (fun M e h ↦ ⟨h.1, h.2.2⟩) he.1 hconn
    refine eq_of_walkConn hR hCB (T := (· ∈ T \ {M})) ?_ (fun m hm ↦ hm.1.1.1) hM.1.1 ?_ hw
      he.2.2 he'.2.2
    · intro m m' hm hm' hle
      exact (hm.1.2 m' hm'.1.1 hle).symm
    · intro m hm
      refine ⟨fun hle ↦ hm.2 ?_, fun hle ↦ hm.2 ?_⟩
      · exact (hm.1.2 M hM.1 hle).symm
      · exact hM.2 m hm.1.1 hle
  obtain ⟨w, hw⟩ := exists_potential r hTfin.toFinset hacyc
  -- the extended weight
  let c' : ArrowWeight A := fun {x y} e ↦
    if h : x.out = s then w ⟨y.out, eqToHom h.symm ≫ e.1⟩ else c e
  have hc'off : ∀ {x y : RayVert A} (e : x ⟶ y), x.out ≠ s → c' e = c e := by
    intro x y e hx
    simp only [c', dif_neg hx]
  refine ⟨c', ?_, hc'off⟩
  have hHs : ∀ a ∈ H, a ≠ s := fun a ha ↦ ha.2
  intro x y p q hp hq hpq h0
  by_cases hx : x.out = s
  swap
  · have hp' := pathIn_diff hmin hx p hp
    have hq' := pathIn_diff hmin hx q hq
    rw [pathWeight_congr_off c c' hc'off hHs p hp', pathWeight_congr_off c c' hc'off hHs q hq']
    exact hc p q hp' hq' hpq h0
  obtain rfl : RayVert.mk s = x := hx.symm
  have hsS : s ∈ S := PathIn.start hp
  have hnoret : ∀ {z : RayVert A} (v : Quiver.Path (RayVert.mk s) z), PathIn S v →
      0 < v.length → z.out ≠ s := by
    intro z v hv hl hz
    cases v with
    | nil => simp at hl
    | cons v' e' =>
      obtain rfl : RayVert.mk s = z := hz.symm
      exact hmin e' (PathIn.target hv.1)
  by_cases hl : p.length = 0
  · have hql : q.length = 0 := by
      by_contra hq0
      exact hnoret q hq (by omega)
        (congrArg RayVert.out (Quiver.Path.eq_of_length_zero p hl)).symm
    obtain rfl := Quiver.Path.eq_of_length_zero p hl
    rw [Quiver.Path.eq_nil_of_length_zero p hl, Quiver.Path.eq_nil_of_length_zero q hql]
  have hy : y.out ≠ s := hnoret p hp (by omega)
  have hql : 0 < q.length := by
    by_contra hq0
    exact hy (congrArg RayVert.out (Quiver.Path.eq_of_length_zero q (by omega))).symm
  -- the maximal morphism above the common value
  have hmF : (⟨y.out, pathVal p⟩ : BMor s) ∈ F := ⟨h0, PathIn.target hp, hy⟩
  obtain ⟨M, hMT, σ, hσ⟩ := habove _ hmF
  have hσ0 : σ ≠ 0 := fun h ↦ hMT.1.1 (by rw [← hσ, h, comp_zero])
  set D := pathWeight c (pathOf (P := A) σ hσ0)
  have key : ∀ {c₁ : RayVert A} (e : RayVert.mk s ⟶ c₁) (p' : Quiver.Path c₁ y),
      PathIn S (e.toPath.comp p') → e.1 ≫ pathVal p' = pathVal p →
      (⟨c₁.out, e.1⟩ : BMor s) ∈ E M ∧
        pathWeight c' (e.toPath.comp p') + D = w ⟨c₁.out, e.1⟩ + r M ⟨c₁.out, e.1⟩ := by
    intro c₁ e p' hin hval
    have hp'S := PathIn.of_comp_right _ p' hin
    have hc₁ : c₁.out ≠ s := by
      intro h
      obtain rfl : RayVert.mk s = c₁ := h.symm
      exact hmin e hsS
    have hp'H := pathIn_diff hmin hc₁ p' hp'S
    have hle : BLe (⟨c₁.out, e.1⟩ : BMor s) M :=
      ⟨pathVal p' ≫ σ, by rw [← hσ, ← hval, Category.assoc]⟩
    refine ⟨⟨e.2, PathIn.start hp'H, hle⟩, ?_⟩
    have hρ : hle.choose = pathVal p' ≫ σ := by
      refine hL e.1 _ _ (hle.choose_spec.trans ?_) ?_
      · rw [← hσ, ← hval, Category.assoc]
      · rw [hle.choose_spec]
        exact hMT.1.1
    have hr : r M ⟨c₁.out, e.1⟩ = C (pathVal p' ≫ σ) := by
      simp only [r, dif_pos hle, hρ]
    have hpo : pathVal (pathOf (P := A) σ hσ0) = σ := pathVal_pathOf (P := A) σ hσ0
    have hcomp0 : pathVal (p'.comp (pathOf (P := A) σ hσ0)) ≠ 0 := by
      rw [pathVal_comp, hpo]
      intro h
      apply hMT.1.1
      rw [← hσ, ← hval, Category.assoc, h, comp_zero]
    have hcompH : PathIn H (p'.comp (pathOf (P := A) σ hσ0)) :=
      pathIn_diff hmin hc₁ _ (hconv (p'.comp (pathOf (P := A) σ hσ0)) (PathIn.start hp'S) hMT.1.2.1)
    have hw1 := hC _ hcompH hcomp0
    rw [pathWeight_comp] at hw1
    have hv : pathVal (p'.comp (pathOf (P := A) σ hσ0)) = pathVal p' ≫ σ := by
      rw [pathVal_comp, hpo]
    rw [hv] at hw1
    have hwp : pathWeight c' (e.toPath.comp p') = w ⟨c₁.out, e.1⟩ + pathWeight c p' := by
      rw [pathWeight_comp, pathWeight_congr_off c c' hc'off hHs p' hp'H]
      congr 1
      show 0 + c' e = _
      simp only [c', dif_pos (rfl : (RayVert.mk s).out = s), eqToHom_refl, Category.id_comp,
        zero_add]
    rw [hwp, hr, ← hw1]
    ring
  obtain ⟨c₁, e, p', -, rfl⟩ := Quiver.Path.eq_toPath_comp_of_length_eq_succ p
    (Nat.succ_pred_eq_of_pos (by omega)).symm
  obtain ⟨c₂, e₂, q', -, rfl⟩ := Quiver.Path.eq_toPath_comp_of_length_eq_succ q
    (Nat.succ_pred_eq_of_pos hql).symm
  obtain ⟨hαE, hα⟩ := key e p' hp (by rw [pathVal_comp, pathVal_toPath])
  obtain ⟨hβE, hβ⟩ := key e₂ q' hq (by rw [hpq, pathVal_comp, pathVal_toPath])
  have := hw M (hTfin.mem_toFinset.2 hMT) _ hαE _ hβE
  linarith

end Extend

end LargeIndecomposable.RayCat
