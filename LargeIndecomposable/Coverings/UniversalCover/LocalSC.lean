module

public import LargeIndecomposable.FundamentalGroups.Fischbacher.Lemma42

/-!
# Convex pieces of a simply connected category are simply connected

Let `A` be a countable, interval-finite ray category without oriented cycles, chain-bounded
with cancellation, in which every cocycle is a coboundary. Then every cocycle on a finite
convex set `D` is a coboundary on `D` (`isCoboundaryOn_of_global`; Fischbacher 4.1(b),
Bretscher–Gabriel 2.6–2.8, Bongartz, *A criterion for finite representation type*, 2.3):
extend it along an exhaustion of `A` by finite convex hulls (`exists_extend_cocycle`) to a
cocycle on `A`, which is a coboundary.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

universe v u

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [IsRayCategory A]

/-- The convex hull of a set: points between two of its points. -/
def hullOf (T : Set A) : Set A := {z | ∃ a ∈ T, ∃ b ∈ T, Reaches a z ∧ Reaches z b}

lemma subset_hullOf (T : Set A) : T ⊆ hullOf T :=
  fun a ha ↦ ⟨a, ha, a, ha, Reaches.refl a, Reaches.refl a⟩

lemma convexR_hullOf (T : Set A) : ConvexR (hullOf T) := by
  rintro x ⟨a, ha, -, -, hax, -⟩ y ⟨-, -, b, hb, -, hyb⟩ z hxz hzy
  exact ⟨a, ha, b, hb, hax.trans hxz, hzy.trans hyb⟩

lemma hullOf_mono {T T' : Set A} (h : T ⊆ T') : hullOf T ⊆ hullOf T' :=
  fun _ ⟨a, ha, b, hb, h1, h2⟩ ↦ ⟨a, h ha, b, h hb, h1, h2⟩

lemma finite_hullOf (hint : ∀ a b : A, (interval a b).Finite) {T : Set A} (hT : T.Finite) :
    (hullOf T).Finite := by
  refine (hT.biUnion fun a _ ↦ hT.biUnion fun b _ ↦ hint a b).subset ?_
  rintro z ⟨a, ha, b, hb, h1, h2⟩
  exact Set.mem_biUnion ha (Set.mem_biUnion hb ⟨h1, h2⟩)

lemma pathIn_univ {x : RayVert A} : ∀ {y : RayVert A} (p : Quiver.Path x y),
    PathIn (Set.univ : Set A) p
  | _, .nil => Set.mem_univ _
  | _, .cons p _ => ⟨pathIn_univ p, Set.mem_univ _⟩

/-- Weights agreeing on the arrows inside `S` give the same weight to paths inside `S`. -/
lemma pathWeight_congr_in {S : Set A} (c c' : ArrowWeight A)
    (h : ∀ {x y : RayVert A} (e : x ⟶ y), x.out ∈ S → y.out ∈ S → c' e = c e) {x : RayVert A} :
    ∀ {y : RayVert A} (p : Quiver.Path x y), PathIn S p → pathWeight c' p = pathWeight c p
  | _, .nil, _ => rfl
  | _, .cons p e, hp => by
    rw [pathWeight, pathWeight, pathWeight_congr_in c c' h p hp.1, h e (PathIn.target hp.1) hp.2]

/-- An arrow weight, wrapped (to recurse on it). -/
structure AW (A : Type u) [Category.{v} A] [HasZeroMorphisms A] where
  /-- The weight. -/
  w : ArrowWeight A

/-- **Convex pieces are simply connected** (cocycle form). -/
theorem isCoboundaryOn_of_global [Countable A] (hL : LeftCancel A) (hR : RightCancel A)
    (hCB : ChainBounded A) (hint : ∀ a b : A, (interval a b).Finite)
    (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)), p.length = 0)
    (hglob : ∀ c : ArrowWeight A, IsCocycle c → IsCoboundary c) {D : Set A} (hDfin : D.Finite)
    (hD : ConvexR D) (c : ArrowWeight A) (hc : IsCocycleOn D c) : IsCoboundaryOn D c := by
  classical
  rcases isEmpty_or_nonempty A with hA | hA
  · exact ⟨fun _ ↦ 0, fun {x} _ _ _ ↦ (hA.false x).elim⟩
  obtain ⟨f, hf⟩ := exists_surjective_nat A
  let Dm : ℕ → Set A := fun m ↦ hullOf (D ∪ f '' Set.Iic m)
  have hDmfin : ∀ m, (Dm m).Finite := fun m ↦
    finite_hullOf hint (hDfin.union ((Set.finite_Iic m).image f))
  have hDmconv : ∀ m, ConvexR (Dm m) := fun m ↦ convexR_hullOf _
  have hDDm : ∀ m, D ⊆ Dm m := fun m ↦ Set.subset_union_left.trans (subset_hullOf _)
  have hmono : Monotone Dm := fun k m hkm ↦
    hullOf_mono (Set.union_subset_union_right _ (Set.image_mono (Set.Iic_subset_Iic.2 hkm)))
  have hcfm : ∀ m, CycleFreeOn (Dm m) := fun m x _ p ↦ hcf x p
  have step : ∀ m (c₁ : AW A), IsCocycleOn (Dm m) c₁.w → ∃ c₂ : AW A,
      IsCocycleOn (Dm (m + 1)) c₂.w ∧ ∀ {x y : RayVert A} (e : x ⟶ y), x.out ∈ Dm m →
        y.out ∈ Dm m → c₂.w e = c₁.w e := by
    intro m c₁ h
    obtain ⟨c₂, h₂, h₂'⟩ := exists_extend_cocycle hL hR hCB (hDmfin _) (hmono (Nat.le_succ m))
      (hDmconv m) (hDmconv _) (hcfm _) c₁.w h
    exact ⟨⟨c₂⟩, h₂, h₂'⟩
  have start := exists_extend_cocycle hL hR hCB (hDmfin 0) (hDDm 0) hD (hDmconv 0) (hcfm 0) c hc
  have step' : ∀ m (c₁ : AW A), ∃ c₂ : AW A, IsCocycleOn (Dm m) c₁.w →
      IsCocycleOn (Dm (m + 1)) c₂.w ∧ ∀ {x y : RayVert A} (e : x ⟶ y), x.out ∈ Dm m →
        y.out ∈ Dm m → c₂.w e = c₁.w e := by
    intro m c₁
    by_cases h : IsCocycleOn (Dm m) c₁.w
    · obtain ⟨c₂, h₂, h₂'⟩ := step m c₁ h
      exact ⟨c₂, fun _ ↦ ⟨h₂, h₂'⟩⟩
    · exact ⟨c₁, fun h' ↦ (h h').elim⟩
  let F : ℕ → AW A → AW A := fun m c₁ ↦ (step' m c₁).choose
  have hF : ∀ m (c₁ : AW A), IsCocycleOn (Dm m) c₁.w →
      IsCocycleOn (Dm (m + 1)) (F m c₁).w ∧ ∀ {x y : RayVert A} (e : x ⟶ y), x.out ∈ Dm m →
        y.out ∈ Dm m → (F m c₁).w e = c₁.w e := fun m c₁ ↦ (step' m c₁).choose_spec
  let seq : ℕ → AW A := fun m ↦ Nat.rec (motive := fun _ ↦ AW A) ⟨start.choose⟩ F m
  have hseqs : ∀ m, seq (m + 1) = F m (seq m) := fun m ↦ rfl
  have hP : ∀ m, IsCocycleOn (Dm m) (seq m).w := by
    intro m
    induction m with
    | zero => exact start.choose_spec.1
    | succ m ih =>
      rw [hseqs]
      intro x y p q hp hq h1 h2
      exact (hF m (seq m) ih).1 p q hp hq h1 h2
  have hagree1 : ∀ m {x y : RayVert A} (e : x ⟶ y), x.out ∈ Dm m → y.out ∈ Dm m →
      (seq (m + 1)).w e = (seq m).w e := by
    intro m x y e hx hy
    rw [hseqs]
    exact (hF m (seq m) (hP m)).2 e hx hy
  have hagree : ∀ k m, k ≤ m → ∀ {x y : RayVert A} (e : x ⟶ y), x.out ∈ Dm k → y.out ∈ Dm k →
      (seq m).w e = (seq k).w e := by
    intro k m hkm
    induction hkm with
    | refl => intros; rfl
    | @step m hkm ih =>
      intro x y e hx hy
      rw [hagree1 m e (hmono hkm hx) (hmono hkm hy), ih e hx hy]
  -- indices of points
  let idx : A → ℕ := fun a ↦ (hf a).choose
  have hidx : ∀ a m, idx a ≤ m → a ∈ Dm m := fun a m h ↦
    subset_hullOf _ (Or.inr ⟨idx a, h, (hf a).choose_spec⟩)
  let cinf : ArrowWeight A := fun {x y} e ↦ (seq (max (idx x.out) (idx y.out))).w e
  have hcinf : ∀ m {x y : RayVert A} (e : x ⟶ y), x.out ∈ Dm m → y.out ∈ Dm m →
      cinf e = (seq m).w e := by
    intro m x y e hx hy
    have h1 := hagree (max (idx x.out) (idx y.out)) (max m (max (idx x.out) (idx y.out)))
      (le_max_right _ _) e (hidx _ _ (le_max_left _ _)) (hidx _ _ (le_max_right _ _))
    have h2 := hagree m (max m (max (idx x.out) (idx y.out))) (le_max_left _ _) e hx hy
    exact h1.symm.trans h2
  have hcoc : IsCocycle cinf := by
    intro x y p q hpq h0
    let m := max (idx x.out) (idx y.out)
    have hx : x.out ∈ Dm m := hidx _ _ (le_max_left _ _)
    have hy : y.out ∈ Dm m := hidx _ _ (le_max_right _ _)
    have hp := pathConvex_of_convexR (hDmconv m) p hx hy
    have hq := pathConvex_of_convexR (hDmconv m) q hx hy
    rw [pathWeight_congr_in (seq m).w cinf (fun e hx hy ↦ hcinf m e hx hy) p hp,
      pathWeight_congr_in (seq m).w cinf (fun e hx hy ↦ hcinf m e hx hy) q hq]
    exact hP m p q hp hq hpq h0
  obtain ⟨φ, hφ⟩ := hglob cinf hcoc
  refine ⟨fun a ↦ φ (RayVert.mk a), fun {x y} e hx hy ↦ ?_⟩
  change c e = _
  rw [← start.choose_spec.2 e hx hy]
  change (seq 0).w e = _
  rw [← hcinf 0 e (hDDm 0 hx) (hDDm 0 hy)]
  exact hφ e

end LargeIndecomposable.RayCat
