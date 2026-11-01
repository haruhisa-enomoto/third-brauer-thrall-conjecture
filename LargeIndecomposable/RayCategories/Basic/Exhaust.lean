module

public import LargeIndecomposable.FundamentalGroups.Basic.CocycleExtendMax

/-!
# Exhausting a finite convex set by extremal points

Let `C ⊆ H` be finite convex sets of objects (for reachability along arrows) such that `H`
contains no oriented cycle. Then `H` arises from `C` by adding one point at a time, each
minimal or maximal in the new set, and every intermediate set is convex (Bretscher–Gabriel,
*The standard form of a representation-finite algebra*, 2.7, finite case). With the
extension lemmas this extends every cocycle on `C` to `H` (`exists_extend_cocycle`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

universe v u

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

/-- `y` is reachable from `x` along arrows. -/
def Reaches (x y : A) : Prop := Nonempty (Quiver.Path (RayVert.mk x) (RayVert.mk y))

lemma Reaches.refl (x : A) : Reaches x x := ⟨Quiver.Path.nil⟩

lemma Reaches.trans {x y z : A} (h : Reaches x y) (h' : Reaches y z) : Reaches x z :=
  ⟨h.some.comp h'.some⟩

/-- Convexity for reachability. -/
def ConvexR (S : Set A) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z, Reaches x z → Reaches z y → z ∈ S

/-- No oriented cycle through a point of `H`. -/
def CycleFreeOn (H : Set A) : Prop :=
  ∀ x ∈ H, ∀ p : Quiver.Path (RayVert.mk x) (RayVert.mk x), p.length = 0

lemma pathIn_of_convexR {S : Set A} (hS : ConvexR S) {x : RayVert A} (hx : x.out ∈ S) :
    ∀ {y : RayVert A} (p : Quiver.Path x y), (∃ w ∈ S, Reaches y.out w) → PathIn S p
  | _, .nil, _ => hx
  | _, .cons (b := y') p e, ⟨w, hw, hyw⟩ => by
    have hy'w : Reaches y'.out w := Reaches.trans ⟨e.toPath⟩ hyw
    refine ⟨pathIn_of_convexR hS hx p ⟨w, hw, hy'w⟩, ?_⟩
    exact hS _ hx w hw _ ⟨p.cons e⟩ hyw

lemma pathConvex_of_convexR {S : Set A} (hS : ConvexR S) : PathConvex S := by
  intro x y p hx hy
  exact pathIn_of_convexR hS hx p ⟨y.out, hy, Reaches.refl _⟩

lemma eq_of_reaches_cycle {H : Set A} (hcf : CycleFreeOn H) {t z : A} (ht : t ∈ H)
    (h₁ : Reaches t z) (h₂ : Reaches z t) : z = t := by
  by_contra hne
  obtain ⟨p⟩ := h₁
  obtain ⟨q⟩ := h₂
  have hp : 0 < p.length := by
    by_contra h0
    exact hne (Quiver.Path.eq_of_length_zero p (by omega)).symm
  have := hcf t ht (p.comp q)
  rw [Quiver.Path.length_comp] at this
  omega

/-- A maximal element of a finite set for reachability. -/
lemma exists_max_reaches {H X : Set A} (hcf : CycleFreeOn H) (hXH : X ⊆ H) (hX : X.Finite)
    (hne : X.Nonempty) : ∃ t ∈ X, ∀ x ∈ X, Reaches t x → x = t := by
  classical
  obtain ⟨t, ht, hmin⟩ := Set.exists_min_image X (fun x ↦ {y ∈ X | Reaches x y}.ncard) hX hne
  refine ⟨t, ht, fun x hx htx ↦ ?_⟩
  by_contra hxt
  have hsub : {y ∈ X | Reaches x y} ⊂ {y ∈ X | Reaches t y} := by
    refine ⟨fun y hy ↦ ⟨hy.1, htx.trans hy.2⟩, fun h ↦ hxt ?_⟩
    have := h ⟨ht, Reaches.refl t⟩
    exact (eq_of_reaches_cycle hcf (hXH ht) htx this.2).symm ▸ rfl
  have := Set.ncard_lt_ncard hsub (hX.subset fun y hy ↦ hy.1)
  have := hmin x hx
  omega

/-- A minimal element of a finite set for reachability. -/
lemma exists_min_reaches {H X : Set A} (hcf : CycleFreeOn H) (hXH : X ⊆ H) (hX : X.Finite)
    (hne : X.Nonempty) : ∃ t ∈ X, ∀ x ∈ X, Reaches x t → x = t := by
  classical
  obtain ⟨t, ht, hmin⟩ := Set.exists_min_image X (fun x ↦ {y ∈ X | Reaches y x}.ncard) hX hne
  refine ⟨t, ht, fun x hx hxt ↦ ?_⟩
  by_contra hne'
  have hsub : {y ∈ X | Reaches y x} ⊂ {y ∈ X | Reaches y t} := by
    refine ⟨fun y hy ↦ ⟨hy.1, hy.2.trans hxt⟩, fun h ↦ hne' ?_⟩
    have := h ⟨ht, Reaches.refl t⟩
    exact eq_of_reaches_cycle hcf (hXH ht) this.2 hxt
  have := Set.ncard_lt_ncard hsub (hX.subset fun y hy ↦ hy.1)
  have := hmin x hx
  omega

/-- `t` is minimal in `S`: no arrow into `t` from `S`. -/
def IsMinIn (S : Set A) (t : A) : Prop := ∀ {x : RayVert A} (_ : x ⟶ RayVert.mk t), x.out ∉ S

/-- `t` is maximal in `S`: no arrow from `t` into `S`. -/
def IsMaxIn (S : Set A) (t : A) : Prop := ∀ {y : RayVert A} (_ : RayVert.mk t ⟶ y), y.out ∉ S

/-- **Exhaustion by extremal points.** -/
theorem exhaust (Q : Set A → Prop) {H : Set A} (hHfin : H.Finite) (hH : ConvexR H)
    (hcf : CycleFreeOn H)
    (hstep : ∀ D t, D ⊆ H → t ∈ H → t ∉ D → ConvexR D → ConvexR (insert t D) →
      (IsMinIn (insert t D) t ∨ IsMaxIn (insert t D) t) → Q D → Q (insert t D)) :
    ∀ n : ℕ, ∀ C : Set A, C ⊆ H → ConvexR C → (H \ C).ncard = n → Q C → Q H := by
  intro n
  induction n with
  | zero =>
    intro C hCH _ hn hQ
    have : H \ C = ∅ := (Set.ncard_eq_zero (hHfin.diff)).1 hn
    rwa [show H = C from Set.Subset.antisymm (Set.diff_eq_empty.1 this) hCH]
  | succ n ih =>
    intro C hCH hC hn hQ
    classical
    have hD : (H \ C).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    -- choose the next point
    have key : ∃ t ∈ H \ C, ConvexR (insert t C) ∧
        (IsMinIn (insert t C) t ∨ IsMaxIn (insert t C) t) := by
      have hloop : ∀ t ∈ H, ∀ (e : RayVert.mk t ⟶ RayVert.mk t), False := by
        intro t ht e
        have := hcf t ht e.toPath
        simp at this
      by_cases hX : {x ∈ H \ C | ∃ y ∈ C, Reaches x y}.Nonempty
      · obtain ⟨t, ⟨htD, y, hy, hty⟩, hmax⟩ := exists_max_reaches hcf
          (fun x hx ↦ hx.1.1) (hHfin.subset fun x hx ↦ hx.1.1) hX
        refine ⟨t, htD, ?_, Or.inl ?_⟩
        · rintro a ha b hb z haz hzb
          rcases ha with rfl | ha <;> rcases hb with rfl | hb
          · exact Or.inl (eq_of_reaches_cycle hcf htD.1 haz hzb)
          · by_cases hz : z ∈ C
            · exact Or.inr hz
            · exact Or.inl (hmax z ⟨⟨hH _ htD.1 _ (hCH hb) _ haz hzb, hz⟩, b, hb, hzb⟩ haz)
          · exact absurd (hC _ ha _ hy _ (haz.trans hzb) hty) htD.2
          · exact Or.inr (hC _ ha _ hb _ haz hzb)
        · intro x e hx
          rcases hx with hx | hx
          · obtain rfl : RayVert.mk t = x := hx.symm
            exact hloop t htD.1 e
          · exact htD.2 (hC _ hx _ hy _ ⟨e.toPath⟩ hty)
      · by_cases hY : {x ∈ H \ C | ∃ y ∈ C, Reaches y x}.Nonempty
        · obtain ⟨t, ⟨htD, y, hy, hyt⟩, hmin⟩ := exists_min_reaches hcf
            (fun x hx ↦ hx.1.1) (hHfin.subset fun x hx ↦ hx.1.1) hY
          have hnX : ∀ x ∈ H \ C, ∀ y ∈ C, ¬Reaches x y := fun x hx y hy h ↦ hX ⟨x, hx, y, hy, h⟩
          refine ⟨t, htD, ?_, Or.inr ?_⟩
          · rintro a ha b hb z haz hzb
            rcases ha with rfl | ha <;> rcases hb with rfl | hb
            · exact Or.inl (eq_of_reaches_cycle hcf htD.1 haz hzb)
            · exact absurd (haz.trans hzb) (hnX _ htD _ hb)
            · by_cases hz : z ∈ C
              · exact Or.inr hz
              · exact Or.inl (hmin z ⟨⟨hH _ (hCH ha) _ htD.1 _ haz hzb, hz⟩, a, ha, haz⟩ hzb)
            · exact Or.inr (hC _ ha _ hb _ haz hzb)
          · intro y e hy'
            rcases hy' with hy' | hy'
            · obtain rfl : RayVert.mk t = y := hy'.symm
              exact hloop t htD.1 e
            · exact hnX _ htD _ hy' ⟨e.toPath⟩
        · obtain ⟨t, htD⟩ := hD
          have hnX : ∀ y ∈ C, ¬Reaches t y := fun y hy h ↦ hX ⟨t, htD, y, hy, h⟩
          have hnY : ∀ y ∈ C, ¬Reaches y t := fun y hy h ↦ hY ⟨t, htD, y, hy, h⟩
          refine ⟨t, htD, ?_, Or.inl ?_⟩
          · rintro a ha b hb z haz hzb
            rcases ha with rfl | ha <;> rcases hb with rfl | hb
            · exact Or.inl (eq_of_reaches_cycle hcf htD.1 haz hzb)
            · exact absurd (haz.trans hzb) (hnX _ hb)
            · exact absurd (haz.trans hzb) (hnY _ ha)
            · exact Or.inr (hC _ ha _ hb _ haz hzb)
          · intro x e hx
            rcases hx with hx | hx
            · obtain rfl : RayVert.mk t = x := hx.symm
              exact hloop t htD.1 e
            · exact hnY _ hx ⟨e.toPath⟩
    obtain ⟨t, htD, hconv, hext⟩ := key
    have hsub : insert t C ⊆ H := Set.insert_subset htD.1 hCH
    have hcard : (H \ insert t C).ncard = n := by
      have h1 : H \ C = insert t (H \ insert t C) := by
        ext x
        simp only [Set.mem_diff, Set.mem_insert_iff]
        constructor
        · rintro ⟨hx, hxC⟩
          by_cases hxt : x = t
          · exact Or.inl hxt
          · exact Or.inr ⟨hx, fun h ↦ h.elim hxt hxC⟩
        · rintro (rfl | ⟨hx, hxC⟩)
          · exact htD
          · exact ⟨hx, fun h ↦ hxC (Or.inr h)⟩
      have h2 : t ∉ H \ insert t C := fun h ↦ h.2 (Or.inl rfl)
      rw [h1, Set.ncard_insert_of_notMem h2 (hHfin.diff)] at hn
      omega
    exact ih (insert t C) hsub hconv hcard
      (hstep C t hCH htD.1 htD.2 hC hconv hext hQ)

variable [IsRayCategory A]

/-- **Extending a cocycle from a convex set to a larger finite convex set.** -/
theorem exists_extend_cocycle (hL : LeftCancel A) (hR : RightCancel A) (hCB : ChainBounded A)
    {C H : Set A} (hHfin : H.Finite) (hCH : C ⊆ H) (hC : ConvexR C) (hH : ConvexR H)
    (hcf : CycleFreeOn H) (c : ArrowWeight A) (hc : IsCocycleOn C c) :
    ∃ c' : ArrowWeight A, IsCocycleOn H c' ∧
      ∀ {x y : RayVert A} (e : x ⟶ y), x.out ∈ C → y.out ∈ C → c' e = c e := by
  suffices h : C ⊆ H ∧ ∃ c' : ArrowWeight A, IsCocycleOn H c' ∧
      ∀ {x y : RayVert A} (e : x ⟶ y), x.out ∈ C → y.out ∈ C → c' e = c e from h.2
  refine exhaust (fun D ↦ C ⊆ D ∧ ∃ c' : ArrowWeight A, IsCocycleOn D c' ∧
      ∀ {x y : RayVert A} (e : x ⟶ y), x.out ∈ C → y.out ∈ C → c' e = c e)
    hHfin hH hcf ?_ _ C hCH hC rfl ⟨subset_rfl, c, hc, fun _ _ _ ↦ rfl⟩
  rintro D t hDH htH htD hD hD' hext ⟨hCD, c₁, hc₁, hagree⟩
  have hdiff : insert t D \ {t} = D := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx | hx, hxt⟩
      · exact absurd hx hxt
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, fun h ↦ htD (h ▸ hx)⟩
  have hc₁' : IsCocycleOn (insert t D \ {t}) c₁ := by rwa [hdiff]
  have htC : ∀ a ∈ C, a ≠ t := fun a ha h ↦ htD (h ▸ hCD ha)
  refine ⟨hCD.trans (Set.subset_insert t D), ?_⟩
  rcases hext with hmin | hmax
  · obtain ⟨c', hc', hoff⟩ := exists_extend_min hL hR hCB (pathConvex_of_convexR hD') hmin c₁ hc₁'
    exact ⟨c', hc', fun e hx hy ↦ (hoff e (htC _ hx)).trans (hagree e hx hy)⟩
  · obtain ⟨c', hc', hoff⟩ := exists_extend_max hL hR hCB (pathConvex_of_convexR hD') hmax c₁ hc₁'
    exact ⟨c', hc', fun e hx hy ↦ (hoff e (htC _ hy)).trans (hagree e hx hy)⟩

end LargeIndecomposable.RayCat
