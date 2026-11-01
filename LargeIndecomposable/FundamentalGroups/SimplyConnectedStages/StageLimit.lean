module

public import LargeIndecomposable.FundamentalGroups.SimplyConnectedStages.StageGood
public import LargeIndecomposable.FundamentalGroups.Fischbacher.Lemma52
public import LargeIndecomposable.RayCategories.Basic.Balls
public import LargeIndecomposable.Coverings.UniversalCover.CoverGood

/-!
# The limit step of Satz 5.1

If the stage killing all lifts of the `αᵢ` is good, then so is every stage restoring finitely many
points (`good_finite`, by `good_step`). Every path of the cover lives in such a stage
(`exists_finset_avoids`), so the cover is cycle-free; and for `d` on a path from `a` to `c`,
Lemma 5.2 in a stage containing that path and a fixed path `W : a ⇝ c` gives a chain from `d`
to a point of `W`. Chains have bounded length, and the head of a chain lies in a ball around its
last target (`chain_head_mem_ball`), so the interval `[a, c]` is finite (`coverGood_limit`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits LargeIndecomposable

section ChainBall

variable {A : Type*} [Category A] [HasZeroMorphisms A] [IsRayCategory A]

/-- The head of a chain lies in a ball around its last target. -/
lemma chain_head_mem_ball : ∀ {o : ℕ} (l : List (RayMor A)) (_ : IsChain o l) (h : l ≠ []),
    (l.head h).2.1 ∈ ball (l.getLast h).2.1 (2 * l.length)
  | _, [], _, h => absurd rfl h
  | _, [f], _, _ => by
    simp only [List.head_cons, List.getLast_singleton]
    exact ball_mono _ (Nat.zero_le _) (Set.mem_singleton f.2.1)
  | _, f :: g :: l, hc, _ => by
    obtain ⟨hf0, hlink, hc'⟩ := isChain_cons_cons.1 hc
    have ih := chain_head_mem_ball (g :: l) hc' (List.cons_ne_nil _ _)
    have hg0 : g.2.2 ≠ 0 := hc'.1 g (by simp)
    rw [List.getLast_cons (List.cons_ne_nil _ _), List.head_cons]
    rw [List.head_cons] at ih
    have hlen : 2 * (f :: g :: l).length = 2 * (g :: l).length + 2 := by simp; omega
    rw [hlen]
    unfold Link at hlink
    split_ifs at hlink
    · obtain ⟨he, -, -⟩ := hlink
      rw [he]
      exact ball_mono _ (by omega) ih
    · obtain ⟨he, -, -⟩ := hlink
      have h1 := mem_ball_succ ih (Or.inr ⟨g.2.2, hg0⟩)
      exact mem_ball_succ h1 (he ▸ Or.inl ⟨f.2.2, hf0⟩)

lemma length_le_of_chain1 {N : ℕ} (hN : ∀ l : List (RayMor A), IsChain 0 l → l.length ≤ N)
    {l : List (RayMor A)} (hl : IsChain 1 l) : l.length ≤ N + 1 := by
  have h := hN l.tail ((isChain_add_two 0 l.tail).1 hl.tail)
  rw [List.length_tail] at h
  omega

end ChainBall

lemma pathVerts_toQI {C : Type*} [Category C] [HasZeroMorphisms C] [IsRayCategory C]
    {I : ZeroHomIdeal C} (hI : I.IsProper) {x : RayVert C} :
    ∀ {y : RayVert C} (p : Quiver.Path x y) (h : AvoidsI I p),
      pathVerts (toQI hI p h) = (fun z : C ↦ (⟨z⟩ : CategoryTheory.Quotient I.rel)) '' pathVerts p
  | _, .nil, _ => by
    change {_} = _
    rw [pathVerts, Set.image_singleton]
    rfl
  | _, .cons p e, h => by
    change insert _ (pathVerts (toQI hI p h.1)) = _
    rw [pathVerts_toQI hI p h.1, pathVerts, Set.image_insert_eq]
    rfl

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [LargeIndecomposable.IsFiniteRayCategory0 P]
  [Finite P] {x₀ : P} {ι : Type} {b : P} {d : ι → P} {α : ∀ i, b ⟶ d i}

attribute [local instance] isRayCategory_of_finiteRayCategory

namespace Stage

variable (D : RedData α) (hα : ∀ i, ¬IsIso (α i))

include D hα in
/-- **Finitely many points restored: still good.** -/
lemma good_finite (hLF : LoopFree P) (hL : LeftCancel P) (hR : RightCancel P)
    (hCB : ChainBounded P) (h0 : Good (x₀ := x₀) (α := α) Set.univ)
    (F : Finset (vtx x₀ ⟶ vtx b)) : Good (x₀ := x₀) (α := α) (Set.univ \ (F : Set _)) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using h0
  | insert w F hw ih =>
    have h := good_step D hα hLF hL hR hCB (K := Set.univ \ (F : Set _)) (w₀ := w) ⟨trivial, hw⟩ ih
    have he : (Set.univ \ (F : Set _)) \ {w} = Set.univ \ ((insert w F : Finset _) : Set _) := by
      ext v
      simp only [Set.mem_diff, Set.mem_univ, true_and, Finset.coe_insert, Set.mem_insert_iff,
        Set.mem_singleton_iff, Finset.mem_coe, not_or]
      tauto
    rwa [he] at h

/-- Every path of the cover lives in a stage restoring finitely many points. -/
lemma exists_finset_avoids {a : RayVert (Cover x₀)} : ∀ {c : RayVert (Cover x₀)}
    (p : Quiver.Path a c), ∃ F : Finset (vtx x₀ ⟶ vtx b),
      AvoidsI (arrSetIdeal (killed (x₀ := x₀) (α := α) (Set.univ \ (F : Set _)))) p
  | _, .nil => ⟨∅, trivial⟩
  | _, .cons p e => by
    classical
    obtain ⟨F, hF⟩ := exists_finset_avoids p
    by_cases hk : killed (α := α) Set.univ e
    · obtain ⟨w, -, hx, -⟩ := hk
      refine ⟨insert w F, avoidsI_of_avoidsJ (fun f h ↦ arrSetIdeal_mono
        (Set.diff_subset_diff_right (by simp)) f h) p hF, fun hm ↦ ?_⟩
      obtain ⟨w', hw', hx', -⟩ := mem_of_irreducible _ e hm
      have : w' = w := eq_of_heq (Cover.mk.inj (hx'.symm.trans hx)).2
      exact hw'.2 (by rw [this]; simp)
    · exact ⟨F, hF, fun hm ↦ hk (killed_mono (Set.subset_univ _) e (mem_of_irreducible _ e hm))⟩

lemma avoids_mono {F F' : Finset (vtx x₀ ⟶ vtx b)} (h : F ⊆ F') {a c : RayVert (Cover x₀)}
    {p : Quiver.Path a c}
    (hp : AvoidsI (arrSetIdeal (killed (x₀ := x₀) (α := α) (Set.univ \ (F : Set _)))) p) :
    AvoidsI (arrSetIdeal (killed (x₀ := x₀) (α := α) (Set.univ \ (F' : Set _)))) p :=
  avoidsI_of_avoidsJ (fun f hf ↦ arrSetIdeal_mono
    (Set.diff_subset_diff_right (by exact_mod_cast h)) f hf) p hp

/-- **The limit step.** -/
theorem coverGood_limit (hL : LeftCancel P) (hR : RightCancel P) (hCB : ChainBounded P)
    (hG : ∀ F : Finset (vtx x₀ ⟶ vtx b), Good (x₀ := x₀) (α := α) (Set.univ \ (F : Set _))) :
    CoverGood x₀ := by
  classical
  refine ⟨fun c p ↦ ?_, fun a c ↦ ?_⟩
  · obtain ⟨F, hF⟩ := exists_finset_avoids (α := α) p
    have := (hG F).1 _ (toQI (isProper _) p hF)
    rwa [length_toQI] at this
  · by_cases hne : (interval a c).Nonempty
    swap
    · rw [Set.not_nonempty_iff_eq_empty.1 hne]
      exact Set.finite_empty
    obtain ⟨z, ⟨p₁⟩, ⟨p₂⟩⟩ := hne
    obtain ⟨N, hN⟩ := chainBounded_cover (x₀ := x₀) hCB
    refine ((pathVerts_finite (p₁.comp p₂)).biUnion fun s _ ↦ ball_finite s (2 * (N + 1))).subset
      ?_
    rintro e ⟨⟨v₁⟩, ⟨v₂⟩⟩
    obtain ⟨F₁, h₁⟩ := exists_finset_avoids (α := α) (v₁.comp v₂)
    obtain ⟨F₂, h₂⟩ := exists_finset_avoids (α := α) (p₁.comp p₂)
    have h₁' := avoids_mono (F' := F₁ ∪ F₂) Finset.subset_union_left h₁
    have h₂' := avoids_mono (F' := F₁ ∪ F₂) Finset.subset_union_right h₂
    set K : Set (vtx x₀ ⟶ vtx b) :=
      Set.univ \ ((F₁ ∪ F₂ : Finset (vtx x₀ ⟶ vtx b)) : Set (vtx x₀ ⟶ vtx b)) with hKdef
    obtain ⟨hcf, hint, hsc⟩ : Good (x₀ := x₀) (α := α) K := hG (F₁ ∪ F₂)
    have hcf' : ∀ (x : Y (x₀ := x₀) (α := α) K) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)),
        p.length = 0 := fun x p ↦ hcf _ p
    have hLY : LeftCancel (Y (x₀ := x₀) (α := α) K) := leftCancel_quotient _ (leftCancel_cover hL)
    have hRY : RightCancel (Y (x₀ := x₀) (α := α) K) :=
      rightCancel_quotient _ (rightCancel_cover hR)
    have hCBY : ChainBounded (Y (x₀ := x₀) (α := α) K) := chainBounded_quotI (chainBounded_cover hCB)
    have hscL : ∀ S : Set (Y (x₀ := x₀) (α := α) K),
        S.Finite → ConvexR S → ∀ c', IsCocycleOn S c' → IsCoboundaryOn S c' :=
      fun S hS hSc c' hc' ↦ isCoboundaryOn_of_global hLY hRY hCBY hint hcf' hsc hS hSc c' hc'
    have hd : (⟨e⟩ : Y (x₀ := x₀) (α := α) K) ∈ pathVerts (toQI (isProper _) (v₁.comp v₂) h₁') := by
      rw [pathVerts_toQI, pathVerts_comp]
      exact ⟨e, Or.inl (mem_pathVerts_end v₁), rfl⟩
    obtain ⟨l, hl, hl0, hhead, hlast⟩ := lemma52 hcf' hint hscL hLY hRY hCBY
      (toQI (isProper _) (v₁.comp v₂) h₁') (toQI (isProper _) (p₁.comp p₂) h₂') hd
    have hl' := isChain_liftRMI hl
    have hlen := length_le_of_chain1 hN hl'
    have hne' : l.map liftRMI ≠ [] := by simpa using hl0
    have hball := chain_head_mem_ball (l.map liftRMI) hl' hne'
    rw [List.head_map, List.getLast_map, List.length_map] at hball
    rw [List.length_map] at hlen
    change (l.head hl0).2.1.as ∈ ball (l.getLast hl0).2.1.as _ at hball
    rw [hhead] at hball
    rw [pathVerts_toQI] at hlast
    obtain ⟨s, hs, hs'⟩ := hlast
    rw [← hs'] at hball
    exact Set.mem_biUnion hs (ball_mono _ (by omega) hball)

end Stage

end LargeIndecomposable.RayCat
