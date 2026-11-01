module

public import LargeIndecomposable.Cleaving.Basic.BipDiagram

/-!
# Oriented trees

For a graph `G` and an orientation `o` of its edges, `OT G o` has an arrow
`a → b` when `o a b`. If `G` is a forest, two paths with the same ends agree
(`RayCat.OT.path_eq`), the quiver is acyclic, and its underlying graph is `G`.
The local cleaving criterion then only asks for nonzero path images and for
non-factorization between different branches at each vertex
(`RayCat.OT.arrowCleaving`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

/-- The quiver of an oriented graph. -/
structure OT {V : Type} (G : SimpleGraph V) (o : V → V → Prop) where
  /-- The underlying vertex. -/
  as : V

namespace OT

variable {V : Type} {G : SimpleGraph V} {o : V → V → Prop}

instance quiver : Quiver.{0} (OT G o) where
  Hom a b := PLift (o a.as b.as)

instance (a b : OT G o) : Subsingleton (a ⟶ b) := inferInstanceAs (Subsingleton (PLift _))

instance (a b : OT G o) : Finite (a ⟶ b) := Finite.of_subsingleton

lemma hom_down {a b : OT G o} (e : a ⟶ b) : o a.as b.as := PLift.down e

/-- The vertex equivalence. -/
def equiv : OT G o ≃ V := ⟨OT.as, OT.mk, fun _ ↦ rfl, fun _ ↦ rfl⟩

instance [Fintype V] : Fintype (OT G o) := Fintype.ofEquiv V equiv.symm

instance [DecidableEq V] : DecidableEq (OT G o) := equiv.decidableEq

section Orient

variable (ho : ∀ a b, o a b → G.Adj a b)
include ho

/-- A path read as a walk in `G`. -/
def toWalk : ∀ {a b : OT G o}, Quiver.Path a b → G.Walk a.as b.as
  | _, _, .nil => .nil
  | _, _, .cons p e => (toWalk p).concat (ho _ _ (hom_down e))

lemma length_toWalk {a b : OT G o} (p : Quiver.Path a b) : (toWalk ho p).length = p.length := by
  induction p with
  | nil => simp [toWalk]
  | cons p e ih => simp [toWalk, ih]

variable (hasym : ∀ a b, o a b → ¬o b a)
include hasym

lemma isChain_toWalk {a b : OT G o} (p : Quiver.Path a b) :
    List.IsChain (· ≠ ·) (toWalk ho p).edges ∧
      ∀ x ∈ (toWalk ho p).edges.getLast?, ∃ c : V, o c b.as ∧ x = s(c, b.as) := by
  induction p with
  | nil => simp [toWalk]
  | @cons b c p e ih =>
    simp only [toWalk, SimpleGraph.Walk.edges_concat, List.concat_eq_append,
      List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.mem_def,
      Option.some.injEq]
    refine ⟨List.IsChain.append ih.1 (List.isChain_singleton _) fun x hx y hy ↦ ?_,
      fun x hx ↦ ⟨b.as, hom_down e, hx.symm⟩⟩
    obtain ⟨d, hd, rfl⟩ := ih.2 x hx
    obtain rfl : s(b.as, c.as) = y := by simpa using hy
    intro hdc
    rcases Sym2.eq_iff.mp hdc with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact (G.irrefl (ho _ _ hd))
    · exact hasym _ _ hd (hom_down e)

lemma toWalk_inj {a : OT G o} : ∀ {b : OT G o} (p q : Quiver.Path a b),
    toWalk ho p = toWalk ho q → p = q
  | _, .nil, .nil, _ => rfl
  | _, .nil, .cons q e, h => by
    have := congrArg SimpleGraph.Walk.length h
    rw [length_toWalk, length_toWalk] at this
    simp at this
  | _, .cons p e, .nil, h => by
    have := congrArg SimpleGraph.Walk.length h
    rw [length_toWalk, length_toWalk] at this
    simp at this
  | _, .cons (b := c) p e, .cons (b := c') q e', h => by
    have h' : (toWalk ho p).concat (ho _ _ (hom_down e)) =
        (toWalk ho q).concat (ho _ _ (hom_down e')) := by
      simp only [toWalk] at h; exact h
    obtain ⟨hv, hpq⟩ := SimpleGraph.Walk.concat_inj h'
    obtain rfl : c = c' := congrArg OT.mk hv
    simp only [SimpleGraph.Walk.copy_rfl_rfl] at hpq
    rw [toWalk_inj p q hpq, Subsingleton.elim e e']

/-- **Paths in an oriented forest are unique.** -/
lemma path_eq (hG : G.IsAcyclic) {a b : OT G o} (p q : Quiver.Path a b) : p = q := by
  apply toWalk_inj ho hasym
  have hp := (hG.isPath_iff_isChain _).2 (isChain_toWalk ho hasym p).1
  have hq := (hG.isPath_iff_isChain _).2 (isChain_toWalk ho hasym q).1
  exact congrArg Subtype.val ((hG.subsingleton_path _ _).elim ⟨_, hp⟩ ⟨_, hq⟩)

lemma isAcyclic (hG : G.IsAcyclic) : LargeIndecomposable.Foundations.Quiver.IsAcyclic (OT G o) := by
  rw [LargeIndecomposable.Foundations.Quiver.isAcyclic_def]
  intro a p
  exact path_eq ho hasym hG p _

variable (hcov : ∀ a b, G.Adj a b → o a b ∨ o b a)
include hcov

omit hasym in
/-- The underlying graph is `G`. -/
def graphIso : LargeIndecomposable.Foundations.Quiver.underlyingGraph (OT G o) ≃g G where
  toEquiv := equiv
  map_rel_iff' {a b} := by
    change G.Adj a.as b.as ↔ _
    rw [LargeIndecomposable.Foundations.Quiver.underlyingGraph_adj]
    constructor
    · intro h
      refine ⟨fun e ↦ G.irrefl (e ▸ h), ?_⟩
      rcases hcov _ _ h with h' | h'
      · exact Or.inl ⟨⟨h'⟩⟩
      · exact Or.inr ⟨⟨h'⟩⟩
    · rintro ⟨-, ⟨e⟩ | ⟨e⟩⟩
      · exact ho _ _ (hom_down e.some)
      · exact (ho _ _ (hom_down e.some)).symm

end Orient

section Cleaving

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]
  {F : PathCat (OT G o) ⥤ P} [F.PreservesZeroMorphisms]

/-- **The local cleaving criterion for oriented forests.** -/
theorem arrowCleaving (ho : ∀ a b, o a b → G.Adj a b) (hasym : ∀ a b, o a b → ¬o b a)
    (hG : G.IsAcyclic)
    (h0 : ∀ {a b : OT G o} (p : Quiver.Path a b), F.map (PathCat.ofPath p) ≠ 0)
    (hiso : ∀ {a b : OT G o} (e : a ⟶ b), ¬IsIso (F.map (PathCat.ofPath e.toPath)))
    (hl : ∀ {a c c' b : OT G o} (e : a ⟶ c) (e' : a ⟶ c') (q : Quiver.Path c' b), c ≠ c' →
      ¬∃ g, F.map (PathCat.ofPath e.toPath) ≫ g = F.map (PathCat.ofPath (e'.toPath.comp q)))
    (hr : ∀ {a c c' b : OT G o} (e : c ⟶ b) (e' : c' ⟶ b) (q : Quiver.Path a c'), c ≠ c' →
      ¬∃ g, g ≫ F.map (PathCat.ofPath e.toPath) = F.map (PathCat.ofPath (q.cons e'))) :
    PathCat.ArrowCleaving F where
  ne_zero p := h0 p
  injective p q _ := path_eq ho hasym hG p q
  left {a c b} e p := by
    rintro ⟨g, hg⟩
    cases hlen : p.length with
    | zero =>
      obtain rfl : b = a := by
        cases p with
        | nil => rfl
        | cons p e => simp at hlen
      obtain rfl : p = Quiver.Path.nil := path_eq ho hasym hG _ _
      rw [PathCat.map_ofPath_nil] at hg
      exact (hiso e (isIso_of_isIso_comp _ g (fun h ↦ h0 _ (h)) (by rw [hg]; infer_instance))).elim
    | succ n =>
      obtain ⟨c', e', q, -, rfl⟩ := Quiver.Path.eq_toPath_comp_of_length_eq_succ p hlen
      by_cases hc : c = c'
      · subst hc
        exact ⟨q, by rw [Subsingleton.elim e e']⟩
      · exact (hl e e' q hc ⟨g, hg⟩).elim
  right {a c b} e p := by
    rintro ⟨g, hg⟩
    cases p with
    | nil =>
      rw [PathCat.map_ofPath_nil] at hg
      have hg0 : g ≠ 0 := fun h ↦ IsRayCategory.id_ne_zero _ (by rw [← hg, h, zero_comp])
      have hc : IsIso (g ≫ F.map (PathCat.ofPath e.toPath)) := by rw [hg]; infer_instance
      have := isIso_of_isIso_comp g (F.map (PathCat.ofPath e.toPath)) hg0 hc
      exact (hiso e (IsIso.of_isIso_comp_left g _)).elim
    | cons q e' =>
      rename_i c'
      by_cases hc : c = c'
      · subst hc
        exact ⟨q, by rw [Subsingleton.elim e e']⟩
      · exact (hr e e' q hc ⟨g, hg⟩).elim

end Cleaving

end OT

end RayCat

end LargeIndecomposable

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

lemma composePath_comp_functor {Q : Type} [Quiver.{0} Q] {C D : Type*} [Category C] [Category D]
    (φ : Q ⥤q C) (H : C ⥤ D) {a b : Q} (p : Quiver.Path a b) :
    composePath ((φ ⋙q H.toPrefunctor).mapPath p) = H.map (composePath (φ.mapPath p)) := by
  induction p with
  | nil => exact (H.map_id _).symm
  | cons p e ih =>
    change composePath ((φ ⋙q H.toPrefunctor).mapPath p) ≫ H.map (φ.map e) =
      H.map (composePath (φ.mapPath p) ≫ φ.map e)
    rw [ih]
    exact (H.map_comp _ _).symm

/-- The value in `P` of a path of a diagram. -/
abbrev pval {Q : Type} [Quiver.{0} Q] {C : Type*} [Category C] (φ : Q ⥤q C) {a b : Q}
    (p : Quiver.Path a b) : φ.obj a ⟶ φ.obj b := composePath (φ.mapPath p)

namespace OT

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {o : V → V → Prop}
  (ho : ∀ a b, o a b → G.Adj a b) (hcov : ∀ a b, G.Adj a b → o a b ∨ o b a)
  [Fact (LargeIndecomposable.Foundations.Quiver.IsAcyclic (OT G o))] (k : Type*) [Field k]

open LargeIndecomposable.Foundations.Quiver

include ho hcov

/-- An oriented tree containing `D̃ₘ₊₄` is representation-infinite. -/
theorem not_isRepresentationFinite_affineD (m : ℕ)
    (f : (underlyingGraph (AffineD m)).Copy G) :
    ¬Statement.IsRepresentationFinite (RayQuiver.Linearization (PathCat (OT G o)) k) :=
  not_isRepresentationFinite_of_copy_affineD m
    ((graphIso ho hcov).symm.toEmbedding.toCopy.comp f)

/-- An oriented tree containing `Ẽ₆` is representation-infinite. -/
theorem not_isRepresentationFinite_affineE6 (f : (underlyingGraph AffineE6).Copy G) :
    ¬Statement.IsRepresentationFinite (RayQuiver.Linearization (PathCat (OT G o)) k) :=
  not_isRepresentationFinite_of_copy_affineE6 ((graphIso ho hcov).symm.toEmbedding.toCopy.comp f)

/-- An oriented tree containing `Ẽ₇` is representation-infinite. -/
theorem not_isRepresentationFinite_affineE7 (f : (underlyingGraph AffineE7).Copy G) :
    ¬Statement.IsRepresentationFinite (RayQuiver.Linearization (PathCat (OT G o)) k) :=
  not_isRepresentationFinite_of_copy_affineE7 ((graphIso ho hcov).symm.toEmbedding.toCopy.comp f)

/-- An oriented tree containing `Ẽ₈` is representation-infinite. -/
theorem not_isRepresentationFinite_affineE8 (f : (underlyingGraph AffineE8).Copy G) :
    ¬Statement.IsRepresentationFinite (RayQuiver.Linearization (PathCat (OT G o)) k) :=
  not_isRepresentationFinite_of_copy_affineE8 ((graphIso ho hcov).symm.toEmbedding.toCopy.comp f)

end OT

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **No oriented-tree cleaving diagram in `P/τ`.** -/
theorem not_ot_diagram
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (o : V → V → Prop) (ho : ∀ a b, o a b → G.Adj a b) (hasym : ∀ a b, o a b → ¬o b a)
    (hG : G.IsAcyclic) [Fact (LargeIndecomposable.Foundations.Quiver.IsAcyclic (OT G o))]
    (hD : ¬Statement.IsRepresentationFinite (Linearization (PathCat (OT G o)) k))
    (φ : OT G o ⥤q P)
    (h0 : ∀ {x y : OT G o} (p : Quiver.Path x y), 0 < p.length →
      ¬FactorsThroughMorphism τ (pval φ p))
    (hiso : ∀ {x y : OT G o} (e : x ⟶ y), ¬IsIso (φ.map e))
    (hl : ∀ {x c c' y : OT G o} (e : x ⟶ c) (e' : x ⟶ c') (q : Quiver.Path c' y), c ≠ c' →
      ¬∃ g, φ.map e ≫ g = pval φ (e'.toPath.comp q))
    (hr : ∀ {x c c' y : OT G o} (e : c ⟶ y) (e' : c' ⟶ y) (q : Quiver.Path x c'), c ≠ c' →
      ¬∃ g, g ≫ φ.map e = pval φ (q.cons e')) :
    False := by
  letI := rayResidueCategory_isFiniteRayCategory τ hτ
  letI : IsRayCategory (RayCat.Res τ) := isRayCategory_of_finiteRayCategory
  let F := PathCat.lift (φ ⋙q (resF τ).toPrefunctor)
  have hFp : ∀ {x y : OT G o} (p : Quiver.Path x y),
      F.map (PathCat.ofPath p) = (resF τ).map (pval φ p) := fun p ↦ by
    rw [PathCat.lift_map_ofPath, composePath_comp_functor]
  have h0' : ∀ {x y : OT G o} (p : Quiver.Path x y), ¬FactorsThroughMorphism τ (pval φ p) := by
    intro x y p
    cases p with
    | nil => exact not_factorsThrough_id hτ _
    | cons p e => exact h0 _ (by simp)
  have hval : ∀ {x y : OT G o} (e : x ⟶ y), pval φ e.toPath = φ.map e := fun e ↦
    Category.id_comp _
  refine B.not_pathCat_cleaving_res hmin hL hR τ hτ hτ0 hD F
    (OT.arrowCleaving ho hasym hG (fun p ↦ ?_) (fun e ↦ ?_) (fun e e' q h ↦ ?_)
      (fun e e' q h ↦ ?_))
  · rw [hFp]
    exact fun h ↦ h0' p ((rayResidueFunctor_map_eq_zero_iff τ _).1 h)
  · rw [hFp, hval]
    intro hi
    obtain ⟨c, hc1, -⟩ := hi.out
    let c' : (resF τ).obj (φ.obj _) ⟶ (resF τ).obj (φ.obj _) := c
    have h1 : 𝟙 _ = φ.map e ≫ lift τ c' := by
      refine resF_map_injective τ (not_factorsThrough_id hτ _) ?_
      rw [Functor.map_comp, resF_lift, CategoryTheory.Functor.map_id]
      exact hc1.symm
    have hne : φ.map e ≠ 0 := fun h ↦ h0' e.toPath (by rw [hval, h]; exact ⟨0, 0, by simp⟩)
    exact hiso e (isIso_of_isIso_comp _ _ hne (by rw [← h1]; infer_instance))
  · rw [hFp, hFp, hval]
    rintro ⟨g, hg⟩
    let g' : (resF τ).obj (φ.obj _) ⟶ (resF τ).obj (φ.obj _) := g
    have hg' : (resF τ).map (φ.map e) ≫ (resF τ).map (lift τ g') =
        (resF τ).map (pval φ (e'.toPath.comp q)) := by rw [resF_lift]; exact hg
    refine hl e e' q h ⟨lift τ g', (resF_map_injective τ (h0' _) ?_).symm⟩
    rw [Functor.map_comp, hg']
  · rw [hFp, hFp, hval]
    rintro ⟨g, hg⟩
    let g' : (resF τ).obj (φ.obj _) ⟶ (resF τ).obj (φ.obj _) := g
    have hg' : (resF τ).map (lift τ g') ≫ (resF τ).map (φ.map e) =
        (resF τ).map (pval φ (q.cons e')) := by rw [resF_lift]; exact hg
    refine hr e e' q h ⟨lift τ g', (resF_map_injective τ (h0' _) ?_).symm⟩
    rw [Functor.map_comp, hg']

end MulBasis

end RayQuiver

end LargeIndecomposable
