module

public import LargeIndecomposable.MildContours.Basic.SetupOp
public import LargeIndecomposable.RayCategories.Basic.MorphismDepth
public import LargeIndecomposable.RayCategories.ClosedChains.ClosedChainOf
public import LargeIndecomposable.MildContours.Basic.EndCyclic
public import LargeIndecomposable.MildContours.Basic.Assembly

/-!
# Global facts about the ray category of a minimal representation-infinite algebra

Two consequences of minimality used in [mild] §4, stated for a ray category:

* `NoProjInj`: no nonzero `μ₀ : x ⟶ z` is both the unique right-deep ray out of
  `x` and the unique left-deep ray into `z` (no projective-injective `B e_x`);
* `NoSplit`: no point `z` splits the category into a receiver part and an
  emitter part with nonzero morphisms on both sides.

Both are symmetric under passing to `Pᵒᵖ` (`NoProjInj.op`, `NoSplit.op`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Opposite

namespace RayCat

variable {Q : Type*} [Category Q] [HasZeroMorphisms Q]

/-- `μ` is killed by every non-invertible morphism after it. -/
def RightDeep {x y : Q} (μ : x ⟶ y) : Prop := ∀ {w : Q} (ζ : y ⟶ w), ¬IsIso ζ → μ ≫ ζ = 0

/-- `μ` is killed by every non-invertible morphism before it. -/
def LeftDeep {w x : Q} (μ : w ⟶ x) : Prop := ∀ {u : Q} (ζ : u ⟶ w), ¬IsIso ζ → ζ ≫ μ = 0

/-- `μ₀` is the unique right-deep ray out of `x` and the unique left-deep ray into
`z` (`B e_x` is projective-injective with socle the ray of `μ₀`). -/
def ProjInjAt {x z : Q} (μ₀ : x ⟶ z) : Prop :=
  μ₀ ≠ 0 ∧ RightDeep μ₀ ∧ LeftDeep μ₀ ∧
    (∀ {y : Q} (μ : x ⟶ y), μ ≠ 0 → RightDeep μ → ∃ h : y = z, μ ≫ eqToHom h = μ₀) ∧
    (∀ {w : Q} (ν : w ⟶ z), ν ≠ 0 → LeftDeep ν → ∃ h : w = x, eqToHom h.symm ≫ ν = μ₀)

/-- No projective-injective vertex. -/
def NoProjInj (Q : Type) [Category.{0} Q] [HasZeroMorphisms Q] : Prop :=
  ∀ {x z : Q} (μ₀ : x ⟶ z), ¬ProjInjAt μ₀

/-- A **tiny penny-farthing point** `x` ([Standard] §3.1, §3.2): `s : x ⟶ z` is the
unique left-deep ray into `z`, the right-deep rays out of `x` are `s` and an
irreducible `t : x ⟶ b` (`b ≠ z`, `b ≠ x`), and every non-invertible morphism into `b`
factors through `t`. Then the indecomposables not killed by `s` are `B e_x` and
`B e_x / (t)` (`RepresentationType/MinimalInfinite/Tiny.lean`), so `B` is not minimal
representation-infinite. -/
def TinyAt {x z b : Q} (s : x ⟶ z) (t : x ⟶ b) : Prop :=
  s ≠ 0 ∧ t ≠ 0 ∧ z ≠ b ∧ x ≠ b ∧ RightDeep s ∧ LeftDeep s ∧ RightDeep t ∧
    (∀ {y : Q} (a : x ⟶ y) (c : y ⟶ b), a ≫ c = t → IsIso a ∨ IsIso c) ∧
    (∀ {y : Q} (μ : x ⟶ y), μ ≠ 0 → RightDeep μ →
      (∃ h : y = z, μ ≫ eqToHom h = s) ∨ (∃ h : y = b, μ ≫ eqToHom h = t)) ∧
    (∀ {w : Q} (ν : w ⟶ z), ν ≠ 0 → LeftDeep ν → ∃ h : w = x, eqToHom h.symm ≫ ν = s) ∧
    (∀ {y : Q} (ν : y ⟶ b), ¬IsIso ν → ∃ ν' : y ⟶ x, ν = ν' ≫ t)

/-- No tiny penny-farthing point. -/
def NoTiny (Q : Type) [Category.{0} Q] [HasZeroMorphisms Q] : Prop :=
  ∀ {x z b : Q} (s : x ⟶ z) (t : x ⟶ b), ¬TinyAt s t

/-- A splitting of the point `z`: `V₁` receives into `z`, the rest `V₂` (without
`z`) is reached from `z`, there is nothing else between the parts, `z` has no
nonzero radical endomorphism, and both sides are nonzero. -/
def SplitAt (V₁ : Set Q) (z : Q) : Prop :=
  z ∉ V₁ ∧
    (∀ i ∈ V₁, ∀ j, j ∉ V₁ → j ≠ z → ∀ f : i ⟶ j, f = 0) ∧
    (∀ i, i ∉ V₁ → i ≠ z → ∀ j ∈ V₁, ∀ f : i ⟶ j, f = 0) ∧
    (∀ i, i ∉ V₁ → i ≠ z → ∀ f : i ⟶ z, f = 0) ∧
    (∀ j ∈ V₁, ∀ f : z ⟶ j, f = 0) ∧
    (∀ f : z ⟶ z, ¬IsIso f → f = 0) ∧
    (∃ i ∈ V₁, ∃ f : i ⟶ z, f ≠ 0) ∧
    (∃ j, j ∉ V₁ ∧ j ≠ z ∧ ∃ f : z ⟶ j, f ≠ 0)

/-- No split point. -/
def NoSplit (Q : Type) [Category.{0} Q] [HasZeroMorphisms Q] : Prop :=
  ∀ (V₁ : Set Q) (z : Q), ¬SplitAt V₁ z

lemma rightDeep_op {x y : Q} {μ : x ⟶ y} : RightDeep μ.op ↔ LeftDeep μ := by
  constructor
  · intro h u ζ hζ
    have := h ζ.op (fun hi ↦ hζ ((isIso_op_iff ζ).1 hi))
    exact Quiver.Hom.op_inj (by rw [op_comp, this, op_zero])
  · intro h W ζ hζ
    have := h ζ.unop (fun hi ↦ hζ ((isIso_unop_iff ζ).1 hi))
    exact Quiver.Hom.unop_inj (by rw [unop_comp, Quiver.Hom.unop_op, this, unop_zero])

lemma leftDeep_op {x y : Q} {μ : x ⟶ y} : LeftDeep μ.op ↔ RightDeep μ := by
  constructor
  · intro h w ζ hζ
    have := h ζ.op (fun hi ↦ hζ ((isIso_op_iff ζ).1 hi))
    exact Quiver.Hom.op_inj (by rw [op_comp, this, op_zero])
  · intro h U ζ hζ
    have := h ζ.unop (fun hi ↦ hζ ((isIso_unop_iff ζ).1 hi))
    exact Quiver.Hom.unop_inj (by rw [unop_comp, Quiver.Hom.unop_op, this, unop_zero])

/-- A projective-injective vertex of `Qᵒᵖ` reverses to one of `Q`. -/
lemma projInjAt_unop {X Z : Qᵒᵖ} {μ₀ : X ⟶ Z} (h : ProjInjAt μ₀) : ProjInjAt μ₀.unop := by
  obtain ⟨h0, hr, hl, hu, hu'⟩ := h
  refine ⟨fun h ↦ h0 (Quiver.Hom.unop_inj (by rw [h, unop_zero])),
    leftDeep_op.1 hl, rightDeep_op.1 hr, fun {y} μ hμ hd ↦ ?_, fun {w} ν hν hd ↦ ?_⟩
  · obtain ⟨hX, he⟩ := hu' μ.op (fun h ↦ hμ (Quiver.Hom.op_inj (by rw [h, op_zero])))
      (leftDeep_op.2 hd)
    obtain ⟨X⟩ := X
    have hX' : y = X := congrArg unop hX
    subst hX'
    refine ⟨rfl, ?_⟩
    have := congrArg Quiver.Hom.unop he
    simpa using this
  · obtain ⟨hZ, he⟩ := hu ν.op (fun h ↦ hν (Quiver.Hom.op_inj (by rw [h, op_zero])))
      (rightDeep_op.2 hd)
    obtain ⟨Z⟩ := Z
    have hZ' : w = Z := congrArg unop hZ
    subst hZ'
    refine ⟨rfl, ?_⟩
    have := congrArg Quiver.Hom.unop he
    simpa using this

lemma NoProjInj.op {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] (h : NoProjInj Q) : NoProjInj Qᵒᵖ := fun μ₀ hμ ↦ h _ (projInjAt_unop hμ)

/-- A split point of `Qᵒᵖ` is one of `Q`, with the parts exchanged. -/
lemma splitAt_unop {V₁ : Set Qᵒᵖ} {Z : Qᵒᵖ} (h : SplitAt V₁ Z) :
    SplitAt {j : Q | op j ∉ V₁ ∧ op j ≠ Z} Z.unop := by
  obtain ⟨hz, h12, h21, h2z, hz1, hzz, ⟨i, hi, f, hf⟩, ⟨j, hj, hjz, g, hg⟩⟩ := h
  refine ⟨fun h ↦ h.2 rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj hjz f
    have hj' : op j ∈ V₁ := by
      by_contra hn; exact hj ⟨hn, fun h ↦ hjz (congrArg unop h)⟩
    exact Quiver.Hom.op_inj (by rw [h12 (op j) hj' (op i) hi.1 hi.2 f.op, op_zero])
  · intro i hi hiz j hj f
    have hi' : op i ∈ V₁ := by
      by_contra hn; exact hi ⟨hn, fun h ↦ hiz (congrArg unop h)⟩
    exact Quiver.Hom.op_inj (by rw [h21 (op j) hj.1 hj.2 (op i) hi' f.op, op_zero])
  · intro i hi hiz f
    have hi' : op i ∈ V₁ := by
      by_contra hn; exact hi ⟨hn, fun h ↦ hiz (congrArg unop h)⟩
    exact Quiver.Hom.op_inj (by rw [hz1 (op i) hi' f.op, op_zero])
  · intro j hj f
    exact Quiver.Hom.op_inj (by rw [h2z (op j) hj.1 hj.2 f.op, op_zero])
  · intro f hf
    exact Quiver.Hom.op_inj (by
      rw [hzz f.op (fun hi ↦ hf ((isIso_op_iff f).1 hi)), op_zero])
  · exact ⟨j.unop, ⟨hj, hjz⟩, g.unop, fun h ↦ hg (Quiver.Hom.unop_inj (by rw [h, unop_zero]))⟩
  · refine ⟨i.unop, fun h ↦ h.1 hi, fun h ↦ hz (by
      have : i = Z := congrArg op h
      rw [← this]; exact hi), f.unop,
      fun h ↦ hf (Quiver.Hom.unop_inj (by rw [h, unop_zero]))⟩

lemma NoSplit.op {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] (h : NoSplit Q) : NoSplit Qᵒᵖ := fun V₁ Z hs ↦ h _ _ (splitAt_unop hs)

/-- The dual of `TinyAt` (a tiny point of `Qᵒᵖ`, read in `Q`). -/
def TinyAtDual {x z b : Q} (s : z ⟶ x) (t : b ⟶ x) : Prop :=
  s ≠ 0 ∧ t ≠ 0 ∧ z ≠ b ∧ x ≠ b ∧ LeftDeep s ∧ RightDeep s ∧ LeftDeep t ∧
    (∀ {y : Q} (c : b ⟶ y) (a : y ⟶ x), c ≫ a = t → IsIso c ∨ IsIso a) ∧
    (∀ {y : Q} (ν : y ⟶ x), ν ≠ 0 → LeftDeep ν →
      (∃ h : y = z, eqToHom h.symm ≫ ν = s) ∨ (∃ h : y = b, eqToHom h.symm ≫ ν = t)) ∧
    (∀ {w : Q} (μ : z ⟶ w), μ ≠ 0 → RightDeep μ → ∃ h : w = x, μ ≫ eqToHom h = s) ∧
    (∀ {y : Q} (μ : b ⟶ y), ¬IsIso μ → ∃ μ' : x ⟶ y, μ = t ≫ μ')

/-- A tiny point of `Qᵒᵖ` is a dual tiny point of `Q`. -/
lemma tinyAtDual_of_op {X Z Bp : Qᵒᵖ} {s : X ⟶ Z} {t : X ⟶ Bp} (h : TinyAt s t) :
    TinyAtDual s.unop t.unop := by
  obtain ⟨hs0, ht0, hzb, hxb, hsR, hsL, htR, hirr, hRu, hLu, hfac⟩ := h
  refine ⟨fun h ↦ hs0 (Quiver.Hom.unop_inj (by rw [h, unop_zero])),
    fun h ↦ ht0 (Quiver.Hom.unop_inj (by rw [h, unop_zero])),
    fun h ↦ hzb (Opposite.unop_injective h), fun h ↦ hxb (Opposite.unop_injective h),
    (rightDeep_op (μ := s.unop)).1 hsR, (leftDeep_op (μ := s.unop)).1 hsL,
    (rightDeep_op (μ := t.unop)).1 htR, ?_, ?_, ?_, ?_⟩
  · intro y c a hca
    rcases hirr a.op c.op (by rw [← op_comp, hca]; rfl) with h | h
    · exact Or.inr ((isIso_op_iff a).1 h)
    · exact Or.inl ((isIso_op_iff c).1 h)
  · intro y ν hν0 hν
    rcases hRu ν.op (fun h ↦ hν0 (Quiver.Hom.op_inj (by rw [h, op_zero])))
      ((rightDeep_op (μ := ν)).2 hν) with ⟨h, he⟩ | ⟨h, he⟩
    · left
      obtain ⟨z⟩ := Z
      have h' : y = z := Opposite.op_injective h
      subst h'
      refine ⟨rfl, ?_⟩
      rw [eqToHom_refl, Category.comp_id] at he
      rw [eqToHom_refl, Category.id_comp, ← he]; rfl
    · right
      obtain ⟨b⟩ := Bp
      have h' : y = b := Opposite.op_injective h
      subst h'
      refine ⟨rfl, ?_⟩
      rw [eqToHom_refl, Category.comp_id] at he
      rw [eqToHom_refl, Category.id_comp, ← he]; rfl
  · intro w μ hμ0 hμ
    obtain ⟨h, he⟩ := hLu μ.op (fun h ↦ hμ0 (Quiver.Hom.op_inj (by rw [h, op_zero])))
      ((leftDeep_op (μ := μ)).2 hμ)
    obtain ⟨x⟩ := X
    have h' : w = x := Opposite.op_injective h
    subst h'
    refine ⟨rfl, ?_⟩
    rw [eqToHom_refl, Category.id_comp] at he
    rw [eqToHom_refl, Category.comp_id, ← he]; rfl
  · intro y μ hμ
    obtain ⟨ν', hν'⟩ := hfac μ.op (fun h ↦ hμ ((isIso_op_iff μ).1 h))
    exact ⟨ν'.unop, by rw [← Quiver.Hom.op_inj.eq_iff, op_comp, hν']; rfl⟩

/-- A dual tiny point of `Qᵒᵖ` is a tiny point of `Q`. -/
lemma tinyAt_of_dual_op {X Z Bp : Qᵒᵖ} {s : Z ⟶ X} {t : Bp ⟶ X} (h : TinyAtDual s t) :
    TinyAt s.unop t.unop := by
  obtain ⟨hs0, ht0, hzb, hxb, hsL, hsR, htL, hirr, hLu, hRu, hfac⟩ := h
  refine ⟨fun h ↦ hs0 (Quiver.Hom.unop_inj (by rw [h, unop_zero])),
    fun h ↦ ht0 (Quiver.Hom.unop_inj (by rw [h, unop_zero])),
    fun h ↦ hzb (Opposite.unop_injective h), fun h ↦ hxb (Opposite.unop_injective h),
    (leftDeep_op (μ := s.unop)).1 hsL, (rightDeep_op (μ := s.unop)).1 hsR,
    (leftDeep_op (μ := t.unop)).1 htL, ?_, ?_, ?_, ?_⟩
  · intro y a c hac
    rcases hirr c.op a.op (by rw [← op_comp, hac]; rfl) with h | h
    · exact Or.inr ((isIso_op_iff c).1 h)
    · exact Or.inl ((isIso_op_iff a).1 h)
  · intro y μ hμ0 hμ
    rcases hLu μ.op (fun h ↦ hμ0 (Quiver.Hom.op_inj (by rw [h, op_zero])))
      ((leftDeep_op (μ := μ)).2 hμ) with ⟨h, he⟩ | ⟨h, he⟩
    · left
      obtain ⟨z⟩ := Z
      have h' : y = z := Opposite.op_injective h
      subst h'
      refine ⟨rfl, ?_⟩
      rw [eqToHom_refl, Category.id_comp] at he
      rw [eqToHom_refl, Category.comp_id, ← he]; rfl
    · right
      obtain ⟨b⟩ := Bp
      have h' : y = b := Opposite.op_injective h
      subst h'
      refine ⟨rfl, ?_⟩
      rw [eqToHom_refl, Category.id_comp] at he
      rw [eqToHom_refl, Category.comp_id, ← he]; rfl
  · intro w ν hν0 hν
    obtain ⟨h, he⟩ := hRu ν.op (fun h ↦ hν0 (Quiver.Hom.op_inj (by rw [h, op_zero])))
      ((rightDeep_op (μ := ν)).2 hν)
    obtain ⟨x⟩ := X
    have h' : w = x := Opposite.op_injective h
    subst h'
    refine ⟨rfl, ?_⟩
    rw [eqToHom_refl, Category.comp_id] at he
    rw [eqToHom_refl, Category.id_comp, ← he]; rfl
  · intro y ν hν
    obtain ⟨μ', hμ'⟩ := hfac ν.op (fun h ↦ hν ((isIso_op_iff ν).1 h))
    exact ⟨μ'.unop, by rw [← Quiver.Hom.op_inj.eq_iff, op_comp, hμ']; rfl⟩

/-- `NoTiny` passes to the double opposite. -/
lemma NoTiny.op_op {Q : Type} [Category.{0} Q] [HasZeroMorphisms Q] (h : NoTiny Q) :
    NoTiny Qᵒᵖᵒᵖ := fun s t hst ↦ h _ _ (tinyAt_of_dual_op (tinyAtDual_of_op hst))

section Extend

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Finite P]

/-- **Every nonzero morphism extends to a right-deep one.** -/
theorem exists_rightDeep_ext {x y : P} (μ : x ⟶ y) (hμ : μ ≠ 0) :
    ∃ (z : P) (ν : y ⟶ z), μ ≫ ν ≠ 0 ∧ RightDeep (μ ≫ ν) := by
  classical
  have hdep : ∀ {a b : P} (f : a ⟶ b), f ≠ 0 → depth f ≤ Nat.card (RayMor P) := by
    intro a b f hf
    obtain ⟨p, hpl, hp⟩ := exists_path_depth hf
    have h1 := length_le_ncard_below p (by rw [hp]; exact hf)
    have h2 : (IsRayCategory.below (rm p)).ncard ≤ Nat.card (RayMor P) := Set.ncard_le_card _
    omega
  suffices H : ∀ n : ℕ, ∀ {y : P} (μ : x ⟶ y), μ ≠ 0 → Nat.card (RayMor P) - depth μ ≤ n →
      ∃ (z : P) (ν : y ⟶ z), μ ≫ ν ≠ 0 ∧ RightDeep (μ ≫ ν) from H _ μ hμ le_rfl
  intro n
  induction n with
  | zero =>
      intro y μ hμ hn
      refine ⟨y, 𝟙 y, by rw [Category.comp_id]; exact hμ, ?_⟩
      intro w ζ hζ
      by_contra h
      rw [Category.comp_id] at h
      have := depth_lt_comp_right μ ζ h hζ
      have := hdep _ h
      omega
  | succ n ih =>
      intro y μ hμ hn
      by_cases hd : RightDeep μ
      · exact ⟨y, 𝟙 y, by rw [Category.comp_id]; exact hμ, by rw [Category.comp_id]; exact hd⟩
      · simp only [RightDeep, not_forall] at hd
        obtain ⟨w, ζ, hζ, h⟩ := hd
        have := depth_lt_comp_right μ ζ h hζ
        have := hdep _ h
        obtain ⟨z, ν, hν, hd'⟩ := ih (μ ≫ ζ) h (by omega)
        exact ⟨z, ζ ≫ ν, by rw [← Category.assoc]; exact hν, by rw [← Category.assoc]; exact hd'⟩

end Extend

/-- Axiom (d) passes to the opposite category. -/
lemma EndCyclic.op {P : Type} [Category.{0} P] (h : EndCyclic P) : EndCyclic Pᵒᵖ := by
  intro X
  obtain ⟨π, hπ⟩ := h X.unop
  refine ⟨π.op, fun e he ↦ ?_⟩
  obtain ⟨n, hn, hen⟩ := hπ e.unop (fun hi ↦ he ((isIso_unop_iff e).1 hi))
  exact ⟨n, hn, by rw [← op_rpow, ← hen]; rfl⟩

end RayCat

end LargeIndecomposable
