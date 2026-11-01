module

public import LargeIndecomposable.MildContours.PennyFarthings.Contour

/-!
# [mild] Theorem 3, the core case: assembly

`CoreHyp P` (no mild contour with `ρ = ω' ≫ α`) from the three cases of [mild]
Lemma 2.2: penny-farthing (`ω'` invertible, the arrow before `α` is `α`),
dumb-bell (`ω'` invertible, the arrow before `α` is `β`) and diamond (`ω'` not
invertible).

The penny-farthing case is split into the closed case
(`PFData.closed_false`: `ρ³` is projective-injective) and the open case
(`PFData.open_false`, a tiny penny-farthing point), the latter possibly in
`Pᵒᵖ`.

The hypotheses of `coreHyp` are `PFOpenStmt`, `DBStmt` and `DiamondStmt`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Opposite RayCat LargeIndecomposable

universe w

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]
  [Fintype P] [DecidableEq P] [IsFiniteRayCategory P] {k : Type w} [Field k] [Infinite k]

namespace PFData

end PFData

variable (k P) in
/-- **[mild] LPF, MIPF and [Standard] §3 (open penny-farthing)**: if a nonzero
morphism out of `x₀` ends outside `w`, there is a tiny penny-farthing point.
(Open statement.) -/
def PFOpenStmt : Prop :=
  ∀ {x : RayVert P} (D : PFData x x), D.q = .nil → ∀ {c : RayVert P} (a₁ : x ⟶ c)
    (w₁ : Quiver.Path c D.t), D.w' = (Quiver.Path.nil.cons a₁).comp w₁ → MildHyp k P →
    MildHyp k Pᵒᵖ → EndCyclic P → NoTiny P → ∀ {z : RayVert P} (μ : x.out ⟶ z.out), μ ≠ 0 →
    (¬∃ (p : Quiver.Path x z) (s₁ : Quiver.Path z x), D.w'.cons D.β = p.comp s₁) → False

namespace PFData

/-- **[mild] Theorem 3, penny-farthing case.** -/
theorem pf_false {x : RayVert P} (D : PFData x x) (hq : D.q = .nil) {c : RayVert P}
    (a₁ : x ⟶ c) (w₁ : Quiver.Path c D.t) (hw : D.w' = (Quiver.Path.nil.cons a₁).comp w₁)
    (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P) (hNPI : NoProjInj P)
    (hNT : NoTiny P) (hNTo : NoTiny Pᵒᵖ) (hPF : PFOpenStmt P k)
    (hPFo : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); letI : Fintype Pᵒᵖ := Fintype.ofFinite _
      letI : DecidableEq Pᵒᵖ := Classical.decEq _; PFOpenStmt Pᵒᵖ k) : False := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  letI : Fintype Pᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq Pᵒᵖ := Classical.decEq _
  by_cases hclR : ∀ {z : RayVert P} (μ : x.out ⟶ z.out), μ ≠ 0 →
      ∃ (p : Quiver.Path x z) (s₁ : Quiver.Path z x), D.w'.cons D.β = p.comp s₁
  · by_cases hclL : ∀ {z : RayVert P} (μ : z.out ⟶ x.out), μ ≠ 0 →
        ∃ (p : Quiver.Path x z) (s₁ : Quiver.Path z x), D.w'.cons D.β = p.comp s₁
    · exact D.closed_false hq a₁ w₁ hw hM hE hNPI hclR hclL
    · push Not at hclL
      obtain ⟨z, μ, hμ, hz⟩ := hclL
      refine hPFo (D.op hq a₁ w₁ hw) rfl (revArr D.β) (revPath w₁) rfl hMo hMo.op hE.op hNTo
        (show (RayVert.mk (Opposite.op x.out) : RayVert Pᵒᵖ).out ⟶
          (RayVert.mk (Opposite.op z.out) : RayVert Pᵒᵖ).out from μ.op)
        (fun h ↦ hμ (Quiver.Hom.op_inj (by exact h.trans (op_zero _ _).symm))) ?_
      rintro ⟨p, s₁, hps⟩
      apply hz (unrevPath s₁) (unrevPath p)
      have h1 : (D.op hq a₁ w₁ hw).w'.cons (D.op hq a₁ w₁ hw).β = revPath (D.w'.cons D.β) :=
        (D.revPath_w a₁ w₁ hw).symm
      have h2 := congrArg unrevPath (h1.symm.trans hps)
      rw [unrevPath_revPath, unrevPath_comp] at h2
      exact h2
  · push Not at hclR
    obtain ⟨z, μ, hμ, hz⟩ := hclR
    exact hPF D hq a₁ w₁ hw hM hMo hE hNT μ hμ (fun ⟨p, s₁, h⟩ ↦ hz p s₁ h)

end PFData

/-- Contour data in case (DB) of [mild] Lemma 2.2: `v = q β α`, `w = w' β`,
`α` a loop at `y` with `ρ = α`. -/
structure DBData (x y : RayVert P) where
  α : y ⟶ y
  t : RayVert P
  w' : Quiver.Path x t
  β : t ⟶ y
  q : Quiver.Path x t
  hval : pathVal ((q.cons β).cons α) = pathVal (w'.cons β)
  h0 : pathVal ((q.cons β).cons α) ≠ 0
  hni : ¬Interlaced ((q.cons β).cons α) (w'.cons β)
  hρ : ∀ f : y.out ⟶ y.out, ¬IsIso f → ∃ n, 0 < n ∧ f = rpow α.1 n
  hωρ : pathVal ((q.cons β).cons α) ≫ α.1 ≠ 0

variable (k P) in
/-- **[mild] Theorem 3, dumb-bell case** (PDB, LDB, MIDB). The closed dumb-bell
needs a further global fact (see the reconstruction notes). (Open statement.) -/
def DBStmt : Prop :=
  ∀ {x y : RayVert P} (_ : DBData x y), MildHyp k P → MildHyp k Pᵒᵖ → EndCyclic P →
    NoProjInj P → NoTiny P → NoTiny Pᵒᵖ → False

variable (k P) in
/-- **[mild] Theorem 3, diamond case** (PD, LD, MID). (Open statement.) -/
def DiamondStmt : Prop :=
  ∀ {x y : P} (C : MildContour x y) (ω' : y ⟶ C.sv), ¬IsIso ω' → C.ρ = ω' ≫ C.α.1 →
    MildHyp k P → MildHyp k Pᵒᵖ → EndCyclic P → NoProjInj P → NoTiny P → NoTiny Pᵒᵖ → False

/-- **The core case of [mild] Theorem 3**: no mild contour with `ρ = ω' ≫ α`. -/
theorem coreHyp (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : EndCyclic P)
    (hNPI : NoProjInj P) (hNT : NoTiny P) (hNTo : NoTiny Pᵒᵖ) (hPF : PFOpenStmt P k)
    (hPFo : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); letI : Fintype Pᵒᵖ := Fintype.ofFinite _
      letI : DecidableEq Pᵒᵖ := Classical.decEq _; PFOpenStmt Pᵒᵖ k)
    (hDB : DBStmt P k) (hD : DiamondStmt P k) : CoreHyp P := by
  intro x y C ω' hρ
  by_cases hω' : IsIso ω'
  swap
  · exact hD C ω' hω' hρ hM hMo hE hNPI hNT hNTo
  have hR : RightCancel P := hM.right
  have hv := C.v'_pos hR
  have hw := C.w'_pos hR
  obtain ⟨sv, sw, v', α, w', β, hval, h0, hni, ρ, hρρ, hωρ⟩ := C
  obtain ⟨h, he⟩ := RayQuiver.eq_id_of_isIso ω'
  dsimp only at h he hρ hv hw
  subst he
  subst h
  change ρ = 𝟙 _ ≫ α.1 at hρ
  rw [Category.id_comp] at hρ
  subst hρ
  change 0 < v'.length at hv
  change 0 < w'.length at hw
  obtain ⟨s, e, v'', hv''⟩ : ∃ (s : P) (e : (RayVert.mk s : RayVert P) ⟶ RayVert.mk y)
      (v'' : Quiver.Path (RayVert.mk x) (RayVert.mk s)), v' = v''.cons e := by
    cases v' with
    | nil => simp at hv
    | cons v'' e => exact ⟨_, e, v'', rfl⟩
  subst hv''
  rcases MildContour.loop_prev hM v'' e α w' β hval h0 hni hρρ hωρ with ⟨hs, hes⟩ | ⟨hs, hes⟩
  · subst hs
    have he' := eq_of_heq hes
    subst he'
    have hq := (PFData.mk (x := RayVert.mk x) (y := RayVert.mk s) e (RayVert.mk sw) w' β v''
      hval h0 hni hρρ hωρ).q_length hM
    change v''.length = 0 at hq
    obtain ⟨c, a₁, w₁, hw₁⟩ := path_first_arrow w' (by omega)
    cases v'' with
    | nil =>
        exact (PFData.mk (x := RayVert.mk x) (y := RayVert.mk x) e (RayVert.mk sw) w' β .nil
          hval h0 hni hρρ hωρ).pf_false rfl a₁ w₁ hw₁ hM hMo hE hNPI hNT hNTo hPF hPFo
    | cons _ _ => simp at hq
  · subst hs
    have he' := eq_of_heq hes
    subst he'
    exact hDB ⟨α, RayVert.mk s, w', e, v'', hval, h0, hni, hρρ, hωρ⟩ hM hMo hE hNPI hNT hNTo

end RayCat

end LargeIndecomposable
