module

public import LargeIndecomposable.Coverings.Pieces.PieceAlgebra

/-!
# Extensions of quiver representations

For representations `X`, `Y` of a finite quiver and maps `z_α : X(s α) → Y(t α)`, the extension
`E(z)` has spaces `Y(i) × X(i)` and arrows `(y, x) ↦ (Y(α) y + z_α x, X(α) x)` (`extR`). A path
acts on `E(z)` by a block-triangular operator whose off-diagonal block is `cross z l`
(`πY_pathTot`), which is additive and homogeneous in `z` (`cross_add`, `cross_smul`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.FinQuiver.Ext

open CategoryTheory

universe u

variable {k : Type u} [Field k] {D : FinQuiver} (X Y : Rep k D)

/-- Extension data: one map per arrow. -/
abbrev Data := ∀ α : D.A, X.obj (D.src α) →ₗ[k] Y.obj (D.tgt α)

variable {X Y} (z : Data X Y)

/-- **The extension `E(z)`.** -/
def extR : Rep k D where
  obj i := ModuleCat.of k (Y.obj i × X.obj i)
  map α := ModuleCat.ofHom (LinearMap.prod (LinearMap.coprod (Y.map α).hom (z α))
    ((X.map α).hom ∘ₗ LinearMap.snd k _ _))

/-- The `Y`-part of the total space. -/
def πY : (extR z).Tot →ₗ[k] Y.Tot :=
  LinearMap.pi fun i ↦ LinearMap.fst k _ _ ∘ₗ LinearMap.proj (φ := fun i ↦ (extR z).obj i) i

/-- The `X`-part of the total space. -/
def πX : (extR z).Tot →ₗ[k] X.Tot :=
  LinearMap.pi fun i ↦ LinearMap.snd k _ _ ∘ₗ LinearMap.proj (φ := fun i ↦ (extR z).obj i) i

/-- The inclusion of the `X`-part. -/
def ιX : X.Tot →ₗ[k] (extR z).Tot :=
  LinearMap.pi fun i ↦ LinearMap.inr k _ _ ∘ₗ LinearMap.proj (φ := fun i ↦ X.obj i) i

/-- The inclusion of the `Y`-part. -/
def ιY : Y.Tot →ₗ[k] (extR z).Tot :=
  LinearMap.pi fun i ↦ LinearMap.inl k _ _ ∘ₗ LinearMap.proj (φ := fun i ↦ Y.obj i) i

/-- The extension block of an arrow. -/
def zOp (e : D.A) : X.Tot →ₗ[k] Y.Tot :=
  LinearMap.single k (fun i ↦ Y.obj i) (D.tgt e) ∘ₗ z e ∘ₗ
    LinearMap.proj (φ := fun i ↦ X.obj i) (D.src e)

/-- The extension block of a path. -/
def cross : List D.A → (X.Tot →ₗ[k] Y.Tot)
  | [] => 0
  | e :: le => Y.pathTot le ∘ₗ zOp z e + cross le ∘ₗ X.arrOp e

lemma πX_apply (x : (extR z).Tot) (l : D.V) : πX z x l = (x l).2 := rfl

lemma πY_apply (x : (extR z).Tot) (l : D.V) : πY z x l = (x l).1 := rfl

lemma πX_arrOp (e : D.A) : πX z ∘ₗ (extR z).arrOp e = X.arrOp e ∘ₗ πX z := by
  refine LinearMap.ext fun x ↦ funext fun l ↦ ?_
  simp only [LinearMap.comp_apply, Rep.arrOp_apply, πX_apply]
  by_cases h : l = D.tgt e
  · subst h
    simp only [Pi.single_eq_same]
    rfl
  · simp only [Pi.single_eq_of_ne h]
    rfl

lemma πY_arrOp (e : D.A) : πY z ∘ₗ (extR z).arrOp e =
    Y.arrOp e ∘ₗ πY z + zOp z e ∘ₗ πX z := by
  refine LinearMap.ext fun x ↦ funext fun l ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, Rep.arrOp_apply, πY_apply, Pi.add_apply,
    zOp, LinearMap.coe_single, LinearMap.coe_proj, Function.eval]
  by_cases h : l = D.tgt e
  · subst h
    simp only [Pi.single_eq_same]
    rfl
  · simp only [Pi.single_eq_of_ne h, add_zero]
    rfl

lemma πX_pathTot : ∀ le : List D.A,
    πX z ∘ₗ (extR z).pathTot le = X.pathTot le ∘ₗ πX z
  | [] => rfl
  | e :: le => by
    change πX z ∘ₗ ((extR z).pathTot le ∘ₗ (extR z).arrOp e) =
      X.pathTot le ∘ₗ X.arrOp e ∘ₗ πX z
    rw [← LinearMap.comp_assoc, πX_pathTot le, LinearMap.comp_assoc, πX_arrOp]

lemma πY_pathTot : ∀ le : List D.A,
    πY z ∘ₗ (extR z).pathTot le = Y.pathTot le ∘ₗ πY z + cross z le ∘ₗ πX z
  | [] => by simp [cross]; rfl
  | e :: le => by
    change πY z ∘ₗ ((extR z).pathTot le ∘ₗ (extR z).arrOp e) =
      (Y.pathTot le ∘ₗ Y.arrOp e) ∘ₗ πY z +
        (Y.pathTot le ∘ₗ zOp z e + cross z le ∘ₗ X.arrOp e) ∘ₗ πX z
    rw [← LinearMap.comp_assoc, πY_pathTot le, LinearMap.add_comp, LinearMap.comp_assoc,
      πY_arrOp, LinearMap.comp_assoc, πX_arrOp, LinearMap.comp_add, LinearMap.add_comp]
    simp only [LinearMap.comp_assoc]
    abel

lemma πY_ιX : πY z ∘ₗ ιX z = 0 := by
  refine LinearMap.ext fun x ↦ funext fun l ↦ ?_; rfl

lemma πX_ιX : πX z ∘ₗ ιX z = LinearMap.id := by
  refine LinearMap.ext fun x ↦ funext fun l ↦ ?_; rfl

/-- **The extension block of a path, read on the `X`-part.** -/
lemma cross_eq (le : List D.A) : cross z le = πY z ∘ₗ (extR z).pathTot le ∘ₗ ιX z := by
  rw [← LinearMap.comp_assoc, πY_pathTot, LinearMap.add_comp, LinearMap.comp_assoc,
    πY_ιX, LinearMap.comp_zero, zero_add, LinearMap.comp_assoc, πX_ιX, LinearMap.comp_id]

lemma zOp_add (z z' : Data X Y) (e : D.A) : zOp (z + z') e = zOp z e + zOp z' e := by
  simp only [zOp, Pi.add_apply, LinearMap.add_comp, LinearMap.comp_add]

lemma zOp_smul (c : k) (e : D.A) : zOp (c • z) e = c • zOp z e := by
  simp only [zOp, Pi.smul_apply, LinearMap.smul_comp, LinearMap.comp_smul]

lemma cross_add (z z' : Data X Y) : ∀ le : List D.A, cross (z + z') le = cross z le + cross z' le
  | [] => by simp [cross]
  | e :: le => by
    simp only [cross, zOp_add, cross_add z z' le, LinearMap.comp_add, LinearMap.add_comp]
    abel

lemma cross_smul (c : k) : ∀ le : List D.A, cross (c • z) le = c • cross z le
  | [] => by simp [cross]
  | e :: le => by
    simp only [cross, zOp_smul, cross_smul c le, LinearMap.comp_smul, LinearMap.smul_comp,
      smul_add]

variable (X Y) in
/-- **The coboundary** of vertex maps `h_i : X(i) → Y(i)`: `h_t X(α) - Y(α) h_s`. -/
def cob (h : ∀ i, X.obj i →ₗ[k] Y.obj i) : Data X Y := fun α ↦
  h (D.tgt α) ∘ₗ (X.map α).hom - (Y.map α).hom ∘ₗ h (D.src α)

/-- The coboundary map is linear. -/
def cobL : (∀ i, X.obj i →ₗ[k] Y.obj i) →ₗ[k] Data X Y where
  toFun := cob X Y
  map_add' h h' := by
    funext α
    simp only [cob, Pi.add_apply, LinearMap.add_comp, LinearMap.comp_add]
    abel
  map_smul' c h := by
    funext α
    simp only [cob, Pi.smul_apply, LinearMap.smul_comp, LinearMap.comp_smul, RingHom.id_apply,
      smul_sub]

/-- **A section of `E(z) → X` makes `z` a coboundary.** -/
theorem eq_cob_of_section (σ : X ⟶ extR z) (hσ : ∀ i (x : X.obj i), ((σ.app i).hom x).2 = x) :
    z = cob X Y (fun i ↦ LinearMap.fst k _ _ ∘ₗ (σ.app i).hom) := by
  funext α
  refine LinearMap.ext fun x ↦ ?_
  have h := congrArg (fun f ↦ (ModuleCat.Hom.hom f) x) (σ.comm α)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  have h1 := congrArg Prod.fst h
  change ((σ.app (D.tgt α)).hom ((X.map α).hom x)).1 =
    (Y.map α).hom ((σ.app (D.src α)).hom x).1 + z α ((σ.app (D.src α)).hom x).2 at h1
  rw [hσ] at h1
  change z α x = ((σ.app (D.tgt α)).hom ((X.map α).hom x)).1 -
    (Y.map α).hom ((σ.app (D.src α)).hom x).1
  rw [h1]
  abel

/-! ### The extension block of an element of the path algebra -/

/-- The action of the path algebra on a total space. -/
abbrev act (W : Rep k D) (a : D.PathAlgebra k) : W.Tot →ₗ[k] W.Tot :=
  W.pdAct (FinQuiver.Hom.id D) a

/-- The extension block of an element of the path algebra. -/
def crossA (a : D.PathAlgebra k) : X.Tot →ₗ[k] Y.Tot := πY z ∘ₗ act (extR z) a ∘ₗ ιX z

lemma act_vertex (W : Rep k D) (v : D.V) : act W (FinQuiver.vertex k D v) = W.idm v := by
  rw [act, Rep.pdAct_vertex, Rep.pdVert_id]

lemma act_word (W : Rep k D) (l : List D.A) : act W (FinQuiver.word k D l) = W.pathTot l :=
  Rep.pdAct_id_word W l

lemma πX_idm (v : D.V) : πX z ∘ₗ (extR z).idm v = X.idm v ∘ₗ πX z := by
  refine LinearMap.ext fun x ↦ funext fun l ↦ ?_
  simp only [LinearMap.comp_apply, Rep.idm_apply, πX_apply]
  by_cases h : l = v
  · subst h; simp only [Pi.single_eq_same]; try rfl
  · simp only [Pi.single_eq_of_ne h]; try rfl

lemma πY_idm (v : D.V) : πY z ∘ₗ (extR z).idm v = Y.idm v ∘ₗ πY z := by
  refine LinearMap.ext fun x ↦ funext fun l ↦ ?_
  simp only [LinearMap.comp_apply, Rep.idm_apply, πY_apply]
  by_cases h : l = v
  · subst h; simp only [Pi.single_eq_same]; try rfl
  · simp only [Pi.single_eq_of_ne h]; try rfl

/-- **Block form of the action**: the `X`-layer is a quotient. -/
lemma πX_act (a : D.PathAlgebra k) : πX z ∘ₗ act (extR z) a = act X a ∘ₗ πX z := by
  have ha : a ∈ vwSpan k (Q := D) := by rw [vwSpan_eq_top]; trivial
  induction ha using Submodule.span_induction with
  | mem b hb =>
    rcases hb with ⟨v, rfl⟩ | ⟨l, rfl⟩
    · rw [act_vertex, act_vertex, πX_idm]
    · rw [act_word, act_word, πX_pathTot]
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, ha, hb]
  | smul c a _ ha => simp only [map_smul, LinearMap.comp_smul, LinearMap.smul_comp, ha]

/-- **Block form of the action**: the `Y`-row. -/
lemma πY_act (a : D.PathAlgebra k) :
    πY z ∘ₗ act (extR z) a = act Y a ∘ₗ πY z + crossA z a ∘ₗ πX z := by
  have ha : a ∈ vwSpan k (Q := D) := by rw [vwSpan_eq_top]; trivial
  induction ha using Submodule.span_induction with
  | mem b hb =>
    rcases hb with ⟨v, rfl⟩ | ⟨l, rfl⟩
    · have h0 : crossA z (FinQuiver.vertex k D v) = 0 := by
        unfold crossA
        rw [act_vertex, ← LinearMap.comp_assoc, πY_idm, LinearMap.comp_assoc, πY_ιX,
          LinearMap.comp_zero]
      rw [h0, act_vertex, act_vertex, πY_idm, LinearMap.zero_comp, add_zero]
    · have h1 : crossA z (FinQuiver.word k D l) = cross z l := by
        unfold crossA; rw [act_word, cross_eq]
      rw [h1, act_word, act_word, πY_pathTot]
  | zero =>
    have : crossA z (0 : D.PathAlgebra k) = 0 := by simp [crossA]
    simp [this]
  | add a b _ _ ha hb =>
    have : crossA z (a + b) = crossA z a + crossA z b := by
      simp [crossA, LinearMap.add_comp, LinearMap.comp_add]
    simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, ha, hb, this]
    abel
  | smul c a _ ha =>
    have : crossA z (c • a) = c • crossA z a := by
      simp [crossA, LinearMap.smul_comp, LinearMap.comp_smul]
    simp only [map_smul, LinearMap.comp_smul, LinearMap.smul_comp, ha, this, smul_add]

/-- **The Leibniz rule** for extension blocks. -/
lemma crossA_mul (a b : D.PathAlgebra k) :
    crossA z (a * b) = act Y a ∘ₗ crossA z b + crossA z a ∘ₗ act X b := by
  refine LinearMap.ext fun x ↦ ?_
  have e1 := LinearMap.congr_fun (πY_act z a) (act (extR z) b (ιX z x))
  have e2 := LinearMap.congr_fun (πX_act z b) (ιX z x)
  have e3 := LinearMap.congr_fun (πX_ιX z) x
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply] at e1 e2 e3
  simp only [crossA, LinearMap.comp_apply, LinearMap.add_apply, act, map_mul,
    Module.End.mul_apply]
  simp only [act] at e1 e2
  rw [e1, e2, e3]
  rfl

lemma crossA_add_left (z z' : Data X Y) (a : D.PathAlgebra k) :
    crossA (z + z') a = crossA z a + crossA z' a := by
  have ha : a ∈ vwSpan k (Q := D) := by rw [vwSpan_eq_top]; trivial
  induction ha using Submodule.span_induction with
  | mem b hb =>
    rcases hb with ⟨v, rfl⟩ | ⟨l, rfl⟩
    · have h0 : ∀ w : Data X Y, crossA w (FinQuiver.vertex k D v) = 0 := fun w ↦ by
        unfold crossA
        rw [act_vertex, ← LinearMap.comp_assoc, πY_idm, LinearMap.comp_assoc, πY_ιX,
          LinearMap.comp_zero]
      rw [h0, h0, h0, add_zero]
    · have h1 : ∀ w : Data X Y, crossA w (FinQuiver.word k D l) = cross w l := fun w ↦ by
        unfold crossA; rw [act_word, cross_eq]
      rw [h1, h1, h1, cross_add]
  | zero => simp [crossA]
  | add a b _ _ ha hb =>
    simp only [crossA, map_add, LinearMap.add_comp, LinearMap.comp_add] at ha hb ⊢
    rw [ha, hb]; abel
  | smul c a _ ha =>
    simp only [crossA, map_smul, LinearMap.smul_comp, LinearMap.comp_smul] at ha ⊢
    rw [ha, smul_add]

lemma crossA_smul_left (c : k) (a : D.PathAlgebra k) :
    crossA (c • z) a = c • crossA z a := by
  have ha : a ∈ vwSpan k (Q := D) := by rw [vwSpan_eq_top]; trivial
  induction ha using Submodule.span_induction with
  | mem b hb =>
    rcases hb with ⟨v, rfl⟩ | ⟨l, rfl⟩
    · have h0 : ∀ w : Data X Y, crossA w (FinQuiver.vertex k D v) = 0 := fun w ↦ by
        unfold crossA
        rw [act_vertex, ← LinearMap.comp_assoc, πY_idm, LinearMap.comp_assoc, πY_ιX,
          LinearMap.comp_zero]
      rw [h0, h0, smul_zero]
    · have h1 : ∀ w : Data X Y, crossA w (FinQuiver.word k D l) = cross w l := fun w ↦ by
        unfold crossA; rw [act_word, cross_eq]
      rw [h1, h1, cross_smul]
  | zero => simp [crossA]
  | add a b _ _ ha hb =>
    simp only [crossA, map_add, LinearMap.add_comp, LinearMap.comp_add] at ha hb ⊢
    rw [ha, hb, smul_add]
  | smul c' a _ ha =>
    simp only [crossA, map_smul, LinearMap.smul_comp, LinearMap.comp_smul] at ha ⊢
    rw [ha, smul_comm]

/-! ### Cocycles for a set of relations -/

/-- The elements killed in both layers whose extension block vanishes. -/
def goodIdeal : TwoSidedIdeal (D.PathAlgebra k) :=
  TwoSidedIdeal.mk' {ρ | act X ρ = 0 ∧ act Y ρ = 0 ∧ crossA z ρ = 0}
    ⟨by simp, by simp, by simp [crossA]⟩
    (fun ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ ↦ ⟨by simp [a1, b1], by simp [a2, b2], by
      simp only [crossA, map_add, LinearMap.add_comp, LinearMap.comp_add] at a3 b3 ⊢
      rw [a3, b3, add_zero]⟩)
    (fun ⟨a1, a2, a3⟩ ↦ ⟨by simp [a1], by simp [a2], by
      simp only [crossA, map_neg, LinearMap.neg_comp, LinearMap.comp_neg] at a3 ⊢
      rw [a3, neg_zero]⟩)
    (fun {a b} ⟨b1, b2, b3⟩ ↦ ⟨by simp [map_mul, b1], by simp [map_mul, b2], by
      rw [crossA_mul, b3, LinearMap.comp_zero, b1, LinearMap.comp_zero, add_zero]⟩)
    (fun {a b} ⟨a1, a2, a3⟩ ↦ ⟨by simp [map_mul, a1], by simp [map_mul, a2], by
      rw [crossA_mul, a3, LinearMap.zero_comp, a2, LinearMap.zero_comp, zero_add]⟩)

/-- **Cocycle conditions on generators suffice.** If both layers are killed by the ideal generated
by `R` and the extension blocks of `R` vanish, all extension blocks of the ideal vanish. -/
theorem crossA_eq_zero_of_span (R : Set (D.PathAlgebra k))
    (hX : ∀ ρ ∈ TwoSidedIdeal.span R, act X ρ = 0) (hY : ∀ ρ ∈ TwoSidedIdeal.span R, act Y ρ = 0)
    (hz : ∀ ρ ∈ R, crossA z ρ = 0) : ∀ ρ ∈ TwoSidedIdeal.span R, crossA z ρ = 0 := by
  have hle : TwoSidedIdeal.span R ≤ goodIdeal z := by
    rw [TwoSidedIdeal.span_le]
    intro ρ hρ
    rw [SetLike.mem_coe, goodIdeal, TwoSidedIdeal.mem_mk']
    exact ⟨hX ρ (TwoSidedIdeal.subset_span hρ), hY ρ (TwoSidedIdeal.subset_span hρ), hz ρ hρ⟩
  intro ρ hρ
  have := hle hρ
  rw [goodIdeal, TwoSidedIdeal.mem_mk'] at this
  exact this.2.2

end LargeIndecomposable.FinQuiver.Ext
