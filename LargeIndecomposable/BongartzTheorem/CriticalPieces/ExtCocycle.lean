module

public import LargeIndecomposable.BongartzTheorem.CriticalPieces.PieceRigid
public import LargeIndecomposable.BongartzTheorem.CriticalPieces.BoundedLength
public import LargeIndecomposable.BongartzTheorem.CriticalPieces.PointBrickData

/-!
# Cocycles from a presentation

Let `0 → K → P → X → 0` be vertexwise exact, with a vertexwise section `s`. The maps
`δ_α = ι⁻¹(s X(α) - P(α) s)` are extension data for `X` by `K`, with coboundary image in `P`. Pushing
along `φ : K → Y` gives data for `X` by `Y`. These are cocycles when `X` and `P` are killed by the
relations (`mem_cocycles_push`), and they vanish only if `φ` extends to `P` (`extends_of_push`).
So the cocycles of `X` by `Y` are at least as many as the extension classes
(`two_le_cocycles`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.FinQuiver.Ext

open CategoryTheory

universe u

variable {k : Type u} [Field k] {D : FinQuiver}

section Post

variable {X Y Y' : Rep k D} (h : Y ⟶ Y') (z : Data X Y)

/-- Pushing data along a morphism. -/
def push : Data X Y' := fun α ↦ (h.app (D.tgt α)).hom ∘ₗ z α

lemma zOp_push (e : D.A) : zOp (push h z) e = h.tot ∘ₗ zOp z e := by
  refine LinearMap.ext fun x ↦ funext fun j ↦ ?_
  simp only [zOp, push, LinearMap.comp_apply, LinearMap.coe_single, LinearMap.coe_proj,
    Function.eval, Rep.Hom.tot_apply]
  by_cases hj : j = D.tgt e
  · subst hj
    simp
  · simp [Pi.single_eq_of_ne hj]

lemma tot_comp_pathTot : ∀ le : List D.A, h.tot ∘ₗ Y.pathTot le = Y'.pathTot le ∘ₗ h.tot
  | [] => rfl
  | e :: le => by
    change h.tot ∘ₗ (Y.pathTot le ∘ₗ Y.arrOp e) = Y'.pathTot le ∘ₗ Y'.arrOp e ∘ₗ h.tot
    rw [← LinearMap.comp_assoc, tot_comp_pathTot le, LinearMap.comp_assoc,
      Rep.Hom.tot_comp_arrOp]

lemma cross_push : ∀ le : List D.A, cross (push h z) le = h.tot ∘ₗ cross z le
  | [] => by simp [cross]
  | e :: le => by
    simp only [cross, cross_push le, zOp_push, LinearMap.comp_add]
    rw [← LinearMap.comp_assoc, ← tot_comp_pathTot, LinearMap.comp_assoc, LinearMap.comp_assoc]

/-- **The extension block of a pushed datum.** -/
lemma crossA_push (a : D.PathAlgebra k) : crossA (push h z) a = h.tot ∘ₗ crossA z a := by
  have ha : a ∈ vwSpan k (Q := D) := by rw [vwSpan_eq_top]; trivial
  induction ha using Submodule.span_induction with
  | mem b hb =>
    rcases hb with ⟨v, rfl⟩ | ⟨l, rfl⟩
    · rw [crossA_vertex, crossA_vertex, LinearMap.comp_zero]
    · have h1 : ∀ {Y₁ : Rep k D} (z₁ : Data X Y₁), crossA z₁ (FinQuiver.word k D l) = cross z₁ l := by
        intro Y₁ z₁
        unfold crossA; rw [act_word, cross_eq]
      rw [h1, h1, cross_push]
  | zero => simp [crossA]
  | add a b _ _ ha hb =>
    have h1 : ∀ {Y₁ : Rep k D} (z₁ : Data X Y₁), crossA z₁ (a + b) = crossA z₁ a + crossA z₁ b := by
      intro Y₁ z₁
      simp [crossA, LinearMap.add_comp, LinearMap.comp_add]
    rw [h1, h1, ha, hb, LinearMap.comp_add]
  | smul c a _ ha =>
    have h1 : ∀ {Y₁ : Rep k D} (z₁ : Data X Y₁), crossA z₁ (c • a) = c • crossA z₁ a := by
      intro Y₁ z₁
      simp [crossA, LinearMap.smul_comp, LinearMap.comp_smul]
    rw [h1, h1, ha, LinearMap.comp_smul]

end Post

section Pres

variable {X P K : Rep k D} (ι : K ⟶ P) (π : P ⟶ X)

/-- A vertexwise short exact sequence. -/
structure VExact : Prop where
  inj : ∀ i, Function.Injective (ι.app i).hom
  surj : ∀ i, Function.Surjective (π.app i).hom
  ex : ∀ i, LinearMap.range (ι.app i).hom = LinearMap.ker (π.app i).hom

variable {ι π} (hE : VExact ι π)
include hE

/-- A vertexwise section. -/
lemma exists_section : ∃ s : ∀ i, X.obj i →ₗ[k] P.obj i, ∀ i, (π.app i).hom ∘ₗ s i = LinearMap.id := by
  have h : ∀ i, ∃ s : X.obj i →ₗ[k] P.obj i, (π.app i).hom ∘ₗ s = LinearMap.id := fun i ↦
    (π.app i).hom.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 (hE.surj i))
  choose s hs using h
  exact ⟨s, hs⟩

/-- Lifting along the injection. -/
lemma exists_lift_ι {W : Type*} [AddCommGroup W] [Module k W] (i : D.V) (f : W →ₗ[k] P.obj i)
    (hf : (π.app i).hom ∘ₗ f = 0) : ∃ g : W →ₗ[k] K.obj i, (ι.app i).hom ∘ₗ g = f := by
  have hmem : ∀ w, f w ∈ LinearMap.range (ι.app i).hom := fun w ↦ by
    rw [hE.ex i]
    exact LinearMap.congr_fun hf w
  refine ⟨(LinearEquiv.ofInjective _ (hE.inj i)).symm.toLinearMap ∘ₗ f.codRestrict _ hmem, ?_⟩
  refine LinearMap.ext fun w ↦ ?_
  have := (LinearEquiv.ofInjective _ (hE.inj i)).apply_symm_apply (f.codRestrict _ hmem w)
  exact congrArg Subtype.val this

variable {s : ∀ i, X.obj i →ₗ[k] P.obj i} (hs : ∀ i, (π.app i).hom ∘ₗ s i = LinearMap.id)
include hs

/-- **The data of a presentation.** -/
lemma exists_delta : ∃ δ : Data X K, ∀ α, (ι.app (D.tgt α)).hom ∘ₗ δ α = cob X P s α := by
  have h : ∀ α, ∃ g : X.obj (D.src α) →ₗ[k] K.obj (D.tgt α),
      (ι.app (D.tgt α)).hom ∘ₗ g = cob X P s α := by
    intro α
    refine exists_lift_ι hE _ _ (LinearMap.ext fun x ↦ ?_)
    have h1 := LinearMap.congr_fun (hs (D.tgt α)) ((X.map α).hom x)
    have h2 := congrArg (fun f ↦ (ModuleCat.Hom.hom f) ((s (D.src α)) x)) (π.comm α)
    have h3 := LinearMap.congr_fun (hs (D.src α)) x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.id_apply] at h1 h2 h3
    simp only [cob, LinearMap.comp_apply, LinearMap.sub_apply, map_sub, LinearMap.zero_apply]
    rw [h1]
    have h4 : (π.app (D.tgt α)).hom ((P.map α).hom (s (D.src α) x)) = (X.map α).hom x :=
      h2.trans (by rw [h3])
    rw [h4, sub_self]
  choose δ hδ using h
  exact ⟨δ, hδ⟩

omit hs hE in
/-- **Pushed data are cocycles.** -/
theorem crossA_push_eq_zero {Y : Rep k D} (hE : VExact ι π)
    {δ : Data X K} (hδ : ∀ α, (ι.app (D.tgt α)).hom ∘ₗ δ α = cob X P s α) (φ : K ⟶ Y)
    (a : D.PathAlgebra k) (hX : act X a = 0) (hP : act P a = 0) : crossA (push φ δ) a = 0 := by
  have h1 : push ι δ = cob X P s := funext hδ
  have h2 : ι.tot ∘ₗ crossA δ a = 0 := by
    rw [← crossA_push, h1, crossA_cob, hX, hP, LinearMap.comp_zero, LinearMap.zero_comp, sub_self]
  have h3 : crossA δ a = 0 := by
    refine LinearMap.ext fun x ↦ funext fun j ↦ hE.inj j ?_
    have := congrFun (LinearMap.congr_fun h2 x) j
    simpa using this
  rw [crossA_push, h3, LinearMap.comp_zero]

/-- **If the pushed data vanish, the morphism extends.** -/
theorem extends_of_push {Y : Rep k D} {δ : Data X K}
    (hδ : ∀ α, (ι.app (D.tgt α)).hom ∘ₗ δ α = cob X P s α) (φ : K ⟶ Y)
    (h0 : push φ δ = 0) : ∃ ψ : P ⟶ Y, ι ≫ ψ = φ := by
  -- the retractions
  have hr : ∀ i, ∃ r : P.obj i →ₗ[k] K.obj i,
      (ι.app i).hom ∘ₗ r = LinearMap.id - s i ∘ₗ (π.app i).hom := fun i ↦
    exists_lift_ι hE i _ (by
      refine LinearMap.ext fun p ↦ ?_
      have h1 := LinearMap.congr_fun (hs i) ((π.app i).hom p)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
      simp [h1])
  choose r hr using hr
  have hι : ∀ i (x : K.obj i), (π.app i).hom ((ι.app i).hom x) = 0 := fun i x ↦ by
    have : (ι.app i).hom x ∈ LinearMap.ker (π.app i).hom := by
      rw [← hE.ex i]
      exact ⟨x, rfl⟩
    exact this
  have hri : ∀ i (x : K.obj i), r i ((ι.app i).hom x) = x := fun i x ↦ by
    apply hE.inj i
    have h1 := LinearMap.congr_fun (hr i) ((ι.app i).hom x)
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at h1
    rw [h1, hι, map_zero, sub_zero]
  refine ⟨{ app := fun i ↦ ModuleCat.ofHom ((φ.app i).hom ∘ₗ r i)
            comm := fun α ↦ ?_ }, ?_⟩
  · ext p
    change (φ.app (D.tgt α)).hom (r (D.tgt α) ((P.map α).hom p)) =
      (Y.map α).hom ((φ.app (D.src α)).hom (r (D.src α) p))
    -- the difference is `δ (π p)`
    have hd : r (D.tgt α) ((P.map α).hom p) =
        (K.map α).hom (r (D.src α) p) - δ α ((π.app (D.src α)).hom p) := by
      apply hE.inj (D.tgt α)
      have h1 := LinearMap.congr_fun (hr (D.tgt α)) ((P.map α).hom p)
      have h2 := LinearMap.congr_fun (hr (D.src α)) p
      have h3 := LinearMap.congr_fun (hδ α) ((π.app (D.src α)).hom p)
      have h4 := congrArg (fun f ↦ (ModuleCat.Hom.hom f) (r (D.src α) p)) (ι.comm α)
      have h5 := congrArg (fun f ↦ (ModuleCat.Hom.hom f) p) (π.comm α)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.sub_apply,
        LinearMap.id_apply] at h1 h2 h3 h4 h5
      rw [map_sub, h1, h4, h2, h3]
      simp only [cob, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
      rw [h5]
      abel
    rw [hd, map_sub]
    have h0' : (φ.app (D.tgt α)).hom (δ α ((π.app (D.src α)).hom p)) = 0 :=
      LinearMap.congr_fun (congrFun h0 α) _
    rw [h0', sub_zero]
    have := congrArg (fun f ↦ (ModuleCat.Hom.hom f) (r (D.src α) p)) (φ.comm α)
    simpa using this
  · refine Rep.hom_ext fun i ↦ ?_
    ext x
    change (φ.app i).hom (r i ((ι.app i).hom x)) = (φ.app i).hom x
    rw [hri]

end Pres

end LargeIndecomposable.FinQuiver.Ext

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover RayQuiver Covering FinQuiver Module

universe u

variable {k : Type u} [Field k]
  {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)}

/-- The data respecting all relations of the cover. -/
def relSub (X Y : Rep k (pieceQuiver S)) : Submodule k (Ext.Data X Y) where
  carrier := {z | ∀ ρ ∈ relGens k S, Ext.crossA z ρ = 0}
  add_mem' {a b} ha hb ρ hρ := by
    rw [Ext.crossA_add_left, ha ρ hρ, hb ρ hρ, add_zero]
  zero_mem' ρ _ := by
    have h := Ext.crossA_smul_left (0 : Ext.Data X Y) (0 : k) ρ
    simpa using h
  smul_mem' c a ha ρ hρ := by
    rw [Ext.crossA_smul_left, ha ρ hρ, smul_zero]

lemma crossOK_of_rel (K : KroneckerPair k (pieceQuiver S))
    (z : ∀ α : (pieceQuiver S).A, K.P.obj ((pieceQuiver S).src α) →ₗ[k]
      K.Q₀.obj ((pieceQuiver S).tgt α))
    (hz : z ∈ relSub K.P K.Q₀) : CrossOK K z := by
  refine ⟨fun le i j h h0 ↦ ?_, fun le le' i j h h' he ↦ ?_⟩
  · rw [kcross_eq, ← crossA_word]
    exact hz _ (Or.inl ⟨le, i, j, h, h0, rfl⟩)
  · rw [kcross_eq, kcross_eq, ← crossA_word, ← crossA_word, ← sub_eq_zero, ← crossA_sub]
    exact hz _ (Or.inr ⟨le, le', i, j, h, h', he, rfl⟩)

/-- **Point–brick data from two independent data respecting the relations.** -/
theorem pointBrick'_of_rel (x : (pieceQuiver S).V) (V : Rep k (pieceQuiver S))
    (finV : ∀ i, FiniteDimensional k (V.obj i)) (hVx : Subsingleton (V.obj x))
    (brickV : ∀ f : V ⟶ V, ∃ c : k, ∀ i, (f.app i).hom = c • LinearMap.id)
    (hV : ∃ i, Nontrivial (V.obj i)) (hVc : RespectsCover V)
    (h2 : 2 ≤ Module.finrank k (relSub V (Rep.pointRep (k := k) x))) :
    PointBrick' (k := k) S := by
  haveI := finV
  haveI : ∀ i, FiniteDimensional k ((Rep.pointRep (k := k) x).obj i) := fun i ↦
    inferInstanceAs (FiniteDimensional k (Fin _ → k))
  obtain ⟨w₁, w₂, hw⟩ := exists_pair h2
  have hind : ∀ c₁ c₂ : k, (∀ α, c₁ • (w₁ : Ext.Data V (Rep.pointRep (k := k) x)) α +
      c₂ • (w₂ : Ext.Data V (Rep.pointRep (k := k) x)) α = 0) → c₁ = 0 ∧ c₂ = 0 := by
    intro c₁ c₂ hc
    apply hw
    apply Subtype.ext
    funext α
    simpa using hc α
  have hK : ∀ w : relSub V (Rep.pointRep (k := k) x),
      CrossOK (pairAtSink x V finV hVx brickV hV (w₁ : Ext.Data V (Rep.pointRep (k := k) x))
        (w₂ : Ext.Data V (Rep.pointRep (k := k) x)) hind)
        (w : Ext.Data V (Rep.pointRep (k := k) x)) := fun w ↦ crossOK_of_rel _ _ w.2
  exact ⟨x, V, finV, hVx, brickV, hV, hVc,
    Or.inr ⟨(w₁ : Ext.Data V (Rep.pointRep (k := k) x)),
      (w₂ : Ext.Data V (Rep.pointRep (k := k) x)), hind, hK w₁, hK w₂⟩⟩

/-- **Point–brick data at a source from two independent data respecting the relations.** -/
theorem pointBrick'_of_rel_source (x : (pieceQuiver S).V) (V : Rep k (pieceQuiver S))
    (finV : ∀ i, FiniteDimensional k (V.obj i)) (hVx : Subsingleton (V.obj x))
    (brickV : ∀ f : V ⟶ V, ∃ c : k, ∀ i, (f.app i).hom = c • LinearMap.id)
    (hV : ∃ i, Nontrivial (V.obj i)) (hVc : RespectsCover V)
    (h2 : 2 ≤ Module.finrank k (relSub (Rep.pointRep (k := k) x) V)) :
    PointBrick' (k := k) S := by
  haveI := finV
  haveI : ∀ i, FiniteDimensional k ((Rep.pointRep (k := k) x).obj i) := fun i ↦
    inferInstanceAs (FiniteDimensional k (Fin _ → k))
  obtain ⟨w₁, w₂, hw⟩ := exists_pair h2
  have hind : ∀ c₁ c₂ : k, (∀ α, c₁ • (w₁ : Ext.Data (Rep.pointRep (k := k) x) V) α +
      c₂ • (w₂ : Ext.Data (Rep.pointRep (k := k) x) V) α = 0) → c₁ = 0 ∧ c₂ = 0 := by
    intro c₁ c₂ hc
    apply hw
    apply Subtype.ext
    funext α
    simpa using hc α
  have hK : ∀ w : relSub (Rep.pointRep (k := k) x) V,
      CrossOK (pairAtSource x V finV hVx brickV hV
        (w₁ : Ext.Data (Rep.pointRep (k := k) x) V) (w₂ : Ext.Data (Rep.pointRep (k := k) x) V) hind)
        (w : Ext.Data (Rep.pointRep (k := k) x) V) := fun w ↦ crossOK_of_rel _ _ w.2
  exact ⟨x, V, finV, hVx, brickV, hV, hVc,
    Or.inl ⟨(w₁ : Ext.Data (Rep.pointRep (k := k) x) V),
      (w₂ : Ext.Data (Rep.pointRep (k := k) x) V), hind, hK w₁, hK w₂⟩⟩

/-- **Independent extension classes give independent data.** Let `0 → K → P → X → 0` be a vertexwise
exact sequence of representations respecting the cover, and `Φ : E → Hom(K, Y)` a family, linear on
vertices, such that the elements of `E` for which `Φ e` extends to `P` lie in `N`. Then `relSub X Y`
has dimension at least `dim E - dim N`. -/
theorem two_le_relSub {X Y Kr Pr : Rep k (pieceQuiver S)} (hX : RespectsCover X)
    (hP : RespectsCover Pr) [∀ i, FiniteDimensional k (X.obj i)]
    [∀ i, FiniteDimensional k (Y.obj i)] {ι : Kr ⟶ Pr} {π : Pr ⟶ X} (hE : Ext.VExact ι π)
    {E : Type*} [AddCommGroup E] [Module k E] [FiniteDimensional k E] (Φ : E → (Kr ⟶ Y))
    (Φi : ∀ i, E →ₗ[k] (Kr.obj i →ₗ[k] Y.obj i)) (hΦ : ∀ e i, ((Φ e).app i).hom = Φi i e)
    (N : Submodule k E) (hN : ∀ e, (∃ ψ : Pr ⟶ Y, ι ≫ ψ = Φ e) → e ∈ N)
    (hd : finrank k N + 2 ≤ finrank k E) : 2 ≤ finrank k (relSub X Y) := by
  obtain ⟨s, hs⟩ := Ext.exists_section hE
  obtain ⟨δ, hδ⟩ := Ext.exists_delta hE hs
  let G : E →ₗ[k] Ext.Data X Y :=
    { toFun := fun e α ↦ Φi ((pieceQuiver S).tgt α) e ∘ₗ δ α
      map_add' := fun a b ↦ by
        funext α
        simp only [map_add, LinearMap.add_comp, Pi.add_apply]
      map_smul' := fun c a ↦ by
        funext α
        simp only [map_smul, LinearMap.smul_comp, Pi.smul_apply, RingHom.id_apply] }
  have hG : ∀ e, G e = Ext.push (Φ e) δ := fun e ↦ by
    funext α
    change Φi _ e ∘ₗ δ α = ((Φ e).app _).hom ∘ₗ δ α
    rw [hΦ]
  have hmem : ∀ e, G e ∈ relSub X Y := fun e ρ hρ ↦ by
    rw [hG]
    exact Ext.crossA_push_eq_zero hE hδ (Φ e) ρ ((respectsCover_iff X).1 hX ρ hρ)
      ((respectsCover_iff Pr).1 hP ρ hρ)
  let G' : E →ₗ[k] relSub X Y := G.codRestrict _ hmem
  have hker : LinearMap.ker G' ≤ N := by
    intro e he
    have h0 : G e = 0 := congrArg Subtype.val he
    rw [hG] at h0
    exact hN e (Ext.extends_of_push hE hs hδ (Φ e) h0)
  have h1 := LinearMap.finrank_range_add_finrank_ker G'
  have h2 := Submodule.finrank_mono hker
  have h3 : finrank k (LinearMap.range G') ≤ finrank k (relSub X Y) := Submodule.finrank_le _
  omega

/-- A vertexwise exact sequence from the total maps. -/
lemma vExact_of_tot {D : FinQuiver} {K Pr X : Rep k D} (ι : K ⟶ Pr) (π : Pr ⟶ X)
    [DecidableEq D.V]
    (hinj : Function.Injective ι.tot) (hsurj : Function.Surjective π.tot)
    (hex : ∀ p, π.tot p = 0 ↔ ∃ x, ι.tot x = p) : Ext.VExact ι π := by
  classical
  refine ⟨fun i a b hab ↦ ?_, fun i y ↦ ?_, fun i ↦ ?_⟩
  · have h1 : ι.tot (Pi.single i a) = ι.tot (Pi.single i b) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simpa using hab
      · simp [Pi.single_eq_of_ne hj]
    have := congrFun (hinj h1) i
    simpa using this
  · obtain ⟨p, hp⟩ := hsurj (Pi.single i y)
    refine ⟨p i, ?_⟩
    have := congrFun hp i
    simpa using this
  · ext p
    constructor
    · rintro ⟨a, rfl⟩
      have h1 : π.tot (ι.tot (Pi.single i a)) = 0 := (hex _).2 ⟨_, rfl⟩
      have := congrFun h1 i
      simpa using this
    · intro hp
      have hp' : (π.app i).hom p = 0 := hp
      have h1 : π.tot (Pi.single i p) = 0 := by
        funext j
        by_cases hj : j = i
        · subst hj
          simpa using hp'
        · simp [Pi.single_eq_of_ne hj]
      obtain ⟨x, hx⟩ := (hex _).1 h1
      refine ⟨x i, ?_⟩
      have := congrFun hx i
      simpa using this

end LargeIndecomposable.RayCat
