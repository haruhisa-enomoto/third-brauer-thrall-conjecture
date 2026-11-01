module

public import LargeIndecomposable.DirectedAlgebras.EulerForm.EulerDirecting2
public import LargeIndecomposable.RepresentationType.MinimalInfinite.BoundedFinite

/-!
# Sincere directing modules

Let `U` be a sincere directing module over a directed algebra. No tilting theory is used.

* `injE x`, the indecomposable injective at `x`, as a space of functionals; every map into it
  is given by a functional (`homToInj`), so it is injective (`injE_extend`) and a brick
  (`injE_brick`).
* A nonsplit extension of indecomposables gives a path (`reach_of_nonsplit`).
* If `W` is a predecessor of `U`, the syzygy of `W` has no extensions at all
  (`extVanish_syz_of_pred`). This is the elementary part of "a sincere directing module makes the
  algebra tilted": projective dimension at most one for predecessors of `U`.
* **Vossieck's lemma** (`mono_or_epi`): every nonzero morphism `v : x → y` with `x ≠ y` acts on `U`
  injectively or surjectively. Here the proof uses no Auslander–Reiten translate.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- **A nonsplit extension of indecomposables gives a path.** -/
theorem reach_of_nonsplit {X Y E : FDMod k A} (hX : IsInd X) (hY : IsInd Y) (i : X →ₗ[A] E)
    (p : E →ₗ[A] Y) (hp : Function.Surjective p) (hex : LinearMap.range i = LinearMap.ker p)
    (hns : ¬∃ s : Y →ₗ[A] E, p ∘ₗ s = LinearMap.id) : Reach₁ X Y := by
  classical
  obtain ⟨d⟩ := FDMod.exists_decomp E
  let ij : ∀ j, X →ₗ[A] d.obj j := fun j ↦ FDMod.lin (d.proj j) ∘ₗ i
  let pj : ∀ j, d.obj j →ₗ[A] Y := fun j ↦ p ∘ₗ FDMod.lin (d.inc j)
  have hsum : ∀ x : E, ∑ j, FDMod.lin (d.inc j) (FDMod.lin (d.proj j) x) = x := fun x ↦ by
    have := LinearMap.congr_fun d.sum_id x
    simpa using this
  have hpj : ∀ j, ¬Function.Bijective (pj j) := by
    intro j hb
    apply hns
    let e := LinearEquiv.ofBijective (pj j) hb
    refine ⟨FDMod.lin (d.inc j) ∘ₗ e.symm.toLinearMap, ?_⟩
    ext x
    exact e.apply_symm_apply x
  have hij : ∀ j, ¬Function.Bijective (ij j) := by
    intro j hb
    apply hns
    let e := LinearEquiv.ofBijective (ij j) hb
    let r : E →ₗ[A] X := e.symm.toLinearMap ∘ₗ FDMod.lin (d.proj j)
    have hr : r ∘ₗ i = LinearMap.id := by
      ext x; exact e.symm_apply_apply x
    exact split_of_endo' i p hp hex (LinearMap.id - i ∘ₗ r) (fun x ↦ by
        simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.coe_comp,
          Function.comp_apply, map_sub]
        rw [mem_ker_of_range hex, sub_zero]) (fun m ↦ by
        simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.coe_comp,
          Function.comp_apply]
        rw [show r (i m) = m from LinearMap.congr_fun hr m, sub_self])
  by_cases hboth : ∃ j, ij j ≠ 0 ∧ pj j ≠ 0
  · obtain ⟨j, h1, h2⟩ := hboth
    have hInd : IsInd (d.obj j) := ⟨d.indec j, d.nt j⟩
    exact Reach₁.trans (Reach₁.step hX hInd (show X ⟶ d.obj j from ij j) h1 (hij j))
      (Reach₁.step hInd hY (show d.obj j ⟶ Y from pj j) h2 (hpj j))
  · push Not at hboth
    exfalso
    apply hns
    let e₂ : E →ₗ[A] E := ∑ j ∈ Finset.univ.filter (fun j ↦ ij j = 0),
      FDMod.lin (d.inc j) ∘ₗ FDMod.lin (d.proj j)
    have hpe : ∀ x, p (e₂ x) = p x := by
      intro x
      conv_rhs => rw [← hsum x]
      rw [map_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j ↦ ij j = 0)]
      rw [Finset.sum_eq_zero (s := Finset.univ.filter fun j ↦ ¬ij j = 0) (fun j hj ↦ by
        have := hboth j (Finset.mem_filter.1 hj).2
        exact LinearMap.congr_fun this _), add_zero]
      simp only [e₂, LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply, map_sum]
    have hei : ∀ m, e₂ (i m) = 0 := by
      intro m
      rw [LinearMap.sum_apply]
      exact Finset.sum_eq_zero fun j hj ↦ by
        have := LinearMap.congr_fun (Finset.mem_filter.1 hj).2 m
        simp only [LinearMap.coe_comp, Function.comp_apply]
        change FDMod.lin (d.inc j) (ij j m) = 0
        rw [this, LinearMap.zero_apply, map_zero]
    exact split_of_endo' i p hp hex e₂ hpe hei

/-- A path followed by a nonzero map or an isomorphism: prepending. -/
lemma Reach₁.iso_trans {X Y Z : FDMod k A} (e : IsoM X Y) (hX : IsInd X) (h : Reach₁ Y Z) :
    Reach₁ X Z := by
  induction h generalizing X with
  | step hY hZ f hf hnb =>
    obtain ⟨g, hg⟩ := e
    refine Reach₁.step hX hZ (g ≫ f) (fun h0 ↦ hf ?_) (fun hb ↦ hnb ?_)
    · refine LinearMap.ext fun y ↦ ?_
      obtain ⟨x, rfl⟩ := hg.2 y
      exact LinearMap.congr_fun h0 x
    · have heq : ⇑(FDMod.lin f) = ⇑(FDMod.lin (g ≫ f)) ∘ ⇑(LinearEquiv.ofBijective (FDMod.lin g) hg).symm := by
        funext y
        change FDMod.lin f y = FDMod.lin f (FDMod.lin g ((LinearEquiv.ofBijective (FDMod.lin g) hg).symm y))
        congr 1
        exact ((LinearEquiv.ofBijective (FDMod.lin g) hg).apply_symm_apply y).symm
      rw [heq]
      exact hb.comp (LinearEquiv.ofBijective (FDMod.lin g) hg).symm.bijective
  | trans _ _ ih1 ih2 => exact Reach₁.trans (ih1 e hX) ‹_›

namespace DirData

variable (D : DirData k A)

/-- The functionals `ψ` on `A` with `ψ(c) = ψ(e_x c)`: the injective `I_x = D(e_x A)`. -/
def injSub (x : D.ι) : Submodule A (DA k A) where
  carrier := {ψ | ∀ c, ψ.ev (D.e x * c) = ψ.ev c}
  add_mem' {a b} ha hb c := by
    rw [DA.ev_add, DA.ev_add, ha c, hb c]
  zero_mem' c := by simp
  smul_mem' a ψ hψ c := by
    rw [DA.ev_smulA, DA.ev_smulA, mul_assoc]
    exact hψ _

/-- The indecomposable injective at `x`. -/
abbrev injE (x : D.ι) : FDMod k A := FDMod.ofSub (P := FDMod.dualA k A) (D.injSub x)

variable {D}

/-- The map into `I_x` given by a functional. -/
def homToInj (x : D.ι) {W : FDMod k A} (l : Module.Dual k W) : W →ₗ[A] D.injE x where
  toFun w := ⟨DA.mk
    { toFun := fun b ↦ l ((D.e x * b) • w)
      map_add' := fun b c ↦ by rw [mul_add, add_smul, map_add]
      map_smul' := fun c b ↦ by
        rw [mul_smul_comm, smul_assoc, map_smul]; rfl }, fun c ↦ by
      change l ((D.e x * (D.e x * c)) • w) = l ((D.e x * c) • w)
      rw [← mul_assoc, D.e_mul_e]⟩
  map_add' a b := by
    apply Subtype.ext
    apply DA.ext
    intro c
    change l ((D.e x * c) • (a + b)) = l ((D.e x * c) • a) + l ((D.e x * c) • b)
    rw [smul_add, map_add]
  map_smul' a w := by
    apply Subtype.ext
    apply DA.ext
    intro c
    change l ((D.e x * c) • (a • w)) = l ((D.e x * (c * a)) • w)
    rw [← mul_smul, mul_assoc]

lemma homToInj_ev (x : D.ι) {W : FDMod k A} (l : Module.Dual k W) (w : W) (b : A) :
    ((homToInj x l w : D.injE x).1 : DA k A).ev b = l ((D.e x * b) • w) := rfl

/-- The functional of a map into `I_x`. -/
def funOfInj (x : D.ι) {W : FDMod k A} (g : W →ₗ[A] D.injE x) : Module.Dual k W where
  toFun w := ((g w).1 : DA k A).ev 1
  map_add' a b := by rw [map_add]; rfl
  map_smul' c a := by
    rw [LinearMap.map_smul_of_tower]
    rfl

lemma funOfInj_apply (x : D.ι) {W : FDMod k A} (g : W →ₗ[A] D.injE x) (w : W) :
    funOfInj x g w = ((g w).1 : DA k A).ev 1 := rfl

/-- **Every map into `I_x` is given by a functional.** -/
lemma homToInj_funOfInj (x : D.ι) {W : FDMod k A} (g : W →ₗ[A] D.injE x) :
    homToInj x (funOfInj x g) = g := by
  refine LinearMap.ext fun w ↦ Subtype.ext (DA.ext fun b ↦ ?_)
  rw [homToInj_ev, funOfInj_apply, map_smul]
  change ((g w).1 : DA k A).ev (1 * (D.e x * b)) = _
  rw [one_mul]
  exact (g w).2 b

/-- **`I_x` is injective.** -/
theorem injE_extend (x : D.ι) {W W' : FDMod k A} (f : W →ₗ[A] W') (hf : Function.Injective f)
    (g : W →ₗ[A] D.injE x) : ∃ g' : W' →ₗ[A] D.injE x, g' ∘ₗ f = g := by
  obtain ⟨r, hr⟩ := (f.restrictScalars k).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hf)
  refine ⟨homToInj x (funOfInj x g ∘ₗ r), ?_⟩
  conv_rhs => rw [← homToInj_funOfInj x g]
  refine LinearMap.ext fun w ↦ Subtype.ext (DA.ext fun b ↦ ?_)
  change funOfInj x g (r ((D.e x * b) • f w)) = funOfInj x g ((D.e x * b) • w)
  rw [← map_smul, show r (f ((D.e x * b) • w)) = (D.e x * b) • w from
    LinearMap.congr_fun hr _]

/-- A sincere module maps nonzero to `I_x`. -/
lemma exists_hom_injE_ne (x : D.ι) {U : FDMod k A} {u : U} (hu : D.e x • u ≠ 0) :
    ∃ g : U →ₗ[A] D.injE x, g ≠ 0 := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero k hu
  refine ⟨homToInj x l, fun h0 ↦ hl ?_⟩
  have := congrArg (fun g : U →ₗ[A] D.injE x ↦ ((g u).1 : DA k A).ev 1) h0
  simp only [LinearMap.zero_apply] at this
  rw [homToInj_ev, mul_one] at this
  simpa using this

lemma injSub_ev_right {x : D.ι} {ψ : DA k A} (hψ : ψ ∈ D.injSub x) (c : A) :
    (D.e x • ψ).ev c = ψ.ev (D.e x * c * D.e x) := by
  rw [DA.ev_smulA, ← hψ (c * D.e x), mul_assoc]

/-- The unit functional of `I_x`, reading off the coefficient at `x`. -/
lemma e_smul_inj_eq {x : D.ι} (hx : x ∈ D.T) (ψ : D.injE x) (c : A) :
    (((D.e x • ψ : D.injE x).1 : DA k A)).ev c = D.chi x hx c * (ψ.1 : DA k A).ev (D.e x) := by
  change ((D.e x • ψ.1 : DA k A)).ev c = _
  rw [injSub_ev_right ψ.2, D.chi_spec x hx, DA.ev_smulB]

/-- **`I_x` is a brick.** -/
theorem injE_brick {x : D.ι} (hx : x ∈ D.T) (φ : D.injE x ⟶ D.injE x) :
    ∃ c : k, FDMod.lin φ = c • LinearMap.id := by
  -- the unit functional
  let ε : DA k A := DA.mk
    { toFun := fun c ↦ D.chi x hx c
      map_add' := fun a b ↦ map_add _ a b
      map_smul' := fun a b ↦ by simp }
  have hε : ε ∈ D.injSub x := fun c ↦ by
    change D.chi x hx (D.e x * c) = D.chi x hx c
    rw [map_mul, D.chi_e_self, one_mul]
  let u : D.injE x := ⟨ε, hε⟩
  have hu1 : (u.1 : DA k A).ev (D.e x) = 1 := D.chi_e_self x hx
  -- every element fixed by `e_x` is a multiple of `u`
  have hfix : ∀ ψ : D.injE x, D.e x • ψ = (ψ.1 : DA k A).ev (D.e x) • u := by
    intro ψ
    apply Subtype.ext
    apply DA.ext
    intro c
    rw [e_smul_inj_eq hx ψ c]
    change _ = (ψ.1 : DA k A).ev (D.e x) * D.chi x hx c
    ring
  refine ⟨(FDMod.lin φ u).1.ev (D.e x), LinearMap.ext fun ψ ↦ ?_⟩
  apply Subtype.ext
  apply DA.ext
  intro c
  set t := (FDMod.lin φ u).1.ev (D.e x) with ht
  -- evaluate through `e_x c`
  have h1 : (FDMod.lin φ ψ).1.ev c = (FDMod.lin φ ψ).1.ev (D.e x * c) :=
    ((FDMod.lin φ ψ).2 c).symm
  have h2 : (FDMod.lin φ ψ).1.ev (D.e x * c) =
      ((D.e x * c) • (FDMod.lin φ ψ : D.injE x)).1.ev 1 := by
    change _ = (((D.e x * c) • (FDMod.lin φ ψ).1 : DA k A)).ev 1
    rw [DA.ev_smulA, one_mul]
  have h3 : ((D.e x * c) • (FDMod.lin φ ψ : D.injE x)) =
      D.e x • FDMod.lin φ (c • ψ) := by
    rw [← map_smul, ← map_smul, smul_smul]
  have h4 : D.e x • FDMod.lin φ (c • ψ) = FDMod.lin φ (D.e x • (c • ψ)) := (map_smul _ _ _).symm
  have h5 := hfix (c • ψ)
  have h6 : (D.e x • FDMod.lin φ u) = t • u := hfix _
  have h7 : ((c • ψ : D.injE x).1 : DA k A).ev (D.e x) = (ψ.1 : DA k A).ev (D.e x * c) := by
    change ((c • ψ.1 : DA k A)).ev (D.e x) = _
    rw [DA.ev_smulA]
  have h8 : (FDMod.lin φ u).1.ev 1 = t := by
    have := (FDMod.lin φ u).2 1
    rw [mul_one] at this
    exact this.symm
  have h9 : FDMod.lin φ (((c • ψ : D.injE x).1 : DA k A).ev (D.e x) • u) =
      ((c • ψ : D.injE x).1 : DA k A).ev (D.e x) • FDMod.lin φ u :=
    LinearMap.map_smul_of_tower _ _ _
  rw [h1, h2, h3, h4, h5, h9]
  change ((c • ψ : D.injE x).1 : DA k A).ev (D.e x) * (FDMod.lin φ u).1.ev 1 =
    t * (ψ.1 : DA k A).ev c
  rw [h7, h8, ψ.2 c, mul_comm]

/-- `U` is sincere. -/
def Sincere (D : DirData k A) (U : FDMod k A) : Prop := ∀ x, ∃ u : U, D.e x • u ≠ 0

/-- `P` has the lifting property of a projective. -/
def IsProjL (P : FDMod k A) : Prop :=
  ∀ (X Y : FDMod k A) (q : X →ₗ[A] Y), Function.Surjective q → ∀ φ : P →ₗ[A] Y,
    ∃ g : P →ₗ[A] X, q ∘ₗ g = φ

lemma isProjL_projE {e : A} (he : IsIdempotentElem e) : IsProjL (projE (k := k) he) := by
  intro X Y q hq φ
  obtain ⟨g, hg⟩ := projE_lift he (show X ⟶ Y from q) hq (show projE he ⟶ Y from φ)
  exact ⟨g, hg⟩

/-- The index set of an injective envelope. -/
abbrev EnvIdx (D : DirData k A) (Y : FDMod k A) : Type u :=
  ULift.{u} (D.ι × Fin (finrank k (Module.Dual k Y)))

/-- The product of injectives in which `Y` embeds. -/
abbrev envJ (D : DirData k A) (Y : FDMod k A) : FDMod k A :=
  FDMod.pi fun j : EnvIdx D Y ↦ D.injE j.down.1

/-- The embedding. -/
def envMap (Y : FDMod k A) : Y →ₗ[A] envJ D Y :=
  LinearMap.pi fun j ↦ homToInj j.down.1 (Module.finBasis k (Module.Dual k Y) j.down.2)

lemma envMap_injective (Y : FDMod k A) : Function.Injective (envMap (D := D) Y) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  have h1 : ∀ x, D.e x • w = 0 := fun x ↦ by
    have h2 : ∀ l : Module.Dual k Y, l (D.e x • w) = 0 := fun l ↦ by
      have h3 : ∀ i, Module.finBasis k (Module.Dual k Y) i (D.e x • w) = 0 := fun i ↦ by
        have h' : (((envMap (D := D) Y w) ⟨(x, i)⟩).1 : DA k A).ev 1 = 0 :=
          (congrArg (fun φ : envJ D Y ↦ ((φ ⟨(x, i)⟩).1 : DA k A).ev 1) hw).trans
            (by change (0 : DA k A).ev 1 = 0; simp)
        change Module.finBasis k (Module.Dual k Y) i ((D.e x * 1) • w) = 0 at h'
        simpa using h'
      have h4 : l = ∑ i, (Module.finBasis k (Module.Dual k Y)).repr l i •
          Module.finBasis k (Module.Dual k Y) i :=
        ((Module.finBasis k (Module.Dual k Y)).sum_repr l).symm
      rw [h4, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [LinearMap.smul_apply, h3, smul_zero]
    exact (Module.forall_dual_apply_eq_zero_iff k _).1 h2
  have h5 : w = ∑ x, D.e x • w := by
    rw [← Finset.sum_smul, D.sum, one_smul]
  rw [h5]
  exact Finset.sum_eq_zero fun x _ ↦ h1 x

/-- The product of injectives is injective. -/
lemma envJ_extend (Y : FDMod k A) {W W' : FDMod k A} (f : W →ₗ[A] W')
    (hf : Function.Injective f) (g : W →ₗ[A] envJ D Y) :
    ∃ g' : W' →ₗ[A] envJ D Y, g' ∘ₗ f = g := by
  choose g' hg' using fun j : EnvIdx D Y ↦ injE_extend (D := D) j.down.1 f hf
    (LinearMap.proj (R := A) (φ := fun j : EnvIdx D Y ↦ D.injE j.down.1) j ∘ₗ g)
  refine ⟨LinearMap.pi g', LinearMap.ext fun w ↦ funext fun j ↦ ?_⟩
  exact LinearMap.congr_fun (hg' j) w

variable {U : FDMod k A}

/-- **Summands of the cosyzygy of `Y` have no extensions from a predecessor of `U`.** -/
theorem extVanish_cosyz (hT : ∀ x, x ∈ D.T) (hU : Directing U) (hs : Sincere D U) {W : FDMod k A}
    (hW : IsInd W) (hWU : Reach₁ W U ∨ IsoM W U) (Y : FDMod k A) :
    ExtVanish W (FDMod.ofQuot (envJ D Y) (LinearMap.range (envMap (D := D) Y))) := by
  classical
  let Q := FDMod.ofQuot (envJ D Y) (LinearMap.range (envMap (D := D) Y))
  obtain ⟨d⟩ := FDMod.exists_decomp Q
  have hsum : ∑ t, FDMod.lin (d.inc t) ∘ₗ FDMod.lin (d.proj t) = LinearMap.id := d.sum_id
  refine extVanish_snd (fun t ↦ FDMod.lin (d.inc t)) (fun t ↦ FDMod.lin (d.proj t)) d.retr hsum
    fun t ↦ ?_
  intro E i p hi hp hex
  by_contra hns
  have hind : IsInd (d.obj t) := ⟨d.indec t, d.nt t⟩
  have hreach : Reach₁ (d.obj t) U := by
    have h1 := reach_of_nonsplit hind hW i p hp hex hns
    rcases hWU with h | h
    · exact h1.trans h
    · exact h1.trans_iso hU.1 h
  -- the surjection from the product of injectives
  let ρ : envJ D Y →ₗ[A] d.obj t := FDMod.lin (d.proj t) ∘ₗ
    (LinearMap.range (envMap (D := D) Y)).mkQ
  have hρ : Function.Surjective ρ := fun y ↦ by
    obtain ⟨q, hq⟩ := Submodule.mkQ_surjective _ (FDMod.lin (d.inc t) y)
    exact ⟨q, by
      change FDMod.lin (d.proj t) ((LinearMap.range (envMap (D := D) Y)).mkQ q) = y
      rw [hq]
      exact LinearMap.congr_fun (d.retr t) y⟩
  obtain ⟨j, hj⟩ : ∃ j : EnvIdx D Y, ρ ∘ₗ LinearMap.single A
      (fun j : EnvIdx D Y ↦ D.injE j.down.1) j ≠ 0 := by
    by_contra hall
    push Not at hall
    haveI := d.nt t
    obtain ⟨y, hy⟩ := exists_ne (0 : d.obj t)
    apply hy
    obtain ⟨q, rfl⟩ := hρ y
    have hq : q = ∑ j, LinearMap.single A (fun j : EnvIdx D Y ↦ D.injE j.down.1) j (q j) := by
      funext c
      rw [Finset.sum_apply]
      simp [LinearMap.single_apply, Pi.single_apply]
    rw [hq, map_sum]
    exact Finset.sum_eq_zero fun j _ ↦ LinearMap.congr_fun (hall j) _
  obtain ⟨u, hu⟩ := hs j.down.1
  obtain ⟨a, ha⟩ := exists_hom_injE_ne (D := D) j.down.1 hu
  have hI : IsInd (D.injE j.down.1) := by
    refine ⟨isIndecMod_of_brick (injE_brick (hT _)), ?_⟩
    obtain ⟨w, hw⟩ : ∃ w, a w ≠ 0 := by
      by_contra h
      push Not at h
      exact ha (LinearMap.ext h)
    exact ⟨⟨_, 0, hw⟩⟩
  let b : D.injE j.down.1 →ₗ[A] d.obj t := ρ ∘ₗ LinearMap.single A
      (fun j : EnvIdx D Y ↦ D.injE j.down.1) j
  have hIU : Reach₁ (D.injE j.down.1) U := by
    by_cases hb : Function.Bijective b
    · exact Reach₁.iso_trans ⟨show _ ⟶ _ from b, hb⟩ hI hreach
    · exact Reach₁.trans (Reach₁.step hI hind (show _ ⟶ _ from b) hj hb) hreach
  by_cases ha' : Function.Bijective a
  · exact hU.2 (Reach₁.iso_trans ⟨show _ ⟶ _ from a, ha'⟩ hU.1 hIU)
  · exact hU.2 (Reach₁.trans (Reach₁.step hU.1 hI (show _ ⟶ _ from a) ha ha') hIU)

/-- If `W` has no extensions by the cosyzygy of `Y`, a syzygy of `W` has no extensions by `Y`. -/
theorem extVanish_syz_of_cosyz {W K P : FDMod k A} (f : K →ₗ[A] P)
    (g : P →ₗ[A] W) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : LinearMap.range f = LinearMap.ker g) (hP : IsProjL P) (Y : FDMod k A)
    (hv : ExtVanish W (FDMod.ofQuot (envJ D Y) (LinearMap.range (envMap (D := D) Y)))) :
    ExtVanish K Y := by
  intro E i p hi hp hexE
  let N := LinearMap.range (envMap (D := D) Y)
  let Q := FDMod.ofQuot (envJ D Y) N
  let π : envJ D Y →ₗ[A] Q := N.mkQ
  have hπ : Function.Surjective π := Submodule.mkQ_surjective _
  obtain ⟨h, hh⟩ := envJ_extend (D := D) Y i hi (envMap (D := D) Y)
  have hψ0 : (π ∘ₗ h) ∘ₗ i = 0 := by
    refine LinearMap.ext fun y ↦ ?_
    change π (h (i y)) = 0
    rw [show h (i y) = envMap (D := D) Y y from LinearMap.congr_fun hh y]
    exact (Submodule.Quotient.mk_eq_zero N).2 ⟨y, rfl⟩
  obtain ⟨ψ, hψ⟩ := exists_factor i p hp hexE (π ∘ₗ h) hψ0
  obtain ⟨ψ', hψ'⟩ := extend_of_extVanish f g hf hg hex hv ψ
  obtain ⟨g₁, hg₁⟩ := hP (envJ D Y) Q π hπ ψ'
  let δ : E →ₗ[A] envJ D Y := h - g₁ ∘ₗ f ∘ₗ p
  have hδ : π ∘ₗ δ = 0 := by
    refine LinearMap.ext fun e ↦ ?_
    have h1 : π (h e) = ψ (p e) := (LinearMap.congr_fun hψ e).symm
    have h2 : π (g₁ (f (p e))) = ψ' (f (p e)) := LinearMap.congr_fun hg₁ _
    have h3 : ψ' (f (p e)) = ψ (p e) := LinearMap.congr_fun hψ' _
    change π (h e - g₁ (f (p e))) = 0
    rw [map_sub, h1, h2, h3, sub_self]
  obtain ⟨r, hr⟩ := exists_lift (envMap (D := D) Y) π (envMap_injective Y)
    (Submodule.ker_mkQ N).symm δ hδ
  refine exists_section_of_retr i p hp hexE r (LinearMap.ext fun y ↦ ?_)
  apply envMap_injective (D := D) Y
  change envMap (D := D) Y (r (i y)) = envMap (D := D) Y y
  have h1 : envMap (D := D) Y (r (i y)) = δ (i y) := LinearMap.congr_fun hr _
  have h2 : p (i y) = 0 := mem_ker_of_range hexE y
  rw [h1]
  change h (i y) - g₁ (f (p (i y))) = _
  rw [h2, map_zero, map_zero, sub_zero]
  exact LinearMap.congr_fun hh y

/-- **Lemma 3: predecessors of a sincere directing module have projective syzygies.** -/
theorem extVanish_syz_of_pred (hT : ∀ x, x ∈ D.T) (hU : Directing U) (hs : Sincere D U)
    {W K P : FDMod k A} (hW : IsInd W) (hWU : Reach₁ W U ∨ IsoM W U) (f : K →ₗ[A] P)
    (g : P →ₗ[A] W) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : LinearMap.range f = LinearMap.ker g) (hP : IsProjL P) (Y : FDMod k A) :
    ExtVanish K Y :=
  extVanish_syz_of_cosyz f g hf hg hex hP Y (extVanish_cosyz (D := D) hT hU hs hW hWU Y)

/-- Right multiplication by `v`, from `P_y` to `P_x`. -/
def rmul {x : D.ι} (y : D.ι) (v : A) (hv : v * D.e x = v) :
    projE (k := k) (D.idem y) →ₗ[A] projE (k := k) (D.idem x) where
  toFun b := ⟨(b : A) * v, by
    change (b : A) * v * D.e x = _
    rw [mul_assoc, hv]⟩
  map_add' a b := Subtype.ext (add_mul _ _ _)
  map_smul' a b := Subtype.ext (mul_assoc _ _ _)

/-- The generator of `P_x`. -/
def genP (x : D.ι) : projE (k := k) (D.idem x) := ⟨D.e x, e_mem (D.idem x)⟩

lemma smul_gen (x : D.ι) (b : projE (k := k) (D.idem x)) : (b : A) • genP (k := k) x = b :=
  Subtype.ext b.2

/-- **Quotients of `P_x` are bricks.** -/
theorem quot_brick {x : D.ι} (hx : x ∈ D.T) (N : Submodule A (projE (k := k) (D.idem x)))
    (φ : FDMod.ofQuot (projE (k := k) (D.idem x)) N ⟶
      FDMod.ofQuot (projE (k := k) (D.idem x)) N) :
    ∃ c : k, FDMod.lin φ = c • LinearMap.id := by
  let ge : FDMod.ofQuot (projE (k := k) (D.idem x)) N := N.mkQ (genP x)
  obtain ⟨c, hc⟩ := Submodule.mkQ_surjective N (FDMod.lin φ ge)
  have hee : D.e x • genP (k := k) x = genP x := Subtype.ext (D.idem x).eq
  have hge : D.e x • ge = ge := by
    change D.e x • N.mkQ (genP x) = _
    rw [← map_smul, hee]
  have h1 : D.e x • (c : projE (k := k) (D.idem x)) = D.chi x hx (c : A) • genP (k := k) x := by
    apply Subtype.ext
    change D.e x * (c : A) = D.chi x hx (c : A) • D.e x
    rw [← D.chi_spec, mul_assoc, show (c : A) * D.e x = c from c.2]
  have h2 : FDMod.lin φ ge = D.chi x hx (c : A) • ge := by
    have h3 : FDMod.lin φ ge = D.e x • FDMod.lin φ ge := by
      rw [← map_smul, hge]
    rw [h3, ← hc, ← map_smul, h1]
    rfl
  refine ⟨D.chi x hx (c : A), LinearMap.ext fun z ↦ ?_⟩
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective N z
  have h4 : N.mkQ b = (b : A) • ge := by
    change N.mkQ b = (b : A) • N.mkQ (genP x)
    rw [← map_smul, smul_gen]
  rw [h4, map_smul, h2, LinearMap.smul_apply, LinearMap.id_apply, smul_comm]

/-- **Lemma 4 (Vossieck).** A nonzero morphism `v : x → y`, `x ≠ y`, acts on a sincere directing
module injectively or surjectively. -/
theorem mono_or_epi (hT : ∀ x, x ∈ D.T) (hU : Directing U) (hs : Sincere D U) {x y : D.ι}
    (hxy : x ≠ y) (a : A) (hv : D.e y * a * D.e x ≠ 0) :
    (∀ u : U, D.e x • u = u → (D.e y * a * D.e x) • u = 0 → u = 0) ∨
      ∀ w : U, D.e y • w = w → ∃ u : U, D.e x • u = u ∧ (D.e y * a * D.e x) • u = w := by
  classical
  set v := D.e y * a * D.e x with hvdef
  have hvr : v * D.e x = v := by rw [hvdef, mul_assoc, D.e_mul_e]
  have hvl : D.e y * v = v := by rw [hvdef, ← mul_assoc, ← mul_assoc, D.e_mul_e]
  let P := projE (k := k) (D.idem x)
  let Py := projE (k := k) (D.idem y)
  let p : Py →ₗ[A] P := rmul y v hvr
  let N := LinearMap.range p
  let V : FDMod k A := FDMod.ofQuot P N
  let π : P →ₗ[A] V := N.mkQ
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨u, hu1, hu2, hu0⟩, ⟨w, hw1, hw2⟩⟩ := hcon
  -- `V` is a nonzero brick
  have hgenP : genP (k := k) x ∉ N := by
    rintro ⟨b, hb⟩
    have h1 : (b : A) * v = D.e x := congrArg Subtype.val hb
    have h2 : (D.e x * (b : A) * D.e y) * (D.e y * a * D.e x) = 0 := D.corner_cross hxy _ _
    have h3 : D.e x = D.e x * ((b : A) * v) * D.e x := by rw [h1, D.e_mul_e, D.e_mul_e]
    apply D.ne x (hT x)
    rw [h3, ← h2, hvdef]
    have hb' : (b : A) * D.e y = b := b.2
    conv_lhs => rw [← hb']
    simp only [mul_assoc, D.e_mul_e]
  have hVnt : Nontrivial V := ⟨⟨N.mkQ (genP x), 0, fun h ↦ hgenP ((Submodule.Quotient.mk_eq_zero N).1 h)⟩⟩
  have hVi : IsInd V := ⟨isIndecMod_of_brick (quot_brick (hT x) N), hVnt⟩
  -- the map `V → U`
  let F : P →ₗ[A] U :=
    { toFun := fun b ↦ (b : A) • u
      map_add' := fun a b ↦ add_smul _ _ _
      map_smul' := fun a b ↦ mul_smul _ _ _ }
  have hF : N ≤ LinearMap.ker F := by
    rintro _ ⟨b, rfl⟩
    change ((b : A) * v) • u = 0
    rw [mul_smul, hu2, smul_zero]
  let f : V →ₗ[A] U := N.liftQ F hF
  have hf0 : f ≠ 0 := by
    intro h0
    apply hu0
    have h1 : f (N.mkQ (genP x)) = D.e x • u := rfl
    rw [h0, LinearMap.zero_apply, hu1] at h1
    exact h1.symm
  have hVU : Reach₁ V U ∨ IsoM V U := by
    by_cases hb : Function.Bijective f
    · exact Or.inr ⟨show _ ⟶ _ from f, hb⟩
    · exact Or.inl (Reach₁.step hVi hU.1 (show _ ⟶ _ from f) hf0 hb)
  -- the syzygy `N` is projective
  have hK := extVanish_syz_of_pred (D := D) hT hU hs (K := FDMod.ofSub N) (P := P) hVi hVU
    N.subtype π Subtype.val_injective (Submodule.mkQ_surjective N)
    (by rw [Submodule.range_subtype]; exact (Submodule.ker_mkQ N).symm)
    (isProjL_projE (D.idem x)) (FDMod.ofSub (LinearMap.ker p))
  let p' : Py →ₗ[A] FDMod.ofSub N := p.rangeRestrict
  obtain ⟨σ, hσ⟩ := hK Py (LinearMap.ker p).subtype p' Subtype.val_injective
    p.surjective_rangeRestrict (by rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict])
  have hσ' : ∀ z, p' (σ z) = z := fun z ↦ LinearMap.congr_fun hσ z
  obtain ⟨c, hc⟩ := projE_brick (k := k) (D.idem y) (D.local_ y)
    (show Py ⟶ Py from σ ∘ₗ p')
  have hc' : ∀ b, σ (p' b) = c • b := fun b ↦ LinearMap.congr_fun hc b
  have hgy : p (genP (k := k) y) = ⟨v, hvr⟩ := Subtype.ext hvl
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 : p' (σ (p' (genP y))) = p' (genP y) := hσ' _
    rw [hc', zero_smul, map_zero] at h1
    have h2 : p (genP y) = 0 := congrArg Subtype.val h1.symm
    rw [hgy] at h2
    exact hv (congrArg Subtype.val h2)
  have hinj : Function.Injective p' := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    have h1 := hc' b
    rw [hb, map_zero] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_left hc0
  have hret : ∀ b, σ (p' b) = b := fun b ↦ hinj (hσ' _)
  -- the extension
  have hv' : ExtVanish V U := by
    rcases hVU with h | ⟨g, hg⟩
    · exact hU.extVanish_pred hVi h
    · exact hU.extVanish.of_iso (LinearEquiv.ofBijective (FDMod.lin g) hg).symm
  let G : Py →ₗ[A] U :=
    { toFun := fun b ↦ (b : A) • w
      map_add' := fun a b ↦ add_smul _ _ _
      map_smul' := fun a b ↦ mul_smul _ _ _ }
  obtain ⟨ψ, hψ⟩ := extend_of_extVanish (P₀ := P) (P₁ := FDMod.ofSub N) (Z := V) (W := U)
    N.subtype π Subtype.val_injective (Submodule.mkQ_surjective N)
    (by rw [Submodule.range_subtype]; exact (Submodule.ker_mkQ N).symm) hv' (G ∘ₗ σ)
  refine hw2 (ψ (genP x)) ?_ ?_
  · rw [← map_smul]
    congr 1
    exact Subtype.ext (D.idem x).eq
  · rw [← map_smul]
    have h1 : v • genP (k := k) x = N.subtype (p' (genP y)) :=
      Subtype.ext (hvr.trans hvl.symm)
    rw [h1]
    have h2 : ψ (N.subtype (p' (genP y))) = G (σ (p' (genP y))) := LinearMap.congr_fun hψ _
    rw [h2, hret]
    exact hw1

end DirData

end LargeIndecomposable.AR
