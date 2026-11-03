module

public import LargeIndecomposable.RepresentationEmbeddings.QuotientConstruction.QuotientProps
public import LargeIndecomposable.RepresentationEmbeddings.Control.Retraction

/-!
# Proposition 4.1: retractions for the quotient construction

For `F₁(T) = (Λe_y ⊗ W)/{s ⊗ a(v) + t ⊗ b(v)}` (Construction 3.3), a
homomorphism `f : F₁(T) → F₁(U)` induces `h : W → W'` on the tops, and the map
`d(w₁, w₂) = s w₁ + t w₂` with kernel `{(a(v), b(v))}` (3.1) gives the unique
`g : V → V'` with `ha = a'g`, `hb = b'g`. Then `ρ(f) = (g, h)` are retractions
for `F₁` on `D`; `ρ(f) = 0` exactly when `f` maps into `J F₁(U)`, so any
`n` such maps compose to zero if `J^n = 0`. The argument does not use finite
dimension.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair TensorProduct

universe u

variable {k : Type u} [Field k] {Λ : Type u} [Ring Λ] [Algebra k Λ]

namespace QuotientData

variable (Q : QuotientData k Λ)

/-- The underlying type of `F₁(X)`. -/
abbrev Qt (X : Kron k) : Type u := Q.P ⊗[k] X.W ⧸ Q.relSub X

/-- A homomorphism `F₁(X) → F₁(Y)` as a `Λ`-linear map. -/
abbrev fL {X Y : Kron k} (f : Q.functor.obj X ⟶ Q.functor.obj Y) : Q.Qt X →ₗ[Λ] Q.Qt Y := f.hom

instance : Q.functor.Additive where
  map_add {X Y f f'} := by
    apply ModuleCat.hom_ext
    change Q.fL (Q.functor.map (f + f')) = Q.fL (Q.functor.map f) + Q.fL (Q.functor.map f')
    refine Submodule.linearMap_qext _ (TensorProduct.AlgebraTensorModule.ext fun p w ↦ ?_)
    exact (congrArg (Submodule.Quotient.mk (p := Q.relSub Y))
      (TensorProduct.tmul_add p ((f.app one).hom w) ((f'.app one).hom w))).trans
      (Submodule.Quotient.mk_add _)

lemma lTensor_smul_eq {W W' : ModuleCat.{u} k} (h : W ⟶ W') (c : k) (x : Q.P ⊗[k] W) :
    Q.tensorMap (c • h) x = Q.tensorMap h (algebraMap k Λ c • x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p w =>
    rw [tensorMap_tmul, TensorProduct.smul_tmul', tensorMap_tmul, ModuleCat.hom_smul,
      LinearMap.smul_apply, TensorProduct.tmul_smul, algebraMap_smul, TensorProduct.smul_tmul']
  | add x y hx hy => rw [map_add, hx, hy, smul_add, map_add]

open ModuleCat in
instance : Q.functor.Linear k where
  map_smul {X Y} f c := by
    have key : ∀ x : Q.P ⊗[k] X.W, Q.fL (Q.functor.map (c • f)) (Submodule.Quotient.mk x) =
        Q.fL (Q.functor.map f) (algebraMap k Λ c • Submodule.Quotient.mk x) := fun x ↦ by
      change Submodule.Quotient.mk (Q.tensorMap ((c • f).app one) x) =
        Submodule.Quotient.mk (Q.tensorMap (f.app one) (algebraMap k Λ c • x))
      rw [NatTrans.app_smul, lTensor_smul_eq]
    ext m
    conv_rhs => rw [ModuleCat.hom_smul, LinearMap.smul_apply, ← algebraMap_smul Λ c, ← map_smul]
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (Q.relSub X) m
    exact key x

variable {Q}

lemma s_smul_radPow {M : Type u} [AddCommGroup M] [Module Λ M] {m : M}
    (hm : m ∈ radPow Λ M 1) : Q.s • m = 0 := by
  induction hm using AddSubgroup.closure_induction with
  | mem m hm =>
    obtain ⟨l, hl, hJ, m, rfl⟩ := hm
    obtain ⟨j, rfl⟩ := List.length_eq_one_iff.1 hl
    rw [List.prod_singleton, ← mul_smul, Q.s_mul_J j (hJ j (by simp)), zero_smul]
  | zero => simp
  | add x y _ _ h₁ h₂ => rw [smul_add, h₁, h₂, add_zero]
  | neg x _ h => rw [smul_neg, h, neg_zero]

lemma t_smul_radPow {M : Type u} [AddCommGroup M] [Module Λ M] {m : M}
    (hm : m ∈ radPow Λ M 1) : Q.t • m = 0 := by
  induction hm using AddSubgroup.closure_induction with
  | mem m hm =>
    obtain ⟨l, hl, hJ, m, rfl⟩ := hm
    obtain ⟨j, rfl⟩ := List.length_eq_one_iff.1 hl
    rw [List.prod_singleton, ← mul_smul, Q.t_mul_J j (hJ j (by simp)), zero_smul]
  | zero => simp
  | add x y _ _ h₁ h₂ => rw [smul_add, h₁, h₂, add_zero]
  | neg x _ h => rw [smul_neg, h, neg_zero]

section Control

variable (hx : TopOneDim k Q.ex) (hy : TopOneDim k Q.ey)

/-- Every element is `e_y ⊗ (its top)` modulo `J F₁(X)`. -/
lemma sub_gen_topQ_mem (X : Kron k) (m : Q.P ⊗[k] X.W ⧸ Q.relSub X) :
    m - Q.gen X (topQ hy X m) ∈ radPow Λ _ 1 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  exact π_sub_gen_mem hy X x

/-- The map on tops induced by `f : F₁(X) → F₁(Y)`. -/
def hMap {X Y : Kron k} (f : Q.functor.obj X ⟶ Q.functor.obj Y) : X.W →ₗ[k] Y.W :=
  topQ hy Y ∘ₗ ((Q.fL f).restrictScalars k) ∘ₗ Q.gen X

lemma hMap_apply {X Y : Kron k} (f : Q.functor.obj X ⟶ Q.functor.obj Y) (w : X.W) :
    hMap hy f w = topQ hy Y (Q.fL f (Q.gen X w)) := rfl

/-- `f(e_y ⊗ w) = e_y ⊗ h(w)` modulo `J F₁(Y)`. -/
lemma map_gen_sub_mem {X Y : Kron k} (f : Q.functor.obj X ⟶ Q.functor.obj Y) (w : X.W) :
    Q.fL f (Q.gen X w) - Q.gen Y (hMap hy f w) ∈ radPow Λ _ 1 :=
  sub_gen_topQ_mem hy Y _

lemma topQ_map_eq {X Y : Kron k} (f : Q.functor.obj X ⟶ Q.functor.obj Y)
    (m : Q.Qt X) : topQ hy Y (Q.fL f m) = hMap hy f (topQ hy X m) := by
  have hr := sub_gen_topQ_mem hy X m
  have e : Q.fL f m = Q.fL f (Q.gen X (topQ hy X m)) + Q.fL f (m - Q.gen X (topQ hy X m)) := by
    rw [← map_add, add_sub_cancel]
  rw [e, map_add, topQ_radPow hy Y (map_mem_radPow (Q.fL f) hr), add_zero]
  rfl

lemma π_relMap_eq (X : Kron k) (v : X.V) :
    Q.π X (Q.relMap X v) = Q.s • Q.gen X (X.a.hom v) + Q.t • Q.gen X (X.b.hom v) := by
  rw [relMap_apply, map_add, π_tmul, π_tmul]
  rfl

lemma s_gen_add_t_gen (X : Kron k) (w₁ w₂ : X.W) :
    Q.s • Q.gen X w₁ + Q.t • Q.gen X w₂ = Q.π X (Q.sP ⊗ₜ w₁ + Q.tP ⊗ₜ w₂) := by
  rw [map_add, π_tmul, π_tmul]
  rfl

include hx in
/-- (3.1): the kernel of `d(w₁, w₂) = s w₁ + t w₂` is `{(a(v), b(v))}`. -/
lemma d_eq_zero_iff (X : Kron k) (w₁ w₂ : X.W) :
    Q.s • Q.gen X w₁ + Q.t • Q.gen X w₂ = 0 ↔ ∃ v, X.a.hom v = w₁ ∧ X.b.hom v = w₂ := by
  rw [s_gen_add_t_gen, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Q.mem_relSub_iff hx]
  constructor
  · rintro ⟨v, hv⟩
    rw [relMap_apply] at hv
    exact ⟨v, Q.tmul_eq_tmul X.W hv⟩
  · rintro ⟨v, rfl, rfl⟩
    exact ⟨v, rfl⟩

lemma s_smul_map_gen {X Y : Kron k} (f : Q.functor.obj X ⟶ Q.functor.obj Y) (w : X.W) :
    Q.s • Q.fL f (Q.gen X w) = Q.s • Q.gen Y (hMap hy f w) := by
  rw [← sub_eq_zero, ← smul_sub, s_smul_radPow (map_gen_sub_mem hy f w)]

lemma t_smul_map_gen {X Y : Kron k} (f : Q.functor.obj X ⟶ Q.functor.obj Y) (w : X.W) :
    Q.t • Q.fL f (Q.gen X w) = Q.t • Q.gen Y (hMap hy f w) := by
  rw [← sub_eq_zero, ← smul_sub, t_smul_radPow (map_gen_sub_mem hy f w)]

lemma hMap_rel {X Y : Kron k} (f : Q.functor.obj X ⟶ Q.functor.obj Y) (v : X.V) :
    Q.s • Q.gen Y (hMap hy f (X.a.hom v)) + Q.t • Q.gen Y (hMap hy f (X.b.hom v)) = 0 := by
  rw [← s_smul_map_gen, ← t_smul_map_gen, ← (Q.fL f).map_smul, ← (Q.fL f).map_smul,
    ← (Q.fL f).map_add, ← π_relMap_eq, π_relMap, map_zero]

include hx in
lemma exists_g {X Y : Kron k} (f : Q.functor.obj X ⟶ Q.functor.obj Y) (v : X.V) :
    ∃ v', Y.a.hom v' = hMap hy f (X.a.hom v) ∧ Y.b.hom v' = hMap hy f (X.b.hom v) :=
  (d_eq_zero_iff hx Y _ _).1 (hMap_rel hy f v)

lemma eq_of_ab {Y : Kron k} (hY : InD Y) {v v' : Y.V} (ha : Y.a.hom v = Y.a.hom v')
    (hb : Y.b.hom v = Y.b.hom v') : v = v' := by
  rw [← sub_eq_zero]
  exact (inD_iff Y).1 hY _ (by rw [map_sub, ha, sub_self]) (by rw [map_sub, hb, sub_self])

/-- The component `g : V → V'` of `ρ(f)`. -/
def gMap {X Y : Kron k} (hY : InD Y) (f : Q.functor.obj X ⟶ Q.functor.obj Y) : X.V →ₗ[k] Y.V where
  toFun v := (exists_g hx hy f v).choose
  map_add' v v' := by
    have h := (exists_g hx hy f (v + v')).choose_spec
    have h₁ := (exists_g hx hy f v).choose_spec
    have h₂ := (exists_g hx hy f v').choose_spec
    refine eq_of_ab hY ?_ ?_
    · rw [h.1, map_add, map_add, map_add, h₁.1, h₂.1]
    · rw [h.2, map_add, map_add, map_add, h₁.2, h₂.2]
  map_smul' c v := by
    have h := (exists_g hx hy f (c • v)).choose_spec
    have h₁ := (exists_g hx hy f v).choose_spec
    refine eq_of_ab hY ?_ ?_
    · rw [h.1, map_smul, map_smul, map_smul, h₁.1]; rfl
    · rw [h.2, map_smul, map_smul, map_smul, h₁.2]; rfl

lemma gMap_spec {X Y : Kron k} (hY : InD Y) (f : Q.functor.obj X ⟶ Q.functor.obj Y) (v : X.V) :
    Y.a.hom (gMap hx hy hY f v) = hMap hy f (X.a.hom v) ∧
      Y.b.hom (gMap hx hy hY f v) = hMap hy f (X.b.hom v) :=
  (exists_g hx hy f v).choose_spec

/-- Proposition 4.1: the Kronecker morphism `ρ(f) = (g, h)`. -/
def ρK {X Y : Kron k} (hY : InD Y) (f : Q.functor.obj X ⟶ Q.functor.obj Y) : X ⟶ Y :=
  Kron.homMk (ModuleCat.ofHom (gMap hx hy hY f)) (ModuleCat.ofHom (hMap hy f))
    (by ext v; exact (gMap_spec hx hy hY f v).1.symm)
    (by ext v; exact (gMap_spec hx hy hY f v).2.symm)

lemma ρK_ext {X Y : Kron k} (hY : InD Y) (f : Q.functor.obj X ⟶ Q.functor.obj Y) (u : X ⟶ Y)
    (h : ∀ w, hMap hy f w = (u.app one).hom w) : ρK hx hy hY f = u := by
  have h1 : (ρK hx hy hY f).app one = u.app one := by ext w; exact h w
  refine Kron.hom_ext ?_ h1
  ext v
  refine eq_of_ab hY ?_ ?_
  · change Y.a.hom (gMap hx hy hY f v) = _
    rw [(gMap_spec hx hy hY f v).1, h, Kron.a_apply]
  · change Y.b.hom (gMap hx hy hY f v) = _
    rw [(gMap_spec hx hy hY f v).2, h, Kron.b_apply]

lemma hMap_comp {X Y Z : Kron k} (f : Q.functor.obj X ⟶ Q.functor.obj Y)
    (f' : Q.functor.obj Y ⟶ Q.functor.obj Z) (w : X.W) :
    hMap hy (f ≫ f') w = hMap hy f' (hMap hy f w) := by
  change topQ hy Z (Q.fL f' (Q.fL f (Q.gen X w))) = _
  rw [topQ_map_eq]
  rfl

lemma hMap_map {X Y : Kron k} (u : X ⟶ Y) (w : X.W) :
    hMap hy (Q.functor.map u) w = (u.app one).hom w :=
  topQ_functor_map_gen hy u w

/-- `ρ(f) = 0` forces `f` into `J F₁(Y)`. -/
lemma map_mem_radPow_of_hMap {X Y : Kron k} (f : Q.functor.obj X ⟶ Q.functor.obj Y)
    (hf : ∀ w, hMap hy f w = 0) (m : Q.Qt X) : Q.fL f m ∈ radPow Λ _ 1 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p w =>
    have := map_gen_sub_mem hy f w
    rw [hf, map_zero, sub_zero] at this
    change Q.fL f (Q.π X (p ⊗ₜ w)) ∈ _
    rw [π_tmul, map_smul]
    exact smul_mem_radPow _ this
  | add x y hx hy' => rw [Submodule.Quotient.mk_add, map_add]; exact add_mem hx hy'

lemma map_radPow_succ {M N : Type u} [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (φ : M →ₗ[Λ] N) (hφ : ∀ m, φ m ∈ radPow Λ N 1) {i : ℕ} {m : M} (hm : m ∈ radPow Λ M i) :
    φ m ∈ radPow Λ N (i + 1) := by
  induction hm using AddSubgroup.closure_induction with
  | mem m hm =>
    obtain ⟨l, hl, hJ, m, rfl⟩ := hm
    rw [map_smul, ← hl]
    exact list_prod_smul_mem_radPow hJ (hφ m)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  | neg x _ h => rw [map_neg]; exact neg_mem h

lemma mem_radPow_zero {M : Type u} [AddCommGroup M] [Module Λ M] (m : M) : m ∈ radPow Λ M 0 := by
  simpa using smul_mem_radPow_of_mem (Λ := Λ) (l := []) rfl (by simp) m

/-- `F₁` on `D`. -/
abbrev ΦD (Q : QuotientData k Λ) : D k ⥤ ModuleCat.{u} Λ := (InD (k := k)).ι ⋙ Q.functor

lemma hMap_add {X Y : Kron k} (f f' : Q.functor.obj X ⟶ Q.functor.obj Y) (w : X.W) :
    hMap hy (f + f') w = hMap hy f w + hMap hy f' w := by
  rw [hMap_apply, hMap_apply, hMap_apply, ← map_add]
  rfl

open ModuleCat in
lemma hMap_smul {X Y : Kron k} (c : k) (f : Q.functor.obj X ⟶ Q.functor.obj Y) (w : X.W) :
    hMap hy (c • f) w = c • hMap hy f w := by
  rw [hMap_apply, hMap_apply, ← map_smul]
  congr 1
  change (c • f).hom (Q.gen X w) = c • Q.fL f (Q.gen X w)
  exact ((algebraMap_smul Λ c (f.hom (Q.gen X w) : ↑(Q.functor.obj Y))).symm).trans
    (algebraMap_smul Λ c (Q.fL f (Q.gen X w)))

/-- Proposition 4.1: retractions for `F₁` on `D`. -/
def retractions : Retractions k (ΦD Q) where
  ρ X Y :=
    { toFun f := ObjectProperty.homMk (ρK hx hy Y.2 f)
      map_add' f f' := by
        ext1
        exact ρK_ext hx hy Y.2 _ _ fun w ↦ (hMap_add hy f f' w).trans rfl
      map_smul' c f := by
        ext1
        exact ρK_ext hx hy Y.2 _ _ fun w ↦ (hMap_smul hy c f w).trans rfl }
  map_comp {X Y Z} f f' := by
    ext1
    exact ρK_ext hx hy Z.2 _ _ fun w ↦ (hMap_comp hy f f' w).trans rfl
  ρ_map {X Y} u := by
    ext1
    exact ρK_ext hx hy Y.2 _ _ fun w ↦ hMap_map hy u.hom w

lemma hMap_eq_zero_of_ρ {X Y : D k} {f : (ΦD Q).obj X ⟶ (ΦD Q).obj Y}
    (h : (retractions hx hy).ρ X Y f = 0) (w : X.obj.W) : hMap hy f w = 0 := by
  have := congrArg (fun φ : X ⟶ Y ↦ (φ.hom.app one).hom w) h
  exact this

lemma kerChain_mem {n : ℕ} {X Y : D k} {f : (ΦD Q).obj X ⟶ (ΦD Q).obj Y}
    (hf : (retractions hx hy).KerChain n f) (m : Q.Qt X.obj) : Q.fL f m ∈ radPow Λ _ n := by
  induction hf with
  | nil X => exact mem_radPow_zero m
  | cons hf hg ih =>
    exact map_radPow_succ _ (map_mem_radPow_of_hMap hy _ (hMap_eq_zero_of_ρ hx hy hg)) (ih m)

/-- Proposition 4.1: if `J^n = 0`, every composite of `n` maps in the kernels
of the retractions vanishes. -/
theorem nilpotentBound {n : ℕ}
    (hJ : ∀ l : List Λ, l.length = n → (∀ j ∈ l, j ∈ Ring.jacobson Λ) → l.prod = 0) :
    (retractions hx hy).NilpotentBound n := by
  intro X Y f hf
  apply ModuleCat.hom_ext
  exact LinearMap.ext fun m ↦ eq_zero_of_mem_radPow hJ (kerChain_mem hx hy hf m)

end Control

end QuotientData

end LargeIndecomposable
