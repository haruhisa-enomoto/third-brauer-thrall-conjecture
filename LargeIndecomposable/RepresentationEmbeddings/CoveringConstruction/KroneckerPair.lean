module

public import LargeIndecomposable.RepresentationEmbeddings.CoveringConstruction.Datum
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Flat.Basic

/-!
# The functor `L` from a Kronecker pair

A *Kronecker pair* on a finite quiver `D` consists of two representations `P`
and `Q₀` with finite-dimensional spaces, which are bricks and have disjoint
supports, together with two families `z₁, z₂` of maps `z_α : P(i) → Q₀(j)`
for the arrows `α : i → j` that are linearly independent as tuples
(two independent extension classes in `Ext¹(P, Q₀)`).

For a finite-dimensional Kronecker module `T = (V, W; a, b)`,
`L(T)(i) = (Q₀(i) ⊗ W) × (P(i) ⊗ V)` with arrow maps
`[[Q₀(α) ⊗ 1, z₁,α ⊗ a + z₂,α ⊗ b], [0, P(α) ⊗ 1]]`, and `L(g, h) = (1 ⊗ h) × (1 ⊗ g)`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair TensorProduct

universe u

namespace Covering

variable {k : Type u} [Field k]

variable (k) in
/-- A Kronecker pair on a finite quiver `D`. -/
structure KroneckerPair (D : FinQuiver) where
  /-- The brick receiving `V`. -/
  P : Rep k D
  /-- The brick receiving `W`. -/
  Q₀ : Rep k D
  finP : ∀ i, FiniteDimensional k (P.obj i)
  finQ : ∀ i, FiniteDimensional k (Q₀.obj i)
  disjoint : ∀ i, Subsingleton (P.obj i) ∨ Subsingleton (Q₀.obj i)
  brickP : ∀ f : P ⟶ P, ∃ c : k, ∀ i, (f.app i).hom = c • LinearMap.id
  brickQ : ∀ f : Q₀ ⟶ Q₀, ∃ c : k, ∀ i, (f.app i).hom = c • LinearMap.id
  /-- The first extension tuple. -/
  z₁ : ∀ α : D.A, P.obj (D.src α) →ₗ[k] Q₀.obj (D.tgt α)
  /-- The second extension tuple. -/
  z₂ : ∀ α : D.A, P.obj (D.src α) →ₗ[k] Q₀.obj (D.tgt α)
  indep : ∀ c₁ c₂ : k, (∀ α, c₁ • z₁ α + c₂ • z₂ α = 0) → c₁ = 0 ∧ c₂ = 0
  nonzeroP : ∃ i, Nontrivial (P.obj i)
  nonzeroQ : ∃ i, Nontrivial (Q₀.obj i)

/-! ### Tensor products with a brick -/

section BrickTensor

variable {X W : Type u} [AddCommGroup X] [Module k X] [AddCommGroup W] [Module k W]
  [FiniteDimensional k W]

lemma equivFinsupp_apply_eq (t : X ⊗[k] W) (i : Fin (Module.finrank k W)) :
    (TensorProduct.equivFinsuppOfBasisRight (Module.finBasis k W) t) i =
      (TensorProduct.rid k X) (TensorProduct.map LinearMap.id ((Module.finBasis k W).coord i) t) := by
  induction t using TensorProduct.inductionOn with
  | tmul x w => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.coe_add, Pi.add_apply, hx, hy]

/-- An element of `X ⊗ W` is determined by its contractions with functionals
on `W`. -/
lemma tensor_eq_zero_of_contract (t : X ⊗[k] W)
    (h : ∀ μ : Module.Dual k W, (TensorProduct.rid k X) (TensorProduct.map LinearMap.id μ t) = 0) :
    t = 0 := by
  have : TensorProduct.equivFinsuppOfBasisRight (Module.finBasis k W) t = 0 := by
    ext i; rw [equivFinsupp_apply_eq, h]; rfl
  simpa using this

end BrickTensor

/-- Maps between `X ⊗ W` and `X ⊗ W'` commuting with the arrows, for a brick `X`
with finite-dimensional spaces, are `1 ⊗ h`. -/
theorem brick_tensor {D : FinQuiver} (X : Rep k D)
    (hbrick : ∀ f : X ⟶ X, ∃ c : k, ∀ i, (f.app i).hom = c • LinearMap.id)
    {W W' : Type u} [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']
    [FiniteDimensional k W'] (φ : ∀ i, X.obj i ⊗[k] W →ₗ[k] X.obj i ⊗[k] W')
    (hφ : ∀ α : D.A, φ (D.tgt α) ∘ₗ TensorProduct.map (X.map α).hom LinearMap.id =
      TensorProduct.map (X.map α).hom LinearMap.id ∘ₗ φ (D.src α)) :
    ∃ h : W →ₗ[k] W', ∀ i, φ i = TensorProduct.map LinearMap.id h := by
  by_cases hX : ∃ i₀, Nontrivial (X.obj i₀)
  swap
  · push Not at hX
    refine ⟨0, fun i ↦ ?_⟩
    have : Subsingleton (X.obj i) := hX i
    apply TensorProduct.ext'
    intro x w
    rw [Subsingleton.elim x 0]
    simp
  obtain ⟨i₀, hi₀⟩ := hX
  obtain ⟨q₀, hq₀⟩ := exists_ne (0 : X.obj i₀)
  obtain ⟨lam, hlam⟩ := Module.Projective.exists_dual_eq_one k hq₀
  let h : W →ₗ[k] W' := (TensorProduct.lid k W').toLinearMap ∘ₗ TensorProduct.map lam LinearMap.id ∘ₗ
    φ i₀ ∘ₗ TensorProduct.mk k _ _ q₀
  refine ⟨h, fun i ↦ TensorProduct.ext' fun q w ↦ ?_⟩
  -- the endomorphism `q ↦ (1 ⊗ μ)(φ(q ⊗ w))` of `X`
  have hend : ∀ μ : Module.Dual k W', ∃ c : k, ∀ (j : D.V) (q : X.obj j),
      (TensorProduct.rid k (X.obj j)) (TensorProduct.map LinearMap.id μ (φ j (q ⊗ₜ w))) = c • q := by
    intro μ
    let e : X ⟶ X :=
      { app := fun j ↦ ModuleCat.ofHom ((TensorProduct.rid k (X.obj j)).toLinearMap ∘ₗ
          TensorProduct.map LinearMap.id μ ∘ₗ φ j ∘ₗ (TensorProduct.mk k _ _).flip w)
        comm := fun α ↦ by
          ext x
          have := congrArg (fun F ↦ F (x ⊗ₜ w)) (hφ α)
          simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply] at this
          change (TensorProduct.rid k _) (TensorProduct.map LinearMap.id μ
              (φ (D.tgt α) ((X.map α).hom x ⊗ₜ w))) =
            (X.map α).hom ((TensorProduct.rid k _) (TensorProduct.map LinearMap.id μ
              (φ (D.src α) (x ⊗ₜ w))))
          rw [this]
          generalize φ (D.src α) (x ⊗ₜ w) = t
          induction t using TensorProduct.inductionOn with
          | tmul a b => simp
          | add a b ha hb => simp only [map_add, ha, hb] }
    obtain ⟨c, hc⟩ := hbrick e
    exact ⟨c, fun j q ↦ by simpa [e] using congrArg (fun F ↦ F q) (hc j)⟩
  refine sub_eq_zero.1 (tensor_eq_zero_of_contract _ fun μ ↦ ?_)
  obtain ⟨c, hc⟩ := hend μ
  have hμ : μ (h w) = c := by
    have := hc i₀ q₀
    have key : ∀ t : X.obj i₀ ⊗[k] W', μ ((TensorProduct.lid k W') (TensorProduct.map lam LinearMap.id t)) =
        lam ((TensorProduct.rid k (X.obj i₀)) (TensorProduct.map LinearMap.id μ t)) := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul a b => simp [mul_comm]
      | add a b ha hb => simp only [map_add, ha, hb]
    simp only [h, LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
      LinearEquiv.coe_coe]
    rw [key, this, map_smul, hlam, smul_eq_mul, mul_one]
  rw [map_sub, map_sub, hc i q]
  simp [hμ]

namespace KroneckerPair

variable {D : FinQuiver} (K : KroneckerPair k D)

/-- The space `L(T)(i) = (Q₀(i) ⊗ W) × (P(i) ⊗ V)`. -/
abbrev space (T : Kfin k) (i : D.V) : Type u :=
  (K.Q₀.obj i ⊗[k] T.obj.W) × (K.P.obj i ⊗[k] T.obj.V)

/-- The arrow map of `L(T)`. -/
def arrMap (T : Kfin k) (α : D.A) : K.space T (D.src α) →ₗ[k] K.space T (D.tgt α) :=
  LinearMap.prod
    (LinearMap.coprod (TensorProduct.map (K.Q₀.map α).hom LinearMap.id)
      (TensorProduct.map (K.z₁ α) T.obj.a.hom + TensorProduct.map (K.z₂ α) T.obj.b.hom))
    (TensorProduct.map (K.P.map α).hom LinearMap.id ∘ₗ LinearMap.snd k _ _)

/-- The representation `L(T)`. -/
def obj (T : Kfin k) : Rep k D where
  obj i := ModuleCat.of k (K.space T i)
  map α := ModuleCat.ofHom (K.arrMap T α)

/-- The vertex map of `L(g, h)`. -/
def vmap {T U : Kfin k} (f : T ⟶ U) (i : D.V) : K.space T i →ₗ[k] K.space U i :=
  LinearMap.prodMap (TensorProduct.map LinearMap.id (f.hom.app one).hom)
    (TensorProduct.map LinearMap.id (f.hom.app zero).hom)

lemma vmap_comm {T U : Kfin k} (f : T ⟶ U) (α : D.A) :
    K.vmap f (D.tgt α) ∘ₗ K.arrMap T α = K.arrMap U α ∘ₗ K.vmap f (D.src α) := by
  have ha : (f.hom.app one).hom ∘ₗ T.obj.a.hom = U.obj.a.hom ∘ₗ (f.hom.app zero).hom :=
    congrArg ModuleCat.Hom.hom (Kron.a_comp f.hom)
  have hb : (f.hom.app one).hom ∘ₗ T.obj.b.hom = U.obj.b.hom ∘ₗ (f.hom.app zero).hom :=
    congrArg ModuleCat.Hom.hom (Kron.b_comp f.hom)
  apply LinearMap.prod_ext
  · apply TensorProduct.ext'
    intro q w
    simp [vmap, arrMap]
  · apply TensorProduct.ext'
    intro p v
    have e1 := congrArg (fun φ ↦ φ v) ha
    have e2 := congrArg (fun φ ↦ φ v) hb
    simp only [LinearMap.comp_apply] at e1 e2
    simp [vmap, arrMap, e1, e2]

/-- The functor `L`. -/
def functor : Kfin k ⥤ Rep k D where
  obj := K.obj
  map f := ⟨fun i ↦ ModuleCat.ofHom (K.vmap f i), fun α ↦ by
    ext1
    exact K.vmap_comm f α⟩
  map_id T := by
    refine Rep.hom_ext fun i ↦ ?_
    ext1
    apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;> intro x y <;> simp [vmap, obj]
  map_comp f g := by
    apply Rep.hom_ext
    intro i
    ext1
    change K.vmap (f ≫ g) i = K.vmap g i ∘ₗ K.vmap f i
    simp only [vmap]
    rw [LinearMap.prodMap_comp, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
      LinearMap.id_comp]
    rfl

lemma subsingleton_tensor_left {M N : Type u} [AddCommGroup M] [Module k M] [AddCommGroup N]
    [Module k N] [Subsingleton M] : Subsingleton (M ⊗[k] N) :=
  ⟨fun x y ↦ by
    have h : ∀ t : M ⊗[k] N, t = 0 := fun t ↦ by
      induction t using TensorProduct.inductionOn with
      | tmul m n => rw [Subsingleton.elim m 0, TensorProduct.zero_tmul]
      | add a b ha hb => rw [ha, hb, add_zero]
    rw [h x, h y]⟩

/-- The off-diagonal blocks of a map `L(T)(i) → L(U)(i)` vanish. -/
lemma snd_comp_inl {T U : Kfin k} (i : D.V) (φ : K.space T i →ₗ[k] K.space U i) :
    LinearMap.snd k _ _ ∘ₗ φ ∘ₗ LinearMap.inl k _ _ = 0 := by
  have := K.finP i
  have := K.finQ i
  refine LinearMap.ext fun x ↦ ?_
  rcases K.disjoint i with hP | hQ
  · have : Subsingleton (K.P.obj i ⊗[k] U.obj.V) := subsingleton_tensor_left
    exact Subsingleton.elim _ _
  · have : Subsingleton (K.Q₀.obj i ⊗[k] T.obj.W) := subsingleton_tensor_left
    rw [Subsingleton.elim x 0]
    simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.snd_apply, LinearMap.zero_apply]
    rw [Prod.mk_zero_zero, map_zero]; rfl

lemma fst_comp_inr {T U : Kfin k} (i : D.V) (φ : K.space T i →ₗ[k] K.space U i) :
    LinearMap.fst k _ _ ∘ₗ φ ∘ₗ LinearMap.inr k _ _ = 0 := by
  refine LinearMap.ext fun x ↦ ?_
  rcases K.disjoint i with hP | hQ
  · have : Subsingleton (K.P.obj i ⊗[k] T.obj.V) := subsingleton_tensor_left
    rw [Subsingleton.elim x 0]
    simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.fst_apply, LinearMap.zero_apply]
    rw [Prod.mk_zero_zero, map_zero]; rfl
  · have : Subsingleton (K.Q₀.obj i ⊗[k] U.obj.W) := subsingleton_tensor_left
    exact Subsingleton.elim _ _

lemma snd_apply {T U : Kfin k} (i : D.V) (φ : K.space T i →ₗ[k] K.space U i) (a b) :
    (φ (a, b)).2 = (φ (0, b)).2 := by
  have h := congrArg (fun F ↦ F a) (K.snd_comp_inl i φ)
  simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.snd_apply,
    LinearMap.zero_apply] at h
  rw [show (a, b) = (a, 0) + (0, b) by simp, map_add, Prod.snd_add, h, zero_add]

lemma fst_apply {T U : Kfin k} (i : D.V) (φ : K.space T i →ₗ[k] K.space U i) (a b) :
    (φ (a, b)).1 = (φ (a, 0)).1 := by
  have h := congrArg (fun F ↦ F b) (K.fst_comp_inr i φ)
  simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.fst_apply,
    LinearMap.zero_apply] at h
  rw [show (a, b) = (a, 0) + (0, b) by simp, map_add, Prod.fst_add, h, add_zero]

lemma eq_zero_of_tmul_right {M N : Type u} [AddCommGroup M] [Module k M] [AddCommGroup N]
    [Module k N] {q : M} {u : N} (hu : u ≠ 0) (h : q ⊗ₜ[k] u = 0) : q = 0 := by
  obtain ⟨lam, hl⟩ := Module.Projective.exists_dual_eq_one k hu
  have := congrArg (fun t ↦ (TensorProduct.rid k M) (TensorProduct.map LinearMap.id lam t)) h
  simpa [hl] using this

lemma eq_zero_of_tmul {M N : Type u} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    {q : M} (hq : q ≠ 0) {u : N} (h : q ⊗ₜ[k] u = 0) : u = 0 := by
  obtain ⟨lam, hl⟩ := Module.Projective.exists_dual_eq_one k hq
  have := congrArg (fun t ↦ (TensorProduct.lid k N) (TensorProduct.map lam LinearMap.id t)) h
  simpa [hl] using this

lemma eq_prodMap {T U : Kfin k} (i : D.V) (φ : K.space T i →ₗ[k] K.space U i) :
    φ = LinearMap.prodMap (LinearMap.fst k _ _ ∘ₗ φ ∘ₗ LinearMap.inl k _ _)
      (LinearMap.snd k _ _ ∘ₗ φ ∘ₗ LinearMap.inr k _ _) := by
  refine LinearMap.ext fun ⟨a, b⟩ ↦ Prod.ext ?_ ?_
  · simp only [LinearMap.prodMap_apply, LinearMap.comp_apply, LinearMap.inl_apply,
      LinearMap.fst_apply]
    exact K.fst_apply i φ a b
  · simp only [LinearMap.prodMap_apply, LinearMap.comp_apply, LinearMap.inr_apply,
      LinearMap.snd_apply]
    exact K.snd_apply i φ a b

/-- Two independent tuples: `z₁ ⊗ u₁ + z₂ ⊗ u₂ = 0` forces `u₁ = u₂ = 0`. -/
lemma eq_zero_of_indep {W' : Type u} [AddCommGroup W'] [Module k W'] (u₁ u₂ : W')
    (h : ∀ (α : D.A) (p : K.P.obj (D.src α)), K.z₁ α p ⊗ₜ[k] u₁ + K.z₂ α p ⊗ₜ[k] u₂ = 0) :
    u₁ = 0 ∧ u₂ = 0 := by
  have hμ : ∀ μ : Module.Dual k W', μ u₁ = 0 ∧ μ u₂ = 0 := by
    intro μ
    refine K.indep (μ u₁) (μ u₂) fun α ↦ LinearMap.ext fun p ↦ ?_
    have := congrArg (fun t ↦ (TensorProduct.rid k _) (TensorProduct.map LinearMap.id μ t)) (h α p)
    simpa [add_comm] using this
  exact ⟨(Module.forall_dual_apply_eq_zero_iff k u₁).1 fun μ ↦ (hμ μ).1,
    (Module.forall_dual_apply_eq_zero_iff k u₂).1 fun μ ↦ (hμ μ).2⟩

lemma arrMap_fst (T : Kfin k) (α : D.A) (x : K.space T (D.src α)) : (K.arrMap T α x).1 =
    TensorProduct.map (K.Q₀.map α).hom LinearMap.id x.1 +
      (TensorProduct.map (K.z₁ α) T.obj.a.hom + TensorProduct.map (K.z₂ α) T.obj.b.hom) x.2 := by
  simp [arrMap]

lemma arrMap_snd (T : Kfin k) (α : D.A) (x : K.space T (D.src α)) : (K.arrMap T α x).2 =
    TensorProduct.map (K.P.map α).hom LinearMap.id x.2 := by
  simp [arrMap]

lemma snd_zero {T U : Kfin k} (i : D.V) (φ : K.space T i →ₗ[k] K.space U i) (a) :
    (φ (a, 0)).2 = 0 := by
  rw [K.snd_apply i φ a 0, Prod.mk_zero_zero, map_zero]; rfl

lemma fst_zero {T U : Kfin k} (i : D.V) (φ : K.space T i →ₗ[k] K.space U i) (b) :
    (φ (0, b)).1 = 0 := by
  rw [K.fst_apply i φ 0 b, Prod.mk_zero_zero, map_zero]; rfl

instance : K.functor.Full where
  map_surjective {T U} φ := by
    have : FiniteDimensional k U.obj.W := U.2.2
    have : FiniteDimensional k U.obj.V := U.2.1
    let φi : ∀ i, K.space T i →ₗ[k] K.space U i := fun i ↦ (φ.app i).hom
    let φQ : ∀ i, K.Q₀.obj i ⊗[k] T.obj.W →ₗ[k] K.Q₀.obj i ⊗[k] U.obj.W := fun i ↦
      LinearMap.fst k _ _ ∘ₗ φi i ∘ₗ LinearMap.inl k _ _
    let φP : ∀ i, K.P.obj i ⊗[k] T.obj.V →ₗ[k] K.P.obj i ⊗[k] U.obj.V := fun i ↦
      LinearMap.snd k _ _ ∘ₗ φi i ∘ₗ LinearMap.inr k _ _
    have hdec : ∀ i, φi i = LinearMap.prodMap (φQ i) (φP i) := fun i ↦
      K.eq_prodMap i (φi i)
    have hcomm : ∀ (α : D.A) (x : K.space T (D.src α)),
        φi (D.tgt α) (K.arrMap T α x) = K.arrMap U α (φi (D.src α) x) :=
      fun α x ↦ congrArg (fun F ↦ F.hom x) (φ.comm α)
    obtain ⟨h, hh⟩ := brick_tensor K.Q₀ K.brickQ φQ fun α ↦ LinearMap.ext fun x ↦ by
      change (φi (D.tgt α) (TensorProduct.map (K.Q₀.map α).hom LinearMap.id x, 0)).1 =
        TensorProduct.map (K.Q₀.map α).hom LinearMap.id ((φi (D.src α) (x, 0)).1)
      have hx : K.arrMap T α (x, 0) = (TensorProduct.map (K.Q₀.map α).hom LinearMap.id x, 0) :=
        Prod.ext (by rw [arrMap_fst]; simp) (by rw [arrMap_snd]; simp)
      rw [← hx, hcomm, arrMap_fst, K.snd_zero, map_zero, add_zero]
    obtain ⟨g, hg⟩ := brick_tensor K.P K.brickP φP fun α ↦ LinearMap.ext fun y ↦ by
      change (φi (D.tgt α) (0, TensorProduct.map (K.P.map α).hom LinearMap.id y)).2 =
        TensorProduct.map (K.P.map α).hom LinearMap.id ((φi (D.src α) (0, y)).2)
      have e := congrArg Prod.snd (hcomm α (0, y))
      rw [arrMap_snd] at e
      rw [← e, show K.arrMap T α (0, y) = ((K.arrMap T α (0, y)).1,
        TensorProduct.map (K.P.map α).hom LinearMap.id y) from Prod.ext rfl (by rw [arrMap_snd])]
      exact (K.snd_apply (D.tgt α) (φi (D.tgt α)) _ _).symm
    -- the extension tuples force the Kronecker equations
    have hab : ∀ v, h (T.obj.a.hom v) = U.obj.a.hom (g v) ∧
        h (T.obj.b.hom v) = U.obj.b.hom (g v) := by
      intro v
      refine (fun H ↦ ⟨sub_eq_zero.1 H.1, sub_eq_zero.1 H.2⟩) (K.eq_zero_of_indep _ _ fun α p ↦ ?_)
      have e := congrArg Prod.fst (hcomm α (0, p ⊗ₜ v))
      rw [arrMap_fst, K.fst_zero, map_zero, zero_add] at e
      rw [show K.arrMap T α (0, p ⊗ₜ v) = ((K.arrMap T α (0, p ⊗ₜ v)).1,
        (K.arrMap T α (0, p ⊗ₜ v)).2) from rfl, K.fst_apply] at e
      have e1 : (φi (D.tgt α) ((K.arrMap T α (0, p ⊗ₜ v)).1, 0)).1 =
          φQ (D.tgt α) ((K.arrMap T α (0, p ⊗ₜ v)).1) := rfl
      have e2 : (φi (D.src α) (0, p ⊗ₜ v)).2 = φP (D.src α) (p ⊗ₜ v) := rfl
      rw [e1, e2, hh, hg, arrMap_fst] at e
      simp only [map_zero, zero_add, LinearMap.add_apply, TensorProduct.map_tmul,
        LinearMap.id_apply, map_add] at e
      rw [TensorProduct.tmul_sub, TensorProduct.tmul_sub, sub_add_sub_comm, e, sub_self]
    refine ⟨ObjectProperty.homMk (Kron.homMk (ModuleCat.ofHom g) (ModuleCat.ofHom h)
      (ModuleCat.hom_ext (LinearMap.ext fun v ↦ (hab v).1))
      (ModuleCat.hom_ext (LinearMap.ext fun v ↦ (hab v).2))), ?_⟩
    refine Rep.hom_ext fun i ↦ ?_
    ext1
    change K.vmap _ i = φi i
    rw [hdec, hh, hg]
    rfl

instance : K.functor.Faithful where
  map_injective {T U f f'} hff := by
    obtain ⟨iQ, hiQ⟩ := K.nonzeroQ
    obtain ⟨iP, hiP⟩ := K.nonzeroP
    obtain ⟨q, hq⟩ := exists_ne (0 : K.Q₀.obj iQ)
    obtain ⟨p, hp⟩ := exists_ne (0 : K.P.obj iP)
    have h1 := congrArg (fun F ↦ (F.app iQ).hom) hff
    have h2 := congrArg (fun F ↦ (F.app iP).hom) hff
    ext1
    refine Kron.hom_ext ?_ ?_
    · ext v
      have := congrArg (fun F ↦ (F (0, p ⊗ₜ v)).2) h2
      change p ⊗ₜ[k] (f.hom.app zero).hom v = p ⊗ₜ[k] (f'.hom.app zero).hom v at this
      rw [← sub_eq_zero, ← TensorProduct.tmul_sub] at this
      exact sub_eq_zero.1 (eq_zero_of_tmul hp this)
    · ext w
      have := congrArg (fun F ↦ (F (q ⊗ₜ w, 0)).1) h1
      change q ⊗ₜ[k] (f.hom.app one).hom w = q ⊗ₜ[k] (f'.hom.app one).hom w at this
      rw [← sub_eq_zero, ← TensorProduct.tmul_sub] at this
      exact sub_eq_zero.1 (eq_zero_of_tmul hq this)

/-- `L` is fully faithful. -/
def fullyFaithful : K.functor.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _

instance : K.functor.Additive where
  map_add {T U f g} := by
    refine Rep.hom_ext fun i ↦ ?_
    ext1
    change K.vmap (f + g) i = K.vmap f i + K.vmap g i
    simp only [vmap]
    rw [show (f + g).hom.app one = f.hom.app one + g.hom.app one from rfl,
      show (f + g).hom.app zero = f.hom.app zero + g.hom.app zero from rfl,
      ModuleCat.hom_add, ModuleCat.hom_add, TensorProduct.map_add_right,
      TensorProduct.map_add_right]
    apply LinearMap.prod_ext <;> rfl

lemma map_smul' {T U : Kfin k} (c : k) (f : T ⟶ U) (i : D.V) :
    (K.functor.map (c • f)).app i = c • (K.functor.map f).app i := by
  ext1
  change K.vmap (c • f) i = c • K.vmap f i
  simp only [vmap]
  rw [show (c • f).hom.app one = c • f.hom.app one from rfl,
    show (c • f).hom.app zero = c • f.hom.app zero from rfl,
    ModuleCat.hom_smul, ModuleCat.hom_smul, TensorProduct.map_smul_right,
    TensorProduct.map_smul_right]
  apply LinearMap.prod_ext <;> rfl

lemma exact : ExactOnKfin K.functor := by
  intro X Y Z f g h i
  obtain ⟨h0i, h0s, h0e⟩ := h zero
  obtain ⟨h1i, h1s, h1e⟩ := h one
  have e0 : Function.Exact (f.hom.app zero).hom (g.hom.app zero).hom := by
    rw [LinearMap.exact_iff]; exact h0e.symm
  have e1 : Function.Exact (f.hom.app one).hom (g.hom.app one).hom := by
    rw [LinearMap.exact_iff]; exact h1e.symm
  have iQ := Module.Flat.lTensor_preserves_injective_linearMap (M := K.Q₀.obj i) _ h1i
  have iP := Module.Flat.lTensor_preserves_injective_linearMap (M := K.P.obj i) _ h0i
  have sQ := LinearMap.lTensor_surjective (K.Q₀.obj i) h1s
  have sP := LinearMap.lTensor_surjective (K.P.obj i) h0s
  have xQ := Module.Flat.lTensor_exact (K.Q₀.obj i) e1
  have xP := Module.Flat.lTensor_exact (K.P.obj i) e0
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    exact Prod.ext (iQ (congrArg Prod.fst hab)) (iP (congrArg Prod.snd hab))
  · intro y
    obtain ⟨a, ha⟩ := sQ y.1
    obtain ⟨b, hb⟩ := sP y.2
    exact ⟨(a, b), Prod.ext ha hb⟩
  · ext ⟨y₁, y₂⟩
    change (∃ x : K.space X i, (LinearMap.lTensor _ (f.hom.app one).hom x.1,
      LinearMap.lTensor _ (f.hom.app zero).hom x.2) = (y₁, y₂)) ↔ (LinearMap.lTensor _ (g.hom.app one).hom y₁, LinearMap.lTensor _ (g.hom.app zero).hom y₂) = 0
    constructor
    · rintro ⟨⟨x₁, x₂⟩, hx⟩
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 hx
      exact Prod.ext ((xQ _).2 ⟨x₁, rfl⟩) ((xP _).2 ⟨x₂, rfl⟩)
    · intro hy
      obtain ⟨x₁, hx₁⟩ := (xQ y₁).1 (congrArg Prod.fst hy)
      obtain ⟨x₂, hx₂⟩ := (xP y₂).1 (congrArg Prod.snd hy)
      exact ⟨(x₁, x₂), Prod.ext hx₁ hx₂⟩

lemma fin (T : Kfin k) (i : D.V) : Module.Finite k ((K.functor.obj T).obj i) := by
  have := K.finP i
  have := K.finQ i
  have : FiniteDimensional k T.obj.V := T.2.1
  have : FiniteDimensional k T.obj.W := T.2.2
  change Module.Finite k (K.space T i)
  infer_instance

lemma nontrivial_splus (i : D.V) (h : Nontrivial (K.P.obj i)) :
    Nontrivial ((K.functor.obj (SplusK k)).obj i) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : K.P.obj i)
  refine ⟨⟨((0 : K.Q₀.obj i ⊗[k] PUnit), x ⊗ₜ[k] (1 : k)), 0, fun h' ↦ hx ?_⟩⟩
  exact eq_zero_of_tmul_right (show (1 : k) ≠ 0 from one_ne_zero) (congrArg Prod.snd h')

lemma nontrivial_sminus (i : D.V) (h : Nontrivial (K.Q₀.obj i)) :
    Nontrivial ((K.functor.obj (SminusK k)).obj i) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : K.Q₀.obj i)
  refine ⟨⟨(x ⊗ₜ[k] (1 : k), (0 : K.P.obj i ⊗[k] PUnit)), 0, fun h' ↦ hx ?_⟩⟩
  exact eq_zero_of_tmul_right (show (1 : k) ≠ 0 from one_ne_zero) (congrArg Prod.fst h')

end KroneckerPair

variable {A : Type u} [Ring A] [Algebra k A]

variable (k A) in
/-- Covering data: the
finite part of a Galois covering with torsion-free group, a Kronecker pair on
it whose supports cover `D`, and a presentation `kQ → A` whose kernel acts by
zero on the push-downs `p_*L(T)`, `T ∈ D_fin`. -/
structure PairCoveringData where
  /-- The full subquiver of the covering on the support. -/
  D : FinQuiver
  /-- The quiver of the presentation. -/
  Q : FinQuiver
  /-- The restriction of the covering map. -/
  p : FinQuiver.Hom D Q
  locInj : p.LocallyInjective
  /-- The group action of the covering. -/
  C : CoverData p
  /-- The Kronecker pair. -/
  K : KroneckerPair k D
  supp : ∀ i, Nontrivial (K.P.obj i) ∨ Nontrivial (K.Q₀.obj i)
  /-- The presentation. -/
  π : Q.PathAlgebra k →ₐ[k] A
  surj : Function.Surjective π
  kills : ∀ (T : Dfin k) (z : Q.PathAlgebra k), π z = 0 →
    (K.functor.obj ((DfinToKfin k).obj T)).pdAct p z = 0

/-- Covering data from a Kronecker pair. -/
def PairCoveringData.toCoveringData (W : PairCoveringData k A) : CoveringData k A where
  D := W.D
  Q := W.Q
  p := W.p
  locInj := W.locInj
  C := W.C
  L := W.K.functor
  hL := W.K.fullyFaithful
  map_smul := W.K.map_smul'
  exact := W.K.exact
  fin := W.K.fin
  supp i := (W.supp i).imp (W.K.nontrivial_splus i) (W.K.nontrivial_sminus i)
  nonzero := ⟨let ⟨i, hi⟩ := W.K.nonzeroP; ⟨i, W.K.nontrivial_splus i hi⟩,
    let ⟨i, hi⟩ := W.K.nonzeroQ; ⟨i, W.K.nontrivial_sminus i hi⟩⟩
  π := W.π
  surj := W.surj
  kills := W.kills

end Covering

end LargeIndecomposable
