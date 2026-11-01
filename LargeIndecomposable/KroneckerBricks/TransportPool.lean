module

public import LargeIndecomposable.KroneckerBricks.TransportOrth

/-!
# Large orthogonal families of Kronecker bricks

For a well-order `α` of regular uncountable type with `|k| ≤ |α|`, the
transports of the rigid map system of `α` with an extra one-point marker form
`|α|` pairwise orthogonal bricks of dimension `|α|`. With the anchor
`T_{Λ_{Y₀}}` and the non-split classes through the copy of `T_{Λ₀}` they form
an anchored family (`Bricks.transportPool`). This plays the role of the rigid
`κ`-families of Göbel–May (Proposition 4.2) in the singular case.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair TensorProduct
open _root_.Cardinal

universe u

variable {k : Type u} [Field k]

namespace Bricks

/-- Two-sided Hom-orthogonality. -/
def Orth (Z X : Kron k) : Prop := (∀ f : Z ⟶ X, f = 0) ∧ ∀ f : X ⟶ Z, f = 0

lemma orth_T {Λ Λ' : Set k} (h1 : (Λ \ Λ').Infinite) (h2 : (Λ' \ Λ).Infinite) :
    Orth (T Λ) (T Λ') :=
  ⟨hom_eq_zero h1, hom_eq_zero h2⟩

lemma orth_extFamily {Z : Kron k} {ι : Type u} [DecidableEq ι] {C : Kron k} {B : ι → Kron k}
    {α β : ∀ i, (B i).V →ₗ[k] C.W} (hC : Orth Z C) (hB : ∀ i, Orth Z (B i)) :
    Orth Z (extFamily C B α β) :=
  ⟨hom_to_extFamily_eq_zero hC.1 fun i ↦ (hB i).1, hom_extFamily_eq_zero hC.2 fun i ↦ (hB i).2⟩

lemma Anchored.orth_transport {J : Type u} [DecidableEq J] (σ : Anchored k J) {G : Type u}
    [AddCommGroup G] [Module k G] (Gs : J → Submodule k G) {Z : Kron k} (hC : Orth Z σ.C)
    (hB : ∀ j, Orth Z (σ.B j)) : Orth Z (σ.transport Gs) :=
  ⟨σ.hom_to_transport_eq_zero Gs (orth_extFamily (α := fun i : (Set.univ : Set J) ↦ σ.α i)
      (β := fun i : (Set.univ : Set J) ↦ σ.β i) hC fun i ↦ hB i).1,
    σ.hom_transport_to_eq_zero Gs fun j ↦ (orth_extFamily
      (α := fun i : ({j} : Set J) ↦ σ.α i) (β := fun i : ({j} : Set J) ↦ σ.β i)
      hC fun i ↦ hB i).2⟩

section Marks

variable {X : Type u} (M : Rigid.MapSystem X)

variable (k) in
/-- The map-system structure with a one-point marker `(e_a, e_a)` at index `0`. -/
def markN (a : X) : ℕ → Submodule k ((X →₀ k) × (X →₀ k))
  | 0 => Submodule.span k {(Finsupp.single a 1, Finsupp.single a 1)}
  | n + 1 => Rigid.subN k M n

variable (k) in
/-- The marked structure, indexed by `Nu`. -/
def marks (a : X) : Nu → Submodule k ((X →₀ k) × (X →₀ k)) := fun n ↦ markN k M a n.down

lemma marks_one (a : X) : marks k M a ⟨1⟩ = ⊤ := rfl

lemma isRigidR_marks [Infinite k] (h : Rigid.IsRigidSys k M) (a : X) : IsRigidR (marks k M a) :=
  fun ψ hψ ↦ Rigid.isRigidR_of_isRigidSys h ψ fun n x hx ↦ hψ ⟨n.down + 1⟩ x hx

lemma marks_orth [Infinite k] (h : Rigid.IsRigidSys k M) {a b : X} (hab : a ≠ b)
    (Ψ : (X →₀ k) × (X →₀ k) →ₗ[k] (X →₀ k) × (X →₀ k))
    (hΨ : ∀ j, ∀ g ∈ marks k M a j, Ψ g ∈ marks k M b j) : Ψ = 0 := by
  obtain ⟨c, rfl⟩ := Rigid.isRigidR_of_isRigidSys h Ψ fun n x hx ↦ hΨ ⟨n.down + 1⟩ x hx
  have hm := hΨ ⟨0⟩ _ (Submodule.mem_span_singleton_self _)
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hm
  have := congrArg (fun p : (X →₀ k) × (X →₀ k) ↦ p.1 a) hd
  simp only [Prod.smul_fst, Finsupp.smul_apply, LinearMap.smul_apply, LinearMap.id_apply,
    smul_eq_mul, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hab, mul_zero, mul_one] at this
  rw [← this, zero_smul]

end Marks

variable [Infinite k]

/-- Countably many distinct subsets of `k`. -/
def nE (n : ℕ) : Set k := Infinite.natEmbedding (Set k) n

lemma nE_ne {m n : ℕ} (h : m ≠ n) : nE (k := k) m ≠ nE n :=
  fun e ↦ h ((Infinite.natEmbedding (Set k)).injective e)

variable (k) in
/-- The `ω`-seed of the pool, on the sets `nE (n + 2)`. -/
def poolSeed : Anchored k Nu :=
  lamAnchored ⟨fun n ↦ nE (n.down + 2), fun _ _ h ↦ ULift.ext (by
    have := (Infinite.natEmbedding (Set k)).injective h
    omega)⟩

lemma orth_poolSeed {m : ℕ} (hm : m < 2) :
    Orth (T (LamX (nE (k := k) m))) (poolSeed k).C ∧
      ∀ j, Orth (T (LamX (nE (k := k) m))) ((poolSeed k).B j) :=
  ⟨orth_T (diff_lam0_infinite _) (lam0_diff_infinite _), fun j ↦
    orth_T (diff_infinite (nE_ne (by omega))) (diff_infinite (nE_ne (by omega)))⟩

lemma lamX_nonempty (Y : Set k) : (LamX Y).Nonempty :=
  (diff_lam0_infinite Y).nonempty.mono Set.sdiff_subset

lemma lamAnchored_SV_le {J : Type u} [DecidableEq J] (e : J ↪ Set k) (hJ : #J ≤ #k) :
    Module.rank k ((lamAnchored e).SV Set.univ) ≤ #k :=
  (lamAnchored e).rank_SV_le (Cardinal.infinite_iff.1 inferInstance) hJ (rank_T_V_le _)
    fun _ ↦ rank_T_V_le _

lemma lamAnchored_SW_le {J : Type u} [DecidableEq J] (e : J ↪ Set k) (hJ : #J ≤ #k) :
    Module.rank k ((lamAnchored e).SW Set.univ) ≤ #k :=
  (lamAnchored e).rank_SW_le (Cardinal.infinite_iff.1 inferInstance) hJ (rank_T_W_le _)
    fun _ ↦ rank_T_W_le _

lemma rank_V_le_dim (X : Kron k) : Module.rank k X.V ≤ X.dim := le_self_add

lemma rank_W_le_dim (X : Kron k) : Module.rank k X.W ≤ X.dim := le_add_self

section Pool

variable {α : Type u} [LinearOrder α] [WellFoundedLT α] [Nonempty α] [NoMaxOrder α]
  [IsRegularCardinalOrder α] (hα : ℵ₀ < Order.cof α)

/-- The constituents of the pool: marked transports. -/
def poolB (a : Rigid.Dec α) : Kron k :=
  (poolSeed k).transport (marks k (Rigid.regSys hα) a)

lemma poolG_ne (a : Rigid.Dec α) :
    ((Finsupp.single a 1, 0) : (Rigid.Dec α →₀ k) × (Rigid.Dec α →₀ k)) ≠ 0 :=
  fun h ↦ Finsupp.single_ne_zero.2 one_ne_zero (congrArg Prod.fst h)

/-- The point of `Λ₀ \ Λ_{Y₀}` used for the classes. -/
def poolPt : k := (lam0_diff_infinite (nE (k := k) 0)).nonempty.some

lemma pool_cls (a : Rigid.Dec α) :
    ∃ αc βc : (poolB (k := k) hα a).V →ₗ[k] (T (LamX (nE (k := k) 0))).W,
      ¬Splits (T (LamX (nE 0))) (poolB hα a) αc βc :=
  (poolSeed k).exists_not_splits_transport (marks k (Rigid.regSys hα) a)
    (Z := T (LamX (nE 0))) (α0 := 0) (β0 := betaExt Lam0 (LamX (nE 0)) poolPt)
    (not_splits (lam0_diff_infinite _) (lam0_diff_infinite (nE (k := k) 0)).nonempty.some_mem)
    (j0 := ⟨1⟩) (by rw [marks_one]; trivial) (poolG_ne a)

/-- The pool: `|α|` pairwise orthogonal transports over the anchor `T_{Λ_{Y₀}}`. -/
def transportPool : Anchored k (Rigid.Dec α) where
  C := T (LamX (nE 0))
  B := poolB hα
  α a := Classical.choose (pool_cls hα a)
  β a := Classical.choose (Classical.choose_spec (pool_cls hα a))
  hC := isBrick _ (lamX_nonempty _)
  hB a := by
    have : Nontrivial ((Rigid.Dec α →₀ k) × (Rigid.Dec α →₀ k)) :=
      nontrivial_of_ne _ 0 (poolG_ne a)
    exact (poolSeed k).isBrick_transport _ (j0 := ⟨1⟩) (marks_one _ a)
      (isRigidR_marks _ (Rigid.isRigidSys_regSys k hα) a)
  hCB a := ((poolSeed k).orth_transport _ (orth_poolSeed (by omega)).1
    (orth_poolSeed (by omega)).2).1
  hBC a := ((poolSeed k).orth_transport _ (orth_poolSeed (by omega)).1
    (orth_poolSeed (by omega)).2).2
  hBB a b hab := (poolSeed k).transport_hom_eq_zero _ _ (j0 := ⟨1⟩) (marks_one _ a)
    (marks_orth _ (Rigid.isRigidSys_regSys k hα) hab)
  hns a := Classical.choose_spec (Classical.choose_spec (pool_cls hα a))
  c0 := Finsupp.single ⟨_, (lamX_nonempty (nE (k := k) 0)).some_mem⟩ 1
  hc0 := Finsupp.single_ne_zero.2 one_ne_zero
  y a := ⟨(Finsupp.single a 1, 0) ⊗ₜ (poolSeed k).iV ⟨1⟩ ((poolSeed k).c0, 0),
    (poolSeed k).genV_mem _ (n := ⟨1⟩) (by rw [marks_one]; trivial) _⟩
  hy a h := by
    have := congrArg Subtype.val h
    change (Finsupp.single a 1, 0) ⊗ₜ (poolSeed k).iV ⟨1⟩ ((poolSeed k).c0, 0) = 0 at this
    rw [Anchored.iV_anchor] at this
    exact poolG_ne a (eq_zero_of_tmul_right' (poolSeed k).anchor_ne_zero this)

lemma dim_poolB (hk : #k ≤ #α) (a : Rigid.Dec α) : (poolB (k := k) hα a).dim = #α := by
  haveI := Rigid.infinite_of hα
  have hα0 : ℵ₀ ≤ #α := Cardinal.infinite_iff.1 inferInstance
  have hX : #(Rigid.Dec α) = #α :=
    le_antisymm Rigid.Dec.mk_le (mk_le_of_injective (Rigid.Dec.sing_injective (α := α)))
  have hrank : Module.rank k ((Rigid.Dec α →₀ k) × (Rigid.Dec α →₀ k)) = #α := by
    rw [rank_prod', rank_finsupp_self', hX, add_eq_self hα0]
  have hNu : #Nu ≤ #k := by simp
  rw [poolB, (poolSeed k).dim_transport _ (j0 := ⟨1⟩) (marks_one _ a) (hrank ▸ hα0)
    (hrank ▸ (lamAnchored_SV_le _ hNu).trans hk) (hrank ▸ (lamAnchored_SW_le _ hNu).trans hk),
    hrank]

end Pool

end Bricks

end LargeIndecomposable
