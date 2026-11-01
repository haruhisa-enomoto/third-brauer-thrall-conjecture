module

public import LargeIndecomposable.KroneckerBricks.ExtensionOrth
public import LargeIndecomposable.KroneckerBricks.Coefficient

/-!
# Transport of rigid structures to Kronecker modules

An *anchored family* over an index type `J` is an anchor brick `C`, pairwise
orthogonal bricks `B j` orthogonal to `C`, and non-split classes. Gluing gives
the fully rigid family `F_S` (`S ⊆ J`, `KroneckerBricks/ExtensionOrth.lean`). For a
vector space `G` with subspaces `G_j` (`j ∈ J`), the Kronecker module
`H = ∑_j G_j ⊗ F_{{j}} ⊆ G ⊗ F_J` is the *transport*. Morphisms between
transports are `Ψ ⊗ id` with `Ψ(G_j) ⊆ G'_j` (`Bricks.Anchored.hom_transport`,
when some `G_{j₀} = G`); so the transport of a rigid structure is a brick
(`Bricks.Anchored.isBrick_transport`). This is Göbel–Simson, Theorem 3.3,
Step 3, for the algebra `k`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair TensorProduct

universe u

variable {k : Type u} [Field k]

namespace Bricks

/-- The countable index type. -/
abbrev Nu : Type u := ULift.{u} ℕ

/-- A rigid structure: only scalars preserve every `G_j`. -/
def IsRigidR {J G : Type u} [AddCommGroup G] [Module k G] (Gs : J → Submodule k G) : Prop :=
  ∀ ψ : G →ₗ[k] G, (∀ n, ∀ x ∈ Gs n, ψ x ∈ Gs n) → ∃ c : k, ψ = c • LinearMap.id

variable (k) in
/-- An anchored family of bricks with non-split classes and chosen nonzero vectors. -/
structure Anchored (J : Type u) where
  /-- The anchor. -/
  C : Kron k
  /-- The constituents. -/
  B : J → Kron k
  /-- First gluing classes. -/
  α : ∀ j, (B j).V →ₗ[k] C.W
  /-- Second gluing classes. -/
  β : ∀ j, (B j).V →ₗ[k] C.W
  hC : IsBrickKron C
  hB : ∀ j, IsBrickKron (B j)
  hCB : ∀ j (f : C ⟶ B j), f = 0
  hBC : ∀ j (f : B j ⟶ C), f = 0
  hBB : ∀ i j, i ≠ j → ∀ f : B i ⟶ B j, f = 0
  hns : ∀ j, ¬Splits C (B j) (α j) (β j)
  /-- A nonzero vector of the anchor. -/
  c0 : C.V
  hc0 : c0 ≠ 0
  /-- Nonzero vectors of the constituents. -/
  y : ∀ j, (B j).V
  hy : ∀ j, y j ≠ 0

namespace Anchored

variable {J : Type u} [DecidableEq J] (σ : Anchored k J)

/-- The glued module `F_S`. -/
abbrev F (S : Set J) : Kron k := subExt σ.C σ.B σ.α σ.β S

/-- The space `V` of `F_S`. -/
abbrev SV (S : Set J) : Type u := σ.C.V × SumV (fun i : S ↦ σ.B i)

/-- The space `W` of `F_S`. -/
abbrev SW (S : Set J) : Type u := σ.C.W × SumW (fun i : S ↦ σ.B i)

/-- The inclusion `F_{{n}} → F_J` on `V`. -/
def iV (n : J) : σ.SV {n} →ₗ[k] σ.SV Set.univ :=
  inclV σ.C σ.B (Set.subset_univ {n})

/-- The inclusion `F_{{n}} → F_J` on `W`. -/
def iW (n : J) : σ.SW {n} →ₗ[k] σ.SW Set.univ :=
  inclW σ.C σ.B (Set.subset_univ {n})

/-- The arrow `a` of `F_S`. -/
def aS (S : Set J) : σ.SV S →ₗ[k] σ.SW S :=
  famMap σ.C (fun i : S ↦ σ.B i) σ.C.a.hom (fun i ↦ (σ.B i).a.hom) (fun i ↦ σ.α i)

/-- The arrow `b` of `F_S`. -/
def bS (S : Set J) : σ.SV S →ₗ[k] σ.SW S :=
  famMap σ.C (fun i : S ↦ σ.B i) σ.C.b.hom (fun i ↦ (σ.B i).b.hom) (fun i ↦ σ.β i)

lemma iW_aS (n : J) : σ.iW n ∘ₗ σ.aS {n} = σ.aS Set.univ ∘ₗ σ.iV n :=
  LinearMap.ext fun x ↦ incl_comm σ.C σ.B (Set.subset_univ {n}) σ.C.a.hom
    (fun i ↦ (σ.B i).a.hom) σ.α x

lemma iW_bS (n : J) : σ.iW n ∘ₗ σ.bS {n} = σ.bS Set.univ ∘ₗ σ.iV n :=
  LinearMap.ext fun x ↦ incl_comm σ.C σ.B (Set.subset_univ {n}) σ.C.b.hom
    (fun i ↦ (σ.B i).b.hom) σ.β x

variable {G : Type u} [AddCommGroup G] [Module k G] (Gs : J → Submodule k G)

/-- The space `V` of the transported module. -/
def tV : Submodule k (G ⊗[k] σ.SV Set.univ) :=
  ⨆ n, LinearMap.range (TensorProduct.map (Gs n).subtype (σ.iV n))

/-- The space `W` of the transported module. -/
def tW : Submodule k (G ⊗[k] σ.SW Set.univ) :=
  ⨆ n, LinearMap.range (TensorProduct.map (Gs n).subtype (σ.iW n))

lemma map_tV_le (f : σ.SV Set.univ →ₗ[k] σ.SW Set.univ) (g : ∀ n, σ.SV {n} →ₗ[k] σ.SW {n})
    (hfg : ∀ n, σ.iW n ∘ₗ g n = f ∘ₗ σ.iV n) :
    (σ.tV Gs).map (f.lTensor G) ≤ σ.tW Gs := by
  rw [tV, Submodule.map_iSup]
  refine iSup_le fun n ↦ ?_
  rw [← LinearMap.range_comp]
  have : f.lTensor G ∘ₗ TensorProduct.map (Gs n).subtype (σ.iV n) =
      TensorProduct.map (Gs n).subtype (σ.iW n) ∘ₗ (g n).lTensor (Gs n) := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.lTensor_tmul]
    rw [← LinearMap.comp_apply f, ← hfg n]
    rfl
  rw [this, LinearMap.range_comp]
  exact (LinearMap.map_le_range).trans (le_iSup (fun n ↦ LinearMap.range
    (TensorProduct.map (Gs n).subtype (σ.iW n))) n)

/-- The arrow `a` of the transported module. -/
def aH : σ.tV Gs →ₗ[k] σ.tW Gs :=
  ((σ.aS Set.univ).lTensor G).restrict fun _ hx ↦
    σ.map_tV_le Gs _ _ (fun n ↦ σ.iW_aS n) (Submodule.mem_map_of_mem hx)

/-- The arrow `b` of the transported module. -/
def bH : σ.tV Gs →ₗ[k] σ.tW Gs :=
  ((σ.bS Set.univ).lTensor G).restrict fun _ hx ↦
    σ.map_tV_le Gs _ _ (fun n ↦ σ.iW_bS n) (Submodule.mem_map_of_mem hx)

/-- The transported Kronecker module `H = ∑_j G_j ⊗ F_{{j}} ⊆ G ⊗ F_J`. -/
def transport : Kron k :=
  Kron.mk (ModuleCat.of k (σ.tV Gs)) (ModuleCat.of k (σ.tW Gs)) (ModuleCat.ofHom (σ.aH Gs))
    (ModuleCat.ofHom (σ.bH Gs))

end Anchored

section TensorLemmas

variable {G : Type u} [AddCommGroup G] [Module k G] {M : Type u} [AddCommGroup M] [Module k M]

lemma tmul_left_inj {v v' : G} {y : M} (hy : y ≠ 0) (h : v ⊗ₜ[k] y = v' ⊗ₜ[k] y) : v = v' := by
  obtain ⟨lam, hl⟩ := Module.Projective.exists_dual_eq_one k hy
  have := congrArg (fun t ↦ (TensorProduct.rid k G) (TensorProduct.map LinearMap.id lam t)) h
  simpa [hl] using this

lemma eq_zero_of_tmul_right' {v : G} {y : M} (hy : y ≠ 0) (h : v ⊗ₜ[k] y = 0) : v = 0 :=
  tmul_left_inj hy (h.trans (TensorProduct.zero_tmul _ _).symm)

lemma mem_of_tmul_mem (S : Submodule k G) {v : G} {y : M} (hy : y ≠ 0)
    (h : v ⊗ₜ[k] y ∈ LinearMap.range (TensorProduct.map S.subtype (LinearMap.id : M →ₗ[k] M))) :
    v ∈ S := by
  obtain ⟨t, ht⟩ := h
  have hz : TensorProduct.map S.mkQ (LinearMap.id : M →ₗ[k] M)
      (TensorProduct.map S.subtype LinearMap.id t) = 0 := by
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp,
      show S.mkQ ∘ₗ S.subtype = 0 from LinearMap.ext fun x ↦ by simp]
    simp
  rw [ht, TensorProduct.map_tmul, LinearMap.id_apply] at hz
  obtain ⟨lam, hl⟩ := Module.Projective.exists_dual_eq_one k hy
  have := congrArg (fun t ↦ (TensorProduct.rid k (G ⧸ S)) (TensorProduct.map LinearMap.id lam t)) hz
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, hl, TensorProduct.rid_tmul, one_smul,
    map_zero] at this
  exact (Submodule.Quotient.mk_eq_zero S).1 this

lemma dfinsupp_singleton {J : Type u} [DecidableEq J] {m : J} {M : ({m} : Set J) → Type u}
    [∀ i, AddCommGroup (M i)] (y : Π₀ i, M i) :
    y = DFinsupp.single (⟨m, Set.mem_singleton m⟩ : ({m} : Set J)) (y ⟨m, Set.mem_singleton m⟩) := by
  ext ⟨i, hi⟩
  obtain rfl : i = m := hi
  simp

end TensorLemmas

namespace Anchored

variable {J : Type u} [DecidableEq J] (σ : Anchored k J)
variable {G : Type u} [AddCommGroup G] [Module k G] (Gs : J → Submodule k G)

lemma genV_mem {n : J} {g : G} (hg : g ∈ Gs n) (x : σ.SV {n}) : g ⊗ₜ σ.iV n x ∈ σ.tV Gs :=
  Submodule.mem_iSup_of_mem n ⟨⟨g, hg⟩ ⊗ₜ x, by simp⟩

lemma genW_mem {n : J} {g : G} (hg : g ∈ Gs n) (x : σ.SW {n}) : g ⊗ₜ σ.iW n x ∈ σ.tW Gs :=
  Submodule.mem_iSup_of_mem n ⟨⟨g, hg⟩ ⊗ₜ x, by simp⟩

/-- Induction over the generators of `tV`. -/
lemma tV_induction {P : ∀ v, v ∈ σ.tV Gs → Prop}
    (gen : ∀ n (g : G) (hg : g ∈ Gs n) (x : σ.SV {n}), P _ (σ.genV_mem Gs hg x))
    (zero : P 0 (σ.tV Gs).zero_mem)
    (add : ∀ v w hv hw, P v hv → P w hw → P (v + w) ((σ.tV Gs).add_mem hv hw))
    {v : G ⊗[k] σ.SV Set.univ} (hv : v ∈ σ.tV Gs) : P v hv := by
  induction hv using Submodule.iSup_induction' with
  | mem n v hv =>
    obtain ⟨t, rfl⟩ := hv
    induction t using TensorProduct.inductionOn with
    | tmul g x => exact gen n g g.2 x
    | add t t' ht ht' =>
      simp only [map_add]
      exact add _ _ _ _ ht ht'
  | zero => exact zero
  | add v w hv hw ihv ihw => exact add v w _ _ ihv ihw

/-- Induction over the generators of `tW`. -/
lemma tW_induction {P : ∀ v, v ∈ σ.tW Gs → Prop}
    (gen : ∀ n (g : G) (hg : g ∈ Gs n) (x : σ.SW {n}), P _ (σ.genW_mem Gs hg x))
    (zero : P 0 (σ.tW Gs).zero_mem)
    (add : ∀ v w hv hw, P v hv → P w hw → P (v + w) ((σ.tW Gs).add_mem hv hw))
    {v : G ⊗[k] σ.SW Set.univ} (hv : v ∈ σ.tW Gs) : P v hv := by
  induction hv using Submodule.iSup_induction' with
  | mem n v hv =>
    obtain ⟨t, rfl⟩ := hv
    induction t using TensorProduct.inductionOn with
    | tmul g x => exact gen n g g.2 x
    | add t t' ht ht' =>
      simp only [map_add]
      exact add _ _ _ _ ht ht'
  | zero => exact zero
  | add v w hv hw ihv ihw => exact add v w _ _ ihv ihw

lemma iV_anchor (n : J) : σ.iV n (σ.c0, 0) = (σ.c0, 0) := by
  simp [iV, inclV]

/-- The generator map `x ↦ g ⊗ iV x` into `tV`. -/
def genV {n : J} {g : G} (hg : g ∈ Gs n) : σ.SV {n} →ₗ[k] σ.tV Gs :=
  ((TensorProduct.mk k G _ g) ∘ₗ σ.iV n).codRestrict (σ.tV Gs) fun x ↦ σ.genV_mem Gs hg x

/-- The generator map `w ↦ g ⊗ iW w` into `tW`. -/
def genW {n : J} {g : G} (hg : g ∈ Gs n) : σ.SW {n} →ₗ[k] σ.tW Gs :=
  ((TensorProduct.mk k G _ g) ∘ₗ σ.iW n).codRestrict (σ.tW Gs) fun x ↦ σ.genW_mem Gs hg x

lemma aH_genV {n : J} {g : G} (hg : g ∈ Gs n) (x : σ.SV {n}) :
    σ.aH Gs (σ.genV Gs hg x) = σ.genW Gs hg (σ.aS {n} x) := by
  apply Subtype.ext
  change (σ.aS Set.univ).lTensor G (g ⊗ₜ σ.iV n x) = g ⊗ₜ σ.iW n (σ.aS {n} x)
  rw [LinearMap.lTensor_tmul, ← LinearMap.comp_apply (σ.iW n), iW_aS]
  rfl

lemma bH_genV {n : J} {g : G} (hg : g ∈ Gs n) (x : σ.SV {n}) :
    σ.bH Gs (σ.genV Gs hg x) = σ.genW Gs hg (σ.bS {n} x) := by
  apply Subtype.ext
  change (σ.bS Set.univ).lTensor G (g ⊗ₜ σ.iV n x) = g ⊗ₜ σ.iW n (σ.bS {n} x)
  rw [LinearMap.lTensor_tmul, ← LinearMap.comp_apply (σ.iW n), iW_bS]
  rfl

/-- The projection of `V_{F_J}` to the component `V_{B n}`. -/
def projV (n : J) : σ.SV Set.univ →ₗ[k] (σ.B n).V :=
  DFinsupp.lapply (⟨n, Set.mem_univ n⟩ : (Set.univ : Set J)) ∘ₗ LinearMap.snd k _ _

lemma projV_iV_ne {m n : J} (h : m ≠ n) (x : σ.SV {m}) : σ.projV n (σ.iV m x) = 0 := by
  obtain ⟨c, y⟩ := x
  change (extendV σ.B (Set.subset_univ {m}) y) ⟨n, Set.mem_univ n⟩ = 0
  rw [dfinsupp_singleton y, extendV_single, DFinsupp.single_eq_of_ne]
  intro e
  exact h (congrArg Subtype.val e).symm

lemma projV_iV_self (n : J) (x : σ.SV {n}) :
    σ.projV n (σ.iV n x) = x.2 ⟨n, Set.mem_singleton n⟩ := by
  obtain ⟨c, y⟩ := x
  change (extendV σ.B (Set.subset_univ {n}) y) ⟨n, Set.mem_univ n⟩ = _
  rw [dfinsupp_singleton y, extendV_single]
  simp

lemma projV_tV {n : J} {v : G ⊗[k] σ.SV Set.univ} (hv : v ∈ σ.tV Gs) :
    (σ.projV n).lTensor G v ∈
      LinearMap.range (TensorProduct.map (Gs n).subtype (LinearMap.id : (σ.B n).V →ₗ[k] _)) := by
  classical
  induction hv using σ.tV_induction Gs with
  | gen m g hg x =>
    rw [LinearMap.lTensor_tmul]
    by_cases hmn : m = n
    · subst hmn
      exact ⟨⟨g, hg⟩ ⊗ₜ σ.projV m (σ.iV m x), by simp⟩
    · rw [σ.projV_iV_ne hmn, TensorProduct.tmul_zero]
      exact Submodule.zero_mem _
  | zero => simp
  | add v w hv hw ihv ihw =>
    rw [map_add]
    exact Submodule.add_mem _ ihv ihw

/-- The vector `(0, y n)` of `F_{{n}}`. -/
def xB (n : J) : σ.SV {n} := (0, DFinsupp.single ⟨n, Set.mem_singleton n⟩ (σ.y n))

lemma projV_iV_xB (n : J) : σ.projV n (σ.iV n (σ.xB n)) = σ.y n := by
  rw [projV_iV_self]
  simp [xB]

/-- The inclusion `F_{{n}} → F_J`. -/
def u (n : J) : σ.F {n} ⟶ σ.F Set.univ := subIncl σ.C σ.B σ.α σ.β (Set.subset_univ {n})

lemma hu (n : J) (f : σ.F {n} ⟶ σ.F Set.univ) : ∃ c : k, f = c • σ.u n :=
  hom_subExt_of_subset σ.hC σ.hB σ.hCB σ.hBC σ.hBB σ.hns _ f

lemma hx0 (n : J) : ((σ.u n).app zero).hom (σ.c0, 0) ≠ 0 := fun h ↦ by
  have : σ.iV n (σ.c0, 0) = 0 := h
  rw [iV_anchor] at this
  exact σ.hc0 (congrArg Prod.fst this)

lemma anchor_ne_zero : ((σ.c0, 0) : σ.SV Set.univ) ≠ 0 := fun h ↦ σ.hc0 (congrArg Prod.fst h)

variable {G' : Type u} [AddCommGroup G'] [Module k G'] (Gs' : J → Submodule k G')

/-- Morphisms between transports are `Ψ ⊗ id` with `Ψ(G_j) ⊆ G'_j`. -/
theorem hom_transport {j0 : J} (h0 : Gs j0 = ⊤) (f : σ.transport Gs ⟶ σ.transport Gs') :
    ∃ Ψ : G →ₗ[k] G', (∀ j, ∀ g ∈ Gs j, Ψ g ∈ Gs' j) ∧
      (∀ v : σ.tV Gs, ((show σ.tV Gs →ₗ[k] σ.tV Gs' from (f.app zero).hom) v).1 =
        Ψ.rTensor _ (v : G ⊗[k] σ.SV Set.univ)) ∧
      ∀ w : σ.tW Gs, ((show σ.tW Gs →ₗ[k] σ.tW Gs' from (f.app one).hom) w).1 =
        Ψ.rTensor _ (w : G ⊗[k] σ.SW Set.univ) := by
  classical
  have hmem0 : ∀ g : G, g ∈ Gs j0 := fun g ↦ h0 ▸ Submodule.mem_top
  set F : σ.tV Gs →ₗ[k] σ.tV Gs' := (f.app zero).hom
  set Gm : σ.tW Gs →ₗ[k] σ.tW Gs' := (f.app one).hom
  have hFa : ∀ v, Gm (σ.aH Gs v) = σ.aH Gs' (F v) := fun v ↦ Kron.a_apply f v
  have hFb : ∀ v, Gm (σ.bH Gs v) = σ.bH Gs' (F v) := fun v ↦ Kron.b_apply f v
  -- coefficients on each generator family
  have key : ∀ n (g : G) (hg : g ∈ Gs n), ∃ ν : G',
      (∀ x, (F (σ.genV Gs hg x) : G' ⊗[k] σ.SV Set.univ) = ν ⊗ₜ σ.iV n x) ∧
      ∀ w, (Gm (σ.genW Gs hg w) : G' ⊗[k] σ.SW Set.univ) = ν ⊗ₜ σ.iW n w := by
    intro n g hg
    refine coeff_eq (X := σ.F {n}) (Y := σ.F Set.univ) (N := G') (σ.u n) (σ.hu n) (σ.c0, 0)
      (σ.hx0 n) ((σ.tV Gs').subtype ∘ₗ F ∘ₗ σ.genV Gs hg)
      ((σ.tW Gs').subtype ∘ₗ Gm ∘ₗ σ.genW Gs hg) ?_ ?_
    · refine LinearMap.ext fun x ↦ ?_
      change (σ.aS Set.univ).lTensor G' (F (σ.genV Gs hg x) : G' ⊗[k] σ.SV Set.univ) =
        (Gm (σ.genW Gs hg (σ.aS {n} x)) : G' ⊗[k] σ.SW Set.univ)
      have h := hFa (σ.genV Gs hg (show σ.SV {n} from x))
      rw [aH_genV] at h
      exact (congrArg Subtype.val h).symm
    · refine LinearMap.ext fun x ↦ ?_
      change (σ.bS Set.univ).lTensor G' (F (σ.genV Gs hg x) : G' ⊗[k] σ.SV Set.univ) =
        (Gm (σ.genW Gs hg (σ.bS {n} x)) : G' ⊗[k] σ.SW Set.univ)
      have h := hFb (σ.genV Gs hg (show σ.SV {n} from x))
      rw [bH_genV] at h
      exact (congrArg Subtype.val h).symm
  choose ν hνV hνW using key
  have hy0' := σ.anchor_ne_zero
  let Ψ : G → G' := fun g ↦ ν j0 g (hmem0 g)
  -- all coefficients agree with `Ψ` (through the anchor)
  have hνΨ : ∀ n g (hg : g ∈ Gs n), ν n g hg = Ψ g := by
    intro n g hg
    have h1 := hνV n g hg (σ.c0, 0)
    have h2 := hνV j0 g (hmem0 g) (σ.c0, 0)
    have he : σ.genV Gs hg (σ.c0, 0) = σ.genV Gs (hmem0 g) (σ.c0, 0) := by
      apply Subtype.ext
      change g ⊗ₜ σ.iV n (σ.c0, 0) = g ⊗ₜ σ.iV j0 (σ.c0, 0)
      rw [iV_anchor, iV_anchor]
    rw [he, h2, iV_anchor, iV_anchor] at h1
    exact (tmul_left_inj hy0' h1).symm
  have hΨV : ∀ g, (F (σ.genV Gs (hmem0 g) (σ.c0, 0)) : G' ⊗[k] σ.SV Set.univ) =
      Ψ g ⊗ₜ ((σ.c0, 0) : σ.SV Set.univ) := fun g ↦ by
    rw [hνV, iV_anchor]
  have hΨadd : ∀ g g', Ψ (g + g') = Ψ g + Ψ g' := by
    intro g g'
    have he : σ.genV Gs (hmem0 (g + g')) (σ.c0, 0) =
        σ.genV Gs (hmem0 g) (σ.c0, 0) + σ.genV Gs (hmem0 g') (σ.c0, 0) := by
      apply Subtype.ext
      change (g + g') ⊗ₜ σ.iV j0 (σ.c0, 0) = g ⊗ₜ σ.iV j0 (σ.c0, 0) + g' ⊗ₜ σ.iV j0 (σ.c0, 0)
      rw [TensorProduct.add_tmul]
    have := congrArg (fun v : σ.tV Gs' ↦ (v : G' ⊗[k] σ.SV Set.univ)) (congrArg F he)
    simp only [map_add, Submodule.coe_add, hΨV] at this
    rw [← TensorProduct.add_tmul] at this
    exact tmul_left_inj hy0' this
  have hΨsmul : ∀ (r : k) g, Ψ (r • g) = r • Ψ g := by
    intro r g
    have he : σ.genV Gs (hmem0 (r • g)) (σ.c0, 0) = r • σ.genV Gs (hmem0 g) (σ.c0, 0) := by
      apply Subtype.ext
      change (r • g) ⊗ₜ σ.iV j0 (σ.c0, 0) = r • (g ⊗ₜ σ.iV j0 (σ.c0, 0))
      rw [TensorProduct.smul_tmul']
    have := congrArg (fun v : σ.tV Gs' ↦ (v : G' ⊗[k] σ.SV Set.univ)) (congrArg F he)
    simp only [map_smul, Submodule.coe_smul, hΨV] at this
    rw [TensorProduct.smul_tmul'] at this
    exact tmul_left_inj hy0' this
  let Ψl : G →ₗ[k] G' := ⟨⟨Ψ, hΨadd⟩, hΨsmul⟩
  refine ⟨Ψl, fun n g hg ↦ ?_, fun ⟨v, hv⟩ ↦ ?_, fun ⟨v, hv⟩ ↦ ?_⟩
  · have hm := σ.projV_tV Gs' (n := n) (F (σ.genV Gs hg (σ.xB n))).2
    rw [hνV, hνΨ, LinearMap.lTensor_tmul, projV_iV_xB] at hm
    exact mem_of_tmul_mem (Gs' n) (σ.hy n) hm
  · change (F ⟨v, hv⟩ : G' ⊗[k] σ.SV Set.univ) = Ψl.rTensor _ v
    induction hv using σ.tV_induction Gs with
    | gen n g hg x =>
      change (F (σ.genV Gs hg x) : G' ⊗[k] σ.SV Set.univ) = _
      rw [hνV, hνΨ, LinearMap.rTensor_tmul]
      rfl
    | zero =>
      rw [map_zero]
      exact congrArg Subtype.val (map_zero F)
    | add v w hv hw ihv ihw =>
      have : (⟨v + w, (σ.tV Gs).add_mem hv hw⟩ : σ.tV Gs) = ⟨v, hv⟩ + ⟨w, hw⟩ := rfl
      rw [this, map_add, Submodule.coe_add, ihv, ihw, map_add]
  · change (Gm ⟨v, hv⟩ : G' ⊗[k] σ.SW Set.univ) = Ψl.rTensor _ v
    induction hv using σ.tW_induction Gs with
    | gen n g hg x =>
      change (Gm (σ.genW Gs hg x) : G' ⊗[k] σ.SW Set.univ) = _
      rw [hνW, hνΨ, LinearMap.rTensor_tmul]
      rfl
    | zero =>
      rw [map_zero]
      exact congrArg Subtype.val (map_zero Gm)
    | add v w hv hw ihv ihw =>
      have : (⟨v + w, (σ.tW Gs).add_mem hv hw⟩ : σ.tW Gs) = ⟨v, hv⟩ + ⟨w, hw⟩ := rfl
      rw [this, map_add, Submodule.coe_add, ihv, ihw, map_add]

lemma hom_ext_of_rTensor {Ψ : G →ₗ[k] G'} {f g : σ.transport Gs ⟶ σ.transport Gs'}
    (hfV : ∀ v : σ.tV Gs, ((show σ.tV Gs →ₗ[k] σ.tV Gs' from (f.app zero).hom) v).1 =
      Ψ.rTensor _ (v : G ⊗[k] σ.SV Set.univ))
    (hfW : ∀ w : σ.tW Gs, ((show σ.tW Gs →ₗ[k] σ.tW Gs' from (f.app one).hom) w).1 =
      Ψ.rTensor _ (w : G ⊗[k] σ.SW Set.univ))
    (hgV : ∀ v : σ.tV Gs, ((show σ.tV Gs →ₗ[k] σ.tV Gs' from (g.app zero).hom) v).1 =
      Ψ.rTensor _ (v : G ⊗[k] σ.SV Set.univ))
    (hgW : ∀ w : σ.tW Gs, ((show σ.tW Gs →ₗ[k] σ.tW Gs' from (g.app one).hom) w).1 =
      Ψ.rTensor _ (w : G ⊗[k] σ.SW Set.univ)) : f = g := by
  refine Kron.hom_ext ?_ ?_
  · ext v
    exact Subtype.ext ((hfV v).trans (hgV v).symm)
  · ext w
    exact Subtype.ext ((hfW w).trans (hgW w).symm)

/-- Transports are orthogonal when only `0` maps the structures. -/
theorem transport_hom_eq_zero {j0 : J} (h0 : Gs j0 = ⊤)
    (hz : ∀ Ψ : G →ₗ[k] G', (∀ j, ∀ g ∈ Gs j, Ψ g ∈ Gs' j) → Ψ = 0)
    (f : σ.transport Gs ⟶ σ.transport Gs') : f = 0 := by
  obtain ⟨Ψ, hΨ, hV, hW⟩ := σ.hom_transport Gs Gs' h0 f
  obtain rfl := hz Ψ hΨ
  refine σ.hom_ext_of_rTensor Gs Gs' hV hW (fun v ↦ ?_) (fun w ↦ ?_)
  · simp only [LinearMap.rTensor_zero, LinearMap.zero_apply]
    rfl
  · simp only [LinearMap.rTensor_zero, LinearMap.zero_apply]
    rfl

/-- The transport of a rigid structure with `G_{j₀} = G ≠ 0` is a brick. -/
theorem isBrick_transport [Nontrivial G] {j0 : J} (h0 : Gs j0 = ⊤) (hrig : IsRigidR Gs) :
    IsBrickKron (σ.transport Gs) := by
  have hmem0 : ∀ g : G, g ∈ Gs j0 := fun g ↦ h0 ▸ Submodule.mem_top
  refine ⟨fun hz ↦ ?_, fun f ↦ ?_⟩
  · obtain ⟨g, hg⟩ := exists_ne (0 : G)
    have hs : Subsingleton (σ.tV Gs) :=
      ModuleCat.isZero_iff_subsingleton.1 (hz.obj zero)
    have := congrArg Subtype.val
      (@Subsingleton.elim _ hs (σ.genV Gs (hmem0 g) (σ.c0, 0)) 0)
    change g ⊗ₜ σ.iV j0 (σ.c0, 0) = 0 at this
    rw [iV_anchor] at this
    exact hg (eq_zero_of_tmul_right' σ.anchor_ne_zero this)
  obtain ⟨Ψ, hΨ, hV, hW⟩ := σ.hom_transport Gs Gs h0 f
  obtain ⟨c, rfl⟩ := hrig Ψ hΨ
  refine ⟨c, σ.hom_ext_of_rTensor Gs Gs hV hW (fun v ↦ ?_) (fun w ↦ ?_)⟩
  · change c • (v : G ⊗[k] σ.SV Set.univ) = _
    rw [LinearMap.rTensor_smul, LinearMap.rTensor_id]
    rfl
  · change c • (w : G ⊗[k] σ.SW Set.univ) = _
    rw [LinearMap.rTensor_smul, LinearMap.rTensor_id]
    rfl

end Anchored

end Bricks

end LargeIndecomposable
