module

public import LargeIndecomposable.DirectedAlgebras.EulerForm.EulerUnit
public import LargeIndecomposable.DirectedAlgebras.Directing.Degeneration
public import LargeIndecomposable.AuslanderReiten.AlmostSplit.ARSeq
public import LargeIndecomposable.DirectedAlgebras.Directing.RigidMin

/-!
# The Euler form on projective presentations

Call `P` Euler-projective if `⟨dim P, dim W⟩ = dim Hom(P, W)` for every `W`. The indecomposable
projectives `Ae` are Euler-projective (`eulerProj_projE`), and so are binary sums of
Euler-projectives (`EulerProj.prod`). For a short exact sequence `0 → P₁ → P₀ → Z → 0` of
Euler-projectives, `⟨dim Z, dim W⟩ = dim Hom(Z, W) - dim coker(Hom(P₀, W) → Hom(P₁, W))`
(`euler_presentation`); the cokernel is `Ext¹(Z, W)` when `P₀`, `P₁` are projective.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open Module Matrix

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (D : DirData k A)

/-- The dimension vector with integer entries. -/
def dimZ (M : FDMod k A) : D.ι → ℤ := fun j ↦ (dimv D.e M j : ℤ)

/-- `⟨dim P, dim W⟩ = dim Hom(P, W)` for every `W`. -/
def EulerProj (P : FDMod k A) : Prop :=
  ∀ W : FDMod k A, euler D (dimZ D P) (dimZ D W) = finrank k (P →ₗ[A] W)

lemma euler_sub (u v w : D.ι → ℤ) : euler D (u - v) w = euler D u w - euler D v w := by
  unfold euler
  rw [mulVec_sub, sub_dotProduct]

lemma euler_add (u v w : D.ι → ℤ) : euler D (u + v) w = euler D u w + euler D v w := by
  unfold euler
  rw [mulVec_add, add_dotProduct]

/-- **Indecomposable projectives are Euler-projective.** -/
theorem eulerProj_projE (hT : ∀ x, x ∈ D.T) (i : D.ι) : EulerProj D (projE (k := k) (D.idem i)) := by
  intro W
  have h : dimZ D (projE (k := k) (D.idem i)) = fun j ↦ cartan D j i := rfl
  rw [h, euler_cartan_col D hT, (homProjEquiv (D.idem i) W).finrank_eq]
  rfl

lemma dimZ_exact {M N L : FDMod k A} (f : M →ₗ[A] N) (g : N →ₗ[A] L) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hex : LinearMap.range f = LinearMap.ker g) :
    dimZ D N = dimZ D M + dimZ D L := by
  funext x
  simp only [dimZ, Pi.add_apply]
  exact_mod_cast dimv_exact D.e D.idem (M := M) (N := N) (L := L) (FDMod.ofLin (f)) (FDMod.ofLin (g)) hf hg hex x

/-- Maps out of a product. -/
def homProdEquiv (P Q W : FDMod k A) :
    (FDMod.prod P Q →ₗ[A] W) ≃ₗ[k] (P →ₗ[A] W) × (Q →ₗ[A] W) where
  toFun f := (f ∘ₗ LinearMap.inl A P Q, f ∘ₗ LinearMap.inr A P Q)
  map_add' f g := by ext <;> simp
  map_smul' c f := by ext <;> simp
  invFun g := g.1.coprod g.2
  left_inv f := by ext <;> simp
  right_inv g := by ext <;> simp

/-- **Sums of Euler-projectives are Euler-projective.** -/
theorem EulerProj.prod {P Q : FDMod k A} (hP : EulerProj D P) (hQ : EulerProj D Q) :
    EulerProj D (FDMod.prod P Q) := by
  intro W
  have hd : dimZ D (FDMod.prod P Q) = dimZ D P + dimZ D Q :=
    dimZ_exact D (M := P) (N := FDMod.prod P Q) (L := Q) (LinearMap.inl A P Q)
      (LinearMap.snd A P Q) LinearMap.inl_injective (fun q ↦ ⟨(0, q), rfl⟩)
      (by rw [LinearMap.range_inl, LinearMap.ker_snd])
  rw [hd, euler_add, hP W, hQ W, (homProdEquiv P Q W).finrank_eq, Module.finrank_prod]
  push_cast
  rfl

/-- **The Euler form on a presentation.** -/
theorem euler_presentation {P₀ P₁ Z : FDMod k A} (h₀ : EulerProj D P₀) (h₁ : EulerProj D P₁)
    (f : P₁ →ₗ[A] P₀) (g : P₀ →ₗ[A] Z) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : LinearMap.range f = LinearMap.ker g) (W : FDMod k A) :
    euler D (dimZ D Z) (dimZ D W) = (finrank k (Z →ₗ[A] W) : ℤ) -
      ((finrank k (P₁ →ₗ[A] W) : ℤ) -
        finrank k (LinearMap.range (precomp k (Y := W) f))) := by
  have hd := dimZ_exact D f g hf hg hex
  have hZ : dimZ D Z = dimZ D P₀ - dimZ D P₁ := by rw [hd]; abel
  rw [hZ, euler_sub, h₀ W, h₁ W]
  -- `Hom(Z, W)` is the kernel of restriction to `P₁`
  have hker : finrank k (LinearMap.ker (precomp k (Y := W) f)) = finrank k (Z →ₗ[A] W) := by
    have hinj : Function.Injective (precomp k (Y := W) g) := by
      intro φ ψ h
      refine LinearMap.ext fun z ↦ ?_
      obtain ⟨p, rfl⟩ := hg z
      exact LinearMap.congr_fun h p
    have hrange : LinearMap.range (precomp k (Y := W) g) = LinearMap.ker (precomp k (Y := W) f) := by
      ext φ
      constructor
      · rintro ⟨ψ, rfl⟩
        rw [LinearMap.mem_ker]
        refine LinearMap.ext fun p ↦ ?_
        change ψ (g (f p)) = 0
        rw [mem_ker_of_range hex, map_zero]
      · intro hφ
        obtain ⟨ψ, hψ⟩ := exists_factor f g hg hex φ hφ
        exact ⟨ψ, hψ⟩
    rw [← hrange, LinearMap.finrank_range_of_inj hinj]
  have hrn := LinearMap.finrank_range_add_finrank_ker (precomp k (Y := W) f)
  omega

omit [FiniteDimensional k A] in
/-- **Split extensions make restriction onto.** If every extension of `Z` by `W` splits, every
map `P₁ → W` extends along `f : P₁ → P₀` (pushout argument). -/
theorem extend_of_extVanish {P₀ P₁ Z W : FDMod k A} (f : P₁ →ₗ[A] P₀) (g : P₀ →ₗ[A] Z)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : LinearMap.range f = LinearMap.ker g) (hv : ExtVanish Z W) (φ : P₁ →ₗ[A] W) :
    ∃ ψ : P₀ →ₗ[A] W, ψ ∘ₗ f = φ := by
  -- the pushout `E = (W × P₀) / {(φ p, -f p)}`
  let N : Submodule A (W × P₀) := LinearMap.range (LinearMap.prod φ (-f))
  let E := FDMod.ofQuot (FDMod.prod W P₀) N
  let ι : W →ₗ[A] E := N.mkQ ∘ₗ LinearMap.inl A W P₀
  let j : P₀ →ₗ[A] E := N.mkQ ∘ₗ LinearMap.inr A W P₀
  have hN : N ≤ LinearMap.ker (g ∘ₗ LinearMap.snd A W P₀) := by
    rintro _ ⟨p, rfl⟩
    change g (-f p) = 0
    rw [map_neg, mem_ker_of_range hex, neg_zero]
  let π : E →ₗ[A] Z := N.liftQ (g ∘ₗ LinearMap.snd A W P₀) hN
  have hπι : ∀ w, π (ι w) = 0 := fun w ↦ by
    change g 0 = 0
    exact map_zero g
  have hjf : ∀ p, j (f p) = ι (φ p) := fun p ↦ by
    change N.mkQ (0, f p) = N.mkQ (φ p, 0)
    rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨-p, ?_⟩
    simp
  have hι : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    change N.mkQ (w, 0) = 0 at hw
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hw
    obtain ⟨p, hp⟩ := hw
    have h1 : φ p = w := congrArg Prod.fst hp
    have h2 : -f p = 0 := congrArg Prod.snd hp
    have hp0 : p = 0 := hf (by rw [map_zero]; exact neg_eq_zero.1 h2)
    rw [← h1, hp0, map_zero]
  have hπ : Function.Surjective π := fun z ↦ by
    obtain ⟨p, rfl⟩ := hg z
    exact ⟨j p, rfl⟩
  have hexE : LinearMap.range ι = LinearMap.ker π := by
    ext e
    constructor
    · rintro ⟨w, rfl⟩
      exact hπι w
    · intro he
      obtain ⟨⟨w, p⟩, rfl⟩ := N.mkQ_surjective e
      have hgp : g p = 0 := he
      have : p ∈ LinearMap.range f := by rw [hex]; exact hgp
      obtain ⟨q, rfl⟩ := this
      refine ⟨w + φ q, ?_⟩
      change N.mkQ (w + φ q, 0) = N.mkQ (w, f q)
      rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      refine ⟨q, ?_⟩
      simp
  obtain ⟨σ, hσ⟩ := hv E ι π hι hπ hexE
  let d : P₀ →ₗ[A] E := j - σ ∘ₗ g
  have hd : π ∘ₗ d = 0 := by
    refine LinearMap.ext fun p ↦ ?_
    have := LinearMap.congr_fun hσ (g p)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [d, LinearMap.comp_apply, LinearMap.sub_apply, map_sub, this, LinearMap.zero_apply]
    change g p - g p = 0
    exact sub_self _
  obtain ⟨ψ, hψ⟩ := exists_lift ι π hι hexE d hd
  refine ⟨ψ, LinearMap.ext fun p ↦ hι ?_⟩
  have := LinearMap.congr_fun hψ (f p)
  simp only [LinearMap.comp_apply] at this ⊢
  rw [this]
  simp only [d, LinearMap.sub_apply, LinearMap.comp_apply, mem_ker_of_range hex, map_zero,
    sub_zero, hjf]

/-- **The Euler form of a rigid module.** For a presentation by Euler-projectives of `Z` such
that every extension of `Z` by `W` splits, `⟨dim Z, dim W⟩ = dim Hom(Z, W)`. -/
theorem euler_eq_hom_of_extVanish {P₀ P₁ Z : FDMod k A} (h₀ : EulerProj D P₀)
    (h₁ : EulerProj D P₁) (f : P₁ →ₗ[A] P₀) (g : P₀ →ₗ[A] Z) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hex : LinearMap.range f = LinearMap.ker g) (W : FDMod k A)
    (hv : ExtVanish Z W) :
    euler D (dimZ D Z) (dimZ D W) = finrank k (Z →ₗ[A] W) := by
  rw [euler_presentation D h₀ h₁ f g hf hg hex W]
  have hsurj : LinearMap.range (precomp k (Y := W) f) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro φ
    obtain ⟨ψ, hψ⟩ := extend_of_extVanish f g hf hg hex hv φ
    exact ⟨ψ, hψ⟩
  rw [hsurj, finrank_top]
  ring

end LargeIndecomposable.AR
