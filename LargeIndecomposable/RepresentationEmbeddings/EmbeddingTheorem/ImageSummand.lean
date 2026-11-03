module

public import LargeIndecomposable.RepresentationEmbeddings.EmbeddingTheorem.CSub
public import LargeIndecomposable.RepresentationEmbeddings.Control.Retraction
public import LargeIndecomposable.RepresentationEmbeddings.EmbeddingTheorem.FixedSummand
public import LargeIndecomposable.RepresentationEmbeddings.Control.Consequences
public import LargeIndecomposable.RepresentationEmbeddings.EmbeddingTheorem.Colimit
public import LargeIndecomposable.RepresentationEmbeddings.EmbeddingTheorem.Cancellation

/-!
# Images of idempotents of Kronecker modules

The image of an idempotent endomorphism of a Kronecker module is a direct
summand; it lies in `C` when the module does, and is finite-dimensional when
the module is. These are used in Step 1 of the proof of Theorem 5.2. Also:
`S₋` does not lie in `C`, and `S₋` as an object of `D_fin`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair

universe u

variable {k : Type u} [Field k]

/-! ### The image of an idempotent of a Kronecker module -/

namespace Kron

variable {X : Kron k} (η : X ⟶ X) (hη : η ≫ η = η)

/-- The image of an endomorphism, as a subrepresentation. -/
def imSub : Kron.Sub X where
  V := LinearMap.range (η.app zero).hom
  W := LinearMap.range (η.app one).hom
  map_a := by rintro _ ⟨v, rfl⟩; exact ⟨X.a.hom v, Kron.a_apply η v⟩
  map_b := by rintro _ ⟨v, rfl⟩; exact ⟨X.b.hom v, Kron.b_apply η v⟩

include hη in
lemma app_idem (j : WalkingParallelPair) (x : X.obj j) :
    (η.app j).hom ((η.app j).hom x) = (η.app j).hom x := by
  rw [← ModuleCat.comp_apply, ← NatTrans.comp_app, hη]

/-- The corestriction `X → im η`. -/
def imRetr : X ⟶ (imSub η).toKron :=
  Kron.homMk (ModuleCat.ofHom ((η.app zero).hom.rangeRestrict))
    (ModuleCat.ofHom ((η.app one).hom.rangeRestrict))
    (by ext v; exact Subtype.ext (Kron.a_apply η v))
    (by ext v; exact Subtype.ext (Kron.b_apply η v))

lemma imRetr_ι : imRetr η ≫ (imSub η).ι = η := by
  apply Kron.hom_ext <;> rfl

include hη in
lemma ι_imRetr : (imSub η).ι ≫ imRetr η = 𝟙 _ := by
  apply Kron.hom_ext
  · ext ⟨_, v, rfl⟩
    exact Subtype.ext (app_idem η hη zero v)
  · ext ⟨_, w, rfl⟩
    exact Subtype.ext (app_idem η hη one w)

/-- The image of an endomorphism of a module in `C` is in `C`. -/
lemma inC_imSub (hX : InC X) : InC (imSub η).toKron := by
  refine ⟨(imSub η).inD hX.1, ?_⟩
  rw [eq_top_iff]
  rintro ⟨_, w, rfl⟩ -
  have hw : w ∈ LinearMap.range X.a.hom ⊔ LinearMap.range X.b.hom := hX.2 ▸ trivial
  obtain ⟨_, ⟨v, rfl⟩, _, ⟨v', rfl⟩, rfl⟩ := Submodule.mem_sup.1 hw
  let x : LinearMap.range (η.app zero).hom := ⟨_, LinearMap.mem_range_self (η.app zero).hom v⟩
  let x' : LinearMap.range (η.app zero).hom := ⟨_, LinearMap.mem_range_self (η.app zero).hom v'⟩
  have e : (⟨(η.app one).hom (X.a.hom v + X.b.hom v'), ⟨_, rfl⟩⟩ :
      LinearMap.range (η.app one).hom) =
      (imSub η).toKron.a.hom x + (imSub η).toKron.b.hom x' := by
    apply Subtype.ext
    change (η.app one).hom (X.a.hom v + X.b.hom v') =
      X.a.hom ((η.app zero).hom v) + X.b.hom ((η.app zero).hom v')
    rw [map_add, Kron.a_apply, Kron.b_apply]
  have h := Submodule.add_mem_sup (LinearMap.mem_range_self ((imSub η).toKron.a.hom) x)
    (LinearMap.mem_range_self ((imSub η).toKron.b.hom) x')
  convert h using 1
  exact e

lemma isFiniteDimensional_imSub (hX : X.IsFiniteDimensional) :
    (imSub η).toKron.IsFiniteDimensional := by
  obtain ⟨h0, h1⟩ := hX
  exact ⟨inferInstanceAs (FiniteDimensional k (LinearMap.range (η.app zero).hom)),
    inferInstanceAs (FiniteDimensional k (LinearMap.range (η.app one).hom))⟩

end Kron

lemma not_inC_Sminus : ¬ InC (Kron.Sminus k) := by
  rintro ⟨-, h⟩
  have : (1 : k) ∈ (⊤ : Submodule k k) := trivial
  rw [← h] at this
  obtain ⟨_, ⟨v, rfl⟩, _, ⟨v', rfl⟩, h1⟩ := Submodule.mem_sup.1 this
  simp at h1

variable {A : Type u} [Ring A] [Algebra k A]

namespace Extension

/-- `S₋` as an object of `D_fin`. -/
def SminusFin : Dfin k := ⟨Sminus.obj, Sminus.2, Sminus_isFiniteDimensional⟩

lemma Retractions.iter_eq_pow {M : ModuleCat.{u} A} (e : M ⟶ M) (m : ℕ) :
    Retractions.iter e m = ((show End M from e) ^ m : End M) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Retractions.iter, ih, pow_succ', End.mul_def]

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

end Extension

end LargeIndecomposable
