module

public import LargeIndecomposable.Cleaving.Basic.ThinRep

/-!
# One-parameter matrix families of thin representations

A family of matrix representations `M t` of a thin category, indexed by an
infinite type, gives representation-infiniteness as soon as its natural
endomorphisms are scalars and natural maps between different members vanish at
one vertex of positive dimension (`RayCat.MatFam.not_isRepresentationFinite`).
The hypotheses are matrix identities, checked shape by shape.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayQuiver

universe u

namespace RayCat

variable {V : Type} [Fintype V] [DecidableEq V] {T : ThinData V} {k : Type u} [Field k]

open Classical in
variable (T k) in
/-- A family of matrix representations of `ThinCat T`. -/
structure MatFam (α : Type*) where
  d : V → ℕ
  M : α → ∀ x y, Matrix (Fin (d y)) (Fin (d x)) k
  M_id : ∀ t x, M t x x = 1
  M_comp : ∀ t x y z, T.le x y → T.le y z →
    M t y z * M t x y = if T.nz x y z then M t x z else 0

namespace MatFam

open Classical in
/-- A family from the composition law on strict triples. -/
abbrev mk' {α : Type*} (d : V → ℕ) (M : α → ∀ x y, Matrix (Fin (d y)) (Fin (d x)) k)
    (M_id : ∀ t x, M t x x = 1)
    (M_comp : ∀ t x y z, x ≠ y → y ≠ z → T.le x y → T.le y z →
      M t y z * M t x y = if T.nz x y z then M t x z else 0) : MatFam T k α where
  d := d
  M := M
  M_id := M_id
  M_comp t x y z h h' := by
    rcases eq_or_ne x y with rfl | hxy
    · rw [M_id, Matrix.mul_one, ite_eq_left (T.nz_left _ _ h')]
    rcases eq_or_ne y z with rfl | hyz
    · rw [M_id, Matrix.one_mul, ite_eq_left (T.nz_right _ _ h)]
    exact M_comp t x y z hxy hyz h h'

variable {α : Type*} (F : MatFam T k α)

/-- The space at a vertex. -/
abbrev sp (x : V) : ModuleCat.{u} k := ModuleCat.of k (Fin (F.d x) → k)

/-- The map along a relation. -/
def mapLin (t : α) (x y : V) : F.sp x →ₗ[k] F.sp y := Matrix.toLin' (F.M t x y)

/-- The representation of a member. -/
def rep (t : α) : ThinRep T k where
  sp := F.sp
  map x y _ := F.mapLin t x y
  map_id x := by
    change Matrix.toLin' (F.M t x x) = LinearMap.id
    rw [F.M_id, Matrix.toLin'_one]
  map_comp x y z h h' := by
    change Matrix.toLin' (F.M t y z) ∘ₗ Matrix.toLin' (F.M t x y) = _
    rw [← Matrix.toLin'_mul, F.M_comp t x y z h h']
    split_ifs
    · rfl
    · exact map_zero _

/-- A component of a natural map, on coordinate spaces. -/
def toPi {t s : α} {x : V} (g : (F.rep t).sp x →ₗ[k] (F.rep s).sp x) :
    (Fin (F.d x) → k) →ₗ[k] (Fin (F.d x) → k) where
  toFun m := g m
  map_add' := g.map_add
  map_smul' := g.map_smul

/-- The matrix of a component of a natural map. -/
def mat {t s : α} (f : ∀ x, (F.rep t).sp x →ₗ[k] (F.rep s).sp x) (x : V) :
    Matrix (Fin (F.d x)) (Fin (F.d x)) k :=
  LinearMap.toMatrix' (F.toPi (f x))

omit [Fintype V] [DecidableEq V] in
lemma toMatrix'_natural {t s : α} (f : ∀ x, (F.rep t).sp x →ₗ[k] (F.rep s).sp x)
    (hf : ThinRep.IsNatural f) (x y : V) (h : T.le x y) :
    F.mat f y * F.M t x y = F.M s x y * F.mat f x := by
  have e : (F.toPi (f y)).comp (Matrix.toLin' (F.M t x y)) =
      (Matrix.toLin' (F.M s x y)).comp (F.toPi (f x)) :=
    LinearMap.ext fun m ↦ hf x y h m
  have := congrArg LinearMap.toMatrix' e
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
    LinearMap.toMatrix'_toLin'] at this

/-- **Representation-infiniteness from a one-parameter matrix family.** -/
theorem not_isRepresentationFinite [Infinite α] (x₀ : V) (hx₀ : 0 < F.d x₀)
    (hend : ∀ t (G : ∀ x, Matrix (Fin (F.d x)) (Fin (F.d x)) k),
      (∀ x y, T.le x y → G y * F.M t x y = F.M t x y * G x) → ∃ c : k, ∀ x, G x = c • 1)
    (hhom : ∀ t s (G : ∀ x, Matrix (Fin (F.d x)) (Fin (F.d x)) k),
      (∀ x y, T.le x y → G y * F.M t x y = F.M s x y * G x) → t ≠ s → G x₀ = 0) :
    ¬Statement.IsRepresentationFinite (Linearization (ThinCat T) k) := by
  refine ThinRep.not_isRepresentationFinite (F.rep) (fun t x ↦ ?_) (fun t ↦ ?_) ?_ ?_
  · change FiniteDimensional k (Fin (F.d x) → k)
    infer_instance
  · refine ⟨x₀, ?_⟩
    change Nontrivial (Fin (F.d x₀) → k)
    have : Nonempty (Fin (F.d x₀)) := ⟨⟨0, hx₀⟩⟩
    infer_instance
  · intro t f hf
    obtain ⟨c, hc⟩ := hend t (F.mat f) (F.toMatrix'_natural f hf)
    refine ⟨c, fun x ↦ ?_⟩
    have e := congrArg Matrix.toLin' (hc x)
    rw [mat, Matrix.toLin'_toMatrix', map_smul, Matrix.toLin'_one] at e
    exact LinearMap.ext fun m ↦ LinearMap.congr_fun e m
  · intro t s f hf hbij
    by_contra hne
    have h0 := hhom t s (F.mat f) (F.toMatrix'_natural f hf) hne
    have e := congrArg Matrix.toLin' h0
    rw [mat, Matrix.toLin'_toMatrix', map_zero] at e
    have : Nonempty (Fin (F.d x₀)) := ⟨⟨0, hx₀⟩⟩
    obtain ⟨m, hm⟩ := exists_ne (0 : Fin (F.d x₀) → k)
    refine hm ((hbij x₀).1 ?_)
    have h1 : F.toPi (f x₀) m = 0 := by rw [e]; rfl
    exact h1.trans (map_zero (f x₀)).symm

end MatFam

open Classical in
/-- Parameters avoiding the roots of a nonzero polynomial form an infinite type. -/
lemma infinite_nonroot [Infinite k] (p : Polynomial k) (hp : p ≠ 0) :
    Infinite {t : k // p.eval t ≠ 0} := by
  have hfin : {t : k | p.eval t = 0}.Finite :=
    (p.roots.toFinset.finite_toSet).subset fun t ht ↦ by
      simpa [Polynomial.mem_roots hp] using ht
  exact (hfin.infinite_compl).to_subtype

lemma eq_of_mul_sub_eq_zero {a b c : k} (hc : c ≠ 0) (h : c * (a - b) = 0) : a = b :=
  sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hc)

lemma eq_zero_of_mul_eq_zero {a c : k} (hc : c ≠ 0) (h : c * a = 0) : a = 0 :=
  (mul_eq_zero.1 h).resolve_left hc

end RayCat

end LargeIndecomposable
