module

public import LargeIndecomposable.RepresentationEmbeddings.CoveringConstruction.ZeroVertex
public import LargeIndecomposable.RepresentationEmbeddings.WalkConstruction.PdEmbedding
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Perm.Basic

/-!
# The covering construction as a controlled embedding

Alternative (2) of Theorem 3.14 in data form. A Galois covering `R → A` with
torsion-free group `G` enters only through the finite full subquiver `D` of
the quiver of `R` on the support `Σ = supp L(S₊) ∪ supp L(S₋)`, the
restriction `p : D → Q` of the covering map, and the action of `G` on the
objects of `R` (`CoverData`): `G` acts freely, it is torsion-free, and two
arrows of `D` with the same label are `G`-translates of each other. Grouping
block positions `(γ x, x)` by `γ ∈ G` gives the classes of Proposition 4.5
(`CoverData.blockClasses`); a class `γ ≠ 1` misses a column because `γ Σ ≠ Σ`.

`CoveringData k A` adds an exact fully faithful functor `L` from Kronecker
modules of any dimension to representations of `D`, with every vertex of `D` in
the support of `L(S₊)` or `L(S₋)`, and a presentation `kQ → A` whose kernel
acts by zero on `p_*L(T)`. By the facts about `S₋`
(`RepresentationEmbeddings/CoveringConstruction/SimpleInjectiveFacts.lean`) it
gives the data of Theorem 5.2.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair FinQuiver Rep

universe u

namespace Covering

/-- The finite part of a Galois covering with torsion-free group: a free action
of `G` on the objects `R₀`, an embedding `ι` of the vertices of `D`, and the
condition that equally labelled arrows of `D` are translates of each other. -/
structure CoverData {D Q : FinQuiver} (p : FinQuiver.Hom D Q) where
  /-- The group of the covering. -/
  G : Type
  [group : Group G]
  torsionFree : ∀ g : G, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1
  /-- The objects of the covering. -/
  R₀ : Type
  [act : MulAction G R₀]
  free : ∀ (g : G) (x : R₀), g • x = x → g = 1
  /-- The vertices of `D` as objects of the covering. -/
  ι : D.V → R₀
  ι_inj : Function.Injective ι
  /-- Fibres of `p` lie in `G`-orbits. -/
  fibre : ∀ x y : D.V, p.vert x = p.vert y → ∃ g : G, ι y = g • ι x
  arrows : ∀ α β : D.A, p.arr α = p.arr β →
    ∃ g : G, ι (D.src β) = g • ι (D.src α) ∧ ι (D.tgt β) = g • ι (D.tgt α)

attribute [instance] CoverData.group CoverData.act

namespace CoverData

variable {D Q : FinQuiver} {p : FinQuiver.Hom D Q} (C : CoverData p)

lemma smul_unique {g h : C.G} {x : C.R₀} (e : g • x = h • x) : g = h := by
  have := C.free (h⁻¹ * g) x (by rw [mul_smul, e, ← mul_smul, inv_mul_cancel, one_smul])
  rw [← mul_left_cancel_iff (a := h⁻¹), this, inv_mul_cancel]

/-- Relative form: a nontrivial element moves some vertex of a nonempty set `P`
out of `P`. -/
lemma exists_not_mem_of {g : C.G} (hg : g ≠ 1) (P : D.V → Prop) {c₀ : D.V} (hc₀ : P c₀) :
    ∃ c, P c ∧ ∀ j, P j → C.ι j ≠ g • C.ι c := by
  by_contra H
  push Not at H
  have H' : ∀ c : {c // P c}, ∃ j : {c // P c}, C.ι j.1 = g • C.ι c.1 := fun c ↦
    let ⟨j, hj, e⟩ := H c.1 c.2
    ⟨⟨j, hj⟩, e⟩
  choose σ hσ using H'
  have hinj : Function.Injective σ := fun a b h ↦ Subtype.ext
    (C.ι_inj (smul_left_cancel g ((hσ a).symm.trans ((congrArg (C.ι ∘ Subtype.val) h).trans (hσ b)))))
  let e : Equiv.Perm {c // P c} := Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hinj)
  have he : ∀ (m : ℕ) (c : {c // P c}), C.ι ((e ^ m) c).1 = g ^ m • C.ι c.1 := by
    intro m
    induction m with
    | zero => intro c; simp
    | succ m ih =>
      intro c
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', mul_smul, ← ih]
      exact hσ _
  have hpos := orderOf_pos e
  have := he (orderOf e) ⟨c₀, hc₀⟩
  rw [pow_orderOf_eq_one, Equiv.Perm.one_apply] at this
  exact C.torsionFree g hg _ hpos (C.free _ _ this.symm)

open Classical in
/-- The class of a position `(j, i)`: the element `γ` with `j = γ i`, or the
position itself if there is none. -/
def gcls (a : D.V × D.V) : C.G ⊕ (D.V × D.V) :=
  if h : ∃ g : C.G, C.ι a.1 = g • C.ι a.2 then Sum.inl h.choose else Sum.inr a

lemma gcls_of {a : D.V × D.V} {g : C.G} (h : C.ι a.1 = g • C.ι a.2) : C.gcls a = Sum.inl g := by
  have h' : ∃ g : C.G, C.ι a.1 = g • C.ι a.2 := ⟨g, h⟩
  rw [gcls, dite_eq_left h']
  congr 1
  exact C.smul_unique (h'.choose_spec.symm.trans h)

lemma of_gcls_inl {a : D.V × D.V} {g : C.G} (h : C.gcls a = Sum.inl g) :
    C.ι a.1 = g • C.ι a.2 := by
  unfold gcls at h
  split_ifs at h with h'
  · cases h; exact h'.choose_spec

lemma of_gcls_inr {a b : D.V × D.V} (h : C.gcls a = Sum.inr b) : a = b := by
  unfold gcls at h
  split_ifs at h with h'
  · cases h; rfl

/-- A nontrivial element moves some vertex out of `D`: otherwise it would
permute the finite set of vertices, and a power would fix a vertex. -/
lemma exists_not_mem {g : C.G} (hg : g ≠ 1) (c₀ : D.V) : ∃ c, ∀ j, C.ι j ≠ g • C.ι c := by
  by_contra H
  push Not at H
  choose σ hσ using H
  have hinj : Function.Injective σ := fun a b h ↦
    C.ι_inj (smul_left_cancel g ((hσ a).symm.trans ((congrArg C.ι h).trans (hσ b))))
  let e : Equiv.Perm D.V := Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hinj)
  have he : ∀ (m : ℕ) (c : D.V), C.ι ((e ^ m) c) = g ^ m • C.ι c := by
    intro m
    induction m with
    | zero => intro c; simp
    | succ m ih =>
      intro c
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', mul_smul, ← ih]
      exact hσ _
  have hpos := orderOf_pos e
  have := he (orderOf e) c₀
  rw [pow_orderOf_eq_one, Equiv.Perm.one_apply] at this
  exact C.torsionFree g hg _ hpos (C.free _ _ this.symm)

lemma zeroCol_aux (a₀ : D.V × D.V) : ∃ c, ∀ j, C.gcls (j, c) = C.gcls a₀ → j = c := by
  rcases e : C.gcls a₀ with g | b
  · by_cases hg : g = 1
    · subst hg
      refine ⟨a₀.2, fun j hj ↦ ?_⟩
      exact C.ι_inj ((C.of_gcls_inl hj).trans (one_smul _ _))
    · obtain ⟨c, hc⟩ := C.exists_not_mem hg a₀.2
      exact ⟨c, fun j hj ↦ absurd (C.of_gcls_inl hj) (hc j)⟩
  · exact ⟨b.1, fun j hj ↦ congrArg Prod.fst (C.of_gcls_inr hj)⟩

/-- Relative zero column: for a nonempty set `P` of vertices and a class, some
`c ∈ P` has no position `(j, c)` of that class with `j ∈ P`, `j ≠ c`, in the
same fibre. -/
lemma zeroCol_rel (P : D.V → Prop) {c₀ : D.V} (hc₀ : P c₀) (a₀ : D.V × D.V) :
    ∃ c, P c ∧ ∀ j, P j → C.gcls (j, c) = C.gcls a₀ → p.vert j = p.vert c → j = c := by
  rcases e : C.gcls a₀ with g | b
  · by_cases hg : g = 1
    · subst hg
      exact ⟨c₀, hc₀, fun j _ hj _ ↦ C.ι_inj ((C.of_gcls_inl hj).trans (one_smul _ _))⟩
    · obtain ⟨c, hc, hcn⟩ := C.exists_not_mem_of hg P hc₀
      exact ⟨c, hc, fun j hj hjc _ ↦ absurd (C.of_gcls_inl hjc) (hcn j hj)⟩
  · refine ⟨c₀, hc₀, fun j _ hj hp ↦ ?_⟩
    obtain ⟨g, hg⟩ := C.fibre c₀ j hp.symm
    rw [C.gcls_of hg] at hj
    cases hj

open Classical in
/-- The classes of block positions of Proposition 4.5. -/
def blockClasses : PushDown.BlockClasses p where
  ι := Set.range C.gcls
  fin := Set.fintypeRange _
  cls a := ⟨C.gcls a, a, rfl⟩
  sat α β h := by
    obtain ⟨g, hs, ht⟩ := C.arrows α β h
    refine Subtype.ext ?_
    change C.gcls _ = C.gcls _
    rw [C.gcls_of (g := g⁻¹) (by rw [hs, ← mul_smul, inv_mul_cancel, one_smul]),
      C.gcls_of (g := g⁻¹) (by rw [ht, ← mul_smul, inv_mul_cancel, one_smul])]
  diag a b h ha := by
    have h1 : C.gcls a = Sum.inl 1 := C.gcls_of (by rw [ha, one_smul])
    have h2 : C.gcls b = Sum.inl 1 := (congrArg Subtype.val h).symm.trans h1
    exact C.ι_inj ((C.of_gcls_inl h2).trans (one_smul _ _))
  col j j' i _ _ h := by
    have h' : C.gcls (j, i) = C.gcls (j', i) := congrArg Subtype.val h
    rcases e : C.gcls (j, i) with g | b
    · have e' := h'.symm.trans e
      exact C.ι_inj ((C.of_gcls_inl e).trans (C.of_gcls_inl e').symm)
    · have e' := h'.symm.trans e
      exact congrArg Prod.fst ((C.of_gcls_inr e).trans (C.of_gcls_inr e').symm)
  zeroCol κ := by
    obtain ⟨_, a₀, rfl⟩ := κ
    obtain ⟨c, hc⟩ := C.zeroCol_aux a₀
    exact ⟨c, fun j hj ↦ hc j (congrArg Subtype.val hj)⟩

end CoverData

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]

variable (k A) in
/-- The data of alternative (2) of Theorem 3.14, apart from the
representation-embedding property. -/
structure CoveringData where
  /-- The full subquiver of the covering on the support `Σ`. -/
  D : FinQuiver
  /-- The quiver of the presentation. -/
  Q : FinQuiver
  /-- The restriction of the covering map. -/
  p : FinQuiver.Hom D Q
  locInj : p.LocallyInjective
  /-- The group action of the covering. -/
  C : CoverData p
  /-- The functor `L`. -/
  L : Kron k ⥤ Rep k D
  [additive : L.Additive]
  hL : L.FullyFaithful
  map_smul : ∀ {T U : Kron k} (c : k) (f : T ⟶ U) (i : D.V),
    (L.map (c • f)).app i = c • (L.map f).app i
  exact : ExactOnKron L
  fin : ∀ (T : Kron k), T.IsFiniteDimensional → ∀ i : D.V, Module.Finite k ((L.obj T).obj i)
  /-- Every vector of `L(T)` comes from `L(U)` for a finite-dimensional `U ⊆ T`. -/
  finitary : ∀ (T : Kron k) (i : D.V) (x : (L.obj T).obj i),
    ∃ U : Kron.FinSub T, x ∈ Set.range ((L.map (Kron.Sub.ι U.1)).app i).hom
  /-- `L` keeps inclusions injective. -/
  incl_injective : ∀ (T : Kron k) (U : Kron.Sub T) (i : D.V),
    Function.Injective ((L.map (Kron.Sub.ι U)).app i).hom
  supp : ∀ c : D.V, Nontrivial ((L.obj (Kron.Splus k)).obj c) ∨
    Nontrivial ((L.obj (Kron.Sminus k)).obj c)
  nonzero : (∃ c, Nontrivial ((L.obj (Kron.Splus k)).obj c)) ∧
    ∃ c, Nontrivial ((L.obj (Kron.Sminus k)).obj c)
  /-- The presentation `kQ → A`. -/
  π : Q.PathAlgebra k →ₐ[k] A
  surj : Function.Surjective π
  /-- `p_*L(T)` is an `A`-module. -/
  kills : ∀ (T : Kron k) (z : Q.PathAlgebra k), π z = 0 → (L.obj T).pdAct p z = 0

attribute [instance] CoveringData.additive

/-- Covering data as push-down data. -/
def CoveringData.toPdData (W : CoveringData k A) : PushDown.PdData k A where
  D := W.D
  Q := W.Q
  p := W.p
  locInj := W.locInj
  B := W.C.blockClasses
  L := DToKron k ⋙ W.L
  hL := (ObjectProperty.fullyFaithfulι _).comp W.hL
  map_smul c f i := W.map_smul c f.hom i
  zero := zeroAtVertex W.L W.exact W.supp
  exact _ _ _ f g h := W.exact _ _ _ f.hom g.hom h
  fin T := W.fin T.obj T.2.2
  finitary T i x := W.finitary T.obj i x
  incl_injective T U i := W.incl_injective T.obj U.1 i
  π := W.π
  surj := W.surj
  kills T := W.kills T.obj

end Covering

end LargeIndecomposable
