module

public import LargeIndecomposable.KroneckerModules.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# The subcategories `D` and `C`

The simple Kronecker modules `S₊` and `S₋`, the description (2.2) of `D`,
Lemma 2.2(2) and (3), and the splitting (2.3) of a module of `D` into a module
of `C` and copies of `S₋`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair WalkingParallelPairHom

universe u

variable {k : Type u} [Field k]

namespace Kron

variable (k) in
/-- The simple injective Kronecker module `S₊ = (k, 0; 0, 0)`. -/
abbrev Splus : Kron k := Kron.mk (ModuleCat.of k k) (ModuleCat.of k PUnit.{u + 1}) 0 0

variable (k) in
/-- The simple projective Kronecker module `S₋ = (0, k; 0, 0)`. -/
abbrev Sminus : Kron k := Kron.mk (ModuleCat.of k PUnit.{u + 1}) (ModuleCat.of k k) 0 0

end Kron

/-- (2.2): `T ∈ D` if and only if `Hom(S₊, T) = 0`. -/
theorem inD_iff_hom_Splus (X : Kron k) : InD X ↔ ∀ f : Kron.Splus k ⟶ X, f = 0 := by
  rw [inD_iff]
  constructor
  · intro h f
    refine Kron.hom_ext ?_ ?_
    · ext
      refine h _ ?_ ?_
      · rw [← Kron.a_apply]
        exact (congrArg _ (Subsingleton.elim (α := PUnit.{u + 1}) _ 0)).trans (map_zero _)
      · rw [← Kron.b_apply]
        exact (congrArg _ (Subsingleton.elim (α := PUnit.{u + 1}) _ 0)).trans (map_zero _)
    · ext x
      exact (congrArg _ (Subsingleton.elim (α := PUnit.{u + 1}) x 0)).trans (map_zero _)
  · intro h v ha hb
    let f : Kron.Splus k ⟶ X := Kron.homMk (ModuleCat.ofHom (LinearMap.toSpanSingleton k _ v)) 0
      (by ext; simp [ha]) (by ext; simp [hb])
    have := congrArg (fun f : Kron.Splus k ⟶ X ↦ (f.app zero).hom (1 : k)) (h f)
    simpa [f] using this

/-- `T ∈ C` if and only if `T ∈ D` and `Hom(T, S₋) = 0`. -/
theorem inC_iff_hom_Sminus (X : Kron k) :
    InC X ↔ InD X ∧ ∀ f : X ⟶ Kron.Sminus k, f = 0 := by
  unfold InC
  refine and_congr_right fun _ ↦ ?_
  constructor
  · intro h f
    refine Kron.hom_ext (by ext x; exact Subsingleton.elim (α := PUnit.{u + 1}) _ _) ?_
    ext w
    have hw : w ∈ LinearMap.range X.a.hom ⊔ LinearMap.range X.b.hom := h ▸ trivial
    obtain ⟨x, ⟨v, rfl⟩, y, ⟨v', rfl⟩, rfl⟩ := Submodule.mem_sup.1 hw
    change (f.app one).hom (X.a.hom v + X.b.hom v') = 0
    rw [map_add, Kron.a_apply, Kron.b_apply]
    simp
  · intro h
    by_contra hne
    obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    let f : X ⟶ Kron.Sminus k := Kron.homMk 0 (ModuleCat.ofHom φ)
      (by ext v; exact hle (Submodule.mem_sup_left ⟨v, rfl⟩))
      (by ext v; exact hle (Submodule.mem_sup_right ⟨v, rfl⟩))
    exact hφ (congrArg (fun f : X ⟶ Kron.Sminus k ↦ (f.app one).hom) (h f))

lemma inD_of_iso {X Y : Kron k} (e : X ≅ Y) (hX : InD X) : InD Y := by
  rw [inD_iff_hom_Splus] at hX ⊢
  intro f
  simpa using congrArg (· ≫ e.hom) (hX (f ≫ e.inv))

lemma inC_of_iso {X Y : Kron k} (e : X ≅ Y) (hX : InC X) : InC Y := by
  rw [inC_iff_hom_Sminus] at hX ⊢
  refine ⟨inD_of_iso e hX.1, fun f ↦ ?_⟩
  simpa using congrArg (e.inv ≫ ·) (hX.2 (e.hom ≫ f))

lemma inD_of_isZero {X : Kron k} (hX : IsZero X) : InD X :=
  (inD_iff_hom_Splus X).2 fun _ ↦ hX.eq_of_tgt _ _

lemma inC_of_isZero {X : Kron k} (hX : IsZero X) : InC X :=
  (inC_iff_hom_Sminus X).2 ⟨inD_of_isZero hX, fun _ ↦ hX.eq_of_src _ _⟩

/-! ### Lemma 2.2(2) -/

instance : HasFiniteBiproducts (Kron k) := Abelian.hasFiniteBiproducts

/-- Lemma 2.2(2): `D` is closed under submodules. -/
lemma inD_of_mono' {X Y : Kron k} (hY : InD Y) (f : X ⟶ Y) [Mono f] : InD X :=
  inD_of_mono hY f <| (ModuleCat.mono_iff_injective _).1 inferInstance

/-- Lemma 2.2(2): `D` is closed under binary direct sums. -/
lemma inD_biprod {X Y : Kron k} (hX : InD X) (hY : InD Y) : InD (X ⊞ Y) := by
  rw [inD_iff_hom_Splus] at hX hY ⊢
  intro f
  rw [← Category.comp_id f, ← biprod.total, Preadditive.comp_add, ← Category.assoc,
    ← Category.assoc, hX (f ≫ biprod.fst), hY (f ≫ biprod.snd)]
  simp

/-- Lemma 2.2(2): `C` is closed under binary direct sums. -/
lemma inC_biprod {X Y : Kron k} (hX : InC X) (hY : InC Y) : InC (X ⊞ Y) := by
  refine (inC_iff_hom_Sminus _).2 ⟨inD_biprod hX.1 hY.1, fun f ↦ ?_⟩
  rw [inC_iff_hom_Sminus] at hX hY
  rw [← Category.id_comp f, ← biprod.total, Preadditive.add_comp, Category.assoc,
    Category.assoc, hX.2 (biprod.inl ≫ f), hY.2 (biprod.inr ≫ f)]
  simp

/-- Lemma 2.2(2): `C` is closed under finite direct sums. -/
lemma inC_biproduct {ι : Type} [Finite ι] (X : ι → Kron k) (hX : ∀ i, InC (X i)) :
    InC (⨁ X) := by
  have := Fintype.ofFinite ι
  rw [inC_iff_hom_Sminus]
  simp only [inC_iff_hom_Sminus] at hX
  refine ⟨(inD_iff_hom_Splus _).2 fun f ↦ ?_, fun f ↦ ?_⟩
  · rw [← Category.comp_id f, ← biproduct.total, Preadditive.comp_sum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [← Category.assoc, (inD_iff_hom_Splus _).1 (hX i).1 (f ≫ biproduct.π X i)]
    simp
  · rw [← Category.id_comp f, ← biproduct.total, Preadditive.sum_comp]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [Category.assoc, (hX i).2 (biproduct.ι X i ≫ f)]
    simp

/-! ### Lemma 2.2(3): the submodules `T_{V₀}` -/

namespace Kron.Sub

variable {X : Kron k}

/-- The subrepresentation `T_{V₀} = (V₀, a(V₀) + b(V₀); a, b)` of Lemma 2.2(3). -/
def ofV (V₀ : Submodule k X.V) : Kron.Sub X where
  V := V₀
  W := V₀.map X.a.hom ⊔ V₀.map X.b.hom
  map_a v hv := Submodule.mem_sup_left ⟨v, hv, rfl⟩
  map_b v hv := Submodule.mem_sup_right ⟨v, hv, rfl⟩

lemma ofV_mono {V₀ V₁ : Submodule k X.V} (h : V₀ ≤ V₁) : ofV V₀ ≤ ofV V₁ :=
  ⟨h, sup_le_sup (Submodule.map_mono h) (Submodule.map_mono h)⟩

lemma isFin_ofV (V₀ : Submodule k X.V) [FiniteDimensional k V₀] : (ofV V₀).IsFin :=
  ⟨inferInstanceAs (FiniteDimensional k V₀), Submodule.finiteDimensional_sup _ _⟩

/-- Lemma 2.2(3): for `X ∈ D`, the subrepresentations `T_{V₀}` belong to `C`. -/
lemma inC_ofV (hX : InD X) (V₀ : Submodule k X.V) : InC (ofV V₀).toKron := by
  refine ⟨(ofV V₀).inD hX, ?_⟩
  rw [eq_top_iff]
  rintro ⟨w, hw⟩ -
  obtain ⟨x, ⟨v, hv, rfl⟩, y, ⟨v', hv', rfl⟩, rfl⟩ := Submodule.mem_sup.1 hw
  refine Submodule.mem_sup.2 ⟨_, ⟨⟨v, hv⟩, rfl⟩, _, ⟨⟨v', hv'⟩, rfl⟩, rfl⟩

/-- Lemma 2.2(3): for `X ∈ C`, every finite-dimensional subrepresentation lies
in some `T_{V₀}` with `V₀` finite-dimensional. -/
lemma exists_le_ofV (hX : InC X) (U : Kron.Sub X) (hU : U.IsFin) :
    ∃ V₀ : Submodule k X.V, FiniteDimensional k V₀ ∧ U ≤ ofV V₀ := by
  obtain ⟨hV, hW⟩ := hU
  let B := Module.finBasis k U.W
  have hpre : ∀ i, ∃ p : X.V × X.V, X.a.hom p.1 + X.b.hom p.2 = (B i : X.W) := by
    intro i
    have hw : (B i : X.W) ∈ LinearMap.range X.a.hom ⊔ LinearMap.range X.b.hom := hX.2 ▸ trivial
    obtain ⟨_, ⟨v, rfl⟩, _, ⟨v', rfl⟩, h⟩ := Submodule.mem_sup.1 hw
    exact ⟨(v, v'), h⟩
  choose p hp using hpre
  let V₁ : Submodule k X.V :=
    Submodule.span k (Set.range (fun i ↦ (p i).1) ∪ Set.range (fun i ↦ (p i).2))
  have hV₁ : FiniteDimensional k V₁ :=
    FiniteDimensional.span_of_finite k ((Set.finite_range _).union (Set.finite_range _))
  refine ⟨U.V ⊔ V₁, Submodule.finiteDimensional_sup _ _, le_sup_left, ?_⟩
  change U.W ≤ (U.V ⊔ V₁).map X.a.hom ⊔ (U.V ⊔ V₁).map X.b.hom
  have hspan : U.W = Submodule.span k (Set.range fun i ↦ (B i : X.W)) := by
    rw [Set.range_comp' Subtype.val B]
    change _ = Submodule.span k (U.W.subtype '' _)
    rw [← Submodule.map_span, B.span_eq, Submodule.map_top, Submodule.range_subtype]
  rw [hspan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  change (B i : X.W) ∈ _
  rw [← hp i]
  exact Submodule.add_mem_sup
    ⟨_, Submodule.mem_sup_right (Submodule.subset_span (Or.inl ⟨i, rfl⟩)), rfl⟩
    ⟨_, Submodule.mem_sup_right (Submodule.subset_span (Or.inr ⟨i, rfl⟩)), rfl⟩

end Kron.Sub

/-- Lemma 2.2(3): for `X ∈ C`, the finite-dimensional subrepresentations
`T_{V₀}` are cofinal in `Kron.FinSub X`. -/
lemma Kron.FinSub.exists_le_ofV {X : Kron k} (hX : InC X) (U : Kron.FinSub X) :
    ∃ (V₀ : Submodule k X.V) (_ : FiniteDimensional k V₀),
      U ≤ (⟨Kron.Sub.ofV V₀, Kron.Sub.isFin_ofV V₀⟩ : Kron.FinSub X) := by
  obtain ⟨V₀, h, hle⟩ := Kron.Sub.exists_le_ofV hX U.1 U.2
  exact ⟨V₀, h, hle⟩

/-! ### Direct sums of copies of `S₋` -/

namespace Kron

variable (k) in
/-- The Kronecker module `S₋^(I) = (0, k^(I); 0, 0)`. -/
abbrev sumSminus (I : Type u) : Kron k :=
  Kron.mk (ModuleCat.of k PUnit.{u + 1}) (ModuleCat.of k (I →₀ k)) 0 0

lemma ext_of_source_punit {Y : Kron k} {I : Type u} {f g : sumSminus k I ⟶ Y}
    (h : f.app one = g.app one) : f = g :=
  Kron.hom_ext (by ext x; rw [Subsingleton.elim (α := PUnit.{u + 1}) x 0, map_zero, map_zero]) h

/-- The inclusion of the `i`-th copy of `S₋` into `S₋^(I)`. -/
def ιSminus (I : Type u) (i : I) : Sminus k ⟶ sumSminus k I :=
  Kron.homMk 0 (ModuleCat.ofHom (Finsupp.lsingle i)) (by ext; simp) (by ext; simp)

/-- `S₋^(I)` is the coproduct of `I` copies of `S₋`. -/
def isColimitSumSminus (I : Type u) :
    IsColimit (Cofan.mk (sumSminus k I) (ιSminus (k := k) I)) :=
  Cofan.IsColimit.mk _
    (fun s ↦ Kron.homMk 0
      (ModuleCat.ofHom (Finsupp.linearCombination k fun i ↦ ((s.inj i).app one).hom (1 : k)))
      (by ext; simp) (by ext; simp))
    (fun s i ↦ by
      refine Kron.hom_ext ?_ ?_
      · ext x; rw [Subsingleton.elim (α := PUnit.{u + 1}) x 0, map_zero, map_zero]
      · ext; simp [ιSminus])
    (fun s m hm ↦ ext_of_source_punit <| by
      refine ModuleCat.hom_ext (Finsupp.lhom_ext' fun i ↦ LinearMap.ext_ring ?_)
      have := congrArg (fun f : Sminus k ⟶ s.pt ↦ (f.app one).hom (1 : k)) (hm i)
      simpa [ιSminus] using this)

/-- `S₋^(I) ≅ ∐_I S₋`. -/
def sumSminusIso (I : Type u) : sumSminus k I ≅ ∐ fun _ : I ↦ Sminus k :=
  (colimit.isoColimitCocone ⟨_, isColimitSumSminus I⟩).symm

end Kron

/-! ### The splitting (2.3) -/

namespace Kron.Splitting

variable (T : Kron k)

/-- The subspace `a(V) + b(V)` of `W`. -/
abbrev R : Submodule k T.W := (Kron.Sub.ofV (⊤ : Submodule k T.V)).W

/-- A chosen complement of `a(V) + b(V)` in `W`. -/
def Q : Submodule k T.W := (Submodule.exists_isCompl (R T)).choose

lemma isCompl : IsCompl (R T) (Q T) := (Submodule.exists_isCompl (R T)).choose_spec

/-- The index set of a basis of the complement. -/
abbrev I : Type u := Module.Free.ChooseBasisIndex k (Q T)

/-- A basis of the complement. -/
abbrev basis : Module.Basis (I T) k (Q T) := Module.Free.chooseBasis k (Q T)

/-- The summand `T₀ = (V, a(V) + b(V); a, b)`. -/
abbrev T₀ : Kron k := (Kron.Sub.ofV (⊤ : Submodule k T.V)).toKron

lemma mem_R_a (v : T.V) : T.a.hom v ∈ R T := Submodule.mem_sup_left ⟨v, trivial, rfl⟩

lemma mem_R_b (v : T.V) : T.b.hom v ∈ R T := Submodule.mem_sup_right ⟨v, trivial, rfl⟩

/-- The binary bicone `T₀ → T ← S₋^(I)`. -/
def bicone : BinaryBicone (T₀ T) (Kron.sumSminus k (I T)) where
  pt := T
  fst := Kron.homMk (ModuleCat.ofHom (LinearMap.id.codRestrict _ fun _ ↦ trivial))
    (ModuleCat.ofHom ((R T).projectionOnto (Q T) (isCompl T)))
    (by
      ext v
      exact Subtype.ext (by simp [Submodule.projection_apply_of_mem_left _ (mem_R_a T v)]; rfl))
    (by
      ext v
      exact Subtype.ext (by simp [Submodule.projection_apply_of_mem_left _ (mem_R_b T v)]; rfl))
  snd := Kron.homMk 0
    (ModuleCat.ofHom ((basis T).repr.toLinearMap ∘ₗ (Q T).projectionOnto (R T) (isCompl T).symm))
    (by ext v; simp [Submodule.projectionOnto_apply_of_mem_right _ (mem_R_a T v)])
    (by ext v; simp [Submodule.projectionOnto_apply_of_mem_right _ (mem_R_b T v)])
  inl := Kron.Sub.ι _
  inr := Kron.homMk 0 (ModuleCat.ofHom ((Q T).subtype ∘ₗ (basis T).repr.symm.toLinearMap))
    (by ext; simp) (by ext; simp)
  inl_fst := by
    apply Kron.hom_ext
    · ext v; rfl
    · ext w; exact Submodule.projectionOnto_apply_left (isCompl T) w
  inl_snd := by
    apply Kron.hom_ext
    · ext v; rfl
    · ext w
      simp [Kron.Sub.ι]
      exact w.2
  inr_fst := by
    apply Kron.ext_of_source_punit
    ext x
    exact Subtype.ext (by simp)
  inr_snd := by
    apply Kron.ext_of_source_punit
    ext x : 2
    simp [Submodule.projectionOnto_apply_of_mem_left]

lemma total : (bicone T).fst ≫ (bicone T).inl + (bicone T).snd ≫ (bicone T).inr = 𝟙 T := by
  apply Kron.hom_ext
  · rw [NatTrans.app_add]
    ext v
    erw [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_zero, LinearMap.zero_apply, add_zero]
    rfl
  · rw [NatTrans.app_add]
    ext w
    erw [ModuleCat.hom_add, LinearMap.add_apply]
    refine Eq.trans (congrArg₂ (· + ·) rfl ?_)
      (Submodule.projection_add_projection_eq_self (isCompl T) w)
    change ((basis T).repr.symm ((basis T).repr _) : T.W) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl

lemma inC_T₀ (hT : InD T) : InC (T₀ T) := Kron.Sub.inC_ofV hT ⊤

/-- The splitting `T ≅ T₀ ⊕ S₋^(I)` with `T₀ = (V, a(V) + b(V); a, b)`. -/
def isoBiprod : T ≅ T₀ T ⊞ Kron.sumSminus k (I T) :=
  biprod.uniqueUpToIso _ _ (isBinaryBilimitOfTotal (bicone T) (total T))

end Kron.Splitting

/-- (2.3): every `T ∈ D` splits as `T ≅ T₀ ⊕ S₋^(I)` with `T₀ ∈ C`. -/
theorem exists_iso_biprod_sigma_Sminus (T : Kron k) (hT : InD T) :
    ∃ (T₀ : Kron k) (I : Type u), InC T₀ ∧ Nonempty (T ≅ T₀ ⊞ ∐ fun _ : I ↦ Kron.Sminus k) :=
  ⟨_, _, Kron.Splitting.inC_T₀ T hT,
    ⟨Kron.Splitting.isoBiprod T ≪≫ biprod.mapIso (Iso.refl _) (Kron.sumSminusIso _)⟩⟩

lemma Kron.id_Sminus_ne_zero : 𝟙 (Kron.Sminus k) ≠ 0 := by
  intro h
  have := congrArg (fun f : Kron.Sminus k ⟶ Kron.Sminus k ↦ (f.app one).hom (1 : k)) h
  simp at this

/-- The converse remark after (2.3): a module with a direct summand `S₋` is not in `C`. -/
theorem not_inC_of_iso_biprod_Sminus {T T' : Kron k} (e : T ≅ T' ⊞ Kron.Sminus k) : ¬ InC T := by
  intro hT
  apply Kron.id_Sminus_ne_zero (k := k)
  rw [← biprod.inr_snd, ← Category.id_comp biprod.snd, ← e.inv_hom_id, Category.assoc,
    ((inC_iff_hom_Sminus T).1 hT).2 (e.hom ≫ biprod.snd)]
  simp

/-! ### Indecomposable objects of `D` -/

lemma IsIndecomposableKron.eq_zero_or_eq_id_of_iso {X : D k} (hX : IsIndecomposableKron X)
    {Y : Kron k} (e : X.obj ≅ Y) (p : Y ⟶ Y) (hp : p ≫ p = p) : p = 0 ∨ p = 𝟙 Y := by
  let q : X ⟶ X := ObjectProperty.homMk (e.hom ≫ p ≫ e.inv)
  have hq : q ≫ q = q := by
    ext1
    simp [q, reassoc_of% hp]
  have hpq : p = e.inv ≫ q.hom ≫ e.hom := by simp [q]
  rcases hX.2 q hq with h | h
  · left; rw [hpq, h]; simp
  · right; rw [hpq, h]; simp

lemma IsIndecomposableKron.isZero_or_isZero_of_iso_biprod {X : D k}
    (hX : IsIndecomposableKron X) {A B : Kron k} (e : X.obj ≅ A ⊞ B) : IsZero A ∨ IsZero B := by
  rcases IsIndecomposableKron.eq_zero_or_eq_id_of_iso hX e (biprod.fst ≫ biprod.inl) (by simp)
    with h | h
  · left
    rw [IsZero.iff_id_eq_zero, ← biprod.inl_fst, ← Category.comp_id biprod.fst,
      ← biprod.inl_fst (X := A) (Y := B), ← Category.assoc, ← Category.assoc,
      Category.assoc biprod.inl, h]
    simp
  · right
    rw [IsZero.iff_id_eq_zero, ← biprod.inr_snd, ← Category.id_comp biprod.snd, ← h]
    simp

lemma Kron.isZero_sumSminus_of_isEmpty (I : Type u) [IsEmpty I] : IsZero (Kron.sumSminus k I) := by
  rw [IsZero.iff_id_eq_zero]
  apply Kron.ext_of_source_punit
  ext x
  exact Subsingleton.elim (α := I →₀ k) _ _

/-- `S₋^(I) ≅ S₋` when `I` has exactly one element. -/
def Kron.sumSminusIsoSminus {I : Type u} [Subsingleton I] (i : I) :
    Kron.sumSminus k I ≅ Kron.Sminus k :=
  parallelPair.ext (Iso.refl _)
    (LinearEquiv.toModuleIso (Finsupp.uniqueLinearEquiv k k i)) (by simp) (by simp)

/-- After (2.3): an indecomposable object of `D` either lies in `C` or is
isomorphic to `S₋`. -/
theorem inC_or_iso_Sminus_of_isIndecomposable {X : D k} (hX : IsIndecomposableKron X) :
    InC X.obj ∨ Nonempty (X.obj ≅ Kron.Sminus k) := by
  open Kron.Splitting in
  rcases IsIndecomposableKron.isZero_or_isZero_of_iso_biprod hX (isoBiprod X.obj) with h | h
  · right
    let e := isoBiprod X.obj ≪≫ (isoZeroBiprod h).symm
    have hne : Nonempty (I X.obj) := by
      by_contra hI
      rw [not_nonempty_iff] at hI
      exact hX.1 ((Kron.isZero_sumSminus_of_isEmpty _).of_iso e)
    have hsub : Subsingleton (I X.obj) := by
      refine ⟨fun i j ↦ by_contra fun hij ↦ ?_⟩
      let p : Kron.sumSminus k (I X.obj) ⟶ Kron.sumSminus k (I X.obj) :=
        Kron.homMk 0 (ModuleCat.ofHom (Finsupp.lsingle i ∘ₗ Finsupp.lapply i))
          (by ext; simp) (by ext; simp)
      have hp : p ≫ p = p := by
        apply Kron.ext_of_source_punit
        ext x : 2
        simp [p]
      rcases IsIndecomposableKron.eq_zero_or_eq_id_of_iso hX e p hp with h | h
      · have := congrArg (fun f : _ ⟶ _ ↦ (f.app one).hom (Finsupp.single i (1 : k))) h
        simp [p] at this
      · have := congrArg (fun f : _ ⟶ _ ↦ (f.app one).hom (Finsupp.single j (1 : k))) h
        simp [p, Ne.symm hij] at this
        exact Finsupp.single_ne_zero.2 one_ne_zero this.symm
    exact ⟨e ≪≫ Kron.sumSminusIsoSminus (Classical.arbitrary _)⟩
  · left
    exact inC_of_iso (isoBiprod X.obj ≪≫ (isoBiprodZero h).symm).symm (inC_T₀ _ X.2)

end LargeIndecomposable
