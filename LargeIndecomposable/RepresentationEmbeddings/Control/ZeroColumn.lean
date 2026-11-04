module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Block matrices with a zero column

Lemma 4.4 of the manuscript. Let `Ω` be a finite set with a partition, given
by a map `p : Ω → P` whose fibres are the parts, and let `M i` be vector
spaces. Endomorphisms of `⨁ M i = Π i, M i` are block matrices with blocks
`block f j i : M i → M j` (columns are indexed by sources). The diagonal
part `diag f` keeps the blocks `block f i i`.

For a unital subalgebra `E` preserving the part-subspaces, with

1. `diag E ⊆ E`,
2. every coordinate map `E₀ = diag E → End(M i)` injective,
3. `N = ker (diag|_E)` spanned by elements of `N` with at most one nonzero
   block in each column and with a zero column,

`diag : E → E₀` is a split algebra surjection, `N` is a two-sided ideal, and
every product of `m` elements of `N` vanishes, `m` the largest part size.

The proof needs neither `M i ≠ 0` nor `Ω ≠ ∅`; the core lemmas are stated
without them, and `zeroColumn` states the lemma with the manuscript's hypotheses.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

namespace ZeroColumn

universe u v w x

variable {k : Type u} [Field k] {Ω : Type v} [DecidableEq Ω]
  {M : Ω → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]

/-- The block `f_{j,i} : M i → M j` of an endomorphism of `Π i, M i`. -/
def block (f : Module.End k (∀ i, M i)) (j i : Ω) : M i →ₗ[k] M j :=
  LinearMap.proj j ∘ₗ f ∘ₗ LinearMap.single k M i

@[simp]
lemma block_apply (f : Module.End k (∀ i, M i)) (j i : Ω) (y : M i) :
    block f j i y = f (Pi.single i y) j := rfl

variable (k M) in
/-- The diagonal part `δ(f)`, retaining only the blocks `f_{i,i}`. -/
def diag : Module.End k (∀ i, M i) →ₗ[k] Module.End k (∀ i, M i) where
  toFun f := LinearMap.pi fun j ↦ block f j j ∘ₗ LinearMap.proj j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma diag_apply (f : Module.End k (∀ i, M i)) (y : ∀ i, M i) (j : Ω) :
    diag k M f y j = f (Pi.single j (y j)) j := rfl

lemma diag_diag (f : Module.End k (∀ i, M i)) : diag k M (diag k M f) = diag k M f := by
  ext y j; simp

lemma diag_one : diag k M (1 : Module.End k (∀ i, M i)) = 1 := by
  ext y j; simp

lemma apply_single_of_diag {r : Module.End k (∀ i, M i)} (hr : diag k M r = r) (i : Ω)
    (y : M i) : r (Pi.single i y) = Pi.single i (r (Pi.single i y) i) := by
  ext j
  by_cases h : j = i
  · subst h; simp
  · rw [← hr]; simp [h]

lemma apply_of_diag {r : Module.End k (∀ i, M i)} (hr : diag k M r = r) (y : ∀ i, M i)
    (j : Ω) : r y j = r (Pi.single j (y j)) j := by
  rw [← hr]; simp

/-- Diagonal multiplication: `δ(r f) = r δ(f)` for diagonal `r`. -/
lemma diag_mul_left {r : Module.End k (∀ i, M i)} (hr : diag k M r = r)
    (f : Module.End k (∀ i, M i)) : diag k M (r * f) = r * diag k M f := by
  ext y j
  rw [diag_apply, Module.End.mul_apply, Module.End.mul_apply, apply_of_diag hr,
    apply_of_diag hr (diag k M f y), diag_apply]

/-- Diagonal multiplication: `δ(f r) = δ(f) r` for diagonal `r`. -/
lemma diag_mul_right {r : Module.End k (∀ i, M i)} (hr : diag k M r = r)
    (f : Module.End k (∀ i, M i)) : diag k M (f * r) = diag k M f * r := by
  ext y j
  rw [diag_apply, Module.End.mul_apply, Module.End.mul_apply, apply_single_of_diag hr,
    diag_apply, apply_of_diag hr y]

/-- A vector concentrated in the summand `M i`. -/
def Conc (y : ∀ i, M i) (i : Ω) : Prop := ∀ j, j ≠ i → y j = 0

lemma Conc.eq_single {y : ∀ i, M i} {i : Ω} (h : Conc y i) : y = Pi.single i (y i) := by
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj, h j hj]

/-- At most one nonzero block in each column. -/
def ColProp (z : Module.End k (∀ i, M i)) : Prop :=
  ∀ i j j', block z j i ≠ 0 → block z j' i ≠ 0 → j = j'

/-- Some column all of whose blocks are zero. -/
def HasZeroCol (z : Module.End k (∀ i, M i)) : Prop :=
  ∃ i, ∀ j, block z j i = 0

lemma conc_apply {z : Module.End k (∀ i, M i)} (hz : ColProp z) {y : ∀ i, M i} {i : Ω}
    (hy : Conc y i) : ∃ j, Conc (z y) j ∧ (z y ≠ 0 → block z j i ≠ 0) := by
  rw [hy.eq_single]
  by_cases h : ∃ j, block z j i ≠ 0
  · obtain ⟨j, hj⟩ := h
    refine ⟨j, fun j' hj' ↦ ?_, fun _ ↦ hj⟩
    have : block z j' i = 0 := by
      by_contra h'
      exact hj' (hz i j' j h' hj)
    rw [← block_apply, this, LinearMap.zero_apply]
  · push Not at h
    have h0 : z (Pi.single i (y i)) = 0 := by
      ext j; rw [← block_apply, h j]; rfl
    exact ⟨i, fun j _ ↦ by rw [h0]; rfl, fun h' ↦ absurd h0 h'⟩

variable {P : Type x}

/-- `E` preserves each subspace `⨁_{i ∈ Ω'} M i`, `Ω'` a part (a fibre of
`p`). -/
def PreservesParts (E : Subalgebra k (Module.End k (∀ i, M i))) (p : Ω → P) : Prop :=
  ∀ f ∈ E, ∀ (π : P) (y : ∀ i, M i), (∀ i, p i ≠ π → y i = 0) → ∀ i, p i ≠ π → f y i = 0

lemma PreservesParts.block_eq_zero {E : Subalgebra k (Module.End k (∀ i, M i))} {p : Ω → P}
    (hE : PreservesParts E p) {f : Module.End k (∀ i, M i)} (hf : f ∈ E) {i j : Ω}
    (h : p j ≠ p i) : block f j i = 0 := by
  ext y
  refine hE f hf (p i) _ (fun l hl ↦ ?_) j h
  have : l ≠ i := fun e ↦ hl (e ▸ rfl)
  simp [this]

variable (E : Subalgebra k (Module.End k (∀ i, M i)))

/-- `E₀ = δ(E)`. -/
abbrev E₀ : Submodule k (Module.End k (∀ i, M i)) :=
  (Subalgebra.toSubmodule E).map (diag k M)

/-- `N = ker(δ|_E)`. -/
abbrev N : Submodule k (Module.End k (∀ i, M i)) :=
  Subalgebra.toSubmodule E ⊓ LinearMap.ker (diag k M)

/-- Products of `n` elements of `S`. -/
def prods (S : Set (Module.End k (∀ i, M i))) (n : ℕ) : Set (Module.End k (∀ i, M i)) :=
  {f | ∃ l : List (Module.End k (∀ i, M i)), l.length = n ∧ (∀ z ∈ l, z ∈ S) ∧ l.prod = f}

omit [DecidableEq Ω] in
lemma list_prod_mem_span_prods (S : Set (Module.End k (∀ i, M i))) :
    ∀ l : List (Module.End k (∀ i, M i)), (∀ z ∈ l, z ∈ Submodule.span k S) →
      l.prod ∈ Submodule.span k (prods S l.length)
  | [], _ => Submodule.subset_span ⟨[], rfl, by simp, rfl⟩
  | a :: l, h => by
    have ha : a ∈ Submodule.span k S := h a (by simp)
    have hl := list_prod_mem_span_prods S l (fun z hz ↦ h z (by simp [hz]))
    rw [List.prod_cons, List.length_cons]
    have := Submodule.mul_mem_mul ha hl
    rw [Submodule.span_mul_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨s, hs, t, ⟨l', hl', hS, rfl⟩, rfl⟩
    refine ⟨s :: l', by simp [hl'], ?_, by simp⟩
    simp only [List.mem_cons]
    rintro z (rfl | hz)
    exacts [hs, hS z hz]

section Core

variable {E} {p : Ω → P}

/-- The spanning matrices of hypothesis (3), without the row condition. -/
def SpanSet : Set (Module.End k (∀ i, M i)) :=
  {z | z ∈ N E ∧ ColProp z ∧ HasZeroCol z}

lemma diag_eq_zero_of_zeroCol (h2 : ∀ i, Set.InjOn (fun r ↦ block r i i) (E₀ E : Set (Module.End k (∀ i, M i))))
    {f : Module.End k (∀ i, M i)} (hf : f ∈ E) {c : Ω} (hc : ∀ y, f (Pi.single c y) = 0) :
    diag k M f = 0 := by
  refine h2 c ⟨f, hf, rfl⟩ (Submodule.zero_mem _) ?_
  ext y
  simp [hc]

/-- A nonempty product of spanning matrices lies in `E` and has a zero
column. -/
lemma prod_mem_and_zeroCol :
    ∀ l : List (Module.End k (∀ i, M i)), l ≠ [] → (∀ z ∈ l, z ∈ SpanSet (E := E)) →
      l.prod ∈ E ∧ ∃ c, ∀ y, l.prod (Pi.single c y) = 0
  | [], h, _ => absurd rfl h
  | a :: l, _, h => by
    have ha := h a (by simp)
    refine ⟨Subalgebra.list_prod_mem _ fun z hz ↦ (h z hz).1.1, ?_⟩
    by_cases hl : l = []
    · subst hl
      obtain ⟨c, hc⟩ := ha.2.2
      refine ⟨c, fun y ↦ ?_⟩
      ext j
      simpa using congrArg (· y) (hc j)
    · obtain ⟨c, hc⟩ := (prod_mem_and_zeroCol l hl fun z hz ↦ h z (by simp [hz])).2
      exact ⟨c, fun y ↦ by simp [hc]⟩

lemma diag_prod_eq_zero (h2 : ∀ i, Set.InjOn (fun r ↦ block r i i) (E₀ E : Set (Module.End k (∀ i, M i))))
    {l : List (Module.End k (∀ i, M i))} (hl : l ≠ []) (h : ∀ z ∈ l, z ∈ SpanSet (E := E)) :
    diag k M l.prod = 0 := by
  obtain ⟨hE, c, hc⟩ := prod_mem_and_zeroCol l hl h
  exact diag_eq_zero_of_zeroCol h2 hE hc

lemma span_prods_le_ker (h2 : ∀ i, Set.InjOn (fun r ↦ block r i i) (E₀ E : Set (Module.End k (∀ i, M i)))) {n : ℕ}
    (hn : n ≠ 0) : Submodule.span k (prods (SpanSet (E := E)) n) ≤ LinearMap.ker (diag k M) := by
  rw [Submodule.span_le]
  rintro _ ⟨l, rfl, hS, rfl⟩
  exact diag_prod_eq_zero h2 (by rintro rfl; exact hn rfl) hS

/-- Following a single vector through a product of matrices with at most one
nonzero block per column, within one part. -/
lemma conc_prod (hE : PreservesParts E p) {i₀ : Ω} {y : ∀ i, M i} (hy : Conc y i₀) :
    ∀ l : List (Module.End k (∀ i, M i)), (∀ z ∈ l, z ∈ SpanSet (E := E)) →
      ∃ j, Conc (l.prod y) j ∧ (l.prod y ≠ 0 → p j = p i₀)
  | [], _ => ⟨i₀, by simpa using hy, fun _ ↦ rfl⟩
  | a :: l, h => by
    obtain ⟨j₁, hj₁, hp₁⟩ := conc_prod hE hy l fun z hz ↦ h z (by simp [hz])
    have ha := h a (by simp)
    obtain ⟨j, hj, hb⟩ := conc_apply ha.2.1 hj₁
    refine ⟨j, by simpa using hj, fun hne ↦ ?_⟩
    rw [List.prod_cons, Module.End.mul_apply] at hne
    have h1 : l.prod y ≠ 0 := fun h0 ↦ hne (by rw [h0, map_zero])
    rw [← hp₁ h1]
    by_contra hpj
    exact hb hne (hE.block_eq_zero ha.1.1 hpj)

variable [Fintype Ω] [DecidableEq P] in
/-- The core of Lemma 4.4: a product of `m` spanning matrices vanishes. -/
lemma prod_eq_zero (hE : PreservesParts E p) (h2 : ∀ i, Set.InjOn (fun r ↦ block r i i) (E₀ E : Set (Module.End k (∀ i, M i))))
    {m : ℕ} (hm : ∀ i, (Finset.univ.filter fun j ↦ p j = p i).card ≤ m)
    {l : List (Module.End k (∀ i, M i))} (hlen : l.length = m)
    (h : ∀ z ∈ l, z ∈ SpanSet (E := E)) : l.prod = 0 := by
  refine LinearMap.pi_ext fun i₀ y ↦ ?_
  rw [LinearMap.zero_apply]
  by_contra hne
  set v : ∀ i, M i := Pi.single i₀ y
  have hv : Conc v i₀ := fun j hj ↦ by simp [v, hj]
  have hdrop : ∀ n, ∀ z ∈ l.drop n, z ∈ SpanSet (E := E) :=
    fun n z hz ↦ h z (List.mem_of_mem_drop hz)
  let tr : ℕ → ∀ i, M i := fun n ↦ (l.drop n).prod v
  have htr0 : ∀ n, l.prod v = (l.take n).prod (tr n) := fun n ↦ by
    rw [← Module.End.mul_apply, ← List.prod_append, List.take_append_drop]
  have hne' : ∀ n, tr n ≠ 0 := fun n h0 ↦ hne (by rw [htr0 n, h0, map_zero])
  have hex : ∀ n, ∃ j, tr n j ≠ 0 := fun n ↦ by
    by_contra hc; push Not at hc; exact hne' n (funext hc)
  choose idx hidx using hex
  have hconc : ∀ n, Conc (tr n) (idx n) ∧ p (idx n) = p i₀ := fun n ↦ by
    obtain ⟨j, hj, hp⟩ := conc_prod hE hv (l.drop n) (hdrop n)
    have : idx n = j := by by_contra hc; exact hidx n (hj _ hc)
    exact ⟨this ▸ hj, this ▸ hp (hne' n)⟩
  have key : ∀ μ ν, μ < ν → ν ≤ m → idx μ = idx ν → False := by
    intro μ ν hlt hνm heq
    -- `tr μ = W (tr ν)` with `W` a nonempty product of spanning matrices
    set W := ((l.drop μ).take (ν - μ)).prod
    have hW : tr μ = W (tr ν) := by
      simp only [tr, W]
      rw [← Module.End.mul_apply, ← List.prod_append]
      congr 2
      conv_lhs => rw [← List.take_append_drop (ν - μ) (l.drop μ)]
      rw [List.drop_drop, Nat.add_sub_cancel' hlt.le]
    have hWne : (l.drop μ).take (ν - μ) ≠ [] := by
      intro h0
      have := congrArg List.length h0
      simp only [List.length_take, List.length_drop, List.length_nil] at this
      omega
    have hWS : ∀ z ∈ (l.drop μ).take (ν - μ), z ∈ SpanSet (E := E) :=
      fun z hz ↦ hdrop μ z (List.mem_of_mem_take hz)
    have hd := diag_prod_eq_zero h2 hWne hWS
    have := hidx μ
    rw [hW, (hconc ν).1.eq_single, heq] at this
    apply this
    have := congrArg (fun f ↦ f (Pi.single (idx ν) (tr ν (idx ν))) (idx ν)) hd
    simpa [W] using this
  have hinj : Set.InjOn idx (Finset.range (m + 1) : Set ℕ) := by
    intro μ hμ ν hν heq
    simp only [Finset.coe_range, Set.mem_Iio] at hμ hν
    by_contra hμν
    rcases Nat.lt_or_gt_of_ne hμν with h | h
    · exact key μ ν h (by omega) heq
    · exact key ν μ h (by omega) heq.symm
  have hmaps : ∀ n ∈ Finset.range (m + 1),
      idx n ∈ Finset.univ.filter fun j ↦ p j = p i₀ := fun n _ ↦ by
    simp [(hconc n).2]
  have := Finset.card_le_card_of_injOn idx hmaps hinj
  rw [Finset.card_range] at this
  have := hm i₀
  omega

end Core

section Main

variable {E} {p : Ω → P}
  (h1 : ∀ f ∈ E, diag k M f ∈ E)
  (h2 : ∀ i, Set.InjOn (fun r ↦ block r i i) (E₀ E : Set (Module.End k (∀ i, M i))))
  (h3 : N E ≤ Submodule.span k (SpanSet (E := E)))

include h1 in
lemma E₀_le : E₀ E ≤ Subalgebra.toSubmodule E := by
  rintro _ ⟨f, hf, rfl⟩; exact h1 f hf

include h1 in
lemma sub_diag_mem_N {f : Module.End k (∀ i, M i)} (hf : f ∈ E) : f - diag k M f ∈ N E :=
  ⟨E.sub_mem hf (h1 f hf), by simp [diag_diag]⟩

include h2 h3 in
lemma mul_mem_N {z z' : Module.End k (∀ i, M i)} (hz : z ∈ N E) (hz' : z' ∈ N E) :
    z * z' ∈ N E := by
  refine ⟨E.mul_mem hz.1 hz'.1, ?_⟩
  have := list_prod_mem_span_prods (S := SpanSet (E := E)) [z, z']
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;>
      [exact h3 hz; exact h3 hz'])
  simpa using span_prods_le_ker h2 (by simp) this

include h1 h2 h3 in
/-- `δ` is multiplicative on `E`. -/
lemma diag_mul {f g : Module.End k (∀ i, M i)} (hf : f ∈ E) (hg : g ∈ E) :
    diag k M (f * g) = diag k M f * diag k M g := by
  have hn := sub_diag_mem_N h1 hf
  have hn' := sub_diag_mem_N h1 hg
  have hnn := mul_mem_N h2 h3 hn hn'
  have e : f * g = diag k M f * diag k M g + diag k M f * (g - diag k M g) +
      (f - diag k M f) * diag k M g + (f - diag k M f) * (g - diag k M g) := by
    simp only [mul_sub, sub_mul]; abel
  rw [e, map_add, map_add, map_add, diag_mul_left (diag_diag f), diag_diag,
    diag_mul_left (diag_diag f), diag_mul_right (diag_diag g), hn.2, hn'.2, hnn.2]
  simp

include h1 h2 h3 in
/-- `N` is a two-sided ideal of `E`. -/
lemma mul_mem_N_left {f z : Module.End k (∀ i, M i)} (hf : f ∈ E) (hz : z ∈ N E) :
    f * z ∈ N E :=
  ⟨E.mul_mem hf hz.1, LinearMap.mem_ker.2 (by
    rw [diag_mul h1 h2 h3 hf hz.1, LinearMap.mem_ker.1 hz.2, mul_zero])⟩

include h1 h2 h3 in
lemma mul_mem_N_right {f z : Module.End k (∀ i, M i)} (hf : f ∈ E) (hz : z ∈ N E) :
    z * f ∈ N E :=
  ⟨E.mul_mem hz.1 hf, LinearMap.mem_ker.2 (by
    rw [diag_mul h1 h2 h3 hz.1 hf, LinearMap.mem_ker.1 hz.2, zero_mul])⟩

/-- `δ : E → E`, an algebra endomorphism with image `E₀`. -/
def diagHom : E →ₐ[k] E where
  toFun f := ⟨diag k M f, h1 f f.2⟩
  map_one' := Subtype.ext diag_one
  map_mul' f g := Subtype.ext (diag_mul h1 h2 h3 f.2 g.2)
  map_zero' := Subtype.ext (map_zero _)
  map_add' f g := Subtype.ext (map_add _ _ _)
  commutes' c := Subtype.ext (by
    simp [Algebra.algebraMap_eq_smul_one, diag_one])

@[simp]
lemma diagHom_apply (f : E) : (diagHom h1 h2 h3 f : Module.End k (∀ i, M i)) = diag k M f := rfl

/-- `δ` is split by the inclusion `E₀ ⊆ E`. -/
lemma diagHom_of_mem_E₀ (f : E) (hf : (f : Module.End k (∀ i, M i)) ∈ E₀ E) :
    diagHom h1 h2 h3 f = f := by
  obtain ⟨g, -, hg⟩ := hf
  exact Subtype.ext (by simp [← hg, diag_diag])

lemma range_diagHom :
    Set.range (fun f : E ↦ (diagHom h1 h2 h3 f : Module.End k (∀ i, M i))) = E₀ E := by
  ext g
  constructor
  · rintro ⟨f, rfl⟩; exact ⟨f, f.2, rfl⟩
  · rintro ⟨f, hf, rfl⟩; exact ⟨⟨f, hf⟩, rfl⟩

variable [Fintype Ω] [DecidableEq P] in
include h2 h3 in
/-- `N^m = 0`. -/
lemma prod_N_eq_zero (hE : PreservesParts E p) {m : ℕ}
    (hm : ∀ i, (Finset.univ.filter fun j ↦ p j = p i).card ≤ m)
    {l : List (Module.End k (∀ i, M i))} (hlen : l.length = m) (hl : ∀ z ∈ l, z ∈ N E) :
    l.prod = 0 := by
  have := list_prod_mem_span_prods (S := SpanSet (E := E)) l fun z hz ↦ h3 (hl z hz)
  rw [hlen] at this
  have hle : Submodule.span k (prods (SpanSet (E := E)) m) ≤ ⊥ := by
    rw [Submodule.span_le]
    rintro _ ⟨l', hl', hS, rfl⟩
    exact prod_eq_zero hE h2 hm hl' hS
  simpa using hle this

end Main

variable [Fintype Ω] [DecidableEq P]

/-- The largest part size `m = max_{Ω' ∈ 𝒫} |Ω'|`. -/
def maxPart (p : Ω → P) : ℕ := Finset.univ.sup fun i ↦ (Finset.univ.filter fun j ↦ p j = p i).card

/-- Lemma 4.4, with the manuscript's hypotheses. The partition of `Ω` is the
set of fibres of `p`; `E` preserves each part-subspace (`PreservesParts`).
Conclusions: `δ` restricts to an algebra map `E → E` with image `E₀` that
is the identity on `E₀` (a split algebra surjection onto `E₀`); `N` is a
two-sided ideal of `E`; every product of `m` elements of `N` is zero. -/
theorem zeroColumn (E : Subalgebra k (Module.End k (∀ i, M i))) (p : Ω → P)
    (hE : PreservesParts E p)
    (h1 : ∀ f ∈ E, diag k M f ∈ E)
    (h2 : ∀ i, Set.InjOn (fun r ↦ block r i i) (E₀ E : Set (Module.End k (∀ i, M i))))
    (h3 : N E = Submodule.span k {z | z ∈ N E ∧ ColProp z ∧ HasZeroCol z}) :
    ∃ δE : E →ₐ[k] E,
      (∀ f, (δE f : Module.End k (∀ i, M i)) = diag k M f) ∧
      Set.range (fun f : E ↦ (δE f : Module.End k (∀ i, M i))) = E₀ E ∧
      (∀ f : E, (f : Module.End k (∀ i, M i)) ∈ E₀ E → δE f = f) ∧
      (∀ f ∈ E, ∀ z ∈ N E, f * z ∈ N E ∧ z * f ∈ N E) ∧
      ∀ l : List (Module.End k (∀ i, M i)), l.length = maxPart p → (∀ z ∈ l, z ∈ N E) →
        l.prod = 0 := by
  have h3' : N E ≤ Submodule.span k (SpanSet (E := E)) := h3.le
  refine ⟨diagHom h1 h2 h3', fun _ ↦ rfl, range_diagHom h1 h2 h3',
    diagHom_of_mem_E₀ h1 h2 h3', fun f hf z hz ↦
      ⟨mul_mem_N_left h1 h2 h3' hf hz, mul_mem_N_right h1 h2 h3' hf hz⟩,
    fun l hl hN ↦ prod_N_eq_zero h2 h3' hE (fun i ↦ ?_) hl hN⟩
  exact Finset.le_sup (f := fun i ↦ (Finset.univ.filter fun j ↦ p j = p i).card)
    (Finset.mem_univ i)

end ZeroColumn

end LargeIndecomposable
