module

public import LargeIndecomposable.KroneckerBricks.MapSystem
public import Mathlib.SetTheory.Cardinal.Cofinality.Club
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# A rigid map system on a regular uncountable cardinal

For a well-order `α` of regular uncountable type, the set `Dec α` of nonempty
finite strictly decreasing sequences (stored as increasing lists, so the head
is the last entry) carries a rigid map system (`Rigid.isRigidSys_regSys`). The
maps are: dropping the last entry, the ladder coordinates `[δ] ↦ [η_δ(m)]`,
a surjection from a cofinal set `B` of stationary ladder values, a constant
map and an injection into the singletons. This is a linear form of Shelah's
Theorem 2.1 (Israel J. Math. 18, 1974); see the thread note
`2026-10-29-202837-rigid-structures-proof.md`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

universe u

namespace Rigid

open _root_.Cardinal Order Set

variable (α : Type u) [LinearOrder α]

/-- Nonempty strictly increasing lists: decreasing sequences read backwards. -/
abbrev Dec : Type u := {l : List α // l ≠ [] ∧ l.Pairwise (· < ·)}

namespace Dec

variable {α}

/-- The last entry of the sequence (the head of the list). -/
def head (τ : Dec α) : α := τ.1.head τ.2.1

/-- The sequence of length one. -/
def sing (a : α) : Dec α := ⟨[a], List.cons_ne_nil _ _, List.pairwise_singleton _ _⟩

@[simp] lemma head_sing (a : α) : (sing a).head = a := rfl

lemma sing_injective : Function.Injective (sing : α → Dec α) := fun a b h ↦
  congrArg head h

lemma head_le (τ : Dec α) {x : α} (hx : x ∈ τ.1) : τ.head ≤ x := by
  obtain ⟨l, hl, hp⟩ := τ
  cases l with
  | nil => exact absurd rfl hl
  | cons a l =>
    change a ≤ x
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_rfl
    · exact (List.rel_of_pairwise_cons hp hx).le

/-- Append an entry below the last one. -/
def cons (i : α) (τ : Dec α) (h : i < τ.head) : Dec α :=
  ⟨i :: τ.1, List.cons_ne_nil _ _,
    List.pairwise_cons.2 ⟨fun _ hy ↦ h.trans_le (head_le τ hy), τ.2.2⟩⟩

@[simp] lemma head_cons (i : α) (τ : Dec α) (h : i < τ.head) : (cons i τ h).head = i := rfl

/-- The sequence has length at least two. -/
def Long (τ : Dec α) : Prop := τ.1.tail ≠ []

lemma long_cons (i : α) (τ : Dec α) (h : i < τ.head) : (cons i τ h).Long := τ.2.1

open Classical in
/-- Drop the last entry (the identity on sequences of length one). -/
def pre (τ : Dec α) : Dec α :=
  if h : τ.Long then ⟨τ.1.tail, h, τ.2.2.sublist (List.tail_sublist _)⟩ else τ

lemma pre_cons (i : α) (τ : Dec α) (h : i < τ.head) : pre (cons i τ h) = τ := by
  unfold pre
  rw [dif_pos (long_cons i τ h)]
  rfl

lemma head_lt_head_pre {τ : Dec α} (h : τ.Long) : τ.head < (pre τ).head := by
  obtain ⟨l, hl, hp⟩ := τ
  cases l with
  | nil => exact absurd rfl hl
  | cons a l =>
    cases l with
    | nil => exact absurd rfl h
    | cons b l =>
      unfold pre
      rw [dif_pos h]
      exact List.rel_of_pairwise_cons hp List.mem_cons_self

lemma mk_le [Infinite α] : #(Dec α) ≤ #α :=
  (mk_le_of_injective (f := fun τ : Dec α ↦ τ.1) Subtype.val_injective).trans
    (mk_list_eq_mk α).le

end Dec

section Ladders

variable {α} [WellFoundedLT α]

attribute [local instance] WellFoundedLT.toOrderBot WellFoundedLT.conditionallyCompleteLinearOrderBot

lemma bddAbove_range_nat (hα : ℵ₀ < cof α) (g : ℕ → α) : BddAbove (range g) :=
  .of_not_isCofinal fun h ↦ (cof_le h).not_gt
    (hα.trans_le' (by simpa using mk_range_le_lift (f := g)))

lemma isClub_Ici (b : α) : IsClub (Ici b) where
  dirSupClosed _ hd hd0 _ _ hx := let ⟨_, hy⟩ := hd0; (hd hy).trans (hx.1 hy)
  isCofinal x := ⟨max x b, le_max_right _ _, le_max_left _ _⟩

variable (α) in
/-- Suprema of strictly increasing `ω`-sequences. -/
def S : Set α := {δ | ∃ η : ℕ → α, StrictMono η ∧ IsLUB (range η) δ}

open Classical in
/-- A ladder `η_δ ↗ δ` for `δ ∈ S`. -/
def lad (δ : α) (m : ℕ) : α := if h : δ ∈ S α then Classical.choose h m else δ

lemma lad_spec {δ : α} (h : δ ∈ S α) : StrictMono (lad δ) ∧ IsLUB (range (lad δ)) δ := by
  have : lad δ = Classical.choose h := funext fun m ↦ by simp [lad, h]
  rw [this]
  exact Classical.choose_spec h

lemma lad_lt {δ : α} (h : δ ∈ S α) (m : ℕ) : lad δ m < δ :=
  ((lad_spec h).1 (Nat.lt_succ_self m)).trans_le ((lad_spec h).2.1 ⟨m + 1, rfl⟩)

lemma exists_lt_lad {δ : α} (h : δ ∈ S α) {b : α} (hb : b < δ) : ∃ m, b < lad δ m := by
  by_contra hc
  simp only [not_exists, not_lt] at hc
  exact hb.not_ge ((lad_spec h).2.2 (by rintro _ ⟨m, rfl⟩; exact hc m))

variable [Nonempty α] [NoMaxOrder α]

lemma isStationary_S (hα : ℵ₀ < cof α) : IsStationary (S α) := by
  intro C hC
  have step : ∀ a : α, ∃ c ∈ C, a < c := fun a ↦ by
    obtain ⟨b, hb⟩ := exists_gt a
    obtain ⟨c, hc, hbc⟩ := hC.isCofinal b
    exact ⟨c, hc, hb.trans_le hbc⟩
  choose f hfC hf using step
  let a0 : α := Classical.arbitrary α
  let g : ℕ → α := fun n ↦ f^[n + 1] a0
  have hg : StrictMono g := strictMono_nat_of_lt_succ fun n ↦ by
    simp only [g, Function.iterate_succ_apply' f (n + 1)]
    exact hf _
  have hgC : ∀ n, g n ∈ C := fun n ↦ by
    simp only [g, Function.iterate_succ_apply']
    exact hfC _
  have hlub : IsLUB (range g) (sSup (range g)) :=
    isLUB_csSup (range_nonempty g) (bddAbove_range_nat hα g)
  exact ⟨sSup (range g), ⟨g, hg, hlub⟩,
    hC.isLUB_mem (by rintro _ ⟨n, rfl⟩; exact hgC n) (range_nonempty g) hlub⟩

lemma exists_good_coord (hα : ℵ₀ < cof α) :
    ∃ n, ∀ a : α, IsStationary (S α ∩ {δ | a ≤ lad δ n}) := by
  by_contra hc
  simp only [not_exists, not_forall] at hc
  choose a ha using hc
  simp only [not_isStationary_iff] at ha
  choose C hC hdisj using ha
  obtain ⟨b, hb⟩ := bddAbove_range_nat hα a
  obtain ⟨b', hb'⟩ := exists_gt b
  have hclub : IsClub ((⋂ n, C n) ∩ Ici b') :=
    (IsClub.iInter_of_countable hα.ne' hC).inter hα.ne' (isClub_Ici b')
  obtain ⟨δ, hδS, hδC, hδb⟩ := isStationary_S hα hclub
  have hlt : ∀ n, lad δ n < a n := fun n ↦ by
    by_contra h
    exact Set.disjoint_left.1 (hdisj n) ⟨hδS, not_lt.1 h⟩ (mem_iInter.1 hδC n)
  have hub : δ ≤ b := (lad_spec hδS).2.2
    (by rintro _ ⟨n, rfl⟩; exact ((hlt n).trans_le (hb ⟨n, rfl⟩)).le)
  exact (hb'.trans_le hδb).not_ge hub

variable [IsRegularCardinalOrder α]

/-- A ladder coordinate with cofinally many stationary fibres. -/
def n0 (hα : ℵ₀ < cof α) : ℕ := Classical.choose (exists_good_coord hα)

/-- The values of the ladder coordinate `n0` with stationary fibre. -/
def B (hα : ℵ₀ < cof α) : Set α :=
  {β | IsStationary (S α ∩ (fun δ ↦ lad δ (n0 hα)) ⁻¹' {β})}

lemma isCofinal_B (hα : ℵ₀ < cof α) : IsCofinal (B hα) := by
  intro a
  obtain ⟨β, hβ⟩ := exists_isStationary_preimage_singleton (f := fun δ ↦ lad δ (n0 hα)) hα.ne'
    (Classical.choose_spec (exists_good_coord hα) a) (fun δ hδ ↦ lad_lt hδ.1 _)
  obtain ⟨δ, ⟨_, hδa⟩, hδβ⟩ := hβ.nonempty
  refine ⟨β, hβ.mono fun x hx ↦ ⟨hx.1.1, hx.2⟩, ?_⟩
  rw [← (mem_singleton_iff.1 hδβ : lad δ (n0 hα) = β)]
  exact hδa

lemma exists_surj (hα : ℵ₀ < cof α) : ∃ π : α → α, ∀ a, ∃ β ∈ B hα, π β = a := by
  have hle : #α ≤ #(B hα) := (cof_eq_cardinalMk (α := α)).symm.trans_le (cof_le (isCofinal_B hα))
  obtain ⟨f⟩ := (Cardinal.le_def _ _).1 hle
  have hinj : Function.Injective fun a ↦ (f a : α) := fun a b h ↦ f.injective (Subtype.ext h)
  exact ⟨Function.invFun fun a ↦ (f a : α), fun a ↦ ⟨f a, (f a).2,
    Function.leftInverse_invFun hinj a⟩⟩

/-- A surjection from `B` onto `α`. -/
def piMap (hα : ℵ₀ < cof α) : α → α := Classical.choose (exists_surj hα)

lemma piMap_spec (hα : ℵ₀ < cof α) (a : α) : ∃ β ∈ B hα, piMap hα β = a :=
  Classical.choose_spec (exists_surj hα) a

lemma infinite_of (hα : ℵ₀ < cof α) : Infinite α :=
  Cardinal.infinite_iff.2 (hα.le.trans (cof_le_cardinalMk α))

/-- An injection of the decreasing sequences into `α`. -/
def iota (hα : ℵ₀ < cof α) : Dec α ↪ α :=
  haveI := infinite_of hα
  ((Cardinal.le_def _ _).1 Dec.mk_le).some

/-- The rigid map system on `Dec α`. -/
def regSys (hα : ℵ₀ < cof α) : MapSystem (Dec α) where
  dom
    | 0 => {τ | τ.Long}
    | 1 => Dec.sing '' B hα
    | 2 => range Dec.sing
    | 3 => univ
    | _ + 4 => Dec.sing '' S α
  map
    | 0 => Dec.pre
    | 1 => fun τ ↦ Dec.sing (piMap hα τ.head)
    | 2 => fun _ ↦ Dec.sing (Classical.arbitrary α)
    | 3 => fun τ ↦ Dec.sing (iota hα τ)
    | m + 4 => fun τ ↦ Dec.sing (lad τ.head m)

theorem isRigidSys_regSys (k : Type u) [Field k] (hα : ℵ₀ < cof α) :
    IsRigidSys k (regSys hα) := by
  classical
  intro φ hφ
  -- 1. supports only move up (Shelah, Observation III)
  have tri : ∀ γ : α, ∀ τ : Dec α, τ.head = γ →
      ∀ τ' ∈ (φ (Finsupp.single τ 1)).support, γ ≤ τ'.head := by
    intro γ
    induction γ using WellFoundedLT.induction with
    | _ γ IH =>
    intro τ hτ τ' hτ'
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨hsupp, hcomm⟩ := hφ 0 (Dec.cons τ'.head τ (hτ ▸ hlt)) (Dec.long_cons _ _ _)
    change φ (Finsupp.single (Dec.pre (Dec.cons _ τ _)) 1) = _ at hcomm
    rw [Dec.pre_cons] at hcomm
    rw [hcomm] at hτ'
    obtain ⟨v, hv, hvτ⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hτ')
    have hvl : v.Long := (Finsupp.mem_supported _ _).1 hsupp hv
    have h1 := IH τ'.head hlt _ (Dec.head_cons _ _ _) v hv
    have h2 := Dec.head_lt_head_pre hvl
    change (Dec.pre v) = τ' at hvτ
    rw [hvτ] at h2
    exact h1.not_gt h2
  -- 2. the club of closure points (Observation IV)
  let U : α → Set α := fun a ↦
    {δ | ∀ τ' ∈ (φ (Finsupp.single (Dec.sing a) 1)).support, τ'.head < δ}
  have hU : ∀ a, IsClub (U a) := fun a ↦ by
    refine ⟨fun d hd hd0 _ x hx ↦ ?_, fun b ↦ ?_⟩
    · obtain ⟨y, hy⟩ := hd0
      exact fun τ' hτ' ↦ (hd hy τ' hτ').trans_le (hx.1 hy)
    · obtain ⟨u, hu⟩ := ((φ (Finsupp.single (Dec.sing a) 1)).support.image Dec.head).bddAbove
      obtain ⟨c, hc⟩ := exists_gt (max b u)
      exact ⟨c, fun τ' hτ' ↦ (hu (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hτ'))).trans_lt
        ((le_max_right _ _).trans_lt hc), (le_max_left _ _).trans hc.le⟩
  have hC := IsClub.diag hα.ne' hU
  -- 3. diagonal at closure points of countable cofinality (Observation V)
  have obsV : ∀ δ, (∀ b < δ, δ ∈ U b) → δ ∈ S α →
      φ (Finsupp.single (Dec.sing δ) 1) =
        φ (Finsupp.single (Dec.sing δ) 1) (Dec.sing δ) • Finsupp.single (Dec.sing δ) 1 := by
    intro δ hδC hδS
    set x := φ (Finsupp.single (Dec.sing δ) (1 : k)) with hx
    have hxS : ∀ τ ∈ x.support, ∃ j ∈ S α, Dec.sing j = τ := fun τ hτ ↦
      (Finsupp.mem_supported _ _).1 (hφ 4 (Dec.sing δ) ⟨δ, hδS, rfl⟩).1 hτ
    have hsub : x.support ⊆ {Dec.sing δ} := by
      intro τ' hτ'
      by_contra hne
      rw [Finset.mem_singleton] at hne
      have hne' : (x.support.image Dec.head).Nonempty := ⟨_, Finset.mem_image_of_mem _ hτ'⟩
      obtain ⟨τi, hτi, hτii⟩ := Finset.mem_image.1 ((x.support.image Dec.head).max'_mem hne')
      obtain ⟨i, hiS, rfl⟩ := hxS τi hτi
      simp only [Dec.head_sing] at hτii
      have hmax : ∀ τ ∈ x.support, τ.head ≤ i := fun τ hτ ↦
        hτii ▸ Finset.le_max' _ _ (Finset.mem_image_of_mem _ hτ)
      obtain ⟨j, hjS, rfl⟩ := hxS τ' hτ'
      have hδj : δ ≤ j := tri δ (Dec.sing δ) rfl _ hτ'
      have hjne : j ≠ δ := fun h ↦ hne (h ▸ rfl)
      have hδi : δ < i := (lt_of_le_of_ne hδj (Ne.symm hjne)).trans_le (hmax _ hτ')
      let F := insert δ ((x.support.image Dec.head).filter (· < i))
      have hFlt : ∀ y ∈ F, y < i := by
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact hδi
        · exact (Finset.mem_filter.1 hy).2
      let b := F.max' (Finset.insert_nonempty _ _)
      have hbi : b < i := hFlt _ (F.max'_mem _)
      obtain ⟨m, hm⟩ := exists_lt_lad hiS hbi
      obtain ⟨-, hcomm⟩ := hφ (m + 4) (Dec.sing δ) ⟨δ, hδS, rfl⟩
      have hval : Finsupp.mapDomain ((regSys hα).map (m + 4)) x (Dec.sing (lad i m)) =
          x (Dec.sing i) := by
        rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum,
          Finset.sum_eq_single (Dec.sing i)]
        · rw [Finsupp.single_apply]
          exact if_pos rfl
        · intro τ hτ hτne
          obtain ⟨j, hjS, rfl⟩ := hxS τ hτ
          rw [Finsupp.single_apply, if_neg]
          intro heq
          change Dec.sing (lad j m) = Dec.sing (lad i m) at heq
          have hj : j < i := lt_of_le_of_ne (hmax _ hτ) (fun h ↦ hτne (h ▸ rfl))
          have hjF : j ∈ F := Finset.mem_insert_of_mem
            (Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hτ, hj⟩)
          exact ((lad_lt hjS m).trans_le ((F.le_max' j hjF).trans hm.le)).ne
            (Dec.sing_injective heq)
        · intro h
          rw [Finsupp.notMem_support_iff.1 h, Finsupp.single_zero, Finsupp.zero_apply]
      have hmem : Dec.sing (lad i m) ∈ (φ (Finsupp.single (Dec.sing (lad δ m)) 1)).support := by
        rw [Finsupp.mem_support_iff]
        change φ (Finsupp.single ((regSys hα).map (m + 4) (Dec.sing δ)) 1) _ ≠ 0
        rw [hcomm, hval]
        exact Finsupp.mem_support_iff.1 hτi
      have hlt := hδC (lad δ m) (lad_lt hδS m) _ hmem
      have hδb : δ ≤ b := F.le_max' δ (Finset.mem_insert_self _ _)
      exact (not_lt.2 (hδb.trans hm.le)) hlt
    rw [Finsupp.support_subset_singleton.1 hsub, Finsupp.smul_single_one]
    simp
  -- 4. diagonal on `B`
  have onB : ∀ β ∈ B hα, ∃ r : k,
      φ (Finsupp.single (Dec.sing β) 1) = r • Finsupp.single (Dec.sing β) 1 := by
    intro β hβ
    obtain ⟨δ, ⟨hδS, hδβ⟩, hδC⟩ := hβ hC
    obtain ⟨-, hcomm⟩ := hφ (n0 hα + 4) (Dec.sing δ) ⟨δ, hδS, rfl⟩
    have hβ' : lad δ (n0 hα) = β := hδβ
    have hv := obsV δ hδC hδS
    set r := φ (Finsupp.single (Dec.sing δ) 1) (Dec.sing δ) with hr
    refine ⟨r, ?_⟩
    change φ (Finsupp.single (Dec.sing (lad δ (n0 hα))) 1) = _ at hcomm
    rw [hβ'] at hcomm
    rw [hcomm, hv, Finsupp.mapDomain_smul, Finsupp.mapDomain_single]
    change _ • Finsupp.single (Dec.sing (lad δ (n0 hα))) 1 = _
    rw [hβ']
  -- 5. diagonal on all singletons
  have diag : ∀ a, ∃ s : k,
      φ (Finsupp.single (Dec.sing a) 1) = s • Finsupp.single (Dec.sing a) 1 := by
    intro a
    obtain ⟨β, hβ, rfl⟩ := piMap_spec hα a
    obtain ⟨r, hr⟩ := onB β hβ
    obtain ⟨-, hcomm⟩ := hφ 1 (Dec.sing β) ⟨β, hβ, rfl⟩
    refine ⟨r, ?_⟩
    change φ (Finsupp.single (Dec.sing (piMap hα β)) 1) = _ at hcomm
    rw [hcomm, hr, Finsupp.mapDomain_smul, Finsupp.mapDomain_single]
    rfl
  -- 6. one scalar
  choose s hs using diag
  have hsc : ∀ a, s a = s (Classical.arbitrary α) := by
    intro a
    obtain ⟨-, hcomm⟩ := hφ 2 (Dec.sing a) ⟨a, rfl⟩
    change φ (Finsupp.single (Dec.sing (Classical.arbitrary α)) 1) = _ at hcomm
    rw [hs a, Finsupp.mapDomain_smul, Finsupp.mapDomain_single, hs] at hcomm
    exact (smul_left_injective k (Finsupp.single_ne_zero.2 one_ne_zero) hcomm).symm
  -- 7. all sequences, through the injection
  refine ⟨s (Classical.arbitrary α), Finsupp.lhom_ext' fun τ ↦ LinearMap.ext_ring ?_⟩
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.smul_apply,
    LinearMap.id_apply]
  obtain ⟨-, hcomm⟩ := hφ 3 τ trivial
  change φ (Finsupp.single (Dec.sing (iota hα τ)) 1) = _ at hcomm
  rw [hs, hsc] at hcomm
  have hinj : Function.Injective ((regSys hα).map 3) := fun a b h ↦
    (iota hα).injective (Dec.sing_injective h)
  apply Finsupp.mapDomain_injective hinj
  rw [← hcomm, Finsupp.mapDomain_smul, Finsupp.mapDomain_single]
  rfl

end Ladders

end Rigid

end LargeIndecomposable
