module

public import LargeIndecomposable.Cleaving.Basic.ThinRep

/-!
# Thin categories with a `D̃₄` core

A *core poset* has core vertices `C` (ordered), source leaves `S` below some
core vertices and sink leaves `T` above some core vertices; all relations
between leaves pass through the core (`RayCat.CoreData`). Its incidence
category is a thin ray category (`RayCat.CoreData.thin`). Putting `k²` on the
core with identity maps, a vector on each source leaf and a functional on each
sink leaf gives a representation (`RayCat.CoreData.rep`); its natural
endomorphisms are scalars as soon as the leaves cut out three distinct lines,
and one leaf line `⟨(1, t)⟩` gives a one-parameter family of bricks. Category
11 of Gabriel–Roiter 10.7 (BO13a figures 6.4, 6.7, 6.10) is of this kind.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayQuiver

namespace RayCat

/-- A thin category from a partial order (all composites nonzero). -/
def ThinData.ofPoset {V : Type} (le : V → V → Prop) (refl : ∀ x, le x x)
    (antisymm : ∀ x y, le x y → le y x → x = y) (trans : ∀ x y z, le x y → le y z → le x z) :
    ThinData V where
  le := le
  nz x _ z := le x z
  refl := refl
  antisymm := antisymm
  nz_le _ _ _ _ _ h := h
  nz_left _ _ h := h
  nz_right _ _ h := h
  assoc x y z w hxy hyz hzw :=
    ⟨fun h ↦ ⟨trans _ _ _ hyz hzw, h.2⟩, fun h ↦ ⟨trans _ _ _ hxy hyz, h.2⟩⟩

/-- The data of a core poset. -/
structure CoreData where
  C : Type
  S : Type
  T : Type
  cle : C → C → Prop
  sle : S → C → Prop
  tle : C → T → Prop
  crefl : ∀ c, cle c c
  cantisymm : ∀ c c', cle c c' → cle c' c → c = c'
  ctrans : ∀ c c' c'', cle c c' → cle c' c'' → cle c c''
  sle_up : ∀ s c c', sle s c → cle c c' → sle s c'
  tle_down : ∀ c c' t, cle c c' → tle c' t → tle c t

namespace CoreData

variable (K : CoreData)

/-- The vertices. -/
abbrev V : Type := K.C ⊕ (K.S ⊕ K.T)

/-- The order on the vertices. -/
def le : K.V → K.V → Prop
  | .inl c, .inl c' => K.cle c c'
  | .inr (.inl s), .inl c => K.sle s c
  | .inl c, .inr (.inr t) => K.tle c t
  | .inr (.inl s), .inr (.inr t) => ∃ c, K.sle s c ∧ K.tle c t
  | .inr (.inl s), .inr (.inl s') => s = s'
  | .inr (.inr t), .inr (.inr t') => t = t'
  | _, _ => False

lemma le_refl (x : K.V) : K.le x x := by
  rcases x with c | s | t
  · exact K.crefl c
  · rfl
  · rfl

lemma le_antisymm (x y : K.V) (h : K.le x y) (h' : K.le y x) : x = y := by
  rcases x with c | s | t <;> rcases y with c' | s' | t' <;> simp only [le] at h h'
  · rw [K.cantisymm c c' h h']
  · rw [h]
  · rw [h]

lemma le_trans (x y z : K.V) (h : K.le x y) (h' : K.le y z) : K.le x z := by
  rcases x with c | s | t <;> rcases y with c' | s' | t' <;> rcases z with c'' | s'' | t'' <;>
    simp only [le] at h h' ⊢
  all_goals first
    | exact K.ctrans _ _ _ h h'
    | exact K.tle_down _ _ _ h h'
    | exact K.sle_up _ _ _ h h'
    | exact ⟨_, h, h'⟩
    | (subst_vars; assumption)
    | (obtain ⟨c, h1, h2⟩ := h; subst h'; exact ⟨c, h1, h2⟩)
    | (subst h; exact h')

/-- The thin category of a core poset. -/
def thin : ThinData K.V := ThinData.ofPoset K.le K.le_refl K.le_antisymm K.le_trans

section Rep

universe u

variable (k : Type u) [Field k]

/-- A functional on `k²`. -/
def fn (φ : Fin 2 → k) : (Fin 2 → k) →ₗ[k] k where
  toFun v := φ 0 * v 0 + φ 1 * v 1
  map_add' v w := by simp; ring
  map_smul' a v := by simp; ring

@[simp] lemma fn_apply (φ v : Fin 2 → k) : fn k φ v = φ 0 * v 0 + φ 1 * v 1 := rfl

lemma fn_comp_span (φ w : Fin 2 → k) :
    (fn k φ).comp (LinearMap.toSpanSingleton k (Fin 2 → k) w) = (fn k φ w) • LinearMap.id := by
  ext
  simp [LinearMap.toSpanSingleton_apply]

/-- The vertex spaces: `k²` on the core, `k` on the leaves. -/
def sp : K.V → ModuleCat.{u} k
  | .inl _ => ModuleCat.of k (Fin 2 → k)
  | .inr _ => ModuleCat.of k k

variable {k}

/-- The maps of the representation. -/
def map (u : K.S → Fin 2 → k) (φ : K.T → Fin 2 → k) :
    ∀ x y : K.V, K.le x y → (K.sp k x →ₗ[k] K.sp k y)
  | .inl _, .inl _, _ => LinearMap.id
  | .inr (.inl s), .inl _, _ => LinearMap.toSpanSingleton k _ (u s)
  | .inl _, .inr (.inr t), _ => fn k (φ t)
  | .inr (.inl s), .inr (.inr t), _ => (fn k (φ t) (u s)) • LinearMap.id
  | .inr (.inl _), .inr (.inl _), _ => LinearMap.id
  | .inr (.inr _), .inr (.inr _), _ => LinearMap.id
  | .inl _, .inr (.inl _), h => h.elim
  | .inr (.inr _), .inl _, h => h.elim
  | .inr (.inr _), .inr (.inl _), h => h.elim

open Classical in
/-- The representation of the core poset. -/
def rep (u : K.S → Fin 2 → k) (φ : K.T → Fin 2 → k) : ThinRep K.thin k where
  sp := K.sp k
  map := K.map u φ
  map_id x := by rcases x with c | s | t <;> rfl
  map_comp x y z h h' := by
    change K.le x y at h
    change K.le y z at h'
    rw [dif_pos (show K.thin.nz x y z from K.le_trans x y z h h')]
    rcases x with c | s | t <;> rcases y with c' | s' | t' <;> rcases z with c'' | s'' | t'' <;>
      simp only [le] at h h'
    all_goals (try subst_vars)
    all_goals first
      | exact h.elim | exact h'.elim
      | rfl
      | exact fn_comp_span k (φ _) (u _)

end Rep

section Family

universe u

variable {k : Type u} [Field k] [Fintype K.C] [Fintype K.S] [Fintype K.T] [DecidableEq K.C]
  [DecidableEq K.S] [DecidableEq K.T]

variable {u u' : K.S → Fin 2 → k} {φ φ' : K.T → Fin 2 → k}
  {f : ∀ x, (K.rep u φ).sp x →ₗ[k] (K.rep u' φ').sp x}

lemma core_eq (hf : ThinRep.IsNatural f) {c c' : K.C} (h : K.cle c c') (m : Fin 2 → k) :
    f (.inl c') m = f (.inl c) m := hf (.inl c) (.inl c') h m

lemma source_eq (hf : ThinRep.IsNatural f) {s : K.S} {c : K.C} (h : K.sle s c) :
    f (.inl c) (u s) = (@id k (f (.inr (.inl s)) (1 : k))) • u' s := by
  have := hf (.inr (.inl s)) (.inl c) h (1 : k)
  change f (.inl c) ((1 : k) • u s) = _ at this
  rw [one_smul] at this
  exact this

lemma core_eq' (hf : ThinRep.IsNatural f) {c c' : K.C} (h : Relation.EqvGen K.cle c c') :
    ∀ m : Fin 2 → k, f (.inl c') m = f (.inl c) m := by
  induction h with
  | rel x y h => exact K.core_eq hf h
  | refl => exact fun _ ↦ rfl
  | symm x y _ ih => exact fun m ↦ (ih m).symm
  | trans x y z _ _ ih₁ ih₂ => exact fun m ↦ (ih₂ m).trans (ih₁ m)

lemma lin_k (g : k →ₗ[k] k) (x : k) : g x = g 1 * x := by
  have := g.map_smul x (1 : k)
  rw [smul_eq_mul, mul_one, smul_eq_mul] at this
  rw [this, mul_comm]

lemma sink_eq (hf : ThinRep.IsNatural f) {t : K.T} {c : K.C} (h : K.tle c t) (v : Fin 2 → k) :
    fn k (φ' t) (f (.inl c) v) = (@id k (f (.inr (.inr t)) (1 : k))) * fn k (φ t) v := by
  have := hf (.inl c) (.inr (.inr t)) h v
  change f (.inr (.inr t)) (fn k (φ t) v) = fn k (φ' t) (f (.inl c) v) at this
  rw [← this]
  exact lin_k (f (.inr (.inr t))) _

/-- **Core posets give one-parameter families of bricks.** -/
theorem not_isRepresentationFinite [Infinite k] (c₀ : K.C) (hc₀ : ∀ c, Relation.EqvGen K.cle c₀ c)
    (s₀ : K.S) (hsc : ∀ s, ∃ c, K.sle s c) (htc : ∀ t, ∃ c, K.tle c t)
    (u : K.S → Fin 2 → k) (φ : K.T → Fin 2 → k) (hu : ∀ s, s ≠ s₀ → u s ≠ 0)
    (hφ : ∀ t, φ t ≠ 0)
    (hscalar : ∀ F : (Fin 2 → k) →ₗ[k] (Fin 2 → k),
      (∀ s, s ≠ s₀ → ∃ l : k, F (u s) = l • u s) →
      (∀ t, ∃ m : k, ∀ v, fn k (φ t) (F v) = m * fn k (φ t) v) → ∃ a : k, F = a • LinearMap.id) :
    ¬Statement.IsRepresentationFinite (Linearization (ThinCat K.thin) k) := by
  classical
  let U : k → K.S → Fin 2 → k := fun t ↦ Function.update u s₀ ![1, t]
  have hU : ∀ t s, U t s ≠ 0 := fun t s ↦ by
    by_cases hs : s = s₀
    · subst hs
      simp only [U, Function.update_self]
      intro h
      have := congrFun h 0
      simp at this
    · simp only [U, Function.update_of_ne hs]
      exact hu s hs
  have hUs : ∀ t s, s ≠ s₀ → U t s = u s := fun t s hs ↦ Function.update_of_ne hs _ _
  -- the common analysis of a natural family
  have analyse : ∀ t t' (f : ∀ x, (K.rep (U t) φ).sp x →ₗ[k] (K.rep (U t') φ).sp x),
      ThinRep.IsNatural f → ∃ a : k, (∀ c, ∀ v, f (.inl c) v = a • v) ∧
        (∀ s, f (.inl c₀) (U t s) = (@id k (f (.inr (.inl s)) (1 : k))) • U t' s) ∧
        ∀ t₁ v, fn k (φ t₁) (a • v) = (@id k (f (.inr (.inr t₁)) (1 : k))) * fn k (φ t₁) v := by
    intro t t' f hf
    have hcore : ∀ c v, f (.inl c) v = f (.inl c₀) v := fun c v ↦ K.core_eq' hf (hc₀ c) v
    have hsrc : ∀ s, f (.inl c₀) (U t s) = (@id k (f (.inr (.inl s)) (1 : k))) • U t' s := by
      intro s
      obtain ⟨c, hc⟩ := hsc s
      exact (hcore c (U t s)).symm.trans (K.source_eq hf hc)
    have hsnk : ∀ t₁ v, fn k (φ t₁) (f (.inl c₀) v) =
        (@id k (f (.inr (.inr t₁)) (1 : k))) * fn k (φ t₁) v := by
      intro t₁ v
      obtain ⟨c, hc⟩ := htc t₁
      have := K.sink_eq hf hc v
      rwa [hcore c v] at this
    obtain ⟨a, ha⟩ := hscalar (f (.inl c₀) : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
      (fun s hs ↦ ⟨_, by have := hsrc s; rwa [hUs t s hs, hUs t' s hs] at this⟩)
      (fun t₁ ↦ ⟨_, hsnk t₁⟩)
    have hFa : ∀ v : Fin 2 → k, f (.inl c₀) v = a • v := fun v ↦
      (congrArg (fun G : (Fin 2 → k) →ₗ[k] (Fin 2 → k) ↦ G v) ha).trans rfl
    exact ⟨a, fun c v ↦ (hcore c v).trans (hFa v), hsrc, fun t₁ v ↦
      (congrArg (fn k (φ t₁)) (hFa v)).symm.trans (hsnk t₁ v)⟩
  have hfn : ∀ t₁, ∃ v, fn k (φ t₁) v ≠ 0 := fun t₁ ↦ by
    by_contra h
    push_neg at h
    apply hφ t₁
    funext i
    fin_cases i
    · simpa using h ![1, 0]
    · simpa using h ![0, 1]
  refine ThinRep.not_isRepresentationFinite (fun t ↦ K.rep (U t) φ) (fun t x ↦ ?_)
    (fun t ↦ ⟨.inl c₀, show Nontrivial (Fin 2 → k) from inferInstance⟩) (fun t f hf ↦ ?_)
    (fun t t' f hf hbij ↦ ?_)
  · rcases x with c | s | t
    · exact (inferInstance : FiniteDimensional k (Fin 2 → k))
    · exact (inferInstance : FiniteDimensional k k)
    · exact (inferInstance : FiniteDimensional k k)
  · obtain ⟨a, hc, hs, ht⟩ := analyse t t f hf
    refine ⟨a, fun x ↦ ?_⟩
    rcases x with c | s | t₁
    · exact LinearMap.ext (hc c)
    · have h1 : a • U t s = (@id k (f (.inr (.inl s)) (1 : k))) • U t s :=
        (hc c₀ (U t s)).symm.trans (hs s)
      have h2 : a = (@id k (f (.inr (.inl s)) (1 : k))) := by
        have h3 : (a - (@id k (f (.inr (.inl s)) (1 : k)))) • U t s = 0 := by
          rw [sub_smul, h1, sub_self]
        exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right (hU t s))
      refine LinearMap.ext fun x ↦ (lin_k (f (.inr (.inl s))) x).trans ?_
      rw [h2]
      rfl
    · obtain ⟨v, hv⟩ := hfn t₁
      have h1 := ht t₁ v
      rw [LinearMap.map_smul, smul_eq_mul] at h1
      have h2 : a = (@id k (f (.inr (.inr t₁)) (1 : k))) := mul_right_cancel₀ hv h1
      refine LinearMap.ext fun x ↦ (lin_k (f (.inr (.inr t₁))) x).trans ?_
      rw [h2]
      rfl
  · obtain ⟨a, hc, hs, -⟩ := analyse t t' f hf
    have ha : a ≠ 0 := by
      intro h0
      have e0 : (a • (![1, 0] : Fin 2 → k)) = 0 := by rw [h0, zero_smul]
      have e : f (.inl c₀) (![1, 0] : Fin 2 → k) = f (.inl c₀) 0 :=
        ((hc c₀ _).trans e0).trans (map_zero (f (.inl c₀))).symm
      have := congrFun ((hbij (.inl c₀)).1 e) 0
      exact one_ne_zero (this : (1 : k) = 0)
    have h1 : a • U t s₀ = (@id k (f (.inr (.inl s₀)) (1 : k))) • U t' s₀ :=
      (hc c₀ (U t s₀)).symm.trans (hs s₀)
    simp only [U, Function.update_self] at h1
    have e0 := congrFun h1 0
    have e1 := congrFun h1 1
    simp at e0 e1
    rw [← e0] at e1
    exact mul_left_cancel₀ ha e1

/-- **Core posets give one-parameter families of bricks**, with the moving
line on a sink leaf `t₀` (functional `(t, -1)`, kernel `⟨(1, t)⟩`). -/
theorem not_isRepresentationFinite_sink [Infinite k] (c₀ : K.C)
    (hc₀ : ∀ c, Relation.EqvGen K.cle c₀ c)
    (t₀ : K.T) (hsc : ∀ s, ∃ c, K.sle s c) (htc : ∀ t, ∃ c, K.tle c t)
    (u : K.S → Fin 2 → k) (φ : K.T → Fin 2 → k) (hu : ∀ s, u s ≠ 0)
    (hφ : ∀ t, t ≠ t₀ → φ t ≠ 0)
    (hscalar : ∀ F : (Fin 2 → k) →ₗ[k] (Fin 2 → k),
      (∀ s, ∃ l : k, F (u s) = l • u s) →
      (∀ t, t ≠ t₀ → ∃ m : k, ∀ v, fn k (φ t) (F v) = m * fn k (φ t) v) →
        ∃ a : k, F = a • LinearMap.id) :
    ¬Statement.IsRepresentationFinite (Linearization (ThinCat K.thin) k) := by
  classical
  let Φ : k → K.T → Fin 2 → k := fun t ↦ Function.update φ t₀ ![t, -1]
  have hΦ : ∀ t t₁, Φ t t₁ ≠ 0 := fun t t₁ ↦ by
    by_cases ht : t₁ = t₀
    · subst ht
      simp only [Φ, Function.update_self]
      intro h
      have := congrFun h 1
      simp at this
    · simp only [Φ, Function.update_of_ne ht]
      exact hφ t₁ ht
  have hΦt : ∀ t t₁, t₁ ≠ t₀ → Φ t t₁ = φ t₁ := fun t t₁ ht ↦ Function.update_of_ne ht _ _
  have analyse : ∀ t t' (f : ∀ x, (K.rep u (Φ t)).sp x →ₗ[k] (K.rep u (Φ t')).sp x),
      ThinRep.IsNatural f → ∃ a : k, (∀ c, ∀ v, f (.inl c) v = a • v) ∧
        (∀ s, f (.inl c₀) (u s) = (@id k (f (.inr (.inl s)) (1 : k))) • u s) ∧
        ∀ t₁ v, fn k (Φ t' t₁) (a • v) = (@id k (f (.inr (.inr t₁)) (1 : k))) * fn k (Φ t t₁) v := by
    intro t t' f hf
    have hcore : ∀ c v, f (.inl c) v = f (.inl c₀) v := fun c v ↦ K.core_eq' hf (hc₀ c) v
    have hsrc : ∀ s, f (.inl c₀) (u s) = (@id k (f (.inr (.inl s)) (1 : k))) • u s := by
      intro s
      obtain ⟨c, hc⟩ := hsc s
      exact (hcore c (u s)).symm.trans (K.source_eq hf hc)
    have hsnk : ∀ t₁ v, fn k (Φ t' t₁) (f (.inl c₀) v) =
        (@id k (f (.inr (.inr t₁)) (1 : k))) * fn k (Φ t t₁) v := by
      intro t₁ v
      obtain ⟨c, hc⟩ := htc t₁
      have := K.sink_eq hf hc v
      rwa [hcore c v] at this
    obtain ⟨a, ha⟩ := hscalar (f (.inl c₀) : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
      (fun s ↦ ⟨_, hsrc s⟩)
      (fun t₁ ht₁ ↦ ⟨_, fun v ↦ by have := hsnk t₁ v; rwa [hΦt t t₁ ht₁, hΦt t' t₁ ht₁] at this⟩)
    have hFa : ∀ v : Fin 2 → k, f (.inl c₀) v = a • v := fun v ↦
      (congrArg (fun G : (Fin 2 → k) →ₗ[k] (Fin 2 → k) ↦ G v) ha).trans rfl
    exact ⟨a, fun c v ↦ (hcore c v).trans (hFa v), hsrc, fun t₁ v ↦
      (congrArg (fn k (Φ t' t₁)) (hFa v)).symm.trans (hsnk t₁ v)⟩
  have hfn : ∀ t t₁, ∃ v, fn k (Φ t t₁) v ≠ 0 := fun t t₁ ↦ by
    by_contra h
    push_neg at h
    apply hΦ t t₁
    funext i
    fin_cases i
    · simpa using h ![1, 0]
    · simpa using h ![0, 1]
  refine ThinRep.not_isRepresentationFinite (fun t ↦ K.rep u (Φ t)) (fun t x ↦ ?_)
    (fun t ↦ ⟨.inl c₀, show Nontrivial (Fin 2 → k) from inferInstance⟩) (fun t f hf ↦ ?_)
    (fun t t' f hf hbij ↦ ?_)
  · rcases x with c | s | t
    · exact (inferInstance : FiniteDimensional k (Fin 2 → k))
    · exact (inferInstance : FiniteDimensional k k)
    · exact (inferInstance : FiniteDimensional k k)
  · obtain ⟨a, hc, hs, ht⟩ := analyse t t f hf
    refine ⟨a, fun x ↦ ?_⟩
    rcases x with c | s | t₁
    · exact LinearMap.ext (hc c)
    · have h1 : a • u s = (@id k (f (.inr (.inl s)) (1 : k))) • u s :=
        (hc c₀ (u s)).symm.trans (hs s)
      have h2 : a = (@id k (f (.inr (.inl s)) (1 : k))) := by
        have h3 : (a - (@id k (f (.inr (.inl s)) (1 : k)))) • u s = 0 := by
          rw [sub_smul, h1, sub_self]
        exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right (hu s))
      refine LinearMap.ext fun x ↦ (lin_k (f (.inr (.inl s))) x).trans ?_
      rw [h2]
      rfl
    · obtain ⟨v, hv⟩ := hfn t t₁
      have h1 := ht t₁ v
      rw [LinearMap.map_smul, smul_eq_mul] at h1
      have h2 : a = (@id k (f (.inr (.inr t₁)) (1 : k))) := mul_right_cancel₀ hv h1
      refine LinearMap.ext fun x ↦ (lin_k (f (.inr (.inr t₁))) x).trans ?_
      rw [h2]
      rfl
  · obtain ⟨a, hc, -, ht⟩ := analyse t t' f hf
    have ha : a ≠ 0 := by
      intro h0
      have e0 : (a • (![1, 0] : Fin 2 → k)) = 0 := by rw [h0, zero_smul]
      have e : f (.inl c₀) (![1, 0] : Fin 2 → k) = f (.inl c₀) 0 :=
        ((hc c₀ _).trans e0).trans (map_zero (f (.inl c₀))).symm
      have := congrFun ((hbij (.inl c₀)).1 e) 0
      exact one_ne_zero (this : (1 : k) = 0)
    have e1 := ht t₀ ![1, 0]
    have e2 := ht t₀ ![0, 1]
    simp only [Φ, Function.update_self, fn_apply] at e1 e2
    simp at e1 e2
    rw [← e2] at e1
    exact (mul_left_cancel₀ ha (by rw [mul_comm a t', e1, mul_comm])).symm

end Family

section Lines

universe u

variable {k : Type u} [Field k]

/-- The three standard lines `⟨e₁⟩, ⟨e₂⟩, ⟨(1,1)⟩`: spanning vectors. -/
def lvec : Fin 3 → Fin 2 → k := ![![1, 0], ![0, 1], ![1, 1]]

/-- Functionals with kernels the three standard lines. -/
def lfun : Fin 3 → Fin 2 → k := ![![0, 1], ![1, 0], ![1, -1]]

lemma lvec_ne (i : Fin 3) : (lvec i : Fin 2 → k) ≠ 0 := by
  intro h
  fin_cases i
  · simpa [lvec] using congrFun h 0
  · simpa [lvec] using congrFun h 1
  · simpa [lvec] using congrFun h 0

lemma lfun_ne (i : Fin 3) : (lfun i : Fin 2 → k) ≠ 0 := by
  intro h
  fin_cases i
  · simpa [lfun] using congrFun h 1
  · simpa [lfun] using congrFun h 0
  · simpa [lfun] using congrFun h 0

/-- `F` preserves the `i`-th standard line. -/
def Pres (F : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (i : Fin 3) : Prop := ∃ l : k, F (lvec i) = l • lvec i

lemma pres_of_fun (F : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (i : Fin 3)
    (h : ∃ m : k, ∀ v, fn k (lfun i) (F v) = m * fn k (lfun i) v) : Pres F i := by
  obtain ⟨m, hm⟩ := h
  have hv := hm (lvec i)
  fin_cases i
  · refine ⟨F (lvec 0) 0, funext fun j ↦ ?_⟩
    fin_cases j
    · simp [lvec]
    · simpa [lvec, lfun] using hv
  · refine ⟨F (lvec 1) 1, funext fun j ↦ ?_⟩
    fin_cases j
    · simpa [lvec, lfun] using hv
    · simp [lvec]
  · refine ⟨F (lvec 2) 0, funext fun j ↦ ?_⟩
    fin_cases j
    · simp [lvec]
    · simp [lvec, lfun] at hv ⊢
      linear_combination -hv

/-- **Three lines force scalars.** -/
lemma scalar_of_pres (F : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (h0 : Pres F 0) (h1 : Pres F 1)
    (h2 : Pres F 2) : ∃ a : k, F = a • LinearMap.id := by
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  obtain ⟨c, hc⟩ := h2
  have hsum : lvec (k := k) 2 = lvec 0 + lvec 1 := by
    funext j; fin_cases j <;> simp [lvec]
  have hab : a = c ∧ b = c := by
    rw [hsum, map_add, ha, hb] at hc
    have e0 := congrFun hc 0
    have e1 := congrFun hc 1
    simp [lvec] at e0 e1
    exact ⟨e0, e1⟩
  obtain ⟨hac, hbc⟩ := hab
  have hba : b = a := hbc.trans hac.symm
  refine ⟨a, LinearMap.ext fun v ↦ ?_⟩
  have hv : v = v 0 • lvec 0 + v 1 • lvec 1 := by
    funext j; fin_cases j <;> simp [lvec]
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, ha, hb, hba, LinearMap.smul_apply, LinearMap.id_apply]
  conv_rhs => rw [hv]
  rw [smul_add, smul_comm a (v 0), smul_comm a (v 1)]

variable (K : CoreData) [Fintype K.C] [Fintype K.S] [Fintype K.T] [DecidableEq K.C]
  [DecidableEq K.S] [DecidableEq K.T]

/-- **Line assignments.** A core poset with a connected core is
representation-infinite as soon as its leaves other than one moving leaf
carry the three standard lines, each at least once. This covers every
orientation of `D̃ₘ`. -/
theorem not_isRepresentationFinite_lines [Infinite k] (c₀ : K.C)
    (hc₀ : ∀ c, Relation.EqvGen K.cle c₀ c) (hsc : ∀ s, ∃ c, K.sle s c)
    (htc : ∀ t, ∃ c, K.tle c t) (ls : K.S → Fin 3) (lt : K.T → Fin 3) (mov : K.S ⊕ K.T)
    (hcov : ∀ i : Fin 3, (∃ s, Sum.inl s ≠ mov ∧ ls s = i) ∨ ∃ t, Sum.inr t ≠ mov ∧ lt t = i) :
    ¬Statement.IsRepresentationFinite (Linearization (ThinCat K.thin) k) := by
  have key : ∀ F : (Fin 2 → k) →ₗ[k] (Fin 2 → k),
      (∀ s, Sum.inl s ≠ mov → ∃ l : k, F (lvec (ls s)) = l • lvec (ls s)) →
      (∀ t, Sum.inr t ≠ mov → ∃ m : k, ∀ v, fn k (lfun (lt t)) (F v) = m * fn k (lfun (lt t)) v) →
        ∃ a : k, F = a • LinearMap.id := by
    intro F hs ht
    have hp : ∀ i, Pres F i := fun i ↦ by
      rcases hcov i with ⟨s, hs', rfl⟩ | ⟨t, ht', rfl⟩
      · exact hs s hs'
      · exact pres_of_fun F _ (ht t ht')
    exact scalar_of_pres F (hp 0) (hp 1) (hp 2)
  rcases hmov : mov with s₀ | t₀
  · refine K.not_isRepresentationFinite c₀ hc₀ s₀ hsc htc (fun s ↦ lvec (ls s))
      (fun t ↦ lfun (lt t)) (fun s _ ↦ lvec_ne _) (fun t ↦ lfun_ne _) fun F hs ht ↦
      key F (fun s hs' ↦ hs s fun h ↦ hs' (by rw [h, hmov])) fun t _ ↦ ht t
  · refine K.not_isRepresentationFinite_sink c₀ hc₀ t₀ hsc htc (fun s ↦ lvec (ls s))
      (fun t ↦ lfun (lt t)) (fun s ↦ lvec_ne _) (fun t _ ↦ lfun_ne _) fun F hs ht ↦
      key F (fun s _ ↦ hs s) fun t ht' ↦ ht t fun h ↦ ht' (by rw [h, hmov])

end Lines

end CoreData

end RayCat

end LargeIndecomposable
