module

public import LargeIndecomposable.FundamentalGroups.Fischbacher.BWalk

/-!
# Chains of arrows out of a point, minimal for the Dershowitz–Manna order

`BChain c P α β` is a walk of links between arrows out of `c`, each link a nonzero common upper
bound with target in `P`. Among chains between two arrows we take one whose multiset of bound
depths is minimal for the Dershowitz–Manna order (`exists_minC`). Every contiguous piece of a
minimal chain is minimal; a minimal link joins distinct arrows (`IsMinC.ne`), and two minimal
consecutive links satisfy the valley condition at their common arrow (`IsMinC.valley`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

universe v u

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [IsRayCategory A]

/-- A link between two arrows out of `c`: a nonzero common upper bound with target in `P`. -/
structure BLink (c : A) (P : A → Prop) (α β : OutA c) where
  e : A
  x : α.1 ⟶ e
  y : β.1 ⟶ e
  eq : α.2.1 ≫ x = β.2.1 ≫ y
  ne : α.2.1 ≫ x ≠ 0
  he : P e

variable {c : A} {P : A → Prop}

/-- The depth of the bound of a link. -/
def BLink.dep {α β : OutA c} (s : BLink c P α β) : ℕ := depth (α.2.1 ≫ s.x)

/-- Chains of links. -/
inductive BChain (c : A) (P : A → Prop) : OutA c → OutA c → Type (max u v)
  | nil (α : OutA c) : BChain c P α α
  | cons {α β γ : OutA c} (s : BLink c P α β) (W : BChain c P β γ) : BChain c P α γ

namespace BChain

/-- The multiset of bound depths. -/
def bms : ∀ {α β : OutA c}, BChain c P α β → Multiset ℕ
  | _, _, nil _ => 0
  | _, _, cons s W => {s.dep} + bms W

/-- Concatenation. -/
def append : ∀ {α β γ : OutA c}, BChain c P α β → BChain c P β γ → BChain c P α γ
  | _, _, _, nil _, W' => W'
  | _, _, _, cons s W, W' => cons s (append W W')

lemma bms_append : ∀ {α β γ : OutA c} (W : BChain c P α β) (W' : BChain c P β γ),
    (W.append W').bms = W.bms + W'.bms
  | _, _, _, nil _, W' => by simp [append, bms]
  | _, _, _, cons s W, W' => by simp [append, bms, bms_append W W', add_assoc]

end BChain

open BChain

/-- A chain from a list walk. -/
lemma nonempty_bchain : ∀ {α β : OutA c} (L : List (BStep c P)), IsBWalk α β L →
    Nonempty (BChain c P α β)
  | α, β, [], h => by change α = β at h; subst h; exact ⟨nil α⟩
  | α, β, s :: L, ⟨h₁, h₂⟩ => by
    subst h₁
    obtain ⟨W⟩ := nonempty_bchain L h₂
    exact ⟨cons ⟨s.e, s.x, s.y, s.eq, s.ne, s.he⟩ W⟩

/-- A chain is minimal: no chain between the same arrows has a smaller multiset of depths. -/
def IsMinC {α β : OutA c} (W : BChain c P α β) : Prop :=
  ∀ W' : BChain c P α β, ¬Multiset.IsDershowitzMannaLT W'.bms W.bms

/-- **A minimal chain exists.** -/
lemma exists_minC {α β : OutA c} (h : Nonempty (BChain c P α β)) :
    ∃ W : BChain c P α β, IsMinC W := by
  obtain ⟨W, -, hW⟩ := (InvImage.wf (fun W : BChain c P α β ↦ W.bms)
    Multiset.wellFounded_isDershowitzMannaLT).has_min Set.univ
    (let ⟨W⟩ := h; ⟨W, trivial⟩)
  exact ⟨W, fun W' ↦ hW W' trivial⟩

lemma dm_add_left {X M N : Multiset ℕ} (h : Multiset.IsDershowitzMannaLT M N) :
    Multiset.IsDershowitzMannaLT (X + M) (X + N) := by
  obtain ⟨X', Y, Z, hZ, rfl, rfl, hYZ⟩ := h
  exact ⟨X + X', Y, Z, hZ, by rw [add_assoc], by rw [add_assoc], hYZ⟩

lemma dm_add_right {X M N : Multiset ℕ} (h : Multiset.IsDershowitzMannaLT M N) :
    Multiset.IsDershowitzMannaLT (M + X) (N + X) := by
  rw [add_comm M, add_comm N]; exact dm_add_left h

/-- Pieces of minimal chains are minimal. -/
lemma IsMinC.left {α β γ : OutA c} {W : BChain c P α β} {W' : BChain c P β γ}
    (h : IsMinC (W.append W')) : IsMinC W := fun W₁ hlt ↦
  h (W₁.append W') (by rw [BChain.bms_append, BChain.bms_append]; exact dm_add_right hlt)

lemma IsMinC.right {α β γ : OutA c} {W : BChain c P α β} {W' : BChain c P β γ}
    (h : IsMinC (W.append W')) : IsMinC W' := fun W₁ hlt ↦
  h (W.append W₁) (by rw [BChain.bms_append, BChain.bms_append]; exact dm_add_left hlt)

lemma IsMinC.tail {α β γ : OutA c} {s : BLink c P α β} {W : BChain c P β γ}
    (h : IsMinC (cons s W)) : IsMinC W :=
  IsMinC.right (W := cons s (nil β)) h

lemma IsMinC.head {α β γ : OutA c} {s : BLink c P α β} {W : BChain c P β γ}
    (h : IsMinC (cons s W)) : IsMinC (cons s (nil β)) :=
  IsMinC.left (W' := W) h

/-- **A minimal link joins distinct arrows.** -/
lemma IsMinC.ne {α β : OutA c} {s : BLink c P α β} (h : IsMinC (cons s (nil β))) : α ≠ β := by
  rintro rfl
  exact h (nil α) ⟨0, 0, {s.dep}, by simp, by simp [BChain.bms], by simp [BChain.bms], by simp⟩

/-- **Valley condition** at the common arrow of two minimal consecutive links. -/
lemma IsMinC.valley {α β γ : OutA c} {s : BLink c P α β} {s' : BLink c P β γ}
    (h : IsMinC (cons s (cons s' (nil γ)))) :
    (¬∃ k : s.e ⟶ s'.e, s.y ≫ k = s'.x) ∧ ¬∃ k : s'.e ⟶ s.e, s'.x ≫ k = s.y := by
  refine ⟨fun ⟨k, hk⟩ ↦ ?_, fun ⟨k, hk⟩ ↦ ?_⟩
  · -- merge into one link with bound `s'`
    let l : BLink c P α γ := ⟨s'.e, s.x ≫ k, s'.y,
      by rw [← Category.assoc, s.eq, Category.assoc, hk, s'.eq],
      by rw [← Category.assoc, s.eq, Category.assoc, hk]; exact s'.ne, s'.he⟩
    have hd : l.dep = s'.dep := by
      change depth (α.2.1 ≫ s.x ≫ k) = depth (β.2.1 ≫ s'.x)
      rw [← Category.assoc, s.eq, Category.assoc, hk]
    refine h (cons l (nil γ)) ⟨{s'.dep}, 0, {s.dep}, by simp, ?_, ?_, by simp⟩
    · simp [BChain.bms, hd]
    · simp [BChain.bms, add_comm]
  · -- merge into one link with bound `s`
    let l : BLink c P α γ := ⟨s.e, s.x, s'.y ≫ k,
      by rw [s.eq, ← hk, ← Category.assoc, s'.eq, Category.assoc], s.ne, s.he⟩
    refine h (cons l (nil γ)) ⟨{s.dep}, 0, {s'.dep}, by simp, ?_, ?_, by simp⟩
    · simp [BChain.bms, BLink.dep]; rfl
    · simp [BChain.bms, BLink.dep]

namespace BChain

/-- The bound targets of a chain. -/
def bounds : ∀ {α β : OutA c}, BChain c P α β → List A
  | _, _, nil _ => []
  | _, _, cons s W => s.e :: bounds W

lemma exists_of_mem_bounds : ∀ {α β : OutA c} (W : BChain c P α β) {e : A}, e ∈ W.bounds →
    ∃ (β' γ' : OutA c) (M₁ : BChain c P α β') (s' : BLink c P β' γ') (M₂ : BChain c P γ' β),
      W = M₁.append (cons s' M₂) ∧ s'.e = e
  | _, _, nil _, _, h => by simp [bounds] at h
  | _, _, cons s W, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, _, nil _, s, W, rfl, rfl⟩
    · obtain ⟨β', γ', M₁, s', M₂, hW, he⟩ := exists_of_mem_bounds W h
      exact ⟨β', γ', cons s M₁, s', M₂, by rw [hW]; rfl, he⟩

end BChain

lemma BLink.x_ne {α β : OutA c} (s : BLink c P α β) : s.x ≠ 0 := fun h ↦
  s.ne (by rw [h, comp_zero])

lemma BLink.y_ne {α β : OutA c} (s : BLink c P α β) : s.y ≠ 0 := fun h ↦
  s.ne (by rw [s.eq, h, comp_zero])

lemma pathVal_toPath_comp {x y z : RayVert A} (α : x ⟶ y) (p : Quiver.Path y z) :
    pathVal (α.toPath.comp p) = α.1 ≫ pathVal p := by
  rw [pathVal_comp]
  change (𝟙 _ ≫ α.1) ≫ _ = _
  rw [Category.id_comp]

/-- **The bound targets of a minimal chain are pairwise distinct** (via Lemma 4.2). -/
theorem IsMinC.nodup (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)),
      p.length = 0)
    (hint : ∀ a b : A, (interval a b).Finite)
    (hsc : ∀ D : Set A, D.Finite → ConvexR D → ∀ c : ArrowWeight A, IsCocycleOn D c →
      IsCoboundaryOn D c) :
    ∀ {α β : OutA c} {W : BChain c P α β}, IsMinC W → W.bounds.Nodup
  | _, _, BChain.nil _, _ => List.nodup_nil
  | α, β, BChain.cons s W, h => by
    refine List.nodup_cons.2 ⟨fun hmem ↦ ?_, IsMinC.nodup hcf hint hsc h.tail⟩
    obtain ⟨β', γ', M₁, s', M₂, rfl, he⟩ := W.exists_of_mem_bounds hmem
    obtain ⟨e', x', y', eq', ne', he'⟩ := s'
    change e' = s.e at he
    subst he
    have hval : α.2.1 ≫ s.x = γ'.2.1 ≫ y' := by
      have := par hcf hint hsc (α.2.toPath.comp (pathOf s.x s.x_ne))
        (γ'.2.toPath.comp (pathOf y' fun h ↦ ne' (by rw [eq', h, comp_zero])))
      rwa [pathVal_toPath_comp, pathVal_toPath_comp, pathVal_pathOf, pathVal_pathOf] at this
    let l : BLink c P α γ' := ⟨s.e, s.x, y', hval, s.ne, s.he⟩
    refine h (BChain.cons l M₂) ⟨{s.dep} + M₂.bms, 0, M₁.bms + {depth (β'.2.1 ≫ x')}, by simp,
      by simp [BChain.bms, BLink.dep]; rfl, ?_, by simp⟩
    simp only [BChain.bms, BChain.bms_append, BLink.dep]
    abel

/-- The first arrow of a path out of `c`. -/
def firstArr : ∀ {y : RayVert A}, Quiver.Path (RayVert.mk c) y → Option (OutA c)
  | _, .nil => none
  | _, .cons .nil e => some ⟨_, e⟩
  | _, .cons (.cons p e') _ => firstArr (p.cons e')

lemma firstArr_cons {b y : RayVert A} (r : Quiver.Path (RayVert.mk c) b) (hr : 0 < r.length)
    (e : b ⟶ y) : firstArr (r.cons e) = firstArr r := by
  rcases r with _ | ⟨r, e'⟩
  · simp at hr
  · rfl

lemma length_comp_pos {x b y : RayVert A} (p : Quiver.Path x b) (hp : 0 < p.length)
    (q : Quiver.Path b y) : 0 < (p.comp q).length := by
  rw [Quiver.Path.length_comp]; omega

lemma firstArr_comp {b : RayVert A} (p : Quiver.Path (RayVert.mk c) b) (hp : 0 < p.length) :
    ∀ {y : RayVert A} (q : Quiver.Path b y), firstArr (p.comp q) = firstArr p
  | _, .nil => rfl
  | _, .cons q e => by
    change firstArr ((p.comp q).cons e) = _
    rw [firstArr_cons _ (length_comp_pos p hp q), firstArr_comp p hp q]

lemma firstArr_toPath {y : A} (α : RayVert.mk c ⟶ RayVert.mk y) :
    firstArr α.toPath = some ⟨y, α⟩ := rfl

lemma firstArr_isSome : ∀ {y : RayVert A} (p : Quiver.Path (RayVert.mk c) y), 0 < p.length →
    ∃ γ, firstArr p = some γ
  | _, .nil, h => by simp at h
  | _, .cons .nil e, _ => ⟨_, rfl⟩
  | _, .cons (.cons p e') _, _ => firstArr_isSome (p.cons e') (by simp)

lemma eq_comp_of_firstArr : ∀ {y : RayVert A} (p : Quiver.Path (RayVert.mk c) y) {γ : OutA c},
    firstArr p = some γ → ∃ r : Quiver.Path (RayVert.mk γ.1) y, p = γ.2.toPath.comp r
  | _, .nil, _, h => by simp [firstArr] at h
  | _, .cons .nil e, γ, h => by
    simp only [firstArr, Option.some.injEq] at h
    subst h
    exact ⟨.nil, rfl⟩
  | _, .cons (.cons p e') e, γ, h => by
    obtain ⟨r, hr⟩ := eq_comp_of_firstArr (p.cons e') h
    exact ⟨r.cons e, by rw [hr]; rfl⟩

lemma pathVal_of_interStep {x y : RayVert A} {π π' : Quiver.Path x y} (h : InterStep π π') :
    pathVal π = pathVal π' := by
  obtain ⟨a, b, p, v', w', q, rfl, rfl, hvw, -, -⟩ := h
  rw [pathVal_comp, pathVal_comp, pathVal_comp, pathVal_comp, hvw]

/-- Reversing a link. -/
def BLink.swap {α β : OutA c} (s : BLink c P α β) : BLink c P β α :=
  ⟨s.e, s.y, s.x, s.eq.symm, by rw [← s.eq]; exact s.ne, s.he⟩

lemma BLink.dep_swap {α β : OutA c} (s : BLink c P α β) : s.swap.dep = s.dep := by
  change depth (β.2.1 ≫ s.y) = depth (α.2.1 ≫ s.x)
  rw [s.eq]

variable (hcf : ∀ (x : A) (p : Quiver.Path (RayVert.mk x) (RayVert.mk x)), p.length = 0)
include hcf

/-- One interlacing step keeps the first arrow, or changes it along a link with a shallower
bound. -/
lemma interStep_first {e : A} {μ : c ⟶ e} (hμ : μ ≠ 0)
    (hP : ∀ b' : A, Reaches c b' → Reaches b' e → b' ≠ c → P b')
    {π π' : Quiver.Path (RayVert.mk c) (RayVert.mk e)} (h : InterStep π π')
    (hv : pathVal π = μ) :
    firstArr π = firstArr π' ∨ ∃ (γ γ' : OutA c) (l : BLink c P γ γ'),
      firstArr π = some γ ∧ firstArr π' = some γ' ∧ l.dep < depth μ := by
  obtain ⟨a, b, p, v', w', q, rfl, rfl, hvw, hv0, hpq⟩ := h
  by_cases hp : 0 < p.length
  · left
    rw [Quiver.Path.comp_assoc, Quiver.Path.comp_assoc, firstArr_comp p hp, firstArr_comp p hp]
  have hp0 : p.length = 0 := by omega
  have hq : 0 < q.length := hpq.resolve_left hp
  obtain rfl : RayVert.mk c = a := Quiver.Path.eq_of_length_zero p hp0
  obtain rfl := Quiver.Path.eq_nil_of_length_zero p hp0
  simp only [Quiver.Path.nil_comp] at hv ⊢
  by_cases hv' : 0 < v'.length
  · have hw' : 0 < w'.length := by
      by_contra h0
      obtain rfl : RayVert.mk c = b := Quiver.Path.eq_of_length_zero w' (by omega)
      have := hcf c v'
      omega
    right
    obtain ⟨γ, hγ⟩ := firstArr_isSome v' hv'
    obtain ⟨γ', hγ'⟩ := firstArr_isSome w' hw'
    obtain ⟨r, hr⟩ := eq_comp_of_firstArr v' hγ
    obtain ⟨r', hr'⟩ := eq_comp_of_firstArr w' hγ'
    have hbc : b.out ≠ c := by
      intro hb
      have hb' : b = RayVert.mk c := hb
      subst hb'
      have := hcf _ v'
      omega
    have hval : γ.2.1 ≫ pathVal r = γ'.2.1 ≫ pathVal r' := by
      rw [← pathVal_toPath_comp, ← pathVal_toPath_comp, ← hr, ← hr', hvw]
    have hne : γ.2.1 ≫ pathVal r ≠ 0 := by rw [← pathVal_toPath_comp, ← hr]; exact hv0
    refine ⟨γ, γ', ⟨b.out, pathVal r, pathVal r', hval, hne,
      hP b.out ⟨v'⟩ ⟨q⟩ hbc⟩, by rw [firstArr_comp v' hv', hγ],
      by rw [firstArr_comp w' hw', hγ'], ?_⟩
    change depth (γ.2.1 ≫ pathVal r) < depth μ
    rw [← pathVal_toPath_comp, ← hr, ← hv, pathVal_comp]
    exact depth_lt_comp_right _ _ (by rw [← pathVal_comp, hv]; exact hμ)
      (not_isIso_pathVal q hq)
  · left
    have hv0' : v'.length = 0 := by omega
    obtain rfl : RayVert.mk c = b := Quiver.Path.eq_of_length_zero v' hv0'
    rw [Quiver.Path.eq_nil_of_length_zero v' hv0', Quiver.Path.eq_nil_of_length_zero w' (hcf c w')]

omit hcf in
/-- Split a chain at the last link whose bound satisfies `Q`. -/
lemma BChain.split_last (Q : A → Prop) : ∀ {α β : OutA c} (W : BChain c P α β),
    (∀ e ∈ W.bounds, ¬Q e) ∨ ∃ (α'' α' : OutA c) (W₀ : BChain c P α α'') (l : BLink c P α'' α')
      (W₂ : BChain c P α' β), W = W₀.append (BChain.cons l W₂) ∧ Q l.e ∧ ∀ e ∈ W₂.bounds, ¬Q e
  | _, _, BChain.nil _ => Or.inl (by simp [BChain.bounds])
  | _, _, BChain.cons l W => by
    rcases BChain.split_last Q W with h | ⟨α'', α', W₀, l', W₂, rfl, hQ, hW₂⟩
    · by_cases hl : Q l.e
      · exact Or.inr ⟨_, _, BChain.nil _, l, W, rfl, hl, h⟩
      · left
        intro e he
        rcases List.mem_cons.1 he with rfl | he
        · exact hl
        · exact h e he
    · exact Or.inr ⟨α'', α', BChain.cons l W₀, l', W₂, rfl, hQ, hW₂⟩

omit hcf in
/-- Split a chain at the first link whose bound satisfies `Q`. -/
lemma BChain.split_first (Q : A → Prop) : ∀ {α β : OutA c} (W : BChain c P α β),
    (∀ e ∈ W.bounds, ¬Q e) ∨ ∃ (α'' α' : OutA c) (W₀ : BChain c P α α'') (l : BLink c P α'' α')
      (W₂ : BChain c P α' β), W = W₀.append (BChain.cons l W₂) ∧ Q l.e ∧ ∀ e ∈ W₀.bounds, ¬Q e
  | _, _, BChain.nil _ => Or.inl (by simp [BChain.bounds])
  | _, _, BChain.cons l W => by
    by_cases hl : Q l.e
    · exact Or.inr ⟨_, _, BChain.nil _, l, W, rfl, hl, by simp [BChain.bounds]⟩
    · rcases BChain.split_first Q W with h | ⟨α'', α', W₀, l', W₂, rfl, hQ, hW₀⟩
      · left
        intro e he
        rcases List.mem_cons.1 he with rfl | he
        · exact hl
        · exact h e he
      · refine Or.inr ⟨α'', α', BChain.cons l W₀, l', W₂, rfl, hQ, fun e he ↦ ?_⟩
        rcases List.mem_cons.1 he with rfl | he
        · exact hl
        · exact hW₀ e he

omit hcf in
/-- A nonempty chain ends with a link. -/
lemma BChain.eq_snoc : ∀ {α β : OutA c} (W : BChain c P α β),
    W.bounds = [] ∨ ∃ (α' : OutA c) (W' : BChain c P α α') (l : BLink c P α' β),
        W = W'.append (BChain.cons l (BChain.nil β))
  | _, _, BChain.nil _ => Or.inl rfl
  | _, _, BChain.cons l W => by
    rcases BChain.eq_snoc W with h | ⟨α', W', l', rfl⟩
    · cases W with
      | nil => exact Or.inr ⟨_, BChain.nil _, l, rfl⟩
      | cons l' W' => simp [BChain.bounds] at h
    · exact Or.inr ⟨α', BChain.cons l W', l', rfl⟩

omit hcf in
lemma BChain.bounds_append : ∀ {α β γ : OutA c} (W : BChain c P α β) (W' : BChain c P β γ),
    (W.append W').bounds = W.bounds ++ W'.bounds
  | _, _, _, BChain.nil _, _ => rfl
  | _, _, _, BChain.cons l W, W' => by
    simp [BChain.append, BChain.bounds, BChain.bounds_append W W']

omit hcf in
lemma BChain.append_assoc : ∀ {α β γ δ : OutA c} (W₁ : BChain c P α β) (W₂ : BChain c P β γ)
    (W₃ : BChain c P γ δ), (W₁.append W₂).append W₃ = W₁.append (W₂.append W₃)
  | _, _, _, _, BChain.nil _, _, _ => rfl
  | _, _, _, _, BChain.cons l W₁, W₂, W₃ => by
    simp only [BChain.append, BChain.append_assoc W₁ W₂ W₃]

omit hcf in
lemma length_pos_of_ne {e : A} (π : Quiver.Path (RayVert.mk c) (RayVert.mk e)) (hec : e ≠ c) :
    0 < π.length := by
  by_contra h0
  exact hec (Quiver.Path.eq_of_length_zero π (by omega)).symm

/-- **An interlaced contour gives a chain with shallower bounds** between its first arrows. -/
theorem small_chain_of_interlaced {e : A} {μ : c ⟶ e} (hμ : μ ≠ 0) (hec : e ≠ c)
    (hP : ∀ b' : A, Reaches c b' → Reaches b' e → b' ≠ c → P b')
    {π₁ π₂ : Quiver.Path (RayVert.mk c) (RayVert.mk e)} (h : Interlaced π₁ π₂)
    (hv : pathVal π₁ = μ) {α β : OutA c} (hα : firstArr π₁ = some α)
    (hβ : firstArr π₂ = some β) : ∃ W : BChain c P α β, ∀ d ∈ W.bms, d < depth μ := by
  rw [Interlaced, ← Relation.EqvGen.reflTransGen_symmGen] at h
  suffices H : ∀ π, Relation.ReflTransGen (Relation.SymmGen InterStep) π₁ π →
      pathVal π = μ ∧ ∀ γ, firstArr π = some γ → ∃ W : BChain c P α γ, ∀ d ∈ W.bms, d < depth μ
    from (H π₂ h).2 β hβ
  intro π hπ
  induction hπ with
  | refl =>
    refine ⟨hv, fun γ hγ ↦ ?_⟩
    rw [hα, Option.some.injEq] at hγ
    subst hγ
    exact ⟨BChain.nil α, by simp [BChain.bms]⟩
  | @tail π π' _ hstep ih =>
    obtain ⟨hvπ, ihW⟩ := ih
    obtain ⟨γ₀, hγ₀⟩ := firstArr_isSome π (length_pos_of_ne π hec)
    obtain ⟨W₀, hW₀⟩ := ihW γ₀ hγ₀
    have hvπ' : pathVal π' = μ := by
      rcases hstep with hs | hs
      · rw [← pathVal_of_interStep hs, hvπ]
      · rw [pathVal_of_interStep hs, hvπ]
    refine ⟨hvπ', fun γ hγ ↦ ?_⟩
    have hext : ∀ l : BLink c P γ₀ γ, l.dep < depth μ →
        ∃ W : BChain c P α γ, ∀ d ∈ W.bms, d < depth μ := by
      intro l hl
      refine ⟨W₀.append (BChain.cons l (BChain.nil γ)), fun d hd ↦ ?_⟩
      rw [BChain.bms_append, Multiset.mem_add] at hd
      rcases hd with hd | hd
      · exact hW₀ d hd
      · simp [BChain.bms] at hd
        rw [hd]; exact hl
    rcases hstep with hs | hs
    · rcases interStep_first hcf hμ hP hs hvπ with heq | ⟨γ₁, γ₁', l, h1, h2, hd⟩
      · rw [hγ₀, hγ, Option.some.injEq] at heq
        subst heq
        exact ⟨W₀, hW₀⟩
      · rw [hγ₀, Option.some.injEq] at h1
        rw [hγ, Option.some.injEq] at h2
        subst h1 h2
        exact hext l hd
    · rcases interStep_first hcf hμ hP hs hvπ' with heq | ⟨γ₁, γ₁', l, h1, h2, hd⟩
      · rw [hγ₀, hγ, Option.some.injEq] at heq
        subst heq
        exact ⟨W₀, hW₀⟩
      · rw [hγ, Option.some.injEq] at h1
        rw [hγ₀, Option.some.injEq] at h2
        subst h1 h2
        exact hext l.swap (by rw [BLink.dep_swap]; exact hd)

/-- **The contour of a minimal link is essential.** -/
theorem IsMinC.essential {α β : OutA c} {s : BLink c P α β} (h : IsMinC (BChain.cons s (BChain.nil β)))
    (hP : ∀ b' : A, Reaches c b' → Reaches b' s.e → b' ≠ c → P b') (hec : s.e ≠ c) :
    ¬Interlaced (α.2.toPath.comp (pathOf s.x s.x_ne)) (β.2.toPath.comp (pathOf s.y s.y_ne)) := by
  intro hI
  have hv : pathVal (α.2.toPath.comp (pathOf s.x s.x_ne)) = α.2.1 ≫ s.x := by
    rw [pathVal_toPath_comp, pathVal_pathOf]
  have hα : firstArr (α.2.toPath.comp (pathOf s.x s.x_ne)) = some α := by
    rw [firstArr_comp _ (by simp), firstArr_toPath]
  have hβ : firstArr (β.2.toPath.comp (pathOf s.y s.y_ne)) = some β := by
    rw [firstArr_comp _ (by simp), firstArr_toPath]
  obtain ⟨W, hW⟩ := small_chain_of_interlaced hcf s.ne hec hP hI hv hα hβ
  exact h W ⟨0, W.bms, {s.dep}, by simp, by simp, by simp [BChain.bms],
    fun y hy ↦ ⟨s.dep, by simp, hW y hy⟩⟩

end LargeIndecomposable.RayCat
