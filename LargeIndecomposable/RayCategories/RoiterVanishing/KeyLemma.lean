module

public import LargeIndecomposable.RayCategories.RoiterVanishing.Chain
public import LargeIndecomposable.RayCategories.Basic.Long

/-!
# The key lemma on efficient tackles (BGRS 8.4)

If the last morphism `t` of an efficient hook tackle occurs in a path `v` of an
essential contour `(v, w)`, then `t` is the first arrow of `v`
(`RayCat.key_hook`). The proof is BGRS's alternating induction down the
tackle: at each stage a candidate tackle with larger efficiency is built from
the first or last arrow of `w`; since it cannot be a tackle, a chain
condition fails, and every failure either makes `v` and `w` interlaced or
moves one step down. Left and right cancellation are assumed (they hold for
the ray categories of distributive algebras). Fischbacher's variant (tackles
ending in an arrow of an essential contour) is covered by the admissibility
predicate.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe v u

namespace RayCat

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- Left cancellation for nonzero composites. -/
def LeftCancel (P : Type u) [Category.{v} P] [HasZeroMorphisms P] : Prop :=
  ∀ {x y z : P} (f : x ⟶ y) (g h : y ⟶ z), f ≫ g = f ≫ h → f ≫ g ≠ 0 → g = h

/-- Right cancellation for nonzero composites. -/
def RightCancel (P : Type u) [Category.{v} P] [HasZeroMorphisms P] : Prop :=
  ∀ {x y z : P} (f g : x ⟶ y) (h : y ⟶ z), f ≫ h = g ≫ h → f ≫ h ≠ 0 → f = g

omit [IsRayCategory P] in
lemma interStep_prefix {x a y : RayVert P} (p : Quiver.Path x a) (hp : 0 < p.length)
    (v' w' : Quiver.Path a y) (h : pathVal v' = pathVal w') (h0 : pathVal v' ≠ 0) :
    InterStep (p.comp v') (p.comp w') :=
  ⟨a, y, p, v', w', .nil, by simp, by simp, h, h0, Or.inl hp⟩

omit [IsRayCategory P] in
lemma interStep_suffix {x b y : RayVert P} (v' w' : Quiver.Path x b) (q : Quiver.Path b y)
    (hq : 0 < q.length) (h : pathVal v' = pathVal w') (h0 : pathVal v' ≠ 0) :
    InterStep (v'.comp q) (w'.comp q) :=
  ⟨x, b, .nil, v', w', q, by simp, by simp, h, h0, Or.inr hq⟩

/-- A path for a nonzero morphism. -/
def pathOf {x y : P} (f : x ⟶ y) (hf : f ≠ 0) : Quiver.Path (RayVert.mk x) (RayVert.mk y) :=
  (exists_path f hf).choose

lemma pathVal_pathOf {x y : P} (f : x ⟶ y) (hf : f ≠ 0) : pathVal (pathOf f hf) = f :=
  (exists_path f hf).choose_spec

lemma length_pathOf_pos {x y : P} (f : x ⟶ y) (hf : f ≠ 0) (hiso : ¬IsIso f) :
    0 < (pathOf f hf).length := by
  rcases h : pathOf f hf with _ | ⟨p, e⟩
  · exfalso
    have := pathVal_pathOf f hf
    rw [h] at this
    exact hiso (this ▸ IsIso.id _)
  · simp

omit [IsRayCategory P] in
lemma isIso_pathVal_of_length_zero {x y : RayVert P} (p : Quiver.Path x y) (h : p.length = 0) :
    IsIso (pathVal p) := by
  cases p with
  | nil => exact IsIso.id _
  | cons p e => simp at h

omit [IsRayCategory P] in
lemma pathVal_toPath {x y : RayVert P} (e : x ⟶ y) : pathVal e.toPath = e.1 :=
  Category.id_comp _

/-- A nonzero split monomorphism is invertible. -/
lemma isIso_of_isIso_comp {x y z : P} (f : x ⟶ y) (g : y ⟶ z) (hf : f ≠ 0) (h : IsIso (f ≫ g)) :
    IsIso f := by
  have hr : f ≫ (g ≫ inv (f ≫ g)) = 𝟙 x := by rw [← Category.assoc, IsIso.hom_inv_id]
  have hfix : f ≫ (g ≫ inv (f ≫ g) ≫ f) = f := by
    rw [← Category.assoc, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  by_cases he : g ≫ inv (f ≫ g) ≫ f = 𝟙 y
  · exact ⟨⟨g ≫ inv (f ≫ g), hr, by rw [Category.assoc]; exact he⟩⟩
  · exact absurd (IsRayCategory.eq_zero_of_comp_end f _ he hfix) hf

/-- A nonempty path has a non-invertible value. -/
lemma not_isIso_pathVal {x y : RayVert P} (p : Quiver.Path x y) (hp : 0 < p.length) :
    ¬IsIso (pathVal p) := by
  intro hiso
  obtain ⟨hxy, he⟩ := eq_eqToHom_of_isIso (pathVal p)
  change x = y at hxy
  subst hxy
  exact pathVal_ne_id_of_length p hp he

omit [HasZeroMorphisms P] [IsRayCategory P] in
lemma not_isIso_of_peak {f g : RayMor P} (h : Peak f g) : ¬IsIso f.2.2 := by
  obtain ⟨he, -, h2⟩ := h
  intro hf
  exact h2 ⟨g.2.2 ≫ eqToHom he.symm ≫ inv f.2.2, by simp⟩

omit [HasZeroMorphisms P] [IsRayCategory P] in
lemma not_isIso_of_valley {f g : RayMor P} (h : Valley f g) : ¬IsIso f.2.2 := by
  obtain ⟨he, h1, -⟩ := h
  intro hf
  exact h1 ⟨inv f.2.2 ≫ eqToHom he ≫ g.2.2, by simp⟩

omit [IsRayCategory P] in
/-- Entries of a tackle are not invertible. -/
lemma not_isIso_entry {adm : RayMor P → Prop} {o : ℕ} {l : List (RayMor P)}
    (hl : IsTackle adm o l) (k : ℕ) (hk : k < l.length) : ¬IsIso l[k].2.2 := by
  obtain ⟨hne, hch, hirr, -⟩ := hl
  by_cases hk' : k + 1 < l.length
  · have := hch.2 k hk'
    unfold Link at this
    split_ifs at this
    · exact not_isIso_of_peak this
    · exact not_isIso_of_valley this
  · have hlast : l[k] = l.getLast hne := by
      rw [List.getLast_eq_getElem]
      congr 1
      omega
    rw [hlast]
    exact hirr.2.1

section Key

variable (adm : RayMor P → Prop) (o : ℕ) (l : List (RayMor P)) {x y : RayVert P}
  (v w : Quiver.Path x y)

/-- Stage at position `k`: a path interlaced with `v` through the `k`-th entry
(with its endpoints renamed along equations). -/
def Stage (k : ℕ) (hk : k < l.length) : Prop :=
  ∃ (X Z : P) (hX : l[k].1 = X) (hZ : l[k].2.1 = Z) (p : Quiver.Path x (RayVert.mk X))
    (r : Quiver.Path (RayVert.mk X) (RayVert.mk Z)) (q : Quiver.Path (RayVert.mk Z) y),
    0 < p.length ∧ pathVal r = eqToHom hX.symm ≫ l[k].2.2 ≫ eqToHom hZ ∧
      ((k + 1 = l.length ∧ (k + o) % 2 = 0) ∨ 0 < q.length) ∧ Interlaced v ((p.comp r).comp q)

variable {adm o l v w}

omit [IsRayCategory P] in
lemma pathVal_comp_comp {x a b y : RayVert P} (p : Quiver.Path x a) (r : Quiver.Path a b)
    (q : Quiver.Path b y) : pathVal ((p.comp r).comp q) = pathVal p ≫ pathVal r ≫ pathVal q := by
  rw [pathVal_comp, pathVal_comp, Category.assoc]

/-- The cohook step (even positions). -/
lemma step_even (hR : RightCancel P) (hl : IsEfficient adm o l) (k : ℕ) (hk : k < l.length)
    (hev : (k + o) % 2 = 0) {yζ : RayVert P} (w₂ : Quiver.Path x yζ) (ζ : yζ ⟶ y)
    (hw : w = w₂.cons ζ) (hadm : adm ⟨yζ.out, y.out, ζ.1⟩) (hvw : pathVal v = pathVal w)
    (hv0 : pathVal v ≠ 0) (hni : ¬Interlaced v w) (hst : Stage o l v k hk) :
    ∃ hk0 : 0 < k, Stage o l v (k - 1) (by omega) := by
  obtain ⟨X, Z, hX, hZ, p, r, q, hp, hr, hq, hint⟩ := hst
  subst hX hZ
  have hr' : pathVal r = l[k].2.2 := by rw [hr]; simp
  have hval : pathVal p ≫ l[k].2.2 ≫ pathVal q = pathVal v := by
    rw [← hr', ← pathVal_comp_comp]
    exact (interlaced_val hint).symm
  have hf0 : l[k].2.2 ≫ pathVal q ≠ 0 := fun h0 ↦ hv0 (by rw [← hval, h0, comp_zero])
  have hρ : ¬IsIso l[k].2.2 := not_isIso_entry hl.1 k hk
  have hρ0 : l[k].2.2 ≠ 0 := fun h0 ↦ hf0 (by rw [h0, zero_comp])
  have hrl : 0 < r.length := by
    by_contra h0
    exact hρ (hr' ▸ isIso_pathVal_of_length_zero r (by omega))
  -- the peak condition between `ρ ū` and `ζ`
  have hpeak : Peak (⟨l[k].1, y.out, l[k].2.2 ≫ pathVal q⟩ : RayMor P) ⟨yζ.out, y.out, ζ.1⟩ := by
    refine ⟨rfl, ?_, ?_⟩
    · rintro ⟨c, hc⟩
      simp only [eqToHom_refl, Category.comp_id] at hc
      have hc0 : c ≠ 0 := fun h0 ↦ hf0 (by rw [← hc, h0, zero_comp])
      let γ := pathOf c hc0
      apply hni
      have h1 : Interlaced ((p.comp r).comp q) ((p.comp γ).cons ζ) := by
        refine Relation.EqvGen.rel _ _ ?_
        rw [Quiver.Path.comp_assoc, ← Quiver.Path.comp_cons]
        refine interStep_prefix p hp _ _ ?_ ?_
        · rw [pathVal_comp, hr']
          change _ = pathVal γ ≫ ζ.1
          rw [pathVal_pathOf, hc]
        · rw [pathVal_comp, hr']
          exact hf0
      have h2 : Interlaced ((p.comp γ).cons ζ) w := by
        rw [hw]
        refine Relation.EqvGen.rel _ _ ?_
        have e1 : ∀ {b : RayVert P} (s : Quiver.Path x b) (e : b ⟶ y),
            s.cons e = s.comp ((Quiver.Path.nil).cons e) := fun s e ↦ rfl
        rw [e1, e1 w₂]
        refine interStep_suffix _ _ _ (by simp) ?_ ?_
        · refine hR _ _ ζ.1 ?_ ?_
          · rw [pathVal_comp, pathVal_pathOf, Category.assoc, hc, hval, hvw, hw]
            rfl
          · rw [pathVal_comp, pathVal_pathOf, Category.assoc, hc, hval]
            exact hv0
        · rw [pathVal_comp, pathVal_pathOf]
          intro h0
          apply hv0
          rw [← hval, ← hc, ← Category.assoc, h0, zero_comp]
      exact hint.trans _ _ _ (h1.trans _ _ _ h2)
    · rintro ⟨c, hc⟩
      simp only [eqToHom_refl, Category.comp_id] at hc
      rcases ζ.2.2.2 _ c _ hc.symm with hci | hci
      · obtain ⟨hy, rfl⟩ := eq_eqToHom_of_isIso c
        change yζ = RayVert.mk l[k].1 at hy
        subst hy
        have hc2 : ζ.1 = l[k].2.2 ≫ pathVal q := by
          rw [← hc]
          change 𝟙 _ ≫ l[k].2.2 ≫ pathVal q = _
          rw [Category.id_comp]
        rcases ζ.2.2.2 _ _ _ hc2 with h1 | h1
        · exact hρ h1
        · have hq0 : q.length = 0 := by
            by_contra h0
            exact not_isIso_pathVal q (by omega) h1
          have hy := Quiver.Path.eq_of_length_zero q hq0
          subst hy
          have hqn := Quiver.Path.eq_nil_of_length_zero q hq0
          subst hqn
          have hc3 : ζ.1 = l[k].2.2 := by rw [hc2]; exact Category.comp_id _
          have hval2 : pathVal p ≫ l[k].2.2 = pathVal v := by
            rw [← hval]; simp [pathVal]
          apply hni
          have h1 : Interlaced ((p.comp r).comp Quiver.Path.nil) (p.comp (Quiver.Path.nil.cons ζ)) := by
            refine Relation.EqvGen.rel _ _ ?_
            rw [Quiver.Path.comp_nil]
            refine interStep_prefix p hp _ _ ?_ ?_
            · rw [hr']
              change _ = 𝟙 _ ≫ ζ.1
              rw [Category.id_comp, hc3]
            · rw [hr']
              exact hρ0
          have h2 : Interlaced (p.comp (Quiver.Path.nil.cons ζ)) w := by
            rw [hw]
            refine Relation.EqvGen.rel _ _ ?_
            change InterStep (p.comp (Quiver.Path.nil.cons ζ)) (w₂.comp (Quiver.Path.nil.cons ζ))
            refine interStep_suffix _ _ _ (by simp) ?_ ?_
            · refine hR _ _ ζ.1 ?_ ?_
              · rw [hc3, hval2, hvw, hw]
                change pathVal w₂ ≫ ζ.1 = _
                rw [hc3]
              · rw [hc3, hval2]
                exact hv0
            · intro h0
              apply hv0
              rw [← hval2, h0, zero_comp]
          exact hint.trans _ _ _ (h1.trans _ _ _ h2)
      · exact not_isIso_pathVal (r.comp q) (by simp; omega) (by rw [pathVal_comp, hr']; exact hci)
  -- data of the tackle `l`
  obtain ⟨hne, hch, -, -⟩ := hl.1
  have hζ0 : ζ.1 ≠ 0 := ζ.2.1
  -- the candidate tackle and its efficiency
  have hcand : ∀ (hlink : ∀ h : 0 < k, Link (k - 1 + o) (l[k - 1]'(by omega))
      (⟨l[k].1, y.out, l[k].2.2 ≫ pathVal q⟩ : RayMor P)),
      IsTackle adm o (l.take k ++ [⟨l[k].1, y.out, l[k].2.2 ≫ pathVal q⟩, ⟨yζ.out, y.out, ζ.1⟩]) := by
    intro hlink
    have hgl := getLast_append_pair (l.take k)
      (⟨l[k].1, y.out, l[k].2.2 ≫ pathVal q⟩ : RayMor P) ⟨yζ.out, y.out, ζ.1⟩ (by simp)
    refine ⟨by simp, isChain_take_append l hch k hk.le _ _ hf0 hζ0 hlink ?_, ?_, ?_⟩
    · simp only [Link, hev, ↓reduceIte]
      exact hpeak
    · rw [hgl]
      exact ζ.2
    · rw [hgl]
      exact hadm
  have hlex : List.Lex (· < ·) (efficiency l) (efficiency (l.take k ++
      [⟨l[k].1, y.out, l[k].2.2 ≫ pathVal q⟩, ⟨yζ.out, y.out, ζ.1⟩])) := by
    refine lex_candidate l k hk _ _ (depth_le_comp_right _ _ hf0) ?_
    rcases hq with hq | hq
    · exact Or.inl hq.1
    · exact Or.inr (depth_lt_comp_right _ _ hf0 (not_isIso_pathVal q hq))
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · exact absurd hlex (hl.2 _ (hcand fun h ↦ absurd h (by omega)))
  refine ⟨hk0, ?_⟩
  -- the valley between `σ = l[k-1]` and `ρ`
  have hodd : (k - 1 + o) % 2 ≠ 0 := by omega
  have hvalley : Valley (l[k - 1]'(by omega)) l[k] := by
    have := hch.2 (k - 1) (by omega)
    simp only [Link, hodd, ↓reduceIte] at this
    convert this using 2
    simp [Nat.sub_add_cancel hk0]
  obtain ⟨hσρ, hv1, hv2⟩ := hvalley
  by_cases hgood : ∃ c : (l[k - 1]'(by omega)).2.1 ⟶ y.out,
      eqToHom hσρ.symm ≫ (l[k - 1]'(by omega)).2.2 ≫ c = l[k].2.2 ≫ pathVal q
  · obtain ⟨c, hc⟩ := hgood
    have hσ0 : (l[k - 1]'(by omega)).2.2 ≠ 0 := hch.1 _ (List.getElem_mem _)
    have hσ'0 : eqToHom hσρ.symm ≫ (l[k - 1]'(by omega)).2.2 ≠ 0 := by
      intro h0
      apply hσ0
      have := congrArg (fun t ↦ eqToHom hσρ ≫ t) h0
      simpa using this
    have hc0 : c ≠ 0 := fun h0 ↦ hf0 (by rw [← hc, h0, comp_zero, comp_zero])
    have hcni : ¬IsIso c := by
      intro hci
      apply hv2
      refine ⟨pathVal q ≫ inv c, ?_⟩
      rw [← Category.assoc (l[k].2.2), ← hc]
      simp
    refine ⟨l[k].1, (l[k - 1]'(by omega)).2.1, hσρ, rfl, p,
      pathOf _ hσ'0, pathOf (y := y.out) c hc0, hp, ?_,
      Or.inr (length_pathOf_pos c hc0 hcni), ?_⟩
    · rw [pathVal_pathOf]
      simp
    · refine hint.trans _ _ _ (Relation.EqvGen.rel _ _ ?_)
      rw [Quiver.Path.comp_assoc, Quiver.Path.comp_assoc]
      refine interStep_prefix p hp _ _ ?_ ?_
      · rw [pathVal_comp, pathVal_comp, hr', pathVal_pathOf, pathVal_pathOf, Category.assoc, hc]
      · rw [pathVal_comp, hr']
        exact hf0
  · exfalso
    refine hl.2 _ (hcand fun _ ↦ ?_) hlex
    simp only [Link, hodd, ↓reduceIte]
    refine ⟨hσρ, hgood, ?_⟩
    rintro ⟨c, hc⟩
    exact hv2 ⟨pathVal q ≫ c, by simpa [Category.assoc] using hc⟩

/-- The hook step (odd positions). -/
lemma step_odd (hL : LeftCancel P) (hl : IsEfficient adm o l) (k : ℕ) (hk : k < l.length)
    (hod : (k + o) % 2 = 1) {yα : RayVert P} (α : x ⟶ yα) (w₃ : Quiver.Path yα y)
    (hw : w = α.toPath.comp w₃) (hadm : adm ⟨x.out, yα.out, α.1⟩)
    (hvw : pathVal v = pathVal w) (hv0 : pathVal v ≠ 0) (hni : ¬Interlaced v w)
    (hst : Stage o l v k hk) : ∃ hk0 : 0 < k, Stage o l v (k - 1) (by omega) := by
  obtain ⟨X, Z, hX, hZ, p, r, q, hp, hr, hq, hint⟩ := hst
  subst hX hZ
  have hq' : 0 < q.length := hq.resolve_left (by omega)
  have hr' : pathVal r = l[k].2.2 := by rw [hr]; simp
  have hval : pathVal p ≫ l[k].2.2 ≫ pathVal q = pathVal v := by
    rw [← hr', ← pathVal_comp_comp]
    exact (interlaced_val hint).symm
  have hf0 : pathVal p ≫ l[k].2.2 ≠ 0 := fun h0 ↦
    hv0 (by rw [← hval, ← Category.assoc, h0, zero_comp])
  have hσ : ¬IsIso l[k].2.2 := not_isIso_entry hl.1 k hk
  have hσ0 : l[k].2.2 ≠ 0 := fun h0 ↦ hf0 (by rw [h0, comp_zero])
  have hpi : ¬IsIso (pathVal p) := not_isIso_pathVal p hp
  obtain ⟨hne, hch, -, -⟩ := hl.1
  -- the valley between `p σ` and `α`
  have hvalley : Valley (⟨x.out, l[k].2.1, pathVal p ≫ l[k].2.2⟩ : RayMor P)
      ⟨x.out, yα.out, α.1⟩ := by
    refine ⟨rfl, ?_, ?_⟩
    · rintro ⟨c, hc⟩
      simp only [eqToHom_refl, Category.id_comp, Category.assoc] at hc
      rcases α.2.2.2 _ _ _ hc.symm with h1 | h1
      · exact hpi h1
      · exact hσ (isIso_of_isIso_comp _ _ hσ0 h1)
    · rintro ⟨c, hc⟩
      simp only [eqToHom_refl, Category.id_comp] at hc
      have hc0 : c ≠ 0 := fun h0 ↦ hf0 (by rw [← hc, h0, comp_zero])
      apply hni
      let γ := pathOf (x := yα.out) c hc0
      have hαγ : α.1 ≫ pathVal (γ.comp q) = pathVal v := by
        rw [pathVal_comp, pathVal_pathOf, ← Category.assoc, hc, Category.assoc, hval]
      have hw₃ : α.1 ≫ pathVal w₃ = pathVal v := by
        rw [hvw, hw, pathVal_comp, pathVal_toPath]
      have h1 : Interlaced ((p.comp r).comp q) ((α.toPath.comp γ).comp q) := by
        refine Relation.EqvGen.rel _ _ (interStep_suffix _ _ q hq' ?_ ?_)
        · rw [pathVal_comp, pathVal_comp, hr', pathVal_toPath, pathVal_pathOf, hc]
        · rw [pathVal_comp, hr']
          exact hf0
      have h2 : Interlaced ((α.toPath.comp γ).comp q) w := by
        rw [hw, Quiver.Path.comp_assoc]
        refine Relation.EqvGen.rel _ _ (interStep_prefix _ (by simp) _ _ ?_ ?_)
        · exact hL α.1 _ _ (by rw [hαγ, hw₃]) (by rw [hαγ]; exact hv0)
        · intro h0
          apply hv0
          rw [← hαγ, h0, comp_zero]
      exact hint.trans _ _ _ (h1.trans _ _ _ h2)
  have hcand : ∀ (hlink : ∀ h : 0 < k, Link (k - 1 + o) (l[k - 1]'(by omega))
      (⟨x.out, l[k].2.1, pathVal p ≫ l[k].2.2⟩ : RayMor P)),
      IsTackle adm o (l.take k ++ [⟨x.out, l[k].2.1, pathVal p ≫ l[k].2.2⟩,
        ⟨x.out, yα.out, α.1⟩]) := by
    intro hlink
    have hgl := getLast_append_pair (l.take k)
      (⟨x.out, l[k].2.1, pathVal p ≫ l[k].2.2⟩ : RayMor P) ⟨x.out, yα.out, α.1⟩ (by simp)
    refine ⟨by simp, isChain_take_append l hch k hk.le _ _ hf0 α.2.1 hlink ?_, ?_, ?_⟩
    · simp only [Link, show (k + o) % 2 ≠ 0 by omega, ↓reduceIte]
      exact hvalley
    · rw [hgl]
      exact α.2
    · rw [hgl]
      exact hadm
  have hlt : depth l[k].2.2 < depth (pathVal p ≫ l[k].2.2) := depth_lt_comp_left _ _ hf0 hpi
  have hlex : List.Lex (· < ·) (efficiency l) (efficiency (l.take k ++
      [⟨x.out, l[k].2.1, pathVal p ≫ l[k].2.2⟩, ⟨x.out, yα.out, α.1⟩])) :=
    lex_candidate l k hk _ _ hlt.le (Or.inr hlt)
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · exact absurd hlex (hl.2 _ (hcand fun h ↦ absurd h (by omega)))
  refine ⟨hk0, ?_⟩
  -- the peak between `ρ = l[k-1]` and `σ = l[k]`
  have hpk : Peak (l[k - 1]'(by omega)) l[k] := by
    have := hch.2 (k - 1) (by omega)
    simp only [Link, show (k - 1 + o) % 2 = 0 by omega, ↓reduceIte] at this
    convert this using 2
    simp [Nat.sub_add_cancel hk0]
  obtain ⟨hρσ, hp1, hp2⟩ := hpk
  by_cases hgood : ∃ c : x.out ⟶ (l[k - 1]'(by omega)).1,
      c ≫ (l[k - 1]'(by omega)).2.2 ≫ eqToHom hρσ = pathVal p ≫ l[k].2.2
  · obtain ⟨c, hc⟩ := hgood
    have hc0 : c ≠ 0 := fun h0 ↦ hf0 (by rw [← hc, h0, zero_comp])
    have hcni : ¬IsIso c := fun hci ↦
      hp1 ⟨inv c ≫ pathVal p, by rw [Category.assoc, ← hc, IsIso.inv_hom_id_assoc]⟩
    have hρ0 : (l[k - 1]'(by omega)).2.2 ≫ eqToHom hρσ ≠ 0 := fun h0 ↦
      hf0 (by rw [← hc, h0, comp_zero])
    refine ⟨(l[k - 1]'(by omega)).1, l[k].2.1, rfl, hρσ, pathOf (x := x.out) c hc0,
      pathOf _ hρ0, q, length_pathOf_pos c hc0 hcni, ?_, Or.inr hq', ?_⟩
    · rw [pathVal_pathOf]
      simp
    · refine hint.trans _ _ _ (Relation.EqvGen.rel _ _ (interStep_suffix _ _ q hq' ?_ ?_))
      · rw [pathVal_comp, pathVal_comp, hr', pathVal_pathOf, pathVal_pathOf, hc]
      · rw [pathVal_comp, hr']
        exact hf0
  · exfalso
    refine hl.2 _ (hcand fun _ ↦ ?_) hlex
    simp only [Link, show (k - 1 + o) % 2 = 0 by omega, ↓reduceIte]
    refine ⟨hρσ, ?_, hgood⟩
    rintro ⟨c, hc⟩
    exact hp1 ⟨c ≫ pathVal p, by rw [Category.assoc]; exact hc⟩

/-- No stage exists: the alternating induction ends in an interlacing of `v`
and `w`. -/
theorem not_stage (hL : LeftCancel P) (hR : RightCancel P) (hl : IsEfficient adm o l)
    {yα yζ : RayVert P} (α : x ⟶ yα) (w₃ : Quiver.Path yα y) (hwα : w = α.toPath.comp w₃)
    (hadmα : adm ⟨x.out, yα.out, α.1⟩) (w₂ : Quiver.Path x yζ) (ζ : yζ ⟶ y)
    (hwζ : w = w₂.cons ζ) (hadmζ : adm ⟨yζ.out, y.out, ζ.1⟩) (hvw : pathVal v = pathVal w)
    (hv0 : pathVal v ≠ 0) (hni : ¬Interlaced v w) :
    ∀ (k : ℕ) (hk : k < l.length), ¬Stage o l v k hk := by
  intro k
  induction k with
  | zero =>
    intro hk hst
    rcases Nat.mod_two_eq_zero_or_one (0 + o) with h | h
    · obtain ⟨h, -⟩ := step_even hR hl 0 hk h w₂ ζ hwζ hadmζ hvw hv0 hni hst
      omega
    · obtain ⟨h, -⟩ := step_odd hL hl 0 hk h α w₃ hwα hadmα hvw hv0 hni hst
      omega
  | succ k ih =>
    intro hk hst
    rcases Nat.mod_two_eq_zero_or_one (k + 1 + o) with h | h
    · obtain ⟨_, h'⟩ := step_even hR hl (k + 1) hk h w₂ ζ hwζ hadmζ hvw hv0 hni hst
      exact ih _ h'
    · obtain ⟨_, h'⟩ := step_odd hL hl (k + 1) hk h α w₃ hwα hadmα hvw hv0 hni hst
      exact ih _ h'

end Key

/-- **Key lemma** (BGRS 8.4, hook case). Let `l` be an efficient tackle whose
last link is a valley (`m + o` even), and `(v, w)` an essential contour
whose first and last arrows are admissible. If `v` passes through a path `r`
for `l[m]`, then `r` starts at the beginning of `v`. -/
theorem key_hook {adm : RayMor P → Prop} {o : ℕ} {l : List (RayMor P)} {x y : RayVert P}
    {v w : Quiver.Path x y} (hL : LeftCancel P) (hR : RightCancel P) (hl : IsEfficient adm o l)
    (m : ℕ) (hm : m + 1 = l.length) (hev : (m + o) % 2 = 0)
    {yα yζ : RayVert P} (α : x ⟶ yα) (w₃ : Quiver.Path yα y) (hwα : w = α.toPath.comp w₃)
    (hadmα : adm ⟨x.out, yα.out, α.1⟩) (w₂ : Quiver.Path x yζ) (ζ : yζ ⟶ y)
    (hwζ : w = w₂.cons ζ) (hadmζ : adm ⟨yζ.out, y.out, ζ.1⟩) (hvw : pathVal v = pathVal w)
    (hv0 : pathVal v ≠ 0) (hni : ¬Interlaced v w)
    (X Z : P) (hX : l[m].1 = X) (hZ : l[m].2.1 = Z) (p : Quiver.Path x (RayVert.mk X))
    (r : Quiver.Path (RayVert.mk X) (RayVert.mk Z)) (u : Quiver.Path (RayVert.mk Z) y)
    (hr : pathVal r = eqToHom hX.symm ≫ l[m].2.2 ≫ eqToHom hZ) (hv : v = (p.comp r).comp u) :
    p.length = 0 := by
  by_contra hp
  refine not_stage hL hR hl α w₃ hwα hadmα w₂ ζ hwζ hadmζ hvw hv0 hni m (by omega)
    ⟨X, Z, hX, hZ, p, r, u, by omega, hr, Or.inl ⟨hm, hev⟩, ?_⟩
  rw [← hv]
  exact Relation.EqvGen.refl _

end RayCat

end LargeIndecomposable
