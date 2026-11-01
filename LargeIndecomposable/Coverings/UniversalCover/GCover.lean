module

public import LargeIndecomposable.RayCategories.Basic.Long
public import LargeIndecomposable.RayCategories.Basic.Prefix

/-!
# Galois covers of a ray category

A voltage `V` on a ray category `P` assigns to every morphism an element of a group `H`,
multiplicatively on nonzero composites. The Galois cover `GCover V` has objects `(y, h)` with
`y : P`, `h : H`; a nonzero morphism `(y, h) ⟶ (z, h')` is a nonzero `f : y ⟶ z` with
`h' = h · V(f)`, and composition is that of `P` (zero when the composite vanishes). It is a ray
category, finite when `P` and `H` are (`finite_gcover`). Cancellation and chain-boundedness pass
from `P` to the cover (`leftCancel_gcover`, `rightCancel_gcover`, `chainBounded_gcover`), and
irreducible morphisms correspond (`isIrreducible_val`, `isIrreducible_liftAt`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

universe v u

/-- A voltage: a group-valued function on morphisms, multiplicative on nonzero composites. -/
structure Voltage (P : Type u) [Category.{v} P] [HasZeroMorphisms P] (H : Type) [Group H] where
  /-- The value of a morphism. -/
  w : ∀ {x y : P}, (x ⟶ y) → H
  w_id : ∀ x : P, w (𝟙 x) = 1
  w_comp : ∀ {x y z : P} (f : x ⟶ y) (g : y ⟶ z), f ≫ g ≠ 0 → w (f ≫ g) = w f * w g

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P] [IsRayCategory P]
  {H : Type} [Group H]

/-- The objects of the Galois cover. -/
@[nolint unusedArguments]
structure GCover (_V : Voltage P H) where
  /-- The underlying object. -/
  y : P
  /-- The sheet. -/
  h : H

namespace GCover

variable {V : Voltage P H}

/-- The nonzero morphisms of the Galois cover. -/
def NZHom (a b : GCover V) : Type v :=
  {f : a.y ⟶ b.y // f ≠ 0 ∧ b.h = a.h * V.w f}

/-- Composition of nonzero morphisms, zero if the composite vanishes. -/
def compNZ {a b c : GCover V} (f : NZHom a b) (g : NZHom b c) : Option (NZHom a c) := by
  classical
  exact if hfg : f.1 ≫ g.1 = 0 then none else
    some ⟨f.1 ≫ g.1, hfg, by rw [V.w_comp _ _ hfg, ← mul_assoc, ← f.2.2]; exact g.2.2⟩

/-- The underlying morphism of `P` (zero for `none`). -/
def val {a b : GCover V} : Option (NZHom a b) → (a.y ⟶ b.y)
  | none => 0
  | some f => f.1

lemma val_injective {a b : GCover V} : Function.Injective (val (a := a) (b := b)) := by
  rintro (_ | f) (_ | g) h
  · rfl
  · exact absurd h.symm g.2.1
  · exact absurd h f.2.1
  · exact congrArg some (Subtype.ext h)

/-- The composite of two morphisms. -/
def comp' {a b c : GCover V} (f : Option (NZHom a b)) (g : Option (NZHom b c)) :
    Option (NZHom a c) :=
  f.bind fun f ↦ g.bind fun g ↦ compNZ f g

lemma val_comp' {a b c : GCover V} (f : Option (NZHom a b)) (g : Option (NZHom b c)) :
    val (comp' f g) = val f ≫ val g := by
  rcases f with _ | f
  · exact (zero_comp).symm
  rcases g with _ | g
  · exact (comp_zero).symm
  change val (compNZ f g) = f.1 ≫ g.1
  unfold compNZ
  split_ifs with h
  · exact h.symm
  · rfl

instance : Category.{v} (GCover V) where
  Hom a b := Option (NZHom a b)
  id a := some ⟨𝟙 a.y, IsRayCategory.id_ne_zero a.y, by rw [V.w_id, mul_one]⟩
  comp f g := comp' f g
  id_comp f := val_injective (by rw [val_comp']; exact Category.id_comp _)
  comp_id f := val_injective (by rw [val_comp']; exact Category.comp_id _)
  assoc f g h := val_injective (by rw [val_comp', val_comp', val_comp', val_comp', Category.assoc])

lemma val_comp {a b c : GCover V} (f : a ⟶ b) (g : b ⟶ c) : val (f ≫ g) = val f ≫ val g :=
  val_comp' f g

lemma val_id (a : GCover V) : val (𝟙 a) = 𝟙 a.y := rfl

instance : HasZeroMorphisms (GCover V) where
  zero _ _ := ⟨none⟩
  comp_zero _ _ := val_injective (by rw [val_comp]; exact comp_zero)
  zero_comp _ _ _ _ := val_injective (by rw [val_comp]; exact zero_comp)

lemma val_zero {a b : GCover V} : val (0 : a ⟶ b) = 0 := rfl

lemma val_eq_zero_iff {a b : GCover V} (f : a ⟶ b) : val f = 0 ↔ f = 0 :=
  ⟨fun h ↦ val_injective h, fun h ↦ h ▸ val_zero⟩

lemma val_ne_zero {a b : GCover V} {f : a ⟶ b} (hf : f ≠ 0) : val f ≠ 0 :=
  fun h ↦ hf ((val_eq_zero_iff _).1 h)

/-- The sheet of the target of a nonzero morphism. -/
lemma h_eq {a b : GCover V} (f : a ⟶ b) (hf : f ≠ 0) : b.h = a.h * V.w (val f) := by
  rcases f with _ | f
  · exact absurd rfl hf
  exact f.2.2

variable (V) in
/-- The covering functor `GCover V ⥤ P`. -/
def proj : GCover V ⥤ P where
  obj a := a.y
  map f := val f
  map_id _ := rfl
  map_comp f g := val_comp f g

lemma val_rpow {a : GCover V} (e : a ⟶ a) : ∀ n, val (rpow e n) = rpow (val e) n
  | 0 => rfl
  | n + 1 => by rw [rpow_succ, rpow_succ, val_comp, val_rpow e n]

omit [IsRayCategory P] in
lemma ext' {a b : GCover V} (hy : a.y = b.y) (hh : a.h = b.h) : a = b := by
  obtain ⟨y, h⟩ := a
  obtain ⟨y', h'⟩ := b
  change y = y' at hy
  change h = h' at hh
  subst hy hh
  rfl

instance : IsRayCategory (GCover V) where
  skeletal a b h := by
    obtain ⟨i⟩ := h
    have h1 : val i.hom ≫ val i.inv = 𝟙 a.y := by rw [← val_comp, i.hom_inv_id]; rfl
    have h2 : val i.inv ≫ val i.hom = 𝟙 b.y := by rw [← val_comp, i.inv_hom_id]; rfl
    have hy : a.y = b.y := IsRayCategory.skeletal ⟨⟨_, _, h1, h2⟩⟩
    obtain ⟨y, k⟩ := a
    obtain ⟨y', k'⟩ := b
    change y = y' at hy
    subst hy
    rcases hi : i.hom with _ | f
    · exact absurd (by rw [hi] at h1; simpa [val] using h1.symm) (IsRayCategory.id_ne_zero y)
    · have hf1 : f.1 = 𝟙 y := by
        have e : 𝟙 y = f.1 ≫ 𝟙 y ≫ val i.inv := by rw [Category.id_comp, ← h1, hi]; rfl
        exact (IsRayCategory.eq_id_of_two_sided _ (IsRayCategory.id_ne_zero y) _ _ e).1
      obtain ⟨-, hfh⟩ := f.2
      change k' = k * V.w f.1 at hfh
      rw [hf1, V.w_id, mul_one] at hfh
      rw [hfh]
  finite_out a := by
    classical
    have hfin := IsRayCategory.finite_out a.y
    let T : Set (GCover V) := ⋃ z ∈ {z : P | ∃ f : a.y ⟶ z, f ≠ 0},
      Set.range (fun f : {f : a.y ⟶ z // f ≠ 0} ↦ (⟨z, a.h * V.w f.1⟩ : GCover V))
    have hT : T.Finite := Set.Finite.biUnion hfin fun z _ ↦ by
      have := IsRayCategory.finite_hom a.y z
      exact Set.finite_range _
    refine hT.subset ?_
    rintro b ⟨f, hf⟩
    rcases f with _ | f
    · exact absurd rfl hf
    · obtain ⟨hf0, hfh⟩ := f.2
      simp only [T, Set.mem_iUnion, Set.mem_range]
      exact ⟨b.y, ⟨f.1, hf0⟩, ⟨f.1, hf0⟩, ext' rfl hfh.symm⟩
  finite_in a := by
    classical
    have hfin := IsRayCategory.finite_in a.y
    let T : Set (GCover V) := ⋃ z ∈ {z : P | ∃ f : z ⟶ a.y, f ≠ 0},
      Set.range (fun f : {f : z ⟶ a.y // f ≠ 0} ↦ (⟨z, a.h * (V.w f.1)⁻¹⟩ : GCover V))
    have hT : T.Finite := Set.Finite.biUnion hfin fun z _ ↦ by
      have := IsRayCategory.finite_hom z a.y
      exact Set.finite_range _
    refine hT.subset ?_
    rintro b ⟨f, hf⟩
    rcases f with _ | f
    · exact absurd rfl hf
    · obtain ⟨hf0, hfh⟩ := f.2
      simp only [T, Set.mem_iUnion, Set.mem_range]
      refine ⟨b.y, ⟨f.1, hf0⟩, ⟨f.1, hf0⟩, ext' rfl ?_⟩
      change a.h = b.h * V.w f.1 at hfh
      change a.h * (V.w f.1)⁻¹ = b.h
      rw [eq_comm, eq_mul_inv_iff_mul_eq]
      exact hfh.symm
  finite_hom a b := by
    have := IsRayCategory.finite_hom a.y b.y
    change Finite (Option (NZHom a b))
    unfold NZHom
    infer_instance
  id_ne_zero a h := Option.some_ne_none _ h
  nil a e he := by
    have hv : val e ≠ 𝟙 a.y := fun h ↦ he (val_injective (h.trans (val_id a).symm))
    obtain ⟨n, hn⟩ := IsRayCategory.nil a.y (val e) hv
    exact ⟨n, (val_eq_zero_iff _).1 ((val_rpow e n).trans hn)⟩

/-- The Galois cover of a finite ray category by a finite group is finite. -/
instance finite_gcover [Finite P] [Finite H] : Finite (GCover V) :=
  Finite.of_injective (fun a : GCover V ↦ (a.y, a.h)) fun a b h ↦
    ext' (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- The lift of a nonzero morphism starting at `a`. -/
def liftAt (a : GCover V) {z : P} (f : a.y ⟶ z) (hf : f ≠ 0) :
    a ⟶ (⟨z, a.h * V.w f⟩ : GCover V) :=
  some ⟨f, hf, rfl⟩

lemma val_liftAt (a : GCover V) {z : P} (f : a.y ⟶ z) (hf : f ≠ 0) :
    val (liftAt a f hf) = f := rfl

lemma isIso_val {a b : GCover V} (f : a ⟶ b) [IsIso f] : IsIso (val f) :=
  inferInstanceAs (IsIso ((proj V).map f))

lemma isIso_of_isIso_val {a b : GCover V} (g : a ⟶ b) (hg : IsIso (val g)) : IsIso g := by
  obtain ⟨hy, he⟩ := eq_eqToHom_of_isIso (val g)
  obtain ⟨y, k⟩ := a
  obtain ⟨y', k'⟩ := b
  change y = y' at hy
  subst hy
  have h1 : val g = 𝟙 y := he
  rcases g with _ | g
  · exact absurd h1.symm (IsRayCategory.id_ne_zero y)
  obtain ⟨hg0, hgh⟩ := g.2
  obtain rfl : k' = k := by
    change k' = k * V.w g.1 at hgh
    change g.1 = 𝟙 y at h1
    rw [hgh, h1, V.w_id, mul_one]
  have : (some g : (⟨y, k'⟩ : GCover V) ⟶ ⟨y, k'⟩) = 𝟙 (⟨y, k'⟩ : GCover V) :=
    val_injective (h1.trans (val_id (⟨y, k'⟩ : GCover V)).symm)
  rw [this]
  infer_instance

/-- The image of an irreducible morphism of the cover is irreducible. -/
theorem isIrreducible_val {a b : GCover V} {f : a ⟶ b} (hf : IsIrreducible f) :
    IsIrreducible (val f) := by
  have hf0 : val f ≠ 0 := val_ne_zero hf.1
  refine ⟨hf0, fun hiso ↦ hf.2.1 (isIso_of_isIso_val f hiso), fun z g k hgk ↦ ?_⟩
  have hg : g ≠ 0 := fun h0 ↦ hf0 (by rw [hgk, h0, zero_comp])
  have hk : k ≠ 0 := fun h0 ↦ hf0 (by rw [hgk, h0, comp_zero])
  let g' := liftAt a g hg
  let k' : (⟨z, a.h * V.w g⟩ : GCover V) ⟶ b := some ⟨k, hk, by
    rw [mul_assoc, ← V.w_comp g k (by rw [← hgk]; exact hf0), ← hgk]
    exact h_eq f hf.1⟩
  have hfac : f = g' ≫ k' := val_injective (by rw [val_comp]; exact hgk)
  rcases hf.2.2 _ g' k' hfac with h1 | h1
  · exact Or.inl (isIso_val g')
  · exact Or.inr (isIso_val k')

/-- The lift of an irreducible morphism is irreducible. -/
theorem isIrreducible_liftAt (a : GCover V) {z : P} {f : a.y ⟶ z} (hf : IsIrreducible f) :
    IsIrreducible (liftAt a f hf.1) := by
  refine ⟨fun h ↦ Option.some_ne_none _ h, fun hiso ↦ ?_, fun c g k hgk ↦ ?_⟩
  · exact hf.2.1 (isIso_val (liftAt a f hf.1))
  · have := congrArg val hgk
    rw [val_comp, val_liftAt] at this
    rcases hf.2.2 _ _ _ this with h1 | h1
    · exact Or.inl (isIso_of_isIso_val g h1)
    · exact Or.inr (isIso_of_isIso_val k h1)

end GCover

open GCover

variable {V : Voltage P H}

lemma leftCancel_gcover (hL : LeftCancel P) : LeftCancel (GCover V) := by
  intro a b c f g h hfg h0
  apply val_injective
  refine hL (val f) (val g) (val h) ?_ ?_
  · rw [← val_comp, ← val_comp, hfg]
  · rw [← val_comp]
    exact fun h' ↦ h0 ((val_eq_zero_iff _).1 h')

lemma rightCancel_gcover (hR : RightCancel P) : RightCancel (GCover V) := by
  intro a b c f g h hfg h0
  apply val_injective
  refine hR (val f) (val g) (val h) ?_ ?_
  · rw [← val_comp, ← val_comp, hfg]
  · rw [← val_comp]
    exact fun h' ↦ h0 ((val_eq_zero_iff _).1 h')

namespace GCover

/-- A factorization `c ≫ val g = val f` of nonzero morphisms with a common target lifts. -/
lemma exists_lift_left {a a' b : GCover V} (f : a ⟶ b) (g : a' ⟶ b) (hf : f ≠ 0) (hg : g ≠ 0)
    (c : a.y ⟶ a'.y) (hc : c ≫ val g = val f) : ∃ C : a ⟶ a', C ≫ g = f := by
  have hfc : c ≫ val g ≠ 0 := hc ▸ val_ne_zero hf
  have hc0 : c ≠ 0 := fun h ↦ hfc (by rw [h, zero_comp])
  have hh : a'.h = a.h * V.w c := by
    have h1 := h_eq f hf
    have h2 := h_eq g hg
    rw [← hc, V.w_comp _ _ hfc, ← mul_assoc, h2] at h1
    exact mul_right_cancel h1.symm |>.symm
  refine ⟨some ⟨c, hc0, hh⟩, val_injective ?_⟩
  rw [val_comp]
  exact hc

/-- A factorization `val f ≫ c = val g` of nonzero morphisms with a common source lifts. -/
lemma exists_lift_right {a b b' : GCover V} (f : a ⟶ b) (g : a ⟶ b') (hf : f ≠ 0) (hg : g ≠ 0)
    (c : b.y ⟶ b'.y) (hc : val f ≫ c = val g) : ∃ C : b ⟶ b', f ≫ C = g := by
  have hfc : val f ≫ c ≠ 0 := hc ▸ val_ne_zero hg
  have hc0 : c ≠ 0 := fun h ↦ hfc (by rw [h, comp_zero])
  have hh : b'.h = b.h * V.w c := by
    rw [h_eq g hg, ← hc, V.w_comp _ _ hfc, h_eq f hf, mul_assoc]
  refine ⟨some ⟨c, hc0, hh⟩, val_injective ?_⟩
  rw [val_comp]
  exact hc

end GCover

/-- The projection of a morphism of the cover. -/
def projRMG (F : RayMor (GCover V)) : RayMor P := ⟨F.1.y, F.2.1.y, val F.2.2⟩

lemma peak_projRMG {F G : RayMor (GCover V)} (hF : F.2.2 ≠ 0) (hG : G.2.2 ≠ 0) (h : Peak F G) :
    Peak (projRMG F) (projRMG G) := by
  obtain ⟨a, b, f⟩ := F
  obtain ⟨a', b', g⟩ := G
  obtain ⟨hb, h1, h2⟩ := h
  change b = b' at hb
  subst hb
  simp only [eqToHom_refl, Category.comp_id] at h1 h2
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨c, hc⟩
    change c ≫ val g = val f ≫ eqToHom (rfl : b.y = b.y) at hc
    rw [eqToHom_refl, Category.comp_id] at hc
    obtain ⟨C, hC⟩ := exists_lift_left f g hF hG c hc
    exact h1 ⟨C, hC⟩
  · rintro ⟨c, hc⟩
    change c ≫ val f ≫ eqToHom (rfl : b.y = b.y) = val g at hc
    have hc' : c ≫ val f = val g :=
      (congrArg (c ≫ ·) (Category.comp_id (val f))).symm.trans hc
    obtain ⟨C, hC⟩ := exists_lift_left g f hG hF c hc'
    exact h2 ⟨C, hC⟩

lemma valley_projRMG {F G : RayMor (GCover V)} (hF : F.2.2 ≠ 0) (hG : G.2.2 ≠ 0)
    (h : Valley F G) : Valley (projRMG F) (projRMG G) := by
  obtain ⟨a, b, f⟩ := F
  obtain ⟨a', b', g⟩ := G
  obtain ⟨ha, h1, h2⟩ := h
  change a = a' at ha
  subst ha
  simp only [eqToHom_refl, Category.id_comp] at h1 h2
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨c, hc⟩
    change eqToHom (rfl : a.y = a.y) ≫ val f ≫ c = val g at hc
    rw [eqToHom_refl, Category.id_comp] at hc
    obtain ⟨C, hC⟩ := exists_lift_right f g hF hG c hc
    exact h1 ⟨C, hC⟩
  · rintro ⟨c, hc⟩
    change eqToHom (rfl : a.y = a.y) ≫ val g ≫ c = val f at hc
    rw [eqToHom_refl, Category.id_comp] at hc
    obtain ⟨C, hC⟩ := exists_lift_right g f hG hF c hc
    exact h2 ⟨C, hC⟩

lemma isChain_map_projRMG {o : ℕ} {l : List (RayMor (GCover V))} (hl : IsChain o l) :
    IsChain o (l.map projRMG) := by
  refine ⟨fun f hf ↦ ?_, fun j hj ↦ ?_⟩
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact val_ne_zero (hl.1 g hg)
  · rw [List.length_map] at hj
    have hl' := hl.2 j hj
    have h0 := hl.1 _ (List.getElem_mem (show j < l.length by omega))
    have h1 := hl.1 _ (List.getElem_mem hj)
    simp only [List.getElem_map]
    unfold Link at hl' ⊢
    split_ifs at hl' ⊢
    · exact peak_projRMG h0 h1 hl'
    · exact valley_projRMG h0 h1 hl'

/-- **Chain-boundedness passes to Galois covers.** -/
lemma chainBounded_gcover (hCB : ChainBounded P) : ChainBounded (GCover V) := by
  obtain ⟨N, hN⟩ := hCB
  refine ⟨N, fun l hl ↦ ?_⟩
  have := hN _ (isChain_map_projRMG hl)
  rwa [List.length_map] at this

end LargeIndecomposable.RayCat
