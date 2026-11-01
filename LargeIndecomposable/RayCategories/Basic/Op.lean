module

public import LargeIndecomposable.RayCategories.RoiterVanishing.Efficient

/-!
# The opposite ray category

`Pᵒᵖ` is again a finite ray category (`RayCat.isFiniteRayCategory_op`);
irreducible morphisms correspond, paths reverse (`RayCat.revPath`), and so do
interlacing and essential contours. Chains of `P` with offset `o` are chains
of `Pᵒᵖ` with offset `o + 1`, with the same efficiency; this turns a tackle
of `P` whose last link is a peak into one of `Pᵒᵖ` whose last link is a
valley (Fischbacher's "bis auf Dualität").
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Opposite

universe v u

namespace RayCat

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P]

omit [HasZeroMorphisms P] in
lemma unop_pow_end {X : Pᵒᵖ} (f : End X) (n : ℕ) :
    (f ^ n : End X).unop = (End.of f.unop) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ', End.mul_def, End.mul_def, unop_comp, ih]

/-- The opposite of a finite ray category. -/
instance isFiniteRayCategory_op [LargeIndecomposable.IsFiniteRayCategory P] :
    LargeIndecomposable.IsFiniteRayCategory Pᵒᵖ where
  id_ne_zero X h := LargeIndecomposable.IsFiniteRayCategory.id_ne_zero X.unop
    (by simpa using congrArg Quiver.Hom.unop h)
  hom_finite X Y := by
    have := LargeIndecomposable.IsFiniteRayCategory.hom_finite Y.unop X.unop
    exact Finite.of_equiv _ (opEquiv X Y).symm
  endomorphism_nilpotent {X} f hf := by
    have hf' : (f.unop : End X.unop) ≠ 𝟙 X.unop := fun h ↦ hf (Quiver.Hom.unop_inj h)
    obtain ⟨n, hn, hfn⟩ := LargeIndecomposable.IsFiniteRayCategory.endomorphism_nilpotent _ hf'
    refine ⟨n, hn, Quiver.Hom.unop_inj ?_⟩
    rw [unop_pow_end]
    exact hfn
  skeletal {X Y} h := by
    obtain ⟨e⟩ := h
    exact unop_injective (LargeIndecomposable.IsFiniteRayCategory.skeletal ⟨e.unop⟩).symm
  factorization_comparable f g := by
    rcases LargeIndecomposable.IsFiniteRayCategory.factorization_comparable f.unop g.unop with
      ⟨a, b, h⟩ | ⟨a, b, h⟩
    · exact Or.inl ⟨b.op, a.op, Quiver.Hom.unop_inj (by simpa [Category.assoc] using h)⟩
    · exact Or.inr ⟨b.op, a.op, Quiver.Hom.unop_inj (by simpa [Category.assoc] using h)⟩
  source_stabilizer_trivial {X Y Z} f g a h0 h := by
    have h0' : g.unop ≫ f.unop ≠ 0 := fun h' ↦ h0 (Quiver.Hom.unop_inj (by simpa using h'))
    have h' : (g.unop ≫ f.unop) ≫ a.unop = g.unop ≫ f.unop := by
      simpa [Category.assoc] using congrArg Quiver.Hom.unop h
    by_contra ha
    have ha' : (a.unop : X.unop ⟶ X.unop) ≠ 𝟙 _ := fun h'' ↦ ha (Quiver.Hom.unop_inj h'')
    obtain ⟨n, hn, han⟩ := LargeIndecomposable.IsFiniteRayCategory.endomorphism_nilpotent
      (a.unop : End X.unop) ha'
    have : ∀ m, (g.unop ≫ f.unop) ≫ ((End.of a.unop) ^ m : End X.unop) = g.unop ≫ f.unop := by
      intro m
      induction m with
      | zero => exact Category.comp_id _
      | succ m ih =>
        rw [pow_succ, End.mul_def]
        change (g.unop ≫ f.unop) ≫ (a.unop ≫ _) = _
        rw [← Category.assoc, h', ih]
    apply h0'
    rw [← this n, han]
    exact comp_zero

/-- The opposite of a finite ray category (basic axioms). -/
instance isFiniteRayCategory0_op [LargeIndecomposable.IsFiniteRayCategory0 P] :
    LargeIndecomposable.IsFiniteRayCategory0 Pᵒᵖ where
  id_ne_zero X h := LargeIndecomposable.IsFiniteRayCategory0.id_ne_zero X.unop
    (by simpa using congrArg Quiver.Hom.unop h)
  hom_finite X Y := by
    have := LargeIndecomposable.IsFiniteRayCategory0.hom_finite Y.unop X.unop
    exact Finite.of_equiv _ (opEquiv X Y).symm
  endomorphism_nilpotent {X} f hf := by
    have hf' : (f.unop : End X.unop) ≠ 𝟙 X.unop := fun h ↦ hf (Quiver.Hom.unop_inj h)
    obtain ⟨n, hn, hfn⟩ := LargeIndecomposable.IsFiniteRayCategory0.endomorphism_nilpotent _ hf'
    refine ⟨n, hn, Quiver.Hom.unop_inj ?_⟩
    rw [unop_pow_end]
    exact hfn
  skeletal {X Y} h := by
    obtain ⟨e⟩ := h
    exact unop_injective (LargeIndecomposable.IsFiniteRayCategory0.skeletal ⟨e.unop⟩).symm

instance finite_op [Finite P] : Finite Pᵒᵖ := Finite.of_equiv _ Opposite.equivToOpposite

lemma isIrreducible_op {x y : P} (f : x ⟶ y) : IsIrreducible f.op ↔ IsIrreducible f := by
  constructor
  · rintro ⟨h0, hi, hf⟩
    refine ⟨fun h ↦ h0 (by rw [h, op_zero]), fun h ↦ hi inferInstance, fun z g h hgh ↦ ?_⟩
    rcases hf (op z) h.op g.op (by rw [hgh, op_comp]) with h1 | h1
    · exact Or.inr ((isIso_op_iff h).1 h1)
    · exact Or.inl ((isIso_op_iff g).1 h1)
  · rintro ⟨h0, hi, hf⟩
    refine ⟨fun h ↦ h0 (Quiver.Hom.op_inj (by rw [h, op_zero])), fun h ↦ hi ((isIso_op_iff f).1 h),
      fun z g h hgh ↦ ?_⟩
    rcases hf z.unop h.unop g.unop (by rw [← unop_comp, ← hgh]; rfl) with h1 | h1
    · exact Or.inr ((isIso_unop_iff h).1 h1)
    · exact Or.inl ((isIso_unop_iff g).1 h1)

lemma isIrreducible_unop {X Y : Pᵒᵖ} (f : X ⟶ Y) : IsIrreducible f.unop ↔ IsIrreducible f :=
  (isIrreducible_op f.unop).symm

/-- An arrow of `P`, reversed. -/
def revArr {x y : RayVert P} (e : x ⟶ y) :
    (RayVert.mk (op y.out) : RayVert Pᵒᵖ) ⟶ RayVert.mk (op x.out) :=
  ⟨e.1.op, (isIrreducible_op e.1).2 e.2⟩

/-- An arrow of `Pᵒᵖ`, reversed. -/
def unrevArr {X Y : RayVert Pᵒᵖ} (e : X ⟶ Y) :
    (RayVert.mk Y.out.unop : RayVert P) ⟶ RayVert.mk X.out.unop :=
  ⟨e.1.unop, (isIrreducible_unop e.1).2 e.2⟩

/-- A path of `P`, reversed. -/
def revPath {x : RayVert P} : ∀ {y : RayVert P}, Quiver.Path x y →
    Quiver.Path (RayVert.mk (op y.out) : RayVert Pᵒᵖ) (RayVert.mk (op x.out))
  | _, .nil => .nil
  | _, .cons p e => (revArr e).toPath.comp (revPath p)

/-- A path of `Pᵒᵖ`, reversed. -/
def unrevPath {X : RayVert Pᵒᵖ} : ∀ {Y : RayVert Pᵒᵖ}, Quiver.Path X Y →
    Quiver.Path (RayVert.mk Y.out.unop : RayVert P) (RayVert.mk X.out.unop)
  | _, .nil => .nil
  | _, .cons p e => (unrevArr e).toPath.comp (unrevPath p)

lemma pathVal_revPath {x : RayVert P} : ∀ {y : RayVert P} (p : Quiver.Path x y),
    pathVal (revPath p) = (pathVal p).op
  | _, .nil => rfl
  | _, .cons p e => by
    change pathVal ((revArr e).toPath.comp (revPath p)) = (pathVal p ≫ e.1).op
    rw [pathVal_comp, pathVal_toPath, pathVal_revPath p, op_comp]
    rfl

lemma pathVal_unrevPath {X : RayVert Pᵒᵖ} : ∀ {Y : RayVert Pᵒᵖ} (p : Quiver.Path X Y),
    pathVal (unrevPath p) = (pathVal p).unop
  | _, .nil => rfl
  | _, .cons p e => by
    change pathVal ((unrevArr e).toPath.comp (unrevPath p)) = (pathVal p ≫ e.1).unop
    rw [pathVal_comp, pathVal_toPath, pathVal_unrevPath p, unop_comp]
    rfl

lemma length_revPath {x : RayVert P} : ∀ {y : RayVert P} (p : Quiver.Path x y),
    (revPath p).length = p.length
  | _, .nil => rfl
  | _, .cons p e => by
    rw [revPath, Quiver.Path.length_comp, length_revPath p]
    simp; omega

lemma length_unrevPath {X : RayVert Pᵒᵖ} : ∀ {Y : RayVert Pᵒᵖ} (p : Quiver.Path X Y),
    (unrevPath p).length = p.length
  | _, .nil => rfl
  | _, .cons p e => by
    rw [unrevPath, Quiver.Path.length_comp, length_unrevPath p]
    simp; omega

lemma revPath_comp {x y : RayVert P} (p : Quiver.Path x y) : ∀ {z : RayVert P}
    (q : Quiver.Path y z), revPath (p.comp q) = (revPath q).comp (revPath p)
  | _, .nil => (Quiver.Path.nil_comp _).symm
  | _, .cons q e => by
    change (revArr e).toPath.comp (revPath (p.comp q)) = ((revArr e).toPath.comp (revPath q)).comp _
    rw [revPath_comp p q, Quiver.Path.comp_assoc]

lemma unrevPath_comp {X Y : RayVert Pᵒᵖ} (p : Quiver.Path X Y) : ∀ {Z : RayVert Pᵒᵖ}
    (q : Quiver.Path Y Z), unrevPath (p.comp q) = (unrevPath q).comp (unrevPath p)
  | _, .nil => (Quiver.Path.nil_comp _).symm
  | _, .cons q e => by
    change (unrevArr e).toPath.comp (unrevPath (p.comp q)) =
      ((unrevArr e).toPath.comp (unrevPath q)).comp _
    rw [unrevPath_comp p q, Quiver.Path.comp_assoc]

lemma interStep_revPath {x y : RayVert P} {v w : Quiver.Path x y} (h : InterStep v w) :
    InterStep (revPath v) (revPath w) := by
  obtain ⟨a, c, p, v', w', q, rfl, rfl, hval, h0, hlen⟩ := h
  refine ⟨_, _, revPath q, revPath v', revPath w', revPath p, ?_, ?_, ?_, ?_, ?_⟩
  · rw [revPath_comp, revPath_comp, Quiver.Path.comp_assoc]
  · rw [revPath_comp, revPath_comp, Quiver.Path.comp_assoc]
  · rw [pathVal_revPath, pathVal_revPath, hval]
  · rw [pathVal_revPath]
    exact fun h ↦ h0 (Quiver.Hom.op_inj (by rw [h, op_zero]))
  · rw [length_revPath, length_revPath]
    exact hlen.symm

lemma interStep_unrevPath {X Y : RayVert Pᵒᵖ} {v w : Quiver.Path X Y} (h : InterStep v w) :
    InterStep (unrevPath v) (unrevPath w) := by
  obtain ⟨a, c, p, v', w', q, rfl, rfl, hval, h0, hlen⟩ := h
  refine ⟨_, _, unrevPath q, unrevPath v', unrevPath w', unrevPath p, ?_, ?_, ?_, ?_, ?_⟩
  · rw [unrevPath_comp, unrevPath_comp, Quiver.Path.comp_assoc]
  · rw [unrevPath_comp, unrevPath_comp, Quiver.Path.comp_assoc]
  · rw [pathVal_unrevPath, pathVal_unrevPath, hval]
  · rw [pathVal_unrevPath]
    exact fun h ↦ h0 (Quiver.Hom.unop_inj (by rw [h, unop_zero]))
  · rw [length_unrevPath, length_unrevPath]
    exact hlen.symm

lemma interlaced_revPath {x y : RayVert P} {v w : Quiver.Path x y} (h : Interlaced v w) :
    Interlaced (revPath v) (revPath w) := by
  induction h with
  | rel _ _ h => exact .rel _ _ (interStep_revPath h)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih ih' => exact .trans _ _ _ ih ih'

lemma interlaced_unrevPath {X Y : RayVert Pᵒᵖ} {v w : Quiver.Path X Y} (h : Interlaced v w) :
    Interlaced (unrevPath v) (unrevPath w) := by
  induction h with
  | rel _ _ h => exact .rel _ _ (interStep_unrevPath h)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih ih' => exact .trans _ _ _ ih ih'

/-- `revPath` and `unrevPath` are mutually inverse. -/
lemma unrevPath_revPath {x : RayVert P} : ∀ {y : RayVert P} (p : Quiver.Path x y),
    unrevPath (revPath p) = p
  | _, .nil => rfl
  | _, .cons p e => by
    rw [revPath, unrevPath_comp, unrevPath_revPath p]
    rfl

/-- A morphism of `P` as a morphism of `Pᵒᵖ`. -/
def opRM (f : RayMor P) : RayMor Pᵒᵖ := ⟨op f.2.1, op f.1, f.2.2.op⟩

/-- A morphism of `Pᵒᵖ` as a morphism of `P`. -/
def unopRM (F : RayMor Pᵒᵖ) : RayMor P := ⟨F.2.1.unop, F.1.unop, F.2.2.unop⟩

omit [HasZeroMorphisms P] in
@[simp] lemma opRM_unopRM (F : RayMor Pᵒᵖ) : opRM (unopRM F) = F := rfl

omit [HasZeroMorphisms P] in
@[simp] lemma unopRM_opRM (f : RayMor P) : unopRM (opRM f) = f := rfl

lemma inEss_opRM {f : RayMor P} (h : InEss f) : InEss (opRM f) := by
  obtain ⟨x, y, v, w, p, e, q, hvw, h0, hi, he, hv⟩ := h
  refine ⟨_, _, revPath v, revPath w, revPath q, revArr e, revPath p, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pathVal_revPath, pathVal_revPath, hvw]
  · rw [pathVal_revPath]
    exact fun h ↦ h0 (Quiver.Hom.op_inj (by rw [h, op_zero]))
  · intro h
    apply hi
    have := interlaced_unrevPath h
    rwa [unrevPath_revPath, unrevPath_revPath] at this
  · change e.1.op = f.2.2.op
    rw [he]
  · rw [hv, revPath_comp, revPath, ← Quiver.Path.comp_assoc]
    rfl

lemma revPath_unrevPath {X : RayVert Pᵒᵖ} : ∀ {Y : RayVert Pᵒᵖ} (p : Quiver.Path X Y),
    revPath (unrevPath p) = p
  | _, .nil => rfl
  | _, .cons p e => by
    rw [unrevPath, revPath_comp, revPath_unrevPath p]
    rfl

lemma inEss_unopRM {F : RayMor Pᵒᵖ} (h : InEss F) : InEss (unopRM F) := by
  obtain ⟨x, y, v, w, p, e, q, hvw, h0, hi, he, hv⟩ := h
  refine ⟨_, _, unrevPath v, unrevPath w, unrevPath q, unrevArr e, unrevPath p, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pathVal_unrevPath, pathVal_unrevPath, hvw]
  · rw [pathVal_unrevPath]
    exact fun h ↦ h0 (Quiver.Hom.unop_inj (by rw [h, unop_zero]))
  · intro h
    apply hi
    have := interlaced_revPath h
    rwa [revPath_unrevPath, revPath_unrevPath] at this
  · change e.1.unop = F.2.2.unop
    rw [he]
  · rw [hv, unrevPath_comp, unrevPath, ← Quiver.Path.comp_assoc]
    rfl

lemma inEss_opRM_iff (f : RayMor P) : InEss (opRM f) ↔ InEss f :=
  ⟨fun h ↦ inEss_unopRM h, inEss_opRM⟩

/-- Depth is invariant under passing to `Pᵒᵖ`. -/
lemma depth_op {x y : P} (f : x ⟶ y) : depth f.op = depth f := by
  unfold depth
  congr 1
  ext n
  constructor
  · rintro ⟨p, hl, hp⟩
    exact ⟨unrevPath p, (length_unrevPath p).trans hl,
      (pathVal_unrevPath p).trans (by rw [hp]; rfl)⟩
  · rintro ⟨p, hl, hp⟩
    exact ⟨revPath p, (length_revPath p).trans hl, (pathVal_revPath p).trans (by rw [hp])⟩

omit [HasZeroMorphisms P] in
lemma peak_mk_iff {a a' c : P} (φ : a ⟶ c) (ψ : a' ⟶ c) :
    Peak (⟨a, c, φ⟩ : RayMor P) ⟨a', c, ψ⟩ ↔ (¬∃ k, k ≫ ψ = φ) ∧ ¬∃ k, k ≫ φ = ψ := by
  constructor
  · rintro ⟨h, h1, h2⟩
    simp only [eqToHom_refl, Category.comp_id] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨rfl, by simpa using h1, by simpa using h2⟩

omit [HasZeroMorphisms P] in
lemma valley_mk_iff {a c c' : P} (φ : a ⟶ c) (ψ : a ⟶ c') :
    Valley (⟨a, c, φ⟩ : RayMor P) ⟨a, c', ψ⟩ ↔ (¬∃ k, φ ≫ k = ψ) ∧ ¬∃ k, ψ ≫ k = φ := by
  constructor
  · rintro ⟨h, h1, h2⟩
    simp only [eqToHom_refl, Category.id_comp] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨rfl, by simpa using h1, by simpa using h2⟩

omit [HasZeroMorphisms P] in
lemma not_exists_op_comp {a a' c : P} (φ : a ⟶ c) (ψ : a' ⟶ c) :
    (¬∃ K : op a ⟶ op a', φ.op ≫ K = ψ.op) ↔ ¬∃ k : a' ⟶ a, k ≫ φ = ψ := by
  refine not_congr ⟨fun ⟨K, hK⟩ ↦ ⟨K.unop, ?_⟩, fun ⟨k, hk⟩ ↦ ⟨k.op, ?_⟩⟩
  · have := congrArg Quiver.Hom.unop hK
    simpa using this
  · rw [← op_comp, hk]

omit [HasZeroMorphisms P] in
lemma not_exists_comp_op {a c c' : P} (φ : a ⟶ c) (ψ : a ⟶ c') :
    (¬∃ K : op c ⟶ op c', K ≫ ψ.op = φ.op) ↔ ¬∃ k : c' ⟶ c, ψ ≫ k = φ := by
  refine not_congr ⟨fun ⟨K, hK⟩ ↦ ⟨K.unop, ?_⟩, fun ⟨k, hk⟩ ↦ ⟨k.op, ?_⟩⟩
  · have := congrArg Quiver.Hom.unop hK
    simpa using this
  · rw [← op_comp, hk]

omit [HasZeroMorphisms P] in
lemma peak_iff_valley_op (f g : RayMor P) : Peak f g ↔ Valley (opRM f) (opRM g) := by
  obtain ⟨a, c, φ⟩ := f
  obtain ⟨a', c', ψ⟩ := g
  by_cases hc : c = c'
  · subst hc
    rw [peak_mk_iff]
    change _ ↔ Valley ⟨op c, op a, φ.op⟩ ⟨op c, op a', ψ.op⟩
    rw [valley_mk_iff, not_exists_op_comp, not_exists_op_comp]
    exact And.comm
  · exact ⟨fun ⟨h, _⟩ ↦ absurd h hc, fun ⟨h, _⟩ ↦ absurd (congrArg unop h) hc⟩

omit [HasZeroMorphisms P] in
lemma valley_iff_peak_op (f g : RayMor P) : Valley f g ↔ Peak (opRM f) (opRM g) := by
  obtain ⟨a, c, φ⟩ := f
  obtain ⟨a', c', ψ⟩ := g
  by_cases ha : a = a'
  · subst ha
    rw [valley_mk_iff]
    change _ ↔ Peak ⟨op c, op a, φ.op⟩ ⟨op c', op a, ψ.op⟩
    rw [peak_mk_iff, not_exists_comp_op, not_exists_comp_op]
    exact And.comm
  · exact ⟨fun ⟨h, _⟩ ↦ absurd h ha, fun ⟨h, _⟩ ↦ absurd (congrArg unop h) ha⟩

lemma link_opRM (j : ℕ) (f g : RayMor P) : Link (j + 1) (opRM f) (opRM g) ↔ Link j f g := by
  unfold Link
  by_cases hj : j % 2 = 0
  · rw [if_neg (by omega), if_pos hj, peak_iff_valley_op]
  · rw [if_pos (by omega), if_neg hj, valley_iff_peak_op]

lemma isChain_map_opRM (o : ℕ) (l : List (RayMor P)) :
    IsChain (o + 1) (l.map opRM) ↔ IsChain o l := by
  unfold IsChain
  refine and_congr ⟨fun h f hf ↦ ?_, fun h F hF ↦ ?_⟩ ⟨fun h j hj ↦ ?_, fun h j hj ↦ ?_⟩
  · have := h (opRM f) (List.mem_map_of_mem hf)
    exact fun h0 ↦ this (by change f.2.2.op = 0; rw [h0, op_zero])
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hF
    exact fun h0 ↦ h f hf (Quiver.Hom.op_inj (by rw [op_zero]; exact h0))
  · have := h j (by simpa using hj)
    simp only [List.getElem_map, ← add_assoc] at this
    exact (link_opRM _ _ _).1 this
  · simp only [List.getElem_map, ← add_assoc]
    exact (link_opRM _ _ _).2 (h j (by simpa using hj))

omit [HasZeroMorphisms P] in
lemma link_add_two (j : ℕ) (f g : RayMor P) : Link (j + 2) f g ↔ Link j f g := by
  unfold Link
  rw [show (j + 2) % 2 = j % 2 by omega]

lemma isChain_add_two (o : ℕ) (l : List (RayMor P)) : IsChain (o + 2) l ↔ IsChain o l := by
  unfold IsChain
  refine and_congr Iff.rfl (forall_congr' fun j ↦ forall_congr' fun _ ↦ ?_)
  rw [← add_assoc, link_add_two]

lemma IsChain.tail {o : ℕ} {l : List (RayMor P)} (h : IsChain o l) : IsChain (o + 1) l.tail := by
  refine ⟨fun f hf ↦ h.1 f (List.mem_of_mem_tail hf), fun j hj ↦ ?_⟩
  have := h.2 (j + 1) (by simp at hj; omega)
  simp only [List.getElem_tail]
  rwa [show j + (o + 1) = j + 1 + o by omega]

lemma efficiency_map_opRM (l : List (RayMor P)) : efficiency (l.map opRM) = efficiency l := by
  unfold efficiency
  rw [List.map_map]
  exact List.map_congr_left fun f _ ↦ depth_op f.2.2

lemma isTackle_map_opRM (o : ℕ) (l : List (RayMor P)) :
    IsTackle InEss (o + 1) (l.map opRM) ↔ IsTackle InEss o l := by
  constructor
  · rintro ⟨hne, hch, hirr, hadm⟩
    have hne' : l ≠ [] := by simpa using hne
    rw [List.getLast_map] at hirr hadm
    exact ⟨hne', (isChain_map_opRM o l).1 hch, (isIrreducible_op _).1 hirr,
      (inEss_opRM_iff _).1 hadm⟩
  · rintro ⟨hne, hch, hirr, hadm⟩
    refine ⟨by simpa using hne, (isChain_map_opRM o l).2 hch, ?_, ?_⟩
    · rw [List.getLast_map]
      exact (isIrreducible_op _).2 hirr
    · rw [List.getLast_map]
      exact inEss_opRM hadm

/-- An efficient tackle of `P` with offset `o` is an efficient tackle of `Pᵒᵖ`
with offset `o + 1`. -/
lemma IsEfficient.map_opRM {o : ℕ} {l : List (RayMor P)} (hl : IsEfficient InEss o l) :
    IsEfficient InEss (o + 1) (l.map opRM) := by
  refine ⟨(isTackle_map_opRM o l).2 hl.1, fun L hL ↦ ?_⟩
  have hL' : L = (L.map unopRM).map opRM := by
    rw [List.map_map, show (opRM ∘ unopRM : RayMor Pᵒᵖ → RayMor Pᵒᵖ) = id from rfl, List.map_id]
  rw [hL', isTackle_map_opRM] at hL
  rw [efficiency_map_opRM, hL', efficiency_map_opRM]
  exact hl.2 _ hL

lemma leftCancel_op (hR : RightCancel P) : LeftCancel Pᵒᵖ := by
  intro x y z f g h hfg h0
  apply Quiver.Hom.unop_inj
  refine hR _ _ f.unop ?_ ?_
  · rw [← unop_comp, ← unop_comp, hfg]
  · rw [← unop_comp]
    exact fun h' ↦ h0 (Quiver.Hom.unop_inj (by rw [h', unop_zero]))

lemma rightCancel_op (hL : LeftCancel P) : RightCancel Pᵒᵖ := by
  intro x y z f g h hfg h0
  apply Quiver.Hom.unop_inj
  refine hL h.unop _ _ ?_ ?_
  · rw [← unop_comp, ← unop_comp, hfg]
  · rw [← unop_comp]
    exact fun h' ↦ h0 (Quiver.Hom.unop_inj (by rw [h', unop_zero]))

lemma chainBounded_op (h : ChainBounded P) : ChainBounded Pᵒᵖ := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 1, fun L hL ↦ ?_⟩
  have hL' : L = (L.map unopRM).map opRM := by
    rw [List.map_map, show (opRM ∘ unopRM : RayMor Pᵒᵖ → RayMor Pᵒᵖ) = id from rfl, List.map_id]
  rw [hL', ← isChain_add_two, show (0 + 2 : ℕ) = 1 + 1 by rfl, isChain_map_opRM] at hL
  have := hN _ ((isChain_add_two 0 _).1 (by simpa using hL.tail))
  simp only [List.length_tail, List.length_map] at this
  omega

/-- Start-version reduction data (Fischbacher 2.1–2.2) for a finite ray
category. -/
def HasRedData (Q : Type u) [Category.{v} Q] [HasZeroMorphisms Q]
    [LargeIndecomposable.IsFiniteRayCategory0 Q] [Finite Q] : Prop :=
  ∃ (b : Q) (ι : Type (max u v)) (d : ι → Q) (α : ∀ i, b ⟶ d i) (hα : ∀ i, ¬IsIso (α i))
    (D : RedData α), D.EssHyp (hα := hα) ∧ D.EssHypVal ∧ Nonempty ι

attribute [local instance] isRayCategory_of_finiteRayCategory in
/-- **Fischbacher's Lemma 2.1** ("bis auf Dualität"): a finite chain-bounded
ray category with cancellation and an essential contour has reduction data,
or its opposite has. -/
theorem hasRedData_or_op [LargeIndecomposable.IsFiniteRayCategory0 P] [Finite P]
    (hL : LeftCancel P) (hR : RightCancel P) (hCB : ChainBounded P) {x y : RayVert P}
    (v w : Quiver.Path x y) (hvw : pathVal v = pathVal w) (h0 : pathVal v ≠ 0)
    (hi : ¬Interlaced v w) : HasRedData P ∨ HasRedData Pᵒᵖ := by
  obtain ⟨l, hl⟩ := exists_efficient hCB v w hvw h0 hi
  have hne : l ≠ [] := hl.1.choose
  have hm : l.length - 1 + 1 = l.length := by
    have := List.length_pos_of_ne_nil hne
    omega
  rcases Nat.mod_two_eq_zero_or_one (l.length - 1) with h | h
  · exact Or.inl (exists_redData_of_efficient hL hR hCB hl _ hm (by simpa using h))
  · right
    exact exists_redData_of_efficient (leftCancel_op hR) (rightCancel_op hL)
      (chainBounded_op hCB) hl.map_opRM (l.length - 1) (by simpa using hm) (by omega)

end RayCat

end LargeIndecomposable
