module

public import LargeIndecomposable.Cleaving.ClosedChains.ClosedZigzag
public import LargeIndecomposable.Modules.KrullSchmidt.LocalEndFiniteDimensional

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable.ClosedZigzag

universe u

variable {k : Type u} [Field k]

/-- The free linear source category used by the cleaving/coend argument.  The
opposite compensates for the reversed path convention in
`LinearPathCategory`. -/
abbrev LinearSource (k : Type u) [Field k] (n : ℕ) :=
  LinearPathCategory.Category k (Vertex n)ᵒᵖ

/-- The object of the free linear source attached to a displayed cycle
vertex. -/
def linearVertexObj (n : ℕ) (a : Vertex n) : LinearSource k n :=
  LinearPathCategory.obj k (Vertex n)ᵒᵖ (Opposite.op a)

/-- The generator of the free linear source corresponding to an original
cycle arrow. -/
def linearGeneratorHom {n : ℕ} {a b : Vertex n} (e : a ⟶ b) :
    linearVertexObj (k := k) n a ⟶ linearVertexObj (k := k) n b :=
  LinearPathCategory.pathHom (Quiver.Hom.toPath (Quiver.Hom.op e))

/-- Linearization of the thin one-parameter closed-zigzag representation. -/
def linearModule (n : ℕ) (c : k) :
    LinearSource k n ⥤ ModuleCat k :=
  LinearPathCategory.lift
    (fun _ ↦ ModuleCat.of k k)
    (fun {i j} e ↦ scalarHom
      (arrowScalar j.unop i.unop c e.unop))

instance linearModule_additive (n : ℕ) (c : k) :
    (linearModule n c).Additive := by
  unfold linearModule
  infer_instance

instance linearModule_linear (n : ℕ) (c : k) :
    (linearModule n c).Linear k := by
  unfold linearModule
  infer_instance

@[simp]
theorem linearModule_obj (n : ℕ) (c : k) (a : Vertex n) :
    (linearModule n c).obj (linearVertexObj (k := k) n a) =
      ModuleCat.of k k :=
  rfl

@[simp]
theorem linearModule_map_generator {n : ℕ} (c : k)
    {a b : Vertex n} (e : a ⟶ b) :
    (linearModule n c).map (linearGeneratorHom (k := k) e) =
      scalarHom (arrowScalar a b c e) := by
  unfold linearModule linearGeneratorHom
  rw [LinearPathCategory.lift_map_pathHom]
  simp only [Quiver.Hom.toPath, LinearPathCategory.pathMap_cons,
    LinearPathCategory.pathMap_nil, Category.comp_id]
  cases e <;> rfl

/-- Component of a natural transformation at a displayed cycle vertex. -/
def linearComponentHom {n : ℕ} {c d : k}
    (f : linearModule n c ⟶ linearModule n d) (a : Vertex n) :
    ModuleCat.of k k ⟶ ModuleCat.of k k :=
  f.app (linearVertexObj (k := k) n a)

/-- Scalar coefficient of a natural transformation at one vertex. -/
def linearHomCoeff {n : ℕ} {c d : k}
    (f : linearModule n c ⟶ linearModule n d) (a : Vertex n) : k :=
  linearComponentHom f a 1

theorem linearHom_app_eq_mul_coeff {n : ℕ} {c d : k}
    (f : linearModule n c ⟶ linearModule n d)
    (a : Vertex n) (x : k) :
    linearComponentHom f a x = x * linearHomCoeff f a := by
  change linearComponentHom f a x = x * linearComponentHom f a 1
  simpa using (linearComponentHom f a).hom.map_smul x 1

/-- Naturality across one linear-source generator, reduced to scalars. -/
theorem linearHomCoeff_naturality {n : ℕ} {c d : k}
    (f : linearModule n c ⟶ linearModule n d)
    {a b : Vertex n} (e : a ⟶ b) :
    arrowScalar a b c e * linearHomCoeff f b =
      linearHomCoeff f a * arrowScalar a b d e := by
  have h := f.naturality (linearGeneratorHom (k := k) e)
  rw [linearModule_map_generator, linearModule_map_generator] at h
  change scalarHom (arrowScalar a b c e) ≫ linearComponentHom f b =
    linearComponentHom f a ≫ scalarHom (arrowScalar a b d e) at h
  have h := congrArg
    (fun q : ModuleCat.of k k ⟶ ModuleCat.of k k ↦ q 1) h
  change linearComponentHom f b (arrowScalar a b c e * 1) =
    arrowScalar a b d e * linearComponentHom f a 1 at h
  rw [linearHom_app_eq_mul_coeff] at h
  simpa [linearHomCoeff, mul_comm] using h

theorem linearHomCoeff_source_eq_sink {n : ℕ} {c d : k}
    (f : linearModule n c ⟶ linearModule n d) (i : Fin (n + 1)) :
    linearHomCoeff f (.source i) = linearHomCoeff f (.sink i) := by
  simpa [arrowScalar] using
    (linearHomCoeff_naturality f (Arrow.rho i)).symm

theorem linearHomCoeff_nextSource_eq_sink {n : ℕ} {c d : k}
    (f : linearModule n c ⟶ linearModule n d) (i : Fin n) :
    linearHomCoeff f (.source i.succ) =
      linearHomCoeff f (.sink i.castSucc) := by
  simpa [arrowScalar] using
    (linearHomCoeff_naturality f (Arrow.sigma i)).symm

theorem linearHomCoeff_close {n : ℕ} {c d : k}
    (f : linearModule n c ⟶ linearModule n d) :
    c * linearHomCoeff f (.sink (Fin.last n)) =
      linearHomCoeff f (.source 0) * d := by
  simpa [arrowScalar] using
    linearHomCoeff_naturality f (Arrow.close (n := n))

theorem linearHomCoeff_source_eq_source_zero {n : ℕ} {c d : k}
    (f : linearModule n c ⟶ linearModule n d) (i : Fin (n + 1)) :
    linearHomCoeff f (.source i) = linearHomCoeff f (.source 0) := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
      calc
        linearHomCoeff f (.source i.succ) =
            linearHomCoeff f (.sink i.castSucc) :=
          linearHomCoeff_nextSource_eq_sink f i
        _ = linearHomCoeff f (.source i.castSucc) :=
          (linearHomCoeff_source_eq_sink f i.castSucc).symm
        _ = linearHomCoeff f (.source 0) := ih

theorem linearHomCoeff_eq_source_zero {n : ℕ} {c d : k}
    (f : linearModule n c ⟶ linearModule n d) (a : Vertex n) :
    linearHomCoeff f a = linearHomCoeff f (.source 0) := by
  cases a with
  | source i => exact linearHomCoeff_source_eq_source_zero f i
  | sink i =>
      calc
        linearHomCoeff f (.sink i) = linearHomCoeff f (.source i) :=
          (linearHomCoeff_source_eq_sink f i).symm
        _ = linearHomCoeff f (.source 0) :=
          linearHomCoeff_source_eq_source_zero f i

theorem linearHomCoeff_lastSink_eq_source_zero {n : ℕ} {c d : k}
    (f : linearModule n c ⟶ linearModule n d) :
    linearHomCoeff f (.sink (Fin.last n)) =
      linearHomCoeff f (.source 0) :=
  linearHomCoeff_eq_source_zero f _

/-- A map between the linearized thin modules is determined by one scalar. -/
theorem linearHom_ext {n : ℕ} {c d : k}
    {f g : linearModule n c ⟶ linearModule n d}
    (h : linearHomCoeff f (.source 0) =
      linearHomCoeff g (.source 0)) : f = g := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change linearComponentHom f (LinearPathCategory.vertex X).unop x =
    linearComponentHom g (LinearPathCategory.vertex X).unop x
  rw [linearHom_app_eq_mul_coeff, linearHom_app_eq_mul_coeff,
    linearHomCoeff_eq_source_zero f, linearHomCoeff_eq_source_zero g, h]

@[simp]
theorem linearHomCoeff_zero {n : ℕ} {c d : k} (a : Vertex n) :
    linearHomCoeff (0 : linearModule n c ⟶ linearModule n d) a = 0 :=
  rfl

@[simp]
theorem linearHomCoeff_id {n : ℕ} {c : k} (a : Vertex n) :
    linearHomCoeff (𝟙 (linearModule n c)) a = 1 :=
  rfl

@[simp]
theorem linearHomCoeff_add {n : ℕ} {c d : k}
    (f g : linearModule n c ⟶ linearModule n d) (a : Vertex n) :
    linearHomCoeff (f + g) a =
      linearHomCoeff f a + linearHomCoeff g a :=
  rfl

@[simp]
theorem linearHomCoeff_smul {n : ℕ} {c d : k} (r : k)
    (f : linearModule n c ⟶ linearModule n d) (a : Vertex n) :
    linearHomCoeff (r • f) a = r * linearHomCoeff f a :=
  rfl

@[simp]
theorem linearHomCoeff_comp {n : ℕ} {c d e : k}
    (f : linearModule n c ⟶ linearModule n d)
    (g : linearModule n d ⟶ linearModule n e) (a : Vertex n) :
    linearHomCoeff (f ≫ g) a =
      linearHomCoeff f a * linearHomCoeff g a := by
  change linearComponentHom g a (linearComponentHom f a 1) = _
  rw [linearHom_app_eq_mul_coeff]
  rfl

theorem linearHomCoeff_ne_zero_of_iso {n : ℕ} {c d : k}
    (e : linearModule n c ≅ linearModule n d) (a : Vertex n) :
    linearHomCoeff e.hom a ≠ 0 := by
  have h := e.hom_inv_id_app (linearVertexObj (k := k) n a)
  change linearComponentHom e.hom a ≫ linearComponentHom e.inv a =
    𝟙 (ModuleCat.of k k) at h
  have h := congrArg
    (fun q : ModuleCat.of k k ⟶ ModuleCat.of k k ↦ q 1) h
  change linearComponentHom e.inv a (linearComponentHom e.hom a 1) = 1 at h
  rw [linearHom_app_eq_mul_coeff] at h
  change linearHomCoeff e.hom a * linearHomCoeff e.inv a = 1 at h
  intro hzero
  rw [hzero, zero_mul] at h
  exact zero_ne_one h

/-- The parameter remains a complete invariant after passing from the path
representation to the free linear source. -/
theorem linearParameter_eq_of_iso {n : ℕ} {c d : k}
    (e : linearModule n c ≅ linearModule n d) : c = d := by
  have h := linearHomCoeff_close e.hom
  rw [linearHomCoeff_lastSink_eq_source_zero] at h
  apply mul_right_cancel₀ (linearHomCoeff_ne_zero_of_iso e (.source 0))
  simpa [mul_comm] using h

instance linearModule_obj_finite (n : ℕ) (c : k) (X : LinearSource k n) :
    Module.Finite k ((linearModule n c).obj X) := by
  change Module.Finite k k
  infer_instance

theorem linearModule_obj_finrank (n : ℕ) (c : k)
    (X : LinearSource k n) :
    Module.finrank k ((linearModule n c).obj X) = 1 := by
  change Module.finrank k k = 1
  simp

theorem linearEnd_eq_zero_or_id_of_idempotent {n : ℕ} {c : k}
    (p : linearModule n c ⟶ linearModule n c) (hp : p ≫ p = p) :
    p = 0 ∨ p = 𝟙 (linearModule n c) := by
  have hcoeff := congrArg
    (fun q : linearModule n c ⟶ linearModule n c ↦
      linearHomCoeff q (.source 0)) hp
  rw [linearHomCoeff_comp] at hcoeff
  have hsq : linearHomCoeff p (.source 0) ^ 2 =
      linearHomCoeff p (.source 0) := by
    simpa [pow_two] using hcoeff
  rcases eq_zero_or_one_of_sq_eq_self hsq with hzero | hone
  · left
    apply linearHom_ext
    simpa using hzero
  · right
    apply linearHom_ext
    simpa using hone

theorem linearModule_not_isZero (n : ℕ) (c : k) :
    ¬ IsZero (linearModule n c) := by
  intro hzero
  have hid : (𝟙 (linearModule n c) :
      linearModule n c ⟶ linearModule n c) = 0 :=
    (IsZero.iff_id_eq_zero _).1 hzero
  have h := congrArg
    (fun q : linearModule n c ⟶ linearModule n c ↦
      linearHomCoeff q (.source 0)) hid
  simp at h

/-- Every member of the linearized thin family is indecomposable. -/
theorem linearModule_indecomposable (n : ℕ) (c : k) :
    Indecomposable (linearModule n c) := by
  refine ⟨linearModule_not_isZero n c, ?_⟩
  intro Y Z e
  let p : linearModule n c ⟶ linearModule n c :=
    e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv
  have hp : p ≫ p = p := by
    simp [p, Category.assoc]
  rcases linearEnd_eq_zero_or_id_of_idempotent p hp with hzero | hone
  · left
    rw [IsZero.iff_id_eq_zero]
    have hproj := congrArg
      (fun q : linearModule n c ⟶ linearModule n c ↦
        e.inv ≫ q ≫ e.hom) hzero
    have hproj : biprod.fst ≫ biprod.inl =
        (0 : (Y ⊞ Z) ⟶ (Y ⊞ Z)) := by
      simpa [p, Category.assoc] using hproj
    have h := congrArg
      (fun q : (Y ⊞ Z) ⟶ (Y ⊞ Z) ↦
        biprod.inl ≫ q ≫ biprod.fst) hproj
    simpa only [Category.assoc, Limits.biprod.inl_fst_assoc,
      Limits.biprod.inl_fst, Category.comp_id, comp_zero, zero_comp] using h
  · right
    rw [IsZero.iff_id_eq_zero]
    have hproj := congrArg
      (fun q : linearModule n c ⟶ linearModule n c ↦
        e.inv ≫ q ≫ e.hom) hone
    have hproj : biprod.fst ≫ biprod.inl = 𝟙 (Y ⊞ Z) := by
      simpa [p, Category.assoc] using hproj
    have h := congrArg
      (fun q : (Y ⊞ Z) ⟶ (Y ⊞ Z) ↦
        biprod.inr ≫ q ≫ biprod.snd) hproj
    simpa only [Category.assoc, Limits.biprod.inr_fst_assoc,
      zero_comp, Limits.biprod.inr_snd, Category.id_comp,
      Category.comp_id] using h.symm

/-- Evaluation at one vertex identifies the endomorphism ring of a
linearized thin module with the ground field. -/
def linearEndRingEquiv (n : ℕ) (c : k) :
    CategoryTheory.End (linearModule n c) ≃+* k where
  toFun f := linearHomCoeff f (.source 0)
  invFun r := r • 𝟙 (linearModule n c)
  left_inv f := by
    apply linearHom_ext
    simp
  right_inv r := by simp
  map_add' f g := by
    change linearHomCoeff
      (CategoryTheory.End.asHom f + CategoryTheory.End.asHom g)
        (.source 0) =
      linearHomCoeff (CategoryTheory.End.asHom f) (.source 0) +
        linearHomCoeff (CategoryTheory.End.asHom g) (.source 0)
    exact linearHomCoeff_add _ _ _
  map_mul' f g := by
    change linearHomCoeff
      (CategoryTheory.End.asHom g ≫ CategoryTheory.End.asHom f)
        (.source 0) =
      linearHomCoeff (CategoryTheory.End.asHom f) (.source 0) *
        linearHomCoeff (CategoryTheory.End.asHom g) (.source 0)
    rw [linearHomCoeff_comp]
    exact mul_comm _ _

/-- The endomorphism ring needed in the finite cleaving transfer is local;
in fact it is the ground field. -/
instance linearModule_end_isLocalRing (n : ℕ) (c : k) :
    IsLocalRing (CategoryTheory.End (linearModule n c)) :=
  LargeIndecomposable.RingEquiv.isLocalRing_noncommutative
    (linearEndRingEquiv n c).symm

section InfiniteFamily

variable [Infinite k]

/-- Countable pairwise-distinct linearized thin family. -/
def linearFamily (n i : ℕ) : LinearSource k n ⥤ ModuleCat k :=
  linearModule n (Infinite.natEmbedding k i)

theorem linearFamily_obj_finite (n i : ℕ) (X : LinearSource k n) :
    Module.Finite k ((linearFamily (k := k) n i).obj X) := by
  unfold linearFamily
  infer_instance

theorem linearFamily_obj_finrank (n i : ℕ) (X : LinearSource k n) :
    Module.finrank k ((linearFamily (k := k) n i).obj X) = 1 :=
  linearModule_obj_finrank n (Infinite.natEmbedding k i) X

theorem linearFamily_indecomposable (n i : ℕ) :
    Indecomposable (linearFamily (k := k) n i) :=
  linearModule_indecomposable n (Infinite.natEmbedding k i)

/-- Distinct indices remain nonisomorphic in the free linear source
functor category. -/
theorem linearFamily_eq_of_iso {n i j : ℕ}
    (e : linearFamily (k := k) n i ≅ linearFamily (k := k) n j) :
    i = j := by
  apply (Infinite.natEmbedding k).injective
  exact linearParameter_eq_of_iso e

theorem linearFamily_end_isLocalRing (n i : ℕ) :
    IsLocalRing (CategoryTheory.End (linearFamily (k := k) n i)) := by
  unfold linearFamily
  infer_instance

end InfiniteFamily

end LargeIndecomposable.ClosedZigzag
