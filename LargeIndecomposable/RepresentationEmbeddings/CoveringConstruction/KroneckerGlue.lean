module

public import LargeIndecomposable.Coverings.Pieces.PairKills
public import LargeIndecomposable.Coverings.UniversalCover.PieceKills

/-!
# Kronecker pairs from two extensions

Morphisms of representations commute with path operators (`Rep.Hom.tot_comp_pathTot`), so a
representation with two jointly injective maps to representations respecting the relations of
the cover respects them too (`respectsCover_of_two`). For a Kronecker pair `(P, Q₀; z₁, z₂)`,
the extensions `E(z_c)` (spaces `Q₀(i) × P(i)`, arrows `(q, p) ↦ (Q₀(α) q + z_c(α) p, P(α) p)`)
receive such maps from the generic objects `L(S₋)` and `L(P₁)`. Hence, if both extensions
respect the relations, so do the generic objects (`respectsCover_generic`): a Kronecker pair
needs only the two module structures `E(z₁)`, `E(z₂)`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits TensorProduct Covering

universe u

variable {k : Type u} [Field k] {D : FinQuiver}

namespace Rep

lemma Hom.tot_comp_pathTot {X Y : Rep k D} (φ : X ⟶ Y) :
    ∀ le : List D.A, φ.tot ∘ₗ X.pathTot le = Y.pathTot le ∘ₗ φ.tot
  | [] => rfl
  | e :: le => by
    change φ.tot ∘ₗ (X.pathTot le ∘ₗ X.arrOp e) = Y.pathTot le ∘ₗ Y.arrOp e ∘ₗ φ.tot
    rw [← LinearMap.comp_assoc, Hom.tot_comp_pathTot φ le, LinearMap.comp_assoc,
      Hom.tot_comp_arrOp]

end Rep

namespace RayCat

open Cover RayQuiver

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)}

/-- **Relations pass along jointly injective maps.** -/
theorem respectsCover_of_two {X Y₁ Y₂ : Rep k (pieceQuiver S)} (f₁ : X ⟶ Y₁) (f₂ : X ⟶ Y₂)
    (hinj : ∀ x : X.Tot, f₁.tot x = 0 → f₂.tot x = 0 → x = 0) (h₁ : RespectsCover Y₁)
    (h₂ : RespectsCover Y₂) : RespectsCover X := by
  have hc : ∀ (f : X ⟶ Y₁) (x : X.Tot) (le : List (pieceQuiver S).A),
      f.tot (X.pathTot le x) = Y₁.pathTot le (f.tot x) :=
    fun f x le ↦ LinearMap.congr_fun (Rep.Hom.tot_comp_pathTot f le) x
  have hc₂ : ∀ (x : X.Tot) (le : List (pieceQuiver S).A),
      f₂.tot (X.pathTot le x) = Y₂.pathTot le (f₂.tot x) :=
    fun x le ↦ LinearMap.congr_fun (Rep.Hom.tot_comp_pathTot f₂ le) x
  refine ⟨fun le i j h h0 ↦ LinearMap.ext fun x ↦ hinj _ ?_ ?_,
    fun le le' i j h h' he ↦ LinearMap.ext fun x ↦ sub_eq_zero.1 (hinj _ ?_ ?_)⟩
  · rw [hc, h₁.1 le i j h h0]; rfl
  · rw [hc₂, h₂.1 le i j h h0]; rfl
  · rw [map_sub, hc, hc, h₁.2 le le' i j h h' he, sub_self]
  · rw [map_sub, hc₂, hc₂, h₂.2 le le' i j h h' he, sub_self]

end RayCat

namespace Covering.KroneckerPair

variable (K : KroneckerPair k D)

/-- The extension `E(z)`: spaces `Q₀(i) × P(i)`, arrows `(q, p) ↦ (Q₀(α) q + z(α) p, P(α) p)`. -/
def extRep (z : ∀ α : D.A, K.P.obj (D.src α) →ₗ[k] K.Q₀.obj (D.tgt α)) : Rep k D where
  obj i := ModuleCat.of k (K.Q₀.obj i × K.P.obj i)
  map α := ModuleCat.ofHom (LinearMap.prod (LinearMap.coprod (K.Q₀.map α).hom (z α))
    ((K.P.map α).hom ∘ₗ LinearMap.snd k _ _))

/-- The vertex map `L(P₁)(i) → E(z)(i)` through a coordinate `π` of `W = k²`. -/
def toExtP1Map (π : k × k →ₗ[k] k) (i : D.V) :
    K.space (P1K k) i →ₗ[k] K.Q₀.obj i × K.P.obj i :=
  LinearMap.prodMap
    ((TensorProduct.rid k (K.Q₀.obj i)).toLinearMap ∘ₗ TensorProduct.map LinearMap.id π)
    (TensorProduct.rid k (K.P.obj i)).toLinearMap

lemma toExtP1Map_comm (π : k × k →ₗ[k] k)
    (z : ∀ α : D.A, K.P.obj (D.src α) →ₗ[k] K.Q₀.obj (D.tgt α))
    (hz : ∀ α (p : K.P.obj (D.src α)), π (1, 0) • K.z₁ α p + π (0, 1) • K.z₂ α p = z α p)
    (α : D.A) (x : K.space (P1K k) (D.src α)) :
    K.toExtP1Map π (D.tgt α) (K.arrMap (P1K k) α x) =
      (LinearMap.prod (LinearMap.coprod (K.Q₀.map α).hom (z α))
        ((K.P.map α).hom ∘ₗ LinearMap.snd k _ _)) (K.toExtP1Map π (D.src α) x) := by
  obtain ⟨t, s⟩ := x
  have hπ : ∀ v : k, π (v, 0) = v * π (1, 0) ∧ π (0, v) = v * π (0, 1) := fun v ↦ by
    constructor
    · rw [← smul_eq_mul, ← map_smul]; simp
    · rw [← smul_eq_mul, ← map_smul]; simp
  have key : ∀ (t : K.Q₀.obj (D.src α) ⊗[k] (k × k)) (s : K.P.obj (D.src α) ⊗[k] k),
      ((TensorProduct.rid k _) (TensorProduct.map LinearMap.id π
        (TensorProduct.map (K.Q₀.map α).hom LinearMap.id t +
          (TensorProduct.map (K.z₁ α) (LinearMap.inl k k k) +
            TensorProduct.map (K.z₂ α) (LinearMap.inr k k k)) s)),
        (TensorProduct.rid k _) (TensorProduct.map (K.P.map α).hom LinearMap.id s)) =
      ((K.Q₀.map α).hom ((TensorProduct.rid k _) (TensorProduct.map LinearMap.id π t)) +
        z α ((TensorProduct.rid k _) s), (K.P.map α).hom ((TensorProduct.rid k _) s)) := by
    intro t s
    have h1 : (TensorProduct.rid k _) (TensorProduct.map LinearMap.id π
        (TensorProduct.map (K.Q₀.map α).hom LinearMap.id t)) =
        (K.Q₀.map α).hom ((TensorProduct.rid k _) (TensorProduct.map LinearMap.id π t)) := by
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul q w => simp
      | add t t' ht ht' => simp only [map_add, ht, ht']
    have h2 : (TensorProduct.rid k _) (TensorProduct.map LinearMap.id π
        ((TensorProduct.map (K.z₁ α) (LinearMap.inl k k k) +
          TensorProduct.map (K.z₂ α) (LinearMap.inr k k k)) s)) =
        z α ((TensorProduct.rid k _) s) := by
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul p v =>
        simp only [LinearMap.add_apply, TensorProduct.map_tmul, map_add, LinearMap.id_apply,
          TensorProduct.rid_tmul, LinearMap.inl_apply, LinearMap.inr_apply, (hπ v).1, (hπ v).2,
          map_smul, ← hz α p, smul_add, mul_smul]
      | add s s' hs hs' => simp only [map_add, hs, hs']
    have h3' : (TensorProduct.rid k (K.P.obj (D.tgt α))).toLinearMap ∘ₗ
        TensorProduct.map (K.P.map α).hom (LinearMap.id : k →ₗ[k] k) =
        (K.P.map α).hom ∘ₗ (TensorProduct.rid k (K.P.obj (D.src α))).toLinearMap :=
      TensorProduct.ext' fun p v ↦ by simp
    have h3 := LinearMap.congr_fun h3' s
    refine Prod.ext ?_ h3
    change (TensorProduct.rid k _) (TensorProduct.map LinearMap.id π
        (TensorProduct.map (K.Q₀.map α).hom LinearMap.id t +
          (TensorProduct.map (K.z₁ α) (LinearMap.inl k k k) +
            TensorProduct.map (K.z₂ α) (LinearMap.inr k k k)) s)) = _
    rw [map_add (TensorProduct.map LinearMap.id π), map_add (TensorProduct.rid k _), h1, h2]
  exact key t s

/-- The morphism `L(P₁) → E(z)`. -/
def toExtP1 (π : k × k →ₗ[k] k) (z : ∀ α : D.A, K.P.obj (D.src α) →ₗ[k] K.Q₀.obj (D.tgt α))
    (hz : ∀ α (p : K.P.obj (D.src α)), π (1, 0) • K.z₁ α p + π (0, 1) • K.z₂ α p = z α p) :
    K.functor.obj (P1K k) ⟶ K.extRep z where
  app i := ModuleCat.ofHom (K.toExtP1Map π i)
  comm α := ModuleCat.hom_ext (LinearMap.ext fun x ↦ K.toExtP1Map_comm π z hz α x)

/-- The vertex map `L(S₋)(i) → E(z)(i)`. -/
def toExtSmMap (i : D.V) : K.space (Kron.Sminus k) i →ₗ[k] K.Q₀.obj i × K.P.obj i :=
  show (K.Q₀.obj i ⊗[k] k) × (K.P.obj i ⊗[k] PUnit.{u + 1}) →ₗ[k] K.Q₀.obj i × K.P.obj i from
    LinearMap.prod ((TensorProduct.rid k (K.Q₀.obj i)).toLinearMap ∘ₗ
      LinearMap.fst k (K.Q₀.obj i ⊗[k] k) (K.P.obj i ⊗[k] PUnit.{u + 1})) 0

lemma toExtSmMap_comm (z : ∀ α : D.A, K.P.obj (D.src α) →ₗ[k] K.Q₀.obj (D.tgt α)) (α : D.A)
    (x : K.space (Kron.Sminus k) (D.src α)) :
    K.toExtSmMap (D.tgt α) (K.arrMap (Kron.Sminus k) α x) =
      (LinearMap.prod (LinearMap.coprod (K.Q₀.map α).hom (z α))
        ((K.P.map α).hom ∘ₗ LinearMap.snd k _ _)) (K.toExtSmMap (D.src α) x) := by
  obtain ⟨t, s⟩ := x
  have key : ∀ (t : K.Q₀.obj (D.src α) ⊗[k] k) (s : K.P.obj (D.src α) ⊗[k] PUnit.{u + 1}),
      ((TensorProduct.rid k _) (TensorProduct.map (K.Q₀.map α).hom LinearMap.id t +
          (TensorProduct.map (K.z₁ α) (0 : PUnit.{u + 1} →ₗ[k] k) +
            TensorProduct.map (K.z₂ α) (0 : PUnit.{u + 1} →ₗ[k] k)) s), (0 : K.P.obj (D.tgt α))) =
      ((K.Q₀.map α).hom ((TensorProduct.rid k _) t) + z α 0, (K.P.map α).hom 0) := by
    intro t s
    have h1' : (TensorProduct.rid k (K.Q₀.obj (D.tgt α))).toLinearMap ∘ₗ
        TensorProduct.map (K.Q₀.map α).hom (LinearMap.id : k →ₗ[k] k) =
        (K.Q₀.map α).hom ∘ₗ (TensorProduct.rid k (K.Q₀.obj (D.src α))).toLinearMap :=
      TensorProduct.ext' fun q v ↦ by simp
    have h1 := LinearMap.congr_fun h1' t
    simp only [TensorProduct.map_zero_right, add_zero, LinearMap.zero_apply, map_zero]
    exact Prod.ext h1 rfl
  exact key t s

/-- The morphism `L(S₋) → E(z)`. -/
def toExtSm (z : ∀ α : D.A, K.P.obj (D.src α) →ₗ[k] K.Q₀.obj (D.tgt α)) :
    K.functor.obj (Kron.Sminus k) ⟶ K.extRep z where
  app i := ModuleCat.ofHom (K.toExtSmMap i)
  comm α := ModuleCat.hom_ext (LinearMap.ext fun x ↦ K.toExtSmMap_comm z α x)

lemma toExtP1_inj (x : (K.functor.obj (P1K k)).Tot)
    (h₁ : (K.toExtP1 (LinearMap.fst k k k) K.z₁ (fun α p ↦ by simp)).tot x = 0)
    (h₂ : (K.toExtP1 (LinearMap.snd k k k) K.z₂ (fun α p ↦ by simp)).tot x = 0) : x = 0 := by
  funext i
  have e₁ := congrFun h₁ i
  have e₂ := congrFun h₂ i
  have key : ∀ (t : K.Q₀.obj i ⊗[k] (k × k)) (s : K.P.obj i ⊗[k] k),
      ((TensorProduct.rid k _) (TensorProduct.map LinearMap.id (LinearMap.fst k k k) t),
        (TensorProduct.rid k _) s) = 0 →
      ((TensorProduct.rid k _) (TensorProduct.map LinearMap.id (LinearMap.snd k k k) t),
        (TensorProduct.rid k _) s) = 0 → ((t, s) : (K.Q₀.obj i ⊗[k] (k × k)) × (K.P.obj i ⊗[k] k)) = 0 := by
    intro t s ha hb
    have hf : ∀ t : K.Q₀.obj i ⊗[k] (k × k),
        TensorProduct.map LinearMap.id (LinearMap.fst k k k) t =
          (TensorProduct.prodRight k k (K.Q₀.obj i) k k t).1 := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul q w => simp
      | add t t' ht ht' => simp only [map_add, ht, ht', Prod.fst_add]
    have hs : ∀ t : K.Q₀.obj i ⊗[k] (k × k),
        TensorProduct.map LinearMap.id (LinearMap.snd k k k) t =
          (TensorProduct.prodRight k k (K.Q₀.obj i) k k t).2 := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul q w => simp
      | add t t' ht ht' => simp only [map_add, ht, ht', Prod.snd_add]
    obtain ⟨ha1, ha2⟩ := Prod.mk.inj ha
    obtain ⟨hb1, -⟩ := Prod.mk.inj hb
    rw [LinearEquiv.map_eq_zero_iff, hf] at ha1
    rw [LinearEquiv.map_eq_zero_iff, hs] at hb1
    rw [LinearEquiv.map_eq_zero_iff] at ha2
    have ht : TensorProduct.prodRight k k (K.Q₀.obj i) k k t = 0 := Prod.ext ha1 hb1
    rw [LinearEquiv.map_eq_zero_iff] at ht
    rw [ht, ha2]
    rfl
  exact key (x i).1 (x i).2 e₁ e₂

lemma toExtSm_inj (z : ∀ α : D.A, K.P.obj (D.src α) →ₗ[k] K.Q₀.obj (D.tgt α))
    (x : (K.functor.obj (Kron.Sminus k)).Tot) (h : (K.toExtSm z).tot x = 0) : x = 0 := by
  funext i
  have e := congrFun h i
  have key : ∀ (t : K.Q₀.obj i ⊗[k] k) (s : K.P.obj i ⊗[k] PUnit.{u + 1}),
      ((TensorProduct.rid k _) t, (0 : K.P.obj i)) = 0 →
        ((t, s) : (K.Q₀.obj i ⊗[k] k) × (K.P.obj i ⊗[k] PUnit.{u + 1})) = 0 := by
    intro t s h
    obtain ⟨h1, -⟩ := Prod.mk.inj h
    rw [LinearEquiv.map_eq_zero_iff] at h1
    have hs : s = 0 := by
      induction s using TensorProduct.induction_on with
      | zero => rfl
      | tmul p v => rw [Subsingleton.elim v 0, TensorProduct.tmul_zero]
      | add s s' hs hs' => rw [hs, hs', add_zero]
    rw [h1, hs]
    rfl
  exact key (x i).1 (x i).2 e

end Covering.KroneckerPair

namespace Covering.KroneckerPair

variable (K : KroneckerPair k D) (z : ∀ α : D.A, K.P.obj (D.src α) →ₗ[k] K.Q₀.obj (D.tgt α))

/-- The `Q₀`-part of the total space of `E(z)`. -/
def πQ : (K.extRep z).Tot →ₗ[k] K.Q₀.Tot :=
  LinearMap.pi fun i ↦ LinearMap.fst k _ _ ∘ₗ LinearMap.proj (φ := fun i ↦ (K.extRep z).obj i) i

/-- The `P`-part of the total space of `E(z)`. -/
def πP : (K.extRep z).Tot →ₗ[k] K.P.Tot :=
  LinearMap.pi fun i ↦ LinearMap.snd k _ _ ∘ₗ LinearMap.proj (φ := fun i ↦ (K.extRep z).obj i) i

/-- The extension block of an arrow. -/
def zOp (e : D.A) : K.P.Tot →ₗ[k] K.Q₀.Tot :=
  LinearMap.single k (fun i ↦ K.Q₀.obj i) (D.tgt e) ∘ₗ z e ∘ₗ
    LinearMap.proj (φ := fun i ↦ K.P.obj i) (D.src e)

/-- The extension block of a path. -/
def cross : List D.A → (K.P.Tot →ₗ[k] K.Q₀.Tot)
  | [] => 0
  | e :: le => K.Q₀.pathTot le ∘ₗ K.zOp z e + cross le ∘ₗ K.P.arrOp e

lemma πP_apply (x : (K.extRep z).Tot) (l : D.V) : K.πP z x l = (x l).2 := rfl

lemma πQ_apply (x : (K.extRep z).Tot) (l : D.V) : K.πQ z x l = (x l).1 := rfl

lemma πP_arrOp (e : D.A) : K.πP z ∘ₗ (K.extRep z).arrOp e = K.P.arrOp e ∘ₗ K.πP z := by
  refine LinearMap.ext fun x ↦ funext fun l ↦ ?_
  simp only [LinearMap.comp_apply, Rep.arrOp_apply, πP_apply]
  by_cases h : l = D.tgt e
  · subst h
    simp only [Pi.single_eq_same]
    rfl
  · simp only [Pi.single_eq_of_ne h]
    rfl

lemma πQ_arrOp (e : D.A) : K.πQ z ∘ₗ (K.extRep z).arrOp e =
    K.Q₀.arrOp e ∘ₗ K.πQ z + K.zOp z e ∘ₗ K.πP z := by
  refine LinearMap.ext fun x ↦ funext fun l ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, Rep.arrOp_apply, πQ_apply, Pi.add_apply,
    zOp, LinearMap.coe_single, LinearMap.coe_proj, Function.eval]
  by_cases h : l = D.tgt e
  · subst h
    simp only [Pi.single_eq_same]
    rfl
  · simp only [Pi.single_eq_of_ne h, add_zero]
    rfl

lemma πP_pathTot : ∀ le : List D.A,
    K.πP z ∘ₗ (K.extRep z).pathTot le = K.P.pathTot le ∘ₗ K.πP z
  | [] => rfl
  | e :: le => by
    change K.πP z ∘ₗ ((K.extRep z).pathTot le ∘ₗ (K.extRep z).arrOp e) =
      K.P.pathTot le ∘ₗ K.P.arrOp e ∘ₗ K.πP z
    rw [← LinearMap.comp_assoc, πP_pathTot le, LinearMap.comp_assoc, πP_arrOp]

lemma πQ_pathTot : ∀ le : List D.A,
    K.πQ z ∘ₗ (K.extRep z).pathTot le = K.Q₀.pathTot le ∘ₗ K.πQ z + K.cross z le ∘ₗ K.πP z
  | [] => by simp [cross]; rfl
  | e :: le => by
    change K.πQ z ∘ₗ ((K.extRep z).pathTot le ∘ₗ (K.extRep z).arrOp e) =
      (K.Q₀.pathTot le ∘ₗ K.Q₀.arrOp e) ∘ₗ K.πQ z +
        (K.Q₀.pathTot le ∘ₗ K.zOp z e + K.cross z le ∘ₗ K.P.arrOp e) ∘ₗ K.πP z
    rw [← LinearMap.comp_assoc, πQ_pathTot le, LinearMap.add_comp, LinearMap.comp_assoc,
      πQ_arrOp, LinearMap.comp_assoc, πP_arrOp, LinearMap.comp_add, LinearMap.add_comp]
    simp only [LinearMap.comp_assoc]
    abel

lemma eq_zero_of_π (x : (K.extRep z).Tot) (hQ : K.πQ z x = 0) (hP : K.πP z x = 0) : x = 0 :=
  funext fun i ↦ Prod.ext (congrFun hQ i) (congrFun hP i)

end Covering.KroneckerPair

namespace RayCat

open Cover RayQuiver

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P} {S : Finset (Cover x₀)}

/-- **An extension respects the cover** when its two layers and its extension blocks do. -/
theorem respectsCover_extRep (K : KroneckerPair k (pieceQuiver S))
    (z : ∀ α : (pieceQuiver S).A, K.P.obj ((pieceQuiver S).src α) →ₗ[k]
      K.Q₀.obj ((pieceQuiver S).tgt α))
    (hQ : RespectsCover K.Q₀) (hP : RespectsCover K.P)
    (hc0 : ∀ le i j (h : FinQuiver.PathFrom i le j), compD S le i j h = 0 → K.cross z le = 0)
    (hc : ∀ le le' i j (h : FinQuiver.PathFrom i le j) (h' : FinQuiver.PathFrom i le' j),
      compD S le i j h = compD S le' i j h' → K.cross z le = K.cross z le') :
    RespectsCover (K.extRep z) := by
  have eQ : ∀ le x, K.πQ z ((K.extRep z).pathTot le x) =
      K.Q₀.pathTot le (K.πQ z x) + K.cross z le (K.πP z x) := fun le x ↦ by
    simpa using LinearMap.congr_fun (K.πQ_pathTot z le) x
  have eP : ∀ le x, K.πP z ((K.extRep z).pathTot le x) = K.P.pathTot le (K.πP z x) :=
    fun le x ↦ by simpa using LinearMap.congr_fun (K.πP_pathTot z le) x
  refine ⟨fun le i j h h0 ↦ LinearMap.ext fun x ↦ K.eq_zero_of_π z _ ?_ ?_,
    fun le le' i j h h' he ↦ LinearMap.ext fun x ↦ sub_eq_zero.1 (K.eq_zero_of_π z _ ?_ ?_)⟩
  · rw [eQ, hQ.1 le i j h h0, hc0 le i j h h0]
    simp
  · rw [eP, hP.1 le i j h h0]
    rfl
  · rw [map_sub, eQ, eQ, hQ.2 le le' i j h h' he, hc le le' i j h h' he, sub_self]
  · rw [map_sub, eP, eP, hP.2 le le' i j h h' he, sub_self]

/-- **The generic objects of a Kronecker pair respect the cover** when its two extensions do. -/
theorem respectsCover_generic (K : KroneckerPair k (pieceQuiver S))
    (h₁ : RespectsCover (K.extRep K.z₁)) (h₂ : RespectsCover (K.extRep K.z₂)) :
    RespectsCover (K.functor.obj (Kron.Sminus k)) ∧ RespectsCover (K.functor.obj (P1K k)) :=
  ⟨respectsCover_of_two (K.toExtSm K.z₁) (K.toExtSm K.z₁)
      (fun x hx _ ↦ K.toExtSm_inj K.z₁ x hx) h₁ h₁,
    respectsCover_of_two _ _ (fun x hx hy ↦ K.toExtP1_inj x hx hy) h₁ h₂⟩

end RayCat

end LargeIndecomposable
