module

public import LargeIndecomposable.RepresentationEmbeddings.CoveringConstruction.Datum

/-!
# The facts about `S₋` for the covering construction

For covering data, the two facts about `S₋` used in Theorem 2.7 hold
automatically, so covering data alone yield a controlled embedding.

* `F₂(S₋) = π_*L(S₋)` is indecomposable: `L(S₋)` is a brick, and for each class
  `γ ≠ 1` of block positions some vertex `x` of the support of `L(S₋)` has
  `γ x` outside the support (the argument of Proposition 4.4 for `L(S₋)`), so
  `PdData.isIndecomposable_of_brick` applies.
* `F₂(S₋) ≇ F₂(T)` for `T ∈ C_fin`: by exactness, `dim L(T)(x)` is
  `dim L(0, W)(x) + dim L(V, 0)(x)`, and `S₋`, `S₊` are retracts of `(0, W)`,
  `(V, 0)` when `W`, `V` are nonzero; so a nonzero `T ∈ C` has
  `dim F₂(T) ≥ dim L(S₊) + dim L(S₋) > dim F₂(S₋)`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Statement WalkingParallelPair FinQuiver Rep

universe u

namespace Covering

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]

/-- `S₋` is a brick. -/
lemma sminus_brick (φ : Extension.SminusFin (k := k) ⟶ Extension.SminusFin) :
    ∃ c : k, φ = c • 𝟙 _ := by
  let g : k →ₗ[k] k := (φ.hom.app one).hom
  refine ⟨g 1, ?_⟩
  ext1
  refine Kron.hom_ext (hom_ext_punit' _ _) ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun (t : k) ↦ ?_)
  change g t = g 1 * t
  rw [show t = t • (1 : k) by simp, _root_.map_smul, smul_eq_mul, mul_comm, smul_eq_mul, mul_one]

namespace CoveringData

variable (W : CoveringData k A)

lemma indecS : IsIndecomposable A (W.toPdData.functor.obj Extension.SminusFin) := by
  classical
  let P : W.D.V → Prop := fun c ↦ Nontrivial ((W.L.obj (SminusK k)).obj c)
  obtain ⟨c₀, hc₀⟩ := W.nonzero.2
  refine W.toPdData.isIndecomposable_of_brick Extension.SminusFin P sminus_brick
    (fun _ h ↦ h) (fun κ ↦ ?_) ⟨c₀, hc₀⟩
  obtain ⟨a₀, hκ⟩ := κ.2
  obtain ⟨c, hc, hcj⟩ := W.C.zeroCol_rel P hc₀ a₀
  refine ⟨c, hc, fun f hf ↦ ?_⟩
  refine (comp_idm_eq_sum _ _).trans ?_
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  refine (bl_restr _ _ j c).trans ?_
  split_ifs with hj
  · by_cases hp : W.p.vert j = W.p.vert c
    · have hnP : ¬ P j := fun hPj ↦ hj.1 (hcj j hPj ((congrArg Subtype.val hj.2).trans hκ.symm) hp)
      have : Subsingleton ((W.L.obj (SminusK k)).obj j) := not_nontrivial_iff_subsingleton.1 hnP
      have h0 : (W.toPdData.L.obj Extension.SminusFin).idm j = 0 :=
        @idm_eq_zero _ _ _ (W.toPdData.L.obj Extension.SminusFin) j this
      simp only [bl, h0, LinearMap.zero_comp]
    · exact hf.1 j c hp
  · rfl

/-- The vertexwise dimension splits along `(0, W) → X → (V, 0)`. -/
lemma finrank_split (X : Kfin k) (c : W.D.V) :
    Module.finrank k ((W.L.obj X).obj c) = Module.finrank k ((W.L.obj (socK X)).obj c) +
      Module.finrank k ((W.L.obj (topK X)).obj c) := by
  have := W.fin X c
  have := W.fin (socK X) c
  have := W.fin (topK X) c
  obtain ⟨hinj, hsurj, hre⟩ := W.exact _ _ _ (fromSoc X) (toTop X) (isShortExact_soc_top X) c
  set f := ((W.L.map (fromSoc X)).app c).hom
  set g := ((W.L.map (toTop X)).app c).hom
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, ← hre, LinearMap.finrank_range_of_inj hinj] at h1
  omega

lemma finrank_le_of_retract {X Y : Kfin k} (s : X ⟶ Y) (r : Y ⟶ X) (h : s ≫ r = 𝟙 X)
    (c : W.D.V) :
    Module.finrank k ((W.L.obj X).obj c) ≤ Module.finrank k ((W.L.obj Y).obj c) := by
  have := W.fin Y c
  refine LinearMap.finrank_le_finrank_of_injective (f := ((W.L.map s).app c).hom) fun x y hxy ↦ ?_
  have e : ∀ z, ((W.L.map r).app c).hom (((W.L.map s).app c).hom z) = z := by
    intro z
    have := congrArg (fun φ ↦ (φ.app c).hom z) (W.L.map_comp s r)
    simp only [h, CategoryTheory.Functor.map_id] at this
    exact this.symm
  rw [← e x, ← e y, hxy]

lemma splus_le_top (X : Kfin k) (hV : Nontrivial X.obj.V) (c : W.D.V) :
    Module.finrank k ((W.L.obj (SplusK k)).obj c) ≤ Module.finrank k ((W.L.obj (topK X)).obj c) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : X.obj.V)
  obtain ⟨lam, hlam⟩ := Module.Projective.exists_dual_eq_one k hv
  let s : SplusK k ⟶ topK X := ObjectProperty.homMk (Kron.homMk
    (ModuleCat.ofHom (LinearMap.toSpanSingleton k _ v)) 0 (hom_ext_punit _ _) (hom_ext_punit _ _))
  let r : topK X ⟶ SplusK k := ObjectProperty.homMk (Kron.homMk (ModuleCat.ofHom lam) 0
    (hom_ext_punit _ _) (hom_ext_punit _ _))
  refine W.finrank_le_of_retract s r ?_ c
  ext1
  refine Kron.hom_ext (ModuleCat.hom_ext (LinearMap.ext fun (t : k) ↦ ?_)) (hom_ext_punit _ _)
  change lam (t • v) = t
  rw [_root_.map_smul, hlam, smul_eq_mul, mul_one]

lemma sminus_le_soc (X : Kfin k) (hW : Nontrivial X.obj.W) (c : W.D.V) :
    Module.finrank k ((W.L.obj (SminusK k)).obj c) ≤ Module.finrank k ((W.L.obj (socK X)).obj c) := by
  obtain ⟨w, hw⟩ := exists_ne (0 : X.obj.W)
  obtain ⟨lam, hlam⟩ := Module.Projective.exists_dual_eq_one k hw
  let s : SminusK k ⟶ socK X := ObjectProperty.homMk (Kron.homMk 0
    (ModuleCat.ofHom (LinearMap.toSpanSingleton k _ w)) (hom_ext_punit' _ _) (hom_ext_punit' _ _))
  let r : socK X ⟶ SminusK k := ObjectProperty.homMk (Kron.homMk 0 (ModuleCat.ofHom lam)
    (hom_ext_punit' _ _) (hom_ext_punit' _ _))
  refine W.finrank_le_of_retract s r ?_ c
  ext1
  refine Kron.hom_ext (hom_ext_punit' _ _) (ModuleCat.hom_ext (LinearMap.ext fun (t : k) ↦ ?_))
  change lam (t • w) = t
  rw [_root_.map_smul, hlam, smul_eq_mul, mul_one]

lemma finrank_tot (X : Kfin k) :
    Module.finrank k (W.L.obj X).Tot = ∑ c, Module.finrank k ((W.L.obj X).obj c) := by
  have := W.fin X
  exact Module.finrank_pi_fintype k

lemma notIsoS (X : Dfin k) (hX : InC X.obj) :
    IsEmpty (W.toPdData.functor.obj Extension.SminusFin ≅ W.toPdData.functor.obj X) := by
  refine ⟨fun e ↦ ?_⟩
  have h := W.toPdData.finrank_eq_of_iso e
  change Module.finrank k (W.L.obj (SminusK k)).Tot =
    Module.finrank k (W.L.obj ((DfinToKfin k).obj X)).Tot at h
  rw [W.finrank_tot, W.finrank_tot] at h
  set X' := (DfinToKfin k).obj X
  obtain ⟨cm, hcm⟩ := W.nonzero.2
  have hposm : 0 < ∑ c, Module.finrank k ((W.L.obj (SminusK k)).obj c) := by
    have := W.fin (SminusK k) cm
    exact lt_of_lt_of_le (Module.finrank_pos (R := k) (M := (W.L.obj (SminusK k)).obj cm))
      (Finset.single_le_sum (f := fun c ↦ Module.finrank k ((W.L.obj (SminusK k)).obj c))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ cm))
  have hX' := X.2.2
  have : Module.Finite k X.obj.V := hX'.1
  have : Module.Finite k X.obj.W := hX'.2
  by_cases hV : Nontrivial X.obj.V
  · have hW : Nontrivial X.obj.W := by
      by_contra hW
      rw [not_nontrivial_iff_subsingleton] at hW
      obtain ⟨v, hv⟩ := exists_ne (0 : X.obj.V)
      exact hv ((inD_iff X.obj).1 hX.1 v (Subsingleton.elim _ _) (Subsingleton.elim _ _))
    obtain ⟨cp, hcp⟩ := W.nonzero.1
    have hle : ∀ c, Module.finrank k ((W.L.obj (SminusK k)).obj c) +
        Module.finrank k ((W.L.obj (SplusK k)).obj c) ≤ Module.finrank k ((W.L.obj X').obj c) :=
      fun c ↦ by
        rw [W.finrank_split X' c]
        exact add_le_add (W.sminus_le_soc X' hW c) (W.splus_le_top X' hV c)
    have hposp : 0 < Module.finrank k ((W.L.obj (SplusK k)).obj cp) := by
      have := W.fin (SplusK k) cp
      exact Module.finrank_pos
    have hsum := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) ↦ hle c
    rw [Finset.sum_add_distrib] at hsum
    have := Finset.single_le_sum (f := fun c ↦ Module.finrank k ((W.L.obj (SplusK k)).obj c))
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ cp)
    omega
  · rw [not_nontrivial_iff_subsingleton] at hV
    -- then `X = 0`, so `L(X) = 0`
    have hW : Subsingleton X.obj.W := by
      refine ⟨fun w w' ↦ ?_⟩
      have htop : (⊤ : Submodule k X.obj.W) = ⊥ := by
        rw [← hX.2]
        simp [Subsingleton.elim _ (0 : X.obj.V →ₗ[k] X.obj.W)]
      have hw : w ∈ (⊥ : Submodule k X.obj.W) := htop ▸ Submodule.mem_top
      have hw' : w' ∈ (⊥ : Submodule k X.obj.W) := htop ▸ Submodule.mem_top
      rw [Submodule.mem_bot] at hw hw'
      rw [hw, hw']
    have hid : 𝟙 X' = 0 := by
      ext1
      refine Kron.hom_ext (ModuleCat.hom_ext (LinearMap.ext fun _ ↦ Subsingleton.elim (α := X.obj.V) _ _))
        (ModuleCat.hom_ext (LinearMap.ext fun _ ↦ Subsingleton.elim (α := X.obj.W) _ _))
    have hz : ∀ c, Module.finrank k ((W.L.obj X').obj c) = 0 := by
      intro c
      have := W.fin X' c
      refine Module.finrank_zero_iff.2 ⟨fun a b ↦ ?_⟩
      have e : ∀ z : (W.L.obj X').obj c, z = 0 := by
        intro z
        have := congrArg (fun φ ↦ (φ.app c).hom z) (congrArg W.L.map hid)
        simp only [CategoryTheory.Functor.map_id, Functor.map_zero] at this
        exact this
      rw [e a, e b]
    simp only [hz, Finset.sum_const_zero] at h
    omega

/-- Covering data give push-down data with the facts
about `S₋` used in Theorem 2.7. -/
def toPdDatum : PushDown.PdDatum k A where
  toPdData := W.toPdData
  indecS := W.indecS
  notIsoS := W.notIsoS

/-- The covering construction as a controlled embedding. -/
def controlledEmbedding : ControlledEmbedding k A := W.toPdDatum.controlledEmbedding

end CoveringData

end Covering

end LargeIndecomposable
