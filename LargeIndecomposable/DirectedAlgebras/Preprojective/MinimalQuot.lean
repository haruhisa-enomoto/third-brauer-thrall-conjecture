module

public import LargeIndecomposable.DirectedAlgebras.Directing.QuotAny
public import LargeIndecomposable.DirectedAlgebras.Preprojective.CriticalAbstract

/-!
# The minimal quotient

Let `D` be a directed algebra whose indecomposable projectives are good, with unbounded
indecomposables and `dim e_y A e_x ≤ 1`. A minimal set `T'` of points such that the quotient
`A / ⟨e_v : v ∉ T'⟩` has unbounded indecomposables carries point–brick data (`exists_pointBrick`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

section Generic

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  (D : DirData k A)

/-- If all vertex projectives are good, the good modules form a preprojective component. -/
theorem preprojComp_of_goodProj (hT : ∀ x, x ∈ D.T)
    (hg : ∀ x, Good (projE (k := k) (D.idem x))) (x₀ : D.ι) :
    PreprojComp (Good (k := k) (A := A)) := by
  have hproj : ∀ P : FDMod k A, IndNT P → IsFreeSummand A P → Good P := fun P hP hfree ↦ by
    obtain ⟨y, hy, hiso⟩ := D.iso_proj_of_freeSummand hP hfree
    exact (hg y).of_iso hiso.symm
  exact preprojComp_good ⟨_, hg x₀⟩ fun X Y hX hY f hf ↦ good_succ hproj X hX Y hY f hf

lemma exists_e_smul_ne {N : FDMod k A} (hN : Nontrivial N) : ∃ (x : D.ι) (n : N), D.e x • n ≠ 0 := by
  obtain ⟨n, hn⟩ := exists_ne (0 : N)
  by_contra h
  push Not at h
  apply hn
  have h5 : n = ∑ x, D.e x • n := by
    rw [← Finset.sum_smul, D.sum, one_smul]
  rw [h5]
  exact Finset.sum_eq_zero fun x _ ↦ h x n

lemma exists_proj_hom_ne' {i : D.ι} {U : FDMod k A} {u : U} (hu : D.e i • u ≠ 0) :
    ∃ f : projE (k := k) (D.idem i) ⟶ U, FDMod.lin f ≠ 0 := by
  refine ⟨(FDMod.ofLin (show projE (k := k) (D.idem i) →ₗ[A] U from
    { toFun := fun b ↦ (b : A) • u
      map_add' := fun a b ↦ add_smul _ _ _
      map_smul' := fun a b ↦ mul_smul _ _ _ })), fun h0 ↦ hu ?_⟩
  exact LinearMap.congr_fun h0 (DirData.genP i)

/-- A preprojective component of bounded modules containing all projectives is everything. -/
theorem good_of_closed (hg : ∀ x, Good (projE (k := k) (D.idem x)))
    (hcl : ClosedClass (Good (k := k) (A := A))) (N : FDMod k A) (hN : IndNT N) : Good N := by
  obtain ⟨x, n, hn⟩ := exists_e_smul_ne D hN.2
  obtain ⟨f, hf⟩ := exists_proj_hom_ne' D hn
  exact hcl.mem_of_hom_from hN.1 (hg x) f hf

/-- With a bound on good modules, the good modules form a closed class. -/
lemma closedClass_good (h𝒞 : PreprojComp (Good (k := k) (A := A))) (b : ℕ)
    (hb : ∀ X : FDMod k A, Good X → finrank k X ≤ b) : ClosedClass (Good (k := k) (A := A)) where
  indNT := h𝒞.indNT
  iso := h𝒞.iso
  pred := h𝒞.pred_chosen
  las := h𝒞.lasFam
  bound := ⟨b, hb⟩

/-- **Unbounded indecomposables give unbounded good modules.** -/
theorem good_unbounded (hg : ∀ x, Good (projE (k := k) (D.idem x)))
    (h𝒞 : PreprojComp (Good (k := k) (A := A)))
    (hunb : ∀ b, ∃ N : FDMod k A, IndNT N ∧ b < finrank k N) (b : ℕ) :
    ∃ X : FDMod k A, Good X ∧ b < finrank k X := by
  by_contra hno
  push Not at hno
  obtain ⟨N, hN, hNb⟩ := hunb b
  have := hno N (good_of_closed D hg (closedClass_good h𝒞 b hno) N hN)
  omega

/-- **Bounded algebras with good projectives are directed.** -/
theorem directing_of_bounded (hg : ∀ x, Good (projE (k := k) (D.idem x)))
    (hT : ∀ x, x ∈ D.T) (b : ℕ) (hb : ∀ N : FDMod k A, IndNT N → finrank k N ≤ b) (N : FDMod k A)
    (hN : IndNT N) : Directing N := by
  obtain ⟨x, -, -⟩ := exists_e_smul_ne D hN.2
  have h𝒞 := preprojComp_of_goodProj D hT hg x
  exact h𝒞.directing (good_of_closed D hg (closedClass_good h𝒞 b fun X hX ↦ hb X hX.1) N hN)

end Generic

namespace DirData

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  (D : DirData k A)

/-- Unbounded indecomposables on the quotient for `T'`. -/
def Unb (T' : Set D.ι) : Prop :=
  ∀ b, ∃ N : FDMod k (D.QAlg T'), IndNT N ∧ b < finrank k N

variable {D}

/-- An extension of modules with a common smaller support descends. -/
theorem extVanish_of_descend {T' T'' : Set D.ι} {X Y : FDMod k (D.QAlg T')}
    (hX : LivesOn T'' (resFD (D.qmap T') X)) (hY : LivesOn T'' (resFD (D.qmap T') Y))
    (hv : ExtVanish (descendQ _ hX) (descendQ _ hY)) : ExtVanish X Y := by
  intro E i p hi hp hex
  have hφ := D.qmap_surjective T'
  have hφ' := D.qmap_surjective T''
  -- `E` lives on `T''`
  have hE : LivesOn T'' (resFD (D.qmap T') E) := by
    intro v hv' m
    have h1 : D.qmap T' (D.e v) • (show E from m) = 0 := by
      have h2 : p (D.qmap T' (D.e v) • (show E from m)) = 0 := by
        rw [map_smul]
        exact hX v hv' (ofX (p m))
      have h3 : D.qmap T' (D.e v) • (show E from m) ∈ LinearMap.ker p := h2
      rw [← hex] at h3
      obtain ⟨y, hy⟩ := h3
      have h4 : i (D.qmap T' (D.e v) • y) = D.qmap T' (D.e v) • (show E from m) := by
        rw [map_smul, hy, ← mul_smul, ← map_mul, D.e_mul_e]
      rw [← h4]
      have h5 : D.qmap T' (D.e v) • y = 0 := hY v hv' (ofX y)
      rw [h5, map_zero]
    exact h1
  let E₁ := descendQ _ hE
  let i₁ : descendQ _ hY →ₗ[D.QAlg T''] E₁ :=
    { toFun := fun y ↦ i y
      map_add' := fun a b ↦ map_add i a b
      map_smul' := fun a y ↦ by
        obtain ⟨a, rfl⟩ := hφ' a
        change i (actQ (resFD (D.qmap T') Y) hY (D.qmap T'' a)
            (show resFD (D.qmap T') Y from y)) =
          actQ (resFD (D.qmap T') E) hE (D.qmap T'' a)
            (show resFD (D.qmap T') E from i (show Y from y))
        rw [actQ_qmap, actQ_qmap]
        exact map_smul i (D.qmap T' a) (show Y from y) }
  let p₁ : E₁ →ₗ[D.QAlg T''] descendQ _ hX :=
    { toFun := fun y ↦ p y
      map_add' := fun a b ↦ map_add p a b
      map_smul' := fun a y ↦ by
        obtain ⟨a, rfl⟩ := hφ' a
        change p (actQ (resFD (D.qmap T') E) hE (D.qmap T'' a)
            (show resFD (D.qmap T') E from y)) =
          actQ (resFD (D.qmap T') X) hX (D.qmap T'' a)
            (show resFD (D.qmap T') X from p (show E from y))
        rw [actQ_qmap, actQ_qmap]
        exact map_smul p (D.qmap T' a) (show E from y) }
  obtain ⟨s₁, hs₁⟩ := hv E₁ i₁ p₁ hi hp (by
    ext x
    exact (Set.ext_iff.1 (congrArg (fun U : Submodule _ _ ↦ (U : Set E)) hex) x))
  refine ⟨{ toFun := fun x ↦ s₁ x
            map_add' := fun a b ↦ map_add s₁ a b
            map_smul' := fun a y ↦ ?_ }, LinearMap.ext fun x ↦ LinearMap.congr_fun hs₁ x⟩
  obtain ⟨a, rfl⟩ := hφ a
  have h1 := map_smul s₁ (D.qmap T'' a) (show descendQ _ hX from y)
  change s₁ (actQ (resFD (D.qmap T') X) hX (D.qmap T'' a) (show resFD (D.qmap T') X from y)) =
    actQ (resFD (D.qmap T') E) hE (D.qmap T'' a) (show resFD (D.qmap T') E from s₁ y) at h1
  rw [actQ_qmap, actQ_qmap] at h1
  exact h1

lemma euler_smul (D : DirData k A) (c : ℤ) (u w : D.ι → ℤ) : euler D (c • u) w = c * euler D u w := by
  unfold euler
  rw [Matrix.mulVec_smul, smul_dotProduct, smul_eq_mul]

/-- **A critical Schurian directed algebra has at least three points.** -/
theorem three_le_card (D : DirData k A) (hT : ∀ x, x ∈ D.T) (hsch : ∀ x y, cartan D y x ≤ 1)
    (hq : (eulerForm D hT).Critical) : 3 ≤ Fintype.card D.ι := by
  classical
  by_contra hc
  push Not at hc
  obtain ⟨z, hz, hv⟩ := Forms.UnitForm.Critical.exists_sincere _ hq
  rw [eulerForm_val] at hv
  haveI : Nonempty D.ι := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    exact hq.1 fun x hx ↦ absurd (funext fun i ↦ hemp.elim i) hx.2
  obtain ⟨a, -, hmin⟩ := (Finset.univ : Finset D.ι).exists_min_image D.depth Finset.univ_nonempty
  have hsink : IsSink D a := by
    intro y hy c
    by_contra h
    have h1 := D.depth_lt (Ne.symm hy) c h
    have h2 := hmin y (Finset.mem_univ y)
    omega
  have hea : ∀ v, euler D (Pi.single a 1) v = v a := euler_sink hT hsink
  by_cases hb : ∃ b, b ≠ a
  · obtain ⟨b, hba⟩ := hb
    have hall : ∀ c, c = a ∨ c = b := by
      intro c
      by_contra hne
      push Not at hne
      have h1 : ({a, b, c} : Finset D.ι).card = 3 := by
        rw [Finset.card_eq_three]
        exact ⟨a, b, c, Ne.symm hba, Ne.symm hne.1, Ne.symm hne.2, rfl⟩
      have h2 := Finset.card_le_card (Finset.subset_univ ({a, b, c} : Finset D.ι))
      rw [h1, Finset.card_univ] at h2
      omega
    let p : ℤ := cartan D a b
    have hp0 : 0 ≤ p := by simp [p, cartan]
    have hp1 : p ≤ 1 := hsch b a
    have hP : (fun j ↦ cartan D j b) = p • (Pi.single a 1 : D.ι → ℤ) + Pi.single b 1 := by
      funext j
      rcases hall j with rfl | rfl
      · simp [p, Pi.single_apply, hba.symm]
      · simp [cartan_diag D (hT j), Pi.single_apply, hba]
    have hzz : z = z a • (Pi.single a 1 : D.ι → ℤ) + z b • (Pi.single b 1 : D.ι → ℤ) := by
      funext j
      rcases hall j with rfl | rfl
      · simp [Pi.single_apply, hba.symm]
      · simp [Pi.single_apply, hba]
    have h1 := euler_cartan_col D hT b z
    rw [hP, euler_add, euler_smul, hea] at h1
    have h2 : euler D z z = z a * z a + z b * euler D (Pi.single b 1) z := by
      conv_lhs => rw [hzz]
      rw [euler_add, euler_smul, euler_smul, ← hzz, hea]
    have ha := hz a
    have hbp := hz b
    have h3 : euler D (Pi.single b 1) z = z b - p * z a := by linarith
    rw [h3] at h2
    have h4 : p = 0 ∨ p = 1 := by omega
    rcases h4 with h4 | h4 <;> rw [h4] at h2 <;> nlinarith [sq_nonneg (z a - z b)]
  · push Not at hb
    have hzz : z = z a • (Pi.single a 1 : D.ι → ℤ) := by
      funext j
      rw [hb j]
      simp
    have h2 : euler D z z = z a * z a := by
      conv_lhs => rw [hzz]
      rw [euler_smul, ← hzz, hea]
    have ha := hz a
    nlinarith

/-- Corners of the quotient are quotients of corners. -/
lemma cartan_quotAny_le {T' : Set D.ι} (hT : T' ⊆ D.T) (x y : T') :
    cartan (D.quotAny hT) y x ≤ cartan D y.1 x.1 := by
  let g := D.piP hT x
  let ψ : eSub (projE (k := k) (D.idem x.1)) (D.e y.1) →ₗ[k]
      eSub (projE (k := k) ((D.quotAny hT).idem x)) ((D.quotAny hT).e y) :=
    { toFun := fun m ↦ ⟨toX (g m), by
        change D.qmap T' (D.e y.1) • toX (g m) = toX (g m)
        have h1 : g (D.e y.1 • (m : projE (k := k) (D.idem x.1))) =
            D.e y.1 • g m := map_smul g _ _
        rw [show D.e y.1 • (m : projE (k := k) (D.idem x.1)) = m from m.2] at h1
        exact (congrArg toX h1).symm⟩
      map_add' := fun a b ↦ Subtype.ext (map_add g _ _)
      map_smul' := fun c a ↦ Subtype.ext (LinearMap.map_smul_of_tower g c _) }
  have hψ : Function.Surjective ψ := by
    rintro ⟨m, hm⟩
    obtain ⟨l, hl⟩ := D.piP_surjective hT x (ofX m)
    have hmem : D.e y.1 • l ∈ eSub (projE (k := k) (D.idem x.1)) (D.e y.1) := by
      change D.e y.1 • D.e y.1 • l = _
      rw [← mul_smul, D.e_mul_e]
    refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    change toX (g (D.e y.1 • l)) = m
    rw [map_smul]
    change D.qmap T' (D.e y.1) • toX (g l) = m
    rw [show toX (g l) = m from congrArg toX hl]
    exact hm
  have := LinearMap.finrank_le_finrank_of_surjective hψ
  change ((finrank k (eSub (projE (k := k) ((D.quotAny hT).idem x)) ((D.quotAny hT).e y)) : ℕ) : ℤ) ≤
    ((finrank k (eSub (projE (k := k) (D.idem x.1)) (D.e y.1)) : ℕ) : ℤ)
  exact_mod_cast this

/-- Modules killed by `e_i` live on `T' \ {i}`. -/
lemma livesOn_diff {T' : Set D.ι} (hT : T' ⊆ D.T) (i : T') {N : FDMod k (D.QAlg T')}
    (h : ∀ m : N, (D.quotAny hT).e i • m = 0) :
    LivesOn (T' \ {i.1}) (resFD (D.qmap T') N) := by
  intro v hv m
  by_cases hvT : v ∈ T'
  · have hvi : v = i.1 := by
      by_contra hne
      exact hv ⟨hvT, hne⟩
    subst hvi
    exact h m
  · change D.qmap T' (D.e v) • (show N from m) = 0
    rw [D.qmap_e_out T' hvT, zero_smul]

/-- **Point–brick data on a minimal quotient.** -/
theorem exists_pointBrick [IsAlgClosed k] (hT : ∀ x, x ∈ D.T) (hsch : ∀ x y, cartan D y x ≤ 1)
    (hg : ∀ x, Good (projE (k := k) (D.idem x))) (hunb : D.Unb Set.univ) :
    ∃ (T' : Set D.ι) (hT' : T' ⊆ D.T), PointBrickM (D.quotAny hT') (fun _ ↦ Set.mem_univ _) := by
  classical
  have hex : ∃ n, ∃ T' : Set D.ι, T'.ncard = n ∧ D.Unb T' := ⟨_, _, rfl, hunb⟩
  obtain ⟨T', hn, hU⟩ := Nat.find_spec hex
  have hmin : ∀ T'' : Set D.ι, T''.ncard < T'.ncard → ¬D.Unb T'' := fun T'' hlt hu ↦
    Nat.find_min hex (hn ▸ hlt) ⟨T'', rfl, hu⟩
  have hsub : T' ⊆ D.T := fun x _ ↦ hT x
  have hTB : ∀ x, x ∈ (D.quotAny hsub).T := fun _ ↦ Set.mem_univ _
  refine ⟨T', hsub, ?_⟩
  let DB := D.quotAny hsub
  have hgB : ∀ x, Good (projE (k := k) (DB.idem x)) := fun x ↦ good_quot hsub x (hg x.1)
  obtain ⟨N₀, hN₀, -⟩ := hU 0
  obtain ⟨x₀, -, -⟩ := exists_e_smul_ne DB hN₀.2
  have h𝒞 := preprojComp_of_goodProj DB hTB hgB x₀
  have hun := good_unbounded DB hgB h𝒞 hU
  have hφ := D.qmap_surjective T'
  -- bounds off a point
  have hoff0 : ∀ i : T', ∃ b, ∀ N : FDMod k (D.QAlg (T' \ {i.1})), IndNT N → finrank k N ≤ b := by
    intro i
    have h1 := hmin (T' \ {i.1}) (Set.ncard_sdiff_singleton_lt_of_mem i.2 (Set.toFinite _))
    unfold Unb at h1
    push Not at h1
    exact h1
  have hindD : ∀ (i : T') (N : FDMod k (D.QAlg T')) (hN : IndNT N)
      (hl : LivesOn (T' \ {i.1}) (resFD (D.qmap T') N)), IndNT (descendQ _ hl) := by
    intro i N hN hl
    exact (indNT_res_iff (D.qmap_surjective _) _).1
      (indNT_of_iso (isoM_descend' _ hl) ((indNT_res_iff hφ N).2 hN))
  have hoff : ∀ i : T', ∃ b, ∀ N : FDMod k (D.QAlg T'), IndNT N →
      (∀ m : N, DB.e i • m = 0) → finrank k N ≤ b := by
    intro i
    obtain ⟨b, hb⟩ := hoff0 i
    exact ⟨b, fun N hN hk ↦ hb _ (hindD i N hN (livesOn_diff hsub i hk))⟩
  have hR : RigidOff DB := by
    intro i N h1 h2 hk
    have hl := livesOn_diff hsub i hk
    obtain ⟨b, hb⟩ := hoff0 i
    have hsub' : T' \ {i.1} ⊆ D.T := fun x _ ↦ hT x
    have hdir := directing_of_bounded (D.quotAny hsub') (fun x ↦ good_quot hsub' x (hg x.1))
      (fun _ ↦ Set.mem_univ _) b hb _ (hindD i N ⟨h1, h2⟩ hl)
    exact extVanish_of_descend hl hl hdir.extVanish
  have hc : ∀ b, ∃ X : FDMod k (D.QAlg T'), Directing X ∧ Sincere DB X ∧ b < finrank k X := by
    intro b
    choose B hB using hoff
    obtain ⟨X, hX, hXb⟩ := hun (b + ∑ i : DB.ι, B i)
    refine ⟨X, h𝒞.directing hX, ?_, by omega⟩
    by_contra hns
    simp only [Sincere, not_forall, not_exists, not_not] at hns
    obtain ⟨x, hx⟩ := hns
    have h1 := hB x X hX.1 hx
    have h2 : B x ≤ ∑ i : DB.ι, B i :=
      Finset.single_le_sum (f := B) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ x)
    omega
  have hcrit := eulerForm_critical hTB hR hc h𝒞 hun
  have hcard := three_le_card DB hTB (fun x y ↦ (cartan_quotAny_le hsub x y).trans (hsch _ _)) hcrit
  exact pointBrickM hTB hcard hR hc h𝒞 hun

section Res

variable {A' : Type u} [Ring A'] [Algebra k A'] {φ : A →ₐ[k] A'}

/-- Restriction identifies homomorphism spaces. -/
def homResEquiv (hφ : Function.Surjective φ) (X Y : FDMod k A') :
    (X →ₗ[A'] Y) ≃ₗ[k] (resFD φ X →ₗ[A] resFD φ Y) where
  toFun e := FDMod.lin (resHom φ (show X ⟶ Y from (FDMod.ofLin (e))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun e := FDMod.lin (unresHom hφ (show resFD φ X ⟶ resFD φ Y from (FDMod.ofLin (e))))
  left_inv _ := rfl
  right_inv _ := rfl

lemma finrank_range_res (hφ : Function.Surjective φ) {K P Y : FDMod k A'} (f : K →ₗ[A'] P) :
    finrank k (LinearMap.range (precomp k (Y := resFD φ Y)
      (FDMod.lin (resHom φ (show K ⟶ P from (FDMod.ofLin (f))))))) =
      finrank k (LinearMap.range (precomp k (Y := Y) f)) := by
  have h : LinearMap.range (precomp k (Y := resFD φ Y)
      (FDMod.lin (resHom φ (show K ⟶ P from (FDMod.ofLin (f)))))) =
      (LinearMap.range (precomp k (Y := Y) f)).map (homResEquiv hφ K Y).toLinearMap := by
    ext e
    constructor
    · rintro ⟨ψ, rfl⟩
      exact ⟨precomp k (Y := Y) f ((homResEquiv hφ P Y).symm ψ), ⟨_, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨ψ, rfl⟩, rfl⟩
      exact ⟨homResEquiv hφ P Y ψ, rfl⟩
  rw [h]
  exact LinearEquiv.finrank_map_eq (homResEquiv hφ K Y) _

end Res

/-- Point–brick data over `A`: a brick missing `x`, a one-dimensional module concentrated at `x`,
and a presentation of one of them with two independent classes of extensions by the other. -/
def PointBrickA (D : DirData k A) : Prop :=
  ∃ (x : D.ι) (V S K P : FDMod k A) (f : K →ₗ[A] P),
    (∀ φ : V ⟶ V, ∃ c : k, FDMod.lin φ = c • LinearMap.id) ∧ Nontrivial V ∧
    (∀ m : V, D.e x • m = 0) ∧ (∀ m : S, D.e x • m = m) ∧ finrank k S = 1 ∧
    Function.Injective f ∧
    ((∃ g : P →ₗ[A] V, Function.Surjective g ∧ LinearMap.range f = LinearMap.ker g ∧
        finrank k (LinearMap.range (precomp k (Y := S) f)) + 2 ≤ finrank k (K →ₗ[A] S)) ∨
      ∃ g : P →ₗ[A] S, Function.Surjective g ∧ LinearMap.range f = LinearMap.ker g ∧
        finrank k (LinearMap.range (precomp k (Y := V) f)) + 2 ≤ finrank k (K →ₗ[A] V))

/-- **Point–brick data on a quotient inflate.** -/
theorem pointBrickA_of_quot {T' : Set D.ι} (hT : T' ⊆ D.T)
    (h : PointBrickM (D.quotAny hT) (fun _ ↦ Set.mem_univ _)) : PointBrickA D := by
  obtain ⟨x, V, hb, hnt, hk, hext⟩ := h
  have hφ := D.qmap_surjective T'
  let φ := D.qmap T'
  let DB := D.quotAny hT
  have hxT : x ∈ DB.T := Set.mem_univ x
  let Sb := DB.simpleM x hxT
  have hbrick : ∀ f : resFD φ V ⟶ resFD φ V, ∃ c : k, FDMod.lin f = c • LinearMap.id := by
    intro f
    obtain ⟨c, hc⟩ := hb (unresHom hφ f)
    refine ⟨c, LinearMap.ext fun m ↦ ?_⟩
    exact LinearMap.congr_fun hc (toX m)
  have hV : ∀ m : resFD φ V, D.e x.1 • m = 0 := fun m ↦ hk (toX m)
  have hS : ∀ m : resFD φ Sb, D.e x.1 • m = m := fun m ↦ by
    change DB.chi x hxT (DB.e x) * (show k from m) = m
    rw [DB.chi_e_self x hxT, one_mul]
  have hS1 : finrank k (resFD φ Sb) = 1 := Module.finrank_self k
  rcases hext with h | h
  · refine ⟨x.1, resFD φ V, resFD φ Sb, resFD φ (syz DB V),
      resFD φ (sumProj DB ((coverList DB V).map Sigma.fst)),
      FDMod.lin (resHom φ (show syz DB V ⟶ _ from (FDMod.ofLin ((LinearMap.ker (sumMap DB V (coverList DB V))).subtype)))),
      hbrick, hnt, hV, hS, hS1, Subtype.val_injective, Or.inl
      ⟨FDMod.lin (resHom φ (show _ ⟶ V from (FDMod.ofLin (sumMap DB V (coverList DB V))))),
        sumMap_coverList_surjective DB V, ?_, ?_⟩⟩
    · ext p
      constructor
      · rintro ⟨q, rfl⟩
        exact q.2
      · intro hp
        exact ⟨⟨p, hp⟩, rfl⟩
    · rw [finrank_range_res hφ, (homResEquiv hφ (syz DB V) Sb).finrank_eq.symm]
      exact h
  · refine ⟨x.1, resFD φ V, resFD φ Sb, resFD φ (syz DB Sb),
      resFD φ (sumProj DB ((coverList DB Sb).map Sigma.fst)),
      FDMod.lin (resHom φ (show syz DB Sb ⟶ _ from (FDMod.ofLin ((LinearMap.ker (sumMap DB Sb (coverList DB Sb))).subtype)))),
      hbrick, hnt, hV, hS, hS1, Subtype.val_injective, Or.inr
      ⟨FDMod.lin (resHom φ (show _ ⟶ Sb from (FDMod.ofLin (sumMap DB Sb (coverList DB Sb))))),
        sumMap_coverList_surjective DB Sb, ?_, ?_⟩⟩
    · ext p
      constructor
      · rintro ⟨q, rfl⟩
        exact q.2
      · intro hp
        exact ⟨⟨p, hp⟩, rfl⟩
    · rw [finrank_range_res hφ, (homResEquiv hφ (syz DB Sb) V).finrank_eq.symm]
      exact h

/-- **Directed Schurian algebras with good projectives and unbounded indecomposables carry
point–brick data.** -/
theorem exists_pointBrickA [IsAlgClosed k] (hT : ∀ x, x ∈ D.T) (hsch : ∀ x y, cartan D y x ≤ 1)
    (hg : ∀ x, Good (projE (k := k) (D.idem x))) (hunb : D.Unb Set.univ) : PointBrickA D := by
  obtain ⟨T', hT', h⟩ := exists_pointBrick hT hsch hg hunb
  exact pointBrickA_of_quot hT' h

end DirData

end LargeIndecomposable.AR
