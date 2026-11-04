module

public import LargeIndecomposable.DirectedAlgebras.Preprojective.MinimalQuot
public import LargeIndecomposable.DirectedAlgebras.Preprojective.CriticalLine

/-!
# The minimal quotient with its support and line

`exists_pointBrick` with more output: the point–brick data live on the minimal set `T'`
(the brick vanishes outside `T'`, the point lies in `T'`; `PointBrickAIn`), and if `T'` has at
least `30` points, the Euler form of the quotient gives a line (`exists_critical_line`). This is
`exists_pointBrick_line`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

namespace DirData

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  {D : DirData k A}

variable (D) in
/-- Point–brick data over `A` living on `T'`. -/
def PointBrickAIn (T' : Set D.ι) : Prop :=
  ∃ (x : D.ι) (_ : x ∈ T') (V : FDMod k A) (_ : ∀ v, v ∉ T' → ∀ m : V, D.e v • m = 0)
    (S K P : FDMod k A) (f : K →ₗ[A] P),
    (∀ φ : V ⟶ V, ∃ c : k, FDMod.lin φ = c • LinearMap.id) ∧ Nontrivial V ∧
    (∀ m : V, D.e x • m = 0) ∧ (∀ m : S, D.e x • m = m) ∧ finrank k S = 1 ∧
    Function.Injective f ∧
    ((∃ g : P →ₗ[A] V, Function.Surjective g ∧ LinearMap.range f = LinearMap.ker g ∧
        finrank k (LinearMap.range (precomp k (Y := S) f)) + 2 ≤ finrank k (K →ₗ[A] S)) ∨
      ∃ g : P →ₗ[A] S, Function.Surjective g ∧ LinearMap.range f = LinearMap.ker g ∧
        finrank k (LinearMap.range (precomp k (Y := V) f)) + 2 ≤ finrank k (K →ₗ[A] V))

/-- **Point–brick data on a quotient inflate, living on `T'`.** -/
theorem pointBrickAIn_of_quot {T' : Set D.ι} (hT : T' ⊆ D.T)
    (h : PointBrickM (D.quotAny hT) (fun _ ↦ Set.mem_univ _)) : D.PointBrickAIn T' := by
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
  · refine ⟨x.1, x.2, resFD φ V, fun v hv m ↦ by
      change D.qmap T' (D.e v) • (show V from m) = 0
      rw [D.qmap_e_out T' hv, zero_smul], resFD φ Sb, resFD φ (syz DB V),
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
  · refine ⟨x.1, x.2, resFD φ V, fun v hv m ↦ by
      change D.qmap T' (D.e v) • (show V from m) = 0
      rw [D.qmap_e_out T' hv, zero_smul], resFD φ Sb, resFD φ (syz DB Sb),
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


/-- **The minimal quotient with its point–brick data and, for at least `30` points, a line.** -/
theorem exists_pointBrick_line [IsAlgClosed k] (hT : ∀ x, x ∈ D.T)
    (hsch : ∀ x y, cartan D y x ≤ 1)
    (hg : ∀ x, Good (projE (k := k) (D.idem x))) (hunb : D.Unb Set.univ)
    (hH : ∀ a b, D.Arr a b →
      (∀ v, Relation.ReflTransGen D.Arr a v → Relation.ReflTransGen D.Arr v b → v = a ∨ v = b) ∧
        (∃ c, D.e b * c * D.e a ≠ 0) ∧ cartan D b a ≤ 1) :
    ∃ (T' : Set D.ι), D.PointBrickAIn T' ∧ (T'.ncard ≤ 29 ∨
      ∃ (P : ℕ → D.ι) (V : FDMod k A),
        (∀ i, i < T'.ncard - 2 → P i ∈ T') ∧
        (∀ i j, i < T'.ncard - 2 → j < T'.ncard - 2 → P i = P j → i = j) ∧
        (∀ i, i + 1 < T'.ncard - 2 → D.Arr (P i) (P (i + 1)) ∨ D.Arr (P (i + 1)) (P i)) ∧
        (∀ i j, j < T'.ncard - 2 → i + 2 ≤ j → ¬D.Arr (P i) (P j) ∧ ¬D.Arr (P j) (P i)) ∧
        IsIndecMod A V ∧
        (∀ x, (∀ i, i < T'.ncard - 2 → P i ≠ x) → ∀ v : V, D.e x • v = 0) ∧
        (∀ i, i < T'.ncard - 2 → finrank k (eSub V (D.e (P i))) = 1) ∧
        (∀ i, i + 1 < T'.ncard - 2 → ∃ (c : A) (v : V),
          (D.e (P (i + 1)) * c * D.e (P i)) • v ≠ 0 ∨ (D.e (P i) * c * D.e (P (i + 1))) • v ≠ 0)) := by
  classical
  have hex : ∃ n, ∃ T' : Set D.ι, T'.ncard = n ∧ D.Unb T' := ⟨_, _, rfl, hunb⟩
  obtain ⟨T', hn, hU⟩ := Nat.find_spec hex
  have hmin : ∀ T'' : Set D.ι, T''.ncard < T'.ncard → ¬D.Unb T'' := fun T'' hlt hu ↦
    Nat.find_min hex (hn ▸ hlt) ⟨T'', rfl, hu⟩
  have hsub : T' ⊆ D.T := fun x _ ↦ hT x
  have hTB : ∀ x, x ∈ (D.quotAny hsub).T := fun _ ↦ Set.mem_univ _
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
  refine ⟨T', pointBrickAIn_of_quot hsub (pointBrickM hTB hcard hR hc h𝒞 hun), ?_⟩
  have hcardT : Fintype.card DB.ι = T'.ncard := by
    rw [Fintype.card_eq_nat_card]
    exact Nat.card_coe_set_eq T'
  by_cases h30 : T'.ncard ≤ 29
  · exact Or.inl h30
  right
  obtain ⟨U, hU', hs, -⟩ := hc 0
  have h10 : 10 ≤ Fintype.card DB.ι := by omega
  have := exists_critical_line hsub hT hH hU' hs hR hcrit h10
  rw [hcardT] at this
  exact this

end DirData

end LargeIndecomposable.AR
