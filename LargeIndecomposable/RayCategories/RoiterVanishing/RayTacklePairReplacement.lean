module

public import LargeIndecomposable.RayCategories.RoiterVanishing.RayTackleExtension
public import Mathlib.Data.Fin.Tuple.Take

@[expose] public section

/-!
# Replacing the last pair of a ray tackle

Package the alternating same-length candidates in BGRS Figure 55.  One
candidate retains a hook tackle through its penultimate `rho`, deepens the
following `sigma`, and installs a new irreducible hook.  The dual candidate
retains a cohook tackle through its penultimate `sigma`, deepens the following
`rho`, and installs a new irreducible cohook.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace NonzeroHom

/-- Bundle a nonzero precomposition by a ray path. -/
def precompRayPath {X Y : C} (f : NonzeroHom X Y)
    {W : RayVertex C} (p : Quiver.Path (RayVertex.mk X) W)
    (hcomp : rayPathMap p ≫ f.1 ≠ 0) : NonzeroHom W.obj Y :=
  ⟨rayPathMap p ≫ f.1, hcomp⟩

/-- Bundle a nonzero postcomposition by a ray path. -/
def postcompRayPath {X Y : C} (f : NonzeroHom X Y)
    {W : RayVertex C} (p : Quiver.Path W (RayVertex.mk Y))
    (hcomp : f.1 ≫ rayPathMap p ≠ 0) : NonzeroHom X W.obj :=
  ⟨f.1 ≫ rayPathMap p, hcomp⟩

/-- Precomposing a nonzero ray morphism by a nonidentity irreducible path
strictly increases its depth, provided the composite remains nonzero. -/
theorem depth_lt_precompRayPath
    [HasFiniteRayPathDepth C]
    {X Y : C} (f : NonzeroHom X Y)
    {W : RayVertex C} (p : Quiver.Path (RayVertex.mk X) W)
    (hcomp : rayPathMap p ≫ f.1 ≠ 0) (hp : p.length ≠ 0) :
    f.depth < (f.precompRayPath p hcomp).depth := by
  let F : NonzeroHom W.obj Y := f.precompRayPath p hcomp
  obtain ⟨q, hq⟩ :=
    exists_rayPathPresentation_length_eq_depth f.toMorphismFrom
  let r : RayPathPresentation F.toMorphismFrom :=
    { path := q.path.comp p
      map_eq := by
        calc
          rayPathMap (q.path.comp p) =
              rayPathMap p ≫ rayPathMap q.path := by
            exact LinearPathCategory.pathMap_comp
              RayVertex.obj rayArrowMorphism q.path p
          _ = rayPathMap p ≫ f.1 := by rw [q.map_eq]
          _ = F.toMorphismFrom.hom := rfl }
  have hr := r.length_le_depth
  change r.path.length ≤ F.depth at hr
  dsimp only [r] at hr
  simp only [Quiver.Path.length_comp] at hr
  change q.path.length = f.depth at hq
  change f.depth < F.depth
  omega

/-- Postcomposing a nonzero ray morphism by a nonidentity irreducible path
strictly increases its depth, provided the composite remains nonzero. -/
theorem depth_lt_postcompRayPath
    [HasFiniteRayPathDepth C]
    {X Y : C} (f : NonzeroHom X Y)
    {W : RayVertex C} (p : Quiver.Path W (RayVertex.mk Y))
    (hcomp : f.1 ≫ rayPathMap p ≠ 0) (hp : p.length ≠ 0) :
    f.depth < (f.postcompRayPath p hcomp).depth := by
  let F : NonzeroHom X W.obj := f.postcompRayPath p hcomp
  obtain ⟨q, hq⟩ :=
    exists_rayPathPresentation_length_eq_depth f.toMorphismFrom
  let r : RayPathPresentation F.toMorphismFrom :=
    { path := p.comp q.path
      map_eq := by
        calc
          rayPathMap (p.comp q.path) =
              rayPathMap q.path ≫ rayPathMap p := by
            exact LinearPathCategory.pathMap_comp
              RayVertex.obj rayArrowMorphism p q.path
          _ = f.1 ≫ rayPathMap p := by rw [q.map_eq]
          _ = F.toMorphismFrom.hom := rfl }
  have hr := r.length_le_depth
  change r.path.length ≤ F.depth at hr
  dsimp only [r] at hr
  simp only [Quiver.Path.length_comp] at hr
  change q.path.length = f.depth at hq
  change f.depth < F.depth
  omega

end NonzeroHom

/-- Alternating equally long prefixes commutes with appending arbitrary
tails. -/
theorem alternateLists_append_of_length_eq {α : Type*}
    (xs ys as bs : List α) (h : xs.length = ys.length) :
    alternateLists (xs ++ as) (ys ++ bs) =
      alternateLists xs ys ++ alternateLists as bs := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => simp [alternateLists]
      | cons y ys => simp at h
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at h
          simpa [alternateLists] using
            congrArg (fun zs ↦ x :: y :: zs) (ih ys h)

/-- Alternating preserves simultaneous list prefixes of equal length. -/
theorem alternateLists_isPrefix_of_isPrefix_of_length_eq {α : Type*}
    {xs ys xs' ys' : List α}
    (hxy : xs.length = ys.length)
    (hx : xs <+: xs') (hy : ys <+: ys') :
    alternateLists xs ys <+: alternateLists xs' ys' := by
  obtain ⟨as, rfl⟩ := hx
  obtain ⟨bs, rfl⟩ := hy
  rw [alternateLists_append_of_length_eq xs ys as bs hxy]
  exact List.prefix_append _ _

namespace RayHookChain

/-- The depth word of a hook chain, without requiring its final `rho` to be
irreducible. -/
def efficiency [HasFiniteRayPathDepth C] {m : ℕ}
    (c : RayHookChain (C := C) m) : List ℕ :=
  alternateLists
    (List.ofFn fun i ↦ (c.rho i).depth)
    (List.ofFn fun i ↦ (c.sigma i).depth)

/-- Cut a hook tackle immediately after `rho_n`, retaining precisely the
alternating prefix before `sigma_n`. -/
def prefixAt {m n : ℕ} (t : RayHookTackle (C := C) m)
    (h : n < m) : RayHookChain (C := C) n where
  x := Fin.take (n + 1) (by omega) t.x
  z := Fin.take (n + 1) (by omega) t.z
  rho := Fin.take (n + 1) (by omega) t.rho
  sigma := Fin.take n (Nat.le_of_lt h) t.sigma
  peak_incomparable := fun i ↦ by
    simp only [Fin.take]
    let j : Fin m := i.castLE (Nat.le_of_lt h)
    have hr : j.castSucc = i.castSucc.castLE (by omega) := by
      apply Fin.ext
      rfl
    have hs : j.succ = i.succ.castLE (by omega) := by
      apply Fin.ext
      rfl
    cases hr
    cases hs
    exact t.peak_incomparable j
  valley_incomparable := fun i ↦ by
    simp only [Fin.take]
    let j : Fin m := i.castLE (Nat.le_of_lt h)
    have hr : j.castSucc = i.castSucc.castLE (by omega) := by
      apply Fin.ext
      rfl
    have hs : j.succ = i.succ.castLE (by omega) := by
      apply Fin.ext
      rfl
    cases hr
    cases hs
    exact t.valley_incomparable j

/-- Append a new final `sigma,rho` pair to a hook chain.  The appended `rho`
is irreducible, so the result is a hook tackle. -/
def appendSigmaHook {n : ℕ} (c : RayHookChain (C := C) n)
    {X Z : C}
    (f : NonzeroHom X (c.z (Fin.last n)))
    (g : NonzeroHom X Z)
    (hpeak : RayTargetIncomparable (c.rho (Fin.last n)) f)
    (hvalley : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    RayHookTackle (C := C) (n + 1) := by
  let x' : Fin (n + 2) → C := Fin.lastCases X c.x
  let z' : Fin (n + 2) → C := Fin.lastCases Z c.z
  have hxCastSucc (i : Fin (n + 1)) : x' i.castSucc = c.x i := by
    simp [x']
  have hzCastSucc (i : Fin (n + 1)) : z' i.castSucc = c.z i := by
    simp [z']
  have hxPrevious (i : Fin n) :
      x' i.castSucc.succ = c.x i.succ := by
    rw [Fin.succ_castSucc]
    exact hxCastSucc i.succ
  have hxLast : x' (Fin.last (n + 1)) = X := by
    simp [x']
  have hzLast : z' (Fin.last (n + 1)) = Z := by
    simp [z']
  let rho' : ∀ i : Fin (n + 2), NonzeroHom (x' i) (z' i) :=
    Fin.lastCases
      (g.cast hxLast.symm hzLast.symm)
      (fun i : Fin (n + 1) ↦
        (c.rho i).cast (hxCastSucc i).symm (hzCastSucc i).symm)
  let sigma' : ∀ i : Fin (n + 1),
      NonzeroHom (x' i.succ) (z' i.castSucc) :=
    Fin.lastCases
      (f.cast hxLast.symm (hzCastSucc (Fin.last n)).symm)
      (fun i : Fin n ↦
        (c.sigma i).cast
          (hxPrevious i).symm (hzCastSucc i.castSucc).symm)
  exact
    { x := x'
      z := z'
      rho := rho'
      sigma := sigma'
      peak_incomparable := Fin.lastCases
        (by
          simp only [rho', sigma', Fin.lastCases_castSucc,
            Fin.lastCases_last]
          exact hpeak.cast
            (hxCastSucc (Fin.last n)).symm hxLast.symm
            (hzCastSucc (Fin.last n)).symm)
        (fun i : Fin n ↦ by
          simp only [rho', sigma', Fin.lastCases_castSucc]
          exact (c.peak_incomparable i).cast
            (hxCastSucc i.castSucc).symm (hxPrevious i).symm
            (hzCastSucc i.castSucc).symm)
      valley_incomparable := Fin.lastCases
        (by
          simp only [rho', sigma', Fin.lastCases_last, Fin.succ_last]
          exact hvalley.cast hxLast.symm
            (hzCastSucc (Fin.last n)).symm hzLast.symm)
        (fun i : Fin n ↦ by
          have hzNext : c.z i.succ = z' i.castSucc.succ := by
            simpa [Fin.castSucc_succ] using
              (hzCastSucc i.succ).symm
          simp only [rho', sigma', Fin.lastCases_castSucc,
            Fin.succ_castSucc]
          exact (c.valley_incomparable i).cast
            (hxPrevious i).symm
            (hzCastSucc i.castSucc).symm hzNext)
      last_irreducible := by
        simp only [rho', Fin.lastCases_last]
        exact isIrreducibleMorphism_cast hxLast.symm hzLast.symm g hg }

@[simp]
theorem appendSigmaHook_x_zero {n : ℕ}
    (c : RayHookChain (C := C) n)
    {X Z : C}
    (f : NonzeroHom X (c.z (Fin.last n)))
    (g : NonzeroHom X Z)
    (hpeak : RayTargetIncomparable (c.rho (Fin.last n)) f)
    (hvalley : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    (c.appendSigmaHook f g hpeak hvalley hg).x 0 = c.x 0 := by
  change Fin.lastCases X c.x ((0 : Fin (n + 1)).castSucc) = c.x 0
  exact Fin.lastCases_castSucc 0

/-- Appending the Figure 55 pair adds precisely the two new depths to the
hook-chain word. -/
theorem efficiency_appendSigmaHook
    [HasFiniteRayPathDepth C] {n : ℕ}
    (c : RayHookChain (C := C) n)
    {X Z : C}
    (f : NonzeroHom X (c.z (Fin.last n)))
    (g : NonzeroHom X Z)
    (hpeak : RayTargetIncomparable (c.rho (Fin.last n)) f)
    (hvalley : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    (c.appendSigmaHook f g hpeak hvalley hg).efficiency =
      c.efficiency ++ [f.depth, g.depth] := by
  unfold RayHookTackle.efficiency efficiency
  rw [List.ofFn_succ'
    (fun i : Fin (n + 2) ↦
      ((c.appendSigmaHook f g hpeak hvalley hg).rho i).depth)]
  rw [List.ofFn_succ'
    (fun i : Fin (n + 1) ↦
      ((c.appendSigmaHook f g hpeak hvalley hg).sigma i).depth)]
  rw [alternateLists_concat_both_of_length_eq_succ _ _ _ _ (by simp)]
  congr 1 <;> simp [appendSigmaHook]

@[simp]
theorem prefixAt_x_zero {m n : ℕ}
    (t : RayHookTackle (C := C) m) (h : n < m) :
    (RayHookChain.prefixAt t h).x 0 = t.x 0 := by
  simp [prefixAt, Fin.take]

/-- The first `sigma` omitted by a hook-chain cutoff, transported to the
cutoff chain's last target. -/
def cutoffSigma {m n : ℕ} (t : RayHookTackle (C := C) m)
    (h : n < m) :
    NonzeroHom (t.x ((Fin.last n).castLE h).succ)
      ((RayHookChain.prefixAt t h).z (Fin.last n)) := by
  let i : Fin m := (Fin.last n).castLE h
  have hz : t.z i.castSucc =
      (RayHookChain.prefixAt t h).z (Fin.last n) := by
    simp only [RayHookChain.prefixAt, Fin.take, i]
    congr 1
  exact (t.sigma i).cast rfl hz

@[simp]
theorem cutoffSigma_depth [HasFiniteRayPathDepth C]
    {m n : ℕ} (t : RayHookTackle (C := C) m) (h : n < m) :
    (RayHookChain.cutoffSigma t h).depth =
      (t.sigma ((Fin.last n).castLE h)).depth := by
  simp [cutoffSigma]
  rfl

@[simp]
theorem cutoffSigma_depth_explicit [HasFiniteRayPathDepth C]
    {m n : ℕ} (t : RayHookTackle (C := C) m) (h : n < m) :
    (RayHookChain.cutoffSigma t h).depth =
      (t.sigma (⟨n, h⟩ : Fin m)).depth := by
  rw [RayHookChain.cutoffSigma_depth]
  have hi : (Fin.last n).castLE h = (⟨n, h⟩ : Fin m) := by
    apply Fin.ext
    rfl
  rw [hi]

/-- The last `rho` of the cutoff chain remains peak-incomparable with the
first omitted `sigma`. -/
theorem cutoff_peak_incomparable {m n : ℕ}
    (t : RayHookTackle (C := C) m) (h : n < m) :
    RayTargetIncomparable
      ((RayHookChain.prefixAt t h).rho (Fin.last n))
      (RayHookChain.cutoffSigma t h) := by
  simpa [RayHookChain.prefixAt, RayHookChain.cutoffSigma,
    NonzeroHom.cast, Fin.take] using
      t.peak_incomparable ((Fin.last n).castLE h)

/-- The cutoff-chain efficiency followed by the omitted `sigma_n` is a
prefix of the original tackle's efficiency word. -/
theorem efficiency_append_cutoffSigma_isPrefix
    [HasFiniteRayPathDepth C] {m n : ℕ}
    (t : RayHookTackle (C := C) m) (h : n < m) :
    (RayHookChain.prefixAt t h).efficiency ++
        [(t.sigma (⟨n, h⟩ : Fin m)).depth] <+:
      t.efficiency := by
  let c := RayHookChain.prefixAt t h
  let rs : List ℕ := List.ofFn fun i ↦ (t.rho i).depth
  let ss : List ℕ := List.ofFn fun i ↦ (t.sigma i).depth
  let crs : List ℕ := List.ofFn fun i ↦ (c.rho i).depth
  let css : List ℕ := List.ofFn fun i ↦ (c.sigma i).depth
  have hcrs : crs = rs.take (n + 1) := by
    change List.ofFn
      (Fin.take (n + 1) (by omega)
        (fun i : Fin (m + 1) ↦ (t.rho i).depth)) =
      (List.ofFn fun i : Fin (m + 1) ↦ (t.rho i).depth).take (n + 1)
    exact Fin.ofFn_take_eq_take_ofFn (n := m + 1) (m := n + 1)
      (by omega) (fun i : Fin (m + 1) ↦ (t.rho i).depth)
  have hcss : css = ss.take n := by
    change List.ofFn
      (Fin.take n (Nat.le_of_lt h)
        (fun i : Fin m ↦ (t.sigma i).depth)) =
      (List.ofFn fun i : Fin m ↦ (t.sigma i).depth).take n
    exact Fin.ofFn_take_eq_take_ofFn (n := m) (m := n)
      (Nat.le_of_lt h) (fun i : Fin m ↦ (t.sigma i).depth)
  have hrPrefix : crs <+: rs := by
    rw [hcrs]
    exact List.take_prefix _ _
  have hsTake : css.concat (t.sigma (⟨n, h⟩ : Fin m)).depth =
      ss.take (n + 1) := by
    rw [hcss]
    rw [List.take_succ_eq_append_getElem (by simp [ss, h])]
    simp [ss]
  have hsPrefix : css.concat (t.sigma (⟨n, h⟩ : Fin m)).depth <+: ss := by
    rw [hsTake]
    exact List.take_prefix _ _
  change alternateLists crs css ++
      [(t.sigma (⟨n, h⟩ : Fin m)).depth] <+:
    alternateLists rs ss
  rw [← alternateLists_concat_right_of_length_eq_succ
    crs css (t.sigma (⟨n, h⟩ : Fin m)).depth (by simp [crs, css])]
  exact alternateLists_isPrefix_of_isPrefix_of_length_eq
    (by simp [crs, css]) hrPrefix hsPrefix

/-- At any cutoff, replacing `sigma_n` by a deeper morphism and appending an
irreducible hook produces a tackle strictly more efficient than the original
one, regardless of the discarded tail. -/
theorem efficiency_lex_appendSigmaHook_prefixAt
    [HasFiniteRayPathDepth C] {m n : ℕ}
    (t : RayHookTackle (C := C) m) (h : n < m)
    {X Z : C}
    (f : NonzeroHom X ((RayHookChain.prefixAt t h).z (Fin.last n)))
    (g : NonzeroHom X Z)
    (hpeak : RayTargetIncomparable
      ((RayHookChain.prefixAt t h).rho (Fin.last n)) f)
    (hvalley : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : (RayHookChain.cutoffSigma t h).depth < f.depth) :
    List.Lex (fun a b : ℕ ↦ a < b)
      t.efficiency
      ((RayHookChain.prefixAt t h).appendSigmaHook
        f g hpeak hvalley hg).efficiency := by
  obtain ⟨tail, htail⟩ :=
    RayHookChain.efficiency_append_cutoffSigma_isPrefix t h
  rw [← htail]
  rw [(RayHookChain.prefixAt t h).efficiency_appendSigmaHook
    f g hpeak hvalley hg]
  have hfdepth' : (t.sigma (⟨n, h⟩ : Fin m)).depth < f.depth := by
    rw [← RayHookChain.cutoffSigma_depth_explicit t h]
    exact hfdepth
  have hlex : List.Lex (fun a b : ℕ ↦ a < b)
      ((t.sigma (⟨n, h⟩ : Fin m)).depth :: tail)
      [f.depth, g.depth] :=
    List.Lex.rel hfdepth'
  simpa [List.append_assoc] using
    List.Lex.append_left (fun a b : ℕ ↦ a < b)
      hlex (RayHookChain.prefixAt t h).efficiency

/-- The arbitrary-cutoff hook propagation step.  Against an efficient
original tackle, a deeper replacement for the first omitted `sigma` which is
source-incomparable with a proposed new hook must factor through the cutoff
chain's last `rho`. -/
theorem exists_factorThroughCutoffRho_of_isEfficientAt
    [HasFiniteRayPathDepth C] {m n : ℕ}
    (t : RayHookTackle (C := C) m) (hcut : n < m) {y X Z : C}
    (ht : (RayTackle.hook m t).IsEfficientAt y)
    (f : NonzeroHom X
      ((RayHookChain.prefixAt t hcut).z (Fin.last n)))
    (g : NonzeroHom X Z)
    (a : X ⟶ t.x ((Fin.last n).castLE hcut).succ)
    (hfactor : a ≫ (RayHookChain.cutoffSigma t hcut).1 = f.1)
    (hvalley : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : (RayHookChain.cutoffSigma t hcut).depth < f.depth) :
    ∃ q : X ⟶ (RayHookChain.prefixAt t hcut).x (Fin.last n),
      q ≠ 0 ∧ q ≫
        ((RayHookChain.prefixAt t hcut).rho (Fin.last n)).1 = f.1 := by
  let c := RayHookChain.prefixAt t hcut
  have hnot : ¬RayTargetIncomparable (c.rho (Fin.last n)) f := by
    intro hpeak
    apply ht.2 (RayTackle.hook (n + 1)
      (c.appendSigmaHook f g hpeak hvalley hg))
    · change (c.appendSigmaHook f g hpeak hvalley hg).x 0 = y
      exact (c.appendSigmaHook_x_zero
        f g hpeak hvalley hg).trans
          ((RayHookChain.prefixAt_x_zero t hcut).trans ht.1)
    · simpa only [RayTackle.efficiency, c] using
        RayHookChain.efficiency_lex_appendSigmaHook_prefixAt
          t hcut f g hpeak hvalley hg hfdepth
  by_cases hfr : ∃ q : X ⟶ c.x (Fin.last n),
      q ≫ (c.rho (Fin.last n)).1 = f.1
  · obtain ⟨q, hq⟩ := hfr
    refine ⟨q, ?_, hq⟩
    rintro rfl
    apply f.2
    have hfzero : f.1 = 0 := by
      simpa only [zero_comp] using hq.symm
    exact hfzero
  · have hrf : ∃ q : c.x (Fin.last n) ⟶ X,
        q ≫ f.1 = (c.rho (Fin.last n)).1 := by
      by_contra hrf
      exact hnot ⟨hrf, hfr⟩
    obtain ⟨q, hq⟩ := hrf
    exfalso
    apply (RayHookChain.cutoff_peak_incomparable t hcut).1
    refine ⟨q ≫ a, ?_⟩
    rw [Category.assoc, hfactor, hq]

/-- Cut a cohook tackle immediately after `rho_n`, viewing the retained
prefix as a hook chain.  This is the cross-orientation cutoff used by the
alternating Figure 55 walk in case 2 of BGRS 1.9. -/
def prefixOfCohookAt {m n : ℕ} (t : RayCohookTackle (C := C) m)
    (h : n < m) : RayHookChain (C := C) n where
  x := Fin.take (n + 1) (by omega) t.x
  z := Fin.take (n + 1) (by omega) t.z
  rho := Fin.take (n + 1) (by omega) t.rho
  sigma := Fin.take n (by omega) t.sigma
  peak_incomparable := fun i ↦ by
    simp only [Fin.take]
    let j : Fin (m + 1) := i.castLE (by omega)
    have hr : j = i.castSucc.castLE (by omega) := by
      apply Fin.ext
      rfl
    have hs : j = i.castLE (by omega) := by
      apply Fin.ext
      rfl
    cases hr
    cases hs
    exact t.peak_incomparable j
  valley_incomparable := fun i ↦ by
    simp only [Fin.take]
    let j : Fin m := i.castLE (Nat.le_of_lt h)
    have hs : j.castSucc = i.castLE (by omega) := by
      apply Fin.ext
      rfl
    have hr : j.succ = i.succ.castLE (by omega) := by
      apply Fin.ext
      rfl
    cases hs
    cases hr
    exact t.valley_incomparable j

@[simp]
theorem prefixOfCohookAt_x_zero {m n : ℕ}
    (t : RayCohookTackle (C := C) m) (h : n < m) :
    (RayHookChain.prefixOfCohookAt t h).x 0 = t.x 0 := by
  simp [prefixOfCohookAt, Fin.take]

/-- The first `sigma` omitted from the hook-shaped prefix of a cohook
tackle. -/
def cutoffSigmaOfCohook {m n : ℕ} (t : RayCohookTackle (C := C) m)
    (h : n < m) :
    NonzeroHom (t.x ((Fin.last n).castLE h).succ.castSucc)
      ((RayHookChain.prefixOfCohookAt t h).z (Fin.last n)) := by
  let i : Fin m := (Fin.last n).castLE h
  have hz : t.z i.castSucc =
      (RayHookChain.prefixOfCohookAt t h).z (Fin.last n) := by
    simp only [RayHookChain.prefixOfCohookAt, Fin.take, i]
    congr 1
  exact (t.sigma i.castSucc).cast rfl hz

@[simp]
theorem cutoffSigmaOfCohook_depth_index [HasFiniteRayPathDepth C]
    {m n : ℕ} (t : RayCohookTackle (C := C) m) (h : n < m) :
    (RayHookChain.cutoffSigmaOfCohook t h).depth =
      (t.sigma ((Fin.last n).castLE h).castSucc).depth := by
  simp [cutoffSigmaOfCohook]
  rfl

@[simp]
theorem cutoffSigmaOfCohook_depth [HasFiniteRayPathDepth C]
    {m n : ℕ} (t : RayCohookTackle (C := C) m) (h : n < m) :
    (RayHookChain.cutoffSigmaOfCohook t h).depth =
      (t.sigma (⟨n, by omega⟩ : Fin (m + 1))).depth := by
  rw [RayHookChain.cutoffSigmaOfCohook_depth_index]
  congr 2

/-- The retained `rho_n` remains peak-incomparable with the omitted
`sigma_n` in a cross-orientation cutoff. -/
theorem cutoffOfCohook_peak_incomparable {m n : ℕ}
    (t : RayCohookTackle (C := C) m) (h : n < m) :
    RayTargetIncomparable
      ((RayHookChain.prefixOfCohookAt t h).rho (Fin.last n))
      (RayHookChain.cutoffSigmaOfCohook t h) := by
  let i : Fin m := (Fin.last n).castLE h
  have hi : i.castSucc =
      (Fin.last n).castLE (by omega) := by
    apply Fin.ext
    rfl
  cases hi
  simpa [RayHookChain.prefixOfCohookAt,
    RayHookChain.cutoffSigmaOfCohook, NonzeroHom.cast, Fin.take, i] using
      t.peak_incomparable i.castSucc

/-- The cross-orientation prefix through `rho_n`, followed by the omitted
`sigma_n`, is a prefix of the original cohook tackle's efficiency word. -/
theorem efficiency_append_cutoffSigmaOfCohook_isPrefix
    [HasFiniteRayPathDepth C] {m n : ℕ}
    (t : RayCohookTackle (C := C) m) (h : n < m) :
    (RayHookChain.prefixOfCohookAt t h).efficiency ++
        [(t.sigma (⟨n, by omega⟩ : Fin (m + 1))).depth] <+:
      t.efficiency := by
  let c := RayHookChain.prefixOfCohookAt t h
  let rs : List ℕ := List.ofFn fun i ↦ (t.rho i).depth
  let ss : List ℕ := List.ofFn fun i ↦ (t.sigma i).depth
  let crs : List ℕ := List.ofFn fun i ↦ (c.rho i).depth
  let css : List ℕ := List.ofFn fun i ↦ (c.sigma i).depth
  have hcrs : crs = rs.take (n + 1) := by
    change List.ofFn
      (Fin.take (n + 1) (by omega)
        (fun i : Fin (m + 1) ↦ (t.rho i).depth)) =
      (List.ofFn fun i : Fin (m + 1) ↦ (t.rho i).depth).take (n + 1)
    exact Fin.ofFn_take_eq_take_ofFn (n := m + 1) (m := n + 1)
      (by omega) (fun i : Fin (m + 1) ↦ (t.rho i).depth)
  have hcss : css = ss.take n := by
    change List.ofFn
      (Fin.take n (by omega)
        (fun i : Fin (m + 1) ↦ (t.sigma i).depth)) =
      (List.ofFn fun i : Fin (m + 1) ↦ (t.sigma i).depth).take n
    exact Fin.ofFn_take_eq_take_ofFn (n := m + 1) (m := n)
      (by omega) (fun i : Fin (m + 1) ↦ (t.sigma i).depth)
  have hrPrefix : crs <+: rs := by
    rw [hcrs]
    exact List.take_prefix _ _
  have hsTake : css.concat
      (t.sigma (⟨n, by omega⟩ : Fin (m + 1))).depth =
      ss.take (n + 1) := by
    have hn : n < ss.length := by
      simp [ss]
      omega
    have hget : ss[n] =
        (t.sigma (⟨n, by omega⟩ : Fin (m + 1))).depth := by
      change (List.ofFn fun i : Fin (m + 1) ↦ (t.sigma i).depth)[n] =
        (t.sigma (⟨n, by omega⟩ : Fin (m + 1))).depth
      rw [List.getElem_ofFn]
    calc
      css.concat (t.sigma (⟨n, by omega⟩ : Fin (m + 1))).depth =
          ss.take n ++
            [(t.sigma (⟨n, by omega⟩ : Fin (m + 1))).depth] := by
        rw [List.concat_eq_append, hcss]
      _ = ss.take n ++ [ss[n]] := by rw [hget]
      _ = ss.take (n + 1) :=
        (List.take_succ_eq_append_getElem hn).symm
  have hsPrefix : css.concat
      (t.sigma (⟨n, by omega⟩ : Fin (m + 1))).depth <+: ss := by
    rw [hsTake]
    exact List.take_prefix _ _
  change alternateLists crs css ++
      [(t.sigma (⟨n, by omega⟩ : Fin (m + 1))).depth] <+:
    alternateLists rs ss
  rw [← alternateLists_concat_right_of_length_eq_succ crs css
    (t.sigma (⟨n, by omega⟩ : Fin (m + 1))).depth
      (by simp [crs, css])]
  exact alternateLists_isPrefix_of_isPrefix_of_length_eq
    (by simp [crs, css]) hrPrefix hsPrefix

/-- Replacing the omitted `sigma_n` by a deeper morphism and appending a
hook improves the original cohook tackle, even after discarding its tail. -/
theorem efficiency_lex_appendSigmaHook_prefixOfCohookAt
    [HasFiniteRayPathDepth C] {m n : ℕ}
    (t : RayCohookTackle (C := C) m) (h : n < m)
    {X Z : C}
    (f : NonzeroHom X
      ((RayHookChain.prefixOfCohookAt t h).z (Fin.last n)))
    (g : NonzeroHom X Z)
    (hpeak : RayTargetIncomparable
      ((RayHookChain.prefixOfCohookAt t h).rho (Fin.last n)) f)
    (hvalley : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : (RayHookChain.cutoffSigmaOfCohook t h).depth < f.depth) :
    List.Lex (fun a b : ℕ ↦ a < b) t.efficiency
      ((RayHookChain.prefixOfCohookAt t h).appendSigmaHook
        f g hpeak hvalley hg).efficiency := by
  obtain ⟨tail, htail⟩ :=
    RayHookChain.efficiency_append_cutoffSigmaOfCohook_isPrefix t h
  rw [← htail]
  rw [(RayHookChain.prefixOfCohookAt t h).efficiency_appendSigmaHook
    f g hpeak hvalley hg]
  have hfdepth' :
      (t.sigma (⟨n, by omega⟩ : Fin (m + 1))).depth < f.depth := by
    rw [← RayHookChain.cutoffSigmaOfCohook_depth t h]
    exact hfdepth
  have hlex : List.Lex (fun a b : ℕ ↦ a < b)
      ((t.sigma (⟨n, by omega⟩ : Fin (m + 1))).depth :: tail)
      [f.depth, g.depth] := List.Lex.rel hfdepth'
  simpa [List.append_assoc] using
    List.Lex.append_left (fun a b : ℕ ↦ a < b)
      hlex (RayHookChain.prefixOfCohookAt t h).efficiency

/-- Cross-orientation Figure 55 propagation inside one efficient cohook
tackle: the deeper replacement for `sigma_n` must factor through the
retained `rho_n`. -/
theorem exists_factorThroughCutoffRho_of_cohook_isEfficientAt
    [HasFiniteRayPathDepth C] {m n : ℕ}
    (t : RayCohookTackle (C := C) m) (hcut : n < m) {y X Z : C}
    (ht : (RayTackle.cohook m t).IsEfficientAt y)
    (f : NonzeroHom X
      ((RayHookChain.prefixOfCohookAt t hcut).z (Fin.last n)))
    (g : NonzeroHom X Z)
    (a : X ⟶ t.x ((Fin.last n).castLE hcut).succ.castSucc)
    (hfactor : a ≫ (RayHookChain.cutoffSigmaOfCohook t hcut).1 = f.1)
    (hvalley : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : (RayHookChain.cutoffSigmaOfCohook t hcut).depth < f.depth) :
    ∃ q : X ⟶ (RayHookChain.prefixOfCohookAt t hcut).x (Fin.last n),
      q ≠ 0 ∧
        q ≫ ((RayHookChain.prefixOfCohookAt t hcut).rho (Fin.last n)).1 =
          f.1 := by
  let c := RayHookChain.prefixOfCohookAt t hcut
  have hnot : ¬RayTargetIncomparable (c.rho (Fin.last n)) f := by
    intro hpeak
    apply ht.2 (RayTackle.hook (n + 1)
      (c.appendSigmaHook f g hpeak hvalley hg))
    · change (c.appendSigmaHook f g hpeak hvalley hg).x 0 = y
      exact (c.appendSigmaHook_x_zero f g hpeak hvalley hg).trans
        ((RayHookChain.prefixOfCohookAt_x_zero t hcut).trans ht.1)
    · simpa only [RayTackle.efficiency, c] using
        RayHookChain.efficiency_lex_appendSigmaHook_prefixOfCohookAt
          t hcut f g hpeak hvalley hg hfdepth
  by_cases hfr : ∃ q : X ⟶ c.x (Fin.last n),
      q ≫ (c.rho (Fin.last n)).1 = f.1
  · obtain ⟨q, hq⟩ := hfr
    refine ⟨q, ?_, hq⟩
    rintro rfl
    apply f.2
    simpa only [zero_comp] using hq.symm
  · have hrf : ∃ q : c.x (Fin.last n) ⟶ X,
        q ≫ f.1 = (c.rho (Fin.last n)).1 := by
      by_contra hrf
      exact hnot ⟨hrf, hfr⟩
    obtain ⟨q, hq⟩ := hrf
    exfalso
    apply (RayHookChain.cutoffOfCohook_peak_incomparable t hcut).1
    refine ⟨q ≫ a, ?_⟩
    rw [Category.assoc, hfactor, hq]

end RayHookChain

namespace RayCohookChain

/-- The depth word of a cohook chain, without requiring its final `sigma` to
be irreducible. -/
def efficiency [HasFiniteRayPathDepth C] {m : ℕ}
    (c : RayCohookChain (C := C) m) : List ℕ :=
  alternateLists
    (List.ofFn fun i ↦ (c.rho i).depth)
    (List.ofFn fun i ↦ (c.sigma i).depth)

/-- Cut a cohook tackle immediately after `sigma_n`, retaining precisely the
alternating prefix before `rho_(n+1)`. -/
def prefixAt {m n : ℕ} (t : RayCohookTackle (C := C) m)
    (h : n < m) : RayCohookChain (C := C) n where
  x := Fin.take (n + 2) (by omega) t.x
  z := Fin.take (n + 1) (by omega) t.z
  rho := Fin.take (n + 1) (by omega) t.rho
  sigma := Fin.take (n + 1) (by omega) t.sigma
  peak_incomparable := fun i ↦ by
    simp only [Fin.take]
    let j : Fin (m + 1) := i.castLE (by omega)
    have hr : j.castSucc = i.castSucc.castLE (by omega) := by
      apply Fin.ext
      rfl
    have hs : j.succ = i.succ.castLE (by omega) := by
      apply Fin.ext
      rfl
    cases hr
    cases hs
    exact t.peak_incomparable j
  valley_incomparable := fun i ↦ by
    simp only [Fin.take]
    let j : Fin m := i.castLE (Nat.le_of_lt h)
    have hs : j.castSucc = i.castSucc.castLE (by omega) := by
      apply Fin.ext
      rfl
    have hr : j.succ = i.succ.castLE (by omega) := by
      apply Fin.ext
      rfl
    cases hs
    cases hr
    exact t.valley_incomparable j

/-- Append a new final `rho,sigma` pair to a cohook chain.  The appended
`sigma` is irreducible, so the result is a cohook tackle. -/
def appendRhoCohook {n : ℕ} (c : RayCohookChain (C := C) n)
    {X Z : C}
    (f : NonzeroHom (c.x (Fin.last (n + 1))) Z)
    (g : NonzeroHom X Z)
    (hvalley : RaySourceIncomparable (c.sigma (Fin.last n)) f)
    (hpeak : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    RayCohookTackle (C := C) (n + 1) := by
  let x' : Fin (n + 3) → C := Fin.lastCases X c.x
  let z' : Fin (n + 2) → C := Fin.lastCases Z c.z
  have hxCastSucc (i : Fin (n + 2)) : x' i.castSucc = c.x i := by
    simp [x']
  have hzCastSucc (i : Fin (n + 1)) : z' i.castSucc = c.z i := by
    simp [z']
  have hxPrevious (i : Fin (n + 1)) :
      x' i.castSucc.succ = c.x i.succ := by
    rw [Fin.succ_castSucc]
    exact hxCastSucc i.succ
  have hxLast : x' (Fin.last (n + 2)) = X := by
    simp [x']
  have hzLast : z' (Fin.last (n + 1)) = Z := by
    simp [z']
  let rho' : ∀ i : Fin (n + 2),
      NonzeroHom (x' i.castSucc) (z' i) :=
    Fin.lastCases
      (f.cast (hxCastSucc (Fin.last (n + 1))).symm hzLast.symm)
      (fun i : Fin (n + 1) ↦
        (c.rho i).cast
          (hxCastSucc i.castSucc).symm (hzCastSucc i).symm)
  let sigma' : ∀ i : Fin (n + 2),
      NonzeroHom (x' i.succ) (z' i) :=
    Fin.lastCases
      (g.cast hxLast.symm hzLast.symm)
      (fun i : Fin (n + 1) ↦
        (c.sigma i).cast
          (hxPrevious i).symm (hzCastSucc i).symm)
  exact
    { x := x'
      z := z'
      rho := rho'
      sigma := sigma'
      peak_incomparable := Fin.lastCases
        (by
          simp only [rho', sigma', Fin.lastCases_last]
          exact hpeak.cast
            (hxCastSucc (Fin.last (n + 1))).symm hxLast.symm
            hzLast.symm)
        (fun i : Fin (n + 1) ↦ by
          simp only [rho', sigma', Fin.lastCases_castSucc]
          exact (c.peak_incomparable i).cast
            (hxCastSucc i.castSucc).symm (hxPrevious i).symm
            (hzCastSucc i).symm)
      valley_incomparable := Fin.lastCases
        (by
          simp only [rho', sigma', Fin.lastCases_castSucc,
            Fin.lastCases_last, Fin.succ_last]
          exact hvalley.cast
            (hxPrevious (Fin.last n)).symm
            (hzCastSucc (Fin.last n)).symm hzLast.symm)
        (fun i : Fin n ↦ by
          have hzNext : c.z i.succ = z' i.castSucc.succ := by
            simpa [Fin.castSucc_succ] using
              (hzCastSucc i.succ).symm
          simp only [rho', sigma', Fin.lastCases_castSucc,
            Fin.succ_castSucc]
          exact (c.valley_incomparable i).cast
            (hxPrevious i.castSucc).symm
            (hzCastSucc i.castSucc).symm hzNext)
      last_irreducible := by
        simp only [sigma', Fin.lastCases_last]
        exact isIrreducibleMorphism_cast hxLast.symm hzLast.symm g hg }

@[simp]
theorem appendRhoCohook_x_zero {n : ℕ}
    (c : RayCohookChain (C := C) n)
    {X Z : C}
    (f : NonzeroHom (c.x (Fin.last (n + 1))) Z)
    (g : NonzeroHom X Z)
    (hvalley : RaySourceIncomparable (c.sigma (Fin.last n)) f)
    (hpeak : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    (c.appendRhoCohook f g hvalley hpeak hg).x 0 = c.x 0 := by
  change Fin.lastCases X c.x ((0 : Fin (n + 2)).castSucc) = c.x 0
  exact Fin.lastCases_castSucc 0

/-- Appending the dual Figure 55 pair adds precisely the two new depths to
the cohook-chain word. -/
theorem efficiency_appendRhoCohook
    [HasFiniteRayPathDepth C] {n : ℕ}
    (c : RayCohookChain (C := C) n)
    {X Z : C}
    (f : NonzeroHom (c.x (Fin.last (n + 1))) Z)
    (g : NonzeroHom X Z)
    (hvalley : RaySourceIncomparable (c.sigma (Fin.last n)) f)
    (hpeak : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    (c.appendRhoCohook f g hvalley hpeak hg).efficiency =
      c.efficiency ++ [f.depth, g.depth] := by
  unfold RayCohookTackle.efficiency efficiency
  rw [List.ofFn_succ'
    (fun i : Fin (n + 2) ↦
      ((c.appendRhoCohook f g hvalley hpeak hg).rho i).depth)]
  rw [List.ofFn_succ'
    (fun i : Fin (n + 2) ↦
      ((c.appendRhoCohook f g hvalley hpeak hg).sigma i).depth)]
  rw [alternateLists_concat_both_of_length_eq _ _ _ _ (by simp)]
  congr 1 <;> simp [appendRhoCohook]

@[simp]
theorem prefixAt_x_zero {m n : ℕ}
    (t : RayCohookTackle (C := C) m) (h : n < m) :
    (RayCohookChain.prefixAt t h).x 0 = t.x 0 := by
  simp [prefixAt, Fin.take]

/-- The first `rho` omitted by a cohook-chain cutoff, transported from the
cutoff chain's last source. -/
def cutoffRho {m n : ℕ} (t : RayCohookTackle (C := C) m)
    (h : n < m) :
    NonzeroHom ((RayCohookChain.prefixAt t h).x (Fin.last (n + 1)))
      (t.z ((Fin.last n).castLE h).succ) := by
  let i : Fin m := (Fin.last n).castLE h
  have hx : t.x i.succ.castSucc =
      (RayCohookChain.prefixAt t h).x (Fin.last (n + 1)) := by
    simp only [RayCohookChain.prefixAt, Fin.take, i]
    congr 1
  exact (t.rho i.succ).cast hx rfl

@[simp]
theorem cutoffRho_depth [HasFiniteRayPathDepth C]
    {m n : ℕ} (t : RayCohookTackle (C := C) m) (h : n < m) :
    (RayCohookChain.cutoffRho t h).depth =
      (t.rho ((Fin.last n).castLE h).succ).depth := by
  simp [cutoffRho]

@[simp]
theorem cutoffRho_depth_explicit [HasFiniteRayPathDepth C]
    {m n : ℕ} (t : RayCohookTackle (C := C) m) (h : n < m) :
    (RayCohookChain.cutoffRho t h).depth =
      (t.rho (⟨n + 1, by omega⟩ : Fin (m + 1))).depth := by
  rw [RayCohookChain.cutoffRho_depth]
  have hi : ((Fin.last n).castLE h).succ =
      (⟨n + 1, by omega⟩ : Fin (m + 1)) := by
    apply Fin.ext
    rfl
  rw [hi]

/-- The last `sigma` of the cutoff chain remains valley-incomparable with the
first omitted `rho`. -/
theorem cutoff_valley_incomparable {m n : ℕ}
    (t : RayCohookTackle (C := C) m) (h : n < m) :
    RaySourceIncomparable
      ((RayCohookChain.prefixAt t h).sigma (Fin.last n))
      (RayCohookChain.cutoffRho t h) := by
  let i : Fin m := (Fin.last n).castLE h
  have hx : t.x i.castSucc.succ =
      t.x ((Fin.last (n + 1)).castLE (by omega)) := by
    congr 1
  simpa [RayCohookChain.prefixAt, RayCohookChain.cutoffRho,
    NonzeroHom.cast, Fin.take, i] using
      (t.valley_incomparable i).cast hx rfl rfl

/-- The cutoff-chain efficiency followed by the omitted `rho_(n+1)` is a
prefix of the original cohook tackle's efficiency word. -/
theorem efficiency_append_cutoffRho_isPrefix
    [HasFiniteRayPathDepth C] {m n : ℕ}
    (t : RayCohookTackle (C := C) m) (h : n < m) :
    (RayCohookChain.prefixAt t h).efficiency ++
        [(t.rho (⟨n + 1, by omega⟩ : Fin (m + 1))).depth] <+:
      t.efficiency := by
  let c := RayCohookChain.prefixAt t h
  let rs : List ℕ := List.ofFn fun i ↦ (t.rho i).depth
  let ss : List ℕ := List.ofFn fun i ↦ (t.sigma i).depth
  let crs : List ℕ := List.ofFn fun i ↦ (c.rho i).depth
  let css : List ℕ := List.ofFn fun i ↦ (c.sigma i).depth
  have hcrs : crs = rs.take (n + 1) := by
    change List.ofFn
      (Fin.take (n + 1) (by omega)
        (fun i : Fin (m + 1) ↦ (t.rho i).depth)) =
      (List.ofFn fun i : Fin (m + 1) ↦ (t.rho i).depth).take (n + 1)
    exact Fin.ofFn_take_eq_take_ofFn (n := m + 1) (m := n + 1)
      (by omega) (fun i : Fin (m + 1) ↦ (t.rho i).depth)
  have hcss : css = ss.take (n + 1) := by
    change List.ofFn
      (Fin.take (n + 1) (by omega)
        (fun i : Fin (m + 1) ↦ (t.sigma i).depth)) =
      (List.ofFn fun i : Fin (m + 1) ↦ (t.sigma i).depth).take (n + 1)
    exact Fin.ofFn_take_eq_take_ofFn (n := m + 1) (m := n + 1)
      (by omega) (fun i : Fin (m + 1) ↦ (t.sigma i).depth)
  have hrTake : crs.concat
        (t.rho (⟨n + 1, by omega⟩ : Fin (m + 1))).depth =
      rs.take (n + 2) := by
    rw [hcrs]
    conv_rhs =>
      rw [List.take_succ_eq_append_getElem (by simp [rs]; omega)]
    simp [rs]
  have hrPrefix : crs.concat
        (t.rho (⟨n + 1, by omega⟩ : Fin (m + 1))).depth <+: rs := by
    rw [hrTake]
    exact List.take_prefix _ _
  have hsPrefix : css <+: ss := by
    rw [hcss]
    exact List.take_prefix _ _
  obtain ⟨rtail, hrtail⟩ := hrPrefix
  obtain ⟨stail, hstail⟩ := hsPrefix
  change alternateLists crs css ++
      [(t.rho (⟨n + 1, by omega⟩ : Fin (m + 1))).depth] <+:
    alternateLists rs ss
  rw [← hrtail, ← hstail]
  rw [show crs.concat
      (t.rho (⟨n + 1, by omega⟩ : Fin (m + 1))).depth ++ rtail =
      crs ++ (t.rho (⟨n + 1, by omega⟩ : Fin (m + 1))).depth :: rtail by
        simp]
  rw [alternateLists_append_of_length_eq crs css
    ((t.rho (⟨n + 1, by omega⟩ : Fin (m + 1))).depth :: rtail)
    stail (by simp [crs, css])]
  cases stail <;> simp [alternateLists]

/-- At any positive cohook cutoff, replacing `rho_(n+1)` by a deeper
morphism and appending an irreducible cohook produces a tackle strictly more
efficient than the original one, regardless of the discarded tail. -/
theorem efficiency_lex_appendRhoCohook_prefixAt
    [HasFiniteRayPathDepth C] {m n : ℕ}
    (t : RayCohookTackle (C := C) m) (h : n < m)
    {X Z : C}
    (f : NonzeroHom
      ((RayCohookChain.prefixAt t h).x (Fin.last (n + 1))) Z)
    (g : NonzeroHom X Z)
    (hvalley : RaySourceIncomparable
      ((RayCohookChain.prefixAt t h).sigma (Fin.last n)) f)
    (hpeak : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : (RayCohookChain.cutoffRho t h).depth < f.depth) :
    List.Lex (fun a b : ℕ ↦ a < b)
      t.efficiency
      ((RayCohookChain.prefixAt t h).appendRhoCohook
        f g hvalley hpeak hg).efficiency := by
  obtain ⟨tail, htail⟩ :=
    RayCohookChain.efficiency_append_cutoffRho_isPrefix t h
  rw [← htail]
  rw [(RayCohookChain.prefixAt t h).efficiency_appendRhoCohook
    f g hvalley hpeak hg]
  have hfdepth' :
      (t.rho (⟨n + 1, by omega⟩ : Fin (m + 1))).depth < f.depth := by
    rw [← RayCohookChain.cutoffRho_depth_explicit t h]
    exact hfdepth
  have hlex : List.Lex (fun a b : ℕ ↦ a < b)
      ((t.rho (⟨n + 1, by omega⟩ : Fin (m + 1))).depth :: tail)
      [f.depth, g.depth] :=
    List.Lex.rel hfdepth'
  simpa [List.append_assoc] using
    List.Lex.append_left (fun a b : ℕ ↦ a < b)
      hlex (RayCohookChain.prefixAt t h).efficiency

/-- The arbitrary-cutoff cohook propagation step.  Against an efficient
original tackle, a deeper replacement for the first omitted `rho` which is
target-incomparable with a proposed new cohook must factor through the cutoff
chain's last `sigma`. -/
theorem exists_factorThroughCutoffSigma_of_isEfficientAt
    [HasFiniteRayPathDepth C] {m n : ℕ}
    (t : RayCohookTackle (C := C) m) (hcut : n < m) {y X Z : C}
    (ht : (RayTackle.cohook m t).IsEfficientAt y)
    (f : NonzeroHom
      ((RayCohookChain.prefixAt t hcut).x (Fin.last (n + 1))) Z)
    (g : NonzeroHom X Z)
    (b : t.z ((Fin.last n).castLE hcut).succ ⟶ Z)
    (hfactor : (RayCohookChain.cutoffRho t hcut).1 ≫ b = f.1)
    (hpeak : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : (RayCohookChain.cutoffRho t hcut).depth < f.depth) :
    ∃ q : (RayCohookChain.prefixAt t hcut).z (Fin.last n) ⟶ Z,
      q ≠ 0 ∧
        ((RayCohookChain.prefixAt t hcut).sigma (Fin.last n)).1 ≫ q =
          f.1 := by
  let c := RayCohookChain.prefixAt t hcut
  have hnot : ¬RaySourceIncomparable (c.sigma (Fin.last n)) f := by
    intro hvalley
    apply ht.2 (RayTackle.cohook (n + 1)
      (c.appendRhoCohook f g hvalley hpeak hg))
    · change (c.appendRhoCohook f g hvalley hpeak hg).x 0 = y
      exact (c.appendRhoCohook_x_zero
        f g hvalley hpeak hg).trans
          ((RayCohookChain.prefixAt_x_zero t hcut).trans ht.1)
    · simpa only [RayTackle.efficiency, c] using
        RayCohookChain.efficiency_lex_appendRhoCohook_prefixAt
          t hcut f g hvalley hpeak hg hfdepth
  by_cases hsf : ∃ q : c.z (Fin.last n) ⟶ Z,
      (c.sigma (Fin.last n)).1 ≫ q = f.1
  · obtain ⟨q, hq⟩ := hsf
    refine ⟨q, ?_, hq⟩
    rintro rfl
    apply f.2
    have hfzero : f.1 = 0 := by
      rw [← hq]
      simp only [comp_zero]
    exact hfzero
  · have hfs : ∃ q : Z ⟶ c.z (Fin.last n),
        f.1 ≫ q = (c.sigma (Fin.last n)).1 := by
      by_contra hfs
      exact hnot ⟨hsf, hfs⟩
    obtain ⟨q, hq⟩ := hfs
    exfalso
    apply (RayCohookChain.cutoff_valley_incomparable t hcut).2
    refine ⟨b ≫ q, ?_⟩
    calc
      (RayCohookChain.cutoffRho t hcut).1 ≫ (b ≫ q) =
          ((RayCohookChain.cutoffRho t hcut).1 ≫ b) ≫ q := by
        rw [Category.assoc]
      _ = f.1 ≫ q := congrArg (fun r ↦ r ≫ q) hfactor
      _ = (c.sigma (Fin.last n)).1 := hq

/-- Cut a hook tackle immediately after `sigma_n`, viewing the retained
prefix as a cohook chain.  This is the cross-orientation cutoff used by the
alternating Figure 55 walk in case 1 of BGRS 1.9. -/
def prefixOfHookAt {m n : ℕ} (t : RayHookTackle (C := C) m)
    (h : n < m) : RayCohookChain (C := C) n where
  x := Fin.take (n + 2) (by omega) t.x
  z := Fin.take (n + 1) (by omega) t.z
  rho := Fin.take (n + 1) (by omega) t.rho
  sigma := Fin.take (n + 1) (by omega) t.sigma
  peak_incomparable := fun i ↦ by
    simp only [Fin.take]
    let j : Fin m := i.castLE (by omega)
    have hr : j.castSucc = i.castSucc.castLE (by omega) := by
      apply Fin.ext
      rfl
    have hs : j.succ = i.succ.castLE (by omega) := by
      apply Fin.ext
      rfl
    cases hr
    cases hs
    exact t.peak_incomparable j
  valley_incomparable := fun i ↦ by
    simp only [Fin.take]
    let j : Fin m := i.castLE (Nat.le_of_lt h)
    have hs : j.castSucc = i.castSucc.castLE (by omega) := by
      apply Fin.ext
      rfl
    have hr : j.succ = i.succ.castLE (by omega) := by
      apply Fin.ext
      rfl
    cases hs
    cases hr
    exact t.valley_incomparable j

@[simp]
theorem prefixOfHookAt_x_zero {m n : ℕ}
    (t : RayHookTackle (C := C) m) (h : n < m) :
    (RayCohookChain.prefixOfHookAt t h).x 0 = t.x 0 := by
  simp [prefixOfHookAt, Fin.take]

/-- The first `rho` omitted from the cohook-shaped prefix of a hook tackle. -/
def cutoffRhoOfHook {m n : ℕ} (t : RayHookTackle (C := C) m)
    (h : n < m) :
    NonzeroHom ((RayCohookChain.prefixOfHookAt t h).x
        (Fin.last (n + 1)))
      (t.z ((Fin.last n).castLE h).succ) := by
  let i : Fin m := (Fin.last n).castLE h
  have hx : t.x i.succ =
      (RayCohookChain.prefixOfHookAt t h).x (Fin.last (n + 1)) := by
    simp only [RayCohookChain.prefixOfHookAt, Fin.take, i]
    congr 1
  exact (t.rho i.succ).cast hx rfl

@[simp]
theorem cutoffRhoOfHook_depth_index [HasFiniteRayPathDepth C]
    {m n : ℕ} (t : RayHookTackle (C := C) m) (h : n < m) :
    (RayCohookChain.cutoffRhoOfHook t h).depth =
      (t.rho ((Fin.last n).castLE h).succ).depth := by
  simp [cutoffRhoOfHook]

@[simp]
theorem cutoffRhoOfHook_depth [HasFiniteRayPathDepth C]
    {m n : ℕ} (t : RayHookTackle (C := C) m) (h : n < m) :
    (RayCohookChain.cutoffRhoOfHook t h).depth =
      (t.rho (⟨n + 1, by omega⟩ : Fin (m + 1))).depth := by
  rw [RayCohookChain.cutoffRhoOfHook_depth_index]
  congr 2

/-- The retained `sigma_n` remains valley-incomparable with the omitted
`rho_(n+1)` in a cross-orientation cutoff. -/
theorem cutoffOfHook_valley_incomparable {m n : ℕ}
    (t : RayHookTackle (C := C) m) (h : n < m) :
    RaySourceIncomparable
      ((RayCohookChain.prefixOfHookAt t h).sigma (Fin.last n))
      (RayCohookChain.cutoffRhoOfHook t h) := by
  let i : Fin m := (Fin.last n).castLE h
  have hx : t.x i.succ =
      t.x ((Fin.last (n + 1)).castLE (by omega)) := by
    congr 1
  simpa [RayCohookChain.prefixOfHookAt,
    RayCohookChain.cutoffRhoOfHook, NonzeroHom.cast, Fin.take, i] using
      (t.valley_incomparable i).cast hx rfl rfl

/-- The cross-orientation prefix through `sigma_n`, followed by the omitted
`rho_(n+1)`, is a prefix of the original hook tackle's efficiency word. -/
theorem efficiency_append_cutoffRhoOfHook_isPrefix
    [HasFiniteRayPathDepth C] {m n : ℕ}
    (t : RayHookTackle (C := C) m) (h : n < m) :
    (RayCohookChain.prefixOfHookAt t h).efficiency ++
        [(t.rho (⟨n + 1, by omega⟩ : Fin (m + 1))).depth] <+:
      t.efficiency := by
  let c := RayCohookChain.prefixOfHookAt t h
  let rs : List ℕ := List.ofFn fun i ↦ (t.rho i).depth
  let ss : List ℕ := List.ofFn fun i ↦ (t.sigma i).depth
  let crs : List ℕ := List.ofFn fun i ↦ (c.rho i).depth
  let css : List ℕ := List.ofFn fun i ↦ (c.sigma i).depth
  have hcrs : crs = rs.take (n + 1) := by
    change List.ofFn
      (Fin.take (n + 1) (by omega)
        (fun i : Fin (m + 1) ↦ (t.rho i).depth)) =
      (List.ofFn fun i : Fin (m + 1) ↦ (t.rho i).depth).take (n + 1)
    exact Fin.ofFn_take_eq_take_ofFn (n := m + 1) (m := n + 1)
      (by omega) (fun i : Fin (m + 1) ↦ (t.rho i).depth)
  have hcss : css = ss.take (n + 1) := by
    change List.ofFn
      (Fin.take (n + 1) (by omega)
        (fun i : Fin m ↦ (t.sigma i).depth)) =
      (List.ofFn fun i : Fin m ↦ (t.sigma i).depth).take (n + 1)
    exact Fin.ofFn_take_eq_take_ofFn (n := m) (m := n + 1)
      (by omega) (fun i : Fin m ↦ (t.sigma i).depth)
  have hrTake : crs.concat
        (t.rho (⟨n + 1, by omega⟩ : Fin (m + 1))).depth =
      rs.take (n + 2) := by
    rw [hcrs]
    conv_rhs =>
      rw [List.take_succ_eq_append_getElem (by simp [rs]; omega)]
    simp [rs]
  have hrPrefix : crs.concat
        (t.rho (⟨n + 1, by omega⟩ : Fin (m + 1))).depth <+: rs := by
    rw [hrTake]
    exact List.take_prefix _ _
  have hsPrefix : css <+: ss := by
    rw [hcss]
    exact List.take_prefix _ _
  obtain ⟨rtail, hrtail⟩ := hrPrefix
  obtain ⟨stail, hstail⟩ := hsPrefix
  change alternateLists crs css ++
      [(t.rho (⟨n + 1, by omega⟩ : Fin (m + 1))).depth] <+:
    alternateLists rs ss
  rw [← hrtail, ← hstail]
  rw [show crs.concat
      (t.rho (⟨n + 1, by omega⟩ : Fin (m + 1))).depth ++ rtail =
      crs ++ (t.rho (⟨n + 1, by omega⟩ : Fin (m + 1))).depth :: rtail by
        simp]
  rw [alternateLists_append_of_length_eq crs css
    ((t.rho (⟨n + 1, by omega⟩ : Fin (m + 1))).depth :: rtail)
    stail (by simp [crs, css])]
  cases stail <;> simp [alternateLists]

/-- Replacing the omitted `rho_(n+1)` by a deeper morphism and appending a
cohook improves the original hook tackle, even after discarding its tail. -/
theorem efficiency_lex_appendRhoCohook_prefixOfHookAt
    [HasFiniteRayPathDepth C] {m n : ℕ}
    (t : RayHookTackle (C := C) m) (h : n < m)
    {X Z : C}
    (f : NonzeroHom
      ((RayCohookChain.prefixOfHookAt t h).x (Fin.last (n + 1))) Z)
    (g : NonzeroHom X Z)
    (hvalley : RaySourceIncomparable
      ((RayCohookChain.prefixOfHookAt t h).sigma (Fin.last n)) f)
    (hpeak : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : (RayCohookChain.cutoffRhoOfHook t h).depth < f.depth) :
    List.Lex (fun a b : ℕ ↦ a < b) t.efficiency
      ((RayCohookChain.prefixOfHookAt t h).appendRhoCohook
        f g hvalley hpeak hg).efficiency := by
  obtain ⟨tail, htail⟩ :=
    RayCohookChain.efficiency_append_cutoffRhoOfHook_isPrefix t h
  rw [← htail]
  rw [(RayCohookChain.prefixOfHookAt t h).efficiency_appendRhoCohook
    f g hvalley hpeak hg]
  have hfdepth' :
      (t.rho (⟨n + 1, by omega⟩ : Fin (m + 1))).depth < f.depth := by
    rw [← RayCohookChain.cutoffRhoOfHook_depth t h]
    exact hfdepth
  have hlex : List.Lex (fun a b : ℕ ↦ a < b)
      ((t.rho (⟨n + 1, by omega⟩ : Fin (m + 1))).depth :: tail)
      [f.depth, g.depth] := List.Lex.rel hfdepth'
  simpa [List.append_assoc] using
    List.Lex.append_left (fun a b : ℕ ↦ a < b)
      hlex (RayCohookChain.prefixOfHookAt t h).efficiency

/-- Cross-orientation Figure 55 propagation inside one efficient hook
tackle: the deeper replacement for `rho_(n+1)` must factor through the
retained `sigma_n`. -/
theorem exists_factorThroughCutoffSigma_of_hook_isEfficientAt
    [HasFiniteRayPathDepth C] {m n : ℕ}
    (t : RayHookTackle (C := C) m) (hcut : n < m) {y X Z : C}
    (ht : (RayTackle.hook m t).IsEfficientAt y)
    (f : NonzeroHom
      ((RayCohookChain.prefixOfHookAt t hcut).x (Fin.last (n + 1))) Z)
    (g : NonzeroHom X Z)
    (b : t.z ((Fin.last n).castLE hcut).succ ⟶ Z)
    (hfactor : (RayCohookChain.cutoffRhoOfHook t hcut).1 ≫ b = f.1)
    (hpeak : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : (RayCohookChain.cutoffRhoOfHook t hcut).depth < f.depth) :
    ∃ q : (RayCohookChain.prefixOfHookAt t hcut).z (Fin.last n) ⟶ Z,
      q ≠ 0 ∧
        ((RayCohookChain.prefixOfHookAt t hcut).sigma (Fin.last n)).1 ≫ q =
          f.1 := by
  let c := RayCohookChain.prefixOfHookAt t hcut
  have hnot : ¬RaySourceIncomparable (c.sigma (Fin.last n)) f := by
    intro hvalley
    apply ht.2 (RayTackle.cohook (n + 1)
      (c.appendRhoCohook f g hvalley hpeak hg))
    · change (c.appendRhoCohook f g hvalley hpeak hg).x 0 = y
      exact (c.appendRhoCohook_x_zero f g hvalley hpeak hg).trans
        ((RayCohookChain.prefixOfHookAt_x_zero t hcut).trans ht.1)
    · simpa only [RayTackle.efficiency, c] using
        RayCohookChain.efficiency_lex_appendRhoCohook_prefixOfHookAt
          t hcut f g hvalley hpeak hg hfdepth
  by_cases hsf : ∃ q : c.z (Fin.last n) ⟶ Z,
      (c.sigma (Fin.last n)).1 ≫ q = f.1
  · obtain ⟨q, hq⟩ := hsf
    refine ⟨q, ?_, hq⟩
    rintro rfl
    apply f.2
    rw [← hq]
    simp
  · have hfs : ∃ q : Z ⟶ c.z (Fin.last n),
        f.1 ≫ q = (c.sigma (Fin.last n)).1 := by
      by_contra hfs
      exact hnot ⟨hsf, hfs⟩
    obtain ⟨q, hq⟩ := hfs
    exfalso
    apply (RayCohookChain.cutoffOfHook_valley_incomparable t hcut).2
    refine ⟨b ≫ q, ?_⟩
    calc
      (RayCohookChain.cutoffRhoOfHook t hcut).1 ≫ (b ≫ q) =
          ((RayCohookChain.cutoffRhoOfHook t hcut).1 ≫ b) ≫ q := by
        rw [Category.assoc]
      _ = f.1 ≫ q := congrArg (fun r ↦ r ≫ q) hfactor
      _ = (c.sigma (Fin.last n)).1 := hq

end RayCohookChain

namespace RayHookTackle

/-- The efficiency word before the final `sigma,rho` pair of a positive-length
hook tackle. -/
def efficiencyPairPrefix [HasFiniteRayPathDepth C] {n : ℕ}
    (t : RayHookTackle (C := C) (n + 1)) : List ℕ :=
  alternateLists
    (List.ofFn fun i : Fin (n + 1) ↦ (t.rho i.castSucc).depth)
    (List.ofFn fun i : Fin n ↦ (t.sigma i.castSucc).depth)

/-- A positive-length hook tackle consists of its pair prefix followed by its
last `sigma` and last `rho`. -/
theorem efficiency_eq_efficiencyPairPrefix_append_last
    [HasFiniteRayPathDepth C] {n : ℕ}
    (t : RayHookTackle (C := C) (n + 1)) :
    t.efficiency = t.efficiencyPairPrefix ++
      [(t.sigma (Fin.last n)).depth,
        (t.rho (Fin.last (n + 1))).depth] := by
  unfold RayHookTackle.efficiency efficiencyPairPrefix
  rw [List.ofFn_succ'
    (fun i : Fin (n + 2) ↦ (t.rho i).depth)]
  rw [List.ofFn_succ'
    (fun i : Fin (n + 1) ↦ (t.sigma i).depth)]
  exact alternateLists_concat_both_of_length_eq_succ _ _ _ _ (by simp)

/-- Retain a positive-length hook tackle up to its penultimate `rho`, replace
the final `sigma` by `f`, and replace the final hook by the irreducible `g`.
The new last valley and the preceding peak are supplied explicitly. -/
def deepenLastSigmaToHook {n : ℕ}
    (t : RayHookTackle (C := C) (n + 1))
    {X Z : C}
    (f : NonzeroHom X (t.z (Fin.last n).castSucc))
    (g : NonzeroHom X Z)
    (hpeak : RayTargetIncomparable
      (t.rho (Fin.last n).castSucc) f)
    (hvalley : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    RayHookTackle (C := C) (n + 1) := by
  let x' : Fin (n + 2) → C :=
    Fin.lastCases X (fun i : Fin (n + 1) ↦ t.x i.castSucc)
  let z' : Fin (n + 2) → C :=
    Fin.lastCases Z (fun i : Fin (n + 1) ↦ t.z i.castSucc)
  have hxCastSucc (i : Fin (n + 1)) :
      x' i.castSucc = t.x i.castSucc := by
    simp [x']
  have hzCastSucc (i : Fin (n + 1)) :
      z' i.castSucc = t.z i.castSucc := by
    simp [z']
  have hxPrevious (i : Fin n) :
      x' i.castSucc.succ = t.x i.castSucc.succ := by
    rw [Fin.succ_castSucc]
    simpa [Fin.castSucc_succ] using hxCastSucc i.succ
  have hxLast : x' (Fin.last (n + 1)) = X := by
    simp [x']
  have hzLast : z' (Fin.last (n + 1)) = Z := by
    simp [z']
  let rho' : ∀ i : Fin (n + 2), NonzeroHom (x' i) (z' i) :=
    Fin.lastCases
      (g.cast hxLast.symm hzLast.symm)
      (fun i : Fin (n + 1) ↦
        (t.rho i.castSucc).cast
          (hxCastSucc i).symm (hzCastSucc i).symm)
  let sigma' : ∀ i : Fin (n + 1),
      NonzeroHom (x' i.succ) (z' i.castSucc) :=
    Fin.lastCases
      (f.cast hxLast.symm (hzCastSucc (Fin.last n)).symm)
      (fun i : Fin n ↦
        (t.sigma i.castSucc).cast
          (hxPrevious i).symm (hzCastSucc i.castSucc).symm)
  exact
    { x := x'
      z := z'
      rho := rho'
      sigma := sigma'
      peak_incomparable := Fin.lastCases
        (by
          simp only [rho', sigma', Fin.lastCases_castSucc,
            Fin.lastCases_last]
          exact hpeak.cast
            (hxCastSucc (Fin.last n)).symm hxLast.symm
            (hzCastSucc (Fin.last n)).symm)
        (fun i : Fin n ↦ by
          simp only [rho', sigma', Fin.lastCases_castSucc]
          exact (t.peak_incomparable i.castSucc).cast
            (hxCastSucc i.castSucc).symm (hxPrevious i).symm
            (hzCastSucc i.castSucc).symm)
      valley_incomparable := Fin.lastCases
        (by
          simp only [rho', sigma', Fin.lastCases_last, Fin.succ_last]
          exact hvalley.cast hxLast.symm
            (hzCastSucc (Fin.last n)).symm hzLast.symm)
        (fun i : Fin n ↦ by
          have hzNext : t.z i.castSucc.succ =
              z' i.castSucc.succ := by
            simpa [Fin.castSucc_succ] using
              (hzCastSucc i.succ).symm
          simp only [rho', sigma', Fin.lastCases_castSucc,
            Fin.succ_castSucc]
          exact (t.valley_incomparable i.castSucc).cast
            (hxPrevious i).symm
            (hzCastSucc i.castSucc).symm hzNext)
      last_irreducible := by
        simp only [rho', Fin.lastCases_last]
        exact isIrreducibleMorphism_cast hxLast.symm hzLast.symm g hg }

@[simp]
theorem deepenLastSigmaToHook_x_zero {n : ℕ}
    (t : RayHookTackle (C := C) (n + 1))
    {X Z : C}
    (f : NonzeroHom X (t.z (Fin.last n).castSucc))
    (g : NonzeroHom X Z)
    (hpeak : RayTargetIncomparable
      (t.rho (Fin.last n).castSucc) f)
    (hvalley : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    (t.deepenLastSigmaToHook f g hpeak hvalley hg).x 0 = t.x 0 := by
  change Fin.lastCases X (fun i : Fin (n + 1) ↦ t.x i.castSucc)
      ((0 : Fin (n + 1)).castSucc) = t.x 0
  simpa using (Fin.lastCases_castSucc
    (motive := fun _ : Fin (n + 2) ↦ C)
    (last := X) (cast := fun i : Fin (n + 1) ↦ t.x i.castSucc) 0)

@[simp]
theorem deepenLastSigmaToHook_rho_castSucc_depth
    [HasFiniteRayPathDepth C] {n : ℕ}
    (t : RayHookTackle (C := C) (n + 1))
    {X Z : C}
    (f : NonzeroHom X (t.z (Fin.last n).castSucc))
    (g : NonzeroHom X Z)
    (hpeak : RayTargetIncomparable
      (t.rho (Fin.last n).castSucc) f)
    (hvalley : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) (i : Fin (n + 1)) :
    ((t.deepenLastSigmaToHook f g hpeak hvalley hg).rho i.castSucc).depth =
      (t.rho i.castSucc).depth := by
  simp [deepenLastSigmaToHook]

@[simp]
theorem deepenLastSigmaToHook_rho_last_depth
    [HasFiniteRayPathDepth C] {n : ℕ}
    (t : RayHookTackle (C := C) (n + 1))
    {X Z : C}
    (f : NonzeroHom X (t.z (Fin.last n).castSucc))
    (g : NonzeroHom X Z)
    (hpeak : RayTargetIncomparable
      (t.rho (Fin.last n).castSucc) f)
    (hvalley : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    ((t.deepenLastSigmaToHook f g hpeak hvalley hg).rho
      (Fin.last (n + 1))).depth = g.depth := by
  simp [deepenLastSigmaToHook]

@[simp]
theorem deepenLastSigmaToHook_sigma_castSucc_depth
    [HasFiniteRayPathDepth C] {n : ℕ}
    (t : RayHookTackle (C := C) (n + 1))
    {X Z : C}
    (f : NonzeroHom X (t.z (Fin.last n).castSucc))
    (g : NonzeroHom X Z)
    (hpeak : RayTargetIncomparable
      (t.rho (Fin.last n).castSucc) f)
    (hvalley : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) (i : Fin n) :
    ((t.deepenLastSigmaToHook f g hpeak hvalley hg).sigma i.castSucc).depth =
      (t.sigma i.castSucc).depth := by
  simp [deepenLastSigmaToHook]

@[simp]
theorem deepenLastSigmaToHook_sigma_last_depth
    [HasFiniteRayPathDepth C] {n : ℕ}
    (t : RayHookTackle (C := C) (n + 1))
    {X Z : C}
    (f : NonzeroHom X (t.z (Fin.last n).castSucc))
    (g : NonzeroHom X Z)
    (hpeak : RayTargetIncomparable
      (t.rho (Fin.last n).castSucc) f)
    (hvalley : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    ((t.deepenLastSigmaToHook f g hpeak hvalley hg).sigma
      (Fin.last n)).depth = f.depth := by
  simp [deepenLastSigmaToHook]

/-- The Figure 55 hook candidate retains the old efficiency prefix and
replaces only its last `sigma,rho` pair. -/
theorem efficiency_deepenLastSigmaToHook
    [HasFiniteRayPathDepth C] {n : ℕ}
    (t : RayHookTackle (C := C) (n + 1))
    {X Z : C}
    (f : NonzeroHom X (t.z (Fin.last n).castSucc))
    (g : NonzeroHom X Z)
    (hpeak : RayTargetIncomparable
      (t.rho (Fin.last n).castSucc) f)
    (hvalley : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    (t.deepenLastSigmaToHook f g hpeak hvalley hg).efficiency =
      t.efficiencyPairPrefix ++ [f.depth, g.depth] := by
  unfold RayHookTackle.efficiency efficiencyPairPrefix
  rw [List.ofFn_succ'
    (fun i : Fin (n + 2) ↦
      ((t.deepenLastSigmaToHook f g hpeak hvalley hg).rho i).depth)]
  rw [List.ofFn_succ'
    (fun i : Fin (n + 1) ↦
      ((t.deepenLastSigmaToHook f g hpeak hvalley hg).sigma i).depth)]
  rw [alternateLists_concat_both_of_length_eq_succ _ _ _ _ (by simp)]
  rw [t.deepenLastSigmaToHook_sigma_last_depth f g hpeak hvalley hg,
    t.deepenLastSigmaToHook_rho_last_depth f g hpeak hvalley hg]
  congr 1 <;> simp

/-- Deepening the last `sigma` strictly improves efficiency, independently of
the new irreducible hook's depth. -/
theorem efficiency_lex_deepenLastSigmaToHook
    [HasFiniteRayPathDepth C] {n : ℕ}
    (t : RayHookTackle (C := C) (n + 1))
    {X Z : C}
    (f : NonzeroHom X (t.z (Fin.last n).castSucc))
    (g : NonzeroHom X Z)
    (hpeak : RayTargetIncomparable
      (t.rho (Fin.last n).castSucc) f)
    (hvalley : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : (t.sigma (Fin.last n)).depth < f.depth) :
    List.Lex (fun a b : ℕ ↦ a < b)
      t.efficiency
      (t.deepenLastSigmaToHook f g hpeak hvalley hg).efficiency := by
  rw [t.efficiency_eq_efficiencyPairPrefix_append_last,
    t.efficiency_deepenLastSigmaToHook f g hpeak hvalley hg]
  exact List.Lex.append_left (fun a b : ℕ ↦ a < b)
    (List.Lex.rel hfdepth) t.efficiencyPairPrefix

/-- The second, peak-side Figure 55 propagation step.  For an efficient hook
tackle, a deeper last `sigma` which is source-incomparable with a proposed
new hook cannot also remain incomparable with the preceding `rho`.  Failure
in the opposite factorization direction would contradict the old peak, so the
deeper morphism factors through that `rho`. -/
theorem exists_factorThroughPrecedingRho_of_isEfficientAt
    [HasFiniteRayPathDepth C] {n : ℕ}
    (t : RayHookTackle (C := C) (n + 1)) {y X Z : C}
    (ht : (RayTackle.hook (n + 1) t).IsEfficientAt y)
    (f : NonzeroHom X (t.z (Fin.last n).castSucc))
    (g : NonzeroHom X Z)
    (a : X ⟶ t.x (Fin.last n).succ)
    (hfactor : a ≫ (t.sigma (Fin.last n)).1 = f.1)
    (hvalley : RaySourceIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : (t.sigma (Fin.last n)).depth < f.depth) :
    ∃ h : X ⟶ t.x (Fin.last n).castSucc,
      h ≠ 0 ∧ h ≫ (t.rho (Fin.last n).castSucc).1 = f.1 := by
  have hnot : ¬RayTargetIncomparable
      (t.rho (Fin.last n).castSucc) f := by
    intro hpeak
    apply ht.2 (RayTackle.hook (n + 1)
      (t.deepenLastSigmaToHook f g hpeak hvalley hg))
    · change (t.deepenLastSigmaToHook f g hpeak hvalley hg).x 0 = y
      exact (t.deepenLastSigmaToHook_x_zero
        f g hpeak hvalley hg).trans ht.1
    · simpa only [RayTackle.efficiency] using
        t.efficiency_lex_deepenLastSigmaToHook
          f g hpeak hvalley hg hfdepth
  by_cases hfr : ∃ h : X ⟶ t.x (Fin.last n).castSucc,
      h ≫ (t.rho (Fin.last n).castSucc).1 = f.1
  · obtain ⟨h, hh⟩ := hfr
    refine ⟨h, ?_, hh⟩
    rintro rfl
    apply f.2
    have hfzero : f.1 = 0 := by
      simpa only [zero_comp] using hh.symm
    exact hfzero
  · have hrf : ∃ h : t.x (Fin.last n).castSucc ⟶ X,
        h ≫ f.1 = (t.rho (Fin.last n).castSucc).1 := by
      by_contra hrf
      exact hnot ⟨hrf, hfr⟩
    obtain ⟨h, hh⟩ := hrf
    exfalso
    apply (t.peak_incomparable (Fin.last n)).1
    refine ⟨h ≫ a, ?_⟩
    rw [Category.assoc, hfactor, hh]

end RayHookTackle

namespace RayCohookTackle

/-- The efficiency word before the final `rho,sigma` pair of a cohook tackle
with a preceding valley. -/
def efficiencyPairPrefix [HasFiniteRayPathDepth C] {n : ℕ}
    (t : RayCohookTackle (C := C) (n + 1)) : List ℕ :=
  alternateLists
    (List.ofFn fun i : Fin (n + 1) ↦ (t.rho i.castSucc).depth)
    (List.ofFn fun i : Fin (n + 1) ↦ (t.sigma i.castSucc).depth)

/-- A positive-length cohook tackle consists of its pair prefix followed by
its last `rho` and last `sigma`. -/
theorem efficiency_eq_efficiencyPairPrefix_append_last
    [HasFiniteRayPathDepth C] {n : ℕ}
    (t : RayCohookTackle (C := C) (n + 1)) :
    t.efficiency = t.efficiencyPairPrefix ++
      [(t.rho (Fin.last (n + 1))).depth,
        (t.sigma (Fin.last (n + 1))).depth] := by
  unfold RayCohookTackle.efficiency efficiencyPairPrefix
  rw [List.ofFn_succ'
    (fun i : Fin (n + 2) ↦ (t.rho i).depth)]
  rw [List.ofFn_succ'
    (fun i : Fin (n + 2) ↦ (t.sigma i).depth)]
  exact alternateLists_concat_both_of_length_eq _ _ _ _ (by simp)

/-- Retain a cohook tackle through its penultimate `sigma`, replace its final
`rho` by `f`, and replace its final cohook by the irreducible `g`. -/
def deepenLastRhoToCohook {n : ℕ}
    (t : RayCohookTackle (C := C) (n + 1))
    {X Z : C}
    (f : NonzeroHom (t.x (Fin.last (n + 1)).castSucc) Z)
    (g : NonzeroHom X Z)
    (hvalley : RaySourceIncomparable
      (t.sigma (Fin.last n).castSucc) f)
    (hpeak : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    RayCohookTackle (C := C) (n + 1) := by
  let x' : Fin (n + 3) → C :=
    Fin.lastCases X (fun i : Fin (n + 2) ↦ t.x i.castSucc)
  let z' : Fin (n + 2) → C :=
    Fin.lastCases Z (fun i : Fin (n + 1) ↦ t.z i.castSucc)
  have hxCastSucc (i : Fin (n + 2)) :
      x' i.castSucc = t.x i.castSucc := by
    simp [x']
  have hzCastSucc (i : Fin (n + 1)) :
      z' i.castSucc = t.z i.castSucc := by
    simp [z']
  have hxPrevious (i : Fin (n + 1)) :
      x' i.castSucc.succ = t.x i.castSucc.succ := by
    rw [Fin.succ_castSucc]
    simpa [Fin.castSucc_succ] using hxCastSucc i.succ
  have hxLast : x' (Fin.last (n + 2)) = X := by
    simp [x']
  have hzLast : z' (Fin.last (n + 1)) = Z := by
    simp [z']
  let rho' : ∀ i : Fin (n + 2),
      NonzeroHom (x' i.castSucc) (z' i) :=
    Fin.lastCases
      (f.cast (hxCastSucc (Fin.last (n + 1))).symm hzLast.symm)
      (fun i : Fin (n + 1) ↦
        (t.rho i.castSucc).cast
          (hxCastSucc i.castSucc).symm (hzCastSucc i).symm)
  let sigma' : ∀ i : Fin (n + 2),
      NonzeroHom (x' i.succ) (z' i) :=
    Fin.lastCases
      (g.cast hxLast.symm hzLast.symm)
      (fun i : Fin (n + 1) ↦
        (t.sigma i.castSucc).cast
          (hxPrevious i).symm (hzCastSucc i).symm)
  exact
    { x := x'
      z := z'
      rho := rho'
      sigma := sigma'
      peak_incomparable := Fin.lastCases
        (by
          simp only [rho', sigma', Fin.lastCases_last]
          exact hpeak.cast
            (hxCastSucc (Fin.last (n + 1))).symm hxLast.symm
            hzLast.symm)
        (fun i : Fin (n + 1) ↦ by
          simp only [rho', sigma', Fin.lastCases_castSucc]
          exact (t.peak_incomparable i.castSucc).cast
            (hxCastSucc i.castSucc).symm (hxPrevious i).symm
            (hzCastSucc i).symm)
      valley_incomparable := Fin.lastCases
        (by
          simp only [rho', sigma', Fin.lastCases_castSucc,
            Fin.lastCases_last, Fin.succ_last]
          exact hvalley.cast
            (hxPrevious (Fin.last n)).symm
            (hzCastSucc (Fin.last n)).symm hzLast.symm)
        (fun i : Fin n ↦ by
          have hzNext : t.z i.castSucc.succ =
              z' i.castSucc.succ := by
            simpa [Fin.castSucc_succ] using
              (hzCastSucc i.succ).symm
          simp only [rho', sigma', Fin.lastCases_castSucc,
            Fin.succ_castSucc]
          exact (t.valley_incomparable i.castSucc).cast
            (hxPrevious i.castSucc).symm
            (hzCastSucc i.castSucc).symm hzNext)
      last_irreducible := by
        simp only [sigma', Fin.lastCases_last]
        exact isIrreducibleMorphism_cast hxLast.symm hzLast.symm g hg }

@[simp]
theorem deepenLastRhoToCohook_x_zero {n : ℕ}
    (t : RayCohookTackle (C := C) (n + 1))
    {X Z : C}
    (f : NonzeroHom (t.x (Fin.last (n + 1)).castSucc) Z)
    (g : NonzeroHom X Z)
    (hvalley : RaySourceIncomparable
      (t.sigma (Fin.last n).castSucc) f)
    (hpeak : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    (t.deepenLastRhoToCohook f g hvalley hpeak hg).x 0 = t.x 0 := by
  change Fin.lastCases X (fun i : Fin (n + 2) ↦ t.x i.castSucc)
      ((0 : Fin (n + 2)).castSucc) = t.x 0
  simpa using (Fin.lastCases_castSucc
    (motive := fun _ : Fin (n + 3) ↦ C)
    (last := X) (cast := fun i : Fin (n + 2) ↦ t.x i.castSucc) 0)

@[simp]
theorem deepenLastRhoToCohook_rho_castSucc_depth
    [HasFiniteRayPathDepth C] {n : ℕ}
    (t : RayCohookTackle (C := C) (n + 1))
    {X Z : C}
    (f : NonzeroHom (t.x (Fin.last (n + 1)).castSucc) Z)
    (g : NonzeroHom X Z)
    (hvalley : RaySourceIncomparable
      (t.sigma (Fin.last n).castSucc) f)
    (hpeak : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) (i : Fin (n + 1)) :
    ((t.deepenLastRhoToCohook f g hvalley hpeak hg).rho i.castSucc).depth =
      (t.rho i.castSucc).depth := by
  simp [deepenLastRhoToCohook]

@[simp]
theorem deepenLastRhoToCohook_rho_last_depth
    [HasFiniteRayPathDepth C] {n : ℕ}
    (t : RayCohookTackle (C := C) (n + 1))
    {X Z : C}
    (f : NonzeroHom (t.x (Fin.last (n + 1)).castSucc) Z)
    (g : NonzeroHom X Z)
    (hvalley : RaySourceIncomparable
      (t.sigma (Fin.last n).castSucc) f)
    (hpeak : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    ((t.deepenLastRhoToCohook f g hvalley hpeak hg).rho
      (Fin.last (n + 1))).depth = f.depth := by
  simp [deepenLastRhoToCohook]

@[simp]
theorem deepenLastRhoToCohook_sigma_castSucc_depth
    [HasFiniteRayPathDepth C] {n : ℕ}
    (t : RayCohookTackle (C := C) (n + 1))
    {X Z : C}
    (f : NonzeroHom (t.x (Fin.last (n + 1)).castSucc) Z)
    (g : NonzeroHom X Z)
    (hvalley : RaySourceIncomparable
      (t.sigma (Fin.last n).castSucc) f)
    (hpeak : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) (i : Fin (n + 1)) :
    ((t.deepenLastRhoToCohook f g hvalley hpeak hg).sigma i.castSucc).depth =
      (t.sigma i.castSucc).depth := by
  simp [deepenLastRhoToCohook]

@[simp]
theorem deepenLastRhoToCohook_sigma_last_depth
    [HasFiniteRayPathDepth C] {n : ℕ}
    (t : RayCohookTackle (C := C) (n + 1))
    {X Z : C}
    (f : NonzeroHom (t.x (Fin.last (n + 1)).castSucc) Z)
    (g : NonzeroHom X Z)
    (hvalley : RaySourceIncomparable
      (t.sigma (Fin.last n).castSucc) f)
    (hpeak : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    ((t.deepenLastRhoToCohook f g hvalley hpeak hg).sigma
      (Fin.last (n + 1))).depth = g.depth := by
  simp [deepenLastRhoToCohook]

/-- The dual Figure 55 candidate retains the old efficiency prefix and
replaces only its last `rho,sigma` pair. -/
theorem efficiency_deepenLastRhoToCohook
    [HasFiniteRayPathDepth C] {n : ℕ}
    (t : RayCohookTackle (C := C) (n + 1))
    {X Z : C}
    (f : NonzeroHom (t.x (Fin.last (n + 1)).castSucc) Z)
    (g : NonzeroHom X Z)
    (hvalley : RaySourceIncomparable
      (t.sigma (Fin.last n).castSucc) f)
    (hpeak : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1) :
    (t.deepenLastRhoToCohook f g hvalley hpeak hg).efficiency =
      t.efficiencyPairPrefix ++ [f.depth, g.depth] := by
  unfold RayCohookTackle.efficiency efficiencyPairPrefix
  rw [List.ofFn_succ'
    (fun i : Fin (n + 2) ↦
      ((t.deepenLastRhoToCohook f g hvalley hpeak hg).rho i).depth)]
  rw [List.ofFn_succ'
    (fun i : Fin (n + 2) ↦
      ((t.deepenLastRhoToCohook f g hvalley hpeak hg).sigma i).depth)]
  rw [alternateLists_concat_both_of_length_eq _ _ _ _ (by simp)]
  rw [t.deepenLastRhoToCohook_rho_last_depth f g hvalley hpeak hg,
    t.deepenLastRhoToCohook_sigma_last_depth f g hvalley hpeak hg]
  congr 1 <;> simp

/-- Deepening the last `rho` strictly improves efficiency, independently of
the new irreducible cohook's depth. -/
theorem efficiency_lex_deepenLastRhoToCohook
    [HasFiniteRayPathDepth C] {n : ℕ}
    (t : RayCohookTackle (C := C) (n + 1))
    {X Z : C}
    (f : NonzeroHom (t.x (Fin.last (n + 1)).castSucc) Z)
    (g : NonzeroHom X Z)
    (hvalley : RaySourceIncomparable
      (t.sigma (Fin.last n).castSucc) f)
    (hpeak : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : (t.rho (Fin.last (n + 1))).depth < f.depth) :
    List.Lex (fun a b : ℕ ↦ a < b)
      t.efficiency
      (t.deepenLastRhoToCohook f g hvalley hpeak hg).efficiency := by
  rw [t.efficiency_eq_efficiencyPairPrefix_append_last,
    t.efficiency_deepenLastRhoToCohook f g hvalley hpeak hg]
  exact List.Lex.append_left (fun a b : ℕ ↦ a < b)
    (List.Lex.rel hfdepth) t.efficiencyPairPrefix

/-- The dual valley-side Figure 55 propagation step.  Efficiency prevents a
deeper last `rho`, together with a proposed new cohook, from retaining the
preceding valley.  The wrong factorization direction contradicts the old
valley, so the deeper morphism factors through the preceding `sigma`. -/
theorem exists_factorThroughPrecedingSigma_of_isEfficientAt
    [HasFiniteRayPathDepth C] {n : ℕ}
    (t : RayCohookTackle (C := C) (n + 1)) {y X Z : C}
    (ht : (RayTackle.cohook (n + 1) t).IsEfficientAt y)
    (f : NonzeroHom (t.x (Fin.last (n + 1)).castSucc) Z)
    (g : NonzeroHom X Z)
    (b : t.z (Fin.last (n + 1)) ⟶ Z)
    (hfactor : (t.rho (Fin.last (n + 1))).1 ≫ b = f.1)
    (hpeak : RayTargetIncomparable f g)
    (hg : IsIrreducibleRayMorphism g.1)
    (hfdepth : (t.rho (Fin.last (n + 1))).depth < f.depth) :
    ∃ h : t.z (Fin.last n).castSucc ⟶ Z,
      h ≠ 0 ∧ (t.sigma (Fin.last n).castSucc).1 ≫ h = f.1 := by
  have hnot : ¬RaySourceIncomparable
      (t.sigma (Fin.last n).castSucc) f := by
    intro hvalley
    apply ht.2 (RayTackle.cohook (n + 1)
      (t.deepenLastRhoToCohook f g hvalley hpeak hg))
    · change (t.deepenLastRhoToCohook f g hvalley hpeak hg).x 0 = y
      exact (t.deepenLastRhoToCohook_x_zero
        f g hvalley hpeak hg).trans ht.1
    · simpa only [RayTackle.efficiency] using
        t.efficiency_lex_deepenLastRhoToCohook
          f g hvalley hpeak hg hfdepth
  by_cases hsf : ∃ h : t.z (Fin.last n).castSucc ⟶ Z,
      (t.sigma (Fin.last n).castSucc).1 ≫ h = f.1
  · obtain ⟨h, hh⟩ := hsf
    refine ⟨h, ?_, hh⟩
    rintro rfl
    apply f.2
    have hfzero : f.1 = 0 := by
      rw [← hh]
      simp only [comp_zero]
    exact hfzero
  · have hfs : ∃ h : Z ⟶ t.z (Fin.last n).castSucc,
        f.1 ≫ h = (t.sigma (Fin.last n).castSucc).1 := by
      by_contra hfs
      exact hnot ⟨hsf, hfs⟩
    obtain ⟨h, hh⟩ := hfs
    exfalso
    apply (t.valley_incomparable (Fin.last n)).2
    refine ⟨b ≫ h, ?_⟩
    have hres : (t.rho (Fin.last (n + 1))).1 ≫ (b ≫ h) =
        (t.sigma (Fin.last n).castSucc).1 := by
      calc
        (t.rho (Fin.last (n + 1))).1 ≫ (b ≫ h) =
            ((t.rho (Fin.last (n + 1))).1 ≫ b) ≫ h := by
          rw [Category.assoc]
        _ = f.1 ≫ h := congrArg (fun q ↦ q ≫ h) hfactor
        _ = (t.sigma (Fin.last n).castSucc).1 := hh
    simpa only [Fin.succ_last, Fin.succ_castSucc] using hres

end RayCohookTackle

end LargeIndecomposable
