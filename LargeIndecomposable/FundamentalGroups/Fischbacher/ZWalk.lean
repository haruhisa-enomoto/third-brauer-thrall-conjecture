module

public import LargeIndecomposable.Coverings.UniversalCover.LocalSC

/-!
# Zigzag walks (for Fischbacher's Lemma 5.2)

A zigzag walk from `b` back to `b` (Fischbacher, Lemma 5.2) descends a path `v'` to a peak
`d₀`, then runs through segments `dᵢ ⇜ cᵢ₊₁ ⇝ dᵢ₊₁` (a `t`-path and an `s`-path out of the valley
`cᵢ₊₁`), and climbs a path `w'` from the last peak back to `b`. Segments are kept as a list
(`ZWalk.segs`) so that §5.3 can insert new peaks by list surgery. This file sets up the walks,
their vertex sets and convex hulls (`ZWalk.hull`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

universe v u

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

/-- The vertices of a path. -/
def pathVerts {x : RayVert A} : ∀ {y : RayVert A}, Quiver.Path x y → Set A
  | _, .nil => {x.out}
  | y, .cons p _ => insert y.out (pathVerts p)

lemma mem_pathVerts_start {x : RayVert A} : ∀ {y : RayVert A} (p : Quiver.Path x y),
    x.out ∈ pathVerts p
  | _, .nil => rfl
  | _, .cons p _ => Set.mem_insert_of_mem _ (mem_pathVerts_start p)

lemma mem_pathVerts_end {x : RayVert A} : ∀ {y : RayVert A} (p : Quiver.Path x y),
    y.out ∈ pathVerts p
  | _, .nil => rfl
  | _, .cons _ _ => Set.mem_insert _ _

lemma pathVerts_finite {x : RayVert A} : ∀ {y : RayVert A} (p : Quiver.Path x y),
    (pathVerts p).Finite
  | _, .nil => Set.finite_singleton _
  | _, .cons p _ => (pathVerts_finite p).insert _

/-- A vertex of a path is reachable from its start and reaches its end. -/
lemma reaches_of_mem_pathVerts {x : RayVert A} : ∀ {y : RayVert A} (p : Quiver.Path x y) {z : A},
    z ∈ pathVerts p → Reaches x.out z ∧ Reaches z y.out
  | _, .nil, z, h => by
    rw [pathVerts, Set.mem_singleton_iff] at h
    subst h
    exact ⟨Reaches.refl _, Reaches.refl _⟩
  | _, .cons p e, z, h => by
    rcases h with rfl | h
    · exact ⟨⟨p.cons e⟩, Reaches.refl _⟩
    · obtain ⟨h1, h2⟩ := reaches_of_mem_pathVerts p h
      exact ⟨h1, h2.trans ⟨e.toPath⟩⟩

/-- A path lies in any set containing its vertices. -/
lemma pathIn_of_verts_subset {S : Set A} {x : RayVert A} :
    ∀ {y : RayVert A} (p : Quiver.Path x y), pathVerts p ⊆ S → PathIn S p
  | _, .nil, h => h rfl
  | _, .cons p _, h => ⟨pathIn_of_verts_subset p fun z hz ↦ h (Set.mem_insert_of_mem _ hz),
      h (Set.mem_insert _ _)⟩

lemma verts_subset_of_pathIn {S : Set A} {x : RayVert A} :
    ∀ {y : RayVert A} (p : Quiver.Path x y), PathIn S p → pathVerts p ⊆ S
  | _, .nil, h => fun z hz ↦ by rw [pathVerts, Set.mem_singleton_iff] at hz; exact hz ▸ h
  | _, .cons p _, h => by
    intro z hz
    rcases hz with rfl | hz
    · exact h.2
    · exact verts_subset_of_pathIn p h.1 hz

/-- The vertices of a composite path. -/
lemma pathVerts_comp {x y : RayVert A} (p : Quiver.Path x y) :
    ∀ {z : RayVert A} (q : Quiver.Path y z), pathVerts (p.comp q) = pathVerts p ∪ pathVerts q
  | _, .nil => by
    simp only [Quiver.Path.comp_nil, pathVerts]
    exact (Set.union_eq_left.2 (Set.singleton_subset_iff.2 (mem_pathVerts_end p))).symm
  | _, .cons q _ => by
    rw [Quiver.Path.comp_cons, pathVerts, pathVerts, pathVerts_comp p q, Set.union_insert]

/-- A segment `d_left ⇜ c ⇝ d` of a zigzag walk. -/
structure ZSeg (A : Type u) [Category.{v} A] [HasZeroMorphisms A] where
  /-- The valley. -/
  c : A
  /-- The left peak, end of the `t`-path. -/
  dl : A
  /-- The right peak, end of the `s`-path. -/
  d : A
  /-- The descending path on the left. -/
  t : Quiver.Path (RayVert.mk c) (RayVert.mk dl)
  /-- The ascending path on the right. -/
  s : Quiver.Path (RayVert.mk c) (RayVert.mk d)

/-- The vertices of a segment. -/
def ZSeg.verts (σ : ZSeg A) : Set A := pathVerts σ.t ∪ pathVerts σ.s

/-- A segment read backwards: `d ⇜ c ⇝ d_left`. -/
def ZSeg.swap (σ : ZSeg A) : ZSeg A := ⟨σ.c, σ.d, σ.dl, σ.s, σ.t⟩

lemma ZSeg.verts_swap (σ : ZSeg A) : σ.swap.verts = σ.verts := Set.union_comm _ _

/-- Consecutive segments: the left peak of each is the right peak of the previous one. -/
def ZLinked (d₀ : A) : List (ZSeg A) → Prop
  | [] => True
  | σ :: L => σ.dl = d₀ ∧ ZLinked σ.d L

/-- The last peak. -/
def ZLast (d₀ : A) : List (ZSeg A) → A
  | [] => d₀
  | σ :: L => ZLast σ.d L

/-- A zigzag walk from `b` to `b`. -/
structure ZWalk (b : A) where
  /-- The first peak. -/
  d₀ : A
  /-- The segments. -/
  segs : List (ZSeg A)
  linked : ZLinked d₀ segs
  /-- The path from the first peak to `b`. -/
  v' : Quiver.Path (RayVert.mk d₀) (RayVert.mk b)
  /-- The path from the last peak to `b`. -/
  w' : Quiver.Path (RayVert.mk (ZLast d₀ segs)) (RayVert.mk b)

lemma zLast_append : ∀ (d₀ : A) (L₁ L₂ : List (ZSeg A)),
    ZLast d₀ (L₁ ++ L₂) = ZLast (ZLast d₀ L₁) L₂
  | _, [], _ => rfl
  | _, σ :: L₁, L₂ => zLast_append σ.d L₁ L₂

lemma zLinked_append : ∀ (d₀ : A) (L₁ L₂ : List (ZSeg A)),
    ZLinked d₀ (L₁ ++ L₂) ↔ ZLinked d₀ L₁ ∧ ZLinked (ZLast d₀ L₁) L₂
  | _, [], _ => by simp [ZLinked, ZLast]
  | _, σ :: L₁, L₂ => by
    simp only [List.cons_append, ZLinked, ZLast, zLinked_append σ.d L₁ L₂, and_assoc]

/-- Reversing a linked list of segments (each read backwards). -/
lemma zLinked_reverse : ∀ (d₀ : A) (L : List (ZSeg A)), ZLinked d₀ L →
    ZLinked (ZLast d₀ L) (L.reverse.map ZSeg.swap) ∧ ZLast (ZLast d₀ L) (L.reverse.map ZSeg.swap) = d₀
  | _, [], _ => ⟨trivial, rfl⟩
  | d₀, σ :: L, ⟨hdl, hl⟩ => by
    obtain ⟨h1, h2⟩ := zLinked_reverse σ.d L hl
    rw [List.reverse_cons]
    change ZLinked (ZLast σ.d L) ((L.reverse ++ [σ]).map ZSeg.swap) ∧
      ZLast (ZLast σ.d L) ((L.reverse ++ [σ]).map ZSeg.swap) = d₀
    rw [List.map_append, zLinked_append, zLast_append, h2]
    exact ⟨⟨h1, rfl, trivial⟩, hdl⟩

section Conn

variable [IsRayCategory A] {D : Set A} {q : A}

/-- A path whose vertices lie in `D \ {q}` joins its ends in `D \ {q}`. -/
lemma eqvGen_of_path {x y : RayVert A} (p : Quiver.Path x y) (h : pathVerts p ⊆ D \ {q}) :
    Relation.EqvGen (AdjOff D q) x.out y.out :=
  eqvGen_adjOff_of_path p (pathIn_of_verts_subset p h)

/-- **Linked segments avoiding `q` join their end peaks in `D \ {q}`.** -/
lemma eqvGen_of_linked : ∀ (d₀ : A) (L : List (ZSeg A)), ZLinked d₀ L →
    (∀ σ ∈ L, σ.verts ⊆ D \ {q}) → (d₀ ∈ D \ {q}) →
      Relation.EqvGen (AdjOff D q) d₀ (ZLast d₀ L)
  | d₀, [], _, _, _ => Relation.EqvGen.refl _
  | d₀, σ :: L, hl, hv, h₀ => by
    obtain ⟨hdl, hl'⟩ := hl
    have hσ := hv σ (List.mem_cons_self ..)
    have ht := eqvGen_of_path σ.t fun z hz ↦ hσ (Or.inl hz)
    have hs := eqvGen_of_path σ.s fun z hz ↦ hσ (Or.inr hz)
    have hd : σ.d ∈ D \ {q} := hσ (Or.inr (mem_pathVerts_end _))
    have hrest := eqvGen_of_linked σ.d L hl' (fun σ' h' ↦ hv σ' (List.mem_cons_of_mem _ h')) hd
    change Relation.EqvGen (AdjOff D q) d₀ (ZLast σ.d L)
    rw [← hdl]
    exact (ht.symm.trans _ _ _ hs).trans _ _ _ hrest

end Conn

namespace ZWalk

variable {b : A} (z : ZWalk b)

/-- The vertices of a walk. -/
def verts : Set A := pathVerts z.v' ∪ pathVerts z.w' ∪ ⋃ σ ∈ z.segs, σ.verts

lemma verts_finite : z.verts.Finite := by
  refine ((pathVerts_finite _).union (pathVerts_finite _)).union ?_
  exact (z.segs.finite_toSet).biUnion fun σ _ ↦
    (pathVerts_finite σ.t).union (pathVerts_finite σ.s)

/-- The convex hull of a walk. -/
def hull [IsRayCategory A] : Set A := hullOf z.verts

lemma seg_verts_subset {σ : ZSeg A} (h : σ ∈ z.segs) : σ.verts ⊆ z.verts :=
  fun _ hx ↦ Or.inr (Set.mem_biUnion h hx)

variable [IsRayCategory A]

lemma verts_subset_hull : z.verts ⊆ z.hull := subset_hullOf _

lemma convexR_hull : ConvexR z.hull := convexR_hullOf _

lemma hull_finite (hint : ∀ a b : A, (interval a b).Finite) : z.hull.Finite :=
  finite_hullOf hint z.verts_finite

/-- **Fischbacher's Lemma 4.4 (walk form).** Let the peak `q` of a zigzag walk, between the
segments `⟨c, dl, q, t, s₀ e₁⟩` and `⟨c', q, d', t₀ e₂, s'⟩`, meet no other vertex of the walk. If
`q` is maximal in the hull and every cocycle on the hull is a coboundary, the last arrows `e₁`,
`e₂` lie in one component of the morphisms into `q`: `q` is not separating. -/
theorem sepComp_of_peak (hint : ∀ a b : A, (interval a b).Finite)
    (hsc : ∀ c : ArrowWeight A, IsCocycleOn z.hull c → IsCoboundaryOn z.hull c)
    {L₁ L₂ : List (ZSeg A)} {c dl q c' d' : A} {x₁ x₂ : RayVert A}
    {t : Quiver.Path (RayVert.mk c) (RayVert.mk dl)} {s₀ : Quiver.Path (RayVert.mk c) x₁}
    {e₁ : x₁ ⟶ RayVert.mk q} {t₀ : Quiver.Path (RayVert.mk c') x₂} {e₂ : x₂ ⟶ RayVert.mk q}
    {s' : Quiver.Path (RayVert.mk c') (RayVert.mk d')}
    (hsplit : z.segs = L₁ ++ ⟨c, dl, q, t, s₀.cons e₁⟩ :: ⟨c', q, d', t₀.cons e₂, s'⟩ :: L₂)
    (hv' : q ∉ pathVerts z.v') (hw' : q ∉ pathVerts z.w') (hL : ∀ τ ∈ L₁ ++ L₂, q ∉ τ.verts)
    (ht : q ∉ pathVerts t) (hs' : q ∉ pathVerts s') (hs₀ : q ∉ pathVerts s₀)
    (ht₀ : q ∉ pathVerts t₀)
    (hmax : ∀ {y : RayVert A} (_ : RayVert.mk q ⟶ y), y.out ∉ z.hull) :
    SepComp z.hull q ⟨x₁.out, e₁.1⟩ ⟨x₂.out, e₂.1⟩ := by
  set σ : ZSeg A := ⟨c, dl, q, t, s₀.cons e₁⟩
  set σ' : ZSeg A := ⟨c', q, d', t₀.cons e₂, s'⟩
  have hσ : σ ∈ z.segs := by rw [hsplit]; simp
  have hσ' : σ' ∈ z.segs := by rw [hsplit]; simp
  have hin : ∀ {X : Set A}, X ⊆ z.verts → q ∉ X → X ⊆ z.hull \ {q} :=
    fun hX hq _ hx ↦ ⟨z.verts_subset_hull (hX hx), fun h ↦ hq (by rw [Set.mem_singleton_iff] at h; exact h ▸ hx)⟩
  have hσv := z.seg_verts_subset hσ
  have hσ'v := z.seg_verts_subset hσ'
  -- the linking
  have hlink := z.linked
  rw [hsplit, zLinked_append] at hlink
  obtain ⟨hl₁, hdl, -, hl₂⟩ := hlink
  have hlast : ZLast z.d₀ z.segs = ZLast d' L₂ := by rw [hsplit, zLast_append]; rfl
  -- the pieces
  have h1 := eqvGen_of_path (D := z.hull) (q := q) s₀
    (hin (fun _ hx ↦ hσv (Or.inr (Set.mem_insert_of_mem _ hx))) hs₀)
  have h2 := eqvGen_of_path (D := z.hull) (q := q) t (hin (fun _ hx ↦ hσv (Or.inl hx)) ht)
  have hL₁ : ∀ τ ∈ L₁, τ.verts ⊆ z.hull \ {q} := fun τ hτ ↦
    hin (z.seg_verts_subset (by rw [hsplit]; simp [hτ])) (hL τ (List.mem_append_left _ hτ))
  have hL₂ : ∀ τ ∈ L₂, τ.verts ⊆ z.hull \ {q} := fun τ hτ ↦
    hin (z.seg_verts_subset (by rw [hsplit]; simp [hτ])) (hL τ (List.mem_append_right _ hτ))
  have hd₀ : z.d₀ ∈ z.hull \ {q} :=
    hin (fun _ hx ↦ Or.inl (Or.inl hx)) hv' (mem_pathVerts_start z.v')
  have h3 := eqvGen_of_linked z.d₀ L₁ hl₁ hL₁ hd₀
  have h4 := eqvGen_of_path (D := z.hull) (q := q) z.v' (hin (fun _ hx ↦ Or.inl (Or.inl hx)) hv')
  have h5 := eqvGen_of_path (D := z.hull) (q := q) z.w' (hin (fun _ hx ↦ Or.inl (Or.inr hx)) hw')
  have hd' : d' ∈ z.hull \ {q} := hin (fun _ hx ↦ hσ'v (Or.inr hx)) hs' (mem_pathVerts_end s')
  have h6 := eqvGen_of_linked d' L₂ hl₂ hL₂ hd'
  have h7 := eqvGen_of_path (D := z.hull) (q := q) s' (hin (fun _ hx ↦ hσ'v (Or.inr hx)) hs')
  have h8 := eqvGen_of_path (D := z.hull) (q := q) t₀
    (hin (fun _ hx ↦ hσ'v (Or.inl (Set.mem_insert_of_mem _ hx))) ht₀)
  rw [← hdl] at h3
  change Relation.EqvGen _ (ZLast z.d₀ z.segs) _ at h5
  rw [hlast] at h5
  have hconn : Relation.EqvGen (AdjOff z.hull q) x₁.out x₂.out :=
    h1.symm.trans _ _ _ (h2.trans _ _ _ (h3.symm.trans _ _ _ (h4.trans _ _ _
      (h5.symm.trans _ _ _ (h6.symm.trans _ _ _ (h7.symm.trans _ _ _ h8))))))
  have hx₁ : x₁.out ∈ z.hull \ {q} := hin (fun _ hx ↦ hσv (Or.inr (Set.mem_insert_of_mem _ hx)))
    hs₀ (mem_pathVerts_end s₀)
  have hx₂ : x₂.out ∈ z.hull \ {q} := hin (fun _ hx ↦ hσ'v (Or.inl (Set.mem_insert_of_mem _ hx)))
    ht₀ (mem_pathVerts_end t₀)
  exact sepComp_of_coboundary (z.verts_subset_hull (hσv (Or.inr (Set.mem_insert _ _)))) hmax hsc
    e₁ e₂ hx₁.1 hx₂.1 hx₁.2 hx₂.2 hconn

/-- The peaks of a walk, from the first to the last. -/
def peaks : List A := z.d₀ :: z.segs.map ZSeg.d

/-- The conditions of Fischbacher's proof of Lemma 5.2 for a walk relative to a path
`w : a ⇝ b`: (0) `w` runs through the last peak and ends with `w'`; (1) the `s`-paths are nonzero;
the pieces are nontrivial; (2) every inner peak is separating in the hull; (3) consecutive peaks
are incomparable. -/
structure Good {a : A} (w : Quiver.Path (RayVert.mk a) (RayVert.mk b)) : Prop where
  ne_nil : z.segs ≠ []
  along : ∃ w₁ : Quiver.Path (RayVert.mk a) (RayVert.mk (ZLast z.d₀ z.segs)), w = w₁.comp z.w'
  sne : ∀ σ ∈ z.segs, pathVal σ.s ≠ 0
  tpos : ∀ σ ∈ z.segs, 0 < σ.t.length
  spos : ∀ σ ∈ z.segs, 0 < σ.s.length
  sep : ∀ (L₁ L₂ : List (ZSeg A)) (c dl q c' d' : A) (x₁ x₂ : RayVert A)
      (t : Quiver.Path (RayVert.mk c) (RayVert.mk dl)) (s₀ : Quiver.Path (RayVert.mk c) x₁)
      (e₁ : x₁ ⟶ RayVert.mk q) (t₀ : Quiver.Path (RayVert.mk c') x₂) (e₂ : x₂ ⟶ RayVert.mk q)
      (s' : Quiver.Path (RayVert.mk c') (RayVert.mk d')),
      z.segs = L₁ ++ ⟨c, dl, q, t, s₀.cons e₁⟩ :: ⟨c', q, d', t₀.cons e₂, s'⟩ :: L₂ →
        ¬SepComp z.hull q ⟨x₁.out, e₁.1⟩ ⟨x₂.out, e₂.1⟩
  incomp : ∀ σ ∈ z.segs, ¬Reaches σ.dl σ.d ∧ ¬Reaches σ.d σ.dl

end ZWalk

omit [HasZeroMorphisms A] in
/-- In a finite set without oriented cycles every point lies below a maximal one. -/
lemma exists_max_above [HasZeroMorphisms A] {H : Set A} (hcf : CycleFreeOn H) (hfin : H.Finite)
    {x : A} (hx : x ∈ H) : ∃ m ∈ H, Reaches x m ∧ ∀ y ∈ H, Reaches m y → y = m := by
  obtain ⟨m, ⟨hmH, hxm⟩, hmax⟩ := exists_max_reaches (H := H) (X := {y ∈ H | Reaches x y}) hcf
    (fun y hy ↦ hy.1) (hfin.subset fun y hy ↦ hy.1) ⟨x, hx, Reaches.refl x⟩
  exact ⟨m, hmH, hxm, fun y hy hmy ↦ hmax y ⟨hy, hxm.trans hmy⟩ hmy⟩

end LargeIndecomposable.RayCat
