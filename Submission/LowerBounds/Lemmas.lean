import ChallengeDeps

open Finset LeanEval.Geometry.PlatonicClassification

lemma EuclideanSpace.smul_single {ι 𝕜 : Type*} [DecidableEq ι] [RCLike 𝕜] {i : ι} {a c : 𝕜} :
    c • EuclideanSpace.single i a = EuclideanSpace.single i (c * a) := by ext; simp

lemma EuclideanSpace.sum_single {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]
    (x : EuclideanSpace 𝕜 ι) : x = ∑ i, .single i (x i) := by ext; simp

variable {n : ℕ}

/-- Every subset of a sphere coincides with the extreme points of its convex hull.
The key idea is that the closed ball is strictly convex, so any point on the
sphere cannot be a nontrivial convex combination of points in the closed ball. -/
lemma self_eq_extremePoints_convexHull_of_subset_sphere {s : Set (E n)} (c : E n) (r : ℝ)
    (hs : ∀ p ∈ s, dist c p = r) : s = Set.extremePoints ℝ (convexHull ℝ s) := by
  refine subset_antisymm (fun p mp ↦ ?_) extremePoints_convexHull_subset
  have chs : convexHull ℝ s ⊆ Metric.closedBall c r :=
    convexHull_min (fun x hx ↦ by rw [Metric.mem_closedBall']; exact (hs x hx).le)
      (convex_closedBall ..)
  refine ⟨subset_convexHull ℝ s mp, fun x₁ mx₁ x₂ mx₂ mpo ↦ ?_⟩
  by_contra h
  have os : openSegment ℝ x₁ x₂ ⊆ interior (Metric.closedBall c r) :=
    (strictConvex_closedBall ℝ c r).openSegment_subset (chs mx₁) (chs mx₂)
      (by contrapose h; simp_all [openSegment_same])
  specialize os mpo
  have mpb : p ∈ Metric.ball c r := by
    obtain rfl | hr := eq_or_ne r 0
    · obtain rfl | _ := eq_zero_or_neZero n
      · exact absurd (Subsingleton.elim ..) h
      · simp at os
    · rwa [interior_closedBall _ hr] at os
  exact (Metric.mem_ball'.mp mpb).ne (hs p mp)

/-! ### Bracketing points -/

/-- If a nonzero linear form `L` in `n` dimensions is constant on `n` affinely
independent points, any linear form with said property is a scalar multiple of `L`. -/
lemma constantOn_strongDual_characterisation {L M : StrongDual ℝ (E n)} {f : Fin n → E n}
    {c d : ℝ} (nL : L ≠ 0) (aif : AffineIndependent ℝ f)
    (Lc : ∀ i, L (f i) = c) (Md : ∀ i, M (f i) = d) : ∃ k : ℝ, M = k • L := by
  rcases n with _ | n
  · exact absurd (Subsingleton.elim ..) nL
  simp_rw [affineIndependent_iff_linearIndependent_vsub ℝ f 0, vsub_eq_sub] at aif
  let v (i : { i : Fin (n + 1) // i ≠ 0 }) := f i.1 - f 0
  have LM0 (x) (hx : x ∈ Submodule.span ℝ (Set.range v)) : L x = 0 ∧ M x = 0 := by
    induction hx using Submodule.span_induction with
    | mem y my =>
      obtain ⟨i, rfl⟩ := my
      simp [v, Lc, Md]
    | zero => simp
    | add y z my mz hy hz => simp [hy, hz]
    | smul k y my hy => simp [hy]
  obtain ⟨x₀, nx₀⟩ : ∃ x, L x ≠ 0 := not_forall.mp fun h ↦ nL (ContinuousLinearMap.ext h)
  have sek : Submodule.span ℝ (Set.range v) = L.toLinearMap.ker := by
    apply Submodule.eq_of_le_of_finrank_eq (fun x hx ↦ (LM0 x hx).1)
    rw [finrank_span_eq_card aif, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique,
      Nat.add_sub_cancel]
    have surjL : Function.Surjective L := fun w ↦ ⟨(w / L x₀) • x₀, by simp [nx₀]⟩
    rw [← L.coe_coe, ← L.range_eq_top] at surjL
    have rnt := L.toLinearMap.finrank_range_add_finrank_ker
    rwa [finrank_euclideanSpace, Fintype.card_fin, surjL, finrank_top, Module.finrank_self,
      add_comm, add_left_inj, eq_comm] at rnt
  simp_rw [sek, L.mem_ker, L.coe_coe, imp_and, imp_self, true_and] at LM0
  refine ⟨M x₀ / L x₀, ?_⟩
  ext y
  specialize LM0 (y - (L y / L x₀) • x₀)
  simp_rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ nx₀, sub_self, forall_const] at LM0
  rwa [smul_apply, smul_eq_mul, div_mul_comm, ← sub_eq_zero]

/-- Suppose we have a linear form `L` in `n` dimensions, `n` affinely independent vertices
on which `L` is a constant `c` and two more points `p,q` with `L p < c < L q`.
Then the convex hull of the `n` vertices is **not** exposed in
the convex hull of all `n + 2` vertices. -/
theorem not_isExposed_of_bracketing_points [NeZero n]
    {L : StrongDual ℝ (E n)} {f : Fin n → E n} {c : ℝ} {p q : E n}
    (aif : AffineIndependent ℝ f) (Lc : ∀ i, L (f i) = c) (Lp : L p < c) (Lq : c < L q) :
    ¬IsExposed ℝ (convexHull ℝ ↑(univ.image f ∪ {p, q}))
      (convexHull ℝ (univ.image f : Set (E n))) := fun contra ↦ by
  set g := univ.image f
  have ng : (g : Set (E n)).Nonempty := by simp_rw [coe_nonempty, g]; simp
  have sg : convexHull ℝ (g : Set (E n)) ⊆ convexHull ℝ ↑(g ∪ {p, q}) :=
    convexHull_mono subset_union_left
  specialize contra ng.convexHull
  obtain ⟨r, mr⟩ := ng
  obtain ⟨M, hM⟩ := contra
  obtain ⟨d, Md⟩ : ∃ d, ∀ v ∈ g, M v = d := by
    have cM {v w} (mv : v ∈ g) (mw : w ∈ g) : M v = M w := by
      have l₁ := subset_convexHull ℝ _ mv
      have l₂ := subset_convexHull ℝ _ mw
      exact le_antisymm ((hM ▸ l₂).2 _ (sg l₁)) ((hM ▸ l₁).2 _ (sg l₂))
    exact ⟨M r, fun v hv ↦ cM hv mr⟩
  have nL : L ≠ 0 := fun contra ↦ by
    rw [contra, zero_apply] at Lp Lq
    exact Lp.asymm Lq
  have Mdi (i) : M (f i) = d := Md _ (by simp [g])
  obtain ⟨k, rfl⟩ := constantOn_strongDual_characterisation nL aif Lc Mdi
  replace Lc (x) (mx : x ∈ g) : L x = c := by
    simp_rw [g, mem_image] at mx
    obtain ⟨i, -, rfl⟩ := mx
    exact Lc i
  have nk : k ≠ 0 := fun contra ↦ by
    simp_rw [contra, zero_smul, zero_apply, le_rfl, implies_true, and_true, Set.ofPred_mem_eq] at hM
    have mp := subset_convexHull ℝ _ (show p ∈ g ∪ {p, q} by simp)
    rw [← hM, mem_convexHull'] at mp
    obtain ⟨w, -, sw, cw⟩ := mp
    apply_fun L at cw
    simp_rw [map_sum, map_smul, smul_eq_mul] at cw
    rw [sum_congr (g := (w · * c)) rfl fun x mx ↦ by rw [Lc _ mx], ← sum_mul, sw, one_mul] at cw
    exact Lp.ne' cw
  replace hM (x) (mx : x ∈ convexHull ℝ ↑(g ∪ {p, q})) : (k • L) x ≤ d :=
    Md _ mr ▸ (hM ▸ subset_convexHull ℝ _ mr).2 x mx
  simp only [smul_apply, smul_eq_mul] at Md hM
  have Mp : k * L p ≤ d := hM _ (subset_convexHull ℝ _ (by simp))
  have Mq : k * L q ≤ d := hM _ (subset_convexHull ℝ _ (by simp))
  rw [← Md _ mr, Lc _ mr] at Mp Mq
  obtain hk | hk := nk.lt_or_gt
  · rw [mul_le_mul_left_of_neg hk, ← not_lt] at Mp
    exact Mp Lp
  · rw [mul_le_mul_iff_right₀ hk, ← not_lt] at Mq
    exact Mq Lq

theorem not_isFace_of_bracketing_points
    {P : ConvexPolytope n} {L : StrongDual ℝ (E n)} {f : Fin n → E n} {c : ℝ} {p q : E n}
    (sf : univ.image f ∪ {p, q} ⊆ P.vertices) (aif : AffineIndependent ℝ f)
    (Lc : ∀ i, L (f i) = c) (Lp : L p < c) (Lq : c < L q) :
    ¬P.IsFace (convexHull ℝ (univ.image f)) := by
  obtain rfl | nzn := eq_zero_or_neZero n
  · simp [ConvexPolytope.IsFace]
  rw [ConvexPolytope.IsFace, not_and_or]
  left
  have key := not_isExposed_of_bracketing_points aif Lc Lp Lq
  contrapose key
  exact key.mono (convexHull_mono sf) (convexHull_mono subset_union_left)
