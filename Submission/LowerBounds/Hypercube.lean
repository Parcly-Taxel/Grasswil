import Submission.LowerBounds.Orthoplex
import Submission.PolarDual

open Real Finset LeanEval.Geometry.PlatonicClassification

variable {n : ℕ}

/-- A function mapping `n` signs to a vertex of the `n`-hypercube. -/
def hypercubeVert (s : Fin n → Bool) : E n :=
  .toLp _ fun i ↦ if s i then -1 else 1

lemma injective_hypercubeVert : hypercubeVert (n := n).Injective := fun s t e ↦ by
  ext i
  replace e := congr($e i)
  simp_rw [hypercubeVert] at e
  grind +revert

variable (n) in
/-- The `n`-hypercube. -/
noncomputable def hypercube : ConvexPolytope n where
  vertices := univ.image hypercubeVert
  vertices_nonempty := by simp
  vertices_eq_extremePoints := by
    refine self_eq_extremePoints_convexHull_of_subset_sphere 0 √n fun p mp ↦ ?_
    rw [mem_coe, mem_image] at mp
    obtain ⟨p, -, rfl⟩ := mp
    simp [hypercubeVert, EuclideanSpace.dist_eq]

/-- Barycentric weight of the hypercube vertex indexed by `s` for the point with
coordinates `v`. -/
noncomputable def cubeWeight (v : Fin n → ℝ) (s : Fin n → Bool) : ℝ :=
  ∏ i, if s i then (1 - v i) / 2 else (1 + v i) / 2

lemma cubeWeight_nonneg {v : Fin n → ℝ} (hv : ∀ i, |v i| ≤ 1) (s : Fin n → Bool) :
    0 ≤ cubeWeight v s :=
  prod_nonneg fun i _ ↦ by split_ifs <;> linarith [abs_le.mp (hv i)]

lemma sum_cubeWeight {v : Fin n → ℝ} : ∑ s, cubeWeight v s = 1 := by
  unfold cubeWeight
  rw [← Fintype.prod_sum fun _ b ↦ if b = true then _ else _]
  refine Fintype.prod_eq_one _ fun i ↦ ?_
  simp only [Fintype.sum_bool, Bool.false_eq_true, reduceIte]
  ring

lemma sum_cubeWeight_smul_apply {v : Fin n → ℝ} {j : Fin n} :
    (∑ s, cubeWeight v s • hypercubeVert s) j = v j := by
  simp_rw [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  unfold hypercubeVert
  let f (i) (b : Bool) : ℝ := if b then (1 - v i) / 2 else (1 + v i) / 2
  let g (i) (b : Bool) : ℝ := if i = j then f i b * (if b then -1 else 1) else f i b
  have rearr (s) : cubeWeight v s * (if s j then -1 else 1) = ∏ i, g i (s i) := by
    rw [Fintype.prod_eq_mul_prod_compl j, cubeWeight, Fintype.prod_eq_mul_prod_compl j]
    have pcon : ∏ i ∈ {j}ᶜ, f i (s i) = ∏ i ∈ {j}ᶜ, g i (s i) :=
      prod_congr rfl fun i hi ↦ by simp_all [g]
    rw [pcon]
    simp only [g, reduceIte]
    ring
  rw [sum_congr rfl fun s _ ↦ rearr s, ← Fintype.prod_sum, Fintype.prod_eq_single j]
  · simp only [f, g, Fintype.sum_bool, Bool.false_eq_true, reduceIte]
    ring
  · intro i hij
    simp only [f, g, hij, Fintype.sum_bool, Bool.false_eq_true, reduceIte]
    ring

lemma hypercube_toSet_eq_box : (hypercube n).toSet = {v | ∀ i, |v i| ≤ 1} := by
  ext v
  refine ⟨fun mv i ↦ ?_, fun h ↦ ?_⟩
  · simp_rw [ConvexPolytope.toSet, hypercube, mem_convexHull', mem_image,
      sum_image injective_hypercubeVert.injOn, mem_univ, true_and, forall_exists_index,
      forall_apply_eq_imp_iff] at mv
    obtain ⟨w, nw, sw, rfl⟩ := mv
    simp_rw [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc
      _ ≤ _ := abs_sum_le_sum_abs ..
      _ = ∑ x, w (hypercubeVert x) * 1 := by
        congr! 1 with s -
        simp_rw [abs_mul, abs_of_nonneg (nw _), hypercubeVert]
        split_ifs <;> simp
      _ = _ := by simp [sw]
  · simp_rw [ConvexPolytope.toSet, hypercube, Fintype.coe_image_univ]
    apply mem_convexHull_of_exists_fintype (cubeWeight v) hypercubeVert
      (cubeWeight_nonneg h) sum_cubeWeight Set.mem_range_self
    ext i
    exact sum_cubeWeight_smul_apply

lemma orthoplex_polar_eq_box [NeZero n] :
    ⋂ v ∈ (orthoplex n).toSet, {w | inner ℝ v w ≤ 1} = {w | ∀ i, |w i| ≤ 1} := by
  rw [ConvexPolytope.toSet, ← iInter_eq_iInter_convexHull_le]
  ext w
  have iov (i b) : inner ℝ (orthoplexVert i b) w = (if b then -1 else 1) * w i := by
    simp_rw [orthoplexVert, PiLp.inner_apply, PiLp.ofLp_single, inner_apply]
    rw [Fintype.sum_eq_single i fun j h ↦ by simp [Pi.single_eq_of_ne h], Pi.single_eq_same]
  have mem_vert (i b) : orthoplexVert i b ∈ (orthoplex n).vertices :=
    mem_image.mpr ⟨(i, b), mem_univ _, rfl⟩
  simp_rw [Set.mem_iInter₂, Set.mem_ofPred, abs_le]
  refine ⟨fun h i ↦ ?_, fun h v mv ↦ ?_⟩
  · have lb := h (orthoplexVert i true) (mem_vert i true)
    have ub := h (orthoplexVert i false) (mem_vert i false)
    simp only [iov, Bool.false_eq_true, reduceIte, one_mul, neg_mul, ← neg_le] at lb ub
    exact ⟨lb, ub⟩
  · rw [orthoplex, mem_image] at mv
    obtain ⟨⟨i, b⟩, -, rfl⟩ := mv
    obtain ⟨lb, ub⟩ := h i
    cases b <;> simp_all [← neg_le]

lemma isPolarDual_orthoplex_hypercube [NeZero n] : IsPolarDual (orthoplex n) (hypercube n) := by
  rw [IsPolarDual, hypercube_toSet_eq_box, orthoplex_polar_eq_box]

theorem hypercube_isRegular [NeZero n] : (hypercube n).IsRegular := by
  refine isPolarDual_orthoplex_hypercube.isRegular orthoplex_isRegular fun φ sφ ↦ ?_
  suffices (orthoplex n).vertices.centroid ℝ id = 0 from this ▸ sφ.map_centroid
  simp_rw [centroid_eq_inv_smul_sum (orthoplex n).vertices_nonempty, smul_eq_zero, id_eq]
  right
  rw [orthoplex, sum_image injective_orthoplexVert.injOn, Fintype.sum_prod_type]
  refine Fintype.sum_eq_zero _ fun i ↦ ?_
  simp [orthoplexVert, ← PiLp.single_add]
