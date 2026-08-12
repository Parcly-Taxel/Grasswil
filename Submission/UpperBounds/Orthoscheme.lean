import Submission.Face.Flag
import Submission.Symmetry

open Real Finset

namespace LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {n : ℕ} {P : ConvexPolytope n} (rP : P.IsRegular) {F G : P.Flag} {i j : Fin n}

variable (F) in
/-- The baryplex (barycentric simplex) associated with the given flag:
vertex `i` is the centroid of the `i`-dimensional face. -/
noncomputable def Flag.baryplex (i : Fin (n + 1)) : E n :=
  (i.lastCases P.vertices fun j ↦ faceGens (F.isFace j).1 : Finset (E n)).centroid ℝ id

variable (F i) in
/-- The vector from vertex `i` to vertex `i + 1` of `F.baryplex`. -/
noncomputable def Flag.baryplexVec : E n :=
  F.baryplex i.succ - F.baryplex i.castSucc

lemma image_baryplex {φ : Isom n} (sφ : P.isSymmetry φ) (imφ : ∀ k, φ '' F.face k = G.face k)
    {i : Fin (n + 1)} : φ (F.baryplex i) = G.baryplex i := by
  cases i using Fin.lastCases with
  | last => simpa [Flag.baryplex] using sφ.map_centroid
  | cast i =>
    simp_rw [Flag.baryplex, Fin.lastCases_castSucc,
      isom_image_centroid _ (nonempty_faceGens (F.isFace i))]
    congr 1
    rw [← coe_inj, coe_image, self_eq_exch_of_subset (faceGens_subset_vertices (F.isFace i).1),
      self_eq_exch_of_subset (faceGens_subset_vertices (G.isFace i).1), ← convexHull_faceGens,
      ← convexHull_faceGens, ← imφ, isom_image_extremePoints]

include rP in
theorem norm_baryplexVec_invariant : ‖F.baryplexVec i‖ = ‖G.baryplexVec i‖ := by
  obtain ⟨φ, sφ, imφ⟩ := rP.2 F G
  have key := φ.isometry.dist_eq (F.baryplex i.succ) (F.baryplex i.castSucc)
  simp_rw [image_baryplex sφ imφ] at key
  exact key.symm

lemma baryplex_castSucc_mem_face : F.baryplex i.castSucc ∈ F.face i := by
  rw [convexHull_faceGens (F.isFace i).1, Flag.baryplex, Fin.lastCases_castSucc]
  exact centroid_mem_convexHull _ (nonempty_faceGens (F.isFace i))

lemma baryplexVec_mem_vectorSpan (h : i < j) : F.baryplexVec i ∈ vectorSpan ℝ (F.face j) := by
  obtain ⟨k, hk₁, hk₂⟩ : ∃ k : Fin n, i.1 + 1 = k.1 ∧ i.succ = k.castSucc :=
    ⟨⟨i + 1, by lia⟩, rfl, rfl⟩
  have mi := (F.strict_mono _ _ h).subset baryplex_castSucc_mem_face
  have sk : F.face k ⊆ F.face j := F.mono (by lia)
  convert vsub_mem_vectorSpan ℝ (sk baryplex_castSucc_mem_face) mi
  rw [Flag.baryplexVec, hk₂, vsub_eq_sub]

lemma baryplex_agree (h : ∀ j ≥ i, F.face j = G.face j) {j : Fin (n + 1)} (gj : i.castSucc ≤ j) :
    F.baryplex j = G.baryplex j := by
  simp only [Flag.baryplex]
  cases j using Fin.lastCases with
  | last => simp
  | cast j => simp [h _ (by simpa using gj)]

include rP in
lemma baryplexVec_orthogonal_vectorSpan_aux
    {v w : E n} (hv : v ∈ faceGens (F.isFace i).1) (hw : w ∈ faceGens (F.isFace i).1) :
    ∃ φ : Isom n, φ (F.baryplex i.succ) = F.baryplex i.succ ∧
      φ (F.baryplex i.castSucc) = F.baryplex i.castSucc ∧ φ v = w := by
  obtain ⟨Gv, aGv, Gv₀⟩ := exists_substitute_vertex_flag hv
  obtain ⟨Gw, aGw, Gw₀⟩ := exists_substitute_vertex_flag hw
  obtain ⟨φ, sφ, imφ⟩ := rP.2 Gv Gw
  refine ⟨φ, ?_, ?_, ?_⟩
  · nth_rw 1 [baryplex_agree aGv i.castSucc_lt_succ.le, image_baryplex sφ imφ,
      ← baryplex_agree aGw i.castSucc_lt_succ.le]
  · nth_rw 1 [baryplex_agree aGv le_rfl, image_baryplex sφ imφ, ← baryplex_agree aGw le_rfl]
  · have φ₀ := imφ ⟨0, i.pos⟩
    rwa [Gv₀, Gw₀, Set.image_singleton, Set.singleton_eq_singleton_iff] at φ₀

include rP in
lemma baryplexVec_orthogonal_vectorSpan {v : E n} (mv : v ∈ vectorSpan ℝ (F.face i)) :
    inner ℝ (F.baryplexVec i) v = 0 := by
  rw [convexHull_faceGens (F.isFace i).1, vectorSpan_convexHull_eq_vectorSpan] at mv
  set s := faceGens (F.isFace i).1 with hs
  suffices ∀ a ∈ s, ∀ b ∈ s, inner ℝ (F.baryplexVec i) (a - F.baryplex i.castSucc) =
      inner ℝ (F.baryplexVec i) (b - F.baryplex i.castSucc) by
    induction mv using Submodule.span_induction with
    | mem x mx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := mx
      simp_rw [vsub_eq_sub, ← sub_sub_sub_cancel_right a b (F.baryplex i.castSucc)]
      rw [inner_sub_right, sub_eq_zero]
      exact this _ ha _ hb
    | zero => simp
    | add x y _ _ hx hy => simp [inner_add_right, hx, hy]
    | smul c x _ hx => simp [inner_smul_right, hx]
  intro a ha b hb
  obtain ⟨φ, φ₁, φ₀, φa⟩ := baryplexVec_orthogonal_vectorSpan_aux rP ha hb
  have e₁ : φ.linearIsometryEquiv (F.baryplex i.succ - F.baryplex i.castSucc) = φ _ - φ _ :=
    φ.map_vsub ..
  have e₂ : φ.linearIsometryEquiv (a - F.baryplex i.castSucc) = φ _ - φ _ := φ.map_vsub ..
  rw [← φ.linearIsometryEquiv.inner_map_map, Flag.baryplexVec, e₁, φ₁, φ₀, e₂, φa, φ₀]

include rP in
theorem baryplexVec_pairwise_orthogonal :
    Pairwise fun i j ↦ inner ℝ (F.baryplexVec i) (F.baryplexVec j) = 0 :=
  Pairwise.of_gt fun _ _ l ↦ baryplexVec_orthogonal_vectorSpan rP (baryplexVec_mem_vectorSpan l)

lemma baryplex_succ_notMem (dP : P.IsFullDim) : F.baryplex i.succ ∉ F.face i := by
  obtain ⟨L, c, LP, feq⟩ := (F.isFace i).1.exists_dual_eq (F.isFace i).2
  rw [feq, Set.mem_ofPred, not_and_or, Flag.baryplex]
  set s : Finset (E n) := i.succ.lastCases P.vertices fun j ↦ faceGens (F.isFace j).1
  have ns : s.Nonempty := by
    cases hi : i.succ using Fin.lastCases with
    | last => simp [s, hi, P.vertices_nonempty]
    | cast j => simp [s, hi, nonempty_faceGens (F.isFace j)]
  have ss : s ⊆ P.vertices := by
    cases hi : i.succ using Fin.lastCases <;> simp [s, hi, faceGens_subset_vertices]
  refine .inr (ne_of_lt ?_)
  simp_rw [centroid_eq_inv_smul_sum ns, map_smul, map_sum, id_eq]
  rw [inv_smul_lt_iff_of_pos (by simp [ns]), Nat.cast_smul_eq_nsmul, ← sum_const]
  apply sum_lt_sum fun v mv ↦ LP v (subset_convexHull ℝ _ (ss mv))
  obtain ⟨w, mw, nw⟩ : ∃ w ∈ s, w ∉ F.face i := by
    by_contra! contra
    have chs := convexHull_min contra ((F.isFace i).1.convex (convex_convexHull ℝ _))
    cases hi : i.succ using Fin.lastCases with
    | last =>
      simp_rw [s, hi, Fin.lastCases_last] at chs
      have df : faceDim (F.face i) = P.dim :=
        congr(faceDim $(subset_antisymm (F.isFace i).1.subset chs))
      rw [F.dim_eq i, dP] at df
      lia
    | cast j =>
      simp_rw [s, hi, Fin.lastCases_castSucc, ← convexHull_faceGens] at chs
      exact (F.strict_mono _ _ (Fin.succ_lt_succ_iff.mp (hi ▸ Fin.castSucc_lt_succ))).not_subset chs
  refine ⟨w, mw, (LP w (subset_convexHull ℝ _ (ss mw))).lt_of_ne ?_⟩
  rw [feq, Set.mem_ofPred, not_and] at nw
  exact nw (subset_convexHull ℝ _ (ss mw))

include rP in
variable (i) in
theorem norm_baryplexVec_pos : 0 < ‖F.baryplexVec i‖ := by
  rw [norm_pos_iff, Flag.baryplexVec, sub_ne_zero]
  exact fun h ↦ baryplex_succ_notMem rP.1 (h ▸ @baryplex_castSucc_mem_face _ _ F i)

open Matrix

variable (F) in
/-- The square matrix whose **column** `c` is `v_{c.rev} - v_n`,
where `v_0, ..., v_n` are the vertices of `F.baryplex`.
The reversal puts the polytope's origin (fixed by all symmetries) in "front". -/
noncomputable def Flag.baryplexMatrix : Matrix (Fin n) (Fin n) ℝ :=
  of fun r c ↦ (F.baryplex c.rev.castSucc - F.baryplex (Fin.last n)) r

lemma inv_baryplexMatrix_orthogonal (h : i ≠ j.rev) :
    inner ℝ (WithLp.toLp 2 (F.baryplexMatrix⁻¹.row i) : E n)
      (F.baryplex j.castSucc - F.baryplex (Fin.last n)) = 0 := by
  have l₁ (k) : (F.baryplex j.castSucc - F.baryplex (Fin.last n)).ofLp k =
      F.baryplexMatrix k j.rev := by simp [Flag.baryplexMatrix]
  have l₂ : inner ℝ (WithLp.toLp 2 (F.baryplexMatrix⁻¹.row i) : E n)
      (F.baryplex j.castSucc - F.baryplex (Fin.last n)) =
      ∑ k, F.baryplexMatrix⁻¹ i k * F.baryplexMatrix k j.rev := by
    rw [PiLp.inner_apply]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [l₁, inner_apply, WithLp.ofLp_toLp, row_apply]
  rw [l₂, ← mul_apply]
  by_cases ud : IsUnit F.baryplexMatrix.det
  · rw [nonsing_inv_mul _ ud, one_apply, if_neg h]
  · rw [nonsing_inv_apply_not_isUnit _ ud, zero_mul, Matrix.zero_apply]

variable (F) in
/-- The orthogonal matrix in the QR decomposition of `baryplexMatrix`. -/
noncomputable def Flag.Q : Matrix (Fin n) (Fin n) ℝ :=
  of fun r c ↦ -(‖F.baryplexVec c.rev‖⁻¹ • F.baryplexVec c.rev) r

include rP in
lemma orthogonal_Q : F.Q ∈ orthogonalGroup (Fin n) ℝ := by
  rw [mem_orthogonalGroup_iff']
  ext i j
  rw [mul_apply, one_apply]
  have l₁ (k) : F.Qᵀ i k * F.Q k j = ‖F.baryplexVec i.rev‖⁻¹ * ‖F.baryplexVec j.rev‖⁻¹ *
      (F.baryplexVec i.rev k * F.baryplexVec j.rev k) := by
    simp_rw [Flag.Q, transpose_apply, of_apply, PiLp.smul_apply]
    ring
  have l₂ : ∑ k, F.baryplexVec i.rev k * F.baryplexVec j.rev k =
      inner ℝ (F.baryplexVec i.rev) (F.baryplexVec j.rev) := by
    simp_rw [PiLp.inner_apply, inner_apply]
  rw [sum_congr rfl fun k _ ↦ l₁ k, ← mul_sum, l₂]
  rcases eq_or_ne i j with rfl | hn
  · rw [if_pos rfl, real_inner_self_eq_norm_sq, ← sq, ← mul_pow,
      inv_mul_cancel₀ (norm_baryplexVec_pos rP i.rev).ne', one_pow]
  · rw [if_neg hn, baryplexVec_pairwise_orthogonal rP (Fin.rev_injective.ne hn), mul_zero]

lemma sum_baryplexVec_rev_Iic : ∑ j ∈ Iic i, F.baryplexVec j.rev =
    F.baryplex (Fin.last n) - F.baryplex i.rev.castSucc := by
  conv_lhs =>
    enter [2, j]
    rw [Flag.baryplexVec, ← Fin.rev_castSucc, ← Fin.rev_succ, ← neg_sub]
  rw [sum_neg_distrib, Fin.sum_Iic_sub _ fun j ↦ F.baryplex j.rev, neg_sub, Fin.rev_succ,
    Fin.rev_zero]

include rP in
lemma baryplexMatrix_eq_Q_mul :
    F.baryplexMatrix = F.Q * of fun i j ↦ if i ≤ j then ‖F.baryplexVec i.rev‖ else 0 := by
  ext i j
  simp_rw [mul_apply, Flag.Q, of_apply, PiLp.smul_apply, smul_eq_mul, mul_ite, mul_zero]
  conv_rhs =>
    enter [2, k]
    rw [neg_mul, mul_rotate, mul_inv_cancel_right₀ (norm_baryplexVec_pos rP k.rev).ne']
  rw [← sum_filter, filter_ge_eq_Iic, sum_neg_distrib, ← Finset.sum_apply, ← WithLp.ofLp_sum]
  simp [sum_baryplexVec_rev_Iic, Flag.baryplexMatrix]

lemma tri_mul_bidiag_eq_one {c : Fin n → ℝ} (nzc : ∀ i, c i ≠ 0) :
    (of fun (i j : Fin n) ↦ if i ≤ j then c i else 0) *
    (of fun i j ↦ if i = j then (c j)⁻¹ else if i.1 + 1 = j.1 then -(c j)⁻¹ else 0) = 1 := by
  ext i k
  simp_rw [mul_apply, one_apply, of_apply, ite_mul, zero_mul, mul_ite, mul_zero, mul_neg,
    sum_ite, sum_const_zero, add_zero, filter_comm, filter_eq', mem_univ, ite_true]
  rw [sum_filter, sum_singleton]
  have ab (j) : j.1 + 1 = k.1 ∧ ¬j = k ↔ j.1 + 1 = k.1 := by lia
  simp_rw [filter_filter, ab]
  by_cases l : k ≤ i
  · have emp (j) : ¬(j.1 + 1 = k.1 ∧ i ≤ j) := by lia
    simp_rw [emp, filter_false, sum_empty, add_zero]
    by_cases e : i = k
    · rw [if_pos e.le, if_pos e, e, mul_inv_cancel₀ (nzc _)]
    · rw [if_neg (by lia), if_neg e]
  · rw [if_pos (by lia), if_neg (by lia)]
    have unq (j) : j.1 + 1 = k.1 ∧ i ≤ j ↔ j = ⟨k.1 - 1, by lia⟩ := by grind
    simp [unq, filter_eq']

include rP in
lemma inv_baryplexMatrix_eq : F.baryplexMatrix⁻¹ =
    (of fun i j ↦ if i = j then ‖F.baryplexVec j.rev‖⁻¹ else
      if i.1 + 1 = j.1 then -‖F.baryplexVec j.rev‖⁻¹ else 0) * F.Qᵀ := by
  apply inv_eq_right_inv
  rw [baryplexMatrix_eq_Q_mul rP, mul_assoc, ← mul_assoc _ _ F.Qᵀ,
    tri_mul_bidiag_eq_one fun _ ↦ (norm_baryplexVec_pos rP _).ne', one_mul]
  exact (mem_orthogonalGroup_iff ..).mp (orthogonal_Q rP)

include rP in
lemma norm_sq_row_inv_baryplexMatrix : ‖WithLp.toLp 2 (F.baryplexMatrix⁻¹.row i)‖ ^ 2 =
    ‖F.baryplexVec i.rev‖⁻¹ ^ 2 +
    if h : i.1 + 1 < n then ‖F.baryplexVec (Fin.rev ⟨_, h⟩)‖⁻¹ ^ 2 else 0 := by
  have rearr : ‖WithLp.toLp 2 (F.baryplexMatrix⁻¹.row i)‖ ^ 2 =
      (F.baryplexMatrix⁻¹ * F.baryplexMatrix⁻¹.transpose) i i := by
    simp_rw [EuclideanSpace.norm_sq_eq, ← real_inner_self_eq_norm_sq, inner_apply, row_apply,
      mul_apply, transpose_apply]
  rw [rearr, inv_baryplexMatrix_eq rP, transpose_mul, transpose_transpose, ← mul_assoc,
    mul_assoc _ _ F.Q, (mem_orthogonalGroup_iff' ..).mp (orthogonal_Q rP), mul_one]
  simp_rw [mul_apply, transpose_apply, of_apply, ← sq, ite_pow, neg_sq, zero_pow two_ne_zero]
  rw [sum_ite, filter_eq, if_pos (mem_univ _), sum_singleton, add_right_inj]
  have ab (j) : ¬i = j ∧ i.1 + 1 = j.1 ↔ i.1 + 1 = j.1 := by lia
  simp_rw [sum_ite, sum_const_zero, add_zero, filter_filter, ab]
  split_ifs with h
  · have prom (j : Fin n) : i.1 + 1 = j.1 ↔ j = ⟨_, h⟩ := by rw [Fin.ext_iff]; lia
    simp_rw [prom, filter_eq', if_pos (mem_univ _), sum_singleton]
  · exact sum_eq_zero fun j mj ↦ absurd ((mem_filter.mp mj).2 ▸ j.2) h

include rP in
theorem norm_row_inv_baryplexMatrix_invariant :
    ‖WithLp.toLp 2 (F.baryplexMatrix⁻¹.row i)‖ = ‖WithLp.toLp 2 (G.baryplexMatrix⁻¹.row i)‖ := by
  have linvar (i) : ‖F.baryplexVec i‖ = ‖G.baryplexVec i‖ := norm_baryplexVec_invariant rP
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp [linvar, norm_sq_row_inv_baryplexMatrix rP]

include rP in
lemma isUnit_inv_baryplexMatrix : IsUnit F.baryplexMatrix⁻¹ := by
  rw [isUnit_nonsing_inv_iff, baryplexMatrix_eq_Q_mul rP]
  apply (IsUnit.of_mul_eq_one _ (F.Q.mem_orthogonalGroup_iff.mp (orthogonal_Q rP))).mul
  rw [isUnit_iff_isUnit_det, det_of_isUpperTriangular fun _ _ _ ↦ by simp_all]
  simp_rw [of_apply, if_pos le_rfl, IsUnit.prod_univ_iff, isUnit_iff_ne_zero]
  exact fun _ ↦ (norm_baryplexVec_pos rP _).ne'

include rP in
lemma inv_norm_row_inv_baryplexMatrix_ne_zero :
    ‖WithLp.toLp 2 (F.baryplexMatrix⁻¹.row i)‖⁻¹ ≠ 0 := by
  have uM : IsUnit F.baryplexMatrix⁻¹ := isUnit_inv_baryplexMatrix rP
  simp_rw [Ne, inv_eq_zero, norm_eq_zero, WithLp.toLp_eq_zero]
  intro contra
  rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at uM
  exact uM (det_eq_zero_of_row_eq_zero i (congr_fun contra))

variable (F) in
/-- `baryplexMatrix⁻¹` with the rows normalised
(i.e. **norm**alised **I**nverse **B**aryplex **M**atrix). -/
noncomputable def Flag.normIBM : Matrix (Fin n) (Fin n) ℝ :=
  (diagonal fun i ↦ ‖WithLp.toLp 2 (F.baryplexMatrix⁻¹.row i)‖⁻¹) * F.baryplexMatrix⁻¹

include rP in
lemma norm_normIBM_row_eq_one : ‖WithLp.toLp 2 (F.normIBM.row i)‖ = 1 := by
  have nz := inv_norm_row_inv_baryplexMatrix_ne_zero rP (F := F) (i := i)
  simp_rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow, EuclideanSpace.norm_sq_eq, row_apply,
    norm_eq_abs, sq_abs, Flag.normIBM, diagonal_mul, mul_pow, ← mul_sum]
  rw [mul_comm, mul_eq_one_iff_eq_inv₀ (by positivity), inv_pow, inv_inv]
  simp_rw [EuclideanSpace.norm_sq_eq, row_apply, norm_eq_abs, sq_abs]

include rP in
theorem normIBM_mul_transpose_invariant : F.normIBM * F.normIBMᵀ = G.normIBM * G.normIBMᵀ := by
  conv_lhs => rw [Flag.normIBM, transpose_mul, ← mul_assoc, mul_assoc _ F.baryplexMatrix⁻¹]
  conv_rhs => rw [Flag.normIBM, transpose_mul, ← mul_assoc, mul_assoc _ G.baryplexMatrix⁻¹]
  have ninvar (i) : ‖WithLp.toLp 2 (F.baryplexMatrix⁻¹.row i)‖ =
      ‖WithLp.toLp 2 (G.baryplexMatrix⁻¹.row i)‖ := norm_row_inv_baryplexMatrix_invariant rP
  simp_rw [ninvar]
  congr 2
  conv_lhs => rw [inv_baryplexMatrix_eq rP, transpose_mul, ← mul_assoc, transpose_transpose,
    mul_assoc _ _ F.Q, (mem_orthogonalGroup_iff' ..).mp (orthogonal_Q rP), mul_one]
  conv_rhs => rw [inv_baryplexMatrix_eq rP, transpose_mul, ← mul_assoc, transpose_transpose,
    mul_assoc _ _ G.Q, (mem_orthogonalGroup_iff' ..).mp (orthogonal_Q rP), mul_one]
  have linvar (i) : ‖F.baryplexVec i‖ = ‖G.baryplexVec i‖ := norm_baryplexVec_invariant rP
  simp [linvar]

/-- The matrix of dot products of `normIBM`'s rows, i.e. the negative cosines of dihedral angles
between hyperplanes of the regular polytope's characteristic orthoscheme.
This is well-defined by `normIBM_mul_transpose_invariant`. -/
noncomputable def IsRegular.cosineMatrix : Matrix (Fin n) (Fin n) ℝ :=
  rP.1.flag.normIBM * rP.1.flag.normIBMᵀ

lemma posDef_cosineMatrix : rP.cosineMatrix.PosDef := by
  convert PosDef.mul_conjTranspose_self rP.1.flag.normIBM _
  · rw [conjTranspose_eq_transpose_of_trivial, IsRegular.cosineMatrix]
  apply vecMul_injective_of_isUnit
  refine IsUnit.mul ?_ (isUnit_inv_baryplexMatrix rP)
  simp_rw [isUnit_diagonal, Pi.isUnit_iff, isUnit_iff_ne_zero]
  exact fun _ ↦ inv_norm_row_inv_baryplexMatrix_ne_zero rP

lemma cosineMatrix_apply :
    let B := of fun (i j : Fin n) ↦ if i = j then ‖rP.1.flag.baryplexVec j.rev‖⁻¹ else
      if i.1 + 1 = j.1 then -‖rP.1.flag.baryplexVec j.rev‖⁻¹ else 0
    rP.cosineMatrix i j =
    ‖WithLp.toLp 2 (rP.1.flag.baryplexMatrix⁻¹.row i)‖⁻¹ *
    ‖WithLp.toLp 2 (rP.1.flag.baryplexMatrix⁻¹.row j)‖⁻¹ *
    inner ℝ (WithLp.toLp 2 (B.row i)) (WithLp.toLp 2 (B.row j)) := by
  intro B
  rw [IsRegular.cosineMatrix, Flag.normIBM, mul_apply]
  conv_lhs =>
    enter [2, k]
    rw [transpose_apply, diagonal_mul, diagonal_mul, mul_mul_mul_comm]
  rw [← mul_sum, PiLp.inner_apply]
  congr 1
  rw [inv_baryplexMatrix_eq rP]
  change ∑ k, (B * rP.1.flag.Qᵀ) i k * (B * rP.1.flag.Qᵀ) j k = _
  conv_lhs =>
    enter [2, k, 2]
    rw [← (B * rP.1.flag.Qᵀ).transpose_transpose, transpose_apply, transpose_mul,
      transpose_transpose]
  rw [← mul_apply, ← mul_assoc, mul_assoc B,
    rP.1.flag.Q.mem_orthogonalGroup_iff'.mp (orthogonal_Q rP), mul_one, mul_apply]
  simp only [inner_apply, transpose_apply, row_apply]

lemma cosineMatrix_apply_self : rP.cosineMatrix i i = 1 := by
  have key := norm_sq_row_inv_baryplexMatrix rP (F := rP.1.flag) (i := i)
  rw [IsRegular.cosineMatrix, Flag.normIBM, mul_apply]
  simp_rw [transpose_apply, diagonal_mul, ← sq, mul_pow, ← mul_sum, inv_pow]
  simp_rw [EuclideanSpace.real_norm_sq_eq] at key ⊢
  refine inv_mul_cancel₀ (key ▸ (add_pos_of_pos_of_nonneg ?_ ?_).ne')
  · exact sq_pos_of_pos (inv_pos.mpr (norm_baryplexVec_pos rP _))
  · split_ifs <;> simp

lemma cosineMatrix_apply_far (h : i.1 + 1 < j.1) : rP.cosineMatrix i j = 0 := by
  rw [cosineMatrix_apply, PiLp.inner_apply]
  refine mul_eq_zero_of_right _ (Fintype.sum_eq_zero _ fun k ↦ ?_)
  simp_rw [row_apply, of_apply, inner_apply]
  by_cases hi : i = k
  · subst k
    rw [if_pos rfl, if_neg (show j ≠ i by lia), if_neg (show j.1 + 1 ≠ i.1 by lia), mul_zero]
  · rw [if_neg hi]
    by_cases hi' : i.1 + 1 = k.1
    · rw [if_pos hi', if_neg (show j ≠ k by lia), if_neg (show j.1 + 1 ≠ k.1 by lia), mul_zero]
    · rw [if_neg hi', zero_mul]

lemma cosineMatrix_apply_near (h : i.1 + 1 = j.1) : rP.cosineMatrix i j < 0 := by
  simp_rw [cosineMatrix_apply, PiLp.inner_apply, row_apply, of_apply, inner_apply]
  refine mul_neg_of_pos_of_neg (lt_of_le_of_ne (by positivity) ?_) ?_
  · refine (mul_ne_zero ?_ ?_).symm <;> exact inv_norm_row_inv_baryplexMatrix_ne_zero rP
  let f (k : Fin n) :=
    (if i = k then ‖rP.1.flag.baryplexVec k.rev‖⁻¹ else
      if i.1 + 1 = k.1 then -‖rP.1.flag.baryplexVec k.rev‖⁻¹ else 0) *
    (if j = k then ‖rP.1.flag.baryplexVec k.rev‖⁻¹ else
      if j.1 + 1 = k.1 then -‖rP.1.flag.baryplexVec k.rev‖⁻¹ else 0)
  change ∑ k, f k < 0
  have hf (k) (hk : k ≠ j) : f k = 0 := by
    simp_rw [f, if_neg hk.symm, if_neg (show i.1 + 1 ≠ k.1 by lia)]
    obtain hk' | hk' : i ≠ k ∨ j.1 + 1 ≠ k.1 := by lia
    · rw [if_neg hk', zero_mul]
    · rw [if_neg hk', mul_zero]
  simp_rw [Fintype.sum_eq_single _ hf, f, if_neg (show i ≠ j by lia), if_pos h, ite_true,
    neg_mul, Left.neg_neg_iff, mul_self_pos, Ne, inv_eq_zero]
  exact (norm_baryplexVec_pos rP _).ne'

lemma neg_one_lt_cosineMatrix : -1 < rP.cosineMatrix i j := by
  obtain rfl | nij := eq_or_ne i j
  · simp [cosineMatrix_apply_self]
  have rearr : rP.cosineMatrix i j = inner ℝ (WithLp.toLp 2 (rP.1.flag.normIBM.row i))
      (WithLp.toLp 2 (rP.1.flag.normIBM.row j)) := by
    rw [IsRegular.cosineMatrix, mul_apply, PiLp.inner_apply]
    simp [mul_comm]
  have n1 {i} : ‖WithLp.toLp 2 (rP.1.flag.normIBM.row i)‖ = 1 := norm_normIBM_row_eq_one rP
  rw [rearr]
  refine (neg_one_le_real_inner_of_norm_eq_one n1 n1).lt_of_ne' fun hc ↦ ?_
  simp_rw [inner_eq_neg_one_iff_of_norm_eq_one n1 n1, ← WithLp.toLp_neg, PiLp.ext_iff, Pi.neg_apply,
    row_apply, Flag.normIBM, diagonal_mul] at hc
  have dnz := isUnit_inv_baryplexMatrix rP (F := rP.1.flag)
  rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at dnz
  apply dnz
  set B := rP.1.flag.baryplexMatrix⁻¹
  rw [← B.det_updateRow_add_smul_self nij (‖WithLp.toLp 2 (B.row i)‖ / ‖WithLp.toLp 2 (B.row j)‖)]
  refine det_eq_zero_of_row_eq_zero i fun k ↦ ?_
  have q : ‖WithLp.toLp 2 (B.row i)‖ ≠ 0 := by
    rw [← inv_inv ‖_‖]
    exact inv_ne_zero (inv_norm_row_inv_baryplexMatrix_ne_zero rP)
  rw [updateRow_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_mul_comm, ← neg_neg (_ / _),
    div_eq_inv_mul, ← hc, neg_mul, mul_right_comm, inv_mul_cancel₀ q, one_mul, add_neg_eq_zero]

section Similar

variable {Q : ConvexPolytope n} (rQ : Q.IsRegular) {G : Q.Flag}

lemma faceGens_image_of_face_eq (e : E n ≃ᵃ[ℝ] E n)
    (hvert : Q.vertices = P.vertices.image e) {sF sG : Set (E n)}
    (hF : P.IsFace sF) (hG : Q.IsFace sG) (hface : sG = e '' sF) :
    faceGens hG.1 = (faceGens hF.1).image e := by
  obtain ⟨g, _, huq⟩ := existsUnique_faceGens hG.1
  have h1 : faceGens hG.1 ⊆ Q.vertices := faceGens_subset_vertices hG.1
  have h1eq : sG = convexHull ℝ (faceGens hG.1) := convexHull_faceGens hG.1
  have h2sub : (faceGens hF.1).image e ⊆ Q.vertices := by
    rw [hvert]
    exact image_subset_image (faceGens_subset_vertices hF.1)
  have hFeq : sF = convexHull ℝ (faceGens hF.1) := convexHull_faceGens hF.1
  have h2eq : sG = convexHull ℝ ((faceGens hF.1).image e) := by
    rw [hface]
    have hc : e '' sF = e '' convexHull ℝ (faceGens hF.1) := by congr 1
    rw [hc, coe_image]
    exact (e.toAffineMap.image_convexHull _).symm ▸ rfl
  rw [huq _ ⟨h1, h1eq⟩, huq _ ⟨h2sub, h2eq⟩]

lemma similar_baryplex (e : E n ≃ᵃ[ℝ] E n) (hvert : Q.vertices = P.vertices.image e)
    (hgens : ∀ j, faceGens (G.isFace j).1 = (faceGens (F.isFace j).1).image e)
    (i : Fin (n + 1)) : G.baryplex i = e (F.baryplex i) := by
  cases i using Fin.lastCases with
  | last =>
    simp only [Flag.baryplex, Fin.lastCases_last]
    rw [affineEquiv_image_centroid e P.vertices_nonempty, hvert]
  | cast j =>
    simp only [Flag.baryplex, Fin.lastCases_castSucc]
    rw [affineEquiv_image_centroid e (nonempty_faceGens (F.isFace j)), hgens]

lemma norm_baryplexVec_similar {a : ℝ} (ha : 0 < a) {φ : Isom n}
    (hbary : ∀ k, G.baryplex k = a • φ (F.baryplex k)) (i : Fin n) :
    ‖G.baryplexVec i‖ = a * ‖F.baryplexVec i‖ := by
  simp_rw [Flag.baryplexVec, hbary, ← smul_sub, norm_smul, norm_of_nonneg ha.le, ← dist_eq_norm,
    φ.isometry.dist_eq]

include rP rQ in
lemma norm_row_inv_baryplexMatrix_smul {a : ℝ} (ha : 0 < a)
    (hnorm : ∀ i, ‖G.baryplexVec i‖ = a * ‖F.baryplexVec i‖) (i : Fin n) :
    ‖WithLp.toLp 2 (G.baryplexMatrix⁻¹.row i)‖ =
    a⁻¹ * ‖WithLp.toLp 2 (F.baryplexMatrix⁻¹.row i)‖ := by
  have hsqQ := norm_sq_row_inv_baryplexMatrix (F := G) (i := i) rQ
  have hsqP := norm_sq_row_inv_baryplexMatrix (F := F) (i := i) rP
  have hsq : ‖WithLp.toLp 2 (G.baryplexMatrix⁻¹.row i)‖ ^ 2 =
      a⁻¹ ^ 2 * ‖WithLp.toLp 2 (F.baryplexMatrix⁻¹.row i)‖ ^ 2 := by
    rw [hsqQ, hsqP, mul_add]
    congr 1
    · rw [hnorm, mul_inv, mul_pow]
    · split_ifs with h
      · rw [hnorm, mul_inv, mul_pow]
      · ring
  nlinarith [hsq, norm_nonneg (WithLp.toLp 2 (G.baryplexMatrix⁻¹.row i)),
    mul_nonneg (inv_nonneg.mpr ha.le)
      (norm_nonneg (WithLp.toLp 2 (F.baryplexMatrix⁻¹.row i))),
    sq_nonneg (‖WithLp.toLp 2 (G.baryplexMatrix⁻¹.row i)‖ -
      a⁻¹ * ‖WithLp.toLp 2 (F.baryplexMatrix⁻¹.row i)‖),
    sq_nonneg (‖WithLp.toLp 2 (G.baryplexMatrix⁻¹.row i)‖ +
      a⁻¹ * ‖WithLp.toLp 2 (F.baryplexMatrix⁻¹.row i)‖)]

include rP in
lemma normIBM_mul_transpose_eq_reduced :
    F.normIBM * F.normIBMᵀ =
      (diagonal (fun i ↦ ‖WithLp.toLp 2 (F.baryplexMatrix⁻¹.row i)‖⁻¹) *
        (of fun i j ↦ if i = j then ‖F.baryplexVec j.rev‖⁻¹
          else if i.1 + 1 = j.1 then -‖F.baryplexVec j.rev‖⁻¹ else 0)) *
      (diagonal (fun i ↦ ‖WithLp.toLp 2 (F.baryplexMatrix⁻¹.row i)‖⁻¹) *
        (of fun i j ↦ if i = j then ‖F.baryplexVec j.rev‖⁻¹
          else if i.1 + 1 = j.1 then -‖F.baryplexVec j.rev‖⁻¹ else 0))ᵀ := by
  have hQ : F.Qᵀ * F.Q = 1 := (mem_orthogonalGroup_iff' ..).mp (orthogonal_Q rP)
  rw [Flag.normIBM, inv_baryplexMatrix_eq rP, ← mul_assoc, mul_transpose_orthogonal_right hQ]

include rP rQ in
lemma normIBM_mul_transpose_smul {a : ℝ} (ha : 0 < a)
    (hnorm : ∀ i, ‖G.baryplexVec i‖ = a * ‖F.baryplexVec i‖) :
    G.normIBM * G.normIBMᵀ = F.normIBM * F.normIBMᵀ := by
  rw [normIBM_mul_transpose_eq_reduced rP, normIBM_mul_transpose_eq_reduced rQ]
  simp_rw [hnorm, mul_inv, ← mul_neg, ← mul_ite_zero, ← mul_ite, ← smul_eq_mul a⁻¹]
  conv_lhs => enter [1, 2, 2, i]; rw [← Pi.smul_def a⁻¹]
  conv_lhs => enter [2, 1, 2, 2, i]; rw [← Pi.smul_def a⁻¹]
  rw [← Pi.smul_def a⁻¹, ← smul_of, mul_smul_comm, ← smul_mul_assoc]
  suffices (a⁻¹ • diagonal fun i ↦ ‖WithLp.toLp 2 (G.baryplexMatrix⁻¹.row i)‖⁻¹) =
      diagonal fun i ↦ ‖WithLp.toLp 2 (F.baryplexMatrix⁻¹.row i)‖⁻¹ by congr
  simp_rw [norm_row_inv_baryplexMatrix_smul rP rQ ha hnorm, mul_inv, inv_inv, ← smul_eq_mul]
  rw [← Pi.smul_def a, diagonal_smul, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]

/-- `x ↦ a • φ x` as an affine equivalence. -/
noncomputable def similarEquiv {a : ℝ} (ha : 0 < a) (φ : Isom n) : E n ≃ᵃ[ℝ] E n :=
  φ.toAffineEquiv.trans
    (LinearEquiv.smulOfUnit ⟨a, a⁻¹, mul_inv_cancel₀ ha.ne', inv_mul_cancel₀ ha.ne'⟩).toAffineEquiv

lemma similarEquiv_apply {a : ℝ} (ha : 0 < a) {φ : Isom n} {x : E n} :
    similarEquiv ha φ x = a • φ x := rfl

theorem cosineMatrix_eq_of_similar (hs : P.Similar Q) : rP.cosineMatrix = rQ.cosineMatrix := by
  obtain ⟨a, ha, φ, hQ⟩ := hs
  set e := similarEquiv ha φ with he
  have hQtoSet : Q.toSet = e '' P.toSet := by
    simp_rw [hQ, he, ← Set.image_comp, Function.comp_apply, similarEquiv_apply]
  have hvert := vertices_eq_image_of_toSet_eq e hQtoSet
  set F := rP.1.flag with hF
  obtain ⟨G, hface⟩ := exists_similar_flag F e hQtoSet
  have hgens (j) : faceGens (G.isFace j).1 = (faceGens (F.isFace j).1).image e :=
    faceGens_image_of_face_eq e hvert (F.isFace j) (G.isFace j) (hface j)
  have hbary (k) : G.baryplex k = a • φ (F.baryplex k) := by
    rw [similar_baryplex e hvert hgens k, he, similarEquiv_apply]
  have e1 : rP.cosineMatrix = F.normIBM * F.normIBMᵀ := rfl
  have e2 : rQ.cosineMatrix = G.normIBM * G.normIBMᵀ := (normIBM_mul_transpose_invariant rQ).symm
  rw [e1, e2, normIBM_mul_transpose_smul rP rQ ha (norm_baryplexVec_similar ha hbary)]

theorem cosineMatrix_eq_iff_similar : P.Similar Q ↔ rP.cosineMatrix = rQ.cosineMatrix := by
  sorry

end Similar

theorem cosineMatrix_eq_neg_cos_pi_div_nat_of_near (h : i.1 + 1 = j.1) :
    ∃ p : ℕ, rP.cosineMatrix i j = -cos (π / p) := by
  sorry

end LeanEval.Geometry.PlatonicClassification.ConvexPolytope
