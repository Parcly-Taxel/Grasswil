import Submission.Face.Basic
import Submission.LowerBounds.Lemmas
import Submission.Symmetry

open Real Finset LeanEval.Geometry.PlatonicClassification

variable {n : ℕ} {i j : Fin n}

variable (i) in
/-- A function mapping `i : Fin n` to the `i`-th vertex of a regular `n`-gon. -/
noncomputable def polygonVert : E 2 :=
  !₂[cos (2 * π * i / n), sin (2 * π * i / n)]

lemma polygonVert_mem_sphere : dist 0 (polygonVert i) = 1 := by
  simp [polygonVert, EuclideanSpace.dist_eq]

open Complex in
lemma injective_polygonVert : (polygonVert (n := n)).Injective := fun i j h ↦ by
  have ceq : cexp ((2 * π * i / n : ℝ) * I) = cexp ((2 * π * j / n : ℝ) * I) := by
    simp_rw [polygonVert, WithLp.toLp.injEq, Matrix.vecCons_inj, and_true] at h
    simp_rw [Complex.ext_iff, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
    exact h
  rw [exp_eq_exp_iff_exists_int] at ceq
  obtain ⟨k, hk⟩ := ceq
  push_cast at hk
  rw [← sub_eq_iff_eq_add', show 2 * π * i / n * I - 2 * π * j / n * I =
    (i - j) / n * (2 * π * I) by ring, mul_left_inj' (by simp),
    div_eq_iff (by simpa using i.neZero.1), show (i - j : ℂ) = (i - j : ℤ) by simp,
    show (k * n : ℂ) = (k * n : ℤ) by simp, Int.cast_inj] at hk
  have k0 : k = 0 := by nlinarith [i.2, j.2]
  rwa [k0, zero_mul, sub_eq_zero, Nat.cast_inj, Fin.val_eq_val] at hk

lemma finrank_vectorSpan_image_polygonVert_eq_two {s : Finset (Fin n)} (cs : 3 ≤ #s) :
    Module.finrank ℝ (vectorSpan ℝ (s.image polygonVert : Set (E 2))) = 2 := by
  apply le_antisymm ((Submodule.finrank_le _).trans_eq (by simp))
  obtain ⟨t, st, ct⟩ := exists_subset_card_eq cs
  let f (i : Fin 3) : E 2 := polygonVert ((equivFinOfCardEq ct).symm i).1
  suffices 2 ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range f)) by
    refine this.trans (Submodule.finrank_mono (vectorSpan_mono _ fun p mp ↦ ?_))
    simp_rw [f, Set.mem_range, mem_coe, mem_image] at mp ⊢
    obtain ⟨i, rfl⟩ := mp
    exact ⟨_, st ((equivFinOfCardEq ct).symm i).2, rfl⟩
  rw [← affineIndependent_iff_le_finrank_vectorSpan _ _ rfl]
  refine (EuclideanGeometry.Sphere.mk 0 1).cospherical.affineIndependent (fun p mp ↦ ?_)
    (injective_polygonVert.comp (Subtype.val_injective.comp (Equiv.injective _)))
  obtain ⟨i, -, rfl⟩ := mp
  simp_rw [Metric.mem_sphere, f]
  rw [dist_comm]
  exact polygonVert_mem_sphere

lemma rotate_polygonVert :
    (toIsom (rotate2D (2 * π * i / n)) 0) (polygonVert j) = polygonVert (i + j) := by
  ext c
  have nnz : (n : ℝ) ≠ 0 := by simpa using i.neZero.1
  simp_rw [toIsom_apply, WithLp.ofLp_zero, add_zero, rotate2D, polygonVert]
  fin_cases c <;> norm_num
  on_goal 1 => rw [← sub_eq_add_neg, ← cos_add, cos_eq_cos_iff]
  on_goal 2 => nth_rw 1 [mul_comm (sin _), mul_comm (cos _), ← sin_add, sin_eq_sin_iff]
  all_goals
    refine ⟨-((i + j) / n : ℤ), .inl ?_⟩
    field_simp
    norm_cast
    simp_rw [Fin.val_add, Int.natCast_emod, Int.natCast_ediv, Nat.cast_add]
    grind [Int.emod_add_mul_ediv (i + j) n]

lemma reflect_polygonVert :
    (toIsom (reflect2D (2 * π * i / n)) 0) (polygonVert j) = polygonVert (i - j) := by
  ext c
  have nnz : (n : ℝ) ≠ 0 := by simpa using i.neZero.1
  simp_rw [toIsom_apply, WithLp.ofLp_zero, add_zero, reflect2D, polygonVert]
  fin_cases c <;> norm_num
  on_goal 1 =>
    rw [← cos_sub, cos_eq_cos_iff]
    refine ⟨-((i - j) / n : ℤ), .inr ?_⟩
  on_goal 2 =>
    nth_rw 1 [← sub_eq_add_neg, mul_comm (sin _), mul_comm (cos _), ← sin_sub, sin_eq_sin_iff]
    refine ⟨-((i - j) / n : ℤ), .inl ?_⟩
  all_goals
    field_simp
    norm_cast
    simp_rw [Int.subNatNat_eq_coe, Fin.val_sub, Int.natCast_emod, Nat.cast_add]
    rw [Nat.cast_sub j.2.le, sub_add_comm, Int.add_emod_right]
    grind [Int.emod_add_mul_ediv (i - j) n]

variable (n) in
/-- The regular `n`-gon in the Euclidean plane. -/
noncomputable def regularPolygon [NeZero n] : ConvexPolytope 2 where
  vertices := univ.image (polygonVert (n := n))
  vertices_nonempty := by simp
  vertices_eq_extremePoints := by
    refine self_eq_extremePoints_convexHull_of_subset_sphere 0 1 fun p mp ↦ ?_
    rw [mem_coe, mem_image] at mp
    obtain ⟨i, -, rfl⟩ := mp
    exact polygonVert_mem_sphere

lemma regularPolygon_isFullDim (hn : 3 ≤ n) (nzn : NeZero n := ⟨by lia⟩) :
    (regularPolygon n).IsFullDim := by
  rw [ConvexPolytope.IsFullDim, ConvexPolytope.dim, ConvexPolytope.toSet,
    vectorSpan_convexHull_eq_vectorSpan]
  exact finrank_vectorSpan_image_polygonVert_eq_two (by simpa)

lemma isSymmetry_regularPolygon_rotate (nzn : NeZero n := i.neZero) :
    (regularPolygon n).isSymmetry (toIsom (rotate2D (2 * π * i / n)) 0) := by
  set R := toIsom (rotate2D (2 * π * i / n)) 0
  let vs := (regularPolygon n).vertices
  have im : R '' vs = vs := by
    apply Set.eq_of_subset_of_card_le
    · rw [Set.image_subset_iff]
      intro v hv
      simp only [vs, regularPolygon, mem_coe, mem_image, Set.mem_preimage] at *
      obtain ⟨j, -, rfl⟩ := hv
      exact ⟨i + j, mem_univ _, rotate_polygonVert.symm⟩
    · rw [Set.card_image_of_injective _ R.injective]
  have ch := isom_image_convexHull R vs
  rwa [im] at ch

lemma isSymmetry_regularPolygon_reflect (nzn : NeZero n := i.neZero) :
    (regularPolygon n).isSymmetry (toIsom (reflect2D (2 * π * i / n)) 0) := by
  set R := toIsom (reflect2D (2 * π * i / n)) 0
  let vs := (regularPolygon n).vertices
  have im : R '' vs = vs := by
    apply Set.eq_of_subset_of_card_le
    · rw [Set.image_subset_iff]
      intro v hv
      simp only [vs, regularPolygon, mem_coe, mem_image, Set.mem_preimage] at *
      obtain ⟨j, -, rfl⟩ := hv
      exact ⟨i - j, mem_univ _, reflect_polygonVert.symm⟩
    · rw [Set.card_image_of_injective _ R.injective]
  have ch := isom_image_convexHull R vs
  rwa [im] at ch

variable (i j) in
/-- A linear form attaining the same value at `polygonVert i` and `polygonVert k`,
used to show that non-adjacent vertices do not form edges. -/
noncomputable def edgeForm : StrongDual ℝ (E 2) :=
  cos ((i + j) * π / n) • EuclideanSpace.proj 0 +
  sin ((i + j) * π / n) • EuclideanSpace.proj 1

lemma edgeForm_apply (k : Fin n) :
    edgeForm i j (polygonVert k) = cos ((i + j - 2 * k) * π / n) := by
  norm_num [edgeForm, polygonVert]
  rw [← cos_sub, ← sub_div, ← mul_rotate, ← sub_mul, mul_comm 2]

lemma edgeForm_lt [NeZero n] (h : i ≠ j + 1) (hij : i < j) :
    cos ((i + j - 2 * (j + 1).1) * π / n) < cos ((i - j) * π / n) := by
  have hn := Fin.nontrivial_iff_two_le.mp ⟨_, _, hij.ne'⟩
  have unwrap : cos ((i + j - 2 * (j + 1).1) * π / n) = cos ((j - i + 2) * π / n) := by
    rw [cos_eq_cos_iff]
    refine ⟨((j + 1) / n : ℤ), .inr ?_⟩
    field_simp
    norm_cast
    simp_rw [Int.subNatNat_eq_coe, Fin.val_add, Fin.one_eq_mk_of_lt hn]
    grind [Int.emod_add_mul_ediv (j + 1) n]
  rw [unwrap]
  conv_rhs => rw [← cos_neg, ← neg_div, ← neg_mul, neg_sub]
  apply cos_lt_cos_of_nonneg_of_le_pi
  · suffices 0 ≤ (j - i : ℝ) by positivity
    rw [sub_nonneg]
    exact_mod_cast hij.le
  · rw [mul_div_right_comm, mul_le_iff_le_one_left pi_pos]
    refine div_le_one_of_le₀ ?_ (by simp)
    rw [← add_sub_right_comm, sub_le_iff_le_add]
    norm_cast
    by_cases! hij₂ : 0 < i.1 ∨ j + 1 < n; · lia
    replace hij₂ : i = 0 ∧ j.1 + 1 = n := by lia
    rw [← Fin.val_ne_iff, Fin.val_add, Fin.one_eq_mk_of_lt hn, hij₂.2, Nat.mod_self] at h
    lia
  · gcongr ?_ * _ / _
    linarith only

lemma edgeForm_gt [NeZero n] (h : j ≠ i + 1) (hij : i < j) :
    cos ((i - j) * π / n) < cos ((i + j - 2 * (i + 1).1) * π / n) := by
  rw [i.val_add_one_of_lt' (by lia), Nat.cast_add_one,
    show i + j - 2 * (i + 1 : ℝ) = j - i - 2 by ring, ← cos_neg, ← neg_div, ← neg_mul, neg_sub]
  have hn := Fin.nontrivial_iff_two_le.mp ⟨_, _, hij.ne'⟩
  apply cos_lt_cos_of_nonneg_of_le_pi
  · suffices 0 ≤ (j - i - 2 : ℝ) by positivity
    rw [sub_nonneg, le_sub_iff_add_le]
    norm_cast
    rw [← Fin.val_ne_iff, i.val_add_one_of_lt' (by lia)] at h
    lia
  · rw [mul_div_right_comm, mul_le_iff_le_one_left pi_pos]
    refine div_le_one_of_le₀ ?_ (by simp)
    trans (j : ℝ) <;> simp
  · gcongr ?_ * _ / _
    linarith only

lemma adjacent_verts_of_isFace [NeZero n] (nij : i ≠ j)
    (h : (regularPolygon n).IsFace ((convexHull ℝ) {polygonVert i, polygonVert j})) :
    j = i + 1 ∨ j = i - 1 := by
  rw [eq_sub_iff_add_eq, @eq_comm _ _ i]
  contrapose! h
  rw [← coe_pair]
  wlog hij : i < j generalizing i j
  · specialize this nij.symm h.symm (by lia)
    rwa [pair_comm]
  let f : Fin 2 → E 2 := ![polygonVert i, polygonVert j]
  have tr : univ.image f = {polygonVert i, polygonVert j} := by ext v; simp [f]; tauto
  have sf : univ.image f ∪ {polygonVert (j + 1), polygonVert (i + 1)} ⊆
      (regularPolygon n).vertices := by
    simp_rw [tr, union_subset_iff, insert_subset_iff, singleton_subset_iff, regularPolygon]
    simp
  have aif := affineIndependent_of_ne ℝ (injective_polygonVert.ne nij)
  have Lc (k) : edgeForm i j (f k) = cos ((i - j) * π / n) := by
    fin_cases k <;> simp [f] <;> rw [edgeForm_apply, two_mul]
    · rw [add_sub_add_left_eq_sub, ← cos_neg, ← neg_div, ← neg_mul, neg_sub]
    · simp
  rw [← tr]
  refine not_isFace_of_bracketing_points sf aif Lc ?_ ?_
  · rw [edgeForm_apply]
    exact edgeForm_lt h.2 hij
  · rw [edgeForm_apply]
    exact edgeForm_gt h.1 hij

theorem regularPolygon_flag_characterisation [NeZero n] (F : (regularPolygon n).Flag) :
    ∃ i : Fin n, F.face 0 = {polygonVert i} ∧
    (F.face 1 = convexHull ℝ {polygonVert i, polygonVert (i + 1)} ∨
      F.face 1 = convexHull ℝ {polygonVert i, polygonVert (i - 1)}) := by
  obtain ⟨v, mv, F₀⟩ := zero_dim_face_iff_vertex.mp ⟨F.isFace 0, F.dim_eq 0⟩
  obtain ⟨w, mw, x, mx, nik, F₁⟩ := one_dim_face_is_edge (F.isFace 1) (F.dim_eq 1)
  have inc := faceGens_ssubset_iff (F.isFace 0).1 (F.isFace 1).1
  simp_rw [F.strict_mono 0 1 (by lia), iff_true] at inc
  generalize_proofs _ ex₀ ex₁ at inc
  have e₀ : faceGens ex₀ = {v} :=
    (existsUnique_faceGens ex₀).unique (exists_faceGens ex₀).choose_spec
      ⟨by simpa using mv, by simpa using F₀⟩
  have e₁ : faceGens ex₁ = {w, x} := by
    refine (existsUnique_faceGens ex₁).unique (exists_faceGens ex₁).choose_spec
      ⟨?_, by simpa using F₁⟩
    rw [insert_subset_iff, singleton_subset_iff]
    exact ⟨mw, mx⟩
  rw [regularPolygon, mem_image] at mv mw mx
  obtain ⟨i, -, rfl⟩ := mv
  obtain ⟨j, -, rfl⟩ := mw
  obtain ⟨k, -, rfl⟩ := mx
  refine ⟨i, F₀, ?_⟩
  rw [e₀, e₁] at inc
  replace inc := inc.subset
  simp_rw [singleton_subset_iff, mem_insert, mem_singleton, injective_polygonVert.eq_iff] at inc
  wlog eij : i = j generalizing j k
  · rw [pair_comm] at e₁
    rw [Set.pair_comm] at F₁
    exact this k j nik.symm F₁ e₁ inc.symm (inc.resolve_left eij)
  subst eij
  rw [injective_polygonVert.ne_iff] at nik
  exact (adjacent_verts_of_isFace nik (F₁ ▸ F.isFace 1)).imp
    (fun e ↦ by rwa [e] at F₁) (fun e ↦ by rwa [e] at F₁)

lemma exists_symmetry_plus
    {s : Fin n} (nzn : NeZero n := s.neZero) {F G : (regularPolygon n).Flag}
    (F₀ : F.face 0 = {polygonVert i}) (G₀ : G.face 0 = {polygonVert j})
    (F₁ : F.face 1 = (convexHull ℝ) {polygonVert i, polygonVert (i + s)})
    (G₁ : G.face 1 = (convexHull ℝ) {polygonVert j, polygonVert (j + s)}) :
    ∃ φ, (regularPolygon n).isSymmetry φ ∧ ∀ k, φ '' F.face k = G.face k := by
  refine ⟨toIsom (rotate2D (2 * π * (j - i).1 / n)) 0, isSymmetry_regularPolygon_rotate,
    fun d ↦ ?_⟩
  fin_cases d <;> norm_num
  · rw [F₀, G₀, Set.image_singleton, Set.singleton_eq_singleton_iff,
      rotate_polygonVert, sub_add_cancel]
  · rw [F₁, G₁, isom_image_convexHull]
    congr
    ext v
    simp_rw [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp,
      existsAndEq, true_and, rotate_polygonVert, ← add_assoc, sub_add_cancel]
    tauto

lemma exists_symmetry_minus
    {s : Fin n} (nzn : NeZero n := s.neZero) {F G : (regularPolygon n).Flag}
    (F₀ : F.face 0 = {polygonVert i}) (G₀ : G.face 0 = {polygonVert j})
    (F₁ : F.face 1 = (convexHull ℝ) {polygonVert i, polygonVert (i + s)})
    (G₁ : G.face 1 = (convexHull ℝ) {polygonVert j, polygonVert (j - s)}) :
    ∃ φ, (regularPolygon n).isSymmetry φ ∧ ∀ k, φ '' F.face k = G.face k := by
  refine ⟨toIsom (reflect2D (2 * π * (j + i).1 / n)) 0, isSymmetry_regularPolygon_reflect,
    fun d ↦ ?_⟩
  fin_cases d <;> norm_num
  · rw [F₀, G₀, Set.image_singleton, Set.singleton_eq_singleton_iff,
      reflect_polygonVert, add_sub_cancel_right]
  · rw [F₁, G₁, isom_image_convexHull]
    congr
    ext v
    simp_rw [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp,
      existsAndEq, true_and, reflect_polygonVert, ← sub_sub, add_sub_cancel_right]
    tauto

theorem regularPolygon_isRegular (hn : 3 ≤ n) (nzn : NeZero n := ⟨by lia⟩) :
    (regularPolygon n).IsRegular := by
  refine ⟨regularPolygon_isFullDim hn, fun F G ↦ ?_⟩
  obtain ⟨i, F₀, F₁⟩ := regularPolygon_flag_characterisation F
  obtain ⟨j, G₀, G₁⟩ := regularPolygon_flag_characterisation G
  obtain F₁ | F₁ := F₁ <;> obtain G₁ | G₁ := G₁
  · exact exists_symmetry_plus _ F₀ G₀ F₁ G₁
  · exact exists_symmetry_minus _ F₀ G₀ F₁ G₁
  · rw [sub_eq_add_neg] at F₁
    rw [← sub_neg_eq_add] at G₁
    exact exists_symmetry_minus _ F₀ G₀ F₁ G₁
  · rw [sub_eq_add_neg] at F₁ G₁
    exact exists_symmetry_plus _ F₀ G₀ F₁ G₁
