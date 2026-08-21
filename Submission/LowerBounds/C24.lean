import Submission.LowerBounds.Lemmas
import Submission.PolarDual
import Submission.Symmetry

open Real Finset LeanEval.Geometry.PlatonicClassification ConvexPolytope

/-- The 24-cell's vertex function. -/
noncomputable def cell24Vert (t : Fin 4 × Bool ⊕ (Fin 4 → Bool)) : E 4 :=
  t.elim (fun ⟨i, s⟩ ↦ .single i (if s then -1 else 1))
    fun s ↦ .toLp _ fun i ↦ if s i then -2⁻¹ else 2⁻¹

lemma norm_cell24Vert {t : Fin 4 × Bool ⊕ (Fin 4 → Bool)} : ‖cell24Vert t‖ = 1 := by
  cases t with
  | inl p => simp [cell24Vert, abs_ite]
  | inr s => norm_num [cell24Vert, PiLp.norm_eq_of_L2]

lemma injective_cell24Vert : cell24Vert.Injective := by
  refine Function.Injective.sumElim (fun ⟨i₁, s₁⟩ ⟨i₂, s₂⟩ e ↦ ?_) (fun s₁ s₂ e ↦ ?_) ?_
  · replace e := congr($e i₁)
    rw [PiLp.single_eq_same, PiLp.single_apply] at e
    grind
  · ext i
    grind [congr($e i)]
  · rintro ⟨i, s⟩ t
    by_contra h
    replace h := congr($h 0)
    grind [PiLp.single_apply]

/-- Index type for the dual 24-cell. -/
@[ext]
structure C24Index where
  /-- Coordinates `a, b` -/
  (a b : Fin 4)
  /-- Signs `s, t` -/
  (s t : Bool)
  /-- The coordinates are strictly ordered -/
  l : a < b
deriving Fintype, DecidableEq

instance : Inhabited C24Index where
  default := ⟨0, 1, false, false, by lia⟩

/-- The dual 24-cell's vertex function. -/
noncomputable def cell24DualVert (I : C24Index) : E 4 :=
  .single I.a (if I.s then -1 else 1) + .single I.b (if I.t then -1 else 1)

lemma norm_cell24DualVert (I : C24Index) : ‖cell24DualVert I‖ = √2 := by
  rw [PiLp.norm_eq_of_L2]
  congr
  have res (i) (hi : ‖cell24DualVert I i‖ ^ 2 ≠ 0) : i ∈ ({I.a, I.b} : Finset _) := by
    contrapose hi
    rw [mem_insert, mem_singleton, not_or] at hi
    simp_rw [cell24DualVert, WithLp.ofLp_add, PiLp.ofLp_single, Pi.add_apply]
    simp [Pi.single_eq_of_ne hi.1, Pi.single_eq_of_ne hi.2]
  simp_rw [← Fintype.sum_subset res, sum_pair I.l.ne, cell24DualVert, WithLp.ofLp_add,
    PiLp.ofLp_single, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne I.l.ne,
    Pi.single_eq_of_ne' I.l.ne, add_zero, zero_add, norm_eq_abs, sq_abs, ite_pow, neg_sq, ite_self]
  norm_num

lemma injective_cell24DualVert : cell24DualVert.Injective := fun I J e ↦ by
  simp only [cell24DualVert] at e
  have la := congr($e I.a)
  have lb := congr($e I.b)
  simp_rw [PiLp.add_apply, PiLp.single_apply] at la lb
  have ea : I.a = J.a := by grind [I.l, J.l]
  have eb : I.b = J.b := by grind [I.l]
  simp_rw [← ea, ← eb, I.l.ne, I.l.ne', reduceIte] at la lb
  apply C24Index.ext ea eb <;> grind

/-- The 24-cell (unit Hurwitz quaternions). -/
noncomputable def cell24 : ConvexPolytope 4 where
  vertices := univ.image cell24Vert
  vertices_nonempty := by simp
  vertices_eq_extremePoints := by
    refine self_eq_extremePoints_convexHull_of_subset_sphere 0 1 fun t mt ↦ ?_
    rw [mem_coe, mem_image] at mt
    obtain ⟨t, -, rfl⟩ := mt
    simp [norm_cell24Vert]

/-- The dual 24-cell (all permutations of `(±1, ±1, 0, 0)`). -/
noncomputable def cell24Dual : ConvexPolytope 4 where
  vertices := univ.image cell24DualVert
  vertices_nonempty := by simp
  vertices_eq_extremePoints := by
    refine self_eq_extremePoints_convexHull_of_subset_sphere 0 √2 fun t mt ↦ ?_
    rw [mem_coe, mem_image] at mt
    obtain ⟨I, -, rfl⟩ := mt
    simp [norm_cell24DualVert]

lemma card_cell24_vertices : #cell24.vertices = 24 := by
  simp [cell24, card_image_of_injective _ injective_cell24Vert]

lemma card_cell24Dual_vertices : #cell24Dual.vertices = 24 := by
  rw [cell24Dual, card_image_of_injective _ injective_cell24DualVert]
  decide

lemma cell24_toSet_subset : cell24.toSet ⊆ {v | ∀ i j, i < j → |v i| + |v j| ≤ 1} := by
  refine convexHull_min (fun v mv ↦ ?_) fun x hx y hy a b la lb s i j l ↦ ?_
  · rw [Set.mem_ofPred]
    rw [mem_coe, cell24, mem_image] at mv
    obtain ⟨t, -, rfl⟩ := mv
    cases t with
    | inl p => simp_rw [cell24Vert, Sum.elim_inl, PiLp.single_apply]; grind
    | inr s => simp_rw [cell24Vert, Sum.elim_inr, abs_ite]; norm_num
  · simp_rw [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    calc
      _ ≤ _ := add_le_add (abs_add_le ..) (abs_add_le ..)
      _ = a * (|x i| + |x j|) + b * (|y i| + |y j|) := by
        simp_rw [abs_mul, abs_of_nonneg la, abs_of_nonneg lb]; ring
      _ ≤ a * 1 + b * 1 := by specialize hx _ _ l; specialize hy _ _ l; gcongr
      _ = _ := by simpa

lemma tesseract_subset_cell24_toSet : {v | ∀ i, |v i| ≤ 2⁻¹} ⊆ cell24.toSet := fun v mv ↦ by
  let w (s : Fin 4 → Bool) := ∏ i, if s i then 2⁻¹ - v i else 2⁻¹ + v i
  apply mem_convexHull_of_exists_fintype (Sum.elim (fun _ ↦ 0) w) cell24Vert
  · rintro (p | s)
    · simp
    · exact prod_nonneg fun i _ ↦ by split_ifs <;> linarith [abs_le.mp (mv i)]
  · simp_rw [Fintype.sum_sum_type, Sum.elim_inl, sum_const_zero, zero_add, Sum.elim_inr]
    rw [← Fintype.prod_sum fun _ b ↦ if b = true then _ else _]
    refine Fintype.prod_eq_one _ fun i ↦ ?_
    simp only [Fintype.sum_bool, Bool.false_eq_true, reduceIte]
    ring
  · exact fun _ ↦ mem_image_of_mem _ (mem_univ _)
  · simp_rw [Fintype.sum_sum_type, Sum.elim_inl, zero_smul, sum_const_zero, zero_add]
    ext j
    simp_rw [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      cell24Vert, Sum.elim_inr]
    let f (i) (b : Bool) := if b then 2⁻¹ - v i else 2⁻¹ + v i
    let g (i) (b : Bool) := if i = j then f i b * (if b then -2⁻¹ else 2⁻¹) else f i b
    have rearr (s) : w s * (if s j then -2⁻¹ else 2⁻¹) = ∏ i, g i (s i) := by
      simp_rw [Fintype.prod_eq_mul_prod_compl j, w, Fintype.prod_eq_mul_prod_compl j]
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

lemma cell24_toSet_superset : {v | ∀ i j, i < j → |v i| + |v j| ≤ 1} ⊆ cell24.toSet := fun v mv ↦ by
  by_cases! tess : ∀ i, |v i| ≤ 2⁻¹
  · exact tesseract_subset_cell24_toSet tess
  obtain ⟨i, hi⟩ := tess
  let s := decide (v i < 0)
  have sma : v i = (if s then -1 else 1) * |v i| := by
    obtain h | h := abs_cases (v i) <;> simp [h, s]
  let c : ℝ := 2 * (1 - |v i|)
  have nnc : 0 ≤ c := by
    obtain rfl | li : i = 3 ∨ i < 3 := by lia
    · specialize mv 0 3 (by lia)
      linarith [abs_nonneg (v 0)]
    · specialize mv i (i + 1) (by lia)
      linarith [abs_nonneg (v (i + 1))]
  obtain c0 | cpos := nnc.eq_or_lt'
  · suffices v = cell24Vert (.inl (i, s)) from
      this ▸ subset_convexHull ℝ _ (mem_image_of_mem _ (mem_univ _))
    ext j
    rw [mul_eq_zero_iff_left two_ne_zero, sub_eq_zero] at c0
    simp_rw [cell24Vert, Sum.elim_inl, PiLp.single_apply]
    obtain l | rfl | l := lt_trichotomy j i
    · simpa [← c0, l.ne] using mv _ _ l
    · rw [sma, ← c0]; simp
    · simpa [← c0, l.ne'] using mv _ _ l
  let p := c⁻¹ • (v - (1 - c) • cell24Vert (.inl (i, s)))
  have cc : (1 - c) • cell24Vert (.inl (i, s)) + c • p = v := by
    simp [p, smul_smul, mul_inv_cancel₀ cpos.ne']
  rw [← cc]
  refine convex_convexHull ℝ _ (subset_convexHull ℝ _ <| mem_image_of_mem _ <| mem_univ _)
    (tesseract_subset_cell24_toSet fun j ↦ ?_) (by linarith) cpos.le (by ring)
  simp_rw [p, cell24Vert, Sum.elim_inl, PiLp.smul_apply, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul, abs_mul, abs_inv, abs_of_pos cpos]
  obtain l | rfl | l := lt_trichotomy i j
  · rw [PiLp.single_eq_of_ne' _ l.ne, mul_zero, sub_zero, inv_mul_le_iff₀' cpos]
    linarith [mv _ _ l]
  · rw [PiLp.single_eq_same, sma, mul_comm (1 - c), ← mul_sub, abs_mul, abs_ite, abs_neg, ite_self,
      abs_one, one_mul, show |v.ofLp i| - (1 - c) = 2⁻¹ * c by ring, abs_mul, abs_of_pos cpos]
    simp [mul_left_comm, inv_mul_cancel₀ cpos.ne']
  · rw [PiLp.single_eq_of_ne _ l.ne, mul_zero, sub_zero, inv_mul_le_iff₀' cpos]
    linarith [mv _ _ l]

lemma cell24_toSet_eq : cell24.toSet = {v | ∀ i j, i < j → |v i| + |v j| ≤ 1} :=
  subset_antisymm cell24_toSet_subset cell24_toSet_superset

lemma cell24Dual_polar_eq :
    ⋂ v ∈ cell24Dual.toSet, {w | inner ℝ v w ≤ 1} = {v | ∀ i j, i < j → |v i| + |v j| ≤ 1} := by
  ext w
  simp_rw [toSet, ← iInter_eq_iInter_convexHull_le, Set.mem_iInter, Set.mem_ofPred_eq]
  refine ⟨fun h i j l ↦ ?_, fun h v mv ↦ ?_⟩
  · have mv (I) : cell24DualVert I ∈ cell24Dual.vertices := mem_image.mpr ⟨I, mem_univ _, rfl⟩
    have FF := h _ (mv ⟨i, j, false, false, l⟩)
    have FT := h _ (mv ⟨i, j, false, true, l⟩)
    have TF := h _ (mv ⟨i, j, true, false, l⟩)
    have TT := h _ (mv ⟨i, j, true, true, l⟩)
    simp_rw [cell24DualVert, inner_add_left, PiLp.inner_apply, Bool.false_eq_true, reduceIte,
      PiLp.single_apply, inner_apply, ite_mul, zero_mul, Fintype.sum_ite_eq'] at FF FT TF TT
    grind
  · rw [cell24Dual, mem_image] at mv
    obtain ⟨⟨a, b, s, t, l⟩, -, rfl⟩ := mv
    simp_rw [cell24DualVert, inner_add_left, PiLp.inner_apply, PiLp.single_apply, inner_apply,
      ite_mul, zero_mul, Fintype.sum_ite_eq']
    refine le_of_abs_le ((abs_add_le ..).trans ?_)
    simp_rw [abs_ite, abs_mul, abs_neg, ite_self, abs_one, one_mul]
    exact h a b l

lemma isPolarDual_cell24Dual_cell24 : IsPolarDual cell24Dual cell24 := by
  rw [IsPolarDual, cell24_toSet_eq, cell24Dual_polar_eq]

/-! ### Symmetries of the 24-cell -/

open Matrix

lemma sum_cell24_vertices : ∑ v ∈ cell24.vertices, v = 0 := by
  rw [cell24, sum_image (by simp [injective_cell24Vert]), Fintype.sum_sum_type]
  simp_rw [cell24Vert, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type]
  rw [Fintype.sum_eq_zero _ (by simp [← PiLp.single_add]), zero_add]
  ext i
  simp_rw [WithLp.ofLp_sum, Finset.sum_apply, PiLp.zero_apply]
  let e : Equiv.Perm (Fin 4 → Bool) := ⟨(!· ·), (!· ·), fun _ ↦ by simp, fun _ ↦ by simp⟩
  nth_rw 1 [← mul_eq_zero_iff_left two_ne_zero, two_mul, ← Equiv.sum_comp e, ← sum_add_distrib]
  refine Fintype.sum_eq_zero _ fun s ↦ ?_
  simp_rw [e, Equiv.coe_fn_mk, Bool.not_iff_not, ite_not, ite_add_ite]
  simp

lemma centroid_cell24_vertices : cell24.vertices.centroid ℝ id = 0 := by
  simp [centroid_eq_inv_smul_sum cell24.vertices_nonempty, sum_cell24_vertices]

lemma cell24_isSymmetry_fixes_zero {φ : Isom 4} (sφ : cell24.isSymmetry φ) : φ 0 = 0 := by
  have key := sφ.map_centroid
  rwa [centroid_cell24_vertices] at key

lemma isSymmetry_cell24Dual_of_cell24 {φ : Isom 4} (sφ : cell24.isSymmetry φ) :
    cell24Dual.isSymmetry φ :=
  isPolarDual_cell24Dual_cell24.symm.isSymmetry sφ (cell24_isSymmetry_fixes_zero sφ)

lemma coordPerm_cell24Vert {σ : Equiv.Perm (Fin 4)} {t : Fin 4 × Bool ⊕ (Fin 4 → Bool)} :
    (toIsom (coordPerm σ) 0) (cell24Vert t) =
    cell24Vert (t.map (fun ⟨i, s⟩ ↦ (σ⁻¹ i, s)) (· ∘ σ)) := by
  ext i
  simp_rw [toIsom_apply, WithLp.ofLp_zero, add_zero, coordPerm, permMatrix_mulVec]
  cases t <;> simp [cell24Vert, -PiLp.ofLp_single, σ.eq_symm_apply]

lemma coordFlip_cell24Vert {m : Fin 4 → Bool} {t : Fin 4 × Bool ⊕ (Fin 4 → Bool)} :
    (toIsom (coordFlip m) 0) (cell24Vert t) =
    cell24Vert (t.map (fun ⟨i, s⟩ ↦ (i, m i ^^ s)) fun s i ↦ m i ^^ s i) := by
  ext i
  simp_rw [toIsom_apply, WithLp.ofLp_zero, add_zero, coordFlip]
  cases t with
  | inl p =>
    simp_rw [cell24Vert, Sum.map_inl, Sum.elim_inl, mulVec_diagonal, PiLp.single_apply]
    split_ifs <;> simp_all
  | inr s =>
    simp_rw [cell24Vert, Sum.map_inr, Sum.elim_inr, mulVec_diagonal]
    split_ifs <;> simp_all

section Coordinates

variable {a b : Fin 4} {s t : Bool} {σ : Equiv.Perm (Fin 4)} {m : Fin 4 → Bool}

/-- The vertices of the dual 24-cell, without the ordering constraint on the coordinates. -/
noncomputable def dualVert (a b : Fin 4) (s t : Bool) : E 4 :=
  .single a (if s then -1 else 1) + .single b (if t then -1 else 1)

lemma dualVert_comm : dualVert a b s t = dualVert b a t s := add_comm ..

lemma exists_dualVert {w : E 4} (hw : w ∈ cell24Dual.vertices) :
    ∃ a b s t, a ≠ b ∧ w = dualVert a b s t := by
  rw [cell24Dual, mem_image] at hw
  obtain ⟨I, -, rfl⟩ := hw
  exact ⟨I.a, I.b, I.s, I.t, I.l.ne, rfl⟩

lemma exists_cell24Vert {v : E 4} (hv : v ∈ cell24.vertices) : ∃ x, v = cell24Vert x := by
  rw [cell24, mem_image] at hv
  obtain ⟨x, -, rfl⟩ := hv
  exact ⟨x, rfl⟩

lemma toIsom_add {R : orthogonalGroup (Fin 4) ℝ} (x y : E 4) :
    toIsom R 0 (x + y) = toIsom R 0 x + toIsom R 0 y := by
  simp [toIsom_apply, mulVec_add]

lemma coordPerm_dualVert :
    toIsom (coordPerm σ) 0 (dualVert a b s t) = dualVert (σ⁻¹ a) (σ⁻¹ b) s t := by
  rw [dualVert, toIsom_add]
  apply congrArg₂ (· + ·) <;> ext i <;>
  simp [toIsom_apply, coordPerm, permMatrix_mulVec, -PiLp.ofLp_single, σ.eq_symm_apply]

lemma coordFlip_dualVert :
    toIsom (coordFlip m) 0 (dualVert a b s t) = dualVert a b (m a ^^ s) (m b ^^ t) := by
  rw [dualVert, toIsom_add]
  apply congrArg₂ (· + ·) <;> ext i <;> simp_rw [toIsom_apply, WithLp.ofLp_zero, add_zero,
    coordFlip, mulVec_diagonal, PiLp.single_apply] <;> split_ifs <;> simp_all

lemma isSymmetry_cell24_coordPerm : cell24.isSymmetry (toIsom (coordPerm σ) 0) := by
  set R := toIsom (coordPerm σ) 0
  have im : R '' cell24.vertices = cell24.vertices := by
    apply Set.eq_of_subset_of_card_le
    · rw [Set.image_subset_iff]
      intro v hv
      simp only [R, cell24, mem_coe, mem_image, Set.mem_preimage] at *
      obtain ⟨t, -, rfl⟩ := hv
      exact ⟨t.map (fun ⟨i, s⟩ ↦ (σ⁻¹ i, s)) (· ∘ σ), mem_univ _, coordPerm_cell24Vert.symm⟩
    · rw [Set.card_image_of_injective _ R.injective]
  have ch := isom_image_convexHull R cell24.vertices
  rwa [im] at ch

lemma isSymmetry_cell24_coordFlip : cell24.isSymmetry (toIsom (coordFlip m) 0) := by
  set R := toIsom (coordFlip m) 0
  have im : R '' (cell24.vertices : Set (E 4)) = cell24.vertices := by
    apply Set.eq_of_subset_of_card_le
    · rw [Set.image_subset_iff]
      intro v hv
      simp only [R, cell24, mem_coe, mem_image, Set.mem_preimage] at *
      obtain ⟨t, -, rfl⟩ := hv
      exact ⟨t.map (fun ⟨i, s⟩ ↦ (i, m i ^^ s)) fun s i ↦ m i ^^ s i, mem_univ _,
        coordFlip_cell24Vert.symm⟩
    · rw [Set.card_image_of_injective _ R.injective]
  have ch := isom_image_convexHull R cell24.vertices
  rwa [im] at ch

end Coordinates

/-- The matrix of the orthogonal involution exchanging the two orbits of the coordinate
symmetries on the vertices of the 24-cell. -/
noncomputable def cell24HadMat : Matrix (Fin 4) (Fin 4) ℝ :=
  (2⁻¹ : ℝ) • !![1,1,1,1; 1,1,-1,-1; 1,-1,1,-1; 1,-1,-1,1]

lemma cell24HadMat_transpose : cell24HadMatᵀ = cell24HadMat := by
  rw [cell24HadMat, transpose_smul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma cell24HadMat_mul_self : cell24HadMat * cell24HadMat = 1 := by
  rw [cell24HadMat, smul_mul_smul_comm]
  ext i j
  simp_rw [Matrix.smul_apply, mul_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

/-- The orthogonal involution exchanging the two orbits of the coordinate symmetries on the
vertices of the 24-cell. -/
noncomputable def cell24Had : orthogonalGroup (Fin 4) ℝ where
  val := cell24HadMat
  property := by
    rw [mem_orthogonalGroup_iff, cell24HadMat_transpose, cell24HadMat_mul_self]

lemma cell24Had_val : cell24Had.1 = cell24HadMat := rfl

lemma cell24Had_mul_self : cell24Had.1 * cell24Had.1 = 1 := cell24HadMat_mul_self

lemma cell24Had_involutive (v : E 4) : toIsom cell24Had 0 (toIsom cell24Had 0 v) = v := by
  simp_rw [toIsom_apply, WithLp.ofLp_zero, add_zero, mulVec_mulVec, cell24Had_mul_self, one_mulVec]

lemma cell24Had_apply_zero (v : E 4) : toIsom cell24Had 0 v 0 = 2⁻¹ * (v 0 + v 1 + v 2 + v 3) := by
  simp [toIsom_apply, cell24Had_val, cell24HadMat, dotProduct, Fin.sum_univ_four]
  ring

lemma cell24Had_apply_one (v : E 4) : toIsom cell24Had 0 v 1 = 2⁻¹ * (v 0 + v 1 - v 2 - v 3) := by
  simp [toIsom_apply, cell24Had_val, cell24HadMat, dotProduct, Fin.sum_univ_four]
  ring

lemma cell24Had_apply_two (v : E 4) : toIsom cell24Had 0 v 2 = 2⁻¹ * (v 0 - v 1 + v 2 - v 3) := by
  simp [toIsom_apply, cell24Had_val, cell24HadMat, dotProduct, Fin.sum_univ_four]
  ring

lemma cell24Had_apply_three (v : E 4) : toIsom cell24Had 0 v 3 = 2⁻¹ * (v 0 - v 1 - v 2 + v 3) := by
  simp [toIsom_apply, cell24Had_val, cell24HadMat, dotProduct, Fin.sum_univ_four]
  ring

lemma abs_add_abs_le_one {x y p q : ℝ} (hx : x = 2⁻¹ * (p + q)) (hy : y = 2⁻¹ * (p - q))
    (hp : |p| ≤ 1) (hq : |q| ≤ 1) : |x| + |y| ≤ 1 := by
  obtain ⟨hp₁, hp₂⟩ := abs_le.mp hp
  obtain ⟨hq₁, hq₂⟩ := abs_le.mp hq
  rcases abs_cases x with ⟨ex, -⟩ | ⟨ex, -⟩ <;> rcases abs_cases y with ⟨ey, -⟩ | ⟨ey, -⟩ <;>
    rw [ex, ey, hx, hy] <;> linarith

lemma mapsTo_cell24_had {v : E 4} (hv : v ∈ cell24.toSet) :
    toIsom cell24Had 0 v ∈ cell24.toSet := by
  rw [cell24_toSet_eq] at hv ⊢
  have hb (a b : Fin 4) (hab : a ≠ b) : |v a| + |v b| ≤ 1 := by
    rcases hab.lt_or_gt with h | h
    · exact hv a b h
    · rw [add_comm]
      exact hv b a h
  have hadd (a b : Fin 4) (hab : a ≠ b) : |v a + v b| ≤ 1 := (abs_add_le ..).trans (hb a b hab)
  have hsub (a b : Fin 4) (hab : a ≠ b) : |v a - v b| ≤ 1 := by
    rw [sub_eq_add_neg]
    refine (abs_add_le ..).trans ?_
    rw [abs_neg]
    exact hb a b hab
  intro i j hij
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ :
      i = 0 ∧ j = 1 ∨ i = 0 ∧ j = 2 ∨ i = 0 ∧ j = 3 ∨ i = 1 ∧ j = 2 ∨ i = 1 ∧ j = 3 ∨
        i = 2 ∧ j = 3 := by lia
  · exact abs_add_abs_le_one ((cell24Had_apply_zero v).trans (by ring))
      ((cell24Had_apply_one v).trans (by ring)) (hadd 0 1 (by lia)) (hadd 2 3 (by lia))
  · exact abs_add_abs_le_one ((cell24Had_apply_zero v).trans (by ring))
      ((cell24Had_apply_two v).trans (by ring)) (hadd 0 2 (by lia)) (hadd 1 3 (by lia))
  · exact abs_add_abs_le_one ((cell24Had_apply_zero v).trans (by ring))
      ((cell24Had_apply_three v).trans (by ring)) (hadd 0 3 (by lia)) (hadd 1 2 (by lia))
  · exact abs_add_abs_le_one ((cell24Had_apply_one v).trans (by ring))
      ((cell24Had_apply_two v).trans (by ring)) (hsub 0 3 (by lia)) (hsub 1 2 (by lia))
  · exact abs_add_abs_le_one ((cell24Had_apply_one v).trans (by ring))
      ((cell24Had_apply_three v).trans (by ring)) (hsub 0 2 (by lia)) (hsub 1 3 (by lia))
  · exact abs_add_abs_le_one ((cell24Had_apply_two v).trans (by ring))
      ((cell24Had_apply_three v).trans (by ring)) (hsub 0 1 (by lia)) (hsub 2 3 (by lia))

lemma isSymmetry_cell24_had : cell24.isSymmetry (toIsom cell24Had 0) :=
  subset_antisymm (Set.image_subset_iff.mpr fun _ hv ↦ mapsTo_cell24_had hv)
    fun v hv ↦ ⟨_, mapsTo_cell24_had hv, cell24Had_involutive v⟩

lemma cell24Had_half : toIsom cell24Had 0 (cell24Vert (.inr fun _ ↦ false)) =
    cell24Vert (.inl (0, false)) := by
  ext i
  obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by lia
  · rw [cell24Had_apply_zero]
    norm_num [cell24Vert]
  · rw [cell24Had_apply_one]
    simp [cell24Vert]
  · rw [cell24Had_apply_two]
    simp [cell24Vert]
  · rw [cell24Had_apply_three]
    simp [cell24Vert]

/-! ### Flags of the 24-cell -/

/-- An extreme point lying in the segment spanned by two vertices is one of them. -/
lemma mem_pair_of_mem_convexHull_pair {n : ℕ} {P : ConvexPolytope n} {v w w' : E n}
    (mv : v ∈ P.vertices) (mw : w ∈ P.vertices) (mw' : w' ∈ P.vertices)
    (hv : v ∈ convexHull ℝ ({w, w'} : Set (E n))) : v = w ∨ v = w' := by
  have sg : ({w, w'} : Finset (E n)) ⊆ P.vertices := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have cg : (({w, w'} : Finset (E n)) : Set (E n)) = ({w, w'} : Set (E n)) := by simp
  have key := inter_extremePoints_subset_extremePoints_of_subset
    (𝕜 := ℝ) (convexHull_mono (𝕜 := ℝ) (cg ▸ Finset.coe_subset.mpr sg))
  have mv' : v ∈ Set.extremePoints ℝ (convexHull ℝ (P.vertices : Set (E n))) := by
    rw [← P.vertices_eq_extremePoints]
    exact mv
  have hx := key ⟨cg ▸ hv, mv'⟩
  rw [← cg, ← self_eq_exch_of_subset sg] at hx
  simpa using hx

lemma inner_dualVert {a b : Fin 4} {s t : Bool} (y : E 4) :
    inner ℝ y (dualVert a b s t) = (if s then -1 else 1) * y a + (if t then -1 else 1) * y b := by
  rw [dualVert, inner_add_right, EuclideanSpace.inner_single_right,
    EuclideanSpace.inner_single_right]
  simp

lemma cell24Vert_inl_apply {k i : Fin 4} {s : Bool} :
    cell24Vert (.inl (k, s)) i = if i = k then (if s then -1 else 1) else 0 := by
  simp [cell24Vert, PiLp.single_apply]

lemma cell24Vert_inr_apply {m : Fin 4 → Bool} {i : Fin 4} :
    cell24Vert (.inr m) i = if m i then -2⁻¹ else 2⁻¹ := rfl

/-- Symmetries of the 24-cell are linear, hence preserve inner products. -/
lemma inner_map_cell24_isSymmetry {φ : Isom 4} (sφ : cell24.isSymmetry φ) (x y : E 4) :
    inner ℝ (φ x) (φ y) = inner ℝ x y := by
  have φ0 := cell24_isSymmetry_fixes_zero sφ
  have lφ (a) : φ.linearIsometryEquiv a = φ a := by simpa [φ0] using φ.map_vsub a 0
  simp [← lφ]

lemma mem_cell24_vertices_map {φ : Isom 4} (sφ : cell24.isSymmetry φ) {v : E 4}
    (hv : v ∈ cell24.vertices) : φ v ∈ cell24.vertices := by
  rw [← sφ.image_vertices]
  exact mem_image_of_mem _ hv

lemma mem_cell24Dual_vertices_map {φ : Isom 4} (sφ : cell24.isSymmetry φ) {w : E 4}
    (hw : w ∈ cell24Dual.vertices) : φ w ∈ cell24Dual.vertices := by
  rw [← (isSymmetry_cell24Dual_of_cell24 sφ).image_vertices]
  exact mem_image_of_mem _ hw

variable {v₀ v₁ w₂ w₃ : E 4}

/-- The data determining a flag of the 24-cell: its vertex `v₀`, the second vertex `v₁` of its
edge, and the vertices `w₂`, `w₃` of the dual 24-cell dual to its 2-dimensional face and to its
facet. -/
def IsC24FlagData (v₀ v₁ w₂ w₃ : E 4) : Prop :=
  v₀ ∈ cell24.vertices ∧ v₁ ∈ cell24.vertices ∧ v₀ ≠ v₁ ∧
    w₂ ∈ cell24Dual.vertices ∧ w₃ ∈ cell24Dual.vertices ∧ w₂ ≠ w₃ ∧
    inner ℝ v₀ w₂ = 1 ∧ inner ℝ v₁ w₂ = 1 ∧ inner ℝ v₀ w₃ = 1 ∧ inner ℝ v₁ w₃ = 1

lemma IsC24FlagData.map {φ : Isom 4} (sφ : cell24.isSymmetry φ) (h : IsC24FlagData v₀ v₁ w₂ w₃) :
    IsC24FlagData (φ v₀) (φ v₁) (φ w₂) (φ w₃) := by
  obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ := h
  refine ⟨mem_cell24_vertices_map sφ h₀, mem_cell24_vertices_map sφ h₁, fun e ↦ h₂ (φ.injective e),
    mem_cell24Dual_vertices_map sφ h₃, mem_cell24Dual_vertices_map sφ h₄,
    fun e ↦ h₅ (φ.injective e), ?_, ?_, ?_, ?_⟩ <;>
    rw [inner_map_cell24_isSymmetry sφ] <;> assumption

/-- Every flag of the 24-cell is described by flag data. -/
lemma exists_c24FlagData (F : cell24.Flag) : ∃ v₀ v₁ w₂ w₃, IsC24FlagData v₀ v₁ w₂ w₃ ∧
    F.face 0 = {v₀} ∧ F.face 1 = convexHull ℝ {v₀, v₁} ∧
    faceDual cell24Dual (F.face 2) = convexHull ℝ {w₂, w₃} ∧
    faceDual cell24Dual (F.face 3) = {w₃} := by
  have hd := isPolarDual_cell24Dual_cell24.symm
  obtain ⟨v₀, mv₀, hf0⟩ := zero_dim_face_iff_vertex.mp ⟨F.isFace 0, F.dim_eq 0⟩
  obtain ⟨a, ma, b, mb, nab, hf1⟩ := one_dim_face_is_edge (F.isFace 1) (F.dim_eq 1)
  have mv₀1 : v₀ ∈ convexHull ℝ ({a, b} : Set (E 4)) := by
    rw [← hf1]
    exact F.mono zero_le_one (hf0 ▸ rfl)
  obtain ⟨v₁, mv₁, nv, hf1'⟩ :
      ∃ v₁ ∈ cell24.vertices, v₀ ≠ v₁ ∧ F.face 1 = convexHull ℝ {v₀, v₁} := by
    rcases mem_pair_of_mem_convexHull_pair mv₀ ma mb mv₀1 with rfl | rfl
    · exact ⟨b, mb, nab, hf1⟩
    · exact ⟨a, ma, nab.symm, by rw [hf1, Set.pair_comm]⟩
  have df2 : faceDim (F.face 2) < 4 := by rw [F.dim_eq 2]; lia
  have df3 : faceDim (F.face 3) < 4 := by rw [F.dim_eq 3]; lia
  have dg3 : faceDim (faceDual cell24Dual (F.face 3)) = 0 := by
    simpa using hd.dim_eq (F.isFace 3) (i := 3) (F.dim_eq 3)
  obtain ⟨w₃, mw₃, hg3e⟩ := zero_dim_face_iff_vertex.mp ⟨hd.isFace (F.isFace 3) df3, dg3⟩
  have dg2 : faceDim (faceDual cell24Dual (F.face 2)) = 1 := by
    simpa using hd.dim_eq (F.isFace 2) (i := 2) (F.dim_eq 2)
  obtain ⟨p, mp, q, mq, npq, hg2e⟩ := one_dim_face_is_edge (hd.isFace (F.isFace 2) df2) dg2
  have sub : faceDual cell24Dual (F.face 3) ⊆ faceDual cell24Dual (F.face 2) :=
    IsPolarDual.faceDual_subset (F.mono (show 2 ≤ 3 by lia))
  have mw₃' : w₃ ∈ convexHull ℝ ({p, q} : Set (E 4)) := by
    rw [← hg2e]
    exact sub (hg3e ▸ rfl)
  obtain ⟨w₂, mw₂, nw, hg2e'⟩ : ∃ w₂ ∈ cell24Dual.vertices, w₂ ≠ w₃ ∧
      faceDual cell24Dual (F.face 2) = convexHull ℝ {w₂, w₃} := by
    rcases mem_pair_of_mem_convexHull_pair mw₃ mp mq mw₃' with rfl | rfl
    · exact ⟨q, mq, npq.symm, by rw [hg2e, Set.pair_comm]⟩
    · exact ⟨p, mp, npq, hg2e⟩
  have key (w) (hw : w ∈ faceDual cell24Dual (F.face 2)) (v) (hv : v ∈ F.face 2) :
      inner ℝ v w = 1 := Set.mem_iInter₂.mp hw.2 v hv
  have mw₂f : w₂ ∈ faceDual cell24Dual (F.face 2) := by
    rw [hg2e']
    exact subset_convexHull ℝ _ (by simp)
  have mw₃f : w₃ ∈ faceDual cell24Dual (F.face 2) := by
    rw [hg2e']
    exact subset_convexHull ℝ _ (by simp)
  have mv₀2 : v₀ ∈ F.face 2 := F.mono (show 0 ≤ 2 by lia) (hf0 ▸ rfl)
  have mv₁2 : v₁ ∈ F.face 2 := F.mono (show 1 ≤ 2 by lia) (hf1' ▸ subset_convexHull ℝ _ (by simp))
  exact ⟨v₀, v₁, w₂, w₃, ⟨mv₀, mv₁, nv, mw₂, mw₃, nw, key _ mw₂f _ mv₀2, key _ mw₂f _ mv₁2,
    key _ mw₃f _ mv₀2, key _ mw₃f _ mv₁2⟩, hf0, hf1', hg2e', hg3e⟩

/-- Every vertex of the 24-cell can be moved to `(1, 0, 0, 0)` by a symmetry. -/
lemma exists_isSymmetry_map_vertex {v : E 4} (hv : v ∈ cell24.vertices) :
    ∃ φ : Isom 4, cell24.isSymmetry φ ∧ φ v = cell24Vert (.inl (0, false)) := by
  obtain ⟨x, rfl⟩ := exists_cell24Vert hv
  cases x with
  | inl p =>
    obtain ⟨k, s⟩ := p
    refine ⟨toIsom (coordPerm (Equiv.swap 0 k)) 0 * toIsom (coordFlip fun _ ↦ s) 0,
      isSymmetry_cell24_coordPerm.mul isSymmetry_cell24_coordFlip, ?_⟩
    simp_rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, coordFlip_cell24Vert, Sum.map_inl,
      Bool.xor_self, coordPerm_cell24Vert, Sum.map_inl, Equiv.swap_inv, Equiv.swap_apply_right]
  | inr m =>
    refine ⟨toIsom cell24Had 0 * toIsom (coordFlip m) 0,
      isSymmetry_cell24_had.mul isSymmetry_cell24_coordFlip, ?_⟩
    simp_rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, coordFlip_cell24Vert, Sum.map_inr,
      Bool.xor_self]
    exact cell24Had_half

/-- A vertex of the dual 24-cell whose inner product with `(1, 0, 0, 0)` equals `1` is of the
form `(1, 0, 0, 0) ± eᶜ` for a nonzero coordinate `c`. -/
lemma dualVert_normal_form {w : E 4} (hw : w ∈ cell24Dual.vertices)
    (h : inner ℝ (cell24Vert (.inl (0, false))) w = 1) :
    ∃ c t, c ≠ 0 ∧ w = dualVert 0 c false t := by
  obtain ⟨a, b, s, t, hab, rfl⟩ := exists_dualVert hw
  rw [inner_dualVert] at h
  simp only [cell24Vert_inl_apply] at h
  rcases eq_or_ne a 0 with rfl | ha
  · have hb : b ≠ 0 := hab.symm
    refine ⟨b, t, hb, ?_⟩
    rw [if_neg hb] at h
    cases s
    · rfl
    · norm_num at h
  · rw [if_neg ha] at h
    rcases eq_or_ne b 0 with rfl | hb
    · refine ⟨a, s, ha, ?_⟩
      cases t
      · exact dualVert_comm
      · norm_num at h
    · rw [if_neg hb] at h
      norm_num at h

/-- A half-integral vertex of the 24-cell meets a facet of the dual 24-cell only if both of the
relevant coordinates are positive. -/
lemma half_inner_eq_one {p q r : Bool}
    (h : ((if false then -1 else 1) * (if p then -2⁻¹ else 2⁻¹) +
      (if r then -1 else 1) * if q then -2⁻¹ else 2⁻¹) = (1 : ℝ)) : p = false ∧ r = q := by
  revert h
  cases p <;> cases q <;> cases r <;> norm_num

/-- A vertex of the 24-cell of the form `±eᵏ` other than `(1, 0, 0, 0)` determines the dual
vertices it is incident to. -/
lemma inl_eq_of_inner_dualVert {k b : Fin 4} {n t : Bool} (hb : b ≠ 0)
    (nv : cell24Vert (.inl (0, false)) ≠ cell24Vert (.inl (k, n)))
    (h : inner ℝ (cell24Vert (.inl (k, n))) (dualVert 0 b false t) = 1) : b = k ∧ t = n := by
  rw [inner_dualVert] at h
  simp only [cell24Vert_inl_apply] at h
  rcases eq_or_ne k 0 with rfl | hk
  · rw [if_neg hb] at h
    cases n
    · exact absurd rfl nv
    · norm_num at h
  · rw [if_neg hk.symm] at h
    rcases eq_or_ne b k with rfl | hbk
    · refine ⟨rfl, ?_⟩
      revert h
      cases t <;> cases n <;> norm_num
    · rw [if_neg hbk] at h
      norm_num at h

/-- Flag data based at the vertex `(1, 0, 0, 0)` is given by a sign vector and two distinct
nonzero coordinates. -/
lemma c24FlagData_normal_form (h : IsC24FlagData (cell24Vert (.inl (0, false))) v₁ w₂ w₃) :
    ∃ (m : Fin 4 → Bool) (b c : Fin 4), m 0 = false ∧ b ≠ 0 ∧ c ≠ 0 ∧ b ≠ c ∧
      v₁ = cell24Vert (.inr m) ∧ w₃ = dualVert 0 b false (m b) ∧
      w₂ = dualVert 0 c false (m c) := by
  obtain ⟨-, mv₁, nv, mw₂, mw₃, nw, i₂₀, i₂₁, i₃₀, i₃₁⟩ := h
  obtain ⟨c, u, hc, rfl⟩ := dualVert_normal_form mw₂ i₂₀
  obtain ⟨b, t, hb, rfl⟩ := dualVert_normal_form mw₃ i₃₀
  obtain ⟨x, rfl⟩ := exists_cell24Vert mv₁
  cases x with
  | inl p =>
    obtain ⟨k, n⟩ := p
    obtain ⟨rfl, rfl⟩ := inl_eq_of_inner_dualVert hb nv i₃₁
    obtain ⟨rfl, rfl⟩ := inl_eq_of_inner_dualVert hc nv i₂₁
    exact absurd rfl nw
  | inr m =>
    rw [inner_dualVert] at i₂₁ i₃₁
    simp only [cell24Vert_inr_apply] at i₂₁ i₃₁
    obtain ⟨hm0, rfl⟩ := half_inner_eq_one i₃₁
    obtain ⟨-, rfl⟩ := half_inner_eq_one i₂₁
    refine ⟨m, b, c, hm0, hb, hc, ?_, rfl, rfl, rfl⟩
    rintro rfl
    exact absurd rfl nw

/-- A permutation of `Fin 4` fixing `0` and sending two distinct nonzero coordinates
to `1` and `2`. -/
lemma exists_perm_fin_four {b c : Fin 4} (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = 0 ∧ σ b = 1 ∧ σ c = 2 := by
  decide +revert

/-- Any flag data can be moved to the standard one by a symmetry. -/
lemma exists_isSymmetry_c24FlagData_std (h : IsC24FlagData v₀ v₁ w₂ w₃) :
    ∃ φ : Isom 4, cell24.isSymmetry φ ∧ φ v₀ = cell24Vert (.inl (0, false)) ∧
      φ v₁ = cell24Vert (.inr fun _ ↦ false) ∧ φ w₂ = dualVert 0 2 false false ∧
      φ w₃ = dualVert 0 1 false false := by
  obtain ⟨ψ, sψ, hψ⟩ := exists_isSymmetry_map_vertex h.1
  obtain ⟨m, b, c, hm, hb, hc, hbc, e₁, e₃, e₂⟩ := c24FlagData_normal_form (hψ ▸ h.map sψ)
  obtain ⟨σ, hσ0, hσb, hσc⟩ := exists_perm_fin_four hb hc hbc
  refine ⟨toIsom (coordPerm σ⁻¹) 0 * toIsom (coordFlip m) 0 * ψ,
    (isSymmetry_cell24_coordPerm.mul isSymmetry_cell24_coordFlip).mul sψ, ?_, ?_, ?_, ?_⟩ <;>
  simp_rw [AffineIsometryEquiv.coe_mul, Function.comp_apply]
  · simp_rw [hψ, coordFlip_cell24Vert, Sum.map_inl, hm, Bool.xor_self,
      coordPerm_cell24Vert, Sum.map_inl, inv_inv, hσ0]
  · simp_rw [e₁, coordFlip_cell24Vert, Sum.map_inr, Bool.xor_self,
      coordPerm_cell24Vert, Sum.map_inr, Function.false_comp]
  · simp_rw [e₂, coordFlip_dualVert, hm, Bool.xor_self, coordPerm_dualVert, inv_inv, hσ0, hσc]
  · simp_rw [e₃, coordFlip_dualVert, hm, Bool.xor_self, coordPerm_dualVert, inv_inv, hσ0, hσb]

/-- The symmetry group of the 24-cell acts transitively on flag data. -/
lemma exists_isSymmetry_c24FlagData {v₀' v₁' w₂' w₃' : E 4} (h : IsC24FlagData v₀ v₁ w₂ w₃)
    (h' : IsC24FlagData v₀' v₁' w₂' w₃') : ∃ φ : Isom 4, cell24.isSymmetry φ ∧
      φ v₀ = v₀' ∧ φ v₁ = v₁' ∧ φ w₂ = w₂' ∧ φ w₃ = w₃' := by
  obtain ⟨φ, sφ, e₀, e₁, e₂, e₃⟩ := exists_isSymmetry_c24FlagData_std h
  obtain ⟨χ, sχ, f₀, f₁, f₂, f₃⟩ := exists_isSymmetry_c24FlagData_std h'
  refine ⟨χ⁻¹ * φ, sχ.inv.mul sφ, ?_, ?_, ?_, ?_⟩ <;>
    simp_rw [AffineIsometryEquiv.coe_mul, Function.comp_apply]
  · rw [e₀, ← f₀, AffineIsometryEquiv.coe_inv, χ.symm_apply_apply]
  · rw [e₁, ← f₁, AffineIsometryEquiv.coe_inv, χ.symm_apply_apply]
  · rw [e₂, ← f₂, AffineIsometryEquiv.coe_inv, χ.symm_apply_apply]
  · rw [e₃, ← f₃, AffineIsometryEquiv.coe_inv, χ.symm_apply_apply]

theorem cell24_isRegular : cell24.IsRegular := by
  refine ⟨isPolarDual_cell24Dual_cell24.symm.isFullDim, fun F G ↦ ?_⟩
  obtain ⟨v₀, v₁, w₂, w₃, hF, hF₀, hF₁, hF₂, hF₃⟩ := exists_c24FlagData F
  obtain ⟨u₀, u₁, x₂, x₃, hG, hG₀, hG₁, hG₂, hG₃⟩ := exists_c24FlagData G
  obtain ⟨φ, sφ, e₀, e₁, e₂, e₃⟩ := exists_isSymmetry_c24FlagData hF hG
  have hd := isPolarDual_cell24Dual_cell24.symm
  have φ0 := cell24_isSymmetry_fixes_zero sφ
  refine ⟨φ, sφ, fun k ↦ ?_⟩
  obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by lia
  · rw [hF₀, hG₀, Set.image_singleton, e₀]
  · rw [hF₁, hG₁, isom_image_convexHull]
    congr 1
    rw [Set.image_pair, e₀, e₁]
  · have dd₁ := hd.faceDual_faceDual (F.isFace 2) (by rw [F.dim_eq 2]; lia)
    have dd₂ := hd.faceDual_faceDual (G.isFace 2) (by rw [G.dim_eq 2]; lia)
    rw [← dd₁, ← dd₂, hF₂, hG₂]
    refine isPolarDual_cell24Dual_cell24.isom_apply (isSymmetry_cell24Dual_of_cell24 sφ) φ0 ?_
    rw [isom_image_convexHull]
    congr 1
    rw [Set.image_pair, e₂, e₃]
  · have dd₁ := hd.faceDual_faceDual (F.isFace 3) (by rw [F.dim_eq 3]; lia)
    have dd₂ := hd.faceDual_faceDual (G.isFace 3) (by rw [G.dim_eq 3]; lia)
    rw [← dd₁, ← dd₂, hF₃, hG₃]
    refine isPolarDual_cell24Dual_cell24.isom_apply (isSymmetry_cell24Dual_of_cell24 sφ) φ0 ?_
    rw [Set.image_singleton, e₃]
