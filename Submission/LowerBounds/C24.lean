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

open Matrix in
lemma similar_cell24Dual_cell24_aux {I : C24Index} :
    (2⁻¹ : ℝ) • .toLp _ (!![-1,1,0,0; 1,1,0,0; 0,0,1,1; 0,0,1,-1] *ᵥ cell24DualVert I) ∈
    cell24.vertices := by
  simp_rw [cell24DualVert, WithLp.ofLp_add, PiLp.ofLp_single, cons_mulVec, empty_mulVec,
    dotProduct_add, dotProduct_single, cell24, mem_image, mem_univ, true_and]
  obtain ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ :
      I.a = 0 ∧ I.b = 1 ∨ I.a = 2 ∧ I.b = 3 ∨ I.a = 0 ∧ I.b = 2 ∨ I.a = 0 ∧ I.b = 3 ∨
      I.a = 1 ∧ I.b = 2 ∨ I.a = 1 ∧ I.b = 3 := by grind [I.l]
  all_goals simp only [ha, hb, Matrix.cons_val, neg_one_mul, zero_mul, one_mul, zero_add, add_zero]
  · refine ⟨.inl (if I.s = I.t then 1 else 0, I.t), ?_⟩
    rw [cell24Vert, Sum.elim_inl, WithLp.toLp.injEq]
    simp_rw [WithLp.ofLp_smul, PiLp.ofLp_single]
    ext i; fin_cases i <;> cases I.s <;> cases I.t <;> norm_num
  · refine ⟨.inl (if I.s = I.t then 2 else 3, I.s), ?_⟩
    rw [cell24Vert, Sum.elim_inl, WithLp.toLp.injEq]
    simp_rw [WithLp.ofLp_smul, PiLp.ofLp_single]
    ext i; fin_cases i <;> cases I.s <;> cases I.t <;>
    simp only [Pi.single_apply, Bool.false_eq_true, Bool.true_eq_false, reduceIte, Pi.smul_apply,
      Fin.reduceFinMk, Fin.reduceEq, Matrix.cons_val] <;> norm_num
  · refine ⟨.inr ![!I.s, I.s, I.t, I.t], ?_⟩
    rw [cell24Vert, Sum.elim_inr, WithLp.toLp.injEq]
    simp_rw [WithLp.ofLp_smul]
    ext i; fin_cases i <;> cases I.s <;> cases I.t <;> simp
  · refine ⟨.inr ![!I.s, I.s, I.t, !I.t], ?_⟩
    rw [cell24Vert, Sum.elim_inr, WithLp.toLp.injEq]
    simp_rw [WithLp.ofLp_smul]
    ext i; fin_cases i <;> cases I.s <;> cases I.t <;> simp
  · refine ⟨.inr ![I.s, I.s, I.t, I.t], ?_⟩
    rw [cell24Vert, Sum.elim_inr, WithLp.toLp.injEq]
    simp_rw [WithLp.ofLp_smul]
    ext i; fin_cases i <;> cases I.s <;> cases I.t <;> simp
  · refine ⟨.inr ![I.s, I.s, I.t, !I.t], ?_⟩
    rw [cell24Vert, Sum.elim_inr, WithLp.toLp.injEq]
    simp_rw [WithLp.ofLp_smul]
    ext i; fin_cases i <;> cases I.s <;> cases I.t <;> simp

open Matrix in
/-- The 24-cell is self-dual. -/
lemma similar_cell24Dual_cell24 : cell24Dual.Similar cell24 := by
  let R : Matrix (Fin 4) (Fin 4) ℝ := (√2)⁻¹ • !![-1,1,0,0; 1,1,0,0; 0,0,1,1; 0,0,1,-1]
  have oR : R ∈ orthogonalGroup (Fin 4) ℝ := by
    simp_rw [mem_orthogonalGroup_iff, R, transpose_smul, smul_mul_smul_comm, ← mul_inv,
      mul_self_sqrt zero_le_two]
    ext i j
    simp_rw [Matrix.smul_apply, mul_apply, transpose_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [show 2⁻¹ * (1 + 1 : ℝ) = 1 by norm_num]
  refine ⟨(√2)⁻¹, by positivity, toIsom ⟨R, oR⟩ 0, ?_⟩
  rw [toSet, toSet, isom_image_convexHull, smul_image_convexHull (by positivity)]
  congr; symm; apply Set.eq_of_subset_of_card_le
  · simp only [Set.image_subset_iff]
    intro v mv
    simp only [cell24Dual, mem_coe, mem_image, Set.mem_preimage] at *
    obtain ⟨I, -, rfl⟩ := mv
    simp_rw [toIsom_apply, WithLp.ofLp_zero, add_zero, R, smul_mulVec, WithLp.toLp_smul, smul_smul]
    rw [← mul_inv, mul_self_sqrt (by positivity)]
    exact similar_cell24Dual_cell24_aux
  · rw [Set.card_image_of_injective _ (smul_right_injective _ (by positivity)),
      Set.card_image_of_injective _ fun _ _ ↦ by simp]
    simp [card_cell24_vertices, card_cell24Dual_vertices]

theorem cell24_isRegular : cell24.IsRegular := by
  sorry
