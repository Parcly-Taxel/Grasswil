import Submission.LowerBounds.Lemmas
import Submission.PolarDual
import Submission.Symmetry

open Real Finset Matrix LeanEval.Geometry.PlatonicClassification ConvexPolytope

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

/-- The unconstrained function underlying `cell24DualVert`. -/
noncomputable abbrev twoE4 (a b : Fin 4) (s t : Bool) : E 4 :=
  .single a (if s then -1 else 1) + .single b (if t then -1 else 1)

/-- The dual 24-cell's vertex function. -/
noncomputable def cell24DualVert (I : C24Index) : E 4 := twoE4 I.a I.b I.s I.t

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

lemma exists_cell24Vert_param {v : E 4} (mv : v ∈ cell24.vertices) : ∃ t, v = cell24Vert t := by
  simpa [cell24, eq_comm] using mv

lemma card_cell24_vertices : #cell24.vertices = 24 := by
  simp [cell24, card_image_of_injective _ injective_cell24Vert]

lemma card_cell24Dual_vertices : #cell24Dual.vertices = 24 := by
  rw [cell24Dual, card_image_of_injective _ injective_cell24DualVert]
  decide

/-! ### Self-duality of the 24-cell -/

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

theorem isPolarDual_cell24Dual_cell24 : IsPolarDual cell24Dual cell24 := by
  rw [IsPolarDual, cell24_toSet_eq, cell24Dual_polar_eq]

/-! ### Symmetries of the 24-cell -/

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

lemma isSymmetry_cell24_coordPerm {σ : Equiv.Perm (Fin 4)} :
    cell24.isSymmetry (toIsom (coordPerm σ) 0) := by
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

lemma isSymmetry_cell24_coordFlip {m : Fin 4 → Bool} :
    cell24.isSymmetry (toIsom (coordFlip m) 0) := by
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

lemma coordPerm_twoE4 {a b : Fin 4} {s t : Bool} {σ : Equiv.Perm (Fin 4)} :
    toIsom (coordPerm σ) 0 (twoE4 a b s t) = twoE4 (σ⁻¹ a) (σ⁻¹ b) s t := by
  rw [toIsom_add]
  apply congrArg₂ (· + ·) <;> ext i <;>
  simp [toIsom_apply, coordPerm, permMatrix_mulVec, -PiLp.ofLp_single, σ.eq_symm_apply]

lemma coordFlip_twoE4 {a b : Fin 4} {s t : Bool} {m : Fin 4 → Bool} :
    toIsom (coordFlip m) 0 (twoE4 a b s t) = twoE4 a b (m a ^^ s) (m b ^^ t) := by
  rw [toIsom_add]
  apply congrArg₂ (· + ·) <;> ext i <;> simp_rw [toIsom_apply, WithLp.ofLp_zero, add_zero,
    coordFlip, mulVec_diagonal, PiLp.single_apply] <;> split_ifs <;> simp_all

/-- **Half** a Hada**mard** matrix, a reflection sending `(½, ½, ½, ½)` to `(1, 0, 0, 0)`. -/
noncomputable def halfmard : orthogonalGroup (Fin 4) ℝ where
  val := (2⁻¹ : ℝ) • !![1,1,1,1; 1,1,-1,-1; 1,-1,1,-1; 1,-1,-1,1]
  property := by
    rw [mem_orthogonalGroup_iff, transpose_smul, smul_mul_smul_comm]
    ext i j
    simp_rw [Matrix.smul_apply, mul_apply, Fin.sum_univ_four, transpose_apply]
    fin_cases i <;> fin_cases j <;> simp [show 2⁻¹ * 2⁻¹ * (1 + 1 + 1 + 1 : ℝ) = 1 by norm_num]

lemma halfmard_mul_self : halfmard.1 * halfmard.1 = 1 := by
  ext i j
  rw [halfmard, smul_mul_smul_comm, Matrix.smul_apply, mul_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp [show 2⁻¹ * 2⁻¹ * (1 + 1 + 1 + 1 : ℝ) = 1 by norm_num]

lemma halfmard_involutive (v : E 4) : toIsom halfmard 0 (toIsom halfmard 0 v) = v := by
  simp_rw [toIsom_apply, WithLp.ofLp_zero, add_zero, mulVec_mulVec, halfmard_mul_self, one_mulVec]

lemma halfmard_apply_zero (v : E 4) : toIsom halfmard 0 v 0 = 2⁻¹ * (v 0 + v 1 + v 2 + v 3) := by
  simp [toIsom_apply, halfmard, dotProduct, Fin.sum_univ_four]
  ring

lemma halfmard_apply_one (v : E 4) : toIsom halfmard 0 v 1 = 2⁻¹ * (v 0 + v 1 - v 2 - v 3) := by
  simp [toIsom_apply, halfmard, dotProduct, Fin.sum_univ_four]
  ring

lemma halfmard_apply_two (v : E 4) : toIsom halfmard 0 v 2 = 2⁻¹ * (v 0 - v 1 + v 2 - v 3) := by
  simp [toIsom_apply, halfmard, dotProduct, Fin.sum_univ_four]
  ring

lemma halfmard_apply_three (v : E 4) : toIsom halfmard 0 v 3 = 2⁻¹ * (v 0 - v 1 - v 2 + v 3) := by
  simp [toIsom_apply, halfmard, dotProduct, Fin.sum_univ_four]
  ring

lemma abs_add_abs_le_one {x y p q : ℝ} (hx : x = 2⁻¹ * (p + q)) (hy : y = 2⁻¹ * (p - q))
    (hp : |p| ≤ 1) (hq : |q| ≤ 1) : |x| + |y| ≤ 1 := by
  obtain ⟨hp₁, hp₂⟩ := abs_le.mp hp
  obtain ⟨hq₁, hq₂⟩ := abs_le.mp hq
  rcases abs_cases x with ⟨ex, -⟩ | ⟨ex, -⟩ <;> rcases abs_cases y with ⟨ey, -⟩ | ⟨ey, -⟩ <;>
    rw [ex, ey, hx, hy] <;> linarith

lemma mapsTo_halfmard {v : E 4} (hv : v ∈ cell24.toSet) : toIsom halfmard 0 v ∈ cell24.toSet := by
  rw [cell24_toSet_eq] at hv ⊢
  have hb (a b) (hab : a ≠ b) : |v a| + |v b| ≤ 1 := by
    rcases hab.lt_or_gt with h | h
    · exact hv a b h
    · rw [add_comm]
      exact hv b a h
  have hadd (a b) (hab : a ≠ b) : |v a + v b| ≤ 1 := (abs_add_le ..).trans (hb a b hab)
  have hsub (a b) (hab : a ≠ b) : |v a - v b| ≤ 1 := by
    rw [sub_eq_add_neg]
    refine (abs_add_le ..).trans ?_
    rw [abs_neg]
    exact hb a b hab
  intro i j hij
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ :
      i = 0 ∧ j = 1 ∨ i = 0 ∧ j = 2 ∨ i = 0 ∧ j = 3 ∨ i = 1 ∧ j = 2 ∨ i = 1 ∧ j = 3 ∨
        i = 2 ∧ j = 3 := by lia
  · exact abs_add_abs_le_one ((halfmard_apply_zero v).trans (by ring))
      ((halfmard_apply_one v).trans (by ring)) (hadd 0 1 (by lia)) (hadd 2 3 (by lia))
  · exact abs_add_abs_le_one ((halfmard_apply_zero v).trans (by ring))
      ((halfmard_apply_two v).trans (by ring)) (hadd 0 2 (by lia)) (hadd 1 3 (by lia))
  · exact abs_add_abs_le_one ((halfmard_apply_zero v).trans (by ring))
      ((halfmard_apply_three v).trans (by ring)) (hadd 0 3 (by lia)) (hadd 1 2 (by lia))
  · exact abs_add_abs_le_one ((halfmard_apply_one v).trans (by ring))
      ((halfmard_apply_two v).trans (by ring)) (hsub 0 3 (by lia)) (hsub 1 2 (by lia))
  · exact abs_add_abs_le_one ((halfmard_apply_one v).trans (by ring))
      ((halfmard_apply_three v).trans (by ring)) (hsub 0 2 (by lia)) (hsub 1 3 (by lia))
  · exact abs_add_abs_le_one ((halfmard_apply_two v).trans (by ring))
      ((halfmard_apply_three v).trans (by ring)) (hsub 0 1 (by lia)) (hsub 2 3 (by lia))

lemma isSymmetry_cell24_halfmard : cell24.isSymmetry (toIsom halfmard 0) :=
  subset_antisymm (Set.image_subset_iff.mpr fun _ hv ↦ mapsTo_halfmard hv)
    fun v hv ↦ ⟨_, mapsTo_halfmard hv, halfmard_involutive v⟩

lemma halfmard_half : toIsom halfmard 0 (cell24Vert (.inr fun _ ↦ false)) =
    cell24Vert (.inl (0, false)) := by
  ext i
  obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by lia
  · rw [halfmard_apply_zero]
    norm_num [cell24Vert]
  · rw [halfmard_apply_one]
    simp [cell24Vert]
  · rw [halfmard_apply_two]
    simp [cell24Vert]
  · rw [halfmard_apply_three]
    simp [cell24Vert]

/-! ### Flags of the 24-cell -/

variable {φ : Isom 4} (sφ : cell24.isSymmetry φ)

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

include sφ in
lemma cell24_sym_zero : φ 0 = 0 := by
  simpa [centroid_cell24_vertices] using sφ.map_centroid

include sφ in
lemma isSymmetry_cell24Dual_of_cell24 : cell24Dual.isSymmetry φ :=
  isPolarDual_cell24Dual_cell24.symm.isSymmetry sφ (cell24_sym_zero sφ)

/-- `C24FlagData` holds four vertices that together define a flag of the 24-cell:
* the vertex is `{v 0}`
* the edge is `convexHull ℝ {v 0, v 1}`
* the face is `convexHull ℝ {w 0, w 1}`'s **dual**
* the cell is `{w 1}`'s **dual** -/
structure C24FlagData where
  /-- The four defining vertices -/
  (v w : Fin 2 → E 4)
  /-- `v i` is a vertex of the primal 24-cell -/
  mv (i) : v i ∈ cell24.vertices
  /-- `w i` is a vertex of the dual 24-cell -/
  mw (i) : w i ∈ cell24Dual.vertices
  /-- `v 0 ≠ v 1` -/
  nv : v 0 ≠ v 1
  /-- `w 0 ≠ w 1` -/
  nw : w 0 ≠ w 1
  /-- `v i` lies on `w j`'s dual -/
  vw (i j) : inner ℝ (v i) (w j) = 1

/-- Map `C24FlagData` over a 24-cell symmetry. -/
noncomputable def C24FlagData.map (FD : C24FlagData) : C24FlagData where
  v i := φ (FD.v i)
  w i := φ (FD.w i)
  mv i := by
    rw [← sφ.image_vertices]
    exact mem_image_of_mem _ (FD.mv i)
  mw i := by
    rw [← (isSymmetry_cell24Dual_of_cell24 sφ).image_vertices]
    exact mem_image_of_mem _ (FD.mw i)
  nv e := FD.nv (φ.injective e)
  nw e := FD.nw (φ.injective e)
  vw i j := by
    have l (z) : φ.linearIsometryEquiv z = φ z := by simpa [cell24_sym_zero sφ] using φ.map_vsub z 0
    simp [← l, FD.vw]

theorem cell24_flag_characterisation (F : cell24.Flag) : ∃ FD : C24FlagData,
    F.face 0 = {FD.v 0} ∧ F.face 1 = convexHull ℝ {FD.v 0, FD.v 1} ∧
    faceDual cell24Dual (F.face 2) = convexHull ℝ {FD.w 0, FD.w 1} ∧
    faceDual cell24Dual (F.face 3) = {FD.w 1} := by
  have pd := isPolarDual_cell24Dual_cell24.symm
  -- Obtain `v 0` and `v 1`
  obtain ⟨v₀, mv₀, F₀⟩ := zero_dim_face_iff_vertex.mp ⟨F.isFace 0, F.dim_eq 0⟩
  obtain ⟨a, ma, b, mb, nab, F₁⟩ := one_dim_face_is_edge (F.isFace 1) (F.dim_eq 1)
  have mv₀₁ : v₀ ∈ convexHull ℝ {a, b} := F₁ ▸ F.mono zero_le_one (by simp [F₀])
  obtain ⟨v₁, mv₁, nv, F₁'⟩ :
      ∃ v₁ ∈ cell24.vertices, v₀ ≠ v₁ ∧ F.face 1 = convexHull ℝ {v₀, v₁} := by
    obtain rfl | rfl := mem_pair_of_mem_convexHull_pair mv₀ ma mb mv₀₁
    · exact ⟨b, mb, nab, F₁⟩
    · exact ⟨a, ma, nab.symm, by rwa [Set.pair_comm]⟩
  -- Obtain `w 0` and `w 1`
  obtain ⟨w₃, mw₃, F₃⟩ := zero_dim_face_iff_vertex.mp
    ⟨pd.isFace (F.isFace 3) (by simp [F.dim_eq 3]), by
      simpa using pd.dim_eq (F.isFace 3) (F.dim_eq 3)⟩
  obtain ⟨p, mp, q, mq, npq, F₂⟩ := one_dim_face_is_edge
    (pd.isFace (F.isFace 2) (by simp [F.dim_eq 2]))
    (by simpa using pd.dim_eq (F.isFace 2) (F.dim_eq 2))
  have mw₃₂ : w₃ ∈ convexHull ℝ {p, q} :=
    F₂ ▸ IsPolarDual.faceDual_subset (F.mono (show 2 ≤ 3 by lia)) (by simp [F₃])
  obtain ⟨w₂, mw₂, nw, F₂'⟩ : ∃ w₂ ∈ cell24Dual.vertices, w₂ ≠ w₃ ∧
      faceDual cell24Dual (F.face 2) = convexHull ℝ {w₂, w₃} := by
    obtain rfl | rfl := mem_pair_of_mem_convexHull_pair mw₃ mp mq mw₃₂
    · exact ⟨q, mq, npq.symm, by rwa [Set.pair_comm]⟩
    · exact ⟨p, mp, npq, F₂⟩
  -- Construct the required data
  refine ⟨⟨![v₀, v₁], ![w₂, w₃], fun i ↦ ?_, fun i ↦ ?_, nv, nw, fun i j ↦ ?_⟩, F₀, F₁', F₂', F₃⟩
  · fin_cases i; exacts [mv₀, mv₁]
  · fin_cases i; exacts [mw₂, mw₃]
  · have key {v w} (mv : v ∈ F.face 2) (mw : w ∈ faceDual cell24Dual (F.face 2)) :
        inner ℝ v w = 1 := Set.mem_iInter₂.mp mw.2 v mv
    have mw₂d : w₂ ∈ faceDual cell24Dual (F.face 2) := F₂' ▸ subset_convexHull ℝ _ (by simp)
    have mw₃d : w₃ ∈ faceDual cell24Dual (F.face 2) := F₂' ▸ subset_convexHull ℝ _ (by simp)
    have mv₀₂ : v₀ ∈ F.face 2 := F.mono (show 0 ≤ 2 by lia) (F₀ ▸ rfl)
    have mv₁₂ : v₁ ∈ F.face 2 := F.mono (show 1 ≤ 2 by lia) (F₁' ▸ subset_convexHull ℝ _ (by simp))
    fin_cases i <;> fin_cases j
    exacts [key mv₀₂ mw₂d, key mv₀₂ mw₃d, key mv₁₂ mw₂d, key mv₁₂ mw₃d]

lemma cell24_vertex_transitive {v : E 4} (mv : v ∈ cell24.vertices) :
    ∃ φ, cell24.isSymmetry φ ∧ φ v = cell24Vert (.inl (0, false)) := by
  obtain ⟨t, rfl⟩ := exists_cell24Vert_param mv
  cases t with
  | inl p =>
    obtain ⟨i, s⟩ := p
    refine ⟨toIsom (coordPerm (Equiv.swap 0 i)) 0 * toIsom (coordFlip fun _ ↦ s) 0,
      isSymmetry_cell24_coordPerm.mul isSymmetry_cell24_coordFlip, ?_⟩
    simp_rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, coordFlip_cell24Vert, Sum.map_inl,
      Bool.xor_self, coordPerm_cell24Vert, Sum.map_inl, Equiv.swap_inv, Equiv.swap_apply_right]
  | inr m =>
    refine ⟨toIsom halfmard 0 * toIsom (coordFlip m) 0,
      isSymmetry_cell24_halfmard.mul isSymmetry_cell24_coordFlip, ?_⟩
    simp_rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, coordFlip_cell24Vert, Sum.map_inr,
      Bool.xor_self]
    exact halfmard_half

lemma inner_twoE4 {a b : Fin 4} {s t : Bool} {v : E 4} :
    inner ℝ v (twoE4 a b s t) = (if s then -1 else 1) * v a + (if t then -1 else 1) * v b := by
  simp [inner_add_right, EuclideanSpace.inner_single_right]

lemma eq_of_inner_twoE4 {a b : Fin 4} {s t : Bool} (nb : b ≠ 0)
    (nv : cell24Vert (.inl (0, false)) ≠ cell24Vert (.inl (a, s)))
    (h : inner ℝ (cell24Vert (.inl (a, s))) (twoE4 0 b false t) = 1) : a = b ∧ s = t := by
  simp_rw [inner_twoE4, cell24Vert, Sum.elim_inl, PiLp.single_apply] at h
  grind

lemma exists_twoE4_params {w : E 4} (mw : w ∈ cell24Dual.vertices)
    (h : inner ℝ (cell24Vert (.inl (0, false))) w = 1) : ∃ a s, a ≠ 0 ∧ w = twoE4 0 a false s := by
  simp_rw [cell24Dual, mem_image, cell24DualVert] at mw
  obtain ⟨⟨a, b, s, t, l⟩, -, rfl⟩ := mw
  simp_rw [inner_twoE4, cell24Vert, Sum.elim_inl, Bool.false_eq_true, reduceIte,
    PiLp.single_apply] at h
  obtain rfl | na := eq_or_ne a 0
  · exact ⟨b, t, l.ne', by grind⟩
  · grind

lemma exists_C24FlagData_params (FD : C24FlagData) (v₀ : FD.v 0 = cell24Vert (.inl (0, false))) :
    ∃ m : Fin 4 → Bool, ∃ a ≠ 0, ∃ b ≠ 0, m 0 = false ∧ a ≠ b ∧ FD.v 1 = cell24Vert (.inr m) ∧
    FD.w 0 = twoE4 0 b false (m b) ∧ FD.w 1 = twoE4 0 a false (m a) := by
  obtain ⟨a, s, na, w₃⟩ := exists_twoE4_params (FD.mw 1) (v₀ ▸ FD.vw 0 1)
  obtain ⟨b, t, nb, w₂⟩ := exists_twoE4_params (FD.mw 0) (v₀ ▸ FD.vw 0 0)
  obtain ⟨t', v₁⟩ := exists_cell24Vert_param (FD.mv 1)
  cases t' with
  | inl p =>
    obtain ⟨i, u⟩ := p
    obtain ⟨rfl, rfl⟩ := eq_of_inner_twoE4 na (v₀ ▸ v₁ ▸ FD.nv) (v₁ ▸ w₃ ▸ FD.vw 1 1)
    obtain ⟨rfl, rfl⟩ := eq_of_inner_twoE4 nb (v₀ ▸ v₁ ▸ FD.nv) (v₁ ▸ w₂ ▸ FD.vw 1 0)
    exact (w₂ ▸ w₃ ▸ FD.nw).elim rfl
  | inr u =>
    have i₁₂ := FD.vw 1 0
    have i₁₃ := FD.vw 1 1
    simp_rw [v₁, w₂, w₃, inner_twoE4, cell24Vert, Sum.elim_inr] at i₁₂ i₁₃
    obtain ⟨u₀, rfl, rfl⟩ : u 0 = false ∧ s = u a ∧ t = u b := by grind
    exact ⟨u, a, na, b, nb, u₀, fun con ↦ (con ▸ w₂ ▸ w₃ ▸ FD.nw).elim rfl, v₁, w₂, w₃⟩

lemma cell24_flag_transitive_aux (FD : C24FlagData) : ∃ φ, cell24.isSymmetry φ ∧
    φ (FD.v 0) = cell24Vert (.inl (0, false)) ∧ φ (FD.v 1) = cell24Vert (.inr fun _ ↦ false) ∧
    φ (FD.w 0) = twoE4 0 2 false false ∧ φ (FD.w 1) = twoE4 0 1 false false := by
  obtain ⟨φ, sφ, hφ⟩ := cell24_vertex_transitive (FD.mv 0)
  obtain ⟨m, b, hb, c, hc, m₀, nbc, e₁, e₂, e₃⟩ := exists_C24FlagData_params (FD.map sφ) hφ
  simp_rw [C24FlagData.map] at e₁ e₂ e₃
  obtain ⟨σ, hσ0, hσb, hσc⟩ : ∃ σ : Equiv.Perm (Fin 4), σ 0 = 0 ∧ σ b = 1 ∧ σ c = 2 := by
    clear! FD φ; decide +revert
  refine ⟨toIsom (coordPerm σ⁻¹) 0 * toIsom (coordFlip m) 0 * φ,
    (isSymmetry_cell24_coordPerm.mul isSymmetry_cell24_coordFlip).mul sφ, ?_, ?_, ?_, ?_⟩ <;>
  simp_rw [AffineIsometryEquiv.coe_mul, Function.comp_apply]
  · simp_rw [hφ, coordFlip_cell24Vert, Sum.map_inl, m₀, Bool.xor_self, coordPerm_cell24Vert,
      Sum.map_inl, inv_inv, hσ0]
  · simp_rw [e₁, coordFlip_cell24Vert, Sum.map_inr, Bool.xor_self, coordPerm_cell24Vert,
      Sum.map_inr, Function.false_comp]
  · simp_rw [e₂, coordFlip_twoE4, m₀, Bool.xor_self, coordPerm_twoE4, inv_inv, hσ0, hσc]
  · simp_rw [e₃, coordFlip_twoE4, m₀, Bool.xor_self, coordPerm_twoE4, inv_inv, hσ0, hσb]

lemma cell24_flag_transitive (FD GD : C24FlagData) :
    ∃ φ, cell24.isSymmetry φ ∧ ∀ i, φ (FD.v i) = GD.v i ∧ φ (FD.w i) = GD.w i := by
  obtain ⟨φ, sφ, F₀, F₁, F₂, F₃⟩ := cell24_flag_transitive_aux FD
  obtain ⟨ψ, sψ, G₀, G₁, G₂, G₃⟩ := cell24_flag_transitive_aux GD
  refine ⟨ψ⁻¹ * φ, sψ.inv.mul sφ, fun i ↦ ?_⟩
  fin_cases i
  · simp [F₀, F₂, ← G₀, ← G₂]
  · simp [F₁, F₃, ← G₁, ← G₃]

theorem cell24_isRegular : cell24.IsRegular := by
  have pd := isPolarDual_cell24Dual_cell24
  refine ⟨pd.symm.isFullDim, fun F G ↦ ?_⟩
  obtain ⟨FD, F₀, F₁, F₂, F₃⟩ := cell24_flag_characterisation F
  obtain ⟨GD, G₀, G₁, G₂, G₃⟩ := cell24_flag_characterisation G
  obtain ⟨φ, sφ, e⟩ := cell24_flag_transitive FD GD
  refine ⟨φ, sφ, fun i ↦ ?_⟩
  obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by lia
  · rw [F₀, G₀, Set.image_singleton, (e 0).1]
  · rw [F₁, G₁, isom_image_convexHull, Set.image_pair, (e 0).1, (e 1).1]
  · have dd₁ := pd.symm.faceDual_faceDual (F.isFace 2) (by simp [F.dim_eq 2])
    have dd₂ := pd.symm.faceDual_faceDual (G.isFace 2) (by simp [G.dim_eq 2])
    rw [← dd₁, ← dd₂, F₂, G₂]
    apply pd.isom_apply (isSymmetry_cell24Dual_of_cell24 sφ) (cell24_sym_zero sφ)
    rw [isom_image_convexHull, Set.image_pair, (e 0).2, (e 1).2]
  · have dd₁ := pd.symm.faceDual_faceDual (F.isFace 3) (by simp [F.dim_eq 3])
    have dd₂ := pd.symm.faceDual_faceDual (G.isFace 3) (by simp [G.dim_eq 3])
    rw [← dd₁, ← dd₂, F₃, G₃]
    apply pd.isom_apply (isSymmetry_cell24Dual_of_cell24 sφ) (cell24_sym_zero sφ)
    rw [Set.image_singleton, (e 1).2]
