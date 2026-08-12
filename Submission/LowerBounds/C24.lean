import Submission.LowerBounds.C24Flags

open Real Finset Matrix LeanEval.Geometry.PlatonicClassification ConvexPolytope

variable {t : Fin 3 × Fin 4 × Bool}

lemma demitessR_cell24Vert : (toIsom ⟨demitessR, demitessR_mem_orthogonalGroup⟩ 0) (cell24Vert t) =
    cell24Vert (t.1 + 1, t.2.1, t.2.2) := by
  ext j
  simp_rw [toIsom_apply, WithLp.ofLp_zero, add_zero, cell24Vert, mulVec_mulVec, ← pow_succ']
  congr 1
  obtain t₁ | t₁ | t₁ : t.1 = 0 ∨ t.1 = 1 ∨ t.1 = 2 := by lia
  all_goals simp [t₁, demitessR_pow_three]

lemma isSymmetry_cell24_demitessR :
    cell24.isSymmetry (toIsom ⟨demitessR, demitessR_mem_orthogonalGroup⟩ 0) := by
  set R := toIsom ⟨demitessR, demitessR_mem_orthogonalGroup⟩ 0
  let vs := cell24.vertices
  have im : R '' vs = vs := by
    apply Set.eq_of_subset_of_card_le
    · rw [Set.image_subset_iff]
      intro v hv
      simp only [vs, cell24, mem_coe, mem_image, Set.mem_preimage] at *
      obtain ⟨t, -, rfl⟩ := hv
      exact ⟨(t.1 + 1, t.2.1, t.2.2), mem_univ _, demitessR_cell24Vert.symm⟩
    · rw [Set.card_image_of_injective _ R.injective]
  have ch := isom_image_convexHull R vs
  rwa [im] at ch

section Coord

variable {n : ℕ} {x : E n} {i : Fin n}

lemma coordPerm_isom_apply {σ : Equiv.Perm (Fin n)} : toIsom (coordPerm σ) 0 x i = x (σ i) := by
  simp [toIsom_apply, coordPerm, permMatrix_mulVec]

lemma coordFlip_isom_apply {m : Fin n → Bool} :
    toIsom (coordFlip m) 0 x i = if m i then -x i else x i := by
  simp [toIsom_apply, coordFlip, mulVec_diagonal]

end Coord

lemma demitessIsom_apply {x : E 4} {i : Fin 4} :
    toIsom ⟨demitessR, demitessR_mem_orthogonalGroup⟩ 0 x i = ∑ j, demitessR i j * x j := by
  simp [toIsom_apply, mulVec, dotProduct]

/-- The vertex of the 24-cell all of whose coordinates are `±2⁻¹`, with signs given by `m`. -/
noncomputable def cell24HalfVert (m : Fin 4 → Bool) : E 4 :=
  .toLp _ fun i ↦ if m i then -2⁻¹ else 2⁻¹

lemma cell24HalfVert_apply {m : Fin 4 → Bool} {i : Fin 4} :
    cell24HalfVert m i = if m i then -2⁻¹ else 2⁻¹ := rfl

lemma injective_cell24HalfVert : cell24HalfVert.Injective := fun m m' e ↦ by
  ext i
  replace e := congr($e i)
  simp_rw [cell24HalfVert_apply] at e
  grind

lemma eq_cell24HalfVert {x : E 4} (hx : ∀ i, |x i| = 2⁻¹) :
    x = cell24HalfVert fun i ↦ decide (x i < 0) := by
  ext i
  have h := hx i
  rw [abs_eq (by norm_num)] at h
  rw [cell24HalfVert_apply]
  rcases h with h | h <;> simp [h]

lemma image_cell24Vert_eq_image_cell24HalfVert :
    (univ.filter fun t : Fin 3 × Fin 4 × Bool ↦ t.1 ≠ 0).image cell24Vert =
    univ.image cell24HalfVert := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [mem_image, mem_filter, mem_univ, true_and] at hx ⊢
    obtain ⟨t, ht, rfl⟩ := hx
    exact ⟨_, (eq_cell24HalfVert fun i ↦ abs_cell24Vert_apply ht).symm⟩
  · rw [card_image_of_injective _ injective_cell24HalfVert,
      card_image_of_injective _ injective_cell24Vert]
    decide

lemma cell24HalfVert_mem_vertices (m : Fin 4 → Bool) : cell24HalfVert m ∈ cell24.vertices := by
  have h : cell24HalfVert m ∈ univ.image cell24HalfVert := mem_image_of_mem _ (mem_univ m)
  rw [← image_cell24Vert_eq_image_cell24HalfVert, mem_image] at h
  obtain ⟨t, -, ht⟩ := h
  exact ht ▸ mem_image_of_mem _ (mem_univ t)

lemma cell24Vert_apply_of_fst_eq_zero (h : t.1 = 0) (j : Fin 4) :
    cell24Vert t j = if j = t.2.1 then (if t.2.2 then -1 else 1) else 0 := by
  simp_rw [cell24Vert, h, Fin.val_zero, pow_zero, one_mulVec]
  exact Pi.single_apply ..

lemma mem_cell24_vertices_iff {x : E 4} :
    x ∈ cell24.vertices ↔ (∃ i, |x i| = 1 ∧ ∀ j ≠ i, x j = 0) ∨ ∀ i, |x i| = 2⁻¹ := by
  constructor
  · intro hx
    obtain ⟨t, rfl⟩ := exists_cell24_params_single hx
    obtain h0 | h0 := eq_or_ne t.1 0
    · refine Or.inl ⟨t.2.1, ?_, fun j hj ↦ ?_⟩ <;> rw [cell24Vert_apply_of_fst_eq_zero h0]
      · simp [abs_ite]
      · rw [if_neg hj]
    · exact Or.inr fun i ↦ abs_cell24Vert_apply h0
  · rintro (⟨i, h1, h2⟩ | h)
    · have hx : x = cell24Vert (0, i, decide (x i < 0)) := by
        ext j
        rw [cell24Vert_apply_of_fst_eq_zero rfl]
        obtain rfl | hj := eq_or_ne j i
        · rw [abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at h1
          rcases h1 with h1 | h1 <;> simp [h1]
        · rw [if_neg hj]
          exact h2 j hj
      rw [hx]
      exact mem_image_of_mem _ (mem_univ _)
    · rw [eq_cell24HalfVert h]
      exact cell24HalfVert_mem_vertices _

lemma isSymmetry_cell24_one : cell24.isSymmetry 1 := by
  rw [ConvexPolytope.isSymmetry, AffineIsometryEquiv.coe_one, Set.image_id]

lemma isSymmetry_cell24_of_mapsTo {φ : Isom 4}
    (h : ∀ x ∈ cell24.vertices, φ x ∈ cell24.vertices) : cell24.isSymmetry φ := by
  have im : φ '' cell24.vertices = cell24.vertices := by
    apply Set.eq_of_subset_of_card_le
    · rintro - ⟨v, hv, rfl⟩
      exact h v hv
    · rw [Set.card_image_of_injective _ φ.injective]
  have ch := isom_image_convexHull φ cell24.vertices
  rwa [im] at ch

lemma isSymmetry_cell24_coordPerm {σ : Equiv.Perm (Fin 4)} :
    cell24.isSymmetry (toIsom (coordPerm σ) 0) := by
  refine isSymmetry_cell24_of_mapsTo fun x hx ↦ ?_
  rw [mem_cell24_vertices_iff] at hx ⊢
  obtain ⟨i, h1, h2⟩ | h := hx
  · refine Or.inl ⟨σ⁻¹ i, ?_, fun j hj ↦ ?_⟩ <;> rw [coordPerm_isom_apply]
    · simpa using h1
    · exact h2 _ fun hc ↦ hj (by simp [← hc])
  · exact Or.inr fun j ↦ by rw [coordPerm_isom_apply]; exact h _

lemma isSymmetry_cell24_coordFlip {m : Fin 4 → Bool} :
    cell24.isSymmetry (toIsom (coordFlip m) 0) := by
  refine isSymmetry_cell24_of_mapsTo fun x hx ↦ ?_
  rw [mem_cell24_vertices_iff] at hx ⊢
  obtain ⟨i, h1, h2⟩ | h := hx
  · refine Or.inl ⟨i, ?_, fun j hj ↦ ?_⟩ <;> rw [coordFlip_isom_apply]
    · rw [apply_ite abs, abs_neg, ite_self, h1]
    · rw [h2 j hj, neg_zero, ite_self]
  · exact Or.inr fun j ↦ by rw [coordFlip_isom_apply, apply_ite abs, abs_neg, ite_self]; exact h _

lemma cell24Vert_true_eq_neg {k : Fin 3} {c : Fin 4} :
    cell24Vert (k, c, true) = -cell24Vert (k, c, false) := by
  simp_rw [cell24Vert, ← WithLp.toLp_neg, ← mulVec_neg, ← Pi.single_neg]
  norm_num

lemma centroid_cell24_vertices : cell24.vertices.centroid ℝ id = 0 := by
  simp_rw [centroid_eq_inv_smul_sum cell24.vertices_nonempty, smul_eq_zero, id_eq]
  right
  rw [cell24, sum_image fun x _ y _ ↦ injective_cell24Vert.eq_iff.mp, Fintype.sum_prod_type]
  refine Fintype.sum_eq_zero _ fun k ↦ ?_
  rw [Fintype.sum_prod_type]
  refine Fintype.sum_eq_zero _ fun c ↦ ?_
  rw [Fintype.sum_bool, cell24Vert_true_eq_neg, neg_add_cancel]

lemma isSymmetry_cell24_map_zero {φ : Isom 4} (sφ : cell24.isSymmetry φ) : φ 0 = 0 := by
  simpa [centroid_cell24_vertices] using sφ.map_centroid

lemma isSymmetry_cell24_apply_eq_linear {φ : Isom 4} (sφ : cell24.isSymmetry φ) (x : E 4) :
    φ x = φ.linearIsometryEquiv x := by
  simpa [isSymmetry_cell24_map_zero sφ] using φ.map_vadd 0 x

lemma isSymmetry_cell24_inner {φ : Isom 4} (sφ : cell24.isSymmetry φ) (x y : E 4) :
    inner ℝ (φ x) (φ y) = inner ℝ x y := by
  rw [isSymmetry_cell24_apply_eq_linear sφ, isSymmetry_cell24_apply_eq_linear sφ,
    LinearIsometryEquiv.inner_map_map]

lemma isom_map_midpoint {n : ℕ} (φ : Isom n) (x y : E n) :
    φ (midpoint ℝ x y) = midpoint ℝ (φ x) (φ y) :=
  φ.toAffineMap.map_midpoint x y

lemma isom_inv_apply {n : ℕ} {φ : Isom n} {x y : E n} (h : φ x = y) : φ⁻¹ y = x := by
  rw [← h]
  change (φ⁻¹ * φ) x = x
  rw [inv_mul_cancel]
  rfl

namespace C24Index

variable (I : C24Index)

lemma toPoint_apply (j : Fin 4) : I.toPoint j =
    if j = I.a then (if I.s then -2⁻¹ else 2⁻¹)
    else if j = I.b then (if I.t then -2⁻¹ else 2⁻¹) else 0 := by
  rw [C24Index.toPoint]
  simp only [PiLp.add_apply, PiLp.single_apply]
  split_ifs with h1 h2 <;> simp_all [I.l.ne, I.l.ne']

lemma adjPoint_sub_toPoint (k : Fin 3) (b : Bool) : I.adjPoint k b - I.toPoint =
    (if b then -(2 : ℝ)⁻¹ else 2⁻¹) • (I.adjPoint k false - I.adjPoint k true) := by
  rw [← I.adjPoint_apply k]
  cases b
  · simp [invOf_eq_inv]
  · simp [invOf_eq_inv, neg_smul, ← smul_neg, neg_sub]

lemma inner_adjPoint_sub_toPoint_eq_zero {k k' : Fin 3} (hk : k ≠ k') {b b' : Bool} :
    inner ℝ (I.adjPoint k b - I.toPoint) (I.adjPoint k' b' - I.toPoint) = 0 := by
  rw [I.adjPoint_sub_toPoint, I.adjPoint_sub_toPoint, inner_smul_left, inner_smul_right,
    I.pairwise_adjPoint_vec_orthogonal hk]
  simp

lemma midpoint_adjPoint_ne_toPoint {k k' : Fin 3} (hk : k ≠ k') {b b' : Bool} :
    midpoint ℝ (I.adjPoint k b) (I.adjPoint k' b') ≠ I.toPoint := by
  intro h
  rw [midpoint_eq_smul_add, invOf_eq_inv, inv_smul_eq_iff₀ two_ne_zero, two_smul] at h
  have hz : I.adjPoint k' b' - I.toPoint = -(I.adjPoint k b - I.toPoint) := by
    rw [neg_sub, sub_eq_sub_iff_add_eq_add, add_comm]
    exact h
  have key := I.inner_adjPoint_sub_toPoint_eq_zero hk (b := b) (b' := b')
  rw [hz, inner_neg_right, I.inner_adjPoint_sub_toPoint_self] at key
  norm_num at key

lemma midpoint_adjPoint_not (k : Fin 3) (b : Bool) :
    midpoint ℝ (I.adjPoint k b) (I.adjPoint k !b) = I.toPoint := by
  cases b
  · exact I.adjPoint_apply k
  · rw [Bool.not_true, midpoint_comm]
    exact I.adjPoint_apply k

end C24Index

lemma exists_perm_apply_zero_one {a b : Fin 4} (h : a ≠ b) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = a ∧ σ 1 = b := by
  revert h
  revert a b
  decide

/-- The `C24Index` corresponding to the cell with centre `(1, 1, 0, 0)`. -/
def bC24I : C24Index where
  a := 0
  b := 1
  s := false
  t := false
  l := zero_lt_one

lemma cell24_cell_transitive (I : C24Index) :
    ∃ φ, cell24.isSymmetry φ ∧ φ I.toPoint = bC24I.toPoint := by
  obtain ⟨σ, σ0, σ1⟩ := exists_perm_apply_zero_one I.l.ne
  have ha (j) : σ j = I.a ↔ j = 0 := by rw [← σ0, σ.apply_eq_iff_eq]
  have hb (j) : σ j = I.b ↔ j = 1 := by rw [← σ1, σ.apply_eq_iff_eq]
  refine ⟨toIsom (coordFlip fun i ↦ if i = 0 then I.s else if i = 1 then I.t else false) 0 *
    toIsom (coordPerm σ) 0, isSymmetry_cell24_coordFlip.mul isSymmetry_cell24_coordPerm, ?_⟩
  ext j
  rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, coordFlip_isom_apply,
    coordPerm_isom_apply, C24Index.toPoint_apply, C24Index.toPoint_apply]
  simp only [ha, hb, bC24I]
  obtain rfl | h0 := eq_or_ne j 0
  · cases I.s <;> norm_num
  obtain rfl | h1 := eq_or_ne j 1
  · cases I.t <;> norm_num [h0]
  · simp [h0, h1]

lemma exists_adjPoint_image {φ : Isom 4} (sφ : cell24.isSymmetry φ) {I J : C24Index}
    (φI : φ I.toPoint = J.toPoint) (k : Fin 3) (b : Bool) :
    ∃ k' b', φ (I.adjPoint k b) = J.adjPoint k' b' := by
  have mv : φ (I.adjPoint k b) ∈ cell24.vertices := by
    rw [← sφ.image_vertices, mem_image]
    obtain ⟨c, s, hcs⟩ := I.exists_adjPoint_params k b
    exact ⟨_, hcs ▸ mem_image_of_mem _ (mem_univ (k, c, s)), rfl⟩
  obtain ⟨u, hu⟩ := exists_cell24_params_single mv
  have hinner : inner ℝ J.toPoint (cell24Vert u) = 2⁻¹ := by
    rw [← hu, ← φI, isSymmetry_cell24_inner sφ, I.inner_toPoint_adjPoint]
  obtain ⟨s, hs⟩ := (J.inner_toPoint_cell24Vert_eq_iff u).mp hinner
  exact ⟨u.1, s, by rw [hu, hs]⟩

lemma adjPoint_transfer_isom {φ : Isom 4} (sφ : cell24.isSymmetry φ) {I J : C24Index}
    (φI : φ I.toPoint = J.toPoint) (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) :
    ∃ p' : Equiv.Perm (Fin 3), ∃ s' : Fin 3 → Bool,
    ∀ i, φ (I.adjPoint (p i) (s i)) = J.adjPoint (p' i) (s' i) := by
  choose q b hq using fun i : Fin 3 ↦ exists_adjPoint_image sφ φI (p i) (s i)
  have inj : q.Injective := by
    intro i j e
    by_contra hn
    have hpn : p i ≠ p j := fun h ↦ hn (p.injective h)
    have hne : J.adjPoint (q i) (b i) ≠ J.adjPoint (q j) (b j) := by
      rw [← hq, ← hq, ne_eq, φ.injective.eq_iff]
      intro h
      exact hpn congr($(I.injective_adjPoint (a₁ := (p i, s i)) (a₂ := (p j, s j)) h).1)
    have hb : b j = !b i := by
      rw [e] at hne
      cases hbi : b i <;> cases hbj : b j <;> simp_all
    have key : midpoint ℝ (I.adjPoint (p i) (s i)) (I.adjPoint (p j) (s j)) = I.toPoint := by
      apply φ.injective
      rw [isom_map_midpoint, hq, hq, e, hb, J.midpoint_adjPoint_not, φI]
    exact I.midpoint_adjPoint_ne_toPoint hpn key
  exact ⟨Equiv.ofBijective q (Finite.injective_iff_bijective.mp inj), b, hq⟩

lemma bC24I_adj_0F : bC24I.adjPoint 0 false = !₂[1, 0, 0, 0] := by
  have dtps : (C24Index.demitessP 0).symm bC24I = bC24I := by ext <;> decide
  simp_rw [C24Index.adjPoint, dtps, C24Index.toPair, bC24I, cell24Vert, Fin.val_zero, pow_zero,
    one_mulVec]
  ext i
  fin_cases i <;> simp

lemma bC24I_adj_0T : bC24I.adjPoint 0 true = !₂[0, 1, 0, 0] := by
  have dtps : (C24Index.demitessP 0).symm bC24I = bC24I := by ext <;> decide
  simp_rw [C24Index.adjPoint, dtps, C24Index.toPair, bC24I, cell24Vert, Fin.val_zero, pow_zero,
    one_mulVec]
  ext i
  fin_cases i <;> simp

lemma bC24I_adj_1F : bC24I.adjPoint 1 false = !₂[2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹] := by
  have dtps : (C24Index.demitessP 1).symm bC24I = ⟨0, 1, true, false, zero_lt_one⟩ := by
    ext <;> decide
  simp_rw [C24Index.adjPoint, dtps, C24Index.toPair, cell24Vert, Fin.val_one, pow_one]
  ext i
  fin_cases i <;> simp [demitessR]

lemma bC24I_adj_1T : bC24I.adjPoint 1 true = !₂[2⁻¹, 2⁻¹, -2⁻¹, -2⁻¹] := by
  have dtps : (C24Index.demitessP 1).symm bC24I = ⟨0, 1, true, false, zero_lt_one⟩ := by
    ext <;> decide
  simp_rw [C24Index.adjPoint, dtps, C24Index.toPair, cell24Vert, Fin.val_one, pow_one]
  ext i
  fin_cases i <;> simp [demitessR]

lemma bC24I_adj_2F : bC24I.adjPoint 2 false = !₂[2⁻¹, 2⁻¹, -2⁻¹, 2⁻¹] := by
  have dtps : (C24Index.demitessP 2).symm bC24I = ⟨2, 3, true, true, by lia⟩ := by
    ext <;> decide
  simp_rw [C24Index.adjPoint, dtps, C24Index.toPair, cell24Vert, Fin.val_two, demitessR_sq]
  ext i
  fin_cases i <;> simp [demitessR]

lemma bC24I_adj_2T : bC24I.adjPoint 2 true = !₂[2⁻¹, 2⁻¹, 2⁻¹, -2⁻¹] := by
  have dtps : (C24Index.demitessP 2).symm bC24I = ⟨2, 3, true, true, by lia⟩ := by
    ext <;> decide
  simp_rw [C24Index.adjPoint, dtps, C24Index.toPair, cell24Vert, Fin.val_two, demitessR_sq]
  ext i
  fin_cases i <;> simp [demitessR]

lemma bC24I_toPoint : bC24I.toPoint = !₂[2⁻¹, 2⁻¹, 0, 0] := by
  ext i
  fin_cases i <;> simp [C24Index.toPoint, bC24I]

/-- A symmetry of the 24-cell that fixes the centre of the base cell
while cycling the three demitesseracts. -/
noncomputable def cell24TwistS : Isom 4 :=
  toIsom (coordFlip ![true, true, false, false]) 0 *
    toIsom (coordPerm (Equiv.swap 0 2 * Equiv.swap 1 3)) 0 *
    toIsom ⟨demitessR, demitessR_mem_orthogonalGroup⟩ 0

lemma isSymmetry_cell24_twistS : cell24.isSymmetry cell24TwistS :=
  (isSymmetry_cell24_coordFlip.mul isSymmetry_cell24_coordPerm).mul isSymmetry_cell24_demitessR

lemma cell24TwistS_toPoint : cell24TwistS !₂[2⁻¹, 2⁻¹, 0, 0] = !₂[2⁻¹, 2⁻¹, 0, 0] := by
  ext i
  simp only [cell24TwistS, AffineIsometryEquiv.coe_mul, Function.comp_apply, coordFlip_isom_apply,
    coordPerm_isom_apply, demitessIsom_apply]
  fin_cases i <;> simp [demitessR, Fin.sum_univ_four, Equiv.swap_apply_def] <;> norm_num

lemma cell24TwistS_adj : cell24TwistS !₂[1, 0, 0, 0] = !₂[2⁻¹, 2⁻¹, -2⁻¹, -2⁻¹] := by
  ext i
  simp only [cell24TwistS, AffineIsometryEquiv.coe_mul, Function.comp_apply, coordFlip_isom_apply,
    coordPerm_isom_apply, demitessIsom_apply]
  fin_cases i <;> simp [demitessR, Fin.sum_univ_four, Equiv.swap_apply_def]

lemma exists_symmetry_stab_map_adjPoint (k : Fin 3) (b : Bool) :
    ∃ φ, cell24.isSymmetry φ ∧ φ bC24I.toPoint = bC24I.toPoint ∧
      φ (bC24I.adjPoint k b) = bC24I.adjPoint 0 false := by
  have hpt : cell24TwistS⁻¹ bC24I.toPoint = bC24I.toPoint :=
    isom_inv_apply (by rw [bC24I_toPoint, cell24TwistS_toPoint])
  have hadj : cell24TwistS⁻¹ !₂[2⁻¹, 2⁻¹, -2⁻¹, -2⁻¹] = bC24I.adjPoint 0 false :=
    isom_inv_apply (by rw [bC24I_adj_0F, cell24TwistS_adj])
  have key (m : Fin 4 → Bool) (v : E 4)
      (h1 : toIsom (coordFlip m) 0 !₂[2⁻¹, 2⁻¹, 0, 0] = !₂[2⁻¹, 2⁻¹, 0, 0])
      (h2 : toIsom (coordFlip m) 0 v = !₂[2⁻¹, 2⁻¹, -2⁻¹, -2⁻¹]) :
      ∃ φ, cell24.isSymmetry φ ∧ φ bC24I.toPoint = bC24I.toPoint ∧
        φ v = bC24I.adjPoint 0 false := by
    refine ⟨cell24TwistS⁻¹ * toIsom (coordFlip m) 0,
      isSymmetry_cell24_twistS.inv.mul isSymmetry_cell24_coordFlip, ?_, ?_⟩
    · rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, bC24I_toPoint, h1, ← bC24I_toPoint, hpt]
    · rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, h2, hadj]
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by lia
  · cases b
    · exact ⟨1, isSymmetry_cell24_one, rfl, rfl⟩
    · refine ⟨toIsom (coordPerm (Equiv.swap 0 1)) 0, isSymmetry_cell24_coordPerm, ?_, ?_⟩
      · rw [bC24I_toPoint]
        ext i
        fin_cases i <;> simp [coordPerm_isom_apply, Equiv.swap_apply_def]
      · rw [bC24I_adj_0T, bC24I_adj_0F]
        ext i
        fin_cases i <;> simp [coordPerm_isom_apply, Equiv.swap_apply_def]
  · cases b
    · rw [bC24I_adj_1F]
      refine key ![false, false, true, true] _ ?_ ?_ <;> ext i <;>
        fin_cases i <;> simp [coordFlip_isom_apply]
    · rw [bC24I_adj_1T]
      refine key ![false, false, false, false] _ ?_ ?_ <;> ext i <;>
        fin_cases i <;> simp [coordFlip_isom_apply]
  · cases b
    · rw [bC24I_adj_2F]
      refine key ![false, false, false, true] _ ?_ ?_ <;> ext i <;>
        fin_cases i <;> simp [coordFlip_isom_apply]
    · rw [bC24I_adj_2T]
      refine key ![false, false, true, false] _ ?_ ?_ <;> ext i <;>
        fin_cases i <;> simp [coordFlip_isom_apply]

lemma exists_symmetry_stab_edge {k : Fin 3} (hk : k ≠ 0) (b : Bool) :
    ∃ φ, cell24.isSymmetry φ ∧ φ bC24I.toPoint = bC24I.toPoint ∧
      φ (bC24I.adjPoint 0 false) = bC24I.adjPoint 0 false ∧
      φ (bC24I.adjPoint k b) = bC24I.adjPoint 1 false := by
  have key (m : Fin 4 → Bool) (v w : E 4)
      (h1 : toIsom (coordFlip m) 0 !₂[2⁻¹, 2⁻¹, 0, 0] = !₂[2⁻¹, 2⁻¹, 0, 0])
      (h2 : toIsom (coordFlip m) 0 !₂[1, 0, 0, 0] = !₂[1, 0, 0, 0])
      (h3 : toIsom (coordFlip m) 0 v = w) :
      ∃ φ, cell24.isSymmetry φ ∧ φ bC24I.toPoint = bC24I.toPoint ∧
        φ (bC24I.adjPoint 0 false) = bC24I.adjPoint 0 false ∧ φ v = w :=
    ⟨toIsom (coordFlip m) 0, isSymmetry_cell24_coordFlip, by rw [bC24I_toPoint, h1],
      by rw [bC24I_adj_0F, h2], h3⟩
  obtain rfl | rfl : k = 1 ∨ k = 2 := by lia
  · cases b
    · rw [bC24I_adj_1F]
      refine key ![false, false, false, false] _ _ ?_ ?_ ?_ <;> ext i <;>
        fin_cases i <;> simp [coordFlip_isom_apply]
    · rw [bC24I_adj_1T, bC24I_adj_1F]
      refine key ![false, false, true, true] _ _ ?_ ?_ ?_ <;> ext i <;>
        fin_cases i <;> simp [coordFlip_isom_apply]
  · cases b
    · rw [bC24I_adj_2F, bC24I_adj_1F]
      refine key ![false, false, true, false] _ _ ?_ ?_ ?_ <;> ext i <;>
        fin_cases i <;> simp [coordFlip_isom_apply]
    · rw [bC24I_adj_2T, bC24I_adj_1F]
      refine key ![false, false, false, true] _ _ ?_ ?_ ?_ <;> ext i <;>
        fin_cases i <;> simp [coordFlip_isom_apply]

lemma exists_symmetry_stab_swap_two :
    ∃ φ, cell24.isSymmetry φ ∧ φ bC24I.toPoint = bC24I.toPoint ∧
      φ (bC24I.adjPoint 0 false) = bC24I.adjPoint 0 false ∧
      φ (bC24I.adjPoint 1 false) = bC24I.adjPoint 1 false ∧
      φ (bC24I.adjPoint 2 true) = bC24I.adjPoint 2 false := by
  refine ⟨toIsom (coordPerm (Equiv.swap 2 3)) 0, isSymmetry_cell24_coordPerm, ?_, ?_, ?_, ?_⟩
  · rw [bC24I_toPoint]
    ext i
    fin_cases i <;> simp [coordPerm_isom_apply, Equiv.swap_apply_def]
  · rw [bC24I_adj_0F]
    ext i
    fin_cases i <;> simp [coordPerm_isom_apply, Equiv.swap_apply_def]
  · rw [bC24I_adj_1F]
    ext i
    fin_cases i <;> simp [coordPerm_isom_apply, Equiv.swap_apply_def]
  · rw [bC24I_adj_2T, bC24I_adj_2F]
    ext i
    fin_cases i <;> simp [coordPerm_isom_apply, Equiv.swap_apply_def]

lemma cell24_vertex_transitive_in_cell (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) :
    ∃ φ, cell24.isSymmetry φ ∧ φ bC24I.toPoint = bC24I.toPoint ∧
    φ (bC24I.adjPoint (p 0) (s 0)) = !₂[1, 0, 0, 0] := by
  obtain ⟨φ, sφ, fφ, h⟩ := exists_symmetry_stab_map_adjPoint (p 0) (s 0)
  exact ⟨φ, sφ, fφ, by rw [h, bC24I_adj_0F]⟩

lemma cell24_edge_transitive_in_cell (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) :
    ∃ φ, cell24.isSymmetry φ ∧ φ bC24I.toPoint = bC24I.toPoint ∧
    φ (bC24I.adjPoint (p 0) (s 0)) = !₂[1, 0, 0, 0] ∧
    φ (bC24I.adjPoint (p 1) (s 1)) = !₂[2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹] := by
  obtain ⟨φ, sφ, fφ, h0⟩ := cell24_vertex_transitive_in_cell p s
  obtain ⟨q, r, hq⟩ := adjPoint_transfer_isom sφ fφ p s
  obtain ⟨e0a, e0b⟩ := Prod.mk.inj (bC24I.injective_adjPoint (a₁ := (q 0, r 0)) (a₂ := (0, false))
    (by show bC24I.adjPoint (q 0) (r 0) = bC24I.adjPoint 0 false
        rw [← hq, h0, bC24I_adj_0F]))
  have hk : q 1 ≠ 0 := by
    rw [← e0a]
    exact fun h ↦ absurd (q.injective h) (by decide)
  obtain ⟨ψ, sψ, fψ, g0, g1⟩ := exists_symmetry_stab_edge hk (r 1)
  refine ⟨ψ * φ, sψ.mul sφ, ?_, ?_, ?_⟩
  · rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, fφ, fψ]
  · rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, hq, e0a, e0b, g0, bC24I_adj_0F]
  · rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, hq, g1, bC24I_adj_1F]

lemma cell24_flag_transitive_in_cell (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) :
    ∃ φ, cell24.isSymmetry φ ∧ φ bC24I.toPoint = bC24I.toPoint ∧
    ∀ i, φ (bC24I.adjPoint (p i) (s i)) = bC24I.adjPoint i false := by
  obtain ⟨φ, sφ, fφ, h0, h1⟩ := cell24_edge_transitive_in_cell p s
  obtain ⟨q, r, hq⟩ := adjPoint_transfer_isom sφ fφ p s
  obtain ⟨e0a, e0b⟩ := Prod.mk.inj (bC24I.injective_adjPoint (a₁ := (q 0, r 0)) (a₂ := (0, false))
    (by show bC24I.adjPoint (q 0) (r 0) = bC24I.adjPoint 0 false
        rw [← hq, h0, bC24I_adj_0F]))
  obtain ⟨e1a, e1b⟩ := Prod.mk.inj (bC24I.injective_adjPoint (a₁ := (q 1, r 1)) (a₂ := (1, false))
    (by show bC24I.adjPoint (q 1) (r 1) = bC24I.adjPoint 1 false
        rw [← hq, h1, bC24I_adj_1F]))
  have e2a : q 2 = 2 := by
    have k0 := e0a ▸ q.injective (a₁ := 2) (a₂ := 0)
    have k1 := e1a ▸ q.injective (a₁ := 2) (a₂ := 1)
    lia
  cases hr2 : r 2
  · refine ⟨φ, sφ, fφ, fun i ↦ ?_⟩
    obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by lia
    · rw [hq, e0a, e0b]
    · rw [hq, e1a, e1b]
    · rw [hq, e2a, hr2]
  · obtain ⟨ψ, sψ, fψ, g0, g1, g2⟩ := exists_symmetry_stab_swap_two
    refine ⟨ψ * φ, sψ.mul sφ, ?_, fun i ↦ ?_⟩
    · rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, fφ, fψ]
    rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, hq]
    obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by lia
    · rw [e0a, e0b, g0]
    · rw [e1a, e1b, g1]
    · rw [e2a, hr2, g2]

lemma isom_map_adjPoint_not {φ : Isom 4} {I J : C24Index} (hφ : φ I.toPoint = J.toPoint)
    {k k' : Fin 3} {b b' : Bool} (h : φ (I.adjPoint k b) = J.adjPoint k' b') :
    φ (I.adjPoint k !b) = J.adjPoint k' !b' := by
  have m1 : midpoint ℝ (J.adjPoint k' b') (φ (I.adjPoint k !b)) = J.toPoint := by
    rw [← h, ← isom_map_midpoint, I.midpoint_adjPoint_not, hφ]
  have m2 := J.midpoint_adjPoint_not k' b'
  rw [midpoint_eq_iff] at m1 m2
  rw [← m1, ← m2]

lemma image_adjPoint_of_map {φ : Isom 4} {I J : C24Index} (hφ : φ I.toPoint = J.toPoint)
    {p q : Equiv.Perm (Fin 3)} {s r : Fin 3 → Bool}
    (h : ∀ i, φ (I.adjPoint (p i) (s i)) = J.adjPoint (q i) (r i)) :
    φ '' (univ.image fun j : Fin 3 × Bool ↦ I.adjPoint j.1 j.2 : Finset (E 4)) =
      (univ.image fun j : Fin 3 × Bool ↦ J.adjPoint j.1 j.2 : Finset (E 4)) := by
  ext y
  simp only [coe_image, coe_univ, Set.image_univ, Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨-, ⟨⟨k, b⟩, rfl⟩, rfl⟩
    obtain ⟨i, rfl⟩ := p.surjective k
    obtain rfl | rfl : b = s i ∨ b = !s i := by cases b <;> cases hs : s i <;> simp_all
    · exact ⟨(q i, r i), (h i).symm⟩
    · exact ⟨(q i, !r i), (isom_map_adjPoint_not hφ (h i)).symm⟩
  · rintro ⟨⟨k, b⟩, rfl⟩
    obtain ⟨i, rfl⟩ := q.surjective k
    obtain rfl | rfl : b = r i ∨ b = !r i := by cases b <;> cases hs : r i <;> simp_all
    · exact ⟨_, ⟨(p i, s i), rfl⟩, h i⟩
    · exact ⟨_, ⟨(p i, !s i), rfl⟩, isom_map_adjPoint_not hφ (h i)⟩

lemma exists_isom_to_base_flag (I : C24Index) (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) :
    ∃ φ, cell24.isSymmetry φ ∧ φ I.toPoint = bC24I.toPoint ∧
    ∀ i, φ (I.adjPoint (p i) (s i)) = bC24I.adjPoint i false := by
  obtain ⟨φ, sφ, hφ⟩ := cell24_cell_transitive I
  obtain ⟨q, r, hq⟩ := adjPoint_transfer_isom sφ hφ p s
  obtain ⟨ψ, sψ, fψ, hψ⟩ := cell24_flag_transitive_in_cell q r
  exact ⟨ψ * φ, sψ.mul sφ, by rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, hφ, fψ],
    fun i ↦ by rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, hq, hψ]⟩

theorem cell24_isRegular : cell24.IsRegular := by
  refine ⟨isFullDim_cell24, fun F G ↦ ?_⟩
  obtain ⟨I, p, s, hF, hF3⟩ := cell24_flag_characterisation F
  obtain ⟨J, q, r, hG, hG3⟩ := cell24_flag_characterisation G
  obtain ⟨Φ, sΦ, fΦ, hΦ⟩ := exists_isom_to_base_flag I p s
  obtain ⟨Ψ, sΨ, fΨ, hΨ⟩ := exists_isom_to_base_flag J q r
  have fφ : (Ψ⁻¹ * Φ) I.toPoint = J.toPoint := by
    rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, fΦ, isom_inv_apply fΨ]
  have hadj (i) : (Ψ⁻¹ * Φ) (I.adjPoint (p i) (s i)) = J.adjPoint (q i) (r i) := by
    rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, hΦ i, isom_inv_apply (hΨ i)]
  refine ⟨Ψ⁻¹ * Φ, sΨ.inv.mul sΦ, fun k ↦ ?_⟩
  rcases Fin.eq_castSucc_or_eq_last k with ⟨d, rfl⟩ | rfl
  · simp_rw [hF, hG, isom_image_convexHull, coe_image, Set.image_image, hadj]
  · rw [show Fin.last 3 = 3 from rfl, hF3, hG3, isom_image_convexHull,
      image_adjPoint_of_map fφ hadj]
