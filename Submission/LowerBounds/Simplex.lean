import Submission.Face.Basic
import Submission.LowerBounds.Lemmas
import Submission.Symmetry

open Real Finset LeanEval.Geometry.PlatonicClassification ConvexPolytope

variable {n : ℕ}

/-- A function mapping a `Fin (n + 1)` to a vertex of the `n`-simplex. -/
noncomputable def simplexVert (i : Fin (n + 1)) : E n :=
  i.lastCases (.toLp 2 fun _ ↦ (√(n + 1) + 1) / n) (.single · 1)

lemma simplexVert_mem_sphere {i : Fin (n + 1)} :
    dist (.toLp 2 fun _ ↦ (√(n + 1) + 1) / (n * √(n + 1))) (simplexVert i) = √(n / (n + 1)) := by
  have e : √(n + 1) ^ 2 = n + 1 := sq_sqrt (by positivity)
  rw [← sq_eq_sq₀ dist_nonneg (by positivity), EuclideanSpace.dist_sq_eq, sq_sqrt (by positivity)]
  simp only [simplexVert]
  cases i using Fin.lastCases with
  | last =>
    simp_rw [Fin.lastCases_last, sum_const, card_fin, nsmul_eq_mul, dist_eq, sq_abs]
    field_simp
    grind
  | cast i =>
    simp_rw [Fin.lastCases_castSucc, dist_eq, sq_abs, Fintype.sum_eq_add_sum_compl i,
      PiLp.single_eq_same]
    have cgr (j) (mj : j ∈ ({i}ᶜ : Finset _)) :
        ((√(n + 1) + 1) / (↑n * √(n + 1)) - (EuclideanSpace.single i (1 : ℝ)).ofLp j) ^ 2 =
        (√(n + 1) + 1) ^ 2 / (n ^ 2 * (n + 1)) := by
      rw [mem_compl, mem_singleton] at mj
      rw [PiLp.single_eq_of_ne _ mj, sub_zero, div_pow, mul_pow, e]
    have npos := i.pos
    rw [sum_congr rfl cgr, sum_const, card_compl, Fintype.card_fin, card_singleton, nsmul_eq_mul,
      Nat.cast_pred npos]
    field_simp
    grind

variable (n) in
/-- The `n`-simplex. -/
noncomputable def simplex : ConvexPolytope n where
  vertices := univ.image simplexVert
  vertices_nonempty := by simp
  vertices_eq_extremePoints := by
    refine self_eq_extremePoints_convexHull_of_subset_sphere
      (.toLp 2 fun _ ↦ (√(n + 1) + 1) / (n * √(n + 1))) √(n / (n + 1)) fun p mp ↦ ?_
    rw [mem_coe, mem_image] at mp
    obtain ⟨i, -, rfl⟩ := mp
    exact simplexVert_mem_sphere

lemma affineIndependent_simplexVert : AffineIndependent ℝ (simplexVert (n := n)) := by
  rw [affineIndependent_iff_linearIndependent_vsub _ _ (Fin.last n)]
  suffices LinearIndependent ℝ (fun i : Fin n ↦
      EuclideanSpace.single i (1 : ℝ) -ᵥ (.toLp 2 fun _ ↦ (√(n + 1) + 1) / n)) by
    let f (i : { i : Fin (n + 1) // i ≠ Fin.last n }) : Fin n := i.1.castPred i.2
    have injf : f.Injective := fun i j e ↦ by simpa [f, Subtype.val_inj] using e
    convert! this.comp f injf with ⟨i, ni⟩
    cases i using Fin.lastCases with
    | last => contradiction
    | cast i => simp [f, simplexVert]
  refine Fintype.linearIndependent_iff.mpr fun w hw i ↦ ?_
  have cr (j) : w j - (∑ i, w i) * ((√(n + 1) + 1) / n) = 0 := by
    replace hw := congr($hw j)
    simp only [vsub_eq_sub, WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_sub, PiLp.ofLp_single,
      Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, PiLp.zero_apply] at hw
    simp_rw [mul_sub, sum_sub_distrib, ← sum_mul] at hw
    rwa [Fintype.sum_eq_single j (fun _ _ ↦ by simp_all), Pi.single_eq_same, mul_one] at hw
  have scr := Fintype.sum_eq_zero _ cr
  rw [sum_sub_distrib, sum_const, card_fin, nsmul_eq_mul, ← mul_div_assoc,
    mul_div_cancel₀ _ (by simpa using i.pos.ne'), ← mul_one_sub, sub_add_cancel_right, mul_neg,
    neg_eq_zero, mul_eq_zero_iff_right (by positivity)] at scr
  simp_rw [scr, zero_mul, sub_zero] at cr
  exact cr i

lemma injective_simplexVert : simplexVert (n := n).Injective :=
  affineIndependent_simplexVert.injective

lemma simplex_isFullDim : (simplex n).IsFullDim := by
  rw [ConvexPolytope.IsFullDim, ConvexPolytope.dim, ConvexPolytope.toSet,
    vectorSpan_convexHull_eq_vectorSpan, simplex, Fintype.coe_image_univ]
  exact affineIndependent_simplexVert.finrank_vectorSpan (by simp)

lemma exists_simplex_params_single {v : E n} (mv : v ∈ (simplex n).vertices) :
    ∃ i, v = simplexVert i := by
  simp_rw [simplex, mem_image, mem_univ, true_and, eq_comm] at mv
  exact mv

lemma exists_simplex_params {g : Finset (E n)} (sg : g ⊆ (simplex n).vertices) :
    ∃ s : Finset (Fin (n + 1)), g = s.map ⟨_, injective_simplexVert⟩ := by
  refine ⟨g.attach.image fun v ↦ (exists_simplex_params_single (sg v.2)).choose, ?_⟩
  ext v
  simp_rw [mem_map, mem_image, mem_attach, Function.Embedding.coeFn_mk, Subtype.exists, existsAndEq,
    true_and]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ⟨v, h, ((exists_simplex_params_single (sg h)).choose_spec).symm⟩
  · obtain ⟨p, hp, rfl⟩ := h
    rwa [(exists_simplex_params_single (sg hp)).choose_spec] at hp

lemma simplex_flag_small_faces {i : Fin n} {F : (simplex n).Flag} :
    #(faceGens (F.isFace i).1) ≤ n := by
  generalize_proofs ex
  obtain ⟨s, es⟩ := exists_simplex_params (faceGens_subset_vertices ex)
  rw [es, card_map]
  by_contra! h
  replace h : s = univ := by
    have := card_le_univ s
    rw [← card_eq_iff_eq_univ]
    rw [Fintype.card_fin] at this ⊢
    lia
  subst h
  rw [map_eq_image, ← coe_inj, Fintype.coe_image_univ, Function.Embedding.coeFn_mk] at es
  have e := affineIndependent_simplexVert.finrank_vectorSpan (Fintype.card_fin (n + 1))
  rw [← es] at e
  have c := F.dim_eq i
  rw [ConvexPolytope.faceDim, convexHull_faceGens ex, vectorSpan_convexHull_eq_vectorSpan, e] at c
  lia

theorem simplex_flag_characterisation (F : (simplex n).Flag) :
    ∃ p : Equiv.Perm (Fin (n + 1)),
    ∀ i, F.face i = convexHull ℝ ((Iic i.castSucc).image fun j ↦ simplexVert (p j)) := by
  obtain ⟨p, sp, hp⟩ := simplicial_flag_of_small_faces F fun _ ↦ simplex_flag_small_faces
  obtain ⟨q, hq⟩ := exists_simplex_params sp
  have ej (i) : ∃ j, p i = simplexVert j := by
    have key := hq ▸ (mem_map' p).mpr (mem_univ i)
    rw [mem_map] at key
    obtain ⟨js, -, hjs⟩ := key
    exact ⟨js, hjs.symm⟩
  let r (i) := (ej i).choose
  have hr (i) : p i = simplexVert (r i) := (ej i).choose_spec
  have injr : r.Injective := fun i j e ↦ by
    rwa [← p.injective.eq_iff, hr, hr, injective_simplexVert.eq_iff]
  have nsurjr : ¬r.Surjective := by
    by_contra h
    simpa using Fintype.card_le_of_surjective _ h
  rw [Function.Surjective] at nsurjr
  push Not at nsurjr
  obtain ⟨z, hz⟩ := nsurjr
  let r' := Fin.Embedding.snoc ⟨_, injr⟩ (a := z) (by simpa using hz)
  have bijr' : r'.1.Bijective := by
    simp_rw [r', ← Finite.injective_iff_bijective]
    exact r'.inj'
  let perm : Equiv.Perm (Fin (n + 1)) := Equiv.ofBijective _ bijr'
  refine ⟨perm, fun i ↦ ?_⟩
  rw [hp i, map_eq_image]
  congr! 2 with j
  ext v
  simp_rw [mem_image, Fin.exists_iff_castSucc, mem_Iic, Fin.last_le_iff, Fin.castSucc_ne_last,
    false_and, false_or, Fin.castSucc_le_castSucc_iff, perm, Function.Embedding.toFun_eq_coe,
    Equiv.ofBijective_apply, r', Fin.Embedding.coe_snoc, Function.Embedding.coeFn_mk,
    Fin.snoc_castSucc, hr]

section

/-- A simplex symmetry swapping vertices `i.castSucc` and `Fin.last n` and fixing the rest. -/
noncomputable def simplexSwap (i : Fin n) : Isom n :=
  let d := simplexVert (Fin.last n) - simplexVert i.castSucc
  AffineIsometryEquiv.mk'
    ((ℝ ∙ d)ᗮ.reflection · + ((√(n + 1) + 1) / n) • d) (ℝ ∙ d)ᗮ.reflection 0 (by simp)

variable {i : Fin n}

lemma simplexSwap_denom : ‖simplexVert (Fin.last n) - simplexVert i.castSucc‖ ^ 2 = 2 := by
  simp_rw [← dist_eq_norm, EuclideanSpace.dist_sq_eq, simplexVert, Fin.lastCases_last,
    Fin.lastCases_castSucc, dist_eq, sq_abs, Fintype.sum_eq_add_sum_compl i, PiLp.single_eq_same]
  have cgr (j) (mj : j ∈ ({i}ᶜ : Finset _)) :
      ((√(n + 1) + 1) / n - (EuclideanSpace.single i (1 : ℝ)).ofLp j) ^ 2 =
      (√(n + 1) + 1) ^ 2 / n ^ 2 := by
    rw [mem_compl, mem_singleton] at mj
    rw [PiLp.single_eq_of_ne _ mj, sub_zero, div_pow]
  have npos := i.pos
  rw [sum_congr rfl cgr, sum_const, card_compl, Fintype.card_fin, card_singleton, nsmul_eq_mul,
    Nat.cast_pred npos]
  field_simp
  grind

lemma simplexSwap_numer {v : E n} :
    inner ℝ (simplexVert (Fin.last n) - simplexVert i.castSucc) v =
    (√(n + 1) + 1) / n * ∑ j, v j - v i := by
  simp_rw [inner_sub_left, simplexVert, Fin.lastCases_last, Fin.lastCases_castSucc,
    PiLp.inner_apply, inner_apply, ← mul_sum]
  simp

lemma simplexSwap_last :
    inner ℝ (simplexVert (Fin.last n) - simplexVert i.castSucc) (simplexVert (Fin.last n)) =
    (√(n + 1) + 1) / n + 1 := by
  simp_rw [simplexSwap_numer, simplexVert, Fin.lastCases_last, sum_const, card_fin, nsmul_eq_mul]
  have nnz : (n : ℝ) ≠ 0 := by simpa using i.pos.ne'
  grind

lemma simplexSwap_same :
    inner ℝ (simplexVert (Fin.last n) - simplexVert i.castSucc) (simplexVert i.castSucc) =
    (√(n + 1) + 1) / n - 1 := by
  rw [simplexSwap_numer]
  simp [simplexVert]

lemma simplexSwap_other {j : Fin n} (hij : i ≠ j) :
    inner ℝ (simplexVert (Fin.last n) - simplexVert i.castSucc) (simplexVert j.castSucc) =
    (√(n + 1) + 1) / n := by
  rw [simplexSwap_numer]
  simp [hij, simplexVert]

theorem simplexSwap_action {j : Fin (n + 1)} :
    simplexSwap i (simplexVert j) = simplexVert (Equiv.swap i.castSucc (Fin.last n) j) := by
  simp_rw [simplexSwap, AffineIsometryEquiv.coe_mk', Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply, ringHom_apply, simplexSwap_denom]
  rw [← smul_assoc, nsmul_eq_mul, Nat.cast_two, mul_div_cancel₀ _ two_ne_zero, neg_sub, sub_add, ← sub_smul]
  cases j using Fin.lastCases with
  | last =>
    rw [simplexSwap_last, Equiv.swap_apply_right]
    match_scalars <;> ring
  | cast j =>
    obtain rfl | hij := eq_or_ne i j
    · rw [simplexSwap_same, Equiv.swap_apply_left]
      match_scalars <;> ring
    · rw [simplexSwap_other hij, Equiv.swap_apply_of_ne_of_ne (by simpa using hij.symm) (by simp)]
      match_scalars <;> ring

lemma isSymmetry_simplexSwap : (simplex n).isSymmetry (simplexSwap i) := by
  set R := simplexSwap i
  let vs := (simplex n).vertices
  have im : R '' vs = vs := by
    apply Set.eq_of_subset_of_card_le
    · rw [Set.image_subset_iff]
      intro v hv
      simp only [vs, simplex, mem_coe, mem_image, Set.mem_preimage] at *
      obtain ⟨j, -, rfl⟩ := hv
      exact ⟨Equiv.swap i.castSucc (Fin.last n) j, mem_univ _, simplexSwap_action.symm⟩
    · rw [Set.card_image_of_injective _ R.injective]
  have ch := isom_image_convexHull R vs
  rwa [im] at ch

end

/-- Every finite symmetric group is generated by transpositions with a fixed element. -/
lemma Equiv.Perm.mclosure_swap_castSucc_last :
    Submonoid.closure (Set.range fun i : Fin n ↦ swap i.castSucc (Fin.last n)) = ⊤ := by
  rw [eq_top_iff, ← mclosure_swap_castSucc_succ, Submonoid.closure_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨j, h⟩ | h := i.succ.eq_castSucc_or_eq_last <;> simp only [h]
  · apply SubmonoidClass.swap_mem_trans (b := Fin.last n) <;>
    simp [Equiv.swap_comm, Submonoid.mem_closure_of_mem]
  · simp [Submonoid.mem_closure_of_mem]

lemma exists_isSymmetry_for_permutation (p : Equiv.Perm (Fin (n + 1))) :
    ∃ φ, (simplex n).isSymmetry φ ∧ ∀ i, φ (simplexVert i) = simplexVert (p i) := by
  induction p using Submonoid.induction_of_closure_eq_top_right
    Equiv.Perm.mclosure_swap_castSucc_last with
  | one => exact ⟨1, by simp [isSymmetry], fun i ↦ by simp⟩
  | mul_right p s sform ih =>
    obtain ⟨i, hi⟩ := sform
    obtain ⟨φ, sφ, hφ⟩ := ih
    refine ⟨φ * simplexSwap i, sφ.mul isSymmetry_simplexSwap, fun j ↦ ?_⟩
    rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, simplexSwap_action, ← hi]
    exact hφ _

theorem simplex_isRegular : (simplex n).IsRegular := by
  refine ⟨simplex_isFullDim, fun F G ↦ ?_⟩
  obtain ⟨pF, hF⟩ := simplex_flag_characterisation F
  obtain ⟨pG, hG⟩ := simplex_flag_characterisation G
  obtain ⟨φ, sφ, hφ⟩ := exists_isSymmetry_for_permutation (pG * pF⁻¹)
  refine ⟨φ, sφ, fun d ↦ ?_⟩
  rw [hF, hG, isom_image_convexHull, coe_image, Set.image_image, ← coe_image]
  congr! with i
  simp [hφ]
