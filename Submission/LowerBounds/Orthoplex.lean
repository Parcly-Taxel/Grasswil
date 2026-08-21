import Submission.Face.Basic
import Submission.LowerBounds.Lemmas
import Submission.Symmetry

open Real Finset LeanEval.Geometry.PlatonicClassification

variable {n : ℕ} {i : Fin n} {s : Bool}

variable (i s) in
/-- A function mapping a `Fin n` coordinate and sign to a vertex of the `n`-orthoplex. -/
noncomputable def orthoplexVert : E n :=
  .single i (if s then -1 else 1)

lemma injective_orthoplexVert :
    (fun p : Fin n × Bool ↦ orthoplexVert p.1 p.2).Injective := fun ⟨pi, ps⟩ ⟨qi, qs⟩ e ↦ by
  replace e := congr($e pi)
  simp_rw [orthoplexVert, PiLp.single_eq_same, PiLp.single_apply] at e
  grind

variable (n) in
/-- The `n`-orthoplex. -/
noncomputable def orthoplex [NeZero n] : ConvexPolytope n where
  vertices := univ.image (fun p : Fin n × Bool ↦ orthoplexVert p.1 p.2)
  vertices_nonempty := by simp
  vertices_eq_extremePoints := by
    refine self_eq_extremePoints_convexHull_of_subset_sphere 0 1 fun p mp ↦ ?_
    rw [mem_coe, mem_image] at mp
    obtain ⟨p, -, rfl⟩ := mp
    simp [orthoplexVert, abs_ite]

variable (i s) in
lemma mem_orthoplex (nzn : NeZero n := i.neZero) : orthoplexVert i s ∈ (orthoplex n).toSet := by
  apply subset_convexHull
  simp_rw [orthoplex, mem_coe, mem_image]
  exact ⟨(i, s), mem_univ _, rfl⟩

lemma exists_orthoplex_params_single [NeZero n] {v : E n} (mv : v ∈ (orthoplex n).vertices) :
    ∃ p : Fin n × Bool, v = orthoplexVert p.1 p.2 := by
  simpa [orthoplex, eq_comm] using mv

lemma exists_orthoplex_params [NeZero n] {g : Finset (E n)} (sg : g ⊆ (orthoplex n).vertices) :
    ∃ s : Finset (Fin n × Bool), g = s.map ⟨_, injective_orthoplexVert⟩ := by
  refine ⟨g.attach.image fun v ↦ (exists_orthoplex_params_single (sg v.2)).choose, ?_⟩
  ext v
  simp_rw [mem_map, mem_image, mem_attach, Function.Embedding.coeFn_mk, Subtype.exists, existsAndEq,
    true_and]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ⟨v, h, ((exists_orthoplex_params_single (sg h)).choose_spec).symm⟩
  · obtain ⟨p, hp, rfl⟩ := h
    rwa [(exists_orthoplex_params_single (sg hp)).choose_spec] at hp

lemma orthoplex_isFullDim [NeZero n] : (orthoplex n).IsFullDim := by
  have m1 (i) : .single i 1 ∈ vectorSpan ℝ (orthoplex n).toSet := by
    have := Submodule.smul_mem _ (2⁻¹ : ℝ)
      (vsub_mem_vectorSpan ℝ (mem_orthoplex i false) (mem_orthoplex i true))
    simp_rw [orthoplexVert, Bool.false_eq_true, reduceIte, vsub_eq_sub, ← PiLp.single_sub,
      ← PiLp.toLp_single, ← WithLp.toLp_smul, ← Pi.single_smul,
      show (2⁻¹ : ℝ) • (1 - -1 : ℝ) = 1 by norm_num] at this
    exact this
  have key : vectorSpan ℝ (orthoplex n).toSet = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun x ↦ ?_
    convert Submodule.sum_mem (t := univ) _ fun i _ ↦ Submodule.smul_mem _ (x i) (m1 i)
    ext i
    rw [WithLp.ofLp_sum, Finset.sum_apply, sum_eq_single i (by simp_all) (by simp),
      PiLp.smul_apply, PiLp.single_eq_same, smul_eq_mul, mul_one]
  rw [ConvexPolytope.IsFullDim, ConvexPolytope.dim, key, finrank_top, finrank_euclideanSpace_fin]

lemma zero_mem_orthoplex_openSegment_antipodes :
    0 ∈ openSegment ℝ (orthoplexVert i false) (orthoplexVert i true) := by
  refine ⟨_, _, by positivity, by positivity, add_halves 1, ?_⟩
  simp_rw [orthoplexVert, Bool.false_eq_true, reduceIte, ← smul_add, ← PiLp.single_add]
  simp

lemma no_antipodes_of_isFace_orthoplex (nzn : NeZero n := i.neZero) {f : Set (E n)}
    (hf : (orthoplex n).IsFace f) (df : ConvexPolytope.faceDim f < n) :
    orthoplexVert i false ∉ f ∨ orthoplexVert i true ∉ f := by
  replace df : ∃ j t, orthoplexVert j t ∉ f := by
    contrapose! df
    conv_lhs => rw [← orthoplex_isFullDim (n := n), ConvexPolytope.dim, ConvexPolytope.toSet]
    rw [vectorSpan_convexHull_eq_vectorSpan, ConvexPolytope.faceDim]
    refine Submodule.finrank_mono (vectorSpan_mono _ fun x mx ↦ ?_)
    simp_rw [mem_coe, orthoplex, mem_image] at mx
    obtain ⟨⟨j, t⟩, -, rfl⟩ := mx
    exact df j t
  have cf := hf.1.convex (convex_convexHull ..)
  replace hf := hf.1.isExtreme.left_mem_of_mem_openSegment
  contrapose! hf
  obtain ⟨j, t, h⟩ := df
  refine ⟨_, mem_orthoplex j t, _, mem_orthoplex j !t, _,
    cf.openSegment_subset hf.1 hf.2 zero_mem_orthoplex_openSegment_antipodes, ?_, h⟩
  cases t
  · exact zero_mem_orthoplex_openSegment_antipodes
  · rw [openSegment_symm]
    exact zero_mem_orthoplex_openSegment_antipodes

lemma orthoplex_flag_small_faces (nzn : NeZero n := i.neZero) {F : (orthoplex n).Flag} :
    #(faceGens (F.isFace i).1) ≤ n := by
  generalize_proofs ex
  obtain ⟨s, es⟩ := exists_orthoplex_params (faceGens_subset_vertices ex)
  rw [es, card_map]
  by_contra! h
  obtain ⟨j, -, hj⟩ := @exists_lt_card_fiber_of_mul_lt_card_of_maps_to _ _ _ s univ Prod.fst 1
    (by simp) (by simp [h])
  have srw : {p ∈ s | p.1 = j} = map ⟨(j, ·), by simp⟩ {b | (j, b) ∈ s} := by
    ext ⟨k, b⟩
    simp_rw [mem_map, mem_filter, Function.Embedding.coeFn_mk, mem_univ, true_and, Prod.mk.injEq,
      existsAndEq, and_true, @eq_comm _ k, and_congr_left_iff]
    rintro rfl
    rfl
  rw [srw, card_map] at hj
  replace hj : ∀ b, (j, b) ∈ s := by
    have := card_le_univ {b | (j, b) ∈ s}
    rw [Fintype.card_bool] at this
    replace this := le_antisymm this hj
    rw [← Fintype.card_bool, ← card_univ, card_filter_eq_iff] at this
    simpa using this
  replace hj (b) : orthoplexVert j b ∈ faceGens ex := by
    rw [es, mem_map]
    exact ⟨_, hj b, by simp⟩
  have mf := (subset_convexHull ℝ _) (hj false)
  have mt := (subset_convexHull ℝ _) (hj true)
  rw [← convexHull_faceGens] at mf mt
  have nm := no_antipodes_of_isFace_orthoplex (i := j) _ (F.isFace i) ((F.dim_eq i).trans_lt i.2)
  tauto

/-- For every flag `F` of the `n`-orthoplex there is a permutation `p` of the coordinates
and a function `s` from coordinates to signs such that for all `i`, `F.face i` is the convex hull
of `orthoplexVert (p j) (s j)` for all `j ≤ i`. -/
theorem orthoplex_flag_characterisation [NeZero n] (F : (orthoplex n).Flag) :
    ∃ p : Equiv.Perm (Fin n), ∃ s : Fin n → Bool,
    ∀ i, F.face i = convexHull ℝ ((Iic i).image fun j ↦ orthoplexVert (p j) (s j)) := by
  obtain ⟨p, sp, hp⟩ := simplicial_flag_of_small_faces F fun _ ↦ orthoplex_flag_small_faces
  have ex (i) := exists_orthoplex_params_single <| sp <| mem_map_of_mem _ <| mem_univ i
  let p' (i) := (ex i).choose.1
  let s (i) := (ex i).choose.2
  have ψ (i) : p i = orthoplexVert (p' i) (s i) := (ex i).choose_spec
  have bp : p'.Injective := fun i j e ↦ by
    let l : Fin n := ⟨n - 1, Nat.sub_one_lt ‹NeZero n›.ne⟩
    specialize hp l
    have icu : Iic l = univ := by
      rw [eq_univ_iff_forall]
      intro k
      simp_rw [mem_Iic, Fin.le_iff_val_le_val, l, Nat.le_sub_one_iff_lt ‹NeZero n›.pos]
      exact k.2
    rw [icu] at hp
    have mefg : faceGens (F.isFace l).1 = univ.map p :=
      (existsUnique_faceGens (F.isFace l).1).unique
        (exists_faceGens (F.isFace l).1).choose_spec ⟨sp, hp⟩
    rw [← p.injective.eq_iff, ψ, ψ, injective_orthoplexVert.eq_iff]
    change (p' i, s i) = (p' j, s j)
    rw [e, Prod.mk_right_inj]
    have mpi := subset_convexHull ℝ _ ((mem_map' p).mpr (mem_univ i))
    have mpj := subset_convexHull ℝ _ ((mem_map' p).mpr (mem_univ j))
    rw [← mefg, ψ, ← convexHull_faceGens] at mpi mpj
    rw [← e] at mpj
    by_contra! h
    have key := no_antipodes_of_isFace_orthoplex (i := p' i) _
      (F.isFace l) ((F.dim_eq l).trans_lt l.2)
    obtain ⟨si, sj⟩ | ⟨si, sj⟩ : s i = false ∧ s j = true ∨ s i = true ∧ s j = false := by lia
    all_goals
      rw [si] at mpi
      rw [sj] at mpj
      tauto
  rw [Finite.injective_iff_bijective] at bp
  let perm : Equiv.Perm (Fin n) := Equiv.ofBijective p' bp
  refine ⟨perm, s, fun i ↦ ?_⟩
  rw [hp i, map_eq_image]
  congr! with j
  exact ψ j

lemma coordPerm_orthoplexVert {σ : Equiv.Perm (Fin n)} :
    (toIsom (coordPerm σ) 0) (orthoplexVert i s) = orthoplexVert (σ⁻¹ i) s := by
  ext c
  simp [toIsom_apply, coordPerm, Matrix.permMatrix_mulVec, orthoplexVert, -PiLp.ofLp_single,
    σ.eq_symm_apply]

lemma coordFlip_orthoplexVert {m : Fin n → Bool} :
    (toIsom (coordFlip m) 0) (orthoplexVert i s) = orthoplexVert i (m i ^^ s) := by
  ext c
  simp_rw [toIsom_apply, WithLp.ofLp_zero, add_zero, coordFlip, Matrix.mulVec_diagonal,
    orthoplexVert, PiLp.single_apply]
  split_ifs <;> simp_all

lemma isSymmetry_orthoplex_coordPerm [NeZero n] {σ : Equiv.Perm (Fin n)} :
    (orthoplex n).isSymmetry (toIsom (coordPerm σ) 0) := by
  set R := toIsom (coordPerm σ) 0
  let vs := (orthoplex n).vertices
  have im : R '' vs = vs := by
    apply Set.eq_of_subset_of_card_le
    · rw [Set.image_subset_iff]
      intro v hv
      simp only [vs, orthoplex, mem_coe, mem_image, Set.mem_preimage] at *
      obtain ⟨j, -, rfl⟩ := hv
      exact ⟨(σ⁻¹ j.1, j.2), mem_univ _, coordPerm_orthoplexVert.symm⟩
    · rw [Set.card_image_of_injective _ R.injective]
  have ch := isom_image_convexHull R vs
  rwa [im] at ch

lemma isSymmetry_orthoplex_coordFlip [NeZero n] {m : Fin n → Bool} :
    (orthoplex n).isSymmetry (toIsom (coordFlip m) 0) := by
  set R := toIsom (coordFlip m) 0
  let vs := (orthoplex n).vertices
  have im : R '' vs = vs := by
    apply Set.eq_of_subset_of_card_le
    · rw [Set.image_subset_iff]
      intro v hv
      simp only [vs, orthoplex, mem_coe, mem_image, Set.mem_preimage] at *
      obtain ⟨j, -, rfl⟩ := hv
      exact ⟨(j.1, m j.1 ^^ j.2), mem_univ _, coordFlip_orthoplexVert.symm⟩
    · rw [Set.card_image_of_injective _ R.injective]
  have ch := isom_image_convexHull R vs
  rwa [im] at ch

theorem orthoplex_isRegular [NeZero n] : (orthoplex n).IsRegular := by
  refine ⟨orthoplex_isFullDim, fun F G ↦ ?_⟩
  obtain ⟨pF, sF, hF⟩ := orthoplex_flag_characterisation F
  obtain ⟨pG, sG, hG⟩ := orthoplex_flag_characterisation G
  refine ⟨toIsom (coordFlip fun i ↦ sG (pG⁻¹ i)) 0 *
    toIsom (coordPerm (pF * pG⁻¹)) 0 *
    toIsom (coordFlip fun i ↦ sF (pF⁻¹ i)) 0, ?_, fun d ↦ ?_⟩
  · exact (isSymmetry_orthoplex_coordFlip.mul isSymmetry_orthoplex_coordPerm).mul
      isSymmetry_orthoplex_coordFlip
  · rw [hF, hG, isom_image_convexHull]
    congr with v
    simp_rw [coe_image, Set.mem_image, exists_exists_and_eq_and]
    congr! with i
    rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, coordFlip_orthoplexVert,
      AffineIsometryEquiv.coe_mul, Function.comp_apply, coordPerm_orthoplexVert,
      coordFlip_orthoplexVert]
    simp
