import Submission.Face.Halfspace
import Submission.LowerBounds.Icosahedron
import Submission.PolarDual

open Real Finset LeanEval.Geometry.PlatonicClassification ConvexPolytope
open scoped goldenRatio

variable {i : (Fin 3 → Bool) ⊕ Fin 3 × Bool × Bool}

variable (i) in
/-- A function mapping either `Fin 3 → Bool` (8 vertices) or `Fin 3 × Bool × Bool` (12 vertices)
to a vertex of the regular dodecahedron. -/
noncomputable def dodecVert : E 3 :=
  i.elim (fun s ↦ .toLp _ fun i ↦ if s i then -1 else 1)
    fun ⟨i, s, t⟩ ↦ .toLp _ fun j ↦ ![0, if s then -φ else φ, if t then ψ else -ψ] (j + i)

lemma dodecVert_mem_sphere : dist 0 (dodecVert i) = √3 := by
  rw [← sq_eq_sq₀ dist_nonneg (by positivity), EuclideanSpace.dist_sq_eq, sq_sqrt zero_le_three]
  simp_rw [PiLp.zero_apply, dist_zero, norm_eq_abs, sq_abs]
  cases i with
  | inl s => norm_num [dodecVert]
  | inr v =>
    obtain ⟨i, s, t⟩ := v
    simp_rw [dodecVert, Sum.elim_inr]
    change ∑ j, ![_, _, _] (finCycle i j) ^ 2 = _
    rw [Equiv.sum_comp _ fun j ↦ ![_, _, _] j ^ 2, Fin.sum_univ_three]
    simp_rw [Matrix.cons_val, ite_pow, neg_sq, ite_self]
    grind

lemma injective_dodecVert : dodecVert.Injective := by
  refine Function.Injective.sumElim (fun s t e ↦ ?_) ?_ ?_
  · ext i
    replace e := congr($e i)
    grind +revert
  · rintro ⟨vi, vs, vt⟩ ⟨wi, ws, wt⟩ e
    simp only [WithLp.toLp.injEq] at e
    have e₁ := congr($e (-vi))
    simp_rw [neg_add_cancel, Matrix.cons_val_zero] at e₁
    have ei : -vi + wi = 0 := by
      obtain h | h | h : -vi + wi = 0 ∨ -vi + wi = 1 ∨ -vi + wi = 2 := by lia
      · exact h
      · simp_rw [h, Matrix.cons_val] at e₁
        grind
      · simp_rw [h, Matrix.cons_val] at e₁
        grind
    rw [neg_add_eq_zero] at ei
    subst ei
    have es : vs = ws := by
      have e₂ := congr($e (1 - vi))
      simp_rw [sub_add_cancel, Matrix.cons_val] at e₂
      grind
    have et : vt = wt := by
      have e₂ := congr($e (2 - vi))
      simp_rw [sub_add_cancel, Matrix.cons_val] at e₂
      grind
    rw [es, et]
  · rintro s ⟨i, a, b⟩
    by_contra! hc
    replace hc := congr($hc (-i))
    simp_rw [neg_add_cancel, Matrix.cons_val] at hc
    split_ifs at hc <;> simp at hc

/-- The regular dodecahedron, scaled by `ψ ^ 2` to make it `IsPolarDual` to the icosahedron. -/
noncomputable def dodecahedron : ConvexPolytope 3 where
  vertices := univ.image (ψ ^ 2 • dodecVert ·)
  vertices_nonempty := by simp
  vertices_eq_extremePoints := by
    refine self_eq_extremePoints_convexHull_of_subset_sphere 0 (ψ ^ 2 * √3) fun p mp ↦ ?_
    rw [mem_coe, mem_image] at mp
    obtain ⟨p, -, rfl⟩ := mp
    rw [← smul_zero (ψ ^ 2), dist_smul₀, dodecVert_mem_sphere, norm_of_nonneg (by positivity)]

lemma inner_icosahedron_dodecahedron_le_one {v w : E 3}
    (mv : v ∈ icosahedron.vertices) (mw : w ∈ dodecahedron.vertices) : inner ℝ w v ≤ 1 := by
  simp_rw [icosahedron, mem_image] at mv
  simp_rw [dodecahedron, mem_image] at mw
  obtain ⟨⟨i, a, b⟩, -, rfl⟩ := mv
  obtain ⟨j, -, rfl⟩ := mw
  rw [inner_smul_left, ringHom_apply, show 1 = ψ ^ 2 * (φ + 1) by grind]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  cases j with
  | inl s =>
    rw [dodecVert, Sum.elim_inl, EuclideanSpace.inner_toLp_toLp, star_trivial]
    apply le_of_abs_le
    calc
      _ ≤ ∑ k, |(icosaVert i a b) k * if s k = true then -1 else 1| := abs_sum_le_sum_abs ..
      _ = ∑ k, |(icosaVert i a b) k| := by
        congr! 1 with k
        rw [abs_mul, abs_ite]
        norm_num
      _ = _ := by
        change (∑ k, |![_, _, _] (finCycle i k)|) = _
        rw [Equiv.sum_comp _ fun k ↦ |![_, _, _] k|, Fin.sum_univ_three]
        simp [abs_ite, abs_of_nonneg goldenRatio_pos.le, add_comm]
  | inr v =>
    obtain ⟨j, c, d⟩ := v
    rw [dodecVert, Sum.elim_inr, EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct]
    obtain rfl | rfl | rfl : i = j ∨ j = i + 1 ∨ j = i + 2 := by lia
    · change (∑ k, ![_, _, _] (finCycle i k) * ![_, _, _] (finCycle i k)) ≤ _
      rw [Equiv.sum_comp _ fun k ↦ ![_, _, _] k * ![_, _, _] k, Fin.sum_univ_three]
      simp_rw [Matrix.cons_val, zero_mul, zero_add]
      gcongr <;> apply le_of_abs_le
      · simp_rw [abs_mul, abs_ite]
        norm_num [abs_of_nonneg goldenRatio_pos.le]
      · simp_rw [abs_mul, abs_ite, abs_neg, ite_self, ← abs_mul]
        simp
    · simp_rw [← add_assoc]
      change (∑ k, ![_, _, _] (finCycle i k) * ![_, _, _] (finCycle i k + 1)) ≤ _
      rw [Equiv.sum_comp _ fun k ↦ ![_, _, _] k * ![_, _, _] (k + 1), Fin.sum_univ_three]
      simp_rw [Fin.reduceAdd, Matrix.cons_val, zero_mul, zero_add, mul_zero, add_zero]
      apply le_of_abs_le
      simp_rw [abs_mul, abs_ite, abs_neg, ite_self, abs_one, one_mul,
        abs_of_nonpos goldenConj_neg.le]
      linarith [neg_one_lt_goldenConj, goldenRatio_pos]
    · simp_rw [← add_assoc]
      change (∑ k, ![_, _, _] (finCycle i k) * ![_, _, _] (finCycle i k + 2)) ≤ _
      rw [Equiv.sum_comp _ fun k ↦ ![_, _, _] k * ![_, _, _] (k + 2), Fin.sum_univ_three]
      simp_rw [Fin.reduceAdd, Matrix.cons_val, zero_mul, mul_zero, zero_add]
      apply le_of_abs_le
      simp_rw [abs_mul, abs_ite, abs_neg, ite_self, abs_of_nonneg goldenRatio_pos.le, ← sq]
      simp

section FacetEnum

variable {f : Set (E 3)} (hf : icosahedron.IsFace f) (df : faceDim f = 2)

include df in
theorem icosahedron_facet_characterisation :
    (∃ i s t, faceGens hf.1 =
      {icosaVert i s t, icosaVert (i + 1) false s, icosaVert (i + 1) true s}) ∨
    ∃ s t u, faceGens hf.1 = {icosaVert 0 s u, icosaVert 1 t s, icosaVert 2 u t} := by
  have cg : #(faceGens hf.1) = 3 := by
    have lb := faceDim_add_one_le_card_faceGens hf
    have ub := icosahedron_small_faces hf (by lia)
    lia
  obtain ⟨g, ge⟩ := exists_icosahedron_params (faceGens_subset_vertices hf.1)
  suffices (∃ i s t, g = {(i, s, t), (i + 1, false, s), (i + 1, true, s)}) ∨
      ∃ s t u, g = {(0, s, u), (1, t, s), (2, u, t)} by
    obtain ⟨i, s, t, rfl⟩ | ⟨s, t, u, rfl⟩ := this <;>
      simp only [map_insert, Function.Embedding.coeFn_mk, map_singleton] at ge
    · exact .inl ⟨i, s, t, ge⟩
    · exact .inr ⟨s, t, u, ge⟩
  rw [ge, card_map] at cg
  have sg : (faceGens hf.1 : Set _) ⊆ f := fun x mx ↦ by
    rw [convexHull_faceGens hf.1]
    exact subset_convexHull _ _ mx
  obtain cig | cig := (card_image_le (s := g) (f := (·.1))).eq_or_lt
  · replace cig : g.image (·.1) = univ := eq_univ_of_card _ (by simpa [cg] using cig)
    obtain ⟨a, ma, ha⟩ := mem_image.mp (cig.symm ▸ mem_univ 0)
    obtain ⟨b, mb, hb⟩ := mem_image.mp (cig.symm ▸ mem_univ 1)
    obtain ⟨c, mc, hc⟩ := mem_image.mp (cig.symm ▸ mem_univ 2)
    refine .inr ⟨a.2.1, b.2.1, c.2.1, ?_⟩
    have n₁ : a ≠ b := by by_contra! con; simpa [ha, hb] using congr($con.1)
    have n₂ : a ≠ c := by by_contra! con; simpa [ha, hc] using congr($con.1)
    have n₃ : b ≠ c := by by_contra! con; simpa [hb, hc] using congr($con.1)
    have hgabc : g = {a, b, c} := by
      refine (eq_of_subset_of_card_le ?_ ?_).symm
      · rw [insert_subset_iff, insert_subset_iff, singleton_subset_iff]
        exact ⟨ma, mb, mc⟩
      · simp [cg, n₁, n₂, n₃]
    have mva : icosaVert a.1 a.2.1 a.2.2 ∈ f := sg (ge ▸ mem_map_of_mem _ ma)
    have mvb : icosaVert b.1 b.2.1 b.2.2 ∈ f := sg (ge ▸ mem_map_of_mem _ mb)
    have mvc : icosaVert c.1 c.2.1 c.2.2 ∈ f := sg (ge ▸ mem_map_of_mem _ mc)
    have Aab := icosaAdj_of_mem_face_of_ne hf (by lia) mva mvb n₁
    have Aac := icosaAdj_of_mem_face_of_ne hf (by lia) mva mvc n₂
    have Abc := icosaAdj_of_mem_face_of_ne hf (by lia) mvb mvc n₃
    grind [icosaAdj]
  · obtain ⟨a, ma, b, mb, n₁, e₁⟩ := exists_ne_map_eq_of_card_image_lt cig
    have cg' : #((g.erase a).erase b) = 1 := by grind [card_fin]
    rw [card_eq_one] at cg'
    obtain ⟨c, compg⟩ := cg'
    refine .inl ⟨c.1, c.2.1, c.2.2, ?_⟩
    have n₂ : a ≠ c := by by_contra! hc; subst hc; simpa using congr(a ∈ $compg)
    have n₃ : b ≠ c := by by_contra! hc; subst hc; simpa using congr(b ∈ $compg)
    rw [erase_eq_iff_eq_insert (by simp [n₁.symm, mb]) (by simp [n₃]),
      erase_eq_iff_eq_insert ma (by simp [n₁, n₂])] at compg
    have mva : icosaVert a.1 a.2.1 a.2.2 ∈ f := sg (ge ▸ mem_map_of_mem _ ma)
    have mvb : icosaVert b.1 b.2.1 b.2.2 ∈ f := sg (ge ▸ mem_map_of_mem _ mb)
    have mvc : icosaVert c.1 c.2.1 c.2.2 ∈ f := sg (ge ▸ mem_map_of_mem _ (by simp [compg]))
    have Aab := icosaAdj_of_mem_face_of_ne hf (by lia) mva mvb n₁
    have Aac := icosaAdj_of_mem_face_of_ne hf (by lia) mva mvc n₂
    have Abc := icosaAdj_of_mem_face_of_ne hf (by lia) mvb mvc n₃
    grind [icosaAdj]

end FacetEnum

theorem isPolarDual_icosahedron_dodecahedron : IsPolarDual icosahedron dodecahedron := by
  apply IsPolarDual.symm
  unfold IsPolarDual
  conv_rhs => rw [toSet, ← iInter_eq_iInter_convexHull_le]
  refine subset_antisymm ?_ fun x mx ↦ ?_
  · have cvi : Convex ℝ (⋂ v ∈ dodecahedron.vertices, {w | inner ℝ v w ≤ 1}) :=
      convex_iInter₂ fun v mv ↦
        convex_halfSpace_le ⟨by simp [inner_add_right], by simp [inner_smul_right]⟩ _
    rw [toSet, cvi.convexHull_subset_iff]
    exact fun v mv ↦ Set.mem_iInter₂_of_mem fun w mw ↦ inner_icosahedron_dodecahedron_le_one mv mw
  · rw [Set.mem_iInter₂] at mx
    simp_rw [toSet_eq_iInter_facet_halfspaces isFullDim_icosahedron, Set.mem_iInter]
    intro f hf df
    obtain ⟨i, s, t, hg⟩ | ⟨s, t, u, hg⟩ := icosahedron_facet_characterisation hf (by lia)
    · have mw : ψ ^ 2 • dodecVert (Sum.inr (i, s, t)) ∈ dodecahedron.vertices := by
        simp [dodecahedron]
      specialize mx _ mw
      convert mx using 1
      refine unique_facet_halfspace isFullDim_icosahedron hf df one_ne_zero
        (fun v mv ↦ inner_icosahedron_dodecahedron_le_one mv mw) fun v mv ↦ ?_
      rw [hg, mem_insert, mem_insert, mem_singleton] at mv
      simp_rw [inner_smul_left, ringHom_apply, dodecVert, Sum.elim_inr]
      rw [EuclideanSpace.inner_toLp_toLp, star_trivial, show 1 = ψ ^ 2 * (φ + 1) by grind]
      congr 1
      obtain rfl | rfl | rfl := mv
      · change (∑ k, ![_, _, _] (finCycle i k) * ![_, _, _] (finCycle i k)) = _
        rw [Equiv.sum_comp _ fun k ↦ ![_, _, _] k * ![_, _, _] k, Fin.sum_univ_three]
        simp_rw [Matrix.cons_val, zero_mul, zero_add, ite_mul_ite, neg_mul_neg, ← neg_mul_comm,
          ite_self, one_mul, neg_mul, mul_comm φ, goldenConj_mul_goldenRatio, neg_neg]
      all_goals
        simp_rw [icosaVert, ← add_assoc]
        change (∑ k, ![_, _, _] (finCycle i k + 1) * ![_, _, _] (finCycle i k)) = _
        rw [Equiv.sum_comp _ fun k ↦ ![_, _, _] (k + 1) * ![_, _, _] k, Fin.sum_univ_three]
        simp_rw [Fin.reduceAdd, Matrix.cons_val, mul_zero, zero_mul, zero_add, add_zero,
          ite_mul_ite, neg_mul_neg, ite_self, ← sq, goldenRatio_sq]
    · have mw : ψ ^ 2 • dodecVert (Sum.inl ![t, s, u]) ∈ dodecahedron.vertices := by
        simp [dodecahedron]
      specialize mx _ mw
      convert mx using 1
      refine unique_facet_halfspace isFullDim_icosahedron hf df one_ne_zero
        (fun v mv ↦ inner_icosahedron_dodecahedron_le_one mv mw) fun v mv ↦ ?_
      rw [hg, mem_insert, mem_insert, mem_singleton] at mv
      simp_rw [inner_smul_left, ringHom_apply, dodecVert, Sum.elim_inl]
      rw [EuclideanSpace.inner_toLp_toLp, star_trivial, show 1 = ψ ^ 2 * (1 + φ) by grind]
      congr 1
      obtain rfl | rfl | rfl := mv <;>
      simp_rw [dotProduct, icosaVert, Fin.sum_univ_three, Fin.reduceAdd, Matrix.cons_val] <;>
      simp only [zero_mul, zero_add, add_zero]
      · cases s <;> cases u <;> simp
      · cases s <;> cases t <;> simp
      · cases t <;> cases u <;> simp [add_comm]

theorem dodecahedron_isRegular : dodecahedron.IsRegular := by
  refine isPolarDual_icosahedron_dodecahedron.isRegular icosahedron_isRegular fun T sT ↦ ?_
  suffices icosahedron.vertices.centroid ℝ id = 0 from this ▸ sT.map_centroid
  simp_rw [centroid_eq_inv_smul_sum icosahedron.vertices_nonempty, smul_eq_zero, id_eq]
  right
  rw [icosahedron, sum_image injective_icosaVert.injOn, Fintype.sum_prod_type]
  refine Fintype.sum_eq_zero _ fun i ↦ ?_
  simp_rw [Fintype.sum_prod_type, Fintype.sum_bool, icosaVert]
  ext j
  simp_rw [PiLp.add_apply, Bool.false_eq_true, reduceIte, PiLp.zero_apply]
  obtain h | h | h : j + i = 0 ∨ j + i = 1 ∨ j + i = 2 := by lia
  all_goals simp [h]
