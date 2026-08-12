import Submission.Face.Basic
import Submission.LowerBounds.Lemmas
import Submission.Symmetry

open Real Finset Matrix LeanEval.Geometry.PlatonicClassification ConvexPolytope

variable {t u : Fin 3 × Fin 4 × Bool} {x : E 4}

/-- A rotation cycling the 24-cell's three 16-cells (demitesseracts). -/
noncomputable def demitessR : Matrix (Fin 4) (Fin 4) ℝ :=
  of fun i j ↦ if i = 0 ↔ i = j then -2⁻¹ else 2⁻¹

lemma demitessR_sq : demitessR ^ 2 = demitessRᵀ := by
  ext i j
  simp_rw [demitessR, sq, mul_apply, transpose_apply, of_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
  simp only [Fin.reduceFinMk, Fin.reduceEq, iff_true, true_iff, reduceIte] <;> norm_num

lemma demitessR_pow_three : demitessR ^ 3 = 1 := by
  rw [pow_succ, demitessR_sq]
  ext i j
  simp_rw [demitessR, mul_apply, transpose_apply, of_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
  simp only [Fin.reduceFinMk, Fin.reduceEq, iff_true, true_iff, reduceIte] <;> norm_num

lemma demitessR_mem_orthogonalGroup : demitessR ∈ orthogonalGroup (Fin 4) ℝ := by
  rw [mem_orthogonalGroup_iff, ← demitessR_sq, ← pow_succ', demitessR_pow_three]

lemma demitessR_mulVec_single {j : Fin 4} {P : Prop} [Decidable P] :
    demitessR *ᵥ Pi.single j (if P then -2⁻¹ else 2⁻¹) =
    ∑ i, Pi.single i (if (i = 0 ↔ i = j) ↔ P then (4⁻¹ : ℝ) else -4⁻¹) := by
  ext i
  rw [mulVec_apply_eq_sum, Fintype.sum_eq_single j fun k hk ↦ by simp [Pi.single_eq_of_ne hk],
    Pi.single_eq_same, demitessR, of_apply, Finset.sum_apply,
    Fintype.sum_eq_single i fun k hk ↦ by simp [Pi.single_eq_of_ne' hk], Pi.single_eq_same]
  by_cases h : i = 0 ↔ i = j <;> norm_num [h]

variable (t) in
/-- The 24-cell's vertex function. -/
noncomputable def cell24Vert : E 4 :=
  .toLp _ (demitessR ^ t.1.1 *ᵥ Pi.single t.2.1 (if t.2.2 then -1 else 1))

lemma norm_cell24Vert : ‖cell24Vert t‖ = 1 := by
  let R := toIsom (⟨_, demitessR_mem_orthogonalGroup⟩ ^ t.1.1) 0
  have Rt : cell24Vert t = R (.single t.2.1 (if t.2.2 then -1 else 1)) := by
    ext i; simp [R, toIsom_apply, cell24Vert]
  rw [Rt, R.isometry.norm_map_of_map_zero (by simp [R, toIsom])]
  simp [abs_ite]

lemma abs_cell24Vert_apply {i : Fin 4} (ht : t.1 ≠ 0) : |cell24Vert t i| = 2⁻¹ := by
  simp_rw [cell24Vert, mulVec_single, Pi.smul_apply, col_apply, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, abs_mul, abs_ite, abs_neg, ite_self, abs_one, mul_one]
  obtain ek | ek : t.1.1 = 1 ∨ t.1.1 = 2 := by lia
  · rw [ek, pow_one, demitessR, of_apply]
    split_ifs <;> simp
  · rw [ek, demitessR_sq, transpose_apply, demitessR, of_apply]
    split_ifs <;> simp

lemma cell24Vert_apply_even_neg (ht : t.1 = 1) : Even #{i | cell24Vert t i < 0} := by
  simp_rw [cell24Vert, ht, Fin.val_one, pow_one, mulVec_single, Pi.smul_apply, col_apply,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_ite, card_filter, Fin.sum_univ_four,
    demitessR, of_apply]
  obtain ⟨k, c, s⟩ := t
  fin_cases c <;> cases s <;> simp only [Fin.reduceFinMk, Fin.reduceEq] <;> norm_num

lemma cell24Vert_apply_odd_neg (ht : t.1 = 2) : Odd #{i | cell24Vert t i < 0} := by
  simp_rw [cell24Vert, ht, Fin.val_two, demitessR_sq, mulVec_single, Pi.smul_apply, col_apply,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_ite, card_filter, Fin.sum_univ_four,
    transpose_apply, demitessR, of_apply]
  obtain ⟨k, c, s⟩ := t
  fin_cases c <;> cases s <;> simp only [Fin.reduceFinMk, Fin.reduceEq] <;> norm_num

lemma injective_cell24Vert : cell24Vert.Injective := fun t u e ↦ by
  obtain ⟨tk, tc, ts⟩ := t
  obtain ⟨uk, uc, us⟩ := u
  have ek : tk = uk := by
    by_contra! hc
    wlog hl : tk < uk
    · exact this uk uc us tk tc ts e.symm hc.symm (by lia)
    obtain rfl | ⟨rfl, rfl⟩ : tk = 0 ∨ tk = 1 ∧ uk = 2 := by lia
    · replace e := congr(|$e 0|)
      nth_rw 2 [abs_cell24Vert_apply hc.symm] at e
      simp_rw [cell24Vert, Fin.val_zero, pow_zero, one_mulVec, Pi.single_apply] at e
      split_ifs at e <;> norm_num at e
    · have eneg := cell24Vert_apply_even_neg (show (1, tc, ts).1 = 1 by rfl)
      have oneg := cell24Vert_apply_odd_neg (show (2, uc, us).1 = 2 by rfl)
      rw [e, ← Nat.not_odd_iff_even] at eneg
      exact eneg oneg
  subst ek
  simp_rw [cell24Vert, WithLp.toLp.injEq] at e
  replace e := congr(demitessR ^ (tk.rev.1 + 1) *ᵥ $e)
  simp_rw [mulVec_mulVec, ← pow_add, show tk.rev.1 + 1 + tk.1 = 3 by grind, demitessR_pow_three,
    one_mulVec] at e
  replace e := congr($e tc)
  grind

lemma inner_cell24Vert_cell24Vert_eq_zero (h₁ : t.1 = u.1) (h₂ : t.2.1 ≠ u.2.1) :
    inner ℝ (cell24Vert t) (cell24Vert u) = 0 := by
  simp_rw [cell24Vert, EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_mulVec,
    vecMul_mulVec, h₁, transpose_pow, ← demitessR_sq, ← pow_mul, ← pow_add, ← add_one_mul,
    pow_mul, show 2 + 1 = 3 by rfl, demitessR_pow_three, one_pow, vecMul_one, dotProduct_single]
  rw [Pi.single_eq_of_ne h₂, zero_mul]

lemma inner_cell24Vert_cell24Vert_eq_neg_one (h₁ : t.1 = u.1) (h₂ : t.2.1 = u.2.1) (hn : t ≠ u) :
    inner ℝ (cell24Vert t) (cell24Vert u) = -1 := by
  suffices cell24Vert u = -cell24Vert t by simp [this, norm_cell24Vert]
  simp_rw [cell24Vert, ← WithLp.toLp_neg, ← mulVec_neg, ← Pi.single_neg, h₁, h₂,
    show u.2.2 = !t.2.2 by lia]
  cases t.2.2 <;> simp

lemma inner_cell24Vert_cell24Vert_nonpos (h₁ : t.1 = u.1) (hn : t ≠ u) :
    inner ℝ (cell24Vert t) (cell24Vert u) ≤ 0 := by
  by_cases h₂ : t.2.1 = u.2.1
  · simp [inner_cell24Vert_cell24Vert_eq_neg_one h₁ h₂ (by lia)]
  · simp [inner_cell24Vert_cell24Vert_eq_zero h₁ h₂]

lemma inner_cell24Vert_cell24Vert_le_one (h₁ : t.1 = u.1) :
    inner ℝ (cell24Vert t) (cell24Vert u) ≤ 1 := by
  obtain rfl | hn := eq_or_ne t u
  · simp [norm_cell24Vert]
  · exact (inner_cell24Vert_cell24Vert_nonpos h₁ hn).trans zero_le_one

lemma abs_inner_cell24Vert_of_fst_ne (h₁ : t.1 ≠ u.1) :
    |inner ℝ (cell24Vert t) (cell24Vert u)| = 2⁻¹ := by
  simp_rw [cell24Vert, EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_mulVec,
    vecMul_mulVec, dotProduct_single, abs_mul, single_vecMul, Pi.smul_apply, abs_smul, abs_ite,
    abs_neg, ite_self, abs_one, one_smul, mul_one, row_apply, transpose_pow, ← demitessR_sq,
    ← pow_mul, ← pow_add]
  rw [← Nat.div_add_mod (2 * u.1 + t.1) 3, pow_add, pow_mul, demitessR_pow_three, one_pow, one_mul]
  obtain hex | hex : (2 * u.1.1 + t.1) % 3 = 1 ∨ (2 * u.1.1 + t.1) % 3 = 2 := by lia
  · rw [hex, pow_one, demitessR, of_apply]
    split_ifs <;> norm_num
  · rw [hex, demitessR_sq, demitessR, transpose_apply, of_apply]
    split_ifs <;> norm_num

/-- The 24-cell. -/
noncomputable def cell24 : ConvexPolytope 4 where
  vertices := univ.image cell24Vert
  vertices_nonempty := by simp
  vertices_eq_extremePoints := by
    refine self_eq_extremePoints_convexHull_of_subset_sphere 0 1 fun t mt ↦ ?_
    rw [mem_coe, mem_image] at mt
    obtain ⟨t, -, rfl⟩ := mt
    simp [norm_cell24Vert]

variable (t) in
lemma mem_cell24 : cell24Vert t ∈ cell24.toSet := by
  apply subset_convexHull
  simp_rw [cell24, mem_coe, mem_image]
  exact ⟨t, mem_univ _, rfl⟩

lemma isFullDim_cell24 : cell24.IsFullDim := by
  have m1 (i) : .single i 1 ∈ vectorSpan ℝ cell24.toSet := by
    have := Submodule.smul_mem _ (2⁻¹ : ℝ)
      (vsub_mem_vectorSpan ℝ (mem_cell24 (0, i, false)) (mem_cell24 (0, i, true)))
    simp_rw [cell24Vert, Bool.false_eq_true, reduceIte, vsub_eq_sub, Fin.val_zero, pow_zero,
      one_mulVec, PiLp.toLp_single, ← PiLp.single_sub, EuclideanSpace.smul_single,
      show (2⁻¹ : ℝ) * (1 - -1 : ℝ) = 1 by norm_num] at this
    exact this
  have key : vectorSpan ℝ cell24.toSet = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun x ↦ ?_
    convert Submodule.sum_mem (t := univ) _ fun i _ ↦ Submodule.smul_mem _ (x i) (m1 i)
    ext i
    rw [WithLp.ofLp_sum, Finset.sum_apply, sum_eq_single i (by simp_all) (by simp),
      PiLp.smul_apply, PiLp.single_eq_same, smul_eq_mul, mul_one]
  rw [IsFullDim, dim, key, finrank_top, finrank_euclideanSpace_fin]

lemma exists_cell24_params_single (mx : x ∈ cell24.vertices) : ∃ t, x = cell24Vert t := by
  simpa [cell24, eq_comm] using mx

lemma exists_cell24_params {g : Finset (E 4)} (sg : g ⊆ cell24.vertices) :
    ∃ s, g = map ⟨_, injective_cell24Vert⟩ s := by
  refine ⟨g.attach.image fun v ↦ (exists_cell24_params_single (sg v.2)).choose, ?_⟩
  ext v
  simp_rw [mem_map, mem_image, mem_attach, Function.Embedding.coeFn_mk, Subtype.exists, existsAndEq,
    true_and]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ⟨v, h, ((exists_cell24_params_single (sg h)).choose_spec).symm⟩
  · obtain ⟨p, hp, rfl⟩ := h
    rwa [(exists_cell24_params_single (sg hp)).choose_spec] at hp

/-- An index structure that can be interpreted as either

* a pair of non-opposite vertices in a chosen demitesseract
* the midpoint of two such vertices, independent of the choice of demitesseract. -/
@[ext]
structure C24Index where
  /-- Coordinates `a, b` -/
  (a b : Fin 4)
  /-- Signs `s, t` -/
  (s t : Bool)
  /-- The coordinates are strictly ordered -/
  l : a < b

namespace C24Index

variable (I : C24Index)

/-- Interpret a `C24Index` as a pair of non-opposite vertices in a chosen demitesseract. -/
noncomputable def toPair (k : Fin 3) : Bool → E 4
  | false => cell24Vert (k, I.a, I.s)
  | true => cell24Vert (k, I.b, I.t)

/-- Interpret a `C24Index` as a permutation of `(±½, ±½, 0, 0)` (the centres of the 24 cells). -/
noncomputable def toPoint : E 4 :=
  .single I.a (if I.s then -2⁻¹ else 2⁻¹) + .single I.b (if I.t then -2⁻¹ else 2⁻¹)

/-- Replace an ordered pair of axes by the complement ordered pair of axes. -/
def swapAxes : {ab : Fin 4 × Fin 4 // ab.1 < ab.2} → {ab : Fin 4 × Fin 4 // ab.1 < ab.2}
  | ⟨(0, 1), _⟩ => ⟨(2, 3), by lia⟩
  | ⟨(0, 2), _⟩ => ⟨(1, 3), by lia⟩
  | ⟨(0, 3), _⟩ => ⟨(1, 2), by lia⟩
  | ⟨(1, 2), _⟩ => ⟨(0, 3), by lia⟩
  | ⟨(1, 3), _⟩ => ⟨(0, 2), by lia⟩
  | _ => ⟨(0, 1), by lia⟩

/-- The permutation underlying `demitessP` as a plain function. -/
def oneFunc : C24Index where
  a := if I.s = I.t then (swapAxes ⟨(I.a, I.b), I.l⟩).1.1 else I.a
  b := if I.s = I.t then (swapAxes ⟨(I.a, I.b), I.l⟩).1.2 else I.b
  s := if I.a = 0 then !I.s else I.s
  t := !I.s
  l := by
    split_ifs
    · exact (swapAxes _).2
    · exact I.l

lemma oneFunc_iterate_three : I.oneFunc.oneFunc.oneFunc = I := by
  obtain ⟨a, b, s, t, l⟩ := I
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ :
    a = 0 ∧ b = 1 ∨ a = 0 ∧ b = 2 ∨ a = 0 ∧ b = 3 ∨
    a = 1 ∧ b = 2 ∨ a = 1 ∧ b = 3 ∨ a = 2 ∧ b = 3 := by lia
  all_goals cases s <;> cases t <;> simp [oneFunc, swapAxes]

lemma oneFunc_eq_demitessR_mulVec : I.oneFunc.toPoint = demitessR *ᵥ I.toPoint := by
  obtain ⟨a, b, s, t, l⟩ := I
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ :
    a = 0 ∧ b = 1 ∨ a = 0 ∧ b = 2 ∨ a = 0 ∧ b = 3 ∨
    a = 1 ∧ b = 2 ∨ a = 1 ∧ b = 3 ∨ a = 2 ∧ b = 3 := by lia
  all_goals
    simp only [toPoint, oneFunc, swapAxes, WithLp.ofLp_add, PiLp.ofLp_single, Fin.reduceEq,
      reduceIte, mulVec_add, demitessR_mulVec_single, Fin.sum_univ_four, Fin.reduceEq,
      not_true_eq_false, true_iff, false_iff]
    iterate 3 rw [add_add_add_comm, ← Pi.single_add]
    rw [← Pi.single_add]
    cases s <;> cases t <;> norm_num

/-- The permutation underlying `demitessP`. -/
def onePerm : Equiv.Perm C24Index where
  toFun := oneFunc
  invFun := oneFunc ∘ oneFunc
  left_inv _ := by simp [oneFunc_iterate_three]
  right_inv _ := by simp [oneFunc_iterate_three]

/-- The permutation mapping midpoints of `C24Index.toPair` to `C24Index.toPoint`. -/
def demitessP (k : Fin 3) : Equiv.Perm C24Index :=
  onePerm ^ k.1

lemma demitessP_apply {k : Fin 3} :
    midpoint ℝ (I.toPair k false) (I.toPair k true) = (demitessP k I).toPoint := by
  have e : (demitessP k I).toPoint = demitessR ^ k.1 *ᵥ I.toPoint := by
    fin_cases k <;> simp [demitessP, onePerm, sq, oneFunc_eq_demitessR_mulVec]
  rw [WithLp.toLp.injEq, e, midpoint_eq_smul_add, invOf_eq_inv, WithLp.ofLp_smul, WithLp.ofLp_add]
  simp_rw [toPair, cell24Vert, ← mulVec_add, ← mulVec_smul, toPoint, WithLp.ofLp_add,
    PiLp.ofLp_single, smul_add, ← Pi.single_smul, smul_eq_mul, mul_ite, mul_one, mul_neg_one]

/-- The pair of vertices in demitesseract `k` adjacent to `I.toPoint`
(in the sense that the cell with `I.toPoint` as centre includes them). -/
noncomputable def adjPoint (k : Fin 3) : Bool → E 4 :=
  ((demitessP k).symm I).toPair k

lemma adjPoint_apply (k : Fin 3) :
    midpoint ℝ (I.adjPoint k false) (I.adjPoint k true) = I.toPoint := by
  unfold adjPoint
  convert ← demitessP_apply _
  exact Equiv.apply_symm_apply ..

lemma exists_adjPoint_params (k : Fin 3) (s : Bool) :
    ∃ c b, I.adjPoint k s = cell24Vert (k, c, b) := by
  cases s <;> exact ⟨_, _, rfl⟩

lemma adjPoint_mem_toSet {k : Fin 3} {s : Bool} : I.adjPoint k s ∈ cell24.toSet := by
  cases s <;> exact mem_cell24 _

lemma image_adjPoint_subset_vertices :
    (univ.image fun j : Fin 3 × Bool ↦ I.adjPoint j.1 j.2) ⊆ cell24.vertices := fun x mx ↦ by
  rw [mem_image] at mx
  obtain ⟨p, -, rfl⟩ := mx
  cases p.2 <;> exact mem_image_of_mem _ (mem_univ _)

lemma injective_adjPoint : (fun j : Fin 3 × Bool ↦ I.adjPoint j.1 j.2).Injective := by
  rintro ⟨i, s⟩ ⟨j, t⟩ e
  cases s <;> cases t
  all_goals
    simp_rw [adjPoint, toPair, injective_cell24Vert.eq_iff, Prod.mk.injEq] at e
    obtain ⟨rfl, e, -⟩ := e
  · rfl
  · exact absurd e ((demitessP i).symm I).l.ne
  · exact absurd e ((demitessP i).symm I).l.ne'
  · rfl

section IsFace

variable (t) in
lemma inner_toPoint_cell24Vert_le : inner ℝ I.toPoint (cell24Vert t) ≤ 2⁻¹ := by
  rw [← I.adjPoint_apply t.1, midpoint_eq_smul_add, invOf_eq_inv, inner_smul_left, ringHom_apply,
    inv_mul_le_iff₀ zero_lt_two, mul_inv_cancel₀ two_ne_zero, inner_add_left]
  simp_rw [adjPoint, toPair]
  set J := (demitessP t.1).symm I
  obtain h₂ | h₂ : t.2.1 ≠ J.a ∨ t.2.1 ≠ J.b := by grind [J.l]
  · linarith [@inner_cell24Vert_cell24Vert_nonpos (t.1, J.a, J.s) t rfl (by lia),
      @inner_cell24Vert_cell24Vert_le_one (t.1, J.b, J.t) t rfl]
  · linarith [@inner_cell24Vert_cell24Vert_le_one (t.1, J.a, J.s) t rfl,
      @inner_cell24Vert_cell24Vert_nonpos (t.1, J.b, J.t) t rfl (by lia)]

variable (t) in
lemma inner_toPoint_cell24Vert_eq_iff :
    inner ℝ I.toPoint (cell24Vert t) = 2⁻¹ ↔ ∃ s, cell24Vert t = I.adjPoint t.1 s := by
  rw [← I.adjPoint_apply t.1, midpoint_eq_smul_add, invOf_eq_inv, inner_smul_left, ringHom_apply,
    mul_eq_left₀ (by positivity), inner_add_left]
  simp_rw [Bool.exists_bool, adjPoint, toPair, injective_cell24Vert.eq_iff]
  set J := (demitessP t.1).symm I
  constructor <;> intro h
  · contrapose! h
    linarith [@inner_cell24Vert_cell24Vert_nonpos (t.1, J.a, J.s) t rfl h.1.symm,
      @inner_cell24Vert_cell24Vert_nonpos (t.1, J.b, J.t) t rfl h.2.symm]
  · obtain h | h := h
    all_goals
      simp only [← h, real_inner_self_eq_norm_sq, norm_cell24Vert, one_pow,
        add_eq_left, add_eq_right]
      exact inner_cell24Vert_cell24Vert_eq_zero rfl (by grind [J.l])

lemma inner_toPoint_adjPoint {k : Fin 3} {s : Bool} : inner ℝ I.toPoint (I.adjPoint k s) = 2⁻¹ := by
  obtain ⟨c, b, h⟩ := I.exists_adjPoint_params k s
  rw [h, inner_toPoint_cell24Vert_eq_iff]
  exact ⟨_, h.symm⟩

lemma inner_toPoint_le_of_mem_toSet (mx : x ∈ cell24.toSet) : inner ℝ I.toPoint x ≤ 2⁻¹ := by
  simp_rw [toSet, mem_convexHull'] at mx
  obtain ⟨w, nnw, sw, rfl⟩ := mx
  simp_rw [inner_sum, inner_smul_right]
  calc
    _ ≤ ∑ x ∈ cell24.vertices, w x * 2⁻¹ := by
      refine sum_le_sum fun y my ↦ ?_
      obtain ⟨t, rfl⟩ := exists_cell24_params_single my
      exact mul_le_mul_of_nonneg_left (I.inner_toPoint_cell24Vert_le _) (nnw _ my)
    _ = _ := by rw [← sum_mul, sw, one_mul]

lemma inner_toPoint_eq_iff_of_mem_toSet (mx : x ∈ cell24.toSet) :
    inner ℝ I.toPoint x = 2⁻¹ ↔
    x ∈ convexHull ℝ (univ.image fun j : Fin 3 × Bool ↦ I.adjPoint j.1 j.2) := by
  constructor <;> intro h
  · refine mem_convex_of_dual_max (L := innerSL ℝ I.toPoint) (fun v mv ↦ ?_) (fun v mv hv ↦ ?_)
      (convex_convexHull ..) mx h
    · obtain ⟨t, rfl⟩ := exists_cell24_params_single mv
      exact I.inner_toPoint_cell24Vert_le _
    · obtain ⟨t, rfl⟩ := exists_cell24_params_single mv
      rw [coe_innerSL_apply, inner_toPoint_cell24Vert_eq_iff] at hv
      obtain ⟨s, hs⟩ := hv
      exact subset_convexHull ℝ _ (by rw [mem_coe, hs]; exact mem_image_of_mem _ (mem_univ (_, s)))
  · simp_rw [mem_convexHull'] at h
    obtain ⟨w, nnw, sw, rfl⟩ := h
    simp_rw [inner_sum, inner_smul_right]
    set S := univ.image fun j : Fin 3 × Bool ↦ I.adjPoint j.1 j.2
    calc
      _ = ∑ x ∈ S, w x * 2⁻¹ := by
        refine sum_congr rfl fun y my ↦ ?_
        simp_rw [S, mem_image] at my
        obtain ⟨p, -, hp⟩ := my
        rw [← hp, inner_toPoint_adjPoint]
      _ = _ := by rw [← sum_mul, sw, one_mul]

theorem isFace_convexHull_adjPoint :
    cell24.IsFace (convexHull ℝ (univ.image fun j : Fin 3 × Bool ↦ I.adjPoint j.1 j.2)) := by
  refine ⟨fun _ ↦ ⟨innerSL ℝ I.toPoint, ?_⟩, by rw [convexHull_nonempty_iff, coe_nonempty]; simp⟩
  ext x
  simp only [Set.mem_ofPred_eq, coe_innerSL_apply]
  refine ⟨fun mx ↦ ?_, ?_⟩
  · have mxC : x ∈ cell24.toSet :=
      Set.mem_of_subset_of_mem (convexHull_mono I.image_adjPoint_subset_vertices) mx
    refine ⟨mxC, fun y my ↦ ?_⟩
    · rw [(I.inner_toPoint_eq_iff_of_mem_toSet mxC).mpr mx]
      exact I.inner_toPoint_le_of_mem_toSet my
  · rintro ⟨mx, maxx⟩
    rw [← I.inner_toPoint_eq_iff_of_mem_toSet mx]
    apply le_antisymm (I.inner_toPoint_le_of_mem_toSet mx)
    have h := maxx (I.adjPoint 0 false) I.adjPoint_mem_toSet
    rwa [inner_toPoint_adjPoint] at h

end IsFace

section FaceDim

lemma vectorSpan_convexHull_adjPoint :
    Submodule.span ℝ (Set.range fun i ↦ I.adjPoint i false - I.adjPoint i true) ≤
    vectorSpan ℝ (univ.image fun j : Fin 3 × Bool ↦ I.adjPoint j.1 j.2 : Set (E 4)) := by
  rw [Submodule.span_le]
  rintro - ⟨i, rfl⟩
  have ma (s) : I.adjPoint i s ∈ univ.image fun j : Fin 3 × Bool ↦ I.adjPoint j.1 j.2 := by
    rw [mem_image]
    exact ⟨(i, s), mem_univ _, rfl⟩
  exact vsub_mem_vectorSpan ℝ (ma false) (ma true)

lemma inner_toPoint_self : inner ℝ I.toPoint I.toPoint = 2⁻¹ := by
  simp_rw [real_inner_self_eq_norm_sq, EuclideanSpace.norm_sq_eq, norm_eq_abs, sq_abs]
  have nzm (i) (hi : I.toPoint i ^ 2 ≠ 0) : i ∈ ({I.a, I.b} : Finset _) := by
    contrapose hi
    rw [mem_insert, mem_singleton, not_or] at hi
    simp_rw [toPoint, PiLp.add_apply, PiLp.single_eq_of_ne _ hi.1, PiLp.single_eq_of_ne _ hi.2]
    simp
  simp_rw [← Fintype.sum_subset nzm, sum_pair I.l.ne, toPoint, PiLp.add_apply, PiLp.single_eq_same,
    PiLp.single_eq_of_ne _ I.l.ne, PiLp.single_eq_of_ne _ I.l.ne', add_zero, zero_add, ite_pow,
    neg_sq, ite_self]
  norm_num

lemma inner_adjPoint_sub_toPoint_self {k : Fin 3} {s : Bool} :
    inner ℝ (I.adjPoint k s - I.toPoint) (I.adjPoint k s - I.toPoint) = 2⁻¹ := by
  obtain ⟨c, b, h⟩ := I.exists_adjPoint_params k s
  have h : inner ℝ (I.adjPoint k s) (I.adjPoint k s) = 1 := by
    rw [h, real_inner_self_eq_norm_sq, norm_cell24Vert, one_pow]
  rw [inner_sub_sub_self, h, inner_toPoint_adjPoint, real_inner_comm, inner_toPoint_adjPoint,
    inner_toPoint_self]
  norm_num

lemma pairwise_adjPoint_vec_orthogonal :
    Pairwise fun i j ↦ inner ℝ (I.adjPoint i false - I.adjPoint i true)
      (I.adjPoint j false - I.adjPoint j true) = 0 := fun i j hn ↦ by
  suffices inner ℝ (I.adjPoint i false - I.toPoint) (I.adjPoint j false - I.toPoint) = 0 by
    have midi := left_sub_midpoint (R := ℝ) (I.adjPoint i false) (I.adjPoint i true)
    have midj := left_sub_midpoint (R := ℝ) (I.adjPoint j false) (I.adjPoint j true)
    rw [adjPoint_apply, invOf_eq_inv] at midi midj
    rwa [midi, midj, inner_smul_left, ringHom_apply, inner_smul_right, ← mul_assoc,
      mul_eq_zero_iff_left (by positivity)] at this
  have cs := real_inner_mul_inner_self_le
    (I.adjPoint i false - I.toPoint) (I.adjPoint j false - I.toPoint)
  have red : inner ℝ (I.adjPoint i false - I.toPoint) (I.adjPoint j false - I.toPoint) =
      inner ℝ (I.adjPoint i false) (I.adjPoint j false) - 2⁻¹ := by
    simp_rw [inner_sub_left, inner_sub_right, inner_toPoint_adjPoint, real_inner_comm I.toPoint,
      inner_toPoint_adjPoint, inner_toPoint_self, sub_self, sub_zero]
  simp_rw [inner_adjPoint_sub_toPoint_self, red] at cs
  have aia : |inner ℝ (I.adjPoint i false) (I.adjPoint j false)| = 2⁻¹ := by
    obtain ⟨_, _, ei⟩ := I.exists_adjPoint_params i false
    obtain ⟨_, _, ej⟩ := I.exists_adjPoint_params j false
    exact ei ▸ ej ▸ abs_inner_cell24Vert_of_fst_ne hn
  rw [abs_eq (by positivity)] at aia
  obtain h | h := aia
  · rw [red, h, sub_self]
  · norm_num [h] at cs

theorem faceDim_convexHull_adjPoint :
    3 ≤ faceDim (convexHull ℝ (univ.image fun j : _ × _ ↦ I.adjPoint j.1 j.2 : Set (E 4))) := by
  rw [faceDim, vectorSpan_convexHull_eq_vectorSpan]
  suffices Module.finrank ℝ (Submodule.span ℝ (Set.range fun i ↦
      I.adjPoint i false - I.adjPoint i true)) = 3 by
    nth_rw 1 [← this]
    exact Submodule.finrank_mono I.vectorSpan_convexHull_adjPoint
  refine finrank_span_eq_card (linearIndependent_of_ne_zero_of_inner_eq_zero (fun i ↦ ?_)
    I.pairwise_adjPoint_vec_orthogonal)
  simp_rw [sub_ne_zero, adjPoint, toPair, injective_cell24Vert.ne_iff]
  have := ((demitessP i).symm I).l
  lia

end FaceDim

end C24Index

variable {f : Set (E 4)} (hf : cell24.IsFace f) (df : faceDim f < 4)

lemma zero_mem_cell24_openSegment_antipodes {k : Fin 3} {c : Fin 4} :
    0 ∈ openSegment ℝ (cell24Vert (k, c, false)) (cell24Vert (k, c, true)) := by
  refine ⟨_, _, by positivity, by positivity, add_halves 1, ?_⟩
  simp_rw [cell24Vert, Bool.false_eq_true, reduceIte, Pi.single_neg, mulVec_neg, WithLp.toLp_neg,
    smul_neg, add_neg_cancel]

include hf df in
lemma no_antipodes_of_isFace_cell24 (k : Fin 3) (c : Fin 4) :
    cell24Vert (k, c, false) ∉ f ∨ cell24Vert (k, c, true) ∉ f := by
  replace df : ∃ t, cell24Vert t ∉ f := by
    contrapose! df
    conv_lhs => rw [← isFullDim_cell24, dim, toSet]
    rw [vectorSpan_convexHull_eq_vectorSpan, faceDim]
    refine Submodule.finrank_mono (vectorSpan_mono _ fun x mx ↦ ?_)
    simp_rw [mem_coe, cell24, mem_image] at mx
    obtain ⟨t, -, rfl⟩ := mx
    exact df t
  have cf := hf.1.convex (convex_convexHull ..)
  replace hf := hf.1.isExtreme.left_mem_of_mem_openSegment
  contrapose! hf
  obtain ⟨t, h⟩ := df
  refine ⟨_, mem_cell24 t, _, mem_cell24 (t.1, t.2.1, !t.2.2), _,
    cf.openSegment_subset hf.1 hf.2 zero_mem_cell24_openSegment_antipodes, ?_, h⟩
  change 0 ∈ openSegment ℝ (cell24Vert (t.1, t.2.1, t.2.2)) _
  cases hs : t.2.2
  · exact zero_mem_cell24_openSegment_antipodes
  · rw [openSegment_symm]
    exact zero_mem_cell24_openSegment_antipodes

include hf df in
lemma exists_toPoint_mem_of_fst_eq_of_ne (mt : cell24Vert t ∈ f) (mu : cell24Vert u ∈ f)
    (h₁ : t.1 = u.1) (hn : t ≠ u) : ∃ I : C24Index, I.toPoint ∈ f := by
  have h₂ := no_antipodes_of_isFace_cell24 hf df t.1 t.2.1
  replace h₂ : t.2.1 ≠ u.2.1 := by
    contrapose! h₂
    cases ts : t.2.2 <;> simp_rw [← ts, mt]
    · simp_rw [show true = u.2.2 by lia, h₂, h₁, mu, true_and]
    · simp_rw [show false = u.2.2 by lia, h₂, h₁, mu, true_and]
  wlog hl : t.2.1 < u.2.1 generalizing t u
  · exact this mu mt h₁.symm hn.symm h₂.symm (by lia)
  let I : C24Index := ⟨_, _, t.2.2, u.2.2, hl⟩
  have mI : midpoint ℝ (I.toPair t.1 false) (I.toPair t.1 true) ∈ f := by
    simp_rw [C24Index.toPair, I, Prod.mk.eta, h₁, Prod.mk.eta]
    exact (hf.1.convex (convex_convexHull ..)).midpoint_mem mt mu
  rw [I.demitessP_apply] at mI
  exact ⟨_, mI⟩

include hf in
lemma adjPoint_mem_of_toPoint_mem {I : C24Index} (mI : I.toPoint ∈ f) :
    ∀ k s, I.adjPoint k s ∈ f := fun k ↦ by
  replace hf := hf.1.isExtreme.left_mem_of_mem_openSegment
  contrapose! hf
  obtain ⟨s, hs⟩ := hf
  refine ⟨I.adjPoint k s, I.adjPoint_mem_toSet, I.adjPoint k !s, I.adjPoint_mem_toSet,
    _, mI, ?_, hs⟩
  rw [← I.adjPoint_apply k]
  cases s
  · exact midpoint_mem_openSegment ..
  · rw [midpoint_comm]
    exact midpoint_mem_openSegment ..

include hf in
theorem cell24_facet_characterisation (df : faceDim f = 3) :
    ∃ I : C24Index, f = convexHull ℝ (univ.image fun j : Fin 3 × Bool ↦ I.adjPoint j.1 j.2) := by
  have cs := faceDim_add_one_le_card_faceGens hf
  obtain ⟨s, hs⟩ := exists_cell24_params (faceGens_subset_vertices hf.1)
  nth_rw 1 [df, hs, card_map, Nat.add_one_le_iff, ← card_fin 3] at cs
  have sg : (faceGens hf.1 : Set _) ⊆ f := fun x mx ↦ by
    rw [convexHull_faceGens hf.1]
    exact subset_convexHull _ _ mx
  obtain ⟨t, mt, u, mu, hn, h₁⟩ := exists_ne_map_eq_of_card_lt_of_maps_to (f := (·.1)) cs (by simp)
  obtain ⟨I, hI⟩ := exists_toPoint_mem_of_fst_eq_of_ne hf (by lia)
    (sg (hs ▸ mem_map_of_mem _ mt)) (sg (hs ▸ mem_map_of_mem _ mu)) h₁ hn
  refine ⟨I, eq_of_superset_of_not_ssuperset ?_ ?_⟩
  · refine convexHull_min (fun x mx ↦ ?_) (hf.1.convex (convex_convexHull ..))
    rw [mem_coe, mem_image] at mx
    obtain ⟨p, -, rfl⟩ := mx
    exact adjPoint_mem_of_toPoint_mem hf hI ..
  · by_contra! hc
    have := I.faceDim_convexHull_adjPoint
    have := faceDim_strictMono I.isFace_convexHull_adjPoint hf hc
    lia

include hf in
lemma no_adjPoint_antipodes_of_faceDim_lt_three {I : C24Index} (df : faceDim f < 3) {i : Fin 3} :
    I.adjPoint i false ∉ f ∨ I.adjPoint i true ∉ f := by
  by_contra! hc
  have mall : I.toPoint ∈ f := by
    have := (hf.1.convex (convex_convexHull ..)).midpoint_mem hc.1 hc.2
    rwa [I.adjPoint_apply] at this
  replace mall := adjPoint_mem_of_toPoint_mem hf mall
  have csf : convexHull ℝ (univ.image fun j : Fin 3 × Bool ↦ I.adjPoint j.1 j.2) ⊆ f := by
    refine convexHull_min (fun x mx ↦ ?_) (hf.1.convex (convex_convexHull ..))
    rw [mem_coe, mem_image] at mx
    obtain ⟨p, -, rfl⟩ := mx
    exact mall ..
  have := I.faceDim_convexHull_adjPoint
  have := faceDim_mono I.isFace_convexHull_adjPoint hf csf
  lia

theorem cell24_flag_characterisation (F : cell24.Flag) :
    ∃ I : C24Index, ∃ p : Equiv.Perm (Fin 3), ∃ s : Fin 3 → Bool,
    (∀ d, F.face d.castSucc = convexHull ℝ ((Iic d).image fun j ↦ I.adjPoint (p j) (s j))) ∧
    F.face 3 = convexHull ℝ (univ.image fun j : Fin 3 × Bool ↦ I.adjPoint j.1 j.2) := by
  -- Handle the facet characterisation first
  obtain ⟨I, f₃⟩ := cell24_facet_characterisation (F.isFace 3) (F.dim_eq 3)
  suffices ∃ p : Equiv.Perm (Fin 3), ∃ s : Fin 3 → Bool,
      ∀ d, F.face d.castSucc = convexHull ℝ ((Iic d).image fun j ↦ I.adjPoint (p j) (s j)) by
    obtain ⟨p, s, h⟩ := this
    exact ⟨I, p, s, h, f₃⟩
  -- Obtain the `adjPoint` generators `s₂` for the 2D face
  set O := univ.image fun j : Fin 3 × Bool ↦ I.adjPoint j.1 j.2
  have gf₃ : faceGens (F.isFace 3).1 = O :=
    (existsUnique_faceGens (F.isFace 3).1).unique
      (exists_faceGens (F.isFace 3).1).choose_spec ⟨I.image_adjPoint_subset_vertices, f₃⟩
  let g (d : Fin 3) := faceGens (F.isFace d.castSucc).1
  have ssg₂ : g 2 ⊂ O := by
    simp_rw [← gf₃, g, faceGens_ssubset_iff]
    exact F.strict_mono _ _ (by simp)
  obtain ⟨s₂, ims₂⟩ := subset_univ_image_iff.mp ssg₂.subset
  -- Taking the first component is injective on `s₂`
  have inj1 : Set.InjOn (·.1) (s₂ : Set (Fin 3 × Bool)) := by
    unfold Set.InjOn
    by_contra! con
    obtain ⟨p, mp, q, mq, h₁, hn⟩ := con
    replace mp := subset_convexHull ℝ _ (ims₂ ▸ mem_image_of_mem _ mp)
    replace mq := subset_convexHull ℝ _ (ims₂ ▸ mem_image_of_mem _ mq)
    simp_rw [g, ← convexHull_faceGens] at mp mq
    rw [← h₁, show q.2 = !p.2 by lia] at mq
    cases p₂ : p.2 <;> rw [p₂] at mp mq
    · exact no_adjPoint_antipodes_of_faceDim_lt_three (F.isFace 2) (by simp [F.dim_eq 2])
        |>.resolve_right (by simpa using mq) mp
    · exact no_adjPoint_antipodes_of_faceDim_lt_three (F.isFace 2) (by simp [F.dim_eq 2])
        |>.resolve_left (by simpa using mq) mp
  -- Prove hypotheses for `exists_chain_sequencing` and obtain the chain
  have smg (i j) (l : i < j) : g i ⊂ g j := by
    rw [faceGens_ssubset_iff]
    exact F.strict_mono _ _ l
  have cardg (d) : #(g d) = d.1 + 1 := by
    have l₀ : 0 < #(g 0) := card_pos.mpr <| nonempty_faceGens (F.isFace 0)
    have l₁ : #(g 0) < #(g 1) := card_lt_card (smg _ _ (by lia))
    have l₂ : #(g 1) < #(g 2) := card_lt_card (smg _ _ (by lia))
    have l₃ : #(g 2) ≤ 3 := by
      rw [← ims₂, card_image_of_injective _ I.injective_adjPoint]
      contrapose! inj1
      refine not_injOn_of_card_image_lt ((card_le_univ _).trans_lt ?_)
      rwa [Fintype.card_fin]
    fin_cases d <;> lia
  obtain ⟨p, hp⟩ := exists_chain_sequencing cardg smg
  -- Construct the required `p` and `s` and finish
  have ex (i) : ∃ r : Fin 3 × Bool, p i = I.adjPoint r.1 r.2 := by
    specialize hp (Fin.last _)
    rw [Iic_last_eq_univ, show Fin.last 2 = 2 by rfl, ← ims₂] at hp
    replace hp := mem_image.mp (hp ▸ mem_map_of_mem p (mem_univ i))
    obtain ⟨r, -, hr⟩ := hp
    exact ⟨r, hr.symm⟩
  let p' (i) := (ex i).choose.1
  let s (i) := (ex i).choose.2
  have ψ (i) : p i = I.adjPoint (p' i) (s i) := (ex i).choose_spec
  have injp' : p'.Injective := fun i j e ↦ by
    rw [← p.apply_eq_iff_eq]
    unfold Set.InjOn at inj1
    contrapose! inj1
    specialize hp (Fin.last _)
    rw [Iic_last_eq_univ, show Fin.last 2 = 2 by rfl, ← ims₂] at hp
    refine ⟨(p' i, s i), ?_, (p' j, s j), ?_, e, by rwa [← I.injective_adjPoint.ne_iff, ← ψ, ← ψ]⟩
    all_goals rw [mem_coe]
    · obtain ⟨q, mq, hq⟩ := mem_image.mp (hp ▸ mem_map_of_mem p (mem_univ i))
      rw [ψ, I.injective_adjPoint.eq_iff] at hq
      rwa [hq] at mq
    · obtain ⟨q, mq, hq⟩ := mem_image.mp (hp ▸ mem_map_of_mem p (mem_univ j))
      rw [ψ, I.injective_adjPoint.eq_iff] at hq
      rwa [hq] at mq
  rw [Finite.injective_iff_bijective] at injp'
  let perm := Equiv.ofBijective p' injp'
  refine ⟨perm, s, fun d ↦ ?_⟩
  rw [convexHull_faceGens (F.isFace d.castSucc).1,
    show faceGens (F.isFace d.castSucc).1 = g d by rfl, hp, map_eq_image]
  congr! with i
  exact ψ i
