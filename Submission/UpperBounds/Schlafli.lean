import Submission.UpperBounds.Orthoscheme

open Fin Real Matrix

lemma Real.sq_sin_pi_div_four : sin (π / 4) ^ 2 = 1 / 2 := by
  norm_num [div_pow]

lemma Real.sq_cos_pi_div_four : cos (π / 4) ^ 2 = 1 / 2 := by
  norm_num [div_pow]

lemma Real.sq_sin_pi_div_five : sin (π / 5) ^ 2 = (5 - √5) / 8 := by
  rw [sin_sq, cos_pi_div_five]
  nlinarith [sq_sqrt (show 0 ≤ 5 by norm_num)]

namespace LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {n : ℕ} {P Q : ConvexPolytope (n + 1)} (rP : P.IsRegular) (rQ : Q.IsRegular) {i : Fin n}

variable (i) in
/-- The **Schläfli symbol** of a regular polytope of positive dimension. -/
noncomputable def IsRegular.schlafli : ℕ :=
  ⌊π / arccos (-rP.cosineMatrix i.castSucc i.succ)⌋₊

lemma cosineMatrix_eq_neg_cos_pi_div_schlafli :
    rP.cosineMatrix i.castSucc i.succ = -cos (π / rP.schlafli i) := by
  obtain ⟨p, hp⟩ := cosineMatrix_eq_neg_cos_pi_div_nat_of_near rP
    (show i.castSucc.1 + 1 = i.succ.1 by simp)
  rw [IsRegular.schlafli, hp, neg_inj, neg_neg, arccos_cos (by positivity)
      (div_nat_le_self_of_nonnneg pi_nonneg p), div_div_cancel₀ pi_ne_zero, Nat.floor_natCast]

lemma three_le_schlafli : 3 ≤ rP.schlafli i := by
  have lb := neg_one_lt_cosineMatrix rP (i := i.castSucc) (j := i.succ)
  have ub := cosineMatrix_apply_near rP (show i.castSucc.1 + 1 = i.succ.1 by simp)
  rw [cosineMatrix_eq_neg_cos_pi_div_schlafli rP] at lb ub
  by_contra! hc
  interval_cases rP.schlafli i <;> simp_all
  linarith

lemma schlafli_eq_iff_similar : rP.schlafli = rQ.schlafli ↔ P.Similar Q := by
  rw [cosineMatrix_eq_iff_similar rP rQ]
  constructor <;> intro h
  · ext i j
    wlog l : i ≤ j generalizing i j
    · specialize this j i (by lia)
      have syP := (posDef_cosineMatrix rP).1
      have syQ := (posDef_cosineMatrix rQ).1
      rw [isHermitian_iff_isSymm, IsSymm.ext_iff] at syP syQ
      rwa [syP, syQ]
    obtain rfl | hij | hij : i = j ∨ i.1 + 1 = j.1 ∨ i.1 + 1 < j.1 := by lia
    · simp_rw [cosineMatrix_apply_self]
    · let k := i.castPred (by grind)
      have ki : i = k.castSucc := by simp [k]
      have kj : j = k.succ := by ext; simp [k, ← hij]
      simp_rw [ki, kj, cosineMatrix_eq_neg_cos_pi_div_schlafli, h]
    · simp_rw [cosineMatrix_apply_far _ hij]
  · unfold IsRegular.schlafli
    simp_rw [h]

/-- Convert a Schläfli symbol into the corresponding cosine matrix. -/
noncomputable def toCosineMatrix (s : Fin n → ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  .of fun i j ↦ if i = j then 1
    else if h : i.1 + 1 = j.1 then -cos (π / s (j.pred (by simp [ne_iff_vne, ← h])))
    else if h : j.1 + 1 = i.1 then -cos (π / s (i.pred (by simp [ne_iff_vne, ← h])))
    else 0

lemma toCosineMatrix_schlafli : toCosineMatrix rP.schlafli = rP.cosineMatrix := by
  ext i j
  simp_rw [toCosineMatrix, of_apply]
  have sy := (posDef_cosineMatrix rP).1
  rw [isHermitian_iff_isSymm, IsSymm.ext_iff] at sy
  split_ifs with h₁ h₂ h₃
  · rw [h₁, cosineMatrix_apply_self]
  · set k : Fin n := j.pred (by simp [ne_iff_vne, ← h₂])
    rw [show i = k.castSucc by grind, show j = k.succ by grind,
      cosineMatrix_eq_neg_cos_pi_div_schlafli]
  · set k : Fin n := i.pred (by simp [ne_iff_vne, ← h₃])
    rw [show j = k.castSucc by grind, show i = k.succ by grind,
      ← cosineMatrix_eq_neg_cos_pi_div_schlafli]
    exact sy ..
  · obtain h₄ | h₄ : i.1 + 1 < j.1 ∨ j.1 + 1 < i.1 := by lia
    · rw [cosineMatrix_apply_far rP h₄]
    · rw [sy, cosineMatrix_apply_far rP h₄]

/-- A Schläfli symbol is admissible if applying `toCosineMatrix` yields a positive-definite matrix
and all its numbers are at least 3. -/
def IsAdmissibleSymbol (s : Fin n → ℕ) : Prop :=
  (toCosineMatrix s).PosDef ∧ ∀ i, 3 ≤ s i

lemma isAdmissibleSymbol_schlafli : IsAdmissibleSymbol rP.schlafli := by
  rw [IsAdmissibleSymbol, toCosineMatrix_schlafli]
  exact ⟨posDef_cosineMatrix rP, fun _ ↦ three_le_schlafli rP⟩

theorem isAdmissibleSymbol_comp_castSucc {s : Fin (n + 1) → ℕ} (hs : IsAdmissibleSymbol s) :
    IsAdmissibleSymbol (s ∘ castSucc) := by
  have sm : toCosineMatrix (s ∘ castSucc) = (toCosineMatrix s).submatrix castSucc castSucc := by
    ext i j
    simp only [toCosineMatrix, of_apply, submatrix_apply, castSucc_inj]
    congr
  exact ⟨sm ▸ hs.1.submatrix (castSucc_injective _), fun _ ↦ hs.2 _⟩

theorem isAdmissibleSymbol_comp_succ {s : Fin (n + 1) → ℕ} (hs : IsAdmissibleSymbol s) :
    IsAdmissibleSymbol (s ∘ succ) := by
  have sm : toCosineMatrix (s ∘ succ) = (toCosineMatrix s).submatrix succ succ := by
    ext i j
    simp [toCosineMatrix]
  exact ⟨sm ▸ hs.1.submatrix (succ_injective _), fun _ ↦ hs.2 _⟩

theorem det_toCosineMatrix_recursion (a b : ℕ) (s : Fin n → ℕ) :
    (toCosineMatrix (vecCons a (vecCons b s))).det =
    (toCosineMatrix (vecCons b s)).det - cos (π / a) ^ 2 * (toCosineMatrix s).det := by
  rw [det_succ_row_zero, sum_univ_succ, succAbove_zero, val_zero, pow_zero, one_mul,
    show toCosineMatrix (vecCons a (vecCons b s)) 0 0 = 1 by simp [toCosineMatrix], one_mul]
  have z₁ (i : Fin (n + 2)) (hi : i ≠ 0) :
      (-1) ^ i.succ.1 * toCosineMatrix (vecCons a (vecCons b s)) 0 i.succ *
      ((toCosineMatrix (vecCons a (vecCons b s))).submatrix succ i.succ.succAbove).det = 0 := by
    suffices toCosineMatrix (vecCons a (vecCons b s)) 0 i.succ = 0 by simp [this]
    simp [toCosineMatrix, hi, show 0 ≠ i.succ by simp [ne_iff_vne]]
  rw [Fintype.sum_eq_single _ z₁, val_succ, val_zero, zero_add, pow_one, neg_one_mul, neg_mul,
    ← sub_eq_add_neg, sq, ← neg_mul_neg (cos _), mul_assoc]
  congr
  · ext i j
    have e₁ {p q : Fin (n + 2)} : p.succ.1 + 1 = q.succ.1 ↔ p.1 + 1 = q.1 := by simp
    simp_rw [toCosineMatrix, submatrix_apply, of_apply, succ_inj, e₁]
    congr with h
    on_goal 2 => congr with h'
    all_goals
      congr 4
      generalize_proofs _ _ _ n₁
      nth_rw 1 [pred_succ, ← succ_pred _ n₁, cons_val_succ]
  have z₂ (i : Fin (n + 2)) (hi : i ≠ 0) :
      (-1) ^ i.1 * (toCosineMatrix (vecCons a (vecCons b s))).submatrix
        succ (succ 0).succAbove i 0 *
      (((toCosineMatrix (vecCons a (vecCons b s))).submatrix
        succ (succ 0).succAbove).submatrix i.succAbove succ).det = 0 := by
    suffices toCosineMatrix (vecCons a (vecCons b s)) i.succ 0 = 0 by simp [this]
    simp [toCosineMatrix, hi]
  have r₁ : toCosineMatrix (vecCons a (vecCons b s)) (succ 0) (succAbove 1 0) = -cos (π / a) := by
    simp [toCosineMatrix]
  rw [det_succ_column_zero, Fintype.sum_eq_single _ z₂, val_zero, pow_zero, one_mul,
    succ_zero_eq_one, submatrix_apply, r₁, submatrix_submatrix, succAbove_zero]
  clear z₁ z₂ r₁
  congr
  ext i j
  have e₁ {p q : Fin (n + 1)} : p.succ.succ.1 + 1 = q.succ.succ.1 ↔ p.1 + 1 = q.1 := by simp
  simp_rw [submatrix_apply, Function.comp_apply, one_succAbove_succ, toCosineMatrix, of_apply,
    succ_inj, e₁]
  congr with h
  on_goal 2 => congr with h'
  all_goals
    congr 4
    generalize_proofs _ _ _ n₁
    nth_rw 1 [pred_succ, cons_val_succ, ← succ_pred _ n₁, cons_val_succ]

lemma det_toCosineMatrix_length_one {s : Fin 1 → ℕ} :
    (toCosineMatrix s).det = sin (π / s 0) ^ 2 := by
  simp [toCosineMatrix, det_fin_two, ← sq, sin_sq]

lemma det_toCosineMatrix_length_two {s : Fin 2 → ℕ} :
    (toCosineMatrix s).det = sin (π / s 1) ^ 2 - cos (π / s 0) ^ 2 := by
  simp [toCosineMatrix, det_fin_three, ← sq, sin_sq]

lemma det_toCosineMatrix_length_three {s : Fin 3 → ℕ} :
    (toCosineMatrix s).det = sin (π / s 0) ^ 2 * sin (π / s 2) ^ 2 - cos (π / s 1) ^ 2 := by
  have key := det_toCosineMatrix_recursion (s 0) (s 1) ![s 2]
  norm_num [det_toCosineMatrix_length_one, det_toCosineMatrix_length_two] at key
  rw [sub_right_comm, ← one_sub_mul, ← sin_sq] at key
  convert key; ext i; fin_cases i <;> simp

lemma det_toCosineMatrix_length_four {s : Fin 4 → ℕ} :
    (toCosineMatrix s).det = sin (π / s 0) ^ 2 * sin (π / s 3) ^ 2 -
    sin (π / s 0) ^ 2 * cos (π / s 2) ^ 2 - cos (π / s 1) ^ 2 * sin (π / s 3) ^ 2 := by
  have key := det_toCosineMatrix_recursion (s 0) (s 1) ![s 2, s 3]
  norm_num [det_toCosineMatrix_length_two, det_toCosineMatrix_length_three] at key
  simp only [cons_val] at key
  nth_rw 1 [mul_sub, cos_sq' (π / s 0), one_sub_mul, sub_sub_sub_comm, ← sub_add, ← sub_add,
    sub_add_comm (_ * _), sub_add, ← one_sub_mul, ← sin_sq, sub_add, ← one_sub_mul, ← cos_sq',
    sub_right_comm] at key
  convert key; ext i; fin_cases i <;> simp

/-! ### The actual enumeration -/

/-- Note that `three` refers to the polytope dimension, not the length of `s`. -/
theorem admissible_three {s : Fin 2 → ℕ} (hs : IsAdmissibleSymbol s) :
    s = ![3, 3] ∨ s = ![3, 4] ∨ s = ![4, 3] ∨ s = ![3, 5] ∨ s = ![5, 3] := by
  have lb₀ := hs.2 0
  have lb₁ := hs.2 1
  have det := hs.1.det_pos
  have nn₁ : 0 ≤ cos (π / s 0) := by
    refine cos_nonneg_of_mem_Icc ⟨(show 0 ≤ π / s 0 by positivity).trans' ?_, ?_⟩
    · rw [neg_nonpos]; positivity
    · exact div_le_div_of_nonneg_left pi_nonneg zero_lt_two (by norm_cast; lia)
  have nn₂ : 0 ≤ sin (π / s 1) :=
    sin_nonneg_of_mem_Icc ⟨by positivity, div_nat_le_self_of_nonnneg pi_nonneg _⟩
  have mi₁ : π / s 0 ∈ Set.Icc 0 π :=
    ⟨by positivity, div_nat_le_self_of_nonnneg pi_nonneg _⟩
  have mi₂ : π / 2 - π / s 1 ∈ Set.Icc 0 π := by
    constructor
    · rw [sub_nonneg]
      exact div_le_div_of_nonneg_left pi_nonneg zero_lt_two (by norm_cast; lia)
    · exact (sub_le_self _ (by positivity)).trans (half_le_self pi_nonneg)
  simp_rw [det_toCosineMatrix_length_two, sub_pos, sq_lt_sq₀ nn₁ nn₂, ← cos_pi_div_two_sub,
    strictAntiOn_cos.lt_iff_gt mi₁ mi₂, sub_lt_iff_lt_add, div_eq_mul_inv, ← mul_add,
    mul_lt_mul_iff_right₀ pi_pos] at det
  have ub₀ : s 0 ≤ 5 := by
    contrapose! det
    calc
      _ ≤ (s 0 : ℝ)⁻¹ + 3⁻¹ := add_le_add_right (inv_anti₀ zero_lt_three (mod_cast lb₁)) _
      _ ≤ _ := by
        rw [← le_sub_iff_add_le, show (2⁻¹ : ℝ) - 3⁻¹ = 6⁻¹ by norm_num]
        exact inv_anti₀ (by norm_num) (by norm_cast)
  have ub₁ : s 1 ≤ 5 := by
    contrapose! det
    calc
      _ ≤ 3⁻¹ + (s 1 : ℝ)⁻¹ := add_le_add_left (inv_anti₀ zero_lt_three (mod_cast lb₀)) _
      _ ≤ _ := by
        rw [← le_sub_iff_add_le', show (2⁻¹ : ℝ) - 3⁻¹ = 6⁻¹ by norm_num]
        exact inv_anti₀ (by norm_num) (by norm_cast)
  interval_cases s₀ : s 0 <;> interval_cases s₁ : s 1 <;> norm_num at det <;> simp_all [funext_iff]

theorem admissible_four {s : Fin 3 → ℕ} (hs : IsAdmissibleSymbol s) :
    s = ![3, 3, 3] ∨ s = ![3, 3, 4] ∨ s = ![4, 3, 3] ∨
    s = ![3, 4, 3] ∨ s = ![3, 3, 5] ∨ s = ![5, 3, 3] := by
  obtain t | t | t | t | t := admissible_three (isAdmissibleSymbol_comp_castSucc hs) <;>
  obtain u | u | u | u | u := admissible_three (isAdmissibleSymbol_comp_succ hs) <;>
  simp_all [funext_iff, forall_fin_succ]
  all_goals
    have := hs.1.det_pos
    simp_rw [det_toCosineMatrix_length_three, t.1, t.2, u, Nat.cast_ofNat] at this
    simp only [sq_sin_pi_div_three, cos_pi_div_three, sq_sin_pi_div_four, cos_pi_div_five,
      sq_sin_pi_div_five] at this
    nlinarith [sqrt_nonneg 5, sq_sqrt (show 0 ≤ 5 by norm_num)]

theorem admissible_five {s : Fin 4 → ℕ} (hs : IsAdmissibleSymbol s) :
    s = ![3, 3, 3, 3] ∨ s = ![3, 3, 3, 4] ∨ s = ![4, 3, 3, 3] := by
  obtain t | t | t | t | t | t := admissible_four (isAdmissibleSymbol_comp_castSucc hs) <;>
  obtain u | u | u | u | u | u := admissible_four (isAdmissibleSymbol_comp_succ hs) <;>
  simp_all [funext_iff, forall_fin_succ]
  all_goals
    have := hs.1.det_pos
    simp_rw [det_toCosineMatrix_length_four, t.1, t.2.1, t.2.2, u, Nat.cast_ofNat] at this
    simp only [sq_sin_pi_div_three, cos_pi_div_three, sq_sin_pi_div_four, sq_cos_pi_div_four,
      sq_sin_pi_div_five] at this
    nlinarith [sqrt_nonneg 5, sq_sqrt (show 0 ≤ 5 by norm_num)]

lemma vecCons_3_lastCases_4_3 : vecCons 3 (lastCases 4 (3 : Fin n → ℕ)) = lastCases 4 3 := by
  ext i
  cases i using cases with
  | zero =>
    rw [cons_val_zero, show (0 : Fin (n + 2)) = castSucc 0 by rfl, lastCases_castSucc,
      Pi.ofNat_apply]
  | succ i =>
    rw [cons_val_succ]
    cases i using lastCases <;> simp [← castSucc_succ]

lemma det_3n_4 : (toCosineMatrix (lastCases 4 (3 : Fin n → ℕ))).det = 2⁻¹ ^ (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [det_toCosineMatrix_length_one, show lastCases 4 (3 : Fin 0 → ℕ) 0 = 4 by rfl]
    simp [-sin_pi_div_four, sq_sin_pi_div_four]
  | one =>
    rw [det_toCosineMatrix_length_two, show lastCases 4 (3 : Fin 1 → ℕ) 0 = 3 by rfl,
      show lastCases 4 (3 : Fin 1 → ℕ) 1 = 4 by rfl, Nat.cast_four, sq_sin_pi_div_four]
    norm_num
  | more n ih₀ ih₁ =>
    have key := det_toCosineMatrix_recursion 3 3 (lastCases 4 (3 : Fin n → ℕ))
    simp_rw [ih₀, vecCons_3_lastCases_4_3, ih₁, Nat.cast_three, cos_pi_div_three, one_div] at key
    rw [key, pow_succ _ n, ← mul_assoc, ← pow_add, show n + 1 + 1 = 2 + n by lia, ← mul_one_sub,
      pow_succ, show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num]

lemma det_4_3n_4 : (toCosineMatrix (cases 4 (lastCases 4 (3 : Fin n → ℕ)))).det = 0 := by
  cases n with
  | zero =>
    simp [det_toCosineMatrix_length_two, show cases 4 (lastCases 4 (3 : Fin 0 → ℕ)) 1 = 4 by rfl]
  | succ n =>
    have key := det_toCosineMatrix_recursion 4 3 (lastCases 4 (3 : Fin n → ℕ))
    simp_rw [vecCons_3_lastCases_4_3, det_3n_4, Nat.cast_four, sq_cos_pi_div_four, one_div,
      ← pow_succ', sub_self] at key
    convert key with i
    cases i using cases <;> simp

theorem admissible_five_plus {s : Fin (n + 4) → ℕ} (hs : IsAdmissibleSymbol s) :
    s = 3 ∨ s = lastCases 4 3 ∨ s = cases 4 3 := by
  induction n with
  | zero =>
    obtain rfl | rfl | rfl := admissible_five hs <;> simp [funext_iff, forall_fin_succ]
    tauto
  | succ n ih =>
    have c₀ := ih (isAdmissibleSymbol_comp_castSucc hs)
    have c₁ := ih (isAdmissibleSymbol_comp_succ hs)
    have n₀ : s ∘ castSucc ≠ lastCases 4 3 := by
      by_contra hc
      replace hc := congr($hc (last _))
      simp_rw [lastCases_last] at hc
      have feq : (last (n + 3)).castSucc = succ ⟨n + 2, by lia⟩ := rfl
      obtain c₁ | c₁ | c₁ := c₁ <;> replace c₁ := congr($c₁ ⟨n + 2, by lia⟩)
      · rw [Pi.ofNat_apply] at c₁
        lia
      · nth_rw 2 [show ⟨n + 2, by lia⟩ = castSucc ⟨n + 2, by lia⟩ by rfl] at c₁
        simp_rw [lastCases_castSucc, Pi.ofNat_apply] at c₁
        lia
      · simp_rw [cases_succ', Pi.ofNat_apply] at c₁
        lia
    simp_rw [n₀, false_or] at c₀
    have n₁ : s ∘ succ ≠ cases 4 3 := by
      by_contra hc
      replace hc := congr($hc 0)
      simp_rw [cases_zero] at hc
      have feq : succ (0 : Fin (n + 4)) = castSucc ⟨1, by lia⟩ := rfl
      obtain c₀ | c₀ := c₀ <;> replace c₀ := congr($c₀ ⟨1, by lia⟩)
      · rw [Pi.ofNat_apply] at c₀
        lia
      · nth_rw 2 [show ⟨1, by lia⟩ = succ 0 by rfl] at c₀
        simp_rw [cases_succ, Pi.ofNat_apply] at c₀
        lia
    simp_rw [n₁, or_false] at c₁
    obtain c₀ | c₀ := c₀
    · obtain c₁ | c₁ := c₁
      · left; ext i
        cases i using cases with
        | zero => exact congr($c₀ 0)
        | succ i => exact congr($c₁ i)
      · right; left; ext i
        cases i using lastCases with
        | last => simpa using congr($c₁ (last _))
        | cast i => simpa using congr($c₀ i)
    · obtain c₁ | c₁ := c₁
      · right; right; ext i
        cases i using cases with
        | zero => exact congr($c₀ 0)
        | succ i => exact congr($c₁ i)
      · suffices s = cases 4 (lastCases 4 3) by
          have det := this ▸ hs.1.det_pos
          simp [det_4_3n_4] at det
        ext i
        cases i using cases with
        | zero => exact congr($c₀ 0)
        | succ i => exact congr($c₁ i)

lemma image_regularSimilar_eq_singleton (P : regularPolytopes (n + 1)) : ∃ s,
    IsAdmissibleSymbol s ∧ (fun Q ↦ Q.2.schlafli) '' {Q | regularSimilar (n + 1) P Q} = {s} := by
  obtain ⟨P, rP⟩ := P
  refine ⟨rP.schlafli, isAdmissibleSymbol_schlafli rP, ?_⟩
  ext s
  simp only [regularSimilar, Set.mem_image, Set.mem_ofPred, Subtype.exists, exists_and_left]
  constructor <;> intro h
  · obtain ⟨Q, hs, rQ, rfl⟩ := h
    exact ((schlafli_eq_iff_similar rP rQ).mpr hs).symm
  · exact ⟨P, similar_refl, rP, h.symm⟩

lemma schlafli_injOn_platonicCount_set :
    {S | ∃ P, S = {Q | regularSimilar (n + 1) P Q}}.InjOn ((fun Q ↦ Q.2.schlafli) '' ·) := by
  rintro - ⟨⟨P₁, rP₁ : P₁.IsRegular⟩, rfl⟩ - ⟨⟨P₂, rP₂ : P₂.IsRegular⟩, rfl⟩ e
  obtain ⟨s₁, as₁, hs₁⟩ := image_regularSimilar_eq_singleton ⟨P₁, rP₁⟩
  obtain ⟨s₂, as₂, hs₂⟩ := image_regularSimilar_eq_singleton ⟨P₂, rP₂⟩
  simp_rw [hs₁, hs₂, Set.singleton_eq_singleton_iff] at e
  ext ⟨P, rP : P.IsRegular⟩
  simp_rw [regularSimilar, Set.mem_ofPred, ← schlafli_eq_iff_similar rP₁ rP,
    ← schlafli_eq_iff_similar rP₂ rP]
  have m₁ : ⟨P₁, rP₁⟩ ∈ {Q | regularSimilar (n + 1) ⟨P₁, rP₁⟩ Q} := similar_refl
  have m₂ : ⟨P₂, rP₂⟩ ∈ {Q | regularSimilar (n + 1) ⟨P₂, rP₂⟩ Q} := similar_refl
  replace m₁ : rP₁.schlafli ∈ {s₁} := hs₁ ▸ Set.mem_image_of_mem _ m₁
  replace m₂ : rP₂.schlafli ∈ {s₂} := hs₂ ▸ Set.mem_image_of_mem _ m₂
  rw [Set.mem_singleton_iff] at m₁ m₂
  rw [m₁, m₂, e]

end LeanEval.Geometry.PlatonicClassification.ConvexPolytope

open LeanEval.Geometry.PlatonicClassification ConvexPolytope

theorem platonicCount_three_le : platonicCount 3 ≤ 5 := by
  let syms : Set (Set (Fin 2 → ℕ)) := {{![3, 3]}, {![3, 4]}, {![4, 3]}, {![3, 5]}, {![5, 3]}}
  have cs : syms.encard ≤ 5 := by
    change _ ≤ (1 + 1 + 1 + 1 + 1 : ℕ∞)
    iterate 4 refine (Set.encard_insert_le _ _).trans (add_le_add_left ?_ _)
    simp
  refine (Set.encard_le_encard_of_injOn ?_ schlafli_injOn_platonicCount_set).trans cs
  rintro - ⟨P, rfl⟩
  obtain ⟨s, as, hs⟩ := image_regularSimilar_eq_singleton P
  simp_rw [hs, syms, Set.mem_insert_iff, Set.mem_singleton_iff, Set.singleton_eq_singleton_iff]
  exact admissible_three as

theorem platonicCount_four_le : platonicCount 4 ≤ 6 := by
  let syms : Set (Set (Fin 3 → ℕ)) :=
    {{![3, 3, 3]}, {![3, 3, 4]}, {![4, 3, 3]}, {![3, 4, 3]}, {![3, 3, 5]}, {![5, 3, 3]}}
  have cs : syms.encard ≤ 6 := by
    change _ ≤ (1 + 1 + 1 + 1 + 1 + 1 : ℕ∞)
    iterate 5 refine (Set.encard_insert_le _ _).trans (add_le_add_left ?_ _)
    simp
  refine (Set.encard_le_encard_of_injOn ?_ schlafli_injOn_platonicCount_set).trans cs
  rintro - ⟨P, rfl⟩
  obtain ⟨s, as, hs⟩ := image_regularSimilar_eq_singleton P
  simp_rw [hs, syms, Set.mem_insert_iff, Set.mem_singleton_iff, Set.singleton_eq_singleton_iff]
  exact admissible_four as

theorem platonicCount_five_plus_le {n : ℕ} (hn : 5 ≤ n) : platonicCount n ≤ 3 := by
  rw [le_iff_exists_add'] at hn
  obtain ⟨n, rfl⟩ := hn
  let syms : Set (Set (Fin (n + 4) → ℕ)) := {{3}, {lastCases 4 3}, {cases 4 3}}
  have cs : syms.encard ≤ 3 := by
    change _ ≤ (1 + 1 + 1 : ℕ∞)
    iterate 2 refine (Set.encard_insert_le _ _).trans (add_le_add_left ?_ _)
    simp
  refine (Set.encard_le_encard_of_injOn ?_ schlafli_injOn_platonicCount_set).trans cs
  rintro - ⟨P, rfl⟩
  obtain ⟨s, as, hs⟩ := image_regularSimilar_eq_singleton P
  simp_rw [hs, syms, Set.mem_insert_iff, Set.mem_singleton_iff, Set.singleton_eq_singleton_iff]
  exact admissible_five_plus as
