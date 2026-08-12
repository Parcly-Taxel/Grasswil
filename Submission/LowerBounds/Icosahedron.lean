import Submission.Face.Basic
import Submission.LowerBounds.Lemmas
import Submission.Symmetry
import Submission.ToMathlib.Exposed
import Submission.ToMathlib.Misc

open Real Finset LeanEval.Geometry.PlatonicClassification ConvexPolytope
open scoped goldenRatio

variable {i : Fin 3} {s t u : Bool}

variable (i s t) in
/-- A function mapping `Fin 3 × Bool × Bool` to a vertex of the regular icosahedron. -/
noncomputable def icosaVert : E 3 :=
  .toLp _ fun j ↦ ![0, if s then -1 else 1, if t then -φ else φ] (j + i)

lemma icosaVert_mem_sphere : dist 0 (icosaVert i s t) = √(1 + φ ^ 2) := by
  rw [← sq_eq_sq₀ dist_nonneg (by positivity), EuclideanSpace.dist_sq_eq, sq_sqrt (by positivity)]
  simp_rw [icosaVert, PiLp.zero_apply, dist_zero, norm_eq_abs, sq_abs]
  change ∑ j, ![_, _, _] (finCycle i j) ^ 2 = _
  rw [Equiv.sum_comp _ fun j ↦ ![_, _, _] j ^ 2]
  simp [Fin.sum_univ_three]

lemma injective_icosaVert : (fun w : _ × _ × _ ↦ icosaVert w.1 w.2.1 w.2.2).Injective := by
  rintro ⟨vi, vs, vt⟩ ⟨wi, ws, wt⟩ e
  simp_rw [icosaVert, WithLp.toLp.injEq] at e
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

/-- The regular icosahedron. -/
noncomputable def icosahedron : ConvexPolytope 3 where
  vertices := univ.image fun w : _ × _ × _ ↦ icosaVert w.1 w.2.1 w.2.2
  vertices_nonempty := by simp
  vertices_eq_extremePoints := by
    refine self_eq_extremePoints_convexHull_of_subset_sphere 0 √(1 + φ ^ 2) fun p mp ↦ ?_
    rw [mem_coe, mem_image] at mp
    obtain ⟨p, -, rfl⟩ := mp
    exact icosaVert_mem_sphere

variable (i s t) in
lemma mem_icosahedron : icosaVert i s t ∈ icosahedron.toSet := by
  apply subset_convexHull
  simp_rw [icosahedron, mem_coe, mem_image]
  exact ⟨(i, s, t), mem_univ _, rfl⟩

lemma isFullDim_icosahedron : icosahedron.IsFullDim := by
  have m1 (i) : .single i 1 ∈ vectorSpan ℝ icosahedron.toSet := by
    convert Submodule.smul_mem _ (2⁻¹ : ℝ) (vsub_mem_vectorSpan ℝ
      (mem_icosahedron (1 - i) false false) (mem_icosahedron (1 - i) true false))
    ext j
    simp_rw [PiLp.single_apply, icosaVert, Bool.false_eq_true, reduceIte, vsub_eq_sub,
      ← WithLp.toLp_sub, PiLp.smul_apply, Pi.sub_apply]
    obtain rfl | h | h : j = i ∨ j + (1 - i) = 0 ∨ j + (1 - i) = 2 := by lia
    · norm_num
    · rw [if_neg (by lia), h]; simp
    · rw [if_neg (by lia), h]; simp
  have key : vectorSpan ℝ icosahedron.toSet = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun x ↦ ?_
    convert Submodule.sum_mem (t := univ) _ fun i _ ↦ Submodule.smul_mem _ (x i) (m1 i)
    ext i
    rw [WithLp.ofLp_sum, Finset.sum_apply, sum_eq_single i (by simp_all) (by simp),
      PiLp.smul_apply, PiLp.single_eq_same, smul_eq_mul, mul_one]
  rw [IsFullDim, dim, key, finrank_top, finrank_euclideanSpace_fin]

variable (i) in
lemma single_mem_icosahedron_toSet (x : ℝ) (mx : x ∈ Set.Icc (-φ) φ) :
    .single i x ∈ icosahedron.toSet := by
  have msn : .single i (-φ) ∈ icosahedron.toSet := by
    convert! (convex_convexHull ..).midpoint_mem
      (mem_icosahedron (2 - i) false true) (mem_icosahedron (2 - i) true true)
    ext j
    simp_rw [icosaVert, Bool.false_eq_true, reduceIte, midpoint_eq_smul_add, invOf_eq_inv,
      PiLp.single_apply, PiLp.smul_apply, PiLp.add_apply]
    obtain rfl | hn := eq_or_ne j i
    · simp_rw [add_sub_cancel, Matrix.cons_val, ite_true]
      ring
    obtain h | h : j + (2 - i) = 0 ∨ j + (2 - i) = 1 := by lia
    all_goals simp [hn, h]
  have msp : .single i φ ∈ icosahedron.toSet := by
    convert! (convex_convexHull ..).midpoint_mem
      (mem_icosahedron (2 - i) false false) (mem_icosahedron (2 - i) true false)
    ext j
    simp_rw [icosaVert, Bool.false_eq_true, reduceIte, midpoint_eq_smul_add, invOf_eq_inv,
      PiLp.single_apply, PiLp.smul_apply, PiLp.add_apply]
    obtain rfl | hn := eq_or_ne j i
    · simp_rw [add_sub_cancel, Matrix.cons_val, ite_true]
      ring
    obtain h | h : j + (2 - i) = 0 ∨ j + (2 - i) = 1 := by lia
    all_goals simp [hn, h]
  apply (convex_convexHull ..).segment_subset msn msp
  rw [Convex.mem_Icc (by simp [goldenRatio_pos.le])] at mx
  obtain ⟨a, b, la, lb, sab, cab⟩ := mx
  refine ⟨a, b, la, lb, sab, ?_⟩
  simp_rw [EuclideanSpace.smul_single, ← PiLp.single_add, cab]

lemma strongDual_eq_zero_of_icosahedron_nonpos
    {L : StrongDual ℝ (E 3)} (LI : ∀ v ∈ icosahedron.toSet, L v ≤ 0) : L = 0 := by
  have Ls (j) : L (.single j 1) = 0 := by
    have Ln :=
      LI _ (single_mem_icosahedron_toSet j (-1) (by constructor <;> linarith [one_lt_goldenRatio]))
    have Lp :=
      LI _ (single_mem_icosahedron_toSet j 1 (by constructor <;> linarith [one_lt_goldenRatio]))
    rw [← neg_one_mul, ← EuclideanSpace.smul_single, map_smul, neg_one_smul, neg_nonpos] at Ln
    exact le_antisymm Lp Ln
  replace Ls (j x) : L (.single j x) = 0 := by
    rw [← mul_one x, ← EuclideanSpace.smul_single, map_smul, Ls, smul_zero]
  ext p
  rw [zero_apply, p.sum_single, map_sum]
  simp_rw [Ls, sum_const_zero]

lemma exists_icosahedron_params_single {p : E 3} (mp : p ∈ icosahedron.vertices) :
    ∃ v : Fin 3 × Bool × Bool, p = icosaVert v.1 v.2.1 v.2.2 := by
  simpa [icosahedron, eq_comm] using mp

lemma exists_icosahedron_params {g : Finset (E 3)} (sg : g ⊆ icosahedron.vertices) :
    ∃ s : Finset (Fin 3 × Bool × Bool), g = s.map ⟨_, injective_icosaVert⟩ := by
  refine ⟨g.attach.image fun v ↦ (exists_icosahedron_params_single (sg v.2)).choose, ?_⟩
  ext v
  simp_rw [mem_map, mem_image, mem_attach, Function.Embedding.coeFn_mk, Subtype.exists, existsAndEq,
    true_and]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ⟨v, h, ((exists_icosahedron_params_single (sg h)).choose_spec).symm⟩
  · obtain ⟨p, hp, rfl⟩ := h
    rwa [(exists_icosahedron_params_single (sg hp)).choose_spec] at hp

variable {f : Set (E 3)} (hf : icosahedron.IsFace f) (df : faceDim f < 3)
  {v w : Fin 3 × Bool × Bool}

include hf df in
lemma no_antipodes_of_isFace_icosahedron : icosaVert i s t ∉ f ∨ icosaVert i (!s) (!t) ∉ f := by
  contrapose! df
  obtain ⟨mf₁, mf₂⟩ := df
  obtain ⟨L, c, LI, rfl⟩ := hf.1.exists_dual_eq ⟨_, mf₁⟩
  suffices c = 0 by
    subst this
    simp_rw [strongDual_eq_zero_of_icosahedron_nonpos LI, zero_apply, and_true]
    exact isFullDim_icosahedron.ge
  nth_rw 1 [← mul_eq_zero_iff_left two_ne_zero, two_mul, ← mf₁.2, ← mf₂.2, ← map_add, ← map_zero L]
  congr; ext j; unfold icosaVert
  obtain h | h | h : j + i = 0 ∨ j + i = 1 ∨ j + i = 2 := by lia
  · simp [h]
  · cases s <;> simp [h]
  · cases t <;> simp [h]

include hf df in
lemma no_metapodes_of_isFace_icosahedron_aa : icosaVert i s t ∉ f ∨ icosaVert i s (!t) ∉ f := by
  contrapose! df
  obtain ⟨mf₁, mf₂⟩ := df
  obtain ⟨L, c, LI, rfl⟩ := hf.1.exists_dual_eq ⟨_, mf₁⟩
  suffices c = 0 by
    subst this
    simp_rw [strongDual_eq_zero_of_icosahedron_nonpos LI, zero_apply, and_true]
    exact isFullDim_icosahedron.ge
  have Lmid : L (.single (1 - i) (if s then -1 else 1)) = c := by
    nth_rw 1 [← mul_right_inj' two_ne_zero, two_mul c, ← mf₁.2, ← mf₂.2, ← map_add, ← smul_eq_mul,
      ← map_smul]
    congr 1; ext j
    simp_rw [PiLp.smul_apply, PiLp.single_apply, icosaVert, PiLp.add_apply, eq_sub_iff_add_eq]
    obtain h | h | h : j + i = 0 ∨ j + i = 1 ∨ j + i = 2 := by lia
    · simp [h]
    · cases s <;> norm_num [h]
    · cases t <;> simp [h]
  have Ln := LI _ (single_mem_icosahedron_toSet (1 - i) (-φ) (by simp [goldenRatio_pos.le]))
  have Lp := LI _ (single_mem_icosahedron_toSet (1 - i) φ (by simp [goldenRatio_pos.le]))
  split_ifs at Lmid
  · rw [← mul_right_inj' goldenRatio_ne_zero, ← smul_eq_mul, ← map_smul, EuclideanSpace.smul_single,
      mul_neg_one] at Lmid
    rw [Lmid] at Ln
    rw [← neg_inj, ← map_neg, ← PiLp.single_neg, neg_neg] at Lmid
    nlinarith [one_lt_goldenRatio]
  · rw [← mul_right_inj' goldenRatio_ne_zero, ← smul_eq_mul, ← map_smul, EuclideanSpace.smul_single,
      mul_one] at Lmid
    rw [Lmid] at Lp
    rw [← neg_inj, ← map_neg, ← PiLp.single_neg] at Lmid
    nlinarith [one_lt_goldenRatio]

include hf df in
lemma no_metapodes_of_isFace_icosahedron : icosaVert i u s ∉ f ∨ icosaVert (i + 1) t (!u) ∉ f := by
  contrapose! df
  obtain ⟨mf₁, mf₂⟩ := df
  obtain ⟨L, c, LI, rfl⟩ := hf.1.exists_dual_eq ⟨_, mf₁⟩
  suffices c = 0 by
    subst this
    simp_rw [strongDual_eq_zero_of_icosahedron_nonpos LI, zero_apply, and_true]
    exact isFullDim_icosahedron.ge
  let v := (2⁻¹ : ℝ) • (icosaVert i u s + icosaVert (i + 1) t (!u))
  have Lmid : L v = c := by
    nth_rw 1 [← mul_right_inj' two_ne_zero, two_mul c, ← mf₁.2, ← mf₂.2, ← map_add, ← smul_eq_mul]
    simp_rw [← map_smul, v, smul_smul]
    rw [mul_inv_cancel₀ two_ne_zero, one_smul]
  suffices -φ • v ∈ icosahedron.toSet ∧ φ • v ∈ icosahedron.toSet by
    have Ln := LI _ this.1
    have Lp := LI _ this.2
    rw [map_smul, smul_eq_mul] at Ln Lp
    nlinarith [one_lt_goldenRatio]
  constructor
  on_goal 1 =>
    convert! (convex_convexHull ..).midpoint_mem
      (mem_icosahedron i u (!s)) (mem_icosahedron (i + 2) (!s) (!t)) using 1
  on_goal 2 =>
    convert! (convex_convexHull ..).midpoint_mem
      (mem_icosahedron i (!u) s) (mem_icosahedron (i + 2) s t) using 1
  all_goals
    ext j
    simp_rw [v, icosaVert, midpoint_eq_smul_add, invOf_eq_inv, PiLp.smul_apply, PiLp.add_apply]
    rw [← add_assoc, ← add_assoc, smul_comm]
    congr 1
    obtain h | h | h : j + i = 0 ∨ j + i = 1 ∨ j + i = 2 := by lia
    · cases t <;> simp [h]
    · cases u <;> simp [h, ← sq, mul_add]
    · cases s <;> simp [h, ← sq, add_comm]

variable (v w) in
/-- A predicate for adjacency in the icosahedron. -/
def icosaAdj : Prop :=
  v.1 = w.1 ∧ v.2.1 = !w.2.1 ∧ v.2.2 = w.2.2 ∨
  v.1 + 1 = w.1 ∧ v.2.1 = w.2.2 ∨ w.1 + 1 = v.1 ∧ w.2.1 = v.2.2

include hf df in
theorem icosaAdj_of_mem_face_of_ne (mv : icosaVert v.1 v.2.1 v.2.2 ∈ f)
    (mw : icosaVert w.1 w.2.1 w.2.2 ∈ f) (hn : v ≠ w) : icosaAdj v w := by
  obtain ⟨vi, vs, vt⟩ := v
  obtain ⟨wi, ws, wt⟩ := w
  simp_rw [Ne, Prod.mk_inj, not_and_or] at hn
  obtain e₁ | e₁ | e₁ : vi = wi ∨ vi + 1 = wi ∨ wi + 1 = vi := by lia
  · refine .inl ⟨e₁, ?_⟩
    simp_rw [← e₁, Bool.eq_not_iff] at mv mw ⊢
    have teq : vt = wt := by
      contrapose! mw
      rw [← Bool.not_eq_iff] at mw
      rw [← mw]
      obtain rfl | rfl := ws.eq_or_eq_not vs
      · exact (no_metapodes_of_isFace_icosahedron_aa hf df).resolve_left (by simpa)
      · exact (no_antipodes_of_isFace_icosahedron hf df).resolve_left (by simpa)
    tauto
  · refine .inr (.inl ⟨e₁, ?_⟩)
    simp_rw [← e₁] at mv mw ⊢
    contrapose! mw
    rw [← Bool.not_eq_iff] at mw
    rw [← mw]
    exact (no_metapodes_of_isFace_icosahedron hf df).resolve_left (by simpa)
  · refine .inr (.inr ⟨e₁, ?_⟩)
    simp_rw [← e₁] at mv mw ⊢
    contrapose! mw
    rw [← Bool.not_eq_iff] at mw
    rw [← mw] at mv
    exact (no_metapodes_of_isFace_icosahedron hf df).resolve_right (by simpa)

include hf df in
lemma icosahedron_small_faces : #(faceGens hf.1) ≤ 3 := by
  by_contra! cs
  obtain ⟨s, hs⟩ := exists_icosahedron_params (faceGens_subset_vertices hf.1)
  nth_rw 1 [hs, card_map, ← card_fin 3] at cs
  obtain ⟨a, ma, b, mb, n₁, _⟩ := exists_ne_map_eq_of_card_lt_of_maps_to (f := (·.1)) cs (by simp)
  replace cs : 1 < #((s.erase a).erase b) := by grind [card_fin]
  rw [one_lt_card] at cs
  obtain ⟨p, mp, q, mq, n₂⟩ := cs
  simp_rw [mem_erase] at mp mq
  have sg : (faceGens hf.1 : Set _) ⊆ f := fun x mx ↦ by
    rw [convexHull_faceGens hf.1]
    exact subset_convexHull _ _ mx
  have mva : icosaVert a.1 a.2.1 a.2.2 ∈ f := sg (hs ▸ mem_map_of_mem _ ma)
  have mvb : icosaVert b.1 b.2.1 b.2.2 ∈ f := sg (hs ▸ mem_map_of_mem _ mb)
  have mvp : icosaVert p.1 p.2.1 p.2.2 ∈ f := sg (hs ▸ mem_map_of_mem _ mp.2.2)
  have mvq : icosaVert q.1 q.2.1 q.2.2 ∈ f := sg (hs ▸ mem_map_of_mem _ mq.2.2)
  have Aab := icosaAdj_of_mem_face_of_ne hf df mva mvb n₁
  have Apa := icosaAdj_of_mem_face_of_ne hf df mvp mva mp.2.1
  have Apb := icosaAdj_of_mem_face_of_ne hf df mvp mvb mp.1
  have Aqa := icosaAdj_of_mem_face_of_ne hf df mvq mva mq.2.1
  have Aqb := icosaAdj_of_mem_face_of_ne hf df mvq mvb mq.1
  have Apq := icosaAdj_of_mem_face_of_ne hf df mvp mvq n₂
  grind [icosaAdj]

theorem icosahedron_flag_characterisation (F : icosahedron.Flag) :
    ∃ g : Fin 3 → Fin 3 × Bool × Bool, (Pairwise fun i j ↦ icosaAdj (g i) (g j)) ∧
    ∀ i, F.face i = convexHull ℝ ((Iic i).image fun j ↦ icosaVert (g j).1 (g j).2.1 (g j).2.2) := by
  obtain ⟨p, sp, hp⟩ := simplicial_flag_of_small_faces F fun i ↦
    icosahedron_small_faces (F.isFace i) ((F.dim_eq i).trans_lt i.2)
  have ex (i) := exists_icosahedron_params_single <| sp <| mem_map_of_mem _ <| mem_univ i
  refine ⟨fun i ↦ (ex i).choose, fun i j hn ↦ ?_, fun i ↦ ?_⟩
  · apply icosaAdj_of_mem_face_of_ne (F.isFace 2) ((F.dim_eq 2).trans_lt (by lia))
    · rw [← (ex _).choose_spec, hp]
      exact subset_convexHull ℝ _ (mem_map_of_mem _ (by rw [mem_Iic]; lia))
    · rw [← (ex _).choose_spec, hp]
      exact subset_convexHull ℝ _ (mem_map_of_mem _ (by rw [mem_Iic]; lia))
    · contrapose! hn
      replace hn := congr(icosaVert $hn.1 $hn.2.1 $hn.2.2)
      simp_rw [← (ex _).choose_spec] at hn
      exact p.injective hn
  · rw [hp, map_eq_image]
    congr! with j
    exact (ex j).choose_spec

/-! ### Symmetries of the icosahedron -/

lemma icosaAdj_iff_dist_eq_two :
    icosaAdj v w ↔ dist (icosaVert v.1 v.2.1 v.2.2) (icosaVert w.1 w.2.1 w.2.2) = 2 := by
  obtain ⟨i, s, t⟩ := v
  obtain ⟨j, a, b⟩ := w
  conv_rhs => rw [← sq_eq_sq₀ dist_nonneg zero_le_two, show (2 : ℝ) ^ 2 = 4 by norm_num]
  simp_rw [icosaAdj, EuclideanSpace.dist_sq_eq, icosaVert, dist_eq, sq_abs]
  obtain rfl | rfl | rfl : i = j ∨ i + 1 = j ∨ j + 1 = i := by lia
  · simp_rw [true_and, add_eq_left, one_ne_zero, false_and, or_false]
    change _ ↔ ∑ j, (![_, _, _] (finCycle i j) - ![_, _, _] (finCycle i j)) ^ 2 = 4
    rw [Equiv.sum_comp _ fun j ↦ (![_, _, _] j - ![_, _, _] j) ^ 2, Fin.sum_univ_three]
    simp_rw [Matrix.cons_val, sub_self, zero_pow two_ne_zero, zero_add]
    have e₁ : ((if s then -1 else 1 : ℝ) - if a then -1 else 1) ^ 2 = if s = !a then 4 else 0 := by
      cases s <;> cases a <;> norm_num
    have e₂ : ((if t then -φ else φ) - if b then -φ else φ) ^ 2 =
        if t = b then 0 else 4 * φ ^ 2 := by
      cases t <;> cases b <;> simp only [Bool.false_eq_true, Bool.true_eq_false, reduceIte] <;> ring
    rw [e₁, e₂]
    by_cases htb : t = b
    · simp [htb, -Bool.not_eq_not]
    · simp_rw [htb, and_false, false_iff, ite_false]
      suffices 1 < φ ^ 2 by nlinarith
      rw [one_lt_sq_iff₀ (by positivity)]
      exact one_lt_goldenRatio
  · simp_rw [left_eq_add, one_ne_zero, show i + 1 + 1 ≠ i by lia, false_and, true_and, false_or,
      or_false, ← add_assoc]
    change _ ↔ ∑ j, (![_, _, _] (finCycle i j) - ![_, _, _] (finCycle i j + 1)) ^ 2 = 4
    rw [Equiv.sum_comp _ fun j ↦ (![_, _, _] j - ![_, _, _] (j + 1)) ^ 2, Fin.sum_univ_three]
    simp_rw [Fin.reduceAdd, Matrix.cons_val, zero_sub, sub_zero, neg_sq, ite_pow, neg_sq, ite_self]
    cases s <;> cases b <;> grind
  · simp_rw [add_eq_left, one_ne_zero, show j + 1 + 1 ≠ j by lia, false_and, false_or, true_and,
      ← add_assoc]
    change _ ↔ ∑ i, (![_, _, _] (finCycle j i + 1) - ![_, _, _] (finCycle j i)) ^ 2 = 4
    rw [Equiv.sum_comp _ fun i ↦ (![_, _, _] (i + 1) - ![_, _, _] i) ^ 2, Fin.sum_univ_three]
    simp_rw [Fin.reduceAdd, Matrix.cons_val, zero_sub, sub_zero, neg_sq, ite_pow, neg_sq, ite_self]
    cases t <;> cases a <;> grind

lemma icosaAdj_transfer_isom {T : Isom 3} (sT : icosahedron.isSymmetry T)
    (Tv : T (icosaVert v.1 v.2.1 v.2.2) = icosaVert i s t) (adj : icosaAdj v w) :
    ∃ y, T (icosaVert w.1 w.2.1 w.2.2) = icosaVert y.1 y.2.1 y.2.2 ∧ icosaAdj (i, s, t) y := by
  have my : icosaVert w.1 w.2.1 w.2.2 ∈ icosahedron.vertices := by simp [icosahedron]
  rw [← sT.inv.image_vertices, mem_image] at my
  obtain ⟨y, my, Tw⟩ := my
  rw [← T.map_eq_iff, T.coe_inv, T.apply_symm_apply] at Tw
  obtain ⟨y, rfl⟩ := exists_icosahedron_params_single my
  refine ⟨y, Tw.symm, ?_⟩
  rwa [icosaAdj_iff_dist_eq_two, ← Tv, Tw, T.isometry.dist_eq, ← icosaAdj_iff_dist_eq_two]

lemma coordPerm_icosaVert {k : Fin 3} :
    (toIsom (coordPerm (finCycle k)) 0) (icosaVert i s t) = icosaVert (k + i) s t := by
  ext j
  simp_rw [toIsom_apply, WithLp.ofLp_zero, add_zero, coordPerm, icosaVert, Matrix.permMatrix_mulVec,
    Function.comp_apply, finCycle_apply, add_assoc]

lemma isSymmetry_icosahedron_coordPerm {k : Fin 3} :
    icosahedron.isSymmetry (toIsom (coordPerm (finCycle k)) 0) := by
  set R := toIsom (coordPerm (finCycle k)) 0
  let vs := icosahedron.vertices
  have im : R '' vs = vs := by
    apply Set.eq_of_subset_of_card_le
    · rw [Set.image_subset_iff]
      intro v hv
      simp only [vs, icosahedron, mem_coe, mem_image, Set.mem_preimage] at *
      obtain ⟨j, -, rfl⟩ := hv
      exact ⟨(k + j.1, j.2.1, j.2.2), mem_univ _, coordPerm_icosaVert.symm⟩
    · rw [Set.card_image_of_injective _ R.injective]
  have ch := isom_image_convexHull R vs
  rwa [im] at ch

lemma coordFlip_icosaVert {m : Fin 3 → Bool} :
    (toIsom (coordFlip m) 0) (icosaVert i s t) = icosaVert i (m (1 - i) ^^ s) (m (2 - i) ^^ t) := by
  ext j
  simp_rw [toIsom_apply, WithLp.ofLp_zero, add_zero, coordFlip, icosaVert, Matrix.mulVec_diagonal]
  obtain h | h | h : j + i = 0 ∨ j + i = 1 ∨ j + i = 2 := by lia
  · simp [h]
  · have e : j = 1 - i := by lia
    subst j
    cases m (1 - i) <;> cases s <;> simp
  · have e : j = 2 - i := by lia
    subst j
    cases m (2 - i) <;> cases t <;> simp

lemma isSymmetry_icosahedron_coordFlip {m : Fin 3 → Bool} :
    icosahedron.isSymmetry (toIsom (coordFlip m) 0) := by
  set R := toIsom (coordFlip m) 0
  let vs := icosahedron.vertices
  have im : R '' vs = vs := by
    apply Set.eq_of_subset_of_card_le
    · rw [Set.image_subset_iff]
      intro v hv
      simp only [vs, icosahedron, mem_coe, mem_image, Set.mem_preimage] at *
      obtain ⟨j, -, rfl⟩ := hv
      exact ⟨(j.1, m (1 - j.1) ^^ j.2.1, (m (2 - j.1) ^^ j.2.2)),
        mem_univ _, coordFlip_icosaVert.symm⟩
    · rw [Set.card_image_of_injective _ R.injective]
  have ch := isom_image_convexHull R vs
  rwa [im] at ch

section I5

open Matrix

/-- The rotation by 2π/5 about `icosaVert 0 false false`. -/
noncomputable def icosa5 : orthogonalGroup (Fin 3) ℝ where
  val := (2⁻¹ : ℝ) • !![-ψ, -φ, 1; φ, 1, -ψ; -1, -ψ, φ]
  property := by
    rw [mem_orthogonalGroup_iff, transpose_smul, smul_mul_smul_comm, transpose_fin_three]
    simp_rw [mul_fin_three, one_fin_three, smul_of, smul_cons, Matrix.smul_empty, smul_eq_mul]
    grind

/-- Common tactic sequence for proving that `icosa5` is a symmetry. -/
macro "prove_icosa5" : tactic => `(tactic|(
  ext j
  simp only [toIsom_apply, WithLp.ofLp_zero, add_zero, icosa5, smul_mulVec, Pi.smul_apply,
    icosaVert, mulVec_fin_three, of_apply, reduceIte]
  fin_cases j
  all_goals simp only [Fin.reduceFinMk, Fin.reduceAdd, Matrix.cons_val, smul_eq_mul]; grind))

-- 0FF, 0TT are fixed

lemma icosa5_icosaVert_0FF :
    (toIsom icosa5 0) (icosaVert 0 false false) = icosaVert 0 false false := by prove_icosa5

lemma icosa5_icosaVert_0TT :
    (toIsom icosa5 0) (icosaVert 0 true true) = icosaVert 0 true true := by prove_icosa5

-- 0TF → 2FF → 1FF → 1TF → 2FT → (0TF)

lemma icosa5_icosaVert_0TF :
    (toIsom icosa5 0) (icosaVert 0 true false) = icosaVert 2 false false := by prove_icosa5

lemma icosa5_icosaVert_2FF :
    (toIsom icosa5 0) (icosaVert 2 false false) = icosaVert 1 false false := by prove_icosa5

lemma icosa5_icosaVert_1FF :
    (toIsom icosa5 0) (icosaVert 1 false false) = icosaVert 1 true false := by prove_icosa5

lemma icosa5_icosaVert_1TF :
    (toIsom icosa5 0) (icosaVert 1 true false) = icosaVert 2 false true := by prove_icosa5

lemma icosa5_icosaVert_2FT :
    (toIsom icosa5 0) (icosaVert 2 false true) = icosaVert 0 true false := by prove_icosa5

-- 0FT → 2TT → 1TT → 1FT → 2TF → (0FT)

lemma icosa5_icosaVert_0FT :
    (toIsom icosa5 0) (icosaVert 0 false true) = icosaVert 2 true true := by prove_icosa5

lemma icosa5_icosaVert_2TT :
    (toIsom icosa5 0) (icosaVert 2 true true) = icosaVert 1 true true := by prove_icosa5

lemma icosa5_icosaVert_1TT :
    (toIsom icosa5 0) (icosaVert 1 true true) = icosaVert 1 false true := by prove_icosa5

lemma icosa5_icosaVert_1FT :
    (toIsom icosa5 0) (icosaVert 1 false true) = icosaVert 2 true false := by prove_icosa5

lemma icosa5_icosaVert_2TF :
    (toIsom icosa5 0) (icosaVert 2 true false) = icosaVert 0 false true := by prove_icosa5

lemma icosa5_icosaVert : (toIsom icosa5 0) (icosaVert i s t) =
    icosaVert (if s = t then ![0, 1, 1] i else ![2, 2, 0] i)
      (if i = 1 then !s else t) (if i = 0 then t else s) := by
  cases s <;> cases t <;> fin_cases i <;>
  simp only [Bool.true_eq_false, Bool.false_eq_true, Bool.not_false, Bool.not_true, reduceIte,
    Fin.reduceFinMk, Fin.reduceEq, Matrix.cons_val]
  exacts [icosa5_icosaVert_0FF, icosa5_icosaVert_1FF, icosa5_icosaVert_2FF,
          icosa5_icosaVert_0FT, icosa5_icosaVert_1FT, icosa5_icosaVert_2FT,
          icosa5_icosaVert_0TF, icosa5_icosaVert_1TF, icosa5_icosaVert_2TF,
          icosa5_icosaVert_0TT, icosa5_icosaVert_1TT, icosa5_icosaVert_2TT]

lemma isSymmetry_icosahedron_icosa5 : icosahedron.isSymmetry (toIsom icosa5 0) := by
  set R := toIsom icosa5 0
  let vs := icosahedron.vertices
  have im : R '' vs = vs := by
    apply Set.eq_of_subset_of_card_le
    · rw [Set.image_subset_iff]
      intro v hv
      simp only [vs, icosahedron, mem_coe, mem_image, Set.mem_preimage] at *
      obtain ⟨j, -, rfl⟩ := hv
      exact ⟨(if j.2.1 = j.2.2 then ![0, 1, 1] j.1 else ![2, 2, 0] j.1,
          if j.1 = 1 then !j.2.1 else j.2.2, if j.1 = 0 then j.2.2 else j.2.1),
        mem_univ _, icosa5_icosaVert.symm⟩
    · rw [Set.card_image_of_injective _ R.injective]
  have ch := isom_image_convexHull R vs
  rwa [im] at ch

end I5

variable (v) in
lemma icosahedron_vertex_transitive :
    ∃ T, icosahedron.isSymmetry T ∧ T (icosaVert v.1 v.2.1 v.2.2) = icosaVert 0 false false := by
  refine ⟨toIsom (coordFlip ![false, v.2.1, v.2.2]) 0 * toIsom (coordPerm (finCycle (-v.1))) 0,
    isSymmetry_icosahedron_coordFlip.mul isSymmetry_icosahedron_coordPerm, ?_⟩
  rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, coordPerm_icosaVert, coordFlip_icosaVert]
  simp

lemma icosahedron_edge_transitive (adj : icosaAdj v w) :
    ∃ T, icosahedron.isSymmetry T ∧
    T (icosaVert v.1 v.2.1 v.2.2) = icosaVert 0 false false ∧
    T (icosaVert w.1 w.2.1 w.2.2) = icosaVert 0 true false := by
  let R := toIsom icosa5 0
  obtain ⟨T, sT, Tv⟩ := icosahedron_vertex_transitive v
  obtain ⟨y, Tw, ay⟩ := icosaAdj_transfer_isom sT Tv adj
  simp_rw [icosaAdj] at ay
  obtain yi | yi | yi : y.1 = 0 ∨ y.1 = 1 ∨ y.1 = 2 := by lia
  · refine ⟨T, sT, Tv, ?_⟩ -- 0TF
    rw [Tw]
    lia
  · cases ys : y.2.1 with
    | false => -- 1FF
      refine ⟨R⁻¹ * R⁻¹ * T,
        (isSymmetry_icosahedron_icosa5.inv.mul isSymmetry_icosahedron_icosa5.inv).mul sT, ?_, ?_⟩
      · simp_rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, Tv]
        rw [← R.map_eq_iff, ← R.map_eq_iff, R.coe_inv, R.apply_symm_apply, R.apply_symm_apply,
          icosa5_icosaVert_0FF, icosa5_icosaVert_0FF]
      · simp_rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, Tw]
        rw [← R.map_eq_iff, ← R.map_eq_iff, R.coe_inv, R.apply_symm_apply, R.apply_symm_apply,
          icosa5_icosaVert_0TF, icosa5_icosaVert_2FF]
        lia
    | true => -- 1TF
      refine ⟨R * R * T,
        (isSymmetry_icosahedron_icosa5.mul isSymmetry_icosahedron_icosa5).mul sT, ?_, ?_⟩
      · simp_rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, Tv]
        rw [icosa5_icosaVert_0FF, icosa5_icosaVert_0FF]
      · simp_rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, Tw, yi, ys,
          show y.2.2 = false by lia]
        rw [icosa5_icosaVert_1TF, icosa5_icosaVert_2FT]
  · cases ys : y.2.2 with
    | false => -- 2FF
      refine ⟨R⁻¹ * T, isSymmetry_icosahedron_icosa5.inv.mul sT, ?_, ?_⟩
      · simp_rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, Tv]
        rw [← R.map_eq_iff, R.coe_inv, R.apply_symm_apply, icosa5_icosaVert_0FF]
      · simp_rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, Tw]
        rw [← R.map_eq_iff, R.coe_inv, R.apply_symm_apply, icosa5_icosaVert_0TF]
        lia
    | true => -- 2TF
      refine ⟨R * T, isSymmetry_icosahedron_icosa5.mul sT, ?_, ?_⟩
      · simp_rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, Tv]
        rw [icosa5_icosaVert_0FF]
      · simp_rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, Tw, yi, ys,
          show y.2.1 = false by lia]
        rw [icosa5_icosaVert_2FT]

theorem icosahedron_triangle_transitive {g h : Fin 3 → Fin 3 × Bool × Bool}
    (adjg : Pairwise fun i j ↦ icosaAdj (g i) (g j))
    (adjh : Pairwise fun i j ↦ icosaAdj (h i) (h j)) :
    ∃ T, icosahedron.isSymmetry T ∧ ∀ i,
    T (icosaVert (g i).1 (g i).2.1 (g i).2.2) = icosaVert (h i).1 (h i).2.1 (h i).2.2 := by
  obtain ⟨G, sG, G₀, G₁⟩ := icosahedron_edge_transitive (adjg zero_ne_one)
  obtain ⟨H, sH, H₀, H₁⟩ := icosahedron_edge_transitive (adjh zero_ne_one)
  obtain ⟨v, G₂, av₀⟩ := icosaAdj_transfer_isom sG G₀ (adjg (show 0 ≠ 2 by lia))
  obtain ⟨w, G₂', av₁⟩ := icosaAdj_transfer_isom sG G₁ (adjg (show 1 ≠ 2 by lia))
  have e : v = w := by rwa [G₂, injective_icosaVert.eq_iff] at G₂'
  subst e
  obtain ⟨w, H₂, aw₀⟩ := icosaAdj_transfer_isom sH H₀ (adjh (show 0 ≠ 2 by lia))
  obtain ⟨x, H₂', aw₁⟩ := icosaAdj_transfer_isom sH H₁ (adjh (show 1 ≠ 2 by lia))
  have e : w = x := by rwa [H₂, injective_icosaVert.eq_iff] at H₂'
  subst e
  obtain ⟨i, p, a⟩ := v
  obtain ⟨j, q, b⟩ := w
  obtain ⟨rfl, rfl, rfl, rfl⟩ : i = 2 ∧ j = 2 ∧ p = false ∧ q = false := by grind [icosaAdj]
  refine ⟨H⁻¹ * toIsom (coordFlip ![a ^^ b, false, false]) 0 * G,
    (sH.inv.mul isSymmetry_icosahedron_coordFlip).mul sG, fun i ↦ ?_⟩
  simp_rw [AffineIsometryEquiv.coe_mul, Function.comp_apply]
  rw [← H.map_eq_iff, H.coe_inv, H.apply_symm_apply]
  fin_cases i <;> simp only [Fin.reduceFinMk, G₀, G₁, G₂, H₀, H₁, H₂, coordFlip_icosaVert,
    Fin.reduceSub, Matrix.cons_val]
  on_goal 3 => rw [Bool.xor_right_comm]
  all_goals simp

theorem icosahedron_isRegular : icosahedron.IsRegular := by
  refine ⟨isFullDim_icosahedron, fun F G ↦ ?_⟩
  obtain ⟨g, adjg, hF⟩ := icosahedron_flag_characterisation F
  obtain ⟨h, adjh, hG⟩ := icosahedron_flag_characterisation G
  obtain ⟨T, sT, hT⟩ := icosahedron_triangle_transitive adjg adjh
  refine ⟨T, sT, fun i ↦ ?_⟩
  simp_rw [hF, hG, isom_image_convexHull, coe_image, Set.image_image, hT]
