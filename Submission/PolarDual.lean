import Submission.Face.Basic

open Set LeanEval.Geometry.PlatonicClassification ConvexPolytope

variable {n : ℕ}

lemma exists_step_finset (w u : E n) (S : Finset (E n)) (hS : ∀ v ∈ S, inner ℝ v w < 1) :
    ∃ ε > 0, ∀ v ∈ S, inner ℝ v w + ε * inner ℝ v u ≤ 1 := by
  obtain ⟨ε, εpos, hε⟩ : ∃ ε > 0, ∀ v ∈ S, ε * (|inner ℝ v u| + 1) ≤ 1 - inner ℝ v w := by
    obtain rfl | nS := S.eq_empty_or_nonempty
    · exact ⟨1, zero_lt_one, by simp⟩
    · obtain ⟨v₀, hv₀⟩ := S.exists_min_image (fun v ↦ (1 - inner ℝ v w) / (|inner ℝ v u| + 1)) nS
      refine ⟨(1 - inner ℝ v₀ w) / (|inner ℝ v₀ u| + 1), ?_, fun v hv ↦ ?_⟩
      · positivity [sub_pos.mpr (hS v₀ hv₀.1)]
      · rw [← le_div_iff₀ (by positivity)]
        exact hv₀.2 v hv
  exact ⟨ε, εpos, fun v hv ↦ by cases abs_cases (inner ℝ v u) <;> nlinarith [hε v hv]⟩

lemma iInter_eq_iInter_convexHull_le {s : Finset (E n)} :
    ⋂ v ∈ s, {w | inner ℝ v w ≤ 1} = ⋂ v ∈ convexHull ℝ s, {w | inner ℝ v w ≤ 1} := by
  refine subset_antisymm ?_ (biInter_mono (subset_convexHull ..) fun _ _ ↦ subset_rfl)
  simp_rw [subset_def, mem_iInter, mem_ofPred_eq]
  intro u hu v hv
  rw [Finset.mem_convexHull'] at hv
  obtain ⟨w, nnw, sw, rfl⟩ := hv
  simp_rw [sum_inner, inner_smul_left, Real.ringHom_apply, ← sw]
  exact Finset.sum_le_sum fun v mv ↦ by nlinarith [hu v mv, nnw v mv]

lemma iInter_eq_iInter_convexHull_eq {s : Finset (E n)} :
    ⋂ v ∈ s, {w | inner ℝ v w = 1} = ⋂ v ∈ convexHull ℝ s, {w | inner ℝ v w = 1} := by
  refine subset_antisymm ?_ (biInter_mono (subset_convexHull ..) fun _ _ ↦ subset_rfl)
  simp_rw [subset_def, mem_iInter, mem_ofPred_eq]
  intro u hu v hv
  rw [Finset.mem_convexHull'] at hv
  obtain ⟨w, -, sw, rfl⟩ := hv
  simp_all [sum_inner, inner_smul_left]

/-- `Q` is the polar dual of `P` if `Q` equals the intersection of the polars
(relative to the unit sphere) of `P`. -/
def IsPolarDual (P Q : ConvexPolytope n) : Prop :=
  Q.toSet = ⋂ v ∈ P.toSet, {w | inner ℝ v w ≤ 1}

/-- The dual of face `f` in polytope `Q` (understood as the dual of `P`). -/
def faceDual (Q : ConvexPolytope n) (f : Set (E n)) : Set (E n) :=
  Q.toSet ∩ ⋂ v ∈ f, {w | inner ℝ v w = 1}

namespace LeanEval.Geometry.PlatonicClassification.ConvexPolytope

lemma compact (P : ConvexPolytope n) : IsCompact P.toSet :=
  P.vertices.finite_toSet.isCompact_convexHull _

end LeanEval.Geometry.PlatonicClassification.ConvexPolytope

namespace IsPolarDual

variable {P Q : ConvexPolytope n} (h : IsPolarDual P Q) {v : E n}

include h

/-! ### The dual is symmetric -/

lemma mem_iff : v ∈ Q.toSet ↔ ∀ w ∈ P.toSet, inner ℝ w v ≤ 1 := by
  rw [h]; simp

lemma zero_mem : 0 ∈ P.toSet := by
  by_contra contra
  obtain ⟨L, c, Lm, L₀⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull ..) P.compact.isClosed contra
  let d := (InnerProductSpace.toDual ℝ (E n)).symm L
  have Ld (y) : L y = inner ℝ d y := by simp [d]
  have unb {t : ℝ} (ht : 0 ≤ t) : t • d ∈ Q.toSet := by
    refine h.mem_iff.mpr fun v hv ↦ ?_
    simp_all only [inner_zero_right, inner_smul_right, real_inner_comm]
    nlinarith [Lm v hv]
  obtain ⟨R, Rpos, Rub⟩ := Q.compact.isBounded.exists_pos_norm_le
  obtain ⟨t, nnt, Rlb⟩ : ∃ t ≥ 0, R < t * ‖d‖ := by
    by_cases d₀ : d = 0
    · obtain ⟨v, mv⟩ := P.vertices_nonempty
      specialize Lm _ (subset_convexHull ℝ _ mv)
      simp_rw [d₀, inner_zero_left] at Ld
      rw [Ld] at L₀ Lm
      exact absurd L₀ Lm.asymm
    · refine ⟨(R + 1) / ‖d‖, by positivity, ?_⟩
      rw [div_mul_cancel₀ _ (by positivity)]
      linarith
  specialize Rub _ (unb nnt)
  rw [norm_smul_of_nonneg nnt] at Rub
  exact Rlb.not_ge Rub

theorem symm : IsPolarDual Q P := by
  refine subset_antisymm (fun x mx ↦ ?_) fun w mw ↦ ?_
  · unfold IsPolarDual at h
    simp_rw [h, mem_iInter₂, mem_ofPred]
    intro y hy
    rw [real_inner_comm]
    exact hy x mx
  · by_contra contra
    obtain ⟨L, c, Lm, Lw⟩ :=
      geometric_hahn_banach_closed_point (convex_convexHull ..) P.compact.isClosed contra
    have cpos : 0 < c := by simpa using Lm 0 h.zero_mem
    let d := (InnerProductSpace.toDual ℝ (E n)).symm L
    have Ld (y) : inner ℝ d y = L y := by simp [d]
    have mcid : c⁻¹ • d ∈ Q.toSet := by
      refine h.mem_iff.mpr fun v hv ↦ ?_
      rw [real_inner_smul_right, real_inner_comm, Ld, inv_mul_le_one₀ cpos]
      exact (Lm v hv).le
    simp_rw [mem_iInter₂, mem_ofPred] at mw
    specialize mw _ mcid
    rw [inner_smul_left, Real.ringHom_apply, Ld, inv_mul_le_one₀ cpos] at mw
    exact Lw.not_ge mw

/-! ### The dual relates full-dimensional polytopes -/

lemma exists_inner_pos (nv : v ≠ 0) : ∃ y ∈ P.toSet, 0 < inner ℝ v y := by
  by_contra! contra
  have unb {t : ℝ} (ht : 0 ≤ t) : t • v ∈ Q.toSet := by
    refine h.mem_iff.mpr fun w hw ↦ ?_
    rw [inner_smul_right, real_inner_comm]
    nlinarith [contra w hw]
  obtain ⟨R, Rpos, Rub⟩ := Q.compact.isBounded.exists_pos_norm_le
  apply (Rub ((R / ‖v‖ + 1) • v) (unb (by positivity))).not_gt
  rw [← norm_pos_iff] at nv
  rw [norm_smul, Real.norm_of_nonneg (by positivity), add_one_mul, div_mul_cancel₀ _ nv.ne']
  exact lt_add_of_pos_right _ nv

theorem isFullDim : P.IsFullDim := by
  suffices vectorSpan ℝ P.toSet = ⊤ by
    rw [IsFullDim, dim, this, finrank_top, finrank_euclideanSpace_fin]
  rw [← Submodule.orthogonal_eq_bot_iff, ← not_ne_iff, Submodule.ne_bot_iff]
  by_contra contra
  obtain ⟨v, mv, nv⟩ := contra
  have iv (w) (mw : w ∈ vectorSpan ℝ P.toSet) : inner ℝ v w = 0 := by
    simpa only [real_inner_comm] using mv w mw
  obtain ⟨y, my, hy⟩ := h.exists_inner_pos nv
  exact hy.ne' (iv _ (by simpa using vsub_mem_vectorSpan ℝ my h.zero_mem))

variable {f f' : Set (E n)} (hf : P.IsFace f) (df : faceDim f < n)

/-! ### The dual maps faces to faces -/

include hf df in
lemma exists_exposing : ∃ w, ∀ v ∈ P.toSet, inner ℝ v w ≤ 1 ∧ (inner ℝ v w = 1 ↔ v ∈ f) := by
  obtain ⟨z, hz⟩ := hf.2
  obtain ⟨L, rfl⟩ := hf.1 hf.2
  let d := (InnerProductSpace.toDual ℝ (E n)).symm L
  have Ld (y) : L y = inner ℝ d y := by simp [d]
  have pL : 0 < L z := by
    by_cases zd : d = 0
    · simp_rw [Ld, zd, inner_zero_left, le_rfl, implies_true, and_true, ofPred_mem_eq] at df
      exact absurd h.isFullDim df.ne
    · obtain ⟨y, my, ly⟩ := h.exists_inner_pos zd
      rw [← Ld] at ly
      exact ly.trans_le (hz.2 y my)
  refine ⟨(L z)⁻¹ • d, fun v mv ↦ ?_⟩
  simp_rw [mem_ofPred, mv, true_and, inner_smul_right, inv_mul_le_one₀ pL, inv_mul_eq_one₀ pL.ne',
    real_inner_comm d, ← Ld]
  exact ⟨hz.2 v mv, fun e w mw ↦ e ▸ hz.2 w mw, fun maxv ↦ le_antisymm (maxv z hz.1) (hz.2 v mv)⟩

include hf df in
lemma exists_exposed : ∃ w, (∀ v ∈ f, inner ℝ v w = 1) ∧ (∀ v ∈ P.toSet, inner ℝ v w ≤ 1) ∧
    ∀ v ∈ P.toSet, v ∉ f → inner ℝ v w < 1 := by
  obtain ⟨w, hw⟩ := h.exists_exposing hf df
  refine ⟨w, fun v mv ↦ (hw v (hf.1.subset mv)).2.mpr mv, fun v mv ↦ (hw v mv).1, fun v mv nv ↦ ?_⟩
  specialize hw v mv
  exact hw.1.lt_of_ne (hw.2.not.mpr nv)

include hf df in
lemma nonempty_faceDual : (faceDual Q f).Nonempty := by
  obtain ⟨v, hv⟩ := h.exists_exposing hf df
  refine ⟨v, h.mem_iff.mpr fun w mw ↦ (hv w mw).1, ?_⟩
  simp_rw [mem_iInter, mem_ofPred]
  intro w mw
  rwa [(hv w (hf.1.subset mw)).2]

open Finset in
include hf in
lemma isExposed_faceDual : IsExposed ℝ Q.toSet (faceDual Q f) := fun ndual ↦ by
  let g := faceGens hf.1
  have sg : (g : Set (E n)) ⊆ P.toSet := fun x hx ↦
    subset_convexHull _ _ (faceGens_subset_vertices _ hx)
  have fch := convexHull_faceGens hf.1
  refine ⟨∑ v ∈ g, InnerProductSpace.toDual _ _ v, ?_⟩
  ext w
  simp_rw [faceDual, mem_inter_iff, mem_iInter, mem_ofPred_eq, FunLike.coe_sum,
    Finset.sum_apply, InnerProductSpace.toDual_apply_apply, and_congr_right_iff]
  intro mw
  have l₀ (w) (iw : ∀ v ∈ g, inner ℝ v w = 1) : ∑ x ∈ g, inner ℝ x w = #g := by
    rw [sum_congr rfl iw, cast_card]
  have l₁ (w) (mw : w ∈ Q.toSet) : ∑ x ∈ g, inner ℝ x w ≤ #g :=
    (sum_le_sum fun v mv ↦ h.mem_iff.mp mw v (sg mv)).trans_eq (cast_card _).symm
  refine ⟨fun iw x mx ↦ ?_, fun h' ↦ ?_⟩
  · rw [l₀ w fun v hv ↦ iw v (fch.symm ▸ subset_convexHull ℝ _ hv)]
    exact l₁ x mx
  · have l₂ (v) (mv : v ∈ g) : inner ℝ v w = 1 := by
      obtain ⟨x, mx, r⟩ := ndual
      replace r (v) (hv : v ∈ g) : inner ℝ v x = 1 :=
        mem_iInter₂.mp r v (fch.symm ▸ subset_convexHull ℝ _ hv)
      replace r := le_antisymm (l₁ w mw) (l₀ x r ▸ h' x mx)
      replace r : ∑ v ∈ g, (1 - inner ℝ v w) = 0 := by
        rw [sum_sub_distrib, ← cast_card, r, sub_self]
      rw [sum_eq_zero_iff_of_nonneg fun v hv ↦ sub_nonneg_of_le (h.mem_iff.mp mw v (sg hv))] at r
      linarith [r v mv]
    replace l₂ : w ∈ ⋂ v ∈ convexHull ℝ g, {x | inner ℝ v x = 1} :=
      iInter_eq_iInter_convexHull_eq ▸ mem_iInter₂.mpr l₂
    rwa [← fch, mem_iInter₂] at l₂

include hf df in
theorem isFace : Q.IsFace (faceDual Q f) :=
  ⟨h.isExposed_faceDual hf, h.nonempty_faceDual hf df⟩

/-! ### The dual reverses dimensions of faces -/

include hf df in
lemma vectorSpan_faceDual_eq : vectorSpan ℝ (faceDual Q f) = (Submodule.span ℝ f)ᗮ := by
  apply le_antisymm
  · refine Submodule.span_le.mpr fun x mx ↦ ?_
    obtain ⟨w, mw, x, mx, rfl⟩ := mx
    simp_rw [SetLike.mem_coe, Submodule.mem_orthogonal, vsub_eq_sub, inner_sub_right]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y my => simp_all [faceDual]
    | zero => simp
    | add y z my mz hy hz => simp_rw [inner_add_left, add_sub_add_comm, hy, hz, zero_add]
    | smul k y my hy => simp_rw [inner_smul_left, ← mul_sub, hy, mul_zero]
  intro u hu
  obtain ⟨w, hw₁, hw₂, hw₃⟩ := h.exists_exposed hf df
  obtain ⟨ε, εpos, hε⟩ := exists_step_finset w u {v ∈ P.vertices | inner ℝ v w < 1} (by simp)
  replace hε (v) (mv : v ∈ P.vertices) : inner ℝ v w + ε * inner ℝ v u ≤ 1 := by
    by_cases mvf : v ∈ f
    · simp_all [hu v (Submodule.subset_span mvf)]
    · simp_rw [Finset.mem_filter, and_imp] at hε
      exact hε v mv (hw₃ v (subset_convexHull _ _ mv) mvf)
  have key : w + ε • u - w ∈ vectorSpan ℝ (faceDual Q f) := by
    refine Submodule.subset_span ⟨_, ⟨h.mem_iff.mpr fun v hv ↦ ?_, ?_⟩, _, ?_, rfl⟩
    · rw [toSet, Finset.mem_convexHull'] at hv
      obtain ⟨t, nt, st, rfl⟩ := hv
      simp_rw [sum_inner, real_inner_smul_left, inner_add_right, inner_smul_right]
      apply (Finset.sum_le_sum fun x mx ↦ mul_le_mul_of_nonneg_left (hε x mx) (nt x mx)).trans_eq
      simp [st]
    · simp_rw [mem_iInter, mem_ofPred, inner_add_right, inner_smul_right]
      intro v mv
      rw [hw₁ v mv, add_eq_left, mul_eq_zero_iff_left εpos.ne']
      exact hu v (Submodule.subset_span mv)
    · exact ⟨h.mem_iff.mpr hw₂, mem_iInter₂.mpr hw₁⟩
  convert Submodule.smul_mem _ ε⁻¹ key
  simp [εpos.ne']

include hf df in
open Submodule in
lemma finrank_span_eq : Module.finrank ℝ (span ℝ f) = faceDim f + 1 := by
  obtain ⟨z, mz⟩ := hf.2
  obtain ⟨w, hw, -⟩ := h.exists_exposed hf df
  have esup : span ℝ f = vectorSpan ℝ f ⊔ ℝ ∙ z := by
    apply le_antisymm
    · refine Submodule.span_le.mpr fun x mx ↦ ?_
      rw [SetLike.mem_coe, mem_sup]
      exact ⟨x - z, subset_span ⟨x, mx, z, mz, rfl⟩, z, by simp, by simp⟩
    · simp_rw [vectorSpan, sup_le_iff, span_le, singleton_subset_iff, SetLike.mem_coe]
      refine ⟨fun x hx ↦ ?_, subset_span mz⟩
      obtain ⟨a, ma, b, mb, rfl⟩ := hx
      exact Submodule.sub_mem _ (subset_span ma) (subset_span mb)
  rw [esup]
  refine finrank_sup_span_singleton fun mzs ↦ ?_
  have key : inner ℝ z w = 0 := by
    rw [vectorSpan, mem_span_set'] at mzs
    obtain ⟨k, t, p, rfl⟩ := mzs
    rw [sum_inner]
    refine Fintype.sum_eq_zero _ fun i ↦ ?_
    rw [real_inner_smul_left]
    have := (p i).2
    rw [mem_vsub] at this
    obtain ⟨x, mx, y, my, e⟩ := this
    rw [← e, vsub_eq_sub, inner_sub_left, hw x mx, hw y my, sub_self, mul_zero]
  simp [hw z mz] at key

include hf in
theorem dim_eq {i : Fin n} (df : faceDim f = i) : faceDim (faceDual Q f) = i.rev := by
  have key := (Submodule.span ℝ f).finrank_add_finrank_orthogonal
  rw [h.finrank_span_eq hf (df ▸ i.2), finrank_euclideanSpace_fin] at key
  rw [faceDim, h.vectorSpan_faceDual_eq hf (df ▸ i.2), Fin.val_rev]
  omega

/-! ### The dual reverses (strict) face subset relations -/

omit h in
lemma faceDual_subset (sf : f ⊆ f') : faceDual Q f' ⊆ faceDual Q f :=
  inter_subset_inter_right _ (biInter_mono sf fun _ _ _ ↦ id)

omit h in
include hf in
lemma faceDim_strictMono (hf' : P.IsFace f') (sf : f ⊂ f') : faceDim f < faceDim f' := by
  by_contra! contra
  obtain ⟨x, hx⟩ := hf.2
  obtain ⟨L, rfl⟩ := hf.1 hf.2
  refine sf.2 fun z mz ↦ ⟨hf'.1.subset mz, fun y hy ↦ (hx.2 y hy).trans_eq ?_⟩
  have work := vsub_mem_vectorSpan ℝ (sf.subset hx) mz
  rw [← Submodule.eq_of_le_of_finrank_le (vectorSpan_mono ℝ sf.1) contra] at work
  simpa [sub_eq_zero] using form_zero_of_mem_vectorSpan work

include hf in
theorem faceDual_ssubset (hf' : P.IsFace f') (df' : faceDim f' < n) (sf : f ⊂ f') :
    faceDual Q f' ⊂ faceDual Q f := by
  have dl := faceDim_strictMono hf hf' sf
  have e₁ : faceDim (faceDual Q f) = n - (faceDim f + 1) := by
    simpa using h.dim_eq hf (i := ⟨_, dl.trans df'⟩) rfl
  have e₂ : faceDim (faceDual Q f') = n - (faceDim f' + 1) := by
    simpa using h.dim_eq hf' (i := ⟨_, df'⟩) rfl
  refine ⟨faceDual_subset sf.subset, fun hc ↦ ?_⟩
  rw [subset_antisymm hc (faceDual_subset sf.subset)] at e₁
  lia

include hf df in
theorem faceDual_faceDual : faceDual P (faceDual Q f) = f := by
  refine subset_antisymm (fun x hx ↦ ?_) fun x hx ↦ ?_
  · obtain ⟨mx, mxi⟩ := hx
    by_contra nx
    obtain ⟨w, hw₁, hw₂, hw₃⟩ := h.exists_exposed hf df
    have mw : w ∈ faceDual Q f := ⟨h.mem_iff.mpr hw₂, mem_iInter₂.mpr hw₁⟩
    have : inner ℝ x w < 1 := hw₃ x mx nx
    rw [← mem_iInter₂.mp mxi w mw, real_inner_comm] at this
    exact (lt_irrefl _) this
  · refine ⟨hf.1.subset hx, mem_iInter₂.mpr fun w hw ↦ ?_⟩
    rw [mem_ofPred, real_inner_comm]
    exact mem_iInter₂.mp hw.2 x hx

/-- `h.dualFlag F` is the dual flag of `F` as a flag in `Q` (the polar dual of `P`). -/
def dualFlag (F : P.Flag) : Q.Flag where
  face k := faceDual Q (F.face k.rev)
  isFace k := h.isFace (F.isFace k.rev) (F.dim_eq _ ▸ k.rev.2)
  dim_eq k := by rw [h.dim_eq (F.isFace _) (F.dim_eq _), Fin.rev_rev]
  strict_mono i j hij :=
    h.faceDual_ssubset (F.isFace _) (F.isFace _) (F.dim_eq _ ▸ i.rev.2)
      (F.strict_mono _ _ (Fin.rev_lt_rev.mpr hij))

variable {φ : Isom n}

/-! ### Isometries preserving the origin play well with duals -/

lemma isSymmetry (sφ : P.isSymmetry φ) (φ0 : φ 0 = 0) : Q.isSymmetry φ := by
  have lφ (a) : φ.linearIsometryEquiv a = φ a := by simpa [φ0] using φ.map_vsub a 0
  have iφ (a b) : inner ℝ (φ a) (φ b) = inner ℝ a b := by simp [← lφ]
  have key (w) : φ w ∈ Q.toSet ↔ w ∈ Q.toSet := by
    simp_rw [h.mem_iff]
    constructor <;> intro h v hv
    · convert h (φ v) _ using 1
      · rw [iφ]
      · exact sφ.subset (mem_image_of_mem _ hv)
    · convert h (φ.symm v) _ using 1
      · rw [← iφ (φ.symm v) w, φ.apply_symm_apply]
      · have := sφ.symm ▸ mem_image_of_mem φ.symm hv
        simpa [image_image] using this
  ext x
  exact ⟨fun ⟨y, hy, hy'⟩ ↦ (hy'.symm ▸ key y).mpr hy,
    fun hx ↦ ⟨φ.symm x, (key _).mp (by simpa [φ0] using hx), by simp⟩⟩

lemma isom_apply (sφ : P.isSymmetry φ) (φ0 : φ 0 = 0) (mf : φ '' f = f') :
    φ '' faceDual Q f = faceDual Q f' := by
  have lφ (a) : φ.linearIsometryEquiv a = φ a := by simpa [φ0] using φ.map_vsub a 0
  have iφ (a b) : inner ℝ (φ a) (φ b) = inner ℝ a b := by simp [← lφ]
  have sQ := h.isSymmetry sφ φ0
  ext y
  simp_rw [faceDual, mem_inter_iff]
  constructor
  · rintro ⟨x, ⟨mx, mxi⟩, rfl⟩
    refine ⟨sQ ▸ mem_image_of_mem _ mx, mem_iInter₂.mpr fun v' hv' ↦ ?_⟩
    rw [← mf] at hv'
    obtain ⟨v, hv, rfl⟩ := hv'
    rw [mem_ofPred, iφ]
    exact mem_iInter₂.mp mxi v hv
  · intro hy
    refine ⟨φ.symm y, ⟨?_, mem_iInter₂.mpr fun v hv ↦ ?_⟩, φ.apply_symm_apply y⟩
    · obtain ⟨x, mx, rfl⟩ := sQ.symm ▸ hy.1
      rwa [φ.symm_apply_apply]
    · have hv' := mf ▸ mem_image_of_mem _ hv
      rw [mem_ofPred, ← iφ v (φ.symm y), φ.apply_symm_apply]
      exact mem_iInter₂.mp hy.2 (φ v) hv'

theorem isRegular (hP : P.IsRegular) (centred : ∀ φ, P.isSymmetry φ → φ 0 = 0) : Q.IsRegular := by
  refine ⟨h.symm.isFullDim, fun G₁ G₂ ↦ ?_⟩
  obtain ⟨φ, hsym, hmap⟩ := hP.2 (h.symm.dualFlag G₁) (h.symm.dualFlag G₂)
  refine ⟨φ, h.isSymmetry hsym (centred φ hsym), fun j ↦ ?_⟩
  have mφ : φ '' faceDual P (G₁.face j) = faceDual P (G₂.face j) := by
    simpa only [dualFlag, Fin.rev_rev] using hmap j.rev
  have dd₁ := h.symm.faceDual_faceDual (G₁.isFace j) (G₁.dim_eq _ ▸ j.2)
  have dd₂ := h.symm.faceDual_faceDual (G₂.isFace j) (G₂.dim_eq _ ▸ j.2)
  have final := h.isom_apply hsym (centred φ hsym) mφ
  rwa [dd₁, dd₂] at final

end IsPolarDual
