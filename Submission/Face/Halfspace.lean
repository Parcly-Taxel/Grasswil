import Submission.Face.Lattice

namespace LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {n : ℕ} {P : ConvexPolytope n} (dP : P.IsFullDim) {f : Set (E n)} (hf : P.IsFace f)
variable {x : E n} {M : StrongDual ℝ (E n)} {d : ℝ}

/-- The linear functional corresponding to a polytope face. -/
noncomputable def IsFace.L : StrongDual ℝ (E n) :=
  (hf.1.exists_dual_eq hf.2).choose

/-- The value assumed by `IsFace.L` on the face, which is a maximum. -/
noncomputable def IsFace.c : ℝ :=
  (hf.1.exists_dual_eq hf.2).choose_spec.choose

lemma IsFace.L_le_on_toSet : ∀ v ∈ P.toSet, hf.L v ≤ hf.c :=
  (hf.1.exists_dual_eq hf.2).choose_spec.choose_spec.1

lemma IsFace.L_max_on_self : f = {v ∈ P.toSet | hf.L v = hf.c} :=
  (hf.1.exists_dual_eq hf.2).choose_spec.choose_spec.2

include dP hf in
lemma vectorSpan_facet_eq_ker_of_exposing (df : faceDim f + 1 = n)
    (hM : ∀ v ∈ P.toSet, M v ≤ d) (hface : f = {v ∈ P.toSet | M v = d}) :
    vectorSpan ℝ f = LinearMap.ker M.toLinearMap := by
  obtain ⟨w, hw⟩ := hf.2
  have hw' := hface ▸ hw
  have hmax : f = {v ∈ P.toSet | ∀ y ∈ P.toSet, M y ≤ M v} := by
    rw [hface]
    ext v
    simp only [Set.mem_ofPred_eq, and_congr_right_iff]
    exact fun hv ↦ ⟨fun he y hy ↦ (hM y hy).trans_eq he.symm,
      fun hm ↦ le_antisymm (hM v hv) (hw'.2 ▸ hm w hw'.1)⟩
  have hle : vectorSpan ℝ f ≤ LinearMap.ker M.toLinearMap := fun v hv ↦ by
    rw [LinearMap.mem_ker]
    exact form_zero_of_mem_vectorSpan (hmax ▸ hv)
  have hMne : M.toLinearMap ≠ 0 := fun hzero ↦ by
    have Mzero (z : E n) : M z = 0 := LinearMap.congr_fun hzero z
    have deq : d = 0 := by simpa [Mzero] using hw'.2.symm
    have feq : f = P.toSet := by simp [hface, Mzero, deq]
    have hdim : faceDim f = P.dim := by rw [faceDim, dim, feq]
    rw [hdim, dP] at df
    lia
  apply Submodule.eq_of_le_of_finrank_le hle
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hMne
  rw [finrank_euclideanSpace_fin] at hk
  rw [faceDim] at df
  omega

include dP hf in
/-- The halfspace defined by a facet of a full-dimensional polytope is unique.
TODO: replace `hd` with `x ≠ 0`? -/
lemma unique_facet_halfspace (df : faceDim f + 1 = n) (hd : d ≠ 0)
    (LP : ∀ w ∈ P.vertices, inner ℝ x w ≤ d) (maxL : ∀ w ∈ faceGens hf.1, inner ℝ x w = d) :
    {w | hf.L w ≤ hf.c} = {w | inner ℝ x w ≤ d} := by
  let M : StrongDual ℝ (E n) := InnerProductSpace.toDual ℝ (E n) x
  have hM_apply (v) : M v = inner ℝ x v := rfl
  have hM : ∀ v ∈ P.toSet, M v ≤ d := fun v hv ↦ by
    rw [toSet] at hv
    exact dual_le_of_mem_convexHull (fun w hw ↦ hM_apply w ▸ LP w hw) hv
  let g := {v ∈ P.toSet | M v = d}
  obtain ⟨w, hw⟩ := hf.2
  have hfg : f ⊆ g := fun v hv ↦ by
    refine ⟨hf.1.subset hv, ?_⟩
    have hv' : v ∈ convexHull ℝ (faceGens hf.1) := by rwa [← convexHull_faceGens hf.1]
    rw [Finset.mem_convexHull'] at hv'
    obtain ⟨a, -, ha, rfl⟩ := hv'
    have hmax (u) (hu : u ∈ faceGens hf.1) : M u = d := by
      rw [hM_apply]
      exact maxL u hu
    rw [map_sum]
    calc
      _ = ∑ u ∈ faceGens hf.1, a u * d := by
        refine Finset.sum_congr rfl fun u hu ↦ ?_
        rw [map_smul, smul_eq_mul, hmax u hu]
      _ = d := by rw [← Finset.sum_mul, ha, one_mul]
  have hwg : w ∈ g := hfg hw
  have hgexp : IsExposed ℝ P.toSet g := fun _ ↦ by
    refine ⟨M, ?_⟩
    ext v
    simp only [g, Set.mem_ofPred_eq, and_congr_right_iff]
    exact fun hv ↦ ⟨fun he y hy ↦ (hM y hy).trans_eq he.symm,
      fun hm ↦ le_antisymm (hM v hv) (hwg.2 ▸ hm w hwg.1)⟩
  have hg : P.IsFace g := ⟨hgexp, ⟨w, hwg⟩⟩
  have hMne : M.toLinearMap ≠ 0 := fun hzero ↦ by
    obtain ⟨v, hv⟩ := nonempty_faceGens hf
    apply hd
    rw [← maxL v hv, ← hM_apply]
    exact LinearMap.congr_fun hzero v
  have gne : g ≠ P.toSet := fun hgp ↦ by
    have hmax : {v | v ∈ P.toSet ∧ ∀ y ∈ P.toSet, M y ≤ M v} = P.toSet := by
      ext v
      simp only [Set.mem_ofPred_eq]
      constructor
      · exact fun hv ↦ hv.1
      · intro hv
        refine ⟨hv, fun y hy ↦ ?_⟩
        have hMy : M y = d := (show y ∈ g from hgp.symm ▸ hy).2
        have hMv : M v = d := (show v ∈ g from hgp.symm ▸ hv).2
        rw [hMy, hMv]
    apply hMne
    ext v
    apply form_zero_of_mem_vectorSpan (s := P.toSet)
    rw [hmax]
    have hspan : vectorSpan ℝ P.toSet = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [show Module.finrank ℝ (vectorSpan ℝ P.toSet) = P.dim by rfl, dP,
        finrank_euclideanSpace_fin]
    rw [hspan]
    exact Submodule.mem_top
  have hfg_eq : f = g := by
    apply subset_antisymm hfg
    by_contra hgf
    have hss : f ⊂ g := ⟨hfg, hgf⟩
    have hdlt := faceDim_strictMono hf hg hss
    have hglt : faceDim g < n := by
      have hP : P.IsFace P.toSet := ⟨IsExposed.refl _, by simp [toSet, P.vertices_nonempty]⟩
      have hs : g ⊂ P.toSet := ⟨hg.1.subset, fun h ↦ gne (subset_antisymm hg.1.subset h)⟩
      have := faceDim_strictMono hg hP hs
      rwa [show faceDim P.toSet = P.dim from rfl, dP] at this
    lia
  have hkM := vectorSpan_facet_eq_ker_of_exposing dP hf df hM (hfg_eq.trans rfl)
  have hkL := vectorSpan_facet_eq_ker_of_exposing dP hf df hf.L_le_on_toSet hf.L_max_on_self
  have hker := hkM.symm.trans hkL
  have hspan : hf.L.toLinearMap ∈ ℝ ∙ M.toLinearMap := by
    simpa using mem_span_of_iInf_ker_le_ker (ι := Unit) (L := fun _ ↦ M.toLinearMap)
      (K := hf.L.toLinearMap) (by simp [hker])
  rw [Submodule.mem_span_singleton] at hspan
  obtain ⟨a, ha⟩ := hspan
  have hfun (v : E n) : a * M v = hf.L v := by
    simpa [smul_eq_mul] using LinearMap.congr_fun ha v
  obtain ⟨z, hzP, hzg⟩ : ∃ z ∈ P.toSet, z ∉ g := by
    contrapose! gne
    exact subset_antisymm hg.1.subset gne
  have hzM : M z < d := (hM z hzP).lt_of_ne fun he ↦ hzg (by simp [g, hzP, he])
  have hwL := (hf.L_max_on_self ▸ hw).2
  have hzL : hf.L z < hf.c :=
    (hf.L_le_on_toSet z hzP).lt_of_ne fun he ↦ hzg (hfg (hf.L_max_on_self ▸ ⟨hzP, he⟩))
  have hwM := (hfg_eq ▸ hw).2
  have apos : 0 < a := by
    rw [← hwL, ← hfun, ← hfun] at hzL
    nlinarith
  ext v
  simp only [Set.mem_ofPred_eq, ← hM_apply]
  rw [← hwL, ← hfun, ← hfun w, hwM, mul_le_mul_iff_right₀ apos]

include dP hf in
lemma facet_canonical_separates_of_exposing (df : faceDim f + 1 = n) (hM : ∀ v ∈ P.toSet, M v ≤ d)
    (hface : f = {v ∈ P.toSet | M v = d}) (hx : d < M x) : hf.c < hf.L x := by
  have hkM := vectorSpan_facet_eq_ker_of_exposing dP hf df hM hface
  have hkL := vectorSpan_facet_eq_ker_of_exposing dP hf df hf.L_le_on_toSet hf.L_max_on_self
  have hker := hkM.symm.trans hkL
  have hspan : hf.L.toLinearMap ∈ ℝ ∙ M.toLinearMap := by
    simpa using mem_span_of_iInf_ker_le_ker (ι := Unit) (L := fun _ ↦ M.toLinearMap)
      (K := hf.L.toLinearMap) (by simp [hker])
  rw [Submodule.mem_span_singleton] at hspan
  obtain ⟨a, ha⟩ := hspan
  have hfun (z : E n) : a * M z = hf.L z := by simpa [smul_eq_mul] using LinearMap.congr_fun ha z
  obtain ⟨w, hw⟩ := hf.2
  have hwM := (hface ▸ hw).2
  have hwL := (hf.L_max_on_self ▸ hw).2
  have hproper : f ≠ P.toSet := fun heq ↦ by
    have hdim : faceDim f = P.dim := by rw [faceDim, dim, heq]
    rw [hdim, dP] at df
    simp_all
  obtain ⟨z, hzP, hzf⟩ : ∃ z ∈ P.toSet, z ∉ f := by
    contrapose! hproper
    exact subset_antisymm hf.1.subset hproper
  have hzM : M z < d := (hM z hzP).lt_of_ne fun he ↦ hzf (hface ▸ ⟨hzP, he⟩)
  have hzL : hf.L z < hf.c :=
    (hf.L_le_on_toSet z hzP).lt_of_ne fun he ↦ hzf (hf.L_max_on_self ▸ ⟨hzP, he⟩)
  have apos : 0 < a := by
    have hneg : a * (M z - M w) < 0 := by
      rw [mul_sub, hfun, hfun, hwL]
      linarith
    have hdiff : M z - M w < 0 := by rw [hwM]; linarith
    nlinarith
  rw [← hwL, ← hfun, ← hfun]
  nlinarith

lemma exists_exposing_face_separating (hx : x ∉ P.toSet) :
    ∃ (f : Set (E n)) (_ : P.IsFace f) (M : StrongDual ℝ (E n)) (d : ℝ),
    (∀ v ∈ P.toSet, M v ≤ d) ∧ f = {v ∈ P.toSet | M v = d} ∧ d < M x := by
  have hclosed : IsClosed P.toSet := P.vertices.finite_toSet.isClosed_convexHull (𝕜 := ℝ)
  obtain ⟨M, d, hM, hxM⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hclosed hx
  have hc := P.vertices.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hn : P.toSet.Nonempty := by
    rw [toSet, convexHull_nonempty_iff]
    exact P.vertices_nonempty
  obtain ⟨w, hwP, hw⟩ := hc.exists_isMaxOn hn M.continuous.continuousOn
  let f := {v ∈ P.toSet | M v = M w}
  have hfexp : IsExposed ℝ P.toSet f := fun _ ↦ by
    refine ⟨M, ?_⟩
    ext v
    simp only [f, Set.mem_ofPred_eq, and_congr_right_iff]
    exact fun hv ↦ ⟨fun he y hy ↦ (hw hy).trans_eq he.symm,
      fun hmax ↦ le_antisymm (hw hv) (hmax w hwP)⟩
  have hf : P.IsFace f := ⟨hfexp, ⟨w, hwP, rfl⟩⟩
  refine ⟨f, hf, M, M w, hw, rfl, ?_⟩
  exact (hM w hwP).trans hxM

include dP hf in
lemma faceDim_lt_of_strict_exposing (hface : f = {v ∈ P.toSet | M v = d}) (hx : d < M x) :
    faceDim f < n := by
  have hP : P.IsFace P.toSet := ⟨IsExposed.refl _, by simp [toSet, P.vertices_nonempty]⟩
  have hd := faceDim_strictMono hf hP
  rw [show faceDim P.toSet = P.dim from rfl, dP] at hd
  apply hd
  refine ⟨hf.1.subset, fun hsub ↦ ?_⟩
  obtain ⟨w, hw⟩ := hf.2
  have hw' := hface ▸ hw
  have hmax : f = {v ∈ P.toSet | ∀ y ∈ P.toSet, M y ≤ M v} := by
    rw [hface]
    ext v
    simp only [Set.mem_ofPred_eq, and_congr_right_iff]
    exact fun hv ↦ ⟨fun he y hy ↦ he ▸ (hface ▸ hsub hy).2.le,
      fun hm ↦ le_antisymm ((hface ▸ hsub hv).2.le) (hw'.2 ▸ hm w hw'.1)⟩
  have hzero : M.toLinearMap = 0 := by
    ext z
    apply form_zero_of_mem_vectorSpan
    rw [← hmax, hf.1.subset.antisymm hsub]
    have hspan : vectorSpan ℝ P.toSet = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [show Module.finrank ℝ (vectorSpan ℝ P.toSet) = P.dim from rfl, dP,
        finrank_euclideanSpace_fin]
    simp [hspan]
  have Mzero : M x = 0 := LinearMap.congr_fun hzero x
  have deq : d = 0 := hw'.2.symm.trans (LinearMap.congr_fun hzero w)
  linarith

include dP hf in
lemma exists_larger_exposing_separator (df : faceDim f + 1 < n)
    (hM : ∀ v ∈ P.toSet, M v ≤ d) (hface : f = {v ∈ P.toSet | M v = d}) (hx : d < M x) :
    ∃ (g : Set (E n)) (_ : P.IsFace g) (N : StrongDual ℝ (E n)) (e : ℝ),
    f ⊂ g ∧ (∀ v ∈ P.toSet, N v ≤ e) ∧ g = {v ∈ P.toSet | N v = e} ∧ e < N x := by
  have dfl : faceDim f < P.dim := by rw [dP]; lia
  obtain ⟨g, sfg, hg, dg⟩ := exists_superface hf dfl
  by_cases hgx : hg.c < hg.L x
  · exact ⟨g, hg, hg.L, hg.c, sfg, hg.L_le_on_toSet, hg.L_max_on_self, hgx⟩
  classical
  let S := P.vertices.filter fun v ↦ v ∉ g
  have S_def : S = P.vertices.filter fun v ↦ v ∉ g := rfl
  have gne : g ≠ P.toSet := fun geq ↦ by
    have gdim : faceDim g = P.dim := by rw [faceDim, dim, geq]
    rw [gdim, dP] at dg
    lia
  have nS : S.Nonempty := by
    by_contra hS
    have hvert (v) (hv : v ∈ P.vertices) : v ∈ g := by
      by_contra hvg
      apply hS
      exact ⟨v, by simp only [S, Finset.mem_filter, hv, hvg, not_false_eq_true, and_self]⟩
    have hPg : P.toSet ⊆ g := by
      rw [toSet]
      exact convexHull_min hvert (hg.1.convex (convex_convexHull ℝ _))
    exact gne (subset_antisymm hg.1.subset hPg)
  let r (v : E n) := (d - M v) / (hg.c - hg.L v)
  let t := (S.image r).min' (nS.image r)
  have rt (v) (hv : v ∈ S) : t ≤ r v := Finset.min'_le _ _ (Finset.mem_image_of_mem r hv)
  have rpos (v) (hv : v ∈ S) : 0 < r v := by
    have hvP : v ∈ P.toSet :=
      subset_convexHull ℝ _ (Finset.mem_filter.mp (by simpa only [S] using hv)).1
    have hvg : v ∉ g := by
      have hv' : v ∈ P.vertices ∧ v ∉ g := by simpa only [S, Finset.mem_filter] using hv
      exact hv'.2
    have hL : hg.L v < hg.c :=
      (hg.L_le_on_toSet v hvP).lt_of_ne fun he ↦ hvg (hg.L_max_on_self ▸ ⟨hvP, he⟩)
    have hvf : v ∉ f := fun hvf ↦ hvg (sfg.1 hvf)
    have hMv : M v < d := (hM v hvP).lt_of_ne fun he ↦ hvf (hface ▸ ⟨hvP, he⟩)
    exact div_pos (sub_pos.mpr hMv) (sub_pos.mpr hL)
  have tpos : 0 < t := by
    obtain ⟨v, hv, hvt⟩ := Finset.mem_image.mp (Finset.min'_mem _ (nS.image r))
    change 0 < (S.image r).min' (nS.image r)
    rw [← hvt]
    exact rpos v hv
  let N : StrongDual ℝ (E n) := M - t • hg.L
  let e := d - t * hg.c
  have hNvert (v) (hv : v ∈ P.vertices) : N v ≤ e := by
    by_cases hvg : v ∈ g
    · have hLv := (hg.L_max_on_self ▸ hvg).2
      simp only [N, e, sub_apply, smul_apply, smul_eq_mul, hLv]
      linarith [hM v (subset_convexHull ℝ _ hv)]
    · have hvS : v ∈ S := S_def.symm ▸ Finset.mem_filter.mpr ⟨hv, hvg⟩
      have hvP : v ∈ P.toSet := subset_convexHull ℝ _ hv
      have hL : 0 < hg.c - hg.L v := sub_pos.mpr <|
        (hg.L_le_on_toSet v hvP).lt_of_ne fun he ↦ hvg (hg.L_max_on_self ▸ ⟨hvP, he⟩)
      have hratio := rt v hvS
      change t ≤ (d - M v) / (hg.c - hg.L v) at hratio
      rw [le_div_iff₀ hL] at hratio
      simp only [N, e, sub_apply, smul_apply, smul_eq_mul]
      linarith
  have hN : ∀ v ∈ P.toSet, N v ≤ e := fun v hv ↦ dual_le_of_mem_convexHull hNvert hv
  let q := {v ∈ P.toSet | N v = e}
  obtain ⟨w, hw⟩ := hf.2
  have hwM := (hface ▸ hw).2
  have hwL := (hg.L_max_on_self ▸ sfg.1 hw).2
  have hwq : w ∈ q := ⟨hf.1.subset hw, by simp [N, e, hwM, hwL]⟩
  have hqexp : IsExposed ℝ P.toSet q := fun _ ↦ by
    refine ⟨N, ?_⟩
    ext v
    simp only [q, Set.mem_ofPred_eq, and_congr_right_iff]
    exact fun hv ↦ ⟨fun he y hy ↦ (hN y hy).trans_eq he.symm,
      fun hm ↦ le_antisymm (hN v hv) (hwq.2 ▸ hm w hwq.1)⟩
  have hq : P.IsFace q := ⟨hqexp, ⟨w, hwq⟩⟩
  have sfq : f ⊂ q := by
    refine ⟨fun v hv ↦ ?_, ?_⟩
    · have hvM := (hface ▸ hv).2
      have hvL := (hg.L_max_on_self ▸ sfg.1 hv).2
      exact ⟨hf.1.subset hv, by simp [N, e, hvM, hvL]⟩
    · obtain ⟨z, hzS, hrz⟩ := Finset.mem_image.mp (Finset.min'_mem _ (nS.image r))
      intro hqf
      have hzS' : z ∈ P.vertices ∧ z ∉ g := by simpa only [S, Finset.mem_filter] using hzS
      have hzP : z ∈ P.toSet := subset_convexHull ℝ _ hzS'.1
      have hzL : 0 < hg.c - hg.L z := sub_pos.mpr <|
        (hg.L_le_on_toSet z hzP).lt_of_ne fun he ↦ hzS'.2 (hg.L_max_on_self ▸ ⟨hzP, he⟩)
      have hratio : t * (hg.c - hg.L z) = d - M z := by
        change (S.image r).min' (nS.image r) * (hg.c - hg.L z) = d - M z
        rw [← hrz]
        change ((d - M z) / (hg.c - hg.L z)) * (hg.c - hg.L z) = d - M z
        exact div_mul_cancel₀ _ hzL.ne'
      have hzq : z ∈ q := by
        refine ⟨hzP, ?_⟩
        simp only [N, e, sub_apply, smul_apply, smul_eq_mul]
        linarith
      exact hzS'.2 (sfg.1 (hqf hzq))
  refine ⟨q, hq, N, e, sfq, hN, rfl, ?_⟩
  simp only [N, e, sub_apply, smul_apply, smul_eq_mul]
  have hxM : 0 < M x - d := sub_pos.mpr hx
  have hxL : hg.L x - hg.c ≤ 0 := sub_nonpos.mpr (not_lt.mp hgx)
  nlinarith [mul_nonpos_of_nonneg_of_nonpos tpos.le hxL]

include dP hf in
lemma extend_exposing_separator_to_facet
    (hM : ∀ v ∈ P.toSet, M v ≤ d) (hface : f = {v ∈ P.toSet | M v = d}) (hx : d < M x) :
    ∃ (g : Set (E n)) (_ : P.IsFace g) (N : StrongDual ℝ (E n)) (e : ℝ),
    faceDim g + 1 = n ∧ (∀ v ∈ P.toSet, N v ≤ e) ∧ g = {v ∈ P.toSet | N v = e} ∧ e < N x := by
  induction hk : n - (faceDim f + 1) using Nat.strong_induction_on generalizing f M d with | _ k ih
  have fdlt : faceDim f < n := faceDim_lt_of_strict_exposing dP hf hface hx
  by_cases df : faceDim f + 1 = n
  · exact ⟨f, hf, M, d, df, hM, hface, hx⟩
  have dflt : faceDim f + 1 < n := by lia
  obtain ⟨g, hg, N, e, sfg, hN, hgface, hxN⟩ :=
    exists_larger_exposing_separator dP hf dflt hM hface hx
  have gd := faceDim_strictMono hf hg sfg
  exact ih (n - (faceDim g + 1)) (by lia) hg hN hgface hxN rfl

include dP in
lemma exists_exposing_facet_separating (hx : x ∉ P.toSet) :
    ∃ (f : Set (E n)) (_ : P.IsFace f) (M : StrongDual ℝ (E n)) (d : ℝ),
    faceDim f + 1 = n ∧ (∀ v ∈ P.toSet, M v ≤ d) ∧ f = {v ∈ P.toSet | M v = d} ∧ d < M x := by
  obtain ⟨f, hf, M, d, hM, hface, hxM⟩ := exists_exposing_face_separating hx
  exact extend_exposing_separator_to_facet dP hf hM hface hxM

include dP in
lemma exists_facet_separating (hx : x ∉ P.toSet) :
    ∃ (f : Set (E n)) (hf : P.IsFace f), faceDim f + 1 = n ∧ hf.c < hf.L x := by
  obtain ⟨f, hf, M, d, df, hM, hface, hxM⟩ := exists_exposing_facet_separating dP hx
  exact ⟨f, hf, df, facet_canonical_separates_of_exposing dP hf df hM hface hxM⟩

include dP in
/-- A full-dimensional polytope is the intersection of the halfspaces defined by its facets
(its **H-representation**). -/
theorem toSet_eq_iInter_facet_halfspaces :
    P.toSet = ⋂ (f) (hf : P.IsFace f) (_ : faceDim f + 1 = n), {x | hf.L x ≤ hf.c} := by
  refine subset_antisymm (fun x mx ↦ ?_) fun x mx ↦ ?_
  · simp only [Set.mem_iInter]
    exact fun _ hf _ ↦ hf.L_le_on_toSet x mx
  · simp only [Set.mem_iInter] at mx
    by_contra nx
    obtain ⟨f, hf, df, hfx⟩ := exists_facet_separating dP nx
    exact hfx.not_ge (mx f hf df)

end LeanEval.Geometry.PlatonicClassification.ConvexPolytope
