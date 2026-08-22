import ChallengeDeps
import Submission.ToMathlib.Exposed
import Submission.ToMathlib.Misc

noncomputable section
open Finset Real Matrix LeanEval.Geometry.PlatonicClassification ConvexPolytope

variable {n : ℕ} {R : orthogonalGroup (Fin n) ℝ} {v p : E n}

variable (R) in
/-- Construct a linear isometry from an orthogonal matrix. -/
def toLI : E n ≃ₗᵢ[ℝ] E n where
  toLinearEquiv := R.1.toLinearEquiv (PiLp.basisFun ..) (UnitaryGroup.det_isUnit _)
  norm_map' p := by
    simp_rw [EuclideanSpace.norm_eq, norm_eq_abs, sq_abs, sq]
    suffices (R.1 *ᵥ p) ⬝ᵥ (R.1 *ᵥ p) = p ⬝ᵥ p by congr 1
    have ho : R.1ᵀ * R.1 = 1 := R.2.1
    simp [dotProduct_mulVec, vecMul_mulVec, ho]

variable (R v) in
/-- Construct an `Isom` from an orthogonal matrix and a translation vector. -/
def toIsom : Isom n := AffineIsometryEquiv.mk' (toLI R · + v) (toLI R) 0 (by simp)

lemma toIsom_apply : toIsom R v p = .toLp 2 (R.1 *ᵥ p + v) := rfl

lemma toIsom_add : toIsom R 0 (v + p) = toIsom R 0 v + toIsom R 0 p := by
  simp [toIsom_apply, mulVec_add]

lemma isom_image_convexHull (R : Isom n) (s : Set (E n)) :
    R '' convexHull ℝ s = convexHull ℝ (R '' s) :=
  R.toAffineMap.image_convexHull s

lemma smul_image_convexHull {a : ℝ} (na : a ≠ 0) (s : Set (E n)) :
    (a • ·) '' convexHull ℝ s = convexHull ℝ ((a • ·) '' s) := by
  let A := LinearEquiv.smulOfUnit (M := E n) ⟨_, _, mul_inv_cancel₀ na, inv_mul_cancel₀ na⟩
  exact A.toAffineMap.image_convexHull s

lemma affineEquiv_image_extremePoints (R : E n ≃ᵃ[ℝ] E n) (s : Set (E n)) :
    R '' Set.extremePoints ℝ s = Set.extremePoints ℝ (R '' s) := by
  ext y
  simp only [Set.mem_image, mem_extremePoints, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, ← exists_and_right, and_assoc]
  conv_lhs => enter [1, x, 2]; rw [and_comm]
  refine exists_congr fun x ↦ ?_
  simp only [and_congr_right_iff]
  rintro mx rfl
  refine forall₄_congr fun a ma b mb ↦ ?_
  simp only [R.injective.eq_iff]
  apply imp_congr_left
  have key : R '' openSegment ℝ a b = openSegment ℝ (R a) (R b) :=
    image_openSegment _ R.toAffineMap a b
  simp [← key]

lemma isom_image_extremePoints (R : Isom n) (s : Set (E n)) :
    R '' Set.extremePoints ℝ s = Set.extremePoints ℝ (R '' s) :=
  affineEquiv_image_extremePoints R s

lemma smul_image_extremePoints {a : ℝ} (na : a ≠ 0) (s : Set (E n)) :
    (a • ·) '' Set.extremePoints ℝ s = Set.extremePoints ℝ ((a • ·) '' s) := by
  let A := LinearEquiv.smulOfUnit (M := E n) ⟨_, _, mul_inv_cancel₀ na, inv_mul_cancel₀ na⟩
  exact affineEquiv_image_extremePoints A.toAffineEquiv s

lemma affineEquiv_image_centroid (R : E n ≃ᵃ[ℝ] E n) {s : Finset (E n)} (hs : s.Nonempty) :
    R (s.centroid ℝ id) = (s.image R).centroid ℝ id := by
  have key := centroid_map (k := ℝ) s ⟨R, R.injective⟩ id
  rw [map_eq_image, Function.Embedding.coeFn_mk] at key
  rw [key]
  exact map_affineCombination s _ _ (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs) R.toAffineMap

lemma isom_image_centroid (R : Isom n) {s : Finset (E n)} (hs : s.Nonempty) :
    R (s.centroid ℝ id) = (s.image R).centroid ℝ id :=
  affineEquiv_image_centroid R hs

lemma smul_image_centroid {a : ℝ} {s : Finset (E n)} (na : a ≠ 0) (hs : s.Nonempty) :
    a • (s.centroid ℝ id) = (s.image (a • ·)).centroid ℝ id := by
  let A := LinearEquiv.smulOfUnit (M := E n) ⟨_, _, mul_inv_cancel₀ na, inv_mul_cancel₀ na⟩
  exact affineEquiv_image_centroid A.toAffineEquiv hs

lemma centroid_eq_inv_smul_sum {s : Finset (E n)} {f : E n → E n} (ns : s.Nonempty) :
    s.centroid ℝ f = (#s : ℝ)⁻¹ • ∑ v ∈ s, f v := by
  simp_rw [centroid_eq_centerMass _ ns, centerMass, centroidWeights_apply, sum_const, nsmul_eq_mul]
  rw [← card_ne_zero] at ns
  rw [mul_inv_cancel₀ (by simp [ns]), inv_one, one_smul, ← smul_sum]

namespace LeanEval.Geometry.PlatonicClassification.ConvexPolytope

lemma faceDim_image_affineEquiv {s : Set (E n)} (e : E n ≃ᵃ[ℝ] E n) :
    faceDim (e '' s) = faceDim s := by
  have h : (⇑e '' s) = (⇑e.toAffineMap '' s) := rfl
  rw [faceDim, h, ← AffineMap.map_vectorSpan]
  exact (Submodule.equivMapOfInjective _ e.linear.injective _).finrank_eq.symm

variable {P Q : ConvexPolytope n}

lemma vertices_eq_image_of_toSet_eq (e : E n ≃ᵃ[ℝ] E n) (hQ : Q.toSet = e '' P.toSet) :
    Q.vertices = P.vertices.image e := by
  simp_rw [toSet] at hQ
  rw [← coe_inj, coe_image, P.vertices_eq_extremePoints, Q.vertices_eq_extremePoints,
    affineEquiv_image_extremePoints, hQ]

section

variable {φ ψ : Isom n} {a b : ℝ} (ha : a ≠ 0)

lemma isSymmetry.mul (sφ : P.isSymmetry φ) (sψ : P.isSymmetry ψ) : P.isSymmetry (φ * ψ) := by
  unfold isSymmetry at sφ sψ ⊢
  rwa [AffineIsometryEquiv.coe_mul, Set.image_comp, sψ]

lemma isSymmetry.inv (sφ : P.isSymmetry φ) : P.isSymmetry φ⁻¹ := by
  unfold isSymmetry at sφ ⊢
  nth_rw 1 [← sφ, ← Set.image_comp]
  simp

lemma isSymmetry.image_vertices (sφ : P.isSymmetry φ) : P.vertices.image φ = P.vertices := by
  rw [← coe_inj, coe_image, vertices_eq_extremePoints, isom_image_extremePoints]
  congr

lemma isSymmetry.map_centroid (sφ : P.isSymmetry φ) :
    φ (P.vertices.centroid ℝ id) = P.vertices.centroid ℝ id := by
  conv_rhs => rw [← sφ.image_vertices]
  exact affineEquiv_image_centroid _ P.vertices_nonempty

variable (φ) in
/-- Conjugating an affine isometry by a nonzero scaling remains an affine isometry. -/
def Isom.conj : Isom n :=
  AffineIsometryEquiv.mk' (fun x ↦ a⁻¹ • φ (a • x)) φ.linearIsometryEquiv 0 fun x ↦ by
    simpa [inv_smul_smul₀ ha] using congr(a⁻¹ • $(φ.map_vadd 0 (a • x)))

lemma Isom.smul_conj : a • φ.conj ha v = φ (a • v) := by
  change a • (a⁻¹ • φ (a • v)) = _
  rw [smul_inv_smul₀ ha]

lemma image_scale_isom_scale {s : Set (E n)} :
    (b • ·) '' φ '' (a • ·) '' s = ((b * a) • ·) '' φ.conj ha '' s := by
  simp_rw [Set.image_image, ← φ.smul_conj ha, smul_smul]

end

lemma similar_refl : P.Similar P :=
  ⟨1, zero_lt_one, 1, by simp⟩

lemma similar_symm (hs : P.Similar Q) : Q.Similar P := by
  obtain ⟨a, apos, φ, hφ⟩ := hs
  have ha : a ≠ 0 := apos.ne'
  let ψ := Isom.conj φ.symm (inv_ne_zero ha)
  have hψ (x) : ψ x = a • φ.symm (a⁻¹ • x) := by
    change a⁻¹⁻¹ • φ.symm (a⁻¹ • x) = _
    rw [inv_inv]
  refine ⟨a⁻¹, inv_pos.mpr apos, ψ, ?_⟩
  rw [hφ]
  calc
    _ = id '' P.toSet := by simp
    _ = ((a⁻¹ • ·) ∘ ψ ∘ (a • ·) ∘ φ) '' P.toSet := by
      simp_rw [Function.comp_apply, hψ, inv_smul_smul₀ ha, φ.symm_apply_apply, id_eq]
    _ = _ := by simp_rw [Set.image_comp]

lemma similar_trans {R : ConvexPolytope n} (sP : P.Similar Q) (sQ : Q.Similar R) : P.Similar R := by
  obtain ⟨a, apos, φ, hφ⟩ := sP
  obtain ⟨b, bpos, ψ, hψ⟩ := sQ
  have ha : a ≠ 0 := apos.ne'
  refine ⟨b * a, mul_pos bpos apos, ψ.conj ha * φ, ?_⟩
  rw [hψ, hφ, image_scale_isom_scale ha, (ψ.conj ha).coe_mul, Set.image_comp]

lemma Similar.card_vertices_eq (hs : P.Similar Q) : #P.vertices = #Q.vertices := by
  obtain ⟨a, apos, φ, map⟩ := hs
  suffices Q.vertices = P.vertices.image (a • φ ·) by
    rw [this]
    refine (card_image_of_injective _ fun x y hxy ↦ ?_).symm
    rwa [smul_right_inj apos.ne', φ.injective.eq_iff] at hxy
  rw [← coe_inj, Q.vertices_eq_extremePoints, coe_image, P.vertices_eq_extremePoints,
    show (a • φ ·) = (a • ·) ∘ φ by rfl, Set.image_comp, isom_image_extremePoints,
    smul_image_extremePoints apos.ne']
  congr

lemma exists_similar_flag (F : P.Flag) (e : E n ≃ᵃ[ℝ] E n) (hQ : Q.toSet = e '' P.toSet) :
    ∃ G : Q.Flag, ∀ k, G.face k = e '' F.face k := by
  refine ⟨⟨fun k ↦ e '' F.face k, fun k ↦ ?_, fun k ↦ ?_, fun i j hij ↦ ?_⟩, fun _ ↦ rfl⟩
  · refine ⟨?_, (F.isFace k).2.image e⟩
    rw [hQ]
    exact (F.isFace k).1.image_affineEquiv e
  · rw [faceDim_image_affineEquiv, F.dim_eq]
  · exact image_ssubset_of_inj e.injective (F.strict_mono i j hij)

lemma Similar.isRegular (hs : P.Similar Q) (rP : P.IsRegular) : Q.IsRegular := by
  obtain ⟨a, apos, φ, hQ⟩ := hs
  have ha : a ≠ 0 := apos.ne'
  let A : E n ≃ₗ[ℝ] E n := LinearEquiv.smulOfUnit ⟨a, a⁻¹, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha⟩
  let e : E n ≃ᵃ[ℝ] E n := φ.toAffineEquiv.trans A.toAffineEquiv
  have he : Q.toSet = e '' P.toSet := by rw [hQ, Set.image_image]; rfl
  refine ⟨?_, fun G₁ G₂ ↦ ?_⟩
  · change faceDim Q.toSet = n
    rw [he, faceDim_image_affineEquiv]
    exact rP.1
  · have he' : P.toSet = e.symm '' Q.toSet := by simp [he, Set.image_image]
    obtain ⟨F₁, hF₁⟩ := exists_similar_flag G₁ e.symm he'
    obtain ⟨F₂, hF₂⟩ := exists_similar_flag G₂ e.symm he'
    obtain ⟨T, sT, hT⟩ := rP.2 F₁ F₂
    let U := (φ * T * φ⁻¹).conj (inv_ne_zero ha)
    have hU (x) : U (e x) = e (T x) := by
      apply (smul_right_inj (inv_ne_zero ha)).mp
      rw [Isom.smul_conj]
      change (φ * T * φ⁻¹) (a⁻¹ • (a • φ x)) = a⁻¹ • (a • φ (T x))
      simp [inv_smul_smul₀ ha]
    refine ⟨U, ?_, fun k ↦ ?_⟩
    · unfold isSymmetry at sT ⊢
      rw [he, ← Set.image_image]
      simpa only [Set.image_image, hU] using congr(e '' $sT)
    · have hG₁ : G₁.face k = e '' F₁.face k := by rw [hF₁, Set.image_image]; simp
      have hG₂ : G₂.face k = e '' F₂.face k := by rw [hF₂, Set.image_image]; simp
      rw [hG₁, hG₂, Set.image_image]
      change (fun x ↦ U (e x)) '' F₁.face k = e '' F₂.face k
      simp_rw [hU, ← Set.image_image, hT]

end LeanEval.Geometry.PlatonicClassification.ConvexPolytope

/-- The 2×2 matrix expressing a rotation by `θ`. -/
def rotate2D (θ : ℝ) : orthogonalGroup (Fin 2) ℝ where
  val := !![cos θ, -sin θ; sin θ, cos θ]
  property := by
    rw [mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [mul_apply] <;> grind [sin_sq_add_cos_sq]

/-- The 2×2 matrix expressing a reflection about the line with angle `θ / 2`. -/
def reflect2D (θ : ℝ) : orthogonalGroup (Fin 2) ℝ where
  val := !![cos θ, sin θ; sin θ, -cos θ]
  property := by
    rw [mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [mul_apply] <;> grind [sin_sq_add_cos_sq]

/-- The n×n matrix permuting the coordinates according to the permutation `σ`
(where the `i`-th coordinate of `R *ᵥ v` is `v (σ i)`). -/
def coordPerm (σ : Equiv.Perm (Fin n)) : orthogonalGroup (Fin n) ℝ where
  val := σ.permMatrix ℝ
  property := by
    rw [mem_orthogonalGroup_iff, transpose_permMatrix, ← permMatrix_mul, inv_mul_cancel,
      permMatrix_one]

/-- The n×n matrix flipping the coordinate axes according to the sign function `s`.
`false` gives a `+1` and `true` a `-1`. -/
def coordFlip (m : Fin n → Bool) : orthogonalGroup (Fin n) ℝ where
  val := diagonal fun i ↦ if m i then -1 else 1
  property := by
    simp_rw [mem_orthogonalGroup_iff, diagonal_transpose, diagonal_mul_diagonal, ← sq]
    simp
