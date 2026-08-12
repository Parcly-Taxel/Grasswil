import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Topology.Algebra.Module.FiniteDimension

variable {𝕜 : Type*} [TopologicalSpace 𝕜] [AddCommGroup 𝕜] [Module ℝ 𝕜]
  {L : StrongDual ℝ 𝕜} {c : ℝ} {A B C : Set 𝕜} {x : 𝕜}

lemma dual_le_of_mem_convexHull (LA : ∀ v ∈ A, L v ≤ c) (mx : x ∈ convexHull ℝ A) : L x ≤ c := by
  by_contra contra
  rw [mem_convexHull_iff] at mx
  exact contra (mx {y | L y ≤ c} LA (convex_halfSpace_le ⟨by simp, by simp⟩ _))

/-- Extract parameters defining a nonempty exposed subset. -/
lemma IsExposed.exists_dual_eq (hB : IsExposed ℝ A B) (nB : B.Nonempty) :
    ∃ (L : StrongDual ℝ 𝕜) (c : ℝ), (∀ v ∈ A, L v ≤ c) ∧ B = {v ∈ A | L v = c} := by
  obtain ⟨L, rfl⟩ := hB nB
  obtain ⟨w, mw⟩ := nB
  refine ⟨L, L w, mw.2, ?_⟩
  ext x
  simp_rw [Set.mem_ofPred, and_congr_right_iff]
  exact fun mx ↦ ⟨fun maxx ↦ le_antisymm (mw.2 x mx) (maxx w mw.1),
    fun Lx y my ↦ (mw.2 y my).trans_eq Lx.symm⟩

lemma IsExposed.inter_subset (hC : IsExposed ℝ A C) (sB : B ⊆ A) : IsExposed ℝ B (C ∩ B) := by
  intro ⟨z, zC, zB⟩
  obtain ⟨K, rfl⟩ := hC ⟨z, zC⟩
  refine ⟨K, ?_⟩
  ext x
  simp_rw [Set.mem_inter_iff, and_comm, Set.mem_ofPred, and_congr_right_iff]
  exact fun xB ↦ ⟨fun maxx y yB ↦ maxx.2 y (sB yB),
    fun maxy ↦ ⟨sB xB, fun y yA ↦ (zC.2 y yA).trans (maxy z zB)⟩⟩

open Finset in
/-- If a linear functional `L` is `≤ c` on a finset `s`
and `x` in the convex hull of `s` satisfies `L x = c`,
`x` is in any convex set `A` containing all `v ∈ s` where `L v = c`. -/
lemma mem_convex_of_dual_max {s : Finset 𝕜} (Ls : ∀ v ∈ s, L v ≤ c) (Lm : ∀ v ∈ s, L v = c → v ∈ A)
    (cvA : Convex ℝ A) (mx : x ∈ convexHull ℝ s) (Lx : L x = c) : x ∈ A := by
  rw [mem_convexHull'] at mx
  obtain ⟨w, nw, sw, rfl⟩ := mx
  have toA (v) (mv : v ∈ s) (hv : 0 < w v) : v ∈ A := by
    apply Lm v mv
    have wcL : ∑ v ∈ s, w v • (c - L v) = 0 := by simp_all [mul_sub, ← sum_mul]
    contrapose! wcL
    refine (sum_pos' (fun a ma ↦ smul_nonneg (nw a ma) ?_) ⟨v, mv, smul_pos hv ?_⟩).ne'
    · exact sub_nonneg.mpr (Ls a ma)
    · exact sub_pos.mpr ((Ls v mv).lt_of_ne wcL)
  replace cvA : ∑ v ∈ s with 0 < w v, w v • v ∈ A := by
    refine cvA.sum_mem (fun v mv ↦ ?_) ?_ (fun v mv ↦ ?_)
    · rw [mem_filter] at mv
      exact mv.2.le
    · rw [← sw]
      exact sum_filter_of_ne fun a ma na ↦ (nw a ma).lt_of_ne na.symm
    · rw [mem_filter] at mv
      exact toA _ mv.1 mv.2
  convert ← cvA using 1
  refine sum_filter_of_ne fun v mv nv ↦ ?_
  rw [smul_ne_zero_iff] at nv
  exact (nw v mv).lt_of_ne nv.1.symm

lemma dual_eq_of_mem_spanPoints (LA : ∀ v ∈ A, L v = c) (mx : x ∈ spanPoints ℝ A) : L x = c := by
  obtain ⟨z, mz, w, hw, rfl⟩ := mx
  rw [vadd_eq_add, map_add, LA z mz, add_eq_right]
  induction hw using Submodule.span_induction with
  | mem v mv =>
    obtain ⟨a, ma, b, mb, rfl⟩ := mv
    simp [LA a ma, LA b mb]
  | zero => exact L.map_zero
  | add a ma b mb ha hb => simp [ha, hb]
  | smul k v mv hv => simp [hv, L.map_smul]

/-- Proposition 2.3(iv) in Ziegler's _Lectures on Polytopes_. -/
lemma IsExposed.eq_inter_spanPoints (hB : IsExposed ℝ A B) : B = A ∩ spanPoints ℝ B := by
  obtain rfl | nB := B.eq_empty_or_nonempty
  · simp [spanPoints]
  · obtain ⟨L, c, LA, rfl⟩ := hB.exists_dual_eq nB
    ext v
    rw [Set.mem_ofPred, Set.mem_inter_iff, and_congr_right_iff]
    exact fun mv ↦ ⟨fun Lv ↦ subset_spanPoints ℝ _ ⟨mv, Lv⟩,
      fun mvs ↦ dual_eq_of_mem_spanPoints (fun a ma ↦ ma.2) mvs⟩

variable [IsTopologicalAddGroup 𝕜] [ContinuousSMul ℝ 𝕜] [T2Space 𝕜] [FiniteDimensional ℝ 𝕜]

lemma IsExposed.image_affineEquiv (h : IsExposed ℝ A B) (e : 𝕜 ≃ᵃ[ℝ] 𝕜) :
    IsExposed ℝ (e '' A) (e '' B) := by
  rintro ⟨_, b, hbB, rfl⟩
  obtain ⟨L, rfl⟩ := h ⟨b, hbB⟩
  let M := L.comp e.linear.symm.toContinuousLinearMap
  refine ⟨M, ?_⟩
  have dM (x) : M (e x) = L x + M (e 0) := by
    have he : e.linear (x - 0) = e x - e 0 := AffineMap.linearMap_vsub e.toAffineMap ..
    rw [← LinearEquiv.eq_symm_apply, sub_zero, map_sub, eq_sub_iff_add_eq] at he
    change L (e.linear.symm (e x)) = L x + L (e.linear.symm (e 0))
    rw [← he, map_add]
  have hM (x y) : M (e y) ≤ M (e x) ↔ L y ≤ L x := by rw [dM x, dM y, add_le_add_iff_right]
  ext x
  simp_rw [Set.mem_image, Set.mem_ofPred]
  conv_lhs => enter [1, y]; rw [and_right_comm]
  rw [← exists_and_right]
  refine exists_congr fun y ↦ and_congr_right fun ⟨my, rfl⟩ ↦ ?_
  simp_rw [forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, hM]
