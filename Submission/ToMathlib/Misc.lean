import Mathlib.LinearAlgebra.Matrix.Notation

lemma image_ssubset_of_inj {α β : Type*} {e : α → β} (hinj : e.Injective)
    {s t : Set α} (h : s ⊂ t) : e '' s ⊂ e '' t := by
  rw [Set.ssubset_iff_subset_ne] at h ⊢
  exact ⟨Set.image_mono h.1, fun hc ↦ h.2 (hinj.image_injective hc)⟩

namespace Matrix

lemma transpose_fin_three {α : Type*} (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ : α) :
    !![a₁₁, a₁₂, a₁₃; a₂₁, a₂₂, a₂₃; a₃₁, a₃₂, a₃₃]ᵀ =
    !![a₁₁, a₂₁, a₃₁; a₁₂, a₂₂, a₃₂; a₁₃, a₂₃, a₃₃] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma mulVec_fin_three {R : Type*} [Semiring R] (m : Matrix (Fin 3) (Fin 3) R) (v : Fin 3 → R) :
    m *ᵥ v = ![m 0 0 * v 0 + m 0 1 * v 1 + m 0 2 * v 2,
               m 1 0 * v 0 + m 1 1 * v 1 + m 1 2 * v 2,
               m 2 0 * v 0 + m 2 1 * v 1 + m 2 2 * v 2] := by
  ext i
  fin_cases i <;> simp [mulVec_eq_sum, Fin.sum_univ_three]

lemma mul_transpose_orthogonal_right {n R : Type*} [Fintype n] [DecidableEq n] [CommSemiring R]
    {M O : Matrix n n R} (hO : Oᵀ * O = 1) : (M * Oᵀ) * (M * Oᵀ)ᵀ = M * Mᵀ := by
  rw [transpose_mul, transpose_transpose, mul_assoc, ← mul_assoc Oᵀ O Mᵀ, hO, one_mul]

end Matrix
