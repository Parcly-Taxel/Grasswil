import Submission.LowerBounds.C24
import Submission.LowerBounds.Dodecahedron
import Submission.LowerBounds.Hypercube
import Submission.LowerBounds.Simplex
import Submission.LowerBounds.Two

open Finset LeanEval.Geometry.PlatonicClassification ConvexPolytope

theorem platonicCount_two : platonicCount 2 = ⊤ := by
  rw [platonicCount, Set.encard_eq_top_iff]
  let P (n : ℕ) : regularPolytopes 2 := ⟨_, regularPolygon_isRegular (Nat.le_add_left 3 n)⟩
  let f (n : ℕ) : Set (regularPolytopes 2) := {Q | regularSimilar 2 (P n) Q}
  refine Set.infinite_of_injective_forall_mem (fun p q e ↦ ?_) (fun n ↦ by exact ⟨P n, rfl⟩)
  rw [Set.ext_iff] at e
  specialize e (P p)
  simp_rw [Set.mem_ofPred, regularSimilar, P, similar_refl, true_iff] at e
  have key := e.card_vertices_eq
  simp_rw [regularPolygon, card_image_of_injective _ injective_polygonVert, card_fin] at key
  lia

lemma platonicCount_ge_of_examples {n k : ℕ} (f : Fin k → regularPolytopes n)
    (hf : (fun i ↦ #(f i).1.vertices).Injective) : k ≤ platonicCount n := by
  let g (i) : Set (regularPolytopes n) := {Q | regularSimilar n (f i) Q}
  have injg : g.Injective := fun i j e ↦ by
    have key : f j ∈ g j := similar_refl
    simp_rw [← e, g, Set.mem_ofPred] at key
    exact hf key.card_vertices_eq
  have cg : (Set.range g).encard = k := by
    rw [Set.encard_eq_coe_toFinset_card, Set.toFinset_range, Nat.cast_inj,
      card_image_of_injective _ injg, card_fin]
  rw [← cg]
  apply Set.encard_le_encard
  rintro _ ⟨i, rfl⟩
  exact ⟨f i, rfl⟩

theorem platonicCount_ge {n : ℕ} (hn : 3 ≤ n) : 3 ≤ platonicCount n := by
  have nzn : NeZero n := ⟨by lia⟩
  let f : Fin 3 → regularPolytopes n :=
    ![⟨_, simplex_isRegular⟩, ⟨_, orthoplex_isRegular⟩, ⟨_, hypercube_isRegular⟩]
  apply platonicCount_ge_of_examples f
  let v : Fin 3 → ℕ := ![n + 1, 2 * n, 2 ^ n]
  have e : (fun i ↦ #(f i).1.vertices) = v := by
    ext i; fin_cases i <;> norm_num [f, v]
    · rw [simplex, card_image_of_injective _ injective_simplexVert, card_fin]
    · rw [orthoplex, card_image_of_injective _ injective_orthoplexVert, card_univ,
        Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, mul_comm]
    · rw [hypercube, card_image_of_injective _ injective_hypercubeVert, card_univ,
        Fintype.card_pi, Fintype.card_bool, prod_const, card_fin]
  simp_rw [e, v]
  apply StrictMono.injective
  simp only [strictMono_vecCons, Matrix.cons_val_zero, Nat.reduceAdd, strictMono_vecEmpty, and_true]
  clear! nzn v
  refine ⟨by lia, ?_⟩
  induction n, hn using Nat.le_induction <;> lia

theorem platonicCount_three_ge : 5 ≤ platonicCount 3 := by
  let f : Fin 5 → regularPolytopes 3 :=
    ![⟨_, simplex_isRegular⟩, ⟨_, orthoplex_isRegular⟩, ⟨_, hypercube_isRegular⟩,
      ⟨_, icosahedron_isRegular⟩, ⟨_, dodecahedron_isRegular⟩]
  apply platonicCount_ge_of_examples f
  let v : Fin 5 → ℕ := ![4, 6, 8, 12, 20]
  have e : (fun i ↦ #(f i).1.vertices) = v := by
    ext i; fin_cases i <;> norm_num [f, v]
    · rw [simplex, card_image_of_injective _ injective_simplexVert, card_fin]
    · rw [orthoplex, card_image_of_injective _ injective_orthoplexVert]
      simp
    · rw [hypercube, card_image_of_injective _ injective_hypercubeVert]
      simp
    · rw [icosahedron, card_image_of_injective _ injective_icosaVert]
      simp
    · have inj : (Real.goldenConj ^ 2 • dodecVert ·).Injective := by
        refine (smul_right_injective (E 3) ?_).comp injective_dodecVert
        exact pow_ne_zero _ Real.goldenConj_neg.ne
      rw [dodecahedron, card_image_of_injective _ inj]
      simp
  simp_rw [e, v]
  apply StrictMono.injective
  simp only [strictMono_vecCons, Matrix.cons_val_zero, Nat.reduceAdd, strictMono_vecEmpty, and_true]
  lia

theorem platonicCount_four_ge : 4 ≤ platonicCount 4 := by
  let f : Fin 4 → regularPolytopes 4 :=
    ![⟨_, simplex_isRegular⟩, ⟨_, orthoplex_isRegular⟩, ⟨_, hypercube_isRegular⟩,
      ⟨_, cell24_isRegular⟩]
  apply platonicCount_ge_of_examples f
  let v : Fin 4 → ℕ := ![5, 8, 16, 24]
  have e : (fun i ↦ #(f i).1.vertices) = v := by
    ext i; fin_cases i <;> norm_num [f, v]
    · rw [simplex, card_image_of_injective _ injective_simplexVert, card_fin]
    · rw [orthoplex, card_image_of_injective _ injective_orthoplexVert]
      simp
    · rw [hypercube, card_image_of_injective _ injective_hypercubeVert]
      simp
    · exact card_cell24_vertices
  simp_rw [e, v]
  apply StrictMono.injective
  simp only [strictMono_vecCons, Matrix.cons_val_zero, Nat.reduceAdd, strictMono_vecEmpty, and_true]
  lia
