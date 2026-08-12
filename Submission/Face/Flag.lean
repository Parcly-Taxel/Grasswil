import Submission.Face.Lattice

open Set LeanEval.Geometry.PlatonicClassification ConvexPolytope

variable {n : ℕ} {P : ConvexPolytope n} {f : Set (E n)}

lemma exists_lower_flag (hf : P.IsFace f) : ∃ d : ℕ → Set (E n),
    d (faceDim f) = f ∧ (∀ i ≤ faceDim f, P.IsFace (d i) ∧ faceDim (d i) = i) ∧
    StrictMonoOn d (Iic (faceDim f)) := by
  induction df : faceDim f generalizing f with
  | zero => exact ⟨fun _ ↦ f, rfl, by simp_all, fun _ ↦ by simp⟩
  | succ m ih =>
    obtain ⟨g, sg, hg, dg⟩ := exists_subface hf (by lia)
    obtain ⟨d, rfl, ih₁, ih₂⟩ := ih hg (by lia)
    refine ⟨fun i ↦ if i < faceDim f then d i else f, by simp [df], fun i li ↦ ?_, ?_⟩
    · dsimp only
      split_ifs with hi
      · exact ih₁ i (by lia)
      · exact ⟨hf, by lia⟩
    · rintro i - j (lj : j ≤ _) li
      simp_rw [df, li.trans_le lj, ite_true]
      split_ifs with hj
      · exact ih₂ (by rw [mem_Iic]; lia) (by rw [mem_Iic]; lia) li
      · suffices d i ≤ d m from this.trans_lt sg
        exact ih₂.monotoneOn (by rw [mem_Iic]; lia) (by simp) (by lia)

lemma exists_upper_flag (hf : P.IsFace f) : ∃ u : ℕ → Set (E n),
    u (faceDim f) = f ∧ (∀ k ≥ faceDim f, k ≤ P.dim → P.IsFace (u k) ∧ faceDim (u k) = k) ∧
    StrictMonoOn u (Icc (faceDim f) P.dim) := by
  induction df : P.dim - faceDim f generalizing f with
  | zero =>
    replace df : P.dim = faceDim f := by
      rw [Nat.sub_eq_zero_iff_le] at df
      exact le_antisymm df (Submodule.finrank_mono (vectorSpan_mono ℝ hf.1.subset))
    simp_rw [df, Icc_self, strictMonoOn_singleton, and_true]
    exact ⟨fun _ ↦ f, rfl, by lia⟩
  | succ m ih =>
    obtain ⟨g, sg, hg, dg⟩ := exists_superface hf (by lia)
    obtain ⟨u, ih₀, ih₁, ih₂⟩ := ih hg (by lia)
    refine ⟨fun i ↦ if i ≤ faceDim f then f else u i, by simp, fun i gi li ↦ ?_, ?_⟩
    · dsimp only
      split_ifs with hi
      · exact ⟨hf, by lia⟩
      · exact ih₁ i (by lia) li
    · rintro i ⟨gi, -⟩ j ⟨-, lj⟩ li
      simp_rw [show ¬j ≤ faceDim f by lia, ite_false]
      split_ifs with hi
      · apply sg.trans_le
        rw [← ih₀]
        exact ih₂.monotoneOn (by rw [mem_Icc]; lia) (by rw [mem_Icc]; lia) (by lia)
      · exact ih₂ ⟨by lia, by lia⟩ ⟨by lia, lj⟩ li

/-- Every face of a convex polytope is part of some flag.
Theorem 2.7(i) in Ziegler's _Lectures on Polytopes_. -/
theorem exists_flag_with_face (hf : P.IsFace f) : ∃ c : ℕ → Set (E n),
    c (faceDim f) = f ∧ (∀ i ≤ P.dim, P.IsFace (c i) ∧ faceDim (c i) = i) ∧
    StrictMonoOn c (Iic P.dim) := by
  obtain ⟨d, dself, hd, smd⟩ := exists_lower_flag hf
  obtain ⟨u, uself, hu, smu⟩ := exists_upper_flag hf
  refine ⟨fun k ↦ if k ≤ faceDim f then d k else u k, by simp [dself], fun i li ↦ ?_, ?_⟩
  · dsimp only
    split_ifs with hi
    · exact hd i hi
    · exact hu i (not_le.mp hi).le li
  · rintro i - j (lj : j ≤ _) li
    by_cases lj' : j ≤ faceDim f
    · simp_rw [lj', show i ≤ faceDim f by lia, ite_true]
      exact smd (li.le.trans lj') lj' li
    · simp_rw [lj', ite_false]
      by_cases li' : i ≤ faceDim f
      · simp_rw [li', ite_true]
        rw [not_le] at lj'
        apply (smu (by rw [mem_Icc]; lia) (by rw [mem_Icc]; lia) lj').trans_le'
        rw [uself, ← dself]
        exact smd.monotoneOn li' self_mem_Iic li'
      · simp_rw [li', ite_false]
        exact smu (by rw [mem_Icc]; lia) (by rw [mem_Icc]; lia) li

/-- Every proper face of a full-dimensional polytope is part of some `Flag`. -/
theorem exists_proper_flag_with_face (dP : P.IsFullDim) (hf : P.IsFace f)
    {i : Fin n} (df : faceDim f = i) : ∃ F : P.Flag, F.face i = f := by
  rw [IsFullDim] at dP
  obtain ⟨c, cself, hc, smc⟩ := exists_flag_with_face hf
  rw [dP] at hc smc
  exact ⟨⟨fun i ↦ c i.1, fun i ↦ (hc _ (by simp)).1, fun i ↦ (hc _ (by simp)).2,
    fun i j ↦ smc (by simp) (by simp)⟩, by simp [← df, cself]⟩

theorem flag_nonempty_of_isFullDim (dP : P.IsFullDim) : Nonempty P.Flag := by
  obtain rfl | nzn := eq_zero_or_neZero n
  · exact ⟨fun _ ↦ ∅, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i _ _ ↦ i.elim0⟩
  · exact ⟨(exists_proper_flag_with_face dP
      ⟨vertex_isExposed P.vertices_nonempty.choose_spec, by simp⟩
      (i := 0) (by simp [faceDim])).choose⟩

namespace LeanEval.Geometry.PlatonicClassification.ConvexPolytope

/-- An arbitrary `Flag` of a full-dimensional polytope. -/
noncomputable def IsFullDim.flag (dP : P.IsFullDim) : P.Flag :=
  (flag_nonempty_of_isFullDim dP).some

end LeanEval.Geometry.PlatonicClassification.ConvexPolytope

/-- Substitute the vertex face of a flag with another one in the `i`-dimensional face. -/
lemma exists_substitute_vertex_flag
    {F : P.Flag} {i : Fin n} {v : E n} (mv : v ∈ faceGens (F.isFace i).1) :
    ∃ G : P.Flag, (∀ j ≥ i, F.face j = G.face j) ∧ G.face ⟨0, i.pos⟩ = {v} := by
  let Q := (F.isFace i).toPolytope
  change v ∈ Q.vertices at mv
  obtain ⟨d, dself, hd, smd⟩ := exists_flag_with_face ⟨vertex_isExposed mv, by simp⟩
  rw [faceDim, vectorSpan_singleton, finrank_bot] at dself
  have eQ : Q.toSet = F.face i := by rw [IsFace.toSet_toPolytope]
  have dQ : Q.dim = i := by
    rw [dim, eQ]
    exact F.dim_eq i
  rw [dQ] at hd smd
  refine ⟨⟨fun j ↦ if i ≤ j.1 then F.face j else d j.1, fun j ↦ ?_, fun j ↦ ?_, fun j k l ↦ ?_⟩,
    fun j hj ↦ by simp [hj], ?_⟩
  · split_ifs with h
    · exact F.isFace j
    · obtain ⟨l₁, l₂⟩ := (hd j (by lia)).1
      rw [eQ] at l₁
      exact ⟨(F.isFace i).1.trans_polytope l₁, l₂⟩
  · split_ifs with h
    · exact F.dim_eq j
    · exact (hd j (by lia)).2
  · split_ifs with hj hk hk
    · exact F.strict_mono _ _ l
    · lia
    · have dss : d j ⊂ F.face i := by
        rw [← eQ]
        refine ssubset_iff_subset_ne.mpr ⟨(hd _ (by lia)).1.1.subset, ?_⟩
        by_contra contra
        replace contra := congr(faceDim $contra)
        rw [(hd _ (by lia)).2, eQ, F.dim_eq] at contra
        exact hj contra.symm.le
      exact dss.trans_subset (F.mono (by lia))
    · exact smd (by rw [mem_Iic]; lia) (by rw [mem_Iic]; lia) l
  · simp only [nonpos_iff_eq_zero]
    split_ifs with h
    · rw [h, dim_eq_zero_iff_card_vertices, Finset.card_eq_one] at dQ
      obtain ⟨w, hv⟩ := dQ
      rw [hv, Finset.mem_singleton] at mv
      subst w
      rw [← convexHull_singleton (𝕜 := ℝ), ← Finset.coe_singleton, ← hv]
      change _ = Q.toSet
      simp_rw [← h, eQ]
    · exact dself

lemma card_substitute_faces_eq_two (dP : P.IsFullDim) (F : P.Flag) (i : Fin n) :
    {s | P.IsFace s ∧ faceDim s = i.1 ∧
      (∀ j < i, F.face j ⊂ s) ∧ ∀ j > i, s ⊂ F.face j}.ncard = 2 := by
  by_cases hi : i.1 = 0
  · rcases n with _ | _ | n
    · exact i.elim0
    · change faceDim P.toSet = 1 at dP
      have hP : P.IsFace P.toSet := ⟨IsExposed.refl _, by simp [toSet, P.vertices_nonempty]⟩
      simp_all only [Nat.reduceAdd, Fin.val_eq_zero, isEmpty_Prop, not_lt, le_of_subsingleton,
        IsEmpty.forall_iff, implies_true, and_true]
      convert card_faces_strict_below_dim_one_eq_two hP dP using 4 with f
      refine and_congr_right fun hf ↦ ⟨fun df ↦ ?_, fun sf ↦ ?_⟩
      · exact ssubset_iff_subset_ne.mpr ⟨hf.1.subset, by lia⟩
      · have := faceDim_strictMono hf hP sf
        lia
    · let one : Fin (n + 1 + 1) := ⟨1, by lia⟩
      simp_all only [Fin.val_eq_zero_iff, Fin.coe_ofNat_eq_mod, Nat.zero_mod, not_lt_zero,
        IsEmpty.forall_iff, implies_true, true_and]
      convert card_faces_strict_below_dim_one_eq_two (F.isFace one) (F.dim_eq one) using 4 with f
      refine and_congr_right fun hf ↦ ⟨fun h ↦ h.2 _ (by simp [one]), fun sf ↦ ⟨?_, fun j gj ↦ ?_⟩⟩
      · have := faceDim_strictMono hf (F.isFace one) sf
        rw [F.dim_eq] at this
        lia
      · replace gj := Fin.one_le_of_ne_zero gj.ne'
        obtain hj | hj := gj.eq_or_lt
        · rwa [← hj]
        · exact sf.trans (F.strict_mono _ _ hj)
  · let lbf := F.face ⟨i.1 - 1, by lia⟩
    let ubf := if h : i.1 + 1 < n then F.face ⟨i.1 + 1, h⟩ else P.toSet
    have hubf : P.IsFace ubf := by
      simp_rw [ubf]
      split_ifs with h
      · exact F.isFace _
      · exact ⟨IsExposed.refl _, by simp [toSet, P.vertices_nonempty]⟩
    have slu : lbf ⊂ ubf := by
      simp_rw [ubf]
      split_ifs with h
      · exact F.strict_mono _ _ (by simp)
      · refine ssubset_iff_subset_ne.mpr ⟨(F.isFace _).1.subset, ?_⟩
        by_contra contra
        replace contra := congr(faceDim $contra)
        rw [F.dim_eq, show faceDim P.toSet = n from dP] at contra
        lia
    have dubf : faceDim ubf = i.1 + 1 := by
      simp_rw [ubf]
      split_ifs with h
      · rw [F.dim_eq]
      · rwa [show i.1 + 1 = n by lia]
    have key := card_faces_strict_between_eq_two (F.isFace ⟨i.1 - 1, by lia⟩) hubf slu
      (by rw [F.dim_eq]; lia)
    convert key using 4 with f
    refine and_congr_right fun hf ↦ ⟨fun ⟨df, sf₁, sf₂⟩ ↦ ?_,
      fun ⟨sf₁, sf₂⟩ ↦ ⟨?_, fun j lj ↦ ?_, fun j gj ↦ ?_⟩⟩
    · refine ⟨sf₁ _ (by rw [Fin.lt_def]; lia), ?_⟩
      simp_rw [ubf]
      split_ifs with h
      · exact sf₂ _ (by rw [gt_iff_lt, Fin.lt_def]; lia)
      · refine ssubset_iff_subset_ne.mpr ⟨hf.1.subset, ?_⟩
        by_contra contra
        replace contra := congr(faceDim $contra)
        rw [df, show faceDim P.toSet = n from dP] at contra
        lia
    · have lb := faceDim_strictMono (F.isFace _) hf sf₁
      have ub := faceDim_strictMono hf hubf sf₂
      rw [F.dim_eq] at lb
      lia
    · replace lj : j ≤ ⟨i.1 - 1, by lia⟩ := by rw [Fin.le_def]; lia
      obtain hj | hj := lj.eq_or_lt
      · rwa [hj]
      · exact (F.strict_mono _ _ hj).trans sf₁
    · have il : i.1 + 1 < n := by lia
      simp_rw [ubf, il, dite_true] at sf₂
      replace gj : ⟨i.1 + 1, il⟩ ≤ j := by rw [Fin.le_def]; lia
      obtain hj | hj := gj.eq_or_lt
      · rwa [← hj]
      · exact sf₂.trans (F.strict_mono _ _ hj)

lemma existsUnique_substitute_face (dP : P.IsFullDim) (F : P.Flag) (i : Fin n) :
    ∃! s ≠ F.face i, P.IsFace s ∧ faceDim s = i.1 ∧
      (∀ j < i, F.face j ⊂ s) ∧ ∀ j > i, s ⊂ F.face j := by
  obtain ⟨a, b, hn, key⟩ := ncard_eq_two.mp (card_substitute_faces_eq_two dP F i)
  obtain ha | hb : F.face i = a ∨ F.face i = b :=
    key.subset ⟨F.isFace i, F.dim_eq i,
      fun j hj ↦ F.strict_mono j i hj, fun j hj ↦ F.strict_mono i j hj⟩
  all_goals simp_rw [Set.ext_iff, mem_ofPred, mem_insert_iff, mem_singleton_iff] at key
  · exact ⟨b, ⟨ha ▸ hn.symm, by specialize key b; tauto⟩, fun c hc ↦ by grind⟩
  · exact ⟨a, ⟨hb.symm ▸ hn, by specialize key a; tauto⟩, fun c hc ↦ by grind⟩

/-- For every dimension of a flag `F` of a full-dimensional polytope
there is a unique flag differing from `F` exactly in the face of that dimension. -/
theorem existsUnique_modified_flag (dP : P.IsFullDim) (F : P.Flag) (i : Fin n) :
    ∃! G : P.Flag, ∀ j, i ≠ j ↔ F.face j = G.face j := by
  obtain ⟨g, ⟨ng, hg, dg, subg, supg⟩, ug⟩ := existsUnique_substitute_face dP F i
  refine ⟨⟨Function.update F.face i g, fun j ↦ ?_, fun j ↦ ?_, fun j k l ↦ ?_⟩,
    fun j ↦ ?_, fun G hG ↦ ?_⟩
  · by_cases! hj : i = j
    · simp [hj, hg]
    · rw [Function.update_of_ne hj.symm]
      exact F.isFace j
  · by_cases! hj : i = j
    · simp [hj, dg]
    · rw [Function.update_of_ne hj.symm]
      exact F.dim_eq j
  · by_cases hj : j = i
    · rw [hj, Function.update_self, Function.update_of_ne (hj ▸ l).ne']
      exact supg k (hj ▸ l)
    rw [Function.update_of_ne hj]
    by_cases hk : k = i
    · rw [hk, Function.update_self]
      exact subg j (hk ▸ l)
    rw [Function.update_of_ne hk]
    exact F.strict_mono _ _ l
  · by_cases! hj : i = j
    · simp_rw [Ne, hj, not_true_eq_false, Function.update_self, ← hj, ng.symm]
    · simp_rw [Ne, hj, not_false_eq_true, true_iff, Function.update_of_ne hj.symm g F.face]
  · have hG' (j) (hj : j ≠ i) : G.face j = F.face j := ((hG j).1 hj.symm).symm
    ext j v
    by_cases hj : j = i
    · simp_rw [hj, Function.update_self]
      congr!
      exact ug (G.face i) ⟨by grind, G.isFace i, G.dim_eq i,
        fun j hj ↦ hG' j hj.ne ▸ G.strict_mono j i hj,
        fun j hj ↦ hG' j hj.ne' ▸ G.strict_mono i j hj⟩
    · simp [hj, hG']
