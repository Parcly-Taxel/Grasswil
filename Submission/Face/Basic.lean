import ChallengeDeps

open Set Finset LeanEval.Geometry.PlatonicClassification ConvexPolytope

variable {n : ℕ} {P : ConvexPolytope n} {s s' : Set (E n)}
  (es : IsExposed ℝ P.toSet s) (es' : IsExposed ℝ P.toSet s')

lemma self_eq_exch_of_subset {g : Finset (E n)} (sg : g ⊆ P.vertices) :
    SetLike.coe g = extremePoints ℝ (convexHull ℝ g) := by
  refine subset_antisymm ?_ (extremePoints_convexHull_subset ..)
  have key := inter_extremePoints_subset_extremePoints_of_subset (𝕜 := ℝ)
    (convexHull_mono (𝕜 := ℝ) sg)
  rw [← P.vertices_eq_extremePoints] at key
  exact (subset_inter (subset_convexHull ℝ _) sg).trans key

include es in
/-- For every face of a convex polytope there exists a subset of its vertices
that constitutes its convex hull. -/
lemma exists_faceGens : ∃ g ⊆ P.vertices, s = convexHull ℝ g := by
  have km : closure (convexHull ℝ (extremePoints ℝ s)) = s := by
    apply closure_convexHull_extremePoints
    · have cp := P.vertices.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
      exact cp.of_isClosed_subset (es.isClosed cp.isClosed) es.subset
    · exact es.convex (convex_convexHull ℝ _)
  have se : extremePoints ℝ s ⊆ P.vertices := by
    rw [P.vertices_eq_extremePoints]
    exact es.isExtreme.extremePoints_subset_extremePoints
  lift extremePoints ℝ s to Finset (E n) using P.vertices.finite_toSet.subset se with f
  refine ⟨f, coe_subset.mp se, ?_⟩
  rw [← km]
  exact f.finite_toSet.isClosed_convexHull (𝕜 := ℝ).closure_eq

include es in
/-- The subset in `exists_faceGens` is unique. -/
lemma existsUnique_faceGens : ∃! g ⊆ P.vertices, s = convexHull ℝ g := by
  apply existsUnique_of_exists_of_unique (exists_faceGens es)
  rintro g g' ⟨sg, eg⟩ ⟨sg', eg'⟩
  rw [← coe_inj, self_eq_exch_of_subset sg, ← eg, eg', ← self_eq_exch_of_subset sg']

/-- The subset of polytope points generating this face. -/
noncomputable def faceGens : Finset (E n) :=
  (exists_faceGens es).choose

lemma faceGens_subset_vertices : faceGens es ⊆ P.vertices :=
  (exists_faceGens es).choose_spec.1

lemma convexHull_faceGens : s = convexHull ℝ (faceGens es) :=
  (exists_faceGens es).choose_spec.2

lemma nonempty_faceGens (hs : P.IsFace s) : (faceGens hs.1).Nonempty := by
  have := hs.2
  rwa [convexHull_faceGens hs.1, convexHull_nonempty_iff] at this

lemma faceGens_subset_iff : faceGens es ⊆ faceGens es' ↔ s ⊆ s' := by
  refine ⟨fun h ↦ convexHull_faceGens es ▸ convexHull_faceGens es' ▸ convexHull_mono h, fun h ↦ ?_⟩
  rw [← Finset.coe_subset, self_eq_exch_of_subset (faceGens_subset_vertices es'),
    ← convexHull_faceGens es', self_eq_exch_of_subset (faceGens_subset_vertices es),
    ← convexHull_faceGens es]
  exact (subset_inter (extremePoints_subset.trans h)
    es.isExtreme.extremePoints_subset_extremePoints).trans
      (inter_extremePoints_subset_extremePoints_of_subset es'.subset)

lemma faceGens_eq_iff : faceGens es = faceGens es' ↔ s = s' := by
  simp_rw [subset_antisymm_iff]
  exact Iff.and (faceGens_subset_iff es es') (faceGens_subset_iff es' es)

lemma faceGens_ssubset_iff : faceGens es ⊂ faceGens es' ↔ s ⊂ s' := by
  simp_rw [Set.ssubset_def]
  apply Iff.and (faceGens_subset_iff es es')
  rw [not_iff_not]
  exact faceGens_subset_iff es' es

lemma form_zero_of_mem_vectorSpan {L : StrongDual ℝ (E n)} {v : E n}
    (mv : v ∈ vectorSpan ℝ {x | x ∈ s ∧ ∀ y ∈ s, L y ≤ L x}) : L v = 0 := by
  induction mv using Submodule.span_induction with
  | mem a ma =>
    obtain ⟨x, mx, y, my, rfl⟩ := ma
    simpa [sub_eq_zero] using le_antisymm (my.2 x mx.1) (mx.2 y my.1)
  | zero => simp
  | add a b ma mb ha hb => simp [ha, hb]
  | smul k a ma ha => simp [ha]

lemma faceDim_strictMono (fs : P.IsFace s) (fs' : P.IsFace s') (ss : s ⊂ s') :
    faceDim s < faceDim s' := by
  by_contra! contra
  obtain ⟨x, hx⟩ := fs.2
  obtain ⟨L, rfl⟩ := fs.1 fs.2
  refine ss.2 fun z mz ↦ ⟨fs'.1.subset mz, fun y hy ↦ (hx.2 y hy).trans_eq ?_⟩
  have work := vsub_mem_vectorSpan ℝ (ss.subset hx) mz
  rw [← Submodule.eq_of_le_of_finrank_le (vectorSpan_mono ℝ ss.1) contra] at work
  simpa [sub_eq_zero] using form_zero_of_mem_vectorSpan work

lemma faceDim_mono (fs : P.IsFace s) (fs' : P.IsFace s') (ss : s ⊆ s') :
    faceDim s ≤ faceDim s' := by
  obtain rfl | ss := ss.eq_or_ssubset
  · rfl
  · exact (faceDim_strictMono fs fs' ss).le

namespace LeanEval.Geometry.PlatonicClassification.ConvexPolytope

lemma IsFace.exists_vertex_mem (fs : P.IsFace s) : ∃ v ∈ P.vertices, v ∈ s := by
  have := fs.2
  rw [convexHull_faceGens fs.1, convexHull_nonempty_iff] at this
  obtain ⟨v, hv⟩ := this
  refine ⟨v, faceGens_subset_vertices fs.1 hv, ?_⟩
  rw [convexHull_faceGens fs.1]
  exact subset_convexHull ℝ _ hv

variable (P) in
lemma finite_isFace : {f | P.IsFace f}.Finite := by
  let e (f : {f // P.IsFace f}) : {g // g ⊆ P.vertices} :=
    ⟨faceGens f.2.1, faceGens_subset_vertices f.2.1⟩
  have he : e.Injective := fun f g h ↦ by
    rw [Subtype.ext_iff, ← faceGens_eq_iff f.2.1 g.2.1]
    exact congr(↑$h)
  exact .of_injective e he

variable (P) in
lemma finite_flag : Finite P.Flag := by
  have : Finite {f // P.IsFace f} := finite_coe_iff.mpr (finite_isFace P)
  let e (F : P.Flag) (i) : {f // P.IsFace f} := ⟨_, F.isFace i⟩
  apply Finite.of_injective e
  rintro ⟨ff, fi, fd, fs⟩ ⟨gf, gi, gd, gs⟩ h
  rw [Flag.mk.injEq]
  funext i
  exact congr(↑$(congrFun h i))

end LeanEval.Geometry.PlatonicClassification.ConvexPolytope

/-! ### Characterising faces -/

lemma vectorSpan_convexHull_eq_vectorSpan : vectorSpan ℝ (convexHull ℝ s) = vectorSpan ℝ s := by
  simp_rw [← direction_affineSpan]
  congr 1
  exact ge_antisymm (affineSpan_mono ℝ (subset_convexHull ℝ s))
    (affineSpan_le.mpr (convexHull_min (subset_affineSpan ℝ s) (affineSpan ℝ s).convex))

lemma exists_vertex_separator {v : E n} (mv : v ∈ P.vertices) :
    ∃ (L : StrongDual ℝ (E n)) (c : ℝ),
    (∀ a ∈ convexHull ℝ (P.vertices.erase v), L a < c) ∧ c < L v := by
  have nch : v ∈ extremePoints ℝ P.toSet := by rwa [← mem_coe, P.vertices_eq_extremePoints] at mv
  rw [toSet, (convex_convexHull ℝ _).mem_extremePoints_iff_mem_sdiff_convexHull_sdiff] at nch
  replace nch : v ∉ convexHull ℝ (P.vertices.erase v) := by
    replace nch := nch.2
    contrapose! nch
    refine convexHull_mono (fun w mw ↦ ?_) nch
    rw [mem_coe, mem_erase] at mw
    rw [mem_sdiff, mem_singleton_iff]
    exact ⟨subset_convexHull ℝ _ mw.2, mw.1⟩
  exact geometric_hahn_banach_closed_point
    (convex_convexHull ℝ _) ((finite_toSet _).isClosed_convexHull (𝕜 := ℝ)) nch

lemma vertex_isExposed {v : E n} (mv : v ∈ P.vertices) : IsExposed ℝ P.toSet {v} := by
  obtain ⟨L, c, Lo, Lv⟩ := exists_vertex_separator mv
  replace Lo (x) (mx : x ∈ P.vertices.erase v) : L x < L v :=
    (Lo x (subset_convexHull ℝ _ mx)).trans Lv
  have Le (x) (mx : x ∈ P.vertices) : L x ≤ L v := by
    obtain rfl | nx := eq_or_ne x v; · rfl
    exact (Lo x (mem_erase.mpr ⟨nx, mx⟩)).le
  rintro -
  refine ⟨L, ?_⟩
  suffices ∀ x ∈ P.toSet, L x ≤ L v ∧ (L v ≤ L x → x = v) by
    ext x
    constructor
    · rintro rfl
      exact ⟨subset_convexHull ℝ _ mv, fun y hy ↦ (this y hy).1⟩
    · rintro ⟨mx, hx⟩
      exact (this x mx).2 (hx v (subset_convexHull ℝ _ mv))
  intro x mx
  rw [toSet, mem_convexHull'] at mx
  obtain ⟨w, nnw, sw, rfl⟩ := mx
  simp_rw [map_sum, map_smul, smul_eq_mul]
  have e : ∑ x ∈ P.vertices, w x * L x ≤ L v :=
    calc
      _ ≤ ∑ x ∈ P.vertices, w x * L v :=
        sum_le_sum fun x mx ↦ mul_le_mul_of_nonneg_left (Le _ mx) (nnw _ mx)
      _ = _ := by rw [← sum_mul, sw, one_mul]
  refine ⟨e, fun e' ↦ ?_⟩
  replace e := le_antisymm e e'
  replace e' (x) (mx : x ∈ P.vertices.erase v) : w x = 0 := by
    contrapose! e
    apply ne_of_lt
    calc
      _ < ∑ x ∈ P.vertices, w x * L v := by
        have mx' := mem_erase.mp mx
        refine sum_lt_sum (fun y my ↦ mul_le_mul_of_nonneg_left (Le _ my) (nnw _ my)) ?_
        exact ⟨x, mx'.2, mul_lt_mul_of_pos_left (Lo _ mx) ((nnw _ mx'.2).lt_of_ne e.symm)⟩
      _ = _ := by rw [← sum_mul, sw, one_mul]
  rw [← add_sum_erase _ _ mv] at sw ⊢
  rw [sum_eq_zero e', add_zero] at sw
  rw [sum_eq_zero (fun x mx ↦ by simp [e' _ mx]), add_zero, sw, one_smul]

/-- 0D faces are vertices of the polytope and vice versa. -/
lemma zero_dim_face_iff_vertex : P.IsFace s ∧ faceDim s = 0 ↔ ∃ v ∈ P.vertices, s = {v} := by
  rw [faceDim, Submodule.finrank_eq_zero, vectorSpan_eq_bot_iff_subsingleton]
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨v, rfl⟩ := exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨h₁.2, h₂⟩
    simp_rw [singleton_eq_singleton_iff]
    rw [exists_eq_right', ← mem_coe, P.vertices_eq_extremePoints]
    have ex := h₁.1.isExtreme
    rwa [isExtreme_singleton] at ex
  · obtain ⟨v, hv, rfl⟩ := h
    exact ⟨⟨vertex_isExposed hv, singleton_nonempty _⟩, subsingleton_singleton⟩

/-- 1D faces are edges of the polytope. -/
lemma one_dim_face_is_edge (fs : P.IsFace s) (ds : faceDim s = 1) :
    ∃ v ∈ P.vertices, ∃ w ∈ P.vertices, v ≠ w ∧ s = convexHull ℝ {v, w} := by
  obtain ⟨g, sg, rfl⟩ := exists_faceGens fs.1
  suffices #g = 2 by
    rw [card_eq_two] at this
    obtain ⟨v, w, hn, rfl⟩ := this
    exact ⟨v, sg (by simp), w, sg (by simp), hn, by simp⟩
  rw [faceDim, vectorSpan_convexHull_eq_vectorSpan] at ds
  have cg1 : 1 < #g := by
    contrapose! ds
    rw [card_le_one_iff_subsingleton, ← vectorSpan_eq_bot_iff_subsingleton ℝ] at ds
    rw [ds, Module.finrank_eq_zero_of_subsingleton]
    exact zero_ne_one
  suffices #g ≤ 2 by lia
  contrapose! ds
  rw [two_lt_card] at ds
  obtain ⟨a, ma, b, mb, c, mc, nab, nac, nbc⟩ := ds
  by_cases! col : ¬Collinear ℝ {a, b, c}
  · rw [collinear_iff_finrank_le_one, not_le] at col
    refine (col.trans_le (Submodule.finrank_mono (vectorSpan_mono _ fun d md ↦ ?_))).ne'
    rw [mem_insert_iff, mem_insert_iff, mem_singleton_iff] at md
    rw [mem_coe]
    obtain rfl | rfl | rfl := md <;> assumption
  replace col := col.wbtw_or_wbtw_or_wbtw
  wlog tw : Wbtw ℝ a b c generalizing a b c
  · obtain tw' | tw' := col.resolve_left tw
    · rw [or_rotate] at col
      exact this _ mb _ mc _ ma nbc nab.symm nac.symm col tw'
    · rw [← or_rotate] at col
      exact this _ mc _ ma _ mb nac.symm nbc.symm nab col tw'
  obtain ⟨t, bt, ht⟩ := (sbtw_iff_mem_image_Ioo_and_ne.mp ⟨tw, nab.symm, nbc⟩).1
  have nex : b ∉ extremePoints ℝ P.toSet := by
    rw [mem_extremePoints]
    push Not
    rintro -
    refine ⟨a, subset_convexHull ℝ _ (sg ma), c, subset_convexHull ℝ _ (sg mc), ?_, by tauto⟩
    rw [← ht]
    exact lineMap_mem_openSegment _ _ _ bt
  refine absurd ?_ nex
  rw [toSet, ← P.vertices_eq_extremePoints]
  exact sg mb

lemma dim_ne_zero_iff_card_vertices : P.dim ≠ 0 ↔ 1 < #P.vertices := by
  rw [← not_iff_not, not_ne_iff, not_lt, card_le_one_iff_subsingleton,
    ← vectorSpan_eq_bot_iff_subsingleton ℝ, ← vectorSpan_convexHull_eq_vectorSpan, dim,
    Submodule.finrank_eq_zero, toSet]

lemma dim_eq_zero_iff_card_vertices : P.dim = 0 ↔ #P.vertices = 1 := by
  have := card_pos.mpr P.vertices_nonempty
  rw [← not_iff_not, ← Ne, dim_ne_zero_iff_card_vertices]
  lia

lemma dim_eq_one_iff_card_vertices : P.dim = 1 ↔ #P.vertices = 2 := by
  have nP : P.toSet.Nonempty := convexHull_nonempty_iff.mpr (coe_nonempty.mpr P.vertices_nonempty)
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨v, hv, w, hw, hn, hP⟩ := one_dim_face_is_edge ⟨IsExposed.refl _, nP⟩ h
    have vseq : {v, w} ⊆ P.vertices := by simp [Finset.insert_subset_iff, hv, hw]
    replace vseq : P.vertices = {v, w} := by
      rw [← coe_inj, P.vertices_eq_extremePoints, self_eq_exch_of_subset vseq, coe_pair, ← hP]
      rfl
    rw [vseq, card_pair hn]
  · obtain ⟨v, w, hn, hP⟩ := card_eq_two.mp h
    replace hP : P.toSet = convexHull ℝ {v, w} := by rw [toSet, hP, coe_pair]
    rw [dim, hP, vectorSpan_convexHull_eq_vectorSpan, vectorSpan_pair,
      finrank_span_singleton fun hc ↦ hn (vsub_eq_zero_iff_eq.mp hc)]

lemma dim_ge_two_iff_card_vertices : 2 ≤ P.dim ↔ 3 ≤ #P.vertices := by
  rw [← not_iff_not, not_le, Order.lt_two_iff, Nat.le_one_iff_eq_zero_or_eq_one,
    dim_eq_zero_iff_card_vertices, dim_eq_one_iff_card_vertices]
  have := card_pos.mpr P.vertices_nonempty
  lia

lemma dim_eq_one_face_characterisation (dP : P.dim = 1) :
    ∃ x y, x ≠ y ∧ {f | IsExposed ℝ P.toSet f} = {∅, {x}, {y}, convexHull ℝ {x, y}} := by
  rw [dim_eq_one_iff_card_vertices, card_eq_two] at dP
  obtain ⟨x, y, hn, vP⟩ := dP
  refine ⟨x, y, hn, ?_⟩
  ext f
  simp_rw [mem_ofPred, mem_insert_iff, mem_singleton_iff]
  constructor <;> intro hf
  · rw [convexHull_faceGens hf]
    have sfgen := faceGens_subset_vertices hf
    rw [vP, ← Finset.coe_subset, coe_pair, subset_pair_iff_eq] at sfgen
    exact sfgen.imp (by simp) (Or.imp (by simp) (Or.imp (by simp) (by simp_all)))
  · obtain rfl | rfl | rfl | rfl := hf
    · exact isExposed_empty
    · exact vertex_isExposed (by simp [vP])
    · exact vertex_isExposed (by simp [vP])
    · rw [toSet, vP, coe_pair]

/-! ### Characterising flags -/

namespace LeanEval.Geometry.PlatonicClassification.ConvexPolytope

@[ext]
lemma Flag.ext_face {F G : P.Flag} (h : F.face = G.face) : F = G := by
  cases F; cases G; cases h; rfl

lemma Flag.mono (F : P.Flag) {i j : Fin n} (l : i ≤ j) : F.face i ⊆ F.face j := by
  obtain rfl | h := l.eq_or_lt
  · rfl
  · exact (F.strict_mono _ _ h).subset

end LeanEval.Geometry.PlatonicClassification.ConvexPolytope

lemma Iic_last_eq_univ : (Finset.Iic (Fin.last n)) = Finset.univ := by ext; simp [Fin.le_last]

/-- Given a chain of finsets with cardinalities `1, 2, ..., n`,
there exists an injective function whose prefixes match the chain. -/
lemma exists_chain_sequencing {α : Type*} {f : Fin n → Finset α}
    (cf : ∀ i, #(f i) = i.1 + 1) (sf : ∀ i j, i < j → f i ⊂ f j) :
    ∃ p : Fin n ↪ α, ∀ i, f i = (Finset.Iic i).map p := by
  induction n with
  | zero => simp
  | succ n ih => ?_
  obtain ⟨p, hp⟩ := ih (f := (f ·.castSucc))
    (fun k ↦ by simpa using cf k.castSucc) fun i j l ↦ sf _ _ (by simpa using l)
  obtain ⟨a, ma, na⟩ : ∃ a ∈ f (Fin.last n), a ∉ univ.map p :=
    exists_mem_notMem_of_card_lt_card (by simp [cf])
  refine ⟨Fin.Embedding.snoc (a := a) p (by simpa using na), fun i ↦ ?_⟩
  cases i using Fin.lastCases with
  | cast i =>
    ext v
    simp [hp i, Fin.exists_iff_castSucc]
  | last => ?_
  set q := Fin.Embedding.snoc (a := a) p (by simpa using na)
  have icm : (Finset.Iic (Fin.last n)).map q = (univ.map p).cons a na := by
    ext v
    simp_rw [Iic_last_eq_univ, mem_cons, mem_map, q, Finset.mem_univ, true_and,
      Fin.Embedding.coe_snoc]
    refine ⟨?_, fun h ↦ ?_⟩
    · rw [forall_exists_index]
      intro i hi
      cases i using Fin.lastCases with
      | last =>
        rw [Fin.snoc_last] at hi
        exact .inl hi.symm
      | cast i =>
        rw [Fin.snoc_castSucc] at hi
        exact .inr ⟨_, hi⟩
    · obtain rfl | ⟨i, rfl⟩ := h
      · exact ⟨Fin.last n, by simp⟩
      · exact ⟨i.castSucc, by simp⟩
  rw [icm, eq_comm]
  refine eq_of_subset_of_card_le (fun v hv ↦ ?_) (by simp [cf (Fin.last n)])
  simp_rw [mem_cons, mem_map, Finset.mem_univ, true_and] at hv
  obtain rfl | ⟨i, rfl⟩ := hv
  · exact ma
  · exact (hp i ▸ sf _ _ i.castSucc_lt_last).subset (mem_map.mpr ⟨i, by simp, rfl⟩)

/-- If the faces of a flag of an `n`-polytope have at most `n` vertices, the flag is simplicial
(there exists an injection from `Fin n` to the vertices whose prefixes give the flag's faces). -/
theorem simplicial_flag_of_small_faces (F : P.Flag) (hF : ∀ i, #(faceGens (F.isFace i).1) ≤ n) :
    ∃ p : Fin n ↪ E n, univ.map p ⊆ P.vertices ∧
      ∀ i, F.face i = convexHull ℝ ((Finset.Iic i).map p) := by
  obtain ⟨p, hp⟩ : ∃ p : Fin n ↪ E n, ∀ i, faceGens (F.isFace i).1 = (Finset.Iic i).map p := by
    refine exists_chain_sequencing (fun i ↦ ?_) fun i j l ↦ ?_
    · let c (i : Fin n) := #(faceGens (F.isFace i).1)
      have e₁ : c = (Finset.Icc 1 n).orderEmbOfFin (by simp) := by
        refine orderEmbOfFin_unique _ (fun i ↦ ?_) fun i j l ↦ ?_
        · simp_rw [c, Finset.mem_Icc, one_le_card]
          generalize_proofs ex
          have key := (F.isFace i).2
          rw [convexHull_faceGens ex, convexHull_nonempty_iff] at key
          exact ⟨key, hF i⟩
        · apply Finset.card_lt_card
          rw [faceGens_ssubset_iff]
          exact F.strict_mono _ _ l
      have e₂ : (fun i : Fin n ↦ i.1 + 1) = (Finset.Icc 1 n).orderEmbOfFin (by simp) :=
        orderEmbOfFin_unique _ (by simp) fun i j l ↦ by lia
      exact congr($(e₁.trans e₂.symm) i)
    · rw [faceGens_ssubset_iff]
      exact F.strict_mono _ _ l
  refine ⟨p, ?_, fun i ↦ ?_⟩
  · cases n with
    | zero => simp
    | succ n =>
      rw [← Iic_last_eq_univ, ← hp]
      exact faceGens_subset_vertices _
  · rw [← hp]
    exact convexHull_faceGens _

/-! ### Lower bound on the number of vertices in a face based on dimension -/

lemma faceDim_add_one_le_card_faceGens (hs : P.IsFace s) : faceDim s + 1 ≤ #(faceGens hs.1) := by
  let g := faceGens hs.1
  have ng : Nonempty g := by
    simp_rw [g, nonempty_subtype]
    exact nonempty_faceGens hs
  have h := finrank_vectorSpan_range_add_one_le ℝ (fun x : ↥g ↦ x.1)
  rw [show Set.range (fun x : ↥g ↦ x.1) = g by simp] at h
  have heq : vectorSpan ℝ s = vectorSpan ℝ (g : Set (E n)) := by
    rw [convexHull_faceGens hs.1, vectorSpan_convexHull_eq_vectorSpan]
  rw [faceDim, heq]
  simpa [g] using h

lemma card_vertices_le_of_isFullDim (dP : P.IsFullDim) : n + 1 ≤ #P.vertices := by
  have hP : P.IsFace P.toSet := ⟨IsExposed.refl _, by simp [toSet, P.vertices_nonempty]⟩
  have h := faceDim_add_one_le_card_faceGens hP
  rw [show faceDim P.toSet = P.dim by rfl, dP] at h
  exact h.trans (card_le_card (faceGens_subset_vertices hP.1))
