import Submission.Face.Basic
import Submission.ToMathlib.Exposed

open Set Finset LeanEval.Geometry.PlatonicClassification ConvexPolytope

variable {n : ℕ} {P : ConvexPolytope n} {f g : Set (E n)}

/-- Two subtypes whose defining predicates are pointwise equivalent are order isomorphic
(for the inherited subtype order). -/
def subtypeOrderIsoOfIff {α : Type*} [Preorder α] {p q : α → Prop}
    (h : ∀ a, p a ↔ q a) : {a // p a} ≃o {a // q a} where
  toFun a := ⟨a.1, (h a.1).mp a.2⟩
  invFun a := ⟨a.1, (h a.1).mpr a.2⟩
  map_rel_iff' := Iff.rfl

/-- An order isomorphism restricts to an order isomorphism between the corresponding
upper sets (`Ici`) of a point and its image. -/
def OrderIso.iciCongr {α β : Type*} [Preorder α] [Preorder β] (e : α ≃o β) (a₀ : α) :
    {a // a₀ ≤ a} ≃o {b // e a₀ ≤ b} where
  toFun a := ⟨e a.1, e.le_iff_le.mpr a.2⟩
  invFun b := ⟨e.symm b.1, by have h := e.symm.le_iff_le.mpr b.2; rwa [e.symm_apply_apply] at h⟩
  left_inv a := by ext; simp
  right_inv b := by ext; simp
  map_rel_iff' {a b} := e.le_iff_le

/-- Reassociate a subtype carved out by an extra "upper set" condition as an upper set of
the subtype. -/
def upSetSubtypeIso {α : Type*} [Preorder α] (p : α → Prop) (a₀ : {a // p a}) :
    {a // p a ∧ a₀.1 ≤ a} ≃o {b : {a // p a} // a₀ ≤ b} where
  toFun a := ⟨⟨a.1, a.2.1⟩, a.2.2⟩
  invFun b := ⟨b.1.1, b.1.2, b.2⟩
  map_rel_iff' := Iff.rfl

theorem IsExposed.trans_polytope (hf : IsExposed ℝ P.toSet f) (hg : IsExposed ℝ f g) :
    IsExposed ℝ P.toSet g := fun ng ↦ by
  have nf := ng.mono hg.subset
  obtain ⟨L, c, LP, feq⟩ := hf.exists_dual_eq nf
  obtain ⟨M, d, Mf, geq⟩ := hg.exists_dual_eq ng
  obtain ⟨z, mz⟩ := ng
  classical let s := {v ∈ P.vertices | v ∉ f}
  have Lz := (feq ▸ hg.subset mz).2
  have Mz := (geq ▸ mz).2
  obtain ⟨k, hk⟩ : ∃ k : ℝ, ∀ v ∈ s, (k • L + M) v < (k • L + M) z := by
    obtain es | ns := s.eq_empty_or_nonempty
    · exact ⟨0, by simp [es]⟩
    let k := (s.image (fun v ↦ (M v - d) / (c - L v))).max' (by simp [ns])
    refine ⟨k + 1, fun v mv ↦ ?_⟩
    simp_rw [add_apply, smul_apply]
    have csL : 0 < c - L v := by
      simp_rw [s, mem_filter] at mv
      have mv' : v ∈ P.toSet := subset_convexHull ℝ _ mv.1
      simp_rw [feq, notMem_ofPred_iff, mv', true_and] at mv
      exact sub_pos.mpr ((LP v mv').lt_of_ne mv.2)
    rw [smul_eq_mul, add_comm, smul_eq_mul, ← sub_lt_sub_iff, Lz, Mz, ← mul_sub, ← div_lt_iff₀ csL]
    exact (le_max' _ _ (mem_image_of_mem _ mv)).trans_lt (lt_add_one k)
  replace hk (v) (mv : v ∈ P.vertices) (nv : v ∉ g) : (k • L + M) v < (k • L + M) z := by
    by_cases hv : v ∈ f
    · simp_rw [add_apply, smul_apply, Lz, Mz, (feq ▸ hv).2]
      apply add_lt_add_right
      simp_rw [geq, notMem_ofPred_iff, hv, true_and] at nv
      exact (Mf v hv).lt_of_ne nv
    · classical exact hk _ (mem_filter.mpr ⟨mv, hv⟩)
  have ek (v) (mv : v ∈ g) : (k • L + M) v = (k • L + M) z := by
    simp [Lz, Mz, (feq ▸ hg.subset mv).2, (geq ▸ mv).2]
  have lk (v) (mv : v ∈ P.vertices) : (k • L + M) v ≤ (k • L + M) z := by
    by_cases hv : v ∈ g
    · rw [ek v hv]
    · exact (hk v mv hv).le
  refine ⟨k • L + M, ?_⟩
  ext v
  rw [mem_ofPred]
  refine ⟨fun mv ↦ ⟨hf.subset (geq ▸ mv).1, ?_⟩, fun hv ↦ ?_⟩
  · refine fun _ ↦ dual_le_of_mem_convexHull fun w mw ↦ ?_
    rw [ek v mv]
    exact lk w mw
  · refine mem_convex_of_dual_max lk (fun w mw hw ↦ ?_)
      (hg.convex (hf.convex (convex_convexHull ..))) hv.1
      (le_antisymm (dual_le_of_mem_convexHull lk hv.1) (hv.2 z (hf.subset (hg.subset mz))))
    contrapose hw
    exact (hk w mw hw).ne

/-- The natural order isomorphism between faces of a face `f` of a polytope `P` and
faces of `P` contained in `f`. Proposition 2.3(iii) in Ziegler's _Lectures on Polytopes_. -/
def IsExposed.polytopeOrderIso (hf : IsExposed ℝ P.toSet f) :
    {g // IsExposed ℝ f g} ≃o {g // IsExposed ℝ P.toSet g ∧ g ⊆ f} where
  toFun g := ⟨g.1, hf.trans_polytope g.2, g.2.subset⟩
  invFun g := ⟨g.1, g.2.1.mono hf.subset g.2.2⟩
  map_rel_iff' := by simp

namespace LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable (P) in
/-- The section of a convex polytope by a linear functional `L` and a real number `c`.
When the parameters separate exactly one vertex `v` from the rest
this is the _vertex figure_ at `v`. -/
def lsection (L : StrongDual ℝ (E n)) (c : ℝ) : Set (E n) :=
  {v ∈ P.toSet | L v = c}

variable {L : StrongDual ℝ (E n)} {c : ℝ} {v : E n} (mv : v ∈ P.vertices)
  (Lo : ∀ w ∈ convexHull ℝ (P.vertices.erase v), L w < c) (Lv : c < L v)

lemma isExposed_lsection_of_isExposed_toSet (hf : IsExposed ℝ P.toSet f) :
    IsExposed ℝ (P.lsection L c) {w ∈ f | L w = c} := by
  have sl : P.lsection L c ⊆ P.toSet := sep_subset ..
  convert hf.inter_subset sl using 1
  ext x
  simp_rw [lsection, mem_inter_iff, mem_ofPred_eq, ← and_assoc, and_congr_left_iff, iff_self_and]
  exact fun _ mx ↦ hf.subset mx

include mv Lo Lv in
lemma isExposed_toSet_of_isExposed_lsection (hf : IsExposed ℝ (P.lsection L c) f) :
    let f' := P.toSet ∩ spanPoints ℝ (insert v f)
    IsExposed ℝ P.toSet f' ∧ v ∈ f' := by
  intro f'
  have mvP : v ∈ P.toSet := subset_convexHull ℝ _ mv
  have mvs : v ∈ spanPoints ℝ (insert v f) := subset_spanPoints ℝ _ (mem_insert v f)
  refine ⟨?_, ⟨mvP, mvs⟩⟩
  obtain rfl | nf := f.eq_empty_or_nonempty
  · simp_rw [f', insert_empty_eq, ← coe_affineSpan, AffineSubspace.coe_affineSpan_singleton,
      inter_eq_right.mpr (singleton_subset_iff.mpr mvP), vertex_isExposed mv]
  obtain ⟨K, b, Ks, feq⟩ := hf.exists_dual_eq nf
  rintro -
  let M := (L v - c) • K + (b - K v) • L
  have eM (a) (ma : a ∈ insert v f) : M a = M v := by
    simp_rw [M, add_apply, smul_apply, smul_eq_mul]
    obtain rfl | ma := ma
    on_goal 2 => rw [(hf.subset ma).2, ((feq ▸ ma).2 : K a = b)]
    all_goals ring
  have lM (a) (ma : a ∈ P.vertices) : M a ≤ M v ∧ (M a = M v → a ∈ spanPoints ℝ (insert v f)) := by
    obtain rfl | na := eq_or_ne a v; · simp [mvs]
    have La : L a < c := Lo a (subset_convexHull ℝ _ (mem_erase.mpr ⟨na, ma⟩))
    have pden : 0 < L v - L a := sub_pos.mpr (La.trans Lv)
    let t := (L v - c) / (L v - L a)
    have tpos : 0 < t := by positivity
    have mcc : (1 - t) • v + t • a ∈ P.toSet := by
      refine segment_subset_convexHull mv ma ⟨1 - t, t, ?_, tpos.le, by simp⟩
      simp_rw [sub_nonneg, t, div_le_one pden, sub_le_sub_iff_left, La.le]
    have Lcc : L ((1 - t) • v + t • a) = c := by
      simp_rw [map_add, map_smul, smul_eq_mul, t, one_sub_mul, sub_add, ← mul_sub,
        div_mul_cancel₀ _ pden.ne', sub_sub_cancel]
    have Mcc : M ((1 - t) • v + t • a) ≤ M v := by
      simp_rw [M, add_apply, smul_apply, Lcc,
        show (L v - c) • K v + (b - K v) • L v = (L v - c) • b + (b - K v) • c by ring,
        add_le_add_iff_right]
      exact smul_le_smul_of_nonneg_left (Ks _ ⟨mcc, Lcc⟩) (sub_pos_of_lt Lv).le
    simp_rw [map_add, map_smul, smul_eq_mul] at Mcc
    refine ⟨by nlinarith, fun Ma ↦ ?_⟩
    replace Mcc : (1 - t) * M v + t * M a = M v := by rw [← Ma, ← add_mul, sub_add_cancel, one_mul]
    replace mcc : (1 - t) • v + t • a ∈ f := by
      rw [feq]
      refine ⟨⟨mcc, Lcc⟩, ?_⟩
      have q : M ((1 - t) • v + t • a) = M ((1 - t) • v + t • a) := rfl
      conv_rhs at q => simp only [map_add, map_smul, smul_eq_mul, Mcc]
      simp_rw [M, add_apply, smul_apply, Lcc,
        show (L v - c) • K v + (b - K v) • L v = (L v - c) • b + (b - K v) • c by ring] at q
      rwa [add_left_inj, smul_right_inj (sub_pos_of_lt Lv).ne'] at q
    have mva := subset_affineSpan ℝ _ (mem_insert v f)
    have mcca := subset_affineSpan ℝ _ (mem_insert_of_mem v mcc)
    convert! (affineSpan ℝ (insert v f)).smul_vsub_vadd_mem t⁻¹ mcca mva mva
    rw [vadd_eq_add, vsub_eq_sub, add_sub_right_comm]
    nth_rw 2 [← one_smul ℝ v]
    rw [← sub_smul, sub_sub_cancel_left, neg_smul, ← sub_eq_neg_add, ← smul_sub, smul_smul,
      inv_mul_cancel₀ tpos.ne', one_smul, sub_add_cancel]
  rw [forall₂_and] at lM
  refine ⟨M, ?_⟩
  ext w
  subst f'
  rw [mem_inter_iff, mem_ofPred, and_congr_right_iff]
  refine fun mwP ↦ ⟨fun mws y hy ↦ ?_, fun hw ↦ ?_⟩
  · rw [dual_eq_of_mem_spanPoints eM mws]
    exact dual_le_of_mem_convexHull lM.1 hy
  exact mem_convex_of_dual_max lM.1 lM.2 (affineSpan ..).convex mwP
    (le_antisymm (dual_le_of_mem_convexHull lM.1 mwP) (hw v mvP))

include Lv in
lemma mem_spanPoints_insert_of_eq {w : E n} (hf : ∀ y ∈ f, L y = c)
    (mw : w ∈ spanPoints ℝ (insert v f)) (Lw : L w = c) : w ∈ spanPoints ℝ f := by
  obtain rfl | ⟨z, mz⟩ := f.eq_empty_or_nonempty
  · rw [insert_empty_eq, ← coe_affineSpan, AffineSubspace.coe_affineSpan_singleton,
      mem_singleton_iff] at mw
    exact absurd (mw ▸ Lw) Lv.ne'
  · rw [← coe_affineSpan, ← affineSpan_insert_affineSpan, SetLike.mem_coe,
      AffineSubspace.mem_affineSpan_insert_iff (subset_affineSpan ℝ _ mz) v w] at mw
    obtain ⟨r, x, mx, rfl⟩ := mw
    rw [vadd_eq_add, map_add, dual_eq_of_mem_spanPoints hf mx, add_eq_right, vsub_eq_sub, map_smul,
      map_sub, hf z mz, smul_eq_zero_iff_left (sub_pos_of_lt Lv).ne'] at Lw
    simpa [Lw]

include Lv in
lemma slice_cone_eq (hs : IsExposed ℝ (P.lsection L c) f) :
    {w ∈ P.toSet ∩ spanPoints ℝ (insert v f) | L w = c} = f := by
  ext w
  simp only [mem_inter_iff, mem_ofPred_eq]
  refine ⟨?_, fun mw ↦ ?_⟩
  · rintro ⟨⟨mw, mws⟩, Lw⟩
    rw [hs.eq_inter_spanPoints]
    exact ⟨⟨mw, Lw⟩, mem_spanPoints_insert_of_eq Lv (fun x mx ↦ (hs.subset mx).2) mws Lw⟩
  · exact ⟨⟨(hs.subset mw).1, subset_spanPoints ℝ _ (mem_insert_of_mem v mw)⟩, (hs.subset mw).2⟩

include Lo Lv in
lemma cone_slice_eq (hs : IsExposed ℝ P.toSet f) (mv : v ∈ f) :
    P.toSet ∩ spanPoints ℝ (insert v {w ∈ f | L w = c}) = f := by
  apply subset_antisymm
  · rintro w ⟨mw, mws⟩
    rw [hs.eq_inter_spanPoints]
    exact ⟨mw, affineSpan_mono ℝ (fun x mx ↦ Set.insert_subset mv (by simp) mx) mws⟩
  refine subset_inter_iff.mpr ⟨hs.subset, ?_⟩
  nth_rw 1 [convexHull_faceGens hs]
  refine convexHull_min (fun a ma ↦ ?_) (affineSpan ℝ _).convex
  have maf : a ∈ f := by rw [convexHull_faceGens hs]; exact subset_convexHull ℝ _ ma
  replace ma : a ∈ P.vertices := faceGens_subset_vertices hs ma
  obtain rfl | na := eq_or_ne a v
  · exact subset_spanPoints ℝ _ (mem_insert a _)
  have La : L a < c := Lo a (subset_convexHull ℝ _ (mem_erase.mpr ⟨na, ma⟩))
  have pden : 0 < L v - L a := sub_pos.mpr (La.trans Lv)
  let t := (L v - c) / (L v - L a)
  have tpos : 0 < t := by positivity
  have mcc : (1 - t) • v + t • a ∈ {w ∈ f | L w = c} := by
    constructor
    · refine hs.convex (convex_convexHull ℝ _) mv maf ?_ tpos.le (by simp)
      simp_rw [sub_nonneg, t, div_le_one pden, sub_le_sub_iff_left, La.le]
    · simp_rw [map_add, map_smul, smul_eq_mul, t, one_sub_mul, sub_add, ← mul_sub,
        div_mul_cancel₀ _ pden.ne', sub_sub_cancel]
  have mva := subset_affineSpan ℝ _ (mem_insert v {w ∈ f | L w = c})
  have mcca := subset_affineSpan ℝ _ (mem_insert_of_mem v mcc)
  convert! (affineSpan ℝ (insert v _)).smul_vsub_vadd_mem t⁻¹ mcca mva mva
  rw [vadd_eq_add, vsub_eq_sub, add_sub_right_comm]
  nth_rw 2 [← one_smul ℝ v]
  rw [← sub_smul, sub_sub_cancel_left, neg_smul, ← sub_eq_neg_add, ← smul_sub, smul_smul,
    inv_mul_cancel₀ tpos.ne', one_smul, sub_add_cancel]

include mv Lo Lv in
/-- The order isomorphism between faces of the vertex figure at `v`, a vertex of a polytope `P`,
and faces of `P` containing `v`. -/
def vertexFigureOrderIso :
    {g // IsExposed ℝ (P.lsection L c) g} ≃o {g // IsExposed ℝ P.toSet g ∧ v ∈ g} where
  toFun g := ⟨_, isExposed_toSet_of_isExposed_lsection mv Lo Lv g.2⟩
  invFun g := ⟨_, isExposed_lsection_of_isExposed_toSet g.2.1⟩
  left_inv g := Subtype.ext (slice_cone_eq Lv g.2)
  right_inv g := Subtype.ext (cone_slice_eq Lo Lv g.2.1 g.2.2)
  map_rel_iff' {a b} := by
    constructor <;> intro h
    · rw [← Subtype.coe_le_coe, ← slice_cone_eq Lv a.2, ← slice_cone_eq Lv b.2]
      exact fun x ⟨hx, hLx⟩ ↦ ⟨h hx, hLx⟩
    · exact inter_subset_inter (by rfl) fun x hx ↦ affineSpan_mono ℝ (insert_subset_insert h) hx

variable (ntriv : P.vertices.Nontrivial)

include mv Lo Lv ntriv in
lemma lsection_nonempty : (P.lsection L c).Nonempty := by
  obtain ⟨a, ma, na⟩ := ntriv.exists_ne v
  have La : L a < c := Lo a (subset_convexHull ℝ _ (mem_erase.mpr ⟨na, ma⟩))
  have pden : 0 < L v - L a := sub_pos.mpr (La.trans Lv)
  let t := (L v - c) / (L v - L a)
  refine ⟨(1 - t) • v + t • a, ?_, ?_⟩
  · refine segment_subset_convexHull mv ma ⟨1 - t, t, ?_, by positivity, by simp⟩
    simp_rw [sub_nonneg, t, div_le_one pden, sub_le_sub_iff_left, La.le]
  · simp_rw [map_add, map_smul, smul_eq_mul, t, one_sub_mul, sub_add, ← mul_sub,
      div_mul_cancel₀ _ pden.ne', sub_sub_cancel]

include mv Lo Lv in
lemma affineSpan_toSet_eq_insert_lsection :
    affineSpan ℝ P.toSet = affineSpan ℝ (insert v (P.lsection L c)) := by
  have mvP : v ∈ P.toSet := subset_convexHull ℝ _ mv
  apply le_antisymm
  · rw [affineSpan_le, ← cone_slice_eq Lo Lv (IsExposed.refl P.toSet) mvP]
    exact inter_subset_right
  · exact affineSpan_mono ℝ (insert_subset mvP (sep_subset ..))

include mv Lo Lv ntriv in
lemma faceDim_lsection : faceDim (P.lsection L c) + 1 = P.dim := by
  obtain ⟨p, hp⟩ := lsection_nonempty mv Lo Lv ntriv
  have hp' : p ∈ affineSpan ℝ (P.lsection L c) := subset_affineSpan ℝ _ hp
  have hvspan : v ∉ (affineSpan ℝ (P.lsection L c) : Set (E n)) := fun hv ↦
    absurd (dual_eq_of_mem_spanPoints (fun w hw ↦ hw.2) hv) Lv.ne'
  have hdiff : v -ᵥ p ∉ vectorSpan ℝ (P.lsection L c) := fun hd ↦ by
    apply hvspan
    rw [← direction_affineSpan] at hd
    simpa using AffineSubspace.vadd_mem_of_mem_direction hd hp'
  have hins : vectorSpan ℝ (insert v (P.lsection L c))
      = (ℝ ∙ (v -ᵥ p)) ⊔ vectorSpan ℝ (P.lsection L c) := by
    rw [← direction_affineSpan, ← affineSpan_insert_affineSpan,
      AffineSubspace.direction_affineSpan_insert hp', direction_affineSpan]
  have hPdim : P.dim = Module.finrank ℝ (vectorSpan ℝ (insert v (P.lsection L c))) := by
    rw [dim, ← direction_affineSpan, ← direction_affineSpan,
      affineSpan_toSet_eq_insert_lsection mv Lo Lv]
  rw [faceDim, hPdim, hins, sup_comm, Submodule.finrank_sup_span_singleton hdiff]

include mv Lv in
/-- Coning a nonempty face `f` of the section over the separated vertex `v` raises its
affine dimension by exactly one. -/
lemma faceDim_cone_eq (hf : IsExposed ℝ (P.lsection L c) f) (nf : f.Nonempty) :
    faceDim (P.toSet ∩ spanPoints ℝ (insert v f)) = faceDim f + 1 := by
  have mvP : v ∈ P.toSet := subset_convexHull ℝ _ mv
  have Lf : ∀ w ∈ f, L w = c := fun w hw ↦ (hf.subset hw).2
  obtain ⟨p, hp⟩ := nf
  have hp' : p ∈ affineSpan ℝ f := subset_affineSpan ℝ _ hp
  have hvspan : v ∉ (affineSpan ℝ f : Set (E n)) := fun hv ↦
    absurd (dual_eq_of_mem_spanPoints Lf hv) Lv.ne'
  have hdiff : v -ᵥ p ∉ vectorSpan ℝ f := fun hd ↦ by
    apply hvspan
    rw [← direction_affineSpan] at hd
    simpa using AffineSubspace.vadd_mem_of_mem_direction hd hp'
  have hins : vectorSpan ℝ (insert v f) = ℝ ∙ (v -ᵥ p) ⊔ vectorSpan ℝ f := by
    rw [← direction_affineSpan, ← affineSpan_insert_affineSpan,
      AffineSubspace.direction_affineSpan_insert hp', direction_affineSpan]
  have haff : affineSpan ℝ (P.toSet ∩ spanPoints ℝ (insert v f)) = affineSpan ℝ (insert v f) := by
    apply le_antisymm
    · rw [affineSpan_le]
      exact inter_subset_right
    · refine affineSpan_mono ℝ (insert_subset ?_ ?_)
      · exact ⟨mvP, subset_spanPoints ℝ _ (mem_insert v f)⟩
      · exact fun w hw ↦ ⟨(hf.subset hw).1, subset_spanPoints ℝ _ (mem_insert_of_mem v hw)⟩
  rw [faceDim, faceDim, ← direction_affineSpan, haff, direction_affineSpan, hins,
    sup_comm, Submodule.finrank_sup_span_singleton hdiff]

include Lo Lv in
/-- The section of a positive-dimensional face `f` containing the separated vertex `v` is
nonempty: the segment from `v` to any other vertex of `f` crosses the hyperplane. -/
lemma lsection_face_nonempty (hf : IsExposed ℝ P.toSet f) (mv : v ∈ f)
    (hfd : faceDim f ≠ 0) : {w ∈ f | L w = c}.Nonempty := by
  obtain ⟨u, huV, huf, hune⟩ : ∃ u ∈ P.vertices, u ∈ f ∧ u ≠ v := by
    by_contra! hcon
    have hsub : (faceGens hf : Set (E n)) ⊆ {v} := fun u hu ↦ by
      rw [mem_coe] at hu
      have huf : u ∈ f := by rw [convexHull_faceGens hf]; exact subset_convexHull ℝ _ hu
      exact hcon u (faceGens_subset_vertices hf hu) huf
    have hfv : f = {v} := by
      rw [convexHull_faceGens hf]
      apply subset_antisymm (convexHull_min (hsub.trans (by simp)) (convex_singleton v))
      rw [Set.singleton_subset_iff, ← convexHull_faceGens hf]; exact mv
    apply hfd; rw [hfv, faceDim, vectorSpan_singleton, finrank_bot]
  have Lu : L u < c := Lo u (subset_convexHull ℝ _ (mem_erase.mpr ⟨hune, huV⟩))
  have hden : 0 < L v - L u := sub_pos.mpr (Lu.trans Lv)
  set s := (L v - c) / (L v - L u) with hs
  have spos : 0 < s := div_pos (sub_pos.mpr Lv) hden
  have sle : s ≤ 1 := by rw [hs, div_le_one hden]; linarith
  refine ⟨(1 - s) • v + s • u, ?_, ?_⟩
  · exact hf.convex (convex_convexHull ℝ _) mv huf (by linarith) spos.le (by ring)
  · simp_rw [map_add, map_smul, smul_eq_mul, hs, one_sub_mul, sub_add, ← mul_sub,
      div_mul_cancel₀ _ hden.ne', sub_sub_cancel]

include mv Lo Lv in
/-- The vertex-figure order isomorphism restricts to an order isomorphism between section faces
containing `fσ = {w ∈ f | L w = c}` and polytope faces containing `f`. -/
def faceFigureStepIso (hf : IsExposed ℝ P.toSet f) (mvf : v ∈ f) :
    {s // IsExposed ℝ (P.lsection L c) s ∧ {w ∈ f | L w = c} ⊆ s} ≃o
    {s // IsExposed ℝ P.toSet s ∧ f ⊆ s} := by
  have hfσexp : IsExposed ℝ (P.lsection L c) {w ∈ f | L w = c} :=
    isExposed_lsection_of_isExposed_toSet hf
  have hφf : (vertexFigureOrderIso mv Lo Lv ⟨{w ∈ f | L w = c}, hfσexp⟩).1 = f :=
    cone_slice_eq Lo Lv hf mvf
  refine (upSetSubtypeIso (fun s ↦ IsExposed ℝ (P.lsection L c) s)
      ⟨{w ∈ f | L w = c}, hfσexp⟩).trans ?_
  refine (OrderIso.iciCongr (vertexFigureOrderIso mv Lo Lv)
      ⟨{w ∈ f | L w = c}, hfσexp⟩).trans ?_
  refine (upSetSubtypeIso (fun s ↦ IsExposed ℝ P.toSet s ∧ v ∈ s)
      (vertexFigureOrderIso mv Lo Lv ⟨{w ∈ f | L w = c}, hfσexp⟩)).symm.trans ?_
  refine subtypeOrderIsoOfIff fun s ↦ ?_
  simp_rw [hφf, and_right_comm, and_iff_left_iff_imp, and_imp]
  exact fun _ sf ↦ sf mvf

/-- Interpret the convex hull of a nonempty finite point set as a convex polytope. -/
lemma exists_polytope_of_convexHull_finset {s : Finset (E n)}
    (ns : (convexHull ℝ (s : Set (E n))).Nonempty) :
    ∃ Q : ConvexPolytope n, Q.toSet = convexHull ℝ s := by
  let C := convexHull ℝ (s : Set (E n))
  have cC : IsCompact C := s.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have feC : (extremePoints ℝ C).Finite := s.finite_toSet.subset extremePoints_convexHull_subset
  lift extremePoints ℝ C to Finset (E n) using feC with W Weq
  have chW : convexHull ℝ W = C := by
    rw [← (W.finite_toSet.isClosed_convexHull (𝕜 := ℝ)).closure_eq, Weq]
    exact closure_convexHull_extremePoints cC (convex_convexHull ℝ _)
  refine ⟨⟨W, ?_, by rwa [chW]⟩, chW⟩
  rw [← coe_nonempty, Weq]
  exact cC.extremePoints_nonempty ns

include mv Lo Lv in
/-- The section `{L = c}` separating the vertex `v` is the convex hull of the finite set of
points where the segments from `v` to the remaining vertices cross the hyperplane `{L = c}`. -/
lemma exists_finset_convexHull_eq_lsection :
    ∃ G : Finset (E n), convexHull ℝ G = P.lsection L c := by
  classical
  have hcne : L v - c ≠ 0 := (sub_pos_of_lt Lv).ne'
  set t : E n → ℝ := fun u ↦ (L v - c) / (L v - L u) with ht
  set p : E n → E n := fun u ↦ (1 - t u) • v + t u • u with hp
  have hLu : ∀ u ∈ P.vertices.erase v, L u < c := fun u hu ↦
    Lo u (subset_convexHull ℝ _ hu)
  have hden : ∀ u ∈ P.vertices.erase v, 0 < L v - L u := fun u hu ↦
    sub_pos.mpr ((hLu u hu).trans Lv)
  have htpos : ∀ u ∈ P.vertices.erase v, 0 < t u := fun u hu ↦
    div_pos (sub_pos.mpr Lv) (hden u hu)
  have htle : ∀ u ∈ P.vertices.erase v, t u ≤ 1 := fun u hu ↦ by
    rw [ht, div_le_one (hden u hu)]; linarith [hLu u hu]
  have hpmemP : ∀ u ∈ P.vertices.erase v, p u ∈ P.toSet := fun u hu ↦ by
    have hu' : u ∈ P.vertices := (mem_erase.mp hu).2
    exact segment_subset_convexHull mv hu'
      ⟨1 - t u, t u, by linarith [htle u hu], (htpos u hu).le, by ring, rfl⟩
  have hpmemL : ∀ u ∈ P.vertices.erase v, L (p u) = c := fun u hu ↦ by
    have hd := (hden u hu).ne'
    simp only [hp, map_add, map_smul, smul_eq_mul, ht]
    field_simp
    ring
  have hconvL : Convex ℝ (P.lsection L c) :=
    (convex_convexHull ℝ _).inter (convex_hyperplane L.isLinear c)
  refine ⟨(P.vertices.erase v).image p, ?_⟩
  apply subset_antisymm
  · apply convexHull_min _ hconvL
    rintro y hy
    rw [coe_image, mem_image] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    exact ⟨hpmemP u hu, hpmemL u hu⟩
  · rintro x ⟨hxP, hxL⟩
    rw [toSet, mem_convexHull'] at hxP
    obtain ⟨w, hw0, hw1, hwx⟩ := hxP
    have hsumw : ∑ u ∈ P.vertices.erase v, w u = 1 - w v := by
      have h := add_sum_erase P.vertices w mv
      rw [hw1] at h; linarith [h]
    have hLxsum : ∑ u ∈ P.vertices, w u * L u = c := by
      have hh : L x = ∑ u ∈ P.vertices, w u * L u := by
        rw [← hwx, map_sum]; simp [map_smul, smul_eq_mul]
      rw [← hh, hxL]
    have hsumwL : ∑ u ∈ P.vertices.erase v, w u * L u = c - w v * L v := by
      have h := add_sum_erase P.vertices (fun u ↦ w u * L u) mv
      rw [hLxsum] at h; linarith [h]
    have hμsum : ∑ u ∈ P.vertices.erase v, w u / t u = 1 := by
      have expand : ∀ u ∈ P.vertices.erase v, w u / t u = w u * (L v - L u) / (L v - c) := by
        intro u hu; rw [ht, div_div_eq_mul_div]
      rw [sum_congr rfl expand, ← sum_div]
      have key : ∑ u ∈ P.vertices.erase v, w u * (L v - L u)
          = L v * (∑ u ∈ P.vertices.erase v, w u) - ∑ u ∈ P.vertices.erase v, w u * L u := by
        rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun u _ ↦ by ring
      rw [key, hsumw, hsumwL]; field_simp; ring
    have hcm : (P.vertices.erase v).centerMass (fun u ↦ w u / t u) p = x := by
      rw [centerMass, hμsum, inv_one, one_smul]
      have hxsplit : ∑ u ∈ P.vertices.erase v, w u • u = x - w v • v := by
        have h := add_sum_erase P.vertices (fun u ↦ w u • u) mv
        rw [hwx] at h
        rw [eq_sub_iff_add_eq, add_comm]; exact h
      have expand2 : ∀ u ∈ P.vertices.erase v, (w u / t u) • p u
          = (w u * (1 - t u) / t u) • v + w u • u := fun u hu ↦ by
        have hd := (htpos u hu).ne'
        simp_rw [hp, smul_add, smul_smul]
        congr 1
        · congr 1; ring
        · congr 1; field_simp
      rw [sum_congr rfl expand2, sum_add_distrib, ← sum_smul, hxsplit]
      have hscal : ∑ u ∈ P.vertices.erase v, w u * (1 - t u) / t u = w v := by
        have expand3 : ∀ u ∈ P.vertices.erase v,
            w u * (1 - t u) / t u = w u * (c - L u) / (L v - c) := fun u hu ↦ by
          simp only [ht]
          have hd := (hden u hu).ne'
          field_simp
          ring
        rw [sum_congr rfl expand3, ← sum_div]
        have key2 : ∑ u ∈ P.vertices.erase v, w u * (c - L u)
            = c * (∑ u ∈ P.vertices.erase v, w u) - ∑ u ∈ P.vertices.erase v, w u * L u := by
          rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun u _ ↦ by ring
        rw [key2, hsumw, hsumwL]; field_simp; ring
      rw [hscal]; abel
    rw [← hcm]
    exact centerMass_mem_convexHull _
      (fun u hu ↦ div_nonneg (hw0 u (mem_of_mem_erase hu)) (htpos u hu).le)
      (by rw [hμsum]; norm_num)
      (fun u hu ↦ mem_coe.mpr (mem_image_of_mem p hu))

include mv Lo Lv ntriv in
lemma lsection_as_polytope : ∃ Q : ConvexPolytope n, Q.toSet = P.lsection L c := by
  obtain ⟨G, hG⟩ := exists_finset_convexHull_eq_lsection mv Lo Lv
  have hne : (convexHull ℝ (G : Set (E n))).Nonempty := by
    rw [hG]; exact lsection_nonempty mv Lo Lv ntriv
  obtain ⟨Q, hQ⟩ := exists_polytope_of_convexHull_finset hne
  exact ⟨Q, hQ.trans hG⟩

include mv ntriv in
theorem exists_vertex_figure : ∃ Q : ConvexPolytope n, Q.dim + 1 = P.dim ∧
    Nonempty ({g // IsExposed ℝ Q.toSet g} ≃o {g // IsExposed ℝ P.toSet g ∧ v ∈ g}) := by
  obtain ⟨L, c, Lo, Lv⟩ := exists_vertex_separator mv
  obtain ⟨Q, Qs⟩ := lsection_as_polytope mv Lo Lv ntriv
  refine ⟨Q, ?_, ?_⟩
  · rw [dim, Qs]; exact faceDim_lsection mv Lo Lv ntriv
  · rw [Qs]; exact ⟨vertexFigureOrderIso mv Lo Lv⟩

theorem exists_face_figure (hf : P.IsFace f) (df : faceDim f < P.dim) :
    ∃ Q : ConvexPolytope n, Q.dim + faceDim f + 1 = P.dim ∧
    Nonempty ({g // IsExposed ℝ Q.toSet g} ≃o {g // IsExposed ℝ P.toSet g ∧ f ⊆ g}) := by
  induction hd : faceDim f using Nat.strongRecOn generalizing P f with | _ d ih
  obtain ⟨v, mvP, mv⟩ := hf.exists_vertex_mem
  have ntriv : P.dim ≠ 0 := by lia
  rw [dim_ne_zero_iff_card_vertices, one_lt_card_iff_nontrivial] at ntriv
  obtain ⟨L, c, Lo, Lv⟩ := exists_vertex_separator mvP
  obtain rfl | dpos := d.eq_zero_or_pos
  · obtain ⟨Q, hQdim, ⟨eV⟩⟩ := exists_vertex_figure mvP ntriv
    refine ⟨Q, by lia, ?_⟩
    have hfsing : f = {v} := by
      have hz : P.IsFace f ∧ faceDim f = 0 := ⟨hf, by lia⟩
      rw [zero_dim_face_iff_vertex] at hz
      obtain ⟨v', _, hv'⟩ := hz
      rw [hv', mem_singleton_iff] at mv
      rw [hv', mv]
    let hcong : {s // IsExposed ℝ P.toSet s ∧ v ∈ s} ≃o {s // IsExposed ℝ P.toSet s ∧ f ⊆ s} :=
      subtypeOrderIsoOfIff (fun s ↦ by rw [hfsing, Set.singleton_subset_iff])
    exact ⟨eV.trans hcong⟩
  · obtain ⟨Q1, hQ1⟩ := lsection_as_polytope mvP Lo Lv ntriv
    have hfσexp : IsExposed ℝ (P.lsection L c) {w ∈ f | L w = c} :=
      isExposed_lsection_of_isExposed_toSet hf.1
    have hfσne : ({w ∈ f | L w = c}).Nonempty :=
      lsection_face_nonempty Lo Lv hf.1 mv (by lia)
    have hcone : P.toSet ∩ spanPoints ℝ (insert v {w ∈ f | L w = c}) = f :=
      cone_slice_eq Lo Lv hf.1 mv
    have hfdim : faceDim f = faceDim {w ∈ f | L w = c} + 1 := by
      have h := faceDim_cone_eq mvP Lv hfσexp hfσne; rwa [hcone] at h
    have hQ1face : Q1.IsFace {w ∈ f | L w = c} := ⟨hQ1 ▸ hfσexp, hfσne⟩
    have hQ1dim : Q1.dim = faceDim (P.lsection L c) := by rw [dim, hQ1]; rfl
    have hlsdim : faceDim (P.lsection L c) + 1 = P.dim := faceDim_lsection mvP Lo Lv ntriv
    have hfσdimlt : faceDim {w ∈ f | L w = c} < Q1.dim := by omega
    obtain ⟨Q, hQdim, ⟨eIH⟩⟩ := ih (faceDim {w ∈ f | L w = c}) (by omega) hQ1face hfσdimlt rfl
    refine ⟨Q, by lia, ?_⟩
    let e1 : {s // IsExposed ℝ Q1.toSet s ∧ {w ∈ f | L w = c} ⊆ s} ≃o
        {s // IsExposed ℝ (P.lsection L c) s ∧ {w ∈ f | L w = c} ⊆ s} :=
      subtypeOrderIsoOfIff (fun s ↦ by rw [hQ1])
    let e2 := faceFigureStepIso mvP Lo Lv hf.1 mv
    exact ⟨(eIH.trans e1).trans e2⟩

/-- Turn a face of a polytope into a polytope in its own right. -/
noncomputable def IsFace.toPolytope (hf : P.IsFace f) : ConvexPolytope n where
  vertices := faceGens hf.1
  vertices_nonempty := by
    have := hf.2
    rwa [convexHull_faceGens hf.1, convexHull_nonempty_iff] at this
  vertices_eq_extremePoints := self_eq_exch_of_subset (faceGens_subset_vertices _)

lemma IsFace.toSet_toPolytope (hf : P.IsFace f) : hf.toPolytope.toSet = f :=
  (convexHull_faceGens hf.1).symm

/-- Theorem 2.7(ii) in Ziegler's _Lectures on Polytopes_. -/
theorem exists_interval_figure (hf : P.IsFace f) (hg : P.IsFace g) (sfg : f ⊂ g) :
    ∃ Q : ConvexPolytope n, Q.dim + faceDim f + 1 = faceDim g ∧
    Nonempty ({s // IsExposed ℝ Q.toSet s} ≃o {s // IsExposed ℝ P.toSet s ∧ f ⊆ s ∧ s ⊆ g}) := by
  have hfg : IsExposed ℝ g f := hf.1.mono hg.1.subset sfg.subset
  have hg'face : hg.toPolytope.IsFace f := ⟨by rwa [hg.toSet_toPolytope], hf.2⟩
  have hg'dim : hg.toPolytope.dim = faceDim g := by rw [dim, hg.toSet_toPolytope, faceDim]
  have hdf : faceDim f < hg.toPolytope.dim := by
    rw [hg'dim]; exact faceDim_strictMono hf hg sfg
  obtain ⟨Q, hQdim, ⟨eF⟩⟩ := exists_face_figure hg'face hdf
  refine ⟨Q, by rw [← hg'dim]; exact hQdim, ?_⟩
  refine ⟨eF.trans ?_⟩
  refine (subtypeOrderIsoOfIff (p := fun s ↦ IsExposed ℝ hg.toPolytope.toSet s ∧ f ⊆ s)
    (q := fun s ↦ IsExposed ℝ g s ∧ f ⊆ s) (fun s ↦ by rw [hg.toSet_toPolytope])).trans ?_
  refine (upSetSubtypeIso (IsExposed ℝ g) ⟨f, hfg⟩).trans ?_
  refine (OrderIso.iciCongr (hg.1.polytopeOrderIso) ⟨f, hfg⟩).trans ?_
  refine (upSetSubtypeIso (fun s ↦ IsExposed ℝ P.toSet s ∧ s ⊆ g)
    (hg.1.polytopeOrderIso ⟨f, hfg⟩)).symm.trans ?_
  refine subtypeOrderIsoOfIff fun s ↦ ?_
  rw [and_right_comm, and_assoc]
  rfl

end LeanEval.Geometry.PlatonicClassification.ConvexPolytope

lemma exists_face_strict_between (hf : P.IsFace f) (hg : P.IsFace g) (sfg : f ⊂ g)
    (hd : faceDim f + 1 < faceDim g) : ∃ s, P.IsFace s ∧ f ⊂ s ∧ s ⊂ g := by
  obtain ⟨Q, dQ, ⟨e⟩⟩ := exists_interval_figure hf hg sfg
  obtain ⟨v, mv⟩ := Q.vertices_nonempty
  let sol := e ⟨{v}, vertex_isExposed mv⟩
  refine ⟨sol.1, ⟨sol.2.1, hf.2.mono sol.2.2.1⟩, ?_, ?_⟩
  · have ssf : ⟨_, isExposed_empty⟩ ≤ e.symm ⟨f, hf.1, subset_rfl, sfg.subset⟩ :=
      Subtype.mk_le_mk.mpr (empty_subset _)
    rw [OrderIso.le_symm_apply] at ssf
    replace ssf : (e ⟨_, isExposed_empty⟩).1 = f := le_antisymm ssf (e ⟨_, isExposed_empty⟩).2.2.1
    simp [← ssf, sol]
  · refine (e ⟨Q.toSet, IsExposed.refl _⟩).2.2.2.trans_lt'
      (e.lt_iff_lt.mpr ⟨Set.singleton_subset_iff.mpr (subset_convexHull ℝ _ mv), fun h ↦ ?_⟩)
    replace h : Q.toSet = {v} := h.antisymm (by simpa [toSet] using subset_convexHull ℝ _ mv)
    rw [dim, h, vectorSpan_singleton, finrank_bot] at dQ
    lia

theorem exists_superface (hf : P.IsFace f) (df : faceDim f < P.dim) :
    ∃ g ⊃ f, P.IsFace g ∧ faceDim g = faceDim f + 1 := by
  let K := {d | ∃ g, P.IsFace g ∧ f ⊂ g ∧ faceDim g = d}
  have nK : K.Nonempty := by
    refine ⟨_, P.toSet, ⟨IsExposed.refl _, ?_⟩, ?_, rfl⟩
    · exact ⟨_, subset_convexHull ℝ _ P.vertices_nonempty.choose_spec⟩
    · exact hf.1.subset.lt_of_ne fun h ↦ df.ne (h ▸ rfl)
  obtain ⟨-, ⟨g, hg, sfg, rfl⟩, mg⟩ := wellFounded_lt.has_min K nK
  refine ⟨g, sfg, hg, ?_⟩
  contrapose! mg
  have dg := faceDim_strictMono hf hg sfg
  obtain ⟨z, hz, sfz, szg⟩ := exists_face_strict_between hf hg sfg (by lia)
  exact ⟨_, ⟨z, hz, sfz, rfl⟩, faceDim_strictMono hz hg szg⟩

theorem exists_subface (hf : P.IsFace f) (df : 0 < faceDim f) :
    ∃ g ⊂ f, P.IsFace g ∧ faceDim g = faceDim f - 1 := by
  let K := {d | ∃ g, P.IsFace g ∧ g ⊂ f ∧ faceDim f - faceDim g = d}
  have nK : K.Nonempty := by
    obtain ⟨v, mvP, mv⟩ := hf.exists_vertex_mem
    refine ⟨faceDim f, ⟨_, ⟨vertex_isExposed mvP, by simp⟩, ?_, ?_⟩⟩
    · obtain ⟨w, hn, mw⟩ : ∃ w ≠ v, w ∈ f := by
        contrapose df
        simp_rw [not_exists, not_and', not_ne_iff] at df
        replace df := eq_singleton_iff_unique_mem.mpr ⟨mv, df⟩
        simp [df, faceDim]
      exact LE.le.ssubset_of_mem_notMem (by simp [mv]) mw (by simp [hn])
    · nth_rw 2 [faceDim]
      rw [vectorSpan_singleton, finrank_bot, tsub_zero]
  obtain ⟨-, ⟨g, hg, sgf, rfl⟩, mg⟩ := wellFounded_lt.has_min K nK
  refine ⟨g, sgf, hg, ?_⟩
  contrapose! mg
  have dg := faceDim_strictMono hg hf sgf
  obtain ⟨z, hz, sgz, szf⟩ := exists_face_strict_between hg hf sgf (by lia)
  exact ⟨_, ⟨z, hz, szf, rfl⟩, Nat.sub_lt_sub_left dg (faceDim_strictMono hg hz sgz)⟩

/-- Given two faces `f ⊂ g` of a polytope with dimensions differing by two,
there are exactly four faces between them. Theorem 2.7(iii) in Ziegler's _Lectures on Polytopes_. -/
theorem card_faces_between_eq_four (hf : P.IsFace f) (hg : P.IsFace g) (sfg : f ⊂ g)
    (hd : faceDim f + 2 = faceDim g) : {s | P.IsFace s ∧ f ⊆ s ∧ s ⊆ g}.ncard = 4 := by
  obtain ⟨Q, dQ, ⟨e⟩⟩ := exists_interval_figure hf hg sfg
  replace dQ : Q.dim = 1 := by lia
  obtain ⟨x, y, hn, fQ⟩ := dim_eq_one_face_characterisation dQ
  have cbtw : Nat.card {s // IsExposed ℝ Q.toSet s} = 4 := by
    rw [Nat.subtype_card {∅, {x}, {y}, convexHull ℝ {x, y}} (by simpa using Set.ext_iff.mp fQ.symm)]
    have n₁ : ∅ ∉ ({{x}, {y}, (convexHull ℝ) {x, y}} : Finset _) := by
      simp_rw [Finset.mem_insert, Set.empty_ne_singleton, Finset.mem_singleton, false_or]
      rw [← Ne, ← Set.nonempty_iff_empty_ne, convexHull_nonempty_iff]
      simp
    have n₂ : {x} ∉ ({{y}, (convexHull ℝ) {x, y}} : Finset _) := by
      simp_rw [Finset.mem_insert, singleton_eq_singleton_iff, not_or, hn, not_false_eq_true,
        true_and, Finset.mem_singleton, subset_antisymm_iff, not_and_or,
        not_subset_iff_exists_mem_notMem]
      exact .inr ⟨y, by simp [right_mem_segment], by simp [hn.symm]⟩
    simp only [card_insert_of_notMem n₁, card_insert_of_notMem n₂, Nat.reduceEqDiff]
    apply card_pair
    simp_rw [Ne, subset_antisymm_iff, not_and_or, not_subset_iff_exists_mem_notMem]
    exact .inr ⟨x, by simp [left_mem_segment], by simp [hn]⟩
  rw [Nat.card_eq_of_bijective _ e.bijective] at cbtw
  change {s | IsExposed ℝ P.toSet s ∧ f ⊆ s ∧ s ⊆ g}.ncard = 4 at cbtw
  convert cbtw using 4 with s
  simp_rw [← and_assoc, and_congr_left_iff]
  rintro - sf
  simp [IsFace, hf.2.mono sf]

/-- Given two faces `f ⊂ g` of a polytope with dimensions differing by two,
there are exactly two faces strictly between them. -/
theorem card_faces_strict_between_eq_two (hf : P.IsFace f) (hg : P.IsFace g) (sfg : f ⊂ g)
    (hd : faceDim f + 2 = faceDim g) : {s | P.IsFace s ∧ f ⊂ s ∧ s ⊂ g}.ncard = 2 := by
  have ps : {f, g} ⊆ {s | P.IsFace s ∧ f ⊆ s ∧ s ⊆ g} := by
    rw [pair_subset_iff]
    exact ⟨⟨hf, subset_rfl, sfg.subset⟩, ⟨hg, sfg.subset, subset_rfl⟩⟩
  rw [show 2 = 4 - 2 by rfl, ← card_faces_between_eq_four hf hg sfg hd, ← ncard_pair sfg.ne,
    ← ncard_sdiff ps]
  congr 1
  ext s
  simp_rw [mem_sdiff, mem_ofPred, mem_insert_iff, mem_singleton_iff, Set.ssubset_iff_subset_ne]
  tauto

/-- `card_faces_strict_between_eq_two` for `faceDim g = 1`
(here `f` would be the empty face, which is not `P.IsFace`). -/
theorem card_faces_strict_below_dim_one_eq_two (hg : P.IsFace g) (dg : faceDim g = 1) :
    {s | P.IsFace s ∧ s ⊂ g}.ncard = 2 := by
  obtain ⟨v, mv, w, mw, hn, rfl⟩ := one_dim_face_is_edge hg dg
  suffices {s | P.IsFace s ∧ s ⊂ (convexHull ℝ) {v, w}} = {{v}, {w}} from
    this ▸ ncard_pair (by simp [hn])
  ext s
  simp_rw [mem_ofPred, mem_insert_iff, mem_singleton_iff]
  refine ⟨fun ⟨hs, ss⟩ ↦ ?_, fun h ↦ ?_⟩
  · have ds := Nat.lt_one_iff.mp (dg ▸ faceDim_strictMono hs hg ss)
    obtain ⟨x, mx, rfl⟩ := zero_dim_face_iff_vertex.mp ⟨hs, ds⟩
    simp_rw [singleton_eq_singleton_iff]
    have g₀ : faceGens hs.1 = {x} :=
      (existsUnique_faceGens hs.1).unique (exists_faceGens hs.1).choose_spec (by simp [mx])
    have g₁ : faceGens hg.1 = {v, w} := by
      refine (existsUnique_faceGens hg.1).unique (exists_faceGens hg.1).choose_spec ⟨?_, by simp⟩
      rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨mv, mw⟩
    have key := (g₀ ▸ g₁ ▸ (faceGens_ssubset_iff hs.1 hg.1).mpr ss).subset
    simpa using key
  · obtain rfl | rfl := h
    · exact ⟨⟨vertex_isExposed mv, by simp⟩,
        LE.le.ssubset_of_mem_notMem (by simpa using left_mem_segment ..)
          (by simpa using right_mem_segment ..) (by simp [hn.symm])⟩
    · exact ⟨⟨vertex_isExposed mw, by simp⟩,
        LE.le.ssubset_of_mem_notMem (by simpa using right_mem_segment ..)
          (by simpa using left_mem_segment ..) (by simp [hn])⟩
