import Submission.LowerBounds.Count
import Submission.UpperBounds.Schlafli

open LeanEval.Geometry.PlatonicClassification

namespace Submission

theorem platonic_classification :
    platonicCount 2 = ⊤ ∧ platonicCount 3 = 5 ∧ platonicCount 4 = 6 ∧
    ∀ d, 5 ≤ d → platonicCount d = 3 := by
  refine ⟨platonicCount_two,
    le_antisymm platonicCount_three_le platonicCount_three_ge,
    le_antisymm platonicCount_four_le ?_,
    fun n hn ↦ le_antisymm (platonicCount_five_plus_le hn) (platonicCount_ge (by lia))⟩
  sorry

end Submission

/- Consider all the flags whose `baryplex`es contain `rP.1.flag.baryplex k` for all `k`
not equal to `i.rev.castSucc` or `j.rev.castSucc`:

* There are a finite number of them, since there are a finite number of flags.
* There are an even number of them by `card_substitute_faces_eq_two`
  and the adjacency of `i` and `j`.
* There are a positive number of them, since `rP.1.flag` itself is an example.
* The flags' orthoschemes are all congruent since the polytope is regular.
* When the orthoschemes are projected to the orthogonal complement of `C`'s span, which has
  dimension 2, they tile the space around the orthogonal complement's origin, because
  the orthoscheme is a fundamental domain.

Let `H_i` be the hyperplane containing `rP.1.flag.baryplex k` for all `k` not equal to
`i.rev.castSucc`, and similarly for `H_j`. It is easy to see that `rP.cosineMatrix i j = -cos θ`
where `θ` is the dihedral angle between `H_i` and `H_j`. By all the properties listed above,
`θ = π / p` for some positive integer `p`, which leads to the result. -/
