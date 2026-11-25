# Supporting Hyperplane Theorem

This Lean 4 project formalizes Q1134296, the Supporting hyperplane theorem.

Q1134296 states that, for a convex set s ⊆ ℝⁿ and a point x on the boundary of s,
there exists a **supporting hyperplane** of s: a hyperplane that contains × and (inclusively)
contains s in one of its two half-spaces.

## Proof Outline

The general proof outline is as follows:

If the interior of s is nonempty, then the result follows directly from `geometric_hahn_banach_of_nonempty_interior_point`. If it is nonempty, then s must reside in a lower-dimensional subspace (by `interior_nonempty_iff_affineSpan_eq_top`), and the supporting hyperplane can be chosen as a superspace thereof.

## AI Usage Disclosure

All Lean code in this repository is human-written. AI agents were consulted for ideas, and to create boilerplate elements (e.g. lake-manifest.json, lakefile.toml).
