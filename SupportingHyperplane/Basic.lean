/-
Copyright (c) 2026 Campbell Bradley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Campbell Bradley
-/
module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!

# Supporting Hyperplane Theorem

This file formalizes Q1134296, the Supporting hyperplane theorem.

Q1134296 states that, for a convex set s ⊆ ℝⁿ and a point x on the boundary of s,
there exists a **supporting hyperplane** of s: a hyperplane that contains × and (inclusively)
contains s in one of its two half-spaces.

## References

* <https://en.wikipedia.org/wiki/Supporting_hyperplane>

## Tags

convex set, supporting hyperplane, separation
-/

open Set
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
variable {s : Set E} {x : E}

/- If a convex set of real vectors s has an empty interior, then there exists
a linear function f that maps the vector span of s to zero. -/
theorem Convex.exists_dual_map_vectorSpan_eq_bot_of_interior_eq_empty
    (hconv : Convex ℝ s) (hi : interior s = ∅) :
    ∃ (f : Module.Dual ℝ E), f ≠ 0 ∧ Submodule.map f (vectorSpan ℝ s) = ⊥ := by
  have haff : ¬affineSpan ℝ s = ⊤ :=
    mt hconv.interior_nonempty_iff_affineSpan_eq_top.mpr (by simp [hi])
  have hvec : vectorSpan ℝ s < ⊤ := by
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nontrivial] at haff
    exact Ne.lt_top haff
  exact Submodule.exists_dual_map_eq_bot_of_lt_top hvec inferInstance

theorem Convex.supporting_hyperplane_of_empty_interior
    (hconv : Convex ℝ s) (hi : interior s = ∅) (hx : x ∈ frontier s) :
    ∃ (f : StrongDual ℝ E), f ≠ 0 ∧ ∀ y ∈ s, f y ≤ f x := by
  obtain ⟨f, hf, hs⟩ := Convex.exists_dual_map_vectorSpan_eq_bot_of_interior_eq_empty hconv hi
  simp_rw [← LinearMap.le_ker_iff_map] at hs
  let g := LinearMap.toContinuousLinearMap f
  rw [← LinearMap.coe_toContinuousLinearMap f] at hf
  have hg : g ≠ 0 := by simpa [g] using hf
  refine ⟨g, hg, ?_⟩
  intro y hy
  have hsub : s ⊆ {z : E | g z = g y} := by
    intro z hz
    have := hs (vsub_mem_vectorSpan ℝ hz hy)
    rwa [LinearMap.mem_ker, vsub_eq_sub, map_sub, sub_eq_zero] at this
  have hclosed : IsClosed {z : E | g z = g y} :=
    isClosed_eq g.continuous continuous_const
  obtain ⟨hcl, _⟩ := hx
  have hx : g x = g y :=
    closure_minimal hsub hclosed hcl
  exact hx.ge

public theorem Convex.supporting_hyperplane (hconv : Convex ℝ s) (hx : x ∈ frontier s) :
    ∃ (f : StrongDual ℝ E), f ≠ 0 ∧ ∀ y ∈ s, f y ≤ f x := by
  obtain he | hne := (interior s).eq_empty_or_nonempty
  · exact Convex.supporting_hyperplane_of_empty_interior hconv he hx
  · obtain ⟨f, hf, hs⟩ := geometric_hahn_banach_of_nonempty_interior_point hconv hx.2 hne
    exact ⟨f, hf, hs⟩
