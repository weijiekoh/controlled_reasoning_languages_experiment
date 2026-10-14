import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-701»

def IsUnboundedBelowOn (C : Set α) (f : α → ℝ) : Prop :=
  ∀ M : ℝ, ∃ x ∈ C, f x < M

theorem unconstrained_quadratic_unbounded_below_of_not_psd
    {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ) (q : n → ℝ) (r : ℝ)
    (h_symm : P.IsSymm) (hP : ¬ P.PosSemidef) :
    IsUnboundedBelowOn Set.univ
      (fun x : n → ℝ => (1 / 2 : ℝ) * dotProduct x (fun i => ∑ j, P i j * x j) + dotProduct q x + r) := by
  sorry

end «CAM-Bench-701»
