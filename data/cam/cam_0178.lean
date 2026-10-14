import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-178»

open scoped BigOperators

theorem risk_budgeting_normalized_weights_exist_unique
    (n : ℕ)
    (Sigma : Matrix (Fin n) (Fin n) ℝ)
    (rdes : Fin n → ℝ)
    (hSigma_symm : Sigma.IsSymm)
    (hSigma_pos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < dotProduct x (fun i => ∑ j, Sigma i j * x j))
    (hrpos : ∀ i, 0 < rdes i)
    (hrsum : ∑ i, rdes i = 1) :
    ∃! xstar : Fin n → ℝ,
      (∀ i, 0 < xstar i) ∧
      (∀ x : Fin n → ℝ,
        (∀ i, 0 < x i) →
        (1 / 2) * dotProduct x (fun i => ∑ j, Sigma i j * x j) - ∑ i, rdes i * Real.log (x i) ≥
          (1 / 2) * dotProduct xstar (fun i => ∑ j, Sigma i j * xstar j) - ∑ i, rdes i * Real.log (xstar i)) ∧
      let xhat : Fin n → ℝ := fun i => xstar i / (∑ j, xstar j)
      (∑ i, xhat i = 1) ∧
      (∀ i,
        xhat i * (∑ j, Sigma i j * xhat j) /
            dotProduct xhat (fun k => ∑ j, Sigma k j * xhat j) =
          rdes i) := by
  sorry

end «CAM-Bench-178»
