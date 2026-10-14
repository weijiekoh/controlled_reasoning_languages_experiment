import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-564»

def LogConcaveOn {n : ℕ} (C : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Convex ℝ C ∧
    (∀ x ∈ C, 0 < f x) ∧
    ConcaveOn ℝ C (fun x => Real.log (f x))

theorem elementarySymmetric_logConcave_on_negative_orthant
    (n i : ℕ) (hi : 1 ≤ i ∧ i ≤ n) :
    LogConcaveOn
      {lam : Fin n → ℝ | ∀ j : Fin n, lam j < 0}
      (fun lam : Fin n → ℝ =>
        (-1 : ℝ) ^ i *
          Polynomial.coeff
            (∏ j : Fin n, (Polynomial.X - Polynomial.C (lam j))) (n - i)) := by
  sorry

end «CAM-Bench-564»
