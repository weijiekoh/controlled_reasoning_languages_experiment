import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-236»

open scoped BigOperators

theorem polynomial_oscillation_on_Icc_convex
    (n : ℕ) (hn : 1 ≤ n) (a b : ℝ) (hab : a < b) :
    ConvexOn ℝ Set.univ (fun x : Fin n → ℝ =>
      sSup ((fun t : ℝ => ∑ i : Fin n, x i * t ^ (i : ℕ)) '' Set.Icc a b) -
        sInf ((fun t : ℝ => ∑ i : Fin n, x i * t ^ (i : ℕ)) '' Set.Icc a b)) := by
  sorry

end «CAM-Bench-236»
