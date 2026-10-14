import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-183»

theorem minimum_value_found_by_convex_optimization_problem
    (n m : ℕ)
    (hn : 1 ≤ n)
    (hm : 1 ≤ m)
    (e : Fin n → ℝ)
    (ρ : ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) :
    let objective :
        ((Fin (n + 1) → ℝ) × (Fin n → ℝ) × (Fin m → ℝ)) → ℝ :=
      fun y => y.1 0 + ∑ j, y.2.2 j
    let feasible :
        Set ((Fin (n + 1) → ℝ) × (Fin n → ℝ) × (Fin m → ℝ)) :=
      { y : (Fin (n + 1) → ℝ) × (Fin n → ℝ) × (Fin m → ℝ) |
        (∀ t : Fin n, y.1 (Fin.succ t) = (1 + ρ) * y.1 (Fin.castSucc t) - y.2.1 t) ∧
        (∀ t : Fin (n + 1), 0 ≤ y.1 t) ∧
        (∀ j : Fin m, 0 ≤ y.2.2 j) ∧
        (∀ t : Fin n, e t ≤ y.2.1 t + ∑ j, P t j * y.2.2 j) }
    ConvexOn ℝ feasible objective ∧
      Convex ℝ feasible := by
  sorry

end «CAM-Bench-183»
