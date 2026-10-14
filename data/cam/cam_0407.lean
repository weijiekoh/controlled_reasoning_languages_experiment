import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-407»

open Matrix

theorem initial_point_feasible_and_S_not_closed :
    let A : Matrix (Fin 2) (Fin 3) ℝ :=
      !![2, 1, 0;
        1, 1, 1]
    let b : Fin 2 → ℝ := ![1, 1]
    let x0 : Fin 3 → ℝ := ![(1 : ℝ) / 20, 9 / 10, (1 : ℝ) / 20]
    let f : (Fin 3 → ℝ) → ℝ := fun x =>
      ∑ i : Fin 3, x i * Real.log (x i)
    let S : Set (Fin 3 → ℝ) := {x | (∀ i, 0 < x i) ∧ A.mulVec x = b ∧ f x ≤ f x0}
    A.mulVec x0 = b ∧ ¬ IsClosed S := by
  sorry

end «CAM-Bench-407»
