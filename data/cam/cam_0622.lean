import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-622»

theorem avg_mem_fixedPoints_of_finite_matrixGroup
    {n : ℕ} {G : Type*} [Fintype G] [Group G]
    (rho : G → Matrix (Fin n) (Fin n) ℝ)
    (hrho_one : rho 1 = 1)
    (hrho_mul : ∀ g h : G, rho (g * h) = rho g * rho h)
    (x : Fin n → ℝ) :
    let xbar := ((1 : ℝ) / (Fintype.card G : ℝ)) • ∑ Q : G, (rho Q).mulVec x
    let F : Set (Fin n → ℝ) := {y | ∀ Q : G, (rho Q).mulVec y = y}
    xbar ∈ F := by
  sorry

end «CAM-Bench-622»
