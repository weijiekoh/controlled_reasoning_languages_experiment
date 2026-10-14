import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-198»

structure MinimumFuelDescentFixedTouchdownTime where
  K : ℕ
  h : ℝ
  γ : ℝ
  thrustProfiles : Set (Fin K → EuclideanSpace ℝ (Fin 3))

def MinimumFuelDescentFixedTouchdownTime.objective
    (P : MinimumFuelDescentFixedTouchdownTime)
    (f : Fin P.K → EuclideanSpace ℝ (Fin 3)) : ℝ :=
  P.γ * P.h * ∑ k : Fin P.K, ‖f k‖

def MinimumFuelDescentFixedTouchdownTime.is_feasible
    (P : MinimumFuelDescentFixedTouchdownTime)
    (f : Fin P.K → EuclideanSpace ℝ (Fin 3)) : Prop :=
  f ∈ P.thrustProfiles

def MinimumFuelDescentFixedTouchdownTime.solution_set
    (P : MinimumFuelDescentFixedTouchdownTime) : Set (Fin P.K → EuclideanSpace ℝ (Fin 3)) :=
  P.thrustProfiles

theorem minimumFuelDescentFixedTouchdownTime_equiv_convex_optimization
    (P : MinimumFuelDescentFixedTouchdownTime)
    (hprofiles_convex : Convex ℝ P.thrustProfiles)
    (hγ_nonneg : 0 ≤ P.γ * P.h) :
    Convex ℝ P.solution_set ∧
      ConvexOn ℝ Set.univ (P.objective) := by
  sorry

end «CAM-Bench-198»
