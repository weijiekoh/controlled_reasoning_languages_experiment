import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-702»

structure UnconstrainedQuadraticProgram (n : ℕ) where
  P : Matrix (Fin n) (Fin n) ℝ
  q : Fin n → ℝ
  r : ℝ
  symm : P.IsSymm

def UnconstrainedQuadraticProgram.objective_fn {n : ℕ}
    (qp : UnconstrainedQuadraticProgram n) (x : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * dotProduct x (fun i => dotProduct (fun j => qp.P i j) x) +
    dotProduct qp.q x + qp.r

def UnconstrainedQuadraticProgram.feasibleSet {n : ℕ}
    (_qp : UnconstrainedQuadraticProgram n) : Set (Fin n → ℝ) :=
  Set.univ

def UnconstrainedQuadraticProgram.objective {n : ℕ} (qp : UnconstrainedQuadraticProgram n)
    (x : Fin n → ℝ) : ℝ :=
  qp.objective_fn x

theorem unconstrainedQuadraticProgram_unbounded_below_of_no_stationary_point
    {n : ℕ} (qp : UnconstrainedQuadraticProgram n)
    (hPsd : ∀ x : Fin n → ℝ, 0 ≤ dotProduct x (fun i => dotProduct (fun j => qp.P i j) x))
    (hNoSol : ¬ ∃ x : Fin n → ℝ, (fun i => dotProduct (fun j => qp.P i j) x) = (fun i => -qp.q i)) :
    ∀ M : ℝ, ∃ x : Fin n → ℝ, qp.objective x < M := by
  sorry

end «CAM-Bench-702»
