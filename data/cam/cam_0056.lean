import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-56»

structure EqualityConstrainedQuadraticProgram where
  n : ℕ
  m : ℕ
  G : Matrix (Fin n) (Fin n) ℝ
  c : Fin n → ℝ
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  Z : Matrix (Fin n) (Fin (n - m)) ℝ
  full_row_rank : Function.Surjective A.toLin'
  nullspace_parametrization : ∀ d : Fin n → ℝ, A.mulVec d = 0 ↔ ∃ p : Fin (n - m) → ℝ, Z.mulVec p = d

def EqualityConstrainedQuadraticProgram.objective
    (P : EqualityConstrainedQuadraticProgram) (x : Fin P.n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * dotProduct x (P.G.mulVec x) + dotProduct x P.c

def EqualityConstrainedQuadraticProgram.isFeasible
    (P : EqualityConstrainedQuadraticProgram) (x : Fin P.n → ℝ) : Prop :=
  P.A.mulVec x = P.b

theorem EqualityConstrainedQuadraticProgram.no_finite_solution_of_exists_negative_direction
    (P : EqualityConstrainedQuadraticProgram)
    (hfeasible : ∃ x : Fin P.n → ℝ, P.isFeasible x)
    (hneg :
      ∃ p : Fin (P.n - P.m) → ℝ,
        dotProduct p ((P.Z.transpose.mulVec) (P.G.mulVec (P.Z.mulVec p))) < 0) :
    ∀ x : Fin P.n → ℝ, P.isFeasible x →
      ∃ y : Fin P.n → ℝ, P.isFeasible y ∧ P.objective y < P.objective x := by
  sorry

end «CAM-Bench-56»
