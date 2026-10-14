import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-734»

structure EqualityConstrainedLeastSquares where
  n : ℕ
  p : ℕ
  m : ℕ
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  G : Matrix (Fin p) (Fin n) ℝ
  h : Fin p → ℝ

def EqualityConstrainedLeastSquares.residual
    (P : EqualityConstrainedLeastSquares) (x : Fin P.n → ℝ) : Fin P.m → ℝ :=
  fun i => (∑ j : Fin P.n, P.A i j * x j) - P.b i

def EqualityConstrainedLeastSquares.objective
    (P : EqualityConstrainedLeastSquares) (x : Fin P.n → ℝ) : ℝ :=
  ‖P.residual x‖ ^ 2

def EqualityConstrainedLeastSquares.feasible
    (P : EqualityConstrainedLeastSquares) (x : Fin P.n → ℝ) : Prop :=
  ∀ i : Fin P.p, (∑ j : Fin P.n, P.G i j * x j) = P.h i

def dualProblem
    {n m : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    ((Fin m → ℝ) → ℝ) :=
  fun lam =>
    sInf {t : ℝ | ∃ x : Fin n → ℝ, t = f x + ∑ i : Fin m, lam i * ((∑ j : Fin n, A i j * x j) - b i)}

def EqualityConstrainedLeastSquares.IsPrimalOptimal
    (P : EqualityConstrainedLeastSquares) (xStar : Fin P.n → ℝ) : Prop :=
  P.feasible xStar ∧ ∀ x : Fin P.n → ℝ, P.feasible x → P.objective xStar ≤ P.objective x

def IsDualOptimal
    {n m : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (lamStar : Fin m → ℝ) : Prop :=
  ∀ lam : Fin m → ℝ,
    dualProblem f A b lam ≤ dualProblem f A b lamStar

structure EqualityConstrainedLeastSquaresProblem where
  toProblem : EqualityConstrainedLeastSquares

def EqualityConstrainedLeastSquaresProblem.is_feasible
    (P : EqualityConstrainedLeastSquaresProblem) (x : Fin P.toProblem.n → ℝ) : Prop :=
  P.toProblem.feasible x

def EqualityConstrainedLeastSquaresProblem.objective_value
    (P : EqualityConstrainedLeastSquaresProblem) (x : Fin P.toProblem.n → ℝ) : ℝ :=
  P.toProblem.objective x

theorem equality_constrained_least_squares_kkt_and_explicit_solution
    (P : EqualityConstrainedLeastSquares)
    (rankA : P.A.rank = P.n)
    (rankG : P.G.rank = P.p) :
    let Q : Matrix (Fin P.n) (Fin P.n) ℝ := P.A.transpose * P.A
    let q : Fin P.n → ℝ := fun i => ∑ j : Fin P.m, P.A j i * P.b j
    ∃ xStar : Fin P.n → ℝ,
      ∃ lamStar : Fin P.p → ℝ,
        P.IsPrimalOptimal xStar ∧
        (∀ lam : Fin P.p → ℝ,
          dualProblem P.objective P.G P.h lam ≤ dualProblem P.objective P.G P.h lamStar) ∧
        (∀ i : Fin P.n,
          2 * (∑ j : Fin P.n, Q i j * xStar j) +
              (∑ k : Fin P.p, P.G k i * lamStar k) =
            2 * q i) ∧
        (∀ i : Fin P.p,
          ∑ j : Fin P.n, P.G i j * xStar j = P.h i) ∧
        lamStar =
          (fun i =>
            2 * (∑ j : Fin P.p,
              ((P.G * (Q⁻¹) * P.G.transpose)⁻¹) i j *
                ((∑ k : Fin P.n, (P.G * (Q⁻¹)) j k * q k) - P.h j))) ∧
        xStar =
          (fun i =>
            ∑ j : Fin P.n, (Q⁻¹) i j *
              (q j - ((1 / 2 : ℝ) * ∑ k : Fin P.p, P.G k j * lamStar k))) := by
  sorry

end «CAM-Bench-734»
