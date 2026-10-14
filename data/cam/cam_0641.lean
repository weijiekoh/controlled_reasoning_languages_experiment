import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-641»

def euclideanLength {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (dotProduct x x)

def IsLeastSquaresSolution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x_ls : Fin n → ℝ) : Prop :=
  IsMinOn (fun x : Fin n → ℝ => euclideanLength (A.mulVec x - b)) Set.univ x_ls

def norm_equivalence_l2_linf (m : ℕ) : Prop :=
  0 < m ∧
  ∀ z : Fin m → ℝ,
    (1 / Real.sqrt (m : ℝ)) * euclideanLength z ≤ sSup (Set.range fun i : Fin m => |z i|) ∧
    sSup (Set.range fun i : Fin m => |z i|) ≤ euclideanLength z

structure ChebyshevRegressionProblem where
  m : ℕ
  n : ℕ
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  rank_eq : Module.finrank ℝ (LinearMap.range A.toLin') = n

def ChebyshevRegressionProblem.residual (p : ChebyshevRegressionProblem) (x : Fin p.n → ℝ) :
    Fin p.m → ℝ :=
  p.A.mulVec x - p.b

def ChebyshevRegressionProblem.objective (p : ChebyshevRegressionProblem)
    (x : Fin p.n → ℝ) : ℝ :=
  sSup (Set.range fun i : Fin p.m => |p.A.mulVec x i - p.b i|)

def ChebyshevRegressionProblem.isOptimal (p : ChebyshevRegressionProblem) (x : Fin p.n → ℝ) :
    Prop :=
  IsMinOn (fun y : Fin p.n → ℝ => sSup (Set.range fun i : Fin p.m => |p.residual y i|)) Set.univ x

structure LeastSquaresRegressionProblem where
  m : ℕ
  n : ℕ
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ

def LeastSquaresRegressionProblem.residual (p : LeastSquaresRegressionProblem)
    (x : Fin p.n → ℝ) : Fin p.m → ℝ :=
  p.A.mulVec x - p.b

def LeastSquaresRegressionProblem.objective (p : LeastSquaresRegressionProblem)
    (x : Fin p.n → ℝ) : ℝ :=
  euclideanLength (p.residual x)

def LeastSquaresRegressionProblem.isSolution (p : LeastSquaresRegressionProblem)
    (x : Fin p.n → ℝ) : Prop :=
  IsLeastSquaresSolution p.A p.b x

def LeastSquaresRegressionProblem.closedFormCandidate (p : LeastSquaresRegressionProblem)
    (_hInv : Invertible (p.A.transpose * p.A)) : Fin p.n → ℝ :=
  (⅟ (p.A.transpose * p.A)).mulVec (p.A.transpose.mulVec p.b)

theorem leastSquares_residual_linf_le_sqrt_m_mul_chebyshev_optimal
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hrank : Module.finrank ℝ (LinearMap.range A.toLin') = n)
    (x_ch x_ls : Fin n → ℝ)
    (hxch : IsMinOn (fun y : Fin n → ℝ => sSup (Set.range fun i : Fin m => |(A.mulVec y - b) i|)) Set.univ x_ch)
    (hxls : IsLeastSquaresSolution A b x_ls)
    (hnorm : norm_equivalence_l2_linf m) :
    sSup (Set.range fun i : Fin m => |(A.mulVec x_ls - b) i|) ≤
      Real.sqrt (m : ℝ) *
        sSup (Set.range fun i : Fin m => |(A.mulVec x_ch - b) i|) := by
  sorry

end «CAM-Bench-641»
