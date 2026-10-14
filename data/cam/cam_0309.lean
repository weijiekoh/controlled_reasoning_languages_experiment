import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-309»

structure SpectralTraceMaximization where
  n : Type*
  fintype_n : Fintype n
  decEq_n : DecidableEq n
  A : Matrix n n ℝ
  r : ℝ

def SpectralTraceMaximization.feasibleSet (P : SpectralTraceMaximization) :
    Set (Matrix P.n P.n ℝ) :=
  letI := P.fintype_n
  letI := P.decEq_n
  {X | X.IsSymm ∧ Matrix.trace X = P.r ∧ X.PosSemidef ∧ (1 - X).PosSemidef}

def SpectralTraceMaximization.objective (P : SpectralTraceMaximization) :
    Matrix P.n P.n ℝ → ℝ :=
  letI := P.fintype_n
  letI := P.decEq_n
  fun X => Matrix.trace (P.A * X)

theorem spectral_trace_maximization
    (n r : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm)
    (hr_lower : 1 ≤ r)
    (hr_upper : r ≤ n) :
    sSup {t : ℝ | ∃ X : Matrix (Fin n) (Fin n) ℝ,
      X.IsSymm ∧
      Matrix.trace X = (r : ℝ) ∧
      X.PosSemidef ∧
      (1 - X).PosSemidef ∧
      t = Matrix.trace (A * X)} =
      ∑ k : Fin r,
        (by simpa using hA : A.IsHermitian).eigenvalues
          ⟨k.1, Nat.lt_of_lt_of_le k.2 hr_upper⟩ := by
  sorry

end «CAM-Bench-309»
