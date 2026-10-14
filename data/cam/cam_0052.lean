import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-52»

open Matrix

theorem jacobian_correction_satisfies_linearized_constraint
    {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (c : (n → ℝ) → (m → ℝ)) (xk pk : n → ℝ) (Ak : Matrix m n ℝ)
    (hAk_jacobian : Ak = fun i j => fderiv ℝ c xk (Pi.single j (1 : ℝ)) i)
    [Invertible (Ak * Ak.transpose)]
    : Ak.mulVec
        (-(Ak.transpose.mulVec
            ((⅟ (Ak * Ak.transpose)).mulVec (c (xk + pk))))) +
        c (xk + pk) = 0 := by
  sorry

end «CAM-Bench-52»
