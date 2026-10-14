import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-545»

def convexConjugate {n : ℕ} (f : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun y => sSup {r : EReal | ∃ x : Fin n → ℝ, r = (∑ i : Fin n, y i * x i) - f x}

def convexConjugateProd {n : ℕ} (f : ((Fin n → ℝ) × ℝ) → EReal) :
    ((Fin n → ℝ) × ℝ) → EReal :=
  fun ys => sSup
    {r : EReal | ∃ xt : (Fin n → ℝ) × ℝ, r = (∑ i : Fin n, ys.1 i * xt.1 i) + ys.2 * xt.2 - f xt}

theorem convexConjugateProd_log_barrier_eq
    (n : ℕ)
    (f : ((Fin n → ℝ) × ℝ) → EReal)
    (hf :
      f = fun xt : (Fin n → ℝ) × ℝ =>
          if Real.sqrt (∑ i : Fin n, (xt.1 i) ^ 2) < xt.2 then
            ((-Real.log (xt.2 ^ 2 - ∑ i : Fin n, (xt.1 i) ^ 2) : ℝ) : EReal)
          else ⊤) :
    convexConjugateProd f =
      fun ys : ((Fin n → ℝ) × ℝ) =>
        if Real.sqrt (∑ i : Fin n, (ys.1 i) ^ 2) < -ys.2 then
          (((-2 + Real.log 4 - Real.log (ys.2 ^ 2 - ∑ i : Fin n, (ys.1 i) ^ 2)) : ℝ) : EReal)
        else ⊤ := by
  sorry

end «CAM-Bench-545»
