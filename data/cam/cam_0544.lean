import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-544»

open scoped BigOperators

def convexConjugate {n : ℕ} (f : (Fin n → ℝ) → WithTop ℝ) : (Fin n → ℝ) → WithTop ℝ :=
  fun y => sSup (Set.range fun x : Fin n → ℝ => ((↑(∑ i, y i * x i : ℝ) : WithTop ℝ) - f x))

theorem convexConjugate_neg_geomMean_eq_indicator_nonpos_prod_ge_one
    {n : ℕ} (hn : 1 ≤ n) :
    convexConjugate
      (fun x : Fin n → ℝ =>
        if hx : ∀ i, 0 < x i then
          ((-Real.rpow (∏ i, x i) (1 / (n : ℝ)) : ℝ) : WithTop ℝ)
        else
          (⊤ : WithTop ℝ))
      =
      fun y : Fin n → ℝ =>
        if hy : (∀ i, y i ≤ 0) ∧ (1 : ℝ) ≤ (n : ℝ) ^ n * ∏ i, (-(y i)) then
          (0 : WithTop ℝ)
        else
          ⊤ := by
  sorry

end «CAM-Bench-544»
