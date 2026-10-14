import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-642»

def logSumExp {m : ℕ} (z : Fin m → ℝ) : ℝ :=
  Real.log (∑ i : Fin m, Real.exp (z i))

structure PiecewiseLinearMinimizationProblem where
  n : ℕ
  φ : (Fin n → ℝ) → ℝ
  f₀ : (Fin n → ℝ) → ℝ

def PiecewiseLinearMinimizationProblem.pPwlStar
    (P : PiecewiseLinearMinimizationProblem) : ℝ :=
  sInf (Set.range P.φ)

def PiecewiseLinearMinimizationProblem.pGpStar
    (P : PiecewiseLinearMinimizationProblem) : ℝ :=
  sInf (Set.range P.f₀)

def PiecewiseLinearMinimizationProblem.isMinimizerPwl
    (P : PiecewiseLinearMinimizationProblem) (x : Fin P.n → ℝ) : Prop :=
  P.φ x = P.pPwlStar

def PiecewiseLinearMinimizationProblem.isMinimizerGp
    (P : PiecewiseLinearMinimizationProblem) (x : Fin P.n → ℝ) : Prop :=
  P.f₀ x = P.pGpStar

theorem gpStar_sub_pPwlStar_bounds
    (P : PiecewiseLinearMinimizationProblem)
    (m : ℕ)
    (hm : 1 ≤ m)
    (a : Fin m → Fin P.n → ℝ)
    (b : Fin m → ℝ)
    (hφ :
      P.φ = fun x =>
        sSup (Set.range (fun i : Fin m => ∑ j : Fin P.n, a i j * x j + b i)))
    (hf₀ :
      P.f₀ = fun x =>
        logSumExp (fun i : Fin m => ∑ j : Fin P.n, a i j * x j + b i)) :
    0 ≤ P.pGpStar - P.pPwlStar ∧ P.pGpStar - P.pPwlStar ≤ Real.log m := by
  sorry

end «CAM-Bench-642»
