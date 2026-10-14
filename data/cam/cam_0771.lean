import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-771»

def HasLLipschitzGradient {d : Type*} [NormedAddCommGroup d] [InnerProductSpace ℝ d]
    [CompleteSpace d] (f : d → ℝ) (L : ℝ) : Prop :=
  Differentiable ℝ f ∧
    ∀ x y : d, ‖∇ f x - ∇ f y‖ ≤ L * ‖x - y‖

def StochasticGradientDescentStep {d : Type*} [NormedAddCommGroup d] [InnerProductSpace ℝ d]
    (xk gk : d) (αk : ℝ) : d :=
  xk - αk • gk

def IsStochasticGradientEstimator {d : Type*} [NormedAddCommGroup d] [InnerProductSpace ℝ d]
    [CompleteSpace d] (f : d → ℝ) (xk gk : d) : Prop :=
  HasGradientAt f gk xk

def FiniteSumStochasticGradient {d : Type*} [NormedAddCommGroup d] [InnerProductSpace ℝ d]
    [CompleteSpace d] {ι : Type*} (fi : ι → d → ℝ) (sk : ι) (xk : d) : d :=
  ∇ (fi sk) xk

theorem sgd_stochastic_gradient_norm_sq_le_lipschitz_dist_sq_plus_variance
    {d : Type*} [NormedAddCommGroup d] [InnerProductSpace ℝ d] [CompleteSpace d]
    {N : ℕ} (f : d → ℝ) (fi : Fin N → d → ℝ) (L : ℝ) (xk xstar : d)
    (havg : ∀ x, f x = (1 / (N : ℝ)) * ∑ i : Fin N, fi i x)
    (hL : HasLLipschitzGradient f L)
    (hmin : IsLocalMin f xstar) :
    (∑ i : Fin N, ‖FiniteSumStochasticGradient fi i xk‖ ^ 2) / N
      ≤ L ^ 2 * ‖xk - xstar‖ ^ 2
        + (∑ i : Fin N, ‖FiniteSumStochasticGradient fi i xk - ∇ f xk‖ ^ 2) / N := by
  sorry

end «CAM-Bench-771»
