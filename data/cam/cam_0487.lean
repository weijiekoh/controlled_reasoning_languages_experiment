import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-487»

def bregmanDivergence {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Set E) (f : E → ℝ) (hs : Convex ℝ s)
    (hf_diff : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hf_conv : ConvexOn ℝ s f)
    (u v : E) (hu : u ∈ s) (hv : v ∈ s) : ℝ :=
  f u - f v - fderiv ℝ f v (u - v)

def kullbackLeiblerDivergence {n : ℕ} (u v : Fin n → ℝ)
    (hu : ∀ i, 0 < u i)
    (hv : ∀ i, 0 < v i) : ℝ :=
  ∑ i : Fin n, ((u i) * Real.log ((u i) / (v i)) - (u i) + (v i))

theorem kullbackLeiblerDivergence_nonneg_and_eq_zero_iff {n : ℕ} (u v : Fin n → ℝ)
    (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i) :
    0 ≤ kullbackLeiblerDivergence u v hu hv ∧
      (kullbackLeiblerDivergence u v hu hv = 0 ↔ u = v) := by
  sorry

end «CAM-Bench-487»
