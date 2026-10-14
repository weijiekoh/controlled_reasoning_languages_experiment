import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-484»

theorem expectedValue_convex_perturbation_monotone
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x₀ : Fin n → ℝ}
    {v : Ω → Fin n → ℝ} {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (hf : ConvexOn ℝ Set.univ f)
    (hv_int : MeasureTheory.Integrable v μ)
    (hv_mean_zero : ∫ ω, v ω ∂μ = 0)
    (hfin : ∀ t : ℝ, 0 ≤ t → MeasureTheory.Integrable (fun ω => f (x₀ + t • v ω)) μ) :
    MonotoneOn (fun t : ℝ => ∫ ω, f (x₀ + t • v ω) ∂μ) (Set.Ici 0) := by
  sorry

end «CAM-Bench-484»
