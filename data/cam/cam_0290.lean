import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-290»

def IndependentRandomVariables
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) {α : Type*}
    (ω : Fin N → Ω → α)
    [MeasurableSpace α] : Prop :=
  (∀ i, Measurable (ω i)) ∧
  ∀ s : Fin N → Set α,
    (∀ i, MeasurableSet (s i)) →
      P (⋂ i, ω i ⁻¹' s i) = ∏ i, P (ω i ⁻¹' s i)

def SameDistribution
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    {α : Type*} [MeasurableSpace α] (ξ η : Ω → α) : Prop :=
  ∀ s : Set α, MeasurableSet s → P (ξ ⁻¹' s) = P (η ⁻¹' s)

open scoped BigOperators

theorem expected_empirical_optimum_le_optimum
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (n N : ℕ)
    (hN : 1 ≤ N)
    (f : (Fin n → ℝ) → Ω → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (ωSamples : Fin N → Ω → Ω)
    (pStar : ℝ)
    (pHatStar : Ω → ℝ)
    (hf_convex : ∀ ω0 : Ω, ConvexOn ℝ Set.univ (fun x : Fin n → ℝ => f x ω0))
    (hf_measurable : ∀ x : Fin n → ℝ, Measurable (f x))
    (hf_integrable : ∀ x : Fin n → ℝ, MeasureTheory.Integrable (f x) P)
    (hF : ∀ x : Fin n → ℝ, F x = ∫ ω0, f x ω0 ∂P)
    (hω_indep : IndependentRandomVariables P ωSamples)
    (hω_same_dist : ∀ i : Fin N, SameDistribution P (ωSamples i) (fun ω0 : Ω => ω0))
    (hpStar : sInf (Set.range F) = pStar)
    (hpHatStar_measurable : Measurable pHatStar)
    (hpHatStar_integrable : MeasureTheory.Integrable pHatStar P)
    (hpHatStar : ∀ ω0 : Ω,
      sInf (Set.range (fun x : Fin n → ℝ => (1 / (N : ℝ)) * ∑ i, f x (ωSamples i ω0))) = pHatStar ω0) :
    ∫ ω0, pHatStar ω0 ∂P ≤ pStar := by
  sorry

end «CAM-Bench-290»
