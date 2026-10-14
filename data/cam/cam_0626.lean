import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-626»

structure StochasticConvexProgram
    (Ω : Type*)
    [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (n k m : ℕ) where
  u : Ω → EuclideanSpace ℝ (Fin k)
  f : Fin (m + 1) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k) → ℝ
  convex_in_x :
    ∀ (i : Fin (m + 1)) (ω : Ω),
      ConvexOn ℝ Set.univ (fun x => f i x (u ω))
  integrable :
    ∀ (i : Fin (m + 1)) (x : EuclideanSpace ℝ (Fin n)),
      MeasureTheory.Integrable (fun ω => f i x (u ω)) μ

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
variable {n k m : ℕ}

def StochasticConvexProgram.objective
    (P : StochasticConvexProgram Ω μ n k m)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ ω, P.f 0 x (P.u ω) ∂μ

def StochasticConvexProgram.constraint
    (P : StochasticConvexProgram Ω μ n k m)
    (i : Fin m)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ ω, P.f i.succ x (P.u ω) ∂μ

def StochasticConvexProgram.isFeasible
    (P : StochasticConvexProgram Ω μ n k m)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ i : Fin m, P.constraint i x ≤ 0

theorem stochastic_convex_program_is_convex
    (P : StochasticConvexProgram Ω μ n k m) :
    ConvexOn ℝ Set.univ P.objective ∧
      ∀ i : Fin m, ConvexOn ℝ Set.univ (P.constraint i) := by
  sorry

end «CAM-Bench-626»
