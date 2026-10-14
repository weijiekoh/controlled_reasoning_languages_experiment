import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-226»

def Quasiconvex (g : ℝ → ℝ) : Prop :=
  ∀ α : ℝ, Convex ℝ {z : ℝ | g z ≤ α}

theorem perspective_quasiconvex
    {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) :
    QuasiconvexOn ℝ {z : (Fin n → ℝ) × ℝ | 0 < z.2}
      (fun z : (Fin n → ℝ) × ℝ => f ((1 / z.2) • z.1)) := by
  sorry

end «CAM-Bench-226»
