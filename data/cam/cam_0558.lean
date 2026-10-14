import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-558»

def LogConcaveOn (D : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Convex ℝ D ∧
  (∀ x ∈ D, 0 < f x) ∧
  ConcaveOn ℝ D (fun x => Real.log (f x))

theorem logConcaveOn_iff_ratio_le_exp_inner_deriv
    {n : ℕ} {D : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hD : Convex ℝ D)
    (hf : DifferentiableOn ℝ f D)
    (hpos : ∀ x ∈ D, 0 < f x) :
    LogConcaveOn D f ↔
      ∀ x ∈ D, ∀ y ∈ D,
        f y / f x ≤
          Real.exp (((fderiv ℝ f x) (y - x)) / f x) := by
  sorry

end «CAM-Bench-558»
