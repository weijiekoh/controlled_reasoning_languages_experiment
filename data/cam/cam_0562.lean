import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-562»

def LogConcaveOn (C : Set ℝ) (f : ℝ → ℝ) : Prop :=
  Convex ℝ C ∧
    Set.MapsTo f C (Set.Ioi 0) ∧
      ∀ ⦃x y : ℝ⦄, x ∈ C → y ∈ C →
        ∀ ⦃θ : ℝ⦄, θ ∈ Set.Icc (0 : ℝ) 1 →
          f (θ * x + (1 - θ) * y) ≥ Real.rpow (f x) θ * Real.rpow (f y) (1 - θ)

theorem det_div_trace_logConcaveOn_posDef
    (n : Type*) [Fintype n] [DecidableEq n] :
    ConcaveOn ℝ
      {X : Matrix n n ℝ | X.PosDef}
      (fun X : Matrix n n ℝ => Real.log (Matrix.det X) - Real.log (Matrix.trace X)) := by
  sorry

end «CAM-Bench-562»
