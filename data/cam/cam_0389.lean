import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-389»

def IsQuasiconvexOptimizationProblem
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (X : Set E) (f : E → ℝ) : Prop :=
  ∀ t : ℝ, Convex ℝ {x | x ∈ X ∧ f x ≤ t}

theorem feasibility_sets_convex_and_filter_problem_quasiconvex
    (N : ℕ) (α : ℝ) (hα : 0 ≤ α) :
    let H : (Fin (N + 1) → ℝ) → ℝ → ℝ :=
      fun a ω => ∑ k : Fin (N + 1), a k * Real.cos ((k : ℝ) * ω)
    let F : ℝ → Set (Fin (N + 1) → ℝ) :=
      fun t =>
        {a | (∀ ω ∈ Set.Icc (0 : ℝ) (Real.pi / 3), 0.89 ≤ H a ω ∧ H a ω ≤ 1.12) ∧
             (∀ ω ∈ Set.Icc t Real.pi, |H a ω| ≤ α)}
    let feasibleT : Set ℝ :=
      {t : ℝ | t ∈ Set.Icc (0 : ℝ) Real.pi ∧ (F t).Nonempty}
    (∀ t ∈ Set.Icc (0 : ℝ) Real.pi, Convex ℝ (F t)) ∧
      IsQuasiconvexOptimizationProblem
        feasibleT
        (fun t => t) := by
  sorry

end «CAM-Bench-389»
