import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-221»

theorem sigmoid_sum_not_quasiconcave_counterexample :
    ∃ (n K : ℕ) (l u : Fin n → ℝ) (w : Fin K → Fin n → ℝ) (v P : Fin K → ℝ),
      (∀ i, l i < 0 ∧ 0 < u i) ∧
      (let g : ℝ → ℝ := fun z => 1 / (1 + Real.exp (-z))
       let f : Fin K → (Fin n → ℝ) → ℝ := fun k x => g ((∑ i : Fin n, w k i * x i) + v k)
       let V : (Fin n → ℝ) → ℝ := fun x => ∑ k : Fin K, P k * f k x
       let C : Set (Fin n → ℝ) := {x | ∀ i, l i ≤ x i ∧ x i ≤ u i}
       (∀ k, 0 ≤ P k) ∧
       (∃ x y, x ∈ C ∧ y ∈ C ∧ V x ≠ V y) ∧
       ¬ QuasiconcaveOn ℝ C V) := by
  sorry

end «CAM-Bench-221»
