import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-443»

open scoped BigOperators

theorem perspective_image_convexHull_eq_convexHull_div
    {n K : ℕ} (v : Fin K → Fin n → ℝ) (t : Fin K → ℝ)
    (ht : ∀ i, 0 < t i) :
    (Set.image
      (fun y : (Fin n → ℝ) × ℝ => (fun j : Fin n => y.1 j / y.2))
      (convexHull ℝ (Set.range fun i : Fin K => ((v i, t i) : (Fin n → ℝ) × ℝ)))) =
      convexHull ℝ (Set.range fun i : Fin K => (fun j => v i j / t i : Fin n → ℝ)) := by
  sorry

end «CAM-Bench-443»
