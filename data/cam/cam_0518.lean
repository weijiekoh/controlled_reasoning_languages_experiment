import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-518»

def probabilitySimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1}

theorem variance_on_probabilitySimplex_concave_quasiconcave_not_convex_not_quasiconvex
    (n : ℕ)
    (hn : 2 ≤ n)
    (a : Fin n → ℝ)
    (hmono : StrictMono a) :
    let variance : (Fin n → ℝ) → ℝ :=
      fun p =>
        let ex : ℝ := ∑ i, a i * p i
        ∑ i, p i * (a i - ex) ^ 2
    ConcaveOn ℝ (probabilitySimplex n : Set (Fin n → ℝ)) variance ∧
      QuasiconcaveOn ℝ (probabilitySimplex n : Set (Fin n → ℝ)) variance ∧
      ¬ ConvexOn ℝ (probabilitySimplex n : Set (Fin n → ℝ)) variance ∧
      ¬ QuasiconvexOn ℝ (probabilitySimplex n : Set (Fin n → ℝ)) variance := by
  sorry

end «CAM-Bench-518»
