import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-385»

theorem minimization_of_rejection_supnorm_is_convex_optimization
    (N : ℕ) (Ω_rej : Set (ℝ × ℝ))
    (hN : 1 ≤ N)
    (hΩ : Ω_rej.Nonempty)
    (hΩ_subset : ∀ ω ∈ Ω_rej, 0 ≤ ω.1 ∧ ω.1 ≤ Real.pi ∧ 0 ≤ ω.2 ∧ ω.2 ≤ Real.pi) :
    Convex ℝ
      {h : Fin N → Fin N → ℝ |
        (∑ k : Fin N, ∑ l : Fin N,
          h k l * Real.cos ((k.1 : ℝ) * 0) * Real.cos ((l.1 : ℝ) * 0)) = 1} ∧
    ConvexOn ℝ
      {h : Fin N → Fin N → ℝ |
        (∑ k : Fin N, ∑ l : Fin N,
          h k l * Real.cos ((k.1 : ℝ) * 0) * Real.cos ((l.1 : ℝ) * 0)) = 1}
      (fun h : Fin N → Fin N → ℝ =>
        sSup
          ((fun ω : ℝ × ℝ =>
              |∑ k : Fin N, ∑ l : Fin N,
                h k l * Real.cos ((k.1 : ℝ) * ω.1) * Real.cos ((l.1 : ℝ) * ω.2)|) '' Ω_rej)) := by
  sorry

end «CAM-Bench-385»
