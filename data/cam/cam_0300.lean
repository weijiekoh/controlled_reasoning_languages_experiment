import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-300»

open scoped BigOperators

theorem power_constraint_set_convex
    (m n : ℕ)
    (hm : 10 ≤ m)
    (a : Fin n → Fin m → ℝ)
    (I_des : ℝ)
    (hI : 0 < I_des) :
    Convex ℝ
      {p : Fin m → ℝ |
        (∀ j, 0 ≤ p j) ∧
        ∀ S : Finset (Fin m),
          S.card = 10 →
            Finset.sum S p ≤ (1 / 2 : ℝ) * ∑ j : Fin m, p j} := by
  sorry

end «CAM-Bench-300»
