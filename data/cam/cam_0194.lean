import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-194»

open scoped BigOperators

theorem spring_energy_min_concave_on_feasible_set
    (n N p : ℕ)
    (hp₁ : 1 ≤ p)
    (hpn : p ≤ n)
    (m : Fin n → ℝ)
    (hm : ∀ i, 0 < m i)
    (xFixed yFixed : Fin p → ℝ)
    (g kTot : ℝ)
    (A : Matrix (Fin n) (Fin N) ℝ) :
    ConcaveOn ℝ
      {k : Fin N → ℝ | (∀ j, 0 ≤ k j) ∧ (∑ j, k j = kTot)}
      (fun k =>
        sInf
          {e : ℝ |
            ∃ x : Fin n → ℝ, ∃ y : Fin n → ℝ,
              (∀ i : Fin p, x (Fin.castLE hpn i) = xFixed i) ∧
              (∀ i : Fin p, y (Fin.castLE hpn i) = yFixed i) ∧
              e =
                (∑ i, g * m i * y i) +
                  (1 / 2 : ℝ) *
                    ∑ j,
                      k j *
                        (((∑ i, A i j * x i) ^ 2) +
                          ((∑ i, A i j * y i) ^ 2))}) := by
  sorry

end «CAM-Bench-194»
