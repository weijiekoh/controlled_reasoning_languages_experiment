import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-171»

def giniCoefficient {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  let xsorted : List ℝ := ((List.finRange n).map z).mergeSort (· ≤ ·)
  let f : Fin (n + 1) → ℝ := fun i =>
    ((List.take i xsorted).sum) / (∑ k : Fin n, z k)
  (2 : ℝ) / (n : ℝ) * ∑ i : Fin n, ((((i : ℕ) + 1 : ℕ) : ℝ) / (n : ℝ) - f ⟨i + 1, Nat.succ_lt_succ i.is_lt⟩)

theorem gini_coefficient_quasiconvex_on_nonnegative_nonzero {n : ℕ} (hn : 1 ≤ n) :
    ∀ x y : Fin n → ℝ,
      (∀ i, 0 ≤ x i) → x ≠ 0 →
      (∀ i, 0 ≤ y i) → y ≠ 0 →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      (∀ i, 0 ≤ θ * x i + (1 - θ) * y i) →
      (fun i => θ * x i + (1 - θ) * y i) ≠ 0 →
      giniCoefficient (fun i => θ * x i + (1 - θ) * y i) ≤
        max (giniCoefficient x) (giniCoefficient y) := by
  sorry

end «CAM-Bench-171»
