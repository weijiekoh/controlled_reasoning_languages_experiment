import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-537»

open scoped ENNReal

def M_C {n : ℕ} (C : Set (Fin n → ℝ)) : (Fin n → ℝ) → ℝ≥0∞ :=
  fun x =>
    sInf (ENNReal.ofReal '' {t : ℝ | 0 < t ∧ (fun i => x i / t) ∈ C})

theorem minkowskiFunctional_convex
    {n : ℕ} {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) :
    ∀ x y : Fin n → ℝ, ∀ lam : ℝ,
      0 ≤ lam → lam ≤ 1 →
      M_C C (fun i => lam * x i + (1 - lam) * y i) ≤
        ENNReal.ofReal lam * M_C C x +
        ENNReal.ofReal (1 - lam) * M_C C y := by
  sorry

end «CAM-Bench-537»
