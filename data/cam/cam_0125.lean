import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-125»

def IsQuadraticFunction (g : (Fin m → ℝ) → ℝ) : Prop :=
  ∃ (A : Matrix (Fin m) (Fin m) ℝ) (b : Fin m → ℝ) (d : ℝ),
    Aᵀ = A ∧
      ∀ x : Fin m → ℝ,
        g x = (1 / 2 : ℝ) * dotProduct x (fun i => ∑ j : Fin m, A i j * x j) + dotProduct b x + d

theorem composition_with_independent_directions_is_strictly_convex_quadratic
    {n k : ℕ} (hk : 1 ≤ k)
    (x₀ c : Fin n → ℝ) (r : ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ)
    (p : Fin k → (Fin n → ℝ))
    (hp_lin : LinearIndependent ℝ p)
    (hQsymm : Qᵀ = Q)
    (hQpos : ∀ x : Fin n → ℝ, x ≠ 0 →
      0 < dotProduct x (fun i => ∑ j : Fin n, Q i j * x j)) :
    let h : (Fin k → ℝ) → ℝ :=
      fun σ =>
        let x : Fin n → ℝ := fun i => x₀ i + ∑ j : Fin k, σ j * p j i
        (1 / 2 : ℝ) * dotProduct x (fun i => ∑ j : Fin n, Q i j * x j) + dotProduct c x + r
    IsQuadraticFunction h ∧ StrictConvexOn ℝ Set.univ h := by
  sorry

end «CAM-Bench-125»
