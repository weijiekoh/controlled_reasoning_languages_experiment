import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-287»

def IsPosynomial {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ m : ℕ, ∃ c : Fin m → ℝ, ∃ a : Fin n → Fin m → ℝ,
    (∀ k : Fin m, 0 < c k) ∧
    ∀ x : Fin n → ℝ,
      (∀ i : Fin n, 0 < x i) →
        f x = ∑ k : Fin m, c k * ∏ i : Fin n, (x i) ^ (a i k)

theorem posynomial_geometric_convexity
    {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : IsPosynomial f)
    (x y : Fin n → ℝ) (θ : ℝ)
    (hx : ∀ i : Fin n, 0 < x i)
    (hy : ∀ i : Fin n, 0 < y i)
    (hfx : 0 < f x)
    (hfy : 0 < f y)
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) :
    let z : Fin n → ℝ := fun i => Real.rpow (x i) θ * Real.rpow (y i) (1 - θ)
    f z ≤ Real.rpow (f x) θ * Real.rpow (f y) (1 - θ) := by
  sorry

end «CAM-Bench-287»
