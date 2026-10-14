import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-328»

structure QuadraticTrustRegionProblem (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  b : Fin n → ℝ

def QuadraticTrustRegionProblem.objective {n : ℕ}
    (p : QuadraticTrustRegionProblem n) (x : Fin n → ℝ) : ℝ :=
  dotProduct x (p.A *ᵥ x) + 2 * dotProduct p.b x

def QuadraticTrustRegionProblem.feasibleSet {n : ℕ}
    (_p : QuadraticTrustRegionProblem n) : Set (Fin n → ℝ) :=
  {x | dotProduct x x ≤ 1}

def QuadraticTrustRegionProblem.isFeasible {n : ℕ} (p : QuadraticTrustRegionProblem n)
    (x : Fin n → ℝ) : Prop :=
  x ∈ p.feasibleSet

theorem trust_region_global_minimizer_exists_kkt_multiplier
    {n : ℕ} (p : QuadraticTrustRegionProblem n) (x : Fin n → ℝ)
    (h_symm : p.A.IsSymm)
    (h_min :
      x ∈ p.feasibleSet ∧
        ∀ y : Fin n → ℝ, y ∈ p.feasibleSet → p.objective x ≤ p.objective y) :
    ∃ lam : ℝ,
      x ∈ p.feasibleSet ∧
      0 ≤ lam ∧
      (p.A + lam • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
      ((p.A + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x = (fun i => -p.b i)) ∧
      lam * (1 - dotProduct x x) = 0 := by
  sorry

end «CAM-Bench-328»
