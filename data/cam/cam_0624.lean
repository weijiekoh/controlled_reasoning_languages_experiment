import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-624»

def IsConvexFunction {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x y : Fin n → ℝ, ∀ lam ∈ Set.Icc (0 : ℝ) 1,
    f (fun i => lam * x i + (1 - lam) * y i) ≤ lam * f x + (1 - lam) * f y

def IsPermutationMatrix (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ π : Equiv.Perm (Fin n),
    ∀ i j : Fin n, P i j = if j = π i then 1 else 0

open scoped BigOperators

theorem exists_minimizer_const_on_ones_of_convex_permInvariant
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (hfconv : ConvexOn ℝ Set.univ f)
    (hperm : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ),
      f (fun i => x (σ i)) = f x)
    (hmin : ∃ x₀ : Fin n → ℝ, ∀ x : Fin n → ℝ, f x₀ ≤ f x) :
    ∃ (α : ℝ), ∀ x : Fin n → ℝ, f (fun _ : Fin n => α) ≤ f x := by
  sorry

end «CAM-Bench-624»
