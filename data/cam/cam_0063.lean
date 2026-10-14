import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-63»

def activeSet {n : ℕ} (l u x : Fin n → ℝ) : Fin n → Bool × Bool :=
  fun i => (x i = l i, x i = u i)

def feasiblePoint {n : ℕ} (l u x : Fin n → ℝ) : Prop :=
  ∀ i, l i ≤ x i ∧ x i ≤ u i

def feasibleSet {n : ℕ} (l u : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | feasiblePoint l u x}

structure BoundConstrainedOptimizationProblem (n : ℕ) where
  l : Fin n → ℝ
  u : Fin n → ℝ
  objective : (Fin n → ℝ) → ℝ

def BoundConstrainedOptimizationProblem.feasibleSet {n : ℕ}
    (p : BoundConstrainedOptimizationProblem n) : Set (Fin n → ℝ) :=
  {x | ∀ i, p.l i ≤ x i ∧ x i ≤ p.u i}

structure ExtendedBoundConstrainedOptimizationProblem (n : ℕ) where
  l : Fin n → WithTop (WithBot ℝ)
  u : Fin n → WithTop (WithBot ℝ)
  objective : (Fin n → ℝ) → ℝ
  bounds_ordered : ∀ i, l i ≤ u i
  feasible_nonempty : ∃ x : Fin n → ℝ, ∀ i, l i ≤ (x i : WithTop (WithBot ℝ)) ∧ ((x i : WithTop (WithBot ℝ)) ≤ u i)

def ExtendedBoundConstrainedOptimizationProblem.isFeasible {n : ℕ}
    (p : ExtendedBoundConstrainedOptimizationProblem n) (x : Fin n → ℝ) : Prop :=
  ∀ i, p.l i ≤ (x i : WithTop (WithBot ℝ)) ∧ ((x i : WithTop (WithBot ℝ)) ≤ p.u i)

def ExtendedBoundConstrainedOptimizationProblem.feasibleSet {n : ℕ}
    (p : ExtendedBoundConstrainedOptimizationProblem n) : Set (Fin n → ℝ) :=
  {x | p.isFeasible x}

theorem card_activeSet_range_le_three_pow
    {n : ℕ} (l u : Fin n → ℝ) :
    ∃ s : Finset (Fin n → Bool × Bool),
      (∀ x, feasiblePoint l u x → activeSet l u x ∈ s) ∧ s.card ≤ 3 ^ n := by
  sorry

end «CAM-Bench-63»
