import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-583»

abbrev InfinityNormApproximationProblem (n m : ℕ) :=
  Matrix (Fin m) (Fin n) ℝ × (Fin m → ℝ)

def InfinityNormApproximationProblem.A {n m : ℕ}
    (p : InfinityNormApproximationProblem n m) : Matrix (Fin m) (Fin n) ℝ :=
  p.1

def InfinityNormApproximationProblem.b {n m : ℕ}
    (p : InfinityNormApproximationProblem n m) : Fin m → ℝ :=
  p.2

def InfinityNormApproximationProblem.objective {n m : ℕ}
    (p : InfinityNormApproximationProblem n m) (x : Fin n → ℝ) : ℝ :=
  sSup (Set.range fun i : Fin m => |p.A.mulVec x i - p.b i|)

def InfinityNormApproximationProblem.isMinimizer {n m : ℕ}
    (p : InfinityNormApproximationProblem n m) (x : Fin n → ℝ) : Prop :=
  ∀ y : Fin n → ℝ, p.objective x ≤ p.objective y

structure InfinityNormApproximationEpigraphProblem (n m : ℕ) where
  base : InfinityNormApproximationProblem n m

def InfinityNormApproximationEpigraphProblem.isFeasible {n m : ℕ}
    (p : InfinityNormApproximationEpigraphProblem n m) (x : Fin n → ℝ) (t : ℝ) : Prop :=
  0 ≤ t ∧
    (∀ i : Fin m, p.base.A.mulVec x i - p.base.b i ≤ t) ∧
    ∀ i : Fin m, -t ≤ p.base.A.mulVec x i - p.base.b i

def InfinityNormApproximationEpigraphProblem.objective {n m : ℕ}
    (p : InfinityNormApproximationEpigraphProblem n m) (_x : Fin n → ℝ) (t : ℝ) : ℝ :=
  t

def InfinityNormApproximationEpigraphProblem.isMinimizer {n m : ℕ}
    (p : InfinityNormApproximationEpigraphProblem n m) (x : Fin n → ℝ) (t : ℝ) : Prop :=
  p.isFeasible x t ∧
    ∀ y : Fin n → ℝ, ∀ s : ℝ, p.isFeasible y s → t ≤ p.objective y s

theorem infinityNormApproximation_equiv_epigraph
    {n m : ℕ} (p : InfinityNormApproximationProblem n m) (x : Fin n → ℝ) :
    (sInf
      (((fun t : ℝ => ((t : ℝ) : EReal)) ''
        {t : ℝ | InfinityNormApproximationEpigraphProblem.isFeasible ⟨p⟩ x t}) : Set EReal) =
      ((p.objective x : ℝ) : EReal)) ∧
    (p.isMinimizer x ↔
      ∃ t : ℝ,
        InfinityNormApproximationEpigraphProblem.isMinimizer ⟨p⟩ x t ∧
          t = p.objective x) := by
  sorry

end «CAM-Bench-583»
