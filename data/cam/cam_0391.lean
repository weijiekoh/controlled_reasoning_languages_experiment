import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-391»

structure LogFractionMaximizationProblem (n : ℕ) where
  B : Matrix (Fin n) (Fin n) ℝ
  p : Fin n → ℝ

def LogFractionMaximizationProblem.yVec {n : ℕ} (P : LogFractionMaximizationProblem n)
    (p : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j, P.B i j * p j

def LogFractionMaximizationProblem.objectiveFn {n : ℕ} (P : LogFractionMaximizationProblem n)
    (p : Fin n → ℝ) : ℝ :=
  ∑ i, Real.log ((P.yVec p i) / (P.yVec p i - p i))

def LogFractionMaximizationProblem.isFeasible {n : ℕ}
    (_P : LogFractionMaximizationProblem n) (p : Fin n → ℝ) : Prop :=
  (∑ i, p i = 1) ∧ ∀ i, 0 ≤ p i

structure EquivalentConvexOptimizationProblem (n : ℕ) where
  C : Matrix (Fin n) (Fin n) ℝ
  y : Fin n → ℝ

def EquivalentConvexOptimizationProblem.Cy {n : ℕ} (P : EquivalentConvexOptimizationProblem n) :
    Fin n → ℝ :=
  fun i => ∑ j, P.C i j * P.y j

def EquivalentConvexOptimizationProblem.objectiveFn {n : ℕ}
    (P : EquivalentConvexOptimizationProblem n) : ℝ :=
  -∑ i, Real.log (1 + P.Cy i)

def EquivalentConvexOptimizationProblem.isFeasible {n : ℕ}
    (P : EquivalentConvexOptimizationProblem n) : Prop :=
  ((∑ i, P.y i) - ∑ i, P.Cy i = 1) ∧ ∀ i, 0 ≤ P.y i - P.Cy i

theorem logFractionProblem_equivalent_to_convexProblem
    (n : ℕ)
    (A C : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (hv_nonneg : ∀ i, 0 ≤ v i)
    (hA_diag : ∀ i, A i i = 1)
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (h_equiv :
      let B : Matrix (Fin n) (Fin n) ℝ := fun i j => A i j + v i
      IsUnit B ∧ B⁻¹ = 1 - C) :
    let B : Matrix (Fin n) (Fin n) ℝ := fun i j => A i j + v i
    ∀ P : LogFractionMaximizationProblem n,
      P.B = B →
      ∃ Q : EquivalentConvexOptimizationProblem n,
        Q.C = C ∧
        Q.y = (fun i => ∑ j, B i j * P.p j) ∧
          (LogFractionMaximizationProblem.isFeasible P P.p ↔
            EquivalentConvexOptimizationProblem.isFeasible Q) ∧
          (LogFractionMaximizationProblem.objectiveFn P P.p = Q.objectiveFn) := by
  sorry

end «CAM-Bench-391»
