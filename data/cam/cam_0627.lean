import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-627»

open scoped BigOperators

structure LogUtilityPortfolioProblem (n m : ℕ) where
  π : Fin m → ℝ
  p : Fin m → Fin n → ℝ

def LogUtilityPortfolioProblem.scenarioReturn {n m : ℕ}
    (P : LogUtilityPortfolioProblem n m) (j : Fin m) (x : Fin n → ℝ) : ℝ :=
  ∑ i, P.p j i * x i

def LogUtilityPortfolioProblem.inDomain {n m : ℕ}
    (P : LogUtilityPortfolioProblem n m) (x : Fin n → ℝ) : Prop :=
  ∀ j, 0 < P.scenarioReturn j x

def LogUtilityPortfolioProblem.isFeasible {n m : ℕ}
    (P : LogUtilityPortfolioProblem n m) (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ (∑ i, x i = 1)

def LogUtilityPortfolioProblem.isAdmissible {n m : ℕ}
    (P : LogUtilityPortfolioProblem n m) (x : Fin n → ℝ) : Prop :=
  P.isFeasible x ∧ P.inDomain x

def LogUtilityPortfolioProblem.objective {n m : ℕ}
    (P : LogUtilityPortfolioProblem n m) (x : Fin n → ℝ) : ℝ :=
  ∑ j, P.π j * Real.log (P.scenarioReturn j x)

theorem logUtilityPortfolioProblem_isConvexOptimization
    {n m : ℕ} (P : LogUtilityPortfolioProblem n m)
    (hπ_nonneg : ∀ j, 0 ≤ P.π j)
    (hπ_sum : ∑ j, P.π j = 1) :
    ∃ S : Set (Fin n → ℝ), ∃ f : (Fin n → ℝ) → ℝ,
      S = {x : Fin n → ℝ | P.isAdmissible x} ∧
      f = P.objective ∧
      Convex ℝ S ∧
      ConcaveOn ℝ S f := by
  sorry

end «CAM-Bench-627»
