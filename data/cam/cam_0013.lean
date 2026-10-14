import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-13»

def feasible {ι α : Type*} (g : ι → α → ℝ) (x : α) : Prop :=
  ∀ i : ι, g i x ≤ 0

def active {ι α : Type*} (g : ι → α → ℝ) (i : ι) (x : α) : Prop :=
  g i x = 0

def linearFunction {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x y : Fin n → ℝ, ∀ α β : ℝ, g (α • x + β • y) = α * g x + β * g y

def LICQ {ι n : Type*} [Fintype ι] (g : ι → (n → ℝ) → ℝ) (x : n → ℝ) : Prop :=
  feasible g x ∧
  (∀ i : {i : ι // active g i x}, DifferentiableAt ℝ (g i) x) ∧
  LinearIndependent ℝ (fun i : {i : ι // active g i x} => fderiv ℝ (g i) x)

def linearlyDependent {m n : ℕ} (v : Fin m → Fin n → ℝ) : Prop :=
  ∃ a : Fin m → ℝ, a ≠ 0 ∧ ∑ i : Fin m, a i • v i = 0

structure RedundantConstraintFeasibilityProblem where
  objective : (Fin 2 → ℝ) → ℝ
  g : Fin 2 → (Fin 2 → ℝ) → ℝ

def RedundantConstraintFeasibilityProblem.isFeasible
    (p : RedundantConstraintFeasibilityProblem) (x : Fin 2 → ℝ) : Prop :=
  feasible p.g x

def RedundantConstraintFeasibilityProblem.default :
    RedundantConstraintFeasibilityProblem where
  objective := fun _ => 0
  g := fun
    | 0 => fun x => x 0
    | 1 => fun x => 2 * x 0

theorem redundant_constraint_problem_at_origin :
    let p := RedundantConstraintFeasibilityProblem.default
    let xstar : Fin 2 → ℝ := fun
      | ⟨0, _⟩ => 0
      | ⟨1, _⟩ => 0
    p.isFeasible xstar ∧
      active p.g 0 xstar ∧
      active p.g 1 xstar ∧
      linearFunction (p.g 0) ∧
      linearFunction (p.g 1) ∧
      ¬ LICQ p.g xstar := by
  sorry

end «CAM-Bench-13»
