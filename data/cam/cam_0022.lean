import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-22»

def KarushKuhnTuckerConditions
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (g : ι → E → ℝ) (xstar : E) : Prop :=
  DifferentiableAt ℝ f xstar ∧
  (∀ i, DifferentiableAt ℝ (g i) xstar) ∧
  (∀ i, 0 ≤ g i xstar) ∧
  ∃ lam : ι → ℝ,
    (∀ i, 0 ≤ lam i) ∧
    gradient f xstar - ∑ i, (lam i) • gradient (g i) xstar = 0 ∧
    ∀ i, lam i * g i xstar = 0

def IsOptimalSolution
    {E : Type*}
    (feasible : E → Prop) (f : E → ℝ) (xstar : E) : Prop :=
  feasible xstar ∧ ∀ x, feasible x → f xstar ≤ f x

structure TwoConstraintNonlinearProgram where
  xstar : Fin 2 → ℝ
  objective : (Fin 2 → ℝ) → ℝ
  g1 : (Fin 2 → ℝ) → ℝ
  g2 : (Fin 2 → ℝ) → ℝ

def TwoConstraintNonlinearProgram.standard : TwoConstraintNonlinearProgram where
  xstar := ![0, 1]
  objective := fun x => -2 * x 0 + x 1
  g1 := fun x => (1 - x 0) ^ 3 - x 1
  g2 := fun x => x 1 + (1 / 4 : ℝ) * (x 0) ^ 2 - 1

def TwoConstraintNonlinearProgram.isFeasible (P : TwoConstraintNonlinearProgram) (x : Fin 2 → ℝ) : Prop :=
  P.g1 x ≥ 0 ∧ P.g2 x ≥ 0

def TwoConstraintNonlinearProgram.objectiveValue (P : TwoConstraintNonlinearProgram) (x : Fin 2 → ℝ) : ℝ :=
  P.objective x

theorem twoConstraintNonlinearProgram_kkt_satisfied :
    let P := TwoConstraintNonlinearProgram.standard
    KarushKuhnTuckerConditions
        (fun x : EuclideanSpace ℝ (Fin 2) =>
          P.objective ((EuclideanSpace.equiv (Fin 2) ℝ) x))
        (fun i : Fin 2 =>
          match i.1 with
          | 0 => fun x : EuclideanSpace ℝ (Fin 2) =>
              P.g1 ((EuclideanSpace.equiv (Fin 2) ℝ) x)
          | 1 => fun x : EuclideanSpace ℝ (Fin 2) =>
              P.g2 ((EuclideanSpace.equiv (Fin 2) ℝ) x)
          | _ => fun x : EuclideanSpace ℝ (Fin 2) =>
              P.g1 ((EuclideanSpace.equiv (Fin 2) ℝ) x))
        ((EuclideanSpace.equiv (Fin 2) ℝ).symm P.xstar) := by
  sorry

end «CAM-Bench-22»
